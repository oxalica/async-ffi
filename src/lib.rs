//! # FFI-compatible futures
//!
//! In case of an async program with some async plugins, `Future`s need to cross the FFI boundary.
//! But Rust currently doesn't provide stable ABI nor stable layout of related structs like
//! `dyn Future` and `Waker`.
//! With this crate, we can easily wrap async blocks or async functions to make this happen.
//!
//! [`FfiFuture<T>`] provides the same function as `Box<dyn Future<Output = T> + Send>` but FFI-compatible (`repr(C)`).
//! Any future implementing `Send` can be converted to [`FfiFuture<T>`] by calling [`into_ffi`] on it.
//!
//! [`FfiFuture<T>`] also implements `Future<Output = T> + Send`. You can simply `await` a [`FfiFuture<T>`]
//! like a normal `Future` to get the output.
//!
//! There is also a non-`Send` version [`LocalFfiFuture<T>`] working like
//! `Box<dyn Future<Output = T>>`, which can be used for local future or single-threaded targets.
//! It is ABI-compatible to [`FfiFuture<T>`], but it's your duty to guarantee that non-`Send` types
//! never cross thread boundary.
//!
//! ## Panics
//!
//! [Unwinding across an FFI boundary is Undefined Behaviour](https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics).
//!
//! ### Panic in `Future::poll`
//!
//! Since the body of `async fn` is translated to `Future::poll` by compiler, it is most likely to
//! panic. In this case, the wrapped [`FfiFuture`] will catch unwinding with [`std::panic::catch_unwind`],
//! returning [`FfiPoll::Panicked`]. And the other side (usually the plugin host) will get this value
//! and explicit panic, just like [`std::sync::Mutex`]'s poisoning mechanism.
//!
//! ### Panic in `Future::drop` or any waker vtable functions `Waker::*`
//!
//! Unfortunately, this is very difficult to handle since drop cleanup and `Waker` functions are
//! expected to be infallible. If these functions panic, we would just call [`std::process::abort`].
//!
//! ## Example
//!
//! Provide some async functions in library: (plugin side)
//! ```
//! # async fn do_some_io(_: u32) -> u32 { 0 }
//! # async fn do_some_sleep(_: u32) {}
//! // Compile with `crate-type = ["cdylib"]`.
//! use async_ffi::{FfiFuture, FutureExt};
//!
//! #[no_mangle]
//! pub extern "C" fn work(arg: u32) -> FfiFuture<u32> {
//!     async move {
//!         let ret = do_some_io(arg).await;
//!         do_some_sleep(42).await;
//!         ret
//!     }
//!     .into_ffi()
//! }
//! ```
//!
//! Execute async functions from external library: (host or executor side)
//! ```
//! use async_ffi::{FfiFuture, FutureExt};
//!
//! // #[link(name = "myplugin...")]
//! extern "C" {
//!     #[no_mangle]
//!     fn work(arg: u32) -> FfiFuture<u32>;
//! }
//!
//! async fn run_work(arg: u32) -> u32 {
//!     unsafe { work(arg).await }
//! }
//! ```
//!
//! [`FfiFuture<T>`]: type.FfiFuture.html
//! [`LocalFfiFuture<T>`]: type.LocalFfiFuture.html
//! [`into_ffi`]: trait.FutureExt.html#tymethod.into_ffi
#![deny(missing_docs)]
use std::{
    convert::{TryFrom, TryInto},
    fmt,
    future::Future,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

/// The ABI version of `FfiFuture` and `LocalFfiFuture`.
/// Every non-compatible ABI change will increase this number.
pub const ABI_VERSION: u32 = 2;

type PollFn<T> = unsafe extern "C" fn(fut_ptr: *mut (), context_ptr: *mut FfiContext) -> FfiPoll<T>;

/// The FFI compatible [`std::task::Poll`]
///
/// [`std::task::Poll`]: std::task::Poll
#[repr(C, u8)]
pub enum FfiPoll<T> {
    /// Represents that a value is immediately ready.
    Ready(T),
    /// Represents that a value is not ready yet.
    Pending,
    /// Represents that the future panicked
    Panicked,
}

/// Abort on drop with a message.
struct DropBomb(&'static str);

impl DropBomb {
    fn with<T, F: FnOnce() -> T>(message: &'static str, f: F) -> T {
        let bomb = DropBomb(message);
        let ret = f();
        mem::forget(bomb);
        ret
    }
}

impl Drop for DropBomb {
    fn drop(&mut self) {
        use std::io::Write;
        // Use `Stderr::write_all` instead of `eprintln!` to avoid panicking here.
        let mut stderr = std::io::stderr();
        let _ = stderr.write_all(b"async-ffi: abort due to panic across the FFI boundary in ");
        let _ = stderr.write_all(self.0.as_bytes());
        let _ = stderr.write_all(b"\n");
        std::process::abort();
    }
}

/// The FFI compatible [`std::task::Context`]
///
/// [`std::task::Context`]: std::task::Context
#[repr(C)]
pub struct FfiContext<'a> {
    /// This waker is passed as borrow semantic.
    /// The external fn must not `drop` or `wake` it.
    waker_ref: *const FfiWaker,
    /// Lets the compiler know that this references the FfiWaker and should not outlive it
    phantom: PhantomData<&'a FfiWaker>,
}

impl<'a> FfiContext<'a> {
    fn new(waker: &'a FfiWaker) -> Self {
        Self {
            waker_ref: waker as *const _ as *const FfiWaker,
            phantom: PhantomData,
        }
    }

    /// Runs a closure with the [`FfiContext`] as a normal [`std::task::Context`].
    ///
    /// [`std::task::Context`]: std::task::Context
    pub unsafe fn with_context<T, F: FnOnce(&mut Context) -> T>(&mut self, closure: F) -> T {
        // C vtable functions are considered from FFI and they are not expected to unwind, so we don't
        // need to wrap them with `DropBomb`.
        static RUST_WAKER_VTABLE: RawWakerVTable = {
            unsafe fn clone(data: *const ()) -> RawWaker {
                let waker = data.cast::<FfiWaker>();
                let cloned = ((*waker).vtable.clone)(waker);
                RawWaker::new(cloned.cast(), &RUST_WAKER_VTABLE)
            }
            unsafe fn wake(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*waker).vtable.wake)(waker);
            }
            unsafe fn wake_by_ref(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*waker).vtable.wake_by_ref)(waker);
            }
            unsafe fn drop(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*waker).vtable.drop)(waker);
            }
            RawWakerVTable::new(clone, wake, wake_by_ref, drop)
        };

        // The `waker_ref` is borrowed from external context. We must not call drop on it.
        let waker = ManuallyDrop::new(Waker::from_raw(RawWaker::new(
            self.waker_ref.cast(),
            &RUST_WAKER_VTABLE,
        )));
        let mut ctx = Context::from_waker(&*waker);

        closure(&mut ctx)
    }
}

/// Helper trait to provide convenience methods for converting a [`std::task::Context`] to [`FfiContext`]
///
/// [`std::task::Context`]: std::task::Context
pub trait ContextExt {
    /// Runs a closure with the [`std::task::Context`] as a [`FfiContext`].
    ///
    /// [`std::task::Context`]: std::task::Context
    fn with_ffi_context<T, F: FnOnce(&mut FfiContext) -> T>(&mut self, closure: F) -> T;
}

impl<'a> ContextExt for Context<'a> {
    fn with_ffi_context<T, F: FnOnce(&mut FfiContext) -> T>(&mut self, closure: F) -> T {
        static C_WAKER_VTABLE_OWNED: FfiWakerVTable = {
            unsafe extern "C" fn clone(data: *const FfiWaker) -> *const FfiWaker {
                DropBomb::with("Waker::clone", || {
                    let waker: Waker = (*(*data).waker.owned).clone();
                    Box::into_raw(Box::new(FfiWaker {
                        vtable: &C_WAKER_VTABLE_OWNED,
                        waker: WakerUnion {
                            owned: ManuallyDrop::new(waker),
                        },
                    }))
                    .cast()
                })
            }
            // In this case, we must own `data`. This can only happen when the `data` pointer is returned from `clone`.
            // Thus the it is `Box<FfiWaker>`.
            unsafe extern "C" fn wake(data: *const FfiWaker) {
                DropBomb::with("Waker::wake", || {
                    let b = Box::from_raw(data as *mut FfiWaker);
                    ManuallyDrop::into_inner(b.waker.owned).wake();
                })
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWaker) {
                DropBomb::with("Waker::wake_by_ref", || {
                    (*data).waker.owned.wake_by_ref();
                })
            }
            // Same as `wake`.
            unsafe extern "C" fn drop(data: *const FfiWaker) {
                DropBomb::with("Waker::drop", || {
                    let mut b = Box::from_raw(data as *mut FfiWaker);
                    ManuallyDrop::drop(&mut b.waker.owned);
                    mem::drop(b);
                });
            }
            FfiWakerVTable {
                clone,
                wake,
                wake_by_ref,
                drop,
            }
        };

        static C_WAKER_VTABLE_REF: FfiWakerVTable = {
            unsafe extern "C" fn clone(data: *const FfiWaker) -> *const FfiWaker {
                DropBomb::with("Waker::clone", || {
                    let waker: Waker = (*(*data).waker.reference).clone();
                    Box::into_raw(Box::new(FfiWaker {
                        vtable: &C_WAKER_VTABLE_OWNED,
                        waker: WakerUnion {
                            owned: ManuallyDrop::new(waker),
                        },
                    }))
                    .cast()
                })
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWaker) {
                DropBomb::with("Waker::wake_by_ref", || {
                    (*(*data).waker.reference).wake_by_ref();
                })
            }
            unsafe extern "C" fn unreachable(_: *const FfiWaker) {
                std::process::abort();
            }
            FfiWakerVTable {
                clone,
                wake: unreachable,
                wake_by_ref,
                drop: unreachable,
            }
        };

        let waker = FfiWaker {
            vtable: &C_WAKER_VTABLE_REF,
            waker: WakerUnion {
                reference: self.waker(),
            },
        };

        let mut ctx = FfiContext::new(&waker);

        closure(&mut ctx)
    }
}

// Inspired by Gary Guo (github.com/nbdd0121)
#[repr(C)]
struct FfiWaker {
    vtable: &'static FfiWakerVTable,
    waker: WakerUnion,
}

#[repr(C)]
union WakerUnion {
    reference: *const Waker,
    owned: ManuallyDrop<Waker>,
    unknown: (),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C)]
struct FfiWakerVTable {
    clone: unsafe extern "C" fn(*const FfiWaker) -> *const FfiWaker,
    wake: unsafe extern "C" fn(*const FfiWaker),
    wake_by_ref: unsafe extern "C" fn(*const FfiWaker),
    drop: unsafe extern "C" fn(*const FfiWaker),
}

/// The FFI compatible future type with `Send` bound.
///
/// See [module level documentation](index.html) for more details.
#[repr(transparent)]
pub struct BorrowingFfiFuture<'a, T>(LocalBorrowingFfiFuture<'a, T>);

/// The FFI compatible future type with `Send` bound and `'static` lifetime,
/// which is needed for most use cases.
///
/// See [module level documentation](index.html) for more details.
pub type FfiFuture<T> = BorrowingFfiFuture<'static, T>;

/// Helper trait to provide conversion from `Future` to `FfiFuture` or `LocalFfiFuture`.
///
/// See [module level documentation](index.html) for more details.
pub trait FutureExt: Future + Sized {
    /// Convert a Rust `Future` implementing `Send` into a FFI-compatible `FfiFuture`.
    fn into_ffi<'a>(self) -> BorrowingFfiFuture<'a, Self::Output>
    where
        Self: Send + 'a,
    {
        BorrowingFfiFuture::new(self)
    }

    /// Convert a Rust `Future` into a FFI-compatible `LocalFfiFuture`.
    fn into_local_ffi<'a>(self) -> LocalBorrowingFfiFuture<'a, Self::Output>
    where
        Self: 'a,
    {
        LocalBorrowingFfiFuture::new(self)
    }
}

impl<F> FutureExt for F where F: Future + Sized {}

/// Represents that the poll function panicked.
#[derive(Debug)]
pub struct PollPanicked {
    _private: (),
}

impl fmt::Display for PollPanicked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("FFI poll function panicked")
    }
}

impl std::error::Error for PollPanicked {}

impl<T> FfiPoll<T> {
    /// Converts a [`std::task::Poll`] to the [`FfiPoll`].
    ///
    /// [`std::task::Poll`]: std::task::Poll
    pub fn from_poll(poll: Poll<T>) -> Self {
        match poll {
            Poll::Ready(r) => Self::Ready(r),
            Poll::Pending => Self::Pending,
        }
    }

    /// Try to convert a [`FfiPoll`] back to the [`std::task::Poll`].
    ///
    /// Returns `Err(PollPanicked)` if the result indicates the poll function panicked.
    ///
    /// [`std::task::Poll`]: std::task::Poll
    pub fn try_into_poll(self) -> Result<Poll<T>, PollPanicked> {
        match self {
            Self::Ready(r) => Ok(Poll::Ready(r)),
            Self::Pending => Ok(Poll::Pending),
            Self::Panicked => Err(PollPanicked { _private: () }),
        }
    }
}

impl<T> From<Poll<T>> for FfiPoll<T> {
    fn from(poll: Poll<T>) -> Self {
        Self::from_poll(poll)
    }
}

impl<T> TryFrom<FfiPoll<T>> for Poll<T> {
    type Error = PollPanicked;

    fn try_from(ffi_poll: FfiPoll<T>) -> Result<Self, PollPanicked> {
        ffi_poll.try_into_poll()
    }
}

impl<'a, T> BorrowingFfiFuture<'a, T> {
    /// Convert a Rust `Future` implementing `Send` into a FFI-compatible `FfiFuture`.
    ///
    /// Usually [`into_ffi`] is preferred and is identical to this method.
    ///
    /// [`into_ffi`]: trait.FutureExt.html#tymethod.into_ffi
    pub fn new<F: Future<Output = T> + Send + 'a>(fut: F) -> Self {
        Self(LocalBorrowingFfiFuture::new(fut))
    }
}

// This is safe since we allow only `Send` Future in `FfiFuture::new`.
unsafe impl<T> Send for BorrowingFfiFuture<'_, T> {}

impl<T> Future for BorrowingFfiFuture<'_, T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut self.0).poll(ctx)
    }
}

/// The FFI compatible future type without `Send` bound.
///
/// Non-`Send` `Future`s can only be converted into `LocalFfiFuture`. It is not able to be
/// `spawn`d in a multi-threaded runtime, but is useful for thread-local futures, single-threaded
/// runtimes, or single-threaded targets like `wasm`.
///
/// See [module level documentation](index.html) for more details.
#[repr(C)]
pub struct LocalBorrowingFfiFuture<'a, T> {
    fut_ptr: *mut (),
    poll_fn: PollFn<T>,
    drop_fn: unsafe extern "C" fn(*mut ()),
    _marker: PhantomData<&'a ()>,
}

/// The FFI compatible future type without `Send` bound but with `'static` lifetime.
///
/// See [module level documentation](index.html) for more details.
pub type LocalFfiFuture<T> = LocalBorrowingFfiFuture<'static, T>;

impl<'a, T> LocalBorrowingFfiFuture<'a, T> {
    /// Convert a Rust `Future` into a FFI-compatible `LocalFfiFuture`.
    ///
    /// Usually [`into_local_ffi`] is preferred and is identical to this method.
    ///
    /// [`into_local_ffi`]: trait.FutureExt.html#tymethod.into_local_ffi
    pub fn new<F: Future<Output = T> + 'a>(fut: F) -> Self {
        unsafe extern "C" fn poll_fn<F: Future>(
            fut_ptr: *mut (),
            context_ptr: *mut FfiContext,
        ) -> FfiPoll<F::Output> {
            // The poll fn is likely to panic since it contains most of user logic.
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let fut_pin = Pin::new_unchecked(&mut *fut_ptr.cast::<F>());
                (*context_ptr).with_context(|ctx| F::poll(fut_pin, ctx))
            })) {
                Ok(p) => p.into(),
                Err(payload) => {
                    // Panic payload may panic when dropped, ensure not propagate it.
                    // https://github.com/rust-lang/rust/issues/86027
                    DropBomb::with("drop of panic payload from Future::poll", move || {
                        drop(payload);
                    });
                    FfiPoll::Panicked
                }
            }
        }

        unsafe extern "C" fn drop_fn<T>(ptr: *mut ()) {
            DropBomb::with("Future::drop", || {
                drop(Box::from_raw(ptr.cast::<T>()));
            });
        }

        let ptr = Box::into_raw(Box::new(fut));
        Self {
            fut_ptr: ptr.cast(),
            poll_fn: poll_fn::<F>,
            drop_fn: drop_fn::<F>,
            _marker: PhantomData,
        }
    }
}

impl<T> Drop for LocalBorrowingFfiFuture<'_, T> {
    fn drop(&mut self) {
        unsafe { (self.drop_fn)(self.fut_ptr) };
    }
}

impl<T> Future for LocalBorrowingFfiFuture<'_, T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        ctx.with_ffi_context(|ctx| unsafe { (self.poll_fn)(self.fut_ptr, ctx) })
            .try_into()
            // Propagate panic from FFI.
            .unwrap_or_else(|_| panic!("FFI future panicked"))
    }
}
