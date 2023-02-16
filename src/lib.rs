//! # FFI-compatible [`Future`][`std::future::Future`]s
//!
//! Rust currently doesn't provide stable ABI nor stable layout of related structs like
//! `dyn Future` or `Waker`.
//! With this crate, we can wrap async blocks or async functions to make a `Future` FFI-safe.
//!
//! [`FfiFuture`] provides the same functionality as `Box<dyn Future<Output = T> + Send>` but
//! it's FFI-compatible, aka. `repr(C)`. Any `Future<Output = T> + Send + 'static` can be converted
//! into [`FfiFuture`] by calling [`into_ffi`][`FutureExt::into_ffi`] on it, after `use`ing the
//! trait [`FutureExt`].
//!
//! [`FfiFuture`] implements `Future<Output = T> + Send`. You can `await` a [`FfiFuture`] just like
//! a normal `Future` to wait and get the output.
//!
//! For non-[`Send`] or non-`'static` futures, see the section
//! [Variants of `FfiFuture`](#variants-of-ffifuture) below.
//!
//! ## Examples
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
//! ## Proc-macro helpers
//! If you enable the feature `macros` (disabled by default), an attribute-like procedural macro
#![cfg_attr(not(feature = "macros"), doc = r"`async_ffi`")]
#![cfg_attr(feature = "macros", doc = r"[`async_ffi`]")]
//! is available at top-level. See its own documentation for details.
//!
//! With the macro, the example above can be simplified to:
//! ```
//! # #[cfg(feature = "macros")] {
//! # async fn do_some_io(_: u32) -> u32 { 0 }
//! # async fn do_some_sleep(_: u32) {}
//! use async_ffi::async_ffi;
//!
//! #[no_mangle]
//! #[async_ffi]
//! pub async extern "C" fn work(arg: u32) -> u32 {
//!     let ret = do_some_io(arg).await;
//!     do_some_sleep(42).await;
//!     ret
//! }
//! # }
//! ```
//!
//! ## Panics
//!
//! You should know that
//! [unwinding across an FFI boundary is Undefined Behaviour](https://doc.rust-lang.org/nomicon/ffi.html#ffi-and-panics).
//!
//! ### Panic in `Future::poll`
//!
//! Since the body of `async fn` is translated to [`Future::poll`] by the compiler, the `poll`
//! method is likely to panic. If this happen, the wrapped [`FfiFuture`] will catch unwinding
//! with [`std::panic::catch_unwind`], returning [`FfiPoll::Panicked`] to cross the FFI boundary.
//! And the other side (usually the plugin host) will get this value in the implementation of
//! `<FfiFuture<T> as std::future::Future>::poll`, and explicit propagate the panic,
//! just like [`std::sync::Mutex`]'s poisoning mechanism.
//!
//! ### Panic in `Future::drop` or any waker vtable functions `Waker::*`
//!
//! Unfortunately, this is very difficult to handle since drop cleanup and `Waker` functions are
//! expected to be infallible. If these functions panic, we would just call [`std::process::abort`]
//! to terminate the whole program.
//!
//! ## Variants of `FfiFuture`
//!
//! There are a few variants of [`FfiFuture`]. The table below shows their coresponding `std`
//! type.
//!
//! | Type                                                          | The coresponding `std` type                    |
//! |---------------------------------------------------------------|------------------------------------------------|
//! | [`FfiFuture<T>`]                                              | `Box<dyn Future<Output = T> + Send + 'static>` |
//! | [`LocalFfiFuture<T>`]                                         | `Box<dyn Future<Output = T> + 'static>`        |
//! | [`BorrowingFfiFuture<'a, T>`][`BorrowingFfiFuture`]           | `Box<dyn Future<Output = T> + Send + 'a>`      |
//! | [`LocalBorrowingFfiFuture<'a, T>`][`LocalBorrowingFfiFuture`] | `Box<dyn Future<Output = T> + 'a>`             |
//!
//! All of these variants are ABI-compatible to each other, since lifetimes and [`Send`] cannot be
//! represented by the C ABI. These bounds are only checked in the Rust side. It's your duty to
//! guarantee that the [`Send`] and lifetime bounds are respected in the foreign code of your
//! external `fn`s.
//!
//! ## Performance and cost
//!
//! The conversion between `FfiFuture` and orinary `Future` is not cost-free. Currently
//! [`FfiFuture::new`] and its alias [`FutureExt::into_ffi`] does one extra allocation.
//! When `poll`ing an `FfiFuture`, the `Waker` supplied does one extra allocation when `clone`d.
//!
//! It's recommanded to only wrap you `async` code once right at the FFI boundary, and use ordinary
//! `Future` everywhere else. It's usually not a good idea to use `FfiFuture` in methods, trait
//! methods, or generic codes.
//!
//! ## [`abi-stable`] suppport
//!
//! If you want to use this crate with [`abi-stable`] interfaces. You can enable the feature flag
//! `abi_stable` (disabled by default), then the struct `FfiFuture` and friends would derive
//! `abi_stable::StableAbi`.
//!
//! [`abi-stable`]: https://github.com/rodrimati1992/abi_stable_crates/
#![deny(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]
use std::{
    convert::{TryFrom, TryInto},
    fmt,
    future::Future,
    marker::PhantomData,
    mem::{self, ManuallyDrop},
    pin::Pin,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

#[cfg(feature = "macros")]
#[cfg_attr(docsrs, doc(cfg(feature = "macros")))]
pub use macros::async_ffi;

/// The ABI version of [`FfiFuture`] and all variants.
/// Every non-compatible ABI change will increase this number, as well as the crate major version.
pub const ABI_VERSION: u32 = 2;

/// The FFI compatible [`std::task::Poll`]
///
/// [`std::task::Poll`]: std::task::Poll
#[repr(C, u8)]
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
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
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
pub struct FfiContext<'a> {
    /// This waker is passed as borrow semantic.
    /// The external fn must not `drop` or `wake` it.
    waker: *const FfiWakerBase,
    /// Lets the compiler know that this references the FfiWaker and should not outlive it
    _marker: PhantomData<&'a FfiWakerBase>,
}

impl<'a> FfiContext<'a> {
    /// SAFETY: Vtable functions of `waker` are unsafe, the caller must ensure they have a
    /// sane behavior as a Waker. `with_context` relies on this to be safe.
    unsafe fn new(waker: &'a FfiWaker) -> Self {
        Self {
            waker: (waker as *const FfiWaker).cast::<FfiWakerBase>(),
            _marker: PhantomData,
        }
    }

    /// Runs a closure with the [`FfiContext`] as a normal [`std::task::Context`].
    ///
    /// [`std::task::Context`]: std::task::Context
    pub fn with_context<T, F: FnOnce(&mut Context) -> T>(&mut self, closure: F) -> T {
        // C vtable functions are considered from FFI and they are not expected to unwind, so we don't
        // need to wrap them with `DropBomb`.
        static RUST_WAKER_VTABLE: RawWakerVTable = {
            unsafe fn clone(data: *const ()) -> RawWaker {
                let waker = data.cast::<FfiWaker>();
                let cloned = ((*(*waker).base.vtable).clone)(waker.cast());
                RawWaker::new(cloned.cast(), &RUST_WAKER_VTABLE)
            }
            unsafe fn wake(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*(*waker).base.vtable).wake)(waker.cast());
            }
            unsafe fn wake_by_ref(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*(*waker).base.vtable).wake_by_ref)(waker.cast());
            }
            unsafe fn drop(data: *const ()) {
                let waker = data.cast::<FfiWaker>();
                ((*(*waker).base.vtable).drop)(waker.cast());
            }
            RawWakerVTable::new(clone, wake, wake_by_ref, drop)
        };

        // SAFETY: `waker`'s vtable functions must have sane behaviors, this is the contract of
        // `FfiContext::new`.
        let waker = unsafe {
            // The waker reference is borrowed from external context. We must not call drop on it.
            ManuallyDrop::new(Waker::from_raw(RawWaker::new(
                self.waker.cast(),
                &RUST_WAKER_VTABLE,
            )))
        };
        let mut ctx = Context::from_waker(&waker);

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
            unsafe extern "C" fn clone(data: *const FfiWakerBase) -> *const FfiWakerBase {
                DropBomb::with("Waker::clone", || {
                    let data = data as *mut FfiWaker;
                    let waker: Waker = (*(*data).waker.owned).clone();
                    Box::into_raw(Box::new(FfiWaker {
                        base: FfiWakerBase {
                            vtable: &C_WAKER_VTABLE_OWNED,
                        },
                        waker: WakerUnion {
                            owned: ManuallyDrop::new(waker),
                        },
                    }))
                    .cast()
                })
            }
            // In this case, we must own `data`. This can only happen when the `data` pointer is returned from `clone`.
            // Thus the it is `Box<FfiWaker>`.
            unsafe extern "C" fn wake(data: *const FfiWakerBase) {
                DropBomb::with("Waker::wake", || {
                    let b = Box::from_raw(data as *mut FfiWaker);
                    ManuallyDrop::into_inner(b.waker.owned).wake();
                });
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWakerBase) {
                DropBomb::with("Waker::wake_by_ref", || {
                    let data = data as *mut FfiWaker;
                    (*data).waker.owned.wake_by_ref();
                });
            }
            // Same as `wake`.
            unsafe extern "C" fn drop(data: *const FfiWakerBase) {
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
            unsafe extern "C" fn clone(data: *const FfiWakerBase) -> *const FfiWakerBase {
                DropBomb::with("Waker::clone", || {
                    let data = data as *mut FfiWaker;
                    let waker: Waker = (*(*data).waker.reference).clone();
                    Box::into_raw(Box::new(FfiWaker {
                        base: FfiWakerBase {
                            vtable: &C_WAKER_VTABLE_OWNED,
                        },
                        waker: WakerUnion {
                            owned: ManuallyDrop::new(waker),
                        },
                    }))
                    .cast()
                })
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWakerBase) {
                DropBomb::with("Waker::wake_by_ref", || {
                    let data = data as *mut FfiWaker;
                    (*(*data).waker.reference).wake_by_ref();
                });
            }
            unsafe extern "C" fn unreachable(_: *const FfiWakerBase) {
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
            base: FfiWakerBase {
                vtable: &C_WAKER_VTABLE_REF,
            },
            waker: WakerUnion {
                reference: self.waker(),
            },
        };

        // SAFETY: The behavior of `waker` is sane since we forward them to another valid Waker.
        // That waker must be safe to use due to the contract of `RawWaker::new`.
        let mut ctx = unsafe { FfiContext::new(&waker) };

        closure(&mut ctx)
    }
}

// Inspired by Gary Guo (github.com/nbdd0121)
//
// The base is what can be accessed through FFI, and the regular struct contains
// internal data (the original waker).
#[repr(C)]
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
struct FfiWakerBase {
    vtable: *const FfiWakerVTable,
}
#[repr(C)]
struct FfiWaker {
    base: FfiWakerBase,
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
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
struct FfiWakerVTable {
    clone: unsafe extern "C" fn(*const FfiWakerBase) -> *const FfiWakerBase,
    wake: unsafe extern "C" fn(*const FfiWakerBase),
    wake_by_ref: unsafe extern "C" fn(*const FfiWakerBase),
    drop: unsafe extern "C" fn(*const FfiWakerBase),
}

/// The FFI compatible future type with [`Send`] bound.
///
/// See [module level documentation](`crate`) for more details.
#[repr(transparent)]
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
pub struct BorrowingFfiFuture<'a, T>(LocalBorrowingFfiFuture<'a, T>);

/// The FFI compatible future type with [`Send`] bound and `'static` lifetime,
/// which is needed for most use cases.
///
/// See [module level documentation](`crate`) for more details.
pub type FfiFuture<T> = BorrowingFfiFuture<'static, T>;

/// Helper trait to provide conversion from `Future` to [`FfiFuture`] or [`LocalFfiFuture`].
///
/// See [module level documentation](`crate`) for more details.
pub trait FutureExt: Future + Sized {
    /// Convert a Rust `Future` implementing [`Send`] into a FFI-compatible [`FfiFuture`].
    fn into_ffi<'a>(self) -> BorrowingFfiFuture<'a, Self::Output>
    where
        Self: Send + 'a,
    {
        BorrowingFfiFuture::new(self)
    }

    /// Convert a Rust `Future` into a FFI-compatible [`LocalFfiFuture`].
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
    /// # Errors
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
    /// Convert an [`std::future::Future`] implementing [`Send`] into a FFI-compatible [`FfiFuture`].
    ///
    /// Usually [`FutureExt::into_ffi`] is preferred and is identical to this method.
    pub fn new<F: Future<Output = T> + Send + 'a>(fut: F) -> Self {
        Self(LocalBorrowingFfiFuture::new(fut))
    }
}

// SAFETY: This is safe since we allow only `Send` Future in `FfiFuture::new`.
unsafe impl<T> Send for BorrowingFfiFuture<'_, T> {}

impl<T> Future for BorrowingFfiFuture<'_, T> {
    type Output = T;

    fn poll(mut self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        Pin::new(&mut self.0).poll(ctx)
    }
}

/// The FFI compatible future type without [`Send`] bound.
///
/// Non-[`Send`] `Future`s can only be converted into [`LocalFfiFuture`]. It is not able to be
/// `spawn`ed in a multi-threaded runtime, but is useful for thread-local futures, single-threaded
/// runtimes, or single-threaded targets like `wasm32-unknown-unknown`.
///
/// See [module level documentation](`crate`) for more details.
#[repr(C)]
#[cfg_attr(feature = "abi_stable", derive(abi_stable::StableAbi))]
pub struct LocalBorrowingFfiFuture<'a, T> {
    fut_ptr: *mut (),
    poll_fn: unsafe extern "C" fn(fut_ptr: *mut (), context_ptr: *mut FfiContext) -> FfiPoll<T>,
    drop_fn: unsafe extern "C" fn(*mut ()),
    _marker: PhantomData<&'a ()>,
}

/// The FFI compatible future type without `Send` bound but with `'static` lifetime.
///
/// See [module level documentation](`crate`) for more details.
pub type LocalFfiFuture<T> = LocalBorrowingFfiFuture<'static, T>;

impl<'a, T> LocalBorrowingFfiFuture<'a, T> {
    /// Convert an [`std::future::Future`] into a FFI-compatible [`LocalFfiFuture`].
    ///
    /// Usually [`FutureExt::into_local_ffi`] is preferred and is identical to this method.
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
        // SAFETY: This is safe since `drop_fn` is construct from `LocalBorrowingFfiFuture::new`
        // and is a dropper
        // `LocalBorrowingFfiFuture::new` and they are just a Box pointer and its coresponding
        // dropper.
        unsafe { (self.drop_fn)(self.fut_ptr) };
    }
}

impl<T> Future for LocalBorrowingFfiFuture<'_, T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY: This is safe since `poll_fn` is constructed from `LocalBorrowingFfiFuture::new`
        // and it just forwards to the original safe `Future::poll`.
        ctx.with_ffi_context(|ctx| unsafe { (self.poll_fn)(self.fut_ptr, ctx) })
            .try_into()
            // Propagate panic from FFI.
            .unwrap_or_else(|_| panic!("FFI future panicked"))
    }
}
