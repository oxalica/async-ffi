use std::{
    future::Future,
    mem::ManuallyDrop,
    pin::Pin,
    process::abort,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

#[repr(C)]
pub struct FfiFuture<T> {
    fut_ptr: *mut (),
    poll_fn: PollFn<T>,
    drop_fn: unsafe extern "C" fn(*mut ()),
}

type PollFn<T> = unsafe extern "C" fn(fut_ptr: *mut (), context_ptr: *mut FfiContext) -> FfiPoll<T>;

#[repr(C, u8)]
enum FfiPoll<T> {
    Ready(T),
    Pending,
}

#[repr(C)]
struct FfiContext {
    /// This waker is passed as borrow semantic.
    /// The external fn must not `drop` or `wake` it.
    waker_ref: *const FfiWaker,
}

// Inspired by Gary Guo (github.com/nbdd0121)
#[repr(C)]
struct FfiWaker {
    vtable: &'static FfiWakerVTable,
    // Opaque fields after the end of struct.
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C)]
struct FfiWakerVTable {
    clone: unsafe extern "C" fn(*const FfiWaker) -> *const FfiWaker,
    wake: unsafe extern "C" fn(*const FfiWaker),
    wake_by_ref: unsafe extern "C" fn(*const FfiWaker),
    drop: unsafe extern "C" fn(*const FfiWaker),
}

pub trait FutureExt<T> {
    fn into_ffi(self) -> FfiFuture<T>;
}

impl<T, F> FutureExt<T> for F
where
    T: 'static,
    F: Future<Output = T> + Send + 'static,
{
    fn into_ffi(self) -> FfiFuture<T> {
        FfiFuture::new(self)
    }
}

impl<T: 'static> FfiFuture<T> {
    pub fn new<F: Future<Output = T> + Send + 'static>(fut: F) -> FfiFuture<T> {
        unsafe extern "C" fn poll_fn<F: Future>(
            fut_ptr: *mut (),
            context_ptr: *mut FfiContext,
        ) -> FfiPoll<F::Output> {
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
                (*context_ptr).waker_ref.cast(),
                &RUST_WAKER_VTABLE,
            )));
            let fut_pin = Pin::new_unchecked(&mut *fut_ptr.cast::<F>());
            let mut ctx = Context::from_waker(&*waker);
            match F::poll(fut_pin, &mut ctx) {
                Poll::Ready(v) => FfiPoll::Ready(v),
                Poll::Pending => FfiPoll::Pending,
            }
        }

        unsafe extern "C" fn drop_fn<T>(ptr: *mut ()) {
            drop(Box::from_raw(ptr.cast::<T>()));
        }

        let ptr = Box::into_raw(Box::new(fut));
        FfiFuture {
            fut_ptr: ptr.cast(),
            poll_fn: poll_fn::<F>,
            drop_fn: drop_fn::<F>,
        }
    }
}

/// This is safe since we allow only `Send` Future in `FfiFuture::new`.
unsafe impl<T> Send for FfiFuture<T> {}

impl<T> Drop for FfiFuture<T> {
    fn drop(&mut self) {
        unsafe { (self.drop_fn)(self.fut_ptr) };
    }
}

impl<T> Future for FfiFuture<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        #[repr(C)]
        struct FfiWakerImplOwned {
            vtable: &'static FfiWakerVTable,
            waker: Waker,
        }

        static C_WAKER_VTABLE_OWNED: FfiWakerVTable = {
            unsafe extern "C" fn clone(data: *const FfiWaker) -> *const FfiWaker {
                let waker: Waker = (*data.cast::<FfiWakerImplOwned>()).waker.clone();
                Box::into_raw(Box::new(FfiWakerImplOwned {
                    vtable: &C_WAKER_VTABLE_OWNED,
                    waker,
                }))
                .cast()
            }
            // In this case, we must own `data`. This can only happen on the `CRawWaker` returned from `clone`.
            // Thus the `data` is a `Box<Waker>`.
            unsafe extern "C" fn wake(data: *const FfiWaker) {
                let b = Box::from_raw(data as *mut FfiWakerImplOwned);
                b.waker.wake();
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWaker) {
                (*data.cast::<FfiWakerImplOwned>()).waker.wake_by_ref();
            }
            // Same as `wake`.
            unsafe extern "C" fn drop(data: *const FfiWaker) {
                let b = Box::from_raw(data as *mut FfiWakerImplOwned);
                std::mem::drop(b);
            }
            FfiWakerVTable {
                clone,
                wake,
                wake_by_ref,
                drop,
            }
        };

        #[repr(C)]
        struct FfiWakerImplRef {
            vtable: &'static FfiWakerVTable,
            waker: *const Waker,
        }

        static C_WAKER_VTABLE_REF: FfiWakerVTable = {
            unsafe extern "C" fn clone(data: *const FfiWaker) -> *const FfiWaker {
                let waker: Waker = (*(*data.cast::<FfiWakerImplRef>()).waker).clone();
                Box::into_raw(Box::new(FfiWakerImplOwned {
                    vtable: &C_WAKER_VTABLE_OWNED,
                    waker,
                }))
                .cast()
            }
            unsafe extern "C" fn wake_by_ref(data: *const FfiWaker) {
                (*(*data.cast::<FfiWakerImplRef>()).waker).wake_by_ref();
            }
            unsafe extern "C" fn unreachable(_: *const FfiWaker) {
                abort();
            }
            FfiWakerVTable {
                clone,
                wake: unreachable,
                wake_by_ref,
                drop: unreachable,
            }
        };

        let waker = FfiWakerImplRef {
            vtable: &C_WAKER_VTABLE_REF,
            waker: ctx.waker(),
        };
        let mut ctx = FfiContext {
            waker_ref: &waker as *const _ as *const FfiWaker,
        };
        match unsafe { (self.poll_fn)(self.fut_ptr, &mut ctx) } {
            FfiPoll::Ready(v) => Poll::Ready(v),
            FfiPoll::Pending => Poll::Pending,
        }
    }
}
