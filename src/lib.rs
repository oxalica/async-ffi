use std::future::Future;
use std::mem::ManuallyDrop;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

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
    /// This waker is pass as borrow semantic.
    /// The external fn must not `drop` or `wake` it.
    waker_ref: *const FfiWaker,
}

#[repr(C)]
struct FfiWaker {
    data: *const (),
    vtable: &'static FfiWakerVTable,
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
#[repr(C)]
struct FfiWakerVTable {
    clone: unsafe extern "C" fn(*const ()) -> FfiWaker,
    wake: unsafe extern "C" fn(*const ()),
    wake_by_ref: unsafe extern "C" fn(*const ()),
    drop: unsafe extern "C" fn(*const ()),
}

pub trait FutureExt<T> {
    fn into_ffi(self) -> FfiFuture<T>;
}

impl<T, F> FutureExt<T> for F
where
    T: 'static,
    F: Future<Output = T> + 'static,
{
    fn into_ffi(self) -> FfiFuture<T> {
        FfiFuture::new(self)
    }
}

impl<T: 'static> FfiFuture<T> {
    // Called in executor or async fn provider side.
    pub fn new<F: Future<Output = T> + 'static>(fut: F) -> FfiFuture<T> {
        unsafe extern "C" fn poll_fn<F: Future>(
            fut_ptr: *mut (),
            context_ptr: *mut FfiContext,
        ) -> FfiPoll<F::Output> {
            static RUST_WAKER_VTABLE: RawWakerVTable = {
                unsafe fn clone(data: *const ()) -> RawWaker {
                    let c_waker = &*data.cast::<FfiWaker>();
                    let cloned: FfiWaker = (c_waker.vtable.clone)(c_waker.data);
                    let data = Box::into_raw(Box::new(cloned));
                    RawWaker::new(data as *const _ as *const (), &RUST_WAKER_VTABLE)
                }
                // In this case, we must own `data`. This can only happen on the `RawWaker` returned from `clone`.
                // Thus the `data` is a `Box<CRawWaker>`.
                unsafe fn wake(data: *const ()) {
                    let c_waker = Box::from_raw(data.cast::<FfiWaker>() as *mut FfiWaker);
                    (c_waker.vtable.wake)(c_waker.data);
                }
                unsafe fn wake_by_ref(data: *const ()) {
                    let c_waker = &*data.cast::<FfiWaker>();
                    (c_waker.vtable.wake_by_ref)(c_waker.data);
                }
                // Same as `wake`.
                unsafe fn drop(data: *const ()) {
                    let c_waker = Box::from_raw(data.cast::<FfiWaker>() as *mut FfiWaker);
                    (c_waker.vtable.drop)(c_waker.data);
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

impl<T> Drop for FfiFuture<T> {
    fn drop(&mut self) {
        unsafe { (self.drop_fn)(self.fut_ptr) };
    }
}

impl<T> Future for FfiFuture<T> {
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        static C_WAKER_VTABLE: FfiWakerVTable = {
            unsafe extern "C" fn clone(data: *const ()) -> FfiWaker {
                let w: Waker = (*data.cast::<Waker>()).clone();
                FfiWaker {
                    data: Box::into_raw(Box::new(w)).cast(),
                    vtable: &C_WAKER_VTABLE,
                }
            }
            // In this case, we must own `data`. This can only happen on the `CRawWaker` returned from `clone`.
            // Thus the `data` is a `Box<Waker>`.
            unsafe extern "C" fn wake(data: *const ()) {
                Box::from_raw(data.cast::<Waker>() as *mut Waker).wake();
            }
            unsafe extern "C" fn wake_by_ref(data: *const ()) {
                (*data.cast::<Waker>()).wake_by_ref();
            }
            // Same as `wake`.
            unsafe extern "C" fn drop(data: *const ()) {
                std::mem::drop(Box::from_raw(data.cast::<Waker>() as *mut Waker));
            }
            FfiWakerVTable {
                clone,
                wake,
                wake_by_ref,
                drop,
            }
        };

        let c_waker = FfiWaker {
            data: cx.waker() as *const Waker as *const (),
            vtable: &C_WAKER_VTABLE,
        };
        let mut c_ctx = FfiContext {
            waker_ref: &c_waker,
        };
        match unsafe { (self.poll_fn)(self.fut_ptr, &mut c_ctx) } {
            FfiPoll::Ready(v) => Poll::Ready(v),
            FfiPoll::Pending => Poll::Pending,
        }
    }
}
