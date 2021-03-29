use std::{
    future::Future,
    pin::Pin,
    rc::Rc,
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

use async_ffi::FutureExt as _;

#[tokio::test]
async fn call_test() {
    async fn foo(x: u32) -> u32 {
        x + 42
    }

    let ret = foo(1).into_ffi().await;
    assert_eq!(ret, 43);
}

#[test]
fn future_drop_test() {
    let rc = Rc::new(());

    struct Dropper(Rc<()>);
    let d = Dropper(rc.clone());
    let fut = async move { drop(d) }.into_ffi();
    assert_eq!(Rc::strong_count(&rc), 2);
    drop(fut);
    assert_eq!(Rc::strong_count(&rc), 1);
}

#[test]
fn waker_test() {
    static VTABLE: RawWakerVTable = {
        unsafe fn log(data: *const (), s: &str) {
            (*(data as *mut () as *mut Vec<String>)).push(s.to_owned());
        }
        unsafe fn clone(data: *const ()) -> RawWaker {
            log(data, "clone");
            RawWaker::new(data, &VTABLE)
        }
        unsafe fn wake(data: *const ()) {
            log(data, "wake");
        }
        unsafe fn wake_by_ref(data: *const ()) {
            log(data, "wake_by_ref");
        }
        unsafe fn drop(data: *const ()) {
            log(data, "drop");
        }
        RawWakerVTable::new(clone, wake, wake_by_ref, drop)
    };

    struct Fut(usize, Option<Waker>);
    impl Future for Fut {
        type Output = i32;
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            let w = cx.waker();
            match self.0 {
                0 => {
                    w.wake_by_ref();
                    self.0 = 1;
                    Poll::Pending
                }
                1 => {
                    let w2 = w.clone();
                    w2.wake_by_ref();
                    self.1 = Some(w2.clone());
                    self.0 = 2;
                    Poll::Pending
                }
                2 => {
                    self.1.take().unwrap().wake();
                    self.0 = 3;
                    Poll::Ready(42)
                }
                _ => unreachable!(),
            }
        }
    }

    let mut v: Vec<String> = Vec::new();
    let v = &mut v as *mut _;
    let waker = unsafe { Waker::from_raw(RawWaker::new(v as *const (), &VTABLE)) };
    let mut ctx = Context::from_waker(&waker);

    let look = || std::mem::take(unsafe { &mut *v });

    let mut c_fut = Fut(0, None).into_ffi();
    assert_eq!(Pin::new(&mut c_fut).poll(&mut ctx), Poll::Pending);
    assert_eq!(look(), &["wake_by_ref"]);
    assert_eq!(Pin::new(&mut c_fut).poll(&mut ctx), Poll::Pending);
    assert_eq!(look(), &["clone", "wake_by_ref", "clone", "drop"]);
    assert_eq!(Pin::new(&mut c_fut).poll(&mut ctx), Poll::Ready(42));
    assert_eq!(look(), &["wake"]);
}
