use async_ffi::{BorrowingFfiFuture, FfiFuture, LocalBorrowingFfiFuture, LocalFfiFuture};
use async_ffi_macros::async_ffi;

#[async_ffi]
#[no_mangle]
async extern "C" fn empty() {}

const _: extern "C" fn() -> FfiFuture<()> = empty;

#[async_ffi(?Send)]
#[no_mangle]
async extern "C" fn local() -> i32 {
    42
}

const _: extern "C" fn() -> LocalFfiFuture<i32> = local;

#[async_ffi]
#[no_mangle]
async extern "C" fn has_args(x: i32) -> i32 {
    x
}

const _: extern "C" fn(i32) -> FfiFuture<i32> = has_args;

extern "C" {
    #[async_ffi]
    pub async fn extern_fn(arg1: u32) -> u32;
}

const _: unsafe extern "C" fn(u32) -> FfiFuture<u32> = extern_fn;

#[async_ffi('fut)]
pub async fn borrow(a: &'fut i32) -> i32 {
    *a
}

const _: for<'a> fn(&'a i32) -> BorrowingFfiFuture<'a, i32> = borrow;

#[async_ffi('fut, ?Send)]
pub async fn borrow_non_send(a: &'fut i32) -> i32 {
    *a
}

const _: for<'a> fn(&'a i32) -> LocalBorrowingFfiFuture<'a, i32> = borrow_non_send;

#[async_ffi]
pub async fn pat_param(_: i32, (a, _, _b): (i32, i32, i32), x: i32, mut y: i32) -> i32 {
    y += 1;
    a + x + y
}

#[test]
#[allow(clippy::toplevel_ref_arg, clippy::unused_async)]
fn drop_order() {
    use std::cell::RefCell;
    use std::future::Future;
    use std::pin::Pin;
    use std::rc::Rc;
    use std::task::{Context, Poll};

    struct Dropper(&'static str, Rc<RefCell<Vec<&'static str>>>);

    impl Drop for Dropper {
        fn drop(&mut self) {
            self.1.borrow_mut().push(self.0);
        }
    }

    fn check_order<F>(
        f: fn(Dropper, Dropper, Dropper, (Dropper, Dropper)) -> F,
    ) -> Vec<&'static str>
    where
        F: Future<Output = ()>,
    {
        let order = Rc::new(RefCell::new(Vec::new()));
        let mut fut = f(
            Dropper("a", order.clone()),
            Dropper("b", order.clone()),
            Dropper("_arg", order.clone()),
            (Dropper("c", order.clone()), Dropper("_pat", order.clone())),
        );
        Dropper("ret", order.clone());
        let fut_pinned = unsafe { Pin::new_unchecked(&mut fut) };
        let mut cx = Context::from_waker(futures_task::noop_waker_ref());
        assert_eq!(fut_pinned.poll(&mut cx), Poll::Ready(()));
        Dropper("done", order.clone());
        drop(fut);
        let ret = order.borrow().to_vec();
        ret
    }

    #[async_ffi(?Send)]
    async fn func1(a: Dropper, ref mut _b: Dropper, _: Dropper, (_c, _): (Dropper, Dropper)) {
        a.1.borrow_mut().push("run");
    }
    async fn func2(a: Dropper, ref mut _b: Dropper, _: Dropper, (_c, _): (Dropper, Dropper)) {
        a.1.borrow_mut().push("run");
    }

    let ord1 = check_order(func1);
    let ord2 = check_order(func2);
    assert_eq!(ord1, ord2);
}
