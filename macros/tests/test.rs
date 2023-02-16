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
