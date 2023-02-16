#![deny(unused_variables)]
use async_ffi_macros::async_ffi;

#[async_ffi]
pub async fn unused_param(x: i32) -> i32 {
    42
}

fn main() {}
