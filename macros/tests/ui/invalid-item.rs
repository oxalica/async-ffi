use async_ffi_macros::async_ffi;

#[async_ffi]
pub fn not_async() {}

pub trait Trait {
    #[async_ffi_macros::async_ffi]
    async fn method(&self);
}

impl Trait for () {
    #[async_ffi_macros::async_ffi]
    async fn method(&self) {}
}

fn main() {}
