use async_ffi::{FfiFuture, FutureExt as _};

#[no_mangle]
pub unsafe extern "C" fn plugin_run(a: u32, b: u32) -> FfiFuture<u32> {
    async move {
        async_std::task::sleep(std::time::Duration::from_millis(500)).await;
        a + b
    }
    .into_ffi()
}
