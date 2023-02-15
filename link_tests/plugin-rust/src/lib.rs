#[async_ffi::async_ffi]
#[no_mangle]
pub async unsafe extern "C" fn plugin_run(a: u32, b: u32) -> u32 {
    async_std::task::sleep(std::time::Duration::from_millis(500)).await;
    a + b
}
