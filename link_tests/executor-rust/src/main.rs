use anyhow::{Context as _, Result};
use async_ffi::FfiFuture;
use libloading::{Library, Symbol};
use std::time::{Duration, Instant};

// Some plugin fn.
type PluginRunFn = unsafe extern "C" fn(a: u32, b: u32) -> FfiFuture<u32>;

#[tokio::main]
async fn main() -> Result<()> {
    let path = std::env::args().nth(1).context("Missing argument")?;

    unsafe {
        let lib = Library::new(&path).context("Cannot load library")?;
        let plugin_run: Symbol<PluginRunFn> = lib.get(b"plugin_run")?;

        let t = Instant::now();
        let ret = plugin_run(42, 1).await;
        // We did some async sleep in plugin_run.
        assert!(Duration::from_millis(500) < t.elapsed());
        assert_eq!(ret, 43);
        println!("42 + 1 = {}", ret);
    }

    Ok(())
}
