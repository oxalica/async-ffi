# async-ffi: FFI-compatible futures

[![Crates.io](https://img.shields.io/crates/v/async-ffi)](https://crates.io/crates/async-ffi)
[![docs.rs](https://img.shields.io/docsrs/async-ffi)][docs]

Convert your Rust `Future`s into a FFI-compatible struct without relying unstable Rust ABI and struct layout.
Easily provide async functions in dynamic library maybe compiled with different Rust than the invoker.

See [documentation][docs] for more details.

[docs]: https://docs.rs/async-ffi

Provide some async functions in library: (plugin side)
```rust
// Compile with `crate-type = ["cdylib"]`.
use async_ffi::{FfiFuture, FutureExt};

#[no_mangle]
pub extern "C" fn work(arg: u32) -> FfiFuture<u32> {
    async move {
        let ret = do_some_io(arg).await;
        do_some_sleep(42).await;
        ret
    }
    .into_ffi()
}
```

Execute async functions from external library: (host or executor side)
```rust
use async_ffi::{FfiFuture, FutureExt};

extern "C" {
    #[no_mangle]
    fn work(arg: u32) -> FfiFuture<u32>;
}

async fn run_work(arg: u32) -> u32 {
    unsafe { work(arg).await }
}
```

#### License

MIT Licensed.
