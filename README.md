# async-ffi: FFI-compatible `Future`s

[![crates.io](https://img.shields.io/crates/v/async-ffi)](https://crates.io/crates/async-ffi)
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

By default `FfiFuture` requires the original `Future` to be `Send`.
In case of single-threaded runtime or target (like `wasm32-none-none`), we may need to relax this requirement.
So we have `LocalFfiFuture`, which is the almost the same as `FfiFuture` but without `Send` requirement.

```rust
// Compile with `crate-type = ["cdylib"]`, targeting `wasm32-none-none`.
use async_ffi::{LocalFfiFuture, FutureExt};

#[no_mangle]
pub extern "C" fn work(arg: u32) -> LocalFfiFuture<u32> {
    async move {
        let ret = do_some_io(arg).await;
        do_some_sleep(42).await;
        ret
    }
    .into_local_ffi()
}
```

## [`abi-stable`] suppport

If you want to use this crate with [`abi-stable`] interfaces. You can enable the feature flag
`abi_stable` (disabled by default), then the struct `FfiFuture` and friends would derive
`abi_stable::StableAbi`.

[`abi-stable`]: https://github.com/rodrimati1992/abi_stable_crates/

## [`cbindgen`] support

This crate includes support for [`cbindgen`]. You can generate the C/C++ bindings with:

```
$ cbindgen --config cbindgen.toml --output async_ffi.h
```

[`cbindgen`]: https://github.com/eqrion/cbindgen

#### License

MIT Licensed.
