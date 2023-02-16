# async-ffi: FFI-compatible `Future`s

[![crates.io](https://img.shields.io/crates/v/async-ffi)](https://crates.io/crates/async-ffi)
[![docs.rs](https://img.shields.io/docsrs/async-ffi)][docs]
[![CI](https://github.com/oxalica/async-ffi/actions/workflows/ci.yaml/badge.svg)](https://github.com/oxalica/async-ffi/actions/workflows/ci.yaml)

Convert your Rust `Future`s into a FFI-compatible struct without relying unstable Rust ABI and struct layout.
Easily provide async functions in dynamic library maybe compiled with different Rust than the invoker.

See [documentation][docs] for more details.

See [`link_tests`](link_tests) directory for cross-linking examples.

[docs]: https://docs.rs/async-ffi

#### License

MIT Licensed.
