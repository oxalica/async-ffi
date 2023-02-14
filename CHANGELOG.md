# Unreleased

- [minor] Bump dependency `abi_stable` to 0.11.
- [fix] Unignore tests for `miri` since they work now.

# 0.4.0

- [minor] Add an optional feature `abi_stable` to derive `StableAbi`.
  Some internal structs are tweaked to fit the requirement of `StableAbi`,
  but the interface C ABI is unchanged.
- [fix] Tweak crate descriptions.
- [fix] Ignore tests using `tokio` on `miri` interpreter.

# 0.3.1

- [fix] Abort when panicking across the FFI boundary in corner cases. (#8)

  `Future::drop`, panic payload from `Future::poll`, all `Waker` vtable functions `Waker::*` are
  are now wrapped in `std::panic::catch_unwind`. An `abort` will be emitted when panic occurs,
  since these functions are infallible and doesn't have sane value to return when panicking.
  A short message would be printed to stderr before `abort`.

- [fix] `FfiContext::with_context` is actually safe.

# 0.3.0

- [major] Introduce a Poll variant `Panicked` which returns when `Future::poll` panicked in order to
  propagate panic to the host.
- [minor] Public `FfiPoll` and `FfiContext`.

# 0.2.1
