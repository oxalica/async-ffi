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
