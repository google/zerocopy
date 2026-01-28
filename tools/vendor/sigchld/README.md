## `sigchld` [![Actions Status](https://github.com/oconnor663/sigchld.rs/workflows/tests/badge.svg)](https://github.com/oconnor663/sigchld.rs/actions) [![crates.io](https://img.shields.io/crates/v/sigchld.svg)](https://crates.io/crates/sigchld) [![docs.rs](https://docs.rs/sigchld/badge.svg)](https://docs.rs/sigchld)

This crate is a low-level building block for child process management. Unix doesn't provide a
portable API for waiting for a child process to exit _with a timeout_. (Linux has `pidfd`, but
there's no equivalent on e.g. macOS.) The next best thing is waiting for the `SIGCHLD` signal,
but Unix signal handling is complicated and error-prone. This crate implements `SIGCHLD`
handling using [`signal_hook`] internally, for compatibility with other Rust signal handling
libraries. It allows any number of threads to wait for `SIGCHLD` with an optional timeout.

Note that `SIGCHLD` indicates that _any_ child process has exited, but there's no reliable way
to know _which_ child it was. You generally need to [poll your child process][try_wait] in a
loop, and wait again if it hasn't exited yet. This is still a bit error-prone, and most
applications will prefer a higher-level API that does this loop internally, like
[`shared_child`](https://docs.rs/shared_child) or [`duct`](https://docs.rs/duct).

This crate only supports Unix and doesn't build on Windows. Portable callers need to put this
crate in the `[target.'cfg(unix)'.dependencies]` section of their `Cargo.toml` and only use it
inside of `#[cfg(unix)]` blocks or similar.

## Example

```rust
let mut waiter = sigchld::Waiter::new()?;
// If SIGCHLD arrives after this point, the Waiter will buffer it.
let mut child = std::process::Command::new("sleep").arg("1").spawn()?;
// Block until *any* child exits. See also `wait_timeout` and `wait_deadline`.
waiter.wait()?;
// There's only one child process in this example, so we know that it exited. But in general
// we might not know which child woke us up, and in that case we'd need to wait and check in a
// loop. See the Waiter examples.
assert!(child.try_wait()?.is_some(), "sleep has exited");
```

[`signal_hook`]: https://docs.rs/signal-hook
[try_wait]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
[`wait_timeout`]: https://docs.rs/shared_child/latest/shared_child/struct.SharedChild.html#method.wait_timeout
[`wait_deadline`]: https://docs.rs/shared_child/latest/shared_child/struct.SharedChild.html#method.wait_deadline
