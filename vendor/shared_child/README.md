# shared_child.rs [![Actions Status](https://github.com/oconnor663/shared_child.rs/workflows/tests/badge.svg)](https://github.com/oconnor663/shared_child.rs/actions) [![crates.io](https://img.shields.io/crates/v/shared_child.svg)](https://crates.io/crates/shared_child) [![docs.rs](https://docs.rs/shared_child/badge.svg)](https://docs.rs/shared_child)

A library for awaiting and killing child processes from multiple threads.

- [Docs](https://docs.rs/shared_child)
- [Crate](https://crates.io/crates/shared_child)
- [Repo](https://github.com/oconnor663/shared_child.rs)

The
[`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html)
type in the standard library provides
[`wait`](https://doc.rust-lang.org/std/process/struct.Child.html#method.wait)
and
[`kill`](https://doc.rust-lang.org/std/process/struct.Child.html#method.kill)
methods that take `&mut self`, making it impossible to kill a child process
while another thread is waiting on it. That design works around a race
condition in Unix's `waitpid` function, where a PID might get reused as soon
as the wait returns, so a signal sent around the same time could
accidentally get delivered to the wrong process.

However with the newer POSIX `waitid` function, we can wait on a child
without freeing its PID for reuse. That makes it safe to send signals
concurrently. Windows has actually always supported this, by preventing PID
reuse while there are still open handles to a child process. This library
wraps `std::process::Child` for concurrent use, backed by these APIs.

Compatibility note: The `libc` crate doesn't currently support `waitid` on
NetBSD or OpenBSD, or on older versions of OSX. There [might also
be](https://bugs.python.org/msg167016) some version of OSX where the
`waitid` function exists but is broken. We can add a "best effort"
workaround using `waitpid` for these platforms as we run into them. Please
[file an issue](https://github.com/oconnor663/shared_child.rs/issues/new) if
you hit this.

## Example

```rust
use shared_child::SharedChild;
use std::process::Command;
use std::sync::Arc;

// Spawn a child that will just sleep for a long time,
// and put it in an Arc to share between threads.
let mut command = Command::new("python");
command.arg("-c").arg("import time; time.sleep(1000000000)");
let shared_child = SharedChild::spawn(&mut command).unwrap();
let child_arc = Arc::new(shared_child);

// On another thread, wait on the child process.
let child_arc_clone = child_arc.clone();
let thread = std::thread::spawn(move || {
    child_arc_clone.wait().unwrap()
});

// While the other thread is waiting, kill the child process.
// This wouldn't be possible with e.g. Arc<Mutex<Child>> from
// the standard library, because the waiting thread would be
// holding the mutex.
child_arc.kill().unwrap();

// Join the waiting thread and get the exit status.
let exit_status = thread.join().unwrap();
assert!(!exit_status.success());
```
