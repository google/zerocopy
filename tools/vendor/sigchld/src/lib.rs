//! # `sigchld` [![Actions Status](https://github.com/oconnor663/sigchld.rs/workflows/tests/badge.svg)](https://github.com/oconnor663/sigchld.rs/actions) [![crates.io](https://img.shields.io/crates/v/sigchld.svg)](https://crates.io/crates/sigchld) [![docs.rs](https://docs.rs/sigchld/badge.svg)](https://docs.rs/sigchld)
//!
//! This crate is a low-level building block for child process management. Unix doesn't provide a
//! portable API for waiting for a child process to exit _with a timeout_. (Linux has `pidfd`, but
//! there's no equivalent on e.g. macOS.) The next best thing is waiting for the `SIGCHLD` signal,
//! but Unix signal handling is complicated and error-prone. This crate implements `SIGCHLD`
//! handling using [`signal_hook`] internally, for compatibility with other Rust signal handling
//! libraries. It allows any number of threads to wait for `SIGCHLD` with an optional timeout.
//!
//! Note that `SIGCHLD` indicates that _any_ child process has exited, but there's no reliable way
//! to know _which_ child it was. You generally need to [poll your child process][try_wait] in a
//! loop, and wait again if it hasn't exited yet. This is still a bit error-prone, and most
//! applications will prefer a higher-level API that does this loop internally, like
//! [`shared_child`](https://docs.rs/shared_child) or [`duct`](https://docs.rs/duct).
//!
//! This crate only supports Unix and doesn't build on Windows. Portable callers need to put this
//! crate in the `[target.'cfg(unix)'.dependencies]` section of their `Cargo.toml` and only use it
//! inside of `#[cfg(unix)]` blocks or similar.
//!
//! # Example
//!
//! ```rust
//! # fn main() -> std::io::Result<()> {
//! # use std::time::Duration;
//! let mut waiter = sigchld::Waiter::new()?;
//! // If SIGCHLD arrives after this point, the Waiter will buffer it.
//! let mut child = std::process::Command::new("sleep").arg("1").spawn()?;
//! // Block until *any* child exits. See also `wait_timeout` and `wait_deadline`.
//! waiter.wait()?;
//! // There's only one child process in this example, so we know that it exited. But in general
//! // we might not know which child woke us up, and in that case we'd need to wait and check in a
//! // loop. See the Waiter examples.
//! assert!(child.try_wait()?.is_some(), "sleep has exited");
//! # Ok(())
//! # }
//! ```
//!
//! [`signal_hook`]: https://docs.rs/signal-hook
//! [try_wait]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
//! [`wait_timeout`]: https://docs.rs/shared_child/latest/shared_child/struct.SharedChild.html#method.wait_timeout
//! [`wait_deadline`]: https://docs.rs/shared_child/latest/shared_child/struct.SharedChild.html#method.wait_deadline

#[cfg(not(unix))]
compile_error!(
    "This crate is Unix-only. Put it in [target.'cfg(unix)'.dependencies] in Cargo.toml."
);

use std::io::{self, ErrorKind, Read};
use std::os::raw::c_int;
use std::os::unix::io::AsRawFd;
use std::time::{Duration, Instant};

// `os_pipe` predates `std::io::pipe`, and they have almost the exact same API. Taking the
// dependency reduces the MSRV from 1.87 to 1.63 (inherited from `libc`).
#[cfg(feature = "os_pipe")]
use os_pipe::{pipe, PipeReader};
#[cfg(not(feature = "os_pipe"))]
use std::io::{pipe, PipeReader};

// Use anyhow errors in testing, for backtraces.
#[cfg(test)]
type Result<T> = anyhow::Result<T>;
#[cfg(not(test))]
type Result<T> = io::Result<T>;

/// An object that buffers `SIGCHLD` signals so that you can wait on them reliably.
///
/// `Waiter` can't tell you _which_ process woke you up, so you usually need to wait in a loop and
/// [poll your `Child`][try_wait] each time through. One way to make sure you don't miss a signal
/// (and potentially wait forever) is to create a `Waiter` before you spawn your child process,
/// like this:
///
/// ```
/// # use std::io;
/// # fn main() -> io::Result<()> {
/// let mut waiter = sigchld::Waiter::new()?;
/// // Any SIGCHLD after this point will be buffered by the Waiter.
/// let mut child = std::process::Command::new("sleep").arg("1").spawn()?;
/// loop {
///     waiter.wait()?;
///     // *Some* child has exited. Check whether it was our child.
///     if child.try_wait()?.is_some() {
///         break;
///     }
/// }
/// // Our child has exited.
/// # Ok(())
/// # }
/// ```
///
/// If you create a `Waiter` after your child is already running, then you need to poll the child
/// at least once before you wait:
///
/// ```
/// # use std::io;
/// # fn main() -> io::Result<()> {
/// let mut child = std::process::Command::new("sleep").arg("1").spawn()?;
/// // If SIGCHLD arrives here, before the Waiter is created, we could miss it.
/// let mut waiter = sigchld::Waiter::new()?;
/// while child.try_wait()?.is_none() {
///     // Now we know the child didn't exit before we created the Waiter.
///     waiter.wait()?;
/// }
/// // Our child has exited.
/// # Ok(())
/// # }
/// ```
///
/// The following order of operations is broken. You could miss `SIGCHLD` and wait forever:
///
/// <div class="warning">
///
/// ```no_run
/// # use std::io;
/// # fn main() -> io::Result<()> {
/// let mut child = std::process::Command::new("sleep").arg("1").spawn()?;
/// // If SIGCHLD arrives now, before the Waiter is created, we could miss it.
/// let mut waiter = sigchld::Waiter::new()?;
/// // OOPS: If we missed SIGCHLD, we'll wait forever.
/// waiter.wait()?;
/// # Ok(())
/// # }
/// ```
///
/// </div>
///
/// Most applications will prefer higher-level APIs like
/// [`shared_child`](https://docs.rs/shared_child) or [`duct`](https://docs.rs/duct), where you
/// don't have to worry about this sort of mistake. This crate is intended more as a building block
/// for those APIs.
///
/// [try_wait]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
#[derive(Debug)]
pub struct Waiter {
    reader: PipeReader,
    sig_id: signal_hook::SigId,
}

impl Waiter {
    /// Create a `Waiter`.
    ///
    /// Any `SIGCHLD` signals that arrive after a `Waiter` is created, but before a call to
    /// [`wait`](Self::wait), [`wait_timeout`](Self::wait_timeout), or
    /// [`wait_deadline`](Self::wait_deadline), will be buffered. In that case the next call to one
    /// of those methods will return immediately. Note that each wait clears the entire buffer, so
    /// a single wakeup could indicate that multiple signals arrived. In other words, signals can
    /// be "coalesced".
    pub fn new() -> Result<Self> {
        let (reader, writer) = pipe()?;
        set_nonblocking(&reader)?;
        set_nonblocking(&writer)?;
        let sig_id = signal_hook::low_level::pipe::register(libc::SIGCHLD, writer)?;
        Ok(Self { reader, sig_id })
    }

    /// Block the current thread until any `SIGCHLD` signal arrives.
    ///
    /// If any `SIGCHLD` signals have arrived since the `Waiter` was created, this function will
    /// return immediately. This avoids a race condition where the child exits right after you call
    /// [`Child::try_wait`] but right before you call this function.
    ///
    /// This function does not reap any exited children. Child process cleanup is only done by
    /// [`Child::wait`] or [`Child::try_wait`].
    ///
    /// This function is not currently susceptible to "spurious wakeups" (i.e. returning early for
    /// no reason), but this property isn't guaranteed, and future versions might be. Getting woken
    /// up early by an unrelated child process exiting (e.g. one spawned by some unknown library
    /// code running on another thread) is similar to a spurious wakeup, and you might need to be
    /// defensive and wait in a loop either way.
    ///
    /// [`Child::wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.wait
    /// [`Child::try_wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
    pub fn wait(&mut self) -> Result<()> {
        let signaled = self.wait_inner(None)?;
        debug_assert!(signaled, "timeout shouldn't be possible");
        Ok(())
    }

    /// Block the current thread until either any `SIGCHLD` signal arrives or a timeout passes.
    /// Return `true` if a signal arrived before the timeout.
    ///
    /// If any `SIGCHLD` signals have arrived since the `Waiter` was created, this function will
    /// return immediately. This avoids a race condition where the child exits right after you call
    /// [`Child::try_wait`] but right before you call this function.
    ///
    /// This function does not reap any exited children. Child process cleanup is only done by
    /// [`Child::wait`] or [`Child::try_wait`].
    ///
    /// This function is not currently susceptible to "spurious wakeups" (i.e. returning early for
    /// no reason), but this property isn't guaranteed, and future versions might be. Getting woken
    /// up early by an unrelated child process exiting (e.g. one spawned by some unknown library
    /// code running on another thread) is similar to a spurious wakeup, and you might need to be
    /// defensive and wait in a loop either way.
    ///
    /// [`Child::wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.wait
    /// [`Child::try_wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
    pub fn wait_timeout(&mut self, timeout: Duration) -> Result<bool> {
        let deadline = Instant::now() + timeout;
        self.wait_inner(Some(deadline))
    }

    /// Block the current thread until either any `SIGCHLD` signal arrives or a deadline passes.
    /// Return `true` if a signal arrived before the deadline.
    ///
    /// If any `SIGCHLD` signals have arrived since the `Waiter` was created, this function will
    /// return immediately. This avoids a race condition where the child exits right after you call
    /// [`Child::try_wait`] but right before you call this function.
    ///
    /// This function does not reap any exited children. Child process cleanup is only done by
    /// [`Child::wait`] or [`Child::try_wait`].
    ///
    /// This function is not currently susceptible to "spurious wakeups" (i.e. returning early for
    /// no reason), but this property isn't guaranteed, and future versions might be. Getting woken
    /// up early by an unrelated child process exiting (e.g. one spawned by some unknown library
    /// code running on another thread) is similar to a spurious wakeup, and you might need to be
    /// defensive and wait in a loop either way.
    ///
    /// [`Child::wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.wait
    /// [`Child::try_wait`]: https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait
    pub fn wait_deadline(&mut self, deadline: Instant) -> Result<bool> {
        self.wait_inner(Some(deadline))
    }

    fn wait_inner(&mut self, maybe_deadline: Option<Instant>) -> Result<bool> {
        // Loop to handle spurious wakeups from poll().
        loop {
            // Read the pipe until EWOULDBLOCK. This could take more than one read.
            let mut buf = [0u8; 1024];
            let mut signaled = false;
            loop {
                match self.reader.read(&mut buf) {
                    Ok(0) => unreachable!("this pipe should never close"),
                    Ok(_) => signaled = true,
                    Err(e) if e.kind() == ErrorKind::WouldBlock => break,
                    // EINTR shouldn't be possible for a nonblocking read.
                    #[allow(clippy::useless_conversion)]
                    Err(e) => return Err(e.into()),
                }
            }
            // If we were signaled, return true.
            if signaled {
                return Ok(true);
            }
            // If the deadline has passed, return false.
            if let Some(deadline) = maybe_deadline {
                if Instant::now() > deadline {
                    return Ok(false);
                }
            }
            // Use poll() to wait until either the deadline passes or the pipe is readable.
            let mut poll_fd = libc::pollfd {
                fd: self.reader.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            let timeout_ms: c_int = if let Some(deadline) = maybe_deadline {
                let timeout = deadline.saturating_duration_since(Instant::now());
                // Convert to milliseconds, rounding *up*. (That way we don't repeatedly sleep for
                // 0ms when we're close to the timeout.)
                (timeout.as_nanos().saturating_add(999_999) / 1_000_000)
                    .try_into()
                    .unwrap_or(c_int::MAX)
            } else {
                -1 // infinite timeout
            };
            let poll_return_code = unsafe {
                libc::poll(
                    &mut poll_fd, // an "array" of one
                    1,            // the "array" length
                    timeout_ms,
                )
            };
            if poll_return_code < 0 {
                // EINTR is expected here, and the delivery of SIGCHLD usually causes it.
                let last_error = io::Error::last_os_error();
                if last_error.kind() != ErrorKind::Interrupted {
                    #[allow(clippy::useless_conversion)]
                    return Err(last_error.into());
                }
            }
            // Go back to the top of the loop and try to read again.
        }
    }
}

impl Drop for Waiter {
    fn drop(&mut self) {
        let existed = signal_hook::low_level::unregister(self.sig_id);
        debug_assert!(existed, "should've existed");
    }
}

// The standard library doesn't expose set_nonblocking for pipes. Do it the old-fashioned way.
fn set_nonblocking(fd: &impl AsRawFd) -> Result<()> {
    unsafe {
        let return_code = libc::fcntl(fd.as_raw_fd(), libc::F_SETFL, libc::O_NONBLOCK);
        if return_code == -1 {
            #[allow(clippy::useless_conversion)]
            Err(io::Error::last_os_error().into())
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use duct::cmd;
    use std::sync::{Arc, Mutex, MutexGuard};
    use std::time::{Duration, Instant};

    // We need to make sure only one test runs at a time, because these waits are global, and
    // they'll confuse each other. Use a parking_lot mutex so that it doesn't get poisoned.
    //
    // XXX: These tests don't wait in a loop, because if there are bugs here that cause early
    // wakeups, I'd rather the tests fail than hide the bug. I expect these tests will "randomly"
    // fail under certain circumstances, and that's worth it to me to catch more bugs. But real
    // callers should wait in a loop so that they don't randomly fail.
    static ONE_TEST_AT_A_TIME: Mutex<()> = Mutex::new(());

    fn lock_no_poison<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
        match mutex.lock() {
            Ok(guard) => guard,
            Err(e) => e.into_inner(),
        }
    }

    #[track_caller]
    fn assert_approx_eq(dur1: Duration, dur2: Duration) {
        const CLOSE_ENOUGH: f64 = 0.1; // 10%
        let lower_bound = 1.0 - CLOSE_ENOUGH;
        let upper_bound = 1.0 + CLOSE_ENOUGH;
        let ratio = dur1.as_secs_f64() / dur2.as_secs_f64();
        assert!(
            lower_bound < ratio && ratio < upper_bound,
            "{dur1:?} and {dur2:?} are not close enough",
        );
    }

    #[test]
    fn test_wait() -> Result<()> {
        let _test_guard = lock_no_poison(&ONE_TEST_AT_A_TIME); // see comment on the lock
        let start = Instant::now();

        let mut waiter = Waiter::new()?;
        cmd!("sleep", "0.25").start()?;
        waiter.wait()?;
        let dur = Instant::now() - start;
        assert_approx_eq(Duration::from_millis(250), dur);

        Ok(())
    }

    #[test]
    fn test_wait_deadline() -> Result<()> {
        let _test_guard = lock_no_poison(&ONE_TEST_AT_A_TIME); // see comment on the lock
        let start = Instant::now();

        let timeout = Duration::from_millis(500);
        let mut waiter = Waiter::new()?;
        cmd!("sleep", "0.25").start()?;
        // This first wait should return true.
        let signaled = waiter.wait_deadline(Instant::now() + timeout)?;
        let dur = Instant::now() - start;
        assert_approx_eq(Duration::from_millis(250), dur);
        assert!(signaled);

        // This second wait should time out and return false.
        let mut waiter2 = Waiter::new()?;
        let signaled2 = waiter2.wait_deadline(Instant::now() + timeout)?;
        let dur2 = Instant::now() - start;
        assert_approx_eq(Duration::from_millis(750), dur2);
        assert!(!signaled2);

        Ok(())
    }

    #[test]
    fn test_wait_timeout() -> Result<()> {
        let _test_guard = lock_no_poison(&ONE_TEST_AT_A_TIME); // see comment on the lock
        let start = Instant::now();

        let timeout = Duration::from_millis(500);
        let mut waiter = Waiter::new()?;
        cmd!("sleep", "0.25").start()?;
        // This first wait should return true.
        let signaled = waiter.wait_timeout(timeout)?;
        let dur = Instant::now() - start;
        assert_approx_eq(Duration::from_millis(250), dur);
        assert!(signaled);

        // This second wait should time out and return false.
        let mut waiter2 = Waiter::new()?;
        let signaled2 = waiter2.wait_timeout(timeout)?;
        let dur2 = Instant::now() - start;
        assert_approx_eq(Duration::from_millis(750), dur2);
        assert!(!signaled2);

        Ok(())
    }

    #[test]
    fn test_wait_many_threads() -> Result<()> {
        let _test_guard = lock_no_poison(&ONE_TEST_AT_A_TIME); // see comment on the lock
        let start = Instant::now();

        let handle = Arc::new(cmd!("sleep", "1").start()?);
        let mut wait_threads = Vec::new();
        let mut short_timeout_threads = Vec::new();
        let mut long_timeout_threads = Vec::new();
        for _ in 0..3 {
            let handle_clone = handle.clone();
            let mut waiter = Waiter::new()?;
            wait_threads.push(std::thread::spawn(move || -> Result<Duration> {
                waiter.wait()?;
                let dur = Instant::now() - start;
                assert!(handle_clone.try_wait()?.is_some(), "should've exited");
                Ok(dur)
            }));
            let handle_clone = handle.clone();
            let mut waiter = Waiter::new()?;
            short_timeout_threads.push(std::thread::spawn(move || -> Result<bool> {
                let signaled = waiter.wait_timeout(Duration::from_millis(500))?;
                assert!(handle_clone.try_wait()?.is_none(), "shouldn't have exited");
                Ok(signaled)
            }));
            let handle_clone = handle.clone();
            let mut waiter = Waiter::new()?;
            long_timeout_threads.push(std::thread::spawn(move || -> Result<bool> {
                let signaled = waiter.wait_timeout(Duration::from_millis(1500))?;
                assert!(handle_clone.try_wait()?.is_some(), "should've exited");
                Ok(signaled)
            }));
        }
        for thread in wait_threads {
            let dur = thread.join().unwrap()?;
            assert_approx_eq(Duration::from_millis(1000), dur);
        }
        for thread in short_timeout_threads {
            assert!(!thread.join().unwrap()?, "should not be signaled");
        }
        for thread in long_timeout_threads {
            assert!(thread.join().unwrap()?, "should be signaled");
        }

        Ok(())
    }
}
