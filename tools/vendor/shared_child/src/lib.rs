//! A library for awaiting and killing child processes from multiple threads.
//!
//! - [Docs](https://docs.rs/shared_child)
//! - [Crate](https://crates.io/crates/shared_child)
//! - [Repo](https://github.com/oconnor663/shared_child.rs)
//!
//! The
//! [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html)
//! type in the standard library provides
//! [`wait`](https://doc.rust-lang.org/std/process/struct.Child.html#method.wait)
//! and
//! [`kill`](https://doc.rust-lang.org/std/process/struct.Child.html#method.kill)
//! methods that take `&mut self`, making it impossible to kill a child process
//! while another thread is waiting on it. That design works around a race
//! condition in Unix's `waitpid` function, where a PID might get reused as soon
//! as the wait returns, so a signal sent around the same time could
//! accidentally get delivered to the wrong process.
//!
//! However with the newer POSIX `waitid` function, we can wait on a child
//! without freeing its PID for reuse. That makes it safe to send signals
//! concurrently. Windows has actually always supported this, by preventing PID
//! reuse while there are still open handles to a child process. This library
//! wraps `std::process::Child` for concurrent use, backed by these APIs.
//!
//! Compatibility note: The `libc` crate doesn't currently support `waitid` on
//! NetBSD or OpenBSD, or on older versions of OSX. There [might also
//! be](https://bugs.python.org/msg167016) some version of OSX where the
//! `waitid` function exists but is broken. We can add a "best effort"
//! workaround using `waitpid` for these platforms as we run into them. Please
//! [file an issue](https://github.com/oconnor663/shared_child.rs/issues/new) if
//! you hit this.
//!
//! # Example
//!
//! ```rust
//! use shared_child::SharedChild;
//! use std::process::Command;
//! use std::sync::Arc;
//!
//! // Spawn a child that will just sleep for a long time,
//! // and put it in an Arc to share between threads.
//! let mut command = Command::new("python");
//! command.arg("-c").arg("import time; time.sleep(1000000000)");
//! let shared_child = SharedChild::spawn(&mut command).unwrap();
//! let child_arc = Arc::new(shared_child);
//!
//! // On another thread, wait on the child process.
//! let child_arc_clone = child_arc.clone();
//! let thread = std::thread::spawn(move || {
//!     child_arc_clone.wait().unwrap()
//! });
//!
//! // While the other thread is waiting, kill the child process.
//! // This wouldn't be possible with e.g. Arc<Mutex<Child>> from
//! // the standard library, because the waiting thread would be
//! // holding the mutex.
//! child_arc.kill().unwrap();
//!
//! // Join the waiting thread and get the exit status.
//! let exit_status = thread.join().unwrap();
//! assert!(!exit_status.success());
//! ```

use std::io;
use std::process::{Child, ChildStderr, ChildStdin, ChildStdout, Command, ExitStatus};
use std::sync::{Condvar, Mutex, MutexGuard};
#[cfg(feature = "timeout")]
use std::time::{Duration, Instant};

mod sys;

// Publish the Unix-only SharedChildExt trait.
#[cfg(unix)]
pub mod unix;

#[derive(Debug)]
enum ChildState {
    NotWaiting,
    Waiting,
    Exited(ExitStatus),
}

use crate::ChildState::{Exited, NotWaiting, Waiting};

#[derive(Debug)]
struct SharedChildInner {
    child: Child,
    state: ChildState,
}

#[derive(Debug)]
pub struct SharedChild {
    inner: Mutex<SharedChildInner>,
    condvar: Condvar,
}

impl SharedChild {
    /// Spawn a new `SharedChild` from a
    /// [`std::process::Command`](https://doc.rust-lang.org/std/process/struct.Command.html).
    pub fn spawn(command: &mut Command) -> io::Result<Self> {
        Ok(SharedChild {
            inner: Mutex::new(SharedChildInner {
                child: command.spawn()?,
                state: NotWaiting,
            }),
            condvar: Condvar::new(),
        })
    }

    /// Construct a new `SharedChild` from an already spawned
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html).
    ///
    /// This constructor needs to know whether `child` has already been waited on, and the only way
    /// to find that out is to call
    /// [`Child::try_wait`](https://doc.rust-lang.org/std/process/struct.Child.html#method.try_wait)
    /// internally. If the child process is currently a zombie, that call will clean it up as a
    /// side effect. The [`SharedChild::spawn`] constructor doesn't need to do this.
    pub fn new(mut child: Child) -> io::Result<Self> {
        let state = if let Some(exit_status) = child.try_wait()? {
            Exited(exit_status)
        } else {
            NotWaiting
        };
        Ok(SharedChild {
            inner: Mutex::new(SharedChildInner { child, state }),
            condvar: Condvar::new(),
        })
    }

    /// Return the child process ID.
    pub fn id(&self) -> u32 {
        self.inner.lock().unwrap().child.id()
    }

    /// Wait for the child to exit, blocking the current thread, and return its
    /// exit status.
    pub fn wait(&self) -> io::Result<ExitStatus> {
        // Start by taking the inner lock, but note that we need to release it before waiting, or
        // else we'd block .try_wait(), .wait_deadline(), and .kill().
        let mut inner_guard = self.inner.lock().unwrap();
        loop {
            match inner_guard.state {
                // The child has already been reaped. Return its saved exit status.
                Exited(exit_status) => return Ok(exit_status),
                // There is another blocking waiter. Sleep until it signals the condvar. Spurious
                // wakeups are acceptable here.
                Waiting => inner_guard = self.condvar.wait(inner_guard).unwrap(),
                // There are no other blocking waiters. Proceed to the blocking wait.
                NotWaiting => break,
            }
        }

        // We are the blocking waiter. Set the state to Waiting and release the lock before
        // blocking. After this, we must reset the state and notify the condvar before returning.
        inner_guard.state = Waiting;
        let handle = sys::get_handle(&inner_guard.child);
        drop(inner_guard);

        // Do the blocking wait.
        let wait_result = sys::wait_noreap(handle);

        // Before checking the result, reacquire the lock, leave the Waiting state, and notify the
        // condvar. If the child did exit, we'll set the Exited state before releasing the lock
        // again, and no other threads will observe NotWaiting.
        inner_guard = self.inner.lock().unwrap();
        inner_guard.state = NotWaiting;
        self.condvar.notify_all();

        wait_result?;
        // The child has exited. Reap it with std::process::Child::wait. The state was Waiting when
        // we re-acquired the lock, so there are no other threads in blocking waits (other waiters
        // would be sleeping on the condvar), and it's safe to free the child PID.
        let exit_status = inner_guard.child.wait()?;
        inner_guard.state = Exited(exit_status);
        Ok(exit_status)
    }

    /// Wait for the child to exit, blocking the current thread, and return its exit status. Or if
    /// the timeout passes before then, return `Ok(None)`.
    ///
    /// This polls the child at least once, and if the child has already exited it will return
    /// `Ok(Some(_))` even if the timeout is zero.
    #[cfg(feature = "timeout")]
    pub fn wait_timeout(&self, timeout: Duration) -> io::Result<Option<ExitStatus>> {
        let deadline = std::time::Instant::now() + timeout;
        self.wait_deadline(deadline)
    }

    /// Wait for the child to exit, blocking the current thread, and return its exit status. Or if
    /// the deadline passes before then, return `Ok(None)`.
    ///
    /// This polls the child at least once, and if the child has already exited it will return
    /// `Ok(Some(_))` even if the deadline is in the past.
    #[cfg(feature = "timeout")]
    pub fn wait_deadline(&self, deadline: Instant) -> io::Result<Option<ExitStatus>> {
        // Start by taking the inner lock, but note that we need to release it before waiting, or
        // else we'd block .try_wait(), .kill(), and other calls to .wait_deadline().
        let mut inner_guard = self.inner.lock().unwrap();
        loop {
            match inner_guard.state {
                // The child has already been reaped. Return its saved exit status.
                Exited(exit_status) => return Ok(Some(exit_status)),
                // The deadline has passed. Poll the child on the way out, to make sure we always
                // poll at least once.
                _ if deadline < Instant::now() => {
                    return self.try_wait_inner(inner_guard);
                }
                // There is another blocking waiter. Sleep until it signals the condvar or the
                // deadline passes. Spurious wakeups are acceptable here.
                Waiting => {
                    let timeout = deadline.saturating_duration_since(Instant::now());
                    inner_guard = self.condvar.wait_timeout(inner_guard, timeout).unwrap().0;
                }
                // There are no other blocking waiters. Proceed to the blocking wait.
                NotWaiting => break,
            }
        }

        // We are the blocking waiter. Set the state to Waiting and release the lock before
        // blocking. After this, we must reset the state and notify the condvar before returning.
        inner_guard.state = Waiting;
        let handle = sys::get_handle(&inner_guard.child);
        drop(inner_guard);

        // Do the blocking wait.
        let wait_result = sys::wait_deadline_noreap(handle, deadline);

        // Before checking the result, reacquire the lock, leave the Waiting state, and notify the
        // condvar. If the child did exit, we'll set the Exited state before releasing the lock
        // again, and no other threads will observe NotWaiting.
        inner_guard = self.inner.lock().unwrap();
        inner_guard.state = NotWaiting;
        self.condvar.notify_all();

        let exited = wait_result?;
        if exited {
            // The child has exited. Reap it with std::process::Child::wait. The state was Waiting
            // when we re-acquired the lock, so there are no other threads in blocking waits (other
            // waiters would be sleeping on the condvar), and it's safe to free the child PID.
            let exit_status = inner_guard.child.wait()?;
            inner_guard.state = Exited(exit_status);
            Ok(Some(exit_status))
        } else {
            Ok(None)
        }
    }

    /// Return the child's exit status if it has already exited. If the child is still running,
    /// return `Ok(None)`.
    pub fn try_wait(&self) -> io::Result<Option<ExitStatus>> {
        // Taking this lock will not block for long, because .wait() and .wait_deadline() don't
        // hold it while waiting.
        let inner_guard = self.inner.lock().unwrap();
        self.try_wait_inner(inner_guard)
    }

    fn try_wait_inner(
        &self,
        mut inner_guard: MutexGuard<SharedChildInner>,
    ) -> io::Result<Option<ExitStatus>> {
        match inner_guard.state {
            // The child has already been reaped. Return its saved exit status.
            Exited(exit_status) => Ok(Some(exit_status)),
            // There are no other blocking waiters, so it's safe to (potentially) reap the child
            // and free the child PID with std::process::Child::try_wait.
            NotWaiting => {
                if let Some(status) = inner_guard.child.try_wait()? {
                    inner_guard.state = Exited(status);
                    Ok(Some(status))
                } else {
                    Ok(None)
                }
            }
            // There is another blocking waiter, which might still be in libc::waitid. Poll the
            // child to see whether it's exited, without reaping it. This library used to take the
            // `Waiting` status as a proxy for "not exited yet", but we no longer do that for two
            // reasons:
            // 1. That risks a subtle race condition. If a wait()ing thread sets the Waiting status
            //    and releases the child lock without first polling the child, a call to try_wait()
            //    from another thread at the exact same time might incorrectly assume the child
            //    hasn't exited yet, even if in fact it exited long ago. Polling before releasing
            //    the lock avoids this, but it's easy to forget. Note that this is currently a bug
            //    in the Python standard library: https://github.com/python/cpython/issues/127050
            // 2. If try_wait() is racing against child exit, it's possible to have a case where
            //    polling *would've* returned true, but we don't poll and instead return false. We
            //    used to say we didn't care about that, because if you're racing exit then you
            //    shouldn't really care answer you get. But that's not entirely fair, because you
            //    might be calling try_wait() in response to receiving SIGCHLD, in which case you
            //    *know* the child has exited.  In that case you're not really racing against exit,
            //    but only against the wait() thread. We prefer to guarantee that you'll get true
            //    in that case. (It's arguably more robust to call wait() instead if you *know* the
            //    child has exited, but either should work after SIGCHLD.)
            Waiting => {
                if sys::try_wait_noreap(sys::get_handle(&inner_guard.child))? {
                    // The child has exited, but we can't reap it without conflicting with the
                    // other waiter, so use `.wait()` instead to synchronize with it.
                    drop(inner_guard);
                    let exit_status = self.wait()?;
                    Ok(Some(exit_status))
                } else {
                    Ok(None)
                }
            }
        }
    }

    /// Send a kill signal to the child. On Unix this sends SIGKILL, and you
    /// should call `wait` afterwards to avoid leaving a zombie. If the process
    /// has already been waited on, this returns `Ok(())` and does nothing.
    pub fn kill(&self) -> io::Result<()> {
        // The reason we can do this, but the standard library can't, is that on Unix our
        // SharedChild::wait function uses the newer (i.e. only 20 years old) libc::waitid with the
        // WNOWAIT flag, which lets it wait for the child to exit without reaping it. The actual
        // reaping happens after SharedChild::wait re-acquires the inner lock, which is the same
        // lock we take here, preventing the PID reuse race.
        //
        // Taking this lock won't block, because .wait() and .wait_deadline() don't hold it while
        // blocking. Also we always reap the child process via std::process::Child methods, so this
        // is a safe no-op after we've freed the child PID.
        self.inner.lock().unwrap().child.kill()
    }

    /// Consume the `SharedChild` and return the
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html) it
    /// contains.
    ///
    /// We never reap the child process except by calling
    /// [`std::process::Child`](https://doc.rust-lang.org/std/process/struct.Child.html) methods on
    /// it, so the child object's inner state is correct, even if it was waited on while it was
    /// shared.
    pub fn into_inner(self) -> Child {
        self.inner.into_inner().unwrap().child
    }

    /// Take the child's
    /// [`stdin`](https://doc.rust-lang.org/std/process/struct.Child.html#structfield.stdin)
    /// handle, if any.
    ///
    /// This will only return `Some` the first time it's called, and then only if the `Command`
    /// that created the child was configured with `.stdin(Stdio::piped())`.
    pub fn take_stdin(&self) -> Option<ChildStdin> {
        self.inner.lock().unwrap().child.stdin.take()
    }

    /// Take the child's
    /// [`stdout`](https://doc.rust-lang.org/std/process/struct.Child.html#structfield.stdout)
    /// handle, if any.
    ///
    /// This will only return `Some` the first time it's called, and then only if the `Command`
    /// that created the child was configured with `.stdout(Stdio::piped())`.
    pub fn take_stdout(&self) -> Option<ChildStdout> {
        self.inner.lock().unwrap().child.stdout.take()
    }

    /// Take the child's
    /// [`stderr`](https://doc.rust-lang.org/std/process/struct.Child.html#structfield.stderr)
    /// handle, if any.
    ///
    /// This will only return `Some` the first time it's called, and then only if the `Command`
    /// that created the child was configured with `.stderr(Stdio::piped())`.
    pub fn take_stderr(&self) -> Option<ChildStderr> {
        self.inner.lock().unwrap().child.stderr.take()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;
    use std::process::{Command, Stdio};
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    // Python isn't available on some Unix platforms, e.g. Android, so we need this instead.
    #[cfg(unix)]
    pub fn true_cmd() -> Command {
        Command::new("true")
    }

    #[cfg(not(unix))]
    pub fn true_cmd() -> Command {
        let mut cmd = Command::new("python");
        cmd.arg("-c").arg("");
        cmd
    }

    // Python isn't available on some Unix platforms, e.g. Android, so we need this instead.
    #[cfg(unix)]
    pub fn sleep_cmd(duration: Duration) -> Command {
        let mut cmd = Command::new("sleep");
        cmd.arg(format!("{}", duration.as_secs_f32()));
        cmd
    }

    #[cfg(not(unix))]
    pub fn sleep_cmd(duration: Duration) -> Command {
        let mut cmd = Command::new("python");
        cmd.arg("-c").arg(format!(
            "import time; time.sleep({})",
            duration.as_secs_f32()
        ));
        cmd
    }

    pub fn sleep_forever_cmd() -> Command {
        sleep_cmd(Duration::from_secs(1000000))
    }

    // Python isn't available on some Unix platforms, e.g. Android, so we need this instead.
    #[cfg(unix)]
    pub fn cat_cmd() -> Command {
        Command::new("cat")
    }

    #[cfg(not(unix))]
    pub fn cat_cmd() -> Command {
        let mut cmd = Command::new("python");
        cmd.arg("-c").arg("");
        cmd
    }

    #[test]
    fn test_wait() {
        let child = SharedChild::spawn(&mut true_cmd()).unwrap();
        // Test the id() function while we're at it.
        let id = child.id();
        assert!(id > 0);
        let status = child.wait().unwrap();
        assert_eq!(status.code().unwrap(), 0);
    }

    #[cfg(feature = "timeout")]
    fn exited_but_unawaited_child() -> SharedChild {
        // The `true` command will exit immediately.
        let child = SharedChild::spawn(&mut true_cmd()).unwrap();
        // Wait on the child "out of band", so the SharedChild state is not updated.
        let handle = sys::get_handle(&child.inner.lock().unwrap().child);
        sys::wait_noreap(handle).unwrap();
        // At this point the child has definitely exited, but the SharedChild is still in the
        // NotWaiting state.
        child
    }

    // This test is pretty much copy-pasted as test_wait_deadline below. Copy-paste any future
    // changes too.
    #[test]
    #[cfg(feature = "timeout")]
    fn test_wait_timeout() {
        let exited_child = exited_but_unawaited_child();
        // The first .wait_timeout reaps the child.
        assert!(exited_child
            .wait_timeout(Duration::from_secs(0))
            .expect("no IO error")
            .expect("did not time out")
            .success());
        // The second returns the cached status.
        assert!(exited_child
            .wait_timeout(Duration::from_secs(0))
            .expect("no IO error")
            .expect("did not time out")
            .success());

        // Test two different timeout cases. First, if we're the only waiter...
        let long_child = Arc::new(SharedChild::spawn(&mut sleep_forever_cmd()).unwrap());
        let status = long_child
            .wait_timeout(Duration::from_millis(10))
            .expect("no IO error");
        assert!(status.is_none(), "timed out");
        // And second, if there's another background thread already waiting (this tests the condvar
        // wait loop, which the first case skips)...
        let long_child_clone = Arc::clone(&long_child);
        std::thread::spawn(move || long_child_clone.wait().unwrap());
        // There's no perfect way to make sure that the bg thread has already entered the blocking
        // wait, so just sleep for a moment before waiting. Weird timing here might mean we're not
        // testing what we meant to, but it won't make the test fail.
        std::thread::sleep(Duration::from_millis(10));
        let status = long_child
            .wait_timeout(Duration::from_millis(10))
            .expect("no IO error");
        assert!(status.is_none(), "timed out");

        // Kill and clean up the long_child, mostly just to avoid leaving processes around after
        // the test suite is finished.
        long_child.kill().unwrap();
        long_child
            .wait_timeout(Duration::from_millis(100))
            .expect("no IO error")
            .expect("did not time out");
    }

    // This test is pretty much copy-pasted as test_wait_timeout above. Copy-paste any future
    // changes too.
    #[test]
    #[cfg(feature = "timeout")]
    fn test_wait_deadline() {
        let exited_child = exited_but_unawaited_child();
        // The first .wait_deadline reaps the child.
        assert!(exited_child
            .wait_deadline(Instant::now() + Duration::from_secs(0))
            .expect("no IO error")
            .expect("did not time out")
            .success());
        // The second returns the cached status.
        assert!(exited_child
            .wait_deadline(Instant::now() + Duration::from_secs(0))
            .expect("no IO error")
            .expect("did not time out")
            .success());

        // Test two different timeout cases. First, if we're the only waiter...
        let long_child = Arc::new(SharedChild::spawn(&mut sleep_forever_cmd()).unwrap());
        let status = long_child
            .wait_deadline(Instant::now() + Duration::from_millis(10))
            .expect("no IO error");
        assert!(status.is_none(), "timed out");
        // And second, if there's another background thread already waiting (this tests the condvar
        // wait loop, which the first case skips)...
        let long_child_clone = Arc::clone(&long_child);
        std::thread::spawn(move || long_child_clone.wait().unwrap());
        // There's no perfect way to make sure that the bg thread has already entered the blocking
        // wait, so just sleep for a moment before waiting. Weird timing here might mean we're not
        // testing what we meant to, but it won't make the test fail.
        std::thread::sleep(Duration::from_millis(10));
        let status = long_child
            .wait_deadline(Instant::now() + Duration::from_millis(10))
            .expect("no IO error");
        assert!(status.is_none(), "timed out");

        // Kill and clean up the long_child, mostly just to avoid leaving processes around after
        // the test suite is finished.
        long_child.kill().unwrap();
        long_child
            .wait_deadline(Instant::now() + Duration::from_millis(100))
            .expect("no IO error")
            .expect("did not time out");
    }

    #[test]
    fn test_kill() {
        let child = SharedChild::spawn(&mut sleep_forever_cmd()).unwrap();
        child.kill().unwrap();
        let status = child.wait().unwrap();
        assert!(!status.success());
    }

    #[test]
    fn test_try_wait() {
        let child = SharedChild::spawn(&mut sleep_forever_cmd()).unwrap();
        let maybe_status = child.try_wait().unwrap();
        assert_eq!(maybe_status, None);
        child.kill().unwrap();
        // The child will handle that signal asynchronously, so we check it
        // repeatedly in a busy loop.
        let mut maybe_status = None;
        while maybe_status.is_none() {
            maybe_status = child.try_wait().unwrap();
        }
        assert!(maybe_status.is_some());
        assert!(!maybe_status.unwrap().success());
    }

    #[test]
    fn test_many_waiters() {
        let child = Arc::new(SharedChild::spawn(&mut sleep_forever_cmd()).unwrap());
        let mut threads = Vec::new();
        for _ in 0..10 {
            let clone = child.clone();
            threads.push(std::thread::spawn(move || clone.wait()));
        }
        child.kill().unwrap();
        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }

    #[test]
    fn test_waitid_after_exit_doesnt_hang() {
        // There are ominous reports (https://bugs.python.org/issue10812) of a
        // broken waitid implementation on OSX, which might hang forever if it
        // tries to wait on a child that's already exited.
        let mut child = true_cmd().spawn().unwrap();
        sys::wait_noreap(sys::get_handle(&child)).unwrap();
        // At this point the child has definitely exited. Wait again to test
        // that a second wait doesn't block.
        sys::wait_noreap(sys::get_handle(&child)).unwrap();
        // Clean up the child to avoid leaving a zombie.
        child.wait().unwrap();
    }

    #[test]
    fn test_into_inner_before_wait() {
        let shared_child = SharedChild::spawn(&mut sleep_forever_cmd()).unwrap();
        let mut child = shared_child.into_inner();
        child.kill().unwrap();
        child.wait().unwrap();
    }

    #[test]
    fn test_into_inner_after_wait() {
        // This makes sure the child's inner state is valid. If we used waitpid
        // on the side, the inner child would try to wait again and cause an
        // error.
        let shared_child = SharedChild::spawn(&mut sleep_forever_cmd()).unwrap();
        shared_child.kill().unwrap();
        shared_child.wait().unwrap();
        let mut child = shared_child.into_inner();
        // Wait should succeed. (Note that we also used to test that
        // child.kill() failed here, but its behavior changed in Rust 1.72.)
        child.wait().unwrap();
    }

    #[test]
    fn test_new() -> Result<(), Box<dyn Error>> {
        // Spawn a short-lived child.
        let mut command = cat_cmd();
        command.stdin(Stdio::piped());
        command.stdout(Stdio::null());
        let mut child = command.spawn()?;
        let child_stdin = child.stdin.take().unwrap();

        // Construct a SharedChild from the Child, which has not yet been waited on. The child is
        // blocked on stdin, so we know it hasn't yet exited.
        let mut shared_child = SharedChild::new(child).unwrap();
        assert!(matches!(
            shared_child.inner.lock().unwrap().state,
            NotWaiting,
        ));

        // Now close the child's stdin. This will cause the child to exit.
        drop(child_stdin);

        // Construct more SharedChild objects from the same child, in a loop. Eventually one of
        // them will notice that the child has exited.
        loop {
            shared_child = SharedChild::new(shared_child.into_inner())?;
            if let Exited(status) = shared_child.inner.lock().unwrap().state {
                assert!(status.success());
                return Ok(());
            }
        }
    }

    #[test]
    fn test_takes() -> Result<(), Box<dyn Error>> {
        let mut command = true_cmd();
        command.stdin(Stdio::piped());
        command.stdout(Stdio::piped());
        command.stderr(Stdio::piped());
        let shared_child = SharedChild::spawn(&mut command)?;

        assert!(shared_child.take_stdin().is_some());
        assert!(shared_child.take_stdout().is_some());
        assert!(shared_child.take_stderr().is_some());

        assert!(shared_child.take_stdin().is_none());
        assert!(shared_child.take_stdout().is_none());
        assert!(shared_child.take_stderr().is_none());

        shared_child.wait()?;
        Ok(())
    }

    #[test]
    fn test_wait_try_wait_race() -> Result<(), Box<dyn Error>> {
        // Make sure that .wait() and .try_wait() can't race against each other. The scenario we're
        // worried about is:
        //   1. wait() takes the lock, set the state to Waiting, and releases the lock.
        //   2. try_wait swoops in, takes the lock, sees the Waiting state, and returns Ok(None).
        //   3. wait() resumes, actually calls waitit(), observes the child has exited, retakes the
        //      lock, reaps the child, and sets the state to Exited.
        // A race like this could cause .try_wait() to report that the child hasn't exited, even if
        // in fact the child exited long ago. A subsequent call to .try_wait() would almost
        // certainly report Ok(Some(_)), but the first call is still a bug. The way to prevent the
        // bug is by making .wait() do a non-blocking call to waitid() before releasing the lock.
        //
        // This was a failing test when I first committed it. Most of the time it would fail after
        // a few hundred iterations, but sometimes it took thousands. Default to one second so that
        // the tests don't take too long, but use an env var to configure a really big run in CI.
        let mut test_duration_secs: u64 = 1;
        if let Ok(test_duration_secs_str) = std::env::var("SHARED_CHILD_RACE_TEST_SECONDS") {
            dbg!(&test_duration_secs_str);
            test_duration_secs = test_duration_secs_str.parse().expect("invalid u64");
        }
        let test_duration = Duration::from_secs(test_duration_secs);
        let test_start = Instant::now();
        let mut iterations = 1u64;
        loop {
            // Start a child that will exit immediately.
            let child = SharedChild::spawn(&mut true_cmd())?;
            // Wait for the child to exit, without updating the SharedChild state.
            let handle = sys::get_handle(&child.inner.lock().unwrap().child);
            sys::wait_noreap(handle)?;
            // Spawn two threads, one to wait() and one to try_wait(). It should be impossible for the
            // try_wait thread to return Ok(None) at this point. However, we want to make sure there's
            // no race condition between them, where the wait() thread has said it's waiting and
            // released the child lock but hasn't yet actually waited.
            let barrier = std::sync::Barrier::new(2);
            let try_wait_ret = std::thread::scope(|scope| {
                scope.spawn(|| {
                    barrier.wait();
                    child.wait().unwrap();
                });
                scope
                    .spawn(|| {
                        barrier.wait();
                        child.try_wait().unwrap()
                    })
                    .join()
                    .unwrap()
            });
            let test_time_so_far = Instant::now().saturating_duration_since(test_start);
            assert!(
                try_wait_ret.is_some(),
                "encountered the race condition after {test_time_so_far:?} ({iterations} iterations)",
            );
            iterations += 1;

            // If we've met the target test duration (1 sec by default), exit with success.
            // Otherwise keep looping and trying to provoke the race.
            if test_time_so_far >= test_duration {
                return Ok(());
            }
        }
    }
}
