//! Unix-only extensions, for sending signals.

use std::io;

pub trait SharedChildExt {
    /// Send a signal to the child process with `libc::kill`. If the process
    /// has already been waited on, this returns `Ok(())` and does nothing.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()>;
}

impl SharedChildExt for super::SharedChild {
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        let inner_guard = self.inner.lock().unwrap();
        // Note that SharedChild::new calls try_wait_and_reap precisely so that we can assume "the
        // child has been reaped if-and-only-if the state is Exited" right here. If we didn't have
        // that guarantee, we'd need to call try_wait_and_reap right here, which would be an odd
        // side effect. Unfortunately std::process::Child doesn't provide a way to query its exit
        // status that doesn't potentially reap it as a side effect.
        if let super::ChildState::Exited(_) = inner_guard.state {
            return Ok(());
        }
        // The child is still running. Signal it. Holding the inner lock here prevents PID races,
        // but note that calling SharedChild::id would reacquire it and deadlock.
        let pid = inner_guard.child.id() as libc::pid_t;
        match unsafe { libc::kill(pid, signal) } {
            -1 => Err(io::Error::last_os_error()),
            _ => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SharedChildExt;
    use crate::tests::*;
    use crate::SharedChild;
    use std::os::unix::process::ExitStatusExt;

    #[test]
    fn test_send_signal() {
        let child = SharedChild::spawn(&mut sleep_forever_cmd()).unwrap();
        child.send_signal(libc::SIGABRT).unwrap();
        let status = child.wait().unwrap();
        assert_eq!(Some(libc::SIGABRT), status.signal());
    }
}
