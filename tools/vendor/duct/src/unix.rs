extern crate libc;

use std::io;

use super::{Handle, HandleInner, PipeHandle};
use shared_child::unix::SharedChildExt;

pub trait HandleExt {
    /// Send a signal to all child processes running under this expression.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()>;
}

impl HandleExt for Handle {
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        self.inner.send_signal(signal)
    }
}

impl HandleExt for HandleInner {
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        match *self {
            HandleInner::Child(ref child_handle) => child_handle.child().send_signal(signal),
            HandleInner::Pipe(ref pipe_handle) => pipe_handle.send_signal(signal),
            HandleInner::StdinBytes(ref stdin_bytes_handle) => {
                stdin_bytes_handle.inner_handle.send_signal(signal)
            }
            HandleInner::Unchecked(ref inner_handle) => inner_handle.send_signal(signal),
        }
    }
}

impl HandleExt for PipeHandle {
    /// Signals both parts of this `pipe` expression. Returns an error if signalling one of the
    /// expressions returned an error.
    fn send_signal(&self, signal: libc::c_int) -> io::Result<()> {
        let left_result = self.left_handle.send_signal(signal);
        let right_result = self.right_handle.send_signal(signal);
        left_result.and(right_result)
    }
}

#[cfg(test)]
mod tests {
    use super::{libc, HandleExt};
    use crate::cmd;
    use crate::test::path_to_exe;

    use std::os::unix::process::ExitStatusExt;
    use std::sync::Arc;
    use std::thread;

    #[test]
    fn test_send_signal_from_other_thread() {
        let sleep_cmd = cmd(path_to_exe("sleep"), &["1000000"]);
        let handle = Arc::new(sleep_cmd.unchecked().start().unwrap());
        let handle_clone = handle.clone();

        thread::spawn(move || handle_clone.send_signal(libc::SIGABRT).unwrap());
        let status = handle.wait().unwrap();

        assert_eq!(Some(libc::SIGABRT), status.status.signal());
    }

    #[test]
    fn test_send_signal_to_pipe() {
        let sleep_cmd = cmd(path_to_exe("sleep"), &["1000000"]);
        let handle = sleep_cmd
            .pipe(sleep_cmd.clone())
            .unchecked()
            .start()
            .unwrap();
        handle.send_signal(libc::SIGABRT).unwrap();
        let status = handle.wait().unwrap();
        assert_eq!(Some(libc::SIGABRT), status.status.signal());
    }
}
