use std::io;
use std::mem::MaybeUninit;
use std::process::Child;
#[cfg(feature = "timeout")]
use std::time::Instant;

// A handle on Unix is just the PID.
#[derive(Copy, Clone)]
pub struct Handle(u32);

pub fn get_handle(child: &Child) -> Handle {
    Handle(child.id())
}

// This blocks until the child exits, without reaping the child.
pub fn wait_noreap(handle: Handle) -> io::Result<()> {
    loop {
        let mut siginfo = MaybeUninit::zeroed();
        let ret = unsafe {
            libc::waitid(
                libc::P_PID,
                handle.0 as libc::id_t,
                siginfo.as_mut_ptr(),
                libc::WEXITED | libc::WNOWAIT,
            )
        };
        if ret == 0 {
            return Ok(());
        }
        let error = io::Error::last_os_error();
        if error.kind() != io::ErrorKind::Interrupted {
            return Err(error);
        }
        // We were interrupted. Loop and retry.
    }
}

// This checks whether the child has already exited, without reaping the child.
pub fn try_wait_noreap(handle: Handle) -> io::Result<bool> {
    let mut siginfo: libc::siginfo_t;
    let ret = unsafe {
        // Darwin doesn't touch the siginfo_t struct if the child hasn't exited
        // yet. It expects us to have zeroed it ahead of time:
        //
        //   The state of the siginfo structure in this case
        //   is undefined.  Some implementations bzero it, some
        //   (like here) leave it untouched for efficiency.
        //
        //   Thus the most portable check for "no matching pid with
        //   WNOHANG" is to store a zero into si_pid before
        //   invocation, then check for a non-zero value afterwards.
        //
        // https://github.com/opensource-apple/xnu/blob/0a798f6738bc1db01281fc08ae024145e84df927/bsd/kern/kern_exit.c#L2150-L2156
        siginfo = std::mem::zeroed();
        libc::waitid(
            libc::P_PID,
            handle.0 as libc::id_t,
            &mut siginfo,
            libc::WEXITED | libc::WNOWAIT | libc::WNOHANG,
        )
    };
    if ret != 0 {
        // EINTR should be impossible here
        Err(io::Error::last_os_error())
    } else if siginfo.si_signo == libc::SIGCHLD {
        // The child has exited.
        Ok(true)
    } else if siginfo.si_signo == 0 {
        // The child has not exited.
        Ok(false)
    } else {
        // This should be impossible if we called waitid correctly. But it will
        // show up on macOS if we forgot to zero the siginfo_t above, for example.
        Err(io::Error::other(format!(
            "unexpected si_signo from waitid: {}",
            siginfo.si_signo
        )))
    }
}

// This blocks until either the child exits or the deadline passes, without reaping the child.
#[cfg(feature = "timeout")]
pub fn wait_deadline_noreap(handle: Handle, deadline: Instant) -> io::Result<bool> {
    let mut sigchld_waiter = sigchld::Waiter::new()?;
    loop {
        // Has the child exited?
        if try_wait_noreap(handle)? {
            return Ok(true);
        }
        // Has the deadline passed?
        if deadline < Instant::now() {
            return Ok(false);
        }
        // Wait for the next SIGCHLD and check again. Note that this returns immediately if a
        // SIGCHLD has arrived since the last wait.
        sigchld_waiter.wait_deadline(deadline)?;
    }
}
