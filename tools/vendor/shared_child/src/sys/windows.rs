use std::io;
use std::os::windows::io::{AsRawHandle, RawHandle};
use std::process::Child;
use windows_sys::Win32::Foundation::{HANDLE, WAIT_OBJECT_0, WAIT_TIMEOUT};
use windows_sys::Win32::System::Threading::{WaitForSingleObject, INFINITE};

#[derive(Copy, Clone)]
pub struct Handle(RawHandle);

// Kind of like a child PID on Unix, it's important not to keep the handle
// around after the child has been cleaned up. The best solution would be to
// have the handle actually borrow the child, but we need to keep the child
// unborrowed. Instead we just avoid storing them.
pub fn get_handle(child: &Child) -> Handle {
    Handle(child.as_raw_handle())
}

// This is very similar to libstd's Child::wait implementation, because the basic wait on Windows
// doesn't reap. (There's no such thing as reaping child processes on Windows. Instead, you close
// the child handle when you're done with it, like a file. These function names are just for
// consistency with the Unix side of things).  The main difference is that this can be called
// without &mut Child.
pub fn wait_noreap(handle: Handle) -> io::Result<()> {
    let wait_ret = unsafe { WaitForSingleObject(handle.0 as HANDLE, INFINITE) };
    match wait_ret {
        WAIT_OBJECT_0 => Ok(()),
        _ => Err(io::Error::last_os_error()),
    }
}

pub fn try_wait_noreap(handle: Handle) -> io::Result<bool> {
    let wait_ret = unsafe { WaitForSingleObject(handle.0 as HANDLE, 0) };
    if wait_ret == WAIT_OBJECT_0 {
        // The child has exited.
        Ok(true)
    } else if wait_ret == WAIT_TIMEOUT {
        // The child has not exited yet.
        Ok(false)
    } else {
        Err(io::Error::last_os_error())
    }
}

// Again there's no such thing as "reaping" a child process on Windows, and these function names is
// just for consistency with the Unix side of things.
#[cfg(feature = "timeout")]
pub fn wait_deadline_noreap(handle: Handle, deadline: std::time::Instant) -> io::Result<bool> {
    let timeout = deadline.saturating_duration_since(std::time::Instant::now());
    // Convert to milliseconds, rounding *up*. (That way we don't repeatedly sleep for 0ms when
    // we're close to the timeout.)
    let timeout_ms = (timeout.as_nanos().saturating_add(999_999) / 1_000_000)
        .try_into()
        .unwrap_or(u32::MAX);
    let wait_ret = unsafe { WaitForSingleObject(handle.0 as HANDLE, timeout_ms) };
    use windows_sys::Win32::Foundation::WAIT_TIMEOUT;
    match wait_ret {
        WAIT_OBJECT_0 => Ok(true),
        WAIT_TIMEOUT => Ok(false),
        _ => Err(io::Error::last_os_error()),
    }
}
