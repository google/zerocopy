// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    io,
    process::{Child, Command},
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::Duration,
};

use anyhow::{Context, Result, ensure};

static INTERRUPTED: AtomicBool = AtomicBool::new(false);

pub(crate) fn interrupted() -> bool {
    INTERRUPTED.load(Ordering::Relaxed)
}

#[cfg(unix)]
pub(crate) struct SignalGuard(Vec<(i32, usize)>);

#[cfg(unix)]
unsafe extern "C" {
    fn signal(number: i32, handler: usize) -> usize;
}

#[cfg(unix)]
extern "C" fn interrupt_signal(_number: i32) {
    INTERRUPTED.store(true, Ordering::Relaxed);
}

#[cfg(unix)]
impl SignalGuard {
    pub(crate) fn install() -> Result<Self> {
        INTERRUPTED.store(false, Ordering::Relaxed);
        let mut guard = Self(Vec::new());
        for number in [2, 15] {
            // SAFETY: SIGINT/SIGTERM use a process-local, allocation-free
            // handler. The prior handlers are restored when run returns.
            let previous = unsafe { signal(number, interrupt_signal as *const () as usize) };
            ensure!(previous != usize::MAX, "Installing editor interruption handler failed");
            guard.0.push((number, previous));
        }
        Ok(guard)
    }
}

#[cfg(unix)]
impl Drop for SignalGuard {
    fn drop(&mut self) {
        for &(number, previous) in &self.0 {
            // SAFETY: restore the original handler for the same signal.
            unsafe {
                signal(number, previous);
            }
        }
    }
}

pub(crate) struct Process {
    pub(crate) child: Child,
    stopped: bool,
}

impl Process {
    pub(crate) fn spawn(command: &mut Command) -> Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        Ok(Self { child: command.spawn().context("Launching bound Lake process")?, stopped: false })
    }
    pub(crate) fn stop(&mut self) {
        self.stop_with_grace(|| thread::sleep(Duration::from_millis(50)));
    }
    fn stop_with_grace(&mut self, grace: impl FnOnce()) {
        if self.stopped {
            return;
        }
        self.stopped = true;
        // Kill the known group even if its leader has exited. Lake workers must
        // not survive a refresh, broken pipe, protocol error, or client EOF.
        #[cfg(unix)]
        {
            unsafe extern "C" {
                fn kill(pid: i32, signal: i32) -> i32;
            }
            let group = -(self.child.id() as i32);
            // SAFETY: kill only receives the numeric group created above.
            let signaled = unsafe { kill(group, 15) };
            if signaled == 0 {
                // Only a group that received SIGTERM needs time to exit.
                grace();
                unsafe {
                    kill(group, 9);
                }
            } else {
                let error = io::Error::last_os_error();
                // ESRCH is 3 on the supported Unix platforms: the exited
                // leader left no descendants, so there is nothing to await.
                if error.raw_os_error() != Some(3) {
                    eprintln!("Anneal: terminating Lake process group failed: {error}");
                    // Other errors do not establish an absent group. Attempt
                    // immediate forced cleanup, then reap the known child below.
                    unsafe {
                        kill(group, 9);
                    }
                }
            }
        }
        #[cfg(not(unix))]
        let _ = grace;
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        self.stop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn exited_process_without_descendants_skips_termination_grace() {
        let mut command = Command::new("/usr/bin/true");
        let mut process = Process::spawn(&mut command).unwrap();
        assert!(process.child.wait().unwrap().success());
        process.stop_with_grace(|| panic!("An absent process group must not incur a grace delay"));
        assert!(process.stopped);
    }

    #[cfg(unix)]
    #[test]
    fn live_process_group_receives_termination_grace() {
        let mut command = Command::new("/bin/sleep");
        command.arg("30");
        let mut process = Process::spawn(&mut command).unwrap();
        let mut waited = false;
        process.stop_with_grace(|| waited = true);
        assert!(waited);
        assert!(process.child.try_wait().unwrap().is_some());
    }
}
