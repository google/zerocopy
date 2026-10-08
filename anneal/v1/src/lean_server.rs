// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{
    fs, io,
    process::{Child, Command},
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, Instant},
};

use anyhow::{Context, Result, ensure};

use crate::lean_sdk::FiniteProducerLease;

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
    completion: Option<FiniteProducerLease>,
    completion_since: Option<Instant>,
}

impl Process {
    pub(crate) fn spawn(command: &mut Command) -> Result<Self> {
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }
        Ok(Self {
            child: command.spawn().context("Launching bound Lake process")?,
            stopped: false,
            completion: None,
            completion_since: None,
        })
    }
    /// Inherit one already-held producer lease in the launched native group.
    /// Only the child descriptor loses CLOEXEC; unrelated parent launches must
    /// never keep this workspace's producer lease alive.
    pub(crate) fn spawn_inheriting(command: &mut Command, producer: &fs::File) -> Result<Self> {
        #[cfg(unix)]
        {
            use std::os::{fd::AsRawFd as _, unix::process::CommandExt as _};
            let descriptor = producer.as_raw_fd();
            // SAFETY: the borrowed producer remains open through spawn, and the
            // child callback uses only async-signal-safe fcntl and errno reads.
            unsafe {
                command.pre_exec(move || {
                    let flags = libc::fcntl(descriptor, libc::F_GETFD);
                    if flags == -1
                        || libc::fcntl(descriptor, libc::F_SETFD, flags & !libc::FD_CLOEXEC) == -1
                    {
                        return Err(io::Error::last_os_error());
                    }
                    Ok(())
                });
            }
            Self::spawn(command)
        }
        #[cfg(not(unix))]
        {
            let _ = (command, producer);
            anyhow::bail!("Native producer lease inheritance is unsupported on this platform")
        }
    }

    /// Only finite groups use this completion barrier. Idle native peers have
    /// independently held shared leases and must not wait for each other.
    pub(crate) fn spawn_finite(
        command: &mut Command,
        completion: FiniteProducerLease,
    ) -> Result<Self> {
        let mut process = Self::spawn_inheriting(command, completion.holder())?;
        process.completion = Some(completion);
        Ok(process)
    }

    /// Signals/reaping initiate cleanup; only this poll certifies completion.
    /// The caller retains its main writer while pending. Error/cancel may drop
    /// that writer, but native holders still fence every successor's admission.
    pub(crate) fn poll_stopped(&mut self) -> Result<bool> {
        self.stop();
        let Some(completion) = &self.completion else { return Ok(true) };
        let reaped = self.child.try_wait()?.is_some();
        if completion.poll_released()? && reaped {
            self.completion = None;
            self.completion_since = None;
            return Ok(true);
        }
        ensure!(
            self.completion_since.is_some_and(|since| since.elapsed() < Duration::from_secs(60)),
            "Lean producer descendants did not stop; close the remaining producer before retrying"
        );
        Ok(false)
    }

    pub(crate) fn stop(&mut self) {
        self.stop_with_grace(|| thread::sleep(Duration::from_millis(50)));
    }
    fn stop_with_grace(&mut self, grace: impl FnOnce()) {
        if self.stopped {
            return;
        }
        self.stopped = true;
        if self.completion.is_some() {
            self.completion_since = Some(Instant::now());
        }
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
                // ESRCH is 3 on the supported Unix platforms: the known
                // group is absent. Finite completion separately waits for
                // inherited holders, including any detached descendants.
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
        if let Some(completion) = &mut self.completion {
            completion.release_parent();
        }
    }
}

impl Drop for Process {
    fn drop(&mut self) {
        self.stop();
    }
}

#[cfg(test)]
mod tests {
    #[cfg(unix)]
    use std::path::PathBuf;

    use super::*;
    #[cfg(unix)]
    use crate::lean_sdk::Workspace;

    #[cfg(unix)]
    #[test]
    fn finite_completion_waits_for_detached_holder_and_cancel_fences_successor() {
        use std::os::fd::AsRawFd as _;
        struct ReleaseOnDrop(PathBuf);
        impl Drop for ReleaseOnDrop {
            fn drop(&mut self) {
                let _ = fs::write(&self.0, b"release");
            }
        }
        let parent = tempfile::tempdir().unwrap();
        let root = parent.path().join("workspace");
        let fixture = crate::lean_sdk::tests::Fixture::new(&["Shared.A"]);
        let workspace = Workspace::create(&fixture.sdk, &root, &["."]).unwrap();
        Workspace::write_lakefile(
            &fixture.sdk,
            workspace.root(),
            &[crate::lean_sdk::LakeLibrary { name: "User", source_root: ".", modules: &[] }],
        )
        .unwrap();
        let root = workspace.root().to_owned();
        let writer = workspace.writer_lock().unwrap();
        let completion = FiniteProducerLease::acquire(&root).unwrap();
        let descriptor = completion.holder().as_raw_fd();
        let ready = parent.path().join("detached-ready");
        let release = parent.path().join("detached-release");
        let release_on_drop = ReleaseOnDrop(release.clone());
        let mut command = Command::new("/usr/bin/python3");
        command
            .args([
                "-I",
                "-B",
                "-c",
                r#"
import os, pathlib, sys, time
fd = int(sys.argv[1])
ready, release = map(pathlib.Path, sys.argv[2:])
if os.fork() == 0:
    os.setsid()
    null = os.open('/dev/null', os.O_RDWR)
    for stream in (0, 1, 2):
        os.dup2(null, stream)
    os.close(null)
    os.fstat(fd)
    ready.write_text('ready')
    deadline = time.monotonic() + 10
    while not release.exists() and time.monotonic() < deadline:
        time.sleep(0.005)
    os._exit(0)
deadline = time.monotonic() + 3
while not ready.exists():
    if time.monotonic() >= deadline:
        os._exit(2)
    time.sleep(0.005)
os._exit(0)
"#,
            ])
            .arg(descriptor.to_string())
            .arg(&ready)
            .arg(&release);
        let mut process = Process::spawn_finite(&mut command, completion).unwrap();
        assert!(process.child.wait().unwrap().success());
        assert!(ready.exists());
        assert!(!process.poll_stopped().unwrap());
        // The completion deadline must fail, never admit a still-live holder.
        process.completion_since = Some(Instant::now() - Duration::from_secs(60));
        assert!(process.poll_stopped().is_err());
        let cancelled = Instant::now();
        drop(process);
        assert!(cancelled.elapsed() < Duration::from_secs(1));
        drop(writer);
        let deadline = Instant::now() + Duration::from_secs(3);
        let mut successor = loop {
            if let Some(successor) = Workspace::try_reserve_root_for_startup(&root).unwrap() {
                break successor;
            }
            assert!(Instant::now() < deadline, "Cancelled parent retained its main writer");
            thread::sleep(Duration::from_millis(5));
        };
        assert!(successor.try_admit().unwrap().is_none());
        fs::write(&release, b"release").unwrap();
        let deadline = Instant::now() + Duration::from_secs(3);
        loop {
            if let Some(writer) = successor.try_admit().unwrap() {
                drop(writer);
                break;
            }
            assert!(Instant::now() < deadline, "Released finite holder still fences its successor");
            thread::sleep(Duration::from_millis(5));
        }
        drop(release_on_drop);
    }

    #[cfg(unix)]
    #[test]
    fn finite_completion_rejects_replacement_of_the_lease_name() {
        use std::os::unix::fs::PermissionsExt as _;
        let parent = tempfile::tempdir().unwrap();
        let root = parent.path().join("workspace");
        fs::create_dir(&root).unwrap();
        let _writer = Workspace::lock_root(&root).unwrap();
        let mut completion = FiniteProducerLease::acquire(&root).unwrap();
        let holder = completion.holder().try_clone().unwrap();
        completion.release_parent();
        let (_, path) = crate::lean_sdk::open_native_producer_lease(&root, false).unwrap();
        fs::rename(&path, parent.path().join("retained-producer-lease")).unwrap();
        fs::write(&path, b"").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        assert!(completion.poll_released().is_err());
        drop(holder);
    }

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
