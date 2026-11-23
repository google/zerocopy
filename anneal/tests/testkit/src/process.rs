// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Process-group and subreaper subprocess supervision with replay fidelity.
//!
//! Replaces direct-child-only timeouts with process-group isolation
//! (`CommandExt::process_group(0)`), Linux `PR_SET_CHILD_SUBREAPER` grandchild
//! adoption, and synchronous `-pgid` reaping until `ECHILD`. Every executed
//! command writes `invocation.json`, `outcome.json`, `stdout`, `stderr`, and a
//! signal-forwarding `reproduce.py` wrapper into a fresh log slot.

use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::fs::{self, File};
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use serde_json::{Value, json};

use crate::TestResult;

/// Caller-supplied command description with complete explicit environment
/// (`env_clear()` before applying `environment`).
#[derive(Clone, Debug)]
pub struct Invocation {
    pub executable: PathBuf,
    pub arguments: Vec<OsString>,
    pub environment: BTreeMap<OsString, OsString>,
}

impl Invocation {
    /// Construct an invocation for an absolute `executable` path with
    /// explicit `arguments` and an initially empty environment.
    pub fn new(executable: impl Into<PathBuf>, arguments: &[&str]) -> Self {
        Self {
            executable: executable.into(),
            arguments: arguments.iter().map(OsString::from).collect(),
            environment: BTreeMap::new(),
        }
    }

    /// Construct an invocation from arbitrary `OsStr` arguments.
    pub fn with_os_args<I, S>(executable: impl Into<PathBuf>, arguments: I) -> Self
    where
        I: IntoIterator<Item = S>,
        S: AsRef<OsStr>,
    {
        Self {
            executable: executable.into(),
            arguments: arguments.into_iter().map(|s| s.as_ref().to_os_string()).collect(),
            environment: BTreeMap::new(),
        }
    }

    /// Insert an environment variable into the cleared child environment.
    pub fn env(mut self, key: impl Into<OsString>, value: impl Into<OsString>) -> Self {
        self.environment.insert(key.into(), value.into());
        self
    }

    /// Append one argument.
    pub fn arg(mut self, arg: impl AsRef<OsStr>) -> Self {
        self.arguments.push(arg.as_ref().to_os_string());
        self
    }
}

/// Terminal disposition of a supervised child process group.
#[derive(Debug)]
pub enum Termination {
    LaunchFailed(String),
    Exited(ExitStatus),
    TimedOut(ExitStatus),
}

impl Termination {
    /// Human-readable summary of the child outcome.
    pub fn describe(&self) -> String {
        match self {
            Self::LaunchFailed(error) => format!("child did not start: {error}"),
            Self::Exited(status) => format!("child exited: {status}"),
            Self::TimedOut(status) => {
                format!("process timed out; reaped process group: {status}")
            }
        }
    }

    /// Structured outcome metadata written to `outcome.json`.
    pub fn metadata(&self) -> Value {
        match self {
            Self::LaunchFailed(error) => {
                json!({"kind": "launch_failed", "error": error})
            }
            Self::Exited(status) => {
                json!({"kind": "exited", "code": status.code(), "status": status.to_string()})
            }
            Self::TimedOut(status) => {
                json!({"kind": "timed_out", "status": status.to_string()})
            }
        }
    }
}

/// Observed output and termination outcome of a supervised invocation.
#[derive(Debug)]
pub struct ProcessOutcome {
    pub invocation: Invocation,
    pub working_directory: PathBuf,
    pub log_dir: PathBuf,
    pub termination: Termination,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl ProcessOutcome {
    /// Require normal exit with `code`, returning diagnostic output on
    /// mismatch.
    pub fn expect_code(&self, code: i32) -> TestResult {
        match self.termination {
            Termination::Exited(status) if status.code() == Some(code) => Ok(()),
            _ => Err(format!("expected exit code {code}: {}", self.describe())),
        }
    }

    /// Format invocation coordinates, exit status, and raw output streams.
    pub fn describe(&self) -> String {
        format!(
            "{} {:?} in {}: {}\nstdout: {}\nstderr: {}",
            self.invocation.executable.display(),
            self.invocation.arguments,
            self.working_directory.display(),
            self.termination.describe(),
            String::from_utf8_lossy(&self.stdout),
            String::from_utf8_lossy(&self.stderr)
        )
    }
}

/// Enable Linux `PR_SET_CHILD_SUBREAPER` once per test process so reparented
/// grandchildren (`lean`, `rustc`, `bwrap`, `ld`) stay waitable children of
/// the test runner rather than escaping to PID 1.
pub fn ensure_child_subreaper() -> TestResult {
    static RESULT: OnceLock<Result<(), String>> = OnceLock::new();
    RESULT
        .get_or_init(|| {
            #[cfg(target_os = "linux")]
            {
                // SAFETY: `prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0)` sets a
                // process-wide kernel attribute with no pointer dereferences.
                let rc = unsafe { libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) };
                if rc != 0 {
                    return Err(format!(
                        "prctl(PR_SET_CHILD_SUBREAPER) failed: {}",
                        std::io::Error::last_os_error()
                    ));
                }
            }
            Ok(())
        })
        .clone()
}

/// Supervises isolated process-group invocations with file-backed stdio and
/// deterministic replay bundle generation.
#[derive(Clone, Debug)]
pub struct ProcessSupervisor {
    timeout: Duration,
}

impl ProcessSupervisor {
    /// Create a supervisor enforcing `timeout` on every invocation.
    pub fn new(timeout: Duration) -> TestResult<Self> {
        if timeout.is_zero() {
            return Err("process timeout must be positive".into());
        }
        ensure_child_subreaper()?;
        Ok(Self { timeout })
    }

    /// Execute `invocation` with `current_dir = work_dir` and emit
    /// `invocation.json`, `outcome.json`, `stdout`, `stderr`, and
    /// `reproduce.py`
    /// under `log_dir` (which must not already exist).
    pub fn run(
        &self,
        invocation: &Invocation,
        work_dir: &Path,
        log_dir: &Path,
        run_root: &Path,
    ) -> TestResult<ProcessOutcome> {
        ensure_child_subreaper()?;
        if !invocation.executable.is_absolute() {
            return Err(format!(
                "tool path must be absolute: {}",
                invocation.executable.display()
            ));
        }
        reject_symlink_components(log_dir)?;
        let parent = log_dir
            .parent()
            .ok_or_else(|| format!("log directory has no parent: {}", log_dir.display()))?;
        fs::create_dir_all(parent)
            .map_err(|error| format!("create command log parent: {error}"))?;
        fs::create_dir(log_dir)
            .map_err(|error| format!("create {}: {error}", log_dir.display()))?;

        let exe_str = path_utf8(&invocation.executable, "executable")?;
        let work_str = path_utf8(work_dir, "working_directory")?;
        let root_str = path_utf8(run_root, "original_run_root")?;
        let args_utf8: Vec<&str> = invocation
            .arguments
            .iter()
            .map(|a| {
                a.to_str().ok_or_else(|| {
                    format!("command argument is not valid UTF-8: {a:?}")
                })
            })
            .collect::<TestResult<Vec<_>>>()?;
        let mut env_utf8 = BTreeMap::new();
        for (k, v) in &invocation.environment {
            let ks = k
                .to_str()
                .ok_or_else(|| format!("env key is not valid UTF-8: {k:?}"))?;
            let vs = v
                .to_str()
                .ok_or_else(|| format!("env value for {ks} is not valid UTF-8: {v:?}"))?;
            env_utf8.insert(ks, vs);
        }

        write_json(
            &log_dir.join("invocation.json"),
            &json!({
                "executable": exe_str,
                "arguments": args_utf8,
                "working_directory": work_str,
                "environment": env_utf8,
                "original_run_root": root_str,
            }),
        )?;
        write_regular_file(&log_dir.join("reproduce.py"), REPRODUCE.as_bytes())?;

        let stdout_path = log_dir.join("stdout");
        let stderr_path = log_dir.join("stderr");
        let stdout_file = File::create(&stdout_path)
            .map_err(|error| format!("create {}: {error}", stdout_path.display()))?;
        let stderr_file = File::create(&stderr_path)
            .map_err(|error| format!("create {}: {error}", stderr_path.display()))?;

        let mut command = Command::new(&invocation.executable);
        command
            .args(&invocation.arguments)
            .current_dir(work_dir)
            .env_clear()
            .envs(&invocation.environment)
            .stdin(Stdio::null())
            .stdout(stdout_file)
            .stderr(stderr_file);
        #[cfg(unix)]
        {
            use std::os::unix::process::CommandExt;
            command.process_group(0);
        }

        let termination = match command.spawn() {
            Err(error) => Termination::LaunchFailed(error.to_string()),
            Ok(child) => supervise_child(child, self.timeout, log_dir)?,
        };

        let observed = termination.describe();
        write_json(&log_dir.join("outcome.json"), &termination.metadata()).map_err(
            |error| {
                format!(
                    "{} {:?}: {observed}; retain process outcome: {error}",
                    invocation.executable.display(),
                    invocation.arguments
                )
            },
        )?;
        let stdout = fs::read(&stdout_path).map_err(|error| {
            format!("read {} after {observed}: {error}", stdout_path.display())
        })?;
        let stderr = fs::read(&stderr_path).map_err(|error| {
            format!("read {} after {observed}: {error}", stderr_path.display())
        })?;

        Ok(ProcessOutcome {
            invocation: invocation.clone(),
            working_directory: work_dir.to_path_buf(),
            log_dir: log_dir.to_path_buf(),
            termination,
            stdout,
            stderr,
        })
    }
}

#[cfg(unix)]
fn supervise_child(
    mut child: Child,
    timeout: Duration,
    log_dir: &Path,
) -> TestResult<Termination> {
    let pgid = child.id() as libc::pid_t;
    let deadline = Instant::now() + timeout;
    let mut poll_sleep = Duration::from_millis(1);

    loop {
        match child.try_wait() {
            Ok(Some(status)) => {
                // Reap reparented grandchildren already terminated in `pgid`,
                // and terminate any orphaned live descendant holding workspace
                // locks before returning. `PR_SET_CHILD_SUBREAPER` keeps
                // reparented descendants attached until we `waitpid` them, so
                // `waitpid(-pgid, WNOHANG) == 0` guarantees `pgid` is pinned by
                // our own live descendant (zero PID-reuse race).
                reap_or_kill_pgid_after_exit(pgid, log_dir)?;
                return Ok(Termination::Exited(status));
            }
            Ok(None) => {
                let now = Instant::now();
                if now >= deadline {
                    // Send SIGKILL to `-pgid` BEFORE reaping `child`, so `pgid`
                    // cannot be recycled before `kill(-pgid)` runs.
                    // SAFETY: `pgid` is positive (`child.id()`) and pinned
                    // until `child.wait()` reaps the group leader below.
                    let kill_rc = unsafe { libc::kill(-pgid, libc::SIGKILL) };
                    let kill_err = (kill_rc != 0).then(std::io::Error::last_os_error);
                    let status = child.wait().map_err(|error| {
                        format!(
                            "reap timed-out child (kill={kill_err:?}) in {}",
                            log_dir.display()
                        )
                            + &format!(": {error}")
                    })?;
                    reap_pgid_blocking(pgid)?;
                    if let Some(err) = kill_err
                        && err.raw_os_error() != Some(libc::ESRCH)
                    {
                        return Err(format!(
                            "kill(-{pgid}, SIGKILL) failed after deadline: {err}; logs={}",
                            log_dir.display()
                        ));
                    }
                    return Ok(Termination::TimedOut(status));
                }
                let remaining = deadline.saturating_duration_since(now);
                std::thread::sleep(poll_sleep.min(remaining));
                poll_sleep = (poll_sleep * 2).min(Duration::from_millis(10));
            }
            Err(error) => {
                // SAFETY: `pgid` is pinned by the still-unreaped `child`.
                let _ = unsafe { libc::kill(-pgid, libc::SIGKILL) };
                let reap = child.wait();
                let _ = reap_pgid_blocking(pgid);
                return Err(format!(
                    "wait failed: {error}; reap={reap:?}; logs={}",
                    log_dir.display()
                ));
            }
        }
    }
}

#[cfg(unix)]
fn reap_pgid_blocking(pgid: libc::pid_t) -> TestResult {
    loop {
        let mut status: libc::c_int = 0;
        // SAFETY: `status` points to valid stack storage; `waitpid` only
        // reaps children of the current process in process group `pgid`.
        let rc = unsafe { libc::waitpid(-pgid, &mut status, 0) };
        if rc > 0 {
            continue;
        }
        let err = std::io::Error::last_os_error();
        match err.raw_os_error() {
            Some(libc::EINTR) => continue,
            Some(libc::ECHILD) => return Ok(()),
            _ => return Err(format!("waitpid(-{pgid}) failed: {err}")),
        }
    }
}

#[cfg(unix)]
fn reap_or_kill_pgid_after_exit(pgid: libc::pid_t, log_dir: &Path) -> TestResult {
    loop {
        let mut status: libc::c_int = 0;
        // SAFETY: `status` points to valid stack storage.
        let rc = unsafe { libc::waitpid(-pgid, &mut status, libc::WNOHANG) };
        if rc > 0 {
            continue;
        }
        if rc == 0 {
            // A live reparented descendant still belongs to us inside `pgid`.
            // Terminate the orphaned group cleanly and reap until `ECHILD`.
            // SAFETY: our own live child holds `pgid` pinned until reaped.
            let kill_rc = unsafe { libc::kill(-pgid, libc::SIGKILL) };
            if kill_rc != 0 {
                let err = std::io::Error::last_os_error();
                if err.raw_os_error() != Some(libc::ESRCH) {
                    return Err(format!(
                        "kill orphaned group -{pgid} failed ({err}); logs={}",
                        log_dir.display()
                    ));
                }
            }
            return reap_pgid_blocking(pgid);
        }
        let err = std::io::Error::last_os_error();
        match err.raw_os_error() {
            Some(libc::EINTR) => continue,
            Some(libc::ECHILD) => return Ok(()),
            _ => {
                return Err(format!(
                    "waitpid(-{pgid}, WNOHANG) failed: {err}; logs={}",
                    log_dir.display()
                ));
            }
        }
    }
}

#[cfg(not(unix))]
fn supervise_child(
    mut child: Child,
    timeout: Duration,
    log_dir: &Path,
) -> TestResult<Termination> {
    let deadline = Instant::now() + timeout;
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return Ok(Termination::Exited(status)),
            Ok(None) if Instant::now() >= deadline => {
                let _ = child.kill();
                let status = child
                    .wait()
                    .map_err(|e| format!("reap timed-out child in {}: {e}", log_dir.display()))?;
                return Ok(Termination::TimedOut(status));
            }
            Ok(None) => std::thread::sleep(Duration::from_millis(5)),
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("wait failed: {error}; logs={}", log_dir.display()));
            }
        }
    }
}

fn path_utf8<'a>(path: &'a Path, label: &str) -> TestResult<&'a str> {
    path.to_str()
        .ok_or_else(|| format!("{label} path is not valid UTF-8: {}", path.display()))
}

pub(crate) fn reject_symlink_components(path: &Path) -> TestResult {
    for ancestor in path.ancestors().collect::<Vec<_>>().into_iter().rev() {
        match fs::symlink_metadata(ancestor) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(format!(
                    "symlink is not an owned fixture destination: {}",
                    ancestor.display()
                ));
            }
            Ok(_) => {}
            Err(error)
                if matches!(
                    error.kind(),
                    std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
                ) => {}
            Err(error) => {
                return Err(format!("inspect {}: {error}", ancestor.display()));
            }
        }
    }
    Ok(())
}

pub(crate) fn validate_single_component(name: &str, label: &str) -> TestResult {
    let mut components = Path::new(name).components();
    if !matches!(
        (components.next(), components.next()),
        (Some(Component::Normal(part)), None) if part == name
    ) {
        return Err(format!("expected a single normal {label}: {name:?}"));
    }
    Ok(())
}

pub(crate) fn write_json(path: &Path, value: &Value) -> TestResult {
    reject_symlink_components(path)?;
    let bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("serialize {}: {error}", path.display()))?;
    write_regular_file(path, &bytes)
}

pub(crate) fn write_regular_file(path: &Path, bytes: &[u8]) -> TestResult {
    use std::io::Write;
    reject_symlink_components(path)?;
    let parent = path
        .parent()
        .ok_or_else(|| format!("destination has no parent directory: {path:?}"))?;
    let permissions = match fs::metadata(path) {
        Ok(metadata) => metadata.is_file().then(|| metadata.permissions()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => return Err(format!("inspect {}: {error}", path.display())),
    };
    let mut temporary = tempfile::NamedTempFile::new_in(parent)
        .map_err(|error| format!("stage {}: {error}", path.display()))?;
    temporary
        .write_all(bytes)
        .map_err(|error| format!("write {}: {error}", path.display()))?;
    if let Some(permissions) = permissions {
        temporary
            .as_file()
            .set_permissions(permissions)
            .map_err(|error| format!("set permissions {}: {error}", path.display()))?;
    }
    temporary
        .persist(path)
        .map_err(|error| format!("replace {}: {error}", path.display()))?;
    Ok(())
}

const REPRODUCE: &str = r#"#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
import pathlib
import signal
import subprocess
import sys

here = pathlib.Path(__file__).resolve().parent
request = json.loads((here / 'invocation.json').read_text())
# Command bundles live at <root>/logs/commands/<NNNN>/reproduce.py.
root = here.parents[2]
run_text = (root / 'run.json').read_text()
run = json.loads(run_text)
old = pathlib.Path(request['original_run_root'])

def relocate(value):
    path = pathlib.Path(value)
    try:
        relative = path.relative_to(old)
    except ValueError:
        return value
    if '..' in relative.parts:
        return value
    prefix = str(old)
    if value.startswith(prefix):
        return str(root) + value[len(prefix):]
    separators = os.sep + (os.altsep or '')
    trailing = value[len(value.rstrip(separators)):]
    return str(root / relative) + trailing

print(run_text, file=sys.stderr)
timeout = run['process_timeout_seconds']
cmd = [relocate(request['executable'])] + list(map(relocate, request['arguments']))
cwd = relocate(request['working_directory'])
env = {k: relocate(v) for k, v in request['environment'].items()}

popen_kwargs = {'cwd': cwd, 'env': env, 'stdin': subprocess.DEVNULL}
if os.name == 'posix':
    if sys.version_info >= (3, 11):
        popen_kwargs['process_group'] = 0
    else:
        popen_kwargs['start_new_session'] = True

proc = subprocess.Popen(cmd, **popen_kwargs)

def forward_signal(signum, _frame):
    if os.name == 'posix':
        try:
            os.killpg(proc.pid, signum)
        except ProcessLookupError:
            pass
    else:
        proc.terminate()

if os.name == 'posix':
    for sig in (signal.SIGINT, signal.SIGTERM):
        signal.signal(sig, forward_signal)

try:
    returncode = proc.wait(timeout=timeout)
except subprocess.TimeoutExpired:
    if os.name == 'posix':
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    else:
        proc.kill()
    proc.wait()
    print(f'process timed out after {timeout} seconds', file=sys.stderr)
    sys.exit(124)

if os.name == 'posix' and returncode < 0:
    signum = -returncode
    print(f'process terminated by signal {signum}', file=sys.stderr, flush=True)
    if signum not in (signal.SIGKILL, signal.SIGSTOP):
        signal.signal(signum, signal.SIG_DFL)
    if hasattr(signal, 'pthread_sigmask'):
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signum})
    os.kill(os.getpid(), signum)
    sys.exit(f'could not reproduce termination by signal {signum}')
sys.exit(returncode)
"#;

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn timeout_kills_and_reaps_detached_grandchild_synchronously() {
        let dir = tempfile::tempdir().unwrap();
        let work = dir.path().join("work");
        let logs = dir.path().join("logs/commands/0000");
        fs::create_dir_all(&work).unwrap();

        let pid_file = work.join("grandchild.pid");
        let sentinel_file = work.join("grandchild.ran");
        let pid_file_str = pid_file.to_str().unwrap();
        let sentinel_str = sentinel_file.to_str().unwrap();

        // Spawn a parent `/bin/sh` that forks a grandchild sleeping 30s and
        // waits; the supervisor must kill the entire process group at timeout
        // and reap the grandchild synchronously before returning.
        let script = format!(
            "python3 -c 'import os, time; open({pid:?}, \"w\").write(str(os.getpid())); time.sleep(30); open({sent:?}, \"w\").write(\"alive\")' & wait",
            pid = pid_file_str,
            sent = sentinel_str,
        );
        let sup = ProcessSupervisor::new(Duration::from_millis(250)).unwrap();
        let inv = Invocation::new("/bin/sh", &["-c", &script])
            .env("PATH", "/usr/bin:/bin");

        let started = Instant::now();
        let outcome = sup.run(&inv, &work, &logs, dir.path()).unwrap();
        assert!(
            matches!(outcome.termination, Termination::TimedOut(_)),
            "{outcome:?}"
        );
        assert!(started.elapsed() < Duration::from_secs(5));

        if let Ok(pid_text) = fs::read_to_string(&pid_file) {
            let gpid: i32 = pid_text.trim().parse().unwrap();
            // Waitpid reaped the grandchild synchronously, so `kill(gpid, 0)`
            // must fail with `ESRCH` (not even a zombie remains).
            // SAFETY: probing PID liveness with signal 0.
            let alive = unsafe { libc::kill(gpid, 0) };
            assert_eq!(alive, -1, "grandchild {gpid} still alive after timeout");
            assert_eq!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::ESRCH)
            );
        }
        assert!(!sentinel_file.exists());
    }

    #[test]
    fn subreaper_kills_and_reaps_reparented_orphan_when_parent_exits_early() {
        let dir = tempfile::tempdir().unwrap();
        let work = dir.path().join("work");
        let logs = dir.path().join("logs/commands/0000");
        fs::create_dir_all(&work).unwrap();

        let pid_file = work.join("orphan.pid");
        let pid_file_str = pid_file.to_str().unwrap();

        // Direct child spawns an orphan grandchild inheriting the same pgid,
        // waits until the grandchild writes its PID file and signals readiness
        // over a pipe, and immediately exits 0 without waiting.
        let script = format!(
            concat!(
                "import os, subprocess, sys; ",
                "r, w = os.pipe(); ",
                "subprocess.Popen([sys.executable, '-c', ",
                "'import os, sys, time; ",
                "open(sys.argv[1], \"w\").write(str(os.getpid())); ",
                "os.write(int(sys.argv[2]), b\"1\"); ",
                "time.sleep(30)', ",
                "{pid:?}, str(w)], pass_fds=(w,)); ",
                "os.close(w); os.read(r, 1); os._exit(0)"
            ),
            pid = pid_file_str,
        );
        let sup = ProcessSupervisor::new(Duration::from_secs(5)).unwrap();
        let inv = Invocation::new("/usr/bin/python3", &["-c", &script]);

        let started = Instant::now();
        let outcome = sup.run(&inv, &work, &logs, dir.path()).unwrap();
        outcome.expect_code(0).unwrap();
        assert!(started.elapsed() < Duration::from_secs(3));

        // `sup.run` already ran `reap_or_kill_pgid_after_exit`, so the
        // reparented grandchild was already killed and synchronously reaped.
        let pid_text = fs::read_to_string(&pid_file).unwrap();
        let gpid: i32 = pid_text.trim().parse().unwrap();
        // SAFETY: probing PID liveness with signal 0.
        let alive = unsafe { libc::kill(gpid, 0) };
        assert_eq!(alive, -1, "reparented orphan {gpid} outlived sup.run");
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::ESRCH)
        );
    }

    #[test]
    fn file_backed_stdio_handles_large_output_without_pipe_deadlock() {
        let dir = tempfile::tempdir().unwrap();
        let work = dir.path().join("work");
        let logs = dir.path().join("logs/commands/0000");
        fs::create_dir_all(&work).unwrap();

        let sup = ProcessSupervisor::new(Duration::from_secs(5)).unwrap();
        let inv = Invocation::new(
            "/usr/bin/python3",
            &["-c", "import sys; sys.stdout.write('A' * 262144); sys.stderr.write('B' * 262144)"],
        );
        let outcome = sup.run(&inv, &work, &logs, dir.path()).unwrap();
        outcome.expect_code(0).unwrap();
        assert_eq!(outcome.stdout.len(), 262_144);
        assert_eq!(outcome.stderr.len(), 262_144);
    }

    #[test]
    fn reproduce_script_relocates_and_forwards_timeout() {
        let dir = tempfile::tempdir().unwrap();
        let work = dir.path().join("work");
        let logs = dir.path().join("logs/commands/0000");
        fs::create_dir_all(&work).unwrap();
        write_json(
            &dir.path().join("run.json"),
            &json!({
                "original_run_root": dir.path(),
                "process_timeout_seconds": 0.2,
            }),
        )
        .unwrap();
        let sup = ProcessSupervisor::new(Duration::from_millis(200)).unwrap();
        let inv = Invocation::new(
            "/usr/bin/python3",
            &["-c", "import time; time.sleep(5)"],
        );
        let outcome = sup.run(&inv, &work, &logs, dir.path()).unwrap();
        assert!(matches!(outcome.termination, Termination::TimedOut(_)));

        let replay = Command::new("/usr/bin/python3")
            .arg(logs.join("reproduce.py"))
            .output()
            .unwrap();
        assert_eq!(replay.status.code(), Some(124));
        assert!(String::from_utf8_lossy(&replay.stderr).contains("process timed out after 0.2 seconds"));
        assert!(logs.join("reproduce.py").metadata().unwrap().permissions().mode() & 0o777 != 0);
    }
}
