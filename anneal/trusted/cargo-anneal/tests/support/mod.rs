// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Private support for the installed smoke suite and its runner tests.

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::Mutex;
use std::time::Duration;

use serde_json::{Value, json};
use wait_timeout::ChildExt;

pub type TestResult<T = ()> = Result<T, String>;

pub fn select_cases<'a>(cases: &[&'a str], selection: Option<&str>) -> TestResult<Vec<&'a str>> {
    for name in cases {
        validate_case_name(name)?;
    }
    let mut discovered = cases.to_vec();
    discovered.sort_unstable();
    if discovered.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err("duplicate integration case name".into());
    }
    let selected: Vec<_> = discovered
        .iter()
        .copied()
        .filter(|name| selection.is_none_or(|wanted| *name == wanted))
        .collect();
    if selected.is_empty() {
        return Err(format!(
            "no integration cases selected by {selection:?}; available: {}",
            discovered.join(", ")
        ));
    }
    Ok(selected)
}

/// Owns all case directories; cleanup never reaches outside this directory.
pub struct RunDirectory {
    dir: tempfile::TempDir,
    timeout: Duration,
}

impl RunDirectory {
    pub fn new(revision: &str, timeout: Duration) -> TestResult<Self> {
        if timeout.is_zero() {
            return Err("process timeout must be positive".into());
        }
        // TMPDIR may be relative or name a symlink. Resolve the base before
        // allocation so ownership, recorded paths, and replay share one root.
        let temporary = fs::canonicalize(std::env::temp_dir())
            .map_err(|error| format!("resolve integration temporary directory: {error}"))?;
        let mut builder = tempfile::Builder::new();
        builder.prefix("anneal-integration-");
        // tempfile directories otherwise inherit ordinary directory defaults.
        // Recordings can contain readable command logs and executable fixtures;
        // their modes must remain useful. Protect the enclosing directory at
        // creation, before any input or output can become visible to others.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let dir = builder
            .tempdir_in(temporary)
            .map_err(|error| format!("create integration directory: {error}"))?;
        let run = Self { dir, timeout };
        write_json(
            &run.path().join("run.json"),
            &json!({
                "source_revision_supplied_by_caller": revision,
                "original_run_root": run.path(),
                "process_timeout_seconds": timeout.as_secs_f64(),
            }),
        )?;
        Ok(run)
    }

    pub fn path(&self) -> &Path {
        self.dir.path()
    }

    pub fn case(&self, name: &str) -> TestResult<CaseDirectory<'_>> {
        validate_case_name(name)?;
        let path = owned_path(self.path(), &Path::new("cases").join(name))?;
        fs::create_dir_all(path.parent().unwrap())
            .map_err(|error| format!("create case parent: {error}"))?;
        fs::create_dir(&path).map_err(|error| format!("create {}: {error}", path.display()))?;
        Ok(CaseDirectory {
            path,
            run_root: self.path(),
            timeout: self.timeout,
            next_command: 0,
        })
    }

    /// Run only the supplied selection, using at most `jobs` worker threads.
    /// Process deadlines apply to each invocation, not arbitrary Rust code.
    pub fn run_cases(
        &self,
        cases: &[&str],
        jobs: usize,
        body: impl Fn(&str, &mut CaseDirectory<'_>) -> TestResult + Sync,
    ) -> TestResult {
        if jobs == 0 || cases.is_empty() {
            return Err("case list and worker count must be nonempty".into());
        }
        // Reject invalid catalog names before creating any directories. Then
        // create every case before running bodies: distinct filenames can
        // alias on the host filesystem, and no case may run if creation fails.
        select_cases(cases, None)?;
        let prepared = cases
            .iter()
            .map(|name| self.case(name).map(|case| (*name, case)))
            .collect::<TestResult<Vec<_>>>()?;
        let pending = Mutex::new(prepared.into_iter());
        let failures = Mutex::new(Vec::new());
        std::thread::scope(|scope| {
            for _ in 0..jobs.min(cases.len()) {
                scope.spawn(|| {
                    loop {
                        let Some((name, mut case)) = pending.lock().unwrap().next() else {
                            break;
                        };
                        eprintln!("RUN installed case {name}");
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            body(name, &mut case)
                        }))
                        .unwrap_or_else(|_| Err("case panicked".into()));
                        match result {
                            Ok(()) => eprintln!("PASS installed case {name}"),
                            Err(error) => failures.lock().unwrap().push(format!("{name}: {error}")),
                        }
                    }
                });
            }
        });
        let mut failures = failures.into_inner().unwrap();
        failures.sort();
        if failures.is_empty() {
            Ok(())
        } else {
            Err(failures.join("\n"))
        }
    }

    /// Preserve the original failure if writing or exporting evidence fails.
    /// The original directory stays available if the export is incomplete.
    pub fn finish(self, result: TestResult, diagnostics: Option<&Path>) -> TestResult {
        let Err(mut failure) = result else {
            return Ok(());
        };
        if let Err(error) = owned_path(self.path(), Path::new("failure.txt"))
            .and_then(|path| write_file(&path, failure.as_bytes()))
        {
            failure.push_str(&format!("\nretain failure text: {error}"));
        }
        let retained = self.dir.keep();
        failure.push_str(&format!("\nevidence retained at {}", retained.display()));
        if let Some(destination) = diagnostics {
            let export = destination.join(retained.file_name().unwrap());
            if let Err(error) = export_evidence(&retained, &export) {
                failure.push_str(&format!(
                    "\nretention export incomplete at {}: {error}",
                    export.display()
                ));
            } else {
                failure.push_str(&format!("\nevidence exported to {}", export.display()));
            }
        }
        Err(failure)
    }
}

/// Borrows its owning run, preventing cleanup or export before its last use.
pub struct CaseDirectory<'run> {
    path: PathBuf,
    run_root: &'run Path,
    timeout: Duration,
    next_command: usize,
}

impl CaseDirectory<'_> {
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn write(&self, relative: impl AsRef<Path>, bytes: &[u8]) -> TestResult {
        let path = owned_path(&self.path, relative.as_ref())?;
        fs::create_dir_all(path.parent().unwrap())
            .map_err(|error| format!("create parent of {}: {error}", path.display()))?;
        write_file(&path, bytes)
    }

    pub fn copy(&self, source: &Path, relative: impl AsRef<Path>) -> TestResult {
        copy_tree(source, &owned_path(&self.path, relative.as_ref())?)
    }

    pub fn run(&mut self, invocation: &Invocation) -> TestResult<ProcessOutcome> {
        if !invocation.executable.is_absolute() {
            return Err(format!(
                "tool path must be absolute: {}",
                invocation.executable.display()
            ));
        }
        let logs = owned_path(
            &self.path,
            Path::new(&format!("commands/{:04}", self.next_command)),
        )?;
        self.next_command += 1;
        fs::create_dir_all(logs.parent().unwrap())
            .map_err(|error| format!("create command parent: {error}"))?;
        // Command logs are fresh destinations, not reusable fixture paths.
        // Reject an existing directory before any log file can be followed.
        fs::create_dir(&logs).map_err(|error| format!("create {}: {error}", logs.display()))?;
        write_json(
            &logs.join("invocation.json"),
            &json!({
                "executable": invocation.executable,
                "arguments": invocation.arguments,
                "working_directory": self.path,
                "environment": invocation.environment,
                "original_run_root": self.run_root,
            }),
        )?;
        fs::write(logs.join("reproduce.py"), REPRODUCE)
            .map_err(|error| format!("write replay script: {error}"))?;
        let stdout_path = logs.join("stdout");
        let stderr_path = logs.join("stderr");
        let stdout = create_file(&stdout_path)?;
        let stderr = create_file(&stderr_path)?;
        let mut command = Command::new(&invocation.executable);
        command
            .args(&invocation.arguments)
            .current_dir(&self.path)
            .env_clear()
            .envs(&invocation.environment)
            .stdin(Stdio::null())
            .stdout(stdout)
            .stderr(stderr);

        // File redirection avoids pipe-buffer deadlocks and keeps raw bytes.
        // The deadline kills and reaps this child only. CI's outer job deadline
        // remains responsible for descendants and cancellation of the runner.
        let termination = match command.spawn() {
            Err(error) => Termination::LaunchFailed(error.to_string()),
            Ok(mut child) => match child.wait_timeout(self.timeout) {
                Ok(Some(status)) => Termination::Exited(status),
                Ok(None) => {
                    let kill = child.kill();
                    let status = child.wait();
                    match (kill, status) {
                        (Ok(()), Ok(status)) => Termination::TimedOut(status),
                        (kill, status) => {
                            return Err(format!(
                                "process deadline reached; kill={kill:?}; reap={status:?}; logs={}",
                                logs.display()
                            ));
                        }
                    }
                }
                Err(error) => {
                    let kill = child.kill();
                    let reap = child.wait();
                    return Err(format!(
                        "wait failed: {error}; kill={kill:?}; reap={reap:?}; logs={}",
                        logs.display()
                    ));
                }
            },
        };
        let observed = termination.describe();
        write_json(&logs.join("outcome.json"), &termination.metadata()).map_err(|error| {
            format!(
                "{} {:?}: {observed}; retain process outcome: {error}",
                invocation.executable.display(),
                invocation.arguments
            )
        })?;
        let stdout = fs::read(&stdout_path)
            .map_err(|error| format!("read {} after {observed}: {error}", stdout_path.display()))?;
        let stderr = fs::read(&stderr_path)
            .map_err(|error| format!("read {} after {observed}: {error}", stderr_path.display()))?;
        Ok(ProcessOutcome {
            invocation: invocation.clone(),
            working_directory: self.path.clone(),
            termination,
            stdout,
            stderr,
        })
    }
}

/// The caller chooses the complete environment; the runner never searches PATH.
#[derive(Clone, Debug)]
pub struct Invocation {
    pub executable: PathBuf,
    pub arguments: Vec<String>,
    pub environment: BTreeMap<String, String>,
}

impl Invocation {
    pub fn new(executable: impl Into<PathBuf>, arguments: &[&str]) -> Self {
        Self {
            executable: executable.into(),
            arguments: arguments.iter().map(|arg| (*arg).to_string()).collect(),
            environment: BTreeMap::new(),
        }
    }
}

#[derive(Debug)]
pub enum Termination {
    LaunchFailed(String),
    Exited(ExitStatus),
    TimedOut(ExitStatus),
}

impl Termination {
    fn describe(&self) -> String {
        match self {
            Self::LaunchFailed(error) => {
                format!("child did not start: {error}")
            }
            Self::Exited(status) => format!("child exited: {status}"),
            Self::TimedOut(status) => {
                format!("process timed out; reaped child: {status}")
            }
        }
    }

    fn metadata(&self) -> Value {
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

#[derive(Debug)]
pub struct ProcessOutcome {
    invocation: Invocation,
    working_directory: PathBuf,
    pub termination: Termination,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl ProcessOutcome {
    pub fn expect_code(&self, code: i32) -> TestResult {
        match self.termination {
            Termination::Exited(status) if status.code() == Some(code) => Ok(()),
            _ => Err(format!("expected exit code {code}: {}", self.describe())),
        }
    }

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

pub fn write_json(path: &Path, value: &Value) -> TestResult {
    reject_symlink_components(path)?;
    let bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("serialize {}: {error}", path.display()))?;
    write_file(path, &bytes)
}

// A child can leave a hard link at a fixture or evidence filename. Replace the
// directory entry with a fresh inode instead of truncating the linked file.
// Retain existing Unix permissions so executable fixtures stay executable.
// New files keep tempfile's default permissions.
fn write_file(path: &Path, bytes: &[u8]) -> TestResult {
    reject_symlink_components(path)?;
    let parent = path
        .parent()
        .ok_or_else(|| format!("file destination has no parent directory: {path:?}"))?;
    let permissions = match fs::metadata(path) {
        Ok(metadata) => metadata.is_file().then(|| metadata.permissions()),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => {
            return Err(format!("inspect {}: {error}", path.display()));
        }
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

fn owned_path(root: &Path, relative: &Path) -> TestResult<PathBuf> {
    if relative.as_os_str().is_empty()
        || !relative
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(format!(
            "expected a case-relative path: {}",
            relative.display()
        ));
    }
    let path = root.join(relative);
    reject_symlink_components(&path)?;
    Ok(path)
}

// These helpers operate on test-owned trees while no child is mutating them.
// Reject existing symlinks, including dangling final symlinks, before any
// operation can follow them. This is not isolation from concurrent writers.
fn reject_symlink_components(path: &Path) -> TestResult {
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

fn validate_case_name(name: &str) -> TestResult {
    let mut components = Path::new(name).components();
    if !matches!(
        (components.next(), components.next()),
        (Some(Component::Normal(part)), None) if part == name
    ) {
        return Err(format!(
            "expected a case name consisting of one filename: {name:?}"
        ));
    }
    Ok(())
}

fn create_file(path: &Path) -> TestResult<File> {
    File::create(path).map_err(|error| format!("create {}: {error}", path.display()))
}

fn export_evidence(source: &Path, destination: &Path) -> TestResult {
    let source = fs::canonicalize(source)
        .map_err(|error| format!("resolve {}: {error}", source.display()))?;
    let destination = resolve_destination(destination)?;
    if destination.starts_with(&source) || source.starts_with(&destination) {
        return Err("evidence export must be disjoint from the retained run".into());
    }
    // Existing export roots are supported: copied file entries below are
    // replaced with fresh inodes so outside hard-link aliases stay unchanged.
    // Keep this root private before copying, allowing readable or executable
    // fixture modes to remain faithful without exposing the evidence. Tighten
    // only this resolved directory; file chmod could affect outside aliases,
    // and existing diagnostics-parent permissions belong to the caller.
    //
    // The caller keeps both trees stable after path resolution. These checks
    // describe existing aliases in a cooperative filesystem namespace.
    let mut builder = fs::DirBuilder::new();
    builder.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(&destination)
        .map_err(|error| format!("create {}: {error}", destination.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&destination, fs::Permissions::from_mode(0o700))
            .map_err(|error| format!("restrict {}: {error}", destination.display()))?;
    }
    for entry in
        fs::read_dir(&source).map_err(|error| format!("list {}: {error}", source.display()))?
    {
        let entry = entry.map_err(|error| format!("read evidence entry: {error}"))?;
        // Toolchains can be several GiB. Keep the owned installation in the
        // original run, but export its identity and paths rather than another
        // copy. Reproduction requires the recorded archive/build artifacts.
        if entry.file_name() != "installation" {
            copy_tree(&entry.path(), &destination.join(entry.file_name()))?;
        }
    }
    Ok(())
}

// Resolve existing ancestors before appending missing directories. Checking
// each component also handles aliases followed by `..` without creating any
// destination directory inside the evidence we are about to copy.
fn resolve_destination(path: &Path) -> TestResult<PathBuf> {
    let absolute = std::path::absolute(path)
        .map_err(|error| format!("resolve {}: {error}", path.display()))?;
    let mut resolved = PathBuf::new();
    for component in absolute.components() {
        match component {
            Component::CurDir => continue,
            Component::ParentDir => {
                resolved.pop();
            }
            other => resolved.push(other),
        }
        match fs::canonicalize(&resolved) {
            Ok(path) => resolved = path,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!("resolve {}: {error}", resolved.display()));
            }
        }
    }
    Ok(resolved)
}

fn copy_tree(source: &Path, destination: &Path) -> TestResult {
    let metadata = fs::symlink_metadata(source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if !metadata.is_file() && !metadata.is_dir() {
        return Err(format!(
            "expected regular fixture file or directory: {}",
            source.display()
        ));
    }
    // Check before creating anything: a destination inside the source would
    // become another source entry while traversal is still in progress.
    reject_symlink_components(destination)?;
    let resolved_source = fs::canonicalize(source)
        .map_err(|error| format!("resolve {}: {error}", source.display()))?;
    let destination = resolve_destination(destination)?;
    if destination.starts_with(&resolved_source) || resolved_source.starts_with(&destination) {
        return Err("fixture copy source and destination must be disjoint".into());
    }
    copy_tree_contents(source, &destination)
}

fn copy_tree_contents(source: &Path, destination: &Path) -> TestResult {
    // A pre-existing descendant of a copied directory can also be a link.
    reject_symlink_components(destination)?;
    let metadata = fs::symlink_metadata(source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if metadata.is_file() {
        fs::create_dir_all(destination.parent().unwrap())
            .map_err(|error| format!("create copy parent: {error}"))?;
        // An existing regular destination can be a hard link outside the owned
        // tree. Copy to a fresh inode, keeping the source's permissions, then
        // replace the destination entry.
        let temporary = tempfile::NamedTempFile::new_in(destination.parent().unwrap())
            .map_err(|error| format!("stage {}: {error}", destination.display()))?;
        fs::copy(source, temporary.path()).map_err(|error| {
            format!(
                "copy {} to {}: {error}",
                source.display(),
                destination.display()
            )
        })?;
        temporary
            .persist(destination)
            .map_err(|error| format!("replace {}: {error}", destination.display()))?;
    } else if metadata.is_dir() {
        fs::create_dir_all(destination)
            .map_err(|error| format!("create {}: {error}", destination.display()))?;
        let mut entries = fs::read_dir(source)
            .map_err(|error| format!("list {}: {error}", source.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read entry in {}: {error}", source.display()))?;
        entries.sort_by_key(|entry| entry.file_name());
        for entry in entries {
            copy_tree_contents(&entry.path(), &destination.join(entry.file_name()))?;
        }
    } else {
        return Err(format!(
            "expected regular fixture file or directory: {}",
            source.display()
        ));
    }
    Ok(())
}

// JSON carries argv and environment without requiring shell escaping. Moving
// a downloaded evidence directory also moves its case inputs. External tool
// and archive paths must be restored from the same recorded build artifacts.
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
# Logs always live at cases/<case>/commands/<number>. A case may itself have
# a fixture named run.json, so metadata filenames cannot identify the root.
root = here.parents[3]
run_text = (root / 'run.json').read_text()
run = json.loads(run_text)
old = pathlib.Path(request['original_run_root'])

def relocate(value):
    # Owned paths occupy a whole value. pathlib supplies the host's component
    # and case rules; a bare string prefix would also match sibling names.
    # Embedded path text and sibling names remain literal values.
    path = pathlib.Path(value)
    try:
        relative = path.relative_to(old)
    except ValueError:
        return value
    if '..' in relative.parts:
        return value
    # Keep the original suffix: source/ can select directory contents while
    # source selects the directory itself. Rebuilding a Path drops that final
    # separator and can change the recorded operation.
    prefix = str(old)
    if value.startswith(prefix):
        return str(root) + value[len(prefix):]
    # Native alternative spellings still use pathlib's ownership check.
    separators = os.sep + (os.altsep or '')
    trailing = value[len(value.rstrip(separators)):]
    return str(root / relative) + trailing

print(run_text, file=sys.stderr)
timeout = run['process_timeout_seconds']
try:
    result = subprocess.run(
        [relocate(request['executable'])] + list(map(relocate, request['arguments'])),
        cwd=relocate(request['working_directory']),
        env={k: relocate(v) for k, v in request['environment'].items()},
        timeout=timeout,
        stdin=subprocess.DEVNULL,
    )
except subprocess.TimeoutExpired:
    # The exception may report a remaining wait interval, not this deadline.
    print(f'process timed out after {timeout} seconds', file=sys.stderr)
    sys.exit(124)
if os.name == 'posix' and result.returncode < 0:
    signum = -result.returncode
    print(f'process terminated by signal {signum}', file=sys.stderr, flush=True)
    # Python ignores SIGPIPE and can inherit other handlers or a signal mask.
    # Restore the default action so replay retains signal termination instead
    # of converting a negative return code into a normal exit modulo 256.
    if signum not in (signal.SIGKILL, signal.SIGSTOP):
        signal.signal(signum, signal.SIG_DFL)
    if hasattr(signal, 'pthread_sigmask'):
        signal.pthread_sigmask(signal.SIG_UNBLOCK, {signum})
    os.kill(os.getpid(), signum)
    sys.exit(f'could not reproduce termination by signal {signum}')
sys.exit(result.returncode)
"#;
