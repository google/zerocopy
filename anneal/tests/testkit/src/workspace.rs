// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Typestate-enforced temporary test workspaces and read-only store guards.
//!
//! [`WorkspaceBuilder`] allocates a `0o700` canonicalized temporary root split
//! into disjoint sibling subdirectories (`<root>/work/`, `<root>/store/`,
//! `<root>/logs/`). Simulated read-only store packages (`0o555` directories and
//! `0o444` files) are registered with [`ReadOnlyTreeGuard`] so top-down
//! `chmod u+rwx` restoration always runs before [`tempfile::TempDir`] drop.

use std::ffi::OsStr;
use std::fs;
use std::marker::PhantomData;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use serde_json::json;

use crate::TestResult;
use crate::assertions::{AuditReport, CaptureStatus, VerifyReceipt};
use crate::process::{
    Invocation, ProcessOutcome, ProcessSupervisor, reject_symlink_components,
    validate_single_component, write_json, write_regular_file,
};
use crate::toolchain::ToolchainEnv;

/// Initial typestate marker for [`WorkspaceBuilder`].
#[derive(Debug)]
pub struct Building;

/// Guards a read-only directory tree (`0o555` dirs / `0o444` files) so owner
/// permissions (`u+rwx`) are restored top-down without following symlinks
/// before temporary-directory cleanup removes the tree.
#[derive(Debug)]
pub struct ReadOnlyTreeGuard {
    root: PathBuf,
    active: bool,
}

impl ReadOnlyTreeGuard {
    /// Freeze `root` bottom-up (`0o555` directories, read-only files preserving
    /// executable bits) and return an active [`ReadOnlyTreeGuard`].
    pub fn freeze(root: impl Into<PathBuf>) -> TestResult<Self> {
        let root = root.into();
        freeze_tree_bottom_up(&root)?;
        Ok(Self { root, active: true })
    }

    /// Path of the protected read-only root.
    pub fn path(&self) -> &Path {
        &self.root
    }

    /// Restore owner `u+rwx` permissions top-down (without following symlinks)
    /// and disarm automatic drop restoration.
    pub fn restore(&mut self) -> TestResult {
        if !self.active {
            return Ok(());
        }
        self.active = false;
        restore_tree_top_down(&self.root)
    }

    /// Keep the directory read-only on drop (used only when retaining a
    /// diagnostic sandbox on disk).
    pub(crate) fn disarm(&mut self) {
        self.active = false;
    }
}

impl Drop for ReadOnlyTreeGuard {
    fn drop(&mut self) {
        if self.active {
            let _ = restore_tree_top_down(&self.root);
            self.active = false;
        }
    }
}

/// Raw process output returned by [`StagedWorkspace::exec`].
#[derive(Debug)]
pub struct RawOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

/// Combined process outcome and typed artifact/receipt output from a staged
/// command execution.
#[derive(Debug)]
pub struct ExecutedRun<Out> {
    pub output: Out,
    pub process: ProcessOutcome,
}

impl<Out> ExecutedRun<Out> {
    /// Assert child exit code equals `expected_code`.
    pub fn expect_code(&self, expected_code: i32) -> TestResult<&Self> {
        self.process.expect_code(expected_code)?;
        Ok(self)
    }
}

/// Linear workspace builder in [`Building`] state.
///
/// Field declaration order ensures `ro_guards` drops *before* `root`
/// (`TempDir`), restoring `u+rwx` on frozen store trees prior to deletion.
#[derive(Debug)]
pub struct WorkspaceBuilder<State = Building> {
    ro_guards: Vec<ReadOnlyTreeGuard>,
    root: tempfile::TempDir,
    work_dir: PathBuf,
    store_dir: PathBuf,
    logs_dir: PathBuf,
    timeout: Duration,
    _state: PhantomData<State>,
}

impl WorkspaceBuilder<Building> {
    /// Allocate a `0o700` canonicalized temporary workspace partitioned into
    /// disjoint `work/`, `store/`, and `logs/` siblings.
    pub fn new(prefix: &str, timeout: Duration) -> TestResult<Self> {
        if timeout.is_zero() {
            return Err("workspace timeout must be positive".into());
        }
        let temp_base = fs::canonicalize(std::env::temp_dir())
            .map_err(|error| format!("resolve temporary directory: {error}"))?;
        let mut builder = tempfile::Builder::new();
        builder.prefix(prefix);
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            builder.permissions(fs::Permissions::from_mode(0o700));
        }
        let root = builder
            .tempdir_in(&temp_base)
            .map_err(|error| format!("create workspace root: {error}"))?;
        let work_dir = root.path().join("work");
        let store_dir = root.path().join("store");
        let logs_dir = root.path().join("logs");
        for dir in [&work_dir, &store_dir, &logs_dir] {
            fs::create_dir(dir)
                .map_err(|error| format!("create {}: {error}", dir.display()))?;
        }
        Ok(Self {
            ro_guards: Vec::new(),
            root,
            work_dir,
            store_dir,
            logs_dir,
            timeout,
            _state: PhantomData,
        })
    }

    pub fn root_dir(&self) -> &Path {
        self.root.path()
    }

    pub fn work_dir(&self) -> &Path {
        &self.work_dir
    }

    pub fn store_dir(&self) -> &Path {
        &self.store_dir
    }

    pub fn logs_dir(&self) -> &Path {
        &self.logs_dir
    }

    /// Symlink-safe atomic file write under `<root>/work/<rel>`.
    pub fn write_work_file(
        &mut self,
        rel: impl AsRef<Path>,
        bytes: &[u8],
    ) -> TestResult<&mut Self> {
        let dest = owned_rel_path(&self.work_dir, rel.as_ref())?;
        if let Some(parent) = dest.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create parent of {}: {error}", dest.display()))?;
        }
        write_regular_file(&dest, bytes)?;
        Ok(self)
    }

    /// Symlink-safe disjoint tree/file copy into `<root>/work/<rel>`.
    pub fn copy_to_work(
        &mut self,
        source: &Path,
        rel: impl AsRef<Path>,
    ) -> TestResult<&mut Self> {
        let dest = owned_rel_path(&self.work_dir, rel.as_ref())?;
        copy_tree(source, &dest)?;
        Ok(self)
    }

    /// Copy minimal `trusted/lean` and `trusted/audit` lockfiles from an
    /// Anneal repository checkout into `<root>/work/` without copying `vendor/`
    /// or `target/`.
    pub fn seed_minimal_audit_locks(&mut self, checkout: &Path) -> TestResult<&mut Self> {
        for rel in [
            "trusted/lean/lean-toolchain",
            "trusted/lean/foundation-lock.json",
            "trusted/audit/TrustedBoundary.lean",
            "trusted/audit/library-lock.json",
        ] {
            let src = checkout.join(rel);
            let bytes = fs::read(&src)
                .map_err(|error| format!("read {}: {error}", src.display()))?;
            self.write_work_file(rel, &bytes)?;
        }
        Ok(self)
    }

    /// Materialize a simulated store package under `<root>/store/<pkg_name>`
    /// and optionally freeze its permissions (`0o555` dirs / read-only files)
    /// behind a [`ReadOnlyTreeGuard`].
    pub fn add_store_package(
        &mut self,
        pkg_name: &str,
        freeze_read_only: bool,
        populate: impl FnOnce(&Path) -> TestResult,
    ) -> TestResult<PathBuf> {
        validate_single_component(pkg_name, "store package name")?;
        let pkg_dir = self.store_dir.join(pkg_name);
        reject_symlink_components(&pkg_dir)?;
        if pkg_dir.exists() {
            return Err(format!(
                "store package already exists: {}",
                pkg_dir.display()
            ));
        }
        fs::create_dir(&pkg_dir)
            .map_err(|error| format!("create store package {}: {error}", pkg_dir.display()))?;
        populate(&pkg_dir)?;
        if freeze_read_only {
            let guard = ReadOnlyTreeGuard::freeze(&pkg_dir)?;
            self.ro_guards.push(guard);
        }
        Ok(pkg_dir)
    }

    /// Seal inputs, record `run.json`, and transition to [`StagedWorkspace`].
    pub fn stage(self) -> TestResult<StagedWorkspace> {
        write_json(
            &self.root.path().join("run.json"),
            &json!({
                "original_run_root": self.root.path(),
                "work_dir": self.work_dir,
                "store_dir": self.store_dir,
                "process_timeout_seconds": self.timeout.as_secs_f64(),
            }),
        )?;
        let supervisor = ProcessSupervisor::new(self.timeout)?;
        Ok(StagedWorkspace {
            ro_guards: self.ro_guards,
            root: self.root,
            work_dir: self.work_dir,
            store_dir: self.store_dir,
            logs_dir: self.logs_dir,
            supervisor,
            next_command: AtomicUsize::new(0),
        })
    }
}

/// Sealed temporary workspace ready for supervised command execution.
///
/// Field declaration order ensures `ro_guards` drops *before* `root`.
pub struct StagedWorkspace {
    ro_guards: Vec<ReadOnlyTreeGuard>,
    root: tempfile::TempDir,
    work_dir: PathBuf,
    store_dir: PathBuf,
    logs_dir: PathBuf,
    supervisor: ProcessSupervisor,
    next_command: AtomicUsize,
}

impl StagedWorkspace {
    pub fn root_dir(&self) -> &Path {
        self.root.path()
    }

    pub fn work_dir(&self) -> &Path {
        &self.work_dir
    }

    pub fn store_dir(&self) -> &Path {
        &self.store_dir
    }

    pub fn logs_dir(&self) -> &Path {
        &self.logs_dir
    }

    pub fn supervisor(&self) -> &ProcessSupervisor {
        &self.supervisor
    }

    /// Allocate the next fresh command log path `<root>/logs/commands/<NNNN>`.
    pub fn next_command_log_dir(&self) -> PathBuf {
        let idx = self.next_command.fetch_add(1, Ordering::Relaxed);
        self.logs_dir.join(format!("commands/{idx:04}"))
    }

    /// Execute an [`Invocation`] inside an isolated process group with
    /// `current_dir = work_dir` and retain replay logs under `<root>/logs/`.
    pub fn exec(&self, inv: &Invocation) -> TestResult<ExecutedRun<RawOutput>> {
        let log_dir = self.next_command_log_dir();
        let process =
            self.supervisor
                .run(inv, &self.work_dir, &log_dir, self.root.path())?;
        let output = RawOutput {
            stdout: process.stdout.clone(),
            stderr: process.stderr.clone(),
        };
        Ok(ExecutedRun { output, process })
    }

    /// Execute `<cli> verify --capture ... --lean ... --sysroot ... <args...>`
    /// and parse its Schema v3 JSON receipt.
    pub fn run_verify(
        &self,
        tools: &ToolchainEnv,
        args: &[&OsStr],
    ) -> TestResult<ExecutedRun<VerifyReceipt>> {
        let cli = tools
            .cli
            .as_ref()
            .ok_or_else(|| "ToolchainEnv has no `cli` (`cargo-anneal`) binary".to_string())?;
        let capture = tools.capture.as_ref().ok_or_else(|| {
            "ToolchainEnv has no `capture` (`anneal-rustc-capture`) binary".to_string()
        })?;
        let mut inv = Invocation::new(cli, &["verify"])
            .arg("--capture")
            .arg(capture)
            .arg("--lean")
            .arg(&tools.lean)
            .arg("--sysroot")
            .arg(&tools.sysroot);
        for arg in args {
            inv = inv.arg(arg);
        }
        let raw = self.exec(&inv)?;
        let receipt = VerifyReceipt::from_json_slice(&raw.process.stdout).map_err(|err| {
            format!("{err}\n{}", raw.process.describe())
        })?;
        Ok(ExecutedRun {
            output: receipt,
            process: raw.process,
        })
    }

    /// Execute `<capture> capture --sysroot ... <args...>` and parse its JSON
    /// status payload.
    pub fn run_capture(
        &self,
        tools: &ToolchainEnv,
        args: &[&OsStr],
    ) -> TestResult<ExecutedRun<CaptureStatus>> {
        let capture = tools.capture.as_ref().ok_or_else(|| {
            "ToolchainEnv has no `capture` (`anneal-rustc-capture`) binary".to_string()
        })?;
        #[cfg(target_os = "macos")]
        let lib_path_var = "DYLD_LIBRARY_PATH";
        #[cfg(not(target_os = "macos"))]
        let lib_path_var = "LD_LIBRARY_PATH";
        let mut inv = Invocation::new(capture, &["capture"])
            .env("PATH", "/usr/bin:/bin")
            .env(lib_path_var, tools.sysroot.join("lib"))
            .arg("--sysroot")
            .arg(&tools.sysroot);
        for arg in args {
            inv = inv.arg(arg);
        }
        let raw = self.exec(&inv)?;
        let status = CaptureStatus::from_json_slice(&raw.process.stdout).map_err(|err| {
            format!("{err}\n{}", raw.process.describe())
        })?;
        Ok(ExecutedRun {
            output: status,
            process: raw.process,
        })
    }

    /// Execute `<auditor> --lean ... --json <args...>` and parse its
    /// `AuditReport` JSON output.
    pub fn run_audit(
        &self,
        tools: &ToolchainEnv,
        args: &[&OsStr],
    ) -> TestResult<ExecutedRun<AuditReport>> {
        let auditor = tools.auditor.as_ref().ok_or_else(|| {
            "ToolchainEnv has no `auditor` (`anneal-audit`) binary".to_string()
        })?;
        let mut inv = Invocation::new(auditor, &[])
            .arg("--lean")
            .arg(&tools.lean)
            .arg("--json");
        for arg in args {
            inv = inv.arg(arg);
        }
        let raw = self.exec(&inv)?;
        let report = AuditReport::from_json_slice(&raw.process.stdout).map_err(|err| {
            format!("{err}\n{}", raw.process.describe())
        })?;
        Ok(ExecutedRun {
            output: report,
            process: raw.process,
        })
    }

    /// Retain `<root>` (and export evidence to `ANNEAL_TEST_DIAGNOSTICS` if
    /// set, skipping multi-GiB `installation/` trees) when `result.is_err()` or
    /// `ANNEAL_KEEP_SANDBOX=1`; otherwise restore read-only guards and clean
    /// `<root>`.
    pub fn finish<T>(self, result: TestResult<T>) -> TestResult<T> {
        let keep_env = std::env::var_os("ANNEAL_KEEP_SANDBOX")
            .is_some_and(|v| v == "1");
        let diag = std::env::var_os("ANNEAL_TEST_DIAGNOSTICS")
            .filter(|v| !v.is_empty())
            .map(PathBuf::from);
        self.finish_with_options(result, keep_env, diag.as_deref())
    }

    /// Explicit finish variant for unit tests and deterministic diagnostics
    /// control without mutating process-wide environment variables.
    pub fn finish_with_options<T>(
        mut self,
        result: TestResult<T>,
        keep_sandbox: bool,
        diagnostics_dir: Option<&Path>,
    ) -> TestResult<T> {
        match result {
            Ok(value) => {
                if keep_sandbox {
                    for guard in &mut self.ro_guards {
                        guard.disarm();
                    }
                    let _retained = self.root.keep();
                } else {
                    for guard in &mut self.ro_guards {
                        guard.restore()?;
                    }
                }
                Ok(value)
            }
            Err(mut failure) => {
                if let Err(err) =
                    write_regular_file(&self.root.path().join("failure.txt"), failure.as_bytes())
                {
                    failure.push_str(&format!("\nretain failure text: {err}"));
                }
                for guard in &mut self.ro_guards {
                    guard.disarm();
                }
                let retained = self.root.keep();
                failure.push_str(&format!("\nevidence retained at {}", retained.display()));
                if let Some(dest_parent) = diagnostics_dir {
                    let export = dest_parent.join(retained.file_name().unwrap());
                    if let Err(err) = export_evidence(&retained, &export) {
                        failure.push_str(&format!(
                            "\nretention export incomplete at {}: {err}",
                            export.display()
                        ));
                    } else {
                        failure.push_str(&format!(
                            "\nevidence exported to {}",
                            export.display()
                        ));
                    }
                }
                Err(failure)
            }
        }
    }
}

fn owned_rel_path(root: &Path, relative: &Path) -> TestResult<PathBuf> {
    if relative.as_os_str().is_empty()
        || !relative
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(format!(
            "expected a workspace-relative path: {}",
            relative.display()
        ));
    }
    let path = root.join(relative);
    reject_symlink_components(&path)?;
    Ok(path)
}

fn freeze_tree_bottom_up(path: &Path) -> TestResult {
    let meta = fs::symlink_metadata(path)
        .map_err(|error| format!("inspect {}: {error}", path.display()))?;
    if meta.file_type().is_symlink() {
        return Ok(());
    }
    if meta.is_dir() {
        let mut entries: Vec<PathBuf> = fs::read_dir(path)
            .map_err(|error| format!("list {}: {error}", path.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read entry in {}: {error}", path.display()))?
            .into_iter()
            .map(|e| e.path())
            .collect();
        entries.sort();
        for child in entries {
            freeze_tree_bottom_up(&child)?;
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::set_permissions(path, fs::Permissions::from_mode(0o555))
                .map_err(|error| format!("chmod 0o555 {}: {error}", path.display()))?;
        }
    } else if meta.is_file() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = meta.permissions().mode() & !0o222;
            fs::set_permissions(path, fs::Permissions::from_mode(mode))
                .map_err(|error| format!("freeze file {}: {error}", path.display()))?;
        }
    }
    Ok(())
}

fn restore_tree_top_down(path: &Path) -> TestResult {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return Ok(()),
        Err(err) => return Err(format!("inspect {}: {err}", path.display())),
    };
    if meta.file_type().is_symlink() {
        return Ok(());
    }
    if meta.is_dir() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = meta.permissions().mode() | 0o700;
            fs::set_permissions(path, fs::Permissions::from_mode(mode))
                .map_err(|error| format!("restore dir perms {}: {error}", path.display()))?;
        }
        let mut entries: Vec<PathBuf> = fs::read_dir(path)
            .map_err(|error| format!("list {}: {error}", path.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| format!("read entry in {}: {error}", path.display()))?
            .into_iter()
            .map(|e| e.path())
            .collect();
        entries.sort();
        for child in entries {
            restore_tree_top_down(&child)?;
        }
    } else if meta.is_file() {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = meta.permissions().mode() | 0o200;
            fs::set_permissions(path, fs::Permissions::from_mode(mode))
                .map_err(|error| format!("restore file perms {}: {error}", path.display()))?;
        }
    }
    Ok(())
}

fn export_evidence(source: &Path, destination: &Path) -> TestResult {
    let source = fs::canonicalize(source)
        .map_err(|error| format!("resolve {}: {error}", source.display()))?;
    let destination = resolve_destination(destination)?;
    if destination.starts_with(&source) || source.starts_with(&destination) {
        return Err("evidence export must be disjoint from the retained run".into());
    }
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
        if entry.file_name() != "installation" {
            copy_tree(&entry.path(), &destination.join(entry.file_name()))?;
        }
    }
    Ok(())
}

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
    if !metadata.is_file() && !metadata.is_dir() && !metadata.file_type().is_symlink() {
        return Err(format!(
            "expected fixture file, directory, or symlink: {}",
            source.display()
        ));
    }
    reject_symlink_components(destination)?;
    let resolved_source = if metadata.file_type().is_symlink() {
        source.to_path_buf()
    } else {
        fs::canonicalize(source)
            .map_err(|error| format!("resolve {}: {error}", source.display()))?
    };
    let destination = resolve_destination(destination)?;
    if destination.starts_with(&resolved_source) || resolved_source.starts_with(&destination) {
        return Err("fixture copy source and destination must be disjoint".into());
    }
    copy_tree_contents(source, &destination)
}

fn copy_tree_contents(source: &Path, destination: &Path) -> TestResult {
    reject_symlink_components(destination)?;
    let metadata = fs::symlink_metadata(source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if metadata.file_type().is_symlink() {
        #[cfg(unix)]
        {
            if let Some(parent) = destination.parent() {
                fs::create_dir_all(parent)
                    .map_err(|error| format!("create copy parent: {error}"))?;
            }
            let target = fs::read_link(source)
                .map_err(|error| format!("read symlink {}: {error}", source.display()))?;
            std::os::unix::fs::symlink(&target, destination).map_err(|error| {
                format!("recreate symlink {}: {error}", destination.display())
            })?;
            return Ok(());
        }
        #[cfg(not(unix))]
        return Err(format!("symlinks unsupported in copy_tree: {}", source.display()));
    }
    if metadata.is_file() {
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| format!("create copy parent: {error}"))?;
        }
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
    }
    Ok(())
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn read_only_tree_guard_cleans_0555_nested_store_without_eacces() {
        let mut ws = WorkspaceBuilder::new("anneal-testkit-ro-", Duration::from_secs(5)).unwrap();
        let root_path = ws.root_dir().to_path_buf();
        let pkg_dir = ws
            .add_store_package("0001-readonly", true, |pkg| {
                let nested = pkg.join("lib/lean/Init");
                fs::create_dir_all(&nested).unwrap();
                fs::write(nested.join("Core.olean"), b"olean-bytes").unwrap();
                let bin = pkg.join("bin");
                fs::create_dir_all(&bin).unwrap();
                fs::write(bin.join("tool"), b"exe").unwrap();
                fs::set_permissions(bin.join("tool"), fs::Permissions::from_mode(0o755)).unwrap();
                Ok(())
            })
            .unwrap();

        assert_eq!(
            fs::metadata(&pkg_dir).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::metadata(pkg_dir.join("lib/lean/Init")).unwrap().permissions().mode() & 0o777,
            0o555
        );
        assert_eq!(
            fs::metadata(pkg_dir.join("lib/lean/Init/Core.olean")).unwrap().permissions().mode()
                & 0o777,
            0o444
        );
        assert_eq!(
            fs::metadata(pkg_dir.join("bin/tool")).unwrap().permissions().mode() & 0o777,
            0o555
        );

        let staged = ws.stage().unwrap();
        // Verify sibling disjointness between `<root>/work` and `<root>/store`.
        assert!(!staged.work_dir().starts_with(staged.store_dir()));
        assert!(!staged.store_dir().starts_with(staged.work_dir()));

        staged.finish_with_options(Ok(()), false, None).unwrap();
        assert!(!root_path.exists(), "TempDir cleanup leaked {}", root_path.display());
    }

    #[test]
    fn write_work_file_rejects_symlinks_and_parent_traversal() {
        let mut ws = WorkspaceBuilder::new("anneal-testkit-sym-", Duration::from_secs(5)).unwrap();
        let outside = tempfile::tempdir().unwrap();
        fs::write(outside.path().join("secret"), b"untouched").unwrap();
        std::os::unix::fs::symlink(outside.path(), ws.work_dir().join("link")).unwrap();

        assert!(ws.write_work_file("../escape", b"bad").is_err());
        let sym_err = ws.write_work_file("link/secret", b"pwned").unwrap_err();
        assert!(sym_err.contains("symlink"), "{sym_err}");
        assert_eq!(fs::read(outside.path().join("secret")).unwrap(), b"untouched");
    }

    #[test]
    fn failure_retains_and_exports_diagnostics_skipping_installation() {
        let mut ws = WorkspaceBuilder::new("anneal-testkit-diag-", Duration::from_secs(5)).unwrap();
        ws.write_work_file("input.rs", b"pub fn f() {}\n").unwrap();
        fs::create_dir(ws.root_dir().join("installation")).unwrap();
        fs::write(ws.root_dir().join("installation/huge.bin"), b"skip-me").unwrap();
        let root_path = ws.root_dir().to_path_buf();

        let staged = ws.stage().unwrap();
        let export_root = tempfile::tempdir().unwrap();
        let err = staged
            .finish_with_options::<()>(
                Err("synthetic boom".into()),
                false,
                Some(export_root.path()),
            )
            .unwrap_err();
        assert!(err.contains("synthetic boom"), "{err}");
        assert!(err.contains("evidence exported to"), "{err}");

        let exported = export_root.path().join(root_path.file_name().unwrap());
        assert_eq!(fs::read(exported.join("work/input.rs")).unwrap(), b"pub fn f() {}\n");
        assert!(!exported.join("installation").exists());
        fs::remove_dir_all(root_path).unwrap();
    }
}
