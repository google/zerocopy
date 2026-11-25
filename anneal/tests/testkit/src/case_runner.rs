// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Multi-case smoke runner and evidence-retention directories.
//!
//! Built on [`ProcessSupervisor`] so installed smoke suites and runner
//! regression tests share one `process_group(0)` + `PR_SET_CHILD_SUBREAPER`
//! execution, symlink-safe staging, and replay implementation.

use std::{
    fs,
    path::{Component, Path, PathBuf},
    sync::{
        Mutex,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use serde_json::json;

use crate::TestResult;
pub use crate::process::{
    Invocation, ProcessOutcome, ProcessSupervisor, Termination, reject_symlink_components,
    write_json, write_regular_file as write_file,
};

/// Validate and deterministically sort `cases`, optionally filtering to
/// `selection`.
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
    /// Allocate a `0o700` canonicalized temporary run root and record
    /// `run.json`.
    pub fn new(revision: &str, timeout: Duration) -> TestResult<Self> {
        let _ = ProcessSupervisor::new(timeout)?;
        // TMPDIR may be relative or name a symlink. Resolve the base before
        // allocation so ownership, recorded paths, and replay share one root.
        let temporary = fs::canonicalize(std::env::temp_dir())
            .map_err(|error| format!("resolve integration temporary directory: {error}"))?;
        let mut builder = tempfile::Builder::new();
        builder.prefix("anneal-integration-");
        // Protect the enclosing directory at creation, before any input or
        // output can become visible to other local users.
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

    /// Create an isolated case directory `<root>/cases/<name>`.
    pub fn case(&self, name: &str) -> TestResult<CaseDirectory<'_>> {
        validate_case_name(name)?;
        let path = owned_path(self.path(), &Path::new("cases").join(name))?;
        fs::create_dir_all(path.parent().unwrap())
            .map_err(|error| format!("create case parent: {error}"))?;
        fs::create_dir(&path).map_err(|error| format!("create {}: {error}", path.display()))?;
        Ok(CaseDirectory {
            path,
            run_root: self.path(),
            supervisor: ProcessSupervisor::new(self.timeout)?,
            next_command: AtomicUsize::new(0),
        })
    }

    /// Run `cases` concurrently using at most `jobs` worker threads.
    pub fn run_cases(
        &self,
        cases: &[&str],
        jobs: usize,
        body: impl Fn(&str, &mut CaseDirectory<'_>) -> TestResult + Sync,
    ) -> TestResult {
        self.run_cases_owned(cases, jobs, |name, mut case| body(name, &mut case))
    }

    /// Run `cases` concurrently, passing each worker ownership of its
    /// [`CaseDirectory`].
    pub fn run_cases_owned(
        &self,
        cases: &[&str],
        jobs: usize,
        body: impl Fn(&str, CaseDirectory<'_>) -> TestResult + Sync,
    ) -> TestResult {
        if jobs == 0 || cases.is_empty() {
            return Err("case list and worker count must be nonempty".into());
        }
        // Reject invalid catalog names before creating any directories. Create
        // every case before running bodies so filesystem alias collisions fail
        // before any case runs.
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
                        let Some((name, case)) = pending.lock().unwrap().next() else {
                            break;
                        };
                        eprintln!("RUN installed case {name}");
                        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            body(name, case)
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
        if failures.is_empty() { Ok(()) } else { Err(failures.join("\n")) }
    }

    /// Preserve the original failure if writing or exporting evidence fails.
    /// The original directory stays available if the export is incomplete;
    /// `installation` is omitted from exported evidence.
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
    supervisor: ProcessSupervisor,
    next_command: AtomicUsize,
}

impl CaseDirectory<'_> {
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Symlink-safe atomic write under `<case>/<relative>`.
    pub fn write(&self, relative: impl AsRef<Path>, bytes: &[u8]) -> TestResult {
        let path = owned_path(&self.path, relative.as_ref())?;
        fs::create_dir_all(path.parent().unwrap())
            .map_err(|error| format!("create parent of {}: {error}", path.display()))?;
        write_file(&path, bytes)
    }

    /// Symlink-safe disjoint regular-tree copy into `<case>/<relative>`.
    pub fn copy(&self, source: &Path, relative: impl AsRef<Path>) -> TestResult {
        copy_regular_tree(source, &owned_path(&self.path, relative.as_ref())?)
    }

    /// Run `invocation` in this case directory using a sequential log slot.
    pub fn run(&mut self, invocation: &Invocation) -> TestResult<ProcessOutcome> {
        self.run_shared(invocation)
    }

    /// Run `invocation` from a shared reference (for parallel case DAG steps).
    pub fn run_shared(&self, invocation: &Invocation) -> TestResult<ProcessOutcome> {
        let command_index = self.next_command.fetch_add(1, Ordering::Relaxed);
        let logs = owned_path(&self.path, Path::new(&format!("commands/{command_index:04}")))?;
        // Logs live at `<run_root>/cases/<case>/commands/<NNNN>` (4 levels
        // below `<run_root>`, so `reproduce.py` resolves `here.parents[3]`).
        self.supervisor.run_at_depth(invocation, &self.path, &logs, self.run_root, 3)
    }
}

fn owned_path(root: &Path, relative: &Path) -> TestResult<PathBuf> {
    if relative.as_os_str().is_empty()
        || !relative.components().all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(format!("expected a case-relative path: {}", relative.display()));
    }
    let path = root.join(relative);
    reject_symlink_components(&path)?;
    Ok(path)
}

fn validate_case_name(name: &str) -> TestResult {
    let mut components = Path::new(name).components();
    if !matches!(
        (components.next(), components.next()),
        (Some(Component::Normal(part)), None) if part == name
    ) {
        return Err(format!("expected a case name consisting of one filename: {name:?}"));
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
    // Existing export roots are supported: copied entries below replace files
    // with fresh inodes so outside hard-link aliases stay unchanged. Tighten
    // only this resolved directory; file chmod could affect outside aliases,
    // and existing diagnostics-parent permissions belong to the caller.
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
        // Toolchains can be several GiB; retain the owned installation in the
        // original run while exporting its identity and command logs.
        if entry.file_name() != "installation" {
            copy_regular_tree(&entry.path(), &destination.join(entry.file_name()))?;
        }
    }
    Ok(())
}

// Resolve existing ancestors before appending missing directories so aliases
// followed by `..` are caught before creating any destination directory.
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

fn copy_regular_tree(source: &Path, destination: &Path) -> TestResult {
    let metadata = fs::symlink_metadata(source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if !metadata.is_file() && !metadata.is_dir() {
        return Err(format!("expected regular fixture file or directory: {}", source.display()));
    }
    reject_symlink_components(destination)?;
    let resolved_source = fs::canonicalize(source)
        .map_err(|error| format!("resolve {}: {error}", source.display()))?;
    let destination = resolve_destination(destination)?;
    if destination.starts_with(&resolved_source) || resolved_source.starts_with(&destination) {
        return Err("fixture copy source and destination must be disjoint".into());
    }
    copy_regular_tree_contents(source, &destination)
}

fn copy_regular_tree_contents(source: &Path, destination: &Path) -> TestResult {
    reject_symlink_components(destination)?;
    let metadata = fs::symlink_metadata(source)
        .map_err(|error| format!("inspect {}: {error}", source.display()))?;
    if metadata.is_file() {
        fs::create_dir_all(destination.parent().unwrap())
            .map_err(|error| format!("create copy parent: {error}"))?;
        // Replace existing regular entries with a fresh inode so outside hard
        // links are never mutated while preserving source file permissions.
        let temporary = tempfile::NamedTempFile::new_in(destination.parent().unwrap())
            .map_err(|error| format!("stage {}: {error}", destination.display()))?;
        fs::copy(source, temporary.path()).map_err(|error| {
            format!("copy {} to {}: {error}", source.display(), destination.display())
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
            copy_regular_tree_contents(&entry.path(), &destination.join(entry.file_name()))?;
        }
    } else {
        return Err(format!("expected regular fixture file or directory: {}", source.display()));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_cases_sorts_dedups_and_filters() {
        let sorted = select_cases(&["z", "a", "m"], None).unwrap();
        assert_eq!(sorted, ["a", "m", "z"]);
        assert_eq!(select_cases(&["z", "a"], Some("z")).unwrap(), ["z"]);
        assert!(select_cases(&["dup", "dup"], None).is_err());
        assert!(select_cases(&["a/b"], None).is_err());
        assert!(select_cases(&["a"], Some("missing")).is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn case_directory_reaps_timed_out_grandchild_via_subreaper() {
        let run = RunDirectory::new("subreaper-check", Duration::from_millis(1500)).unwrap();
        let mut case = run.case("grandchild").unwrap();
        let pid_file = case.path().join("grandchild.pid");
        // Spawn a fresh `/bin/sh -c` grandchild that atomically publishes its
        // own `$$` via temp-file rename and `exec`s `sleep 30` in-place so the
        // PID file is always complete before the 1.5s deadline fires.
        let inner = "echo $$ > \"$1.tmp\" && mv \"$1.tmp\" \"$1\" && exec sleep 30";
        let script = format!("/bin/sh -c '{inner}' _ {:?} & wait", pid_file.to_str().unwrap(),);
        let inv = Invocation::new("/bin/sh", &["-c", &script]).env("PATH", "/usr/bin:/bin");
        let outcome = case.run(&inv).unwrap();
        assert!(matches!(outcome.termination, Termination::TimedOut(_)));
        let pid_text = fs::read_to_string(&pid_file)
            .expect("grandchild pid file must be published before timeout");
        let gpid: i32 = pid_text.trim().parse().expect("valid grandchild pid");
        assert!(gpid > 0, "unexpected grandchild pid {gpid}");
        // SAFETY: probing PID liveness with signal 0.
        let alive = unsafe { libc::kill(gpid, 0) };
        assert_eq!(alive, -1, "grandchild {gpid} survived case timeout");
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(libc::ESRCH));
    }
}
