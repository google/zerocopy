// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Regressions for case ownership, evidence export, and command replay.

mod support;

use std::fs;
use std::io::{ErrorKind, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use serde_json::Value;
use support::{Invocation, RunDirectory, Termination, select_cases};
use wait_timeout::ChildExt;

fn run_directory() -> RunDirectory {
    RunDirectory::new("support-regression", Duration::from_secs(10)).unwrap()
}

// Python is required for replay tests. Resolve it through the caller's PATH,
// then pass the absolute interpreter path to the isolated process runner.
fn python() -> PathBuf {
    let output = Command::new("python3")
        .args(["-c", "import json, sys; print(json.dumps(sys.executable))"])
        .output()
        .expect("Python 3 must be available on PATH for replay tests");
    assert!(output.status.success());
    let path = PathBuf::from(serde_json::from_slice::<String>(&output.stdout).unwrap());
    assert!(path.is_absolute());
    path
}

fn replay(python: &Path, script: &Path, input: &[u8]) -> Output {
    let mut child = Command::new(python)
        .arg(script)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // The wrapper never consumes stdin and may close its read end before
    // this write. A closed pipe is harmless; other write failures are errors.
    if let Err(error) = child.stdin.take().unwrap().write_all(input) {
        assert_eq!(
            error.kind(),
            ErrorKind::BrokenPipe,
            "write replay stdin: {error}"
        );
    }
    if child
        .wait_timeout(Duration::from_secs(10))
        .unwrap()
        .is_none()
    {
        child.kill().unwrap();
        child.wait().unwrap();
        panic!("replay exceeded the test's outer deadline");
    }
    child.wait_with_output().unwrap()
}

#[test]
fn overlapping_names_are_rejected_before_any_case_runs() {
    for invalid in ["", ".", "..", "a/b", "a/", "a/.", "/absolute"] {
        assert!(select_cases(&["a", invalid], Some("a")).is_err());
        let run = run_directory();
        let calls = AtomicUsize::new(0);
        assert!(
            run.run_cases(&["a", invalid], 2, |_, _| {
                calls.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
            .is_err()
        );
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert!(!run.path().join("cases").exists());
        assert!(run.case(invalid).is_err());
        assert!(!run.path().join("cases").exists());
    }

    let run = run_directory();
    assert!(run.run_cases(&["same", "same"], 2, |_, _| Ok(())).is_err());
    assert!(!run.path().join("cases").exists());

    let fixture = tempfile::tempdir().unwrap();
    fs::create_dir(fixture.path().join("nested")).unwrap();
    fs::write(fixture.path().join("nested/run.json"), b"fixture").unwrap();
    let case = run.case(".case with spaces").unwrap();
    case.copy(fixture.path(), "input/tree").unwrap();
    case.write("input/generated/deep.rs", b"generated").unwrap();
    assert_eq!(
        fs::read(case.path().join("input/tree/nested/run.json")).unwrap(),
        b"fixture"
    );
    assert_eq!(
        fs::read(case.path().join("input/generated/deep.rs")).unwrap(),
        b"generated"
    );
}

#[test]
fn case_creation_failure_prevents_every_case_body() {
    for jobs in [1, 2] {
        let run = run_directory();
        let existing = run.case("blocked").unwrap();
        existing.write("sentinel", b"keep").unwrap();
        let calls = AtomicUsize::new(0);
        let error = run
            .run_cases(&["first", "blocked"], jobs, |_, _| {
                calls.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
            .unwrap_err();
        assert!(error.contains(existing.path().to_str().unwrap()), "{error}");
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(fs::read(existing.path().join("sentinel")).unwrap(), b"keep");
    }
}

#[test]
fn case_names_follow_the_host_filesystems_alias_rules() {
    let run = run_directory();
    fs::create_dir(run.path().join("case-fold-probe")).unwrap();
    let folds_case = run.path().join("CASE-FOLD-PROBE").exists();
    let calls = AtomicUsize::new(0);
    let result = run.run_cases(&["foo", "FOO"], 2, |name, case| {
        calls.fetch_add(1, Ordering::SeqCst);
        case.write("value", name.as_bytes())
    });
    if folds_case {
        assert!(result.is_err());
        assert_eq!(calls.load(Ordering::SeqCst), 0);
    } else {
        result.unwrap();
        assert_eq!(calls.load(Ordering::SeqCst), 2);
        for name in ["foo", "FOO"] {
            assert_eq!(
                fs::read(run.path().join("cases").join(name).join("value")).unwrap(),
                name.as_bytes()
            );
        }
    }
}

#[test]
fn replay_tolerates_a_wrapper_that_closes_stdin() {
    let fixture = tempfile::tempdir().unwrap();
    let script = fixture.path().join("close-stdin.py");
    fs::write(&script, b"import os\nos.close(0)\nprint('stdin closed')\n").unwrap();
    let output = replay(&python(), &script, &vec![b'x'; 1024 * 1024]);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(output.stdout, b"stdin closed\n");
}

#[cfg(unix)]
#[test]
fn relative_tmpdir_records_absolute_paths_and_replays_moved_evidence() {
    let fixture = tempfile::tempdir().unwrap();
    fs::create_dir(fixture.path().join("actual-temp")).unwrap();
    std::os::unix::fs::symlink("actual-temp", fixture.path().join("relative-temp")).unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "relative_tmpdir_child_fixture",
            "--ignored",
            "--nocapture",
        ])
        .env("TMPDIR", "relative-temp")
        .env("ANNEAL_SUPPORT_PYTHON", python())
        .current_dir(fixture.path())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    if child
        .wait_timeout(Duration::from_secs(10))
        .unwrap()
        .is_none()
    {
        child.kill().unwrap();
        child.wait().unwrap();
        panic!("relative TMPDIR fixture exceeded the test's outer deadline");
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
}

// Run in a subprocess so TMPDIR and the working directory cannot affect other
// test threads. Unix temp_dir uses TMPDIR without requiring an absolute path.
#[cfg(unix)]
#[test]
#[ignore = "internal subprocess fixture"]
fn relative_tmpdir_child_fixture() {
    assert_eq!(std::env::temp_dir(), Path::new("relative-temp"));
    let python = PathBuf::from(std::env::var_os("ANNEAL_SUPPORT_PYTHON").unwrap());
    let run = run_directory();
    let root = run.path().to_path_buf();
    assert!(root.is_absolute(), "{}", root.display());
    assert_eq!(root, fs::canonicalize(&root).unwrap());
    let mut case = run.case("relative-temp").unwrap();
    case.write("input/value", b"owned input").unwrap();
    let input = case.path().join("input/value");
    let invocation = Invocation::new(
        &python,
        &[
            "-c",
            "import os, pathlib, sys; print(pathlib.Path(sys.argv[1]).read_text()); print(os.getcwd())",
            input.to_str().unwrap(),
        ],
    );
    case.run(&invocation).unwrap().expect_code(0).unwrap();
    let recorded: Value = serde_json::from_slice(
        &fs::read(case.path().join("commands/0000/invocation.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(recorded["original_run_root"], root.to_str().unwrap());
    assert_eq!(recorded["working_directory"], case.path().to_str().unwrap());
    assert_eq!(recorded["arguments"][2], input.to_str().unwrap());
    let metadata: Value =
        serde_json::from_slice(&fs::read(root.join("run.json")).unwrap()).unwrap();
    assert_eq!(metadata["original_run_root"], root.to_str().unwrap());

    let cwd = std::env::current_dir().unwrap();
    let diagnostics = cwd.join("diagnostics");
    let error = run
        .finish(
            Err("retain relative TMPDIR replay".into()),
            Some(&diagnostics),
        )
        .unwrap_err();
    assert!(error.contains("evidence exported to"), "{error}");
    let moved = cwd.join("moved evidence");
    fs::rename(diagnostics.join(root.file_name().unwrap()), &moved).unwrap();
    fs::remove_dir_all(root).unwrap();
    let output = replay(
        &python,
        &moved.join("cases/relative-temp/commands/0000/reproduce.py"),
        b"",
    );
    assert!(output.status.success(), "{output:?}");
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!(
            "owned input\n{}\n",
            moved.join("cases/relative-temp").display()
        )
    );
}

fn assert_rejected_export(run: RunDirectory, destination: &Path) {
    let root = run.path().to_path_buf();
    let export = destination.join(root.file_name().unwrap());
    let error = run
        .finish(Err("original case failure".into()), Some(destination))
        .unwrap_err();
    assert!(error.starts_with("original case failure"));
    assert!(error.contains("retention export incomplete"));
    assert!(error.contains("disjoint from the retained run"));
    assert!(!export.exists());
    assert_eq!(
        fs::read_to_string(root.join("failure.txt")).unwrap(),
        "original case failure"
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn diagnostic_exports_cannot_recurse_into_the_retained_run() {
    let run = run_directory();
    let root = run.path().to_path_buf();
    assert_rejected_export(run, &root);

    let run = run_directory();
    let destination = run.path().join("new/deep/diagnostics");
    assert_rejected_export(run, &destination);

    let run = run_directory();
    let destination = run.path().join("missing/../diagnostics");
    assert_rejected_export(run, &destination);
}

#[cfg(unix)]
#[test]
fn diagnostic_export_checks_resolve_directory_aliases() {
    let aliases = tempfile::tempdir().unwrap();
    let run = run_directory();
    let alias = aliases.path().join("retained-alias");
    std::os::unix::fs::symlink(run.path(), &alias).unwrap();
    assert_rejected_export(run, &alias.join("new/deep"));

    let run = run_directory();
    let alias = aliases.path().join("existing-export-alias");
    fs::create_dir(&alias).unwrap();
    std::os::unix::fs::symlink(run.path(), alias.join(run.path().file_name().unwrap())).unwrap();
    let root = run.path().to_path_buf();
    let error = run
        .finish(Err("original".into()), Some(&alias))
        .unwrap_err();
    assert!(error.starts_with("original"));
    assert!(error.contains("disjoint from the retained run"));
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn moved_replay_relocates_owned_paths_and_preserves_literal_values() {
    let python = python();
    let run = run_directory();
    let root = run.path().to_path_buf();
    let mut case = run.case("replay").unwrap();
    case.write("run.json", b"legitimate case fixture").unwrap();
    case.write("input/tree/value", b"owned input").unwrap();
    case.write(
        "inspect.py",
        br#"import json, os, pathlib, sys
print(json.dumps({
    'arguments': sys.argv[1:],
    'environment': dict(os.environ),
    'cwd': os.getcwd(),
    'input': pathlib.Path(sys.argv[1]).read_text(),
    'stdin': sys.stdin.read(),
}))
"#,
    )
    .unwrap();
    let script = case.path().join("inspect.py");
    let input = case.path().join("input/tree/value");
    let sibling = format!("{}-archive/value", root.display());
    let literal = format!("prefix {} suffix", input.display());
    let option = format!("--literal={}", input.display());
    let trailing = format!(
        "{}{}",
        case.path().join("input/tree").display(),
        std::path::MAIN_SEPARATOR
    );
    let repeated = format!("{trailing}{}", std::path::MAIN_SEPARATOR);
    let mut invocation = Invocation::new(
        &python,
        &[
            script.to_str().unwrap(),
            input.to_str().unwrap(),
            &sibling,
            &literal,
            &option,
            root.to_str().unwrap(),
            &trailing,
            &repeated,
        ],
    );
    invocation
        .environment
        .insert("OWNED".into(), input.display().to_string());
    invocation
        .environment
        .insert("SIBLING".into(), sibling.clone());
    invocation
        .environment
        .insert("LITERAL".into(), literal.clone());
    invocation
        .environment
        .insert("OWNED_DIRECTORY".into(), trailing.clone());
    let outcome = case.run(&invocation).unwrap();
    outcome.expect_code(0).unwrap();
    let original: Value = serde_json::from_slice(&outcome.stdout).unwrap();
    assert_eq!(original["stdin"], "");
    assert_eq!(original["arguments"][5], trailing);
    assert_eq!(original["arguments"][6], repeated);

    let diagnostics = tempfile::tempdir().unwrap();
    let error = run
        .finish(Err("retain replay".into()), Some(diagnostics.path()))
        .unwrap_err();
    assert!(error.contains("evidence exported to"));
    let exported = diagnostics.path().join(root.file_name().unwrap());
    let moved = diagnostics.path().join("moved evidence");
    fs::rename(exported, &moved).unwrap();
    fs::remove_dir_all(&root).unwrap();

    let output = replay(
        &python,
        &moved.join("cases/replay/commands/0000/reproduce.py"),
        b"interactive input must not reach the replayed child",
    );
    assert!(output.status.success(), "{output:?}");
    let observed: Value = serde_json::from_slice(&output.stdout).unwrap();
    let moved_input = moved.join("cases/replay/input/tree/value");
    assert_eq!(observed["arguments"][0], moved_input.to_str().unwrap());
    assert_eq!(observed["arguments"][1], sibling);
    assert_eq!(observed["arguments"][2], literal);
    assert_eq!(observed["arguments"][3], option);
    assert_eq!(observed["arguments"][4], moved.to_str().unwrap());
    let moved_directory = format!(
        "{}{}",
        moved.join("cases/replay/input/tree").display(),
        std::path::MAIN_SEPARATOR
    );
    assert_eq!(observed["arguments"][5], moved_directory);
    assert_eq!(
        observed["arguments"][6],
        format!("{moved_directory}{}", std::path::MAIN_SEPARATOR)
    );
    assert_eq!(observed["environment"]["OWNED_DIRECTORY"], moved_directory);
    assert_eq!(
        observed["environment"]["OWNED"],
        moved_input.to_str().unwrap()
    );
    assert_eq!(observed["environment"]["SIBLING"], sibling);
    assert_eq!(observed["environment"]["LITERAL"], literal);
    assert_eq!(
        observed["cwd"],
        moved.join("cases/replay").to_str().unwrap()
    );
    assert_eq!(observed["input"], "owned input");
    assert_eq!(observed["stdin"], "");
}

#[test]
fn replay_preserves_an_external_executable_with_a_similar_prefix() {
    let python = python();
    let run = run_directory();
    let root = run.path().to_path_buf();
    let mut case = run.case("missing").unwrap();
    let missing = PathBuf::from(format!("{}-archive/missing", root.display()));
    let outcome = case.run(&Invocation::new(&missing, &[])).unwrap();
    assert!(matches!(outcome.termination, Termination::LaunchFailed(_)));
    let diagnostics = tempfile::tempdir().unwrap();
    let error = run
        .finish(
            Err("retain launch failure".into()),
            Some(diagnostics.path()),
        )
        .unwrap_err();
    assert!(error.contains("evidence exported to"));
    fs::remove_dir_all(&root).unwrap();
    let output = replay(
        &python,
        &diagnostics
            .path()
            .join(root.file_name().unwrap())
            .join("cases/missing/commands/0000/reproduce.py"),
        b"",
    );
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains(missing.to_str().unwrap()));
}

#[test]
fn replay_reapplies_the_recorded_process_deadline() {
    let python = python();
    let run = RunDirectory::new("replay-timeout", Duration::from_millis(200)).unwrap();
    let mut case = run.case("timeout").unwrap();
    let outcome = case
        .run(&Invocation::new(
            &python,
            &["-c", "import time; time.sleep(3)"],
        ))
        .unwrap();
    assert!(matches!(outcome.termination, Termination::TimedOut(_)));
    let metadata: Value =
        serde_json::from_slice(&fs::read(case.path().join("commands/0000/outcome.json")).unwrap())
            .unwrap();
    assert_eq!(metadata["kind"], "timed_out");
    let output = replay(
        &python,
        &case.path().join("commands/0000/reproduce.py"),
        b"",
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(124), "replay stderr: {stderr}");
    assert!(
        stderr.contains("process timed out after 0.2 seconds"),
        "replay stderr: {stderr}"
    );

    // Some Python versions put a remaining wait interval in TimeoutExpired.
    // Force a different interval to keep the diagnostic version-independent.
    case.write(
        "remaining-timeout.py",
        br#"import pathlib, runpy, subprocess

def remaining_timeout(*args, **kwargs):
    raise subprocess.TimeoutExpired(args[0], kwargs['timeout'] / 2)

subprocess.run = remaining_timeout
script = pathlib.Path(__file__).parent / 'commands/0000/reproduce.py'
runpy.run_path(str(script), run_name='__main__')
"#,
    )
    .unwrap();
    let output = replay(&python, &case.path().join("remaining-timeout.py"), b"");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(124), "replay stderr: {stderr}");
    assert!(
        stderr.contains("process timed out after 0.2 seconds"),
        "replay stderr: {stderr}"
    );
}

// A subprocess sets umask without changing shared state for other tests.
// A public diagnostics parent must not make private runs public.
#[cfg(unix)]
#[test]
fn exported_evidence_remains_private_under_a_permissive_umask() {
    let mut child = Command::new("/bin/sh")
        .args(["-c", "umask 022; exec \"$@\"", "evidence-permissions"])
        .arg(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "export_permissions_child_fixture",
            "--ignored",
            "--nocapture",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    if child
        .wait_timeout(Duration::from_secs(10))
        .unwrap()
        .is_none()
    {
        child.kill().unwrap();
        child.wait().unwrap();
        panic!("evidence permissions fixture exceeded its outer deadline");
    }
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stdout)
            .contains("test export_permissions_child_fixture ... ok"),
        "fixture did not run: {output:?}"
    );
}

#[cfg(unix)]
#[test]
#[ignore = "internal umask subprocess fixture"]
fn export_permissions_child_fixture() {
    use std::os::unix::fs::PermissionsExt;

    let run = run_directory();
    let root = run.path().to_path_buf();
    let initial_mode = fs::metadata(&root).unwrap().permissions().mode() & 0o777;
    // Restrict the retained run explicitly so export privacy is independent
    // of allocator defaults. Check the initial allocation mode below as well.
    fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
    let case = run.case("private-input").unwrap();
    let bytes = b"private fixture\xff\0";
    fs::write(case.path().join("sensitive"), bytes).unwrap();
    let diagnostics = tempfile::tempdir().unwrap();
    fs::set_permissions(diagnostics.path(), fs::Permissions::from_mode(0o755)).unwrap();
    let error = run
        .finish(
            Err("original command failure".into()),
            Some(diagnostics.path()),
        )
        .unwrap_err();
    assert!(error.starts_with("original command failure"), "{error}");
    assert!(error.contains("evidence exported to"), "{error}");
    let exported = diagnostics.path().join(root.file_name().unwrap());
    assert_eq!(
        fs::metadata(&exported).unwrap().permissions().mode() & 0o777,
        0o700
    );
    assert_eq!(
        initial_mode, 0o700,
        "new run exposed evidence before export"
    );
    assert_eq!(
        fs::metadata(diagnostics.path())
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o755
    );
    assert_eq!(
        fs::read(exported.join("cases/private-input/sensitive")).unwrap(),
        bytes
    );
    assert_eq!(
        fs::read(root.join("cases/private-input/sensitive")).unwrap(),
        bytes
    );
    fs::remove_dir_all(root).unwrap();
}

#[cfg(unix)]
#[test]
fn diagnostic_export_tightens_only_its_existing_run_root() {
    use std::os::unix::fs::PermissionsExt;

    let run = run_directory();
    let root = run.path().to_path_buf();
    let diagnostics = tempfile::tempdir().unwrap();
    fs::set_permissions(diagnostics.path(), fs::Permissions::from_mode(0o755)).unwrap();
    let existing = diagnostics.path().join(root.file_name().unwrap());
    fs::create_dir(&existing).unwrap();
    fs::set_permissions(&existing, fs::Permissions::from_mode(0o755)).unwrap();
    let outside = tempfile::NamedTempFile::new().unwrap();
    fs::write(outside.path(), b"unrelated existing evidence").unwrap();
    fs::hard_link(outside.path(), existing.join("sentinel")).unwrap();
    let outside_permissions = fs::metadata(outside.path()).unwrap().permissions();

    let error = run
        .finish(
            Err("original command failure".into()),
            Some(diagnostics.path()),
        )
        .unwrap_err();

    assert!(error.starts_with("original command failure"), "{error}");
    assert!(error.contains("evidence exported to"), "{error}");
    assert_eq!(
        fs::read(existing.join("sentinel")).unwrap(),
        b"unrelated existing evidence"
    );
    assert_eq!(
        fs::read(outside.path()).unwrap(),
        b"unrelated existing evidence"
    );
    assert_eq!(
        fs::metadata(outside.path()).unwrap().permissions(),
        outside_permissions
    );
    assert_eq!(
        fs::read(existing.join("failure.txt")).unwrap(),
        b"original command failure"
    );
    assert_eq!(
        fs::metadata(&existing).unwrap().permissions().mode() & 0o777,
        0o700
    );
    assert_eq!(
        fs::metadata(diagnostics.path())
            .unwrap()
            .permissions()
            .mode()
            & 0o777,
        0o755
    );
    fs::remove_dir_all(root).unwrap();
}
