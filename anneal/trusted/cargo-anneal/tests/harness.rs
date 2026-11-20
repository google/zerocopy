// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Exercises runner failures without requiring installed Rust or Lean tools.

mod support;

use std::fs;
use std::io::Write;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use support::{Invocation, RunDirectory, Termination, select_cases};

fn run_directory() -> RunDirectory {
    RunDirectory::new("runner-test-revision", Duration::from_secs(10)).unwrap()
}

fn helper(mode: &str) -> Invocation {
    let mut invocation = Invocation::new(
        std::env::current_exe().unwrap(),
        &["--exact", "child_fixture", "--ignored", "--nocapture"],
    );
    invocation
        .environment
        .insert("ANNEAL_CHILD_FIXTURE".into(), mode.into());
    invocation
}

// This is a subprocess fixture, invoked explicitly by the runner tests. It
// exits directly so the test runner cannot convert its exit code or raw bytes.
#[test]
#[ignore = "internal subprocess fixture"]
fn child_fixture() {
    match std::env::var("ANNEAL_CHILD_FIXTURE").unwrap().as_str() {
        "failure" => {
            std::io::stdout().write_all(b"raw stdout\xff\n").unwrap();
            std::io::stderr().write_all(b"raw stderr\xfe\n").unwrap();
            std::process::exit(23);
        }
        "retention-failure" => {
            fs::create_dir("commands/0000/outcome.json").unwrap();
            std::process::exit(23);
        }
        "environment" => {
            assert_eq!(std::env::var("KEPT").unwrap(), "yes");
            assert!(std::env::var_os("HOME").is_none());
            assert!(std::env::var_os("RUSTC_WRAPPER").is_none());
            assert!(std::env::args().any(|arg| arg == "argument with spaces"));
            assert_eq!(
                fs::read("input/argument with spaces").unwrap(),
                b"case input"
            );
            println!("cwd={}", std::env::current_dir().unwrap().display());
        }
        "slow" => {
            eprintln!("slow child started");
            std::thread::sleep(Duration::from_secs(60));
        }
        mode => panic!("unknown child fixture {mode}"),
    }
}

#[test]
fn discovery_selection_and_empty_selection_are_explicit() {
    let names = ["zeta", "alpha", "beta"];
    let first = select_cases(&names, None).unwrap();
    assert_eq!(first, ["alpha", "beta", "zeta"]);
    assert_eq!(first, select_cases(&names, None).unwrap());
    assert_eq!(select_cases(&names, Some("beta")).unwrap(), ["beta"]);
    let error = select_cases(&names, Some("absent")).unwrap_err();
    assert!(error.contains("absent") && error.contains("alpha, beta, zeta"));
    assert!(select_cases(&[], None).is_err());
    assert!(select_cases(&["same", "same"], None).is_err());

    let run = run_directory();
    let selected = select_cases(&names, Some("beta")).unwrap();
    run.run_cases(&selected, 2, |name, case| {
        assert_eq!(name, "beta");
        case.write("ran", b"beta")
    })
    .unwrap();
    assert!(run.path().join("cases/beta/ran").is_file());
    assert!(!run.path().join("cases/alpha").exists());
}

#[test]
fn workers_bound_concurrency_and_keep_case_directories_distinct() {
    let run = run_directory();
    let active = AtomicUsize::new(0);
    let peak = AtomicUsize::new(0);
    let names = select_cases(&["four", "three", "two", "one"], None).unwrap();
    run.run_cases(&names, 2, |name, case| {
        let current = active.fetch_add(1, Ordering::SeqCst) + 1;
        peak.fetch_max(current, Ordering::SeqCst);
        case.write("generated", name.as_bytes())?;
        std::thread::sleep(Duration::from_millis(30));
        active.fetch_sub(1, Ordering::SeqCst);
        Ok(())
    })
    .unwrap();
    assert!((1..=2).contains(&peak.load(Ordering::SeqCst)));
    for name in names {
        assert_eq!(
            fs::read(run.path().join("cases").join(name).join("generated")).unwrap(),
            name.as_bytes()
        );
    }
    assert!(run.run_cases(&["unused"], 0, |_, _| Ok(())).is_err());
}

#[test]
fn fixture_staging_and_cleanup_are_owned_and_errors_are_visible() {
    let fixture = tempfile::tempdir().unwrap();
    fs::create_dir(fixture.path().join("nested")).unwrap();
    fs::write(fixture.path().join("first"), b"one").unwrap();
    fs::write(fixture.path().join("nested/second"), b"two").unwrap();
    let sentinel = fixture.path().join("sentinel");
    fs::write(&sentinel, b"keep").unwrap();
    let run = run_directory();
    let root = run.path().to_path_buf();
    let case = run.case("stage").unwrap();
    case.copy(fixture.path(), "fixture").unwrap();
    case.write("fixture/generated", b"three").unwrap();
    assert_eq!(
        fs::read(case.path().join("fixture/nested/second")).unwrap(),
        b"two"
    );
    assert!(
        case.copy(&fixture.path().join("missing"), "missing")
            .unwrap_err()
            .contains("inspect")
    );
    assert!(
        case.write("fixture/first/blocked", b"x")
            .unwrap_err()
            .contains("create parent")
    );
    assert!(case.write("../escape", b"x").is_err());
    drop(run);
    assert!(!root.exists());
    assert_eq!(fs::read(&sentinel).unwrap(), b"keep");
}

#[test]
fn runner_preserves_launch_failures_and_raw_child_output() {
    let run = run_directory();
    let mut case = run.case("failure").unwrap();
    case.write("generated.input", b"retained input").unwrap();
    let out = case.run(&helper("failure")).unwrap();
    assert!(out.expect_code(23).is_ok());
    assert!(out.stdout.ends_with(b"raw stdout\xff\n"));
    assert!(out.stderr.ends_with(b"raw stderr\xfe\n"));
    let missing = case.path().join("missing-executable");
    let mut invocation = Invocation::new(&missing, &["--version"]);
    invocation
        .environment
        .insert("PATH".into(), "/bin:/usr/bin".into());
    let out = case.run(&invocation).unwrap();
    assert!(matches!(out.termination, Termination::LaunchFailed(_)));
    assert!(out.expect_code(0).is_err());
    assert!(out.describe().contains(missing.to_str().unwrap()));
    case.write("unusable-executable", b"not an executable")
        .unwrap();
    let unusable = case.path().join("unusable-executable");
    let out = case.run(&Invocation::new(&unusable, &[])).unwrap();
    assert!(matches!(out.termination, Termination::LaunchFailed(_)));

    let root = run.path().to_path_buf();
    let export = tempfile::tempdir().unwrap();
    let error = run
        .finish(Err("original assertion failed".into()), Some(export.path()))
        .unwrap_err();
    assert!(error.contains("original assertion failed"));
    let evidence = root.join("cases/failure");
    assert_eq!(
        fs::read(evidence.join("generated.input")).unwrap(),
        b"retained input"
    );
    assert!(
        fs::read(evidence.join("commands/0000/stdout"))
            .unwrap()
            .ends_with(b"\xff\n")
    );
    let launch: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("commands/0001/outcome.json")).unwrap())
            .unwrap();
    assert_eq!(launch["kind"], "launch_failed");
    let invocation: serde_json::Value =
        serde_json::from_slice(&fs::read(evidence.join("commands/0001/invocation.json")).unwrap())
            .unwrap();
    assert_eq!(invocation["executable"], missing.to_str().unwrap());
    assert!(evidence.join("commands/0000/reproduce.py").is_file());
    assert!(
        fs::read_to_string(root.join("run.json"))
            .unwrap()
            .contains("runner-test-revision")
    );
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn requested_environment_and_working_directory_reach_the_child() {
    let run = run_directory();
    let mut case = run.case("environment").unwrap();
    case.write("input/argument with spaces", b"case input")
        .unwrap();
    let mut invocation = helper("environment");
    invocation
        .arguments
        .extend(["--skip".into(), "argument with spaces".into()]);
    invocation.environment.insert("KEPT".into(), "yes".into());
    let out = case.run(&invocation).unwrap();
    out.expect_code(0).unwrap();
    assert!(String::from_utf8_lossy(&out.stdout).contains(case.path().to_str().unwrap()));
    let replay = case.path().join("commands/0000/reproduce.py");
    // The runner requires absolute tool paths and clears PATH. Ask the Python
    // on the test process's PATH for its executable before entering the runner.
    let python = Command::new("python3")
        .args(["-c", "import json, sys; print(json.dumps(sys.executable))"])
        .output()
        .expect("Python 3 must be available on PATH to test replay");
    assert!(
        python.status.success(),
        "resolve Python 3: {}",
        String::from_utf8_lossy(&python.stderr)
    );
    let python: String = serde_json::from_slice(&python.stdout).unwrap();
    let out = case
        .run(&Invocation::new(python, &[replay.to_str().unwrap()]))
        .unwrap();
    out.expect_code(0).unwrap();
    assert!(String::from_utf8_lossy(&out.stderr).contains("runner-test-revision"));
    assert!(
        case.run(&Invocation::new("relative-tool", &[]))
            .unwrap_err()
            .contains("absolute")
    );
}

#[test]
fn timeout_fails_visibly_and_retains_available_output() {
    let run = RunDirectory::new("timeout-test", Duration::from_millis(150)).unwrap();
    let mut case = run.case("timeout").unwrap();
    let started = Instant::now();
    let out = case.run(&helper("slow")).unwrap();
    assert!(matches!(out.termination, Termination::TimedOut(_)));
    assert!(out.expect_code(0).is_err());
    // The deadline may expire before libtest reaches child_fixture. Preserve
    // whatever each stream received, including an empty stream.
    let logs = case.path().join("commands/0000");
    assert_eq!(out.stdout, fs::read(logs.join("stdout")).unwrap());
    assert_eq!(out.stderr, fs::read(logs.join("stderr")).unwrap());
    let outcome: serde_json::Value =
        serde_json::from_slice(&fs::read(logs.join("outcome.json")).unwrap()).unwrap();
    assert_eq!(outcome["kind"], "timed_out");
    assert!(started.elapsed() < Duration::from_secs(5));
}

#[test]
fn retention_failure_does_not_hide_the_original_failure() {
    let run = run_directory();
    let root = run.path().to_path_buf();
    let mut case = run.case("retention").unwrap();
    // The child creates the obstruction after the runner allocates fresh
    // logs, so the process outcome still precedes the evidence-write failure.
    let failure = case.run(&helper("retention-failure")).unwrap_err();
    assert!(failure.contains("child exited") && failure.contains("23"));
    assert!(failure.contains("retain process outcome"));
    let destination = tempfile::NamedTempFile::new().unwrap();
    let error = run
        .finish(Err(failure), Some(destination.path()))
        .unwrap_err();
    assert!(error.contains("child exited") && error.contains("23"));
    assert!(error.contains("retention export incomplete"));
    assert!(root.join("failure.txt").exists());
    fs::remove_dir_all(root).unwrap();
}
