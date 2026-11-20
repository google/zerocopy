// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Checks native signal termination through the runner and command replay.

#![cfg(unix)]

mod support;

use std::fs;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::Duration;

use serde_json::Value;
use support::{Invocation, RunDirectory, Termination};
use wait_timeout::ChildExt;

fn python() -> PathBuf {
    let output = Command::new("python3")
        .args(["-c", "import json, sys; print(json.dumps(sys.executable))"])
        .output()
        .expect("Python 3 must be available on PATH for replay tests");
    assert!(output.status.success(), "{output:?}");
    let path = PathBuf::from(serde_json::from_slice::<String>(&output.stdout).unwrap());
    assert!(path.is_absolute());
    path
}

fn replay(python: &Path, script: &Path, block_termination: bool) -> Output {
    let mut command = Command::new(python);
    if block_termination {
        command.args([
            "-c",
            "import runpy, signal, sys; signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM}); runpy.run_path(sys.argv[1], run_name='__main__')",
        ]);
    }
    let mut child = command
        .arg(script)
        .stdin(Stdio::null())
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
        panic!("signal replay exceeded the test's outer deadline");
    }
    child.wait_with_output().unwrap()
}

const SIGNAL_CHILD: &str = r#"import os, signal, sys
signum = getattr(signal, sys.argv[1])
if signum not in (signal.SIGKILL, signal.SIGSTOP):
    signal.signal(signum, signal.SIG_DFL)
signal.pthread_sigmask(signal.SIG_UNBLOCK, {signum})
os.kill(os.getpid(), signum)
"#;

fn check_signal(name: &str, block_replay_termination: bool) {
    let python = python();
    let run = RunDirectory::new("signal-replay", Duration::from_secs(5)).unwrap();
    let mut case = run.case(name).unwrap();
    let outcome = case
        .run(&Invocation::new(&python, &["-c", SIGNAL_CHILD, name]))
        .unwrap();
    let Termination::Exited(status) = outcome.termination else {
        panic!("expected native signal outcome: {outcome:?}");
    };
    let signum = status.signal().expect("child must terminate by signal");
    let metadata: Value =
        serde_json::from_slice(&fs::read(case.path().join("commands/0000/outcome.json")).unwrap())
            .unwrap();
    assert_eq!(metadata["kind"], "exited");
    assert!(metadata["code"].is_null());
    assert_eq!(metadata["status"], status.to_string());

    let output = replay(
        &python,
        &case.path().join("commands/0000/reproduce.py"),
        block_replay_termination,
    );
    assert_eq!(output.status.signal(), Some(signum), "{output:?}");
    assert_eq!(output.status.code(), None, "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains(&format!("process terminated by signal {signum}")),
        "{output:?}"
    );
}

#[test]
fn replay_preserves_termination_kill_and_python_ignored_signals() {
    for name in ["SIGTERM", "SIGKILL", "SIGPIPE"] {
        check_signal(name, false);
    }
}

#[test]
fn replay_unblocks_the_reproduced_termination_signal() {
    check_signal("SIGTERM", true);
}

#[test]
fn replay_keeps_ordinary_exit_codes() {
    let python = python();
    let run = RunDirectory::new("exit-code-replay", Duration::from_secs(5)).unwrap();
    let mut case = run.case("exit-code").unwrap();
    let outcome = case
        .run(&Invocation::new(
            &python,
            &["-c", "import sys; sys.exit(23)"],
        ))
        .unwrap();
    outcome.expect_code(23).unwrap();
    let output = replay(
        &python,
        &case.path().join("commands/0000/reproduce.py"),
        false,
    );
    assert_eq!(output.status.code(), Some(23), "{output:?}");
    assert_eq!(output.status.signal(), None, "{output:?}");
}
