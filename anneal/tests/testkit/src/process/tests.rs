// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

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
