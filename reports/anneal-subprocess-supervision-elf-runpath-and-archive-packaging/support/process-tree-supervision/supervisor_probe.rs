// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Empirical probe comparing Linux subprocess-tree supervision, termination,
//! and reaping mechanisms:
//! - Strategy A: Direct-child `child.kill()` + `child.wait()` (`wait_timeout` pattern)
//! - Strategy B: `CommandExt::process_group(0)` + `kill(-pgid, SIGKILL)` + `-pgid` poll
//! - Strategy C1: `PR_SET_CHILD_SUBREAPER` + `PR_SET_PDEATHSIG(SIGKILL)` on direct child
//! - Strategy C2: `PR_SET_PDEATHSIG(SIGKILL)` on grandchild when parent exits early
//! - Strategy D: Combined `PR_SET_CHILD_SUBREAPER` + `process_group(0)` + `kill(-pgid, SIGKILL)` + `waitpid(-pgid)` until `ECHILD`

use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::unix::io::AsRawFd;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

unsafe extern "C" {
    fn kill(pid: i32, sig: i32) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn prctl(option: i32, arg2: usize, arg3: usize, arg4: usize, arg5: usize) -> i32;
    fn flock(fd: i32, operation: i32) -> i32;
    fn getpid() -> i32;
    fn __errno_location() -> *mut i32;
}

const SIGKILL: i32 = 9;
const ESRCH: i32 = 3;
const ECHILD: i32 = 10;
const WNOHANG: i32 = 1;
const LOCK_EX: i32 = 2;
const LOCK_NB: i32 = 4;
const LOCK_UN: i32 = 8;
const PR_SET_PDEATHSIG: i32 = 1;
const PR_SET_CHILD_SUBREAPER: i32 = 36;

fn errno() -> i32 {
    unsafe { *__errno_location() }
}

fn is_pid_alive(pid: i32) -> bool {
    let rc = unsafe { kill(pid, 0) };
    if rc == 0 {
        // Also check that it is not a zombie (`State: Z` in `/proc/<pid>/status`).
        if let Ok(status) = fs::read_to_string(format!("/proc/{pid}/status")) {
            for line in status.lines() {
                if line.starts_with("State:") && line.contains('Z') {
                    return false;
                }
            }
        }
        true
    } else {
        errno() != ESRCH
    }
}

fn read_ppid(pid: i32) -> Option<i32> {
    let status = fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("PPid:") {
            return rest.trim().parse::<i32>().ok();
        }
    }
    None
}

fn is_file_locked(path: &Path) -> bool {
    let Ok(f) = OpenOptions::new().read(true).write(true).open(path) else {
        return false;
    };
    let rc = unsafe { flock(f.as_raw_fd(), LOCK_EX | LOCK_NB) };
    if rc == 0 {
        unsafe {
            flock(f.as_raw_fd(), LOCK_UN);
        }
        false
    } else {
        true
    }
}

fn worker_grandchild(lock_path: &Path, ready_path: &Path, set_pdeathsig: bool) {
    if set_pdeathsig {
        unsafe {
            prctl(PR_SET_PDEATHSIG, SIGKILL as usize, 0, 0, 0);
        }
    }
    let lock_file = OpenOptions::new()
        .create(true)
        .read(true)
        .write(true)
        .truncate(true)
        .open(lock_path)
        .expect("open lock file");
    let rc = unsafe { flock(lock_file.as_raw_fd(), LOCK_EX | LOCK_NB) };
    assert_eq!(rc, 0, "grandchild failed to acquire exclusive flock");

    let pid = unsafe { getpid() };
    let tmp = ready_path.with_extension("tmp");
    {
        let mut f = File::create(&tmp).expect("create ready tmp");
        write!(f, "{pid}").expect("write pid");
        f.sync_all().expect("sync ready tmp");
    }
    fs::rename(&tmp, ready_path).expect("rename ready file");

    // Hold the open file descriptor and exclusive lock until terminated.
    thread::sleep(Duration::from_secs(30));
    drop(lock_file);
}

fn worker_parent(lock_path: &Path, ready_path: &Path, early_exit: bool, child_pdeathsig: bool) {
    let exe = env::current_exe().expect("current_exe");
    let mut cmd = Command::new(exe);
    cmd.arg("worker-grandchild")
        .arg(lock_path)
        .arg(ready_path)
        .arg(if child_pdeathsig { "1" } else { "0" })
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    let _grandchild = cmd.spawn().expect("spawn grandchild");

    // Wait until grandchild has acquired the lock and published its PID.
    let start = Instant::now();
    while !ready_path.exists() {
        if start.elapsed() > Duration::from_secs(5) {
            panic!("timed out waiting for grandchild ready file");
        }
        thread::sleep(Duration::from_millis(2));
    }

    if early_exit {
        thread::sleep(Duration::from_millis(20));
        std::process::exit(0);
    }

    thread::sleep(Duration::from_secs(30));
}

fn wait_for_ready_pid(ready_path: &Path) -> i32 {
    let start = Instant::now();
    loop {
        if let Ok(text) = fs::read_to_string(ready_path) {
            if let Ok(pid) = text.trim().parse::<i32>() {
                return pid;
            }
        }
        if start.elapsed() > Duration::from_secs(5) {
            panic!("timed out waiting for grandchild PID in {}", ready_path.display());
        }
        thread::sleep(Duration::from_millis(2));
    }
}

fn run_strategy_a(work_dir: &Path) -> String {
    let dir = work_dir.join("strategy_a");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("case.lock");
    let ready_path = dir.join("grandchild.pid");

    let exe = env::current_exe().unwrap();
    let mut child = Command::new(exe)
        .arg("worker-parent")
        .arg(&lock_path)
        .arg(&ready_path)
        .arg("0")
        .arg("0")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    let p1_pid = child.id() as i32;
    let p2_pid = wait_for_ready_pid(&ready_path);
    thread::sleep(Duration::from_millis(50));

    // Timeout reached: kill and reap direct child only (scaffolding-190 pattern).
    let t0 = Instant::now();
    child.kill().unwrap();
    let _status = child.wait().unwrap();
    let reap_us = t0.elapsed().as_micros();

    let p1_alive = is_pid_alive(p1_pid);
    let p2_alive = is_pid_alive(p2_pid);
    let lock_held = is_file_locked(&lock_path);

    // Clean up leaked orphan grandchild so we leave no stray processes.
    if p2_alive {
        unsafe {
            kill(p2_pid, SIGKILL);
        }
        let start = Instant::now();
        while is_pid_alive(p2_pid) && start.elapsed() < Duration::from_secs(2) {
            let mut st = 0;
            unsafe {
                waitpid(p2_pid, &mut st, WNOHANG);
            }
            thread::sleep(Duration::from_millis(2));
        }
    }

    format!(
        "{{\"strategy\":\"A_direct_child_kill\",\"p1_alive_after_reap\":{p1_alive},\"p2_alive_after_reap\":{p2_alive},\"lock_held_by_orphan_after_reap\":{lock_held},\"reap_latency_us\":{reap_us}}}"
    )
}

fn run_strategy_b(work_dir: &Path) -> String {
    let dir = work_dir.join("strategy_b");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("case.lock");
    let ready_path = dir.join("grandchild.pid");

    let exe = env::current_exe().unwrap();
    let mut child = Command::new(exe)
        .arg("worker-parent")
        .arg(&lock_path)
        .arg(&ready_path)
        .arg("0")
        .arg("0")
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    let pgid = child.id() as i32;
    let p2_pid = wait_for_ready_pid(&ready_path);
    thread::sleep(Duration::from_millis(50));

    let t0 = Instant::now();
    unsafe {
        kill(-pgid, SIGKILL);
    }
    let _status = child.wait().unwrap();
    while unsafe { kill(-pgid, 0) } == 0 || errno() != ESRCH {
        let mut st = 0;
        unsafe {
            waitpid(-pgid, &mut st, WNOHANG);
        }
        thread::sleep(Duration::from_micros(200));
    }
    let reap_us = t0.elapsed().as_micros();

    let p1_alive = is_pid_alive(pgid);
    let p2_alive = is_pid_alive(p2_pid);
    let lock_held = is_file_locked(&lock_path);

    format!(
        "{{\"strategy\":\"B_process_group_killpg\",\"p1_alive_after_reap\":{p1_alive},\"p2_alive_after_reap\":{p2_alive},\"lock_held_by_orphan_after_reap\":{lock_held},\"reap_latency_us\":{reap_us}}}"
    )
}

fn run_strategy_c1(work_dir: &Path) -> String {
    let dir = work_dir.join("strategy_c1");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("case.lock");
    let ready_path = dir.join("grandchild.pid");

    unsafe {
        prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0);
    }
    let supervisor_pid = unsafe { getpid() };

    let exe = env::current_exe().unwrap();
    let mut cmd = Command::new(exe);
    cmd.arg("worker-parent")
        .arg(&lock_path)
        .arg(&ready_path)
        .arg("0")
        .arg("0")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    unsafe {
        cmd.pre_exec(|| {
            prctl(PR_SET_PDEATHSIG, SIGKILL as usize, 0, 0, 0);
            Ok(())
        });
    }
    let mut child = cmd.spawn().unwrap();
    let p1_pid = child.id() as i32;
    let p2_pid = wait_for_ready_pid(&ready_path);
    thread::sleep(Duration::from_millis(50));

    // Supervisor kills P1 on timeout. Because PR_SET_PDEATHSIG is cleared across fork(),
    // P2 has pdeath_signal == 0 and survives, reparented to supervisor_pid!
    let t0 = Instant::now();
    child.kill().unwrap();
    let _status = child.wait().unwrap();
    let reap_us = t0.elapsed().as_micros();

    let p1_alive = is_pid_alive(p1_pid);
    let p2_alive = is_pid_alive(p2_pid);
    let p2_ppid = read_ppid(p2_pid).unwrap_or(-1);
    let reparented_to_subreaper = p2_ppid == supervisor_pid;
    let lock_held = is_file_locked(&lock_path);

    // Clean up reparented P2.
    if p2_alive {
        unsafe {
            kill(p2_pid, SIGKILL);
            let mut st = 0;
            waitpid(p2_pid, &mut st, 0);
        }
    }

    format!(
        "{{\"strategy\":\"C1_subreaper_pdeathsig_on_p1_only\",\"p1_alive_after_reap\":{p1_alive},\"p2_alive_after_reap\":{p2_alive},\"p2_reparented_to_subreaper\":{reparented_to_subreaper},\"lock_held_by_orphan_after_reap\":{lock_held},\"reap_latency_us\":{reap_us}}}"
    )
}

fn run_strategy_c2(work_dir: &Path) -> String {
    let dir = work_dir.join("strategy_c2");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("case.lock");
    let ready_path = dir.join("grandchild.pid");

    unsafe {
        prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0);
    }

    let exe = env::current_exe().unwrap();
    let mut child = Command::new(exe)
        .arg("worker-parent")
        .arg(&lock_path)
        .arg(&ready_path)
        .arg("1") // early_exit = true
        .arg("1") // child_pdeathsig = true
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();

    let p2_pid = wait_for_ready_pid(&ready_path);
    // Wait for P1 to exit normally (after 20ms).
    let status = child.wait().unwrap();
    assert!(status.success());

    // Reap reparented P2 which was prematurely killed by P1's normal exit!
    let mut p2_status = 0;
    let waited = unsafe { waitpid(p2_pid, &mut p2_status, 0) };
    let p2_killed_by_sigkill = waited == p2_pid && (p2_status & 0x7f) == SIGKILL;
    let p2_alive = is_pid_alive(p2_pid);

    format!(
        "{{\"strategy\":\"C2_pdeathsig_on_p2_early_p1_exit\",\"p1_exited_zero\":true,\"p2_prematurely_killed_by_sigkill\":{p2_killed_by_sigkill},\"p2_alive\":{p2_alive}}}"
    )
}

fn run_strategy_d(work_dir: &Path) -> String {
    let dir = work_dir.join("strategy_d");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("case.lock");
    let ready_path = dir.join("grandchild.pid");

    unsafe {
        prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0);
    }

    let exe = env::current_exe().unwrap();
    let mut cmd = Command::new(exe);
    cmd.arg("worker-parent")
        .arg(&lock_path)
        .arg(&ready_path)
        .arg("0")
        .arg("0")
        .process_group(0)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    unsafe {
        cmd.pre_exec(|| {
            prctl(PR_SET_PDEATHSIG, SIGKILL as usize, 0, 0, 0);
            Ok(())
        });
    }
    let mut child = cmd.spawn().unwrap();
    let pgid = child.id() as i32;
    let p2_pid = wait_for_ready_pid(&ready_path);
    thread::sleep(Duration::from_millis(50));

    let t0 = Instant::now();
    unsafe {
        kill(-pgid, SIGKILL);
    }
    let _status = child.wait().unwrap();
    // Because we are a PR_SET_CHILD_SUBREAPER, P2 is reparented to us and we can
    // synchronously reap every process in -pgid via blocking waitpid(-pgid) until ECHILD!
    let mut descendant_reap_count = 0usize;
    loop {
        let mut st = 0;
        let rc = unsafe { waitpid(-pgid, &mut st, 0) };
        if rc > 0 {
            descendant_reap_count += 1;
        } else {
            assert_eq!(errno(), ECHILD, "expected ECHILD when process group is empty");
            break;
        }
    }
    let reap_us = t0.elapsed().as_micros();

    let p1_alive = is_pid_alive(pgid);
    let p2_alive = is_pid_alive(p2_pid);
    let lock_held = is_file_locked(&lock_path);

    format!(
        "{{\"strategy\":\"D_combined_pgroup_and_subreaper_waitpid\",\"p1_alive_after_reap\":{p1_alive},\"p2_alive_after_reap\":{p2_alive},\"descendant_reap_count\":{descendant_reap_count},\"lock_held_by_orphan_after_reap\":{lock_held},\"reap_latency_us\":{reap_us}}}"
    )
}

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("worker-grandchild") => {
            let lock_path = PathBuf::from(&args[2]);
            let ready_path = PathBuf::from(&args[3]);
            let set_pdeathsig = args.get(4).map(String::as_str) == Some("1");
            worker_grandchild(&lock_path, &ready_path, set_pdeathsig);
        }
        Some("worker-parent") => {
            let lock_path = PathBuf::from(&args[2]);
            let ready_path = PathBuf::from(&args[3]);
            let early_exit = args.get(4).map(String::as_str) == Some("1");
            let child_pdeathsig = args.get(5).map(String::as_str) == Some("1");
            worker_parent(&lock_path, &ready_path, early_exit, child_pdeathsig);
        }
        Some("run-all") => {
            let work_dir = PathBuf::from(&args[2]);
            fs::create_dir_all(&work_dir).unwrap();
            let a = run_strategy_a(&work_dir);
            let b = run_strategy_b(&work_dir);
            let c1 = run_strategy_c1(&work_dir);
            let c2 = run_strategy_c2(&work_dir);
            let d = run_strategy_d(&work_dir);
            println!("[{a},{b},{c1},{c2},{d}]");
        }
        _ => {
            eprintln!("Usage: supervisor_probe run-all <work_dir>");
            std::process::exit(2);
        }
    }
}
