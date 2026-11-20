// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end containment and negative escape tests for `ExecSeal` Tier 1
//! (`linux_bwrap`) and Tier 2 (`linux_landlock_seccomp`).

#![cfg(target_os = "linux")]

use std::collections::BTreeMap;
use std::env;
use std::ffi::CString;
use std::fs;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use cargo_anneal::sandbox::{
    ActiveSandbox, MountSpec, PathMapper, SandboxPolicy, SandboxRuntime, create_dir_mode,
    force_tier1_runtime, force_tier2_runtime, make_tree_writable, set_mode,
    validate_and_promote_olean, validate_inspector_result,
};
use cargo_anneal::{Checker, SandboxMode, default_lean_path};

const PROBE_ENV: &str = "ANNEAL_SANDBOX_ESCAPE_PROBE";

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn installed_lean() -> PathBuf {
    if let Some(p) = env::var_os("ANNEAL_LEAN") {
        let path = PathBuf::from(p);
        if path.is_file() {
            return path;
        }
    }
    default_lean_path()
}

fn lean_prefix(lean: &Path) -> PathBuf {
    let out = std::process::Command::new(lean)
        .arg("--print-prefix")
        .output()
        .expect("lean --print-prefix");
    assert!(out.status.success(), "lean --print-prefix failed");
    fs::canonicalize(String::from_utf8(out.stdout).unwrap().trim()).unwrap()
}

/// Child probe invoked when `ANNEAL_SANDBOX_ESCAPE_PROBE` is set in the test
/// binary's environment (the Rust test harness invokes the exact test function
/// via `--exact`).
fn run_child_escape_probe(
    tier: &str,
    ro_file: &Path,
    canary: &Path,
    leaked_fd: i32,
    tmp_dir: &Path,
) {
    let is_tier2 = tier == "tier2";
    let mut failures = Vec::new();

    // 1. Host canary file must not be readable.
    if fs::read(canary).is_ok() {
        failures.push("host canary was readable".to_string());
    }

    // 2. `/etc/passwd` must not be readable.
    if fs::read("/etc/passwd").is_ok() {
        failures.push("/etc/passwd was readable".to_string());
    }

    // 3. RO mount file must be readable, must reject O_WRONLY, and must reject
    //    `open(O_RDONLY | O_TRUNC)` (Landlock ABI >= 3 TRUNCATE protection).
    match fs::read(ro_file) {
        Ok(b) if b == b"ro-sentinel\n" => {}
        other => failures.push(format!("RO file read failed: {other:?}")),
    }
    let cro = CString::new(ro_file.as_os_str().as_bytes()).unwrap();
    // SAFETY: `cro` is a valid NUL-terminated C string.
    let fd_w = unsafe { libc::open(cro.as_ptr(), libc::O_WRONLY) };
    if fd_w >= 0 {
        unsafe { libc::close(fd_w) };
        failures.push("RO file opened O_WRONLY".to_string());
    }
    // SAFETY: `cro` is a valid NUL-terminated C string.
    let fd_trunc = unsafe { libc::open(cro.as_ptr(), libc::O_RDONLY | libc::O_TRUNC) };
    if fd_trunc >= 0 {
        unsafe { libc::close(fd_trunc) };
        failures.push("RO file opened O_RDONLY|O_TRUNC".to_string());
    }

    // 4. Inherited FD must have been closed across `execve` via `close_range`.
    // SAFETY: `F_GETFD` is safe on any integer FD (returns -1/EBADF if closed).
    let fd_flags = unsafe { libc::fcntl(leaked_fd, libc::F_GETFD) };
    if fd_flags >= 0 {
        failures.push(format!("inherited FD {leaked_fd} leaked across execve"));
    }

    // 5. Executing `/bin/sh` must fail in both tiers.
    let bin_sh = CString::new("/bin/sh").unwrap();
    let argv_sh = [bin_sh.as_ptr(), std::ptr::null()];
    // SAFETY: valid C string pointers; only executes if sandbox fails.
    let rc_sh = unsafe { libc::execve(bin_sh.as_ptr(), argv_sh.as_ptr(), std::ptr::null()) };
    if rc_sh == 0 {
        failures.push("execve(/bin/sh) unexpectedly succeeded".to_string());
    }

    // 6. Creating and executing an ELF copy inside `tmp` must fail in both
    //    tiers.
    let evil_path = tmp_dir.join("evil_bin");
    if fs::write(&evil_path, b"\x7fELF\x02\x01\x01\x00").is_ok() {
        let _ = fs::set_permissions(&evil_path, fs::Permissions::from_mode(0o755));
        let cevil = CString::new(evil_path.as_os_str().as_bytes()).unwrap();
        let argv_evil = [cevil.as_ptr(), std::ptr::null()];
        // SAFETY: valid C string pointers.
        let rc_evil = unsafe { libc::execve(cevil.as_ptr(), argv_evil.as_ptr(), std::ptr::null()) };
        if rc_evil == 0 {
            failures.push("execve(tmp/evil_bin) unexpectedly succeeded".to_string());
        }
        let err = std::io::Error::last_os_error();
        if is_tier2 && err.raw_os_error() != Some(libc::EACCES) {
            failures.push(format!(
                "expected EACCES on Tier 2 execve(tmp/evil_bin), got {err}"
            ));
        }
    }

    // 7. Thread creation (`std::thread::spawn` -> `clone3 -> ENOSYS` ->
    //    `clone(CLONE_THREAD)`) must succeed in both tiers.
    let handle = std::thread::spawn(|| 42u32);
    match handle.join() {
        Ok(42) => {}
        other => failures.push(format!("pthread/thread spawn failed: {other:?}")),
    }

    // 8. Tier 2 seccomp-BPF specific syscall guards.
    if is_tier2 {
        // Network sockets & socketpair blocked with EPERM.
        // SAFETY: standard libc syscall.
        let s_inet = unsafe { libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0) };
        if s_inet >= 0 {
            unsafe { libc::close(s_inet) };
            failures.push("socket(AF_INET) allowed in Tier 2".to_string());
        }
        let mut pair = [0i32; 2];
        // SAFETY: valid 2-int buffer.
        if unsafe { libc::socketpair(libc::AF_UNIX, libc::SOCK_STREAM, 0, pair.as_mut_ptr()) } == 0
        {
            unsafe {
                libc::close(pair[0]);
                libc::close(pair[1]);
            }
            failures.push("socketpair(AF_UNIX) allowed in Tier 2".to_string());
        }

        // `fork` (non-`CLONE_THREAD` clone) blocked with EPERM.
        // SAFETY: if allowed, child exits immediately.
        let fpid = unsafe { libc::fork() };
        if fpid == 0 {
            unsafe { libc::_exit(0) };
        } else if fpid > 0 {
            unsafe { libc::waitpid(fpid, std::ptr::null_mut(), 0) };
            failures.push("fork() allowed in Tier 2".to_string());
        }

        // `kill(ppid, 0)` blocked, `kill(getpid(), 0)` allowed.
        // SAFETY: signal 0 checks permission only.
        let ppid = unsafe { libc::getppid() };
        if unsafe { libc::kill(ppid, 0) } == 0 {
            failures.push("kill(ppid, 0) allowed in Tier 2".to_string());
        }
        // SAFETY: signal 0 to self is benign.
        let me = unsafe { libc::getpid() };
        if unsafe { libc::kill(me, 0) } != 0 {
            failures.push(format!(
                "kill(self, 0) failed in Tier 2: {}",
                std::io::Error::last_os_error()
            ));
        }

        // `prlimit64` read-only self allowed; write blocked.
        let mut old = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        // SAFETY: querying own RLIMIT_NOFILE with NULL new_limit.
        if unsafe { libc::prlimit(0, libc::RLIMIT_NOFILE, std::ptr::null(), &mut old) } != 0 {
            failures.push(format!(
                "prlimit64 read-only self failed: {}",
                std::io::Error::last_os_error()
            ));
        }
        let raise = libc::rlimit {
            rlim_cur: 1024,
            rlim_max: 1024,
        };
        // SAFETY: attempting to raise limit (must be blocked with EPERM).
        if unsafe { libc::prlimit(0, libc::RLIMIT_NOFILE, &raise, std::ptr::null_mut()) } == 0 {
            failures.push("prlimit64 write allowed in Tier 2".to_string());
        }

        // `ioctl`, `inotify_init1`, `memfd_create`, `unshare` blocked.
        // SAFETY: benign probe syscalls blocked by default EPERM.
        if unsafe { libc::ioctl(0, libc::FIONREAD, &mut 0i32 as *mut i32) } == 0 {
            failures.push("ioctl allowed in Tier 2".to_string());
        }
        let inot = unsafe { libc::inotify_init1(libc::IN_CLOEXEC) };
        if inot >= 0 {
            unsafe { libc::close(inot) };
            failures.push("inotify_init1 allowed in Tier 2".to_string());
        }
        let memfd_name = CString::new("evil").unwrap();
        let mfd = unsafe { libc::syscall(libc::SYS_memfd_create, memfd_name.as_ptr(), 0u32) };
        if mfd >= 0 {
            unsafe { libc::close(mfd as i32) };
            failures.push("memfd_create allowed in Tier 2".to_string());
        }
        if unsafe { libc::unshare(libc::CLONE_NEWUSER) } == 0 {
            failures.push("unshare(CLONE_NEWUSER) allowed in Tier 2".to_string());
        }

        // `fcntl(F_SETLK)` blocked while `fcntl(F_GETFD)` allowed.
        let mut fl: libc::flock = unsafe { std::mem::zeroed() };
        fl.l_type = libc::F_RDLCK as i16;
        // SAFETY: probing F_SETLK on stdout (must return EPERM).
        if unsafe { libc::fcntl(1, libc::F_SETLK, &fl) } == 0 {
            failures.push("fcntl(F_SETLK) allowed in Tier 2".to_string());
        }
        if unsafe { libc::fcntl(1, libc::F_GETFD) } < 0 {
            failures.push("fcntl(F_GETFD) failed in Tier 2".to_string());
        }

        // `/proc/self/statm` is readable for Lean `-M` accounting, while all
        // other `/proc` paths (own environ/maps and other PIDs) stay blocked.
        if fs::read_to_string("/proc/self/statm").is_err() {
            failures.push("/proc/self/statm not readable in Tier 2".to_string());
        }
        for blocked_proc in ["/proc/self/environ", "/proc/self/maps", "/proc/1/statm"] {
            if fs::read(blocked_proc).is_ok() {
                failures.push(format!("{blocked_proc} was readable in Tier 2"));
            }
        }
    } else {
        // Tier 1 (`linux_bwrap`): must drop all capabilities (`CapEff == 0`),
        // set `NoNewPrivs: 1`, run as PID 1 (`--as-pid-1`), and cap `/dev`
        // tmpfs at 64 KiB so a child cannot exhaust host RAM via `/dev`.
        match fs::read_to_string("/proc/self/status") {
            Ok(status) => {
                if !status.lines().any(|l| l == "CapEff:\t0000000000000000") {
                    failures.push("Tier 1 CapEff is not 0000000000000000".to_string());
                }
                if !status.lines().any(|l| l == "NoNewPrivs:\t1") {
                    failures.push("Tier 1 NoNewPrivs is not 1".to_string());
                }
                if !status.lines().any(|l| l == "Pid:\t1") {
                    failures.push("Tier 1 child is not PID 1 (--as-pid-1)".to_string());
                }
            }
            Err(e) => failures.push(format!("cannot read /proc/self/status in Tier 1: {e}")),
        }
        let dev_fill = vec![0x41u8; 256 * 1024];
        if fs::write("/dev/fill_probe", &dev_fill).is_ok() {
            let _ = fs::remove_file("/dev/fill_probe");
            failures.push("Tier 1 /dev tmpfs accepted 256 KiB write (uncapped)".to_string());
        }
    }

    assert!(
        failures.is_empty(),
        "escape probe failures ({tier}):\n{}",
        failures.join("\n")
    );
}

#[test]
fn sandbox_escape_vectors_blocked_in_tier1_and_tier2() {
    if let Ok(tier) = env::var(PROBE_ENV) {
        let ro_file = PathBuf::from(env::var("ANNEAL_PROBE_RO").unwrap());
        let canary = PathBuf::from(env::var("ANNEAL_PROBE_CANARY").unwrap());
        let leaked_fd: i32 = env::var("ANNEAL_PROBE_FD").unwrap().parse().unwrap();
        let tmp_dir = PathBuf::from(env::var("ANNEAL_PROBE_TMP").unwrap());
        run_child_escape_probe(&tier, &ro_file, &canary, leaked_fd, &tmp_dir);
        return;
    }

    let exe = fs::canonicalize(env::current_exe().unwrap()).unwrap();
    let exe_dir = exe.parent().unwrap().to_path_buf();
    let base_dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(base_dir.path()).unwrap();

    let canary = base.join("host_canary.txt");
    fs::write(&canary, b"secret-host-data\n").unwrap();

    let in_dir = base.join("in");
    let out_dir = base.join("out");
    let tmp_dir = base.join("tmp");
    create_dir_mode(&in_dir, 0o700).unwrap();
    create_dir_mode(&out_dir, 0o700).unwrap();
    create_dir_mode(&tmp_dir, 0o700).unwrap();

    let ro_file = in_dir.join("ro.txt");
    fs::write(&ro_file, b"ro-sentinel\n").unwrap();
    set_mode(&ro_file, 0o444).unwrap();
    set_mode(&in_dir, 0o500).unwrap();

    // Open a file descriptor WITHOUT `O_CLOEXEC` to verify `close_range`.
    let c_canary = CString::new(canary.as_os_str().as_bytes()).unwrap();
    // SAFETY: `c_canary` is a valid NUL-terminated path.
    let leaked_fd = unsafe { libc::open(c_canary.as_ptr(), libc::O_RDONLY) };
    assert!(leaked_fd >= 3, "expected fd >= 3, got {leaked_fd}");

    let runtimes: Vec<(&str, SandboxRuntime)> = vec![
        (
            "tier1",
            force_tier1_runtime(&exe, &exe_dir).expect("Tier 1 bwrap runtime"),
        ),
        (
            "tier2",
            force_tier2_runtime(&exe, &exe_dir).expect("Tier 2 landlock+seccomp runtime"),
        ),
    ];

    for (tier, runtime) in runtimes {
        let ro_mounts = vec![
            MountSpec {
                host: exe_dir.clone(),
                child: PathBuf::from("/toolchain"),
            },
            MountSpec {
                host: in_dir.clone(),
                child: PathBuf::from("/work/in"),
            },
        ];
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);

        let mut extra_env = BTreeMap::new();
        extra_env.insert(PROBE_ENV.to_string(), tier.to_string());
        extra_env.insert(
            "ANNEAL_PROBE_RO".to_string(),
            mapper.map_str(&ro_file).unwrap(),
        );
        extra_env.insert(
            "ANNEAL_PROBE_CANARY".to_string(),
            canary.to_string_lossy().into_owned(),
        );
        extra_env.insert("ANNEAL_PROBE_FD".to_string(), leaked_fd.to_string());
        extra_env.insert(
            "ANNEAL_PROBE_TMP".to_string(),
            mapper.map_str(&tmp_dir).unwrap(),
        );

        let policy = SandboxPolicy {
            exec_bin: exe.clone(),
            args: vec![
                "--exact".to_string(),
                "sandbox_escape_vectors_blocked_in_tier1_and_tier2".to_string(),
                "--nocapture".to_string(),
            ],
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: Duration::from_secs(30),
        };
        let out = runtime.execute(&policy).expect("sandbox execute");
        assert!(
            out.status.success(),
            "{tier} escape probe failed (exit {:?}):\nstdout:\n{}\nstderr:\n{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr),
        );
        // Confirm RO file bytes were never truncated.
        assert_eq!(fs::read(&ro_file).unwrap(), b"ro-sentinel\n");
    }

    // SAFETY: closing our owned leaked_fd test descriptor.
    unsafe { libc::close(leaked_fd) };
    make_tree_writable(&base);
}

#[test]
fn wall_clock_timeout_kills_process_group_in_tier1_and_tier2() {
    const SLEEP_ENV: &str = "ANNEAL_SANDBOX_SLEEP_PROBE";
    if env::var_os(SLEEP_ENV).is_some() {
        std::thread::sleep(Duration::from_secs(30));
        return;
    }

    let exe = fs::canonicalize(env::current_exe().unwrap()).unwrap();
    let exe_dir = exe.parent().unwrap().to_path_buf();
    let base_dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(base_dir.path()).unwrap();
    let out_dir = base.join("out");
    let tmp_dir = base.join("tmp");
    create_dir_mode(&out_dir, 0o700).unwrap();
    create_dir_mode(&tmp_dir, 0o700).unwrap();

    for runtime in [
        force_tier1_runtime(&exe, &exe_dir).unwrap(),
        force_tier2_runtime(&exe, &exe_dir).unwrap(),
    ] {
        let mut extra_env = BTreeMap::new();
        extra_env.insert(SLEEP_ENV.to_string(), "1".to_string());
        let policy = SandboxPolicy {
            exec_bin: exe.clone(),
            args: vec![
                "--exact".to_string(),
                "wall_clock_timeout_kills_process_group_in_tier1_and_tier2".to_string(),
            ],
            ro_mounts: vec![MountSpec {
                host: exe_dir.clone(),
                child: PathBuf::from("/toolchain"),
            }],
            rw_out: MountSpec {
                host: out_dir.clone(),
                child: PathBuf::from("/work/out"),
            },
            rw_tmp: MountSpec {
                host: tmp_dir.clone(),
                child: PathBuf::from("/work/tmp"),
            },
            child_cwd: None,
            extra_env,
            timeout: Duration::from_millis(250),
        };
        let start = Instant::now();
        let err = runtime.execute(&policy).unwrap_err();
        assert_eq!(err.phase, "sandbox-timeout", "{err}");
        assert!(
            start.elapsed() < Duration::from_secs(5),
            "timeout took {:?}",
            start.elapsed()
        );
    }
}

#[test]
fn live_lean_compiles_and_blocks_hostile_eval_in_tier1_and_tier2() {
    let lean = fs::canonicalize(installed_lean()).unwrap();
    let prefix = lean_prefix(&lean);
    let base_dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(base_dir.path()).unwrap();
    let canary = base.join("secret.txt");
    fs::write(&canary, b"do-not-read-me\n").unwrap();

    for (label, runtime) in [
        ("tier1", force_tier1_runtime(&lean, &prefix).unwrap()),
        ("tier2", force_tier2_runtime(&lean, &prefix).unwrap()),
    ] {
        // 1. Clean module compilation succeeds and passes Door 1.
        let run_ok = base.join(format!("{label}-ok"));
        let in_dir = run_ok.join("in");
        let out_dir = run_ok.join("out");
        let tmp_dir = run_ok.join("tmp");
        create_dir_mode(&in_dir, 0o700).unwrap();
        create_dir_mode(&out_dir, 0o700).unwrap();
        create_dir_mode(&tmp_dir, 0o700).unwrap();

        let src = in_dir.join("Clean.lean");
        fs::write(&src, b"prelude\ninductive Ok where | mk\n").unwrap();
        set_mode(&src, 0o444).unwrap();
        set_mode(&in_dir, 0o500).unwrap();

        let ro_mounts = vec![
            MountSpec {
                host: prefix.clone(),
                child: PathBuf::from("/toolchain"),
            },
            MountSpec {
                host: in_dir.clone(),
                child: PathBuf::from("/work/in"),
            },
        ];
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);
        let policy = SandboxPolicy {
            exec_bin: lean.clone(),
            args: vec![
                "-j1".to_string(),
                "-M1024".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                mapper.map_str(&in_dir).unwrap(),
                "-o".to_string(),
                mapper.map_str(&out_dir.join("Clean.olean")).unwrap(),
                mapper.map_str(&src).unwrap(),
            ],
            ro_mounts: ro_mounts.clone(),
            rw_out: rw_out.clone(),
            rw_tmp: rw_tmp.clone(),
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: Duration::from_secs(60),
        };
        let output = runtime.execute(&policy).unwrap();
        assert!(
            output.status.success(),
            "{label} Lean compile failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let promoted = run_ok.join("Clean.olean");
        validate_and_promote_olean(&out_dir, "Clean.olean", &promoted).unwrap();

        // 2. Hostile Lean `#eval` trying to read host canary or spawn `/bin/sh`
        //    must fail inside both Tier 1 and Tier 2.
        let run_hostile = base.join(format!("{label}-hostile"));
        let h_in = run_hostile.join("in");
        let h_out = run_hostile.join("out");
        let h_tmp = run_hostile.join("tmp");
        create_dir_mode(&h_in, 0o700).unwrap();
        create_dir_mode(&h_out, 0o700).unwrap();
        create_dir_mode(&h_tmp, 0o700).unwrap();

        let h_src = h_in.join("Hostile.lean");
        let hostile_code = format!(
            "import Init.System.IO\n\
             #eval show IO Unit from do\n\
               let _ ← IO.FS.readFile \"{}\"\n",
            canary.display()
        );
        fs::write(&h_src, hostile_code).unwrap();
        set_mode(&h_src, 0o444).unwrap();
        set_mode(&h_in, 0o500).unwrap();

        let h_ro = vec![
            MountSpec {
                host: prefix.clone(),
                child: PathBuf::from("/toolchain"),
            },
            MountSpec {
                host: h_in.clone(),
                child: PathBuf::from("/work/in"),
            },
        ];
        let h_rw_out = MountSpec {
            host: h_out.clone(),
            child: PathBuf::from("/work/out"),
        };
        let h_rw_tmp = MountSpec {
            host: h_tmp.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let h_mapper = PathMapper::new(&runtime, &h_ro, &h_rw_out, &h_rw_tmp);
        let h_policy = SandboxPolicy {
            exec_bin: lean.clone(),
            args: vec![
                "-j1".to_string(),
                "-M1024".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                h_mapper.map_str(&h_in).unwrap(),
                "-o".to_string(),
                h_mapper.map_str(&h_out.join("Hostile.olean")).unwrap(),
                h_mapper.map_str(&h_src).unwrap(),
            ],
            ro_mounts: h_ro,
            rw_out: h_rw_out,
            rw_tmp: h_rw_tmp,
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: Duration::from_secs(60),
        };
        let h_output = runtime.execute(&h_policy).unwrap();
        assert!(
            !h_output.status.success(),
            "{label} hostile #eval readFile MUST fail inside sandbox"
        );
        let combined = format!(
            "{}{}",
            String::from_utf8_lossy(&h_output.stdout),
            String::from_utf8_lossy(&h_output.stderr)
        );
        assert!(
            !combined.contains("do-not-read-me"),
            "{label} canary contents leaked: {combined}"
        );

        // 3. Real `TrustedBoundary.lean --run` (`"headers"` mode) succeeds and
        //    passes Door 1 under BOTH Tier 1 and Tier 2.
        let run_insp = base.join(format!("{label}-inspector"));
        let i_in = run_insp.join("in");
        let i_out = run_insp.join("out");
        let i_tmp = run_insp.join("tmp");
        create_dir_mode(&i_in, 0o700).unwrap();
        create_dir_mode(&i_out, 0o700).unwrap();
        create_dir_mode(&i_tmp, 0o700).unwrap();
        let tb_dst = i_in.join("TrustedBoundary.lean");
        fs::copy(
            repo_root().join("trusted/audit/TrustedBoundary.lean"),
            &tb_dst,
        )
        .unwrap();
        set_mode(&tb_dst, 0o444).unwrap();
        let sample_src = i_in.join("Sample.lean");
        fs::write(&sample_src, b"prelude\ndef x : Prop := True\n").unwrap();
        set_mode(&sample_src, 0o444).unwrap();

        let i_ro = vec![
            MountSpec {
                host: prefix.clone(),
                child: PathBuf::from("/toolchain"),
            },
            MountSpec {
                host: i_in.clone(),
                child: PathBuf::from("/work/in"),
            },
        ];
        let i_rw_out = MountSpec {
            host: i_out.clone(),
            child: PathBuf::from("/work/out"),
        };
        let i_rw_tmp = MountSpec {
            host: i_tmp.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let i_mapper = PathMapper::new(&runtime, &i_ro, &i_rw_out, &i_rw_tmp);
        let req_host = i_in.join("request.json");
        let req_json = serde_json::json!({
            "mode": "headers",
            "sysroot": i_mapper.map_str(&prefix).unwrap(),
            "foundation": ["Init.Prelude"],
            "sources": [["Sample", i_mapper.map_str(&sample_src).unwrap()]],
        });
        fs::write(&req_host, serde_json::to_vec(&req_json).unwrap()).unwrap();
        set_mode(&req_host, 0o444).unwrap();
        set_mode(&i_in, 0o500).unwrap();

        let res_host = i_out.join("result.json");
        let i_policy = SandboxPolicy {
            exec_bin: lean.clone(),
            args: vec![
                "-j1".to_string(),
                "-M1024".to_string(),
                "--run".to_string(),
                i_mapper.map_str(&tb_dst).unwrap(),
                i_mapper.map_str(&req_host).unwrap(),
                i_mapper.map_str(&res_host).unwrap(),
            ],
            ro_mounts: i_ro,
            rw_out: i_rw_out,
            rw_tmp: i_rw_tmp,
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: Duration::from_secs(60),
        };
        let i_out_res = runtime.execute(&i_policy).unwrap();
        assert!(
            i_out_res.status.success(),
            "{label} TrustedBoundary headers failed:\n{}",
            String::from_utf8_lossy(&i_out_res.stderr)
        );
        let bytes = validate_inspector_result(&i_out, "result.json")
            .unwrap()
            .expect("result.json present");
        let parsed: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(parsed["ok"], serde_json::json!(true), "{label}: {parsed}");
    }

    // 4. Verify `Checker` defaults to `PreferBwrapOrLandlock` and probes
    //    `LinuxBwrap` on a bwrap-capable Linux host.
    let mut checker = Checker::new(&repo_root(), Some(&lean)).unwrap();
    assert_eq!(checker.sandbox_mode(), SandboxMode::PreferBwrapOrLandlock);
    checker.tool_admission().unwrap();
    let rt = checker.ensure_sandbox_ready().unwrap();
    assert_eq!(rt.backend, ActiveSandbox::LinuxBwrap);
    assert_eq!(checker.active_sandbox(), Some(ActiveSandbox::LinuxBwrap));

    make_tree_writable(&base);
}

#[test]
fn live_lean_tier2_getrusage_enforces_memory_limit() {
    let lean = fs::canonicalize(installed_lean()).unwrap();
    let prefix = lean_prefix(&lean);
    let runtime = force_tier2_runtime(&lean, &prefix).unwrap();
    let base_dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(base_dir.path()).unwrap();
    let in_dir = base.join("in");
    let out_dir = base.join("out");
    let tmp_dir = base.join("tmp");
    create_dir_mode(&in_dir, 0o700).unwrap();
    create_dir_mode(&out_dir, 0o700).unwrap();
    create_dir_mode(&tmp_dir, 0o700).unwrap();

    let src = in_dir.join("Mem.lean");
    fs::write(
        &src,
        b"import Init.Data.List.Basic\ndef alloc : Nat -> List Nat\n  | 0 => []\n  | n + 1 => n :: alloc n\n#eval (alloc 500000).length\n",
    )
    .unwrap();
    set_mode(&src, 0o444).unwrap();
    set_mode(&in_dir, 0o500).unwrap();

    let ro_mounts = vec![
        MountSpec {
            host: prefix.clone(),
            child: PathBuf::from("/toolchain"),
        },
        MountSpec {
            host: in_dir.clone(),
            child: PathBuf::from("/work/in"),
        },
    ];
    let rw_out = MountSpec {
        host: out_dir.clone(),
        child: PathBuf::from("/work/out"),
    };
    let rw_tmp = MountSpec {
        host: tmp_dir.clone(),
        child: PathBuf::from("/work/tmp"),
    };
    let mapper = PathMapper::new(&runtime, &ro_mounts, &rw_out, &rw_tmp);
    let policy = SandboxPolicy {
        exec_bin: lean,
        args: vec![
            "-j1".to_string(),
            "-M1".to_string(),
            "-t0".to_string(),
            "-R".to_string(),
            mapper.map_str(&in_dir).unwrap(),
            "-o".to_string(),
            mapper.map_str(&out_dir.join("Mem.olean")).unwrap(),
            mapper.map_str(&src).unwrap(),
        ],
        ro_mounts,
        rw_out,
        rw_tmp,
        child_cwd: None,
        extra_env: BTreeMap::new(),
        timeout: Duration::from_secs(30),
    };
    let output = runtime.execute(&policy).unwrap();
    assert!(
        !output.status.success(),
        "Lean -M1 must fail when getrusage is permitted in Tier 2"
    );
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("excessive memory consumption"),
        "expected Lean -M1 OOM diagnostic via getrusage, got:\n{combined}"
    );
    make_tree_writable(&base);
}

#[test]
fn tier1_as_pid1_prevents_post_exit_out_writes() {
    if let Ok(out_file) = env::var("ANNEAL_PID1_LATE_WRITE") {
        // Fork a grandchild that sleeps 15 ms then writes to `/work/out` while
        // PID 1 exits immediately. Under `--as-pid-1`, kernel PID-ns teardown
        // kills and reaps the grandchild synchronously before `bwrap` returns.
        // SAFETY: child immediately sleeps/writes and `_exit`s.
        let pid = unsafe { libc::fork() };
        if pid == 0 {
            std::thread::sleep(Duration::from_millis(15));
            let _ = fs::write(&out_file, b"late-write");
            unsafe { libc::_exit(0) };
        }
        return;
    }

    let exe = fs::canonicalize(env::current_exe().unwrap()).unwrap();
    let exe_dir = exe.parent().unwrap().to_path_buf();
    let runtime = force_tier1_runtime(&exe, &exe_dir).unwrap();
    for trial in 0..10 {
        let base_dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(base_dir.path()).unwrap();
        let out_dir = base.join("out");
        let tmp_dir = base.join("tmp");
        create_dir_mode(&out_dir, 0o700).unwrap();
        create_dir_mode(&tmp_dir, 0o700).unwrap();

        let ro_mounts = vec![MountSpec {
            host: exe_dir.clone(),
            child: PathBuf::from("/toolchain"),
        }];
        let rw_out = MountSpec {
            host: out_dir.clone(),
            child: PathBuf::from("/work/out"),
        };
        let rw_tmp = MountSpec {
            host: tmp_dir.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let mut extra_env = BTreeMap::new();
        extra_env.insert(
            "ANNEAL_PID1_LATE_WRITE".to_string(),
            "/work/out/late.txt".to_string(),
        );
        let policy = SandboxPolicy {
            exec_bin: exe.clone(),
            args: vec![
                "--exact".to_string(),
                "tier1_as_pid1_prevents_post_exit_out_writes".to_string(),
                "--nocapture".to_string(),
            ],
            ro_mounts,
            rw_out,
            rw_tmp,
            child_cwd: None,
            extra_env,
            timeout: Duration::from_secs(30),
        };
        let output = runtime.execute(&policy).unwrap();
        assert!(
            output.status.success(),
            "trial {trial}: child failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::thread::sleep(Duration::from_millis(40));
        assert!(
            !out_dir.join("late.txt").exists(),
            "trial {trial}: descendant outlived Tier 1 bwrap and wrote out/late.txt"
        );
    }
}
