// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Rejection of broad sandbox prefixes, hiding of prefix-sibling files,
//! and the tier 1 seccomp filter and nested user namespaces.

use super::*;

#[test]
fn sandbox_rejects_broad_prefixes_and_hides_prefix_sibling_files() {
    use std::os::unix::fs::symlink;

    let lean = fs::canonicalize(installed_lean()).unwrap();
    let real_prefix = lean_prefix(&lean).unwrap();
    let stage_dir = tempfile::tempdir().unwrap();
    let stage = fs::canonicalize(stage_dir.path()).unwrap();

    // 1. Broad host prefixes (`/`, `/tmp`, `/usr`, `$HOME`, `cwd`, `stage`)
    //    must fail closed before any child executes.
    let mut bad_prefixes = vec![
        PathBuf::from("/"),
        PathBuf::from("/tmp"),
        PathBuf::from("/usr"),
        stage.clone(),
        env::current_dir().unwrap(),
    ];
    if let Some(home) = env::var_os("HOME").filter(|h| !h.is_empty()) {
        bad_prefixes.push(PathBuf::from(home));
    }
    for bad in &bad_prefixes {
        if !bad.exists() {
            continue;
        }
        let err = SandboxRuntime::probe(SandboxMode::PreferBwrapOrLandlock, &lean, bad, &stage)
            .unwrap_err();
        assert_eq!(err.code, 2, "expected operational failure for {}: {err}", bad.display());
        assert_eq!(err.phase, "sandbox", "expected sandbox phase for {}: {err}", bad.display());
    }

    // 2. External `lib` or `lib/lean` symlinks pointing to broad or
    //    non-dedicated directories (`/`, `/var/lib`, `/home/shared`-style
    //    trees with unrelated sibling directories/files, or a `lib/lean` tree
    //    containing non-Lean files or escaping symlinks) must fail closed
    //    structurally rather than relying on a fixed path denylist.
    let sym_dir = tempfile::tempdir().unwrap();
    let sym_base = fs::canonicalize(sym_dir.path()).unwrap();
    let bad_sym_prefix = sym_base.join("bad-sym-prefix");
    fs::create_dir_all(bad_sym_prefix.join("lib")).unwrap();
    symlink(Path::new("/"), bad_sym_prefix.join("lib/lean")).unwrap();
    let sym_err = SandboxRuntime::probe(
        SandboxMode::PreferBwrapOrLandlock,
        &lean,
        &bad_sym_prefix,
        &stage,
    )
    .unwrap_err();
    assert_eq!(sym_err.code, 2, "{sym_err}");
    assert_eq!(sym_err.phase, "sandbox", "{sym_err}");

    if Path::new("/var/lib").is_dir() {
        let var_lib_prefix = sym_base.join("var-lib-prefix");
        fs::create_dir_all(&var_lib_prefix).unwrap();
        symlink(Path::new("/var/lib"), var_lib_prefix.join("lib")).unwrap();
        let err = SandboxRuntime::probe(
            SandboxMode::PreferBwrapOrLandlock,
            &lean,
            &var_lib_prefix,
            &stage,
        )
        .unwrap_err();
        assert_eq!(err.code, 2, "{err}");
        assert_eq!(err.phase, "sandbox", "{err}");
    }

    let shared_lib_target = sym_base.join("shared-host-tree");
    fs::create_dir_all(shared_lib_target.join("other-user-data")).unwrap();
    fs::write(
        shared_lib_target.join("other-user-data/secret.txt"),
        b"unrelated",
    )
    .unwrap();
    symlink(real_prefix.join("lib/lean"), shared_lib_target.join("lean")).unwrap();
    let shared_lib_prefix = sym_base.join("shared-lib-prefix");
    fs::create_dir_all(&shared_lib_prefix).unwrap();
    symlink(&shared_lib_target, shared_lib_prefix.join("lib")).unwrap();
    let shared_err = SandboxRuntime::probe(
        SandboxMode::PreferBwrapOrLandlock,
        &lean,
        &shared_lib_prefix,
        &stage,
    )
    .unwrap_err();
    assert_eq!(shared_err.code, 2, "{shared_err}");
    assert_eq!(shared_err.phase, "sandbox", "{shared_err}");

    let polluted_stdlib = sym_base.join("polluted-stdlib");
    fs::create_dir_all(polluted_stdlib.join("Init")).unwrap();
    fs::write(polluted_stdlib.join("Init.olean"), b"olean").unwrap();
    fs::write(polluted_stdlib.join("unrelated_secret.txt"), b"secret").unwrap();
    let polluted_prefix = sym_base.join("polluted-stdlib-prefix");
    fs::create_dir_all(polluted_prefix.join("lib")).unwrap();
    symlink(&polluted_stdlib, polluted_prefix.join("lib/lean")).unwrap();
    let polluted_err = SandboxRuntime::probe(
        SandboxMode::PreferBwrapOrLandlock,
        &lean,
        &polluted_prefix,
        &stage,
    )
    .unwrap_err();
    assert_eq!(polluted_err.code, 2, "{polluted_err}");
    assert_eq!(polluted_err.phase, "sandbox", "{polluted_err}");

    // 3. Even inside a valid custom unpinned prefix, sibling files outside
    //    `lib/` and `exec_lean` (`<custom_prefix>/sibling_secret.txt`) are
    //    never mounted into either Tier 1 (`bwrap`) or Tier 2 (`Landlock`).
    let custom_prefix = sym_base.join("custom-prefix");
    fs::create_dir_all(custom_prefix.join("bin")).unwrap();
    symlink(&lean, custom_prefix.join("bin/lean")).unwrap();
    symlink(real_prefix.join("lib"), custom_prefix.join("lib")).unwrap();
    let sibling_secret = custom_prefix.join("sibling_secret.txt");
    fs::write(&sibling_secret, b"prefix-sibling-secret-payload\n").unwrap();

    // Verify `SandboxRuntime::probe` selects Tier 1 `LinuxBwrap` on the
    // symlinked custom prefix (never silently degrading to Tier 2 due to
    // `DT_RUNPATH` or `findSysroot` failure) and compiles a clean
    // `import Init.Prelude` module via `-R` in both tiers.
    let probed_custom =
        SandboxRuntime::probe(SandboxMode::RequireBwrap, &lean, &custom_prefix, &stage).unwrap();
    assert_eq!(probed_custom.backend, ActiveSandbox::LinuxBwrap);

    for (label, runtime) in [
        ("tier1", probed_custom),
        ("tier2", force_tier2_runtime(&lean, &custom_prefix).unwrap()),
    ] {
        let ok_dir = sym_base.join(format!("{label}-custom-ok"));
        let ok_in = ok_dir.join("in");
        let ok_out = ok_dir.join("out");
        let ok_tmp = ok_dir.join("tmp");
        create_dir_mode(&ok_in, 0o700).unwrap();
        create_dir_mode(&ok_out, 0o700).unwrap();
        create_dir_mode(&ok_tmp, 0o700).unwrap();
        let ok_src = ok_in.join("CustomOk.lean");
        fs::write(&ok_src, b"import Init.Prelude\ndef customOk : Nat := 7\n").unwrap();
        set_mode(&ok_src, 0o444).unwrap();
        set_mode(&ok_in, 0o500).unwrap();
        let ok_ro = vec![MountSpec {
            host: ok_in.clone(),
            child: PathBuf::from("/work/in"),
        }];
        let ok_rw_out = MountSpec {
            host: ok_out.clone(),
            child: PathBuf::from("/work/out"),
        };
        let ok_rw_tmp = MountSpec {
            host: ok_tmp.clone(),
            child: PathBuf::from("/work/tmp"),
        };
        let ok_mapper = PathMapper::new(&runtime, &ok_ro, &ok_rw_out, &ok_rw_tmp);
        let ok_policy = SandboxPolicy {
            exec_bin: lean.clone(),
            args: vec![
                "-j1".to_string(),
                "-M1024".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                ok_mapper.map_str(&ok_in).unwrap(),
                "-o".to_string(),
                ok_mapper.map_str(&ok_out.join("CustomOk.olean")).unwrap(),
                ok_mapper.map_str(&ok_src).unwrap(),
            ],
            ro_mounts: ok_ro,
            rw_out: ok_rw_out,
            rw_tmp: ok_rw_tmp,
            child_cwd: None,
            extra_env: BTreeMap::new(),
            timeout: Duration::from_secs(60),
        };
        let ok_res = runtime.execute(&ok_policy).unwrap();
        assert!(
            ok_res.status.success(),
            "{label} clean custom-prefix compile failed (exit {:?}):\n{}",
            ok_res.status.code(),
            String::from_utf8_lossy(&ok_res.stderr)
        );

        for probe_target in [
            sibling_secret.to_string_lossy().into_owned(),
            "/toolchain/sibling_secret.txt".to_string(),
        ] {
            let run_dir = sym_base.join(format!(
                "{label}-{}",
                probe_target.replace('/', "_")
            ));
            let in_dir = run_dir.join("in");
            let out_dir = run_dir.join("out");
            let tmp_dir = run_dir.join("tmp");
            create_dir_mode(&in_dir, 0o700).unwrap();
            create_dir_mode(&out_dir, 0o700).unwrap();
            create_dir_mode(&tmp_dir, 0o700).unwrap();

            let src = in_dir.join("LeakSibling.lean");
            let code = format!(
                "import Init.System.IO\n\
                 #eval show IO Unit from do\n\
                   let s ← IO.FS.readFile \"{probe_target}\"\n\
                   IO.println s\n"
            );
            fs::write(&src, code).unwrap();
            set_mode(&src, 0o444).unwrap();
            set_mode(&in_dir, 0o500).unwrap();

            let ro = vec![MountSpec {
                host: in_dir.clone(),
                child: PathBuf::from("/work/in"),
            }];
            let rw_out = MountSpec {
                host: out_dir.clone(),
                child: PathBuf::from("/work/out"),
            };
            let rw_tmp = MountSpec {
                host: tmp_dir.clone(),
                child: PathBuf::from("/work/tmp"),
            };
            let mapper = PathMapper::new(&runtime, &ro, &rw_out, &rw_tmp);
            let policy = SandboxPolicy {
                exec_bin: lean.clone(),
                args: vec![
                    "-j1".to_string(),
                    "-M1024".to_string(),
                    "-t0".to_string(),
                    "-R".to_string(),
                    mapper.map_str(&in_dir).unwrap(),
                    "-o".to_string(),
                    mapper.map_str(&out_dir.join("LeakSibling.olean")).unwrap(),
                    mapper.map_str(&src).unwrap(),
                ],
                ro_mounts: ro,
                rw_out,
                rw_tmp,
                child_cwd: None,
                extra_env: BTreeMap::new(),
                timeout: Duration::from_secs(60),
            };
            let out = runtime.execute(&policy).unwrap();
            assert!(
                !out.status.success(),
                "{label} reading {probe_target} must fail inside sandbox"
            );
            let combined = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            assert!(
                !combined.contains("prefix-sibling-secret-payload"),
                "{label} leaked sibling secret via {probe_target}: {combined}"
            );
        }
    }
    make_tree_writable(&sym_base);
}

#[test]
fn tier1_bwrap_enforces_seccomp_and_disables_nested_userns() {
    const CHECK_ENV: &str = "ANNEAL_TIER1_SECCOMP_CHECK";
    if env::var_os(CHECK_ENV).is_some() {
        let status = fs::read_to_string("/proc/self/status").expect("read /proc/self/status");
        assert!(
            status.lines().any(|l| l.trim() == "Seccomp:\t2"),
            "expected Seccomp: 2 (SECCOMP_MODE_FILTER) inside Tier 1 bwrap, got:\n{status}"
        );
        // SAFETY: probe syscalls with valid constants; failure with EPERM is
        // asserted.
        unsafe {
            let sock = libc::socket(libc::AF_INET, libc::SOCK_STREAM, 0);
            assert_eq!(sock, -1, "AF_INET socket must be blocked by Tier 1 seccomp");
            assert_eq!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::EPERM),
                "expected EPERM from Tier 1 seccomp on socket()"
            );

            let unshare_rc = libc::unshare(libc::CLONE_NEWUSER);
            assert_eq!(
                unshare_rc, -1,
                "unshare(CLONE_NEWUSER) must be blocked inside Tier 1 bwrap"
            );
            assert_eq!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::EPERM),
                "expected EPERM from Tier 1 seccomp/disable-userns on unshare()"
            );

            let fork_rc = libc::fork();
            assert_eq!(fork_rc, -1, "fork() must be blocked by Tier 1 seccomp");
            assert_eq!(
                std::io::Error::last_os_error().raw_os_error(),
                Some(libc::EPERM),
                "expected EPERM from Tier 1 seccomp on fork()"
            );
        }
        return;
    }

    let exe = fs::canonicalize(env::current_exe().unwrap()).unwrap();
    let exe_dir = exe.parent().unwrap().to_path_buf();
    let runtime = force_tier1_runtime(&exe, &exe_dir).unwrap();
    assert!(
        runtime.bwrap_seccomp_active,
        "Tier 1 runtime must enable seccomp-BPF on x86_64/aarch64 Linux"
    );

    let base_dir = tempfile::tempdir().unwrap();
    let base = fs::canonicalize(base_dir.path()).unwrap();
    let out_dir = base.join("out");
    let tmp_dir = base.join("tmp");
    create_dir_mode(&out_dir, 0o700).unwrap();
    create_dir_mode(&tmp_dir, 0o700).unwrap();

    let test_name = match module_path!().split_once("::") {
        Some((_, sub)) => {
            format!("{sub}::tier1_bwrap_enforces_seccomp_and_disables_nested_userns")
        }
        None => "tier1_bwrap_enforces_seccomp_and_disables_nested_userns".to_string(),
    };
    let mut extra_env = BTreeMap::new();
    extra_env.insert(CHECK_ENV.to_string(), "1".to_string());
    let policy = SandboxPolicy {
        exec_bin: exe.clone(),
        args: vec!["--exact".to_string(), test_name.clone(), "--nocapture".to_string()],
        ro_mounts: Vec::new(),
        rw_out: MountSpec { host: out_dir, child: PathBuf::from("/work/out") },
        rw_tmp: MountSpec { host: tmp_dir, child: PathBuf::from("/work/tmp") },
        child_cwd: None,
        extra_env,
        timeout: Duration::from_secs(30),
    };
    let output = runtime.execute(&policy).unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success() && stdout.contains("1 passed; 0 failed"),
        "Tier 1 seccomp/disable-userns probe failed or matched 0 tests (filter={test_name}):\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}
