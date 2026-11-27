// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Live Lean compilation under both sandbox tiers: hostile `#eval`
//! blocking and the tier 2 memory limit.

use super::*;

#[test]
fn live_lean_compiles_and_blocks_hostile_eval_in_tier1_and_tier2() {
    let lean = fs::canonicalize(installed_lean()).unwrap();
    let prefix = lean_prefix(&lean).unwrap();
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

        let ro_mounts = vec![MountSpec {
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

        let h_ro = vec![MountSpec {
            host: h_in.clone(),
            child: PathBuf::from("/work/in"),
        }];
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

        let i_ro = vec![MountSpec {
            host: i_in.clone(),
            child: PathBuf::from("/work/in"),
        }];
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
                "-M2048".to_string(),
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
    let prefix = lean_prefix(&lean).unwrap();
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

    let ro_mounts = vec![MountSpec {
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
