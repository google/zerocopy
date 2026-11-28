// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `selected_unit` scope normalization and boundary rejections, and the
//! binding of unsafe contracts to function identities.

use super::*;

fn selected_request(req: &Value) -> Value {
    let mut copy = req.clone();
    copy["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    copy
}

#[test]
fn selected_unit_normalization_and_boundary_rejections() {
    let staged = new_workspace("anneal-sel-boundary-").stage().unwrap();
    let work = staged.work_dir();
    let request = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("whole-crate.json"), &request);
    let whole_art = work.join("whole-crate");
    let first = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", whole_art.to_str().unwrap()],
    );
    expect_verified(&first, "crate_verified", true);

    // Selected unit normalization vs whole-crate unsupported failure.
    fs::write(work.join("rust/lib.rs"), SCALAR_UNSUPPORTED).unwrap();
    let mut sel_req = selected_request(&request);
    sel_req["scope"]["roots"] = json!(["zero", "zero"]);
    sel_req["compilation"]["cfg"] = json!(["omega", "alpha", "omega"]);
    let norm_path = write_json_file(&work.join("norm.json"), &sel_req);
    let normalized = run_verify_strs(&staged, &["--request", norm_path.to_str().unwrap()]);
    let norm_ok = expect_verified(&normalized, "selected_unit_verified", true);
    assert_eq!(norm_ok.scope["roots"], json!(["zero"]));
    assert_eq!(norm_ok.configuration["cfg"], json!(["alpha", "omega"]));
    assert!(
        norm_ok
            .census
            .as_array()
            .unwrap()
            .iter()
            .any(|item| item["path"] == "unsupported" && item["selected"] == false)
    );
    sel_req["scope"]["roots"] = json!(["zero"]);
    sel_req["compilation"]["cfg"] = json!(["alpha", "omega"]);
    let ord_path = write_json_file(&work.join("ord.json"), &sel_req);
    let ordered = run_verify_strs(&staged, &["--request", ord_path.to_str().unwrap()]);
    let ord_ok = expect_verified(&ordered, "selected_unit_verified", true);
    assert_eq!(norm_ok.request_sha256, ord_ok.request_sha256);

    let r = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_failed(&r, 1, "unsupported", Some("capture"), "unsupported");

    fs::write(work.join("rust/lib.rs"), SCALAR_DEPENDENCY).unwrap();
    let sel_only = write_json_file(&work.join("sel-only.json"), &selected_request(&request));
    let r = run_verify_strs(&staged, &["--request", sel_only.to_str().unwrap()]);
    expect_failed(&r, 1, "unsupported", Some("capture"), "unsupported");
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    // Cargo shortcut checks (default features, `--no-default-features` +
    // `--features`, and fail-closed optional-dependency activation).
    let manifest = work.join("rust/Cargo.toml");
    let manifest_base = "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
                         [lib]\npath = \"lib.rs\"\n";
    let opt_dep = work.join("opt-dep");
    fs::create_dir_all(opt_dep.join("src")).unwrap();
    fs::write(
        opt_dep.join("Cargo.toml"),
        "[package]\nname = \"opt_dep\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(opt_dep.join("src/lib.rs"), "").unwrap();
    fs::write(
        &manifest,
        format!(
            "{manifest_base}[dependencies]\nopt_dep = {{ path = {:?}, optional = true }}\n\
             [features]\ndefault = [\"extra\"]\nextra = []\nwith_dep = [\"dep:opt_dep\"]\n",
            opt_dep.display().to_string()
        ),
    )
    .unwrap();
    fs::write(
        work.join("rust/lib.rs"),
        format!(
            "#[cfg(not(all(feature = \"default\", feature = \"extra\")))]\n\
             compile_error!(\"missing default Cargo features\");\n{SCALAR_SOURCE}"
        ),
    )
    .unwrap();
    let lean_dir = work.join("lean");
    let default_feat_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let default_feat_res = run_verify_inv(&staged, &default_feat_inv);
    let default_feat_rec = expect_verified(&default_feat_res, "crate_verified", true);
    assert_eq!(
        default_feat_rec.configuration["cfg"],
        json!(["feature=\"default\"", "feature=\"extra\""])
    );

    fs::write(
        work.join("rust/lib.rs"),
        format!(
            "#[cfg(feature = \"default\")]\ncompile_error!(\"default feature still enabled\");\n\
             #[cfg(not(feature = \"extra\"))]\ncompile_error!(\"missing extra feature\");\n{SCALAR_SOURCE}"
        ),
    )
    .unwrap();
    let custom_feat_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
            OsStr::new("--no-default-features"),
            OsStr::new("--features"),
            OsStr::new("extra"),
        ]),
    );
    let custom_feat_res = run_verify_inv(&staged, &custom_feat_inv);
    let custom_feat_rec = expect_verified(&custom_feat_res, "crate_verified", true);
    assert_eq!(custom_feat_rec.configuration["cfg"], json!(["feature=\"extra\""]));

    for (extra_args, expected_detail) in [
        (&[OsStr::new("--features"), OsStr::new("with_dep")][..], "activates dependency `opt_dep`"),
        (&[OsStr::new("--all-features")], "activates dependency `opt_dep`"),
        (
            &[OsStr::new("--features"), OsStr::new("nonexistent")],
            "does not have feature `nonexistent`",
        ),
    ] {
        let mut args = vec![
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ];
        args.extend_from_slice(extra_args);
        let bad_inv = with_host_cargo_env(&staged, verify_invocation(&args));
        let bad_res = run_verify_inv(&staged, &bad_inv);
        expect_failed(&bad_res, 1, "unsupported", Some("cargo"), expected_detail);
    }
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    fs::write(&manifest, manifest_base).unwrap();
    fs::create_dir(lean_dir.join(".cache")).unwrap();
    fs::write(lean_dir.join(".cache/Ignored.lean"), b"not valid Lean syntax").unwrap();
    let good_cargo_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    )
    .env("RUSTC", work.join("nonexistent-rustc"));
    let r = run_verify_inv(&staged, &good_cargo_inv);
    expect_verified(&r, "crate_verified", true);

    // Workspace-root compiler overrides fail closed on member manifests.
    let ws_root = work.join("workspace-override");
    fs::create_dir_all(ws_root.join(".cargo")).unwrap();
    fs::create_dir_all(ws_root.join("member")).unwrap();
    fs::write(
        ws_root.join("Cargo.toml"),
        "[workspace]\nmembers = [\"member\"]\nresolver = \"2\"\n",
    )
    .unwrap();
    fs::write(
        ws_root.join(".cargo/config.toml"),
        "[build]\nrustflags = [\"--cfg=override_flag\"]\n",
    )
    .unwrap();
    fs::write(ws_root.join("member/Cargo.toml"), manifest_base).unwrap();
    fs::write(ws_root.join("member/lib.rs"), SCALAR_SOURCE).unwrap();
    let member_manifest = ws_root.join("member/Cargo.toml");
    let ws_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            member_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let r = run_verify_inv(&staged, &ws_inv);
    expect_failed(
        &r,
        1,
        "unsupported",
        Some("cargo"),
        "compiler overrides need an explicit configured compilation",
    );

    // Reserved runner/toolchain module names fail before compiling.
    for module in ["Anneal.Shadow", "Anneal", "Trusted", "Trusted.Shadow", "Captured", "Expected"] {
        let mut reserved = request.clone();
        reserved["proof"]["sources"]
            .as_array_mut()
            .unwrap()
            .push(json!({"module": module, "path": "Proof.lean", "role": "proof"}));
        let p = write_json_file(&work.join(format!("res-{module}.json")), &reserved);
        let r = run_verify_strs(&staged, &["--request", p.to_str().unwrap()]);
        expect_failed(
            &r,
            1,
            "unsupported",
            Some("proof"),
            "invalid, duplicate or reserved proof module",
        );
    }

    // Retention preserves caller artifacts when invalid request fails early.
    let mut invalid = request.clone();
    invalid["schema_version"] = json!(0);
    let invalid_path = write_json_file(&work.join("invalid.json"), &invalid);
    let sentinel = whole_art.join("sentinel");
    fs::write(&sentinel, b"keep existing evidence").unwrap();
    let r = run_verify_strs(
        &staged,
        &["--request", invalid_path.to_str().unwrap(), "--artifacts", whole_art.to_str().unwrap()],
    );
    expect_failed(&r, 2, "tool_failed", Some("retention"), "exists");
    assert_eq!(fs::read(sentinel).unwrap(), b"keep existing evidence");

    // Missing capture executable fails as capture-tool error.
    let tools = workspace_tools();
    let missing_inv = Invocation::new(tools.cli.as_deref().unwrap(), &["verify", "--format", "json"])
        .arg("--request")
        .arg(&req_path)
        .arg("--capture")
        .arg(work.join("missing-capture"))
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot);
    let r = run_verify_inv(&staged, &missing_inv);
    expect_failed(&r, 2, "tool_failed", Some("capture-tool"), "cannot inspect");

    // Safe divergence verifies cleanly via `corpora/spin`.
    let spin_dir = corpus_path("spin");
    fs::write(work.join("rust/lib.rs"), fs::read(spin_dir.join("lib.rs")).unwrap()).unwrap();
    fs::write(work.join("lean/Spec.lean"), fs::read(spin_dir.join("Spec.lean")).unwrap()).unwrap();
    fs::write(work.join("lean/Proof.lean"), fs::read(spin_dir.join("Proof.lean")).unwrap())
        .unwrap();
    let spin_run = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_verified(&spin_run, "crate_verified", true);
}

#[test]
fn unsafe_contracts_remain_bound_to_function_identities() {
    let staged = new_workspace("anneal-unsafe-id-").stage().unwrap();
    let work = staged.work_dir();
    let uid = corpus_path("unsafe_identity");

    let rust = work.join("rust");
    let lean = work.join("lean");
    fs::create_dir_all(&rust).unwrap();
    fs::create_dir_all(&lean).unwrap();
    let src = fs::read_to_string(uid.join("lib.rs")).unwrap();
    fs::write(rust.join("lib.rs"), &src).unwrap();
    fs::write(lean.join("Spec.lean"), fs::read(uid.join("Spec.lean")).unwrap()).unwrap();
    fs::write(lean.join("Proof.lean"), fs::read(uid.join("Proof.lean")).unwrap()).unwrap();

    let req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": rust,
            "crate_root": "lib.rs",
            "crate_name": "unsafe_identity",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": lean,
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let req_path = write_json_file(&work.join("uid.json"), &req);
    let pass = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_verified(&pass, "crate_verified", true);

    // Replacing `locked` with `open` moves `unreachable()` away from `locked`,
    // removing the `False` safety precondition and causing audit rejection.
    let swapped = src
        .replace("pub unsafe fn locked()", "pub unsafe fn tmp_open()")
        .replace("pub unsafe fn open()", "pub unsafe fn locked()")
        .replace("pub unsafe fn tmp_open()", "pub unsafe fn open()");
    fs::write(rust.join("lib.rs"), swapped).unwrap();
    let swapped_run = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_failed(&swapped_run, 1, "proof_failed", Some("audit"), "Proof.lean");
}
