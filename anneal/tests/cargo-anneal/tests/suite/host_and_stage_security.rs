// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Host-boundary spoofing, symlink/manifest checks, and env isolation tests.

use std::{
    ffi::OsStr,
    fs,
    os::unix::fs::symlink,
    path::Path,
};

use anneal_testkit::assertions::assert_verified_untainted;
use serde_json::{Value, json};

use crate::helpers::{
    SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, corpus_path, expect_failed, expect_verified,
    new_workspace, run_verify_inv, run_verify_strs, sha256_hex, subcrate_request_json,
    verify_invocation, with_host_cargo_env, write_json_file, write_scalar_baseline,
};

mod compiler_overrides_and_cargo_config;

fn copy_compiled_module_artifacts(src_dir: &Path, dst_dir: &Path, stems: &[&str]) -> Vec<String> {
    fs::create_dir_all(dst_dir).unwrap();
    let mut copied = Vec::new();
    for entry in fs::read_dir(src_dir).expect("read lean-lib dir") {
        let entry = entry.unwrap();
        if !entry.file_type().unwrap().is_file() {
            continue;
        }
        let name = entry.file_name().to_string_lossy().into_owned();
        if stems.iter().any(|stem| name.starts_with(&format!("{stem}."))) {
            let dst = dst_dir.join(&name);
            fs::copy(entry.path(), &dst).unwrap();
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fs::set_permissions(&dst, fs::Permissions::from_mode(0o644)).unwrap();
            }
            copied.push(name);
        }
    }
    copied.sort();
    assert!(
        copied.iter().any(|n| n == "Proof.olean") && copied.iter().any(|n| n == "Captured.olean"),
        "expected Proof.olean and Captured.olean in copied artifacts, got {copied:?}"
    );
    copied
}

fn capture_json_semantic_fingerprint(artifacts_dir: &Path) -> Value {
    let raw = fs::read_to_string(artifacts_dir.join("capture/capture.json")).unwrap();
    let manifest: Value = serde_json::from_str(&raw).unwrap();
    let source_hashes: Vec<String> = manifest["source_files"]
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["sha256"].as_str().unwrap().to_owned())
        .collect();
    json!({
        "program": manifest["program"],
        "census": manifest["census"],
        "selected": manifest["selected"],
        "source_hashes": source_hashes,
    })
}

fn retained_module_sha256(artifacts_dir: &Path, module: &str) -> String {
    let req: Value =
        serde_json::from_slice(&fs::read(artifacts_dir.join("audit-request.json")).unwrap())
            .unwrap();
    req["modules"]
        .as_array()
        .unwrap()
        .iter()
        .find(|m| m["module"] == module)
        .and_then(|m| m["expectedSha256"].as_str())
        .unwrap()
        .to_owned()
}

fn retained_capture_sha256(artifacts_dir: &Path) -> String {
    let req: Value =
        serde_json::from_slice(&fs::read(artifacts_dir.join("audit-request.json")).unwrap())
            .unwrap();
    req["bindings"]["captureSha256"].as_str().unwrap().to_owned()
}

#[test]
fn ignores_tampered_or_spoofed_files_in_dot_anneal_and_proof_olean() {
    let staged = new_workspace("anneal-spoof-").stage().unwrap();
    let work = staged.work_dir();
    let good_dir = corpus_path("scalar_specs/annotated_id");
    let bad_dir = corpus_path("scalar_specs/wrong_id_returns_zero");

    let good_rs = fs::read(good_dir.join("lib.rs")).unwrap();
    let spec_lean = fs::read(good_dir.join("Spec.lean")).unwrap();
    let proof_lean = fs::read(good_dir.join("Proof.lean")).unwrap();
    let bad_rs = fs::read(bad_dir.join("lib.rs")).unwrap();

    // 1. Unspoofed verifying baseline.
    let rust_base = work.join("rust-base");
    let lean_base = work.join("lean-base");
    fs::create_dir_all(&rust_base).unwrap();
    fs::create_dir_all(&lean_base).unwrap();
    fs::write(rust_base.join("lib.rs"), &good_rs).unwrap();
    fs::write(lean_base.join("Spec.lean"), &spec_lean).unwrap();
    fs::write(lean_base.join("Proof.lean"), &proof_lean).unwrap();
    let base_req = subcrate_request_json(&rust_base, "lib.rs", "annotated_id", &lean_base);
    let base_req_path = write_json_file(&work.join("base-req.json"), &base_req);
    let base_art = work.join("art-good-baseline");
    let base_run = run_verify_strs(
        &staged,
        &[
            "--request",
            base_req_path.to_str().unwrap(),
            "--artifacts",
            base_art.to_str().unwrap(),
            "--export-lean-lib",
        ],
    );
    let base_ok = expect_verified(&base_run, "crate_verified", true);
    assert_verified_untainted(&base_run.output).unwrap();
    assert!(cargo_anneal::is_sha256_hex(&base_ok.capture_sha256));
    assert_eq!(base_ok.capture_sha256, retained_capture_sha256(&base_art));

    let good_cap_sha = base_ok.capture_sha256.clone();
    let good_capture_json = fs::read(base_art.join("capture/capture.json")).unwrap();
    assert_eq!(good_cap_sha, sha256_hex(&good_capture_json));
    let good_captured_lean = fs::read(base_art.join("capture/Captured.lean")).unwrap();
    let good_expected_lean = fs::read(base_art.join("generated/Expected.lean")).unwrap();
    let good_mod_sha = retained_module_sha256(&base_art, "Captured");
    assert_eq!(good_mod_sha, sha256_hex(&good_captured_lean));
    let good_fingerprint = capture_json_semantic_fingerprint(&base_art);
    let good_lean_lib = base_art.join("lean-lib");

    // 2. Unspoofed failing baseline establishes distinct capture digests.
    let rust_bad_base = work.join("rust-bad-base");
    fs::create_dir_all(&rust_bad_base).unwrap();
    fs::write(rust_bad_base.join("lib.rs"), &bad_rs).unwrap();
    let bad_base_req =
        subcrate_request_json(&rust_bad_base, "lib.rs", "annotated_id", &lean_base);
    let bad_base_req_path = write_json_file(&work.join("bad-base-req.json"), &bad_base_req);
    let bad_base_art = work.join("art-bad-baseline");
    let bad_base_run = run_verify_strs(
        &staged,
        &[
            "--request",
            bad_base_req_path.to_str().unwrap(),
            "--artifacts",
            bad_base_art.to_str().unwrap(),
        ],
    );
    expect_failed(&bad_base_run, 1, "proof_failed", Some("audit"), "Proof.lean");
    let bad_cap_sha = retained_capture_sha256(&bad_base_art);
    let bad_mod_sha = retained_module_sha256(&bad_base_art, "Captured");
    let bad_fingerprint = capture_json_semantic_fingerprint(&bad_base_art);
    let bad_captured_lean = fs::read(bad_base_art.join("capture/Captured.lean")).unwrap();
    assert_ne!(bad_cap_sha, good_cap_sha);
    assert_ne!(bad_mod_sha, good_mod_sha);
    assert_ne!(bad_fingerprint, good_fingerprint);
    assert_ne!(bad_captured_lean, good_captured_lean);

    // 3. Direction (a): good crate with breaking spoofs and corrupt `.olean`s.
    let rust_a = work.join("rust-good-spoofed");
    let lean_a = work.join("lean-good-spoofed");
    fs::create_dir_all(&rust_a).unwrap();
    fs::create_dir_all(&lean_a).unwrap();
    fs::write(rust_a.join("lib.rs"), &good_rs).unwrap();
    fs::write(lean_a.join("Spec.lean"), &spec_lean).unwrap();
    fs::write(lean_a.join("Proof.lean"), &proof_lean).unwrap();

    let stems = ["Captured", "Spec", "Expected", "Proof"];
    let copied_names = copy_compiled_module_artifacts(&good_lean_lib, &lean_a, &stems);
    fs::create_dir_all(lean_a.join(".anneal")).unwrap();
    for name in &copied_names {
        fs::write(lean_a.join(name), b"corrupt olean bytes").unwrap();
        fs::write(lean_a.join(".anneal").join(name), b"corrupt olean bytes").unwrap();
    }
    let breaking_captured = "prelude\nimport Trusted.MirAst\nnamespace Captured\n\
                             def program : Trusted.MirAst.Program := { bodies := [] }\n\
                             end Captured\n";
    let invalid_lean = "this is intentionally invalid Lean syntax !!!\n";
    fs::write(lean_a.join(".anneal/Captured.lean"), breaking_captured).unwrap();
    fs::write(lean_a.join(".anneal/Proof.lean"), invalid_lean).unwrap();
    fs::write(lean_a.join(".anneal/Spec.lean"), invalid_lean).unwrap();
    fs::write(lean_a.join(".anneal/capture.json"), b"{not json").unwrap();

    fs::create_dir_all(rust_a.join(".anneal")).unwrap();
    fs::write(rust_a.join(".anneal/Captured.lean"), breaking_captured).unwrap();
    fs::write(rust_a.join(".anneal/Proof.lean"), invalid_lean).unwrap();
    fs::write(rust_a.join(".anneal/capture.json"), b"{not json").unwrap();
    fs::write(rust_a.join(".anneal/poison.rs"), b"this is invalid Rust !!!\n").unwrap();

    let req_a = subcrate_request_json(&rust_a, "lib.rs", "annotated_id", &lean_a);
    let req_a_path = write_json_file(&work.join("req-a.json"), &req_a);
    let art_a = work.join("art-good-spoofed");
    let run_a = run_verify_strs(
        &staged,
        &["--request", req_a_path.to_str().unwrap(), "--artifacts", art_a.to_str().unwrap()],
    );
    let ok_a = expect_verified(&run_a, "crate_verified", true);
    assert_eq!(ok_a.capture_sha256, retained_capture_sha256(&art_a));
    assert_ne!(ok_a.capture_sha256, sha256_hex(b"{not json"));
    assert_eq!(
        ok_a.audit["moduleIdentities"]["Captured"]["sourceSha256"].as_str(),
        Some(good_mod_sha.as_str())
    );
    assert_eq!(retained_module_sha256(&art_a, "Captured"), good_mod_sha);
    assert_eq!(capture_json_semantic_fingerprint(&art_a), good_fingerprint);
    assert_eq!(fs::read(art_a.join("capture/Captured.lean")).unwrap(), good_captured_lean);

    // 4. Direction (b): failing program with GENUINE enabling spoofs and
    //    precompiled `.olean` artifacts copied from `base_art`.
    let rust_b = work.join("rust-bad-spoofed");
    let lean_b = work.join("lean-bad-spoofed");
    fs::create_dir_all(&rust_b).unwrap();
    fs::create_dir_all(&lean_b).unwrap();
    fs::write(rust_b.join("lib.rs"), &bad_rs).unwrap();
    fs::write(lean_b.join("Spec.lean"), &spec_lean).unwrap();
    fs::write(lean_b.join("Proof.lean"), &proof_lean).unwrap();

    copy_compiled_module_artifacts(&good_lean_lib, &lean_b, &stems);
    copy_compiled_module_artifacts(&good_lean_lib, &lean_b.join(".anneal"), &stems);
    copy_compiled_module_artifacts(&good_lean_lib, &rust_b.join(".anneal"), &stems);
    for dot_anneal in [lean_b.join(".anneal"), rust_b.join(".anneal")] {
        fs::write(dot_anneal.join("Captured.lean"), &good_captured_lean).unwrap();
        fs::write(dot_anneal.join("capture.json"), &good_capture_json).unwrap();
        fs::write(dot_anneal.join("Spec.lean"), &spec_lean).unwrap();
        fs::write(dot_anneal.join("Proof.lean"), &proof_lean).unwrap();
        fs::write(dot_anneal.join("Expected.lean"), &good_expected_lean).unwrap();
    }
    fs::write(rust_b.join(".anneal/lib.rs"), &good_rs).unwrap();

    let req_b = subcrate_request_json(&rust_b, "lib.rs", "annotated_id", &lean_b);
    let req_b_path = write_json_file(&work.join("req-b.json"), &req_b);
    let art_b = work.join("art-bad-spoofed");
    let run_b = run_verify_strs(
        &staged,
        &["--request", req_b_path.to_str().unwrap(), "--artifacts", art_b.to_str().unwrap()],
    );
    expect_failed(&run_b, 1, "proof_failed", Some("audit"), "Proof.lean");
    assert_ne!(retained_capture_sha256(&art_b), good_cap_sha);
    assert_eq!(retained_module_sha256(&art_b, "Captured"), bad_mod_sha);
    assert_eq!(capture_json_semantic_fingerprint(&art_b), bad_fingerprint);
    assert_eq!(fs::read(art_b.join("capture/Captured.lean")).unwrap(), bad_captured_lean);
}

#[test]
fn rejects_symlinked_sources_and_disallowed_manifest_targets() {
    let staged = new_workspace("anneal-symlinks-").stage().unwrap();
    let work = staged.work_dir();
    let mut base_req = write_scalar_baseline(work);
    let outside = work.join("outside");
    fs::create_dir_all(&outside).unwrap();
    fs::write(outside.join("lib.rs"), SCALAR_SOURCE).unwrap();
    fs::write(outside.join("Spec.lean"), SCALAR_SPEC).unwrap();
    fs::write(outside.join("Proof.lean"), SCALAR_PROOF).unwrap();
    let lean_dir = work.join("lean");

    // 1. Symlinked `src/lib.rs` fails in both Cargo shortcut and `--request`.
    let sym_pkg = work.join("sym-pkg");
    fs::create_dir_all(sym_pkg.join("src")).unwrap();
    fs::write(
        sym_pkg.join("Cargo.toml"),
        "[package]\nname = \"sym_pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    symlink(outside.join("lib.rs"), sym_pkg.join("src/lib.rs")).unwrap();
    let sym_manifest = sym_pkg.join("Cargo.toml");
    let inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            sym_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let r = run_verify_inv(&staged, &inv);
    expect_failed(&r, 1, "unsupported", Some("request"), "unsupported or empty compilation request");

    let mut sym_rust_req = base_req.clone();
    sym_rust_req["compilation"]["source_root"] = json!(sym_pkg.join("src"));
    let sym_rust_path = write_json_file(&work.join("sym-rust.json"), &sym_rust_req);
    let r = run_verify_strs(&staged, &["--request", sym_rust_path.to_str().unwrap()]);
    expect_failed(&r, 1, "unsupported", Some("inputs"), "not a declared regular file");

    // 2. Symlinked `Spec.lean` in request mode, and symlinked `Proof.lean` in
    //    `--proof-dir` mode.
    let sym_lean = work.join("sym-lean");
    fs::create_dir_all(&sym_lean).unwrap();
    symlink(outside.join("Spec.lean"), sym_lean.join("Spec.lean")).unwrap();
    fs::write(sym_lean.join("Proof.lean"), SCALAR_PROOF).unwrap();
    let mut sym_lean_req = base_req.clone();
    sym_lean_req["proof"]["source_root"] = json!(sym_lean);
    let sym_lean_path = write_json_file(&work.join("sym-lean.json"), &sym_lean_req);
    let r = run_verify_strs(&staged, &["--request", sym_lean_path.to_str().unwrap()]);
    expect_failed(&r, 1, "unsupported", Some("inputs"), "not a declared regular file");

    let sym_proof_dir = work.join("sym-proof-dir");
    fs::create_dir_all(&sym_proof_dir).unwrap();
    fs::write(sym_proof_dir.join("Spec.lean"), SCALAR_SPEC).unwrap();
    symlink(outside.join("Proof.lean"), sym_proof_dir.join("Proof.lean")).unwrap();
    let ok_pkg = work.join("ok-pkg");
    fs::create_dir_all(ok_pkg.join("src")).unwrap();
    fs::write(
        ok_pkg.join("Cargo.toml"),
        "[package]\nname = \"ok_pkg\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(ok_pkg.join("src/lib.rs"), SCALAR_SOURCE).unwrap();
    let ok_manifest = ok_pkg.join("Cargo.toml");
    let inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            ok_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            sym_proof_dir.as_os_str(),
        ]),
    );
    let r = run_verify_inv(&staged, &inv);
    expect_failed(
        &r,
        1,
        "unsupported",
        Some("proof"),
        "specification and theorem must have their declared source roles",
    );

    // 3. Path traversal `..` in `source_files`.
    base_req["compilation"]["source_files"] = json!(["lib.rs", "../outside/lib.rs"]);
    let dotdot_path = write_json_file(&work.join("dotdot.json"), &base_req);
    let r = run_verify_strs(&staged, &["--request", dotdot_path.to_str().unwrap()]);
    expect_failed(&r, 1, "unsupported", Some("inputs"), "clean relative paths");

    // 4. Empty `[dependencies]` passes; non-empty `[dependencies]` rejects.
    let dep_case_pkg = work.join("pkg-dependencies");
    fs::create_dir_all(&dep_case_pkg).unwrap();
    fs::write(
        dep_case_pkg.join("Cargo.toml"),
        "[package]\nname = \"d\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [lib]\npath = \"lib.rs\"\n[dependencies]\n",
    )
    .unwrap();
    fs::write(dep_case_pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
    let dep_manifest = dep_case_pkg.join("Cargo.toml");
    let empty_dep_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            dep_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let empty_dep_res = run_verify_inv(&staged, &empty_dep_inv);
    expect_verified(&empty_dep_res, "crate_verified", true);

    let dep_target = work.join("dep-target");
    fs::create_dir_all(&dep_target).unwrap();
    fs::write(
        dep_target.join("Cargo.toml"),
        "[package]\nname = \"dep_target\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [lib]\npath = \"lib.rs\"\n",
    )
    .unwrap();
    fs::write(dep_target.join("lib.rs"), "pub fn g() -> u64 { 0 }\n").unwrap();
    fs::write(
        &dep_manifest,
        format!(
            "[package]\nname = \"d\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             [lib]\npath = \"lib.rs\"\n[dependencies]\ndep_target = {{ path = {:?} }}\n",
            dep_target.display().to_string()
        ),
    )
    .unwrap();
    let nonempty_dep_res = run_verify_inv(&staged, &empty_dep_inv);
    expect_failed(
        &nonempty_dep_res,
        1,
        "unsupported",
        Some("cargo"),
        "Cargo shortcut requires a dependency-free crate",
    );

    // 4b. Cargo `[features]`, `[dev-dependencies]`, inactive optional
    // `[dependencies]`, and top-level `benches/` work out-of-the-box, whereas
    // activating an optional dependency fails closed.
    let feat_pkg = work.join("pkg-cargo-features");
    fs::create_dir_all(feat_pkg.join("src")).unwrap();
    fs::create_dir_all(feat_pkg.join("benches")).unwrap();
    fs::write(feat_pkg.join("src/lib.rs"), SCALAR_SOURCE).unwrap();
    fs::write(
        feat_pkg.join("benches/bench.rs"),
        "compile_error!(\"benches must not be staged in library shortcut\");\n",
    )
    .unwrap();
    let opt_dep_dir = work.join("opt-dep");
    fs::create_dir_all(opt_dep_dir.join("src")).unwrap();
    fs::write(
        opt_dep_dir.join("Cargo.toml"),
        "[package]\nname = \"opt_dep\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(opt_dep_dir.join("src/lib.rs"), "").unwrap();
    let dev_dep_dir = work.join("dev-dep");
    fs::create_dir_all(dev_dep_dir.join("src")).unwrap();
    fs::write(
        dev_dep_dir.join("Cargo.toml"),
        "[package]\nname = \"dev_dep\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
    )
    .unwrap();
    fs::write(dev_dep_dir.join("src/lib.rs"), "").unwrap();
    let feat_manifest = feat_pkg.join("Cargo.toml");
    fs::write(
        &feat_manifest,
        format!(
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\nopt_dep = {{ path = {:?}, optional = true }}\n\n\
             [dev-dependencies]\ndev_dep = {{ path = {:?} }}\n\n\
             [features]\ndefault = [\"foo\"]\nfoo = []\nwith_opt = [\"dep:opt_dep\"]\n",
            opt_dep_dir.display().to_string(),
            dev_dep_dir.display().to_string(),
        ),
    )
    .unwrap();
    let feat_inv = with_host_cargo_env(
        &staged,
        verify_invocation(&[
            OsStr::new("--manifest-path"),
            feat_manifest.as_os_str(),
            OsStr::new("--proof-dir"),
            lean_dir.as_os_str(),
        ]),
    );
    let feat_ok = run_verify_inv(&staged, &feat_inv);
    let feat_ok_rec = expect_verified(&feat_ok, "crate_verified", true);
    let feat_sources: Vec<&str> = feat_ok_rec
        .sources
        .as_array()
        .expect("sources array")
        .iter()
        .map(|entry| entry["relative_path"].as_str().expect("source relative_path"))
        .collect();
    assert_eq!(feat_sources, vec!["src/lib.rs"], "{:?}", feat_ok_rec.sources);
    assert!(
        !feat_sources.iter().any(|path| path.contains("benches")),
        "{:?}",
        feat_ok_rec.sources
    );

    fs::write(
        &feat_manifest,
        format!(
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n\
             [dependencies]\nopt_dep = {{ path = {:?}, optional = true }}\n\n\
             [features]\ndefault = [\"with_opt\"]\nwith_opt = [\"dep:opt_dep\"]\n",
            opt_dep_dir.display().to_string(),
        ),
    )
    .unwrap();
    let active_opt_res = run_verify_inv(&staged, &feat_inv);
    expect_failed(
        &active_opt_res,
        1,
        "unsupported",
        Some("cargo"),
        "activates dependency `opt_dep`",
    );

    // 5. Remaining disallowed Cargo shortcut targets/manifests.
    for (case, toml, extra_files, detail) in [
        (
            "virtual-workspace",
            "[workspace]\nmembers = []\n",
            &[][..],
            "choose a package Cargo.toml, not a virtual workspace",
        ),
        (
            "build-script",
            "[package]\nname = \"b\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             build = \"build.rs\"\n[lib]\npath = \"lib.rs\"\n",
            &[("build.rs", "fn main() {}\n")][..],
            "build scripts and procedural macros need an explicit configured compilation",
        ),
        (
            "proc-macro",
            "[package]\nname = \"p\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             [lib]\npath = \"lib.rs\"\nproc-macro = true\n",
            &[][..],
            "build scripts and procedural macros need an explicit configured compilation",
        ),
        (
            "example-only",
            "[package]\nname = \"e\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             [[example]]\nname = \"ex\"\npath = \"lib.rs\"\n",
            &[][..],
            "Cargo shortcut requires a single library or binary target",
        ),
        (
            "lib-and-bin",
            "[package]\nname = \"m\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             [lib]\npath = \"lib.rs\"\n[[bin]]\nname = \"b\"\npath = \"lib.rs\"\n",
            &[][..],
            "Cargo shortcut requires a single library or binary target",
        ),
        (
            "multi-bin",
            "[package]\nname = \"mb\"\nversion = \"0.0.0\"\nedition = \"2024\"\n",
            &[("src/main.rs", "fn main() {}\n"), ("src/bin/extra.rs", "fn main() {}\n")][..],
            "Cargo shortcut requires a single library or binary target",
        ),
    ] {
        let pkg = work.join(format!("pkg-{case}"));
        fs::create_dir_all(&pkg).unwrap();
        fs::write(pkg.join("Cargo.toml"), toml).unwrap();
        if extra_files.is_empty() {
            fs::write(pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
        } else {
            for (rel, body) in extra_files {
                let p = pkg.join(rel);
                if let Some(parent) = p.parent() {
                    fs::create_dir_all(parent).unwrap();
                }
                fs::write(p, body).unwrap();
            }
            if case == "build-script" {
                fs::write(pkg.join("lib.rs"), SCALAR_SOURCE).unwrap();
            }
        }
        let manifest = pkg.join("Cargo.toml");
        let inv = with_host_cargo_env(
            &staged,
            verify_invocation(&[
                OsStr::new("--manifest-path"),
                manifest.as_os_str(),
                OsStr::new("--proof-dir"),
                lean_dir.as_os_str(),
            ]),
        );
        let res = run_verify_inv(&staged, &inv);
        expect_failed(&res, 1, "unsupported", Some("cargo"), detail);
    }
}

#[test]
fn fast_check_passes_elaboration_and_skips_receipt_end_to_end() {
    let staged = new_workspace("anneal-fast-check-e2e-").stage().unwrap();
    let work = staged.work_dir();
    write_scalar_baseline(work);
    let lean_dir = work.join("lean");
    let manifest = work.join("Cargo.toml");
    fs::write(
        &manifest,
        "[package]\nname = \"scalar\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
         [lib]\npath = \"lib.rs\"\n",
    )
    .unwrap();
    fs::write(work.join("lib.rs"), SCALAR_SOURCE).unwrap();

    let tools = crate::helpers::workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cli binary");
    let capture = tools.capture.as_deref().expect("workspace capture binary");
    let inv = with_host_cargo_env(
        &staged,
        anneal_testkit::Invocation::new(cli, &["verify", "--fast-check", "--format", "auto"])
            .arg("--capture")
            .arg(capture)
            .arg("--lean")
            .arg(&tools.lean)
            .arg("--sysroot")
            .arg(&tools.sysroot)
            .arg("--manifest-path")
            .arg(&manifest)
            .arg("--proof-dir")
            .arg(&lean_dir),
    );
    let run = staged.exec(&inv).expect("execute cargo-anneal verify --fast-check");
    run.process.expect_code(3).unwrap();
    let stdout = String::from_utf8_lossy(&run.process.stdout);
    let stderr = String::from_utf8_lossy(&run.process.stderr);
    assert!(stdout.contains("[UNVERIFIED_DEV_ONLY]"), "{stdout}");
    assert!(stdout.contains("fast_check_dev_mode"), "{stdout}");
    assert!(stdout.contains("exited 3"), "{stdout}");
    assert!(stderr.contains("TAINTED"), "{stderr}");
    assert!(stderr.contains("UNVERIFIED_DEV_ONLY"), "{stderr}");
    assert!(serde_json::from_slice::<Value>(&run.process.stdout).is_err(), "{stdout}");

    // An elaboration-failing proof still fails closed with exit code `1` under
    // `--fast-check`.
    fs::write(
        lean_dir.join("Proof.lean"),
        "import Expected\ntheorem verify : Expected.claim := ()\n",
    )
    .unwrap();
    let bad_run =
        staged.exec(&inv).expect("execute cargo-anneal verify --fast-check on broken proof");
    bad_run.process.expect_code(1).unwrap();
    let bad_stdout = String::from_utf8_lossy(&bad_run.process.stdout);
    let bad_stderr = String::from_utf8_lossy(&bad_run.process.stderr);
    assert!(bad_stdout.contains("[FAIL]"), "{bad_stdout}");
    assert!(bad_stdout.contains("proof_failed"), "{bad_stdout}");
    assert!(bad_stdout.contains("fast_check_dev_mode"), "{bad_stdout}");
    assert!(bad_stderr.contains("TAINTED"), "{bad_stderr}");
    assert!(serde_json::from_slice::<Value>(&bad_run.process.stdout).is_err(), "{bad_stdout}");
}
