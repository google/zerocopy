// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Schema v3 receipts, boundary mutation rejection, `rustc` mode, and taint.

use std::{env, ffi::OsStr, fs, os::unix::fs::symlink, path::PathBuf};

use anneal_testkit::Invocation;
use serde_json::{Value, json};

use crate::helpers::{
    SCALAR_DEPENDENCY, SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, SCALAR_UNSUPPORTED, anneal_root,
    corpus_path, expect_failed, expect_verified, lean_module_source, lean_source, new_workspace,
    run_verify_inv, run_verify_strs, sha256_hex, verify_invocation, with_host_cargo_env,
    workspace_tools, write_json_file, write_scalar_baseline,
};

fn selected_request(req: &Value) -> Value {
    let mut copy = req.clone();
    copy["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    copy
}

#[test]
fn canonicalizes_symlinked_temporary_directory_source_bindings() {
    let staged = new_workspace("anneal-canon-root-").stage().unwrap();
    let work = staged.work_dir();
    let temporary = work.join("temporary-physical");
    fs::create_dir(&temporary).unwrap();
    let alias = work.join("temporary-alias");
    symlink(&temporary, &alias).unwrap();
    let real_parent = work.join("real");
    fs::create_dir(&real_parent).unwrap();
    let alias_parent = work.join("alias");
    symlink(&real_parent, &alias_parent).unwrap();

    let rust = real_parent.join("rust");
    let lean = real_parent.join("lean");
    fs::create_dir(&rust).unwrap();
    fs::create_dir(&lean).unwrap();
    fs::write(rust.join("lib.rs"), SCALAR_SOURCE).unwrap();
    fs::write(lean.join("Spec.lean"), SCALAR_SPEC).unwrap();
    fs::write(lean.join("Proof.lean"), SCALAR_PROOF).unwrap();

    // Canonicalize symlinked `TMPDIR` and `source_root` without leaking temp
    // artifacts or widening `include!` reads to undeclared files.
    let req = json!({
        "schema_version": 1,
        "compilation": {
            "source_root": alias_parent.join("rust"),
            "crate_root": "lib.rs",
            "crate_name": "scalar",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"]
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": alias_parent.join("lean"),
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"}
            ]
        }
    });
    let req_path = write_json_file(&work.join("alias-req.json"), &req);
    let art = work.join("canon-run");
    let inv = verify_invocation(&[
        OsStr::new("--request"),
        req_path.as_os_str(),
        OsStr::new("--artifacts"),
        art.as_os_str(),
    ])
    .env("TMPDIR", &alias);
    let run = run_verify_inv(&staged, &inv);
    let ok = expect_verified(&run, "crate_verified", true);
    assert_eq!(ok.audit["exactType"], true);
    assert_eq!(ok.audit["replay"], true);
    let bytes = fs::read(art.join("capture/capture.json")).unwrap();
    let captured: Value = serde_json::from_slice(&bytes).unwrap();
    assert_eq!(captured["source_files"].as_array().unwrap().len(), 1);
    let input = &captured["source_files"][0];
    let input_path = PathBuf::from(input["path"].as_str().unwrap());
    assert!(input_path.starts_with(fs::canonicalize(&temporary).unwrap()));
    assert_eq!(input["path"], captured["configuration"]["crate_root"]);
    assert_eq!(input["sha256"], sha256_hex(SCALAR_SOURCE.as_bytes()));
    assert_eq!(input["sha256"], ok.sources[0]["sha256"]);
    assert_eq!(ok.capture_sha256, sha256_hex(&bytes));
    assert!(art.join("capture/Captured.lean").is_file());
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());

    let undeclared = work.join("undeclared.rs");
    fs::write(&undeclared, "0").unwrap();
    fs::write(
        rust.join("lib.rs"),
        format!(
            "pub fn zero() -> u64 {{ include!({}) }}\n",
            serde_json::to_string(&undeclared).unwrap()
        ),
    )
    .unwrap();
    let undec_art = work.join("undeclared-run");
    let undec_inv = verify_invocation(&[
        OsStr::new("--request"),
        req_path.as_os_str(),
        OsStr::new("--artifacts"),
        undec_art.as_os_str(),
    ])
    .env("TMPDIR", &alias);
    let undec_run = run_verify_inv(&staged, &undec_inv);
    expect_failed(&undec_run, 1, "unsupported", Some("capture"), "undeclared compiler read");
    assert!(!undec_art.join("capture/capture.json").exists());
    assert!(fs::read_dir(&temporary).unwrap().next().is_none());
}

fn check_provenance_and_toolchain(ok: &anneal_testkit::VerifySuccessReceipt) {
    let expected_identity = if cfg!(target_os = "linux") {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "Lean runtime shared libraries in LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules"
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Rust compiler and sysroot, identified by their reported commit"
            ]
        })
    } else {
        json!({
            "sha256_locked": [
                "Lean executable in foundation-lock.json",
                "foundation-lock.json modules",
                "Lean sysroot Init/Std/Lean .olean/.ir artifacts in LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256",
                "imported library-lock.json modules"
            ],
            "sha256_recorded": ["capture executable as capture_binary_sha256"],
            "unhashed": [
                "Lean shared libraries, identified by lean --version",
                "Rust compiler and sysroot, identified by their reported commit"
            ]
        })
    };
    assert_eq!(ok.toolchain_identity, expected_identity);

    let prov = &ok.correspondence_provenance;
    assert_eq!(prov["schema_version"], 1);
    assert_eq!(prov["upstream_repository"], "https://github.com/proofs-rs/lean-miri.git");
    assert_eq!(prov["upstream_commit"], "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a");
    assert_eq!(prov["build_lean_toolchain"], "leanprover/lean4:v4.34.1");
    assert_eq!(
        prov["sysroot_foundation_manifest_sha256"],
        cargo_anneal::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256
    );
    assert_eq!(prov["upstream_pin_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(prov["correspondence_adapters"].as_object().unwrap().len(), 7);
    assert_eq!(
        prov["correspondence_adapters"]["trusted/correspondence/Trusted/Correspondence.lean"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
    assert_eq!(prov["patched_files"].as_array().unwrap().len(), 13);
    assert_eq!(prov["correspondence_proofs"].as_object().unwrap().len(), 19);
    for proof_key in [
        "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
        "correspondence/Anneal/MirCorrespondence/LayoutAndAlign.lean",
        "correspondence/Anneal/MirCorrespondence/MiriMemoryBridge.lean",
        "correspondence/Anneal/MirCorrespondence/RefinementBundles.lean",
        "correspondence/Anneal/MirCorrespondenceProof.lean",
    ] {
        assert_eq!(prov["correspondence_proofs"][proof_key].as_str().unwrap().len(), 64);
    }
    for lean_key in [
        "trusted/lean/Trusted.lean",
        "trusted/lean/Trusted/MirAst.lean",
        "trusted/lean/Trusted/MirSemantics.lean",
        "trusted/lean/foundation-lock.json",
        "trusted/lean/lean-toolchain",
    ] {
        assert_eq!(prov["trusted_lean"][lean_key].as_str().unwrap().len(), 64);
    }
    assert!(prov["note"].as_str().unwrap().contains("anneal-audit --require-correspondence"));

    let bundled_prov: Value =
        serde_json::from_str(cargo_anneal::EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON).unwrap();
    assert_eq!(prov, &bundled_prov);

    let rendered_py = std::process::Command::new("python3")
        .arg("-B")
        .arg(anneal_root().join("ci/render_correspondence_provenance.py"))
        .arg("--anneal-root")
        .arg(anneal_root())
        .output()
        .unwrap();
    assert!(
        rendered_py.status.success(),
        "render_correspondence_provenance.py failed: {}",
        String::from_utf8_lossy(&rendered_py.stderr)
    );
    assert_eq!(
        String::from_utf8(rendered_py.stdout).unwrap(),
        cargo_anneal::EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON
    );

    if let Ok(install_root) = env::var("ANNEAL_TEST_INSTALL_ROOT")
        && !install_root.is_empty()
    {
        let archive_path =
            PathBuf::from(install_root).join("share/anneal/correspondence-provenance.json");
        let archive_prov: Value =
            serde_json::from_slice(&fs::read(&archive_path).unwrap()).unwrap();
        assert_eq!(&archive_prov, prov);
    }
}

#[test]
fn verifies_real_source_and_rejects_boundary_mutations() {
    let staged = new_workspace("anneal-boundary-").stage().unwrap();
    let work = staged.work_dir();
    let request = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("whole-crate.json"), &request);
    let whole_art = work.join("whole-crate");

    let run = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", whole_art.to_str().unwrap()],
    );
    let ok = expect_verified(&run, "crate_verified", true);
    assert!(ok.experimental, "{ok:?}");
    assert_eq!(ok.candidate_features, vec!["mir_ast", "mir_semantics"]);
    check_provenance_and_toolchain(ok);
    assert!(whole_art.join("capture/Captured.lean").is_file());
    assert!(whole_art.join("generated/Expected.lean").is_file());
    assert!(whole_art.join("audit-request.json").is_file());
    assert!(whole_art.join("result.json").is_file());

    // Changing Rust source body while keeping spec/proof fixed must fail audit.
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE.replace("    0\n", "    1\n")).unwrap();
    let changed_art = work.join("changed-source");
    let changed = run_verify_strs(
        &staged,
        &["--request", req_path.to_str().unwrap(), "--artifacts", changed_art.to_str().unwrap()],
    );
    expect_failed(&changed, 1, "proof_failed", Some("audit"), "Proof.lean");
    let changed_cap: Value =
        serde_json::from_slice(&fs::read(changed_art.join("capture/capture.json")).unwrap())
            .unwrap();
    assert_ne!(ok.sources[0]["sha256"], changed_cap["source_files"][0]["sha256"]);
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    // Negative shortcuts around the canonical closed theorem hit exact guards.
    for (name, decls, rejection) in [
        (
            "wrong-root",
            "public theorem Proof.verify : True := True.intro",
            "policy:target theorem type differs from Expected",
        ),
        (
            "axiom",
            "public axiom fabricated : Expected.claim\npublic theorem Proof.verify : Expected.claim := fabricated",
            "policy:unapproved axiom fabricated from Proof",
        ),
        (
            "sorry",
            "public theorem Proof.verify : Expected.claim := by sorry",
            "policy:unapproved axiom sorryAx from Init.Prelude",
        ),
        (
            "extra-hypothesis",
            "public theorem Proof.verify (assumed : Expected.claim) : Expected.claim := assumed",
            "policy:target theorem type differs from Expected",
        ),
    ] {
        fs::write(work.join("lean/Proof.lean"), lean_module_source("public import Expected", decls)).unwrap();
        let art = work.join(name);
        let res = run_verify_strs(
            &staged,
            &["--request", req_path.to_str().unwrap(), "--artifacts", art.to_str().unwrap()],
        );
        expect_failed(&res, 1, "proof_failed", Some("audit"), rejection);
    }
    fs::write(work.join("lean/Proof.lean"), SCALAR_PROOF).unwrap();

    let mut wrong_role = request.clone();
    wrong_role["proof"]["sources"][0]["role"] = json!("proof");
    let wrong_role_path = write_json_file(&work.join("wrong-role.json"), &wrong_role);
    let r = run_verify_strs(&staged, &["--request", wrong_role_path.to_str().unwrap()]);
    expect_failed(
        &r,
        1,
        "unsupported",
        Some("proof"),
        "specification and theorem must have their declared source roles",
    );

    let shadowed = SCALAR_PROOF
        .replace(
            "public import Expected\n",
            "public import Expected\npublic import Trusted.MirSemantics\npublic import Captured\n",
        )
        .replace(
            "public theorem verify : Expected.claim := by",
            "public def Spec.specs : Specs := ⟨fun _ _ => False, fun _ => True⟩\n\n\
             public theorem verify : CrateTheorem ⟨Captured.program, Spec.specs⟩ := by",
        )
        .replace(", totalCorrectness⟩", ", True.intro⟩");
    fs::write(work.join("lean/Proof.lean"), shadowed).unwrap();
    let r = run_verify_strs(&staged, &["--request", req_path.to_str().unwrap()]);
    expect_failed(
        &r,
        1,
        "proof_failed",
        Some("audit"),
        "policy:target theorem type differs from Expected",
    );
    fs::write(work.join("lean/Proof.lean"), SCALAR_PROOF).unwrap();

    // Hidden specification helper macro inside a proof-role module.
    fs::write(
        work.join("lean/Extra.lean"),
        lean_source("import Trusted.MirSemantics", "macro \"hiddenProperty\" : term => `(True)"),
    )
    .unwrap();
    fs::write(
        work.join("lean/Spec.lean"),
        lean_source(
            "import Trusted.MirSemantics\nimport Extra",
            "namespace Spec\ndef specs : Trusted.MirSemantics.Specs :=\n  \
             ⟨fun _ _ => False, fun _ => hiddenProperty⟩\nend Spec",
        ),
    )
    .unwrap();
    let mut hidden_spec = request.clone();
    hidden_spec["proof"]["sources"]
        .as_array_mut()
        .unwrap()
        .push(json!({"module": "Extra", "path": "Extra.lean", "role": "proof"}));
    let hidden_path = write_json_file(&work.join("hidden.json"), &hidden_spec);
    let hidden = run_verify_strs(&staged, &["--request", hidden_path.to_str().unwrap()]);
    let hidden_fail = expect_failed(&hidden, 1, "proof_failed", Some("audit"), "");
    assert!(
        hidden_fail.detail.contains("specification")
            || hidden_fail.detail.contains("role")
            || hidden_fail.detail.contains("Spec cannot import Extra"),
        "macro must fail at specification origin boundary: {}",
        hidden_fail.detail
    );
    fs::write(work.join("lean/Spec.lean"), SCALAR_SPEC).unwrap();
    fs::remove_file(work.join("lean/Extra.lean")).unwrap();
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
    let default_feat_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        lean_dir.as_os_str(),
    ]));
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
    let custom_feat_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        lean_dir.as_os_str(),
        OsStr::new("--no-default-features"),
        OsStr::new("--features"),
        OsStr::new("extra"),
    ]));
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
        let bad_inv = with_host_cargo_env(verify_invocation(&args));
        let bad_res = run_verify_inv(&staged, &bad_inv);
        expect_failed(&bad_res, 1, "unsupported", Some("cargo"), expected_detail);
    }
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    fs::write(&manifest, manifest_base).unwrap();
    fs::create_dir(lean_dir.join(".cache")).unwrap();
    fs::write(lean_dir.join(".cache/Ignored.lean"), b"not valid Lean syntax").unwrap();
    let good_cargo_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        lean_dir.as_os_str(),
    ]))
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
    let ws_inv = with_host_cargo_env(verify_invocation(&[
        OsStr::new("--manifest-path"),
        member_manifest.as_os_str(),
        OsStr::new("--proof-dir"),
        lean_dir.as_os_str(),
    ]));
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
    let missing_inv = Invocation::new(tools.cli.as_deref().unwrap(), &["verify"])
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

#[test]
fn rustc_mode_symlinks_replay_export_lean_lib_and_unpinned_taint() {
    let staged = new_workspace("anneal-rustc-mode-").stage().unwrap();
    let work = staged.work_dir();
    let cas = work.join("cas");
    fs::create_dir(&cas).unwrap();
    fs::write(cas.join("scalar_lib.rs"), format!("pub mod helper;\n{SCALAR_SOURCE}")).unwrap();
    fs::write(cas.join("helper_phys.rs"), "pub fn unused() -> u64 { 1 }\n").unwrap();
    fs::write(
        cas.join("scalar_spec.lean"),
        SCALAR_SPEC
            .replace("namespace Spec", "namespace Contract")
            .replace("end Spec", "end Contract"),
    )
    .unwrap();
    fs::write(
        cas.join("scalar_proof.lean"),
        SCALAR_PROOF
            .replace("Spec.expectedReturn", "Contract.expectedReturn")
            .replace("Spec.returnsZero", "Contract.returnsZero")
            .replace("namespace Proof", "namespace Spec.Helper")
            .replace("end Proof", "end Spec.Helper")
            .replace("theorem verify :", "theorem custom_verify :"),
    )
    .unwrap();

    let runfiles = work.join("runfiles/pkg/src");
    fs::create_dir_all(&runfiles).unwrap();
    symlink(cas.join("scalar_lib.rs"), runfiles.join("lib.rs")).unwrap();
    symlink(cas.join("helper_phys.rs"), runfiles.join("helper.rs")).unwrap();
    symlink(cas.join("scalar_spec.lean"), runfiles.join("Contract.lean")).unwrap();
    symlink(cas.join("scalar_proof.lean"), runfiles.join("Spec.Helper.lean")).unwrap();

    let lib_rs = runfiles.join("lib.rs");
    let helper_rs = runfiles.join("helper.rs");
    let contract_arg = format!("Contract={}", runfiles.join("Contract.lean").display());
    let helper_arg = format!("Spec.Helper={}", runfiles.join("Spec.Helper.lean").display());
    let run_rustc = |leading: &[&str], spec_arg: &str, proof_arg: &str, thm: Option<&str>| {
        let mut args: Vec<&str> = leading.to_vec();
        args.extend([
            "rustc",
            lib_rs.to_str().unwrap(),
            "--crate-name",
            "scalar",
            "--select",
            "zero",
            "--source-file",
            helper_rs.to_str().unwrap(),
            "--spec-file",
            spec_arg,
            "--proof-file",
            proof_arg,
            "--spec-decl",
            "Contract:Contract.specs",
        ]);
        if let Some(t) = thm {
            args.extend(["--theorem", t]);
        }
        run_verify_strs(&staged, &args)
    };
    let custom_thm = Some("Spec.Helper:Spec.Helper.custom_verify");

    // 1. Passing rustc-mode run with symlinks, --export-lean-lib, and sandbox.
    let pass_art = work.join("rustc-pass");
    let pass = run_rustc(
        &["--artifacts", pass_art.to_str().unwrap(), "--export-lean-lib"],
        &contract_arg,
        &helper_arg,
        custom_thm,
    );
    let pass_ok = expect_verified(&pass, "selected_unit_verified", true);
    assert!(pass_ok.taint_reasons.is_empty());
    assert!(pass.process.stderr.is_empty());
    assert!(matches!(
        pass_ok.elaboration_sandbox.as_deref(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));
    assert!(!pass_ok.deferred.iter().any(|d| d.contains("hostile Lean elaborator")));
    let lean_lib = pass_art.join("lean-lib");
    for present in [
        "Trusted/MirAst.olean",
        "Anneal/MirWp.olean",
        "Captured.olean",
        "Contract.olean",
        "Spec/Helper.olean",
    ] {
        assert!(lean_lib.join(present).is_file(), "missing {present}");
    }
    assert!(!lean_lib.join("lean-toolchain").exists());
    assert!(!lean_lib.join("Spec/Helper.ir").exists());
    assert!(!lean_lib.join("Spec/Helper.ir.sig").exists());

    // 2. Self-contained request.json replays cleanly.
    let replay_art = work.join("rustc-replay");
    let replay = run_verify_strs(
        &staged,
        &[
            "--request",
            pass_art.join("request.json").to_str().unwrap(),
            "--artifacts",
            replay_art.to_str().unwrap(),
        ],
    );
    let replay_ok = expect_verified(&replay, "selected_unit_verified", true);
    assert_eq!(replay_ok.request_sha256, pass_ok.request_sha256);

    // 3. Proof failure exports non-proof .oleans only (never `Proof.olean`).
    fs::write(
        cas.join("bad_proof.lean"),
        lean_source(
            "import Expected",
            "namespace Proof\ntheorem verify : True := True.intro\nend Proof",
        ),
    )
    .unwrap();
    let bad_link = runfiles.join("BadProof.lean");
    symlink(cas.join("bad_proof.lean"), &bad_link).unwrap();
    let fail_art = work.join("rustc-proof-fail");
    let bad_proof_arg = format!("Proof={}", bad_link.display());
    let failed = run_rustc(
        &["--artifacts", fail_art.to_str().unwrap(), "--export-lean-lib"],
        &contract_arg,
        &bad_proof_arg,
        None,
    );
    expect_failed(
        &failed,
        1,
        "proof_failed",
        Some("audit"),
        "policy:target theorem type differs from Expected",
    );
    assert!(fail_art.join("lean-lib/Captured.olean").is_file());
    assert!(fail_art.join("lean-lib/Contract.olean").is_file());
    assert!(!fail_art.join("lean-lib/Proof.olean").exists());

    // 4. Early header error must not create empty/partial lean-lib.
    let bad_import = runfiles.join("BadImportProof.lean");
    fs::write(cas.join("bad_import.lean"), lean_source("import MissingModule", "def x := 1"))
        .unwrap();
    symlink(cas.join("bad_import.lean"), &bad_import).unwrap();
    let early_art = work.join("rustc-early-fail");
    let bad_imp_arg = format!("Proof={}", bad_import.display());
    let early = run_rustc(
        &["--artifacts", early_art.to_str().unwrap(), "--export-lean-lib"],
        &contract_arg,
        &bad_imp_arg,
        None,
    );
    expect_failed(&early, 1, "proof_failed", Some("audit"), "MissingModule");
    assert!(!early_art.join("lean-lib").exists());

    // 5. Unpinned Lean taint receipt + stderr warning.
    let unpinned = run_rustc(&["--allow-unpinned-lean"], &contract_arg, &helper_arg, custom_thm);
    let unpinned_ok = expect_verified(&unpinned, "tainted_selected_unit_verified", true);
    assert!(String::from_utf8_lossy(&unpinned.process.stderr).contains("TAINTED"));
    assert_eq!(unpinned_ok.taint_reasons, vec!["unpinned_lean"]);
    assert_eq!(unpinned_ok.correspondence_provenance["applicable"], json!(false));
    assert_eq!(unpinned_ok.toolchain_identity["sha256_locked"], json!([]));
    assert!(unpinned_ok.assumptions.iter().any(|a| a == "faithful pinned compiler capture"));
    let u = unpinned_ok.unpinned_lean.as_ref().unwrap();
    assert_eq!(u["expected_toolchain"], "leanprover/lean4:v4.34.1");
    assert_eq!(u["lean_binary_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(u["sysroot_modules_sha256"].as_str().unwrap().len(), 64);
    assert_eq!(u["foundation_modules"].as_array().unwrap().len(), 6);
    assert!(u["admitted_sysroot_module_count"].as_u64().unwrap() >= 6);
    assert_eq!(
        u["sysroot_modules_sha256"],
        unpinned_ok.audit["unpinnedLean"]["sysrootModulesSha256"]
    );

    // 6. Unsandboxed elaboration taint.
    let unsandboxed =
        run_rustc(&["--allow-unsandboxed-elaboration"], &contract_arg, &helper_arg, custom_thm);
    let unsandboxed_ok = expect_verified(&unsandboxed, "tainted_selected_unit_verified", true);
    assert!(String::from_utf8_lossy(&unsandboxed.process.stderr).contains("TAINTED"));
    assert_eq!(unsandboxed_ok.taint_reasons, vec!["unsandboxed_elaboration"]);
    assert_eq!(unsandboxed_ok.elaboration_sandbox.as_deref(), Some("none"));
    assert!(unsandboxed_ok.deferred.iter().any(|d| d.contains("hostile Lean elaborator")));
    assert!(unsandboxed_ok.sorry_declarations.is_none());

    // 7. Clean proof with `--allow-sorry-in-proof` still taints cleanly.
    let clean_sorry =
        run_rustc(&["--allow-sorry-in-proof"], &contract_arg, &helper_arg, custom_thm);
    let cs_ok = expect_verified(&clean_sorry, "tainted_selected_unit_verified", true);
    assert!(String::from_utf8_lossy(&clean_sorry.process.stderr).contains("TAINTED"));
    assert_eq!(cs_ok.taint_reasons, vec!["sorry_in_proof"]);
    assert_eq!(cs_ok.sorry_declarations, Some(vec![]));
    assert!(matches!(
        cs_ok.elaboration_sandbox.as_deref(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));

    // 8. Proof with `sorry`: strict fails, `--allow-sorry-in-proof` combines.
    let sorry_proof = runfiles.join("SorryProof.lean");
    fs::write(
        &sorry_proof,
        "prelude\nimport Expected\nnamespace Spec.Helper\n\
         theorem lemma_hole : Expected.claim := sorry\n\
         theorem custom_verify : Expected.claim := lemma_hole\n\
         end Spec.Helper\n",
    )
    .unwrap();
    let sorry_arg = format!("Spec.Helper={}", sorry_proof.display());
    let strict_sorry = run_rustc(&[], &contract_arg, &sorry_arg, custom_thm);
    let ss_fail =
        expect_failed(&strict_sorry, 1, "proof_failed", Some("audit"), "unapproved axiom sorryAx");
    assert!(ss_fail.taint_reasons.is_empty());
    assert!(matches!(
        ss_fail.elaboration_sandbox.as_deref(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));

    let sandboxed_sorry =
        run_rustc(&["--allow-sorry-in-proof"], &contract_arg, &sorry_arg, custom_thm);
    let ss_allow = expect_verified(&sandboxed_sorry, "tainted_selected_unit_verified", true);
    assert!(String::from_utf8_lossy(&sandboxed_sorry.process.stderr).contains("TAINTED"));
    assert_eq!(ss_allow.taint_reasons, vec!["sorry_in_proof"]);
    assert_eq!(ss_allow.sorry_declarations, Some(vec![json!("Spec.Helper.lemma_hole")]));
    assert!(matches!(
        ss_allow.elaboration_sandbox.as_deref(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));

    let all_three = run_rustc(
        &["--allow-unsandboxed-elaboration", "--allow-unpinned-lean", "--allow-sorry-in-proof"],
        &contract_arg,
        &sorry_arg,
        custom_thm,
    );
    let all_ok = expect_verified(&all_three, "tainted_selected_unit_verified", true);
    assert_eq!(
        all_ok.taint_reasons,
        vec!["sorry_in_proof", "unpinned_lean", "unsandboxed_elaboration"]
    );
    assert_eq!(all_ok.elaboration_sandbox.as_deref(), Some("none"));
    assert_eq!(all_ok.sorry_declarations, Some(vec![json!("Spec.Helper.lemma_hole")]));
    assert!(all_ok.unpinned_lean.is_some());
    assert!(all_ok.deferred.iter().any(|d| d.contains("hostile Lean elaborator")));

    // 9. Specification `sorry` still fails even with `--allow-sorry-in-proof`.
    let sorry_spec = runfiles.join("SorryContract.lean");
    fs::write(
        &sorry_spec,
        "prelude\nimport Trusted.MirSemantics\nnamespace Contract\n\
         theorem bad_spec_hole : True := sorry\n\
         def specs (_ : Trusted.MirSemantics.Program) : Prop := True\n\
         end Contract\n",
    )
    .unwrap();
    let sorry_spec_arg = format!("Contract={}", sorry_spec.display());
    let spec_sorry_fail =
        run_rustc(&["--allow-sorry-in-proof"], &sorry_spec_arg, &sorry_arg, custom_thm);
    let sp_fail =
        expect_failed(&spec_sorry_fail, 1, "proof_failed", Some("audit"), "Lean.Parser.Term.sorry");
    assert_eq!(sp_fail.taint_reasons, vec!["sorry_in_proof"]);
    assert!(matches!(
        sp_fail.elaboration_sandbox.as_deref(),
        Some("linux_bwrap" | "linux_landlock_seccomp")
    ));
}
