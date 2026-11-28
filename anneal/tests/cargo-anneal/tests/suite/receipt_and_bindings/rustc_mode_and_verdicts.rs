// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `rustc` mode, replay, Lean library export, and unpinned taint, and the
//! human verdict cards and `--receipt-out` for each receipt tier.

use super::*;

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

#[test]
fn human_verdict_cards_and_receipt_out_cover_ok_scoped_and_tainted_tiers() {
    let tools = workspace_tools();
    let cli = tools.cli.as_deref().expect("workspace cli binary");
    let capture = tools.capture.as_deref().expect("workspace capture binary");
    let staged = new_workspace("anneal-human-card-").stage().unwrap();
    let work = staged.work_dir();
    let request = write_scalar_baseline(work);
    let req_path = write_json_file(&work.join("human-crate.json"), &request);
    let receipt_out = work.join("crate-receipt.json");

    // 1. Default `--format human` with `--color always`, `-v`, `--receipt-out`
    //    on clean whole-crate verify -> `[OK]` + SGR green + 6-phase LineLog
    //    progress + atomic Receipt Schema v3 JSON on disk.
    let ok_inv = Invocation::new(cli, &["--color", "always", "-v", "verify", "--request"])
        .arg(&req_path)
        .arg("--receipt-out")
        .arg(&receipt_out)
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot)
        .env("ANNEAL_TEST_REDACT_TIMING", "1");
    let ok_raw = staged.exec(&ok_inv).unwrap();
    assert_outcome_exit(&ok_raw.process, 0).unwrap();
    let ok_stdout = String::from_utf8(ok_raw.process.stdout).unwrap();
    let ok_stderr = String::from_utf8(ok_raw.process.stderr).unwrap();
    assert!(ok_stdout.contains("\x1b[1;32m[OK]\x1b[0m"), "{ok_stdout}");
    assert!(ok_stdout.contains("CRATE VERIFIED (1/1 required crate bodies)"), "{ok_stdout}");
    assert!(ok_stdout.contains(&format!("Receipt    : {}", receipt_out.display())), "{ok_stdout}");
    for step in ["[1/6]", "[2/6]", "[3/6]", "[4/6]", "[5/6]", "[6/6]"] {
        assert!(ok_stderr.contains(step), "missing {step} in verbose stderr:\n{ok_stderr}");
    }
    let disk_receipt: Value = serde_json::from_slice(&fs::read(&receipt_out).unwrap()).unwrap();
    assert_eq!(disk_receipt["schema_version"], 3);
    assert_eq!(disk_receipt["status"], "crate_verified");

    // 2. Selected-unit verification -> `[SCOPED]`, NEVER `[OK]` / SGR 32 green.
    let mut scoped_req = request.clone();
    scoped_req["compilation"]["source_files"] = json!(["lib.rs", "extra.rs"]);
    fs::write(work.join("rust/lib.rs"), "pub mod extra;\npub fn zero() -> u64 {\n    0\n}\n")
        .unwrap();
    fs::write(work.join("rust/extra.rs"), "pub fn unverified_helper() -> u64 { 42 }\n").unwrap();
    scoped_req["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    let scoped_req_path = write_json_file(&work.join("human-scoped.json"), &scoped_req);

    let scoped_inv = Invocation::new(cli, &["--color", "always", "verify", "--request"])
        .arg(&scoped_req_path)
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot);
    let scoped_raw = staged.exec(&scoped_inv).unwrap();
    assert_outcome_exit(&scoped_raw.process, 0).unwrap();
    let scoped_stdout = String::from_utf8(scoped_raw.process.stdout).unwrap();
    assert!(scoped_stdout.contains("[SCOPED]"), "{scoped_stdout}");
    assert!(!scoped_stdout.contains("[OK]"), "{scoped_stdout}");
    assert!(!scoped_stdout.contains("\x1b[1;32m"), "{scoped_stdout}");
    assert!(
        scoped_stdout.contains("1/2 required crate bodies; 1 required items UNVERIFIED"),
        "{scoped_stdout}"
    );

    // 3. Tainted verification (`--allow-sorry-in-proof -q`) -> `[TAINTED]` with
    //    mandatory `! TAINT` row preserved even under `-q`.
    let tainted_inv = Invocation::new(cli, &["-q", "verify", "--allow-sorry-in-proof", "--request"])
        .arg(&scoped_req_path)
        .arg("--capture")
        .arg(capture)
        .arg("--lean")
        .arg(&tools.lean)
        .arg("--sysroot")
        .arg(&tools.sysroot);
    let tainted_raw = staged.exec(&tainted_inv).unwrap();
    assert_outcome_exit(&tainted_raw.process, 0).unwrap();
    let tainted_stdout = String::from_utf8(tainted_raw.process.stdout).unwrap();
    let tainted_stderr = String::from_utf8(tainted_raw.process.stderr).unwrap();
    assert!(tainted_stdout.contains("[TAINTED]"), "{tainted_stdout}");
    assert!(tainted_stdout.contains("! TAINT    : sorry_in_proof"), "{tainted_stdout}");
    assert!(!tainted_stdout.contains("[OK]"), "{tainted_stdout}");
    assert!(tainted_stderr.contains("TAINTED"), "{tainted_stderr}");
}
