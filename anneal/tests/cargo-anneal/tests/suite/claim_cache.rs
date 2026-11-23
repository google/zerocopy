// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests for the key-bound ClaimCache (`--claim-cache-*`).

use std::{fs, path::Path};

use anneal_testkit::{ExecutedRun, VerifyReceipt};
use serde_json::{Value, json};

use crate::helpers::{
    SCALAR_PROOF, SCALAR_SOURCE, SCALAR_SPEC, expect_failed, expect_verified, lean_source,
    new_workspace, run_verify_inv, verify_invocation, write_json_file, write_scalar_baseline,
};

#[test]
fn claim_cache_hits_honest_provenance_invalidation_and_tamper_rejection() {
    let staged = new_workspace("anneal-claim-cache-").stage().unwrap();
    let work = staged.work_dir();
    let mut base_req = write_scalar_baseline(work);
    base_req["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
    let req_path = write_json_file(&work.join("claim-cache-req.json"), &base_req);
    let claim_dir = work.join("claim-cache");
    let claim_dir_str = claim_dir.to_str().unwrap();
    let default_xdg = work.join("xdg-cache");
    fs::create_dir(&default_xdg).unwrap();

    let run_with_cache = |name: &str,
                          home_override: Option<&Path>,
                          xdg_override: Option<&Path>,
                          extra_args: &[&str]|
     -> ExecutedRun<VerifyReceipt> {
        let mut inv = verify_invocation(&[])
            .arg("--request")
            .arg(&req_path)
            .arg("--artifacts")
            .arg(work.join(name))
            .env("XDG_CACHE_HOME", xdg_override.unwrap_or(&default_xdg));
        if let Some(home) = home_override {
            inv = inv.env("HOME", home);
        }
        for arg in extra_args {
            inv = inv.arg(arg);
        }
        run_verify_inv(&staged, &inv)
    };

    // 1. Cold run stores key-bound evidence and marks `verified_fresh`.
    let cold_run =
        run_with_cache("cc-cold", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    let cold = expect_verified(&cold_run, "selected_unit_verified", true);
    assert!(
        cold_run.process.stderr.is_empty(),
        "stderr={}",
        String::from_utf8_lossy(&cold_run.process.stderr)
    );
    assert_eq!(cold.from_claim_cache, Some(false));
    assert_eq!(cold.cache_status.as_deref(), Some("verified_fresh"));
    let key = cold.claim_cache_key.as_ref().expect("claim_cache_key present").clone();
    assert_eq!(key.len(), 64);

    let evidence_path = claim_dir.join("v1").join(&key).join("evidence.json");
    assert!(evidence_path.is_file(), "expected cached evidence at {}", evidence_path.display());

    // 2. Warm run hits ClaimCache with honest provenance and re-bound
    //    `request_sha256` / `capture_sha256` bindings.
    let warm_run =
        run_with_cache("cc-warm", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    let warm = expect_verified(&warm_run, "selected_unit_verified", true);
    assert!(
        warm_run.process.stderr.is_empty(),
        "stderr={}",
        String::from_utf8_lossy(&warm_run.process.stderr)
    );
    assert_eq!(warm.from_claim_cache, Some(true));
    assert_eq!(warm.cache_status.as_deref(), Some("claim_cache_hit"));
    assert_eq!(warm.claim_cache_key.as_deref(), Some(key.as_str()));
    assert_eq!(warm.audit["exactType"], json!(true));
    assert_eq!(warm.audit["bindings"]["requestSha256"], json!(warm.request_sha256));
    assert_eq!(warm.audit["bindings"]["captureSha256"], json!(warm.capture_sha256));
    assert_eq!(
        warm.audit["bindings"]["specificationManifestSha256"],
        json!(warm.specification_manifest_sha256)
    );
    assert_eq!(warm.audit["bindings"]["modelManifestSha256"], json!(warm.model_manifest_sha256));

    // 3. Adding an unselected function in Rust keeps `Captured.lean` identical
    //    (early cutoff) and refreshes `capture_sha256` in `audit.bindings`.
    fs::write(
        work.join("rust/lib.rs"),
        format!("{SCALAR_SOURCE}\npub fn unrelated_helper(v: usize) -> usize {{ v }}\n"),
    )
    .unwrap();
    let cutoff_run =
        run_with_cache("cc-cutoff", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    let cutoff = expect_verified(&cutoff_run, "selected_unit_verified", true);
    assert_eq!(cutoff.from_claim_cache, Some(true));
    assert_eq!(cutoff.cache_status.as_deref(), Some("claim_cache_hit"));
    assert_eq!(cutoff.claim_cache_key.as_deref(), Some(key.as_str()));
    assert_eq!(cutoff.audit["bindings"]["captureSha256"], json!(cutoff.capture_sha256));

    // 4. Mutating the verified Rust body breaks early cutoff -> misses and
    //    rejects via fresh verification.
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE.replace("    0\n", "    1\n")).unwrap();
    let bad_rust =
        run_with_cache("cc-bad-rust", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    expect_failed(&bad_rust, 1, "proof_failed", Some("audit"), "");
    fs::write(work.join("rust/lib.rs"), SCALAR_SOURCE).unwrap();

    // 5. Mutating `Spec.lean` invalidates cache and rejects bad obligation.
    let broken_spec = SCALAR_SPEC.replace("BitVec.ofNat 128 0", "BitVec.ofNat 128 1");
    assert_ne!(broken_spec, SCALAR_SPEC, "test fixture mutation must alter Spec.lean");
    fs::write(work.join("lean/Spec.lean"), broken_spec).unwrap();
    let bad_spec =
        run_with_cache("cc-bad-spec", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    expect_failed(&bad_spec, 1, "proof_failed", Some("audit"), "");
    fs::write(work.join("lean/Spec.lean"), SCALAR_SPEC).unwrap();

    // 6. Mutating `Proof.lean` with `by sorry` misses cache and fails without
    //    `--allow-sorry-in-proof`.
    let sorry_proof =
        lean_source("import Expected", "theorem Proof.verify : Expected.claim := by sorry");
    fs::write(work.join("lean/Proof.lean"), &sorry_proof).unwrap();
    let bad_proof =
        run_with_cache("cc-bad-proof", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
    expect_failed(&bad_proof, 1, "proof_failed", Some("audit"), "");

    // 7. Policy flag `--allow-sorry-in-proof` produces a distinct key and
    //    tainted receipt; omitting `--allow-sorry-in-proof` rejects again.
    let tainted_run = run_with_cache(
        "cc-sorry-tainted",
        Some(work),
        None,
        &["--claim-cache-dir", claim_dir_str, "--allow-sorry-in-proof"],
    );
    let tainted = expect_verified(&tainted_run, "tainted_selected_unit_verified", true);
    assert_eq!(tainted.taint_reasons, vec!["sorry_in_proof"]);
    assert_eq!(tainted.from_claim_cache, Some(false));
    assert_ne!(tainted.claim_cache_key.as_deref(), Some(key.as_str()));

    let tainted_warm_run = run_with_cache(
        "cc-sorry-tainted-warm",
        Some(work),
        None,
        &["--claim-cache-dir", claim_dir_str, "--allow-sorry-in-proof"],
    );
    let tainted_warm = expect_verified(&tainted_warm_run, "tainted_selected_unit_verified", true);
    assert_eq!(tainted_warm.from_claim_cache, Some(true));
    assert_eq!(tainted_warm.taint_reasons, vec!["sorry_in_proof"]);

    let untainted_reject = run_with_cache(
        "cc-sorry-without-flag",
        Some(work),
        None,
        &["--claim-cache-dir", claim_dir_str],
    );
    expect_failed(&untainted_reject, 1, "proof_failed", Some("audit"), "");
    fs::write(work.join("lean/Proof.lean"), SCALAR_PROOF).unwrap();

    // 8. `--claim-cache-mode=off` and `--no-cache` bypass ClaimCache.
    let mode_off_run = run_with_cache(
        "cc-mode-off",
        Some(work),
        None,
        &["--claim-cache-dir", claim_dir_str, "--claim-cache-mode", "off"],
    );
    let mode_off = expect_verified(&mode_off_run, "selected_unit_verified", true);
    assert_eq!(mode_off.from_claim_cache, Some(false));
    assert_eq!(mode_off.cache_status.as_deref(), Some("claim_cache_disabled"));
    assert_eq!(mode_off.claim_cache_key, None);

    let no_cache_run = run_with_cache("cc-no-cache", Some(work), None, &["--no-cache"]);
    let no_cache = expect_verified(&no_cache_run, "selected_unit_verified", true);
    assert_eq!(no_cache.from_claim_cache, Some(false));
    assert_eq!(no_cache.cache_status.as_deref(), Some("claim_cache_disabled"));

    // 9. Adversarial poisoning on `evidence.json` must fail closed (`2`).
    let orig_evidence = fs::read(&evidence_path).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&evidence_path, fs::Permissions::from_mode(0o600)).unwrap();
    }
    fs::write(&evidence_path, b"{corrupt json").unwrap();
    let corrupt_err = run_with_cache(
        "cc-poison-corrupt",
        Some(work),
        None,
        &["--claim-cache-dir", claim_dir_str],
    );
    expect_failed(&corrupt_err, 2, "tool_failed", Some("claim-cache"), "");

    // Valid JSON with forged `audit` / graph / sources / input fields.
    let orig_json: Value = serde_json::from_slice(&orig_evidence).unwrap();
    for (label, mutate) in [
        (
            "forged-replay",
            Box::new(|v: &mut Value| v["audit"]["replay"] = json!(false))
                as Box<dyn FnOnce(&mut Value)>,
        ),
        ("forged-exact-type", Box::new(|v: &mut Value| v["audit"]["exactType"] = json!(false))),
        (
            "forged-alt-proofs",
            Box::new(|v: &mut Value| v["audit"]["checkedAlternateProofs"] = json!(1)),
        ),
        (
            "forged-sorry-ax",
            Box::new(|v: &mut Value| v["audit"]["axioms"] = json!(["propext", "sorryAx"])),
        ),
        (
            "forged-graph-unknown",
            Box::new(|v: &mut Value| {
                v["audit"]["graph"]["RogueMod"] = json!([]);
            }),
        ),
        (
            "forged-identities",
            Box::new(|v: &mut Value| {
                v["audit"]["moduleIdentities"]["Expected"]["sourceSha256"] = json!("0".repeat(64));
            }),
        ),
        (
            "forged-sources-drop-model",
            Box::new(|v: &mut Value| {
                let arr = v["audit"]["sources"].as_array_mut().unwrap();
                arr.retain(|e| e["role"] != "model");
            }),
        ),
        (
            "forged-input",
            Box::new(|v: &mut Value| v["input"]["allow_sorry_in_proof"] = json!(true)),
        ),
        ("forged-schema", Box::new(|v: &mut Value| v["schema_version"] = json!(99))),
    ] {
        let mut forged = orig_json.clone();
        mutate(&mut forged);
        fs::write(&evidence_path, serde_json::to_vec(&forged).unwrap()).unwrap();
        let err = run_with_cache(label, Some(work), None, &["--claim-cache-dir", claim_dir_str]);
        expect_failed(&err, 2, "tool_failed", Some("claim-cache"), "");
    }

    // 10. Symlinked cache entry and directories fail closed (`2`).
    #[cfg(unix)]
    {
        use std::os::unix::fs::symlink;
        let decoy = work.join("decoy.json");
        fs::write(&decoy, &orig_evidence).unwrap();
        fs::remove_file(&evidence_path).unwrap();
        symlink(&decoy, &evidence_path).unwrap();
        let sym_entry =
            run_with_cache("cc-sym-entry", Some(work), None, &["--claim-cache-dir", claim_dir_str]);
        expect_failed(&sym_entry, 2, "tool_failed", Some("claim-cache"), "");

        let sym_cache_dir = work.join("sym-claim-dir");
        let real_cache_target = work.join("real-claim-target");
        fs::create_dir_all(&real_cache_target).unwrap();
        symlink(&real_cache_target, &sym_cache_dir).unwrap();
        let sym_dir_res = run_with_cache(
            "cc-sym-dir",
            Some(work),
            None,
            &["--claim-cache-dir", sym_cache_dir.to_str().unwrap()],
        );
        expect_failed(&sym_dir_res, 2, "tool_failed", Some("claim-cache"), "");
        assert!(!work.join("cc-sym-dir/result.json").exists());

        // 11. `--export-lean-lib` preserves `"claim-cache"` store failures
        //     without letting stage retention emit `"retention"`, and valid
        //     exports warm the cache for a subsequent hit.
        let exp_sym_res = run_with_cache(
            "cc-export-sym-dir",
            Some(work),
            None,
            &["--export-lean-lib", "--claim-cache-dir", sym_cache_dir.to_str().unwrap()],
        );
        expect_failed(&exp_sym_res, 2, "tool_failed", Some("claim-cache"), "");
        assert!(!work.join("cc-export-sym-dir/result.json").exists());
        assert!(!work.join("cc-export-sym-dir/lean-lib").exists());

        let sym_xdg = work.join("sym-xdg");
        let real_xdg_target = work.join("real-xdg-target");
        fs::create_dir_all(&real_xdg_target).unwrap();
        symlink(&real_xdg_target, &sym_xdg).unwrap();
        let sym_xdg_no_home = run_with_cache("cc-sym-xdg-no-home", None, Some(&sym_xdg), &[]);
        expect_failed(&sym_xdg_no_home, 2, "tool_failed", Some("claim-cache"), "");
        let sym_xdg_with_home =
            run_with_cache("cc-sym-xdg-with-home", Some(work), Some(&sym_xdg), &[]);
        expect_failed(&sym_xdg_with_home, 2, "tool_failed", Some("claim-cache"), "");
    }

    let exp_claim_dir = work.join("claim-cache-export");
    let exp_run = run_with_cache(
        "cc-export-warm",
        Some(work),
        None,
        &["--export-lean-lib", "--claim-cache-dir", exp_claim_dir.to_str().unwrap()],
    );
    let exp_ok = expect_verified(&exp_run, "selected_unit_verified", true);
    assert_eq!(exp_ok.from_claim_cache, Some(false));
    assert_eq!(exp_ok.cache_status.as_deref(), Some("bypassed_export_lean_lib"));
    assert!(work.join("cc-export-warm/lean-lib/Proof.olean").is_file());

    let after_export = run_with_cache(
        "cc-after-export",
        Some(work),
        None,
        &["--claim-cache-dir", exp_claim_dir.to_str().unwrap()],
    );
    let after_ok = expect_verified(&after_export, "selected_unit_verified", true);
    assert_eq!(after_ok.from_claim_cache, Some(true));
    assert_eq!(after_ok.cache_status.as_deref(), Some("claim_cache_hit"));
    assert_eq!(after_ok.claim_cache_key, exp_ok.claim_cache_key);

    // 12. `--allow-unpinned-lean` works across cold store and warm hit.
    let unpinned_cold_run = run_with_cache(
        "cc-unpinned-cold",
        Some(work),
        None,
        &["--allow-unpinned-lean", "--claim-cache-dir", exp_claim_dir.to_str().unwrap()],
    );
    let unpinned_cold = expect_verified(&unpinned_cold_run, "tainted_selected_unit_verified", true);
    assert_eq!(unpinned_cold.taint_reasons, vec!["unpinned_lean"]);
    assert_eq!(unpinned_cold.from_claim_cache, Some(false));
    assert_eq!(unpinned_cold.cache_status.as_deref(), Some("verified_fresh"));
    assert!(unpinned_cold.unpinned_lean.is_some());

    let unpinned_warm_run = run_with_cache(
        "cc-unpinned-warm",
        Some(work),
        None,
        &["--allow-unpinned-lean", "--claim-cache-dir", exp_claim_dir.to_str().unwrap()],
    );
    let unpinned_warm = expect_verified(&unpinned_warm_run, "tainted_selected_unit_verified", true);
    assert_eq!(unpinned_warm.taint_reasons, vec!["unpinned_lean"]);
    assert_eq!(unpinned_warm.from_claim_cache, Some(true));
    assert_eq!(unpinned_warm.cache_status.as_deref(), Some("claim_cache_hit"));
    assert_eq!(unpinned_warm.unpinned_lean, unpinned_cold.unpinned_lean);
    assert_eq!(unpinned_warm.claim_cache_key, unpinned_cold.claim_cache_key);

    // 13. Root `/` and `..` cache paths fail closed (`2`).
    let root_res = run_with_cache("cc-root-dir", Some(work), None, &["--claim-cache-dir", "/"]);
    expect_failed(&root_res, 2, "tool_failed", Some("claim-cache"), "");
    let parent_res = run_with_cache(
        "cc-parent-dir",
        Some(work),
        None,
        &["--claim-cache-dir", &format!("{}/sub/..", exp_claim_dir.display())],
    );
    expect_failed(&parent_res, 2, "tool_failed", Some("claim-cache"), "");
}
