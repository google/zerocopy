// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `--diff` over instantiations, `sorry` counts, directions, shims, and
//! spec warnings, plus malformed spec warnings and orphan seams.

use super::*;

/// Runs the sections of `verify_artifacts_and_three_tier_diff_enforced`
/// that the module documentation lists.
pub(super) fn diff_tracks_scope_sorry_shims_and_warnings(
    tmp: &tempfile::TempDir,
    clean: Value,
    clean_path: PathBuf,
    s3_gutns: Value,
    sorry_path: PathBuf,
    sorry_tainted: Value,
    cap_bin_sha: String,
) {
    // Swapped `scope.instantiations`, `sorry` growth, `forward <-> backward`,
    // and new `spec_warnings` all fail `--diff --no-regressions`; shim
    // upgrades (`assumed` -> `proved`) pass.
    let mut inst_a = clean.clone();
    inst_a["status"] = json!("selected_unit_verified");
    inst_a["scope"] = json!({
        "kind": "selected_unit",
        "roots": ["foo"],
        "instantiations": [{"path": "foo", "args": ["u8"]}]
    });
    inst_a["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
    let mut inst_b = inst_a.clone();
    inst_b["scope"]["instantiations"] = json!([{"path": "foo", "args": ["u16"]}]);
    let inst_a_path = tmp.path().join("inst_a.json");
    let inst_b_path = tmp.path().join("inst_b.json");
    fs::write(&inst_a_path, serde_json::to_vec(&inst_a).unwrap()).unwrap();
    fs::write(&inst_b_path, serde_json::to_vec(&inst_b).unwrap()).unwrap();
    let inst_reg_out = run_inspect(
        &[
            "--diff",
            inst_a_path.to_str().unwrap(),
            inst_b_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(inst_reg_out.status.code(), Some(1));
    let inst_reg_stdout = String::from_utf8_lossy(&inst_reg_out.stdout);
    assert!(inst_reg_stdout.contains("REGRESSIONS DETECTED"), "{inst_reg_stdout}");
    assert!(!inst_reg_stdout.contains("INVALID ENVELOPE(S)"), "{inst_reg_stdout}");
    assert!(inst_reg_stdout.contains("scope.instantiations"), "{inst_reg_stdout}");
    assert!(
        inst_reg_out.stderr.is_empty(),
        "stderr={}",
        String::from_utf8_lossy(&inst_reg_out.stderr)
    );
    let inst_diff_only = run_inspect(
        &[
            "--diff",
            inst_a_path.to_str().unwrap(),
            inst_b_path.to_str().unwrap(),
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(inst_diff_only.status.code(), Some(0));
    let inst_diff_json: Value = serde_json::from_slice(&inst_diff_only.stdout).unwrap();
    assert_eq!(inst_diff_json["has_regressions"], true);
    assert!(inst_diff_json.get("base_invariant_violations").is_none());
    assert!(inst_diff_json.get("head_invariant_violations").is_none());
    assert!(
        inst_diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "scope.instantiations" && c["tier"] == "tier_a")
    );

    let mut sorry_mismatch = sorry_tainted.clone();
    sorry_mismatch["sorry_declarations"] = json!(["Proof.other"]);
    let sorry_mismatch_path = tmp.path().join("sorry_mismatch.json");
    fs::write(&sorry_mismatch_path, serde_json::to_vec(&sorry_mismatch).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[sorry_mismatch_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(1)
    );

    let mut sorry_two = sorry_tainted.clone();
    sorry_two["sorry_declarations"] = json!(["Proof.hole", "Proof.two"]);
    sorry_two["audit"]["sorryDeclarations"] = json!(["Proof.hole", "Proof.two"]);
    let sorry_two_path = tmp.path().join("sorry_two.json");
    fs::write(&sorry_two_path, serde_json::to_vec(&sorry_two).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                sorry_path.to_str().unwrap(),
                sorry_two_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(1)
    );

    let mut dir_fwd = clean.clone();
    dir_fwd["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "wf_stutter",
        "direction": "forward",
        "licensed_claim_shapes": ["forall_safety"]
    });
    let mut dir_bwd = dir_fwd.clone();
    dir_bwd["model_system_relation"]["direction"] = json!("backward");
    let dir_fwd_path = tmp.path().join("dir_fwd.json");
    let dir_bwd_path = tmp.path().join("dir_bwd.json");
    fs::write(&dir_fwd_path, serde_json::to_vec(&dir_fwd).unwrap()).unwrap();
    fs::write(&dir_bwd_path, serde_json::to_vec(&dir_bwd).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                dir_fwd_path.to_str().unwrap(),
                dir_bwd_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(1)
    );

    let mut shim_assumed = clean.clone();
    shim_assumed["tcb_shims"] = json!([{
        "id": "seam_upgrade",
        "kind": "capture_driver",
        "sha256": cap_bin_sha,
        "status": "assumed"
    }]);
    let mut shim_proved = shim_assumed.clone();
    shim_proved["tcb_shims"][0]["status"] = json!("proved");
    let shim_a_path = tmp.path().join("shim_assumed.json");
    let shim_p_path = tmp.path().join("shim_proved.json");
    fs::write(&shim_a_path, serde_json::to_vec(&shim_assumed).unwrap()).unwrap();
    fs::write(&shim_p_path, serde_json::to_vec(&shim_proved).unwrap()).unwrap();
    assert_eq!(
        run_inspect(
            &[
                "--diff",
                shim_a_path.to_str().unwrap(),
                shim_p_path.to_str().unwrap(),
                "--no-regressions"
            ],
            None
        )
        .status
        .code(),
        Some(0)
    );

    let mut head_warn = clean.clone();
    let warn_entries = json!([{
        "code": "unsatisfiable_safety",
        "declaration": "Spec.bad",
        "message": "ensures is unsatisfiable"
    }]);
    head_warn["spec_warnings"] = warn_entries.clone();
    head_warn["audit"]["specWarnings"] = warn_entries.clone();
    let head_warn_path = tmp.path().join("head_warn.json");
    fs::write(&head_warn_path, serde_json::to_vec(&head_warn).unwrap()).unwrap();
    let warn_reg_out = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_warn_path.to_str().unwrap(),
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(warn_reg_out.status.code(), Some(1));
    let warn_reg_stdout = String::from_utf8_lossy(&warn_reg_out.stdout);
    assert!(warn_reg_stdout.contains("REGRESSIONS DETECTED"), "{warn_reg_stdout}");
    assert!(!warn_reg_stdout.contains("INVALID ENVELOPE(S)"), "{warn_reg_stdout}");

    // Stripped top-level `spec_warnings` vs `audit.specWarnings`, malformed
    // `audit.specWarnings`, and extra keys inside `audit.specWarnings` fail
    // closed.
    let mut stripped_warn = clean.clone();
    stripped_warn["audit"]["specWarnings"] = warn_entries.clone();
    let stripped_warn_path = tmp.path().join("stripped_warn.json");
    fs::write(&stripped_warn_path, serde_json::to_vec(&stripped_warn).unwrap()).unwrap();
    let stripped_out = run_inspect(&[stripped_warn_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(stripped_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&stripped_out.stdout).contains("differs from `audit.specWarnings`")
    );
    let mut extra_audit_warn = clean.clone();
    extra_audit_warn["spec_warnings"] = warn_entries;
    extra_audit_warn["audit"]["specWarnings"] = json!([{
        "code": "unsatisfiable_safety",
        "declaration": "Spec.bad",
        "message": "ensures is unsatisfiable",
        "extra_audit_key": true
    }]);
    let extra_audit_warn_path = tmp.path().join("extra_audit_warn.json");
    fs::write(&extra_audit_warn_path, serde_json::to_vec(&extra_audit_warn).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[extra_audit_warn_path.to_str().unwrap(), "--unknown-fields", "deny"], None)
            .status
            .code(),
        Some(2)
    );
    let mut bad_audit_warn = clean.clone();
    bad_audit_warn["audit"]["specWarnings"] = json!("not-an-array");
    let bad_audit_warn_path = tmp.path().join("bad_audit_warn.json");
    fs::write(&bad_audit_warn_path, serde_json::to_vec(&bad_audit_warn).unwrap()).unwrap();
    assert_eq!(run_inspect(&[bad_audit_warn_path.to_str().unwrap()], None).status.code(), Some(2));

    let mut orphan_seam = s3_gutns.clone();
    orphan_seam["correspondence_provenance"]["tcb_shims"].as_array_mut().unwrap().push(json!({
        "id": "orphan_seam",
        "kind": "assumed_seam",
        "sha256": cap_bin_sha,
        "status": "assumed"
    }));
    let orphan_seam_path = tmp.path().join("orphan_seam.json");
    fs::write(&orphan_seam_path, serde_json::to_vec(&orphan_seam).unwrap()).unwrap();
    assert_eq!(
        run_inspect(&[orphan_seam_path.to_str().unwrap(), "--passive"], None).status.code(),
        Some(1)
    );
}
