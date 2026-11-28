// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Multi-kernel downgrades, specification swaps, shim-order invariance,
//! and dropped anchors in `--diff`.

use super::*;

/// Runs the sections of `verify_artifacts_and_three_tier_diff_enforced`
/// that the module documentation lists.
pub(super) fn diff_kernels_specs_shim_order_and_anchors(
    tmp: &tempfile::TempDir,
    clean: Value,
    clean_path: PathBuf,
) {
    // Multi-kernel replay downgrades, spec symbol swaps, tcb_shims order
    // invariance, and `anchored_at` regressions in `--diff`.
    let mut base_mk = clean.clone();
    base_mk["audit"]["auditMode"] = json!("paranoid");
    base_mk["audit"]["kernelsPassed"] = json!(["lean4", "nanoda"]);
    base_mk["audit"]["paranoidQuorum"] = json!(true);
    let base_mk_path = tmp.path().join("base_mk.json");
    fs::write(&base_mk_path, serde_json::to_vec(&base_mk).unwrap()).unwrap();
    let mut head_mk = base_mk.clone();
    head_mk["audit"]["auditMode"] = json!("strict");
    head_mk["audit"]["kernelsPassed"] = json!(["lean4"]);
    head_mk["audit"]["kernelsSkipped"] = json!(["nanoda"]);
    head_mk["audit"]["paranoidQuorum"] = json!(false);
    let head_mk_path = tmp.path().join("head_mk.json");
    fs::write(&head_mk_path, serde_json::to_vec(&head_mk).unwrap()).unwrap();
    let mk_diff = run_inspect(
        &[
            "--diff",
            base_mk_path.to_str().unwrap(),
            head_mk_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(mk_diff.status.code(), Some(1));
    let mk_diff_json: Value = serde_json::from_slice(&mk_diff.stdout).unwrap();
    let mk_fields: Vec<&str> = mk_diff_json["changes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|c| c["tier"] == "tier_a")
        .map(|c| c["field"].as_str().unwrap())
        .collect();
    for expected in
        ["audit.kernelsPassed", "audit.auditMode", "audit.kernelsSkipped", "audit.paranoidQuorum"]
    {
        assert!(mk_fields.contains(&expected), "missing Tier A `{expected}` in {mk_fields:?}");
    }

    // `--require-unchanged-specs` catches `audit.specification` symbol change
    // and exits `1` even without `--no-regressions`.
    let mut spec_swap = clean.clone();
    spec_swap["audit"]["specification"] = json!("Spec.zero_alt");
    let spec_swap_path = tmp.path().join("spec_swap.json");
    fs::write(&spec_swap_path, serde_json::to_vec(&spec_swap).unwrap()).unwrap();
    let spec_swap_standalone = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            spec_swap_path.to_str().unwrap(),
            "--require-unchanged-specs",
        ],
        None,
    );
    assert_eq!(spec_swap_standalone.status.code(), Some(1));
    let spec_swap_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            spec_swap_path.to_str().unwrap(),
            "--require-unchanged-specs",
            "--no-regressions",
        ],
        None,
    );
    assert_eq!(spec_swap_diff.status.code(), Some(1));

    // Reordering `tcb_shims` and nested `guards` produces zero diff changes.
    let mut shims_a = clean.clone();
    shims_a["tcb_shims"] = json!([
        {
            "id": "s1",
            "kind": "append_only_spec_lemma",
            "sha256": "1".repeat(64),
            "status": "proved",
            "guards": ["g1", "g2"]
        },
        {
            "id": "s2",
            "kind": "capture_driver",
            "sha256": "e".repeat(64),
            "status": "tested",
            "guards": ["g3"]
        }
    ]);
    let mut shims_b = clean.clone();
    shims_b["tcb_shims"] = json!([
        {
            "id": "s2",
            "kind": "capture_driver",
            "sha256": "e".repeat(64),
            "status": "tested",
            "guards": ["g3"]
        },
        {
            "id": "s1",
            "kind": "append_only_spec_lemma",
            "sha256": "1".repeat(64),
            "status": "proved",
            "guards": ["g2", "g1"]
        }
    ]);
    let shims_a_path = tmp.path().join("shims_a.json");
    let shims_b_path = tmp.path().join("shims_b.json");
    fs::write(&shims_a_path, serde_json::to_vec(&shims_a).unwrap()).unwrap();
    fs::write(&shims_b_path, serde_json::to_vec(&shims_b).unwrap()).unwrap();
    let shims_diff = run_inspect(
        &[
            "--diff",
            shims_a_path.to_str().unwrap(),
            shims_b_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(shims_diff.status.code(), Some(0));
    let shims_json: Value = serde_json::from_slice(&shims_diff.stdout).unwrap();
    assert_eq!(shims_json["changes"], json!([]));

    // Dropping `anchored_at` on `model_system_relation` is a Tier A regression.
    let mut rel_a = clean.clone();
    rel_a["model_system_relation"] = json!({
        "kind": "simulation",
        "qualifier": "lock_step",
        "direction": "forward",
        "anchored_at": "mir_op",
        "licensed_claim_shapes": ["forall_safety"]
    });
    let mut rel_b = rel_a.clone();
    rel_b["model_system_relation"].as_object_mut().unwrap().remove("anchored_at");
    let rel_a_path = tmp.path().join("rel_a.json");
    let rel_b_path = tmp.path().join("rel_b.json");
    fs::write(&rel_a_path, serde_json::to_vec(&rel_a).unwrap()).unwrap();
    fs::write(&rel_b_path, serde_json::to_vec(&rel_b).unwrap()).unwrap();
    let rel_diff = run_inspect(
        &[
            "--diff",
            rel_a_path.to_str().unwrap(),
            rel_b_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(rel_diff.status.code(), Some(1));
    let rel_json: Value = serde_json::from_slice(&rel_diff.stdout).unwrap();
    assert!(
        rel_json["changes"][0]["base"].as_str().unwrap().contains("anchor=mir_op"),
        "{rel_json}"
    );

    // `candidate_features` mismatch fails validation and newly added candidate
    // features fail `--diff --no-regressions`.
    let mut bad_cf = clean.clone();
    bad_cf["experimental"] = json!(false);
    bad_cf["candidate_features"] = json!(["mir_semantics"]);
    let bad_cf_path = tmp.path().join("bad_cf.json");
    fs::write(&bad_cf_path, serde_json::to_vec(&bad_cf).unwrap()).unwrap();
    let bad_cf_out = run_inspect(&[bad_cf_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(bad_cf_out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&bad_cf_out.stdout).contains("candidate_features"));

    let mut head_cf = clean.clone();
    head_cf["experimental"] = json!(true);
    head_cf["candidate_features"] = json!(["mir_semantics"]);
    let head_cf_path = tmp.path().join("head_cf.json");
    fs::write(&head_cf_path, serde_json::to_vec(&head_cf).unwrap()).unwrap();
    let cf_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            head_cf_path.to_str().unwrap(),
            "--no-regressions",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(cf_diff.status.code(), Some(1));
    let cf_diff_json: Value = serde_json::from_slice(&cf_diff.stdout).unwrap();
    assert!(
        cf_diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "candidate_features" && c["tier"] == "tier_a"),
        "{cf_diff_json}"
    );
}
