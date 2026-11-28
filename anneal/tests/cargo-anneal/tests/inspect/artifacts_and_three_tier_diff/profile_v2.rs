// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The MiniRust provenance requirement and Profile v2 receipts across
//! formats and diffs.

use super::*;

/// Runs the sections of `verify_artifacts_and_three_tier_diff_enforced`
/// that the module documentation lists.
pub(super) fn checks_minirust_and_profile_v2_receipts(
    tmp: &tempfile::TempDir,
    clean: Value,
    clean_path: PathBuf,
) {
    // Omitting `minirust_upstream` on an applicable Profile v1 receipt fails
    // closed operationally (exit 2).
    let mut missing_minirust = clean.clone();
    missing_minirust["correspondence_provenance"]
        .as_object_mut()
        .unwrap()
        .remove("minirust_upstream");
    let missing_minirust_path = tmp.path().join("missing_minirust.json");
    fs::write(&missing_minirust_path, serde_json::to_vec(&missing_minirust).unwrap()).unwrap();
    let missing_minirust_out = run_inspect(&[missing_minirust_path.to_str().unwrap()], None);
    assert_eq!(missing_minirust_out.status.code(), Some(2));
    assert!(
        String::from_utf8_lossy(&missing_minirust_out.stderr)
            .contains("/correspondence_provenance/minirust_upstream"),
        "{}",
        String::from_utf8_lossy(&missing_minirust_out.stderr)
    );

    // Profile v2 receipts (`*TheoremV2`, Profile v2 MIR assumption, and
    // pinned `correspondence_provenance.applicable == false`) pass strict
    // validation across CLI formats and diffing, while mismatches fail closed.
    let mut v2_unit = clean.clone();
    v2_unit["status"] = json!("selected_unit_verified");
    v2_unit["scope"] = json!({
        "kind": "selected_unit",
        "roots": ["scalar::zero"],
        "instantiations": [{ "path": "scalar::zero", "args": [] }]
    });
    v2_unit["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheoremV2");
    v2_unit["audit"]["modelClosure"] = json!([{
        "name": "Trusted.MirSemantics.UnitTheoremV2",
        "module": "Trusted.MirSemantics"
    }]);
    v2_unit["assumptions"] = json!([
        "faithful pinned compiler capture",
        "experimental Profile v2 MIR semantics: bounded caller memory"
    ]);
    v2_unit["correspondence_provenance"] = json!({
        "applicable": false,
        "reason": "bundled Pass 2 correspondence covers Profile v1 semantics only"
    });
    let v2_unit_path = tmp.path().join("v2_unit.json");
    fs::write(&v2_unit_path, serde_json::to_vec(&v2_unit).unwrap()).unwrap();

    let v2_json = run_inspect(
        &[
            v2_unit_path.to_str().unwrap(),
            "--require-untainted",
            "--unknown-fields",
            "deny",
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(v2_json.status.code(), Some(0), "{}", String::from_utf8_lossy(&v2_json.stderr));
    assert!(v2_json.stderr.is_empty());
    let v2_parsed: Value = serde_json::from_slice(&v2_json.stdout).unwrap();
    assert_eq!(v2_parsed["status"], "selected_unit_verified");
    assert_eq!(v2_parsed["tainted"], false);
    assert_eq!(v2_parsed["unrecognized_fields"], json!([]));
    assert_eq!(v2_parsed["invariant_violations"], json!([]));
    assert_eq!(v2_parsed["policy_violations"], json!([]));
    let receipt_str = serde_json::to_string(&v2_parsed["receipt"]).unwrap();
    assert!(receipt_str.contains("\"correspondence_applicable\":false"), "{receipt_str}");
    assert!(receipt_str.contains("Trusted.MirSemantics.UnitTheoremV2"), "{receipt_str}");

    let v2_ledger = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "ledger"], None);
    assert_eq!(v2_ledger.status.code(), Some(0));
    assert!(
        String::from_utf8_lossy(&v2_ledger.stdout)
            .contains("audit.canonical_root=Trusted.MirSemantics.UnitTheoremV2\n")
    );
    let v2_human = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "human"], None);
    assert_eq!(v2_human.status.code(), Some(0));
    let v2_human_out = String::from_utf8_lossy(&v2_human.stdout);
    assert!(v2_human_out.contains("Trusted.MirSemantics.UnitTheoremV2"), "{v2_human_out}");
    // Pass 2 does not certify Profile v2, so the success is qualified.
    assert!(v2_human_out.contains(" [QUALIFIED]\n"), "{v2_human_out}");
    assert!(v2_human_out.contains("correspondence=inapplicable"), "{v2_human_out}");
    assert!(v2_human_out.contains("  correspondence: inapplicable ("), "{v2_human_out}");
    let v2_md = run_inspect(&[v2_unit_path.to_str().unwrap(), "--format", "markdown"], None);
    assert_eq!(v2_md.status.code(), Some(0));
    let v2_md_out = String::from_utf8_lossy(&v2_md.stdout);
    assert!(v2_md_out.contains("selected_unit_verified"), "{v2_md_out}");
    assert!(v2_md_out.contains("`untainted`"), "{v2_md_out}");
    assert!(v2_md_out.contains("`correspondence=inapplicable`"), "{v2_md_out}");

    let v1_to_v2_diff = run_inspect(
        &[
            "--diff",
            clean_path.to_str().unwrap(),
            v2_unit_path.to_str().unwrap(),
            "--format",
            "json",
        ],
        None,
    );
    assert_eq!(v1_to_v2_diff.status.code(), Some(0));
    let diff_json: Value = serde_json::from_slice(&v1_to_v2_diff.stdout).unwrap();
    assert!(
        diff_json["changes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|c| c["field"] == "audit.canonicalRoot"),
        "{diff_json}"
    );

    let mut v2_missing_assump = v2_unit.clone();
    v2_missing_assump["assumptions"] = json!(["faithful pinned compiler capture"]);
    let v2_missing_assump_path = tmp.path().join("v2_missing_assump.json");
    fs::write(&v2_missing_assump_path, serde_json::to_vec(&v2_missing_assump).unwrap()).unwrap();
    let v2_missing_out =
        run_inspect(&[v2_missing_assump_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(v2_missing_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&v2_missing_out.stdout)
            .contains("disagrees with Profile v2 `assumptions`")
    );

    let mut v2_v1_prov = v2_unit;
    v2_v1_prov["correspondence_provenance"] = clean["correspondence_provenance"].clone();
    let v2_v1_prov_path = tmp.path().join("v2_v1_prov.json");
    fs::write(&v2_v1_prov_path, serde_json::to_vec(&v2_v1_prov).unwrap()).unwrap();
    let v2_v1_prov_out = run_inspect(&[v2_v1_prov_path.to_str().unwrap(), "--passive"], None);
    assert_eq!(v2_v1_prov_out.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&v2_v1_prov_out.stdout)
            .contains("correspondence_provenance.applicable == false")
    );
}
