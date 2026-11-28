// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `inspect --verify-artifacts` and the three-tier receipt diff.

use super::*;

#[test]
fn verify_artifacts_and_three_tier_diff_enforced() {
    let tmp = tempfile::tempdir().unwrap();
    let art_dir = tmp.path().join("artifacts");
    let (clean, ..) = sample_receipt_bundle(&art_dir);
    let clean_path = tmp.path().join("clean.json");
    fs::write(&clean_path, serde_json::to_vec(&clean).unwrap()).unwrap();

    let (sorry_tainted, sorry_path, s3_gutns, cap_bin_sha) =
        artifact_checks::verifies_artifacts_and_receipt_gates(
            &tmp,
            art_dir.clone(),
            clean.clone(),
            clean_path.clone(),
        );
    diff_regressions::diff_flags_regressions_and_bad_inputs(
        &tmp,
        art_dir,
        clean.clone(),
        clean_path.clone(),
    );
    diff_semantics::diff_tracks_scope_sorry_shims_and_warnings(
        &tmp,
        clean.clone(),
        clean_path.clone(),
        s3_gutns,
        sorry_path,
        sorry_tainted,
        cap_bin_sha,
    );
    profile_v2::checks_minirust_and_profile_v2_receipts(&tmp, clean.clone(), clean_path.clone());
    diff_invariance::diff_kernels_specs_shim_order_and_anchors(&tmp, clean, clean_path);
}

#[path = "artifacts_and_three_tier_diff/artifact_checks.rs"]
mod artifact_checks;
#[path = "artifacts_and_three_tier_diff/diff_invariance.rs"]
mod diff_invariance;
#[path = "artifacts_and_three_tier_diff/diff_regressions.rs"]
mod diff_regressions;
#[path = "artifacts_and_three_tier_diff/diff_semantics.rs"]
mod diff_semantics;
#[path = "artifacts_and_three_tier_diff/profile_v2.rs"]
mod profile_v2;
