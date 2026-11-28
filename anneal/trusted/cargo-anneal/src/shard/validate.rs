// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Validation of `capture_shards.json` manifests and comparison of shard
//! plans.

use super::{
    CAPTURE_SHARDS_SCHEMA_VERSION, CaptureShardsManifest, SHARD_PLAN_SCHEMA_VERSION, ShardPlan,
};
use crate::is_sha256_hex;

/// Strictly parse and authenticate every structural and DAG-acyclicity
/// invariant of `capture_shards.json`.
pub fn parse_and_validate_capture_shards(
    bytes: &[u8],
    expected_scope: &str,
    expected_bodies: usize,
) -> Result<CaptureShardsManifest, String> {
    let manifest: CaptureShardsManifest =
        serde_json::from_slice(bytes).map_err(|e| format!("invalid capture_shards.json: {e}"))?;
    if manifest.schema_version != CAPTURE_SHARDS_SCHEMA_VERSION {
        return Err(format!(
            "unsupported capture_shards.json schema_version {} (expected {})",
            manifest.schema_version, CAPTURE_SHARDS_SCHEMA_VERSION
        ));
    }
    if manifest.scope != expected_scope {
        return Err(format!(
            "capture_shards.json scope {:?} disagrees with requested scope {:?}",
            manifest.scope, expected_scope
        ));
    }
    if !manifest.is_lean_module {
        return Err(
            "capture_shards.json must emit Lean `module`-mode shards (`is_lean_module: true`)"
                .to_owned(),
        );
    }
    if manifest.total_bodies == 0 || manifest.total_bodies != expected_bodies {
        return Err(format!(
            "capture_shards.json total_bodies {} disagrees with capture.json body count {}",
            manifest.total_bodies, expected_bodies
        ));
    }
    if manifest.total_shards == 0 || manifest.total_shards != manifest.shards.len() {
        return Err(format!(
            "capture_shards.json total_shards {} disagrees with shards array length {}",
            manifest.total_shards,
            manifest.shards.len()
        ));
    }
    if !is_sha256_hex(&manifest.id_tree_sha256) {
        return Err("capture_shards.json carries invalid id_tree_sha256".to_owned());
    }

    let mut cursor = 0usize;
    if manifest.total_sccs == 0 || manifest.total_sccs > manifest.total_bodies {
        return Err(format!(
            "capture_shards.json invalid total_sccs {} for {} bodies",
            manifest.total_sccs, manifest.total_bodies
        ));
    }
    if manifest.cyclic_sccs > manifest.total_sccs {
        return Err(format!(
            "capture_shards.json cyclic_sccs {} exceeds total_sccs {}",
            manifest.cyclic_sccs, manifest.total_sccs
        ));
    }
    let mut seen_sccs = vec![false; manifest.total_sccs];
    let mut cyclic_shards = 0usize;
    let mut cyclic_shard_sccs = 0usize;
    for (idx, shard) in manifest.shards.iter().enumerate() {
        if shard.shard_idx != idx {
            return Err(format!(
                "capture_shards.json shard index {} out of order (expected {idx})",
                shard.shard_idx
            ));
        }
        let expected_cap = format!("Captured.Shard_{idx:03}");
        if shard.capture_module != expected_cap {
            return Err(format!(
                "capture_shards.json shard {idx} capture_module {:?} != {:?}",
                shard.capture_module, expected_cap
            ));
        }
        let expected_proof = format!("Proof.Shard_{idx:03}");
        if shard.proof_module != expected_proof {
            return Err(format!(
                "capture_shards.json shard {idx} proof_module {:?} != {:?}",
                shard.proof_module, expected_proof
            ));
        }
        if !is_sha256_hex(&shard.capture_sha256) {
            return Err(format!("capture_shards.json shard {idx} has invalid capture_sha256"));
        }
        if shard.num_bodies == 0 || shard.num_bodies != shard.identities.len() {
            return Err(format!(
                "capture_shards.json shard {idx} num_bodies {} mismatches {} identities",
                shard.num_bodies,
                shard.identities.len()
            ));
        }
        if shard.scc_ids.is_empty() || shard.scc_ids.len() > shard.num_bodies {
            return Err(format!(
                "capture_shards.json shard {idx} has invalid scc_ids count {} for {} bodies",
                shard.scc_ids.len(),
                shard.num_bodies
            ));
        }
        if shard.oversized_scc && shard.scc_ids.len() != 1 {
            return Err(format!(
                "capture_shards.json shard {idx} marks oversized_scc with {} SCCs (expected 1)",
                shard.scc_ids.len()
            ));
        }
        for &scc_id in &shard.scc_ids {
            let Some(slot) = seen_sccs.get_mut(scc_id) else {
                return Err(format!(
                    "capture_shards.json shard {idx} references out-of-range scc_id {scc_id} \
                     (total_sccs={})",
                    manifest.total_sccs
                ));
            };
            if *slot {
                return Err(format!(
                    "capture_shards.json shard {idx} duplicates scc_id {scc_id}"
                ));
            }
            *slot = true;
        }
        if shard.has_cycle {
            cyclic_shards += 1;
            cyclic_shard_sccs += shard.scc_ids.len();
        }
        let end_inclusive = cursor + shard.num_bodies - 1;
        if shard.global_def_id_range != [cursor, end_inclusive] {
            return Err(format!(
                "capture_shards.json shard {idx} global_def_id_range {:?} != [{cursor}, {end_inclusive}]",
                shard.global_def_id_range
            ));
        }
        cursor += shard.num_bodies;
        for (pos, &callee) in shard.callee_shards.iter().enumerate() {
            if callee >= idx {
                return Err(format!(
                    "capture_shards.json shard {idx} imports non-earlier shard {callee}"
                ));
            }
            if pos > 0 && shard.callee_shards[pos - 1] >= callee {
                return Err(format!(
                    "capture_shards.json shard {idx} has unsorted/duplicate callee_shards"
                ));
            }
        }
    }
    if let Some(missing) = seen_sccs.iter().position(|&seen| !seen) {
        return Err(format!(
            "capture_shards.json shards omit scc_id {missing} of total_sccs {}",
            manifest.total_sccs
        ));
    }
    if manifest.cyclic_sccs < cyclic_shards || manifest.cyclic_sccs > cyclic_shard_sccs {
        return Err(format!(
            "capture_shards.json cyclic_sccs {} is inconsistent with cyclic shard capacities \
             [{cyclic_shards}..={cyclic_shard_sccs}]",
            manifest.cyclic_sccs
        ));
    }
    if cursor != manifest.total_bodies {
        return Err(format!(
            "capture_shards.json shards cover {cursor} bodies != total_bodies {}",
            manifest.total_bodies
        ));
    }
    Ok(manifest)
}

/// Compare two `ShardPlan` values, returning a crisp static-DAG drift
/// diagnostic on mismatch.
pub fn compare_shard_plan(expected: &ShardPlan, actual: &ShardPlan) -> Result<(), String> {
    if expected.schema_version != SHARD_PLAN_SCHEMA_VERSION {
        return Err(format!(
            "unsupported shard-plan schema_version {} (expected {})",
            expected.schema_version, SHARD_PLAN_SCHEMA_VERSION
        ));
    }
    if expected == actual {
        return Ok(());
    }
    let mut diffs = Vec::new();
    if expected.sharded != actual.sharded {
        diffs.push(format!("sharded: expected {}, got {}", expected.sharded, actual.sharded));
    }
    if expected.scope != actual.scope {
        diffs.push(format!("scope: expected {:?}, got {:?}", expected.scope, actual.scope));
    }
    if expected.total_bodies != actual.total_bodies {
        diffs.push(format!(
            "total_bodies: expected {}, got {}",
            expected.total_bodies, actual.total_bodies
        ));
    }
    if expected.total_shards != actual.total_shards {
        diffs.push(format!(
            "total_shards: expected {}, got {}",
            expected.total_shards, actual.total_shards
        ));
    }
    if expected.id_tree_sha256 != actual.id_tree_sha256 {
        diffs.push(format!(
            "id_tree_sha256: expected {:?}, got {:?}",
            expected.id_tree_sha256, actual.id_tree_sha256
        ));
    }
    for idx in 0..expected.shards.len().max(actual.shards.len()) {
        match (expected.shards.get(idx), actual.shards.get(idx)) {
            (Some(e), Some(a)) if e != a => {
                diffs.push(format!(
                    "shard {idx} ({:?} vs {:?}) drifted (identities {:?} vs {:?}, callees {:?} vs {:?})",
                    e.proof_module,
                    a.proof_module,
                    e.identities,
                    a.identities,
                    e.callee_shards,
                    a.callee_shards
                ));
                if diffs.len() >= 5 {
                    break;
                }
            }
            (Some(e), None) => {
                diffs.push(format!("missing shard {idx} ({:?})", e.proof_module));
                break;
            }
            (None, Some(a)) => {
                diffs.push(format!("extra shard {idx} ({:?})", a.proof_module));
                break;
            }
            _ => {}
        }
    }
    if diffs.is_empty() {
        diffs.push("sharding configuration parameters differ".to_owned());
    }
    Err(format!(
        "shard-plan mismatch (re-run `cargo anneal shard-plan --write <PATH>`): {}",
        diffs.join("; ")
    ))
}
