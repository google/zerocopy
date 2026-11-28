// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture shard manifest validation, `Proof.IdTree` decision-tree generation,
//! and static-DAG `anneal-shards.json` planning for Tarjan SCC sharding.

mod id_tree;
mod validate;

use clap::Args;
use serde::{Deserialize, Serialize};

#[cfg(test)]
use self::id_tree::{ByteDecisionTree, byte_list_tag};
pub use self::{
    id_tree::render_id_tree_module,
    validate::{compare_shard_plan, parse_and_validate_capture_shards},
};

pub const CAPTURE_SHARDS_SCHEMA_VERSION: u32 = 1;
pub const SHARD_PLAN_SCHEMA_VERSION: u32 = 1;
pub const DEFAULT_SHARD_MIN_BODIES: usize = 20;
pub const DEFAULT_SHARD_MAX_BODIES: usize = 20;
pub const DEFAULT_SHARD_MAX_AST_NODES: usize = 2_500;

fn parse_positive_usize(raw: &str) -> Result<usize, String> {
    let val: usize = raw.parse().map_err(|_| format!("invalid integer: {raw}"))?;
    if val == 0 {
        return Err("value must be at least 1".to_owned());
    }
    Ok(val)
}

/// Shared CLI flags configuring Tarjan SCC sharding budgets.
#[derive(Args, Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShardArgs {
    /// Minimum body count above which `.olean` sharding activates (`N > min`).
    #[arg(long, global = true, default_value_t = DEFAULT_SHARD_MIN_BODIES, value_name = "N")]
    pub shard_min_bodies: usize,
    /// Maximum bodies packed into a single coarsened shard (`>= 1`).
    #[arg(
        long,
        global = true,
        default_value_t = DEFAULT_SHARD_MAX_BODIES,
        value_name = "N",
        value_parser = parse_positive_usize
    )]
    pub shard_max_bodies: usize,
    /// Maximum AST nodes packed into a single coarsened shard (`>= 1`).
    #[arg(
        long,
        global = true,
        default_value_t = DEFAULT_SHARD_MAX_AST_NODES,
        value_name = "NODES",
        value_parser = parse_positive_usize
    )]
    pub shard_max_ast_nodes: usize,
}

impl Default for ShardArgs {
    fn default() -> Self {
        Self {
            shard_min_bodies: DEFAULT_SHARD_MIN_BODIES,
            shard_max_bodies: DEFAULT_SHARD_MAX_BODIES,
            shard_max_ast_nodes: DEFAULT_SHARD_MAX_AST_NODES,
        }
    }
}

/// Validated runtime sharding budget policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShardConfig {
    pub shard_min_bodies: usize,
    pub shard_max_bodies: usize,
    pub shard_max_ast_nodes: usize,
}

impl From<&ShardArgs> for ShardConfig {
    fn from(args: &ShardArgs) -> Self {
        Self {
            shard_min_bodies: args.shard_min_bodies,
            shard_max_bodies: args.shard_max_bodies,
            shard_max_ast_nodes: args.shard_max_ast_nodes,
        }
    }
}

/// Authenticated per-shard metadata in `capture_shards.json`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CaptureShardEntry {
    pub shard_idx: usize,
    pub capture_module: String,
    pub proof_module: String,
    pub capture_sha256: String,
    pub num_bodies: usize,
    pub ast_nodes: usize,
    pub has_cycle: bool,
    pub oversized_scc: bool,
    pub scc_ids: Vec<usize>,
    pub callee_shards: Vec<usize>,
    pub global_def_id_range: [usize; 2],
    pub identities: Vec<String>,
}

/// Authenticated `capture_shards.json` manifest written with `capture.json`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CaptureShardsManifest {
    pub schema_version: u32,
    pub scope: String,
    pub total_bodies: usize,
    pub total_sccs: usize,
    pub cyclic_sccs: usize,
    pub total_shards: usize,
    pub is_lean_module: bool,
    pub id_tree_sha256: String,
    pub shards: Vec<CaptureShardEntry>,
}

/// Nominal static-DAG shard entry inside `anneal-shards.json`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ShardPlanEntry {
    pub shard_idx: usize,
    pub capture_module: String,
    pub proof_module: String,
    pub num_bodies: usize,
    pub has_cycle: bool,
    pub oversized_scc: bool,
    pub callee_shards: Vec<usize>,
    pub global_def_id_range: [usize; 2],
    pub identities: Vec<String>,
}

/// Nominal static-DAG `anneal-shards.json` plan checked by
/// `--verify-shard-plan` and managed by `cargo anneal shard-plan`.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ShardPlan {
    pub schema_version: u32,
    pub sharded: bool,
    pub scope: String,
    pub shard_min_bodies: usize,
    pub shard_max_bodies: usize,
    pub shard_max_ast_nodes: usize,
    pub total_bodies: usize,
    pub total_shards: usize,
    pub id_tree_sha256: Option<String>,
    pub shards: Vec<ShardPlanEntry>,
}

impl ShardPlan {
    pub fn from_unsharded(scope: &str, total_bodies: usize, config: ShardConfig) -> Self {
        Self {
            schema_version: SHARD_PLAN_SCHEMA_VERSION,
            sharded: false,
            scope: scope.to_owned(),
            shard_min_bodies: config.shard_min_bodies,
            shard_max_bodies: config.shard_max_bodies,
            shard_max_ast_nodes: config.shard_max_ast_nodes,
            total_bodies,
            total_shards: 0,
            id_tree_sha256: None,
            shards: Vec::new(),
        }
    }

    pub fn from_sharded(manifest: &CaptureShardsManifest, config: ShardConfig) -> Self {
        Self {
            schema_version: SHARD_PLAN_SCHEMA_VERSION,
            sharded: true,
            scope: manifest.scope.clone(),
            shard_min_bodies: config.shard_min_bodies,
            shard_max_bodies: config.shard_max_bodies,
            shard_max_ast_nodes: config.shard_max_ast_nodes,
            total_bodies: manifest.total_bodies,
            total_shards: manifest.total_shards,
            id_tree_sha256: Some(manifest.id_tree_sha256.clone()),
            shards: manifest
                .shards
                .iter()
                .map(|s| ShardPlanEntry {
                    shard_idx: s.shard_idx,
                    capture_module: s.capture_module.clone(),
                    proof_module: s.proof_module.clone(),
                    num_bodies: s.num_bodies,
                    has_cycle: s.has_cycle,
                    oversized_scc: s.oversized_scc,
                    callee_shards: s.callee_shards.clone(),
                    global_def_id_range: s.global_def_id_range,
                    identities: s.identities.clone(),
                })
                .collect(),
        }
    }

    pub fn to_pretty_json(&self) -> Result<Vec<u8>, String> {
        let mut out =
            serde_json::to_vec_pretty(self).map_err(|e| format!("serialize shard plan: {e}"))?;
        out.push(b'\n');
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn valid_manifest() -> CaptureShardsManifest {
        CaptureShardsManifest {
            schema_version: CAPTURE_SHARDS_SCHEMA_VERSION,
            scope: "crate".to_owned(),
            total_bodies: 3,
            total_sccs: 2,
            cyclic_sccs: 1,
            total_shards: 2,
            is_lean_module: true,
            id_tree_sha256: "a".repeat(64),
            shards: vec![
                CaptureShardEntry {
                    shard_idx: 0,
                    capture_module: "Captured.Shard_000".to_owned(),
                    proof_module: "Proof.Shard_000".to_owned(),
                    capture_sha256: "b".repeat(64),
                    num_bodies: 2,
                    ast_nodes: 10,
                    has_cycle: true,
                    oversized_scc: false,
                    scc_ids: vec![0],
                    callee_shards: vec![],
                    global_def_id_range: [0, 1],
                    identities: vec!["rust-path-v1::a".to_owned(), "rust-path-v1::b".to_owned()],
                },
                CaptureShardEntry {
                    shard_idx: 1,
                    capture_module: "Captured.Shard_001".to_owned(),
                    proof_module: "Proof.Shard_001".to_owned(),
                    capture_sha256: "c".repeat(64),
                    num_bodies: 1,
                    ast_nodes: 5,
                    has_cycle: false,
                    oversized_scc: false,
                    scc_ids: vec![1],
                    callee_shards: vec![0],
                    global_def_id_range: [2, 2],
                    identities: vec!["rust-path-v1::c".to_owned()],
                },
            ],
        }
    }

    #[test]
    fn rejects_contradictory_scc_metadata() {
        let mut m = valid_manifest();
        m.total_sccs = 0;
        m.cyclic_sccs = 0;
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("invalid total_sccs"), "{err}");

        let mut m = valid_manifest();
        m.total_sccs = 4;
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("invalid total_sccs"), "{err}");

        let mut m = valid_manifest();
        m.cyclic_sccs = 3;
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("exceeds total_sccs"), "{err}");

        let mut m = valid_manifest();
        m.total_sccs = 3;
        m.shards[0].has_cycle = false;
        m.shards[0].scc_ids = vec![0, 1];
        m.shards[1].has_cycle = true;
        m.shards[1].scc_ids = vec![2];
        m.cyclic_sccs = 2;
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("cyclic shard capacities"), "{err}");

        let mut m = valid_manifest();
        m.shards[0].scc_ids = vec![0, 0];
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("duplicates scc_id"), "{err}");

        let mut m = valid_manifest();
        m.shards[1].scc_ids = vec![9];
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("out-of-range scc_id"), "{err}");

        let mut m = valid_manifest();
        m.shards[0].oversized_scc = true;
        m.total_sccs = 3;
        m.shards[0].scc_ids = vec![0, 1];
        m.shards[1].scc_ids = vec![2];
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("oversized_scc"), "{err}");

        let mut m = valid_manifest();
        m.cyclic_sccs = 0;
        let err = parse_and_validate_capture_shards(
            &serde_json::to_vec(&m).unwrap(),
            "crate",
            3,
        )
        .unwrap_err();
        assert!(err.contains("cyclic shard capacities"), "{err}");
    }

    #[test]
    fn decision_tree_stays_logarithmic_on_disjoint_single_byte_diffs_and_tag_collisions() {
        let single_pos: Vec<String> = (0..64)
            .map(|i| {
                let mut s = vec![b'a'; 64];
                s[i] = b'b';
                String::from_utf8(s).unwrap()
            })
            .collect();
        let tree = ByteDecisionTree::build(&single_pos).unwrap();
        assert!(tree.depth() <= 16, "unexpected depth {} for 64 single-diff strings", tree.depth());

        let mut tag_collide = Vec::with_capacity(24);
        for d in 0..24u8 {
            let b0 = 65 + 2 * d;
            let b1 = 90 - d;
            let s = format!("{}{}", b0 as char, b1 as char);
            assert_eq!(byte_list_tag(s.as_bytes()), Some(245));
            tag_collide.push(s);
        }
        let lex_tree = ByteDecisionTree::build(&tag_collide).unwrap();
        assert!(lex_tree.depth() <= 12, "unexpected depth {}", lex_tree.depth());
    }
}
