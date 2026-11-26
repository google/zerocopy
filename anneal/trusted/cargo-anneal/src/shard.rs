// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Capture shard manifest validation, `Proof.IdTree` decision-tree generation,
//! and static-DAG `anneal-shards.json` planning for Tarjan SCC sharding.

use std::fmt::Write as _;

use crate::is_sha256_hex;
use clap::Args;
use serde::{Deserialize, Serialize};

pub const CAPTURE_SHARDS_SCHEMA_VERSION: u32 = 1;
pub const SHARD_PLAN_SCHEMA_VERSION: u32 = 1;
pub const DEFAULT_SHARD_MIN_BODIES: usize = 20;
pub const DEFAULT_SHARD_MAX_BODIES: usize = 20;
pub const DEFAULT_SHARD_MAX_AST_NODES: usize = 2_500;

const ID_TREE_PREAMBLE: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n\
module\nprelude\npublic import Anneal.SccSharding.BinChunkTree\n\n\
@[expose] public section\n\nnamespace Proof.IdTree\n\n";

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

#[derive(Clone, Debug, PartialEq, Eq)]
enum ByteDecisionTree {
    Fail,
    Leaf(usize),
    SplitByte {
        pos: usize,
        threshold: u16,
        lt_branch: Box<Self>,
        ge_branch: Box<Self>,
    },
    SplitTag {
        threshold: u128,
        lt_branch: Box<Self>,
        ge_branch: Box<Self>,
    },
    SplitLex {
        pivot: Vec<u8>,
        le_branch: Box<Self>,
        gt_branch: Box<Self>,
    },
}

fn byte_code_at(bs: &[u8], pos: usize) -> u16 {
    bs.get(pos).copied().map_or(256, u16::from)
}

fn byte_list_tag(bs: &[u8]) -> Option<u128> {
    let mut sum = 0u128;
    for (idx, &b) in bs.iter().enumerate() {
        let w = u128::try_from(idx + 1).ok()?;
        sum = sum.checked_add(w.checked_mul(u128::from(b))?)?;
    }
    Some(sum)
}

fn best_threshold_split<T: Ord + Copy>(sorted_vals: &[T]) -> Option<(T, usize)> {
    let n = sorted_vals.len();
    if n < 2 {
        return None;
    }
    let mut best: Option<(T, usize)> = None;
    for i in 1..n {
        if sorted_vals[i - 1] < sorted_vals[i] {
            let score = i.max(n - i);
            if best.is_none_or(|(_, prev_score)| score < prev_score) {
                best = Some((sorted_vals[i], score));
            }
        }
    }
    best
}

fn join_balanced_lean_lists(chunks: &[String]) -> String {
    match chunks {
        [] => "[]".to_owned(),
        [single] => single.clone(),
        _ => {
            let mid = chunks.len() / 2;
            format!(
                "(_root_.List.append {} {})",
                join_balanced_lean_lists(&chunks[..mid]),
                join_balanced_lean_lists(&chunks[mid..])
            )
        }
    }
}

fn render_u8_list(bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return "[]".to_owned();
    }
    let chunks: Vec<String> = bytes
        .chunks(16)
        .map(|chunk| {
            let items: Vec<String> =
                chunk.iter().map(|b| format!("(_root_.UInt8.ofNat {b})")).collect();
            format!("[{}]", items.join(", "))
        })
        .collect();
    join_balanced_lean_lists(&chunks)
}

impl ByteDecisionTree {
    fn eval(&self, bs: &[u8]) -> Option<usize> {
        let mut node = self;
        loop {
            match node {
                Self::Fail => return None,
                Self::Leaf(id) => return Some(*id),
                Self::SplitByte { pos, threshold, lt_branch, ge_branch } => {
                    node = if byte_code_at(bs, *pos) < *threshold { lt_branch } else { ge_branch };
                }
                Self::SplitTag { threshold, lt_branch, ge_branch } => {
                    let tag = byte_list_tag(bs)?;
                    node = if tag < *threshold { lt_branch } else { ge_branch };
                }
                Self::SplitLex { pivot, le_branch, gt_branch } => {
                    node = if bs <= pivot.as_slice() { le_branch } else { gt_branch };
                }
            }
        }
    }

    #[cfg(test)]
    fn depth(&self) -> usize {
        match self {
            Self::Fail | Self::Leaf(_) => 0,
            Self::SplitByte { lt_branch, ge_branch, .. }
            | Self::SplitTag { lt_branch, ge_branch, .. } => {
                1 + lt_branch.depth().max(ge_branch.depth())
            }
            Self::SplitLex { le_branch, gt_branch, .. } => {
                1 + le_branch.depth().max(gt_branch.depth())
            }
        }
    }

    fn build(identities: &[String]) -> Result<Self, String> {
        let items: Vec<(usize, &[u8])> =
            identities.iter().enumerate().map(|(idx, s)| (idx, s.as_bytes())).collect();
        let mut dedup_check = items.clone();
        dedup_check.sort_unstable_by(|a, b| a.1.cmp(b.1));
        for pair in dedup_check.windows(2) {
            if pair[0].1 == pair[1].1 {
                return Err(
                    "duplicate UTF-8 byte sequences in ByteDecisionTree::build".to_owned(),
                );
            }
        }

        fn build_rec(entries: &[(usize, &[u8])]) -> Result<ByteDecisionTree, String> {
            match entries {
                [] => Ok(ByteDecisionTree::Fail),
                [(idx, _)] => Ok(ByteDecisionTree::Leaf(*idx)),
                _ => {
                    let n = entries.len();
                    let balance_limit = (n * 3) / 4;
                    let half_ceil = n.div_ceil(2);
                    let max_len = entries.iter().map(|(_, bs)| bs.len()).max().unwrap_or(0);
                    let mut best_pos = 0usize;
                    let mut best_thr = 0u16;
                    let mut best_score = usize::MAX;
                    let mut codes = Vec::with_capacity(n);
                    for pos in 0..=max_len {
                        codes.clear();
                        codes.extend(entries.iter().map(|(_, bs)| byte_code_at(bs, pos)));
                        codes.sort_unstable();
                        if let Some((thr, score)) = best_threshold_split(&codes)
                            && score < best_score
                        {
                            best_score = score;
                            best_pos = pos;
                            best_thr = thr;
                            if score <= half_ceil {
                                break;
                            }
                        }
                    }
                    if best_score <= balance_limit {
                        let (lt_entries, ge_entries): (Vec<_>, Vec<_>) = entries
                            .iter()
                            .copied()
                            .partition(|(_, bs)| byte_code_at(bs, best_pos) < best_thr);
                        if !lt_entries.is_empty() && !ge_entries.is_empty() {
                            return Ok(ByteDecisionTree::SplitByte {
                                pos: best_pos,
                                threshold: best_thr,
                                lt_branch: Box::new(build_rec(&lt_entries)?),
                                ge_branch: Box::new(build_rec(&ge_entries)?),
                            });
                        }
                    }

                    let mut tags = Vec::with_capacity(n);
                    let mut all_tagged = true;
                    for &(_, bs) in entries {
                        match byte_list_tag(bs) {
                            Some(t) => tags.push(t),
                            None => {
                                all_tagged = false;
                                break;
                            }
                        }
                    }
                    if all_tagged {
                        tags.sort_unstable();
                        if let Some((tag_thr, tag_score)) = best_threshold_split(&tags)
                            && tag_score <= balance_limit
                        {
                            let (lt_entries, ge_entries): (Vec<_>, Vec<_>) = entries
                                .iter()
                                .copied()
                                .partition(|(_, bs)| byte_list_tag(bs).unwrap() < tag_thr);
                            if !lt_entries.is_empty() && !ge_entries.is_empty() {
                                return Ok(ByteDecisionTree::SplitTag {
                                    threshold: tag_thr,
                                    lt_branch: Box::new(build_rec(&lt_entries)?),
                                    ge_branch: Box::new(build_rec(&ge_entries)?),
                                });
                            }
                        }
                    }

                    let mut sorted = entries.to_vec();
                    sorted.sort_unstable_by(|a, b| a.1.cmp(b.1));
                    let split_at = n / 2;
                    let pivot = sorted[split_at - 1].1.to_vec();
                    let (le_entries, gt_entries) = sorted.split_at(split_at);
                    Ok(ByteDecisionTree::SplitLex {
                        pivot,
                        le_branch: Box::new(build_rec(le_entries)?),
                        gt_branch: Box::new(build_rec(gt_entries)?),
                    })
                }
            }
        }
        let tree = build_rec(&items)?;
        for &(idx, bs) in &items {
            if tree.eval(bs) != Some(idx) {
                return Err(format!("ByteDecisionTree self-verification failed at DefId {idx}"));
            }
        }
        Ok(tree)
    }

    fn render_lean(&self, indent: usize) -> String {
        match self {
            Self::Fail => "Anneal.SccSharding.ByteDecisionTree.fail".to_owned(),
            Self::Leaf(def_id) => format!("(Anneal.SccSharding.ByteDecisionTree.leaf {def_id})"),
            Self::SplitByte { pos, threshold, lt_branch, ge_branch } => {
                let pad = " ".repeat(indent + 2);
                format!(
                    "(Anneal.SccSharding.ByteDecisionTree.splitByte {pos} {threshold}\n\
                     {pad}{}\n\
                     {pad}{})",
                    lt_branch.render_lean(indent + 2),
                    ge_branch.render_lean(indent + 2)
                )
            }
            Self::SplitTag { threshold, lt_branch, ge_branch } => {
                let pad = " ".repeat(indent + 2);
                format!(
                    "(Anneal.SccSharding.ByteDecisionTree.splitTag {threshold}\n\
                     {pad}{}\n\
                     {pad}{})",
                    lt_branch.render_lean(indent + 2),
                    ge_branch.render_lean(indent + 2)
                )
            }
            Self::SplitLex { pivot, le_branch, gt_branch } => {
                let pad = " ".repeat(indent + 2);
                format!(
                    "(Anneal.SccSharding.ByteDecisionTree.splitLex {}\n\
                     {pad}{}\n\
                     {pad}{})",
                    render_u8_list(pivot),
                    le_branch.render_lean(indent + 2),
                    gt_branch.render_lean(indent + 2)
                )
            }
        }
    }
}

/// Render deterministic `Proof/IdTree.lean` source matching `rustc-capture`'s
/// `id_tree_sha256` digest.
pub fn render_id_tree_module(identities_in_def_order: &[String]) -> Result<String, String> {
    let dt = ByteDecisionTree::build(identities_in_def_order)?;
    let mut out = String::from(ID_TREE_PREAMBLE);
    let _ = write!(
        out,
        "def idDecisionTree : Anneal.SccSharding.ByteDecisionTree :=\n\
         \x20 {}\n\n\
         end Proof.IdTree\n\nend\n",
        dt.render_lean(2)
    );
    Ok(out)
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
