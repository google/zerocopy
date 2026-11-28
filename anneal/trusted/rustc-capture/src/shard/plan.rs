// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Contiguous bucket coarsening of SCCs into shards, shard DAG invariants,
//! and verification of checked-in `anneal-shards.json` plans.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
};

use super::{
    CAPTURE_SHARDS_SCHEMA_VERSION, CaptureShardEntry, CaptureShardsManifest, PreparedShards,
    SHARD_PLAN_SCHEMA_VERSION, SccComponent, ShardConfig, ShardPlan,
    id_tree::render_id_tree_module, scc::compute_tarjan_sccs, scope_label,
};
use crate::{identity, ir, lean};

struct CoarsenedBucket {
    sccs: Vec<SccComponent>,
    oversized_scc: bool,
    ast_nodes: usize,
}

fn verify_shard_dag_invariants(
    shards: &[CaptureShardEntry],
    sccs: &[SccComponent],
    identity_to_shard: &BTreeMap<String, usize>,
    total_bodies: usize,
) -> Result<(), String> {
    for comp in sccs {
        if comp.members.len() > 1 {
            let owners: BTreeSet<usize> = comp
                .members
                .iter()
                .map(|m| {
                    identity_to_shard
                        .get(m)
                        .copied()
                        .ok_or_else(|| format!("missing shard assignment for {m}"))
                })
                .collect::<Result<_, _>>()?;
            if owners.len() != 1 {
                return Err(format!(
                    "multi-body SCC {} split across shards {owners:?}",
                    comp.scc_id
                ));
            }
        }
    }
    let mut expected_base = 0usize;
    let mut seen_sccs = vec![false; sccs.len()];
    for (expected_idx, shard) in shards.iter().enumerate() {
        if shard.shard_idx != expected_idx {
            return Err(format!(
                "non-contiguous shard index {} (expected {expected_idx})",
                shard.shard_idx
            ));
        }
        if shard.num_bodies == 0 || shard.identities.len() != shard.num_bodies {
            return Err(format!("invalid body count in {}", shard.capture_module));
        }
        if shard.scc_ids.is_empty() || shard.scc_ids.len() > shard.num_bodies {
            return Err(format!(
                "invalid scc_ids count {} in {}",
                shard.scc_ids.len(),
                shard.capture_module
            ));
        }
        if shard.oversized_scc && shard.scc_ids.len() != 1 {
            return Err(format!(
                "oversized_scc {} has {} SCCs (expected 1)",
                shard.capture_module,
                shard.scc_ids.len()
            ));
        }
        for &scc_id in &shard.scc_ids {
            let Some(slot) = seen_sccs.get_mut(scc_id) else {
                return Err(format!(
                    "out-of-range scc_id {scc_id} in {}",
                    shard.capture_module
                ));
            };
            if *slot {
                return Err(format!("duplicate scc_id {scc_id} in {}", shard.capture_module));
            }
            *slot = true;
        }
        let expected_end = expected_base + shard.num_bodies - 1;
        if shard.global_def_id_range != [expected_base, expected_end] {
            return Err(format!(
                "non-contiguous global_def_id_range {:?} in {}",
                shard.global_def_id_range, shard.capture_module
            ));
        }
        expected_base = expected_end + 1;
        for &cs in &shard.callee_shards {
            if cs >= shard.shard_idx {
                return Err(format!(
                    "shard DAG acyclicity violation: {} depends on Shard_{cs:03}",
                    shard.capture_module
                ));
            }
        }
    }
    if expected_base != total_bodies {
        return Err(format!(
            "shard body ranges covered {expected_base} bodies, expected {total_bodies}"
        ));
    }
    if seen_sccs.iter().any(|&seen| !seen) {
        return Err("shard scc_ids do not cover all SCCs".to_owned());
    }
    Ok(())
}

/// Partition `manifest` into Tarjan SCC shards when `total_bodies >
/// config.shard_min_bodies`, reordering `manifest.program.bodies` and
/// `manifest.selected` into canonical callee-first `DefId` order.
///
/// When `total_bodies <= config.shard_min_bodies`, leaves `manifest` untouched
/// and returns `Ok(None)` so small captures keep the 2-file `Captured.lean` +
/// `capture.json` single-file layout.
pub fn maybe_shard_manifest(
    manifest: &mut ir::Manifest,
    config: ShardConfig,
) -> Result<Option<PreparedShards>, String> {
    config.validate()?;
    let total_bodies = manifest.program.bodies().len();
    if total_bodies <= config.shard_min_bodies {
        return Ok(None);
    }

    let mut old_idx_by_id: BTreeMap<String, usize> = BTreeMap::new();
    let mut identities = Vec::with_capacity(total_bodies);
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for (idx, body) in manifest.program.bodies().iter().enumerate() {
        let id = body.identity().to_owned();
        if old_idx_by_id.insert(id.clone(), idx).is_some() {
            return Err(format!("duplicate body identity {id}"));
        }
        edges.insert(id.clone(), body.callees().clone());
        identities.push(id);
    }

    let (sccs, _) = compute_tarjan_sccs(&identities, &edges)?;
    let cyclic_sccs = sccs.iter().filter(|c| c.is_cyclic).count();

    let mut buckets: Vec<CoarsenedBucket> = Vec::new();
    let mut cur_sccs: Vec<SccComponent> = Vec::new();
    let mut cur_bodies = 0usize;
    let mut cur_ast = 0usize;

    for comp in &sccs {
        let comp_bodies = comp.members.len();
        let comp_ast: usize = comp
            .members
            .iter()
            .map(|m| manifest.program.bodies()[old_idx_by_id[m]].ast_nodes())
            .sum();
        let comp_oversized =
            comp_bodies > config.shard_max_bodies || comp_ast > config.shard_max_ast_nodes;

        if !cur_sccs.is_empty()
            && (comp_oversized
                || cur_bodies + comp_bodies > config.shard_max_bodies
                || cur_ast + comp_ast > config.shard_max_ast_nodes)
        {
            buckets.push(CoarsenedBucket {
                sccs: std::mem::take(&mut cur_sccs),
                oversized_scc: false,
                ast_nodes: cur_ast,
            });
            cur_bodies = 0;
            cur_ast = 0;
        }

        if comp_oversized {
            buckets.push(CoarsenedBucket {
                sccs: vec![comp.clone()],
                oversized_scc: true,
                ast_nodes: comp_ast,
            });
        } else {
            cur_sccs.push(comp.clone());
            cur_bodies += comp_bodies;
            cur_ast += comp_ast;
        }
    }
    if !cur_sccs.is_empty() {
        buckets.push(CoarsenedBucket {
            sccs: cur_sccs,
            oversized_scc: false,
            ast_nodes: cur_ast,
        });
    }

    let mut permutation = Vec::with_capacity(total_bodies);
    let mut identity_to_shard = BTreeMap::new();
    for (s_idx, bucket) in buckets.iter().enumerate() {
        for comp in &bucket.sccs {
            for m in &comp.members {
                permutation.push(old_idx_by_id[m]);
                identity_to_shard.insert(m.clone(), s_idx);
            }
        }
    }
    manifest.reorder_bodies(&permutation)?;

    let ordered_identities: Vec<String> = manifest
        .program
        .bodies()
        .iter()
        .map(|b| b.identity().to_owned())
        .collect();
    let id_tree_lean = render_id_tree_module(&ordered_identities)?;
    let id_tree_sha256 = identity::sha256_bytes(id_tree_lean.as_bytes());

    let mut shard_sources = Vec::with_capacity(buckets.len());
    let mut shard_entries = Vec::with_capacity(buckets.len());
    let mut cursor = 0usize;
    for (s_idx, bucket) in buckets.iter().enumerate() {
        let count: usize = bucket.sccs.iter().map(|c| c.members.len()).sum();
        let slice = &manifest.program.bodies()[cursor..cursor + count];
        let shard_lean = lean::render_shard_module(s_idx, slice);
        let capture_sha256 = identity::sha256_bytes(shard_lean.as_bytes());
        let mut callee_shards_set = BTreeSet::new();
        for body in slice {
            for callee_id in body.callees() {
                if let Some(&cs) = identity_to_shard.get(callee_id)
                    && cs != s_idx
                {
                    callee_shards_set.insert(cs);
                }
            }
        }
        let has_cycle = bucket.sccs.iter().any(|c| c.is_cyclic);
        shard_entries.push(CaptureShardEntry {
            shard_idx: s_idx,
            capture_module: format!("Captured.Shard_{s_idx:03}"),
            proof_module: format!("Proof.Shard_{s_idx:03}"),
            capture_sha256,
            num_bodies: count,
            ast_nodes: bucket.ast_nodes,
            has_cycle,
            oversized_scc: bucket.oversized_scc,
            scc_ids: bucket.sccs.iter().map(|c| c.scc_id).collect(),
            callee_shards: callee_shards_set.into_iter().collect(),
            global_def_id_range: [cursor, cursor + count - 1],
            identities: slice.iter().map(|b| b.identity().to_owned()).collect(),
        });
        shard_sources.push((s_idx, shard_lean));
        cursor += count;
    }

    verify_shard_dag_invariants(&shard_entries, &sccs, &identity_to_shard, total_bodies)?;

    let root_lean = lean::render_sharded_root(
        manifest.program.scope(),
        manifest.program.mir_profile_version(),
        manifest.program.overflow_checks(),
        manifest.program.panic(),
        manifest.program.has_local_panic_handler(),
        &shard_entries,
    );
    let shards_manifest = CaptureShardsManifest {
        schema_version: CAPTURE_SHARDS_SCHEMA_VERSION,
        scope: scope_label(manifest.program.scope()).to_owned(),
        total_bodies,
        total_sccs: sccs.len(),
        cyclic_sccs,
        total_shards: shard_entries.len(),
        is_lean_module: true,
        id_tree_sha256,
        shards: shard_entries,
    };
    let manifest_json =
        serde_json::to_vec_pretty(&shards_manifest).map_err(|e| e.to_string())?;

    Ok(Some(PreparedShards {
        root_lean,
        shard_sources,
        manifest: shards_manifest,
        manifest_json,
    }))
}

/// Verify a checked-in `anneal-shards.json` plan (`--verify-shard-plan <PATH>`)
/// fail-closed against the actual computed [`ShardPlan`].
pub fn verify_shard_plan_file(plan_path: &Path, actual: &ShardPlan) -> Result<(), String> {
    let raw = fs::read(plan_path).map_err(|e| {
        format!(
            "cannot read shard plan {}: {e}",
            plan_path.display()
        )
    })?;
    let expected: ShardPlan = serde_json::from_slice(&raw).map_err(|e| {
        format!(
            "invalid shard plan JSON {}: {e}",
            plan_path.display()
        )
    })?;
    if expected.schema_version != SHARD_PLAN_SCHEMA_VERSION {
        return Err(format!(
            "unsupported shard plan schema_version {} in {} (expected {SHARD_PLAN_SCHEMA_VERSION})",
            expected.schema_version,
            plan_path.display()
        ));
    }
    if &expected != actual {
        return Err(format!(
            "shard plan {} drifted from captured crate topology \
             (expected sharded={} total_bodies={} total_shards={}, \
             got sharded={} total_bodies={} total_shards={}); \
             regenerate with `cargo anneal shard-plan --write {} ...`",
            plan_path.display(),
            expected.sharded,
            expected.total_bodies,
            expected.total_shards,
            actual.sharded,
            actual.total_bodies,
            actual.total_shards,
            plan_path.display()
        ));
    }
    Ok(())
}
