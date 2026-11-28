// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Deterministic Tarjan SCC condensation and Kahn min-heap topological
//! ordering of a capture's call graph.

use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap},
};

use super::SccComponent;

/// Iterative (explicit-stack) Tarjan SCC condensation followed by Kahn
/// lexicographic min-heap callee-first topological ordering.
///
/// Pre-sorting `identities` and adjacency lists by UTF-8 byte order guarantees
/// canonical output independent of `rustc` hash-table iteration order.
pub fn compute_tarjan_sccs(
    identities: &[String],
    edges: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(Vec<SccComponent>, BTreeMap<String, usize>), String> {
    let mut sorted_nodes: Vec<String> = identities.to_vec();
    sorted_nodes.sort();
    sorted_nodes.dedup();
    if sorted_nodes.len() != identities.len() {
        return Err("duplicate body identities in Tarjan SCC input".to_owned());
    }
    let node_to_idx: BTreeMap<&str, usize> = sorted_nodes
        .iter()
        .enumerate()
        .map(|(i, s)| (s.as_str(), i))
        .collect();
    let n = sorted_nodes.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut has_self_edge = vec![false; n];
    for (u_idx, u_id) in sorted_nodes.iter().enumerate() {
        if let Some(callees) = edges.get(u_id) {
            for callee in callees {
                if let Some(&v_idx) = node_to_idx.get(callee.as_str()) {
                    if u_idx == v_idx {
                        has_self_edge[u_idx] = true;
                    }
                    adj[u_idx].push(v_idx);
                }
            }
            adj[u_idx].sort_unstable();
            adj[u_idx].dedup();
        }
    }

    let mut index_counter = 0usize;
    let mut indices: Vec<Option<usize>> = vec![None; n];
    let mut lowlink: Vec<usize> = vec![0; n];
    let mut tarjan_stack: Vec<usize> = Vec::new();
    let mut on_stack: Vec<bool> = vec![false; n];
    let mut raw_sccs: Vec<(Vec<usize>, bool)> = Vec::new();

    for root in 0..n {
        if indices[root].is_some() {
            continue;
        }
        let mut work: Vec<(usize, usize)> = Vec::new();
        indices[root] = Some(index_counter);
        lowlink[root] = index_counter;
        index_counter += 1;
        tarjan_stack.push(root);
        on_stack[root] = true;
        work.push((root, 0));

        while let Some((v, pos)) = work.last().copied() {
            if pos < adj[v].len() {
                let w = adj[v][pos];
                work.last_mut().expect("non-empty work stack").1 = pos + 1;
                if indices[w].is_none() {
                    indices[w] = Some(index_counter);
                    lowlink[w] = index_counter;
                    index_counter += 1;
                    tarjan_stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    let w_idx = indices[w].expect("visited node has index");
                    if w_idx < lowlink[v] {
                        lowlink[v] = w_idx;
                    }
                }
            } else {
                work.pop();
                if let Some(&(parent, _)) = work.last()
                    && lowlink[v] < lowlink[parent]
                {
                    lowlink[parent] = lowlink[v];
                }
                if Some(lowlink[v]) == indices[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = tarjan_stack.pop() {
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    comp.sort_unstable();
                    let is_cyclic = comp.len() > 1 || (comp.len() == 1 && has_self_edge[comp[0]]);
                    raw_sccs.push((comp, is_cyclic));
                }
            }
        }
    }

    let num_sccs = raw_sccs.len();
    let mut raw_node_to_scc = vec![0usize; n];
    for (c_idx, (members, _)) in raw_sccs.iter().enumerate() {
        for &m in members {
            raw_node_to_scc[m] = c_idx;
        }
    }

    let mut callee_sets: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); num_sccs];
    let mut caller_sets: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); num_sccs];
    for u in 0..n {
        let cu = raw_node_to_scc[u];
        for &w in &adj[u] {
            let cw = raw_node_to_scc[w];
            if cu != cw {
                callee_sets[cu].insert(cw);
                caller_sets[cw].insert(cu);
            }
        }
    }

    let mut rem_callees: Vec<usize> = callee_sets.iter().map(BTreeSet::len).collect();
    // Min-heap keyed by `(min_member_node_index, raw_scc_idx)`. Because
    // `sorted_nodes` is already sorted by UTF-8 byte order and each `comp` is
    // non-empty and sorted, `comp[0]` orders SCCs identically to `min`.
    let mut heap: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
    for (c_idx, &rem) in rem_callees.iter().enumerate() {
        if rem == 0 {
            heap.push(Reverse((raw_sccs[c_idx].0[0], c_idx)));
        }
    }

    let mut ordered_sccs = Vec::with_capacity(num_sccs);
    let mut node_to_scc = BTreeMap::new();
    while let Some(Reverse((_, c_idx))) = heap.pop() {
        let new_id = ordered_sccs.len();
        let (ref member_indices, is_cyclic) = raw_sccs[c_idx];
        let members: Vec<String> = member_indices
            .iter()
            .map(|&idx| {
                let s = sorted_nodes[idx].clone();
                node_to_scc.insert(s.clone(), new_id);
                s
            })
            .collect();
        ordered_sccs.push(SccComponent {
            scc_id: new_id,
            members,
            is_cyclic,
        });
        for &caller_c in &caller_sets[c_idx] {
            rem_callees[caller_c] -= 1;
            if rem_callees[caller_c] == 0 {
                heap.push(Reverse((raw_sccs[caller_c].0[0], caller_c)));
            }
        }
    }

    if ordered_sccs.len() != num_sccs {
        return Err("condensed SCC graph contained a cycle".to_owned());
    }

    Ok((ordered_sccs, node_to_scc))
}
