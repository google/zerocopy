// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Canonical strongly-connected-component ordering of a call graph.

use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap},
};

/// One condensed component, in callee-first order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SccComponent {
    /// Position in the callee-first order (`0..components.len()`).
    pub scc_id: usize,
    /// Members, sorted by UTF-8 byte order.
    pub members: Vec<String>,
    /// More than one member, or a single member that calls itself.
    pub is_cyclic: bool,
}

/// Condenses the call graph `edges` over `nodes` into strongly connected
/// components and orders them callee-first.
///
/// Iterative (explicit-stack) Tarjan, then Kahn's algorithm with a min-heap
/// keyed by each component's smallest member. Sorting nodes and adjacency
/// lists first makes the result independent of input order. Edges to nodes
/// outside `nodes` are ignored. Duplicate nodes are an error.
pub fn callee_first_sccs(
    nodes: &[String],
    edges: &BTreeMap<String, BTreeSet<String>>,
) -> Result<Vec<SccComponent>, String> {
    let mut sorted: Vec<String> = nodes.to_vec();
    sorted.sort();
    sorted.dedup();
    if sorted.len() != nodes.len() {
        return Err("duplicate node identities in SCC input".to_owned());
    }
    let index: BTreeMap<&str, usize> =
        sorted.iter().enumerate().map(|(i, s)| (s.as_str(), i)).collect();
    let n = sorted.len();
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut self_edge = vec![false; n];
    for (u, name) in sorted.iter().enumerate() {
        if let Some(callees) = edges.get(name) {
            for callee in callees {
                if let Some(&v) = index.get(callee.as_str()) {
                    self_edge[u] |= u == v;
                    adj[u].push(v);
                }
            }
            adj[u].sort_unstable();
            adj[u].dedup();
        }
    }

    let mut next_index = 0usize;
    let mut indices: Vec<Option<usize>> = vec![None; n];
    let mut lowlink = vec![0usize; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut on_stack = vec![false; n];
    let mut raw: Vec<(Vec<usize>, bool)> = Vec::new();
    for root in 0..n {
        if indices[root].is_some() {
            continue;
        }
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        indices[root] = Some(next_index);
        lowlink[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&(v, pos)) = work.last() {
            if pos < adj[v].len() {
                let w = adj[v][pos];
                if let Some(top) = work.last_mut() {
                    top.1 = pos + 1;
                }
                match indices[w] {
                    None => {
                        indices[w] = Some(next_index);
                        lowlink[w] = next_index;
                        next_index += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        work.push((w, 0));
                    }
                    Some(wi) if on_stack[w] => lowlink[v] = lowlink[v].min(wi),
                    Some(_) => {}
                }
            } else {
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    lowlink[parent] = lowlink[parent].min(lowlink[v]);
                }
                if Some(lowlink[v]) == indices[v] {
                    let mut comp = Vec::new();
                    while let Some(w) = stack.pop() {
                        on_stack[w] = false;
                        comp.push(w);
                        if w == v {
                            break;
                        }
                    }
                    comp.sort_unstable();
                    let cyclic = comp.len() > 1 || self_edge[comp[0]];
                    raw.push((comp, cyclic));
                }
            }
        }
    }

    let mut comp_of = vec![0usize; n];
    for (c, (members, _)) in raw.iter().enumerate() {
        for &m in members {
            comp_of[m] = c;
        }
    }
    let mut callers: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); raw.len()];
    let mut pending: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); raw.len()];
    for u in 0..n {
        for &w in &adj[u] {
            let (cu, cw) = (comp_of[u], comp_of[w]);
            if cu != cw {
                pending[cu].insert(cw);
                callers[cw].insert(cu);
            }
        }
    }
    let mut remaining: Vec<usize> = pending.iter().map(BTreeSet::len).collect();
    let mut heap: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
    for (c, &r) in remaining.iter().enumerate() {
        if r == 0 {
            heap.push(Reverse((raw[c].0[0], c)));
        }
    }
    let mut ordered = Vec::with_capacity(raw.len());
    while let Some(Reverse((_, c))) = heap.pop() {
        let (members, is_cyclic) = &raw[c];
        ordered.push(SccComponent {
            scc_id: ordered.len(),
            members: members.iter().map(|&m| sorted[m].clone()).collect(),
            is_cyclic: *is_cyclic,
        });
        for &caller in &callers[c] {
            remaining[caller] -= 1;
            if remaining[caller] == 0 {
                heap.push(Reverse((raw[caller].0[0], caller)));
            }
        }
    }
    if ordered.len() != raw.len() {
        return Err("condensed SCC graph contained a cycle".to_owned());
    }
    Ok(ordered)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn graph(pairs: &[(&str, &str)]) -> BTreeMap<String, BTreeSet<String>> {
        let mut g: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for (a, b) in pairs {
            g.entry((*a).to_owned()).or_default().insert((*b).to_owned());
        }
        g
    }

    fn names(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|s| (*s).to_owned()).collect()
    }

    #[test]
    fn orders_callees_first_and_groups_cycles() {
        // main -> {f, g}; f <-> g; g -> leaf; leaf -> leaf.
        let g = graph(&[
            ("main", "f"),
            ("main", "g"),
            ("f", "g"),
            ("g", "f"),
            ("g", "leaf"),
            ("leaf", "leaf"),
        ]);
        let sccs = callee_first_sccs(&names(&["main", "g", "leaf", "f"]), &g).unwrap();
        let members: Vec<Vec<String>> = sccs.iter().map(|c| c.members.clone()).collect();
        assert_eq!(members, vec![names(&["leaf"]), names(&["f", "g"]), names(&["main"])]);
        assert_eq!(sccs.iter().map(|c| c.is_cyclic).collect::<Vec<_>>(), vec![true, true, false]);
    }

    #[test]
    fn is_independent_of_input_order() {
        let g = graph(&[("a", "b"), ("b", "c"), ("d", "c")]);
        let one = callee_first_sccs(&names(&["a", "b", "c", "d"]), &g).unwrap();
        let two = callee_first_sccs(&names(&["d", "c", "b", "a"]), &g).unwrap();
        assert_eq!(one, two);
    }

    #[test]
    fn rejects_duplicates_and_ignores_external_callees() {
        assert!(callee_first_sccs(&names(&["a", "a"]), &BTreeMap::new()).is_err());
        let g = graph(&[("a", "extern_fn")]);
        let sccs = callee_first_sccs(&names(&["a"]), &g).unwrap();
        assert_eq!(sccs.len(), 1);
        assert!(!sccs[0].is_cyclic);
    }
}
