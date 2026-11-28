// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `Proof.IdTree` byte decision trees over body identities, and the
//! rendering of the `Proof/IdTree.lean` module.

use std::fmt::Write as _;

const ID_TREE_PREAMBLE: &str = "-- Copyright 2026 The Fuchsia Authors\n--\n\
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n\
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n\
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n\
-- This file may not be copied, modified, or distributed except according to\n\
-- those terms.\n\n\
module\nprelude\npublic import Anneal.SccSharding.BinChunkTree\n\n\
@[expose] public section\n\nnamespace Proof.IdTree\n\n";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ByteDecisionTree {
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

pub(super) fn byte_list_tag(bs: &[u8]) -> Option<u128> {
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
    pub(super) fn depth(&self) -> usize {
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

    pub(super) fn build(identities: &[String]) -> Result<Self, String> {
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
