// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Fuel bounds from the control flow graph of a captured body.

use serde_json::Value;

/// How a terminator field names successor blocks, following its type in
/// `ir::Terminator`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Edge {
    /// `u32`: always a block.
    Block,
    /// `Option<u32>`: a block, or an explicit null for a call that diverges.
    OptionalBlock,
    /// `Vec<(u128, u32)>`: the second element of each pair is a block.
    SwitchTargets,
}

/// Each captured terminator kind with its successor-block fields.
pub(super) const TERMINATOR_EDGES: &[(&str, &[(&str, Edge)])] = &[
    ("goto", &[("block", Edge::Block)]),
    ("switch_int", &[("otherwise", Edge::Block), ("targets", Edge::SwitchTargets)]),
    ("assert", &[("target", Edge::Block)]),
    ("core_call", &[("target", Edge::OptionalBlock)]),
    ("call", &[("target", Edge::OptionalBlock)]),
    ("sysroot_call", &[("target", Edge::OptionalBlock)]),
    ("ret", &[]),
    ("unreachable", &[]),
    ("unsupported", &[]),
];

/// The successor blocks of a terminator.
fn successors(term: &Value) -> Result<Vec<u64>, String> {
    let kind = term.get("kind").and_then(Value::as_str).ok_or("terminator has no kind")?;
    let (_, fields) = TERMINATOR_EDGES
        .iter()
        .find(|(k, _)| *k == kind)
        .ok_or_else(|| format!("unknown terminator kind `{kind}`"))?;
    let mut out = Vec::new();
    for &(name, edge) in *fields {
        let value = term.get(name);
        let malformed = || format!("{kind} has a missing or malformed `{name}`");
        match edge {
            Edge::Block => out.push(value.and_then(Value::as_u64).ok_or_else(malformed)?),
            // The capture always emits the field, so only an explicit null
            // diverges; a missing field or any other non-block value is
            // malformed.
            Edge::OptionalBlock => match value.ok_or_else(malformed)? {
                Value::Null => {}
                v => out.push(v.as_u64().ok_or_else(malformed)?),
            },
            Edge::SwitchTargets => {
                for pair in value.and_then(Value::as_array).ok_or_else(malformed)? {
                    let block = pair.as_array().and_then(|p| p.get(1)).and_then(Value::as_u64);
                    out.push(block.ok_or_else(malformed)?);
                }
            }
        }
    }
    Ok(out)
}

/// The number of statements and terminators in `blocks` when their control
/// flow graph is acyclic, which bounds the length of any single-frame run.
/// `None` for a cyclic graph.
pub(super) fn acyclic_fuel(blocks: &[Value]) -> Result<Option<usize>, String> {
    let mut edges = Vec::with_capacity(blocks.len());
    let mut total = 0usize;
    for (i, block) in blocks.iter().enumerate() {
        let statements = block
            .get("statements")
            .and_then(Value::as_array)
            .ok_or_else(|| format!("block {i} has no statements array"))?;
        total = statements
            .len()
            .checked_add(1)
            .and_then(|n| total.checked_add(n))
            .ok_or("statement count overflows")?;
        let term = block.get("terminator").ok_or_else(|| format!("block {i} has no terminator"))?;
        let succ = successors(term).map_err(|e| format!("block {i}: {e}"))?;
        let succ = succ
            .into_iter()
            .map(|s| {
                usize::try_from(s)
                    .ok()
                    .filter(|&s| s < blocks.len())
                    .ok_or_else(|| format!("block {i} targets missing block {s}"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        edges.push(succ);
    }
    // Iterative three-color depth-first search from every block.
    let mut color = vec![0u8; blocks.len()];
    for start in 0..blocks.len() {
        if color[start] != 0 {
            continue;
        }
        let mut stack = vec![(start, 0usize)];
        color[start] = 1;
        while let Some(&mut (node, ref mut next)) = stack.last_mut() {
            if let Some(&succ) = edges[node].get(*next) {
                *next += 1;
                match color[succ] {
                    0 => {
                        color[succ] = 1;
                        stack.push((succ, 0));
                    }
                    1 => return Ok(None),
                    _ => {}
                }
            } else {
                color[node] = 2;
                stack.pop();
            }
        }
    }
    Ok(Some(total))
}
