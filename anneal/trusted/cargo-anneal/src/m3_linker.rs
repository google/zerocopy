// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Soundness-preserving lambda-lifted proof discharge (`M3`), canonical
//! Merkle constant-cone hashing, Tarjan union-SCC modular shard verification,
//! and offline zero-axiom `Deriv.linkAxioms` stitching.
//!
//! Operates strictly over UTF-8 `NDJSON 3.1.0` streams interned in
//! [`CanonicalArena`], with `#[forbid(unsafe_code)]` enforced on `mod
//! m3_linker`.

use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap, VecDeque},
};

use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

use crate::{
    ndjson_comparator::{
        CanonConstInfo, CanonExpr, CanonExprId, CanonInductiveBlock, CanonLevel, CanonLevelId,
        CanonName, CanonNameId, CanonicalArena, ClosureEntry, DefinitionSafety, ExportedEnv,
        MAX_NDJSON_BYTES, MAX_NDJSON_LINES, PINNED_INIT_PRIMITIVES, QuotKind, RecursorRule,
        ReducibilityHints, STANDARD_PERMITTED_AXIOMS, StructuralCompareRequest,
        StructuralCompareSummary, bfs_cone, build_closure_entries, format_blame_path,
        validate_axiom_list,
    },
    toolchain::{Failure, is_sha256_hex, sha256_bytes},
};

/// Maximum number of deduplicated lifted hypotheses permitted on a single
/// theorem during Option-B bottom-up lambda-lifting.
pub const MAX_LIFTED_HYPS_PER_THM: usize = 512;

/// Floor on the expression-arena budget permitted during M3 rewriting.
pub const MIN_M3_EXPR_BUDGET: usize = 65_536;

/// Multiplier over pre-M3 arena expression count permitted during M3 rewriting.
pub const M3_EXPR_BUDGET_MULTIPLIER: usize = 8;

const QUOT_PRIMITIVES: [(&str, QuotKind); 4] = [
    ("Quot", QuotKind::Type),
    ("Quot.mk", QuotKind::Ctor),
    ("Quot.lift", QuotKind::Lift),
    ("Quot.ind", QuotKind::Ind),
];

// ---------------------------------------------------------------------------
// 1. Universe level normalization & instantiation (`NormLevel`)
// ---------------------------------------------------------------------------

/// Structurally simplified universe level with positional parameter indices.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormLevel {
    Zero,
    Succ(Box<NormLevel>),
    Max(Box<NormLevel>, Box<NormLevel>),
    IMax(Box<NormLevel>, Box<NormLevel>),
    Param(u32),
}

fn comb_norm_max(a: NormLevel, b: NormLevel) -> NormLevel {
    if a == NormLevel::Zero {
        return b;
    }
    if b == NormLevel::Zero || a == b {
        return a;
    }
    if let (NormLevel::Succ(x), NormLevel::Succ(y)) = (&a, &b) {
        return NormLevel::Succ(Box::new(comb_norm_max((**x).clone(), (**y).clone())));
    }
    NormLevel::Max(Box::new(a), Box::new(b))
}

fn simplify_norm_imax(a: NormLevel, b: NormLevel) -> NormLevel {
    if b == NormLevel::Zero {
        return NormLevel::Zero;
    }
    if a == NormLevel::Zero || matches!(&a, NormLevel::Succ(inner) if **inner == NormLevel::Zero) {
        return b;
    }
    if matches!(&b, NormLevel::Succ(_)) {
        return comb_norm_max(a, b);
    }
    if a == b {
        return a;
    }
    NormLevel::IMax(Box::new(a), Box::new(b))
}

/// Normalize `lid` relative to `level_params` (mapping `Param(name)` to its
/// 0-based positional index and failing closed on unbound parameters).
pub fn normalize_level(
    arena: &CanonicalArena,
    lid: CanonLevelId,
    level_params: &[CanonNameId],
    phase: &str,
) -> Result<NormLevel, Failure> {
    match &arena.levels[lid.0 as usize] {
        CanonLevel::Zero => Ok(NormLevel::Zero),
        CanonLevel::Succ(inner) => Ok(NormLevel::Succ(Box::new(normalize_level(
            arena,
            *inner,
            level_params,
            phase,
        )?))),
        CanonLevel::Max(a, b) => {
            let na = normalize_level(arena, *a, level_params, phase)?;
            let nb = normalize_level(arena, *b, level_params, phase)?;
            Ok(comb_norm_max(na, nb))
        }
        CanonLevel::IMax(a, b) => {
            let na = normalize_level(arena, *a, level_params, phase)?;
            let nb = normalize_level(arena, *b, level_params, phase)?;
            Ok(simplify_norm_imax(na, nb))
        }
        CanonLevel::Param(p) => {
            let Some(pos) = level_params.iter().position(|x| x == p) else {
                return Err(Failure::policy(
                    phase,
                    format!("unbound universe level parameter `{}`", arena.name_str(*p)),
                ));
            };
            Ok(NormLevel::Param(pos as u32))
        }
    }
}

fn subst_norm_level(
    lvl: &NormLevel,
    args: &[NormLevel],
    phase: &str,
) -> Result<NormLevel, Failure> {
    match lvl {
        NormLevel::Zero => Ok(NormLevel::Zero),
        NormLevel::Succ(inner) => Ok(NormLevel::Succ(Box::new(subst_norm_level(
            inner, args, phase,
        )?))),
        NormLevel::Max(a, b) => {
            let sa = subst_norm_level(a, args, phase)?;
            let sb = subst_norm_level(b, args, phase)?;
            Ok(comb_norm_max(sa, sb))
        }
        NormLevel::IMax(a, b) => {
            let sa = subst_norm_level(a, args, phase)?;
            let sb = subst_norm_level(b, args, phase)?;
            Ok(simplify_norm_imax(sa, sb))
        }
        NormLevel::Param(idx) => args.get(*idx as usize).cloned().ok_or_else(|| {
            Failure::policy(
                phase,
                format!("universe argument index {idx} out of bounds"),
            )
        }),
    }
}

fn norm_to_canon_level(
    arena: &mut CanonicalArena,
    lvl: &NormLevel,
    level_params: &[CanonNameId],
    phase: &str,
) -> Result<CanonLevelId, Failure> {
    match lvl {
        NormLevel::Zero => Ok(arena.zero_level),
        NormLevel::Succ(inner) => {
            let cid = norm_to_canon_level(arena, inner, level_params, phase)?;
            Ok(arena.intern_level(CanonLevel::Succ(cid)))
        }
        NormLevel::Max(a, b) => {
            let ca = norm_to_canon_level(arena, a, level_params, phase)?;
            let cb = norm_to_canon_level(arena, b, level_params, phase)?;
            Ok(arena.intern_level(CanonLevel::Max(ca, cb)))
        }
        NormLevel::IMax(a, b) => {
            let ca = norm_to_canon_level(arena, a, level_params, phase)?;
            let cb = norm_to_canon_level(arena, b, level_params, phase)?;
            Ok(arena.intern_level(CanonLevel::IMax(ca, cb)))
        }
        NormLevel::Param(idx) => {
            let Some(&pname) = level_params.get(*idx as usize) else {
                return Err(Failure::policy(
                    phase,
                    format!("cannot materialize Param({idx}) outside levelParams"),
                ));
            };
            Ok(arena.intern_level(CanonLevel::Param(pname)))
        }
    }
}

/// Check whether `lid` contains zero universe `Param` nodes.
pub fn is_closed_canon_level(arena: &CanonicalArena, lid: CanonLevelId) -> bool {
    match &arena.levels[lid.0 as usize] {
        CanonLevel::Zero => true,
        CanonLevel::Succ(x) => is_closed_canon_level(arena, *x),
        CanonLevel::Max(a, b) | CanonLevel::IMax(a, b) => {
            is_closed_canon_level(arena, *a) && is_closed_canon_level(arena, *b)
        }
        CanonLevel::Param(_) => false,
    }
}

/// Render a canonical level into a deterministic human/wire string.
pub fn render_canon_level(arena: &CanonicalArena, lid: CanonLevelId) -> String {
    fn as_nat(arena: &CanonicalArena, id: CanonLevelId) -> Option<u64> {
        match &arena.levels[id.0 as usize] {
            CanonLevel::Zero => Some(0),
            CanonLevel::Succ(inner) => as_nat(arena, *inner).and_then(|n| n.checked_add(1)),
            _ => None,
        }
    }
    if let Some(n) = as_nat(arena, lid) {
        return n.to_string();
    }
    match &arena.levels[lid.0 as usize] {
        CanonLevel::Zero => "0".to_owned(),
        CanonLevel::Succ(inner) => format!("(succ {})", render_canon_level(arena, *inner)),
        CanonLevel::Max(a, b) => {
            format!(
                "(max {} {})",
                render_canon_level(arena, *a),
                render_canon_level(arena, *b)
            )
        }
        CanonLevel::IMax(a, b) => {
            format!(
                "(imax {} {})",
                render_canon_level(arena, *a),
                render_canon_level(arena, *b)
            )
        }
        CanonLevel::Param(p) => arena.name_str(*p).to_owned(),
    }
}

/// Parse a rendered wire universe level back into `arena` under `level_params`.
pub fn parse_rendered_level(
    arena: &mut CanonicalArena,
    s: &str,
    level_params: &[CanonNameId],
    phase: &str,
) -> Result<CanonLevelId, Failure> {
    let trimmed = s.trim();
    if let Ok(n) = trimmed.parse::<u64>() {
        let mut cur = arena.zero_level;
        for _ in 0..n {
            cur = arena.intern_level(CanonLevel::Succ(cur));
        }
        return Ok(cur);
    }
    if let Some(inner) = trimmed.strip_prefix('(').and_then(|x| x.strip_suffix(')')) {
        let inner = inner.trim();
        if let Some(rest) = inner.strip_prefix("succ ") {
            let sub = parse_rendered_level(arena, rest, level_params, phase)?;
            return Ok(arena.intern_level(CanonLevel::Succ(sub)));
        }
        for (prefix, is_imax) in [("max ", false), ("imax ", true)] {
            if let Some(rest) = inner.strip_prefix(prefix) {
                let (lhs_s, rhs_s) = split_two_sexpr_args(rest, phase)?;
                let lhs = parse_rendered_level(arena, lhs_s, level_params, phase)?;
                let rhs = parse_rendered_level(arena, rhs_s, level_params, phase)?;
                let node = if is_imax {
                    CanonLevel::IMax(lhs, rhs)
                } else {
                    CanonLevel::Max(lhs, rhs)
                };
                return Ok(arena.intern_level(node));
            }
        }
        return Err(Failure::policy(
            phase,
            format!("malformed level expression `{s}`"),
        ));
    }
    let pid = arena.intern_dotted_name(trimmed);
    if !level_params.contains(&pid) {
        return Err(Failure::policy(
            phase,
            format!("unbound universe level parameter `{trimmed}`"),
        ));
    }
    Ok(arena.intern_level(CanonLevel::Param(pid)))
}

fn split_two_sexpr_args<'a>(s: &'a str, phase: &str) -> Result<(&'a str, &'a str), Failure> {
    let s = s.trim();
    let mut depth = 0usize;
    for (idx, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                if depth == 0 {
                    return Err(Failure::policy(phase, format!("unbalanced `)` in `{s}`")));
                }
                depth -= 1;
            }
            ' ' if depth == 0 => {
                let lhs = s[..idx].trim();
                let rhs = s[idx + 1..].trim();
                if lhs.is_empty() || rhs.is_empty() {
                    return Err(Failure::policy(
                        phase,
                        format!("missing level operand in `{s}`"),
                    ));
                }
                return Ok((lhs, rhs));
            }
            _ => {}
        }
    }
    Err(Failure::policy(
        phase,
        format!("expected two level operands in `{s}`"),
    ))
}

/// Substitute `level_params` in `root_expr` with `level_args` (normalizing and
/// simplifying every resulting level relative to `ambient_params`).
pub fn instantiate_level_params_expr(
    arena: &mut CanonicalArena,
    root_expr: CanonExprId,
    decl_params: &[CanonNameId],
    level_args: &[CanonLevelId],
    ambient_params: &[CanonNameId],
    phase: &str,
) -> Result<CanonExprId, Failure> {
    if decl_params.len() != level_args.len() {
        return Err(Failure::policy(
            phase,
            format!(
                "universe parameter arity mismatch: expected {}, found {}",
                decl_params.len(),
                level_args.len()
            ),
        ));
    }
    if decl_params.is_empty() {
        // Still normalize levels in `root_expr` relative to `ambient_params` so
        // equivalent forms such as `max 1 0` vs `1` unify canonically in
        // `O(1)`.
        return normalize_expr_levels(arena, root_expr, ambient_params, phase);
    }
    let mut norm_args = Vec::with_capacity(level_args.len());
    for &arg in level_args {
        norm_args.push(normalize_level(arena, arg, ambient_params, phase)?);
    }
    let mut l_memo: HashMap<CanonLevelId, CanonLevelId> = HashMap::new();
    let mut map_lvl =
        |arena: &mut CanonicalArena, lid: CanonLevelId| -> Result<CanonLevelId, Failure> {
            if let Some(&cached) = l_memo.get(&lid) {
                return Ok(cached);
            }
            let norm = normalize_level(arena, lid, decl_params, phase)?;
            let subst = subst_norm_level(&norm, &norm_args, phase)?;
            let out = norm_to_canon_level(arena, &subst, ambient_params, phase)?;
            l_memo.insert(lid, out);
            Ok(out)
        };

    let mut e_memo: HashMap<CanonExprId, CanonExprId> = HashMap::new();
    let mut stack = vec![(root_expr, false)];
    while let Some((eid, ready)) = stack.pop() {
        if e_memo.contains_key(&eid) {
            continue;
        }
        let node = arena.exprs[eid.0 as usize].clone();
        if !ready {
            stack.push((eid, true));
            match &node {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, false));
                    stack.push((*a, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, false));
                    stack.push((*body, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, false));
                    stack.push((*value, false));
                    stack.push((*body, false));
                }
                CanonExpr::Proj { struct_expr, .. } => {
                    stack.push((*struct_expr, false));
                }
            }
        } else {
            let rebuilt = match node {
                CanonExpr::BVar(_) | CanonExpr::NatLit(_) | CanonExpr::StrLit(_) => eid,
                CanonExpr::Sort(u) => {
                    let nu = map_lvl(arena, u)?;
                    arena.intern_expr(CanonExpr::Sort(nu))
                }
                CanonExpr::Const(c, us) => {
                    let mut nus = Vec::with_capacity(us.len());
                    for u in us {
                        nus.push(map_lvl(arena, u)?);
                    }
                    arena.intern_expr(CanonExpr::Const(c, nus))
                }
                CanonExpr::App(f, a) => arena.intern_expr(CanonExpr::App(e_memo[&f], e_memo[&a])),
                CanonExpr::Lam { ty, body } => arena.intern_expr(CanonExpr::Lam {
                    ty: e_memo[&ty],
                    body: e_memo[&body],
                }),
                CanonExpr::ForallE { ty, body } => arena.intern_expr(CanonExpr::ForallE {
                    ty: e_memo[&ty],
                    body: e_memo[&body],
                }),
                CanonExpr::LetE { ty, value, body } => arena.intern_expr(CanonExpr::LetE {
                    ty: e_memo[&ty],
                    value: e_memo[&value],
                    body: e_memo[&body],
                }),
                CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr,
                } => arena.intern_expr(CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr: e_memo[&struct_expr],
                }),
            };
            e_memo.insert(eid, rebuilt);
        }
    }
    Ok(e_memo[&root_expr])
}

fn normalize_expr_levels(
    arena: &mut CanonicalArena,
    root_expr: CanonExprId,
    ambient_params: &[CanonNameId],
    phase: &str,
) -> Result<CanonExprId, Failure> {
    let mut l_memo: HashMap<CanonLevelId, CanonLevelId> = HashMap::new();
    let mut map_lvl =
        |arena: &mut CanonicalArena, lid: CanonLevelId| -> Result<CanonLevelId, Failure> {
            if let Some(&cached) = l_memo.get(&lid) {
                return Ok(cached);
            }
            let norm = normalize_level(arena, lid, ambient_params, phase)?;
            let out = norm_to_canon_level(arena, &norm, ambient_params, phase)?;
            l_memo.insert(lid, out);
            Ok(out)
        };
    let mut e_memo: HashMap<CanonExprId, CanonExprId> = HashMap::new();
    let mut stack = vec![(root_expr, false)];
    while let Some((eid, ready)) = stack.pop() {
        if e_memo.contains_key(&eid) {
            continue;
        }
        let node = arena.exprs[eid.0 as usize].clone();
        if !ready {
            stack.push((eid, true));
            match &node {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, false));
                    stack.push((*a, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, false));
                    stack.push((*body, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, false));
                    stack.push((*value, false));
                    stack.push((*body, false));
                }
                CanonExpr::Proj { struct_expr, .. } => {
                    stack.push((*struct_expr, false));
                }
            }
        } else {
            let rebuilt = match node {
                CanonExpr::BVar(_) | CanonExpr::NatLit(_) | CanonExpr::StrLit(_) => eid,
                CanonExpr::Sort(u) => {
                    let nu = map_lvl(arena, u)?;
                    arena.intern_expr(CanonExpr::Sort(nu))
                }
                CanonExpr::Const(c, us) => {
                    let mut nus = Vec::with_capacity(us.len());
                    for u in us {
                        nus.push(map_lvl(arena, u)?);
                    }
                    arena.intern_expr(CanonExpr::Const(c, nus))
                }
                CanonExpr::App(f, a) => arena.intern_expr(CanonExpr::App(e_memo[&f], e_memo[&a])),
                CanonExpr::Lam { ty, body } => arena.intern_expr(CanonExpr::Lam {
                    ty: e_memo[&ty],
                    body: e_memo[&body],
                }),
                CanonExpr::ForallE { ty, body } => arena.intern_expr(CanonExpr::ForallE {
                    ty: e_memo[&ty],
                    body: e_memo[&body],
                }),
                CanonExpr::LetE { ty, value, body } => arena.intern_expr(CanonExpr::LetE {
                    ty: e_memo[&ty],
                    value: e_memo[&value],
                    body: e_memo[&body],
                }),
                CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr,
                } => arena.intern_expr(CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr: e_memo[&struct_expr],
                }),
            };
            e_memo.insert(eid, rebuilt);
        }
    }
    Ok(e_memo[&root_expr])
}

// ---------------------------------------------------------------------------
// 2. Domain-separated canonical Merkle constant-cone hashing
// ---------------------------------------------------------------------------

/// Selects whether `Thm` declarations hash only their statement cone
/// (`TheoremSignatureCone`, proof-body invariant) or their complete
/// statement + proof cone (`FullDeclaration`, for offline shard deduplication).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigestMode {
    TheoremSignatureCone,
    FullDeclaration,
}

fn push_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_be_bytes());
}

fn push_bytes(buf: &mut Vec<u8>, b: &[u8]) {
    push_u64(buf, b.len() as u64);
    buf.extend_from_slice(b);
}

/// Encode `id` segment-by-segment so hierarchical `Str("a.b")` vs
/// `Str("a") -> Str("b")` and `Num(0)` vs `Str("0")` are collision-free.
pub fn encode_canon_name(arena: &CanonicalArena, id: CanonNameId, out: &mut Vec<u8>) {
    let mut segs: Vec<CanonNameId> = Vec::new();
    let mut cur = id;
    loop {
        match &arena.names[cur.0 as usize] {
            CanonName::Anonymous => break,
            CanonName::Str(pre, _) | CanonName::Num(pre, _) => {
                segs.push(cur);
                cur = *pre;
            }
        }
    }
    out.extend_from_slice(b"N:0");
    for seg_id in segs.into_iter().rev() {
        match &arena.names[seg_id.0 as usize] {
            CanonName::Anonymous => {}
            CanonName::Str(_, s) => {
                out.extend_from_slice(b"N:S");
                push_bytes(out, s.as_bytes());
            }
            CanonName::Num(_, n) => {
                out.extend_from_slice(b"N:I");
                push_u64(out, *n);
            }
        }
    }
}

/// Total structural comparison over `CanonNameId` spines.
pub fn cmp_canon_name(arena: &CanonicalArena, a: CanonNameId, b: CanonNameId) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    let mut sa = Vec::new();
    let mut sb = Vec::new();
    encode_canon_name(arena, a, &mut sa);
    encode_canon_name(arena, b, &mut sb);
    sa.cmp(&sb)
}

fn encode_norm_level(lvl: &NormLevel, out: &mut Vec<u8>) {
    match lvl {
        NormLevel::Zero => out.extend_from_slice(b"L0"),
        NormLevel::Succ(inner) => {
            out.extend_from_slice(b"LS");
            encode_norm_level(inner, out);
        }
        NormLevel::Param(idx) => {
            out.extend_from_slice(b"LP");
            push_u64(out, u64::from(*idx));
        }
        NormLevel::Max(l, r) => {
            out.extend_from_slice(b"LM");
            encode_norm_level(l, out);
            encode_norm_level(r, out);
        }
        NormLevel::IMax(l, r) => {
            out.extend_from_slice(b"LI");
            encode_norm_level(l, out);
            encode_norm_level(r, out);
        }
    }
}

fn hash_expr_and_collect_deps(
    arena: &CanonicalArena,
    root_expr: CanonExprId,
    level_params: &[CanonNameId],
    internal_block: &BTreeSet<CanonNameId>,
    phase: &str,
) -> Result<([u8; 32], BTreeSet<CanonNameId>), Failure> {
    let mut ext_deps = BTreeSet::new();
    let mut ememo: HashMap<CanonExprId, [u8; 32]> = HashMap::new();
    let mut stack = vec![(root_expr, false)];

    let mut add_dep = |cid: CanonNameId| {
        if !internal_block.contains(&cid) {
            ext_deps.insert(cid);
        }
    };

    while let Some((eid, done)) = stack.pop() {
        if ememo.contains_key(&eid) {
            continue;
        }
        let expr = &arena.exprs[eid.0 as usize];
        if !done {
            stack.push((eid, true));
            match expr {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, false));
                    stack.push((*a, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, false));
                    stack.push((*body, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, false));
                    stack.push((*value, false));
                    stack.push((*body, false));
                }
                CanonExpr::Proj { struct_expr, .. } => {
                    stack.push((*struct_expr, false));
                }
            }
        } else {
            let mut h = Sha256::new();
            let mut tmp = Vec::new();
            match expr {
                CanonExpr::BVar(i) => {
                    h.update(b"E:BV");
                    h.update(i.to_be_bytes());
                }
                CanonExpr::Sort(u) => {
                    let nl = normalize_level(arena, *u, level_params, phase)?;
                    encode_norm_level(&nl, &mut tmp);
                    h.update(b"E:SO");
                    h.update((tmp.len() as u64).to_be_bytes());
                    h.update(&tmp);
                }
                CanonExpr::Const(c, us) => {
                    add_dep(*c);
                    encode_canon_name(arena, *c, &mut tmp);
                    push_u64(&mut tmp, us.len() as u64);
                    for &u in us {
                        let nl = normalize_level(arena, u, level_params, phase)?;
                        let mut lb = Vec::new();
                        encode_norm_level(&nl, &mut lb);
                        push_bytes(&mut tmp, &lb);
                    }
                    h.update(b"E:CO");
                    h.update(&tmp);
                }
                CanonExpr::App(f, a) => {
                    h.update(b"E:AP");
                    h.update(ememo[f]);
                    h.update(ememo[a]);
                }
                CanonExpr::Lam { ty, body } => {
                    h.update(b"E:LA");
                    h.update(ememo[ty]);
                    h.update(ememo[body]);
                }
                CanonExpr::ForallE { ty, body } => {
                    h.update(b"E:FA");
                    h.update(ememo[ty]);
                    h.update(ememo[body]);
                }
                CanonExpr::LetE { ty, value, body } => {
                    h.update(b"E:LE");
                    h.update(ememo[ty]);
                    h.update(ememo[value]);
                    h.update(ememo[body]);
                }
                CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr,
                } => {
                    add_dep(*type_name);
                    encode_canon_name(arena, *type_name, &mut tmp);
                    h.update(b"E:PR");
                    h.update(&tmp);
                    h.update(idx.to_be_bytes());
                    h.update(ememo[struct_expr]);
                }
                CanonExpr::NatLit(digits) => {
                    h.update(b"E:NA");
                    h.update((digits.len() as u64).to_be_bytes());
                    h.update(digits.as_bytes());
                }
                CanonExpr::StrLit(s) => {
                    h.update(b"E:ST");
                    h.update((s.len() as u64).to_be_bytes());
                    h.update(s.as_bytes());
                }
            }
            let digest: [u8; 32] = h.finalize().into();
            ememo.insert(eid, digest);
        }
    }
    Ok((ememo[&root_expr], ext_deps))
}

/// Compute the transitive statement-cone digest (`TheoremSignatureCone`, proof-
/// body invariant) for `root` inside `env`.
pub fn compute_cone_digest(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    root: CanonNameId,
    phase: &str,
) -> Result<String, Failure> {
    let mut memo = HashMap::new();
    let mut visiting_decls = BTreeSet::new();
    let mut visiting_blocks = BTreeSet::new();
    let raw = compute_digest_rec(
        arena,
        env,
        root,
        Some(root),
        DigestMode::TheoremSignatureCone,
        &mut memo,
        &mut visiting_decls,
        &mut visiting_blocks,
        phase,
    )?;
    Ok(hex_encode_32(&raw))
}

/// Compute the full declaration digest (`FullDeclaration`, including `Thm`
/// proof bodies) for `root` inside `env`.
pub fn compute_decl_digest(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    root: CanonNameId,
    phase: &str,
) -> Result<String, Failure> {
    let mut memo = HashMap::new();
    let mut visiting_decls = BTreeSet::new();
    let mut visiting_blocks = BTreeSet::new();
    let raw = compute_digest_rec(
        arena,
        env,
        root,
        None,
        DigestMode::FullDeclaration,
        &mut memo,
        &mut visiting_decls,
        &mut visiting_blocks,
        phase,
    )?;
    Ok(hex_encode_32(&raw))
}

fn hex_encode_32(bytes: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for &b in bytes {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0x0f) as usize] as char);
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn compute_digest_rec(
    arena: &CanonicalArena,
    env: &ExportedEnv,
    nm: CanonNameId,
    signature_root: Option<CanonNameId>,
    mode: DigestMode,
    memo: &mut HashMap<(CanonNameId, u8), [u8; 32]>,
    visiting_decls: &mut BTreeSet<CanonNameId>,
    visiting_blocks: &mut BTreeSet<usize>,
    phase: &str,
) -> Result<[u8; 32], Failure> {
    let is_sig_root = signature_root == Some(nm);
    let mode_tag = match mode {
        DigestMode::TheoremSignatureCone if is_sig_root => 2u8,
        DigestMode::TheoremSignatureCone => 0u8,
        DigestMode::FullDeclaration => 1u8,
    };
    if let Some(&cached) = memo.get(&(nm, mode_tag)) {
        return Ok(cached);
    }
    let Some(ci) = env.constants.get(&nm) else {
        return Err(Failure::policy(
            phase,
            format!("missing constant `{}` in Merkle cone", arena.name_str(nm)),
        ));
    };

    if let Some(&block_idx) = env.inductive_blocks.get(&nm) {
        if !visiting_blocks.insert(block_idx) {
            return Err(Failure::policy(
                phase,
                format!(
                    "cyclic dependency through inductive block `{}`",
                    arena.name_str(nm)
                ),
            ));
        }
        let blk: &CanonInductiveBlock = &env.blocks[block_idx];
        let members: BTreeSet<CanonNameId> = blk
            .types
            .iter()
            .chain(blk.ctors.iter())
            .chain(blk.recs.iter())
            .copied()
            .collect();
        let mut ext_deps = BTreeSet::new();
        let mut buf = Vec::with_capacity(512);
        buf.extend_from_slice(b"D:IND_BLK");

        push_u64(&mut buf, blk.types.len() as u64);
        for &tid in &blk.types {
            let Some(CanonConstInfo::Induct {
                level_params,
                ty,
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_unsafe,
                is_reflexive,
                ..
            }) = env.constants.get(&tid)
            else {
                return Err(Failure::policy(phase, "corrupt inductive type entry"));
            };
            let (th, d) = hash_expr_and_collect_deps(arena, *ty, level_params, &members, phase)?;
            ext_deps.extend(d);
            encode_canon_name(arena, tid, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            push_u64(&mut buf, *num_params);
            push_u64(&mut buf, *num_indices);
            push_u64(&mut buf, *num_nested);
            buf.extend_from_slice(&[
                u8::from(*is_rec),
                u8::from(*is_unsafe),
                u8::from(*is_reflexive),
            ]);
            push_u64(&mut buf, all.len() as u64);
            for &a in all {
                encode_canon_name(arena, a, &mut buf);
            }
            push_u64(&mut buf, ctors.len() as u64);
            for &c in ctors {
                encode_canon_name(arena, c, &mut buf);
            }
            buf.extend_from_slice(&th);
        }

        push_u64(&mut buf, blk.ctors.len() as u64);
        for &cid in &blk.ctors {
            let Some(CanonConstInfo::Ctor {
                level_params,
                ty,
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
                ..
            }) = env.constants.get(&cid)
            else {
                return Err(Failure::policy(phase, "corrupt constructor entry"));
            };
            let (ch, d) = hash_expr_and_collect_deps(arena, *ty, level_params, &members, phase)?;
            ext_deps.extend(d);
            encode_canon_name(arena, cid, &mut buf);
            encode_canon_name(arena, *induct, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            push_u64(&mut buf, *cidx);
            push_u64(&mut buf, *num_params);
            push_u64(&mut buf, *num_fields);
            buf.push(u8::from(*is_unsafe));
            buf.extend_from_slice(&ch);
        }

        let mut sorted_recs = blk.recs.clone();
        sorted_recs.sort_by(|a, b| cmp_canon_name(arena, *a, *b));
        push_u64(&mut buf, sorted_recs.len() as u64);
        for rid in sorted_recs {
            let Some(CanonConstInfo::Rec {
                level_params,
                ty,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
                ..
            }) = env.constants.get(&rid)
            else {
                return Err(Failure::policy(phase, "corrupt recursor entry"));
            };
            let (rh, d) = hash_expr_and_collect_deps(arena, *ty, level_params, &members, phase)?;
            ext_deps.extend(d);
            encode_canon_name(arena, rid, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            push_u64(&mut buf, *num_params);
            push_u64(&mut buf, *num_indices);
            push_u64(&mut buf, *num_motives);
            push_u64(&mut buf, *num_minors);
            buf.extend_from_slice(&[u8::from(*k), u8::from(*is_unsafe)]);
            push_u64(&mut buf, all.len() as u64);
            for &a in all {
                encode_canon_name(arena, a, &mut buf);
            }
            buf.extend_from_slice(&rh);
            // Preserve `rules` strictly in constructor-index (`cidx`) order!
            push_u64(&mut buf, rules.len() as u64);
            for rl in rules {
                let (rlh, rd) =
                    hash_expr_and_collect_deps(arena, rl.rhs, level_params, &members, phase)?;
                ext_deps.extend(rd);
                encode_canon_name(arena, rl.ctor, &mut buf);
                push_u64(&mut buf, rl.nfields);
                buf.extend_from_slice(&rlh);
            }
        }
        visiting_blocks.remove(&block_idx);

        let mut sorted_ext: Vec<CanonNameId> = ext_deps.into_iter().collect();
        sorted_ext.sort_by(|a, b| cmp_canon_name(arena, *a, *b));
        push_u64(&mut buf, sorted_ext.len() as u64);
        for dep in sorted_ext {
            let dh = compute_digest_rec(
                arena,
                env,
                dep,
                None,
                mode,
                memo,
                visiting_decls,
                visiting_blocks,
                phase,
            )?;
            encode_canon_name(arena, dep, &mut buf);
            buf.extend_from_slice(&dh);
        }
        let block_digest: [u8; 32] = Sha256::digest(&buf).into();
        for &member in &members {
            let mut mbuf = Vec::with_capacity(96);
            mbuf.extend_from_slice(b"D:IND_MEM");
            encode_canon_name(arena, member, &mut mbuf);
            mbuf.extend_from_slice(&block_digest);
            let mh: [u8; 32] = Sha256::digest(&mbuf).into();
            memo.insert((member, mode_tag), mh);
        }
        return Ok(memo[&(nm, mode_tag)]);
    }

    if !visiting_decls.insert(nm) {
        return Err(Failure::policy(
            phase,
            format!(
                "cyclic dependency on non-inductive constant `{}`",
                arena.name_str(nm)
            ),
        ));
    }

    let empty_set = BTreeSet::new();
    let mut buf = Vec::with_capacity(256);
    let mut ext_deps = BTreeSet::new();

    match ci {
        CanonConstInfo::Axiom {
            level_params,
            ty,
            is_unsafe,
            ..
        } => {
            let (th, d) = hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
            ext_deps.extend(d);
            if is_sig_root && mode == DigestMode::TheoremSignatureCone && !*is_unsafe {
                buf.extend_from_slice(b"D:THM_CONE");
                encode_canon_name(arena, nm, &mut buf);
                push_u64(&mut buf, level_params.len() as u64);
                buf.extend_from_slice(&th);
            } else {
                buf.extend_from_slice(b"D:AX");
                encode_canon_name(arena, nm, &mut buf);
                push_u64(&mut buf, level_params.len() as u64);
                buf.push(u8::from(*is_unsafe));
                buf.extend_from_slice(&th);
            }
        }
        CanonConstInfo::Quot {
            level_params,
            ty,
            kind,
            ..
        } => {
            let (th, d) = hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
            ext_deps.extend(d);
            buf.extend_from_slice(b"D:QU");
            encode_canon_name(arena, nm, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            let ktag: u8 = match kind {
                QuotKind::Type => 0,
                QuotKind::Ctor => 1,
                QuotKind::Lift => 2,
                QuotKind::Ind => 3,
            };
            buf.push(ktag);
            buf.extend_from_slice(&th);
        }
        CanonConstInfo::Defn {
            level_params,
            ty,
            value,
            hints,
            safety,
            ..
        } => {
            let (th, d1) = hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
            let (vh, d2) =
                hash_expr_and_collect_deps(arena, *value, level_params, &empty_set, phase)?;
            ext_deps.extend(d1);
            ext_deps.extend(d2);
            buf.extend_from_slice(b"D:DF");
            encode_canon_name(arena, nm, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            match hints {
                ReducibilityHints::Opaque => buf.extend_from_slice(b"H:OP"),
                ReducibilityHints::Abbrev => buf.extend_from_slice(b"H:AB"),
                ReducibilityHints::Regular(h) => {
                    buf.extend_from_slice(b"H:RG");
                    buf.extend_from_slice(&h.to_be_bytes());
                }
            }
            let stag: u8 = match safety {
                DefinitionSafety::Safe => 0,
                DefinitionSafety::Unsafe => 1,
                DefinitionSafety::Partial => 2,
            };
            buf.push(stag);
            buf.extend_from_slice(&th);
            buf.extend_from_slice(&vh);
        }
        CanonConstInfo::Opaque {
            level_params,
            ty,
            value,
            is_unsafe,
            ..
        } => {
            let (th, d1) = hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
            let (vh, d2) =
                hash_expr_and_collect_deps(arena, *value, level_params, &empty_set, phase)?;
            ext_deps.extend(d1);
            ext_deps.extend(d2);
            buf.extend_from_slice(b"D:OP");
            encode_canon_name(arena, nm, &mut buf);
            push_u64(&mut buf, level_params.len() as u64);
            buf.push(u8::from(*is_unsafe));
            buf.extend_from_slice(&th);
            buf.extend_from_slice(&vh);
        }
        CanonConstInfo::Thm {
            level_params,
            ty,
            value,
            ..
        } => match mode {
            DigestMode::TheoremSignatureCone => {
                let (th, d1) =
                    hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
                ext_deps.extend(d1);
                buf.extend_from_slice(b"D:THM_CONE");
                encode_canon_name(arena, nm, &mut buf);
                push_u64(&mut buf, level_params.len() as u64);
                buf.extend_from_slice(&th);
            }
            DigestMode::FullDeclaration => {
                let (th, d1) =
                    hash_expr_and_collect_deps(arena, *ty, level_params, &empty_set, phase)?;
                let (vh, d2) =
                    hash_expr_and_collect_deps(arena, *value, level_params, &empty_set, phase)?;
                ext_deps.extend(d1);
                ext_deps.extend(d2);
                buf.extend_from_slice(b"D:THM_FULL");
                encode_canon_name(arena, nm, &mut buf);
                push_u64(&mut buf, level_params.len() as u64);
                buf.extend_from_slice(&th);
                buf.extend_from_slice(&vh);
            }
        },
        CanonConstInfo::Induct { .. }
        | CanonConstInfo::Ctor { .. }
        | CanonConstInfo::Rec { .. } => {
            return Err(Failure::policy(
                phase,
                format!(
                    "inductive member `{}` missing block registration",
                    arena.name_str(nm)
                ),
            ));
        }
    }

    visiting_decls.remove(&nm);
    let mut sorted_ext: Vec<CanonNameId> = ext_deps.into_iter().collect();
    sorted_ext.sort_by(|a, b| cmp_canon_name(arena, *a, *b));
    push_u64(&mut buf, sorted_ext.len() as u64);
    for dep in sorted_ext {
        let dh = compute_digest_rec(
            arena,
            env,
            dep,
            None,
            mode,
            memo,
            visiting_decls,
            visiting_blocks,
            phase,
        )?;
        encode_canon_name(arena, dep, &mut buf);
        buf.extend_from_slice(&dh);
    }
    let out: [u8; 32] = Sha256::digest(&buf).into();
    memo.insert((nm, mode_tag), out);
    Ok(out)
}

// ---------------------------------------------------------------------------
// 3. Lossless canonical NDJSON 3.1.0 serializer (`emit_ndjson`)
// ---------------------------------------------------------------------------

/// Garbage-collect `env` from `roots` (backfilling missing literal-desugaring
/// primitives from `init_fallback` when available) and serialize a valid,
/// topologically ordered `NDJSON 3.1.0` stream.
pub fn emit_ndjson(
    arena: &mut CanonicalArena,
    env: &ExportedEnv,
    init_fallback: Option<&ExportedEnv>,
    roots: &[CanonNameId],
    phase: &str,
) -> Result<(String, ExportedEnv), Failure> {
    let mut working = env.clone();

    // Check whether any reachable expression uses `NatLit` or `StrLit` and
    // backfill missing literal primitives from `init_fallback` if needed.
    let initial_bfs = bfs_cone(arena, &working, roots);
    let mut needs_nat = false;
    let mut needs_str = false;
    for &cid in &initial_bfs.visited {
        if let Some(ci) = working.constants.get(&cid) {
            scan_const_for_literals(arena, ci, &mut needs_nat, &mut needs_str);
        }
    }
    if let Some(init_env) = init_fallback {
        let mut lit_roots = Vec::new();
        if needs_nat {
            lit_roots.extend([arena.nat_name, arena.nat_zero_name, arena.nat_succ_name]);
        }
        if needs_str {
            lit_roots.extend([
                arena.string_name,
                arena.string_of_list_name,
                arena.char_name,
                arena.char_of_nat_name,
                arena.list_name,
                arena.list_nil_name,
                arena.list_cons_name,
            ]);
        }
        if !lit_roots.is_empty() {
            let lit_bfs = bfs_cone(arena, init_env, &lit_roots);
            for &cid in &init_env.const_order {
                if !lit_bfs.visited.contains(&cid) || working.constants.contains_key(&cid) {
                    continue;
                }
                if let Some(&bidx) = init_env.inductive_blocks.get(&cid) {
                    let blk = init_env.blocks[bidx].clone();
                    let new_bidx = working.blocks.len();
                    for &m in blk
                        .types
                        .iter()
                        .chain(blk.ctors.iter())
                        .chain(blk.recs.iter())
                    {
                        if let Some(mci) = init_env.constants.get(&m) {
                            working.constants.insert(m, mci.clone());
                            working.const_order.push(m);
                            working.inductive_blocks.insert(m, new_bidx);
                        }
                    }
                    working.blocks.push(blk);
                } else if let Some(ci) = init_env.constants.get(&cid) {
                    working.constants.insert(cid, ci.clone());
                    working.const_order.push(cid);
                }
            }
        }
    }

    let gc_bfs = bfs_cone(arena, &working, roots);
    for &r in roots {
        if !gc_bfs.visited.contains(&r) {
            return Err(Failure::policy(
                phase,
                format!(
                    "root declaration `{}` missing during NDJSON emission",
                    arena.name_str(r)
                ),
            ));
        }
    }

    // Order reachable declarations topologically, grouping each
    // `CanonInductiveBlock` into one atomic unit.
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum DeclUnit {
        Single(CanonNameId),
        Block(usize),
    }

    let unit_of = |cid: CanonNameId| -> DeclUnit {
        if let Some(&bidx) = working.inductive_blocks.get(&cid) {
            DeclUnit::Block(bidx)
        } else {
            DeclUnit::Single(cid)
        }
    };

    let mut reachable_units = Vec::new();
    let mut seen_units = std::collections::HashSet::new();
    for &cid in &working.const_order {
        if !gc_bfs.visited.contains(&cid) {
            continue;
        }
        let u = unit_of(cid);
        if seen_units.insert(u) {
            reachable_units.push(u);
        }
    }

    let mut state: HashMap<DeclUnit, u8> = HashMap::new();
    let mut topo_units: Vec<DeclUnit> = Vec::with_capacity(reachable_units.len());

    fn visit_unit(
        u: DeclUnit,
        arena: &CanonicalArena,
        working: &ExportedEnv,
        reachable: &BTreeSet<CanonNameId>,
        state: &mut HashMap<DeclUnit, u8>,
        topo_units: &mut Vec<DeclUnit>,
        phase: &str,
    ) -> Result<(), Failure> {
        match state.get(&u).copied() {
            Some(2) => return Ok(()),
            Some(1) => {
                return Err(Failure::policy(
                    phase,
                    "cycle detected during NDJSON serialization",
                ));
            }
            _ => {}
        }
        state.insert(u, 1);
        let members: Vec<CanonNameId> = match u {
            DeclUnit::Single(cid) => vec![cid],
            DeclUnit::Block(bidx) => {
                let blk = &working.blocks[bidx];
                blk.types
                    .iter()
                    .chain(blk.ctors.iter())
                    .chain(blk.recs.iter())
                    .copied()
                    .collect()
            }
        };
        let member_set: BTreeSet<CanonNameId> = members.iter().copied().collect();
        let mut deps = Vec::new();
        for m in members {
            if let Some(ci) = working.constants.get(&m) {
                for dep in arena.collect_const_deps(ci, false) {
                    if reachable.contains(&dep) && !member_set.contains(&dep) {
                        let du = if let Some(&bidx) = working.inductive_blocks.get(&dep) {
                            DeclUnit::Block(bidx)
                        } else {
                            DeclUnit::Single(dep)
                        };
                        deps.push(du);
                    }
                }
            }
        }
        for du in deps {
            visit_unit(du, arena, working, reachable, state, topo_units, phase)?;
        }
        state.insert(u, 2);
        topo_units.push(u);
        Ok(())
    }

    for &u in &reachable_units {
        visit_unit(
            u,
            arena,
            &working,
            &gc_bfs.visited,
            &mut state,
            &mut topo_units,
            phase,
        )?;
    }

    // Build pruned `ExportedEnv` in exact topological order and serialize
    // lines.
    let mut lines: Vec<String> = Vec::with_capacity(topo_units.len() * 8 + 16);
    lines.push(
        serde_json::to_string(&json!({
            "meta": {
                "exporter": {
                    "name": working.meta.exporter_name,
                    "version": working.meta.exporter_version,
                },
                "format": { "version": working.meta.format_version },
                "lean": {
                    "githash": working.meta.lean_githash,
                    "version": working.meta.lean_version,
                },
            }
        }))
        .map_err(|e| Failure::operational(phase, e.to_string()))?,
    );

    let dummy_binder_name = arena.intern_dotted_name("_x");
    let mut ser = NdjsonEmitter {
        arena,
        lines: &mut lines,
        name_out: HashMap::from([(arena.anonymous_name, 0u64)]),
        next_name: 1,
        level_out: HashMap::from([(arena.zero_level, 0u64)]),
        next_level: 1,
        expr_out: HashMap::new(),
        next_expr: 0,
        dummy_binder_name,
        phase,
    };

    let mut out_constants = HashMap::new();
    let mut out_order = Vec::new();
    let mut out_blocks = Vec::new();
    let mut out_ind_map = HashMap::new();

    for u in topo_units {
        match u {
            DeclUnit::Single(cid) => {
                let ci = working.constants[&cid].clone();
                ser.emit_single_decl(&ci)?;
                out_constants.insert(cid, ci);
                out_order.push(cid);
            }
            DeclUnit::Block(bidx) => {
                let blk = working.blocks[bidx].clone();
                ser.emit_inductive_block(&blk, &working)?;
                let nb = out_blocks.len();
                for &m in blk
                    .types
                    .iter()
                    .chain(blk.ctors.iter())
                    .chain(blk.recs.iter())
                {
                    let mci = working.constants[&m].clone();
                    out_constants.insert(m, mci);
                    out_order.push(m);
                    out_ind_map.insert(m, nb);
                }
                out_blocks.push(blk);
            }
        }
        if ser.lines.len() > MAX_NDJSON_LINES {
            return Err(Failure::policy(
                phase,
                format!("serialized NDJSON exceeds maximum line count ({MAX_NDJSON_LINES})"),
            ));
        }
    }

    let mut rendered = lines.join("\n");
    rendered.push('\n');
    if (rendered.len() as u64) > MAX_NDJSON_BYTES {
        return Err(Failure::policy(
            phase,
            format!("serialized NDJSON exceeds maximum byte size ({MAX_NDJSON_BYTES})"),
        ));
    }

    let pruned_env = ExportedEnv {
        meta: working.meta,
        constants: out_constants,
        const_order: out_order,
        blocks: out_blocks,
        inductive_blocks: out_ind_map,
    };
    Ok((rendered, pruned_env))
}

fn scan_const_for_literals(
    arena: &CanonicalArena,
    ci: &CanonConstInfo,
    needs_nat: &mut bool,
    needs_str: &mut bool,
) {
    let mut roots = Vec::new();
    match ci {
        CanonConstInfo::Axiom { ty, .. }
        | CanonConstInfo::Quot { ty, .. }
        | CanonConstInfo::Induct { ty, .. }
        | CanonConstInfo::Ctor { ty, .. } => roots.push(*ty),
        CanonConstInfo::Defn { ty, value, .. }
        | CanonConstInfo::Thm { ty, value, .. }
        | CanonConstInfo::Opaque { ty, value, .. } => {
            roots.push(*ty);
            roots.push(*value);
        }
        CanonConstInfo::Rec { ty, rules, .. } => {
            roots.push(*ty);
            for r in rules {
                roots.push(r.rhs);
            }
        }
    }
    let mut seen = BTreeSet::new();
    while let Some(eid) = roots.pop() {
        if !seen.insert(eid) {
            continue;
        }
        match &arena.exprs[eid.0 as usize] {
            CanonExpr::BVar(_) | CanonExpr::Sort(_) | CanonExpr::Const(_, _) => {}
            CanonExpr::NatLit(_) => *needs_nat = true,
            CanonExpr::StrLit(_) => *needs_str = true,
            CanonExpr::App(f, a) => {
                roots.push(*f);
                roots.push(*a);
            }
            CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                roots.push(*ty);
                roots.push(*body);
            }
            CanonExpr::LetE { ty, value, body } => {
                roots.push(*ty);
                roots.push(*value);
                roots.push(*body);
            }
            CanonExpr::Proj { struct_expr, .. } => roots.push(*struct_expr),
        }
    }
}

struct NdjsonEmitter<'a> {
    arena: &'a CanonicalArena,
    lines: &'a mut Vec<String>,
    name_out: HashMap<CanonNameId, u64>,
    next_name: u64,
    level_out: HashMap<CanonLevelId, u64>,
    next_level: u64,
    expr_out: HashMap<CanonExprId, u64>,
    next_expr: u64,
    dummy_binder_name: CanonNameId,
    phase: &'a str,
}

impl NdjsonEmitter<'_> {
    fn emit_name(&mut self, id: CanonNameId) -> Result<u64, Failure> {
        if let Some(&idx) = self.name_out.get(&id) {
            return Ok(idx);
        }
        let mut chain = Vec::new();
        let mut cur = id;
        while !self.name_out.contains_key(&cur) {
            chain.push(cur);
            match &self.arena.names[cur.0 as usize] {
                CanonName::Anonymous => break,
                CanonName::Str(pre, _) | CanonName::Num(pre, _) => cur = *pre,
            }
        }
        for nid in chain.into_iter().rev() {
            if self.name_out.contains_key(&nid) {
                continue;
            }
            let out_id = self.next_name;
            self.next_name += 1;
            let rec = match &self.arena.names[nid.0 as usize] {
                CanonName::Anonymous => continue,
                CanonName::Str(pre, s) => {
                    let p = self.name_out[pre];
                    json!({ "in": out_id, "str": { "pre": p, "str": s } })
                }
                CanonName::Num(pre, i) => {
                    let p = self.name_out[pre];
                    json!({ "in": out_id, "num": { "pre": p, "i": i } })
                }
            };
            self.lines.push(
                serde_json::to_string(&rec)
                    .map_err(|e| Failure::operational(self.phase, e.to_string()))?,
            );
            self.name_out.insert(nid, out_id);
        }
        Ok(self.name_out[&id])
    }

    fn emit_name_list(&mut self, ids: &[CanonNameId]) -> Result<Vec<u64>, Failure> {
        let mut out = Vec::with_capacity(ids.len());
        for &id in ids {
            out.push(self.emit_name(id)?);
        }
        Ok(out)
    }

    fn emit_level(&mut self, id: CanonLevelId) -> Result<u64, Failure> {
        if let Some(&idx) = self.level_out.get(&id) {
            return Ok(idx);
        }
        let mut stack = vec![(id, false)];
        while let Some((lid, done)) = stack.pop() {
            if self.level_out.contains_key(&lid) {
                continue;
            }
            if !done {
                stack.push((lid, true));
                match &self.arena.levels[lid.0 as usize] {
                    CanonLevel::Zero | CanonLevel::Param(_) => {}
                    CanonLevel::Succ(x) => stack.push((*x, false)),
                    CanonLevel::Max(a, b) | CanonLevel::IMax(a, b) => {
                        stack.push((*a, false));
                        stack.push((*b, false));
                    }
                }
            } else {
                let rec = match &self.arena.levels[lid.0 as usize] {
                    CanonLevel::Zero => continue,
                    CanonLevel::Succ(x) => {
                        let xi = self.level_out[x];
                        let out_id = self.next_level;
                        self.next_level += 1;
                        self.level_out.insert(lid, out_id);
                        json!({ "il": out_id, "succ": xi })
                    }
                    CanonLevel::Max(a, b) => {
                        let ai = self.level_out[a];
                        let bi = self.level_out[b];
                        let out_id = self.next_level;
                        self.next_level += 1;
                        self.level_out.insert(lid, out_id);
                        json!({ "il": out_id, "max": [ai, bi] })
                    }
                    CanonLevel::IMax(a, b) => {
                        let ai = self.level_out[a];
                        let bi = self.level_out[b];
                        let out_id = self.next_level;
                        self.next_level += 1;
                        self.level_out.insert(lid, out_id);
                        json!({ "il": out_id, "imax": [ai, bi] })
                    }
                    CanonLevel::Param(p) => {
                        let pi = self.emit_name(*p)?;
                        let out_id = self.next_level;
                        self.next_level += 1;
                        self.level_out.insert(lid, out_id);
                        json!({ "il": out_id, "param": pi })
                    }
                };
                self.lines.push(
                    serde_json::to_string(&rec)
                        .map_err(|e| Failure::operational(self.phase, e.to_string()))?,
                );
            }
        }
        Ok(self.level_out[&id])
    }

    fn emit_expr(&mut self, root: CanonExprId) -> Result<u64, Failure> {
        if let Some(&idx) = self.expr_out.get(&root) {
            return Ok(idx);
        }
        let mut stack = vec![(root, false)];
        while let Some((eid, done)) = stack.pop() {
            if self.expr_out.contains_key(&eid) {
                continue;
            }
            if !done {
                stack.push((eid, true));
                match &self.arena.exprs[eid.0 as usize] {
                    CanonExpr::BVar(_)
                    | CanonExpr::Sort(_)
                    | CanonExpr::Const(_, _)
                    | CanonExpr::NatLit(_)
                    | CanonExpr::StrLit(_) => {}
                    CanonExpr::App(f, a) => {
                        stack.push((*a, false));
                        stack.push((*f, false));
                    }
                    CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                        stack.push((*body, false));
                        stack.push((*ty, false));
                    }
                    CanonExpr::LetE { ty, value, body } => {
                        stack.push((*body, false));
                        stack.push((*value, false));
                        stack.push((*ty, false));
                    }
                    CanonExpr::Proj { struct_expr, .. } => stack.push((*struct_expr, false)),
                }
            } else {
                let rec = match &self.arena.exprs[eid.0 as usize] {
                    CanonExpr::BVar(b) => {
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "bvar": b })
                    }
                    CanonExpr::Sort(u) => {
                        let ui = self.emit_level(*u)?;
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "sort": ui })
                    }
                    CanonExpr::Const(c, us) => {
                        let ci = self.emit_name(*c)?;
                        let mut uis = Vec::with_capacity(us.len());
                        for &u in us {
                            uis.push(self.emit_level(u)?);
                        }
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "const": { "name": ci, "us": uis } })
                    }
                    CanonExpr::App(f, a) => {
                        let fi = self.expr_out[f];
                        let ai = self.expr_out[a];
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "app": { "fn": fi, "arg": ai } })
                    }
                    CanonExpr::Lam { ty, body } => {
                        let bn = self.emit_name(self.dummy_binder_name)?;
                        let ti = self.expr_out[ty];
                        let bi = self.expr_out[body];
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({
                            "ie": out_id,
                            "lam": { "name": bn, "type": ti, "body": bi, "binderInfo": "default" }
                        })
                    }
                    CanonExpr::ForallE { ty, body } => {
                        let bn = self.emit_name(self.dummy_binder_name)?;
                        let ti = self.expr_out[ty];
                        let bi = self.expr_out[body];
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({
                            "ie": out_id,
                            "forallE": {
                                "name": bn,
                                "type": ti,
                                "body": bi,
                                "binderInfo": "default"
                            }
                        })
                    }
                    CanonExpr::LetE { ty, value, body } => {
                        let bn = self.emit_name(self.dummy_binder_name)?;
                        let ti = self.expr_out[ty];
                        let vi = self.expr_out[value];
                        let bi = self.expr_out[body];
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({
                            "ie": out_id,
                            "letE": {
                                "name": bn,
                                "type": ti,
                                "value": vi,
                                "body": bi,
                                "nondep": false
                            }
                        })
                    }
                    CanonExpr::Proj {
                        type_name,
                        idx,
                        struct_expr,
                    } => {
                        let tni = self.emit_name(*type_name)?;
                        let si = self.expr_out[struct_expr];
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({
                            "ie": out_id,
                            "proj": { "typeName": tni, "idx": idx, "struct": si }
                        })
                    }
                    CanonExpr::NatLit(digits) => {
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "natVal": digits })
                    }
                    CanonExpr::StrLit(s) => {
                        let out_id = self.next_expr;
                        self.next_expr += 1;
                        self.expr_out.insert(eid, out_id);
                        json!({ "ie": out_id, "strVal": s })
                    }
                };
                self.lines.push(
                    serde_json::to_string(&rec)
                        .map_err(|e| Failure::operational(self.phase, e.to_string()))?,
                );
            }
        }
        Ok(self.expr_out[&root])
    }

    fn emit_single_decl(&mut self, ci: &CanonConstInfo) -> Result<(), Failure> {
        let rec = match ci {
            CanonConstInfo::Axiom {
                name,
                level_params,
                ty,
                is_unsafe,
            } => {
                let ni = self.emit_name(*name)?;
                let lps = self.emit_name_list(level_params)?;
                let ti = self.emit_expr(*ty)?;
                json!({
                    "axiom": {
                        "name": ni,
                        "levelParams": lps,
                        "type": ti,
                        "isUnsafe": is_unsafe,
                    }
                })
            }
            CanonConstInfo::Defn {
                name,
                level_params,
                ty,
                value,
                hints,
                safety,
                all,
            } => {
                let ni = self.emit_name(*name)?;
                let lps = self.emit_name_list(level_params)?;
                let ti = self.emit_expr(*ty)?;
                let vi = self.emit_expr(*value)?;
                let alls = self.emit_name_list(all)?;
                let hints_val = match hints {
                    ReducibilityHints::Opaque => json!("opaque"),
                    ReducibilityHints::Abbrev => json!("abbrev"),
                    ReducibilityHints::Regular(h) => json!({ "regular": h }),
                };
                let safety_str = match safety {
                    DefinitionSafety::Safe => "safe",
                    DefinitionSafety::Unsafe => "unsafe",
                    DefinitionSafety::Partial => "partial",
                };
                json!({
                    "def": {
                        "name": ni,
                        "levelParams": lps,
                        "type": ti,
                        "value": vi,
                        "hints": hints_val,
                        "safety": safety_str,
                        "all": alls,
                    }
                })
            }
            CanonConstInfo::Thm {
                name,
                level_params,
                ty,
                value,
                all,
            } => {
                let ni = self.emit_name(*name)?;
                let lps = self.emit_name_list(level_params)?;
                let ti = self.emit_expr(*ty)?;
                let vi = self.emit_expr(*value)?;
                let alls = self.emit_name_list(all)?;
                json!({
                    "thm": {
                        "name": ni,
                        "levelParams": lps,
                        "type": ti,
                        "value": vi,
                        "all": alls,
                    }
                })
            }
            CanonConstInfo::Opaque {
                name,
                level_params,
                ty,
                value,
                is_unsafe,
                all,
            } => {
                let ni = self.emit_name(*name)?;
                let lps = self.emit_name_list(level_params)?;
                let ti = self.emit_expr(*ty)?;
                let vi = self.emit_expr(*value)?;
                let alls = self.emit_name_list(all)?;
                json!({
                    "opaque": {
                        "name": ni,
                        "levelParams": lps,
                        "type": ti,
                        "value": vi,
                        "isUnsafe": is_unsafe,
                        "all": alls,
                    }
                })
            }
            CanonConstInfo::Quot {
                name,
                level_params,
                ty,
                kind,
            } => {
                let ni = self.emit_name(*name)?;
                let lps = self.emit_name_list(level_params)?;
                let ti = self.emit_expr(*ty)?;
                let kind_str = match kind {
                    QuotKind::Type => "type",
                    QuotKind::Ctor => "ctor",
                    QuotKind::Lift => "lift",
                    QuotKind::Ind => "ind",
                };
                json!({
                    "quot": {
                        "name": ni,
                        "levelParams": lps,
                        "type": ti,
                        "kind": kind_str,
                    }
                })
            }
            CanonConstInfo::Induct { .. }
            | CanonConstInfo::Ctor { .. }
            | CanonConstInfo::Rec { .. } => {
                return Err(Failure::operational(
                    self.phase,
                    "inductive member routed to emit_single_decl",
                ));
            }
        };
        self.lines.push(
            serde_json::to_string(&rec)
                .map_err(|e| Failure::operational(self.phase, e.to_string()))?,
        );
        Ok(())
    }

    fn emit_inductive_block(
        &mut self,
        blk: &CanonInductiveBlock,
        env: &ExportedEnv,
    ) -> Result<(), Failure> {
        let mut types_json = Vec::with_capacity(blk.types.len());
        for &tid in &blk.types {
            let Some(CanonConstInfo::Induct {
                name,
                level_params,
                ty,
                num_params,
                num_indices,
                all,
                ctors,
                num_nested,
                is_rec,
                is_unsafe,
                is_reflexive,
                ..
            }) = env.constants.get(&tid)
            else {
                return Err(Failure::policy(
                    self.phase,
                    "missing inductive type in block",
                ));
            };
            let ni = self.emit_name(*name)?;
            let lps = self.emit_name_list(level_params)?;
            let ti = self.emit_expr(*ty)?;
            let alls = self.emit_name_list(all)?;
            let cts = self.emit_name_list(ctors)?;
            types_json.push(json!({
                "name": ni,
                "levelParams": lps,
                "type": ti,
                "numParams": num_params,
                "numIndices": num_indices,
                "all": alls,
                "ctors": cts,
                "numNested": num_nested,
                "isRec": is_rec,
                "isUnsafe": is_unsafe,
                "isReflexive": is_reflexive,
            }));
        }

        let mut ctors_json = Vec::with_capacity(blk.ctors.len());
        for &cid in &blk.ctors {
            let Some(CanonConstInfo::Ctor {
                name,
                level_params,
                ty,
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            }) = env.constants.get(&cid)
            else {
                return Err(Failure::policy(self.phase, "missing constructor in block"));
            };
            let ni = self.emit_name(*name)?;
            let lps = self.emit_name_list(level_params)?;
            let ti = self.emit_expr(*ty)?;
            let ii = self.emit_name(*induct)?;
            ctors_json.push(json!({
                "name": ni,
                "levelParams": lps,
                "type": ti,
                "induct": ii,
                "cidx": cidx,
                "numParams": num_params,
                "numFields": num_fields,
                "isUnsafe": is_unsafe,
            }));
        }

        let mut recs_json = Vec::with_capacity(blk.recs.len());
        for &rid in &blk.recs {
            let Some(CanonConstInfo::Rec {
                name,
                level_params,
                ty,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
            }) = env.constants.get(&rid)
            else {
                return Err(Failure::policy(self.phase, "missing recursor in block"));
            };
            let ni = self.emit_name(*name)?;
            let lps = self.emit_name_list(level_params)?;
            let ti = self.emit_expr(*ty)?;
            let alls = self.emit_name_list(all)?;
            let mut rules_json = Vec::with_capacity(rules.len());
            for RecursorRule { ctor, nfields, rhs } in rules {
                let ci = self.emit_name(*ctor)?;
                let ri = self.emit_expr(*rhs)?;
                rules_json.push(json!({
                    "ctor": ci,
                    "nfields": nfields,
                    "rhs": ri,
                }));
            }
            recs_json.push(json!({
                "name": ni,
                "levelParams": lps,
                "type": ti,
                "all": alls,
                "numParams": num_params,
                "numIndices": num_indices,
                "numMotives": num_motives,
                "numMinors": num_minors,
                "rules": rules_json,
                "k": k,
                "isUnsafe": is_unsafe,
            }));
        }

        let rec = json!({
            "inductive": {
                "types": types_json,
                "ctors": ctors_json,
                "recs": recs_json,
            }
        });
        self.lines.push(
            serde_json::to_string(&rec)
                .map_err(|e| Failure::operational(self.phase, e.to_string()))?,
        );
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// 4. `PromotedTheoremAllowlist`, `AxiomPromotionReport`, & Option-B M3 Engine
// ---------------------------------------------------------------------------

/// One pre-verified theorem entry eligible for M3 lambda-lifted discharge.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PromotedTheoremEntry {
    pub name: String,
    pub module: String,
    pub num_level_params: usize,
    pub cone_merkle_sha256: String,
    pub used_foundation_axioms: Vec<String>,
    pub model_closure: Vec<ClosureEntry>,
}

/// Merkle-locked allowlist of pre-verified theorems eligible for M3 promotion.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct PromotedTheoremAllowlist {
    pub schema_version: u32,
    pub theory_manifest_sha256: String,
    pub entries: BTreeMap<String, PromotedTheoremEntry>,
}

impl PromotedTheoremAllowlist {
    /// Construct an empty allowlist (disabling promotion, e.g. under
    /// `--full-theory-replay`).
    pub fn empty(theory_manifest_sha256: String) -> Self {
        Self {
            schema_version: 1,
            theory_manifest_sha256,
            entries: BTreeMap::new(),
        }
    }

    /// Deterministic SHA-256 hex digest over the serialized allowlist JSON.
    pub fn allowlist_sha256(&self) -> Result<String, Failure> {
        let bytes = serde_json::to_vec(self)
            .map_err(|e| Failure::operational("m3-allowlist", e.to_string()))?;
        Ok(sha256_bytes(&bytes))
    }
}

/// Receipt record for one outer M3 hypothesis binder prepended to
/// `Proof.verify`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct LiftedHypothesisRecord {
    pub name: String,
    pub universe_levels: Vec<String>,
    pub cone_merkle_sha256: String,
    pub inherited_axioms: Vec<String>,
}

/// Strict typed `axiomPromotion` block attached to
/// [`crate::NdjsonAuditVerdict`].
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct AxiomPromotionReport {
    pub mode: String,
    pub allowlist_sha256: String,
    pub pre_m3_declarations: usize,
    pub post_m3_declarations: usize,
    pub m3_ndjson_sha256: String,
    pub lifted_hypotheses: Vec<LiftedHypothesisRecord>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unliftable_kept: Vec<String>,
}

/// Validate [`AxiomPromotionReport`] schema and axiom-conservation invariants.
pub fn validate_axiom_promotion_report(
    report: &AxiomPromotionReport,
    verdict_axioms: &[String],
) -> Result<(), Failure> {
    let phase = "ndjson-comparator";
    if !matches!(
        report.mode.as_str(),
        "m3_lambda_lifted" | "full_theory_replay" | "none"
    ) {
        return Err(Failure::policy(
            phase,
            format!("invalid axiomPromotion.mode `{}`", report.mode),
        ));
    }
    if !is_sha256_hex(&report.allowlist_sha256) || !is_sha256_hex(&report.m3_ndjson_sha256) {
        return Err(Failure::policy(
            phase,
            "invalid SHA-256 digest in axiomPromotion",
        ));
    }
    if report.post_m3_declarations == 0 {
        return Err(Failure::policy(
            phase,
            "axiomPromotion reported zero postM3Declarations",
        ));
    }
    if report.mode != "m3_lambda_lifted" && !report.lifted_hypotheses.is_empty() {
        return Err(Failure::policy(
            phase,
            "liftedHypotheses must be empty unless mode is m3_lambda_lifted",
        ));
    }
    let verdict_ax_set: BTreeSet<&str> = verdict_axioms.iter().map(String::as_str).collect();
    for hyp in &report.lifted_hypotheses {
        if hyp.name.is_empty() || !is_sha256_hex(&hyp.cone_merkle_sha256) {
            return Err(Failure::policy(phase, "malformed liftedHypothesis entry"));
        }
        for ax in &hyp.inherited_axioms {
            if !STANDARD_PERMITTED_AXIOMS.contains(&ax.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!("unpermitted inherited axiom `{ax}` in liftedHypothesis"),
                ));
            }
            if !verdict_ax_set.contains(ax.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!("inherited axiom `{ax}` missing from top-level verdict axioms"),
                ));
            }
        }
    }
    Ok(())
}

/// Build a verified [`PromotedTheoremAllowlist`] from an isolated `theory_env`
/// export (`Anneal.*` + `Trusted.*` only, zero untrusted `Proof` modules).
///
/// Rejects `theory_env` fail-closed if any constant is `opaque`, `unsafe`,
/// `partial`, `sorryAx`, or an unpermitted custom `axiom`, and admits strictly
/// non-`_private` `CanonConstInfo::Thm` declarations belonging to
/// `allowed_theory_modules`.
pub fn build_promoted_allowlist(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    theory_env: &ExportedEnv,
    allowed_theory_modules: &[String],
    model_modules: &[String],
    theory_manifest_sha256: &str,
) -> Result<PromotedTheoremAllowlist, Failure> {
    build_promoted_allowlist_filtered(
        arena,
        init_primitives,
        theory_env,
        allowed_theory_modules,
        model_modules,
        theory_manifest_sha256,
        None,
    )
}

/// Like [`build_promoted_allowlist`], optionally restricting entry construction
/// to `only_theorems` while still auditing every constant in `theory_env` for
/// `opaque`, `unsafe`/`partial`, `sorryAx`, and custom `axiom`s.
pub fn build_promoted_allowlist_filtered(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    theory_env: &ExportedEnv,
    allowed_theory_modules: &[String],
    model_modules: &[String],
    theory_manifest_sha256: &str,
    only_theorems: Option<&BTreeSet<String>>,
) -> Result<PromotedTheoremAllowlist, Failure> {
    let phase = "m3-allowlist";
    if !is_sha256_hex(theory_manifest_sha256) {
        return Err(Failure::operational(
            phase,
            "invalid theory_manifest_sha256",
        ));
    }
    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|n| arena.intern_dotted_name(n))
        .collect();

    for &cid in &theory_env.const_order {
        let ci = &theory_env.constants[&cid];
        if let Some(pinned) = init_primitives.constants.get(&cid)
            && ci != pinned
        {
            return Err(Failure::policy(
                phase,
                format!(
                    "theory export primitive `{}` differs from clean sysroot",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in promoted theory",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe/partial declaration `{}` forbidden in promoted theory",
                    arena.name_str(cid)
                ),
            ));
        }
        if cid == sorry_ax_id {
            return Err(Failure::policy(
                phase,
                "sorryAx forbidden in promoted theory allowlist",
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) && !standard_axiom_ids.contains(&cid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "unpermitted custom axiom `{}` in promoted theory allowlist",
                    arena.name_str(cid)
                ),
            ));
        }
    }

    let mut sorted_theory_mods: Vec<&str> =
        allowed_theory_modules.iter().map(String::as_str).collect();
    sorted_theory_mods.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));

    let mut sorted_model_mods: Vec<&str> = model_modules.iter().map(String::as_str).collect();
    sorted_model_mods.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));

    let mut cone_memo = HashMap::new();
    let mut visiting_decls = BTreeSet::new();
    let mut visiting_blocks = BTreeSet::new();

    let mut entries = BTreeMap::new();
    for &cid in &theory_env.const_order {
        let full_name = arena.name_str(cid).to_owned();
        if full_name.starts_with("_private.") {
            continue;
        }
        if let Some(filter) = only_theorems
            && !filter.contains(&full_name)
        {
            continue;
        }
        let Some(CanonConstInfo::Thm { level_params, .. }) = theory_env.constants.get(&cid) else {
            continue;
        };
        let num_level_params = level_params.len();
        let Some(&owner_mod) = sorted_theory_mods.iter().find(|&&m| {
            full_name == m
                || (full_name.starts_with(m) && full_name.as_bytes().get(m.len()) == Some(&b'.'))
        }) else {
            continue;
        };

        let raw_digest = compute_digest_rec(
            arena,
            theory_env,
            cid,
            Some(cid),
            DigestMode::TheoremSignatureCone,
            &mut cone_memo,
            &mut visiting_decls,
            &mut visiting_blocks,
            phase,
        )?;
        let cone_merkle_sha256 = hex_encode_32(&raw_digest);

        let full_bfs = bfs_cone(arena, theory_env, &[cid]);
        let mut used_foundation_axioms = Vec::new();
        let mut model_closure = Vec::new();
        for &dep in &full_bfs.visited {
            if dep == sorry_ax_id {
                return Err(Failure::policy(
                    phase,
                    format!("theory theorem `{full_name}` transitively references sorryAx"),
                ));
            }
            if standard_axiom_ids.contains(&dep) {
                used_foundation_axioms.push(arena.name_str(dep).to_owned());
            }
            let dep_str = arena.name_str(dep);
            if let Some(&mmod) = sorted_model_mods.iter().find(|&&m| {
                dep_str == m
                    || (dep_str.starts_with(m) && dep_str.as_bytes().get(m.len()) == Some(&b'.'))
            }) {
                model_closure.push(ClosureEntry {
                    name: dep_str.to_owned(),
                    module: mmod.to_owned(),
                });
            }
        }
        used_foundation_axioms.sort();
        used_foundation_axioms.dedup();
        model_closure.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.module.cmp(&b.module)));
        model_closure.dedup();

        entries.insert(
            full_name.clone(),
            PromotedTheoremEntry {
                name: full_name,
                module: owner_mod.to_owned(),
                num_level_params,
                cone_merkle_sha256,
                used_foundation_axioms,
                model_closure,
            },
        );
    }

    Ok(PromotedTheoremAllowlist {
        schema_version: 1,
        theory_manifest_sha256: theory_manifest_sha256.to_owned(),
        entries,
    })
}

/// Output of [`verify_ndjson_and_apply_m3`].
#[derive(Debug)]
pub struct M3VerificationResult {
    pub summary: StructuralCompareSummary,
    pub promotion_report: AxiomPromotionReport,
    /// Present when M3 lambda-lifted at least one hypothesis (`mode ==
    /// "m3_lambda_lifted"`), holding the serialized `proof_m3.ndjson` bytes and
    /// pruned environment to pass to external kernels.
    pub rewritten_ndjson: Option<(String, ExportedEnv)>,
}

/// Perform full pure-Rust structural verification of `5-init`, `5a`, and `5b`
/// together with Option-B bottom-up lambda-lifted discharge (`M3`) of
/// allowlisted theorems.
#[allow(clippy::too_many_arguments)]
pub fn verify_ndjson_and_apply_m3(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    expected_cone: &ExportedEnv,
    proof_full: &ExportedEnv,
    raw_proof_sha256: &str,
    req: &StructuralCompareRequest<'_>,
    allowlist: &PromotedTheoremAllowlist,
    full_theory_replay: bool,
) -> Result<M3VerificationResult, Failure> {
    let phase = "ndjson-comparator";
    let allowlist_sha256 = allowlist.allowlist_sha256()?;

    // 1–6. Validate sysroot primitives, Quot post-check, `expected_cone ⊆
    // proof_full`, `Expected.claim` canonical root, statement-origin isolation,
    // Spec bans, and PRE-M3 `theorem_name` exact monomorphic target type!
    let pre_m3 = verify_pre_m3_invariants(
        arena,
        init_primitives,
        expected_cone,
        proof_full,
        req,
        allowlist,
        full_theory_replay,
    )?;

    let pre_m3_declarations = proof_full.const_order.len();
    let raw_reach = bfs_cone(
        arena,
        proof_full,
        &[pre_m3.theorem_id, pre_m3.expected_decl_id],
    );

    // Identify candidate promoted roots in `raw_reach` when promotion is
    // active.
    let mut candidate_roots: BTreeMap<CanonNameId, &PromotedTheoremEntry> = BTreeMap::new();
    if !full_theory_replay && !allowlist.entries.is_empty() {
        for &cid in &raw_reach.visited {
            let name_s = arena.name_str(cid);
            if let Some(entry) = allowlist.entries.get(name_s) {
                match &proof_full.constants[&cid] {
                    CanonConstInfo::Thm { .. } => {
                        candidate_roots.insert(cid, entry);
                    }
                    CanonConstInfo::Axiom {
                        is_unsafe: false, ..
                    } => {
                        candidate_roots.insert(cid, entry);
                    }
                    other => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "allowlisted theorem `{name_s}` has invalid declaration kind `{}`",
                                other.kind_label()
                            ),
                        ));
                    }
                }
            }
        }
    }

    // Verify arity + full Merkle statement-cone digest on EVERY allowlist
    // match BEFORE computing the liftable greatest fixed point so tampered
    // `def`s inside `unliftable_kept` never slip by!
    let mut cone_memo = HashMap::new();
    let mut visiting_decls = BTreeSet::new();
    let mut visiting_blocks = BTreeSet::new();
    for (&cid, &entry) in &candidate_roots {
        let actual_arity = proof_full.constants[&cid].level_params().len();
        if actual_arity != entry.num_level_params {
            return Err(Failure::policy(
                phase,
                format!(
                    "promoted theorem `{}` universe arity mismatch (expected {}, found {actual_arity})",
                    entry.name, entry.num_level_params
                ),
            ));
        }
        let raw_cone = compute_digest_rec(
            arena,
            proof_full,
            cid,
            Some(cid),
            DigestMode::TheoremSignatureCone,
            &mut cone_memo,
            &mut visiting_decls,
            &mut visiting_blocks,
            phase,
        )?;
        let actual_cone = hex_encode_32(&raw_cone);
        if actual_cone != entry.cone_merkle_sha256 {
            return Err(Failure::policy(
                phase,
                format!(
                    "Merkle constant-cone mismatch for promoted theorem `{}` \
                     (expected {}, found {actual_cone})",
                    entry.name, entry.cone_merkle_sha256
                ),
            ));
        }
    }

    // Greatest fixed point (`gfp`) of liftable roots: treat candidate roots in
    // `lifted_roots` as signature-only (`skip_value = true`) so dead `Defn`s
    // reachable exclusively inside a lifted theorem's pruned proof body do not
    // pollute `unliftable_bfs`. Any candidate root still reached from
    // `expected_decl_id`, a surviving non-`Thm` declaration, or another lifted
    // binder's domain is demoted to `unliftable_kept` (or rejected fail-closed
    // if it is an `Axiom`).
    let mut lifted_roots = candidate_roots;
    let mut unliftable_kept: Vec<String> = Vec::new();
    let (pruned_reach, unliftable_bfs) = loop {
        let mut p_vis = BTreeSet::new();
        let mut p_queue = VecDeque::new();
        for seed in [pre_m3.theorem_id, pre_m3.expected_decl_id] {
            if proof_full.constants.contains_key(&seed) && p_vis.insert(seed) {
                p_queue.push_back(seed);
            }
        }
        while let Some(cid) = p_queue.pop_front() {
            let Some(ci) = proof_full.constants.get(&cid) else {
                continue;
            };
            let skip_val = lifted_roots.contains_key(&cid);
            for dep in arena.collect_const_deps_filtered(ci, false, skip_val) {
                if proof_full.constants.contains_key(&dep) && p_vis.insert(dep) {
                    p_queue.push_back(dep);
                }
            }
        }

        let mut unliftable_seeds: Vec<CanonNameId> = vec![pre_m3.expected_decl_id];
        for &cid in &p_vis {
            let ci = &proof_full.constants[&cid];
            let is_promoted_ax =
                matches!(ci, CanonConstInfo::Axiom { .. }) && lifted_roots.contains_key(&cid);
            if !matches!(ci, CanonConstInfo::Thm { .. }) && !is_promoted_ax {
                unliftable_seeds.push(cid);
            }
        }
        for &cand_id in lifted_roots.keys() {
            let ty = proof_full.constants[&cand_id].ty();
            let mut ty_deps = BTreeSet::new();
            arena.collect_expr_consts(ty, false, &mut ty_deps);
            unliftable_seeds.extend(ty_deps);
        }
        let u_bfs = bfs_cone(arena, proof_full, &unliftable_seeds);

        let mut blocked_ids = Vec::new();
        for (&cid, &entry) in &lifted_roots {
            if u_bfs.visited.contains(&cid) {
                if matches!(proof_full.constants[&cid], CanonConstInfo::Axiom { .. }) {
                    let chain = format_blame_path(arena, &u_bfs.parent, cid);
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "promoted axiom `{}` cannot appear inside computational/expected cone \
                             (blame: {chain})",
                            entry.name
                        ),
                    ));
                }
                blocked_ids.push((cid, entry.name.clone()));
            }
        }
        if blocked_ids.is_empty() {
            lifted_roots.retain(|cid, _| p_vis.contains(cid));
            break (p_vis, u_bfs);
        }
        for (cid, name) in blocked_ids {
            lifted_roots.remove(&cid);
            unliftable_kept.push(name);
        }
    };
    unliftable_kept.sort();

    // Fast path when zero roots are lifted (either `--full-theory-replay`, no
    // allowlist matches, or all matches were `def`-locked).
    if lifted_roots.is_empty() {
        let summary = finalize_axiom_and_closure_check(
            arena,
            expected_cone,
            proof_full,
            &pre_m3,
            req,
            &BTreeSet::new(),
            &[],
        )?;
        let mode = if full_theory_replay {
            "full_theory_replay"
        } else {
            "none"
        }
        .to_owned();
        return Ok(M3VerificationResult {
            summary,
            promotion_report: AxiomPromotionReport {
                mode,
                allowlist_sha256,
                pre_m3_declarations,
                post_m3_declarations: pre_m3_declarations,
                m3_ndjson_sha256: raw_proof_sha256.to_owned(),
                lifted_hypotheses: Vec::new(),
                unliftable_kept,
            },
            rewritten_ndjson: None,
        });
    }

    // Option-B bottom-up topological lambda-lifting across internal `Thm`s!
    let (m3_ndjson, m3_env, target_slots) = apply_option_b_m3_lift(
        arena,
        init_primitives,
        proof_full,
        pre_m3.expected_decl_id,
        pre_m3.theorem_id,
        &pruned_reach,
        &unliftable_bfs.visited,
        &lifted_roots,
        phase,
    )?;

    // Post-M3 invariant: ZERO `lifted_roots` may survive in `m3_env`!
    for &lid in lifted_roots.keys() {
        if m3_env.constants.contains_key(&lid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "promoted root `{}` survived post-M3 garbage collection",
                    arena.name_str(lid)
                ),
            ));
        }
    }

    let mut inherited_axioms_union = BTreeSet::new();
    let mut inherited_model_closure = Vec::new();
    let mut lifted_records = Vec::with_capacity(target_slots.len());
    for (aid, concrete_us) in &target_slots {
        let entry = lifted_roots[aid];
        for ax in &entry.used_foundation_axioms {
            inherited_axioms_union.insert(ax.clone());
        }
        inherited_model_closure.extend(entry.model_closure.iter().cloned());
        let rendered_us: Vec<String> = concrete_us
            .iter()
            .map(|&u| render_canon_level(arena, u))
            .collect();
        lifted_records.push(LiftedHypothesisRecord {
            name: entry.name.clone(),
            universe_levels: rendered_us,
            cone_merkle_sha256: entry.cone_merkle_sha256.clone(),
            inherited_axioms: entry.used_foundation_axioms.clone(),
        });
    }

    let summary = finalize_axiom_and_closure_check(
        arena,
        expected_cone,
        &m3_env,
        &pre_m3,
        req,
        &inherited_axioms_union,
        &inherited_model_closure,
    )?;
    let m3_ndjson_sha256 = sha256_bytes(m3_ndjson.as_bytes());
    let post_m3_declarations = m3_env.const_order.len();

    Ok(M3VerificationResult {
        summary,
        promotion_report: AxiomPromotionReport {
            mode: "m3_lambda_lifted".to_owned(),
            allowlist_sha256,
            pre_m3_declarations,
            post_m3_declarations,
            m3_ndjson_sha256,
            lifted_hypotheses: lifted_records,
            unliftable_kept,
        },
        rewritten_ndjson: Some((m3_ndjson, m3_env)),
    })
}

struct PreM3Verified {
    expected_decl_id: CanonNameId,
    theorem_id: CanonNameId,
    pre_m3_sorry_used: bool,
    pre_m3_sorry_declarations: BTreeSet<String>,
}

fn verify_pre_m3_invariants(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    expected_cone: &ExportedEnv,
    proof_full: &ExportedEnv,
    req: &StructuralCompareRequest<'_>,
    allowlist: &PromotedTheoremAllowlist,
    full_theory_replay: bool,
) -> Result<PreM3Verified, Failure> {
    let phase = "ndjson-comparator";

    for prim in PINNED_INIT_PRIMITIVES {
        let id = arena.intern_dotted_name(prim);
        if !init_primitives.constants.contains_key(&id) {
            return Err(Failure::operational(
                phase,
                format!("init_primitives_cone is missing required primitive `{prim}`"),
            ));
        }
    }

    let mut quot_ids = BTreeMap::new();
    for (qname, expected_kind) in QUOT_PRIMITIVES {
        let qid = arena.intern_dotted_name(qname);
        match init_primitives.constants.get(&qid) {
            Some(CanonConstInfo::Quot { kind, .. }) if *kind == expected_kind => {
                quot_ids.insert(qid, (qname, expected_kind));
            }
            Some(other) => {
                return Err(Failure::operational(
                    phase,
                    format!(
                        "init_primitives_cone has malformed quotient `{qname}` ({})",
                        other.kind_label()
                    ),
                ));
            }
            None => {
                return Err(Failure::operational(
                    phase,
                    format!("init_primitives_cone missing quotient `{qname}`"),
                ));
            }
        }
    }

    for &name_id in &expected_cone.const_order {
        let expected_ci = &expected_cone.constants[&name_id];
        let Some(proof_ci) = proof_full.constants.get(&name_id) else {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` missing from proof export",
                    arena.name_str(name_id)
                ),
            ));
        };
        if expected_ci != proof_ci {
            return Err(Failure::policy(
                phase,
                format!(
                    "declaration `{}` differs between trusted expected export and proof export",
                    arena.name_str(name_id)
                ),
            ));
        }
    }

    for (label, env) in [("expected_cone", expected_cone), ("proof_full", proof_full)] {
        for &name_id in &env.const_order {
            let ci = &env.constants[&name_id];
            if let Some(pinned_ci) = init_primitives.constants.get(&name_id)
                && ci != pinned_ci
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "pinned Init primitive `{}` in {label} differs from clean sysroot definition",
                        arena.name_str(name_id)
                    ),
                ));
            }
            if let CanonConstInfo::Quot { kind, .. } = ci {
                match quot_ids.get(&name_id) {
                    Some((_, expected_kind)) if expected_kind == kind => {}
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "unexpected quotient declaration `{}` in {label}",
                                arena.name_str(name_id)
                            ),
                        ));
                    }
                }
            }
        }
    }

    let quot_sound_id = arena.intern_dotted_name("Quot.sound");
    let any_quot_present = proof_full.constants.contains_key(&quot_sound_id)
        || quot_ids
            .keys()
            .any(|id| proof_full.constants.contains_key(id));
    if any_quot_present {
        for (&qid, &(qname, expected_kind)) in &quot_ids {
            if let Some(proof_ci) = proof_full.constants.get(&qid) {
                let pinned_ci = &init_primitives.constants[&qid];
                match proof_ci {
                    CanonConstInfo::Quot { kind, .. }
                        if *kind == expected_kind && proof_ci == pinned_ci => {}
                    _ => {
                        return Err(Failure::policy(
                            phase,
                            format!("quotient post-check failed for `{qname}` in proof export"),
                        ));
                    }
                }
            }
        }
    }

    let expected_decl_id = arena.intern_dotted_name(req.expected_declaration);
    let expected_ci = expected_cone
        .constants
        .get(&expected_decl_id)
        .ok_or_else(|| {
            Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` missing from expected_cone",
                    req.expected_declaration
                ),
            )
        })?;
    let prop_sort = arena.intern_expr(CanonExpr::Sort(arena.zero_level));
    let canonical_expr = arena.build_canonical_claim_expr(
        req.canonical_root,
        req.subject_declaration,
        req.specification_declaration,
    );
    let expected_body = match expected_ci {
        CanonConstInfo::Defn {
            level_params,
            ty,
            value,
            safety,
            ..
        } => {
            if !level_params.is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` must not have universe parameters",
                        req.expected_declaration
                    ),
                ));
            }
            if *safety != DefinitionSafety::Safe {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` must be safe",
                        req.expected_declaration
                    ),
                ));
            }
            if *ty != prop_sort {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` must have type Prop",
                        req.expected_declaration
                    ),
                ));
            }
            if *value != canonical_expr {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "compiled expected body of `{}` differs from canonical root application",
                        req.expected_declaration
                    ),
                ));
            }
            *value
        }
        other => {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected declaration `{}` must be a definition (found {})",
                    req.expected_declaration,
                    other.kind_label()
                ),
            ));
        }
    };

    let is_forbidden_expected_const = |arena: &CanonicalArena, cid: CanonNameId| -> bool {
        let root = arena.name_root(cid);
        if req.forbidden_expected_roots.contains(root) {
            return true;
        }
        req.forbidden_expected_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m))
    };
    for &cid in &expected_cone.const_order {
        if is_forbidden_expected_const(arena, cid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "expected cone contains forbidden proof-origin constant `{}`",
                    arena.name_str(cid)
                ),
            ));
        }
        let stripped_deps = arena.collect_const_deps(&expected_cone.constants[&cid], true);
        for dep in stripped_deps {
            if is_forbidden_expected_const(arena, dep) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "expected declaration `{}` references forbidden proof-origin constant `{}`",
                        arena.name_str(cid),
                        arena.name_str(dep)
                    ),
                ));
            }
        }
    }

    for &cid in &expected_cone.const_order {
        let is_spec_const = req
            .specification_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m));
        if is_spec_const {
            let deps = arena.collect_const_deps(&expected_cone.constants[&cid], false);
            for dep in deps {
                let user_dep = arena.strip_private_and_root(dep);
                let is_lean_syntax =
                    user_dep == "Lean.Syntax" || user_dep.starts_with("Lean.Syntax.");
                let is_panic_const = matches!(
                    user_dep,
                    "panic" | "panicCore" | "panicWithPos" | "panicWithPosWithDecl"
                );
                if is_lean_syntax || is_panic_const {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "specification declaration `{}` cannot reference `{}`",
                            arena.name_str(cid),
                            arena.name_str(dep)
                        ),
                    ));
                }
            }
        }
    }

    // Step 6 (CRITICAL PRE-M3 GATE): check `theorem_name` BEFORE M3 adds
    // binders!
    let theorem_id = arena.intern_dotted_name(req.theorem_name);
    let expected_const_expr = arena.intern_expr(CanonExpr::Const(expected_decl_id, Vec::new()));
    let theorem_ci = proof_full.constants.get(&theorem_id).ok_or_else(|| {
        Failure::policy(
            phase,
            format!(
                "target theorem `{}` missing from proof export",
                req.theorem_name
            ),
        )
    })?;
    match theorem_ci {
        CanonConstInfo::Thm {
            level_params, ty, ..
        } => {
            if !level_params.is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "target theorem `{}` must not have universe parameters",
                        req.theorem_name
                    ),
                ));
            }
            if *ty != expected_const_expr && *ty != expected_body {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "target theorem `{}` type differs from `{}` / canonical root",
                        req.theorem_name, req.expected_declaration
                    ),
                ));
            }
        }
        other => {
            return Err(Failure::policy(
                phase,
                format!(
                    "target root `{}` must be a theorem (found {})",
                    req.theorem_name,
                    other.kind_label()
                ),
            ));
        }
    }

    // Global `opaque`, `unsafe`/`partial`, and `expected_cone` 3-axiom check on
    // raw `proof_full` before M3 garbage-collects anything!
    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|n| arena.intern_dotted_name(n))
        .collect();
    let expected_bfs = bfs_cone(arena, expected_cone, &[expected_decl_id]);
    for &cid in &expected_bfs.visited {
        let ci = &expected_cone.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) && !standard_axiom_ids.contains(&cid) {
            let chain = format_blame_path(arena, &expected_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unpermitted axiom `{}` in expected cone (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
    }

    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let expected_cone_set: BTreeSet<CanonNameId> =
        expected_cone.constants.keys().copied().collect();
    let raw_bfs = bfs_cone(arena, proof_full, &[theorem_id, expected_decl_id]);
    let mut pre_m3_sorry_used = false;
    let mut pre_m3_sorry_declarations = BTreeSet::new();

    for &cid in &proof_full.const_order {
        let ci = &proof_full.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            let chain = format_blame_path(arena, &raw_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, &raw_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if let CanonConstInfo::Axiom { is_unsafe, .. } = ci {
            let is_promoted_ax = !full_theory_replay
                && !*is_unsafe
                && raw_bfs.visited.contains(&cid)
                && allowlist.entries.contains_key(arena.name_str(cid));
            let allowed = standard_axiom_ids.contains(&cid)
                || (req.allow_sorry_in_proof && cid == sorry_ax_id)
                || is_promoted_ax;
            if !allowed {
                let chain = format_blame_path(arena, &raw_bfs.parent, cid);
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unpermitted axiom `{}` in proof export (blame: {chain})",
                        arena.name_str(cid)
                    ),
                ));
            }
            if cid == sorry_ax_id && raw_bfs.visited.contains(&cid) {
                pre_m3_sorry_used = true;
            }
        }
        if raw_bfs.visited.contains(&cid) && cid != sorry_ax_id {
            let deps = arena.collect_const_deps(ci, false);
            if deps.contains(&sorry_ax_id) {
                if !req.allow_sorry_in_proof || expected_cone_set.contains(&cid) {
                    let chain = format_blame_path(arena, &raw_bfs.parent, cid);
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "unpermitted sorryAx reference in `{}` (blame: {chain})",
                            arena.name_str(cid)
                        ),
                    ));
                }
                pre_m3_sorry_declarations.insert(arena.name_str(cid).to_owned());
            }
        }
    }

    if proof_full.constants.contains_key(&sorry_ax_id) && !raw_bfs.visited.contains(&sorry_ax_id) {
        return Err(Failure::policy(
            phase,
            "unpermitted unreached sorryAx declaration in proof export",
        ));
    }

    Ok(PreM3Verified {
        expected_decl_id,
        theorem_id,
        pre_m3_sorry_used,
        pre_m3_sorry_declarations,
    })
}

type LiftedConcreteSlots = Vec<(CanonNameId, Vec<CanonLevelId>)>;

#[allow(clippy::too_many_arguments)]
fn apply_option_b_m3_lift(
    arena: &mut CanonicalArena,
    init_primitives: &ExportedEnv,
    proof_full: &ExportedEnv,
    expected_decl_id: CanonNameId,
    theorem_id: CanonNameId,
    reachable: &BTreeSet<CanonNameId>,
    unliftable: &BTreeSet<CanonNameId>,
    lifted_roots: &BTreeMap<CanonNameId, &PromotedTheoremEntry>,
    phase: &str,
) -> Result<(String, ExportedEnv, LiftedConcreteSlots), Failure> {
    let max_m3_exprs =
        MIN_M3_EXPR_BUDGET.max(arena.exprs.len().saturating_mul(M3_EXPR_BUDGET_MULTIPLIER));

    // Topologically sort candidate internal `Thm`s (`reachable \ unliftable \
    // lifted_roots`).
    let mut candidate_thms = BTreeSet::new();
    for &cid in reachable {
        if unliftable.contains(&cid) || lifted_roots.contains_key(&cid) {
            continue;
        }
        if matches!(
            proof_full.constants.get(&cid),
            Some(CanonConstInfo::Thm { .. })
        ) {
            candidate_thms.insert(cid);
        }
    }

    let mut visit_state: HashMap<CanonNameId, u8> = HashMap::new();
    let mut topo_thms: Vec<CanonNameId> = Vec::new();
    fn dfs_thm(
        cid: CanonNameId,
        arena: &CanonicalArena,
        proof_full: &ExportedEnv,
        candidate_thms: &BTreeSet<CanonNameId>,
        visit_state: &mut HashMap<CanonNameId, u8>,
        topo_thms: &mut Vec<CanonNameId>,
        phase: &str,
    ) -> Result<(), Failure> {
        match visit_state.get(&cid).copied() {
            Some(2) => return Ok(()),
            Some(1) => {
                return Err(Failure::policy(
                    phase,
                    format!("cyclic helper theorem dependency `{}`", arena.name_str(cid)),
                ));
            }
            _ => {}
        }
        visit_state.insert(cid, 1);
        if let Some(ci) = proof_full.constants.get(&cid) {
            for dep in arena.collect_const_deps(ci, false) {
                if dep != cid && candidate_thms.contains(&dep) {
                    dfs_thm(
                        dep,
                        arena,
                        proof_full,
                        candidate_thms,
                        visit_state,
                        topo_thms,
                        phase,
                    )?;
                }
            }
        }
        visit_state.insert(cid, 2);
        topo_thms.push(cid);
        Ok(())
    }
    for &cid in &candidate_thms {
        dfs_thm(
            cid,
            arena,
            proof_full,
            &candidate_thms,
            &mut visit_state,
            &mut topo_thms,
            phase,
        )?;
    }

    // `lifted_reqs[X]` stores the canonicalized list of `(root_id,
    // norm_levels)` relative to `X.level_params`.
    let mut lifted_reqs: HashMap<CanonNameId, Vec<(CanonNameId, Vec<NormLevel>)>> = HashMap::new();
    for &aid in lifted_roots.keys() {
        let arity = proof_full.constants[&aid].level_params().len();
        let params: Vec<NormLevel> = (0..arity).map(|i| NormLevel::Param(i as u32)).collect();
        lifted_reqs.insert(aid, vec![(aid, params)]);
    }

    let mut rewritten_env = proof_full.clone();
    let mut target_concrete_slots: Vec<(CanonNameId, Vec<CanonLevelId>)> = Vec::new();

    for thm_id in topo_thms {
        let Some(CanonConstInfo::Thm {
            level_params,
            ty,
            value,
            all,
            ..
        }) = rewritten_env.constants.get(&thm_id).cloned()
        else {
            continue;
        };

        // Scan `ty` and `value` for occurrences of any `X` with non-empty
        // `lifted_reqs[X]`.
        let mut has_ref: HashMap<CanonExprId, bool> = HashMap::new();
        let mut raw_slots: BTreeSet<(Vec<u8>, CanonNameId, Vec<NormLevel>)> = BTreeSet::new();

        for root_e in [ty, value] {
            collect_lifted_occurrences(
                arena,
                root_e,
                &level_params,
                &lifted_reqs,
                &mut has_ref,
                &mut raw_slots,
                phase,
            )?;
        }

        if raw_slots.is_empty() {
            continue;
        }
        if raw_slots.len() > MAX_LIFTED_HYPS_PER_THM {
            return Err(Failure::policy(
                phase,
                format!(
                    "theorem `{}` exceeds MAX_LIFTED_HYPS_PER_THM ({} > {MAX_LIFTED_HYPS_PER_THM})",
                    arena.name_str(thm_id),
                    raw_slots.len()
                ),
            ));
        }

        let slots: Vec<(CanonNameId, Vec<NormLevel>)> = raw_slots
            .into_iter()
            .map(|(_, aid, nus)| (aid, nus))
            .collect();
        let slot_index: HashMap<(CanonNameId, Vec<NormLevel>), usize> = slots
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect();
        let k = slots.len() as u64;

        // Materialize each slot's domain expression `S_s` (closed wrt BVars!).
        let mut slot_domains: Vec<CanonExprId> = Vec::with_capacity(slots.len());
        let mut concrete_slots: Vec<(CanonNameId, Vec<CanonLevelId>)> =
            Vec::with_capacity(slots.len());
        for (aid, norm_us) in &slots {
            let mut concrete_us = Vec::with_capacity(norm_us.len());
            for nl in norm_us {
                let cl = norm_to_canon_level(arena, nl, &level_params, phase)?;
                if thm_id == theorem_id && !is_closed_canon_level(arena, cl) {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "target theorem `{}` lifted non-ground universe level",
                            arena.name_str(thm_id)
                        ),
                    ));
                }
                concrete_us.push(cl);
            }
            let a_ci = &proof_full.constants[aid];
            let dom_ty = instantiate_level_params_expr(
                arena,
                a_ci.ty(),
                a_ci.level_params(),
                &concrete_us,
                &level_params,
                phase,
            )?;
            slot_domains.push(dom_ty);
            concrete_slots.push((*aid, concrete_us));
        }

        if has_loose_bvar_at_least(arena, ty, 0) || has_loose_bvar_at_least(arena, value, 0) {
            return Err(Failure::policy(
                phase,
                format!(
                    "theorem `{}` contains ill-formed loose BVar before M3 lift",
                    arena.name_str(thm_id)
                ),
            ));
        }
        let new_ty_core = rewrite_expr_m3(
            arena,
            ty,
            &level_params,
            k,
            lifted_roots,
            &lifted_reqs,
            &slot_index,
            &has_ref,
            max_m3_exprs,
            phase,
        )?;
        let new_val_core = rewrite_expr_m3(
            arena,
            value,
            &level_params,
            k,
            lifted_roots,
            &lifted_reqs,
            &slot_index,
            &has_ref,
            max_m3_exprs,
            phase,
        )?;

        let mut new_ty = new_ty_core;
        let mut new_val = new_val_core;
        for &dom_ty in slot_domains.iter().rev() {
            new_ty = arena.intern_expr(CanonExpr::ForallE {
                ty: dom_ty,
                body: new_ty,
            });
            new_val = arena.intern_expr(CanonExpr::Lam {
                ty: dom_ty,
                body: new_val,
            });
        }

        rewritten_env.constants.insert(
            thm_id,
            CanonConstInfo::Thm {
                name: thm_id,
                level_params,
                ty: new_ty,
                value: new_val,
                all,
            },
        );
        if thm_id == theorem_id {
            target_concrete_slots = concrete_slots;
        }
        lifted_reqs.insert(thm_id, slots);
    }

    let (m3_ndjson, m3_env) = emit_ndjson(
        arena,
        &rewritten_env,
        Some(init_primitives),
        &[expected_decl_id, theorem_id],
        phase,
    )?;
    Ok((m3_ndjson, m3_env, target_concrete_slots))
}

fn collect_lifted_occurrences(
    arena: &CanonicalArena,
    root: CanonExprId,
    ambient_params: &[CanonNameId],
    lifted_reqs: &HashMap<CanonNameId, Vec<(CanonNameId, Vec<NormLevel>)>>,
    has_ref: &mut HashMap<CanonExprId, bool>,
    raw_slots: &mut BTreeSet<(Vec<u8>, CanonNameId, Vec<NormLevel>)>,
    phase: &str,
) -> Result<bool, Failure> {
    let mut stack = vec![(root, false)];
    while let Some((eid, done)) = stack.pop() {
        if has_ref.contains_key(&eid) {
            continue;
        }
        if !done {
            stack.push((eid, true));
            match &arena.exprs[eid.0 as usize] {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, false));
                    stack.push((*a, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, false));
                    stack.push((*body, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, false));
                    stack.push((*value, false));
                    stack.push((*body, false));
                }
                CanonExpr::Proj { struct_expr, .. } => stack.push((*struct_expr, false)),
            }
        } else {
            let flag = match &arena.exprs[eid.0 as usize] {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => false,
                CanonExpr::Const(cid, call_us) => {
                    if let Some(reqs) = lifted_reqs.get(cid) {
                        let mut norm_call = Vec::with_capacity(call_us.len());
                        for &u in call_us {
                            norm_call.push(normalize_level(arena, u, ambient_params, phase)?);
                        }
                        for (aid, req_lvls) in reqs {
                            let mut inst_lvls = Vec::with_capacity(req_lvls.len());
                            for rl in req_lvls {
                                inst_lvls.push(subst_norm_level(rl, &norm_call, phase)?);
                            }
                            let mut sort_key = Vec::new();
                            encode_canon_name(arena, *aid, &mut sort_key);
                            raw_slots.insert((sort_key, *aid, inst_lvls));
                        }
                        true
                    } else {
                        false
                    }
                }
                CanonExpr::App(f, a) => has_ref[f] || has_ref[a],
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    has_ref[ty] || has_ref[body]
                }
                CanonExpr::LetE { ty, value, body } => {
                    has_ref[ty] || has_ref[value] || has_ref[body]
                }
                CanonExpr::Proj { struct_expr, .. } => has_ref[struct_expr],
            };
            has_ref.insert(eid, flag);
        }
    }
    Ok(has_ref[&root])
}

#[allow(clippy::too_many_arguments)]
fn rewrite_expr_m3(
    arena: &mut CanonicalArena,
    root: CanonExprId,
    ambient_params: &[CanonNameId],
    k: u64,
    lifted_roots: &BTreeMap<CanonNameId, &PromotedTheoremEntry>,
    lifted_reqs: &HashMap<CanonNameId, Vec<(CanonNameId, Vec<NormLevel>)>>,
    slot_index: &HashMap<(CanonNameId, Vec<NormLevel>), usize>,
    has_ref: &HashMap<CanonExprId, bool>,
    max_m3_exprs: usize,
    phase: &str,
) -> Result<CanonExprId, Failure> {
    if !has_ref.get(&root).copied().unwrap_or(false) {
        return Ok(root);
    }
    let mut memo: HashMap<(CanonExprId, u64), CanonExprId> = HashMap::new();
    let mut stack: Vec<(CanonExprId, u64, bool)> = vec![(root, 0, false)];

    while let Some((eid, local_d, done)) = stack.pop() {
        if memo.contains_key(&(eid, local_d)) {
            continue;
        }
        // Any sub-DAG containing zero lifted references has all BVars locally
        // bound inside `root` (`b < local_d`), so it is invariant in `O(1)`!
        if !has_ref.get(&eid).copied().unwrap_or(false) {
            memo.insert((eid, local_d), eid);
            continue;
        }
        let node = arena.exprs[eid.0 as usize].clone();
        if !done {
            stack.push((eid, local_d, true));
            match &node {
                CanonExpr::Const(_, _)
                | CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, local_d, false));
                    stack.push((*a, local_d, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, local_d, false));
                    stack.push((*body, local_d + 1, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, local_d, false));
                    stack.push((*value, local_d, false));
                    stack.push((*body, local_d + 1, false));
                }
                CanonExpr::Proj { struct_expr, .. } => {
                    stack.push((*struct_expr, local_d, false));
                }
            }
        } else {
            let out = match node {
                CanonExpr::Const(cid, call_us) => {
                    if let Some(reqs) = lifted_reqs.get(&cid) {
                        let mut norm_call = Vec::with_capacity(call_us.len());
                        for &u in &call_us {
                            norm_call.push(normalize_level(arena, u, ambient_params, phase)?);
                        }
                        if lifted_roots.contains_key(&cid) {
                            let sidx = slot_index[&(cid, norm_call)] as u64;
                            let bvar_idx = local_d + (k - 1 - sidx);
                            arena.intern_expr(CanonExpr::BVar(bvar_idx))
                        } else {
                            // Internal helper `Thm`: apply each lifted binder
                            // argument in order!
                            let mut acc = arena.intern_expr(CanonExpr::Const(cid, call_us));
                            for (aid, req_lvls) in reqs {
                                let mut inst_lvls = Vec::with_capacity(req_lvls.len());
                                for rl in req_lvls {
                                    inst_lvls.push(subst_norm_level(rl, &norm_call, phase)?);
                                }
                                let sidx = slot_index[&(*aid, inst_lvls)] as u64;
                                let bvar_idx = local_d + (k - 1 - sidx);
                                let arg = arena.intern_expr(CanonExpr::BVar(bvar_idx));
                                acc = arena.intern_expr(CanonExpr::App(acc, arg));
                            }
                            acc
                        }
                    } else {
                        eid
                    }
                }
                CanonExpr::App(f, a) => {
                    let nf = memo[&(f, local_d)];
                    let na = memo[&(a, local_d)];
                    arena.intern_expr(CanonExpr::App(nf, na))
                }
                CanonExpr::Lam { ty, body } => {
                    let nty = memo[&(ty, local_d)];
                    let nbody = memo[&(body, local_d + 1)];
                    arena.intern_expr(CanonExpr::Lam {
                        ty: nty,
                        body: nbody,
                    })
                }
                CanonExpr::ForallE { ty, body } => {
                    let nty = memo[&(ty, local_d)];
                    let nbody = memo[&(body, local_d + 1)];
                    arena.intern_expr(CanonExpr::ForallE {
                        ty: nty,
                        body: nbody,
                    })
                }
                CanonExpr::LetE { ty, value, body } => {
                    let nty = memo[&(ty, local_d)];
                    let nval = memo[&(value, local_d)];
                    let nbody = memo[&(body, local_d + 1)];
                    arena.intern_expr(CanonExpr::LetE {
                        ty: nty,
                        value: nval,
                        body: nbody,
                    })
                }
                CanonExpr::Proj {
                    type_name,
                    idx,
                    struct_expr,
                } => {
                    let ns = memo[&(struct_expr, local_d)];
                    arena.intern_expr(CanonExpr::Proj {
                        type_name,
                        idx,
                        struct_expr: ns,
                    })
                }
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => eid,
            };
            if arena.exprs.len() > max_m3_exprs {
                return Err(Failure::policy(
                    phase,
                    format!("M3 expression arena exceeded budget ({max_m3_exprs})"),
                ));
            }
            memo.insert((eid, local_d), out);
        }
    }
    Ok(memo[&(root, 0)])
}

fn finalize_axiom_and_closure_check(
    arena: &mut CanonicalArena,
    expected_cone: &ExportedEnv,
    active_proof_env: &ExportedEnv,
    pre_m3: &PreM3Verified,
    req: &StructuralCompareRequest<'_>,
    inherited_axioms: &BTreeSet<String>,
    inherited_model_closure: &[ClosureEntry],
) -> Result<StructuralCompareSummary, Failure> {
    let phase = "ndjson-comparator";
    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|n| arena.intern_dotted_name(n))
        .collect();
    let expected_cone_set: BTreeSet<CanonNameId> =
        expected_cone.constants.keys().copied().collect();

    let proof_bfs = bfs_cone(
        arena,
        active_proof_env,
        &[pre_m3.theorem_id, pre_m3.expected_decl_id],
    );
    let mut axioms: BTreeSet<String> = inherited_axioms.clone();
    if pre_m3.pre_m3_sorry_used {
        axioms.insert("sorryAx".to_owned());
    }
    let mut sorry_declarations = pre_m3.pre_m3_sorry_declarations.clone();

    for &cid in &active_proof_env.const_order {
        let ci = &active_proof_env.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) {
            let chain = format_blame_path(arena, &proof_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "opaque declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if ci.is_unsafe_or_partial() {
            let chain = format_blame_path(arena, &proof_bfs.parent, cid);
            return Err(Failure::policy(
                phase,
                format!(
                    "unsafe or partial declaration `{}` forbidden in proof export (blame: {chain})",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) {
            let allowed = standard_axiom_ids.contains(&cid)
                || (req.allow_sorry_in_proof && cid == sorry_ax_id);
            if !allowed {
                let chain = format_blame_path(arena, &proof_bfs.parent, cid);
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unpermitted axiom `{}` in proof export (blame: {chain})",
                        arena.name_str(cid)
                    ),
                ));
            }
            if proof_bfs.visited.contains(&cid) {
                axioms.insert(arena.name_str(cid).to_owned());
            }
        }
        if proof_bfs.visited.contains(&cid) && cid != sorry_ax_id {
            let deps = arena.collect_const_deps(ci, false);
            if deps.contains(&sorry_ax_id) {
                if !req.allow_sorry_in_proof || expected_cone_set.contains(&cid) {
                    let chain = format_blame_path(arena, &proof_bfs.parent, cid);
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "unpermitted sorryAx reference in `{}` (blame: {chain})",
                            arena.name_str(cid)
                        ),
                    ));
                }
                sorry_declarations.insert(arena.name_str(cid).to_owned());
            }
        }
    }

    if active_proof_env.constants.contains_key(&sorry_ax_id)
        && !proof_bfs.visited.contains(&sorry_ax_id)
    {
        return Err(Failure::policy(
            phase,
            "unpermitted unreached sorryAx declaration in proof export",
        ));
    }

    let axiom_vec: Vec<String> = axioms.into_iter().collect();
    let sorry_used = validate_axiom_list(&axiom_vec, req.allow_sorry_in_proof, phase)?;

    let expected_bfs = bfs_cone(arena, expected_cone, &[pre_m3.expected_decl_id]);
    let subject_id = arena.intern_dotted_name(req.subject_declaration);
    let spec_id = arena.intern_dotted_name(req.specification_declaration);
    let subject_bfs = bfs_cone(arena, expected_cone, &[subject_id]);
    let spec_bfs = bfs_cone(arena, expected_cone, &[spec_id]);

    let subject_closure = build_closure_entries(
        arena,
        &subject_bfs.visited,
        &req.capture_modules,
        Some((
            req.subject_declaration,
            req.capture_modules.first().map(String::as_str),
        )),
    );
    let mut model_closure =
        build_closure_entries(arena, &expected_bfs.visited, &req.model_modules, None);
    model_closure.extend(inherited_model_closure.iter().cloned());
    model_closure.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.module.cmp(&b.module)));
    model_closure.dedup();

    let specification_closure = build_closure_entries(
        arena,
        &spec_bfs.visited,
        &req.specification_modules,
        Some((
            req.specification_declaration,
            req.specification_modules.first().map(String::as_str),
        )),
    );

    Ok(StructuralCompareSummary {
        axioms: axiom_vec,
        sorry_declarations: sorry_declarations.into_iter().collect(),
        sorry_used,
        checked_declarations: active_proof_env.const_order.len(),
        expected_cone_declarations: expected_cone.const_order.len(),
        subject_closure,
        model_closure,
        specification_closure,
    })
}

// ---------------------------------------------------------------------------
// 5. Tier 4: Union-Graph Tarjan-SCC Modular Shard Linker
// ---------------------------------------------------------------------------

/// Provenance classification for a non-`theory/` callee contract hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CalleeContractOrigin {
    /// Contract theorem proved by peer shard `shard_id` (`Tier 4a`).
    VerifiedShard {
        shard_id: String,
        cone_merkle_sha256: String,
    },
    /// Unverified external or FFI callee contract (`Tier 4b`).
    AssumedExternal {
        cone_merkle_sha256: String,
        total_termination: bool,
        realizability_witness_verified: bool,
    },
}

/// Input shard node for [`verify_modular_shard_dag`].
#[derive(Debug, Clone)]
pub struct ModularShardNode {
    pub shard_id: String,
    pub theorem_name: String,
    pub contract_cone_sha256: String,
    pub mir_direct_callees: BTreeSet<String>,
    pub indirect_call_provenance: BTreeSet<String>,
    pub m3_lifted_hypotheses: Vec<LiftedHypothesisRecord>,
    pub local_axioms: BTreeSet<String>,
    pub local_sorry_declarations: BTreeSet<String>,
    pub local_taint_reasons: BTreeSet<String>,
    pub local_model_closure: Vec<ClosureEntry>,
}

/// Propagated verification summary for one shard in a verified DAG.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedShardSummary {
    pub shard_id: String,
    pub topological_rank: usize,
    pub union_callees: BTreeSet<String>,
    pub axioms: BTreeSet<String>,
    pub sorry_declarations: BTreeSet<String>,
    pub taint_reasons: BTreeSet<String>,
    pub model_closure: Vec<ClosureEntry>,
}

/// Verify strict acyclicity (Tarjan SCC over MIR direct calls union indirect
/// provenance union kernel-extracted M3 proof hypotheses), Tier-4b contract
/// realizability (`AssumedContractRealizable`), and monotone semilattice
/// propagation across modular shards.
pub fn verify_modular_shard_dag(
    shards: &[ModularShardNode],
    theory_allowlist: &PromotedTheoremAllowlist,
    external_contracts: &BTreeMap<String, CalleeContractOrigin>,
) -> Result<Vec<VerifiedShardSummary>, Failure> {
    let phase = "modular-linker";
    for ext_name in external_contracts.keys() {
        if theory_allowlist.entries.contains_key(ext_name) {
            return Err(Failure::policy(
                phase,
                format!("external contract `{ext_name}` collides with theory_allowlist"),
            ));
        }
    }
    let mut shard_by_id: BTreeMap<&str, &ModularShardNode> = BTreeMap::new();
    let mut contract_registry: BTreeMap<String, CalleeContractOrigin> = external_contracts.clone();

    for s in shards {
        if s.shard_id.is_empty() || s.theorem_name.is_empty() {
            return Err(Failure::policy(phase, "empty shard_id or theorem_name"));
        }
        if theory_allowlist.entries.contains_key(&s.theorem_name) {
            return Err(Failure::policy(
                phase,
                format!(
                    "shard `{}` contract theorem `{}` collides with theory_allowlist",
                    s.shard_id, s.theorem_name
                ),
            ));
        }
        if !is_sha256_hex(&s.contract_cone_sha256) {
            return Err(Failure::policy(
                phase,
                format!("invalid contract_cone_sha256 on shard `{}`", s.shard_id),
            ));
        }
        if shard_by_id.insert(s.shard_id.as_str(), s).is_some() {
            return Err(Failure::policy(
                phase,
                format!("duplicate shard_id `{}`", s.shard_id),
            ));
        }
        if contract_registry
            .insert(
                s.theorem_name.clone(),
                CalleeContractOrigin::VerifiedShard {
                    shard_id: s.shard_id.clone(),
                    cone_merkle_sha256: s.contract_cone_sha256.clone(),
                },
            )
            .is_some()
        {
            return Err(Failure::policy(
                phase,
                format!(
                    "duplicate contract theorem `{}` across shards",
                    s.theorem_name
                ),
            ));
        }
    }

    let mut union_edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut proof_edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut extra_taints: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut theory_axioms_by_shard: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut theory_closure_by_shard: BTreeMap<String, Vec<ClosureEntry>> = BTreeMap::new();

    for s in shards {
        let mut edges = BTreeSet::new();
        let mut p_edges = BTreeSet::new();
        for callee in s
            .mir_direct_callees
            .iter()
            .chain(s.indirect_call_provenance.iter())
        {
            if !shard_by_id.contains_key(callee.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` references unknown callee shard `{callee}`",
                        s.shard_id
                    ),
                ));
            }
            edges.insert(callee.clone());
        }

        for hyp in &s.m3_lifted_hypotheses {
            if let Some(th_entry) = theory_allowlist.entries.get(&hyp.name) {
                if th_entry.cone_merkle_sha256 != hyp.cone_merkle_sha256 {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "shard `{}` hypothesis `{}` cone mismatch against theory allowlist",
                            s.shard_id, hyp.name
                        ),
                    ));
                }
                theory_axioms_by_shard
                    .entry(s.shard_id.clone())
                    .or_default()
                    .extend(th_entry.used_foundation_axioms.iter().cloned());
                theory_closure_by_shard
                    .entry(s.shard_id.clone())
                    .or_default()
                    .extend(th_entry.model_closure.iter().cloned());
                continue;
            }
            let Some(origin) = contract_registry.get(&hyp.name) else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` lifts unresolved hypothesis `{}`",
                        s.shard_id, hyp.name
                    ),
                ));
            };
            match origin {
                CalleeContractOrigin::VerifiedShard {
                    shard_id,
                    cone_merkle_sha256,
                } => {
                    if cone_merkle_sha256 != &hyp.cone_merkle_sha256 {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "shard `{}` hypothesis `{}` cone digest differs from callee shard `{shard_id}`",
                                s.shard_id, hyp.name
                            ),
                        ));
                    }
                    edges.insert(shard_id.clone());
                    p_edges.insert(shard_id.clone());
                }
                CalleeContractOrigin::AssumedExternal {
                    cone_merkle_sha256,
                    total_termination,
                    realizability_witness_verified,
                } => {
                    if cone_merkle_sha256 != &hyp.cone_merkle_sha256 {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "shard `{}` assumed external contract `{}` cone mismatch",
                                s.shard_id, hyp.name
                            ),
                        ));
                    }
                    if *total_termination && !*realizability_witness_verified {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "shard `{}` assumes Total contract `{}` without verified \
                                 AssumedContractRealizable witness",
                                s.shard_id, hyp.name
                            ),
                        ));
                    }
                    extra_taints
                        .entry(s.shard_id.clone())
                        .or_default()
                        .insert("assumed_callee_contract".to_owned());
                }
            }
        }
        union_edges.insert(s.shard_id.clone(), edges);
        proof_edges.insert(s.shard_id.clone(), p_edges);
    }

    // Iterative Tarjan's Strongly Connected Components over `(V, union_edges)`
    // so deep shard chains never consume Rust call-stack frames.
    let mut index_counter: usize = 0;
    let mut indices: HashMap<String, usize> = HashMap::new();
    let mut lowlink: HashMap<String, usize> = HashMap::new();
    let mut t_stack: Vec<String> = Vec::new();
    let mut on_stack: BTreeSet<String> = BTreeSet::new();
    let mut sccs: Vec<Vec<String>> = Vec::new();

    for &start_sid in shard_by_id.keys() {
        if indices.contains_key(start_sid) {
            continue;
        }
        let start = start_sid.to_owned();
        indices.insert(start.clone(), index_counter);
        lowlink.insert(start.clone(), index_counter);
        index_counter += 1;
        t_stack.push(start.clone());
        on_stack.insert(start.clone());
        let init_neighbors: Vec<String> = union_edges
            .get(start_sid)
            .map(|ns| ns.iter().cloned().collect())
            .unwrap_or_default();
        let mut work_stack: Vec<(String, Vec<String>, usize)> = vec![(start, init_neighbors, 0)];

        while let Some((v, neighbors, idx)) = work_stack.last_mut() {
            if *idx < neighbors.len() {
                let w = neighbors[*idx].clone();
                *idx += 1;
                if !indices.contains_key(&w) {
                    indices.insert(w.clone(), index_counter);
                    lowlink.insert(w.clone(), index_counter);
                    index_counter += 1;
                    t_stack.push(w.clone());
                    on_stack.insert(w.clone());
                    let w_neighbors: Vec<String> = union_edges
                        .get(&w)
                        .map(|ns| ns.iter().cloned().collect())
                        .unwrap_or_default();
                    work_stack.push((w, w_neighbors, 0));
                } else if on_stack.contains(&w) {
                    let iw = indices[&w];
                    if let Some(lv) = lowlink.get_mut(v)
                        && iw < *lv
                    {
                        *lv = iw;
                    }
                }
            } else {
                let (finished_v, _, _) = work_stack.pop().expect("non-empty Tarjan stack");
                if lowlink[&finished_v] == indices[&finished_v] {
                    let mut comp = Vec::new();
                    while let Some(w) = t_stack.pop() {
                        on_stack.remove(&w);
                        let done = w == finished_v;
                        comp.push(w);
                        if done {
                            break;
                        }
                    }
                    comp.sort();
                    sccs.push(comp);
                }
                if let Some((parent_v, _, _)) = work_stack.last() {
                    let child_low = lowlink[&finished_v];
                    if let Some(plv) = lowlink.get_mut(parent_v)
                        && child_low < *plv
                    {
                        *plv = child_low;
                    }
                }
            }
        }
    }

    // Tarjan emits reverse topological order (callees BEFORE callers)!
    let mut results: Vec<VerifiedShardSummary> = Vec::with_capacity(sccs.len());
    let mut by_id: HashMap<String, VerifiedShardSummary> = HashMap::new();

    for (rank, comp) in sccs.into_iter().enumerate() {
        if comp.len() > 1 {
            return Err(Failure::policy(
                phase,
                format!(
                    "cyclic modular shard dependency in union graph: [{}]",
                    comp.join(", ")
                ),
            ));
        }
        let sid = &comp[0];
        if union_edges[sid].contains(sid) {
            return Err(Failure::policy(
                phase,
                format!("self-referential modular shard dependency on `{sid}`"),
            ));
        }

        let node = shard_by_id[sid.as_str()];
        let mut axioms = node.local_axioms.clone();
        if let Some(ta) = theory_axioms_by_shard.get(sid) {
            axioms.extend(ta.iter().cloned());
        }
        let mut sorry_declarations = node.local_sorry_declarations.clone();
        let mut taint_reasons = node.local_taint_reasons.clone();
        if let Some(et) = extra_taints.get(sid) {
            taint_reasons.extend(et.iter().cloned());
        }
        let mut model_closure = node.local_model_closure.clone();
        if let Some(tc) = theory_closure_by_shard.get(sid) {
            model_closure.extend(tc.iter().cloned());
        }

        for dep_id in &proof_edges[sid] {
            let dep_sum = &by_id[dep_id];
            axioms.extend(dep_sum.axioms.iter().cloned());
        }
        for dep_id in &union_edges[sid] {
            let dep_sum = &by_id[dep_id];
            sorry_declarations.extend(dep_sum.sorry_declarations.iter().cloned());
            taint_reasons.extend(dep_sum.taint_reasons.iter().cloned());
            model_closure.extend(dep_sum.model_closure.iter().cloned());
        }
        model_closure.sort_by(|a, b| a.name.cmp(&b.name).then_with(|| a.module.cmp(&b.module)));
        model_closure.dedup();

        let sum = VerifiedShardSummary {
            shard_id: sid.clone(),
            topological_rank: rank,
            union_callees: union_edges[sid].clone(),
            axioms,
            sorry_declarations,
            taint_reasons,
            model_closure,
        };
        by_id.insert(sid.clone(), sum.clone());
        results.push(sum);
    }

    Ok(results)
}

/// Cross-check a [`ModularShardNode`]'s `m3_lifted_hypotheses` list directly
/// against the post-M3 outer `ForallE` binder spine of `theorem_name` in a
/// kernel-verified `m3_env` export AND the authoritative contract signatures in
/// `contract_envs` (such as `theory_env` and peer pre-M3/contract exports),
/// ensuring a caller cannot omit, reorder, or substitute hypotheses when
/// constructing [`ModularShardNode`].
pub fn verify_shard_binders_against_m3_env(
    arena: &mut CanonicalArena,
    m3_env: &ExportedEnv,
    contract_envs: &[&ExportedEnv],
    theorem_name: &str,
    expected_declaration: &str,
    lifted_hypotheses: &[LiftedHypothesisRecord],
) -> Result<(), Failure> {
    let phase = "modular-linker";
    if contract_envs.is_empty() && !lifted_hypotheses.is_empty() {
        return Err(Failure::policy(
            phase,
            "contract_envs required to verify non-empty lifted_hypotheses",
        ));
    }
    let thm_id = arena.intern_dotted_name(theorem_name);
    let exp_id = arena.intern_dotted_name(expected_declaration);
    let Some(CanonConstInfo::Thm {
        level_params,
        mut ty,
        ..
    }) = m3_env.constants.get(&thm_id).cloned()
    else {
        return Err(Failure::policy(
            phase,
            format!("missing M3 theorem `{theorem_name}` in verified shard env"),
        ));
    };
    if !level_params.is_empty() {
        return Err(Failure::policy(
            phase,
            format!("M3 theorem `{theorem_name}` must have empty universe parameters"),
        ));
    }
    for hyp in lifted_hypotheses {
        let CanonExpr::ForallE {
            ty: domain_ty,
            body,
        } = arena.exprs[ty.0 as usize]
        else {
            return Err(Failure::policy(
                phase,
                format!(
                    "M3 theorem `{theorem_name}` has fewer outer binders than lifted_hypotheses (`{}`)",
                    hyp.name
                ),
            ));
        };
        if has_loose_bvar_at_least(arena, body, 0) {
            return Err(Failure::policy(
                phase,
                format!(
                    "M3 theorem `{theorem_name}` binder `{}` binds BVar(0) in codomain",
                    hyp.name
                ),
            ));
        }
        let hyp_id = arena.intern_dotted_name(&hyp.name);
        let mut matched_ci: Option<&CanonConstInfo> = None;
        for &src_env in contract_envs {
            if let Some(ci) = src_env.constants.get(&hyp_id) {
                let actual_cone = compute_cone_digest(arena, src_env, hyp_id, phase)?;
                if actual_cone != hyp.cone_merkle_sha256 {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "M3 theorem `{theorem_name}` binder `{}` cone digest mismatch \
                             (expected {}, found {actual_cone})",
                            hyp.name, hyp.cone_merkle_sha256
                        ),
                    ));
                }
                matched_ci = Some(ci);
                break;
            }
        }
        let Some(hyp_ci) = matched_ci else {
            return Err(Failure::policy(
                phase,
                format!(
                    "M3 theorem `{theorem_name}` binder `{}` missing from contract_envs",
                    hyp.name
                ),
            ));
        };
        if !matches!(
            hyp_ci,
            CanonConstInfo::Thm { .. }
                | CanonConstInfo::Axiom {
                    is_unsafe: false,
                    ..
                }
        ) {
            return Err(Failure::policy(
                phase,
                format!(
                    "M3 theorem `{theorem_name}` binder `{}` has invalid contract kind `{}`",
                    hyp.name,
                    hyp_ci.kind_label()
                ),
            ));
        }
        let hyp_lps = hyp_ci.level_params().to_vec();
        let hyp_ty = hyp_ci.ty();
        let mut concrete_us = Vec::with_capacity(hyp.universe_levels.len());
        for u_s in &hyp.universe_levels {
            let lid = parse_rendered_level(arena, u_s, &[], phase)?;
            concrete_us.push(lid);
        }
        let inst_hyp_ty =
            instantiate_level_params_expr(arena, hyp_ty, &hyp_lps, &concrete_us, &[], phase)?;
        let norm_domain_ty = normalize_expr_levels(arena, domain_ty, &[], phase)?;
        if inst_hyp_ty != norm_domain_ty {
            return Err(Failure::policy(
                phase,
                format!(
                    "M3 theorem `{theorem_name}` binder `{}` instantiated type does not match \
                     outer ForallE domain",
                    hyp.name
                ),
            ));
        }
        ty = body;
    }
    let exp_const_expr = arena.intern_expr(CanonExpr::Const(exp_id, Vec::new()));
    let exp_body_opt = match m3_env.constants.get(&exp_id) {
        Some(CanonConstInfo::Defn { value, .. }) => Some(*value),
        _ => None,
    };
    if ty != exp_const_expr && Some(ty) != exp_body_opt {
        return Err(Failure::policy(
            phase,
            format!(
                "M3 theorem `{theorem_name}` residual codomain after {} binders does not match `{expected_declaration}`",
                lifted_hypotheses.len()
            ),
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// 6. Offline Zero-Axiom Stitcher (`Deriv.linkAxioms`)
// ---------------------------------------------------------------------------

/// Input M3-lifted shard export for [`link_m3_shards_to_zero_axioms`].
#[derive(Debug, Clone)]
pub struct M3LinkShardInput {
    pub shard_id: String,
    pub m3_env: ExportedEnv,
    pub theorem_name: String,
    pub expected_declaration: String,
    pub local_modules: BTreeSet<String>,
    pub lifted_hypotheses: Vec<LiftedHypothesisRecord>,
}

/// Output of [`link_m3_shards_to_zero_axioms`].
#[derive(Debug)]
pub struct ZeroAxiomLinkOutcome {
    pub linked_ndjson: String,
    pub linked_env: ExportedEnv,
    pub linked_theorem_name: String,
    pub linked_expected_declaration: String,
    pub axioms: Vec<String>,
}

/// Stitch one or more topologically ordered M3-verified shards with a full
/// zero-axiom `theory_env` (`Deriv.linkAxioms`), producing a single closed
/// `0`-hypothesis, `0`-custom-axiom NDJSON stream checkable by all four
/// external kernels.
pub fn link_m3_shards_to_zero_axioms(
    arena: &mut CanonicalArena,
    init_primitives: Option<&ExportedEnv>,
    theory_env: &ExportedEnv,
    shards: &[M3LinkShardInput],
) -> Result<ZeroAxiomLinkOutcome, Failure> {
    let phase = "zero-axiom-linker";
    if shards.is_empty() {
        return Err(Failure::policy(
            phase,
            "at least one M3 shard is required for linking",
        ));
    }

    let standard_axiom_ids: BTreeSet<CanonNameId> = STANDARD_PERMITTED_AXIOMS
        .iter()
        .map(|n| arena.intern_dotted_name(n))
        .collect();

    // Verify `theory_env` itself contains zero custom axioms, sorryAx, opaque,
    // or unsafe/partial declarations.
    for &cid in &theory_env.const_order {
        let ci = &theory_env.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) || ci.is_unsafe_or_partial() {
            return Err(Failure::policy(
                phase,
                format!(
                    "theory_env contains forbidden declaration `{}`",
                    arena.name_str(cid)
                ),
            ));
        }
        if matches!(ci, CanonConstInfo::Axiom { .. }) && !standard_axiom_ids.contains(&cid) {
            return Err(Failure::policy(
                phase,
                format!(
                    "theory_env contains unpermitted axiom `{}`",
                    arena.name_str(cid)
                ),
            ));
        }
    }

    let mut merged = theory_env.clone();
    // Maps public contract theorem name -> resolved zero-hypothesis
    // `CanonNameId` in `merged`.
    let mut resolved_targets: HashMap<String, CanonNameId> = HashMap::new();
    for &cid in &theory_env.const_order {
        if matches!(
            theory_env.constants.get(&cid),
            Some(CanonConstInfo::Thm { .. })
        ) {
            resolved_targets.insert(arena.name_str(cid).to_owned(), cid);
        }
    }

    let multi_shard = shards.len() > 1;
    let mut last_linked_thm = String::new();
    let mut last_expected_decl = String::new();
    let mut root_ids: Vec<CanonNameId> = Vec::new();

    for shard in shards {
        let rename_map = build_shard_rename_map(arena, shard, &merged, multi_shard);
        let mapped_shard = remap_exported_env(arena, &shard.m3_env, &rename_map, phase)?;

        // Merge `mapped_shard` into `merged`, enforcing strict `decl_digest`
        // (and full `CanonInductiveBlock` digest) equality on shared constants!
        let mut handled_blocks = BTreeSet::new();
        for &cid in &mapped_shard.const_order {
            if let Some(&bidx) = mapped_shard.inductive_blocks.get(&cid) {
                if !handled_blocks.insert(bidx) {
                    continue;
                }
                let blk = &mapped_shard.blocks[bidx];
                let Some(&first_ty) = blk.types.first() else {
                    return Err(Failure::policy(
                        phase,
                        "inductive block has empty types list during shard linking",
                    ));
                };
                if let Some(&existing_bidx) = merged.inductive_blocks.get(&first_ty) {
                    let existing_blk = &merged.blocks[existing_bidx];
                    if blk != existing_blk {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "inductive block member mismatch on `{}` during shard linking",
                                arena.name_str(first_ty)
                            ),
                        ));
                    }
                    let d_new = compute_decl_digest(arena, &mapped_shard, first_ty, phase)?;
                    let d_old = compute_decl_digest(arena, &merged, first_ty, phase)?;
                    if d_new != d_old {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "inductive block Merkle drift on `{}` during shard linking",
                                arena.name_str(first_ty)
                            ),
                        ));
                    }
                } else {
                    for &m in blk
                        .types
                        .iter()
                        .chain(blk.ctors.iter())
                        .chain(blk.recs.iter())
                    {
                        if merged.constants.contains_key(&m) {
                            return Err(Failure::policy(
                                phase,
                                format!(
                                    "partial inductive block collision on `{}`",
                                    arena.name_str(m)
                                ),
                            ));
                        }
                    }
                    let new_bidx = merged.blocks.len();
                    for &m in blk
                        .types
                        .iter()
                        .chain(blk.ctors.iter())
                        .chain(blk.recs.iter())
                    {
                        merged
                            .constants
                            .insert(m, mapped_shard.constants[&m].clone());
                        merged.const_order.push(m);
                        merged.inductive_blocks.insert(m, new_bidx);
                    }
                    merged.blocks.push(blk.clone());
                }
            } else if let Some(existing_ci) = merged.constants.get(&cid) {
                let incoming_ci = &mapped_shard.constants[&cid];
                if existing_ci.kind_label() != incoming_ci.kind_label() {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "shared declaration `{}` kind mismatch ({} vs {})",
                            arena.name_str(cid),
                            existing_ci.kind_label(),
                            incoming_ci.kind_label()
                        ),
                    ));
                }
                if existing_ci != incoming_ci {
                    let d_new = compute_decl_digest(arena, &mapped_shard, cid, phase)?;
                    let d_old = compute_decl_digest(arena, &merged, cid, phase)?;
                    if d_new != d_old {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "shared declaration `{}` Merkle digest mismatch during linking",
                                arena.name_str(cid)
                            ),
                        ));
                    }
                }
            } else {
                merged
                    .constants
                    .insert(cid, mapped_shard.constants[&cid].clone());
                merged.const_order.push(cid);
            }
        }

        let orig_thm_id = arena.intern_dotted_name(&shard.theorem_name);
        let orig_exp_id = arena.intern_dotted_name(&shard.expected_declaration);
        let mapped_thm_id = rename_map.get(&orig_thm_id).copied().unwrap_or(orig_thm_id);
        let mapped_exp_id = rename_map.get(&orig_exp_id).copied().unwrap_or(orig_exp_id);

        let Some(CanonConstInfo::Thm {
            level_params,
            ty: mut cur_ty,
            ..
        }) = merged.constants.get(&mapped_thm_id).cloned()
        else {
            return Err(Failure::policy(
                phase,
                format!(
                    "shard `{}` missing M3 theorem `{}`",
                    shard.shard_id, shard.theorem_name
                ),
            ));
        };
        if !level_params.is_empty() {
            return Err(Failure::policy(
                phase,
                format!(
                    "shard `{}` theorem must be universe-monomorphic",
                    shard.shard_id
                ),
            ));
        }

        let mut app_val = arena.intern_expr(CanonExpr::Const(mapped_thm_id, Vec::new()));
        for hyp in &shard.lifted_hypotheses {
            let CanonExpr::ForallE {
                ty: domain_ty,
                body: next_ty,
            } = arena.exprs[cur_ty.0 as usize].clone()
            else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` theorem lacks outer ForallE binder for `{}`",
                        shard.shard_id, hyp.name
                    ),
                ));
            };
            if has_loose_bvar_at_least(arena, next_ty, 0) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` outer M3 binder for `{}` unexpectedly binds BVar(0) in codomain",
                        shard.shard_id, hyp.name
                    ),
                ));
            }
            let Some(&target_id) = resolved_targets.get(&hyp.name) else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` hypothesis `{}` missing from zero-axiom link environment",
                        shard.shard_id, hyp.name
                    ),
                ));
            };
            let Some(CanonConstInfo::Thm {
                level_params: target_lps,
                ty: target_ty,
                ..
            }) = merged.constants.get(&target_id).cloned()
            else {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "resolved target `{}` is not a theorem",
                        arena.name_str(target_id)
                    ),
                ));
            };
            let mut concrete_us = Vec::with_capacity(hyp.universe_levels.len());
            for u_s in &hyp.universe_levels {
                let lid = parse_rendered_level(arena, u_s, &[], phase)?;
                concrete_us.push(lid);
            }
            let inst_target_ty = instantiate_level_params_expr(
                arena,
                target_ty,
                &target_lps,
                &concrete_us,
                &[],
                phase,
            )?;
            let norm_domain_ty = normalize_expr_levels(arena, domain_ty, &[], phase)?;
            if inst_target_ty != norm_domain_ty {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "shard `{}` hypothesis `{}` instantiated type does not match outer binder domain",
                        shard.shard_id, hyp.name
                    ),
                ));
            }
            let arg_expr = arena.intern_expr(CanonExpr::Const(target_id, concrete_us));
            app_val = arena.intern_expr(CanonExpr::App(app_val, arg_expr));
            cur_ty = next_ty;
        }

        // Verify final `cur_ty` matches `mapped_exp_id` or its body!
        let exp_const_expr = arena.intern_expr(CanonExpr::Const(mapped_exp_id, Vec::new()));
        let exp_body_opt = match merged.constants.get(&mapped_exp_id) {
            Some(CanonConstInfo::Defn { value, .. }) => Some(*value),
            _ => None,
        };
        if cur_ty != exp_const_expr && Some(cur_ty) != exp_body_opt {
            return Err(Failure::policy(
                phase,
                format!(
                    "shard `{}` linked theorem type does not match `{}`",
                    shard.shard_id,
                    arena.name_str(mapped_exp_id)
                ),
            ));
        }

        let linked_name_str = format!("{}_linked", arena.name_str(mapped_thm_id));
        let linked_id = arena.intern_dotted_name(&linked_name_str);
        if merged.constants.contains_key(&linked_id) {
            return Err(Failure::policy(
                phase,
                format!("duplicate linked theorem name `{linked_name_str}`"),
            ));
        }
        merged.constants.insert(
            linked_id,
            CanonConstInfo::Thm {
                name: linked_id,
                level_params: Vec::new(),
                ty: cur_ty,
                value: app_val,
                all: vec![linked_id],
            },
        );
        merged.const_order.push(linked_id);

        // Register BOTH original `shard.theorem_name` and `mapped_thm_id` so
        // downstream caller shards resolve their callee hypothesis seamlessly!
        resolved_targets.insert(shard.theorem_name.clone(), linked_id);
        resolved_targets.insert(arena.name_str(mapped_thm_id).to_owned(), linked_id);

        last_linked_thm = linked_name_str;
        last_expected_decl = arena.name_str(mapped_exp_id).to_owned();
        root_ids.clear();
        root_ids.push(mapped_exp_id);
        root_ids.push(linked_id);
    }

    let (linked_ndjson, linked_env) =
        emit_ndjson(arena, &merged, init_primitives, &root_ids, phase)?;

    // Final zero-custom-axiom, opacity, safety, and sorryAx audit over
    // `linked_env`.
    let sorry_ax_id = arena.intern_dotted_name("sorryAx");
    let mut axioms = BTreeSet::new();
    for &cid in &linked_env.const_order {
        let ci = &linked_env.constants[&cid];
        if matches!(ci, CanonConstInfo::Opaque { .. }) || ci.is_unsafe_or_partial() {
            return Err(Failure::policy(
                phase,
                format!(
                    "forbidden opaque/unsafe/partial declaration `{}` in linked zero-axiom env",
                    arena.name_str(cid)
                ),
            ));
        }
        if cid == sorry_ax_id {
            return Err(Failure::policy(
                phase,
                "sorryAx forbidden in linked zero-axiom env",
            ));
        }
        if let CanonConstInfo::Axiom { .. } = ci {
            if !standard_axiom_ids.contains(&cid) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unpermitted axiom `{}` survived offline zero-axiom linking",
                        arena.name_str(cid)
                    ),
                ));
            }
            axioms.insert(arena.name_str(cid).to_owned());
        }
    }

    Ok(ZeroAxiomLinkOutcome {
        linked_ndjson,
        linked_env,
        linked_theorem_name: last_linked_thm,
        linked_expected_declaration: last_expected_decl,
        axioms: axioms.into_iter().collect(),
    })
}

fn has_loose_bvar_at_least(arena: &CanonicalArena, root: CanonExprId, min_bvar: u64) -> bool {
    let mut memo: HashMap<(CanonExprId, u64), bool> = HashMap::new();
    let mut stack = vec![(root, min_bvar, false)];
    while let Some((eid, cutoff, done)) = stack.pop() {
        if memo.contains_key(&(eid, cutoff)) {
            continue;
        }
        if !done {
            stack.push((eid, cutoff, true));
            match &arena.exprs[eid.0 as usize] {
                CanonExpr::BVar(_)
                | CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => {}
                CanonExpr::App(f, a) => {
                    stack.push((*f, cutoff, false));
                    stack.push((*a, cutoff, false));
                }
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    stack.push((*ty, cutoff, false));
                    stack.push((*body, cutoff + 1, false));
                }
                CanonExpr::LetE { ty, value, body } => {
                    stack.push((*ty, cutoff, false));
                    stack.push((*value, cutoff, false));
                    stack.push((*body, cutoff + 1, false));
                }
                CanonExpr::Proj { struct_expr, .. } => stack.push((*struct_expr, cutoff, false)),
            }
        } else {
            let res = match &arena.exprs[eid.0 as usize] {
                CanonExpr::BVar(i) => *i >= cutoff,
                CanonExpr::Sort(_)
                | CanonExpr::Const(_, _)
                | CanonExpr::NatLit(_)
                | CanonExpr::StrLit(_) => false,
                CanonExpr::App(f, a) => memo[&(*f, cutoff)] || memo[&(*a, cutoff)],
                CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                    memo[&(*ty, cutoff)] || memo[&(*body, cutoff + 1)]
                }
                CanonExpr::LetE { ty, value, body } => {
                    memo[&(*ty, cutoff)] || memo[&(*value, cutoff)] || memo[&(*body, cutoff + 1)]
                }
                CanonExpr::Proj { struct_expr, .. } => memo[&(*struct_expr, cutoff)],
            };
            memo.insert((eid, cutoff), res);
        }
    }
    memo[&(root, min_bvar)]
}

fn build_shard_rename_map(
    arena: &mut CanonicalArena,
    shard: &M3LinkShardInput,
    merged: &ExportedEnv,
    multi_shard: bool,
) -> HashMap<CanonNameId, CanonNameId> {
    let mut map = HashMap::new();
    if !multi_shard || shard.local_modules.is_empty() {
        return map;
    }
    let orig_exp_id = arena.intern_dotted_name(&shard.expected_declaration);
    let exp_cone = bfs_cone(arena, &shard.m3_env, &[orig_exp_id]).visited;
    let exp_cone_collides = exp_cone.iter().any(|&cid| {
        shard
            .local_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m))
            && merged
                .constants
                .get(&cid)
                .is_some_and(|existing| Some(existing) != shard.m3_env.constants.get(&cid))
    });

    let prefix_base = arena.intern_dotted_name(&format!("AnnealLinked.{}", shard.shard_id));
    for &cid in &shard.m3_env.const_order {
        let is_local = shard
            .local_modules
            .iter()
            .any(|m| arena.belongs_to_module(cid, m));
        if is_local && (!exp_cone.contains(&cid) || exp_cone_collides) {
            let renamed = prepend_name_prefix(arena, prefix_base, cid);
            map.insert(cid, renamed);
        }
    }
    map
}

fn prepend_name_prefix(
    arena: &mut CanonicalArena,
    prefix: CanonNameId,
    orig: CanonNameId,
) -> CanonNameId {
    let mut segs = Vec::new();
    let mut cur = orig;
    loop {
        match arena.names[cur.0 as usize].clone() {
            CanonName::Anonymous => break,
            CanonName::Str(pre, s) => {
                segs.push((false, s, 0u64));
                cur = pre;
            }
            CanonName::Num(pre, n) => {
                segs.push((true, String::new(), n));
                cur = pre;
            }
        }
    }
    let mut out = prefix;
    for (is_num, s, n) in segs.into_iter().rev() {
        out = if is_num {
            arena.intern_name(CanonName::Num(out, n))
        } else {
            arena.intern_name(CanonName::Str(out, s))
        };
    }
    out
}

fn remap_exported_env(
    arena: &mut CanonicalArena,
    env: &ExportedEnv,
    rename_map: &HashMap<CanonNameId, CanonNameId>,
    phase: &str,
) -> Result<ExportedEnv, Failure> {
    if rename_map.is_empty() {
        return Ok(env.clone());
    }
    let map_n = |id: CanonNameId| -> CanonNameId { rename_map.get(&id).copied().unwrap_or(id) };
    let mut e_memo: HashMap<CanonExprId, CanonExprId> = HashMap::new();
    let map_e = |arena: &mut CanonicalArena,
                 root: CanonExprId,
                 e_memo: &mut HashMap<CanonExprId, CanonExprId>|
     -> CanonExprId {
        let mut stack = vec![(root, false)];
        while let Some((eid, done)) = stack.pop() {
            if e_memo.contains_key(&eid) {
                continue;
            }
            let node = arena.exprs[eid.0 as usize].clone();
            if !done {
                stack.push((eid, true));
                match &node {
                    CanonExpr::BVar(_)
                    | CanonExpr::Sort(_)
                    | CanonExpr::Const(_, _)
                    | CanonExpr::NatLit(_)
                    | CanonExpr::StrLit(_) => {}
                    CanonExpr::App(f, a) => {
                        stack.push((*f, false));
                        stack.push((*a, false));
                    }
                    CanonExpr::Lam { ty, body } | CanonExpr::ForallE { ty, body } => {
                        stack.push((*ty, false));
                        stack.push((*body, false));
                    }
                    CanonExpr::LetE { ty, value, body } => {
                        stack.push((*ty, false));
                        stack.push((*value, false));
                        stack.push((*body, false));
                    }
                    CanonExpr::Proj { struct_expr, .. } => stack.push((*struct_expr, false)),
                }
            } else {
                let out = match node {
                    CanonExpr::BVar(_)
                    | CanonExpr::Sort(_)
                    | CanonExpr::NatLit(_)
                    | CanonExpr::StrLit(_) => eid,
                    CanonExpr::Const(c, us) => arena.intern_expr(CanonExpr::Const(map_n(c), us)),
                    CanonExpr::App(f, a) => {
                        arena.intern_expr(CanonExpr::App(e_memo[&f], e_memo[&a]))
                    }
                    CanonExpr::Lam { ty, body } => arena.intern_expr(CanonExpr::Lam {
                        ty: e_memo[&ty],
                        body: e_memo[&body],
                    }),
                    CanonExpr::ForallE { ty, body } => arena.intern_expr(CanonExpr::ForallE {
                        ty: e_memo[&ty],
                        body: e_memo[&body],
                    }),
                    CanonExpr::LetE { ty, value, body } => arena.intern_expr(CanonExpr::LetE {
                        ty: e_memo[&ty],
                        value: e_memo[&value],
                        body: e_memo[&body],
                    }),
                    CanonExpr::Proj {
                        type_name,
                        idx,
                        struct_expr,
                    } => arena.intern_expr(CanonExpr::Proj {
                        type_name: map_n(type_name),
                        idx,
                        struct_expr: e_memo[&struct_expr],
                    }),
                };
                e_memo.insert(eid, out);
            }
        }
        e_memo[&root]
    };

    let mut constants = HashMap::with_capacity(env.constants.len());
    let mut const_order = Vec::with_capacity(env.const_order.len());
    for &cid in &env.const_order {
        let ncid = map_n(cid);
        if constants.contains_key(&ncid) {
            return Err(Failure::policy(
                phase,
                format!("shard rename collision on `{}`", arena.name_str(ncid)),
            ));
        }
        let nci = match env.constants[&cid].clone() {
            CanonConstInfo::Axiom {
                level_params,
                ty,
                is_unsafe,
                ..
            } => CanonConstInfo::Axiom {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                is_unsafe,
            },
            CanonConstInfo::Quot {
                level_params,
                ty,
                kind,
                ..
            } => CanonConstInfo::Quot {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                kind,
            },
            CanonConstInfo::Defn {
                level_params,
                ty,
                value,
                hints,
                safety,
                all,
                ..
            } => CanonConstInfo::Defn {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                value: map_e(arena, value, &mut e_memo),
                hints,
                safety,
                all: all.into_iter().map(map_n).collect(),
            },
            CanonConstInfo::Thm {
                level_params,
                ty,
                value,
                all,
                ..
            } => CanonConstInfo::Thm {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                value: map_e(arena, value, &mut e_memo),
                all: all.into_iter().map(map_n).collect(),
            },
            CanonConstInfo::Opaque {
                level_params,
                ty,
                value,
                is_unsafe,
                all,
                ..
            } => CanonConstInfo::Opaque {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                value: map_e(arena, value, &mut e_memo),
                is_unsafe,
                all: all.into_iter().map(map_n).collect(),
            },
            CanonConstInfo::Induct {
                level_params,
                ty,
                num_params,
                num_indices,
                all,
                ctors,
                recs,
                num_nested,
                is_rec,
                is_unsafe,
                is_reflexive,
                ..
            } => CanonConstInfo::Induct {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                num_params,
                num_indices,
                all: all.into_iter().map(map_n).collect(),
                ctors: ctors.into_iter().map(map_n).collect(),
                recs: recs.into_iter().map(map_n).collect(),
                num_nested,
                is_rec,
                is_unsafe,
                is_reflexive,
            },
            CanonConstInfo::Ctor {
                level_params,
                ty,
                induct,
                cidx,
                num_params,
                num_fields,
                is_unsafe,
                ..
            } => CanonConstInfo::Ctor {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                induct: map_n(induct),
                cidx,
                num_params,
                num_fields,
                is_unsafe,
            },
            CanonConstInfo::Rec {
                level_params,
                ty,
                all,
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules,
                k,
                is_unsafe,
                ..
            } => CanonConstInfo::Rec {
                name: ncid,
                level_params,
                ty: map_e(arena, ty, &mut e_memo),
                all: all.into_iter().map(map_n).collect(),
                num_params,
                num_indices,
                num_motives,
                num_minors,
                rules: rules
                    .into_iter()
                    .map(|r| RecursorRule {
                        ctor: map_n(r.ctor),
                        nfields: r.nfields,
                        rhs: map_e(arena, r.rhs, &mut e_memo),
                    })
                    .collect(),
                k,
                is_unsafe,
            },
        };
        constants.insert(ncid, nci);
        const_order.push(ncid);
    }

    let mut blocks = Vec::with_capacity(env.blocks.len());
    let mut inductive_blocks = HashMap::new();
    for (bidx, blk) in env.blocks.iter().enumerate() {
        let nblk = CanonInductiveBlock {
            types: blk.types.iter().copied().map(map_n).collect(),
            ctors: blk.ctors.iter().copied().map(map_n).collect(),
            recs: blk.recs.iter().copied().map(map_n).collect(),
        };
        for &m in nblk
            .types
            .iter()
            .chain(nblk.ctors.iter())
            .chain(nblk.recs.iter())
        {
            inductive_blocks.insert(m, bidx);
        }
        blocks.push(nblk);
    }

    Ok(ExportedEnv {
        meta: env.meta.clone(),
        constants,
        const_order,
        blocks,
        inductive_blocks,
    })
}

#[cfg(test)]
mod tests {
    use std::io::BufReader;

    use super::*;
    use crate::ndjson_comparator::parse_ndjson_reader;

    const META: &str = r#"{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"format":{"version":"3.1.0"},"lean":{"githash":"0000000000000000000000000000000000000000","version":"4.35.0"}}}"#;

    fn build_init_ndjson() -> String {
        let mut lines = vec![META.to_owned()];
        let mut next_in = 1u64;
        let mut name_idx: HashMap<String, u64> = HashMap::new();
        let mut ensure_name = |lines: &mut Vec<String>, dotted: &str| -> u64 {
            if let Some(&id) = name_idx.get(dotted) {
                return id;
            }
            let mut cur = 0u64;
            let mut prefix = String::new();
            for seg in dotted.split('.') {
                if !prefix.is_empty() {
                    prefix.push('.');
                }
                prefix.push_str(seg);
                if let Some(&id) = name_idx.get(&prefix) {
                    cur = id;
                } else {
                    let id = next_in;
                    next_in += 1;
                    lines.push(format!(
                        r#"{{"in":{id},"str":{{"pre":{cur},"str":"{seg}"}}}}"#
                    ));
                    name_idx.insert(prefix.clone(), id);
                    cur = id;
                }
            }
            cur
        };

        lines.push(r#"{"ie":0,"sort":0}"#.to_owned());
        lines.push(r#"{"il":1,"succ":0}"#.to_owned());
        lines.push(r#"{"ie":1,"sort":1}"#.to_owned());

        for prim in PINNED_INIT_PRIMITIVES {
            let nid = ensure_name(&mut lines, prim);
            if let Some((_, qkind)) = QUOT_PRIMITIVES.iter().find(|(n, _)| *n == prim) {
                let kind_str = match qkind {
                    QuotKind::Type => "type",
                    QuotKind::Ctor => "ctor",
                    QuotKind::Lift => "lift",
                    QuotKind::Ind => "ind",
                };
                lines.push(format!(
                    r#"{{"quot":{{"kind":"{kind_str}","levelParams":[],"name":{nid},"type":1}}}}"#
                ));
            } else {
                lines.push(format!(
                    r#"{{"def":{{"all":[{nid}],"hints":"abbrev","levelParams":[],"name":{nid},"safety":"safe","type":1,"value":0}}}}"#
                ));
            }
        }
        lines.join("\n") + "\n"
    }

    fn base_expected_and_theory_fixture() -> (String, String, String, String) {
        let init_nd = build_init_ndjson();
        let expected_nd = [
            META,
            r#"{"in":100,"str":{"pre":0,"str":"Trusted"}}"#,
            r#"{"in":101,"str":{"pre":100,"str":"MirSemantics"}}"#,
            r#"{"in":102,"str":{"pre":101,"str":"UnitTheorem"}}"#,
            r#"{"in":103,"str":{"pre":101,"str":"Crate"}}"#,
            r#"{"in":104,"str":{"pre":103,"str":"mk"}}"#,
            r#"{"in":105,"str":{"pre":0,"str":"Captured"}}"#,
            r#"{"in":106,"str":{"pre":105,"str":"program"}}"#,
            r#"{"in":107,"str":{"pre":0,"str":"Spec"}}"#,
            r#"{"in":108,"str":{"pre":107,"str":"specs"}}"#,
            r#"{"in":109,"str":{"pre":0,"str":"Expected"}}"#,
            r#"{"in":110,"str":{"pre":109,"str":"claim"}}"#,
            r#"{"ie":100,"sort":0}"#,
            r#"{"ie":101,"const":{"name":102,"us":[]}}"#,
            r#"{"ie":102,"const":{"name":104,"us":[]}}"#,
            r#"{"ie":103,"const":{"name":106,"us":[]}}"#,
            r#"{"ie":104,"const":{"name":108,"us":[]}}"#,
            r#"{"ie":105,"app":{"arg":103,"fn":102}}"#,
            r#"{"ie":106,"app":{"arg":104,"fn":105}}"#,
            r#"{"ie":107,"app":{"arg":106,"fn":101}}"#,
            r#"{"def":{"all":[102],"hints":"abbrev","levelParams":[],"name":102,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[104],"hints":"abbrev","levelParams":[],"name":104,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[106],"hints":"abbrev","levelParams":[],"name":106,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[108],"hints":"abbrev","levelParams":[],"name":108,"safety":"safe","type":100,"value":100}}"#,
            r#"{"def":{"all":[110],"hints":"abbrev","levelParams":[],"name":110,"safety":"safe","type":100,"value":107}}"#,
        ]
        .join("\n")
            + "\n";

        // `theory_nd` defines inductive `Anneal.MyNat` (with `MyNat.rec`),
        // `def Anneal.UnsatCnf`, `axiom Classical.choice`, `def
        // Trusted.MirSemantics.extra`, and `thm Anneal.sound : Anneal.UnsatCnf`
        // whose PROOF BODY uses `Classical.choice` and
        // `Trusted.MirSemantics.extra`!
        let theory_nd = [
            META,
            r#"{"in":1,"str":{"pre":0,"str":"Anneal"}}"#,
            r#"{"in":2,"str":{"pre":1,"str":"MyNat"}}"#,
            r#"{"in":3,"str":{"pre":2,"str":"z"}}"#,
            r#"{"in":4,"str":{"pre":2,"str":"s"}}"#,
            r#"{"in":5,"str":{"pre":2,"str":"rec"}}"#,
            r#"{"in":6,"str":{"pre":1,"str":"UnsatCnf"}}"#,
            r#"{"in":7,"str":{"pre":1,"str":"sound"}}"#,
            r#"{"in":8,"str":{"pre":0,"str":"Classical"}}"#,
            r#"{"in":9,"str":{"pre":8,"str":"choice"}}"#,
            r#"{"in":10,"str":{"pre":0,"str":"Trusted"}}"#,
            r#"{"in":11,"str":{"pre":10,"str":"MirSemantics"}}"#,
            r#"{"in":12,"str":{"pre":11,"str":"extra"}}"#,
            r#"{"il":1,"succ":0}"#,
            r#"{"ie":0,"sort":0}"#,
            r#"{"ie":1,"sort":1}"#,
            r#"{"ie":2,"const":{"name":2,"us":[]}}"#,
            r#"{"ie":3,"const":{"name":3,"us":[]}}"#,
            r#"{"ie":4,"const":{"name":6,"us":[]}}"#,
            r#"{"ie":5,"const":{"name":9,"us":[]}}"#,
            r#"{"ie":6,"const":{"name":12,"us":[]}}"#,
            r#"{"ie":7,"app":{"fn":5,"arg":6}}"#,
            r#"{"inductive":{"types":[{"name":2,"levelParams":[],"type":1,"numParams":0,"numIndices":0,"all":[2],"ctors":[3,4],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"ctors":[{"name":3,"levelParams":[],"type":2,"induct":2,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false},{"name":4,"levelParams":[],"type":2,"induct":2,"cidx":1,"numParams":0,"numFields":1,"isUnsafe":false}],"recs":[{"name":5,"levelParams":[],"type":0,"all":[2],"numParams":0,"numIndices":0,"numMotives":1,"numMinors":2,"rules":[{"ctor":3,"nfields":0,"rhs":3},{"ctor":4,"nfields":1,"rhs":2}],"k":false,"isUnsafe":false}]}}"#,
            r#"{"axiom":{"name":9,"levelParams":[],"type":0,"isUnsafe":false}}"#,
            r#"{"def":{"all":[12],"hints":"abbrev","levelParams":[],"name":12,"safety":"safe","type":0,"value":0}}"#,
            r#"{"def":{"all":[6],"hints":"abbrev","levelParams":[],"name":6,"safety":"safe","type":0,"value":3}}"#,
            r#"{"thm":{"all":[7],"levelParams":[],"name":7,"type":4,"value":7}}"#,
        ]
        .join("\n")
            + "\n";

        // `proof_nd` merges `expected_nd` + `theory_nd` + `Proof.helper` ->
        // `Proof.verify`.
        let mut proof_lines: Vec<&str> = expected_nd.lines().collect();
        for line in theory_nd.lines().skip(1) {
            proof_lines.push(line);
        }
        proof_lines.extend([
            r#"{"in":50,"str":{"pre":0,"str":"Proof"}}"#,
            r#"{"in":51,"str":{"pre":50,"str":"helper"}}"#,
            r#"{"in":52,"str":{"pre":50,"str":"verify"}}"#,
            r#"{"ie":50,"const":{"name":110,"us":[]}}"#,
            r#"{"ie":51,"const":{"name":7,"us":[]}}"#,
            r#"{"ie":52,"const":{"name":51,"us":[]}}"#,
            r#"{"thm":{"all":[51],"levelParams":[],"name":51,"type":50,"value":51}}"#,
            r#"{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":52}}"#,
        ]);
        let proof_nd = proof_lines.join("\n") + "\n";
        (init_nd, expected_nd, theory_nd, proof_nd)
    }

    fn default_compare_req() -> StructuralCompareRequest<'static> {
        StructuralCompareRequest {
            theorem_name: "Proof.verify",
            expected_declaration: "Expected.claim",
            canonical_root: "Trusted.MirSemantics.UnitTheorem",
            subject_declaration: "Captured.program",
            specification_declaration: "Spec.specs",
            allow_sorry_in_proof: false,
            forbidden_expected_roots: BTreeSet::from(["Anneal".to_owned(), "Proof".to_owned()]),
            forbidden_expected_modules: BTreeSet::from(["Proof".to_owned()]),
            capture_modules: vec!["Captured".to_owned()],
            model_modules: vec!["Trusted.MirSemantics".to_owned()],
            specification_modules: vec!["Spec".to_owned()],
        }
    }

    #[test]
    fn merkle_cone_detects_poc4_def_drift_hints_rec_k_and_rec_rhs_mutations() {
        let (init_nd, expected_nd, theory_nd, proof_nd) = base_expected_and_theory_fixture();
        let mut arena = CanonicalArena::new();
        let init_env =
            parse_ndjson_reader(BufReader::new(init_nd.as_bytes()), &mut arena, "init").unwrap();
        let expected_env = parse_ndjson_reader(
            BufReader::new(expected_nd.as_bytes()),
            &mut arena,
            "expected",
        )
        .unwrap();
        let theory_env =
            parse_ndjson_reader(BufReader::new(theory_nd.as_bytes()), &mut arena, "theory")
                .unwrap();
        let allowlist = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &theory_env,
            &["Anneal".to_owned()],
            &["Trusted.MirSemantics".to_owned()],
            &"a".repeat(64),
        )
        .unwrap();
        let sound_id = arena.intern_dotted_name("Anneal.sound");
        let base_cone = compute_cone_digest(&arena, &theory_env, sound_id, "test").unwrap();
        let base_decl = compute_decl_digest(&arena, &theory_env, sound_id, "test").unwrap();
        assert_eq!(
            allowlist.entries["Anneal.sound"].cone_merkle_sha256,
            base_cone
        );

        // 1. Changing `Anneal.sound`'s proof body (`value: 7 -> 0`) keeps
        // `cone_digest` identical while changing `decl_digest`!
        let alt_body_theory = theory_nd.replace(
            r#"{"thm":{"all":[7],"levelParams":[],"name":7,"type":4,"value":7}}"#,
            r#"{"thm":{"all":[7],"levelParams":[],"name":7,"type":4,"value":0}}"#,
        );
        let alt_env = parse_ndjson_reader(
            BufReader::new(alt_body_theory.as_bytes()),
            &mut arena,
            "alt_theory",
        )
        .unwrap();
        assert_eq!(
            compute_cone_digest(&arena, &alt_env, sound_id, "test").unwrap(),
            base_cone
        );
        assert_ne!(
            compute_decl_digest(&arena, &alt_env, sound_id, "test").unwrap(),
            base_decl
        );

        // 2. PoC-4: Mutate `UnsatCnf` body (`value: 3 -> 0`), `hints` (`abbrev
        // -> opaque`), `RecRule.rhs` (`rhs: 2 -> 3`), and `Rec.k` (`false ->
        // true`) — ALL must fail closed!
        let mutations = [
            (
                "poc4-def-body-drift",
                r#"{"def":{"all":[6],"hints":"abbrev","levelParams":[],"name":6,"safety":"safe","type":0,"value":3}}"#,
                r#"{"def":{"all":[6],"hints":"abbrev","levelParams":[],"name":6,"safety":"safe","type":0,"value":0}}"#,
            ),
            (
                "defn-hints-drift",
                r#"{"def":{"all":[6],"hints":"abbrev","levelParams":[],"name":6,"safety":"safe","type":0,"value":3}}"#,
                r#"{"def":{"all":[6],"hints":"opaque","levelParams":[],"name":6,"safety":"safe","type":0,"value":3}}"#,
            ),
            (
                "rec-rule-rhs-drift",
                r#"{"ctor":4,"nfields":1,"rhs":2}"#,
                r#"{"ctor":4,"nfields":1,"rhs":3}"#,
            ),
            (
                "rec-k-flag-drift",
                r#""k":false,"isUnsafe":false"#,
                r#""k":true,"isUnsafe":false"#,
            ),
        ];
        let req = default_compare_req();
        for (label, from, to) in mutations {
            let tampered = proof_nd.replace(from, to);
            assert_ne!(tampered, proof_nd, "mutation `{label}` must change input");
            let tampered_env =
                parse_ndjson_reader(BufReader::new(tampered.as_bytes()), &mut arena, label)
                    .unwrap();
            let err = verify_ndjson_and_apply_m3(
                &mut arena,
                &init_env,
                &expected_env,
                &tampered_env,
                &"b".repeat(64),
                &req,
                &allowlist,
                false,
            )
            .unwrap_err();
            assert_eq!(err.code, 1, "{label}: {err}");
            assert!(
                err.message.contains("Merkle constant-cone mismatch"),
                "{label}: {err}"
            );
        }

        // 3. Structured `CanonName` segment encoding never collides dotted
        // strings or numeric vs string segments.
        let n_single = arena.intern_name(CanonName::Str(arena.anonymous_name, "a.b".to_owned()));
        let n_two = arena.intern_dotted_name("a.b");
        let n_str0 = arena.intern_name(CanonName::Str(arena.anonymous_name, "0".to_owned()));
        let n_num0 = arena.intern_name(CanonName::Num(arena.anonymous_name, 0));
        let mut b1 = Vec::new();
        let mut b2 = Vec::new();
        encode_canon_name(&arena, n_single, &mut b1);
        encode_canon_name(&arena, n_two, &mut b2);
        assert_ne!(b1, b2);
        let mut b3 = Vec::new();
        let mut b4 = Vec::new();
        encode_canon_name(&arena, n_str0, &mut b3);
        encode_canon_name(&arena, n_num0, &mut b4);
        assert_ne!(b3, b4);
    }

    #[test]
    fn positive_option_b_m3_preserves_poc2_axioms_closure_and_links_offline() {
        let (init_nd, expected_nd, theory_nd, proof_nd) = base_expected_and_theory_fixture();
        let mut arena = CanonicalArena::new();
        let init_env =
            parse_ndjson_reader(BufReader::new(init_nd.as_bytes()), &mut arena, "init").unwrap();
        let expected_env = parse_ndjson_reader(
            BufReader::new(expected_nd.as_bytes()),
            &mut arena,
            "expected",
        )
        .unwrap();
        let theory_env =
            parse_ndjson_reader(BufReader::new(theory_nd.as_bytes()), &mut arena, "theory")
                .unwrap();
        let proof_env =
            parse_ndjson_reader(BufReader::new(proof_nd.as_bytes()), &mut arena, "proof").unwrap();
        let allowlist = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &theory_env,
            &["Anneal".to_owned()],
            &["Trusted.MirSemantics".to_owned()],
            &"a".repeat(64),
        )
        .unwrap();

        let req = default_compare_req();
        let res = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &proof_env,
            &"c".repeat(64),
            &req,
            &allowlist,
            false,
        )
        .unwrap();

        assert_eq!(res.promotion_report.mode, "m3_lambda_lifted");
        assert_eq!(res.promotion_report.lifted_hypotheses.len(), 1);
        assert_eq!(
            res.promotion_report.lifted_hypotheses[0].name,
            "Anneal.sound"
        );
        // PoC-2: `Classical.choice` and `Trusted.MirSemantics.extra` were ONLY
        // in `Anneal.sound`'s proof body (which M3 garbage-collected!), yet
        // both MUST survive in the verdict!
        assert_eq!(res.summary.axioms, vec!["Classical.choice".to_owned()]);
        assert!(
            res.summary
                .model_closure
                .iter()
                .any(|e| e.name == "Trusted.MirSemantics.extra"),
            "inherited model_closure missing: {:?}",
            res.summary.model_closure
        );

        let (_m3_text, m3_env) = res.rewritten_ndjson.expect("rewritten M3 env");
        let sound_id = arena.intern_dotted_name("Anneal.sound");
        assert!(
            !m3_env.constants.contains_key(&sound_id),
            "Anneal.sound must be GC'd"
        );

        // Positive & negative checks for `verify_shard_binders_against_m3_env`!
        verify_shard_binders_against_m3_env(
            &mut arena,
            &m3_env,
            &[&theory_env],
            "Proof.verify",
            "Expected.claim",
            &res.promotion_report.lifted_hypotheses,
        )
        .unwrap();
        let omit_err = verify_shard_binders_against_m3_env(
            &mut arena,
            &m3_env,
            &[&theory_env],
            "Proof.verify",
            "Expected.claim",
            &[],
        )
        .unwrap_err();
        assert_eq!(omit_err.code, 1);
        assert!(omit_err.message.contains("residual codomain"));

        let mut bad_cone_hyps = res.promotion_report.lifted_hypotheses.clone();
        bad_cone_hyps[0].cone_merkle_sha256 = "0".repeat(64);
        let cone_err = verify_shard_binders_against_m3_env(
            &mut arena,
            &m3_env,
            &[&theory_env],
            "Proof.verify",
            "Expected.claim",
            &bad_cone_hyps,
        )
        .unwrap_err();
        assert_eq!(cone_err.code, 1);
        assert!(cone_err.message.contains("cone digest mismatch"));

        // Offline Deriv.linkAxioms zero-axiom stitching (`PoC-7b`)!
        let linked = link_m3_shards_to_zero_axioms(
            &mut arena,
            Some(&init_env),
            &theory_env,
            &[M3LinkShardInput {
                shard_id: "unit0".to_owned(),
                m3_env,
                theorem_name: "Proof.verify".to_owned(),
                expected_declaration: "Expected.claim".to_owned(),
                local_modules: BTreeSet::from(["Proof".to_owned(), "Expected".to_owned()]),
                lifted_hypotheses: res.promotion_report.lifted_hypotheses,
            }],
        )
        .unwrap();
        assert_eq!(linked.linked_theorem_name, "Proof.verify_linked");
        assert_eq!(linked.axioms, vec!["Classical.choice".to_owned()]);
        let re_parsed = parse_ndjson_reader(
            BufReader::new(linked.linked_ndjson.as_bytes()),
            &mut arena,
            "linked",
        )
        .unwrap();
        let linked_id = arena.intern_dotted_name("Proof.verify_linked");
        let exp_id = arena.intern_dotted_name("Expected.claim");
        let exp_const = arena.intern_expr(CanonExpr::Const(exp_id, Vec::new()));
        match &re_parsed.constants[&linked_id] {
            CanonConstInfo::Thm {
                level_params, ty, ..
            } => {
                assert!(level_params.is_empty());
                assert_eq!(*ty, exp_const, "linked theorem must have 0 outer binders");
            }
            other => panic!("unexpected kind: {}", other.kind_label()),
        }
    }

    #[test]
    fn rejects_poc1a_poc1b_poc2_sorry_poc3_and_poc7a_spoofs() {
        let (init_nd, expected_nd, theory_nd, proof_nd) = base_expected_and_theory_fixture();
        let mut arena = CanonicalArena::new();
        let init_env =
            parse_ndjson_reader(BufReader::new(init_nd.as_bytes()), &mut arena, "init").unwrap();
        let expected_env = parse_ndjson_reader(
            BufReader::new(expected_nd.as_bytes()),
            &mut arena,
            "expected",
        )
        .unwrap();
        let theory_env =
            parse_ndjson_reader(BufReader::new(theory_nd.as_bytes()), &mut arena, "theory")
                .unwrap();
        let allowlist = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &theory_env,
            &["Anneal".to_owned()],
            &["Trusted.MirSemantics".to_owned()],
            &"a".repeat(64),
        )
        .unwrap();
        let req = default_compare_req();

        // 1. PoC-1a: custom free-carrier axiom in `theory_env` rejected by
        // allowlist builder.
        let bad_theory_ax = format!(
            "{theory_nd}{}\n{}\n",
            r#"{"in":90,"str":{"pre":1,"str":"freeCarrier"}}"#,
            r#"{"axiom":{"name":90,"levelParams":[],"type":0,"isUnsafe":false}}"#
        );
        let bad_th_env = parse_ndjson_reader(
            BufReader::new(bad_theory_ax.as_bytes()),
            &mut arena,
            "bad_th",
        )
        .unwrap();
        let err = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &bad_th_env,
            &["Anneal".to_owned()],
            &[],
            &"a".repeat(64),
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("Anneal.freeCarrier"), "{err}");

        // 2. PoC-2: `sorryAx` in `theory_env` rejected by allowlist builder.
        let sorry_theory = format!(
            "{theory_nd}{}\n{}\n",
            r#"{"in":91,"str":{"pre":0,"str":"sorryAx"}}"#,
            r#"{"axiom":{"name":91,"levelParams":[],"type":0,"isUnsafe":false}}"#
        );
        let sorry_th_env = parse_ndjson_reader(
            BufReader::new(sorry_theory.as_bytes()),
            &mut arena,
            "sorry_th",
        )
        .unwrap();
        let err = build_promoted_allowlist(
            &mut arena,
            &init_env,
            &sorry_th_env,
            &["Anneal".to_owned()],
            &[],
            &"a".repeat(64),
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("sorryAx"), "{err}");

        // 3. PoC-3: decoy `Anneal.Evil.forged` custom axiom in `proof_nd`
        // rejected fail-closed!
        let poc3_proof = proof_nd.replace(
            r#"{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":52}}"#,
            r#"{"in":60,"str":{"pre":1,"str":"Evil"}}
{"in":61,"str":{"pre":60,"str":"forged"}}
{"ie":60,"const":{"name":61,"us":[]}}
{"axiom":{"name":61,"levelParams":[],"type":50,"isUnsafe":false}}
{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":60}}"#,
        );
        let poc3_env =
            parse_ndjson_reader(BufReader::new(poc3_proof.as_bytes()), &mut arena, "poc3").unwrap();
        let err = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &poc3_env,
            &"d".repeat(64),
            &req,
            &allowlist,
            false,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("Anneal.Evil.forged"), "{err}");

        // 4. PoC-1b: Promoted valueless `Axiom` stub referenced by a
        // computational `Defn` inside `proof_nd` must fail closed (`cannot
        // appear inside computational/expected cone`)!
        let poc1b_proof = proof_nd
            .replace(
                r#"{"thm":{"all":[7],"levelParams":[],"name":7,"type":4,"value":7}}"#,
                r#"{"axiom":{"name":7,"levelParams":[],"type":4,"isUnsafe":false}}"#,
            )
            .replace(
                r#"{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":52}}"#,
                r#"{"in":70,"str":{"pre":50,"str":"compDef"}}
{"ie":70,"const":{"name":70,"us":[]}}
{"def":{"all":[70],"hints":"abbrev","levelParams":[],"name":70,"safety":"safe","type":50,"value":51}}
{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":70}}"#,
            );
        let poc1b_env =
            parse_ndjson_reader(BufReader::new(poc1b_proof.as_bytes()), &mut arena, "poc1b")
                .unwrap();
        let err = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &poc1b_env,
            &"e".repeat(64),
            &req,
            &allowlist,
            false,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(
            err.message
                .contains("cannot appear inside computational/expected cone"),
            "{err}"
        );

        // 5. PoC-7a: Pre-M3 `Proof.verify` spoofing an outer `ForallE` binder
        // (`UnsatCnf -> Expected.claim`) BEFORE M3 runs must be caught by Step
        // 6!
        let spoof_proof = proof_nd.replace(
            r#"{"thm":{"all":[52],"levelParams":[],"name":52,"type":50,"value":52}}"#,
            r#"{"in":80,"str":{"pre":0,"str":"h"}}
{"ie":80,"forallE":{"name":80,"type":4,"body":50,"binderInfo":"default"}}
{"ie":81,"lam":{"name":80,"type":4,"body":52,"binderInfo":"default"}}
{"thm":{"all":[52],"levelParams":[],"name":52,"type":80,"value":81}}"#,
        );
        let spoof_env =
            parse_ndjson_reader(BufReader::new(spoof_proof.as_bytes()), &mut arena, "spoof")
                .unwrap();
        let err = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &spoof_env,
            &"f".repeat(64),
            &req,
            &allowlist,
            false,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("type differs from"), "{err}");

        // 6. Unreached custom `Axiom` and unreached `sorryAx` in `proof_nd`
        // MUST fail closed BEFORE M3 GC even when `Anneal.sound` is lifted!
        let unreached_ax_proof = format!(
            "{proof_nd}{}\n{}\n",
            r#"{"in":85,"str":{"pre":50,"str":"unusedCustomAx"}}"#,
            r#"{"axiom":{"name":85,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        );
        let unreached_ax_env = parse_ndjson_reader(
            BufReader::new(unreached_ax_proof.as_bytes()),
            &mut arena,
            "unreached_ax",
        )
        .unwrap();
        let err = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &unreached_ax_env,
            &"f".repeat(64),
            &req,
            &allowlist,
            false,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("Proof.unusedCustomAx"), "{err}");

        let unreached_sorry_proof = format!(
            "{proof_nd}{}\n{}\n",
            r#"{"in":86,"str":{"pre":0,"str":"sorryAx"}}"#,
            r#"{"axiom":{"name":86,"levelParams":[],"type":0,"isUnsafe":false}}"#,
        );
        let unreached_sorry_env = parse_ndjson_reader(
            BufReader::new(unreached_sorry_proof.as_bytes()),
            &mut arena,
            "unreached_sorry",
        )
        .unwrap();
        let mut sorry_req = req.clone();
        sorry_req.allow_sorry_in_proof = true;
        let err = verify_ndjson_and_apply_m3(
            &mut arena,
            &init_env,
            &expected_env,
            &unreached_sorry_env,
            &"f".repeat(64),
            &sorry_req,
            &allowlist,
            false,
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("unreached sorryAx"), "{err}");

        // 7. Missing `Const` dependency inside `compute_cone_digest` must fail
        // closed rather than being silently filtered out!
        let mut broken_env = theory_env.clone();
        let unsat_id = arena.intern_dotted_name("Anneal.UnsatCnf");
        broken_env.constants.remove(&unsat_id);
        let sound_id = arena.intern_dotted_name("Anneal.sound");
        let err = compute_cone_digest(&arena, &broken_env, sound_id, "test").unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("missing constant"), "{err}");
    }

    #[test]
    fn tarjan_union_scc_rejects_poc5b_and_poc6a_6b_6c_and_accepts_dag() {
        let allowlist = PromotedTheoremAllowlist::empty("0".repeat(64));
        let h_a = "1".repeat(64);
        let h_b = "2".repeat(64);
        let h_c = "3".repeat(64);

        let mk_node =
            |id: &str, thm: &str, cone: &str, mir: &[&str], ind: &[&str], hyps: &[(&str, &str)]| {
                ModularShardNode {
                    shard_id: id.to_owned(),
                    theorem_name: thm.to_owned(),
                    contract_cone_sha256: cone.to_owned(),
                    mir_direct_callees: mir.iter().map(|s| (*s).to_owned()).collect(),
                    indirect_call_provenance: ind.iter().map(|s| (*s).to_owned()).collect(),
                    m3_lifted_hypotheses: hyps
                        .iter()
                        .map(|(n, c)| LiftedHypothesisRecord {
                            name: (*n).to_owned(),
                            universe_levels: Vec::new(),
                            cone_merkle_sha256: (*c).to_owned(),
                            inherited_axioms: Vec::new(),
                        })
                        .collect(),
                    local_axioms: BTreeSet::new(),
                    local_sorry_declarations: BTreeSet::new(),
                    local_taint_reasons: BTreeSet::new(),
                    local_model_closure: Vec::new(),
                }
            };

        // 1. PoC-6a: Direct MIR cycle `f <-> g`.
        let err = verify_modular_shard_dag(
            &[
                mk_node("f", "F.verify", &h_a, &["g"], &[], &[]),
                mk_node("g", "G.verify", &h_b, &["f"], &[], &[]),
            ],
            &allowlist,
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(
            err.message.contains("cyclic modular shard dependency"),
            "{err}"
        );

        // 2. PoC-6b: Zero MIR calls, mutual M3 proof hypotheses `f -> g -> f`
        // (split-brain!).
        let err = verify_modular_shard_dag(
            &[
                mk_node("f", "F.verify", &h_a, &[], &[], &[("G.verify", &h_b)]),
                mk_node("g", "G.verify", &h_b, &[], &[], &[("F.verify", &h_a)]),
            ],
            &allowlist,
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(
            err.message.contains("cyclic modular shard dependency"),
            "{err}"
        );

        // 3. PoC-6c: Landin's knot / indirect callback cycle (`bad -> apply_cb`
        // in MIR, `apply_cb -> bad` via `indirect_call_provenance`, or
        // self-loop `bad -> bad`).
        let err = verify_modular_shard_dag(
            &[
                mk_node("apply_cb", "Apply.verify", &h_a, &[], &["bad"], &[]),
                mk_node(
                    "bad",
                    "Bad.verify",
                    &h_b,
                    &["apply_cb"],
                    &[],
                    &[("Apply.verify", &h_a)],
                ),
            ],
            &allowlist,
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err.code, 1);
        assert!(
            err.message.contains("cyclic modular shard dependency"),
            "{err}"
        );

        let err_self = verify_modular_shard_dag(
            &[mk_node("bad", "Bad.verify", &h_a, &[], &["bad"], &[])],
            &allowlist,
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(err_self.code, 1);
        assert!(err_self.message.contains("self-referential"), "{err_self}");

        // 4. PoC-5b: Assumed external `Total` contract without
        // `AssumedContractRealizable` witness MUST fail closed (`code == 1`)!
        let mut ext_unverified_total = BTreeMap::new();
        ext_unverified_total.insert(
            "Ext.bump_id_spec".to_owned(),
            CalleeContractOrigin::AssumedExternal {
                cone_merkle_sha256: h_c.clone(),
                total_termination: true,
                realizability_witness_verified: false,
            },
        );
        let err_5b = verify_modular_shard_dag(
            &[mk_node(
                "caller",
                "Caller.verify",
                &h_a,
                &[],
                &[],
                &[("Ext.bump_id_spec", &h_c)],
            )],
            &allowlist,
            &ext_unverified_total,
        )
        .unwrap_err();
        assert_eq!(err_5b.code, 1);
        assert!(
            err_5b.message.contains("AssumedContractRealizable"),
            "{err_5b}"
        );

        // 5. Partial / witness-verified assumed external contract succeeds ONLY
        // with mandatory `"assumed_callee_contract"` taint propagated
        // monotonically to callers!
        let mut ext_partial = BTreeMap::new();
        ext_partial.insert(
            "Ext.partial_spec".to_owned(),
            CalleeContractOrigin::AssumedExternal {
                cone_merkle_sha256: h_c.clone(),
                total_termination: false,
                realizability_witness_verified: false,
            },
        );
        let mut s1 = mk_node(
            "s1",
            "S1.verify",
            &h_a,
            &[],
            &[],
            &[("Ext.partial_spec", &h_c)],
        );
        s1.local_axioms.insert("propext".to_owned());
        let s2 = mk_node(
            "s2",
            "S2.verify",
            &h_b,
            &["s1"],
            &[],
            &[("S1.verify", &h_a)],
        );
        let dag = verify_modular_shard_dag(&[s2, s1], &allowlist, &ext_partial).unwrap();
        assert_eq!(dag.len(), 2);
        assert_eq!(dag[0].shard_id, "s1");
        assert_eq!(dag[1].shard_id, "s2");
        assert!(dag[0].taint_reasons.contains("assumed_callee_contract"));
        assert!(dag[1].taint_reasons.contains("assumed_callee_contract"));
        assert!(dag[1].axioms.contains("propext"));

        // 6. Collisions with `theory_allowlist` are rejected fail-closed, and
        // `theory_allowlist` axioms + `model_closure` propagate automatically!
        let mut th_allow = PromotedTheoremAllowlist::empty("0".repeat(64));
        th_allow.entries.insert(
            "Anneal.ClassicalEm.prop_em".to_owned(),
            PromotedTheoremEntry {
                name: "Anneal.ClassicalEm.prop_em".to_owned(),
                module: "Anneal.ClassicalEm".to_owned(),
                num_level_params: 0,
                cone_merkle_sha256: h_c.clone(),
                used_foundation_axioms: vec!["Classical.choice".to_owned()],
                model_closure: vec![ClosureEntry {
                    name: "Trusted.MirSemantics.step".to_owned(),
                    module: "Trusted.MirSemantics".to_owned(),
                }],
            },
        );
        let collide_err = verify_modular_shard_dag(
            &[mk_node(
                "evil",
                "Anneal.ClassicalEm.prop_em",
                &h_c,
                &[],
                &[],
                &[],
            )],
            &th_allow,
            &BTreeMap::new(),
        )
        .unwrap_err();
        assert_eq!(collide_err.code, 1);
        assert!(
            collide_err
                .message
                .contains("collides with theory_allowlist")
        );

        let dag_th = verify_modular_shard_dag(
            &[mk_node(
                "u0",
                "U0.verify",
                &h_a,
                &[],
                &[],
                &[("Anneal.ClassicalEm.prop_em", &h_c)],
            )],
            &th_allow,
            &BTreeMap::new(),
        )
        .unwrap();
        assert!(dag_th[0].axioms.contains("Classical.choice"));
        assert!(
            dag_th[0]
                .model_closure
                .iter()
                .any(|c| c.name == "Trusted.MirSemantics.step")
        );
    }
}
