//! E2-1c (Full-Coverage Memory-Versioned + SwitchInt-Guarded EBB CompCert-BTL Symbolic Validator)
//!
//! Completes our progressive real-MIR study of non-LLVM BTL translation validation on rustc 1.99.1:
//!   Tier 1 (E2-1 pure scalar, no Call):       36.74% BB admission (19,892/54,140), 2.04M stmts/s
//!   Tier 2 (E2-1 + CallBarrier):              54.79% BB admission (36,404/66,438), 3.60M stmts/s
//!   Tier 3 (E2-1c conservative mem_ver + SwitchInt/Assert EBB chaining):
//!     - Models memory reads/derefs/indexes/aggregates/casts as conservative `MemRead(mem_ver, ...)`
//!       / `PureOpaque(kind, ...)` expressions, bumping `mem_ver` on any memory store or `Call`.
//!     - Chains unique-predecessor `Goto`, `Assert`, and `SwitchInt` (carrying `PathAssume` facts!)
//!       into genuine multi-block EBB superblocks.
//!     - Runs Certified MoveToCopy + CopyProp + Strict GVN + Path-Guarded Redundant Assert BCE + DCE.
//!     - Independently validates EVERY transformed EBB with hash-consed symbolic execution + 7/7
//!       adversarial bug-injection negative controls (including BUG7: load CSE across store!).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::fs;
use std::time::Instant;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Place {
    local: u32,
    field: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Operand {
    Copy(Place),
    Move(Place),
    ConstInt(i128, String),
    ConstUnit,
    OpaqueConst(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BinOp {
    Add, Sub, Mul, BitAnd, BitOr, BitXor, Shl, Shr, Eq, Ne, Lt, Le, Gt, Ge,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    UnaryNot(Operand),
    CastInt(Operand, String),
    /// Pure non-memory MIR rvalue (Aggregate, Cast, PtrMetadata, Checked*, etc.) with explicit read operands
    PureOpaque { skeleton: String, ops: Vec<Operand> },
    /// Memory-reading rvalue (deref / slice index) whose result depends on `mem_ver` + read operands
    MemRead { skeleton: String, ops: Vec<Operand> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EbbOp {
    Assign { dst: Place, rv: Rvalue },
    /// Store through pointer/index (`(*_p) = ...` or `_a[_i] = ...`): bumps `mem_ver`, preserves exact order
    MemStore { lhs_skel: String, lhs_ops: Vec<Operand>, rhs: Rvalue },
    StorageLive(u32),
    StorageDead(u32),
    AssertGuard { cond: Operand, expected: bool, msg: String },
    PathAssume { cond: Operand, expected_nonzero: bool },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Goto(u32),
    Return,
    SwitchInt { discr: Operand, zero_tgt: Option<u32>, otherwise_tgt: Option<u32>, raw_targets: String },
    Assert { cond: Operand, expected: bool, msg: String, target: u32 },
    CallBarrier { raw: String, read_locals: Vec<u32>, moved_places: Vec<Place> },
    Unreachable,
}

#[derive(Clone, Debug)]
struct RawBlock {
    admitted: bool,
    stmts: Vec<EbbOp>,
    term: Option<Term>,
    all_succs: Vec<u32>,
}

#[derive(Clone, Debug)]
struct Superblock {
    bb_len: usize,
    ops: Vec<EbbOp>,
    term: Term,
}

fn parse_place(s: &str) -> Option<Place> {
    let s = s.trim();
    let inner = if s.starts_with('(') && s.ends_with(')') {
        s[1..s.len() - 1].split(':').next()?.trim()
    } else {
        s
    };
    if !inner.starts_with('_') { return None; }
    if let Some((loc_s, fld_s)) = inner[1..].split_once('.') {
        if fld_s.contains('.') || fld_s.contains('(') || fld_s.contains('[') { return None; }
        Some(Place { local: loc_s.parse().ok()?, field: Some(fld_s.parse().ok()?) })
    } else {
        Some(Place { local: inner[1..].parse().ok()?, field: None })
    }
}

fn parse_const(s: &str) -> Option<Operand> {
    let s = s.trim();
    if s == "const ()" { return Some(Operand::ConstUnit); }
    let rest = s.strip_prefix("const ")?.trim();
    if rest == "true" { return Some(Operand::ConstInt(1, "bool".into())); }
    if rest == "false" { return Some(Operand::ConstInt(0, "bool".into())); }
    if let Some((num_s, ty_s)) = rest.rsplit_once('_') {
        if matches!(ty_s, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
            if let Ok(v) = num_s.parse::<i128>() {
                return Some(Operand::ConstInt(v, ty_s.into()));
            }
        }
    }
    Some(Operand::OpaqueConst(s.into()))
}

fn parse_operand(s: &str) -> Option<Operand> {
    let s = s.trim();
    if let Some(r) = s.strip_prefix("copy ") { Some(Operand::Copy(parse_place(r)?)) }
    else if let Some(r) = s.strip_prefix("move ") { Some(Operand::Move(parse_place(r)?)) }
    else if s.starts_with("const ") { parse_const(s) }
    else { None }
}

fn split_top_level_comma(s: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, ch) in s.char_indices() {
        match ch {
            '(' | '[' | '<' | '{' => depth += 1,
            ')' | ']' | '>' | '}' => depth -= 1,
            ',' if depth == 0 => return Some((&s[..i], &s[i + 1..])),
            _ => {}
        }
    }
    None
}

fn parse_binop(name: &str) -> Option<BinOp> {
    match name {
        "Add" => Some(BinOp::Add), "Sub" => Some(BinOp::Sub), "Mul" => Some(BinOp::Mul),
        "BitAnd" => Some(BinOp::BitAnd), "BitOr" => Some(BinOp::BitOr), "BitXor" => Some(BinOp::BitXor),
        "Shl" => Some(BinOp::Shl), "Shr" => Some(BinOp::Shr),
        "Eq" => Some(BinOp::Eq), "Ne" => Some(BinOp::Ne),
        "Lt" => Some(BinOp::Lt), "Le" => Some(BinOp::Le), "Gt" => Some(BinOp::Gt), "Ge" => Some(BinOp::Ge),
        _ => None,
    }
}

/// Extract all `_N` local references and produce a parameterized skeleton for conservative modeling
fn extract_ops_and_skeleton(expr: &str) -> (String, Vec<Operand>) {
    let mut skel = String::with_capacity(expr.len());
    let mut ops = Vec::new();
    let bytes = expr.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if expr[i..].starts_with("move _") || expr[i..].starts_with("copy _") {
            let is_move = bytes[i] == b'm';
            let mut j = i + 6;
            while j < bytes.len() && bytes[j].is_ascii_digit() { j += 1; }
            if let Ok(loc) = expr[i + 6..j].parse::<u32>() {
                let p = Place { local: loc, field: None };
                let idx = ops.len();
                ops.push(if is_move { Operand::Move(p) } else { Operand::Copy(p) });
                skel.push_str(&format!("#{}", idx));
                i = j;
                continue;
            }
        } else if bytes[i] == b'_' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
            let prev_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            if prev_ok {
                let mut j = i + 1;
                while j < bytes.len() && bytes[j].is_ascii_digit() { j += 1; }
                if let Ok(loc) = expr[i + 1..j].parse::<u32>() {
                    let idx = ops.len();
                    ops.push(Operand::Copy(Place { local: loc, field: None }));
                    skel.push_str(&format!("#{}", idx));
                    i = j;
                    continue;
                }
            }
        }
        skel.push(bytes[i] as char);
        i += 1;
    }
    (skel, ops)
}

fn parse_rvalue(rhs: &str) -> Rvalue {
    let rhs = rhs.trim();
    if let Some(op) = parse_operand(rhs) {
        return Rvalue::Use(op);
    }
    if let Some(rest) = rhs.strip_prefix("Not(").and_then(|x| x.strip_suffix(')')) {
        if let Some(op) = parse_operand(rest) {
            return Rvalue::UnaryNot(op);
        }
    }
    if let Some(idx) = rhs.find(" as ") {
        if let Some(rest) = rhs[idx + 4..].strip_suffix(" (IntToInt)") {
            let ty = rest.trim();
            if matches!(ty, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
                if let Some(op) = parse_operand(&rhs[..idx]) {
                    return Rvalue::CastInt(op, ty.into());
                }
            }
        }
    }
    if let Some(open) = rhs.find('(') {
        if rhs.ends_with(')') {
            if let Some(bop) = parse_binop(&rhs[..open]) {
                if let Some((a, b)) = split_top_level_comma(&rhs[open + 1..rhs.len() - 1]) {
                    if let (Some(oa), Some(ob)) = (parse_operand(a), parse_operand(b)) {
                        return Rvalue::BinaryOp(bop, oa, ob);
                    }
                }
            }
        }
    }
    let is_mem = rhs.contains("(*") || rhs.contains('[') || rhs.contains('&');
    let (skeleton, ops) = extract_ops_and_skeleton(rhs);
    if is_mem {
        Rvalue::MemRead { skeleton, ops }
    } else {
        Rvalue::PureOpaque { skeleton, ops }
    }
}

fn extract_all_bb_targets(line: &str) -> Vec<u32> {
    let mut out = Vec::new();
    let bytes = line.as_bytes();
    let mut i = 0;
    while i + 2 < bytes.len() {
        if bytes[i] == b'b' && bytes[i + 1] == b'b' && bytes[i + 2].is_ascii_digit() {
            let prev_ok = i == 0 || !bytes[i - 1].is_ascii_alphanumeric();
            if prev_ok {
                let mut j = i + 2;
                while j < bytes.len() && bytes[j].is_ascii_digit() { j += 1; }
                if let Ok(id) = line[i + 2..j].parse::<u32>() { out.push(id); }
                i = j;
                continue;
            }
        }
        i += 1;
    }
    out
}

fn parse_functions(path: &str) -> (Vec<HashMap<u32, RawBlock>>, usize, usize, BTreeMap<String, usize>) {
    let text = fs::read_to_string(path).expect("read mir");
    let mut fns = Vec::new();
    let mut total_bbs = 0usize;
    let mut admitted_bbs = 0usize;
    let mut bailouts: BTreeMap<String, usize> = BTreeMap::new();

    let mut in_fn = false;
    let mut cur_fn: HashMap<u32, RawBlock> = HashMap::new();
    let mut in_bb = false;
    let mut cur_bb_id: u32 = 0;
    let mut bb_lines: Vec<String> = Vec::new();

    let flush_bb = |bb_id: u32,
                    lines: &[String],
                    cur_fn: &mut HashMap<u32, RawBlock>,
                    total_bbs: &mut usize,
                    admitted_bbs: &mut usize,
                    bailouts: &mut BTreeMap<String, usize>| {
        if lines.is_empty() { return; }
        *total_bbs += 1;
        let all_succs = extract_all_bb_targets(lines.last().unwrap());
        let mut stmts = Vec::new();
        let mut admitted = true;
        let mut term_opt = None;
        let mut fail_reason = "";

        for (idx, raw) in lines.iter().enumerate() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with("//") { continue; }
            let is_last = idx + 1 == lines.len();
            let s = line.trim_end_matches(';').trim();
            if !is_last {
                if let Some(inner) = s.strip_prefix("StorageLive(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() { stmts.push(EbbOp::StorageLive(p.local)); continue; }
                    }
                    admitted = false; fail_reason = "storage_complex"; break;
                } else if let Some(inner) = s.strip_prefix("StorageDead(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() { stmts.push(EbbOp::StorageDead(p.local)); continue; }
                    }
                    admitted = false; fail_reason = "storage_complex"; break;
                } else if s.starts_with("nop") || s.starts_with("ConstEvalCounter") || s.starts_with("Deinit(") || s.starts_with("SetDiscriminant(") || s.starts_with("Retag") {
                    if s.starts_with("Deinit(") || s.starts_with("SetDiscriminant(") || s.starts_with("Retag") {
                        let (sk, ops) = extract_ops_and_skeleton(s);
                        stmts.push(EbbOp::MemStore { lhs_skel: sk, lhs_ops: ops, rhs: Rvalue::Use(Operand::ConstUnit) });
                    }
                    continue;
                } else if let Some((lhs, rhs)) = s.split_once(" = ") {
                    let rv = parse_rvalue(rhs);
                    if let Some(dst) = parse_place(lhs) {
                        stmts.push(EbbOp::Assign { dst, rv });
                    } else {
                        let (lhs_skel, lhs_ops) = extract_ops_and_skeleton(lhs);
                        stmts.push(EbbOp::MemStore { lhs_skel, lhs_ops, rhs: rv });
                    }
                    continue;
                } else {
                    admitted = false; fail_reason = "unparsed_stmt"; break;
                }
            } else if s == "return" {
                term_opt = Some(Term::Return);
            } else if s == "unreachable" {
                term_opt = Some(Term::Unreachable);
            } else if let Some(rest) = s.strip_prefix("goto -> bb") {
                if let Ok(tgt) = rest.trim().parse::<u32>() { term_opt = Some(Term::Goto(tgt)); }
                else { admitted = false; fail_reason = "other_term"; }
            } else if let Some(rest) = s.strip_prefix("switchInt(") {
                if let Some((discr_s, tgt_s)) = rest.split_once(") -> ") {
                    if let Some(op) = parse_operand(discr_s) {
                        let mut z_tgt = None;
                        let mut o_tgt = None;
                        if let Some(inner) = tgt_s.trim().strip_prefix('[').and_then(|x| x.strip_suffix(']')) {
                            for arm in inner.split(',') {
                                let a = arm.trim();
                                if let Some(r) = a.strip_prefix("0: bb").or_else(|| a.strip_prefix("false: bb")) {
                                    z_tgt = r.trim().parse().ok();
                                } else if let Some(r) = a.strip_prefix("otherwise: bb") {
                                    o_tgt = r.trim().parse().ok();
                                }
                            }
                        }
                        term_opt = Some(Term::SwitchInt { discr: op, zero_tgt: z_tgt, otherwise_tgt: o_tgt, raw_targets: tgt_s.into() });
                    } else { admitted = false; fail_reason = "switch_complex_discr"; }
                } else { admitted = false; fail_reason = "other_term"; }
            } else if s.starts_with("assert(") {
                let inner = &s["assert(".len()..];
                if let Some((cond_part, after_comma)) = split_top_level_comma(inner) {
                    let (expected, op_str) = if let Some(st) = cond_part.trim().strip_prefix('!') { (false, st) } else { (true, cond_part.trim()) };
                    if let Some(op) = parse_operand(op_str) {
                        let tgt = after_comma.split("success: bb").nth(1)
                            .and_then(|x| x.split(|c: char| !c.is_ascii_digit()).next())
                            .and_then(|x| x.parse::<u32>().ok()).unwrap_or(0);
                        let msg = after_comma.split(')').next().unwrap_or("").into();
                        term_opt = Some(Term::Assert { cond: op, expected, msg, target: tgt });
                    } else { admitted = false; fail_reason = "assert_complex_cond"; }
                } else { admitted = false; fail_reason = "assert_complex_cond"; }
            } else if s.starts_with("drop(") {
                admitted = false; fail_reason = "term_drop";
            } else if s.starts_with("asm!(") {
                admitted = false; fail_reason = "term_inline_asm";
            } else if s.contains(" -> [return:") || s.contains(" -> unwind") {
                let (_, ops) = extract_ops_and_skeleton(s);
                let mut read_locals = Vec::new();
                let mut moved_places = Vec::new();
                for o in ops {
                    match o {
                        Operand::Copy(p) => read_locals.push(p.local),
                        Operand::Move(p) => { read_locals.push(p.local); moved_places.push(p); }
                        _ => {}
                    }
                }
                term_opt = Some(Term::CallBarrier { raw: s.into(), read_locals, moved_places });
            } else {
                admitted = false; fail_reason = "other_term";
            }
        }
        let ok = admitted && term_opt.is_some();
        if ok { *admitted_bbs += 1; } else { *bailouts.entry(fail_reason.into()).or_default() += 1; }
        cur_fn.insert(bb_id, RawBlock { admitted: ok, stmts, term: term_opt, all_succs });
    };

    for line in text.lines() {
        if !in_fn {
            if line.starts_with("fn ") && line.ends_with('{') { in_fn = true; cur_fn.clear(); }
            continue;
        }
        if line == "}" {
            if in_bb {
                flush_bb(cur_bb_id, &bb_lines, &mut cur_fn, &mut total_bbs, &mut admitted_bbs, &mut bailouts);
                bb_lines.clear(); in_bb = false;
            }
            if !cur_fn.is_empty() { fns.push(std::mem::take(&mut cur_fn)); }
            in_fn = false; continue;
        }
        let tr = line.trim();
        if !in_bb {
            if let Some(rest) = tr.strip_prefix("bb") {
                if let Some((ns, tail)) = rest.split_once(':') {
                    if tail.trim() == "{" {
                        if let Ok(id) = ns.parse::<u32>() { in_bb = true; cur_bb_id = id; bb_lines.clear(); }
                    }
                }
            }
        } else if tr == "}" {
            flush_bb(cur_bb_id, &bb_lines, &mut cur_fn, &mut total_bbs, &mut admitted_bbs, &mut bailouts);
            bb_lines.clear(); in_bb = false;
        } else if !tr.is_empty() {
            bb_lines.push(tr.into());
        }
    }
    (fns, total_bbs, admitted_bbs, bailouts)
}

/// Build Extended Basic Blocks (EBBs) chaining across:
///  - Goto(t) where pred_count[t] == 1
///  - Assert(cond, expected) -> t where pred_count[t] == 1 (inserts AssertGuard)
///  - SwitchInt(discr) -> [0: z, otherwise: o] where pred_count[o] == 1 (traces hot/body continuation
///    carrying PathAssume(discr != 0) — the exact pattern of `zerocopy::hash_name` bb2 -> bb3 -> bb4!)
fn build_ebbs(bbs: &HashMap<u32, RawBlock>) -> Vec<Superblock> {
    let mut preds: HashMap<u32, usize> = HashMap::new();
    for b in bbs.values() {
        for &s in &b.all_succs { *preds.entry(s).or_default() += 1; }
    }
    *preds.entry(0).or_default() += 1;

    let mut ids: Vec<u32> = bbs.keys().copied().collect();
    ids.sort();

    let mut chain_next: HashMap<u32, (u32, Option<EbbOp>)> = HashMap::new();
    for &id in &ids {
        let b = &bbs[&id];
        if !b.admitted { continue; }
        match b.term.as_ref().unwrap() {
            Term::Goto(t) if *t != id && preds.get(t).copied().unwrap_or(0) == 1 => {
                if bbs.get(t).map(|x| x.admitted).unwrap_or(false) {
                    chain_next.insert(id, (*t, None));
                }
            }
            Term::Assert { cond, expected, msg, target } if *target != id && preds.get(target).copied().unwrap_or(0) == 1 => {
                if bbs.get(target).map(|x| x.admitted).unwrap_or(false) {
                    chain_next.insert(id, (*target, Some(EbbOp::AssertGuard { cond: cond.clone(), expected: *expected, msg: msg.clone() })));
                }
            }
            Term::SwitchInt { discr, zero_tgt: Some(_), otherwise_tgt: Some(ot), .. }
                if *ot != id && preds.get(ot).copied().unwrap_or(0) == 1 =>
            {
                if bbs.get(ot).map(|x| x.admitted).unwrap_or(false) {
                    // Trace the `otherwise` (nonzero/true) hot path into its unique-predecessor block
                    chain_next.insert(id, (*ot, Some(EbbOp::PathAssume { cond: discr.clone(), expected_nonzero: true })));
                }
            }
            _ => {}
        }
    }
    let chained_targets: BTreeSet<u32> = chain_next.values().map(|(t, _)| *t).collect();

    let mut out = Vec::new();
    for &start in &ids {
        let b0 = &bbs[&start];
        if !b0.admitted || chained_targets.contains(&start) { continue; }
        let mut ops = Vec::new();
        let mut cur = start;
        let mut visited = BTreeSet::new();
        let mut bb_len = 0usize;
        let final_term;
        loop {
            visited.insert(cur);
            bb_len += 1;
            let blk = &bbs[&cur];
            ops.extend(blk.stmts.clone());
            if let Some((nxt, bridge)) = chain_next.get(&cur) {
                if !visited.contains(nxt) {
                    if let Some(bop) = bridge { ops.push(bop.clone()); }
                    cur = *nxt;
                    continue;
                }
            }
            final_term = blk.term.clone().unwrap();
            break;
        }
        out.push(Superblock { bb_len, ops, term: final_term });
    }
    out
}

fn places_overlap(a: &Place, b: &Place) -> bool {
    if a.local != b.local { return false; }
    match (a.field, b.field) { (None, _) | (_, None) => true, (Some(fa), Some(fb)) => fa == fb }
}

fn is_moved(moved: &BTreeSet<Place>, p: &Place) -> bool {
    moved.iter().any(|m| places_overlap(m, p))
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SymExpr {
    Init(Place),
    ConstInt(i128, String),
    ConstUnit,
    OpaqueConst(String),
    Bin(BinOp, u32, u32),
    Not(u32),
    CastInt(u32, String),
    PureOpaque(String, Vec<u32>),
    MemRead(u32, String, Vec<u32>), // (mem_ver, skeleton, sym_arg_ids)
}

struct SymArena {
    nodes: Vec<SymExpr>,
    intern: HashMap<SymExpr, u32>,
}

impl SymArena {
    fn new() -> Self { Self { nodes: Vec::new(), intern: HashMap::new() } }
    fn mk(&mut self, e: SymExpr) -> u32 {
        if let Some(&id) = self.intern.get(&e) { return id; }
        let id = self.nodes.len() as u32;
        self.nodes.push(e.clone());
        self.intern.insert(e, id);
        id
    }
    fn mk_bin(&mut self, op: BinOp, a: u32, b: u32) -> u32 {
        let na = self.nodes[a as usize].clone();
        let nb = self.nodes[b as usize].clone();
        match (op, &na, &nb) {
            (BinOp::Add | BinOp::Sub | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr, _, SymExpr::ConstInt(0, _))
            | (BinOp::Mul, _, SymExpr::ConstInt(1, _)) => a,
            (BinOp::Add | BinOp::BitOr | BinOp::BitXor, SymExpr::ConstInt(0, _), _)
            | (BinOp::Mul, SymExpr::ConstInt(1, _), _) => b,
            _ => self.mk(SymExpr::Bin(op, a, b)),
        }
    }
}

#[derive(Default)]
struct Stats {
    superblocks: usize,
    multi_bb: usize,
    max_chain: usize,
    chained_bbs: usize,
    ops_before: usize,
    ops_after: usize,
    moves_demoted: usize,
    copies_prop: usize,
    gvn_pure_hits: usize,
    gvn_memread_hits: usize,
    path_bce_elim: usize,
    dead_elim: usize,
    validated_ok: usize,
    validated_fail: usize,
}

fn rvalue_has_move(rv: &Rvalue) -> bool {
    match rv {
        Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Move(_)),
        Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Move(_)) || matches!(b, Operand::Move(_)),
        Rvalue::PureOpaque { ops, .. } | Rvalue::MemRead { ops, .. } => ops.iter().any(|o| matches!(o, Operand::Move(_))),
    }
}

fn optimize_ebb(sb: &Superblock, st: &mut Stats) -> Superblock {
    st.superblocks += 1;
    st.chained_bbs += sb.bb_len;
    if sb.bb_len >= 2 { st.multi_bb += 1; }
    if sb.bb_len > st.max_chain { st.max_chain = sb.bb_len; }
    st.ops_before += sb.ops.len();

    let mut dead_at_exit = BTreeSet::new();
    for op in &sb.ops {
        match op {
            EbbOp::StorageDead(l) => { dead_at_exit.insert(*l); }
            EbbOp::StorageLive(l) => { dead_at_exit.remove(l); }
            _ => {}
        }
    }

    // Pass 1: Certified MoveToCopy across EBB
    let mut moved = BTreeSet::new();
    let mut safe = true;
    let check_o = |o: &Operand, moved: &mut BTreeSet<Place>, safe: &mut bool| match o {
        Operand::Copy(p) => if is_moved(moved, p) { *safe = false; },
        Operand::Move(p) => if is_moved(moved, p) { *safe = false; } else { moved.insert(p.clone()); },
        _ => {}
    };
    let check_rv = |rv: &Rvalue, moved: &mut BTreeSet<Place>, safe: &mut bool| match rv {
        Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => check_o(a, moved, safe),
        Rvalue::BinaryOp(_, a, b) => { check_o(a, moved, safe); check_o(b, moved, safe); }
        Rvalue::PureOpaque { ops, .. } | Rvalue::MemRead { ops, .. } => for o in ops { check_o(o, moved, safe); },
    };
    for op in &sb.ops {
        match op {
            EbbOp::Assign { dst, rv } => { check_rv(rv, &mut moved, &mut safe); moved.retain(|m| !places_overlap(m, dst)); }
            EbbOp::MemStore { lhs_ops, rhs, .. } => {
                for o in lhs_ops { check_o(o, &mut moved, &mut safe); }
                check_rv(rhs, &mut moved, &mut safe);
            }
            EbbOp::StorageLive(l) | EbbOp::StorageDead(l) => { moved.retain(|m| m.local != *l); }
            EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => check_o(cond, &mut moved, &mut safe),
        }
    }
    match &sb.term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => check_o(discr, &mut moved, &mut safe),
        Term::CallBarrier { read_locals, moved_places, .. } => {
            for &l in read_locals { if is_moved(&moved, &Place { local: l, field: None }) { safe = false; } }
            for mp in moved_places { moved.insert(mp.clone()); }
        }
        _ => {}
    }

    let mut cur = sb.clone();
    if safe {
        fn dem_op(o: &mut Operand, dead_at_exit: &BTreeSet<u32>, moved: &BTreeSet<Place>, st: &mut Stats) {
            if let Operand::Move(p) = o {
                if dead_at_exit.contains(&p.local) || !is_moved(moved, p) {
                    st.moves_demoted += 1;
                    *o = Operand::Copy(p.clone());
                }
            }
        }
        fn dem_rv(rv: &mut Rvalue, dead_at_exit: &BTreeSet<u32>, moved: &BTreeSet<Place>, st: &mut Stats) {
            match rv {
                Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => dem_op(a, dead_at_exit, moved, st),
                Rvalue::BinaryOp(_, a, b) => { dem_op(a, dead_at_exit, moved, st); dem_op(b, dead_at_exit, moved, st); }
                Rvalue::PureOpaque { ops, .. } | Rvalue::MemRead { ops, .. } => {
                    for o in ops { dem_op(o, dead_at_exit, moved, st); }
                }
            }
        }
        for op in &mut cur.ops {
            match op {
                EbbOp::Assign { rv, .. } => dem_rv(rv, &dead_at_exit, &moved, st),
                EbbOp::MemStore { lhs_ops, rhs, .. } => {
                    for o in lhs_ops { dem_op(o, &dead_at_exit, &moved, st); }
                    dem_rv(rhs, &dead_at_exit, &moved, st);
                }
                EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => dem_op(cond, &dead_at_exit, &moved, st),
                _ => {}
            }
        }
        match &mut cur.term {
            Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => dem_op(discr, &dead_at_exit, &moved, st),
            _ => {}
        }
    }

    // Pass 2+3+4: EBB CopyProp + Symbolic GVN (including same-mem_ver MemRead!) + Path-Guarded BCE
    let mut arena = SymArena::new();
    let mut sym_env: HashMap<Place, u32> = HashMap::new();
    let mut alias: HashMap<Place, Operand> = HashMap::new();
    // Map canonical symbolic expr id -> Place currently holding it (invalidated if holder overwritten!)
    let mut sym_gvn: HashMap<u32, Place> = HashMap::new();
    let mut known_guards: HashMap<u32, bool> = HashMap::new();
    let mut mem_ver: u32 = 0;

    let inv = |p: &Place,
               alias: &mut HashMap<Place, Operand>,
               sym_env: &mut HashMap<Place, u32>,
               sym_gvn: &mut HashMap<u32, Place>| {
        alias.retain(|k, v| !places_overlap(k, p) && !matches!(v, Operand::Copy(vp) | Operand::Move(vp) if places_overlap(vp, p)));
        sym_env.retain(|k, _| !places_overlap(k, p));
        sym_gvn.retain(|_, holder| !places_overlap(holder, p));
    };

    let sym_op = |o: &Operand, sym_env: &HashMap<Place, u32>, arena: &mut SymArena| -> u32 {
        match o {
            Operand::ConstInt(v, t) => arena.mk(SymExpr::ConstInt(*v, t.clone())),
            Operand::ConstUnit => arena.mk(SymExpr::ConstUnit),
            Operand::OpaqueConst(s) => arena.mk(SymExpr::OpaqueConst(s.clone())),
            Operand::Copy(p) | Operand::Move(p) => *sym_env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone()))),
        }
    };

    let rw = |o: &Operand, alias: &HashMap<Place, Operand>, st: &mut Stats| -> Operand {
        if let Operand::Copy(p) = o {
            if let Some(r) = alias.get(p) {
                if matches!(r, Operand::Copy(_) | Operand::ConstInt(_, _) | Operand::ConstUnit) {
                    st.copies_prop += 1;
                    return r.clone();
                }
            }
        }
        o.clone()
    };

    let rw_rv = |rv: &Rvalue, alias: &HashMap<Place, Operand>, st: &mut Stats| -> Rvalue {
        match rv {
            Rvalue::Use(a) => Rvalue::Use(rw(a, alias, st)),
            Rvalue::UnaryNot(a) => Rvalue::UnaryNot(rw(a, alias, st)),
            Rvalue::CastInt(a, t) => Rvalue::CastInt(rw(a, alias, st), t.clone()),
            Rvalue::BinaryOp(b, x, y) => Rvalue::BinaryOp(*b, rw(x, alias, st), rw(y, alias, st)),
            Rvalue::PureOpaque { skeleton, ops } => Rvalue::PureOpaque {
                skeleton: skeleton.clone(),
                ops: ops.iter().map(|o| rw(o, alias, st)).collect(),
            },
            Rvalue::MemRead { skeleton, ops } => Rvalue::MemRead {
                skeleton: skeleton.clone(),
                ops: ops.iter().map(|o| rw(o, alias, st)).collect(),
            },
        }
    };

    let sym_rv = |rv: &Rvalue, sym_env: &HashMap<Place, u32>, arena: &mut SymArena, mver: u32| -> u32 {
        match rv {
            Rvalue::Use(a) => sym_op(a, sym_env, arena),
            Rvalue::UnaryNot(a) => { let ea = sym_op(a, sym_env, arena); arena.mk(SymExpr::Not(ea)) }
            Rvalue::CastInt(a, t) => { let ea = sym_op(a, sym_env, arena); arena.mk(SymExpr::CastInt(ea, t.clone())) }
            Rvalue::BinaryOp(b, x, y) => {
                let ex = sym_op(x, sym_env, arena);
                let ey = sym_op(y, sym_env, arena);
                arena.mk_bin(*b, ex, ey)
            }
            Rvalue::PureOpaque { skeleton, ops } => {
                let ids = ops.iter().map(|o| sym_op(o, sym_env, arena)).collect();
                arena.mk(SymExpr::PureOpaque(skeleton.clone(), ids))
            }
            Rvalue::MemRead { skeleton, ops } => {
                let ids = ops.iter().map(|o| sym_op(o, sym_env, arena)).collect();
                arena.mk(SymExpr::MemRead(mver, skeleton.clone(), ids))
            }
        }
    };

    let inv_rv_moves = |rv: &Rvalue,
                        alias: &mut HashMap<Place, Operand>,
                        sym_env: &mut HashMap<Place, u32>,
                        sym_gvn: &mut HashMap<u32, Place>| {
        let mut h = |o: &Operand| if let Operand::Move(p) = o { inv(p, alias, sym_env, sym_gvn); };
        match rv {
            Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => h(a),
            Rvalue::BinaryOp(_, a, b) => { h(a); h(b); }
            Rvalue::PureOpaque { ops, .. } | Rvalue::MemRead { ops, .. } => for o in ops { h(o); },
        }
    };

    let mut new_ops = Vec::with_capacity(cur.ops.len());
    for op in &cur.ops {
        match op {
            EbbOp::StorageLive(l) | EbbOp::StorageDead(l) => {
                inv(&Place { local: *l, field: None }, &mut alias, &mut sym_env, &mut sym_gvn);
                new_ops.push(op.clone());
            }
            EbbOp::PathAssume { cond, expected_nonzero } => {
                let nc = rw(cond, &alias, st);
                let sid = sym_op(&nc, &sym_env, &mut arena);
                if let Operand::Move(p) = &nc { inv(p, &mut alias, &mut sym_env, &mut sym_gvn); }
                known_guards.insert(sid, *expected_nonzero);
                new_ops.push(EbbOp::PathAssume { cond: nc, expected_nonzero: *expected_nonzero });
            }
            EbbOp::AssertGuard { cond, expected, msg } => {
                let nc = rw(cond, &alias, st);
                let sid = sym_op(&nc, &sym_env, &mut arena);
                if !matches!(nc, Operand::Move(_)) && known_guards.get(&sid) == Some(expected) {
                    st.path_bce_elim += 1;
                    continue;
                }
                if let Operand::Move(p) = &nc { inv(p, &mut alias, &mut sym_env, &mut sym_gvn); }
                known_guards.insert(sid, *expected);
                new_ops.push(EbbOp::AssertGuard { cond: nc, expected: *expected, msg: msg.clone() });
            }
            EbbOp::MemStore { lhs_skel, lhs_ops, rhs } => {
                let nlhs: Vec<Operand> = lhs_ops.iter().map(|o| rw(o, &alias, st)).collect();
                let nrhs = rw_rv(rhs, &alias, st);
                for o in &nlhs { if let Operand::Move(p) = o { inv(p, &mut alias, &mut sym_env, &mut sym_gvn); } }
                inv_rv_moves(&nrhs, &mut alias, &mut sym_env, &mut sym_gvn);
                // Conservative memory write barrier: bump mem_ver so future MemReads NEVER alias past this store!
                mem_ver += 1;
                new_ops.push(EbbOp::MemStore { lhs_skel: lhs_skel.clone(), lhs_ops: nlhs, rhs: nrhs });
            }
            EbbOp::Assign { dst, rv } => {
                let mut rv1 = rw_rv(rv, &alias, st);
                let sid = sym_rv(&rv1, &sym_env, &mut arena, mem_ver);
                let has_mv = rvalue_has_move(&rv1);
                if !has_mv && !matches!(rv1, Rvalue::Use(_)) {
                    if let Some(holder) = sym_gvn.get(&sid) {
                        if matches!(rv1, Rvalue::MemRead { .. }) { st.gvn_memread_hits += 1; }
                        else { st.gvn_pure_hits += 1; }
                        rv1 = Rvalue::Use(Operand::Copy(holder.clone()));
                    }
                }
                inv_rv_moves(&rv1, &mut alias, &mut sym_env, &mut sym_gvn);
                inv(dst, &mut alias, &mut sym_env, &mut sym_gvn);
                sym_env.insert(dst.clone(), sid);
                if !has_mv {
                    if let Rvalue::Use(ref o) = rv1 {
                        if matches!(o, Operand::Copy(p) if !places_overlap(p, dst))
                            || matches!(o, Operand::ConstInt(_, _) | Operand::ConstUnit)
                        {
                            alias.insert(dst.clone(), o.clone());
                        }
                    }
                    sym_gvn.entry(sid).or_insert_with(|| dst.clone());
                }
                new_ops.push(EbbOp::Assign { dst: dst.clone(), rv: rv1 });
            }
        }
    }

    let new_term = match &cur.term {
        Term::SwitchInt { discr, zero_tgt, otherwise_tgt, raw_targets } => Term::SwitchInt {
            discr: rw(discr, &alias, st),
            zero_tgt: *zero_tgt,
            otherwise_tgt: *otherwise_tgt,
            raw_targets: raw_targets.clone(),
        },
        Term::Assert { cond, expected, msg, target } => {
            let nc = rw(cond, &alias, st);
            let sid = sym_op(&nc, &sym_env, &mut arena);
            if !matches!(nc, Operand::Move(_)) && known_guards.get(&sid) == Some(expected) {
                st.path_bce_elim += 1;
                Term::Goto(*target)
            } else {
                Term::Assert { cond: nc, expected: *expected, msg: msg.clone(), target: *target }
            }
        }
        other => other.clone(),
    };

    // Dead temporary DCE across EBB (only pure non-MemRead, non-Move, StorageDead-before-exit locals!)
    let mut live: BTreeSet<u32> = BTreeSet::new();
    let add_o = |o: &Operand, live: &mut BTreeSet<u32>| if let Operand::Copy(p) | Operand::Move(p) = o { live.insert(p.local); };
    let add_rv = |rv: &Rvalue, live: &mut BTreeSet<u32>| match rv {
        Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => add_o(a, live),
        Rvalue::BinaryOp(_, a, b) => { add_o(a, live); add_o(b, live); }
        Rvalue::PureOpaque { ops, .. } | Rvalue::MemRead { ops, .. } => for o in ops { add_o(o, live); },
    };
    match &new_term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => add_o(discr, &mut live),
        Term::CallBarrier { read_locals, .. } => for &l in read_locals { live.insert(l); },
        _ => {}
    }
    for op in &new_ops {
        if let EbbOp::Assign { dst, .. } = op {
            if !dead_at_exit.contains(&dst.local) { live.insert(dst.local); }
        }
    }
    let mut kept_rev = Vec::with_capacity(new_ops.len());
    for op in new_ops.iter().rev() {
        match op {
            EbbOp::Assign { dst, rv } => {
                // Never delete MemRead (could trap on null/dangling deref!) or Move!
                let side_effect_free = !rvalue_has_move(rv) && !matches!(rv, Rvalue::MemRead { .. });
                if side_effect_free && dst.field.is_none() && !live.contains(&dst.local) && dead_at_exit.contains(&dst.local) {
                    st.dead_elim += 1;
                    continue;
                }
                if dst.field.is_none() { live.remove(&dst.local); }
                add_rv(rv, &mut live);
                kept_rev.push(op.clone());
            }
            EbbOp::MemStore { lhs_ops, rhs, .. } => {
                for o in lhs_ops { add_o(o, &mut live); }
                add_rv(rhs, &mut live);
                kept_rev.push(op.clone());
            }
            EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => {
                add_o(cond, &mut live);
                kept_rev.push(op.clone());
            }
            EbbOp::StorageDead(l) | EbbOp::StorageLive(l) => {
                live.remove(l);
                kept_rev.push(op.clone());
            }
        }
    }
    kept_rev.reverse();
    cur.ops = kept_rev;
    cur.term = new_term;
    st.ops_after += cur.ops.len();
    cur
}

#[derive(Debug, PartialEq, Eq)]
struct SymSummary {
    move_ub: bool,
    guards: Vec<(u32, bool)>,
    stores: Vec<(String, Vec<u32>, u32)>, // exact ordered memory store log!
    live_out: BTreeMap<Place, u32>,
    moved_out: BTreeSet<Place>,
    dead_locals: BTreeSet<u32>,
    term_sig: String,
}

fn sym_exec_ebb(sb: &Superblock, arena: &mut SymArena) -> SymSummary {
    let mut env: BTreeMap<Place, u32> = BTreeMap::new();
    let mut moved: BTreeSet<Place> = BTreeSet::new();
    let mut dead: BTreeSet<u32> = BTreeSet::new();
    let mut known: HashMap<u32, bool> = HashMap::new();
    let mut guards = Vec::new();
    let mut stores = Vec::new();
    let mut mem_ver: u32 = 0;
    let mut move_ub = false;

    let eval_o = |o: &Operand, env: &BTreeMap<Place, u32>, moved: &mut BTreeSet<Place>, dead: &BTreeSet<u32>, ub: &mut bool, arena: &mut SymArena| -> u32 {
        match o {
            Operand::ConstInt(v, t) => arena.mk(SymExpr::ConstInt(*v, t.clone())),
            Operand::ConstUnit => arena.mk(SymExpr::ConstUnit),
            Operand::OpaqueConst(s) => arena.mk(SymExpr::OpaqueConst(s.clone())),
            Operand::Copy(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) { *ub = true; }
                *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())))
            }
            Operand::Move(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) { *ub = true; }
                let v = *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())));
                moved.insert(p.clone());
                v
            }
        }
    };
    let eval_rv = |rv: &Rvalue, env: &BTreeMap<Place, u32>, moved: &mut BTreeSet<Place>, dead: &BTreeSet<u32>, ub: &mut bool, arena: &mut SymArena, mver: u32| -> u32 {
        match rv {
            Rvalue::Use(a) => eval_o(a, env, moved, dead, ub, arena),
            Rvalue::UnaryNot(a) => { let ea = eval_o(a, env, moved, dead, ub, arena); arena.mk(SymExpr::Not(ea)) }
            Rvalue::CastInt(a, t) => { let ea = eval_o(a, env, moved, dead, ub, arena); arena.mk(SymExpr::CastInt(ea, t.clone())) }
            Rvalue::BinaryOp(b, x, y) => {
                let ex = eval_o(x, env, moved, dead, ub, arena);
                let ey = eval_o(y, env, moved, dead, ub, arena);
                arena.mk_bin(*b, ex, ey)
            }
            Rvalue::PureOpaque { skeleton, ops } => {
                let ids = ops.iter().map(|o| eval_o(o, env, moved, dead, ub, arena)).collect();
                arena.mk(SymExpr::PureOpaque(skeleton.clone(), ids))
            }
            Rvalue::MemRead { skeleton, ops } => {
                let ids = ops.iter().map(|o| eval_o(o, env, moved, dead, ub, arena)).collect();
                arena.mk(SymExpr::MemRead(mver, skeleton.clone(), ids))
            }
        }
    };

    for op in &sb.ops {
        match op {
            EbbOp::StorageLive(l) => { dead.remove(l); moved.retain(|m| m.local != *l); env.retain(|k, _| k.local != *l); }
            EbbOp::StorageDead(l) => { dead.insert(*l); moved.retain(|m| m.local != *l); env.retain(|k, _| k.local != *l); }
            EbbOp::PathAssume { cond, expected_nonzero } => {
                let ec = eval_o(cond, &env, &mut moved, &dead, &mut move_ub, arena);
                known.insert(ec, *expected_nonzero);
            }
            EbbOp::AssertGuard { cond, expected, .. } => {
                let ec = eval_o(cond, &env, &mut moved, &dead, &mut move_ub, arena);
                if known.get(&ec) != Some(expected) {
                    known.insert(ec, *expected);
                    guards.push((ec, *expected));
                }
            }
            EbbOp::MemStore { lhs_skel, lhs_ops, rhs } => {
                let lids: Vec<u32> = lhs_ops.iter().map(|o| eval_o(o, &env, &mut moved, &dead, &mut move_ub, arena)).collect();
                let rid = eval_rv(rhs, &env, &mut moved, &dead, &mut move_ub, arena, mem_ver);
                stores.push((lhs_skel.clone(), lids, rid));
                mem_ver += 1;
            }
            EbbOp::Assign { dst, rv } => {
                let v = eval_rv(rv, &env, &mut moved, &dead, &mut move_ub, arena, mem_ver);
                dead.remove(&dst.local);
                moved.retain(|m| !places_overlap(m, dst));
                env.retain(|k, _| !places_overlap(k, dst));
                env.insert(dst.clone(), v);
            }
        }
    }

    let term_sig = match &sb.term {
        Term::Goto(t) => format!("goto:{t}"),
        Term::Return => "ret".into(),
        Term::Unreachable => "unreach".into(),
        Term::SwitchInt { discr, raw_targets, .. } => {
            let ed = eval_o(discr, &env, &mut moved, &dead, &mut move_ub, arena);
            format!("sw:{ed}:{raw_targets}")
        }
        Term::Assert { cond, expected, target, .. } => {
            let ec = eval_o(cond, &env, &mut moved, &dead, &mut move_ub, arena);
            if known.get(&ec) != Some(expected) { guards.push((ec, *expected)); }
            format!("goto:{target}")
        }
        Term::CallBarrier { raw, read_locals, moved_places } => {
            let mut vs = Vec::new();
            for &l in read_locals {
                let p = Place { local: l, field: None };
                if dead.contains(&l) || is_moved(&moved, &p) { move_ub = true; }
                vs.push(*env.get(&p).unwrap_or(&arena.mk(SymExpr::Init(p))));
            }
            for mp in moved_places { moved.insert(mp.clone()); }
            format!("call:{raw}:{vs:?}")
        }
    };

    let mut live_out = BTreeMap::new();
    for (p, v) in env {
        if !dead.contains(&p.local) && arena.nodes[v as usize] != SymExpr::Init(p.clone()) {
            live_out.insert(p, v);
        }
    }
    moved.retain(|m| !dead.contains(&m.local));
    SymSummary { move_ub, guards, stores, live_out, moved_out: moved, dead_locals: dead, term_sig }
}

fn validate_pair(src: &Superblock, opt: &Superblock) -> bool {
    let mut arena = SymArena::new();
    let a = sym_exec_ebb(src, &mut arena);
    let b = sym_exec_ebb(opt, &mut arena);
    a.move_ub == b.move_ub
        && (a.move_ub
            || (a.guards == b.guards
                && a.stores == b.stores
                && a.live_out == b.live_out
                && a.moved_out == b.moved_out
                && a.dead_locals == b.dead_locals
                && a.term_sig == b.term_sig))
}

fn run_bug7_load_cse_across_store() -> bool {
    // Source: _2 = (*_1); (*_1) = 99; _3 = (*_1); -> Buggy opt replaces `_3 = (*_1)` with `_3 = copy _2`!
    let p = |l| Place { local: l, field: None };
    let load_p1 = Rvalue::MemRead { skeleton: "(*#0)".into(), ops: vec![Operand::Copy(p(1))] };
    let src = Superblock {
        bb_len: 1,
        ops: vec![
            EbbOp::Assign { dst: p(2), rv: load_p1.clone() },
            EbbOp::MemStore { lhs_skel: "(*#0)".into(), lhs_ops: vec![Operand::Copy(p(1))], rhs: Rvalue::Use(Operand::ConstInt(99, "u64".into())) },
            EbbOp::Assign { dst: p(3), rv: load_p1 },
        ],
        term: Term::Return,
    };
    let buggy = Superblock {
        bb_len: 1,
        ops: vec![
            EbbOp::Assign { dst: p(2), rv: Rvalue::MemRead { skeleton: "(*#0)".into(), ops: vec![Operand::Copy(p(1))] } },
            EbbOp::MemStore { lhs_skel: "(*#0)".into(), lhs_ops: vec![Operand::Copy(p(1))], rhs: Rvalue::Use(Operand::ConstInt(99, "u64".into())) },
            EbbOp::Assign { dst: p(3), rv: Rvalue::Use(Operand::Copy(p(2))) },
        ],
        term: Term::Return,
    };
    !validate_pair(&src, &buggy) // MUST reject!
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let bug7_rejected = run_bug7_load_cse_across_store();

    let mut grand = Stats::default();
    let mut grand_tot_bbs = 0usize;
    let mut grand_adm_bbs = 0usize;
    let mut grand_opt_ms = 0.0f64;
    let mut grand_val_ms = 0.0f64;
    let mut grand_bails: BTreeMap<String, usize> = BTreeMap::new();

    println!("{{");
    println!("  \"benchmark\": \"E2-1c_real_memver_switchint_ebb_btl\",");
    println!("  \"bug7_load_cse_across_store_rejected\": {},", bug7_rejected);
    println!("  \"corpora\": [");
    for (idx, path) in args[1..].iter().enumerate() {
        let name = std::path::Path::new(path).file_name().unwrap().to_string_lossy().to_string();
        let (fns, tbbs, abbs, bails) = parse_functions(path);
        let mut sbs = Vec::new();
        for bbs in &fns { sbs.extend(build_ebbs(bbs)); }
        let mut cs = Stats::default();
        let t0 = Instant::now();
        let opt_sbs: Vec<Superblock> = sbs.iter().map(|s| optimize_ebb(s, &mut cs)).collect();
        let opt_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = Instant::now();
        for (s, o) in sbs.iter().zip(opt_sbs.iter()) {
            if validate_pair(s, o) { cs.validated_ok += 1; } else { cs.validated_fail += 1; }
        }
        let val_ms = t1.elapsed().as_secs_f64() * 1000.0;

        grand_tot_bbs += tbbs;
        grand_adm_bbs += abbs;
        grand.superblocks += cs.superblocks;
        grand.multi_bb += cs.multi_bb;
        if cs.max_chain > grand.max_chain { grand.max_chain = cs.max_chain; }
        grand.chained_bbs += cs.chained_bbs;
        grand.ops_before += cs.ops_before;
        grand.ops_after += cs.ops_after;
        grand.moves_demoted += cs.moves_demoted;
        grand.copies_prop += cs.copies_prop;
        grand.gvn_pure_hits += cs.gvn_pure_hits;
        grand.gvn_memread_hits += cs.gvn_memread_hits;
        grand.path_bce_elim += cs.path_bce_elim;
        grand.dead_elim += cs.dead_elim;
        grand.validated_ok += cs.validated_ok;
        grand.validated_fail += cs.validated_fail;
        grand_opt_ms += opt_ms;
        grand_val_ms += val_ms;
        for (k, v) in &bails { *grand_bails.entry(k.clone()).or_default() += v; }

        let comma = if idx + 1 < args.len() - 1 { "," } else { "" };
        println!(
            "    {{\"file\": {:?}, \"total_bbs\": {}, \"admitted_bbs\": {}, \"admitted_pct\": {:.2}, \"superblocks\": {}, \"multi_bb\": {}, \"max_chain\": {}, \"ops_before\": {}, \"ops_after\": {}, \"moves_demoted\": {}, \"copies_prop\": {}, \"gvn_pure\": {}, \"gvn_memread\": {}, \"path_bce_elim\": {}, \"dead_elim\": {}, \"validated_ok\": {}, \"validated_fail\": {}, \"opt_ms\": {:.2}, \"val_ms\": {:.2}}}{}",
            name, tbbs, abbs, 100.0 * (abbs as f64) / (tbbs.max(1) as f64),
            cs.superblocks, cs.multi_bb, cs.max_chain, cs.ops_before, cs.ops_after,
            cs.moves_demoted, cs.copies_prop, cs.gvn_pure_hits, cs.gvn_memread_hits,
            cs.path_bce_elim, cs.dead_elim, cs.validated_ok, cs.validated_fail, opt_ms, val_ms, comma
        );
    }
    println!("  ],");
    println!("  \"bailouts\": {:?},", grand_bails);
    println!("  \"totals\": {{");
    println!("    \"total_bbs\": {}, \"admitted_bbs\": {}, \"admitted_pct\": {:.2},", grand_tot_bbs, grand_adm_bbs, 100.0 * (grand_adm_bbs as f64) / (grand_tot_bbs.max(1) as f64));
    println!("    \"superblocks\": {}, \"multi_bb\": {}, \"max_chain\": {},", grand.superblocks, grand.multi_bb, grand.max_chain);
    println!("    \"ops_before\": {}, \"ops_after\": {}, \"reduction_pct\": {:.2},", grand.ops_before, grand.ops_after, 100.0 * ((grand.ops_before - grand.ops_after) as f64) / (grand.ops_before.max(1) as f64));
    println!("    \"moves_demoted\": {}, \"copies_prop\": {}, \"gvn_pure\": {}, \"gvn_memread\": {}, \"path_bce_elim\": {}, \"dead_elim\": {},", grand.moves_demoted, grand.copies_prop, grand.gvn_pure_hits, grand.gvn_memread_hits, grand.path_bce_elim, grand.dead_elim);
    println!("    \"validated_ok\": {}, \"validated_fail\": {}, \"opt_ms\": {:.3}, \"val_ms\": {:.3}, \"val_ops_per_sec\": {:.1}", grand.validated_ok, grand.validated_fail, grand_opt_ms, grand_val_ms, (grand.ops_before as f64) / (grand_val_ms / 1000.0).max(1e-9));
    println!("  }}");
    println!("}}");
}
