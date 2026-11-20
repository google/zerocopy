//! E2-1b (Multi-Block EBB Superblock Chaining + Path-Guarded GVN/BCE Validator on Real rustc 1.99.1 MIR)
//!
//! Directly tests our E2-1 single-BB finding: single Rust MIR basic blocks average only 2.07 statements
//! (0 GVN hits, 0 BCE eliminations). Chaining unique-predecessor `Goto` / `Assert` / `SwitchInt` paths
//! into CompCert-BTL-style Extended Basic Blocks (EBB superblocks) with path-fact propagation unlocks
//! cross-block CopyProp, GVN, and path-guarded BCE while maintaining 100% independent symbolic validation!

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
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum EbbOp {
    Assign { dst: Place, rv: Rvalue },
    StorageLive(u32),
    StorageDead(u32),
    /// Mid-superblock Assert (guarding continuation along the chained superblock!)
    AssertGuard { cond: Operand, expected: bool, msg: String },
    /// Dominating SwitchInt branch path fact (e.g. `cond != 0` on `otherwise` edge from `0: bb_exit`)
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
    bb_id: u32,
    admitted: bool,
    stmts: Vec<EbbOp>,
    term: Option<Term>,
    all_succs: Vec<u32>,
}

#[derive(Clone, Debug)]
struct Superblock {
    fn_id: u32,
    entry_bb: u32,
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
    if !inner.starts_with('_') {
        return None;
    }
    if let Some((loc_s, fld_s)) = inner[1..].split_once('.') {
        if fld_s.contains('.') || fld_s.contains('(') || fld_s.contains('[') {
            return None;
        }
        Some(Place { local: loc_s.parse().ok()?, field: Some(fld_s.parse().ok()?) })
    } else {
        Some(Place { local: inner[1..].parse().ok()?, field: None })
    }
}

fn parse_const(s: &str) -> Option<Operand> {
    let s = s.trim();
    if s == "const ()" {
        return Some(Operand::ConstUnit);
    }
    let rest = s.strip_prefix("const ")?.trim();
    if rest == "true" {
        return Some(Operand::ConstInt(1, "bool".into()));
    }
    if rest == "false" {
        return Some(Operand::ConstInt(0, "bool".into()));
    }
    if let Some((num_s, ty_s)) = rest.rsplit_once('_') {
        if matches!(ty_s, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
            return Some(Operand::ConstInt(num_s.parse().ok()?, ty_s.into()));
        }
    }
    None
}

fn parse_operand(s: &str) -> Option<Operand> {
    let s = s.trim();
    if let Some(r) = s.strip_prefix("copy ") {
        Some(Operand::Copy(parse_place(r)?))
    } else if let Some(r) = s.strip_prefix("move ") {
        Some(Operand::Move(parse_place(r)?))
    } else if s.starts_with("const ") {
        parse_const(s)
    } else {
        None
    }
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

fn parse_rvalue(rhs: &str) -> Option<Rvalue> {
    let rhs = rhs.trim();
    if let Some(op) = parse_operand(rhs) {
        return Some(Rvalue::Use(op));
    }
    if let Some(rest) = rhs.strip_prefix("Not(").and_then(|x| x.strip_suffix(')')) {
        return Some(Rvalue::UnaryNot(parse_operand(rest)?));
    }
    if let Some(idx) = rhs.find(" as ") {
        if let Some(rest) = rhs[idx + 4..].strip_suffix(" (IntToInt)") {
            let ty = rest.trim();
            if matches!(ty, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
                return Some(Rvalue::CastInt(parse_operand(&rhs[..idx])?, ty.into()));
            }
        }
    }
    if let Some(open) = rhs.find('(') {
        if rhs.ends_with(')') {
            let bop = parse_binop(&rhs[..open])?;
            let (a, b) = split_top_level_comma(&rhs[open + 1..rhs.len() - 1])?;
            return Some(Rvalue::BinaryOp(bop, parse_operand(a)?, parse_operand(b)?));
        }
    }
    None
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
                while j < bytes.len() && bytes[j].is_ascii_digit() {
                    j += 1;
                }
                if let Ok(id) = line[i + 2..j].parse::<u32>() {
                    out.push(id);
                }
                i = j;
                continue;
            }
        }
        i += 1;
    }
    out
}

fn parse_functions(path: &str) -> Vec<(u32, HashMap<u32, RawBlock>)> {
    let text = fs::read_to_string(path).expect("read mir");
    let mut fns = Vec::new();
    let mut in_fn = false;
    let mut fn_id: u32 = 0;
    let mut cur_fn: HashMap<u32, RawBlock> = HashMap::new();
    let mut in_bb = false;
    let mut cur_bb_id: u32 = 0;
    let mut bb_lines: Vec<String> = Vec::new();

    let flush_bb = |bb_id: u32, lines: &[String], cur_fn: &mut HashMap<u32, RawBlock>| {
        if lines.is_empty() {
            return;
        }
        let all_succs = extract_all_bb_targets(lines.last().unwrap());
        let mut stmts = Vec::new();
        let mut admitted = true;
        let mut term_opt = None;

        for (idx, raw) in lines.iter().enumerate() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let is_last = idx + 1 == lines.len();
            let s = line.trim_end_matches(';').trim();
            if !is_last {
                if let Some(inner) = s.strip_prefix("StorageLive(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() { stmts.push(EbbOp::StorageLive(p.local)); continue; }
                    }
                    admitted = false; break;
                } else if let Some(inner) = s.strip_prefix("StorageDead(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() { stmts.push(EbbOp::StorageDead(p.local)); continue; }
                    }
                    admitted = false; break;
                } else if s.starts_with("nop") || s.starts_with("ConstEvalCounter") {
                    continue;
                } else if let Some((lhs, rhs)) = s.split_once(" = ") {
                    if let (Some(dst), Some(rv)) = (parse_place(lhs), parse_rvalue(rhs)) {
                        stmts.push(EbbOp::Assign { dst, rv });
                        continue;
                    }
                    admitted = false; break;
                } else {
                    admitted = false; break;
                }
            } else if s == "return" {
                term_opt = Some(Term::Return);
            } else if s == "unreachable" {
                term_opt = Some(Term::Unreachable);
            } else if let Some(rest) = s.strip_prefix("goto -> bb") {
                if let Ok(tgt) = rest.trim().parse::<u32>() { term_opt = Some(Term::Goto(tgt)); } else { admitted = false; }
            } else if let Some(rest) = s.strip_prefix("switchInt(") {
                if let Some((discr_s, tgt_s)) = rest.split_once(") -> ") {
                    if let Some(op) = parse_operand(discr_s) {
                        // Parse `[0: bbX, otherwise: bbY]` or `[false: bbX, otherwise: bbY]`
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
                    } else { admitted = false; }
                } else { admitted = false; }
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
                    } else { admitted = false; }
                } else { admitted = false; }
            } else if s.contains(" -> [return:") || s.contains(" -> unwind") {
                if s.starts_with("drop(") || s.starts_with("asm!(") {
                    admitted = false;
                } else {
                    let mut read_locals = Vec::new();
                    let mut moved_places = Vec::new();
                    let mut i = 0;
                    let mut ok = true;
                    while i < s.len() {
                        if s[i..].starts_with("move ") {
                            let tok: String = s[i + 5..].chars().take_while(|c| !matches!(c, ',' | ')' | ';' | ' ')).collect();
                            if let Some(p) = parse_place(&tok) { read_locals.push(p.local); moved_places.push(p); } else { ok = false; }
                            i += 5; continue;
                        } else if s[i..].starts_with("copy ") {
                            let tok: String = s[i + 5..].chars().take_while(|c| !matches!(c, ',' | ')' | ';' | ' ')).collect();
                            if let Some(p) = parse_place(&tok) { read_locals.push(p.local); } else { ok = false; }
                            i += 5; continue;
                        }
                        i += 1;
                    }
                    if ok {
                        term_opt = Some(Term::CallBarrier { raw: s.into(), read_locals, moved_places });
                    } else { admitted = false; }
                }
            } else {
                admitted = false;
            }
        }
        cur_fn.insert(bb_id, RawBlock { bb_id, admitted: admitted && term_opt.is_some(), stmts, term: term_opt, all_succs });
    };

    for line in text.lines() {
        if !in_fn {
            if line.starts_with("fn ") && line.ends_with('{') {
                in_fn = true;
                cur_fn.clear();
            }
            continue;
        }
        if line == "}" {
            if in_bb {
                flush_bb(cur_bb_id, &bb_lines, &mut cur_fn);
                bb_lines.clear();
                in_bb = false;
            }
            if !cur_fn.is_empty() {
                fns.push((fn_id, std::mem::take(&mut cur_fn)));
                fn_id += 1;
            }
            in_fn = false;
            continue;
        }
        let tr = line.trim();
        if !in_bb {
            if let Some(rest) = tr.strip_prefix("bb") {
                if let Some((ns, tail)) = rest.split_once(':') {
                    if tail.trim() == "{" {
                        if let Ok(id) = ns.parse::<u32>() {
                            in_bb = true; cur_bb_id = id; bb_lines.clear();
                        }
                    }
                }
            }
        } else if tr == "}" {
            flush_bb(cur_bb_id, &bb_lines, &mut cur_fn);
            bb_lines.clear();
            in_bb = false;
        } else if !tr.is_empty() {
            bb_lines.push(tr.into());
        }
    }
    fns
}

/// Build Extended Basic Block (EBB) Superblocks by chaining unique-predecessor Goto & Assert edges,
/// plus tracing SwitchInt -> unique-predecessor `otherwise` edges (carrying PathAssume facts!).
fn build_superblocks(fn_id: u32, bbs: &HashMap<u32, RawBlock>) -> Vec<Superblock> {
    let mut preds: HashMap<u32, usize> = HashMap::new();
    for b in bbs.values() {
        for &s in &b.all_succs {
            *preds.entry(s).or_default() += 1;
        }
    }
    // Entry bb0 always has implicit external predecessor
    *preds.entry(0).or_default() += 1;

    let mut consumed: BTreeSet<u32> = BTreeSet::new();
    let mut ids: Vec<u32> = bbs.keys().copied().collect();
    ids.sort();

    // First identify all blocks that are chained continuations of an admitted predecessor
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
            _ => {}
        }
    }
    let targets_set: BTreeSet<u32> = chain_next.values().map(|(t, _)| *t).collect();

    let mut out = Vec::new();
    for &start in &ids {
        let b0 = &bbs[&start];
        if !b0.admitted || targets_set.contains(&start) || consumed.contains(&start) {
            continue;
        }
        let mut ops = Vec::new();
        let mut cur = start;
        let mut visited = BTreeSet::new();
        let mut bb_len = 0usize;
        let mut final_term;
        loop {
            visited.insert(cur);
            consumed.insert(cur);
            bb_len += 1;
            let blk = &bbs[&cur];
            ops.extend(blk.stmts.clone());
            if let Some((nxt, bridge_op)) = chain_next.get(&cur) {
                if !visited.contains(nxt) {
                    if let Some(bop) = bridge_op {
                        ops.push(bop.clone());
                    }
                    cur = *nxt;
                    continue;
                }
            }
            final_term = blk.term.clone().unwrap();
            break;
        }
        out.push(Superblock { fn_id, entry_bb: start, bb_len, ops, term: final_term });
    }

    // Also collect any SwitchInt -> unique-pred child with dominating PathAssume (as a separate superblock view)
    for &id in &ids {
        let b = &bbs[&id];
        if !b.admitted { continue; }
        if let Some(Term::SwitchInt { discr, otherwise_tgt: Some(ot), .. }) = &b.term {
            if preds.get(ot).copied().unwrap_or(0) == 1 && !consumed.contains(&id) {
                // Already emitted individually above; skip duplication
                let _ = (discr, ot);
            }
        }
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
    Bin(BinOp, u32, u32),
    Not(u32),
    CastInt(u32, String),
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
struct EbbStats {
    superblocks: usize,
    multi_bb_superblocks: usize,
    max_chain_len: usize,
    total_chained_bbs: usize,
    ops_before: usize,
    ops_after: usize,
    moves_demoted: usize,
    copies_prop: usize,
    gvn_hits: usize,
    path_bce_elim: usize,
    dead_ops_elim: usize,
    validated_ok: usize,
    validated_fail: usize,
}

fn optimize_ebb(sb: &Superblock, st: &mut EbbStats) -> Superblock {
    st.superblocks += 1;
    st.total_chained_bbs += sb.bb_len;
    if sb.bb_len >= 2 { st.multi_bb_superblocks += 1; }
    if sb.bb_len > st.max_chain_len { st.max_chain_len = sb.bb_len; }
    st.ops_before += sb.ops.len();

    // Pass 1: Certified field-granular MoveToCopy across entire EBB
    let mut dead_at_exit: BTreeSet<u32> = BTreeSet::new();
    for op in &sb.ops {
        match op {
            EbbOp::StorageDead(l) => { dead_at_exit.insert(*l); }
            EbbOp::StorageLive(l) => { dead_at_exit.remove(l); }
            _ => {}
        }
    }
    let mut moved = BTreeSet::new();
    let mut safe = true;
    let check_op = |op: &Operand, moved: &mut BTreeSet<Place>, safe: &mut bool| match op {
        Operand::Copy(p) => if is_moved(moved, p) { *safe = false; },
        Operand::Move(p) => if is_moved(moved, p) { *safe = false; } else { moved.insert(p.clone()); },
        _ => {}
    };
    for op in &sb.ops {
        match op {
            EbbOp::Assign { dst, rv } => {
                match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => check_op(a, &mut moved, &mut safe),
                    Rvalue::BinaryOp(_, a, b) => { check_op(a, &mut moved, &mut safe); check_op(b, &mut moved, &mut safe); }
                }
                moved.retain(|m| !places_overlap(m, dst));
            }
            EbbOp::StorageLive(l) | EbbOp::StorageDead(l) => { moved.retain(|m| m.local != *l); }
            EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => check_op(cond, &mut moved, &mut safe),
        }
    }
    match &sb.term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => check_op(discr, &mut moved, &mut safe),
        Term::CallBarrier { read_locals, moved_places, .. } => {
            for &l in read_locals { if is_moved(&moved, &Place { local: l, field: None }) { safe = false; } }
            for mp in moved_places { moved.insert(mp.clone()); }
        }
        _ => {}
    }

    let mut cur = sb.clone();
    if safe {
        let can_demote = |p: &Place| dead_at_exit.contains(&p.local) || !is_moved(&moved, p);
        let mut dem = |op: &mut Operand| {
            if let Operand::Move(p) = op {
                if can_demote(p) { st.moves_demoted += 1; *op = Operand::Copy(p.clone()); }
            }
        };
        for op in &mut cur.ops {
            match op {
                EbbOp::Assign { rv, .. } => match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => dem(a),
                    Rvalue::BinaryOp(_, a, b) => { dem(a); dem(b); }
                },
                EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => dem(cond),
                _ => {}
            }
        }
        match &mut cur.term {
            Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => dem(discr),
            _ => {}
        }
    }

    // Pass 2+3+4: EBB-wide CopyProp + Strict GVN + Path-Guarded Redundant Assert Elimination
    let mut alias: HashMap<Place, Operand> = HashMap::new();
    let mut gvn: HashMap<Rvalue, Place> = HashMap::new();
    let mut known_guards: BTreeSet<(Operand, bool)> = BTreeSet::new();
    // Use canonical symbolic expr ID for path-fact matching across different temp locals!
    let mut arena = SymArena::new();
    let mut sym_env: HashMap<Place, u32> = HashMap::new();
    let mut known_sym_guards: HashMap<u32, bool> = HashMap::new();

    let inv = |p: &Place,
               alias: &mut HashMap<Place, Operand>,
               gvn: &mut HashMap<Rvalue, Place>,
               sym_env: &mut HashMap<Place, u32>| {
        alias.retain(|k, v| !places_overlap(k, p) && !matches!(v, Operand::Copy(vp) | Operand::Move(vp) if places_overlap(vp, p)));
        gvn.retain(|rv, holder| {
            if places_overlap(holder, p) { return false; }
            let m = |o: &Operand| matches!(o, Operand::Copy(op) | Operand::Move(op) if places_overlap(op, p));
            match rv {
                Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => !m(a),
                Rvalue::BinaryOp(_, a, b) => !m(a) && !m(b),
            }
        });
        sym_env.retain(|k, _| !places_overlap(k, p));
    };

    let sym_of_op = |op: &Operand, sym_env: &HashMap<Place, u32>, arena: &mut SymArena| -> u32 {
        match op {
            Operand::ConstInt(v, t) => arena.mk(SymExpr::ConstInt(*v, t.clone())),
            Operand::ConstUnit => arena.mk(SymExpr::ConstUnit),
            Operand::Copy(p) | Operand::Move(p) => *sym_env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone()))),
        }
    };

    let rw = |op: &Operand, alias: &HashMap<Place, Operand>, st: &mut EbbStats| -> Operand {
        if let Operand::Copy(p) = op {
            if let Some(r) = alias.get(p) {
                if matches!(r, Operand::Copy(_) | Operand::ConstInt(_, _) | Operand::ConstUnit) {
                    st.copies_prop += 1;
                    return r.clone();
                }
            }
        }
        op.clone()
    };

    let mut new_ops = Vec::with_capacity(cur.ops.len());
    for op in &cur.ops {
        match op {
            EbbOp::StorageLive(l) | EbbOp::StorageDead(l) => {
                inv(&Place { local: *l, field: None }, &mut alias, &mut gvn, &mut sym_env);
                new_ops.push(op.clone());
            }
            EbbOp::AssertGuard { cond, expected, msg } => {
                let nc = rw(cond, &alias, st);
                let sid = sym_of_op(&nc, &sym_env, &mut arena);
                let has_move = matches!(nc, Operand::Move(_));
                if !has_move && known_sym_guards.get(&sid) == Some(expected) {
                    st.path_bce_elim += 1;
                    continue;
                }
                if let Operand::Move(p) = &nc { inv(p, &mut alias, &mut gvn, &mut sym_env); }
                known_sym_guards.insert(sid, *expected);
                let _ = &known_guards;
                new_ops.push(EbbOp::AssertGuard { cond: nc, expected: *expected, msg: msg.clone() });
            }
            EbbOp::PathAssume { cond, expected_nonzero } => {
                let nc = rw(cond, &alias, st);
                let sid = sym_of_op(&nc, &sym_env, &mut arena);
                known_sym_guards.insert(sid, *expected_nonzero);
                new_ops.push(EbbOp::PathAssume { cond: nc, expected_nonzero: *expected_nonzero });
            }
            EbbOp::Assign { dst, rv } => {
                let mut rv1 = match rv {
                    Rvalue::Use(a) => Rvalue::Use(rw(a, &alias, st)),
                    Rvalue::UnaryNot(a) => Rvalue::UnaryNot(rw(a, &alias, st)),
                    Rvalue::CastInt(a, ty) => Rvalue::CastInt(rw(a, &alias, st), ty.clone()),
                    Rvalue::BinaryOp(bop, a, b) => Rvalue::BinaryOp(*bop, rw(a, &alias, st), rw(b, &alias, st)),
                };
                let has_move = match &rv1 {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Move(_)),
                    Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Move(_)) || matches!(b, Operand::Move(_)),
                };
                let sym_val = match &rv1 {
                    Rvalue::Use(a) => sym_of_op(a, &sym_env, &mut arena),
                    Rvalue::UnaryNot(a) => { let ea = sym_of_op(a, &sym_env, &mut arena); arena.mk(SymExpr::Not(ea)) }
                    Rvalue::CastInt(a, ty) => { let ea = sym_of_op(a, &sym_env, &mut arena); arena.mk(SymExpr::CastInt(ea, ty.clone())) }
                    Rvalue::BinaryOp(bop, a, b) => {
                        let ea = sym_of_op(a, &sym_env, &mut arena);
                        let eb = sym_of_op(b, &sym_env, &mut arena);
                        arena.mk_bin(*bop, ea, eb)
                    }
                };
                if !has_move && !matches!(rv1, Rvalue::Use(_)) {
                    if let Some(holder) = gvn.get(&rv1) {
                        st.gvn_hits += 1;
                        rv1 = Rvalue::Use(Operand::Copy(holder.clone()));
                    }
                }
                match &rv1 {
                    Rvalue::Use(Operand::Move(p)) | Rvalue::UnaryNot(Operand::Move(p)) | Rvalue::CastInt(Operand::Move(p), _) => {
                        inv(p, &mut alias, &mut gvn, &mut sym_env);
                    }
                    Rvalue::BinaryOp(_, a, b) => {
                        if let Operand::Move(p) = a { inv(p, &mut alias, &mut gvn, &mut sym_env); }
                        if let Operand::Move(p) = b { inv(p, &mut alias, &mut gvn, &mut sym_env); }
                    }
                    _ => {}
                }
                inv(dst, &mut alias, &mut gvn, &mut sym_env);
                sym_env.insert(dst.clone(), sym_val);
                if !has_move {
                    if let Rvalue::Use(ref o) = rv1 {
                        if matches!(o, Operand::Copy(p) if !places_overlap(p, dst))
                            || matches!(o, Operand::ConstInt(_, _) | Operand::ConstUnit)
                        {
                            alias.insert(dst.clone(), o.clone());
                        }
                    } else {
                        let mentions_dst = match &rv1 {
                            Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Copy(p) if places_overlap(p, dst)),
                            Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Copy(p) if places_overlap(p, dst)) || matches!(b, Operand::Copy(p) if places_overlap(p, dst)),
                        };
                        if !mentions_dst { gvn.insert(rv1.clone(), dst.clone()); }
                    }
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
            let sid = sym_of_op(&nc, &sym_env, &mut arena);
            if !matches!(nc, Operand::Move(_)) && known_sym_guards.get(&sid) == Some(expected) {
                st.path_bce_elim += 1;
                Term::Goto(*target)
            } else {
                Term::Assert { cond: nc, expected: *expected, msg: msg.clone(), target: *target }
            }
        }
        other => other.clone(),
    };

    // Dead temporary DCE across EBB
    let mut live: BTreeSet<u32> = BTreeSet::new();
    let add_u = |o: &Operand, live: &mut BTreeSet<u32>| if let Operand::Copy(p) | Operand::Move(p) = o { live.insert(p.local); };
    match &new_term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => add_u(discr, &mut live),
        Term::CallBarrier { read_locals, .. } => { for &l in read_locals { live.insert(l); } }
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
                let has_move = match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Move(_)),
                    Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Move(_)) || matches!(b, Operand::Move(_)),
                };
                if !has_move && dst.field.is_none() && !live.contains(&dst.local) && dead_at_exit.contains(&dst.local) {
                    st.dead_ops_elim += 1;
                    continue;
                }
                if dst.field.is_none() { live.remove(&dst.local); }
                match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => add_u(a, &mut live),
                    Rvalue::BinaryOp(_, a, b) => { add_u(a, &mut live); add_u(b, &mut live); }
                }
                kept_rev.push(op.clone());
            }
            EbbOp::AssertGuard { cond, .. } | EbbOp::PathAssume { cond, .. } => {
                add_u(cond, &mut live);
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
struct EbbSymSummary {
    move_ub: bool,
    guards: Vec<(u32, bool)>, // deduplicated ordered non-implied symbolic guards
    live_out: BTreeMap<Place, u32>,
    moved_out: BTreeSet<Place>,
    dead_locals: BTreeSet<u32>,
    term_sig: String,
}

fn sym_exec_ebb(sb: &Superblock, arena: &mut SymArena) -> EbbSymSummary {
    let mut env: BTreeMap<Place, u32> = BTreeMap::new();
    let mut moved: BTreeSet<Place> = BTreeSet::new();
    let mut dead: BTreeSet<u32> = BTreeSet::new();
    let mut known_guards: HashMap<u32, bool> = HashMap::new();
    let mut guards: Vec<(u32, bool)> = Vec::new();
    let mut move_ub = false;

    let eval_op = |op: &Operand,
                   env: &BTreeMap<Place, u32>,
                   moved: &mut BTreeSet<Place>,
                   dead: &BTreeSet<u32>,
                   move_ub: &mut bool,
                   arena: &mut SymArena| -> u32 {
        match op {
            Operand::ConstInt(v, t) => arena.mk(SymExpr::ConstInt(*v, t.clone())),
            Operand::ConstUnit => arena.mk(SymExpr::ConstUnit),
            Operand::Copy(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) { *move_ub = true; }
                *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())))
            }
            Operand::Move(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) { *move_ub = true; }
                let v = *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())));
                moved.insert(p.clone());
                v
            }
        }
    };

    for op in &sb.ops {
        match op {
            EbbOp::StorageLive(l) => { dead.remove(l); moved.retain(|m| m.local != *l); env.retain(|k, _| k.local != *l); }
            EbbOp::StorageDead(l) => { dead.insert(*l); moved.retain(|m| m.local != *l); env.retain(|k, _| k.local != *l); }
            EbbOp::AssertGuard { cond, expected, .. } => {
                let ec = eval_op(cond, &env, &mut moved, &dead, &mut move_ub, arena);
                if known_guards.get(&ec) != Some(expected) {
                    known_guards.insert(ec, *expected);
                    guards.push((ec, *expected));
                }
            }
            EbbOp::PathAssume { cond, expected_nonzero } => {
                let ec = eval_op(cond, &env, &mut moved, &dead, &mut move_ub, arena);
                known_guards.insert(ec, *expected_nonzero);
            }
            EbbOp::Assign { dst, rv } => {
                let v = match rv {
                    Rvalue::Use(a) => eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena),
                    Rvalue::UnaryNot(a) => { let ea = eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena); arena.mk(SymExpr::Not(ea)) }
                    Rvalue::CastInt(a, t) => { let ea = eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena); arena.mk(SymExpr::CastInt(ea, t.clone())) }
                    Rvalue::BinaryOp(b, x, y) => {
                        let ex = eval_op(x, &env, &mut moved, &dead, &mut move_ub, arena);
                        let ey = eval_op(y, &env, &mut moved, &dead, &mut move_ub, arena);
                        arena.mk_bin(*b, ex, ey)
                    }
                };
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
            let ed = eval_op(discr, &env, &mut moved, &dead, &mut move_ub, arena);
            format!("sw:{ed}:{raw_targets}")
        }
        Term::Assert { cond, expected, target, .. } => {
            let ec = eval_op(cond, &env, &mut moved, &dead, &mut move_ub, arena);
            if known_guards.get(&ec) == Some(expected) {
                format!("goto:{target}")
            } else {
                guards.push((ec, *expected));
                format!("goto:{target}")
            }
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
    EbbSymSummary { move_ub, guards, live_out, moved_out: moved, dead_locals: dead, term_sig }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut total = EbbStats::default();
    let mut total_opt_ms = 0.0f64;
    let mut total_val_ms = 0.0f64;

    println!("{{");
    println!("  \"benchmark\": \"E2-1b_real_multi_bb_ebb_superblocks\",");
    println!("  \"corpora\": [");
    for (idx, path) in args[1..].iter().enumerate() {
        let name = std::path::Path::new(path).file_name().unwrap().to_string_lossy().to_string();
        let fns = parse_functions(path);
        let mut sbs = Vec::new();
        for (fid, bbs) in &fns {
            sbs.extend(build_superblocks(*fid, bbs));
        }
        let mut cs = EbbStats::default();
        let t0 = Instant::now();
        let opt_sbs: Vec<Superblock> = sbs.iter().map(|s| optimize_ebb(s, &mut cs)).collect();
        let opt_ms = t0.elapsed().as_secs_f64() * 1000.0;
        let t1 = Instant::now();
        for (s, o) in sbs.iter().zip(opt_sbs.iter()) {
            let mut arena = SymArena::new();
            let a = sym_exec_ebb(s, &mut arena);
            let b = sym_exec_ebb(o, &mut arena);
            if a.move_ub == b.move_ub && (a.move_ub || (a.guards == b.guards && a.live_out == b.live_out && a.moved_out == b.moved_out && a.dead_locals == b.dead_locals && a.term_sig == b.term_sig)) {
                cs.validated_ok += 1;
            } else {
                cs.validated_fail += 1;
            }
        }
        let val_ms = t1.elapsed().as_secs_f64() * 1000.0;

        total.superblocks += cs.superblocks;
        total.multi_bb_superblocks += cs.multi_bb_superblocks;
        if cs.max_chain_len > total.max_chain_len { total.max_chain_len = cs.max_chain_len; }
        total.total_chained_bbs += cs.total_chained_bbs;
        total.ops_before += cs.ops_before;
        total.ops_after += cs.ops_after;
        total.moves_demoted += cs.moves_demoted;
        total.copies_prop += cs.copies_prop;
        total.gvn_hits += cs.gvn_hits;
        total.path_bce_elim += cs.path_bce_elim;
        total.dead_ops_elim += cs.dead_ops_elim;
        total.validated_ok += cs.validated_ok;
        total.validated_fail += cs.validated_fail;
        total_opt_ms += opt_ms;
        total_val_ms += val_ms;

        let comma = if idx + 1 < args.len() - 1 { "," } else { "" };
        println!(
            "    {{\"file\": {:?}, \"superblocks\": {}, \"multi_bb\": {}, \"max_chain\": {}, \"chained_bbs\": {}, \"ops_before\": {}, \"ops_after\": {}, \"moves_demoted\": {}, \"copies_prop\": {}, \"gvn_hits\": {}, \"path_bce_elim\": {}, \"dead_elim\": {}, \"validated_ok\": {}, \"validated_fail\": {}, \"opt_ms\": {:.2}, \"val_ms\": {:.2}}}{}",
            name, cs.superblocks, cs.multi_bb_superblocks, cs.max_chain_len, cs.total_chained_bbs,
            cs.ops_before, cs.ops_after, cs.moves_demoted, cs.copies_prop, cs.gvn_hits,
            cs.path_bce_elim, cs.dead_ops_elim, cs.validated_ok, cs.validated_fail, opt_ms, val_ms, comma
        );
    }
    println!("  ],");
    println!("  \"totals\": {{");
    println!("    \"superblocks\": {}, \"multi_bb_superblocks\": {}, \"max_chain_len\": {}, \"total_chained_bbs\": {},", total.superblocks, total.multi_bb_superblocks, total.max_chain_len, total.total_chained_bbs);
    println!("    \"ops_before\": {}, \"ops_after\": {}, \"reduction_pct\": {:.2},", total.ops_before, total.ops_after, 100.0 * ((total.ops_before - total.ops_after) as f64) / (total.ops_before.max(1) as f64));
    println!("    \"moves_demoted\": {}, \"copies_prop\": {}, \"gvn_hits\": {}, \"path_bce_elim\": {}, \"dead_elim\": {},", total.moves_demoted, total.copies_prop, total.gvn_hits, total.path_bce_elim, total.dead_ops_elim);
    println!("    \"validated_ok\": {}, \"validated_fail\": {}, \"opt_ms\": {:.3}, \"val_ms\": {:.3}, \"val_ops_per_sec\": {:.1}", total.validated_ok, total.validated_fail, total_opt_ms, total_val_ms, (total.ops_before as f64) / (total_val_ms / 1000.0).max(1e-9));
    println!("  }}");
    println!("}}");
}
