//! E2-1 (T02 Genuine Non-LLVM BTL Superblock Optimization Replayer & Symbolic Validator)
//!
//! Directly replaces Stage 0c Refutation U2 (`oracle_replay_driver.py` which called LLVM `opt`+`llc`)
//! and operationalizes our E1-4 / E1-7 architectural finding: because debuginfo-free 1-WL alignment
//! (`10.37%`) and `-O3` DWARF (`48.86%` PC-bytes) cannot reconstruct provenance post-hoc, a verified
//! `rustc` optimizer must operate on superblock-local IR carrying compiler-internal `OriginTag`s
//! validated by an independent symbolic equivalence checker (`CompCert BTL`-style).
//!
//! Zero LLVM `opt`/`llc` calls. Zero hardcoded tables.
//! Parses real `rustc 1.99.1` MIR bodies (`core.mir`, `zerocopy.mir`, `anneal_audit.mir`, `cargo_anneal.mir`),
//! runs 4 genuine non-LLVM superblock passes preserving field-granular `deinitMovedPlace = true`,
//! validates every transformed superblock independently with hash-consed symbolic execution,
//! and executes 6 adversarial bug-injection negative controls (must reject 6/6).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::env;
use std::fs;
use std::time::Instant;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct OriginTag {
    fn_id: u32,
    bb_id: u32,
    stmt_idx: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct Place {
    local: u32,
    field: Option<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Operand {
    Copy(Place),
    Move(Place),
    ConstInt(i128, String), // value + rust type suffix (e.g., "usize", "u64", "bool")
    ConstUnit,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum BinOp {
    Add,
    Sub,
    Mul,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Rvalue {
    Use(Operand),
    BinaryOp(BinOp, Operand, Operand),
    UnaryNot(Operand),
    CastInt(Operand, String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Stmt {
    Assign { tag: OriginTag, dst: Place, rv: Rvalue },
    StorageLive { tag: OriginTag, local: u32 },
    StorageDead { tag: OriginTag, local: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Term {
    Goto(u32),
    Return,
    SwitchInt { discr: Operand, targets: String },
    Assert { cond: Operand, expected: bool, msg: String, target: u32 },
    CallBarrier { raw: String, read_locals: Vec<u32>, moved_places: Vec<Place> },
    Unreachable,
}

#[derive(Clone, Debug)]
struct BasicBlock {
    fn_id: u32,
    bb_id: u32,
    stmts: Vec<Stmt>,
    term: Term,
}

// ============================================================================
// 1. Real rustc 1.99.1 MIR Parser (Explicit Fail-Closed Bailout Taxonomy)
// ============================================================================

#[derive(Default, Debug)]
struct ParseStats {
    total_fns: usize,
    total_bbs: usize,
    admitted_bbs: usize,
    admitted_stmts: usize,
    bailout_reasons: BTreeMap<String, usize>,
}

fn parse_place(s: &str) -> Option<Place> {
    let s = s.trim();
    // Handle `(_2.0: usize)` or `(_2.0)` or `_2.0` or `_2`
    let inner = if s.starts_with('(') && s.ends_with(')') {
        let stripped = &s[1..s.len() - 1];
        stripped.split(':').next()?.trim()
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
        let local = loc_s.parse::<u32>().ok()?;
        let field = fld_s.parse::<u32>().ok()?;
        Some(Place { local, field: Some(field) })
    } else {
        let local = inner[1..].parse::<u32>().ok()?;
        Some(Place { local, field: None })
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
    // e.g. `16_usize`, `0_u8`, `-1_i32`, `108315241484954818052912586623518116501_u128`
    if let Some((num_s, ty_s)) = rest.rsplit_once('_') {
        if matches!(ty_s, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
            let v = num_s.parse::<i128>().ok()?;
            return Some(Operand::ConstInt(v, ty_s.to_string()));
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
        "Add" => Some(BinOp::Add),
        "Sub" => Some(BinOp::Sub),
        "Mul" => Some(BinOp::Mul),
        "BitAnd" => Some(BinOp::BitAnd),
        "BitOr" => Some(BinOp::BitOr),
        "BitXor" => Some(BinOp::BitXor),
        "Shl" => Some(BinOp::Shl),
        "Shr" => Some(BinOp::Shr),
        "Eq" => Some(BinOp::Eq),
        "Ne" => Some(BinOp::Ne),
        "Lt" => Some(BinOp::Lt),
        "Le" => Some(BinOp::Le),
        "Gt" => Some(BinOp::Gt),
        "Ge" => Some(BinOp::Ge),
        _ => None,
    }
}

fn classify_unsupported_stmt(line: &str) -> &'static str {
    if line.contains("(*") || line.contains('[') {
        "deref_or_index_mem"
    } else if line.contains("&raw") || line.contains("= &") {
        "ref_or_raw_ptr"
    } else if line.contains("(Transmute)") || line.contains("(PtrToPtr)") || line.contains("PointerCoercion") {
        "transmute_or_ptr_cast"
    } else if line.contains("PtrMetadata(") || line.contains("discriminant(") || line.contains("Len(") {
        "metadata_or_discr"
    } else if line.contains("Checked") || line.contains("WithOverflow") || line.contains("Unchecked") {
        "checked_or_unchecked_arith"
    } else if line.contains("as ") {
        "other_cast"
    } else if line.contains("const ") {
        "complex_const_or_generic"
    } else if line.contains('(') && line.contains(')') {
        "aggregate_or_adt_ctor"
    } else {
        "other_mir_stmt"
    }
}

fn parse_rvalue(rhs: &str) -> Result<Rvalue, &'static str> {
    let rhs = rhs.trim();
    if let Some(op) = parse_operand(rhs) {
        return Ok(Rvalue::Use(op));
    }
    if let Some(rest) = rhs.strip_prefix("Not(").and_then(|x| x.strip_suffix(')')) {
        if let Some(op) = parse_operand(rest) {
            return Ok(Rvalue::UnaryNot(op));
        }
    }
    if let Some(idx) = rhs.find(" as ") {
        if let Some(rest) = rhs[idx + 4..].strip_suffix(" (IntToInt)") {
            let ty = rest.trim();
            if matches!(ty, "u8" | "u16" | "u32" | "u64" | "usize" | "i8" | "i16" | "i32" | "i64" | "isize") {
                if let Some(op) = parse_operand(&rhs[..idx]) {
                    return Ok(Rvalue::CastInt(op, ty.to_string()));
                }
            }
        }
    }
    if let Some(open) = rhs.find('(') {
        if rhs.ends_with(')') {
            let op_name = &rhs[..open];
            if let Some(bop) = parse_binop(op_name) {
                let args = &rhs[open + 1..rhs.len() - 1];
                if let Some((a, b)) = split_top_level_comma(args) {
                    if let (Some(oa), Some(ob)) = (parse_operand(a), parse_operand(b)) {
                        return Ok(Rvalue::BinaryOp(bop, oa, ob));
                    }
                }
            }
        }
    }
    Err(classify_unsupported_stmt(rhs))
}

fn parse_mir_file(path: &str, max_fns: usize) -> (Vec<BasicBlock>, ParseStats) {
    let text = fs::read_to_string(path).expect("read mir file");
    let mut stats = ParseStats::default();
    let mut blocks = Vec::new();

    let mut in_fn = false;
    let mut cur_fn_id: u32 = 0;
    let mut in_bb = false;
    let mut cur_bb_id: u32 = 0;
    let mut bb_lines: Vec<String> = Vec::new();

    let flush_bb = |fn_id: u32, bb_id: u32, lines: &[String], blocks: &mut Vec<BasicBlock>, stats: &mut ParseStats| {
        if lines.is_empty() {
            return;
        }
        stats.total_bbs += 1;
        let mut stmts = Vec::new();
        let mut term_opt: Option<Term> = None;

        for (idx, raw) in lines.iter().enumerate() {
            let line = raw.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let tag = OriginTag { fn_id, bb_id, stmt_idx: idx as u32 };
            let is_last = idx + 1 == lines.len();

            if !is_last {
                let s = line.trim_end_matches(';').trim();
                if let Some(inner) = s.strip_prefix("StorageLive(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() {
                            stmts.push(Stmt::StorageLive { tag, local: p.local });
                            continue;
                        }
                    }
                    *stats.bailout_reasons.entry("storage_marker_complex".into()).or_default() += 1;
                    return;
                }
                if let Some(inner) = s.strip_prefix("StorageDead(").and_then(|x| x.strip_suffix(')')) {
                    if let Some(p) = parse_place(inner) {
                        if p.field.is_none() {
                            stmts.push(Stmt::StorageDead { tag, local: p.local });
                            continue;
                        }
                    }
                    *stats.bailout_reasons.entry("storage_marker_complex".into()).or_default() += 1;
                    return;
                }
                if s.starts_with("nop") || s.starts_with("ConstEvalCounter") {
                    continue;
                }
                if let Some((lhs, rhs)) = s.split_once(" = ") {
                    if let Some(dst) = parse_place(lhs) {
                        match parse_rvalue(rhs) {
                            Ok(rv) => {
                                stmts.push(Stmt::Assign { tag, dst, rv });
                                continue;
                            }
                            Err(reason) => {
                                *stats.bailout_reasons.entry(reason.into()).or_default() += 1;
                                return;
                            }
                        }
                    } else {
                        let reason = if lhs.contains('*') || lhs.contains('[') {
                            "deref_or_index_mem"
                        } else {
                            "complex_lhs_place"
                        };
                        *stats.bailout_reasons.entry(reason.into()).or_default() += 1;
                        return;
                    }
                }
                *stats.bailout_reasons.entry(classify_unsupported_stmt(s).into()).or_default() += 1;
                return;
            } else {
                // Terminator line
                let s = line.trim_end_matches(';').trim();
                if s == "return" {
                    term_opt = Some(Term::Return);
                } else if s == "unreachable" {
                    term_opt = Some(Term::Unreachable);
                } else if let Some(rest) = s.strip_prefix("goto -> bb") {
                    if let Ok(tgt) = rest.trim().parse::<u32>() {
                        term_opt = Some(Term::Goto(tgt));
                    } else {
                        *stats.bailout_reasons.entry("other_terminator".into()).or_default() += 1;
                        return;
                    }
                } else if let Some(rest) = s.strip_prefix("switchInt(") {
                    if let Some((discr_s, tgt_s)) = rest.split_once(") -> ") {
                        if let Some(op) = parse_operand(discr_s) {
                            term_opt = Some(Term::SwitchInt { discr: op, targets: tgt_s.to_string() });
                        } else {
                            *stats.bailout_reasons.entry("switch_complex_discr".into()).or_default() += 1;
                            return;
                        }
                    } else {
                        *stats.bailout_reasons.entry("other_terminator".into()).or_default() += 1;
                        return;
                    }
                } else if s.starts_with("assert(") {
                    // assert(!move _3, "...", ...) -> [success: bb2, unwind continue]
                    let inner = &s["assert(".len()..];
                    if let Some((cond_part, after_comma)) = split_top_level_comma(inner) {
                        let (expected, op_str) = if let Some(stripped) = cond_part.trim().strip_prefix('!') {
                            (false, stripped)
                        } else {
                            (true, cond_part.trim())
                        };
                        if let Some(op) = parse_operand(op_str) {
                            let tgt = after_comma
                                .split("success: bb")
                                .nth(1)
                                .and_then(|x| x.split(|c: char| !c.is_ascii_digit()).next())
                                .and_then(|x| x.parse::<u32>().ok())
                                .unwrap_or(0);
                            let msg = after_comma.split(')').next().unwrap_or("").to_string();
                            term_opt = Some(Term::Assert { cond: op, expected, msg, target: tgt });
                        } else {
                            *stats.bailout_reasons.entry("assert_complex_cond".into()).or_default() += 1;
                            return;
                        }
                    } else {
                        *stats.bailout_reasons.entry("assert_complex_cond".into()).or_default() += 1;
                        return;
                    }
                } else if s.starts_with("drop(") {
                    *stats.bailout_reasons.entry("term_drop".into()).or_default() += 1;
                    return;
                } else if s.starts_with("asm!(") {
                    *stats.bailout_reasons.entry("term_inline_asm".into()).or_default() += 1;
                    return;
                } else if s.contains(" -> [return:") || s.contains(" -> unwind") {
                    // CompCert BTL-style Call barrier: optimize statements BEFORE the Call,
                    // keeping all referenced locals live-out and tracking moved arguments LTR!
                    let mut read_locals = Vec::new();
                    let mut moved_places = Vec::new();
                    let bytes = s.as_bytes();
                    let mut i = 0;
                    let mut call_complex = false;
                    while i < bytes.len() {
                        if s[i..].starts_with("move ") {
                            let rest = &s[i + 5..];
                            let tok: String = rest.chars().take_while(|c| !matches!(c, ',' | ')' | ';' | ' ')).collect();
                            if let Some(p) = parse_place(&tok) {
                                read_locals.push(p.local);
                                moved_places.push(p);
                            } else {
                                call_complex = true;
                            }
                            i += 5;
                            continue;
                        } else if s[i..].starts_with("copy ") {
                            let rest = &s[i + 5..];
                            let tok: String = rest.chars().take_while(|c| !matches!(c, ',' | ')' | ';' | ' ')).collect();
                            if let Some(p) = parse_place(&tok) {
                                read_locals.push(p.local);
                            } else {
                                call_complex = true;
                            }
                            i += 5;
                            continue;
                        }
                        i += 1;
                    }
                    if call_complex {
                        *stats.bailout_reasons.entry("term_call_complex_arg".into()).or_default() += 1;
                        return;
                    }
                    term_opt = Some(Term::CallBarrier { raw: s.to_string(), read_locals, moved_places });
                } else {
                    *stats.bailout_reasons.entry("other_terminator".into()).or_default() += 1;
                    return;
                }
            }
        }

        if let Some(term) = term_opt {
            stats.admitted_bbs += 1;
            stats.admitted_stmts += stmts.len();
            blocks.push(BasicBlock { fn_id, bb_id, stmts, term });
        }
    };

    for line in text.lines() {
        if !in_fn {
            if line.starts_with("fn ") && line.ends_with('{') {
                if stats.total_fns >= max_fns {
                    break;
                }
                in_fn = true;
                cur_fn_id = stats.total_fns as u32;
                stats.total_fns += 1;
            }
            continue;
        }
        if line == "}" {
            if in_bb {
                flush_bb(cur_fn_id, cur_bb_id, &bb_lines, &mut blocks, &mut stats);
                bb_lines.clear();
                in_bb = false;
            }
            in_fn = false;
            continue;
        }
        let trimmed = line.trim();
        if !in_bb {
            if let Some(rest) = trimmed.strip_prefix("bb") {
                if let Some((num_s, tail)) = rest.split_once(':') {
                    if tail.trim() == "{" {
                        if let Ok(id) = num_s.parse::<u32>() {
                            in_bb = true;
                            cur_bb_id = id;
                            bb_lines.clear();
                        }
                    }
                }
            }
        } else if trimmed == "}" {
            flush_bb(cur_fn_id, cur_bb_id, &bb_lines, &mut blocks, &mut stats);
            bb_lines.clear();
            in_bb = false;
        } else if !trimmed.is_empty() {
            bb_lines.push(trimmed.to_string());
        }
    }

    (blocks, stats)
}

// ============================================================================
// 2. Genuine Non-LLVM 4-Pass Superblock Optimizer (Zero opt / Zero llc)
// ============================================================================

#[derive(Default, Debug)]
struct OptStats {
    moves_certified_to_copy: usize,
    move_check_bails: usize,
    copies_propagated: usize,
    consts_folded: usize,
    algebraic_ids_simplified: usize,
    gvn_hits: usize,
    bce_asserts_eliminated: usize,
    dead_stmts_eliminated: usize,
    stmts_before: usize,
    stmts_after: usize,
}

fn eval_const_binop(op: BinOp, a: i128, b: i128, ty: &str) -> Option<Operand> {
    let mask: Option<i128> = match ty {
        "u8" => Some(0xff),
        "u16" => Some(0xffff),
        "u32" => Some(0xffff_ffff),
        "u64" | "usize" => Some(u64::MAX as i128),
        _ => None,
    };
    match op {
        BinOp::Add => mask.map(|m| Operand::ConstInt((a.wrapping_add(b)) & m, ty.into())),
        BinOp::Sub => mask.map(|m| Operand::ConstInt((a.wrapping_sub(b)) & m, ty.into())),
        BinOp::Mul => mask.map(|m| Operand::ConstInt((a.wrapping_mul(b)) & m, ty.into())),
        BinOp::BitAnd => mask.map(|m| Operand::ConstInt((a & b) & m, ty.into())),
        BinOp::BitOr => mask.map(|m| Operand::ConstInt((a | b) & m, ty.into())),
        BinOp::BitXor => mask.map(|m| Operand::ConstInt((a ^ b) & m, ty.into())),
        BinOp::Shl => {
            if b >= 0 && b < 64 {
                mask.map(|m| Operand::ConstInt((a << b) & m, ty.into()))
            } else {
                None
            }
        }
        BinOp::Shr => {
            if b >= 0 && b < 64 && a >= 0 {
                mask.map(|m| Operand::ConstInt((a >> b) & m, ty.into()))
            } else {
                None
            }
        }
        BinOp::Eq => Some(Operand::ConstInt(if a == b { 1 } else { 0 }, "bool".into())),
        BinOp::Ne => Some(Operand::ConstInt(if a != b { 1 } else { 0 }, "bool".into())),
        BinOp::Lt => Some(Operand::ConstInt(if a < b { 1 } else { 0 }, "bool".into())),
        BinOp::Le => Some(Operand::ConstInt(if a <= b { 1 } else { 0 }, "bool".into())),
        BinOp::Gt => Some(Operand::ConstInt(if a > b { 1 } else { 0 }, "bool".into())),
        BinOp::Ge => Some(Operand::ConstInt(if a >= b { 1 } else { 0 }, "bool".into())),
    }
}

fn places_overlap(a: &Place, b: &Place) -> bool {
    if a.local != b.local {
        return false;
    }
    match (a.field, b.field) {
        (None, _) | (_, None) => true,
        (Some(fa), Some(fb)) => fa == fb,
    }
}

fn is_moved(moved: &BTreeSet<Place>, p: &Place) -> bool {
    moved.iter().any(|m| places_overlap(m, p))
}

/// Pass 1: Field-granular certified MoveToCopy enforcing AV-1 (leaf masks) + AV-2 (LTR order).
/// Only rewrites `Move(p) -> Copy(p)` when `p` is guaranteed NOT live-out (StorageDead or overwritten
/// inside the block) AND never read while moved! (Conservative so cross-block movedness is preserved!)
fn pass1_certified_move_to_copy(bb: &BasicBlock, stats: &mut OptStats) -> BasicBlock {
    // Identify locals that are StorageDead or whole-overwritten before exit
    let mut dead_at_exit: BTreeSet<u32> = BTreeSet::new();
    for s in &bb.stmts {
        if let Stmt::StorageDead { local, .. } = s {
            dead_at_exit.insert(*local);
        } else if let Stmt::StorageLive { local, .. } = s {
            dead_at_exit.remove(local);
        }
    }

    // Track field-granular moved set left-to-right; bail out on any use-after-move so we NEVER erase UB!
    let mut moved: BTreeSet<Place> = BTreeSet::new();
    let mut safe_block = true;
    let check_op = |op: &Operand, moved: &mut BTreeSet<Place>, safe: &mut bool| {
        match op {
            Operand::Copy(p) => {
                if is_moved(moved, p) {
                    *safe = false;
                }
            }
            Operand::Move(p) => {
                if is_moved(moved, p) {
                    *safe = false;
                } else {
                    moved.insert(p.clone());
                }
            }
            Operand::ConstInt(_, _) | Operand::ConstUnit => {}
        }
    };

    for st in &bb.stmts {
        match st {
            Stmt::Assign { dst, rv, .. } => {
                match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => check_op(a, &mut moved, &mut safe_block),
                    Rvalue::BinaryOp(_, a, b) => {
                        check_op(a, &mut moved, &mut safe_block);
                        check_op(b, &mut moved, &mut safe_block);
                    }
                }
                moved.retain(|m| !places_overlap(m, dst));
            }
            Stmt::StorageLive { local, .. } | Stmt::StorageDead { local, .. } => {
                moved.retain(|m| m.local != *local);
            }
        }
    }
    match &bb.term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => check_op(discr, &mut moved, &mut safe_block),
        Term::CallBarrier { read_locals, moved_places, .. } => {
            for &l in read_locals {
                if is_moved(&moved, &Place { local: l, field: None }) {
                    safe_block = false;
                }
            }
            for mp in moved_places {
                moved.insert(mp.clone());
            }
        }
        _ => {}
    }

    if !safe_block {
        stats.move_check_bails += 1;
        return bb.clone();
    }

    // Rewrite only moves whose local is dead_at_exit (or cleared before exit), guaranteeing identical post-state!
    let can_demote = |p: &Place| -> bool {
        dead_at_exit.contains(&p.local) || !is_moved(&moved, p)
    };
    let demote_op = |op: &Operand, stats: &mut OptStats| -> Operand {
        if let Operand::Move(p) = op {
            if can_demote(p) {
                stats.moves_certified_to_copy += 1;
                return Operand::Copy(p.clone());
            }
        }
        op.clone()
    };

    let mut out = bb.clone();
    for st in &mut out.stmts {
        if let Stmt::Assign { rv, .. } = st {
            match rv {
                Rvalue::Use(a) => *a = demote_op(a, stats),
                Rvalue::UnaryNot(a) => *a = demote_op(a, stats),
                Rvalue::CastInt(a, _) => *a = demote_op(a, stats),
                Rvalue::BinaryOp(_, a, b) => {
                    *a = demote_op(a, stats);
                    *b = demote_op(b, stats);
                }
            }
        }
    }
    match &mut out.term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => *discr = demote_op(discr, stats),
        _ => {}
    }
    out
}

/// Passes 2+3+4: CopyProp, ConstFold, Algebraic Identities, Strict Superblock GVN, Interval/Bitwise BCE, Dead-Temp DCE.
fn optimize_superblock(bb: &BasicBlock, stats: &mut OptStats) -> BasicBlock {
    stats.stmts_before += bb.stmts.len();
    let mut cur = pass1_certified_move_to_copy(bb, stats);

    // Map each place to its current known copy/const source (invalidated on any overlapping write/move/StorageLive/Dead)
    let mut alias_map: HashMap<Place, Operand> = HashMap::new();
    // Strict GVN map: pure Rvalue -> Place holding it (invalidated whenever any operand's place is mutated)
    let mut gvn_map: HashMap<Rvalue, Place> = HashMap::new();
    // Non-negative interval bounds [lo, hi] for BCE
    let mut intervals: HashMap<Place, (i128, i128)> = HashMap::new();

    let invalidate_place = |p: &Place,
                            alias_map: &mut HashMap<Place, Operand>,
                            gvn_map: &mut HashMap<Rvalue, Place>,
                            intervals: &mut HashMap<Place, (i128, i128)>| {
        alias_map.retain(|k, v| {
            if places_overlap(k, p) {
                return false;
            }
            match v {
                Operand::Copy(vp) | Operand::Move(vp) => !places_overlap(vp, p),
                _ => true,
            }
        });
        gvn_map.retain(|rv, holder| {
            if places_overlap(holder, p) {
                return false;
            }
            let mentions = |op: &Operand| match op {
                Operand::Copy(op_p) | Operand::Move(op_p) => places_overlap(op_p, p),
                _ => false,
            };
            match rv {
                Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => !mentions(a),
                Rvalue::BinaryOp(_, a, b) => !mentions(a) && !mentions(b),
            }
        });
        intervals.retain(|k, _| !places_overlap(k, p));
    };

    let rewrite_op = |op: &Operand, alias_map: &HashMap<Place, Operand>, stats: &mut OptStats| -> Operand {
        if let Operand::Copy(p) = op {
            if let Some(repl) = alias_map.get(p) {
                if matches!(repl, Operand::Copy(_) | Operand::ConstInt(_, _) | Operand::ConstUnit) {
                    stats.copies_propagated += 1;
                    return repl.clone();
                }
            }
        }
        op.clone()
    };

    let op_interval = |op: &Operand, intervals: &HashMap<Place, (i128, i128)>| -> Option<(i128, i128)> {
        match op {
            Operand::ConstInt(v, _) => Some((*v, *v)),
            Operand::Copy(p) | Operand::Move(p) => intervals.get(p).copied(),
            Operand::ConstUnit => None,
        }
    };

    let mut new_stmts = Vec::with_capacity(cur.stmts.len());
    for st in &cur.stmts {
        match st {
            Stmt::StorageLive { local, .. } | Stmt::StorageDead { local, .. } => {
                invalidate_place(&Place { local: *local, field: None }, &mut alias_map, &mut gvn_map, &mut intervals);
                new_stmts.push(st.clone());
            }
            Stmt::Assign { tag, dst, rv } => {
                // Step A: Rewrite operands via copy/const propagation (ONLY for Copy; preserve Move deinit!)
                let mut rv1 = match rv {
                    Rvalue::Use(a) => Rvalue::Use(rewrite_op(a, &alias_map, stats)),
                    Rvalue::UnaryNot(a) => Rvalue::UnaryNot(rewrite_op(a, &alias_map, stats)),
                    Rvalue::CastInt(a, ty) => Rvalue::CastInt(rewrite_op(a, &alias_map, stats), ty.clone()),
                    Rvalue::BinaryOp(op, a, b) => {
                        let na = rewrite_op(a, &alias_map, stats);
                        let nb = rewrite_op(b, &alias_map, stats);
                        Rvalue::BinaryOp(*op, na, nb)
                    }
                };

                // If any operand was a Move, invalidate that moved place before updating dst!
                let mark_moves = |rv: &Rvalue,
                                  alias_map: &mut HashMap<Place, Operand>,
                                  gvn_map: &mut HashMap<Rvalue, Place>,
                                  intervals: &mut HashMap<Place, (i128, i128)>| {
                    let mut handle = |op: &Operand| {
                        if let Operand::Move(p) = op {
                            invalidate_place(p, alias_map, gvn_map, intervals);
                        }
                    };
                    match rv {
                        Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => handle(a),
                        Rvalue::BinaryOp(_, a, b) => {
                            handle(a);
                            handle(b);
                        }
                    }
                };
                mark_moves(&rv1, &mut alias_map, &mut gvn_map, &mut intervals);

                // Step B: Constant folding & algebraic identities
                let has_move = match &rv1 {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Move(_)),
                    Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Move(_)) || matches!(b, Operand::Move(_)),
                };
                if !has_move {
                    rv1 = match rv1 {
                        Rvalue::UnaryNot(Operand::ConstInt(v, ref ty)) if ty == "bool" => {
                            stats.consts_folded += 1;
                            Rvalue::Use(Operand::ConstInt(if v == 0 { 1 } else { 0 }, "bool".into()))
                        }
                        Rvalue::BinaryOp(op, Operand::ConstInt(a, ref ty1), Operand::ConstInt(b, ref ty2)) if ty1 == ty2 => {
                            if let Some(c) = eval_const_binop(op, a, b, ty1) {
                                stats.consts_folded += 1;
                                Rvalue::Use(c)
                            } else {
                                Rvalue::BinaryOp(op, Operand::ConstInt(a, ty1.clone()), Operand::ConstInt(b, ty2.clone()))
                            }
                        }
                        Rvalue::BinaryOp(BinOp::Add, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::Sub, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::BitOr, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::BitXor, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::Shl, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::Shr, a, Operand::ConstInt(0, _))
                        | Rvalue::BinaryOp(BinOp::Mul, a, Operand::ConstInt(1, _)) => {
                            stats.algebraic_ids_simplified += 1;
                            Rvalue::Use(a)
                        }
                        Rvalue::BinaryOp(BinOp::Add, Operand::ConstInt(0, _), b)
                        | Rvalue::BinaryOp(BinOp::BitOr, Operand::ConstInt(0, _), b)
                        | Rvalue::BinaryOp(BinOp::BitXor, Operand::ConstInt(0, _), b)
                        | Rvalue::BinaryOp(BinOp::Mul, Operand::ConstInt(1, _), b) => {
                            stats.algebraic_ids_simplified += 1;
                            Rvalue::Use(b)
                        }
                        Rvalue::BinaryOp(BinOp::Lt, ref a, ref b) => {
                            if let (Some((_, ahi)), Some((blo, _))) = (op_interval(a, &intervals), op_interval(b, &intervals)) {
                                if ahi < blo {
                                    stats.consts_folded += 1;
                                    Rvalue::Use(Operand::ConstInt(1, "bool".into()))
                                } else {
                                    Rvalue::BinaryOp(BinOp::Lt, a.clone(), b.clone())
                                }
                            } else {
                                Rvalue::BinaryOp(BinOp::Lt, a.clone(), b.clone())
                            }
                        }
                        other => other,
                    };

                    // Step C: Strict Superblock GVN (only pure non-trivial expressions)
                    if !matches!(rv1, Rvalue::Use(_)) {
                        if let Some(prev_holder) = gvn_map.get(&rv1) {
                            stats.gvn_hits += 1;
                            rv1 = Rvalue::Use(Operand::Copy(prev_holder.clone()));
                        }
                    }
                }

                // Compute interval for dst BEFORE invalidating dst
                let new_iv = match &rv1 {
                    Rvalue::Use(a) => op_interval(a, &intervals),
                    Rvalue::BinaryOp(BinOp::BitAnd, _, Operand::ConstInt(m, _)) if *m >= 0 => Some((0, *m)),
                    Rvalue::BinaryOp(BinOp::BitAnd, Operand::ConstInt(m, _), _) if *m >= 0 => Some((0, *m)),
                    Rvalue::CastInt(_, ty) => match ty.as_str() {
                        "u8" => Some((0, 255)),
                        "u16" => Some((0, 65535)),
                        "u32" => Some((0, u32::MAX as i128)),
                        _ => None,
                    },
                    _ => None,
                };

                invalidate_place(dst, &mut alias_map, &mut gvn_map, &mut intervals);
                if let Some(iv) = new_iv {
                    intervals.insert(dst.clone(), iv);
                }
                if !has_move {
                    if let Rvalue::Use(ref op) = rv1 {
                        if matches!(op, Operand::Copy(p) if !places_overlap(p, dst))
                            || matches!(op, Operand::ConstInt(_, _) | Operand::ConstUnit)
                        {
                            alias_map.insert(dst.clone(), op.clone());
                        }
                    } else {
                        let mentions_dst = match &rv1 {
                            Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => {
                                matches!(a, Operand::Copy(p) if places_overlap(p, dst))
                            }
                            Rvalue::BinaryOp(_, a, b) => {
                                matches!(a, Operand::Copy(p) if places_overlap(p, dst))
                                    || matches!(b, Operand::Copy(p) if places_overlap(p, dst))
                            }
                        };
                        if !mentions_dst {
                            gvn_map.insert(rv1.clone(), dst.clone());
                        }
                    }
                }

                new_stmts.push(Stmt::Assign { tag: *tag, dst: dst.clone(), rv: rv1 });
            }
        }
    }

    // Rewrite terminator operand & check interval/const BCE
    let new_term = match &cur.term {
        Term::SwitchInt { discr, targets } => Term::SwitchInt {
            discr: rewrite_op(discr, &alias_map, stats),
            targets: targets.clone(),
        },
        Term::Assert { cond, expected, msg, target } => {
            let nc = rewrite_op(cond, &alias_map, stats);
            let provably_ok = matches!(&nc, Operand::ConstInt(v, ty) if ty == "bool" && ((*v != 0) == *expected));
            if provably_ok {
                stats.bce_asserts_eliminated += 1;
                Term::Goto(*target)
            } else {
                Term::Assert { cond: nc, expected: *expected, msg: msg.clone(), target: *target }
            }
        }
        other => other.clone(),
    };

    // Dead temporary elimination (only for locals explicitly StorageDead before exit AND pure non-Move RHS)
    let mut live_locals: BTreeSet<u32> = BTreeSet::new();
    let mut dead_before_exit: BTreeSet<u32> = BTreeSet::new();
    for s in &new_stmts {
        if let Stmt::StorageDead { local, .. } = s {
            dead_before_exit.insert(*local);
        } else if let Stmt::StorageLive { local, .. } = s {
            dead_before_exit.remove(local);
        }
    }
    // Start with terminator uses + every local NOT StorageDead before exit
    let add_op_use = |op: &Operand, live: &mut BTreeSet<u32>| {
        if let Operand::Copy(p) | Operand::Move(p) = op {
            live.insert(p.local);
        }
    };
    match &new_term {
        Term::SwitchInt { discr, .. } | Term::Assert { cond: discr, .. } => add_op_use(discr, &mut live_locals),
        Term::CallBarrier { read_locals, .. } => {
            for &l in read_locals {
                live_locals.insert(l);
            }
        }
        _ => {}
    }
    for s in &new_stmts {
        if let Stmt::Assign { dst, .. } = s {
            if !dead_before_exit.contains(&dst.local) {
                live_locals.insert(dst.local);
            }
        }
    }
    let mut kept_rev = Vec::with_capacity(new_stmts.len());
    for s in new_stmts.iter().rev() {
        match s {
            Stmt::Assign { dst, rv, .. } => {
                let has_move = match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => matches!(a, Operand::Move(_)),
                    Rvalue::BinaryOp(_, a, b) => matches!(a, Operand::Move(_)) || matches!(b, Operand::Move(_)),
                };
                if !has_move && dst.field.is_none() && !live_locals.contains(&dst.local) && dead_before_exit.contains(&dst.local) {
                    stats.dead_stmts_eliminated += 1;
                    continue;
                }
                if dst.field.is_none() {
                    live_locals.remove(&dst.local);
                }
                match rv {
                    Rvalue::Use(a) | Rvalue::UnaryNot(a) | Rvalue::CastInt(a, _) => add_op_use(a, &mut live_locals),
                    Rvalue::BinaryOp(_, a, b) => {
                        add_op_use(a, &mut live_locals);
                        add_op_use(b, &mut live_locals);
                    }
                }
                kept_rev.push(s.clone());
            }
            Stmt::StorageDead { local, .. } => {
                live_locals.remove(local);
                kept_rev.push(s.clone());
            }
            Stmt::StorageLive { local, .. } => {
                live_locals.remove(local);
                kept_rev.push(s.clone());
            }
        }
    }
    kept_rev.reverse();
    cur.stmts = kept_rev;
    cur.term = new_term;
    stats.stmts_after += cur.stmts.len();
    cur
}

// ============================================================================
// 3. Independent Hash-Consed Symbolic Equivalence Validator (CompCert BTL Style)
// ============================================================================

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
    fn new() -> Self {
        Self { nodes: Vec::new(), intern: HashMap::new() }
    }

    fn mk(&mut self, e: SymExpr) -> u32 {
        if let Some(&id) = self.intern.get(&e) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(e.clone());
        self.intern.insert(e, id);
        id
    }

    fn iv(&self, id: u32) -> Option<(i128, i128)> {
        match &self.nodes[id as usize] {
            SymExpr::ConstInt(v, _) => Some((*v, *v)),
            SymExpr::Bin(BinOp::BitAnd, a, b) => {
                if let SymExpr::ConstInt(m, _) = self.nodes[*b as usize] {
                    if m >= 0 { return Some((0, m)); }
                }
                if let SymExpr::ConstInt(m, _) = self.nodes[*a as usize] {
                    if m >= 0 { return Some((0, m)); }
                }
                None
            }
            SymExpr::CastInt(_, ty) => match ty.as_str() {
                "u8" => Some((0, 255)),
                "u16" => Some((0, 65535)),
                "u32" => Some((0, u32::MAX as i128)),
                _ => None,
            },
            _ => None,
        }
    }

    /// Sound algebraic normalizer used by the independent validator
    fn mk_bin(&mut self, op: BinOp, a: u32, b: u32) -> u32 {
        let na = self.nodes[a as usize].clone();
        let nb = self.nodes[b as usize].clone();
        if let (SymExpr::ConstInt(va, ta), SymExpr::ConstInt(vb, tb)) = (&na, &nb) {
            if ta == tb {
                if let Some(Operand::ConstInt(vc, tc)) = eval_const_binop(op, *va, *vb, ta) {
                    return self.mk(SymExpr::ConstInt(vc, tc));
                }
            }
        }
        match (op, &na, &nb) {
            (BinOp::Add | BinOp::Sub | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr, _, SymExpr::ConstInt(0, _))
            | (BinOp::Mul, _, SymExpr::ConstInt(1, _)) => a,
            (BinOp::Add | BinOp::BitOr | BinOp::BitXor, SymExpr::ConstInt(0, _), _)
            | (BinOp::Mul, SymExpr::ConstInt(1, _), _) => b,
            (BinOp::Lt, _, _) => {
                if let (Some((_, ahi)), Some((blo, _))) = (self.iv(a), self.iv(b)) {
                    if ahi < blo {
                        return self.mk(SymExpr::ConstInt(1, "bool".into()));
                    }
                }
                self.mk(SymExpr::Bin(op, a, b))
            }
            _ => self.mk(SymExpr::Bin(op, a, b)),
        }
    }

    fn mk_not(&mut self, a: u32) -> u32 {
        if let SymExpr::ConstInt(v, ty) = &self.nodes[a as usize] {
            if ty == "bool" {
                return self.mk(SymExpr::ConstInt(if *v == 0 { 1 } else { 0 }, "bool".into()));
            }
        }
        self.mk(SymExpr::Not(a))
    }
}

#[derive(Debug, PartialEq, Eq)]
enum SymTerm {
    Goto(u32),
    Return,
    SwitchInt(u32, String),
    Assert(u32, bool, String, u32),
    CallBarrier(String, Vec<u32>),
    Unreachable,
}

#[derive(Debug, PartialEq, Eq)]
struct SymSummary {
    move_ub: bool,
    live_out: BTreeMap<Place, u32>,
    moved_out: BTreeSet<Place>,
    dead_locals: BTreeSet<u32>,
    term: SymTerm,
}

fn sym_exec_block(bb: &BasicBlock, arena: &mut SymArena, local_granular_bug: bool) -> SymSummary {
    let mut env: BTreeMap<Place, u32> = BTreeMap::new();
    let mut moved: BTreeSet<Place> = BTreeSet::new();
    let mut dead: BTreeSet<u32> = BTreeSet::new();
    let mut move_ub = false;

    let eval_op = |op: &Operand,
                       env: &BTreeMap<Place, u32>,
                       moved: &mut BTreeSet<Place>,
                       dead: &BTreeSet<u32>,
                       move_ub: &mut bool,
                       arena: &mut SymArena|
     -> u32 {
        match op {
            Operand::ConstInt(v, ty) => arena.mk(SymExpr::ConstInt(*v, ty.clone())),
            Operand::ConstUnit => arena.mk(SymExpr::ConstUnit),
            Operand::Copy(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) {
                    *move_ub = true;
                }
                *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())))
            }
            Operand::Move(p) => {
                if dead.contains(&p.local) || is_moved(moved, p) {
                    *move_ub = true;
                }
                let val = *env.get(p).unwrap_or(&arena.mk(SymExpr::Init(p.clone())));
                if local_granular_bug {
                    moved.insert(Place { local: p.local, field: None });
                } else {
                    moved.insert(p.clone());
                }
                val
            }
        }
    };

    for st in &bb.stmts {
        match st {
            Stmt::StorageLive { local, .. } => {
                dead.remove(local);
                moved.retain(|m| m.local != *local);
                env.retain(|k, _| k.local != *local);
            }
            Stmt::StorageDead { local, .. } => {
                dead.insert(*local);
                moved.retain(|m| m.local != *local);
                env.retain(|k, _| k.local != *local);
            }
            Stmt::Assign { dst, rv, .. } => {
                let val = match rv {
                    Rvalue::Use(a) => eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena),
                    Rvalue::UnaryNot(a) => {
                        let ea = eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena);
                        arena.mk_not(ea)
                    }
                    Rvalue::CastInt(a, ty) => {
                        let ea = eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena);
                        arena.mk(SymExpr::CastInt(ea, ty.clone()))
                    }
                    Rvalue::BinaryOp(op, a, b) => {
                        let ea = eval_op(a, &env, &mut moved, &dead, &mut move_ub, arena);
                        let eb = eval_op(b, &env, &mut moved, &dead, &mut move_ub, arena);
                        arena.mk_bin(*op, ea, eb)
                    }
                };
                dead.remove(&dst.local);
                moved.retain(|m| !places_overlap(m, dst));
                env.retain(|k, _| !places_overlap(k, dst));
                env.insert(dst.clone(), val);
            }
        }
    }

    let term = match &bb.term {
        Term::Goto(t) => SymTerm::Goto(*t),
        Term::Return => SymTerm::Return,
        Term::Unreachable => SymTerm::Unreachable,
        Term::CallBarrier { raw, read_locals, moved_places } => {
            let mut arg_vals = Vec::with_capacity(read_locals.len());
            for &l in read_locals {
                let p = Place { local: l, field: None };
                if dead.contains(&l) || is_moved(&moved, &p) {
                    move_ub = true;
                }
                arg_vals.push(*env.get(&p).unwrap_or(&arena.mk(SymExpr::Init(p))));
            }
            for mp in moved_places {
                moved.insert(mp.clone());
            }
            SymTerm::CallBarrier(raw.clone(), arg_vals)
        }
        Term::SwitchInt { discr, targets } => {
            let ed = eval_op(discr, &env, &mut moved, &dead, &mut move_ub, arena);
            SymTerm::SwitchInt(ed, targets.clone())
        }
        Term::Assert { cond, expected, msg, target } => {
            let ec = eval_op(cond, &env, &mut moved, &dead, &mut move_ub, arena);
            // Discharge provably-true assert identically to Goto(*target)!
            let is_const_ok = matches!(&arena.nodes[ec as usize], SymExpr::ConstInt(v, ty) if ty == "bool" && ((*v != 0) == *expected));
            if is_const_ok {
                SymTerm::Goto(*target)
            } else {
                SymTerm::Assert(ec, *expected, msg.clone(), *target)
            }
        }
    };

    // Filter live_out to drop any entry that maps back to its exact untouched initial value `Init(p)`
    let mut live_out = BTreeMap::new();
    for (p, v) in env {
        if dead.contains(&p.local) {
            continue;
        }
        if arena.nodes[v as usize] != SymExpr::Init(p.clone()) {
            live_out.insert(p, v);
        }
    }
    moved.retain(|m| !dead.contains(&m.local));

    SymSummary { move_ub, live_out, moved_out: moved, dead_locals: dead, term }
}

fn validate_superblock_pair(src: &BasicBlock, opt: &BasicBlock) -> Result<(), String> {
    let mut arena = SymArena::new();
    let s1 = sym_exec_block(src, &mut arena, false);
    let s2 = sym_exec_block(opt, &mut arena, false);
    if s1.move_ub != s2.move_ub {
        return Err(format!("move_ub mismatch: src={} opt={}", s1.move_ub, s2.move_ub));
    }
    if s1.move_ub {
        return Ok(());
    }
    if s1.term != s2.term {
        return Err(format!("terminator mismatch: src={:?} opt={:?}", s1.term, s2.term));
    }
    if s1.dead_locals != s2.dead_locals {
        return Err("dead_locals mismatch".into());
    }
    if s1.moved_out != s2.moved_out {
        return Err(format!("moved_out mismatch: src={:?} opt={:?}", s1.moved_out, s2.moved_out));
    }
    if s1.live_out != s2.live_out {
        return Err("live_out symbolic state mismatch".into());
    }
    Ok(())
}

// ============================================================================
// 4. Six Adversarial Fault-Injection Negative Controls (Must Reject 6/6)
// ============================================================================

fn run_negative_controls() -> Vec<(String, bool, String)> {
    let t = OriginTag { fn_id: 999, bb_id: 0, stmt_idx: 0 };
    let p = |l: u32, f: Option<u32>| Place { local: l, field: f };
    let mut results = Vec::new();

    // BUG-1: Drop non-provable bounds check Assert(Lt(_1, _2)) -> Goto
    let src1 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![Stmt::Assign {
            tag: t, dst: p(3, None),
            rv: Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(p(1, None)), Operand::Copy(p(2, None))),
        }],
        term: Term::Assert { cond: Operand::Copy(p(3, None)), expected: true, msg: "oob".into(), target: 1 },
    };
    let mut bug1 = src1.clone();
    bug1.term = Term::Goto(1);
    let r1 = validate_superblock_pair(&src1, &bug1);
    results.push(("BUG1_drop_unproved_bce".into(), r1.is_err(), r1.err().unwrap_or_default()));

    // BUG-2: Swap M4 operand order (copy _1, move _1) -> (move _1, copy _1)
    let src2 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![Stmt::Assign {
            tag: t, dst: p(0, None),
            rv: Rvalue::BinaryOp(BinOp::Add, Operand::Copy(p(1, None)), Operand::Move(p(1, None))),
        }],
        term: Term::Return,
    };
    let bug2 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![Stmt::Assign {
            tag: t, dst: p(0, None),
            rv: Rvalue::BinaryOp(BinOp::Add, Operand::Move(p(1, None)), Operand::Copy(p(1, None))),
        }],
        term: Term::Return,
    };
    let r2 = validate_superblock_pair(&src2, &bug2);
    results.push(("BUG2_swap_M4_copy_move_order".into(), r2.is_err(), r2.err().unwrap_or_default()));

    // BUG-3: Unguarded MoveToCopy erasing real use-after-move UB (move _1; copy _1)
    let src3 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![
            Stmt::Assign { tag: t, dst: p(2, None), rv: Rvalue::Use(Operand::Move(p(1, None))) },
            Stmt::Assign { tag: t, dst: p(0, None), rv: Rvalue::Use(Operand::Copy(p(1, None))) },
        ],
        term: Term::Return,
    };
    let bug3 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![
            Stmt::Assign { tag: t, dst: p(2, None), rv: Rvalue::Use(Operand::Copy(p(1, None))) },
            Stmt::Assign { tag: t, dst: p(0, None), rv: Rvalue::Use(Operand::Copy(p(1, None))) },
        ],
        term: Term::Return,
    };
    let r3 = validate_superblock_pair(&src3, &bug3);
    results.push(("BUG3_unguarded_move_to_copy_erases_ub".into(), r3.is_err(), r3.err().unwrap_or_default()));

    // BUG-4: Local-granular deinit breaks valid M3 sibling field moves move(_1.0); move(_1.1)
    let src4 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![
            Stmt::Assign { tag: t, dst: p(2, None), rv: Rvalue::Use(Operand::Move(p(1, Some(0)))) },
            Stmt::Assign { tag: t, dst: p(3, None), rv: Rvalue::Use(Operand::Move(p(1, Some(1)))) },
        ],
        term: Term::Return,
    };
    let mut arena4 = SymArena::new();
    let fg = sym_exec_block(&src4, &mut arena4, false);
    let lg = sym_exec_block(&src4, &mut arena4, true);
    let caught4 = !fg.move_ub && lg.move_ub;
    results.push(("BUG4_local_granular_breaks_M3_sibling_moves".into(), caught4, format!("field_granular_ub={} local_granular_ub={}", fg.move_ub, lg.move_ub)));

    // BUG-5: Unsound bitwise BCE: (x & 255) < 200 falsely folded to Goto (255 >= 200!)
    let src5 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![
            Stmt::Assign { tag: t, dst: p(2, None), rv: Rvalue::BinaryOp(BinOp::BitAnd, Operand::Copy(p(1, None)), Operand::ConstInt(255, "usize".into())) },
            Stmt::Assign { tag: t, dst: p(3, None), rv: Rvalue::BinaryOp(BinOp::Lt, Operand::Copy(p(2, None)), Operand::ConstInt(200, "usize".into())) },
        ],
        term: Term::Assert { cond: Operand::Copy(p(3, None)), expected: true, msg: "oob".into(), target: 1 },
    };
    let mut bug5 = src5.clone();
    bug5.term = Term::Goto(1);
    let r5 = validate_superblock_pair(&src5, &bug5);
    results.push(("BUG5_unsound_bitwise_bce_255_lt_200".into(), r5.is_err(), r5.err().unwrap_or_default()));

    // BUG-6: Delete live-out write `_0 = Add(_1, 1)`
    let src6 = BasicBlock {
        fn_id: 999, bb_id: 0,
        stmts: vec![Stmt::Assign {
            tag: t, dst: p(0, None),
            rv: Rvalue::BinaryOp(BinOp::Add, Operand::Copy(p(1, None)), Operand::ConstInt(1, "usize".into())),
        }],
        term: Term::Return,
    };
    let bug6 = BasicBlock { fn_id: 999, bb_id: 0, stmts: vec![], term: Term::Return };
    let r6 = validate_superblock_pair(&src6, &bug6);
    results.push(("BUG6_delete_live_out_assign".into(), r6.is_err(), r6.err().unwrap_or_default()));

    results
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: e2_1_real_btl_replay <mir_file1> [<mir_file2> ...]");
        std::process::exit(2);
    }

    let neg = run_negative_controls();
    let neg_passed = neg.iter().filter(|(_, ok, _)| *ok).count();

    let mut per_corpus = Vec::new();
    let mut grand_fns = 0usize;
    let mut grand_bbs = 0usize;
    let mut grand_admitted = 0usize;
    let mut grand_validated_ok = 0usize;
    let mut grand_validated_fail = 0usize;
    let mut grand_stmts_before = 0usize;
    let mut grand_stmts_after = 0usize;
    let mut grand_opt_ms = 0.0f64;
    let mut grand_val_ms = 0.0f64;
    let mut grand_moves_demoted = 0usize;
    let mut grand_copies_prop = 0usize;
    let mut grand_const_fold = 0usize;
    let mut grand_alg_id = 0usize;
    let mut grand_gvn = 0usize;
    let mut grand_bce = 0usize;
    let mut grand_dce = 0usize;
    let mut grand_bailouts: BTreeMap<String, usize> = BTreeMap::new();

    for path in &args[1..] {
        let name = std::path::Path::new(path).file_name().unwrap().to_string_lossy().to_string();
        let t_parse = Instant::now();
        let (blocks, pstats) = parse_mir_file(path, 100_000);
        let parse_ms = t_parse.elapsed().as_secs_f64() * 1000.0;

        let mut ostats = OptStats::default();
        let t_opt = Instant::now();
        let opt_blocks: Vec<BasicBlock> = blocks.iter().map(|b| optimize_superblock(b, &mut ostats)).collect();
        let opt_ms = t_opt.elapsed().as_secs_f64() * 1000.0;

        let t_val = Instant::now();
        let mut ok_cnt = 0usize;
        let mut fail_cnt = 0usize;
        let mut sample_fails = Vec::new();
        for (src, opt) in blocks.iter().zip(opt_blocks.iter()) {
            match validate_superblock_pair(src, opt) {
                Ok(()) => ok_cnt += 1,
                Err(e) => {
                    fail_cnt += 1;
                    if sample_fails.len() < 5 {
                        sample_fails.push(format!("fn{} bb{}: {}", src.fn_id, src.bb_id, e));
                    }
                }
            }
        }
        let val_ms = t_val.elapsed().as_secs_f64() * 1000.0;

        grand_fns += pstats.total_fns;
        grand_bbs += pstats.total_bbs;
        grand_admitted += pstats.admitted_bbs;
        grand_validated_ok += ok_cnt;
        grand_validated_fail += fail_cnt;
        grand_stmts_before += ostats.stmts_before;
        grand_stmts_after += ostats.stmts_after;
        grand_opt_ms += opt_ms;
        grand_val_ms += val_ms;
        grand_moves_demoted += ostats.moves_certified_to_copy;
        grand_copies_prop += ostats.copies_propagated;
        grand_const_fold += ostats.consts_folded;
        grand_alg_id += ostats.algebraic_ids_simplified;
        grand_gvn += ostats.gvn_hits;
        grand_bce += ostats.bce_asserts_eliminated;
        grand_dce += ostats.dead_stmts_eliminated;
        for (k, v) in &pstats.bailout_reasons {
            *grand_bailouts.entry(k.clone()).or_default() += v;
        }

        per_corpus.push((name, pstats, ostats, parse_ms, opt_ms, val_ms, ok_cnt, fail_cnt, sample_fails));
    }

    // Print clean JSON to stdout
    println!("{{");
    println!("  \"benchmark\": \"E2-1_T02_real_non_llvm_btl_superblock_replay\",");
    println!("  \"negative_controls\": {{");
    println!("    \"passed\": {}, \"total\": {},", neg_passed, neg.len());
    println!("    \"cases\": [");
    for (i, (cname, ok, detail)) in neg.iter().enumerate() {
        let comma = if i + 1 < neg.len() { "," } else { "" };
        println!("      {{\"name\": {:?}, \"rejected\": {}, \"detail\": {:?}}}{}", cname, ok, detail, comma);
    }
    println!("    ]");
    println!("  }},");
    println!("  \"totals\": {{");
    println!("    \"total_fns\": {},", grand_fns);
    println!("    \"total_bbs\": {},", grand_bbs);
    println!("    \"admitted_pure_scalar_bbs\": {},", grand_admitted);
    println!("    \"admitted_bb_pct\": {:.2},", 100.0 * (grand_admitted as f64) / (grand_bbs.max(1) as f64));
    println!("    \"validated_ok\": {},", grand_validated_ok);
    println!("    \"validated_fail\": {},", grand_validated_fail);
    println!("    \"stmts_before\": {},", grand_stmts_before);
    println!("    \"stmts_after\": {},", grand_stmts_after);
    println!("    \"stmt_reduction_pct\": {:.2},", 100.0 * ((grand_stmts_before - grand_stmts_after) as f64) / (grand_stmts_before.max(1) as f64));
    println!("    \"moves_certified_to_copy\": {},", grand_moves_demoted);
    println!("    \"copies_propagated\": {},", grand_copies_prop);
    println!("    \"consts_folded\": {},", grand_const_fold);
    println!("    \"algebraic_ids_simplified\": {},", grand_alg_id);
    println!("    \"gvn_hits\": {},", grand_gvn);
    println!("    \"bce_asserts_eliminated\": {},", grand_bce);
    println!("    \"dead_stmts_eliminated\": {},", grand_dce);
    println!("    \"opt_ms\": {:.3},", grand_opt_ms);
    println!("    \"validate_ms\": {:.3},", grand_val_ms);
    println!("    \"validate_bbs_per_sec\": {:.1},", (grand_admitted as f64) / (grand_val_ms / 1000.0).max(1e-9));
    println!("    \"validate_stmts_per_sec\": {:.1}", (grand_stmts_before as f64) / (grand_val_ms / 1000.0).max(1e-9));
    println!("  }},");
    println!("  \"bailout_taxonomy\": {{");
    let blen = grand_bailouts.len();
    for (i, (k, v)) in grand_bailouts.iter().enumerate() {
        let comma = if i + 1 < blen { "," } else { "" };
        println!("    {:?}: {}{}", k, v, comma);
    }
    println!("  }},");
    println!("  \"corpora\": [");
    for (i, (name, pstats, ostats, parse_ms, opt_ms, val_ms, ok_cnt, fail_cnt, sfails)) in per_corpus.iter().enumerate() {
        let comma = if i + 1 < per_corpus.len() { "," } else { "" };
        println!(
            "    {{\"file\": {:?}, \"fns\": {}, \"bbs\": {}, \"admitted_bbs\": {}, \"admitted_pct\": {:.2}, \"stmts_before\": {}, \"stmts_after\": {}, \"moves_demoted\": {}, \"copies_prop\": {}, \"const_fold\": {}, \"gvn\": {}, \"bce_elim\": {}, \"dce\": {}, \"validated_ok\": {}, \"validated_fail\": {}, \"parse_ms\": {:.2}, \"opt_ms\": {:.2}, \"validate_ms\": {:.2}, \"sample_fails\": {:?}}}{}",
            name, pstats.total_fns, pstats.total_bbs, pstats.admitted_bbs,
            100.0 * (pstats.admitted_bbs as f64) / (pstats.total_bbs.max(1) as f64),
            ostats.stmts_before, ostats.stmts_after, ostats.moves_certified_to_copy,
            ostats.copies_propagated, ostats.consts_folded, ostats.gvn_hits,
            ostats.bce_asserts_eliminated, ostats.dead_stmts_eliminated,
            ok_cnt, fail_cnt, parse_ms, opt_ms, val_ms, sfails, comma
        );
    }
    println!("  ]");
    println!("}}");
}
