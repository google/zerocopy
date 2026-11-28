// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Constructs that real C11 and C++20 code needs beyond the first two rungs:
//! comparisons used as `int`, brace initializers and compound literals,
//! read-only static locals, externalized callees, block-scope lifetimes,
//! `std::nullptr_t`, and `--entry` reachability. Every fixture is captured
//! from `tests/fixtures/src/` as described in `README.md`.

#![recursion_limit = "256"]

use std::path::PathBuf;

use anneal_lower_cpp::{
    ir::{BinOp, Body, Expr, Program, Sign, Stmt, Terminator, Ty, Width},
    lower_bundle_json, LowerError, Options,
};

fn fixture(name: &str) -> String {
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(format!("tests/fixtures/{name}.json"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("missing fixture {name}.json: {e}"))
}

fn lower_entry(name: &str, entry: Option<&str>) -> Result<Program, LowerError> {
    lower_bundle_json(&fixture(name), &Options { entry: entry.map(str::to_owned) })
}

fn lower_ok(name: &str) -> Program {
    lower_entry(name, None).unwrap_or_else(|e| panic!("{name}: {e}"))
}

fn body<'p>(p: &'p Program, symbol: &str) -> &'p Body {
    p.bodies.iter().find(|b| b.identity == symbol).unwrap_or_else(|| panic!("no body `{symbol}`"))
}

fn local(b: &Body, name: &str) -> usize {
    b.locals
        .iter()
        .position(|l| l.debug_name == name)
        .unwrap_or_else(|| panic!("no local `{name}`"))
}

/// Every expression in `b`, including subexpressions.
fn exprs(b: &Body) -> Vec<&Expr> {
    fn walk<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
        out.push(e);
        match e {
            Expr::ConstInt(..)
            | Expr::ConstBool(_)
            | Expr::NullPtr(_)
            | Expr::ReadPlace(..)
            | Expr::AddrOf(..) => {}
            Expr::Unary(_, _, a)
            | Expr::IntCast(.., a)
            | Expr::IntToBool(a)
            | Expr::BoolToInt(_, _, a)
            | Expr::PtrCast(_, a)
            | Expr::BitCast(_, _, a) => walk(a, out),
            Expr::Binary(_, _, a, c) | Expr::PtrAdd(_, _, a, c) => {
                walk(a, out);
                walk(c, out);
            }
        }
    }
    let mut out = Vec::new();
    for blk in &b.blocks {
        for s in &blk.stmts {
            if let Stmt::Assign(_, _, e) = s {
                walk(e, &mut out);
            }
        }
        match &blk.term {
            Terminator::Branch(c, ..) => walk(c, &mut out),
            Terminator::Call(_, args, ..) => args.iter().for_each(|a| walk(a, &mut out)),
            _ => {}
        }
    }
    out
}

fn stmts(b: &Body) -> impl Iterator<Item = &Stmt> {
    b.blocks.iter().flat_map(|blk| blk.stmts.iter())
}

fn storage_dead_count(b: &Body, l: usize) -> usize {
    stmts(b).filter(|s| matches!(s, Stmt::StorageDead(x) if *x == l)).count()
}

fn is_cmp(op: &BinOp) -> bool {
    matches!(op, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
}

#[track_caller]
fn assert_unsupported(r: Result<Program, LowerError>, needle: &str) {
    match r {
        Err(LowerError::UnsupportedConstruct { detail }) if detail.contains(needle) => {}
        other => panic!("expected UnsupportedConstruct mentioning `{needle}`, got {other:?}"),
    }
}

/// Edits the first `decl_stmt` named `name` in the fixture.
fn edit_decl(fixture_name: &str, name: &str, f: impl Fn(&mut serde_json::Value)) -> String {
    fn find<'v>(v: &'v mut serde_json::Value, name: &str) -> Option<&'v mut serde_json::Value> {
        let is_decl = v.get("kind").and_then(|k| k.as_str()) == Some("decl_stmt")
            && v.get("name").and_then(|n| n.as_str()) == Some(name);
        if is_decl {
            return Some(v);
        }
        match v {
            serde_json::Value::Object(m) => m.values_mut().find_map(|c| find(c, name)),
            serde_json::Value::Array(a) => a.iter_mut().find_map(|c| find(c, name)),
            _ => None,
        }
    }
    let mut v: serde_json::Value = serde_json::from_str(&fixture(fixture_name)).unwrap();
    f(find(&mut v, name).unwrap_or_else(|| panic!("no declaration `{name}`")));
    v.to_string()
}

// ------------------------------ C11 -----------------------------------------

#[test]
fn c11_comparisons_are_bool_valued_and_converted_to_int() {
    let p = lower_ok("pos_cmp_int");
    let b = body(&p, "pos_cmp_int");
    let all = exprs(b);
    let cmps: Vec<_> =
        all.iter().filter(|e| matches!(e, Expr::Binary(op, ..) if is_cmp(op))).collect();
    // a < 0, b < 0, a <= b, p != q, a > b, a == b.
    assert_eq!(cmps.len(), 6, "{b:?}");
    for c in &cmps {
        assert!(matches!(c, Expr::Binary(_, Ty::Bool, ..)), "comparison not bool-valued: {c:?}");
    }
    // Every comparison used as a value is widened to `int`.
    let widened = all
        .iter()
        .filter(|e| {
            matches!(e, Expr::BoolToInt(Width::W32, Sign::Signed, a)
                if matches!(&**a, Expr::Binary(op, Ty::Bool, ..) if is_cmp(op)))
        })
        .count();
    assert_eq!(widened, 5, "{b:?}");
    // The branch condition `a > b` is used directly, not via `int`.
    assert!(b.blocks.iter().any(|blk| matches!(
        &blk.term,
        Terminator::Branch(Expr::Binary(BinOp::Gt, Ty::Bool, ..), ..)
    )));
    assert!(!all.iter().any(
        |e| matches!(e, Expr::IntToBool(a) if matches!(&**a, Expr::Binary(op, ..) if is_cmp(op)))
    ));
}

#[test]
fn c11_init_lists_and_compound_literals_initialize_fieldwise() {
    let p = lower_ok("pos_init_list");
    let b = body(&p, "pos_init_list");
    let u8_array = Ty::Array(Box::new(Ty::Int(Width::W8, Sign::Unsigned, true)), 8);
    let bytes = local(b, "bytes");
    // `{1, 2}` on a padding-free array: zero everything, then store two
    // elements.
    assert!(
        stmts(b).any(|s| matches!(s, Stmt::ZeroInit(pl, t) if pl.base == bytes && *t == u8_array))
    );
    let ratio = Ty::Record("struct.ratio".into());
    let field_stores = stmts(b)
        .filter(|s| {
            matches!(s, Stmt::Assign(pl, _, _)
            if matches!(b.locals[pl.base].ty, Ty::Record(_)) && !pl.projs.is_empty())
        })
        .count();
    // a = {0, 1}, b = {1, 0}, two compound literals: two fields each.
    assert_eq!(field_stores, 8, "{b:?}");
    // The loop body's compound literal dies with its block, like `next`.
    let next = local(b, "next");
    assert_eq!(storage_dead_count(b, next), 1);
    let literal_temps: Vec<usize> = (0..b.locals.len())
        .filter(|l| b.locals[*l].ty == ratio && b.locals[*l].debug_name.starts_with("tmp"))
        .collect();
    assert_eq!(literal_temps.len(), 2);
    for t in literal_temps {
        assert_eq!(storage_dead_count(b, t), 1, "compound literal _{t} must die once");
    }
}

#[test]
fn rejects_short_array_initializer_list_without_filler() {
    let j = edit_decl("pos_static_const", "kTable", |d| {
        d["init"].as_object_mut().unwrap().remove("array_filler");
    });
    match lower_bundle_json(&j, &Options::default()) {
        Err(LowerError::Malformed { detail }) if detail.contains("filler") => {}
        other => panic!("expected Malformed (filler), got {other:?}"),
    }
}

#[test]
fn c11_static_const_locals_are_initialized_on_entry() {
    let p = lower_ok("pos_static_const");
    let b = body(&p, "pos_static_const");
    let rounds = local(b, "kRounds");
    let table = local(b, "kTable");
    let u64_table = Ty::Array(Box::new(Ty::Int(Width::W64, Sign::Unsigned, false)), 4);
    let entry = &b.blocks[0].stmts;
    assert!(matches!(entry[0], Stmt::StorageLive(l) if l == rounds), "{entry:?}");
    assert!(
        matches!(&entry[1], Stmt::Assign(pl, _, Expr::ConstInt(_, _, _, 3)) if pl.base == rounds)
    );
    assert!(matches!(entry[2], Stmt::StorageLive(l) if l == table));
    // The omitted fourth entry is zero.
    assert!(matches!(&entry[3], Stmt::ZeroInit(pl, t) if pl.base == table && *t == u64_table));
    // Static objects live for the whole call.
    assert_eq!(storage_dead_count(b, rounds) + storage_dead_count(b, table), 0);
}

#[test]
fn rejects_static_local_whose_address_escapes() {
    assert_unsupported(lower_entry("neg_static_escape", None), "escapes");
}

#[test]
fn rejects_mutable_static_local() {
    assert_unsupported(lower_entry("neg_static_mutable", None), "static");
}

#[test]
fn rejects_static_local_without_constant_initializer() {
    let j = edit_decl("pos_cmp_int", "sign", |d| d["is_static_const"] = true.into());
    assert_unsupported(lower_bundle_json(&j, &Options::default()), "constant initializer");
}

#[test]
fn externalized_callee_is_declared_without_its_body() {
    let p = lower_ok("pos_externalize");
    assert!(body(&p, "get_ctx").is_external);
    assert!(p.is_partial);
    // `struct ctx` (with a variadic function-pointer field) is only named as
    // a pointee, so it is left out instead of blocking lowering.
    assert!(p.records.is_empty(), "{:?}", p.records);
    // Extracted without `--externalize-callee`, the helper's body needs the
    // record's layout and lowering fails closed.
    assert_unsupported(lower_entry("neg_externalize_off", None), "struct.ctx");
}

#[test]
fn c_block_locals_die_on_every_exit_of_their_scope() {
    let p = lower_ok("pos_scope_cleanup");
    let b = body(&p, "pos_scope_cleanup");
    // `c` dies at the end of the iteration, on `continue`, and on `break`.
    assert_eq!(storage_dead_count(b, local(b, "c")), 3, "{b:?}");
    assert_eq!(storage_dead_count(b, local(b, "x")), 1);
}

// ------------------------------ C++20 ---------------------------------------

#[test]
fn cxx_nullptr_t_values_are_null_pointers_that_are_never_read() {
    let p = lower_ok("cxx_nullptr");
    let void_ptr = Ty::Ptr(Box::new(Ty::Void), false, false, false);
    let ctor = body(&p, "_ZN1VC1EDn");
    assert_eq!(ctor.sig.params[1], void_ptr);
    for b in &p.bodies {
        for e in exprs(b) {
            assert!(
                !matches!(e, Expr::ReadPlace(_, t) if *t == void_ptr),
                "`std::nullptr_t` object read in `{}`",
                b.identity
            );
        }
    }
}

#[test]
fn cxx_deduction_guides_scoped_enums_and_void_statements_lower() {
    // The fixture exists only because the extractor skips the deduction
    // guide; its scoped-enum literal must agree with its type.
    let p = lower_ok("cxx_entry_reach");
    let b = body(&p, "_Z11entry_reachi");
    assert!(exprs(b).iter().any(|e| matches!(e, Expr::ConstInt(Width::W32, Sign::Signed, _, 3))));
    assert!(p.bodies.iter().any(|b| b.identity == "_Z5checki"));
}

#[test]
fn entry_lowers_only_functions_it_can_reach() {
    // Without an entry, every function is lowered, including the sibling
    // with an unsupported `while` condition variable.
    assert_unsupported(lower_entry("cxx_entry_reach_all", None), "condition variable");
    let p = lower_entry("cxx_entry_reach_all", Some("entry_reach")).unwrap();
    assert_eq!(p.bodies[p.entry_def_id].identity, "_Z11entry_reachi");
    assert!(!p.bodies.iter().any(|b| b.identity == "_Z19unreachable_siblingi"));
    assert!(p.bodies.iter().any(|b| b.identity == "_Z5checki"));
}

// ------------------------- fail-closed boundaries ---------------------------

#[test]
fn goto_leaving_blocks_ends_their_lifetimes() {
    let p = lower_ok("pos_goto_cleanup");
    let b = body(&p, "pos_goto_cleanup");
    // `buf` and `i` die at the end of their scopes and on the `goto` path.
    assert_eq!(storage_dead_count(b, local(b, "buf")), 2, "{b:?}");
    assert_eq!(storage_dead_count(b, local(b, "i")), 2, "{b:?}");
}

#[test]
fn rejects_jumps_past_declarations() {
    assert_unsupported(lower_entry("neg_goto_into_block", None), "past a declaration");
    assert_unsupported(lower_entry("neg_switch_skip_decl", None), "after a declaration");
}

#[test]
fn rejects_pointer_subtraction_of_unrepresentable_offsets() {
    assert_unsupported(lower_entry("neg_ptr_sub_u64", None), "pointer subtraction");
    assert_unsupported(lower_entry("neg_ptr_subassign_u64", None), "pointer subtraction");
}

#[test]
fn cxx_aliases_through_references_and_assignments_are_memory() {
    for entry in [
        "ref_elem_unseq",
        "assign_lvalue_order",
        "base_ref_alias",
        "addr_of_assign",
        "unseq_cleanup_ref",
        "cleanup_assign_ref",
        "ctor_conversion_escape",
        "aggregate_ctor_escape",
        "ref_array_call_escape",
    ] {
        match lower_entry("cxx_neg_misc", Some(entry)) {
            Err(LowerError::UnsequencedSideEffects { .. }) => {}
            other => panic!("{entry}: expected UnsequencedSideEffects, got {other:?}"),
        }
    }
    assert_unsupported(lower_entry("cxx_neg_misc", Some("static_ref_escape")), "escapes");
    assert_unsupported(lower_entry("cxx_neg_misc", Some("static_cleanup_escape")), "escapes");
}

#[test]
fn cxx_rejects_side_effects_in_null_pointer_constants() {
    assert_unsupported(lower_entry("cxx_neg_misc", Some("null_with_side_effect")), "side effects");
}

#[test]
fn cxx_rejects_by_value_records_that_are_not_trivially_copyable() {
    assert_unsupported(lower_entry("cxx_neg_misc", Some("make_pinned")), "trivially copyable");
}

#[test]
fn emitted_comments_and_strings_cannot_be_escaped() {
    let mut p = lower_ok("pos_cmp_int");
    let hostile = "x -/ #eval 1 /- y\n#eval 2\u{202e}";
    p.bodies[0].identity = hostile.to_owned();
    p.bodies[0].locals[1].debug_name = hostile.to_owned();
    let lean = p.lean(&anneal_lower_cpp::ir::EmitMeta {
        namespace: "CapturedCpp",
        tu_main_file: hostile,
        target_triple: "x86_64-unknown-linux-gnu",
        lang_standard: "c11",
    });
    assert!(lean.is_ascii(), "non-ASCII text in the output");
    assert!(!lean.lines().any(|l| l.starts_with("#eval")), "{lean}");
    for line in lean.lines().filter(|l| l.starts_with("/--")) {
        assert!(line.ends_with("-/") && line.matches("-/").count() == 1, "{line}");
    }
    // The identity string itself survives, escaped.
    assert!(lean.contains(r#"identity := "x -/ #eval 1 /- y\n#eval 2\u202e""#), "{lean}");
}

// --------------------- Gate-2 Round 1 regressions --------------------------

fn c11_bundle(records: serde_json::Value, functions: serde_json::Value) -> String {
    serde_json::json!({
        "schema_version": 1,
        "tu_main_file": "synthetic.c",
        "target_triple": "x86_64-unknown-linux-gnu",
        "lang_policy": {
            "is_cplusplus": false,
            "lang_standard": "c11",
            "pointer_width_bits": 64,
            "char_is_signed": true,
            "strict_aliasing": false,
            "signed_overflow": "iso_ub",
            "exceptions_enabled": false,
            "fast_math": false
        },
        "records": records,
        "functions": functions
    })
    .to_string()
}

fn cxx20_bundle(records: serde_json::Value, functions: serde_json::Value) -> String {
    serde_json::json!({
        "schema_version": 1,
        "tu_main_file": "synthetic.cc",
        "target_triple": "x86_64-unknown-linux-gnu",
        "lang_policy": {
            "is_cplusplus": true,
            "lang_standard": "c++20",
            "pointer_width_bits": 64,
            "char_is_signed": true,
            "strict_aliasing": false,
            "signed_overflow": "iso_ub",
            "exceptions_enabled": false,
            "fast_math": false
        },
        "records": records,
        "functions": functions
    })
    .to_string()
}

fn i32_ty() -> serde_json::Value {
    serde_json::json!({"kind": "int", "bits": 32, "signed": true, "is_char_like": false})
}

fn u32_ty() -> serde_json::Value {
    serde_json::json!({"kind": "int", "bits": 32, "signed": false, "is_char_like": false})
}

fn int_lit(v: i64) -> serde_json::Value {
    serde_json::json!({
        "kind": "int_lit",
        "ty": i32_ty(),
        "value_category": "prvalue",
        "value_str": v.to_string(),
        "bits": 32,
        "signed": true
    })
}

/// Checks that every root-to-return path through `b` executes `StorageLive(l)`
/// and `StorageDead(l)` in strict 1-to-1 alternation (never live twice, never
/// dead without being live).
fn assert_balanced_storage_on_all_paths(b: &Body, l: usize) {
    fn dfs(b: &Body, bb: usize, mut live: bool, l: usize, path: &mut Vec<usize>) {
        for s in &b.blocks[bb].stmts {
            match s {
                Stmt::StorageLive(x) if *x == l => {
                    assert!(!live, "double StorageLive(_{l}) along {path:?} -> bb{bb}: {b:?}");
                    live = true;
                }
                Stmt::StorageDead(x) if *x == l => {
                    assert!(live, "unpaired StorageDead(_{l}) along {path:?} -> bb{bb}: {b:?}");
                    live = false;
                }
                _ => {}
            }
        }
        path.push(bb);
        let succs = match &b.blocks[bb].term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch(_, t, f) => vec![*t, *f],
            Terminator::Call(_, _, _, n) => vec![*n],
            Terminator::Ret => {
                assert!(!live, "_{l} still live at Ret along {path:?}: {b:?}");
                path.pop();
                return;
            }
            Terminator::Unreachable => {
                path.pop();
                return;
            }
        };
        for nx in succs {
            // Unroll back-edges at most twice (0, 1, and 2 loop iterations).
            if path.iter().filter(|&&p| p == nx).count() <= 2 {
                dfs(b, nx, live, l, path);
            }
        }
        path.pop();
    }
    dfs(b, b.entry_block, false, l, &mut Vec::new());
}

#[test]
fn rejects_static_const_with_mutable_field() {
    // Direct `has_mutable` record on a hoisted `static const` local.
    let rec_s = serde_json::json!({
        "id": "struct.MutBox",
        "is_union": false,
        "size_bytes": 4,
        "align_bytes": 4,
        "has_mutable": true,
        "is_trivially_copyable": true,
        "fields": [{"name": "n", "offset_bits": 0, "bit_width": null, "ty": i32_ty()}]
    });
    let rec_outer = serde_json::json!({
        "id": "struct.Outer",
        "is_union": false,
        "size_bytes": 4,
        "align_bytes": 4,
        "has_mutable": false,
        "is_trivially_copyable": true,
        "fields": [{
            "name": "inner",
            "offset_bits": 0,
            "bit_width": null,
            "ty": {"kind": "record", "id": "struct.MutBox"}
        }]
    });
    let make_fn = |rec_id: &str, write_field: bool, has_mutable_flag: bool| {
        let mut s_rec = rec_s.clone();
        s_rec["has_mutable"] = has_mutable_flag.into();
        let rec_ty = serde_json::json!({"kind": "record", "id": rec_id});
        let init = if rec_id == "struct.Outer" {
            serde_json::json!({
                "kind": "init_list",
                "ty": rec_ty,
                "value_category": "prvalue",
                "inits": [{
                    "kind": "init_list",
                    "ty": {"kind": "record", "id": "struct.MutBox"},
                    "value_category": "prvalue",
                    "inits": [int_lit(0)]
                }]
            })
        } else {
            serde_json::json!({
                "kind": "init_list",
                "ty": rec_ty,
                "value_category": "prvalue",
                "inits": [int_lit(0)]
            })
        };
        let member_n = serde_json::json!({
            "kind": "member",
            "ty": i32_ty(),
            "value_category": "lvalue",
            "base": {
                "kind": "var_ref",
                "ty": {"kind": "record", "id": "struct.MutBox"},
                "value_category": "lvalue",
                "var_id": 0,
                "is_param": false,
                "param_idx": null,
                "is_ref_binding": false
            },
            "is_arrow": false,
            "field_name": "n",
            "record_id": "struct.MutBox",
            "field_idx": 0,
            "is_bitfield": false
        });
        let ret_expr = if write_field {
            serde_json::json!({
                "kind": "cast",
                "cast_kind": "lvalue_to_rvalue",
                "ty": i32_ty(),
                "value_category": "prvalue",
                "sub": {
                    "kind": "unary_op",
                    "op": "pre_inc",
                    "ty": i32_ty(),
                    "value_category": "lvalue",
                    "sub": member_n
                }
            })
        } else {
            int_lit(1)
        };
        cxx20_bundle(
            serde_json::json!([s_rec, rec_outer]),
            serde_json::json!([{
                "symbol": "_Z1fv",
                "unmangled_name": "f",
                "is_definition": true,
                "return_ty": i32_ty(),
                "params": [],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [],
                    "return_passing": {"kind": "direct_int", "bits": 32}
                },
                "body_stmt": {
                    "kind": "compound",
                    "stmts": [
                        {
                            "kind": "decl_stmt",
                            "var_id": 0,
                            "name": "s",
                            "ty": rec_ty,
                            "is_static_const": true,
                            "init": init
                        },
                        {"kind": "return", "expr": ret_expr}
                    ]
                }
            }]),
        )
    };
    assert_unsupported(
        lower_bundle_json(&make_fn("struct.MutBox", false, true), &Options::default()),
        "mutable",
    );
    // Transitive `has_mutable` through an enclosing record.
    assert_unsupported(
        lower_bundle_json(&make_fn("struct.Outer", false, true), &Options::default()),
        "mutable",
    );
    // Even without `has_mutable`, writing to a hoisted static fails closed.
    assert_unsupported(
        lower_bundle_json(&make_fn("struct.MutBox", true, false), &Options::default()),
        "modified",
    );
}

#[test]
fn cxx_conditional_trivial_temp_balances_storage_live_and_dead() {
    // `return c ? S{1}.get() : 0;` where `S` has a trivial destructor.
    let s_ty = serde_json::json!({"kind": "record", "id": "struct.S"});
    let s_ptr_ty = serde_json::json!({
        "kind": "ptr",
        "pointee": s_ty,
        "is_const": true,
        "is_restrict": false,
        "may_alias": false
    });
    let bundle = cxx20_bundle(
        serde_json::json!([{
            "id": "struct.S",
            "is_union": false,
            "size_bytes": 4,
            "align_bytes": 4,
            "is_trivially_copyable": true,
            "fields": [{"name": "x", "offset_bits": 0, "bit_width": null, "ty": i32_ty()}]
        }]),
        serde_json::json!([
            {
                "symbol": "_Z1fb",
                "unmangled_name": "f",
                "is_definition": true,
                "return_ty": i32_ty(),
                "params": [{"name": "c", "ty": {"kind": "bool"}}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "extend_int", "bits": 1}],
                    "return_passing": {"kind": "direct_int", "bits": 32}
                },
                "body_stmt": {
                    "kind": "compound",
                    "stmts": [{
                        "kind": "return",
                        "expr": {
                            "kind": "expr_with_cleanups",
                            "ty": i32_ty(),
                            "value_category": "prvalue",
                            "sub": {
                                "kind": "conditional",
                                "ty": i32_ty(),
                                "value_category": "prvalue",
                                "cond": {
                                    "kind": "cast",
                                    "cast_kind": "lvalue_to_rvalue",
                                    "ty": {"kind": "bool"},
                                    "value_category": "prvalue",
                                    "sub": {
                                        "kind": "var_ref",
                                        "ty": {"kind": "bool"},
                                        "value_category": "lvalue",
                                        "var_id": 0,
                                        "is_param": true,
                                        "param_idx": 0
                                    }
                                },
                                "then_expr": {
                                    "kind": "call",
                                    "ty": i32_ty(),
                                    "value_category": "prvalue",
                                    "callee_symbol": "_ZNK1S3getEv",
                                    "is_indirect": false,
                                    "implicit_object": {
                                        "kind": "materialize_temporary",
                                        "ty": s_ty,
                                        "value_category": "xvalue",
                                        "lifetime_extended": false,
                                        "sub": {
                                            "kind": "init_list",
                                            "ty": s_ty,
                                            "value_category": "prvalue",
                                            "inits": [int_lit(1)]
                                        }
                                    },
                                    "implicit_object_is_ptr": false,
                                    "args": [],
                                    "param_is_ref": []
                                },
                                "else_expr": int_lit(0)
                            }
                        }
                    }]
                }
            },
            {
                "symbol": "_ZNK1S3getEv",
                "unmangled_name": "get",
                "method_kind": "method",
                "is_definition": true,
                "return_ty": i32_ty(),
                "params": [{"name": "this", "ty": s_ptr_ty, "is_this": true}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "direct_ptr"}],
                    "return_passing": {"kind": "direct_int", "bits": 32}
                },
                "body_stmt": {
                    "kind": "compound",
                    "stmts": [{"kind": "return", "expr": int_lit(1)}]
                }
            }
        ]),
    );
    let p = lower_bundle_json(&bundle, &Options::default()).expect("must lower");
    let b = body(&p, "_Z1fb");
    let s_temp = b
        .locals
        .iter()
        .position(|l| l.ty == Ty::Record("struct.S".into()))
        .expect("materialized S temporary");
    assert_balanced_storage_on_all_paths(b, s_temp);
}

#[test]
fn c11_compound_literals_respect_substatement_scopes_and_reject_conditionals() {
    let i32_ptr = serde_json::json!({
        "kind": "ptr",
        "pointee": i32_ty(),
        "is_const": false,
        "is_restrict": false,
        "may_alias": false
    });
    let compound_lit = serde_json::json!({
        "kind": "compound_literal",
        "ty": i32_ty(),
        "value_category": "lvalue",
        "is_file_scope": false,
        "init": int_lit(1)
    });
    let addr_of_lit = serde_json::json!({
        "kind": "unary_op",
        "op": "addr_of",
        "ty": i32_ptr,
        "value_category": "prvalue",
        "sub": compound_lit
    });
    // 1. `if (c) p = &(int){1}; return p != 0;`
    let if_bundle = c11_bundle(
        serde_json::json!([]),
        serde_json::json!([{
            "symbol": "if_subscope",
            "unmangled_name": "if_subscope",
            "is_definition": true,
            "return_ty": i32_ty(),
            "params": [{"name": "c", "ty": i32_ty()}],
            "abi_witness": {
                "cc": "c",
                "param_passing": [{"kind": "direct_int", "bits": 32}],
                "return_passing": {"kind": "direct_int", "bits": 32}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [
                    {
                        "kind": "decl_stmt",
                        "var_id": 1,
                        "name": "p",
                        "ty": i32_ptr,
                        "init": {
                            "kind": "cast",
                            "cast_kind": "null_to_pointer",
                            "ty": i32_ptr,
                            "value_category": "prvalue",
                            "sub": int_lit(0)
                        }
                    },
                    {
                        "kind": "if",
                        "cond": {
                            "kind": "cast",
                            "cast_kind": "lvalue_to_rvalue",
                            "ty": i32_ty(),
                            "value_category": "prvalue",
                            "sub": {
                                "kind": "var_ref",
                                "ty": i32_ty(),
                                "value_category": "lvalue",
                                "var_id": 0,
                                "is_param": true,
                                "param_idx": 0
                            }
                        },
                        "then_branch": {
                            "kind": "expr_stmt",
                            "expr": {
                                "kind": "binary_op",
                                "op": "assign",
                                "ty": i32_ptr,
                                "value_category": "prvalue",
                                "lhs": {
                                    "kind": "var_ref",
                                    "ty": i32_ptr,
                                    "value_category": "lvalue",
                                    "var_id": 1,
                                    "is_param": false,
                                    "param_idx": null
                                },
                                "rhs": addr_of_lit
                            }
                        }
                    },
                    {"kind": "return", "expr": int_lit(0)}
                ]
            }
        }]),
    );
    let p_if = lower_bundle_json(&if_bundle, &Options::default()).expect("if_subscope must lower");
    let b_if = body(&p_if, "if_subscope");
    let lit_local = (0..b_if.locals.len())
        .find(|&l| b_if.locals[l].debug_name.starts_with("tmp") && b_if.locals[l].ty == Ty::I32)
        .expect("compound literal temp");
    assert_balanced_storage_on_all_paths(b_if, lit_local);
    // `StorageDead` must run in the `then` block, not the final return block.
    let ret_bb = b_if.blocks.iter().find(|blk| blk.term == Terminator::Ret).unwrap();
    assert!(!ret_bb.stmts.contains(&Stmt::StorageDead(lit_local)), "{b_if:?}");

    // 2. `while (n--) sink(&(int){1});`
    let while_bundle = c11_bundle(
        serde_json::json!([]),
        serde_json::json!([
            {
                "symbol": "while_subscope",
                "unmangled_name": "while_subscope",
                "is_definition": true,
                "return_ty": {"kind": "void"},
                "params": [{"name": "n", "ty": i32_ty()}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "direct_int", "bits": 32}],
                    "return_passing": {"kind": "ignore"}
                },
                "body_stmt": {
                    "kind": "compound",
                    "stmts": [{
                        "kind": "while",
                        "cond": {
                            "kind": "unary_op",
                            "op": "post_dec",
                            "ty": i32_ty(),
                            "value_category": "prvalue",
                            "sub": {
                                "kind": "var_ref",
                                "ty": i32_ty(),
                                "value_category": "lvalue",
                                "var_id": 0,
                                "is_param": true,
                                "param_idx": 0
                            }
                        },
                        "body": {
                            "kind": "expr_stmt",
                            "expr": {
                                "kind": "call",
                                "ty": {"kind": "void"},
                                "value_category": "prvalue",
                                "callee_symbol": "sink",
                                "is_indirect": false,
                                "args": [addr_of_lit]
                            }
                        }
                    }]
                }
            },
            {
                "symbol": "sink",
                "unmangled_name": "sink",
                "is_definition": false,
                "return_ty": {"kind": "void"},
                "params": [{"name": "p", "ty": i32_ptr}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "direct_ptr"}],
                    "return_passing": {"kind": "ignore"}
                },
                "body_stmt": null
            }
        ]),
    );
    let p_w = lower_bundle_json(&while_bundle, &Options::default()).expect("while_subscope");
    let b_w = body(&p_w, "while_subscope");
    let w_lit = (0..b_w.locals.len())
        .find(|&l| b_w.blocks.iter().any(|blk| blk.stmts.contains(&Stmt::StorageLive(l))))
        .expect("while compound literal");
    assert_balanced_storage_on_all_paths(b_w, w_lit);

    // 3. Braceless `switch (x) case 0: sink(&(int){1});`
    let switch_bundle = c11_bundle(
        serde_json::json!([]),
        serde_json::json!([
            {
                "symbol": "switch_subscope",
                "unmangled_name": "switch_subscope",
                "is_definition": true,
                "return_ty": i32_ty(),
                "params": [{"name": "x", "ty": i32_ty()}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "direct_int", "bits": 32}],
                    "return_passing": {"kind": "direct_int", "bits": 32}
                },
                "body_stmt": {
                    "kind": "compound",
                    "stmts": [
                        {
                            "kind": "switch",
                            "cond": {
                                "kind": "cast",
                                "cast_kind": "lvalue_to_rvalue",
                                "ty": i32_ty(),
                                "value_category": "prvalue",
                                "sub": {
                                    "kind": "var_ref",
                                    "ty": i32_ty(),
                                    "value_category": "lvalue",
                                    "var_id": 0,
                                    "is_param": true,
                                    "param_idx": 0
                                }
                            },
                            "body": {
                                "kind": "case",
                                "value_str": "0",
                                "sub": {
                                    "kind": "expr_stmt",
                                    "expr": {
                                        "kind": "call",
                                        "ty": {"kind": "void"},
                                        "value_category": "prvalue",
                                        "callee_symbol": "sink",
                                        "is_indirect": false,
                                        "args": [addr_of_lit]
                                    }
                                }
                            }
                        },
                        {"kind": "return", "expr": int_lit(0)}
                    ]
                }
            },
            {
                "symbol": "sink",
                "unmangled_name": "sink",
                "is_definition": false,
                "return_ty": {"kind": "void"},
                "params": [{"name": "p", "ty": i32_ptr}],
                "abi_witness": {
                    "cc": "c",
                    "param_passing": [{"kind": "direct_ptr"}],
                    "return_passing": {"kind": "ignore"}
                },
                "body_stmt": null
            }
        ]),
    );
    let p_sw =
        lower_bundle_json(&switch_bundle, &Options::default()).expect("switch_subscope must lower");
    let b_sw = body(&p_sw, "switch_subscope");
    let sw_lit = (0..b_sw.locals.len())
        .find(|&l| b_sw.blocks.iter().any(|blk| blk.stmts.contains(&Stmt::StorageLive(l))))
        .expect("switch compound literal");
    assert_balanced_storage_on_all_paths(b_sw, sw_lit);
    let sw_ret_bb = b_sw.blocks.iter().find(|blk| blk.term == Terminator::Ret).unwrap();
    assert!(!sw_ret_bb.stmts.contains(&Stmt::StorageDead(sw_lit)), "{b_sw:?}");

    // 4. `c ? &(int){1} : 0` must fail closed.
    let cond_lit_bundle = c11_bundle(
        serde_json::json!([]),
        serde_json::json!([{
            "symbol": "cond_lit",
            "unmangled_name": "cond_lit",
            "is_definition": true,
            "return_ty": i32_ptr,
            "params": [{"name": "c", "ty": i32_ty()}],
            "abi_witness": {
                "cc": "c",
                "param_passing": [{"kind": "direct_int", "bits": 32}],
                "return_passing": {"kind": "direct_ptr"}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [{
                    "kind": "return",
                    "expr": {
                        "kind": "conditional",
                        "ty": i32_ptr,
                        "value_category": "prvalue",
                        "cond": {
                            "kind": "cast",
                            "cast_kind": "lvalue_to_rvalue",
                            "ty": i32_ty(),
                            "value_category": "prvalue",
                            "sub": {
                                "kind": "var_ref",
                                "ty": i32_ty(),
                                "value_category": "lvalue",
                                "var_id": 0,
                                "is_param": true,
                                "param_idx": 0
                            }
                        },
                        "then_expr": addr_of_lit,
                        "else_expr": {
                            "kind": "cast",
                            "cast_kind": "null_to_pointer",
                            "ty": i32_ptr,
                            "value_category": "prvalue",
                            "sub": int_lit(0)
                        }
                    }
                }]
            }
        }]),
    );
    assert_unsupported(
        lower_bundle_json(&cond_lit_bundle, &Options::default()),
        "conditionally evaluated compound literal",
    );
}

#[test]
fn c11_bitfield_store_truncates_value_and_incdec_promotes_narrow_bitfield() {
    use anneal_lower_cpp::ir::Proj;
    let bf_rec = serde_json::json!({
        "id": "struct.BF",
        "is_union": false,
        "size_bytes": 8,
        "align_bytes": 4,
        "fields": [
            {"name": "b3", "offset_bits": 0, "bit_width": 3, "ty": u32_ty()},
            {"name": "b31", "offset_bits": 32, "bit_width": 31, "ty": u32_ty()}
        ]
    });
    let s_ptr_ty = serde_json::json!({
        "kind": "ptr",
        "pointee": {"kind": "record", "id": "struct.BF"},
        "is_const": false,
        "is_restrict": false,
        "may_alias": false
    });
    let s_ref = serde_json::json!({
        "kind": "cast",
        "cast_kind": "lvalue_to_rvalue",
        "ty": s_ptr_ty,
        "value_category": "prvalue",
        "sub": {
            "kind": "var_ref",
            "ty": s_ptr_ty,
            "value_category": "lvalue",
            "var_id": 0,
            "is_param": true,
            "param_idx": 0
        }
    });
    let bf_member = |name: &str, idx: u32, off: u64, width: u64| {
        serde_json::json!({
            "kind": "member",
            "ty": u32_ty(),
            "value_category": "lvalue",
            "base": s_ref,
            "is_arrow": true,
            "field_name": name,
            "record_id": "struct.BF",
            "field_idx": idx,
            "is_bitfield": true,
            "bit_offset": off,
            "bit_width": width,
            "field_is_signed": false
        })
    };
    let bundle = c11_bundle(
        serde_json::json!([bf_rec]),
        serde_json::json!([{
            "symbol": "bf_ops",
            "unmangled_name": "bf_ops",
            "is_definition": true,
            "return_ty": u32_ty(),
            "params": [{"name": "s", "ty": s_ptr_ty}],
            "abi_witness": {
                "cc": "c",
                "param_passing": [{"kind": "direct_ptr"}],
                "return_passing": {"kind": "direct_int", "bits": 32}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [
                    {
                        "kind": "expr_stmt",
                        "expr": {
                            "kind": "unary_op",
                            "op": "pre_inc",
                            "ty": u32_ty(),
                            "value_category": "prvalue",
                            "sub": bf_member("b31", 1, 32, 31)
                        }
                    },
                    {
                        "kind": "return",
                        "expr": {
                            "kind": "binary_op",
                            "op": "assign",
                            "ty": u32_ty(),
                            "value_category": "prvalue",
                            "lhs": bf_member("b3", 0, 0, 3),
                            "rhs": {
                                "kind": "int_lit",
                                "ty": u32_ty(),
                                "value_category": "prvalue",
                                "value_str": "10",
                                "bits": 32,
                                "signed": false
                            }
                        }
                    }
                ]
            }
        }]),
    );
    let p = lower_bundle_json(&bundle, &Options::default()).expect("bf_ops must lower");
    let b = body(&p, "bf_ops");
    // 1. `++s->b31` (`uint32_t b31 : 31`) must promote to signed `Ty::I32`!
    assert!(
        exprs(b).iter().any(|e| matches!(e, Expr::Binary(BinOp::Add, Ty::I32, ..))),
        "31-bit unsigned bit-field increment must promote to signed int32: {b:?}"
    );
    // 2. `return (s->b3 = 10);` must write the bit-field FIRST and then read
    // back the truncated bit-field place (not return the untruncated `10`)!
    let stmts_vec: Vec<_> = stmts(b).collect();
    let store_pos = stmts_vec
        .iter()
        .position(|s| {
            matches!(s, Stmt::Assign(pl, _, Expr::ConstInt(_, _, _, 10))
                if matches!(pl.projs.last(), Some(Proj::Bitfield(_, 0, 0, 3, false))))
        })
        .expect("bit-field store of 10");
    let readback_pos = stmts_vec
        .iter()
        .position(|s| {
            matches!(s, Stmt::Assign(dst, _, Expr::ReadPlace(src, _))
                if dst.projs.is_empty()
                    && matches!(src.projs.last(), Some(Proj::Bitfield(_, 0, 0, 3, false))))
        })
        .expect("truncated bit-field readback");
    assert!(store_pos < readback_pos, "{stmts_vec:?}");
}

#[test]
fn rejects_unsequenced_nontrivial_temp_dtors() {
    let log_ty = serde_json::json!({"kind": "record", "id": "struct.Log"});
    let log_temp = |tag: i64| {
        serde_json::json!({
            "kind": "cast",
            "cast_kind": "lvalue_to_rvalue",
            "ty": i32_ty(),
            "value_category": "prvalue",
            "sub": {
                "kind": "member",
                "ty": i32_ty(),
                "value_category": "lvalue",
                "base": {
                    "kind": "materialize_temporary",
                    "ty": log_ty,
                    "value_category": "xvalue",
                    "lifetime_extended": false,
                    "sub": {
                        "kind": "bind_temporary",
                        "ty": log_ty,
                        "value_category": "prvalue",
                        "dtor_symbol": "_ZN3LogD1Ev",
                        "sub": {
                            "kind": "init_list",
                            "ty": log_ty,
                            "value_category": "prvalue",
                            "inits": [int_lit(tag)]
                        }
                    }
                },
                "is_arrow": false,
                "field_name": "tag",
                "record_id": "struct.Log",
                "field_idx": 0,
                "is_bitfield": false
            }
        })
    };
    let make = |ret_expr: serde_json::Value| {
        cxx20_bundle(
            serde_json::json!([{
                "id": "struct.Log",
                "is_union": false,
                "size_bytes": 4,
                "align_bytes": 4,
                "is_trivially_copyable": false,
                "dtor_symbol": "_ZN3LogD1Ev",
                "fields": [{"name": "tag", "offset_bits": 0, "bit_width": null, "ty": i32_ty()}]
            }]),
            serde_json::json!([
                {
                    "symbol": "_Z4testv",
                    "unmangled_name": "test",
                    "is_definition": true,
                    "return_ty": i32_ty(),
                    "params": [],
                    "abi_witness": {
                        "cc": "c",
                        "param_passing": [],
                        "return_passing": {"kind": "direct_int", "bits": 32}
                    },
                    "body_stmt": {
                        "kind": "compound",
                        "stmts": [{
                            "kind": "return",
                            "expr": {
                                "kind": "expr_with_cleanups",
                                "ty": i32_ty(),
                                "value_category": "prvalue",
                                "sub": ret_expr
                            }
                        }]
                    }
                },
                {
                    "symbol": "_ZN3LogD1Ev",
                    "unmangled_name": "~Log",
                    "method_kind": "dtor",
                    "is_definition": false,
                    "return_ty": {"kind": "void"},
                    "params": [{
                        "name": "this",
                        "is_this": true,
                        "ty": {
                            "kind": "ptr",
                            "pointee": log_ty,
                            "is_const": false,
                            "is_restrict": false,
                            "may_alias": false
                        }
                    }],
                    "abi_witness": {
                        "cc": "c",
                        "param_passing": [{"kind": "direct_ptr"}],
                        "return_passing": {"kind": "ignore"}
                    },
                    "body_stmt": null
                },
                {
                    "symbol": "_Z4sinkii",
                    "unmangled_name": "sink",
                    "is_definition": false,
                    "return_ty": i32_ty(),
                    "params": [{"name": "a", "ty": i32_ty()}, {"name": "b", "ty": i32_ty()}],
                    "abi_witness": {
                        "cc": "c",
                        "param_passing": [
                            {"kind": "direct_int", "bits": 32},
                            {"kind": "direct_int", "bits": 32}
                        ],
                        "return_passing": {"kind": "direct_int", "bits": 32}
                    },
                    "body_stmt": null
                }
            ]),
        )
    };
    // 1. `Log{1}.tag + Log{2}.tag`
    let add_expr = serde_json::json!({
        "kind": "binary_op",
        "op": "add",
        "ty": i32_ty(),
        "value_category": "prvalue",
        "lhs": log_temp(1),
        "rhs": log_temp(2)
    });
    assert!(matches!(
        lower_bundle_json(&make(add_expr), &Options::default()),
        Err(LowerError::UnsequencedSideEffects { .. })
    ));
    // 2. `sink(Log{1}.tag, Log{2}.tag)`
    let call_expr = serde_json::json!({
        "kind": "call",
        "ty": i32_ty(),
        "value_category": "prvalue",
        "callee_symbol": "_Z4sinkii",
        "is_indirect": false,
        "args": [log_temp(1), log_temp(2)],
        "param_is_ref": [false, false]
    });
    assert!(matches!(
        lower_bundle_json(&make(call_expr), &Options::default()),
        Err(LowerError::UnsequencedSideEffects { .. })
    ));
}

#[test]
fn rejects_by_value_record_observing_this() {
    let sp_ty = serde_json::json!({"kind": "record", "id": "struct.SelfPtr"});
    let sp_ptr = serde_json::json!({
        "kind": "ptr",
        "pointee": sp_ty,
        "is_const": false,
        "is_restrict": false,
        "may_alias": false
    });
    let make_bundle = |has_flag: bool, include_ctor_body: bool| {
        let mut funcs = vec![serde_json::json!({
            "symbol": "_Z4makev",
            "unmangled_name": "make",
            "is_definition": true,
            "return_ty": sp_ty,
            "params": [],
            "abi_witness": {
                "cc": "c",
                "param_passing": [],
                "return_passing": {"kind": "direct_ptr"}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [{
                    "kind": "return",
                    "expr": {
                        "kind": "construct",
                        "ty": sp_ty,
                        "value_category": "prvalue",
                        "ctor_symbol": "_ZN7SelfPtrC1Ev",
                        "record_id": "struct.SelfPtr",
                        "is_trivial": false,
                        "is_default": true,
                        "construction_kind": "complete",
                        "args": [],
                        "param_is_ref": []
                    }
                }]
            }
        })];
        funcs.push(serde_json::json!({
            "symbol": "_ZN7SelfPtrC1Ev",
            "unmangled_name": "SelfPtr",
            "method_kind": "ctor",
            "is_trivial": false,
            "is_definition": include_ctor_body,
            "return_ty": {"kind": "void"},
            "params": [{"name": "this", "ty": sp_ptr, "is_this": true}],
            "abi_witness": {
                "cc": "c",
                "param_passing": [{"kind": "direct_ptr"}],
                "return_passing": {"kind": "ignore"}
            },
            "ctor_inits": if include_ctor_body {
                serde_json::json!([{
                    "kind": "field",
                    "record_id": "struct.SelfPtr",
                    "field_idx": 0,
                    "init": {
                        "kind": "cxx_this",
                        "ty": sp_ptr,
                        "value_category": "prvalue"
                    }
                }])
            } else {
                serde_json::json!([])
            },
            "body_stmt": if include_ctor_body {
                serde_json::json!({"kind": "compound", "stmts": []})
            } else {
                serde_json::Value::Null
            }
        }));
        cxx20_bundle(
            serde_json::json!([{
                "id": "struct.SelfPtr",
                "is_union": false,
                "size_bytes": 8,
                "align_bytes": 8,
                "is_trivially_copyable": true,
                "has_address_dependent_ctor": has_flag,
                "fields": [{"name": "self", "offset_bits": 0, "bit_width": null, "ty": sp_ptr}]
            }]),
            serde_json::Value::Array(funcs),
        )
    };
    // Caught by `ctor_observes_this` even when `has_address_dependent_ctor` is
    // false.
    assert_unsupported(
        lower_bundle_json(&make_bundle(false, true), &Options::default()),
        "address-dependent constructor",
    );
    // Caught when a non-trivial constructor is bodiless (external).
    assert_unsupported(
        lower_bundle_json(&make_bundle(false, false), &Options::default()),
        "address-dependent constructor",
    );
    // Caught by `has_address_dependent_ctor` from `anneal-clang-dump`.
    assert_unsupported(
        lower_bundle_json(&make_bundle(true, true), &Options::default()),
        "address-dependent constructor",
    );
}

#[test]
fn self_referential_partial_initializers_do_not_upfront_zero_init() {
    use anneal_lower_cpp::ir::Proj;
    let s_ty = serde_json::json!({"kind": "record", "id": "struct.Pair2"});
    let arr_ty = serde_json::json!({"kind": "array", "elem": i32_ty(), "len": 3});
    let bundle = c11_bundle(
        serde_json::json!([{
            "id": "struct.Pair2",
            "is_union": false,
            "size_bytes": 8,
            "align_bytes": 4,
            "fields": [
                {"name": "x", "offset_bits": 0, "bit_width": null, "ty": i32_ty()},
                {"name": "y", "offset_bits": 32, "bit_width": null, "ty": i32_ty()}
            ]
        }]),
        serde_json::json!([{
            "symbol": "self_init",
            "unmangled_name": "self_init",
            "is_definition": true,
            "return_ty": i32_ty(),
            "params": [],
            "abi_witness": {
                "cc": "c",
                "param_passing": [],
                "return_passing": {"kind": "direct_int", "bits": 32}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [
                    {
                        "kind": "decl_stmt",
                        "var_id": 0,
                        "name": "s",
                        "ty": s_ty,
                        "init": {
                            "kind": "init_list",
                            "ty": s_ty,
                            "value_category": "prvalue",
                            "inits": [
                                {
                                    "kind": "cast",
                                    "cast_kind": "lvalue_to_rvalue",
                                    "ty": i32_ty(),
                                    "value_category": "prvalue",
                                    "sub": {
                                        "kind": "member",
                                        "ty": i32_ty(),
                                        "value_category": "lvalue",
                                        "base": {
                                            "kind": "var_ref",
                                            "ty": s_ty,
                                            "value_category": "lvalue",
                                            "var_id": 0,
                                            "is_param": false,
                                            "param_idx": null
                                        },
                                        "is_arrow": false,
                                        "field_name": "y",
                                        "record_id": "struct.Pair2",
                                        "field_idx": 1,
                                        "is_bitfield": false
                                    }
                                },
                                {
                                    "kind": "implicit_value_init",
                                    "ty": i32_ty(),
                                    "value_category": "prvalue"
                                }
                            ]
                        }
                    },
                    {
                        "kind": "decl_stmt",
                        "var_id": 1,
                        "name": "a",
                        "ty": arr_ty,
                        "init": {
                            "kind": "init_list",
                            "ty": arr_ty,
                            "value_category": "prvalue",
                            "array_filler": {
                                "kind": "implicit_value_init",
                                "ty": i32_ty(),
                                "value_category": "prvalue"
                            },
                            "inits": [
                                int_lit(1),
                                {
                                    "kind": "cast",
                                    "cast_kind": "lvalue_to_rvalue",
                                    "ty": i32_ty(),
                                    "value_category": "prvalue",
                                    "sub": {
                                        "kind": "array_subscript",
                                        "ty": i32_ty(),
                                        "value_category": "lvalue",
                                        "base": {
                                            "kind": "cast",
                                            "cast_kind": "array_to_pointer_decay",
                                            "ty": {
                                                "kind": "ptr",
                                                "pointee": i32_ty(),
                                                "is_const": false,
                                                "is_restrict": false,
                                                "may_alias": false
                                            },
                                            "value_category": "prvalue",
                                            "sub": {
                                                "kind": "var_ref",
                                                "ty": arr_ty,
                                                "value_category": "lvalue",
                                                "var_id": 1,
                                                "is_param": false,
                                                "param_idx": null
                                            }
                                        },
                                        "idx": int_lit(2)
                                    }
                                }
                            ]
                        }
                    },
                    {"kind": "return", "expr": int_lit(0)}
                ]
            }
        }]),
    );
    let p = lower_bundle_json(&bundle, &Options::default()).expect("self_init must lower");
    let b = body(&p, "self_init");
    let s_loc = local(b, "s");
    let a_loc = local(b, "a");
    let stmts_vec: Vec<_> = stmts(b).collect();

    // No whole-object `ZeroInit(s)` or `ZeroInit(a)` may exist!
    assert!(
        !stmts_vec
            .iter()
            .any(|st| matches!(st, Stmt::ZeroInit(pl, _) if pl.projs.is_empty() && (pl.base == s_loc || pl.base == a_loc))),
        "whole-object ZeroInit would mask uninitialized self-read UB: {stmts_vec:?}"
    );
    // `s.x = s.y` must execute BEFORE `ZeroInit(s.y)`!
    let sx_assign = stmts_vec
        .iter()
        .position(|st| {
            matches!(st, Stmt::Assign(pl, _, Expr::ReadPlace(rp, _))
                if pl.base == s_loc
                    && matches!(pl.projs.as_slice(), [Proj::Field(_, 0, _)])
                    && rp.base == s_loc
                    && matches!(rp.projs.as_slice(), [Proj::Field(_, 1, _)]))
        })
        .expect("s.x = s.y");
    let sy_zero = stmts_vec
        .iter()
        .position(|st| {
            matches!(st, Stmt::ZeroInit(pl, _)
                if pl.base == s_loc && matches!(pl.projs.as_slice(), [Proj::Field(_, 1, _)]))
        })
        .expect("ZeroInit(s.y)");
    assert!(sx_assign < sy_zero, "{stmts_vec:?}");

    // `a[1] = a[2]` must execute BEFORE `ZeroInit(a[2])`!
    let a1_assign = stmts_vec
        .iter()
        .position(|st| {
            matches!(st, Stmt::Assign(pl, _, Expr::ReadPlace(rp, _))
                if pl.base == a_loc && rp.base == a_loc)
        })
        .expect("a[1] = a[2]");
    let a2_zero = stmts_vec
        .iter()
        .position(|st| matches!(st, Stmt::ZeroInit(pl, _) if pl.base == a_loc))
        .expect("ZeroInit(a[2])");
    assert!(a1_assign < a2_zero, "{stmts_vec:?}");
}

#[test]
fn cxx_lvalue_trivial_assign_lowers_without_declared_operator_callee() {
    // `c = (a = b); return (a = b).x;` with `Pair::operator=` omitted from
    // `bundle.functions` (as `anneal-clang-dump` emits trivial assignments).
    let pair_ty = serde_json::json!({"kind": "record", "id": "struct.Pair"});
    let var = |id: u32| {
        serde_json::json!({
            "kind": "var_ref",
            "ty": pair_ty,
            "value_category": "lvalue",
            "var_id": id,
            "is_param": false,
            "param_idx": null,
            "is_ref_binding": false
        })
    };
    let triv_assign = |lhs: serde_json::Value, rhs: serde_json::Value| {
        serde_json::json!({
            "kind": "call",
            "ty": pair_ty,
            "value_category": "lvalue",
            "callee_symbol": "_ZN4PairaSERKS_",
            "is_indirect": false,
            "implicit_object": lhs,
            "implicit_object_is_ptr": false,
            "args": [rhs],
            "param_is_ref": [true],
            "returns_ref": true,
            "trivial_assign": true
        })
    };
    let init_pair = |x: i64| {
        serde_json::json!({
            "kind": "init_list",
            "ty": pair_ty,
            "value_category": "prvalue",
            "inits": [int_lit(x)]
        })
    };
    let bundle = cxx20_bundle(
        serde_json::json!([{
            "id": "struct.Pair",
            "is_union": false,
            "size_bytes": 4,
            "align_bytes": 4,
            "is_trivially_copyable": true,
            "fields": [{"name": "x", "offset_bits": 0, "bit_width": null, "ty": i32_ty()}]
        }]),
        serde_json::json!([{
            "symbol": "_Z12chain_assignv",
            "unmangled_name": "chain_assign",
            "is_definition": true,
            "return_ty": i32_ty(),
            "params": [],
            "abi_witness": {
                "cc": "c",
                "param_passing": [],
                "return_passing": {"kind": "direct_int", "bits": 32}
            },
            "body_stmt": {
                "kind": "compound",
                "stmts": [
                    {"kind": "decl_stmt", "var_id": 0, "name": "a", "ty": pair_ty, "init": init_pair(1)},
                    {"kind": "decl_stmt", "var_id": 1, "name": "b", "ty": pair_ty, "init": init_pair(2)},
                    {"kind": "decl_stmt", "var_id": 2, "name": "c", "ty": pair_ty, "init": init_pair(3)},
                    {
                        "kind": "expr_stmt",
                        "expr": triv_assign(var(2), triv_assign(var(0), var(1)))
                    },
                    {
                        "kind": "return",
                        "expr": {
                            "kind": "cast",
                            "cast_kind": "lvalue_to_rvalue",
                            "ty": i32_ty(),
                            "value_category": "prvalue",
                            "sub": {
                                "kind": "member",
                                "ty": i32_ty(),
                                "value_category": "lvalue",
                                "base": triv_assign(var(0), var(1)),
                                "is_arrow": false,
                                "field_name": "x",
                                "record_id": "struct.Pair",
                                "field_idx": 0,
                                "is_bitfield": false
                            }
                        }
                    }
                ]
            }
        }]),
    );
    let p = lower_bundle_json(&bundle, &Options::default())
        .expect("lvalue trivial operator= must lower without _ZN4PairaSERKS_ in bundle.functions");
    let b = body(&p, "_Z12chain_assignv");
    let record_copies = stmts(b)
        .filter(|s| matches!(s, Stmt::Assign(_, Ty::Record(r), _) if r == "struct.Pair"))
        .count();
    // `a = b` -> `c = a` -> `a = b` before `.x` = 3 record copies.
    assert_eq!(record_copies, 3, "{b:?}");
}
