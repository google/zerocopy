// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! End-to-end tests over RawCppBundle fixtures captured by a real
//! `anneal-clang-dump` from `tests/fixtures/src/*.c` (see
//! `README.md`).

use std::path::PathBuf;

use anneal_lower_cpp::{
    ir::{Expr, Program, Proj, SignedOverflowMode, Terminator, Ty},
    lower_bundle_json, lower_bundle_json_to_lean, EmitOptions, LowerError, Options,
};

fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures").join(name)
}

fn fixture(name: &str) -> String {
    std::fs::read_to_string(fixture_path(&format!("{name}.json")))
        .unwrap_or_else(|e| panic!("missing fixture {name}.json: {e}"))
}

fn lower(name: &str) -> Result<Program, LowerError> {
    lower_bundle_json(&fixture(name), &Options::default())
}

fn edit(name: &str, f: impl FnOnce(&mut serde_json::Value)) -> String {
    let mut v: serde_json::Value = serde_json::from_str(&fixture(name)).unwrap();
    f(&mut v);
    v.to_string()
}

#[track_caller]
fn assert_unsequenced(name: &str) {
    match lower(name) {
        Err(LowerError::UnsequencedSideEffects { .. }) => {}
        other => panic!("{name}: expected UnsequencedSideEffects, got {other:?}"),
    }
}

// --------------------------- mandatory negatives ---------------------------

#[test]
fn rejects_unsequenced_read_and_write() {
    // x + (x = 1)
    assert_unsequenced("neg_unseq_assign_read");
}

#[test]
fn rejects_unsequenced_call_arguments() {
    // sink(++x, ++x)
    assert_unsequenced("neg_unseq_call_args");
}

#[test]
fn rejects_exceptions_policy() {
    match lower("neg_exceptions") {
        Err(LowerError::UnsupportedLangPolicy { .. }) => {}
        other => panic!("expected UnsupportedLangPolicy, got {other:?}"),
    }
}

#[test]
fn rejects_subscript_with_postincrement_of_index() {
    // a[i] = i++
    assert_unsequenced("neg_subscript_postinc");
}

#[test]
fn rejects_nested_assignment_to_same_variable() {
    // x = (x = 1) + 1
    assert_unsequenced("neg_nested_assign");
}

#[test]
fn rejects_store_unsequenced_with_postincrement() {
    // x = x++
    assert_unsequenced("neg_self_postinc");
}

#[test]
fn rejects_two_indeterminately_sequenced_calls() {
    // g() + h()
    assert_unsequenced("neg_two_calls");
}

// ------------------------------- positives -------------------------------

#[test]
fn accepts_single_side_effect_expressions() {
    // x = x + 1; x += 1; ++x; s1 += *buf++; p[i] = p[i] + 1; while (len > 0)
    let p = lower("pos_ssenf_ok").expect("pos_ssenf_ok must lower");
    assert_eq!(p.bodies.len(), 1);
    assert!(!p.is_partial);
}

#[test]
fn clean_adler32_lowers_to_expected_shape() {
    let p = lower("clean_adler32").expect("clean_adler32 must lower");
    assert_eq!(p.entry_def_id, 0);
    assert_eq!(p.bodies.len(), 1);
    assert!(p.records.is_empty());
    let b = &p.bodies[0];
    assert_eq!(b.identity, "clean_adler32_update");
    assert!(!b.is_external);
    // _0 return slot, _1.._3 parameters, then locals.
    assert_eq!(b.locals[0].ty, b.sig.ret);
    assert!(!b.locals[0].is_param);
    assert!(b.locals[1..=3].iter().all(|l| l.is_param));
    assert!(b.locals[4..].iter().all(|l| !l.is_param));
    let u8_char =
        Ty::Int(anneal_lower_cpp::ir::Width::W8, anneal_lower_cpp::ir::Sign::Unsigned, true);
    assert_eq!(b.sig.params[1], Ty::Ptr(Box::new(u8_char), true, false, false));
    // Two loops: two back edges to loop headers and one `ret`.
    let rets = b.blocks.iter().filter(|blk| blk.term == Terminator::Ret).count();
    assert_eq!(rets, 1);
    // `*buf++` reads through a dereference projection.
    let derefs = format!("{:?}", b.blocks).matches("Deref").count();
    assert!(derefs >= 1);
    assert_eq!(p.policy.signed_overflow, SignedOverflowMode::IsoUB);
    assert!(p.policy.exceptions_off);
}

#[test]
fn control_flow_is_explicit() {
    let p = lower("pos_control_flow").expect("pos_control_flow must lower");
    let b = &p.bodies[0];
    let branches = b.blocks.iter().filter(|blk| matches!(blk.term, Terminator::Branch(..))).count();
    // for-cond, 2x if, ||, &&, ?:, do-while cond (&&, !), 3 switch cases.
    assert!(branches >= 10, "only {branches} branches");
    for (i, blk) in b.blocks.iter().enumerate() {
        let succ = match &blk.term {
            Terminator::Goto(t) => vec![*t],
            Terminator::Branch(_, t, f) => vec![*t, *f],
            Terminator::Call(_, _, _, n) => vec![*n],
            Terminator::Ret | Terminator::Unreachable => vec![],
        };
        for s in succ {
            assert!(s < b.blocks.len(), "bb{i} jumps to missing bb{s}");
        }
    }
}

#[test]
fn struct_fields_and_direct_calls() {
    let p = lower("pos_struct_ptr").expect("pos_struct_ptr must lower");
    assert_eq!(p.bodies.len(), 2);
    assert_eq!(p.bodies[0].identity, "pos_struct_ptr");
    assert_eq!(p.bodies[1].identity, "mix");
    assert_eq!(p.records.len(), 1);
    let r = &p.records[0];
    assert_eq!(r.record_id, "struct.pair");
    assert_eq!((r.size_bytes, r.align_bytes), (8, 4));
    assert_eq!(r.fields[1].offset_bits, 32);
    let calls: Vec<_> = p.bodies[0]
        .blocks
        .iter()
        .filter_map(|b| match &b.term {
            Terminator::Call(c, args, dst, _) => Some((c.clone(), args.len(), dst.is_some())),
            _ => None,
        })
        .collect();
    assert_eq!(calls, vec![("mix".to_owned(), 2, true)]);
    let dbg = format!("{:?}", p.bodies[0].blocks);
    assert!(dbg.contains("Field(\"struct.pair\", 1"));
    let _ = (Proj::Deref, Expr::ConstBool(true));
}

// --------------------------- policy and schema ---------------------------

#[test]
fn rejects_fast_math() {
    let text = edit("clean_adler32", |v| v["lang_policy"]["fast_math"] = true.into());
    assert!(matches!(
        lower_bundle_json(&text, &Options::default()),
        Err(LowerError::UnsupportedLangPolicy { .. })
    ));
}

#[test]
fn rejects_trapping_overflow_and_accepts_wrapv() {
    let trap = edit("clean_adler32", |v| v["lang_policy"]["signed_overflow"] = "trapping".into());
    assert!(matches!(
        lower_bundle_json(&trap, &Options::default()),
        Err(LowerError::UnsupportedLangPolicy { .. })
    ));
    let wrapv = edit("clean_adler32", |v| v["lang_policy"]["signed_overflow"] = "wrapv".into());
    let p = lower_bundle_json(&wrapv, &Options::default()).unwrap();
    assert_eq!(p.policy.signed_overflow, SignedOverflowMode::Wrapv);
}

#[test]
fn rejects_cplusplus_policy() {
    let text = edit("clean_adler32", |v| v["lang_policy"]["is_cplusplus"] = true.into());
    assert!(matches!(
        lower_bundle_json(&text, &Options::default()),
        Err(LowerError::UnsupportedLangPolicy { .. })
    ));
}

#[test]
fn rejects_wrong_schema_version() {
    let text = edit("clean_adler32", |v| v["schema_version"] = 2.into());
    assert!(matches!(
        lower_bundle_json(&text, &Options::default()),
        Err(LowerError::Schema { .. })
    ));
}

#[test]
fn rejects_abi_witness_mismatch() {
    let text = edit("clean_adler32", |v| {
        v["functions"][0]["abi_witness"]["param_passing"][2]["bits"] = 32.into()
    });
    assert!(matches!(
        lower_bundle_json(&text, &Options::default()),
        Err(LowerError::AbiMismatch { .. })
    ));
}

#[test]
fn rejects_unsupported_nodes() {
    let text = edit("clean_adler32", |v| {
        v["functions"][0]["body_stmt"]["stmts"][0] =
            serde_json::json!({"kind": "unsupported_stmt", "desc": "GCCAsmStmt"});
    });
    assert!(matches!(
        lower_bundle_json(&text, &Options::default()),
        Err(LowerError::UnsupportedConstruct { .. })
    ));
}

// ------------------------------ determinism ------------------------------

#[test]
fn clean_adler32_lean_matches_golden() {
    let lean =
        lower_bundle_json_to_lean(&fixture("clean_adler32"), &EmitOptions::default()).unwrap();
    let again =
        lower_bundle_json_to_lean(&fixture("clean_adler32"), &EmitOptions::default()).unwrap();
    assert_eq!(lean, again, "emission must be deterministic");
    let golden = fixture_path("clean_adler32.CapturedCpp.golden");
    if std::env::var_os("ANNEAL_BLESS").is_some() {
        std::fs::write(&golden, &lean).unwrap();
    }
    let want = std::fs::read_to_string(&golden).expect("golden file (bless with ANNEAL_BLESS=1)");
    assert_eq!(lean, want, "CapturedCpp.lean drifted; re-bless with ANNEAL_BLESS=1 if intended");
}

// -------------------------------- globals --------------------------------

#[test]
fn rejects_unsequenced_write_through_alias_of_local() {
    // x + (*q = 1) where q == &x
    assert_unsequenced("neg_escaped_alias");
}

#[test]
fn global_reads_become_disclosed_external_stubs() {
    let p = lower("pos_global_load").expect("pos_global_load must lower");
    assert!(p.is_partial, "a program with a global-load stub must be partial");
    let stub = p.bodies.last().unwrap();
    assert_eq!(stub.identity, "anneal.global_load.pos_global_flag");
    assert!(stub.is_external && stub.blocks.is_empty() && stub.sig.params.is_empty());
    assert_eq!(stub.sig.ret, Ty::I32);
}

#[test]
fn rejects_global_stores() {
    match lower("neg_global_store") {
        Err(LowerError::UnsupportedConstruct { .. }) => {}
        other => panic!("expected UnsupportedConstruct, got {other:?}"),
    }
}

#[test]
fn rejects_volatile_accesses() {
    match lower("neg_volatile") {
        Err(LowerError::UnsupportedConstruct { .. }) => {}
        other => panic!("expected UnsupportedConstruct, got {other:?}"),
    }
}

#[test]
fn local_arrays_in_nested_scopes_lower() {
    let p = lower("pos_local_array").expect("pos_local_array must lower");
    let dbg = format!("{:?}", p.bodies[0].blocks);
    assert!(dbg.contains("Index("), "local array accesses use index projections");
}

// ------------------- Rung 1: C++20 (-fno-exceptions) -------------------

fn body<'p>(p: &'p Program, symbol: &str) -> &'p anneal_lower_cpp::ir::Body {
    p.bodies.iter().find(|b| b.identity == symbol).unwrap_or_else(|| panic!("no body `{symbol}`"))
}

fn lower_ok(name: &str) -> Program {
    lower(name).unwrap_or_else(|e| panic!("{name}: {e}"))
}

#[track_caller]
fn assert_unsupported_construct(name: &str) {
    match lower(name) {
        Err(LowerError::UnsupportedConstruct { .. }) => {}
        other => panic!("{name}: expected UnsupportedConstruct, got {other:?}"),
    }
}

#[test]
fn cxx_instantiated_howmany_lowers_with_itanium_abi() {
    let p = lower_ok("cxx_howmany");
    let b = body(&p, "_Z7HowManyImET_S0_S0_");
    assert!(b.sig.abi_cxx);
    assert_eq!(b.sig.params.len(), 2);
    let text = format!("{b:?}");
    assert!(text.contains("Binary(Div"), "{text}");
    assert!(text.contains("Binary(Add"), "{text}");
}

#[test]
fn cxx_roundup_calls_the_howmany_specialization() {
    let p = lower_ok("cxx_roundup");
    let b = body(&p, "_Z7RoundUpImET_S0_S0_");
    assert!(b
        .blocks
        .iter()
        .any(|blk| matches!(&blk.term, Terminator::Call(s, ..) if s == "_Z7HowManyImET_S0_S0_")));
    body(&p, "_Z7HowManyImET_S0_S0_");
}

#[test]
fn cxx_bitmask_specialization_lowers() {
    let p = lower_ok("cxx_bitmask");
    let text = format!("{:?}", body(&p, "_Z7BitmaskImET_j"));
    assert!(text.contains("Binary(Shl"), "{text}");
    assert!(text.contains("Unary(BitNot"), "{text}");
}

#[test]
fn cxx_guard_return_slot_is_initialized_before_the_destructor_runs() {
    use anneal_lower_cpp::ir::Stmt;
    let p = lower_ok("cxx_guard");
    let b = body(&p, "_Z12guard_returniPi");
    // Locals: _0 return, _1 v, _2 log, _3 x, _4 g.
    let (x, g) = (3, 4);
    let entry = &b.blocks[0];
    let assigns: Vec<usize> = entry
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Assign(pl, ..) if pl.projs.is_empty() => Some(pl.base),
            _ => None,
        })
        .collect();
    // `x = v`, then `x = 42`, then `_0 = x` last, all while `g` is alive.
    assert_eq!(assigns, vec![x, x, 0], "{entry:?}");
    match &entry.stmts.last() {
        Some(Stmt::Assign(pl, _, Expr::ReadPlace(src, _))) => {
            assert_eq!((pl.base, src.base), (0, x));
        }
        other => panic!("last statement {other:?}"),
    }
    let next = match &entry.term {
        Terminator::Call(dtor, args, None, next) => {
            assert_eq!(dtor, "_ZN5GuardD1Ev");
            assert!(matches!(&args[..], [Expr::AddrOf(pl, _)] if pl.base == g));
            *next
        }
        other => panic!("expected the destructor call, got {other:?}"),
    };
    let tail = &b.blocks[next];
    assert_eq!(tail.stmts, vec![Stmt::StorageDead(g), Stmt::StorageDead(x)]);
    assert_eq!(tail.term, Terminator::Ret);
    body(&p, "_ZN5GuardD1Ev");
}

#[test]
fn cxx_std_bit_cast_style_template_binds_a_reference() {
    let p = lower_ok("cxx_bitcast_pod");
    let bc = body(&p, "_Z8bit_castIm3PodET_RKT0_");
    assert_eq!(bc.sig.param_non_null, vec![true]);
    let text = format!("{bc:?}");
    assert!(text.contains("BitCast(Record(\"struct.Pod\"), Int(W64, Unsigned, false)"), "{text}");
    let caller = format!("{:?}", body(&p, "_Z10pod_to_u643Pod"));
    assert!(caller.contains("AddrOf("), "{caller}");
}

#[test]
fn cxx_packed_bitfield_descriptor_round_trips_through_bit_cast() {
    let p = lower_ok("cxx_bitfield_pack");
    let text = format!("{:?}", body(&p, "_Z9pack_descttt"));
    assert!(text.contains("ZeroInit("), "{text}");
    for proj in [
        "Bitfield(\"struct.PacketDesc\", 0, 0, 11, false)",
        "Bitfield(\"struct.PacketDesc\", 2, 16, 14, false)",
        "Bitfield(\"struct.PacketDesc\", 3, 30, 1, false)",
    ] {
        assert!(text.contains(proj), "missing {proj}: {text}");
    }
    assert!(text.contains("BitCast(Record(\"struct.PacketDesc\")"), "{text}");
    let q = lower_ok("cxx_bitfield_unpack");
    let text = format!("{:?}", body(&q, "_Z8desc_lenm"));
    assert!(text.contains("BitCast(Int(W64, Unsigned, false), Record(\"struct.PacketDesc\")"));
    assert!(text.contains("Bitfield(\"struct.PacketDesc\", 2, 16, 14, false)"), "{text}");
}

#[test]
fn cxx_span_constructor_methods_and_subscript_operator() {
    let p = lower_ok("cxx_span_sum");
    let ctor = body(&p, "_ZN4SpanIKhEC1EPS0_m");
    assert_eq!(ctor.sig.param_non_null, vec![true, false, false]);
    let index = body(&p, "_ZNK4SpanIKhEixEm");
    assert!(index.sig.ret.pointee().is_some(), "operator[] returns a reference");
    let caller = body(&p, "_Z8span_sumPKhm");
    for callee in ["_ZN4SpanIKhEC1EPS0_m", "_ZNK4SpanIKhE4sizeEv", "_ZNK4SpanIKhEixEm"] {
        assert!(
            caller.blocks.iter().any(|b| matches!(&b.term, Terminator::Call(s, ..) if s == callee)),
            "no call to {callee}"
        );
    }
    let q = lower_ok("cxx_span_data");
    body(&q, "_ZNK4SpanIKhE4dataEv");
}

#[test]
fn cxx_requires_constrained_template_takes_a_slice_by_value() {
    let p = lower_ok("cxx_requires");
    let b = body(&p, "_Z9slice_lenIiQ5SmallIT_EEm8SliceRefIS0_E");
    assert_eq!(b.sig.params, vec![Ty::Record("struct.SliceRef<int>".into())]);
}

#[test]
fn cxx_references_lower_to_non_null_pointers() {
    let p = lower_ok("cxx_ref");
    assert_eq!(body(&p, "_Z4bumpRi").sig.param_non_null, vec![true]);
    let text = format!("{:?}", body(&p, "_Z7use_refi"));
    assert!(text.contains("AddrOf("), "{text}");
    assert!(text.contains("Deref"), "{text}");
}

#[test]
fn cxx_constructor_initializers_and_member_calls() {
    let p = lower_ok("cxx_counter");
    let ctor = format!("{:?}", body(&p, "_ZN7CounterC1Ev"));
    assert!(ctor.contains("Field(\"struct.Counter\", 0"), "{ctor}");
    let caller = body(&p, "_Z11counter_sumii");
    let calls: Vec<&str> = caller
        .blocks
        .iter()
        .filter_map(|b| match &b.term {
            Terminator::Call(s, ..) => Some(s.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(
        calls,
        vec!["_ZN7CounterC1Ev", "_ZN7Counter3addEi", "_ZN7Counter3addEi", "_ZNK7Counter3getEv"]
    );
}

#[test]
fn cxx_full_expression_temporary_is_destroyed_after_the_return_value() {
    use anneal_lower_cpp::ir::Stmt;
    let p = lower_ok("cxx_temp_dtor");
    let b = body(&p, "_Z9temp_dtorPi");
    let dtor_block = b
        .blocks
        .iter()
        .find(|blk| matches!(&blk.term, Terminator::Call(s, ..) if s == "_ZN6LoggerD1Ev"))
        .expect("temporary destructor call");
    assert!(
        matches!(dtor_block.stmts.last(), Some(Stmt::Assign(pl, ..)) if pl.base == 0),
        "`_0` must be written before the temporary dies: {dtor_block:?}"
    );
}

#[test]
fn cxx_break_runs_the_loop_scope_destructor() {
    let p = lower_ok("cxx_loop_raii");
    let b = body(&p, "_Z9loop_raiiiPi");
    let dtor_calls = b
        .blocks
        .iter()
        .filter(|blk| matches!(&blk.term, Terminator::Call(s, ..) if s == "_ZN6Guard2D1Ev"))
        .count();
    // One on the `break` edge, one at the end of each iteration.
    assert_eq!(dtor_calls, 2);
}

#[test]
fn cxx_rejects_virtual_calls() {
    assert_unsupported_construct("cxx_neg_virtual");
}

#[test]
fn cxx_rejects_exceptions() {
    match lower("cxx_neg_exceptions") {
        Err(LowerError::UnsupportedLangPolicy { .. }) => {}
        other => panic!("expected UnsupportedLangPolicy, got {other:?}"),
    }
}

#[test]
fn cxx_rejects_unsequenced_constructor_arguments() {
    // Foo f(++x, ++x)
    assert_unsequenced("cxx_neg_unseq_ctor");
}

#[test]
fn cxx_rejects_dialects_outside_rung1() {
    let j = edit("cxx_howmany", |v| v["lang_policy"]["lang_standard"] = "c++14".into());
    match lower_bundle_json(&j, &Options::default()) {
        Err(LowerError::UnsupportedLangPolicy { .. }) => {}
        other => panic!("expected UnsupportedLangPolicy, got {other:?}"),
    }
}

#[test]
fn cxx_rejects_undeclared_destructors() {
    let j = edit("cxx_guard", |v| {
        let f = &mut v["functions"][0]["body_stmt"]["stmts"][1];
        f["dtor_symbol"] = "<undeclared>".into();
    });
    match lower_bundle_json(&j, &Options::default()) {
        Err(LowerError::UnsupportedConstruct { .. }) => {}
        other => panic!("expected UnsupportedConstruct, got {other:?}"),
    }
}

#[test]
fn cxx_lean_rendering_uses_the_new_constructors() {
    let lean =
        lower_bundle_json_to_lean(&fixture("cxx_bitfield_pack"), &EmitOptions::default()).unwrap();
    assert!(lean.contains("CppAbiKind.cxxItanium"));
    assert!(lean.contains("CppStmt.zeroInit"));
    assert!(lean.contains("(CppProjElem.bitfield \"struct.PacketDesc\" 2 16 14 false)"));
    assert!(lean.contains("CppExpr.bitCast"));
    let lean = lower_bundle_json_to_lean(&fixture("cxx_ref"), &EmitOptions::default()).unwrap();
    assert!(lean.contains("paramNonNull := [true]"));
}

#[test]
fn cxx_clobbering_destructor_runs_after_the_return_value_is_captured() {
    use anneal_lower_cpp::ir::Stmt;
    let p = lower_ok("cxx_clobber");
    let b = body(&p, "_Z14clobber_returni");
    let entry = &b.blocks[0];
    // `_0 = x` is the last statement before the destructor call.
    assert!(
        matches!(entry.stmts.last(), Some(Stmt::Assign(pl, _, Expr::ReadPlace(src, _)))
            if pl.base == 0 && src.base == 2),
        "{entry:?}"
    );
    assert!(matches!(&entry.term, Terminator::Call(s, ..) if s == "_ZN7ClobberD1Ev"));
}

#[test]
fn large_bodies_are_hoisted_into_bounded_chunks() {
    let mut p = lower("clean_adler32").expect("clean_adler32 must lower");
    let b = &mut p.bodies[0];
    let local = b.locals[4].clone();
    let first_new = b.locals.len();
    for _ in 0..700 {
        b.locals.push(local.clone());
    }
    for id in first_new..first_new + 700 {
        b.blocks[0].stmts.push(anneal_lower_cpp::ir::Stmt::StorageLive(id));
    }
    let lean = p.lean(&anneal_lower_cpp::ir::EmitMeta {
        namespace: "CapturedCpp",
        tu_main_file: "synthetic.c",
        target_triple: "x86_64-unknown-linux-gnu",
        lang_standard: "c11",
    });
    assert!(lean.contains("def body_0_clean_adler32_update_locals_0 : List CppLocalDecl"));
    assert!(lean.contains("def body_0_clean_adler32_update_bb0_stmts_0 : List CppStmt"));
    // Every hoisted leaf holds at most `LEAF_LEN` elements.
    for def in lean.split("\ndef ").filter(|d| d.contains("_locals_") || d.contains("_stmts_")) {
        let body = def.split(":= [").nth(1).unwrap_or("");
        let body = body.split("\n]").next().unwrap_or("");
        assert!(body.matches(",\n").count() < anneal_lower_common::chunk::LEAF_LEN, "{def}");
    }
    if let Some(dir) = std::env::var_os("ANNEAL_LOWER_CPP_DUMP_DIR") {
        std::fs::write(std::path::Path::new(&dir).join("LargeCapturedCpp.lean"), &lean).unwrap();
    }
}
