// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Seams 5 and 6 (`debug_assert!` erasure, `cfg(miri)` refusal, macro
//! expansion, `#[path]`/`include!` provenance, and shadowing) and the
//! `O1a-Dual` adversarial CLI cases.

use super::*;

/// Seam 5: `debug_assert!` expands to a disabled `cfg!(debug_assertions)`
/// (`bool` constant `false`) guard and `#[cfg(debug_assertions)]` is erased at
/// expansion time under `-Cdebug-assertions=no` (even when `--overflow-checks`
/// is enabled), and `cfg(miri)` is refused on all normal crates (both
/// `--select` and `--scope=crate`).
#[test]
fn seam_5_debug_assert_erasure_and_general_cfg_miri_refusal() {
    let dbg_src = b"pub fn selected(x: u64) -> u64 {\n\
        debug_assert!(x != 0);\n\
        #[cfg(debug_assertions)]\n\
        let delta = 1u64;\n\
        #[cfg(not(debug_assertions))]\n\
        let delta = 2u64;\n\
        x + delta\n\
    }\n";

    // Default profile: `-Cdebug-assertions=no -Coverflow-checks=no` keeps
    // `debug_assert!` guarded by `const false` (`BitVec.ofNat 128 0`) with zero
    // `TerminatorKind.assert`, and erases `#[cfg(debug_assertions)]` (`1u64`)
    // before MIR construction so only `delta = 2u64` survives.
    let no_overflow = Capture::new(dbg_src);
    let no_overflow_out =
        no_overflow.selected_command().output().expect("capture debug_assert default");
    assert!(no_overflow_out.status.success(), "{no_overflow_out:?}");
    let no_overflow_lean = no_overflow.lean_source();
    assert!(
        !no_overflow_lean.contains("TerminatorKind.assert"),
        "expected no Assert terminators under default profile:\n{no_overflow_lean}"
    );
    assert!(
        no_overflow_lean.contains("ConstOperand.mk Trusted.MirAst.MirTy.bool (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 0))"),
        "expected debug_assert! cfg!(debug_assertions) guard to evaluate to false:\n{no_overflow_lean}"
    );
    assert!(
        no_overflow_lean.contains("BitVec.ofNat 128 2")
            && !no_overflow_lean.contains("BitVec.ofNat 128 1"),
        "expected #[cfg(debug_assertions)] branch erased leaving only `delta = 2`:\n{no_overflow_lean}"
    );

    // `--overflow-checks`: enables arithmetic overflow `Assert` on `x + delta`
    // without turning `debug_assertions` back on.
    let with_overflow = Capture::new(dbg_src);
    let with_overflow_out = with_overflow
        .selected_command()
        .arg("--overflow-checks")
        .output()
        .expect("capture debug_assert with overflow checks");
    assert!(with_overflow_out.status.success(), "{with_overflow_out:?}");
    let with_overflow_lean = with_overflow.lean_source();
    assert!(
        with_overflow_lean.contains("TerminatorKind.assert"),
        "expected overflow Assert under --overflow-checks:\n{with_overflow_lean}"
    );
    assert!(
        with_overflow_lean.contains("ConstOperand.mk Trusted.MirAst.MirTy.bool (Trusted.MirAst.ConstLit.scalar (BitVec.ofNat 128 0))"),
        "expected debug_assert! guard to stay false under --overflow-checks:\n{with_overflow_lean}"
    );
    assert!(
        with_overflow_lean.contains("BitVec.ofNat 128 2")
            && !with_overflow_lean.contains("BitVec.ofNat 128 1"),
        "expected #[cfg(debug_assertions)] to stay erased under --overflow-checks:\n{with_overflow_lean}"
    );

    // General `cfg(miri)` refusal across all normal crates (protecting
    // `#[cfg(miri)]` branches like `zerocopy/src/util/mod.rs:61`).
    let miri_branch_src = b"#[cfg(miri)]\n\
        pub fn selected(_x: u64) -> u64 { 0 }\n\
        #[cfg(not(miri))]\n\
        pub fn selected(x: u64) -> u64 { x.wrapping_add(1) }\n";

    let without_miri = Capture::new(miri_branch_src);
    let without_miri_out =
        without_miri.selected_command().output().expect("capture cfg(not(miri)) branch");
    assert!(without_miri_out.status.success(), "{without_miri_out:?}");
    assert!(
        without_miri.lean_source().contains("BitVec.ofNat 128 1"),
        "expected non-miri branch to be captured"
    );

    let miri_cases: &[(&str, &[&str])] = &[
        ("selected --cfg=miri", &["--select=selected", "--cfg=miri"]),
        ("whole-crate --cfg=miri", &["--scope=crate", "--cfg=miri"]),
        ("selected --cfg=miri=\"1\"", &["--select=selected", "--cfg=miri=\"1\""]),
    ];
    for (label, args) in miri_cases {
        let miri_fixture = Capture::new(miri_branch_src);
        let out = miri_fixture.command().args(*args).output().expect("capture with cfg(miri)");
        assert_refused(label, &miri_fixture, &out, "unsupported", "cfg(miri)");
    }

    // Even when the source never mentions `cfg(miri)`, passing `--cfg=miri`
    // is refused fail-closed.
    let plain_miri = Capture::new(b"pub fn selected(x: u64) -> u64 { x }\n");
    let plain_miri_out = plain_miri
        .selected_command()
        .arg("--cfg=miri")
        .output()
        .expect("capture plain crate with cfg(miri)");
    assert_refused("plain --cfg=miri", &plain_miri, &plain_miri_out, "unsupported", "cfg(miri)");
}

/// Seam 6: Macro expansion, `#[path]` / `include!` provenance, and
/// primitive/type-name shadowing.
#[test]
fn seam_6_macro_expansion_path_and_shadowing() {
    // 6a. Private `macro_rules!` expansion + nested `#[cfg_attr(all(), ...)]`
    // produces the same captured MIR body as the hand-written equivalent.
    let macro_fixture = Capture::new(
        b"macro_rules! mk_fn {\n\
              ($name:ident, $k:expr) => {\n\
                  #[cfg_attr(all(), inline)]\n\
                  pub fn $name(x: u64) -> u64 { x.wrapping_add($k) }\n\
              };\n\
          }\n\
          mk_fn!(selected, 5);\n",
    );
    let plain_fixture = Capture::new(
        b"#[inline]\n\
          pub fn selected(x: u64) -> u64 { x.wrapping_add(5) }\n",
    );
    let macro_out = macro_fixture.selected_command().output().expect("capture macro-generated fn");
    let plain_out = plain_fixture.selected_command().output().expect("capture plain fn");
    assert!(macro_out.status.success(), "{macro_out:?}");
    assert!(plain_out.status.success(), "{plain_out:?}");
    assert_eq!(
        macro_fixture.manifest()["program"],
        plain_fixture.manifest()["program"],
        "macro-expanded MIR drifted from hand-written MIR"
    );

    // 6b. Macro-smuggled unmodeled codegen attrs (`#[unsafe(no_mangle)]`) and
    // `unsafe trait` items still fail closed after expansion.
    let smuggled_no_mangle = Capture::new(
        b"macro_rules! smuggle {\n\
              ($name:ident) => {\n\
                  #[unsafe(no_mangle)]\n\
                  pub fn $name(x: u64) -> u64 { x }\n\
              };\n\
          }\n\
          smuggle!(selected);\n",
    );
    let smuggled_out =
        smuggled_no_mangle.selected_command().output().expect("capture smuggled no_mangle");
    assert_refused(
        "macro-smuggled no_mangle",
        &smuggled_no_mangle,
        &smuggled_out,
        "unsupported",
        "NO_MANGLE",
    );

    let smuggled_unsafe_trait = Capture::new(
        b"macro_rules! smuggle_trait {\n\
              ($name:ident) => {\n\
                  pub unsafe trait $name {}\n\
              };\n\
          }\n\
          smuggle_trait!(HiddenUnsafe);\n\
          pub fn selected(x: u64) -> u64 { x }\n",
    );
    let smuggled_trait_out = smuggled_unsafe_trait
        .command()
        .arg("--scope=crate")
        .output()
        .expect("capture smuggled unsafe trait");
    assert_refused(
        "macro-smuggled unsafe trait",
        &smuggled_unsafe_trait,
        &smuggled_trait_out,
        "unsupported",
        "whole-crate obligation is unsupported: Trait",
    );

    // 6c. Declared vs. undeclared `#[path = "..."]` module and `include!`.
    let path_fixture = Capture::new(
        b"#[path = \"sub.rs\"]\n\
          mod sub;\n\
          pub fn selected(x: u64) -> u64 { sub::helper(x) }\n",
    );
    let sub_path = path_fixture.directory.path().join("sub.rs");
    std::fs::write(&sub_path, b"pub fn helper(x: u64) -> u64 { x }\n").expect("write sub.rs");
    let undeclared_out =
        path_fixture.selected_command().output().expect("capture undeclared #[path]");
    assert_refused(
        "undeclared #[path]",
        &path_fixture,
        &undeclared_out,
        "unsupported",
        "undeclared compiler read",
    );
    let declared_out = path_fixture
        .selected_command()
        .arg("--source-file")
        .arg(&sub_path)
        .output()
        .expect("capture declared #[path]");
    assert!(declared_out.status.success(), "{declared_out:?}");
    let reads = path_fixture.manifest()["source_files"].as_array().unwrap().clone();
    let canon_sub = sub_path.canonicalize().expect("canonicalize sub.rs");
    assert!(
        reads.iter().any(|r| r["path"] == canon_sub.to_str().unwrap()),
        "declared #[path] file missing from manifest source_files: {reads:?}"
    );

    let include_fixture = Capture::new(b"include!(\"body.inc\");\n");
    let inc_path = include_fixture.directory.path().join("body.inc");
    std::fs::write(&inc_path, b"pub fn selected(x: u64) -> u64 { x }\n").expect("write body.inc");
    let undeclared_inc =
        include_fixture.selected_command().output().expect("capture undeclared include!");
    assert_refused(
        "undeclared include!",
        &include_fixture,
        &undeclared_inc,
        "unsupported",
        "undeclared compiler read",
    );
    let declared_inc = include_fixture
        .selected_command()
        .arg("--source-file")
        .arg(&inc_path)
        .output()
        .expect("capture declared include!");
    assert!(declared_inc.status.success(), "{declared_inc:?}");

    // 6d. Primitive / type-name shadowing (distinct from `mod core`): capture
    // reads resolved `ty::Ty`, never raw source identifiers.
    let alias_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          type usize = u16;\n\
          pub fn selected(x: usize) -> usize { x }\n",
    );
    let alias_out = alias_shadow.selected_command().output().expect("capture type usize = u16");
    assert!(alias_out.status.success(), "{alias_out:?}");
    let alias_lean = alias_shadow.lean_source();
    assert!(
        alias_lean.contains("Trusted.MirAst.IntWidth.i16")
            && !alias_lean.contains("Trusted.MirAst.IntWidth.isize"),
        "expected shadowed `type usize = u16` to capture as i16, not isize:\n{alias_lean}"
    );

    let struct_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          pub struct u8(pub u16);\n\
          pub fn selected(x: u8) -> u16 { x.0 }\n",
    );
    let struct_out = struct_shadow.selected_command().output().expect("capture struct u8");
    assert_refused(
        "struct shadowing primitive u8",
        &struct_shadow,
        &struct_out,
        "unsupported",
        "unsupported type",
    );

    let enum_shadow = Capture::new(
        b"#[allow(non_camel_case_types)]\n\
          #[repr(u8)]\n\
          pub enum usize { A = 0, B = 1 }\n\
          pub fn selected(x: usize) -> usize { x }\n",
    );
    let enum_out = enum_shadow.selected_command().output().expect("capture enum usize");
    assert!(enum_out.status.success(), "{enum_out:?}");
    let enum_lean = enum_shadow.lean_source();
    assert!(
        enum_lean.contains("Trusted.MirAst.MirTy.enum")
            && !enum_lean.contains("Trusted.MirAst.IntWidth.isize"),
        "expected shadowed `enum usize` to capture as MirTy.enum, not isize:\n{enum_lean}"
    );
}

/// `O1a-Dual` CLI-level ill-formedness and dead-branch PME tests: conflicting
/// `#[repr(...)]` attributes fail compilation with the expected rustc error
/// codes and zero artifacts, and instantiated dead-branch `SizeEq` PMEs fail
/// closed during capture (`eval_required_consts`).
#[test]
fn o1a_dual_ill_formed_repr_and_dead_branch_pme_refused() {
    let repr_cases: &[(&str, &[u8], &str)] = &[
        (
            "repr(C, packed) + align conflict",
            b"#[repr(C, packed)]\n\
              #[repr(align(8))]\n\
              pub struct Bad { pub x: u32 }\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0587",
        ),
        (
            "duplicate repr(transparent)",
            b"#[repr(transparent, transparent)]\n\
              pub struct Dup(pub u32);\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0692",
        ),
        (
            "multi-field repr(transparent)",
            b"#[repr(transparent)]\n\
              pub struct Multi { pub a: u32, pub b: u32 }\n\
              pub fn selected(x: u64) -> u64 { x }\n",
            "E0690",
        ),
    ];

    for (label, src, code) in repr_cases {
        let fixture = Capture::new(src);
        let out = fixture.command().arg("--scope=crate").output().expect("capture ill-formed repr");
        assert_refused(label, &fixture, &out, "compiler_failed", "rustc rejected the compilation");
        let err = stderr(&out);
        assert!(
            err.contains(code),
            "{label}: expected rustc error code {code} in stderr, got:\n{err}"
        );
    }

    // Dead-branch generic `SizeEq` PME (`if false { ... }`): even though the
    // const assertion sits in a dead branch, instantiating `bad::<u8, u16>`
    // must fail closed via `eval_required_consts` during capture.
    let pme_src = b"pub fn bad<T, U>(x: u64) -> u64 {\n\
        if false {\n\
            const { assert!(core::mem::size_of::<T>() == core::mem::size_of::<U>()) }\n\
        }\n\
        x\n\
    }\n";
    let pme_ok = Capture::new(pme_src);
    let pme_ok_out = pme_ok
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"bad","args":["u16","u16"]}"#)
        .output()
        .expect("capture matching dead-branch PME instantiation");
    assert!(pme_ok_out.status.success(), "{pme_ok_out:?}");

    let pme_fail = Capture::new(pme_src);
    let pme_fail_out = pme_fail
        .command()
        .arg("--instantiate")
        .arg(r#"{"path":"bad","args":["u8","u16"]}"#)
        .output()
        .expect("capture failing dead-branch PME instantiation");
    assert_eq!(pme_fail_out.status.code(), Some(1), "{pme_fail_out:?}");
    let pme_status = status(&pme_fail_out);
    assert!(
        matches!(pme_status["status"].as_str(), Some("compiler_failed") | Some("unsupported")),
        "expected failing dead-branch PME to fail closed, got {pme_status}"
    );
    pme_fail.assert_no_capture_artifacts();
}
