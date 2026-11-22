#!/usr/bin/env python3
"""Execute rustc (and optionally cargo) on small crates to observe how
`#![forbid(unsafe_code)]`, `-F unsafe_code`, `--cap-lints`, foreign macros,
Edition 2024 unsafe markers and `#[expect]` interact.

Nothing in this file states an outcome as a fact: every `compile_rc`, `stderr`,
`run_rc`, `stdout` and MIR excerpt in the JSON report is captured from a child
process started by this run.  The `expect` entries are hypotheses; a case
passes only when the captured behaviour matches them, and the script exits
non-zero when any executed case fails.

Usage:
    python3 probe_forbid_unsafe_and_cap_lints.py [--out results.json] [--keep DIR]

Environment:
    RUSTC   rustc binary to probe (default: `rustc` on PATH)
    CARGO   cargo binary for the dependency cases (default: `cargo` on PATH;
            the two cargo cases are reported as skipped when cargo or git is
            unavailable)

Requires Python 3.9+ and only the standard library.  One case needs the
unstable `proc_macro_def_site` feature and three cases need `--emit=mir`
output; on a toolchain that rejects `#![feature]` the def-site case is
reported as skipped.
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SCHEMA = "forbid-unsafe-cap-lints-probe/1"
TIMEOUT_S = 180

# --------------------------------------------------------------------------
# Sources.  Every file compiled by the probe is listed here verbatim.
# --------------------------------------------------------------------------

SOURCES: dict[str, str] = {
    # ---- upstream (foreign) crates -------------------------------------
    "up_unsafe_mac.rs": """\
// Foreign `macro_rules!` crate.  Compiled as an rlib with --edition 2021.
#[macro_export]
macro_rules! foreign_unsafe_expr { () => { unsafe { 101u32 } }; }
#[macro_export]
macro_rules! foreign_allow_unsafe_expr {
    () => {{ #[allow(unsafe_code)] let v = unsafe { 102u32 }; v }};
}
#[macro_export]
macro_rules! foreign_passthrough { ($e:expr) => { $e }; }
#[macro_export]
macro_rules! foreign_call_local { ($m:ident) => { $m!() }; }
#[macro_export]
macro_rules! foreign_read_raw { ($p:expr) => { unsafe { *$p } }; }
#[macro_export]
macro_rules! foreign_ed2021_ffi_items {
    () => {
        #[no_mangle]
        pub extern "C" fn up_exported_symbol() -> u32 { 301 }
        extern "C" { fn abs(x: i32) -> i32; }
        pub fn foreign_abs(x: i32) -> i32 { unsafe { abs(x) } }
    };
}
""",
    "up_unsafe_pm.rs": """\
// Foreign function-like proc-macro crate.  `pm_def_site` is compiled only
// when the probe passes `--cfg probe_def_site` (unstable `Span::def_site`).
#![cfg_attr(probe_def_site, feature(proc_macro_def_site))]
extern crate proc_macro;
use proc_macro::{Delimiter, Group, Ident, Literal, Span, TokenStream, TokenTree};

// Emits `unsafe { <value>u32 }` with every token carrying `span`.
fn unsafe_block(value: u32, span: Span) -> TokenStream {
    let mut lit = Literal::u32_suffixed(value);
    lit.set_span(span);
    let inner: TokenStream = TokenTree::Literal(lit).into();
    let mut group = Group::new(Delimiter::Brace, inner);
    group.set_span(span);
    [TokenTree::Ident(Ident::new("unsafe", span)), TokenTree::Group(group)]
        .into_iter()
        .collect()
}

#[proc_macro]
pub fn pm_call_site(_: TokenStream) -> TokenStream { unsafe_block(201, Span::call_site()) }
#[proc_macro]
pub fn pm_mixed_site(_: TokenStream) -> TokenStream { unsafe_block(202, Span::mixed_site()) }
#[cfg(probe_def_site)]
#[proc_macro]
pub fn pm_def_site(_: TokenStream) -> TokenStream { unsafe_block(203, Span::def_site()) }
// Re-uses the span of the first input token, i.e. a span written in the
// invoking crate, for every emitted token.
#[proc_macro]
pub fn pm_input_span(input: TokenStream) -> TokenStream {
    let span = input.into_iter().next().expect("one input token").span();
    unsafe_block(204, span)
}
// Attribute and derive macros that add a function containing an `unsafe`
// block.  Tokens parsed from a string carry `Span::call_site()`.
#[proc_macro_attribute]
pub fn pm_attr_inject(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let extra: TokenStream =
        "fn injected_by_attr() -> u32 { unsafe { 205u32 } }".parse().expect("valid tokens");
    item.into_iter().chain(extra).collect()
}
#[proc_macro_derive(PmDeriveInject)]
pub fn pm_derive_inject(_item: TokenStream) -> TokenStream {
    "fn injected_by_derive() -> u32 { unsafe { 206u32 } }".parse().expect("valid tokens")
}
""",
    # ---- Part A --------------------------------------------------------
    "a_forbid.rs": """\
#![forbid(unsafe_code)]
fn main() { let x = unsafe { 42u32 }; println!("UNSAFE_RAN={}", x); }
""",
    "a_plain.rs": """\
fn main() { let x = unsafe { 42u32 }; println!("UNSAFE_RAN={}", x); }
""",
    # ---- Part B --------------------------------------------------------
    "b0_local_mac.rs": """\
// Local macro_rules! whose body contains the `unsafe` block.
#![forbid(unsafe_code)]
macro_rules! loc_u { () => { unsafe { 100u32 } }; }
fn main() { println!("{}", loc_u!()); }
""",
    "b1_fmac.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("FMAC={}", up_unsafe_mac::foreign_unsafe_expr!()); }
""",
    "b2_fmac_allow.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("FMAC_ALLOW={}", up_unsafe_mac::foreign_allow_unsafe_expr!()); }
""",
    "b3_pm_call.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("PM_CALL={}", up_unsafe_pm::pm_call_site!()); }
""",
    "b4_pm_mixed.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("PM_MIXED={}", up_unsafe_pm::pm_mixed_site!()); }
""",
    "b5_pm_def.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("PM_DEF={}", up_unsafe_pm::pm_def_site!()); }
""",
    # ---- Part C --------------------------------------------------------
    "c1_uop.rs": """\
unsafe fn deref_raw(p: *const u32) -> u32 { *p }
fn main() { let v = 9u32; println!("UOP={}", unsafe { deref_raw(&v) }); }
""",
    "c2_smut.rs": """\
static mut G: u32 = 1;
fn main() { unsafe { let r = &mut G; *r += 1; println!("SMUT={}", *r); } }
""",
    "c2_raw.rs": """\
static mut G: u32 = 1;
fn main() { unsafe { let p = &raw mut G; *p += 1; println!("RAW={}", *p); } }
""",
    "c3_nm.rs": """\
#[no_mangle] pub extern "C" fn foo_nm() -> u32 { 7 }
fn main() { println!("NM={}", foo_nm()); }
""",
    "c4_forbid_nm.rs": """\
#![forbid(unsafe_code)]
#[unsafe(no_mangle)] pub extern "C" fn foo_nm() -> u32 { 7 }
fn main() { println!("NM={}", foo_nm()); }
""",
    "c5_ext.rs": """\
extern "C" { fn abs(x: i32) -> i32; }
fn main() { println!("ABS={}", unsafe { abs(-3) }); }
""",
    "c6_forbid_ext.rs": """\
#![forbid(unsafe_code)]
unsafe extern "C" { safe fn abs(x: i32) -> i32; }
fn main() { println!("ABS={}", abs(-3)); }
""",
    # ---- Part D --------------------------------------------------------
    "d1_e0453.rs": """\
#![forbid(unsafe_code)]
#[allow(unsafe_code)]
fn main() { let _ = unsafe { 1 }; }
""",
    "d2_exp_ok.rs": """\
#[expect(unsafe_code)]
fn main() { let v = 5u32; let p = &raw const v; let x = unsafe { *p }; let _ = x; println!("EXP_OK"); }
""",
    "d3_exp_unful.rs": """\
#[expect(dead_code)]
fn used() -> u32 { 5 }
fn main() { println!("EXP_UNFUL={}", used()); }
""",
    "d4_exp_cap.rs": """\
#[expect(dead_code)]
fn used() -> u32 { 5 }
fn main() { println!("EXP_CAP={}", used()); }
""",
    # ---- Part E (extended discriminators) ------------------------------
    "e_deny_in_forbid.rs": """\
#![forbid(unsafe_code)]
#[deny(unsafe_code)]
fn main() { let _ = unsafe { 1 }; }
""",
    "e_expect_in_forbid.rs": """\
#![forbid(unsafe_code)]
#[expect(unsafe_code)]
fn main() { let _ = unsafe { 1 }; }
""",
    "e_passthrough.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("PASS={}", up_unsafe_mac::foreign_passthrough!(unsafe { 111u32 })); }
""",
    "e_local_wraps_foreign.rs": """\
#![forbid(unsafe_code)]
macro_rules! local_wrap { () => { up_unsafe_mac::foreign_unsafe_expr!() }; }
fn main() { println!("WRAP={}", local_wrap!()); }
""",
    "e_foreign_calls_local.rs": """\
#![forbid(unsafe_code)]
macro_rules! loc_u { () => { unsafe { 112u32 } }; }
fn main() { println!("CALL_LOCAL={}", up_unsafe_mac::foreign_call_local!(loc_u)); }
""",
    "e_pm_input_span.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("PM_INPUT={}", up_unsafe_pm::pm_input_span!(here)); }
""",
    "e_ed2021_ffi_in_2024.rs": """\
#![forbid(unsafe_code)]
up_unsafe_mac::foreign_ed2021_ffi_items!();
fn main() { println!("FFI={} {}", up_exported_symbol(), foreign_abs(-5)); }
""",
    "e_expect_noop_block.rs": """\
#[expect(unsafe_code)]
fn main() { let x = unsafe { 5u32 }; let _ = x; println!("EXP_NOOP"); }
""",
    "e_expect_foreign.rs": """\
#[expect(unsafe_code)]
fn main() { println!("EXP_FOREIGN={}", up_unsafe_mac::foreign_unsafe_expr!()); }
""",
    "e_pm_attr_derive.rs": """\
#![forbid(unsafe_code)]
#[up_unsafe_pm::pm_attr_inject]
fn anchor() {}
#[derive(up_unsafe_pm::PmDeriveInject)]
struct Marker;
fn main() {
    anchor();
    let _ = Marker;
    println!("PM_ATTR_DERIVE={} {}", injected_by_attr(), injected_by_derive());
}
""",
    "e_group_forbid.rs": """\
#![forbid(unused)]
#[allow(unused_variables)]
fn main() { let x = 1; println!("GROUP_FCW"); }
""",
    "e_crate_allow.rs": """\
#![allow(unsafe_code)]
fn main() { let x = unsafe { 42u32 }; println!("UNSAFE_RAN={}", x); }
""",
    "e_e0133.rs": """\
fn main() { let v = 5u32; let p = &raw const v; let x = *p; println!("E0133={}", x); }
""",
    "e_smut_allow_attr.rs": """\
#![allow(static_mut_refs)]
static mut G: u32 = 1;
fn main() { unsafe { let r = &mut G; *r += 1; println!("SMUT_ALLOW={}", *r); } }
""",
    "e_mir_foreign_raw.rs": """\
#![forbid(unsafe_code)]
pub fn read_through_foreign_macro(x: &u32) -> u32 {
    let p = x as *const u32;
    up_unsafe_mac::foreign_read_raw!(p)
}
fn main() { println!("MIR_FOREIGN={}", read_through_foreign_macro(&21)); }
""",
    "e_mir_local_raw.rs": """\
#![forbid(unsafe_code)]
pub fn read_through_local_block(x: &u32) -> u32 {
    let p = x as *const u32;
    unsafe { *p }
}
fn main() { println!("MIR_LOCAL={}", read_through_local_block(&22)); }
""",
    "e_mir_no_op.rs": """\
#![forbid(unsafe_code)]
pub fn unsafe_block_without_unsafe_operation() -> u32 {
    unsafe { 42u32 }
}
fn main() { println!("MIR_NOOP={}", unsafe_block_without_unsafe_operation()); }
""",
    # ---- cargo dependency cases ---------------------------------------
    "cargo/forbid_dep/Cargo.toml": """\
[package]
name = "forbid_dep"
version = "0.1.0"
edition = "2021"
""",
    "cargo/forbid_dep/src/lib.rs": """\
#![forbid(unsafe_code)]
pub fn peek(v: &u32) -> u32 { unsafe { *(v as *const u32) } }
""",
    "cargo/app/src/main.rs": """\
#![forbid(unsafe_code)]
fn main() { println!("DEP_PEEK={}", forbid_dep::peek(&11)); }
""",
}

UNSAFE_BLOCK = "usage of an `unsafe` block"
E0453_ALLOW = "error[E0453]: allow(unsafe_code) incompatible with previous forbid"


def case(source, args=(), edition="2021", ok=True, stderr=(), not_stderr=(),
         stdout=None, externs=(), stderr_empty=False, mir=None, note="", no_errors=False):
    return {
        "source": source, "args": list(args), "edition": edition,
        "externs": list(externs), "mir": mir, "note": note,
        "expect": {
            "compile_ok": ok, "stderr_contains": list(stderr),
            "stderr_not_contains": list(not_stderr), "stderr_empty": stderr_empty,
            "no_error_diagnostics": no_errors, "stdout": stdout,
        },
    }


MAC = ("up_unsafe_mac",)
PM = ("up_unsafe_pm",)

CASES: dict[str, dict[str, dict]] = {
    "part_a_forbid_vs_cap_lints": {
        "default_forbid_rejects": case(
            "a_forbid.rs", ok=False, stderr=["error: " + UNSAFE_BLOCK, "#![forbid(unsafe_code)]"]),
        "cap_lints_allow_bypasses_forbid": case(
            "a_forbid.rs", ["--cap-lints", "allow"], stderr_empty=True, stdout="UNSAFE_RAN=42"),
        "cap_lints_warn_downgrades_forbid": case(
            "a_forbid.rs", ["--cap-lints", "warn"], stderr=["warning: " + UNSAFE_BLOCK],
            no_errors=True, stdout="UNSAFE_RAN=42"),
        "cap_lints_allow_plus_cli_F_unsafe_code": case(
            "a_plain.rs", ["--cap-lints", "allow", "-F", "unsafe_code"],
            stderr_empty=True, stdout="UNSAFE_RAN=42",
            note="Forbid comes only from the command line; cap flag first."),
        "cli_F_unsafe_code_plus_cap_lints_allow": case(
            "a_plain.rs", ["-F", "unsafe_code", "--cap-lints", "allow"],
            stderr_empty=True, stdout="UNSAFE_RAN=42",
            note="Forbid comes only from the command line; cap flag last."),
    },
    "part_b_foreign_macro_and_proc_macro_bypass": {
        "local_macro_rules_unsafe_caught_by_forbid": case(
            "b0_local_mac.rs", ok=False, stderr=["error: " + UNSAFE_BLOCK, "in this macro invocation"]),
        "foreign_macro_rules_unsafe_in_forbid_crate": case(
            "b1_fmac.rs", externs=MAC, stderr_empty=True, stdout="FMAC=101"),
        "foreign_macro_rules_allow_unsafe_in_forbid_crate": case(
            "b2_fmac_allow.rs", externs=MAC, ok=False,
            stderr=[E0453_ALLOW, "this error originates in the macro `up_unsafe_mac::foreign_allow_unsafe_expr`"],
            not_stderr=[UNSAFE_BLOCK]),
        "proc_macro_call_site_unsafe_in_forbid_crate": case(
            "b3_pm_call.rs", externs=PM, stderr_empty=True, stdout="PM_CALL=201"),
        "proc_macro_mixed_site_unsafe_in_forbid_crate": case(
            "b4_pm_mixed.rs", externs=PM, stderr_empty=True, stdout="PM_MIXED=202"),
        "proc_macro_def_site_unsafe_in_forbid_crate": case(
            "b5_pm_def.rs", externs=PM, stderr_empty=True, stdout="PM_DEF=203",
            note="needs_def_site"),
    },
    "part_c_edition2024_unsafe_hardening": {
        "unsafe_op_in_unsafe_fn_ed2021": case(
            "c1_uop.rs", edition="2021", stderr_empty=True, stdout="UOP=9"),
        "unsafe_op_in_unsafe_fn_ed2024": case(
            "c1_uop.rs", edition="2024",
            stderr=["warning[E0133]: dereference of raw pointer is unsafe and requires unsafe block"],
            no_errors=True, stdout="UOP=9"),
        "static_mut_ref_ed2021": case(
            "c2_smut.rs", edition="2021",
            stderr=["warning: creating a mutable reference to mutable static",
                    "`#[warn(static_mut_refs)]`"],
            no_errors=True, stdout="SMUT=2"),
        "static_mut_ref_ed2024": case(
            "c2_smut.rs", edition="2024", ok=False,
            stderr=["error: creating a mutable reference to mutable static",
                    "`#[deny(static_mut_refs)]`"]),
        "raw_mut_static_ed2024": case(
            "c2_raw.rs", edition="2024", stderr_empty=True, stdout="RAW=2"),
        "bare_no_mangle_ed2021": case(
            "c3_nm.rs", edition="2021", stderr_empty=True, stdout="NM=7"),
        "bare_no_mangle_ed2024_rejected": case(
            "c3_nm.rs", edition="2024", ok=False,
            stderr=["error: unsafe attribute used without unsafe"]),
        "forbid_unsafe_code_rejects_unsafe_no_mangle": case(
            "c4_forbid_nm.rs", edition="2024", ok=False,
            stderr=["`no_mangle`", "#![forbid(unsafe_code)]"],
            not_stderr=["unsafe attribute used without unsafe"],
            note="The first line of this unsafe_code diagnostic is worded differently across releases."),
        "bare_extern_c_ed2024_rejected": case(
            "c5_ext.rs", edition="2024", ok=False, stderr=["error: extern blocks must be unsafe"]),
        "forbid_unsafe_code_rejects_unsafe_extern_c": case(
            "c6_forbid_ext.rs", edition="2024", ok=False,
            stderr=["error: usage of an `unsafe extern` block", "#![forbid(unsafe_code)]"]),
    },
    "part_d_expect_and_forbid_override": {
        "allow_under_forbid_rejected_e0453": case(
            "d1_e0453.rs", ok=False, stderr=[E0453_ALLOW, "error: " + UNSAFE_BLOCK]),
        "expect_fulfilled_clean": case(
            "d2_exp_ok.rs", stderr_empty=True, stdout="EXP_OK"),
        "expect_unfulfilled_warns": case(
            "d3_exp_unful.rs",
            stderr=["warning: this lint expectation is unfulfilled",
                    "`#[warn(unfulfilled_lint_expectations)]` on by default"],
            stdout="EXP_UNFUL=5"),
        "expect_unfulfilled_silenced_by_cap_lints_allow": case(
            "d4_exp_cap.rs", ["--cap-lints", "allow"], stderr_empty=True, stdout="EXP_CAP=5"),
    },
    "part_e_extended_discriminators": {
        "cli_F_alone_rejects": case(
            "a_plain.rs", ["-F", "unsafe_code"], ok=False,
            stderr=["error: " + UNSAFE_BLOCK, "requested on the command line with `-F unsafe-code`"]),
        "attr_forbid_plus_cli_F_plus_cap_lints_allow": case(
            "a_forbid.rs", ["-F", "unsafe_code", "--cap-lints", "allow"],
            stderr_empty=True, stdout="UNSAFE_RAN=42"),
        "cap_lints_allow_suppresses_e0453": case(
            "d1_e0453.rs", ["--cap-lints", "allow"], stderr_empty=True),
        "force_warn_survives_cap_lints_allow": case(
            "a_plain.rs", ["--force-warn", "unsafe_code", "--cap-lints", "allow"],
            stderr=["warning: " + UNSAFE_BLOCK,
                    "requested on the command line with `--force-warn unsafe-code`"],
            no_errors=True, stdout="UNSAFE_RAN=42"),
        "cap_lints_repeated_allow_then_forbid": case(
            "a_forbid.rs", ["--cap-lints", "allow", "--cap-lints", "forbid"],
            stderr_empty=True, stdout="UNSAFE_RAN=42",
            note="First --cap-lints occurrence is the one that is read."),
        "cap_lints_repeated_forbid_then_allow": case(
            "a_forbid.rs", ["--cap-lints", "forbid", "--cap-lints", "allow"], ok=False,
            stderr=["error: " + UNSAFE_BLOCK]),
        "cap_lints_deny_keeps_forbid_an_error": case(
            "a_forbid.rs", ["--cap-lints", "deny"], ok=False, stderr=["error: " + UNSAFE_BLOCK]),
        "cli_F_then_cli_A_stays_forbid": case(
            "a_plain.rs", ["-F", "unsafe_code", "-A", "unsafe_code"], ok=False,
            stderr=["error: " + UNSAFE_BLOCK]),
        "cap_lints_deny_makes_forbid_overridable": case(
            "d1_e0453.rs", ["--cap-lints", "deny"], not_stderr=["E0453", UNSAFE_BLOCK], no_errors=True,
            note="Under a deny cap the revealed outer level is deny, so the inner allow is accepted."),
        "cap_lints_rejects_expect_as_a_level": case(
            "a_forbid.rs", ["--cap-lints", "expect"], ok=False,
            stderr=["error: unknown lint level: `expect`"]),
        "force_warn_flag_downgrades_attribute_forbid": case(
            "a_forbid.rs", ["--force-warn", "unsafe_code"],
            stderr=["warning: " + UNSAFE_BLOCK,
                    "requested on the command line with `--force-warn unsafe-code`"],
            no_errors=True, stdout="UNSAFE_RAN=42"),
        "cli_F_then_crate_allow_attribute_is_e0453": case(
            "e_crate_allow.rs", ["-F", "unsafe_code"], ok=False,
            stderr=[E0453_ALLOW, "`forbid` lint level was set on command line"]),
        "forbid_of_lint_group_is_overridable_with_future_compat_warning": case(
            "e_group_forbid.rs",
            stderr=["warning: allow(unused_variables) incompatible with previous forbid",
                    "forbidden_lint_groups"],
            not_stderr=["unused variable"], no_errors=True, stdout="GROUP_FCW",
            note="Concerns a lint group; unsafe_code itself is not reached through this path."),
        "deny_inside_forbid_is_not_e0453": case(
            "e_deny_in_forbid.rs", ok=False, stderr=["error: " + UNSAFE_BLOCK],
            not_stderr=["E0453"]),
        "expect_inside_forbid_is_e0453": case(
            "e_expect_in_forbid.rs", ok=False,
            stderr=["error[E0453]: expect(unsafe_code) incompatible with previous forbid"]),
        "foreign_passthrough_of_local_unsafe_tokens_is_caught": case(
            "e_passthrough.rs", externs=MAC, ok=False, stderr=["error: " + UNSAFE_BLOCK]),
        "local_macro_wrapping_foreign_macro_bypasses": case(
            "e_local_wraps_foreign.rs", externs=MAC, stderr_empty=True, stdout="WRAP=101"),
        "foreign_macro_invoking_local_macro_is_caught": case(
            "e_foreign_calls_local.rs", externs=MAC, ok=False, stderr=["error: " + UNSAFE_BLOCK]),
        "proc_macro_reusing_input_span_is_caught": case(
            "e_pm_input_span.rs", externs=PM, ok=False, stderr=["error: " + UNSAFE_BLOCK]),
        "ed2021_foreign_macro_ffi_items_in_ed2024_forbid_crate": case(
            "e_ed2021_ffi_in_2024.rs", edition="2024", externs=MAC,
            stderr_empty=True, stdout="FFI=301 5",
            note="Bare #[no_mangle] and bare extern \"C\" arrive with Edition 2021 spans."),
        "static_mut_ref_ed2024_under_cap_lints_allow": case(
            "c2_smut.rs", ["--cap-lints", "allow"], edition="2024",
            stderr_empty=True, stdout="SMUT=2"),
        "static_mut_ref_ed2024_under_allow_attribute": case(
            "e_smut_allow_attr.rs", edition="2024", stderr_empty=True, stdout="SMUT_ALLOW=2"),
        "unsafe_op_in_unsafe_fn_ed2024_under_cap_lints_allow": case(
            "c1_uop.rs", ["--cap-lints", "allow"], edition="2024", stderr_empty=True, stdout="UOP=9"),
        "expect_unsafe_code_fulfilled_by_block_without_unsafe_operation": case(
            "e_expect_noop_block.rs", stderr=["warning: unnecessary `unsafe` block"],
            not_stderr=["this lint expectation is unfulfilled"], no_errors=True, stdout="EXP_NOOP"),
        "expect_unsafe_code_unfulfilled_when_only_site_is_foreign_macro": case(
            "e_expect_foreign.rs", externs=MAC,
            stderr=["warning: this lint expectation is unfulfilled"], no_errors=True,
            stdout="EXP_FOREIGN=101"),
        "attribute_and_derive_proc_macros_bypass_forbid": case(
            "e_pm_attr_derive.rs", externs=PM, stderr_empty=True, stdout="PM_ATTR_DERIVE=205 206"),
        "unsafe_operation_outside_unsafe_block_is_e0133_under_cap_lints_allow": case(
            "e_e0133.rs", ["--cap-lints", "allow"], ok=False,
            stderr=["error[E0133]: dereference of raw pointer is unsafe and requires unsafe"],
            note="The unsafety check in a safe context is a hard error, not a lint. The tail of the "
                 "message depends on whether unsafe_op_in_unsafe_fn is revealed as allow."),
        "mir_shows_raw_deref_from_foreign_macro_in_forbid_crate": case(
            "e_mir_foreign_raw.rs", externs=MAC, stderr_empty=True, stdout="MIR_FOREIGN=21",
            mir={"fn": "read_through_foreign_macro", "raw_deref": True}),
        "mir_shows_raw_deref_under_cap_lints_allow": case(
            "e_mir_local_raw.rs", ["--cap-lints", "allow"], stderr_empty=True,
            stdout="MIR_LOCAL=22", mir={"fn": "read_through_local_block", "raw_deref": True}),
        "mir_has_no_raw_deref_for_unsafe_block_without_unsafe_operation": case(
            "e_mir_no_op.rs", ["--cap-lints", "allow"], stderr_empty=True, stdout="MIR_NOOP=42",
            mir={"fn": "unsafe_block_without_unsafe_operation", "raw_deref": False}),
    },
}


# --------------------------------------------------------------------------
# Execution helpers
# --------------------------------------------------------------------------

class Scrubber:
    """Replace machine-specific absolute paths in captured text."""

    def __init__(self) -> None:
        self.pairs: list[tuple[str, str]] = []

    def add(self, path: str | None, token: str) -> None:
        if path:
            for candidate in {path, os.path.realpath(path)}:
                if candidate and candidate != "/":
                    self.pairs.append((candidate, token))
            self.pairs.sort(key=lambda pair: -len(pair[0]))

    def __call__(self, text: str) -> str:
        for path, token in self.pairs:
            text = text.replace(path, token)
        return text


def run(argv, cwd=None, env=None):
    try:
        proc = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True,
                              timeout=TIMEOUT_S, errors="replace")
        return proc.returncode, proc.stdout, proc.stderr
    except FileNotFoundError as exc:
        return 127, "", f"probe: cannot execute {argv[0]}: {exc}"
    except subprocess.TimeoutExpired:
        return 124, "", f"probe: timed out after {TIMEOUT_S}s"


def write_sources(root: Path) -> None:
    for name, text in SOURCES.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")


def raw_deref_lines(mir_text: str, fn_name: str) -> dict:
    """Find raw-pointer locals of `fn_name` and statements dereferencing them."""
    match = re.search(r"^fn " + re.escape(fn_name) + r"\(.*?^}", mir_text, re.S | re.M)
    if not match:
        return {"fn_found": False, "raw_pointer_locals": [], "deref_statements": [], "fn_mir": ""}
    body = match.group(0)
    raw_locals = []
    for line in body.splitlines():
        decl = re.match(r"\s*(?:debug \w+ => )?(?:let (?:mut )?)?(_\d+): (\*(?:const|mut) [^;]+);", line)
        if decl:
            raw_locals.append((decl.group(1), decl.group(2)))
    header = body.splitlines()[0]
    for arg, ty in re.findall(r"(_\d+): (\*(?:const|mut) [^,)]+)", header):
        raw_locals.append((arg, ty))
    derefs = []
    for line in body.splitlines():
        for local, _ in raw_locals:
            if re.search(r"\(\*" + re.escape(local) + r"\)", line):
                derefs.append(line.strip())
    return {
        "fn_found": True,
        "raw_pointer_locals": sorted({f"{name}: {ty}" for name, ty in raw_locals}),
        "deref_statements": sorted(set(derefs)),
        "fn_mir": body,
    }


def evaluate(expect: dict, observed: dict) -> list[str]:
    problems = []
    compile_ok = observed["compile_rc"] == 0
    if compile_ok != expect["compile_ok"]:
        problems.append(f"compile_ok expected {expect['compile_ok']} got {compile_ok}")
    stderr = observed["stderr"]
    for needle in expect["stderr_contains"]:
        if needle not in stderr:
            problems.append(f"stderr lacks {needle!r}")
    for needle in expect["stderr_not_contains"]:
        if needle in stderr:
            problems.append(f"stderr unexpectedly contains {needle!r}")
    if expect["stderr_empty"] and stderr.strip():
        problems.append("stderr expected empty")
    if expect["no_error_diagnostics"] and any(
            line.startswith(("error:", "error[")) for line in stderr.splitlines()):
        problems.append("stderr contains an error diagnostic")
    if expect["stdout"] is not None:
        if observed.get("run_rc") != 0:
            problems.append(f"run_rc expected 0 got {observed.get('run_rc')}")
        if observed.get("stdout") != expect["stdout"]:
            problems.append(f"stdout expected {expect['stdout']!r} got {observed.get('stdout')!r}")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", default="probe_results.json", help="JSON report path")
    parser.add_argument("--keep", default=None, help="use this directory instead of a deleted temp dir")
    args = parser.parse_args()

    rustc = os.environ.get("RUSTC", "rustc")
    cargo = os.environ.get("CARGO", "cargo")
    scrub = Scrubber()
    scrub.add(os.path.expanduser("~"), "$HOME")

    rc, version_text, err = run([rustc, "-vV"])
    if rc != 0:
        print(f"cannot run {rustc} -vV: {err}", file=sys.stderr)
        return 2
    rc, sysroot, _ = run([rustc, "--print", "sysroot"])
    scrub.add(sysroot.strip() if rc == 0 else None, "$SYSROOT")

    report: dict = {
        "schema": SCHEMA,
        "observed_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "toolchain": {"rustc_vV": version_text.strip()},
        "sources": SOURCES,
        "upstream_builds": {},
        "cases": {},
        "cargo_cases": {},
    }

    def with_tmp(tmp: Path) -> None:
        scrub.add(str(tmp), "$TMP")
        write_sources(tmp)
        out_dir = tmp / "out"
        out_dir.mkdir()

        # ---- upstream crates -------------------------------------------
        mac_argv = [rustc, "--edition", "2021", "--crate-type", "rlib", "--crate-name", "up_unsafe_mac",
                    str(tmp / "up_unsafe_mac.rs"), "--out-dir", str(out_dir)]
        rc_mac, _, err_mac = run(mac_argv)
        pm_base = [rustc, "--edition", "2021", "--crate-type", "proc-macro", "--crate-name", "up_unsafe_pm",
                   str(tmp / "up_unsafe_pm.rs"), "--out-dir", str(out_dir)]
        pm_argv = pm_base + ["--cfg", "probe_def_site"]
        rc_pm, _, err_pm = run(pm_argv)
        def_site = rc_pm == 0
        if not def_site:
            first_err = err_pm
            pm_argv = pm_base
            rc_pm, _, err_pm = run(pm_argv)
            err_pm = "first attempt with --cfg probe_def_site failed:\n" + first_err + "\nretry:\n" + err_pm
        report["upstream_builds"] = {
            "up_unsafe_mac": {"argv": [scrub(a) for a in mac_argv], "rc": rc_mac, "stderr": scrub(err_mac)},
            "up_unsafe_pm": {"argv": [scrub(a) for a in pm_argv], "rc": rc_pm, "stderr": scrub(err_pm),
                             "def_site_available": def_site},
        }
        externs = {}
        for name in ("up_unsafe_mac", "up_unsafe_pm"):
            found = sorted(out_dir.glob(f"lib{name}.*"))
            externs[name] = str(found[0]) if found else None

        # ---- rustc cases -----------------------------------------------
        for part, cases in CASES.items():
            report["cases"][part] = {}
            for name, spec in cases.items():
                entry: dict = {"source": spec["source"], "edition": spec["edition"],
                               "note": spec["note"], "expect": spec["expect"]}
                if spec["note"] == "needs_def_site" and not def_site:
                    entry.update(status="skipped", reason="Span::def_site() is unavailable on this toolchain")
                    report["cases"][part][name] = entry
                    continue
                if any(externs.get(e) is None for e in spec["externs"]):
                    entry.update(status="skipped", reason="upstream crate failed to build")
                    report["cases"][part][name] = entry
                    continue
                exe = out_dir / f"{part[:6]}_{name}"
                argv = [rustc, "--edition", spec["edition"], str(tmp / spec["source"]),
                        "--crate-name", "probe_case", "-o", str(exe)] + spec["args"]
                for ext in spec["externs"]:
                    argv += ["--extern", f"{ext}={externs[ext]}"]
                rc_c, _, err_c = run(argv)
                observed = {"argv": [scrub(a) for a in argv], "compile_rc": rc_c, "stderr": scrub(err_c)}
                if rc_c == 0:
                    rc_r, out_r, _ = run([str(exe)])
                    observed.update(run_rc=rc_r, stdout=out_r.strip())
                problems = evaluate(spec["expect"], observed)
                if spec["mir"] is not None and rc_c == 0:
                    mir_path = out_dir / f"{name}.mir"
                    mir_argv = [a for a in argv]
                    mir_argv[mir_argv.index("-o") + 1] = str(mir_path)
                    mir_argv += ["--emit=mir"]
                    rc_m, _, err_m = run(mir_argv)
                    info = {"argv": [scrub(a) for a in mir_argv], "rc": rc_m, "stderr": scrub(err_m)}
                    if rc_m == 0 and mir_path.exists():
                        info.update(raw_deref_lines(mir_path.read_text(encoding="utf-8", errors="replace"),
                                                    spec["mir"]["fn"]))
                        info["fn_mir"] = scrub(info["fn_mir"])
                        has = bool(info["deref_statements"])
                        if not info["fn_found"]:
                            problems.append("MIR function not found")
                        elif has != spec["mir"]["raw_deref"]:
                            problems.append(f"raw deref expected {spec['mir']['raw_deref']} got {has}")
                    else:
                        problems.append("MIR emission failed")
                    info["expect"] = spec["mir"]
                    observed["mir"] = info
                entry.update(observed)
                entry["status"] = "pass" if not problems else "fail"
                entry["problems"] = problems
                report["cases"][part][name] = entry

        # ---- lint table: default level and group membership -------------
        rc_h, help_out, help_err = run([rustc, "-W", "help"])
        help_lines = (help_out + help_err).splitlines()
        group_start = next((i for i, line in enumerate(help_lines)
                            if line.startswith("Lint groups provided by rustc")), len(help_lines))
        table_line = next((line.strip() for line in help_lines[:group_start]
                           if re.match(r"\s*unsafe-code\s", line)), "")
        groups = [line.split()[0] for line in help_lines[group_start:]
                  if re.search(r"\bunsafe-code\b", line) and line.split()]
        problems = []
        if rc_h != 0:
            problems.append("rustc -W help failed")
        if not re.match(r"unsafe-code\s+allow\s", table_line):
            problems.append("unsafe-code is not listed with default level allow")
        if groups:
            problems.append(f"unsafe-code is a member of lint groups {groups}")
        report["cases"]["part_e_extended_discriminators"][
            "unsafe_code_is_allow_by_default_and_in_no_lint_group"] = {
            "argv": ["rustc", "-W", "help"], "compile_rc": rc_h, "lint_table_line": table_line,
            "lint_groups_containing_unsafe_code": groups,
            "expect": {"default_level": "allow", "lint_groups_containing_unsafe_code": []},
            "status": "pass" if not problems else "fail", "problems": problems,
        }

        # ---- cargo dependency cases ------------------------------------
        git = shutil.which("git")
        rc_cv, cargo_v, _ = run([cargo, "-vV"])
        if rc_cv != 0 or git is None:
            reason = "cargo is unavailable" if rc_cv != 0 else "git is unavailable"
            for name in ("path_dependency_forbid_violation_fails_the_build",
                         "git_dependency_forbid_violation_is_capped_and_builds"):
                report["cargo_cases"][name] = {"status": "skipped", "reason": reason}
            return
        # The `os:` line describes the machine rather than the toolchain; leave it out.
        report["toolchain"]["cargo_vV"] = "\n".join(
            line for line in cargo_v.strip().splitlines() if not line.startswith("os:"))
        ws = tmp / "cargo"
        dep = ws / "forbid_dep"
        git_env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_SYSTEM=os.devnull)
        for git_args in (["init", "-q", "-b", "main"], ["add", "-A"],
                         ["-c", "user.name=probe", "-c", "user.email=probe@example.invalid",
                          "commit", "-q", "-m", "forbid_dep"]):
            run([git] + git_args, cwd=dep, env=git_env)
        cargo_env = dict(os.environ, CARGO_HOME=str(tmp / "cargo_home"), CARGO_TERM_COLOR="never",
                         RUSTC=shutil.which(rustc) or rustc)
        cargo_env.pop("RUSTFLAGS", None)
        cargo_env.pop("CARGO_ENCODED_RUSTFLAGS", None)
        variants = {
            "path_dependency_forbid_violation_fails_the_build": {
                "dep": 'forbid_dep = { path = "../forbid_dep" }',
                "expect": {"build_ok": False, "dep_rustc_has_cap_lints_allow": False,
                           "stderr_contains": ["error: " + UNSAFE_BLOCK]},
            },
            "git_dependency_forbid_violation_is_capped_and_builds": {
                "dep": 'forbid_dep = { git = "file://%s" }' % dep,
                "expect": {"build_ok": True, "dep_rustc_has_cap_lints_allow": True,
                           "stderr_contains": [], "stdout": "DEP_PEEK=11"},
            },
        }
        for name, variant in variants.items():
            app = ws / f"app_{name.split('_')[0]}"
            (app / "src").mkdir(parents=True)
            shutil.copy(ws / "app" / "src" / "main.rs", app / "src" / "main.rs")
            manifest = ("[package]\nname = \"app\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n"
                        "[dependencies]\n" + variant["dep"] + "\n")
            (app / "Cargo.toml").write_text(manifest, encoding="utf-8")
            target = tmp / f"target_{name.split('_')[0]}"
            argv = [cargo, "build", "-v", "--manifest-path", str(app / "Cargo.toml"),
                    "--target-dir", str(target)]
            rc_b, _, err_b = run(argv, env=cargo_env)
            dep_lines = [line.strip() for line in err_b.splitlines()
                         if "Running" in line and "--crate-name forbid_dep" in line]
            cap = any("--cap-lints allow" in line for line in dep_lines)
            observed = {
                "manifest": scrub(manifest), "argv": [scrub(a) for a in argv], "build_rc": rc_b,
                "dep_rustc_lines": [scrub(line) for line in dep_lines],
                "dep_rustc_has_cap_lints_allow": cap,
                "stderr": scrub(err_b),
            }
            problems = []
            expect = variant["expect"]
            if (rc_b == 0) != expect["build_ok"]:
                problems.append(f"build_ok expected {expect['build_ok']} got {rc_b == 0}")
            if not dep_lines:
                problems.append("no rustc invocation for forbid_dep found in cargo -v output")
            if cap != expect["dep_rustc_has_cap_lints_allow"]:
                problems.append(f"--cap-lints allow on dependency expected "
                                f"{expect['dep_rustc_has_cap_lints_allow']} got {cap}")
            for needle in expect["stderr_contains"]:
                if needle not in err_b:
                    problems.append(f"stderr lacks {needle!r}")
            if rc_b == 0:
                rc_r, out_r, _ = run([str(target / "debug" / "app")])
                observed.update(run_rc=rc_r, stdout=out_r.strip())
                if expect.get("stdout") is not None and out_r.strip() != expect["stdout"]:
                    problems.append(f"stdout expected {expect['stdout']!r} got {out_r.strip()!r}")
            observed["expect"] = expect
            observed["status"] = "pass" if not problems else "fail"
            observed["problems"] = problems
            report["cargo_cases"][name] = observed

    if args.keep:
        keep = Path(args.keep)
        keep.mkdir(parents=True, exist_ok=True)
        with_tmp(keep)
    else:
        with tempfile.TemporaryDirectory(prefix="forbid_probe_") as tmp:
            with_tmp(Path(tmp))

    entries = [entry for cases in report["cases"].values() for entry in cases.values()]
    entries += list(report["cargo_cases"].values())
    summary = {status: sum(1 for entry in entries if entry["status"] == status)
               for status in ("pass", "fail", "skipped")}
    summary["total"] = len(entries)
    summary["per_part"] = {
        part: {"total": len(cases), "pass": sum(1 for e in cases.values() if e["status"] == "pass")}
        for part, cases in report["cases"].items()
    }
    report["summary"] = summary

    Path(args.out).write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    for part, cases in list(report["cases"].items()) + [("cargo_cases", report["cargo_cases"])]:
        for name, entry in cases.items():
            line = f"{entry['status'].upper():7} {part}/{name}"
            if entry["status"] == "fail":
                line += "  <- " + "; ".join(entry["problems"])
            if entry["status"] == "skipped":
                line += "  <- " + entry["reason"]
            print(line)
    print(json.dumps({k: v for k, v in summary.items() if k != "per_part"}))
    return 0 if summary["fail"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
