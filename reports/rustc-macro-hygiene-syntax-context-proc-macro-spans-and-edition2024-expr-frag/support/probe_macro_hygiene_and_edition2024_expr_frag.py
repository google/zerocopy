#!/usr/bin/env python3
"""Live rustc verification probe for macro hygiene, SyntaxContext/Transparency,
proc-macro Span::{call_site, mixed_site, def_site}, and Edition 2024 :expr/:expr_2021.

Executes real compilations and binaries against the local rustc toolchain in an
isolated temporary directory and emits structured JSON with sanitized <tmp> paths.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _find_rustc() -> str:
    found = shutil.which("rustc")
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / "rustc"
    if candidate.exists():
        return str(candidate)
    raise FileNotFoundError("rustc not found on PATH or in ~/.cargo/bin")


def _sanitize(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir, "<tmp>")


def _run(cmd: list[str], tmpdir: str, cwd: str | None = None) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        cmd,
        cwd=cwd or tmpdir,
        capture_output=True,
        text=True,
        check=False,
    )
    return subprocess.CompletedProcess(
        args=proc.args,
        returncode=proc.returncode,
        stdout=_sanitize(proc.stdout, tmpdir),
        stderr=_sanitize(proc.stderr, tmpdir),
    )


def _compile_and_maybe_run(
    rustc: str,
    tmpdir: Path,
    name: str,
    code: str,
    edition: str,
    crate_type: str = "bin",
    extra_flags: list[str] | None = None,
    run_unpretty: bool = False,
) -> dict[str, Any]:
    src = tmpdir / f"{name}.rs"
    src.write_text(code, encoding="utf-8")
    out_bin = tmpdir / (f"lib{name}.rlib" if crate_type == "rlib" else f"lib{name}.so" if crate_type == "proc-macro" else name)
    cmd = [rustc, f"--edition={edition}", f"--crate-type={crate_type}", str(src), "-o", str(out_bin)]
    if extra_flags:
        cmd.extend(extra_flags)
    comp = _run(cmd, str(tmpdir))
    res: dict[str, Any] = {
        "edition": edition,
        "crate_type": crate_type,
        "compile_returncode": comp.returncode,
        "compile_stderr": comp.stderr.strip(),
    }
    if comp.returncode == 0 and crate_type == "bin":
        run_proc = _run([str(out_bin)], str(tmpdir))
        res["run_returncode"] = run_proc.returncode
        res["run_stdout"] = run_proc.stdout.strip()
        res["run_stderr"] = run_proc.stderr.strip()
    if run_unpretty:
        unp_cmd = [rustc, f"--edition={edition}", f"--crate-type={crate_type}", "-Zunpretty=expanded", str(src)]
        if extra_flags:
            unp_cmd.extend(extra_flags)
        unp = _run(unp_cmd, str(tmpdir))
        res["unpretty_expanded_rc"] = unp.returncode
        res["unpretty_expanded"] = unp.stdout.strip()
        if unp.returncode != 0:
            res["unpretty_expanded_stderr"] = unp.stderr.strip()
    return res


def probe_group_a(rustc: str) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="rustc_hygiene_a_") as td:
        tmp = Path(td)
        results: dict[str, Any] = {}

        code_expr_basic = """\
macro_rules! accept_expr {
    ($e:expr) => {
        $e
    };
}

fn main() {
    let a = accept_expr!(const { 1 + 2 });
    accept_expr!(_) = 99;
    println!("A={a}");
}
"""
        results["edition_2021_expr"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2021_expr", code_expr_basic, "2021"
        )
        results["edition_2024_expr"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2024_expr", code_expr_basic, "2024", run_unpretty=True
        )

        code_ed2021_paren = """\
macro_rules! accept_expr {
    ($e:expr) => {
        $e
    };
}

fn main() {
    let a = accept_expr!((const { 1 + 2 }));
    println!("A_PAREN={a}");
}
"""
        results["edition_2021_expr_parenthesized_subexpr"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2021_paren", code_ed2021_paren, "2021"
        )

        code_ed2024_let = """\
macro_rules! accept_expr {
    ($e:expr) => {
        $e
    };
}

fn main() {
    accept_expr!(let _ = 1);
}
"""
        results["edition_2024_expr_rejects_let"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2024_let", code_ed2024_let, "2024"
        )

        code_expr_2021_const = """\
macro_rules! accept_expr_2021 {
    ($e:expr_2021) => {
        $e
    };
}

fn main() {
    let _ = accept_expr_2021!(const { 1 + 2 });
}
"""
        results["edition_2024_expr_2021_const_block"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2024_expr2021_const", code_expr_2021_const, "2024"
        )

        code_expr_2021_underscore = """\
macro_rules! accept_expr_2021 {
    ($e:expr_2021) => {
        $e
    };
}

fn main() {
    accept_expr_2021!(_) = 99;
}
"""
        results["edition_2024_expr_2021_underscore"] = _compile_and_maybe_run(
            rustc, tmp, "a_ed2024_expr2021_under", code_expr_2021_underscore, "2024"
        )

        # Cross-edition test 1: macro defined in Edition 2021, invoked in Edition 2024.
        lib2021 = _compile_and_maybe_run(
            rustc,
            tmp,
            "mac_ed2021",
            "#[macro_export] macro_rules! m2021 { ($e:expr) => { $e }; }\n",
            "2021",
            crate_type="rlib",
        )
        assert lib2021["compile_returncode"] == 0, lib2021
        results["cross_edition_def2021_call2024"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "caller_2024_of_2021",
            """\
extern crate mac_ed2021;
fn main() {
    let _ = mac_ed2021::m2021!(const { 1 + 2 });
    mac_ed2021::m2021!(_) = 99;
}
""",
            "2024",
            extra_flags=["--extern", f"mac_ed2021={tmp / 'libmac_ed2021.rlib'}"],
        )

        # Cross-edition test 2: macro defined in Edition 2024, invoked in Edition 2021.
        lib2024 = _compile_and_maybe_run(
            rustc,
            tmp,
            "mac_ed2024",
            "#[macro_export] macro_rules! m2024 { ($e:expr) => { $e }; }\n",
            "2024",
            crate_type="rlib",
        )
        assert lib2024["compile_returncode"] == 0, lib2024
        results["cross_edition_def2024_call2021"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "caller_2021_of_2024",
            """\
extern crate mac_ed2024;
fn main() {
    let x = mac_ed2024::m2024!(const { 1 + 2 });
    mac_ed2024::m2024!(_) = 99;
    println!("X21={x}");
}
""",
            "2021",
            extra_flags=["--extern", f"mac_ed2024={tmp / 'libmac_ed2024.rlib'}"],
        )
        return results


def probe_group_b(rustc: str) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="rustc_hygiene_b_") as td:
        tmp = Path(td)
        results: dict[str, Any] = {}

        code_pos = """\
mod inner {
    pub fn helper() -> u32 { 77 }

    #[macro_export]
    macro_rules! hygiene_probe {
        ($v:expr, $leaked_name:ident) => {{
            let x = 1u32;
            struct LeakedItem(u32);
            let item = LeakedItem($v);
            let called = $crate::inner::helper();
            (x, item.0, called)
        }};
    }

    #[macro_export]
    macro_rules! leak_struct {
        () => {
            struct LeakedTop(pub u32);
        };
    }

    #[macro_export]
    macro_rules! call_method_on {
        ($obj:expr) => {
            ($obj.get_val(), $obj.trait_val(), $obj.0)
        };
    }
}

fn helper() -> u32 { 999 }

trait Extrinsic {
    fn trait_val(&self) -> u32;
}

struct Holder(u32);
impl Holder {
    fn get_val(&self) -> u32 { self.0 + 5 }
}
impl Extrinsic for Holder {
    fn trait_val(&self) -> u32 { self.0 + 10 }
}

leak_struct!();

fn main() {
    let x = 2u32;
    let (macro_x, item_v, dc_v) = hygiene_probe!(x, unused_ident);
    let caller_x = x;
    let leaked = LeakedTop(33);
    let h = Holder(10);
    let (meth, tmeth, field_v) = call_method_on!(h);
    println!(
        "OUT=({macro_x},{caller_x}) ITEM={item_v} DC={dc_v} HELPER_SHADOW={} LEAKED={} METH={meth} TMETH={tmeth} FIELD={field_v}",
        helper(),
        leaked.0
    );
}
"""
        for ed in ("2021", "2024"):
            results[f"edition_{ed}"] = _compile_and_maybe_run(
                rustc, tmp, f"b_pos_{ed}", code_pos, ed, run_unpretty=True
            )

        # Cross-crate $crate shadowing + private-item visibility boundary
        dep_code = """\
pub mod inner {
    pub fn dep_fn() -> u32 { 55 }
    fn priv_fn() -> u32 { 66 }
}

#[macro_export]
macro_rules! call_dep_pub {
    () => {
        $crate::inner::dep_fn()
    };
}

#[macro_export]
macro_rules! call_dep_priv {
    () => {
        $crate::inner::priv_fn()
    };
}
"""
        dep_res = _compile_and_maybe_run(
            rustc, tmp, "dep_hygiene", dep_code, "2024", crate_type="rlib"
        )
        assert dep_res["compile_returncode"] == 0, dep_res

        cross_pos = """\
extern crate dep_hygiene as dep_alias;

mod dep_hygiene {
    pub mod inner {
        pub fn dep_fn() -> u32 { 888 }
    }
}

fn main() {
    let ext_dc = dep_alias::call_dep_pub!();
    let shadow = dep_hygiene::inner::dep_fn();
    println!("EXT_DC={ext_dc} SHADOW_MOD={shadow}");
}
"""
        results["cross_crate_dollar_crate_vs_shadow"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "b_cross_pos",
            cross_pos,
            "2024",
            extra_flags=["--extern", f"dep_hygiene={tmp / 'libdep_hygiene.rlib'}"],
        )

        cross_priv = """\
extern crate dep_hygiene as dep_alias;
fn main() {
    let _ = dep_alias::call_dep_priv!();
}
"""
        results["negative_dollar_crate_respects_visibility"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "b_cross_priv",
            cross_priv,
            "2024",
            extra_flags=["--extern", f"dep_hygiene={tmp / 'libdep_hygiene.rlib'}"],
        )

        results["negative_macro_rules_local_does_not_leak"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "b_neg_local_leak",
            """\
macro_rules! def_secret { () => { let secret = 1u32; }; }
fn main() {
    def_secret!();
    let _ = secret;
}
""",
            "2024",
        )

        results["negative_macro_rules_cannot_capture_caller_local"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "b_neg_capture",
            """\
macro_rules! read_caller { () => { caller_only }; }
fn main() {
    let caller_only = 2u32;
    let _ = read_caller!();
}
""",
            "2024",
        )

        results["negative_macro_rules_label_isolation"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "b_neg_label",
            """\
macro_rules! jump_blk { () => { break 'blk 1u32; }; }
fn main() {
    let _v: u32 = 'blk: {
        jump_blk!();
        2u32
    };
}
""",
            "2024",
        )
        return results


def probe_group_c_and_d(rustc: str) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="rustc_hygiene_cd_") as td:
        tmp = Path(td)
        pm_code = """\
#![feature(proc_macro_def_site)]
extern crate proc_macro;
use proc_macro::{Ident, Span, TokenStream};

fn parse_with_span(src: &str, span: Span) -> TokenStream {
    let raw: TokenStream = src.parse().unwrap();
    fn remap(ts: TokenStream, span: Span) -> TokenStream {
        ts.into_iter()
            .map(|mut tt| {
                match &mut tt {
                    proc_macro::TokenTree::Group(g) => {
                        let inner = remap(g.stream(), span);
                        let mut ng = proc_macro::Group::new(g.delimiter(), inner);
                        ng.set_span(span);
                        proc_macro::TokenTree::Group(ng)
                    }
                    _ => {
                        tt.set_span(span);
                        tt
                    }
                }
            })
            .collect()
    }
    remap(raw, span)
}

#[proc_macro]
pub fn read_x_call_site(_input: TokenStream) -> TokenStream {
    TokenStream::from(proc_macro::TokenTree::Ident(Ident::new("x", Span::call_site())))
}

#[proc_macro]
pub fn define_y_call_site(_input: TokenStream) -> TokenStream {
    parse_with_span("let y = 77u32;", Span::call_site())
}

#[proc_macro]
pub fn shadow_x_mixed_site(_input: TokenStream) -> TokenStream {
    parse_with_span("{ let x = 10u32; x }", Span::mixed_site())
}

#[proc_macro]
pub fn read_x_mixed_site(_input: TokenStream) -> TokenStream {
    TokenStream::from(proc_macro::TokenTree::Ident(Ident::new("x", Span::mixed_site())))
}

#[proc_macro]
pub fn define_z_mixed_site(_input: TokenStream) -> TokenStream {
    parse_with_span("let z = 11u32;", Span::mixed_site())
}

#[proc_macro]
pub fn leak_item_mixed_site(_input: TokenStream) -> TokenStream {
    parse_with_span("struct MixedLeaked(pub u32);", Span::mixed_site())
}

#[proc_macro]
pub fn call_method_mixed_site(input: TokenStream) -> TokenStream {
    let mut out = input;
    out.extend(parse_with_span(".get_val()", Span::mixed_site()));
    out
}

#[proc_macro]
pub fn resolved_at_mixed_from_call(_input: TokenStream) -> TokenStream {
    let sp = Span::call_site().resolved_at(Span::mixed_site());
    parse_with_span("{ let x = 19u32; x }", sp)
}

#[proc_macro]
pub fn def_site_internal_item(_input: TokenStream) -> TokenStream {
    parse_with_span("{ struct DefInner(pub u32); DefInner(88).0 }", Span::def_site())
}

#[proc_macro]
pub fn def_site_item_leak_probe(_input: TokenStream) -> TokenStream {
    parse_with_span("struct DefSiteOnly(pub u32);", Span::def_site())
}

#[proc_macro]
pub fn def_site_method_probe(input: TokenStream) -> TokenStream {
    let mut out = input;
    out.extend(parse_with_span(".get_val()", Span::def_site()));
    out
}
"""
        pm_build = _compile_and_maybe_run(
            rustc, tmp, "hygiene_pm", pm_code, "2024", crate_type="proc-macro"
        )
        assert pm_build["compile_returncode"] == 0, pm_build
        pm_extern = ["--extern", f"hygiene_pm={tmp / 'libhygiene_pm.so'}"]

        c_res: dict[str, Any] = {"proc_macro_build": pm_build}

        c_pos_code = """\
extern crate hygiene_pm;

struct Holder(u32);
impl Holder {
    fn get_val(&self) -> u32 { self.0 + 5 }
}

hygiene_pm::leak_item_mixed_site!();

fn main() {
    let x = 42u32;
    let cs = hygiene_pm::read_x_call_site!();
    hygiene_pm::define_y_call_site!();
    let ms = hygiene_pm::shadow_x_mixed_site!();
    let ms_res_at = hygiene_pm::resolved_at_mixed_from_call!();
    let ms_item = MixedLeaked(55).0;
    let h = Holder(10);
    let ms_meth = hygiene_pm::call_method_mixed_site!(h);
    let ds_internal = hygiene_pm::def_site_internal_item!();
    println!(
        "CS={cs} CS_DEF={y} MS={ms} MS_RES_AT={ms_res_at} MS_ITEM={ms_item} MS_METH={ms_meth} DS_INTERNAL={ds_internal} CALLER_X={x}"
    );
}
"""
        c_res["positive_call_site_mixed_site_def_site_internal"] = _compile_and_maybe_run(
            rustc, tmp, "c_pos", c_pos_code, "2024", extra_flags=pm_extern, run_unpretty=True
        )

        c_res["negative_mixed_site_cannot_capture_caller_x"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "c_neg_capture",
            """\
extern crate hygiene_pm;
fn main() {
    let x = 42u32;
    let _ = hygiene_pm::read_x_mixed_site!();
}
""",
            "2024",
            extra_flags=pm_extern,
        )

        c_res["negative_mixed_site_local_does_not_leak"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "c_neg_leak",
            """\
extern crate hygiene_pm;
fn main() {
    hygiene_pm::define_z_mixed_site!();
    let _ = z;
}
""",
            "2024",
            extra_flags=pm_extern,
        )

        c_res["negative_def_site_item_isolated"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "c_neg_def_item",
            """\
extern crate hygiene_pm;
hygiene_pm::def_site_item_leak_probe!();
fn main() {
    let _ = DefSiteOnly(1);
}
""",
            "2024",
            extra_flags=pm_extern,
        )

        c_res["negative_def_site_method_isolated"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "c_neg_def_meth",
            """\
extern crate hygiene_pm;
struct Holder(u32);
impl Holder {
    fn get_val(&self) -> u32 { self.0 + 5 }
}
fn main() {
    let h = Holder(10);
    let _ = hygiene_pm::def_site_method_probe!(h);
}
""",
            "2024",
            extra_flags=pm_extern,
        )

        c_res["positive_def_site_pub_method_accessible"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "c_pos_def_pub_meth",
            """\
extern crate hygiene_pm;
pub struct PubHolder(pub u32);
impl PubHolder {
    pub fn get_val(&self) -> u32 { self.0 + 5 }
}
fn main() {
    let h = PubHolder(10);
    let v = hygiene_pm::def_site_method_probe!(h);
    println!("DS_PUB_METH={v}");
}
""",
            "2024",
            extra_flags=pm_extern,
        )

        # Group D: Macros 2.0 (`#![feature(decl_macro)]`) Opaque transparency
        d_res: dict[str, Any] = {}
        d_res["macros_2_0_opaque_item_isolated"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "d_decl_macro_item_neg",
            """\
#![feature(decl_macro)]

mod defs {
    pub macro decl_leak_struct() {
        pub struct OpaqueStruct(pub u32);
    }
}

defs::decl_leak_struct!();

fn main() {
    let _ = OpaqueStruct(1);
}
""",
            "2024",
        )

        d_res["macros_2_0_opaque_method_privacy_at_def_site"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "d_decl_macro_meth_neg",
            """\
#![feature(decl_macro)]

mod defs {
    pub macro decl_call_priv($obj:expr) { $obj.priv_val() }
}

mod caller_priv {
    pub struct CallerHolder(pub u32);
    impl CallerHolder {
        fn priv_val(&self) -> u32 { self.0 + 6 }
    }
    pub fn run() -> u32 {
        let h = CallerHolder(10);
        super::defs::decl_call_priv!(h)
    }
}

fn main() {
    let _ = caller_priv::run();
}
""",
            "2024",
        )

        d_res["macros_2_0_opaque_def_site_and_pub_method"] = _compile_and_maybe_run(
            rustc,
            tmp,
            "d_decl_macro_pos",
            """\
#![feature(decl_macro)]

mod defs {
    pub struct DefHolder(pub u32);
    impl DefHolder {
        pub fn get_val(&self) -> u32 { self.0 + 5 }
    }
    pub fn helper() -> u32 { 321 }

    pub macro decl_use_def_site() {
        {
            let h = DefHolder(10);
            (h.get_val(), helper())
        }
    }

    pub macro decl_call_pub($obj:expr) {
        $obj.pub_val()
    }
}

mod caller_pub {
    pub struct CallerHolder(pub u32);
    impl CallerHolder {
        pub fn pub_val(&self) -> u32 { self.0 + 9 }
    }
    pub fn run() -> u32 {
        let h = CallerHolder(10);
        super::defs::decl_call_pub!(h)
    }
}

fn helper() -> u32 { 999 }

fn main() {
    let (a, b) = defs::decl_use_def_site!();
    let c = caller_pub::run();
    println!("DECL2_VAL={a} DECL2_HELPER={b} DECL2_PUB_METH={c}");
}
""",
            "2024",
        )

        return {"c": c_res, "d": d_res}


def run_all() -> dict[str, Any]:
    rustc = _find_rustc()
    ver = subprocess.run([rustc, "--version", "--verbose"], capture_output=True, text=True, check=True).stdout.strip()
    cd_res = probe_group_c_and_d(rustc)
    return {
        "rustc_version": ver,
        "experiments": {
            "a_edition_2021_vs_2024_expr_frag_specifier": probe_group_a(rustc),
            "b_macro_rules_semi_opaque_hygiene_and_dollar_crate": probe_group_b(rustc),
            "c_proc_macro_call_site_vs_mixed_site_vs_def_site": cd_res["c"],
            "d_macros_2_0_decl_macro_opaque": cd_res["d"],
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", type=Path, help="Optional output JSON path")
    args = parser.parse_args()
    data = run_all()
    payload = json.dumps(data, indent=2) + "\n"
    if args.json:
        args.json.write_text(payload, encoding="utf-8")
    else:
        sys.stdout.write(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
