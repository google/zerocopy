#!/usr/bin/env python3
"""Empirical rustc probe for macro hygiene, Transparency, proc_macro spans,
FnDef type-privacy vs. name-resolution hygiene, Edition 2021/2024 expr
fragments, default recursion_limit accounting, and host-impure proc_macro
object-file reproducibility.

Produces a clean, path-scrubbed JSON report with exact rustc exit codes,
diagnostics, runtime outputs, and SHA-256 object hashes.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def find_rustc() -> str:
    found = shutil.which("rustc")
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / "rustc"
    if candidate.is_file():
        return str(candidate)
    raise RuntimeError("rustc not found on PATH or in ~/.cargo/bin/rustc")


def scrub_text(text: str, workdir: Path) -> str:
    """Remove temporary workspace prefixes so outputs are reproducible and leak-free."""
    wd = str(workdir)
    out = text.replace(wd + os.sep, "<workdir>/").replace(wd, "<workdir>")
    # Also scrub resolved realpath if different (e.g., symlinked /tmp).
    wd_real = str(workdir.resolve())
    if wd_real != wd:
        out = out.replace(wd_real + os.sep, "<workdir>/").replace(wd_real, "<workdir>")
    return out


def run_cmd(
    cmd: list[str],
    workdir: Path,
    env: dict[str, str] | None = None,
    timeout: int = 60,
) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(workdir),
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )
    return {
        "rc": proc.returncode,
        "stdout": scrub_text(proc.stdout.strip(), workdir),
        "stderr": scrub_text(proc.stderr.strip(), workdir),
    }


def compile_and_maybe_run(
    rustc: str,
    workdir: Path,
    filename: str,
    source: str,
    extra_args: list[str] | None = None,
    run_bin: bool = True,
) -> dict[str, Any]:
    src_path = workdir / filename
    src_path.write_text(source, encoding="utf-8")
    stem = Path(filename).stem
    bin_path = workdir / f"bin_{stem}"
    cmd = [rustc, "--color=never", str(src_path), "-o", str(bin_path)]
    if extra_args:
        cmd.extend(extra_args)
    comp = run_cmd(cmd, workdir)
    res: dict[str, Any] = {
        "compile_rc": comp["rc"],
        "stderr_head": "\n".join(comp["stderr"].splitlines()[:18]),
    }
    if comp["rc"] == 0 and run_bin:
        run = run_cmd([str(bin_path)], workdir)
        res["run_rc"] = run["rc"]
        res["stdout"] = run["stdout"]
        if run["stderr"]:
            res["run_stderr"] = run["stderr"]
    return res


def sha256_file(path: Path) -> tuple[str, int]:
    data = path.read_bytes()
    return hashlib.sha256(data).hexdigest(), len(data)


def run_probe(rustc: str) -> dict[str, Any]:
    ver_proc = subprocess.run(
        [rustc, "--version", "--verbose"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=True,
    )
    rustc_version = ver_proc.stdout.strip()
    commit_match = re.search(r"^commit-hash:\s*([0-9a-f]{40})$", rustc_version, re.M)
    commit_hash = commit_match.group(1) if commit_match else "unknown"

    with tempfile.TemporaryDirectory(prefix="probe_macro_hygiene_") as td:
        workdir = Path(td)

        # ------------------------------------------------------------------
        # Part A: Three-tier hygiene matrix (macro_rules!, decl_macro, proc_macro)
        # ------------------------------------------------------------------
        part_a: dict[str, Any] = {}

        # A1: macro_rules! (SemiOpaque): local & label hygiene, call-site item resolution
        part_a["macro_rules_semi_opaque"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a1_macro_rules.rs",
            """
mod def_mod {
    #[allow(dead_code)]
    pub fn helper() -> u32 { 10 }

    #[macro_export]
    macro_rules! m_semi {
        ($v:expr) => {{
            let x: u32 = 7;
            let lbl_val: u32 = 'lbl: loop {
                break 'lbl 42u32;
            };
            (($v, x), helper(), lbl_val)
        }};
    }

    #[macro_export]
    macro_rules! m_label_bidir {
        ($e:expr) => {{
            #[allow(unreachable_code)]
            'lbl: loop {
                let _ = $e;
                break 'lbl 42u32;
            }
        }};
    }
}

fn helper() -> u32 { 999 }

fn main() {
    let x: u32 = 100;
    let ((caller_x, macro_x), item_val, inner_lbl) = 'lbl: loop {
        break 'lbl m_semi!(x);
    };
    let bidir_lbl: u32 = 'lbl: loop {
        let _ = m_label_bidir!(break 'lbl 99u32);
        break 'lbl 0u32;
    };
    println!(
        "LOCAL_HYG=({},{}) ITEM_CALLSITE={} LABEL_HYG={} LABEL_BIDIR={}",
        caller_x, macro_x, item_val, inner_lbl, bidir_lbl
    );
}
""",
        )

        # A2a: decl_macro (Opaque): local, label, and public def-site item resolution
        part_a["decl_macro_opaque_pub_defsite"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_pub.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    pub fn helper() -> u32 { 10 }
    pub macro m_opaque($v:expr) {{
        let x: u32 = 7;
        let lbl_val: u32 = 'lbl: loop { break 'lbl 55u32; };
        (($v, x), helper(), lbl_val)
    }}
}

#[allow(dead_code)]
fn helper() -> u32 { 999 }

fn main() {
    let x: u32 = 100;
    let ((cx, mx), iv, lv) = 'lbl: loop {
        break 'lbl def_mod::m_opaque!(x);
    };
    println!("OPAQUE_LOCAL=({},{}) OPAQUE_ITEM_DEFSITE={} OPAQUE_LABEL={}", cx, mx, iv, lv);
}
""",
        )

        # A2b: decl_macro calling private fn -> rejected by type-level FnDef privacy (not E0603!)
        part_a["decl_macro_opaque_priv_fn_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_priv_fn.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    fn helper() -> u32 { 10 }
    pub macro m_priv_fn() { helper() }
}

fn main() { println!("{}", def_mod::m_priv_fn!()); }
""",
        )

        # A2c: decl_macro reading private const of public type u32 -> ACCEPTED
        part_a["decl_macro_opaque_priv_const_ok"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_priv_const.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    const SECRET: u32 = 777;
    pub macro m_priv_const() { SECRET }
}

fn main() { println!("OPAQUE_PRIV_CONST={}", def_mod::m_priv_const!()); }
""",
        )

        # A2d: decl_macro reading private static of public type u32 -> test!
        part_a["decl_macro_opaque_priv_static_ok"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_priv_static.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    static SECRET_STATIC: u32 = 888;
    pub macro m_priv_static() { SECRET_STATIC }
}

fn main() { println!("OPAQUE_PRIV_STATIC={}", def_mod::m_priv_static!()); }
""",
        )

        # A2e: decl_macro calling private fn via private const fn-pointer (coerced away from private FnDef!)
        part_a["decl_macro_opaque_priv_fn_via_fnptr_const_ok"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_priv_fnptr.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    fn helper() -> u32 { 10 }
    const HELPER_PTR: fn() -> u32 = helper;
    pub macro m_priv_fn_via_ptr() { (HELPER_PTR)() }
}

fn main() { println!("OPAQUE_PRIV_FNPTR={}", def_mod::m_priv_fn_via_ptr!()); }
""",
        )

        # A2f: decl_macro referencing private unit struct value (private nominal type!) -> test!
        part_a["decl_macro_opaque_priv_struct_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a2_decl_priv_struct.rs",
            """
#![feature(decl_macro)]

mod def_mod {
    struct Hidden(u32);
    impl Hidden {
        pub fn get(&self) -> u32 { self.0 }
    }
    pub macro m_priv_struct() { Hidden(42).get() }
}

fn main() { println!("{}", def_mod::m_priv_struct!()); }
""",
        )

        # A3: Real compiled proc_macro crate testing call_site, mixed_site, def_site
        pm_src = workdir / "pm_hyg.rs"
        pm_src.write_text(
            """
#![feature(proc_macro_def_site)]
extern crate proc_macro;
use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

#[proc_macro]
pub fn read_x_call_site(_input: TokenStream) -> TokenStream {
    TokenStream::from(TokenTree::Ident(Ident::new("x", Span::call_site())))
}

#[proc_macro]
pub fn read_x_mixed_site(_input: TokenStream) -> TokenStream {
    TokenStream::from(TokenTree::Ident(Ident::new("x", Span::mixed_site())))
}

#[proc_macro]
pub fn read_x_def_site(_input: TokenStream) -> TokenStream {
    TokenStream::from(TokenTree::Ident(Ident::new("x", Span::def_site())))
}

#[proc_macro]
pub fn call_item_mixed_site(_input: TokenStream) -> TokenStream {
    // Emits: { let x: u32 = 123; caller_item() } with mixed_site spans
    let ms = Span::mixed_site();
    let inner: Vec<TokenTree> = vec![
        TokenTree::Ident(Ident::new("let", ms)),
        TokenTree::Ident(Ident::new("x", ms)),
        TokenTree::Punct(Punct::new(':', Spacing::Alone)),
        TokenTree::Ident(Ident::new("u32", ms)),
        TokenTree::Punct(Punct::new('=', Spacing::Alone)),
        TokenTree::Literal(Literal::u32_suffixed(123)),
        TokenTree::Punct(Punct::new(';', Spacing::Alone)),
        TokenTree::Ident(Ident::new("let", ms)),
        TokenTree::Ident(Ident::new("_", ms)),
        TokenTree::Punct(Punct::new('=', Spacing::Alone)),
        TokenTree::Ident(Ident::new("x", ms)),
        TokenTree::Punct(Punct::new(';', Spacing::Alone)),
        TokenTree::Ident(Ident::new("caller_item", ms)),
        TokenTree::Group(Group::new(Delimiter::Parenthesis, TokenStream::new())),
    ];
    let mut g = Group::new(Delimiter::Brace, inner.into_iter().collect());
    g.set_span(ms);
    TokenStream::from(TokenTree::Group(g))
}

#[proc_macro]
pub fn call_item_def_site(_input: TokenStream) -> TokenStream {
    let ds = Span::def_site();
    let mut parens = Group::new(Delimiter::Parenthesis, TokenStream::new());
    parens.set_span(ds);
    let toks: Vec<TokenTree> = vec![
        TokenTree::Ident(Ident::new("caller_item", ds)),
        TokenTree::Group(parens),
    ];
    toks.into_iter().collect()
}
""",
            encoding="utf-8",
        )
        pm_so = workdir / "libpm_hyg.so"
        pm_build = run_cmd(
            [
                rustc,
                "--color=never",
                "--crate-type=proc-macro",
                "--crate-name=pm_hyg",
                "--edition=2021",
                str(pm_src),
                "-o",
                str(pm_so),
            ],
            workdir,
        )
        part_a["proc_macro_crate_build"] = {
            "compile_rc": pm_build["rc"],
            "stderr_head": "\n".join(pm_build["stderr"].splitlines()[:12]),
        }

        pm_extern = ["--edition=2021", "--extern", f"pm_hyg={pm_so}"]
        part_a["proc_macro_call_site_captures_local"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a3_pm_call.rs",
            """
fn main() {
    let x: u32 = 77;
    println!("PM_CALL={}", pm_hyg::read_x_call_site!());
}
""",
            extra_args=pm_extern,
        )
        part_a["proc_macro_mixed_site_isolates_local"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a3_pm_mixed_err.rs",
            """
fn main() { let x: u32 = 77; let _ = pm_hyg::read_x_mixed_site!(); }
""",
            extra_args=pm_extern,
        )
        part_a["proc_macro_def_site_isolates_local"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a3_pm_def_err.rs",
            """
fn main() { let x: u32 = 77; let _ = pm_hyg::read_x_def_site!(); }
""",
            extra_args=pm_extern,
        )
        part_a["proc_macro_mixed_site_resolves_item_at_callsite"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a3_pm_mixed_item.rs",
            """
fn caller_item() -> u32 { 321 }
fn main() {
    let x: u32 = 77;
    let v = pm_hyg::call_item_mixed_site!();
    println!("PM_MIXED_ITEM={} CALLER_X={}", v, x);
}
""",
            extra_args=pm_extern,
        )
        part_a["proc_macro_def_site_isolates_callsite_item"] = compile_and_maybe_run(
            rustc,
            workdir,
            "a3_pm_def_item_err.rs",
            """
#[allow(dead_code)]
fn caller_item() -> u32 { 321 }
fn main() { let _ = pm_hyg::call_item_def_site!(); }
""",
            extra_args=pm_extern,
        )

        # ------------------------------------------------------------------
        # Part B: Cross-crate $crate vs. decl_macro privacy
        # ------------------------------------------------------------------
        part_b: dict[str, Any] = {}
        up_src = workdir / "up_mac.rs"
        up_src.write_text(
            """
#![feature(decl_macro)]

pub fn pub_helper() -> u32 { 200 }
fn secret_helper() -> u32 { 404 }
const UPSTREAM_SECRET_CONST: u32 = 505;
static UPSTREAM_SECRET_STATIC: u32 = 606;
const UPSTREAM_HELPER_PTR: fn() -> u32 = secret_helper;

#[macro_export]
macro_rules! call_pub_via_dollar_crate {
    () => { $crate::pub_helper() };
}

#[macro_export]
macro_rules! call_priv_via_dollar_crate {
    () => { $crate::secret_helper() };
}

#[macro_export]
macro_rules! read_priv_const_via_dollar_crate {
    () => { $crate::UPSTREAM_SECRET_CONST };
}

pub macro call_pub_via_decl_macro() { pub_helper() }
pub macro call_priv_via_decl_macro() { secret_helper() }
pub macro read_priv_const_via_decl_macro() { UPSTREAM_SECRET_CONST }
pub macro read_priv_static_via_decl_macro() { UPSTREAM_SECRET_STATIC }
pub macro call_priv_fnptr_via_decl_macro() { (UPSTREAM_HELPER_PTR)() }
""",
            encoding="utf-8",
        )
        up_rlib = workdir / "libup_mac.rlib"
        up_build = run_cmd(
            [
                rustc,
                "--color=never",
                "--crate-type=rlib",
                "--crate-name=up_mac",
                "--edition=2021",
                str(up_src),
                "-o",
                str(up_rlib),
            ],
            workdir,
        )
        part_b["upstream_build_rc"] = up_build["rc"]
        up_extern = ["--edition=2021", "--extern", f"up_mac={up_rlib}"]

        part_b["macro_rules_dollar_crate_pub"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b1_pub.rs",
            'fn main() { println!("DC_PUB={}", up_mac::call_pub_via_dollar_crate!()); }\n',
            extra_args=up_extern,
        )
        part_b["macro_rules_dollar_crate_priv_fn_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b2_priv_fn.rs",
            "fn main() { let _ = up_mac::call_priv_via_dollar_crate!(); }\n",
            extra_args=up_extern,
        )
        part_b["macro_rules_dollar_crate_priv_const_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b2_priv_const.rs",
            "fn main() { let _ = up_mac::read_priv_const_via_dollar_crate!(); }\n",
            extra_args=up_extern,
        )
        part_b["decl_macro_upstream_pub_fn_ok"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b3_decl_pub.rs",
            'fn main() { println!("DECL_PUB={}", up_mac::call_pub_via_decl_macro!()); }\n',
            extra_args=up_extern,
        )
        part_b["decl_macro_upstream_priv_fn_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b3_decl_priv_fn.rs",
            'fn main() { println!("DECL_PRIV={}", up_mac::call_priv_via_decl_macro!()); }\n',
            extra_args=up_extern,
        )
        part_b["decl_macro_upstream_priv_const_ok"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b3_decl_priv_const.rs",
            'fn main() { println!("DECL_PRIV_CONST={}", up_mac::read_priv_const_via_decl_macro!()); }\n',
            extra_args=up_extern,
        )
        part_b["decl_macro_upstream_priv_static_rejected"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b3_decl_priv_static.rs",
            'fn main() { println!("DECL_PRIV_STATIC={}", up_mac::read_priv_static_via_decl_macro!()); }\n',
            extra_args=up_extern,
        )
        part_b["decl_macro_upstream_priv_fnptr_mir_missing"] = compile_and_maybe_run(
            rustc,
            workdir,
            "b3_decl_priv_fnptr.rs",
            'fn main() { println!("DECL_PRIV_FNPTR={}", up_mac::call_priv_fnptr_via_decl_macro!()); }\n',
            extra_args=up_extern,
        )

        # ------------------------------------------------------------------
        # Part C: Edition 2021 vs. 2024 expr/expr_2021 & recursion_limit
        # ------------------------------------------------------------------
        part_c: dict[str, Any] = {}

        src_const = (
            "macro_rules! m { ($e:expr) => { $e }; }\n"
            'fn main() { let v = m!(const { 1 + 2 }); println!("EXPR_CONST={}", v); }\n'
        )
        part_c["ed2021_expr_const_block"] = compile_and_maybe_run(
            rustc, workdir, "c1_2021_const.rs", src_const, extra_args=["--edition=2021"]
        )
        part_c["ed2024_expr_const_block"] = compile_and_maybe_run(
            rustc, workdir, "c1_2024_const.rs", src_const, extra_args=["--edition=2024"]
        )

        src_under = (
            "macro_rules! m { ($e:expr) => { $e = 9 }; }\n"
            'fn main() { m!(_); println!("EXPR_UNDERSCORE_OK"); }\n'
        )
        part_c["ed2021_expr_underscore"] = compile_and_maybe_run(
            rustc, workdir, "c2_2021_under.rs", src_under, extra_args=["--edition=2021"]
        )
        part_c["ed2024_expr_underscore"] = compile_and_maybe_run(
            rustc, workdir, "c2_2024_under.rs", src_under, extra_args=["--edition=2024"]
        )

        src_e2021_const = (
            "macro_rules! m { ($e:expr_2021) => { $e }; }\n"
            "fn main() { let _ = m!(const { 1 + 2 }); }\n"
        )
        part_c["ed2024_expr_2021_rejects_const_block"] = compile_and_maybe_run(
            rustc, workdir, "c3_2024_e2021_const.rs", src_e2021_const, extra_args=["--edition=2024"]
        )

        src_e2021_under = (
            "macro_rules! m { ($e:expr_2021) => { $e = 9 }; }\n"
            "fn main() { m!(_); }\n"
        )
        part_c["ed2024_expr_2021_rejects_underscore"] = compile_and_maybe_run(
            rustc, workdir, "c3_2024_e2021_under.rs", src_e2021_under, extra_args=["--edition=2024"]
        )

        src_e2021_add = (
            "macro_rules! m { ($e:expr_2021) => { $e }; }\n"
            'fn main() { println!("EXPR_2021_ADD={}", m!(1 + 2)); }\n'
        )
        part_c["ed2024_expr_2021_accepts_regular_expr"] = compile_and_maybe_run(
            rustc, workdir, "c3_2024_e2021_add.rs", src_e2021_add, extra_args=["--edition=2024"]
        )

        # Cross-edition macro def-site vs call-site for $e:expr
        ed21_lib = workdir / "ed21_mac.rs"
        ed21_lib.write_text("#[macro_export] macro_rules! m21 { ($e:expr) => { $e }; }\n", encoding="utf-8")
        ed21_rlib = workdir / "libed21_mac.rlib"
        run_cmd(
            [rustc, "--color=never", "--crate-type=rlib", "--crate-name=ed21_mac", "--edition=2021", str(ed21_lib), "-o", str(ed21_rlib)],
            workdir,
        )
        ed24_lib = workdir / "ed24_mac.rs"
        ed24_lib.write_text("#[macro_export] macro_rules! m24 { ($e:expr) => { $e }; }\n", encoding="utf-8")
        ed24_rlib = workdir / "libed24_mac.rlib"
        run_cmd(
            [rustc, "--color=never", "--crate-type=rlib", "--crate-name=ed24_mac", "--edition=2024", str(ed24_lib), "-o", str(ed24_rlib)],
            workdir,
        )
        part_c["cross_edition_def2021_call2024_const_block"] = compile_and_maybe_run(
            rustc,
            workdir,
            "c3_def21_call24.rs",
            'fn main() { println!("XED={}", ed21_mac::m21!(const { 1 + 2 })); }\n',
            extra_args=["--edition=2024", "--extern", f"ed21_mac={ed21_rlib}"],
        )
        part_c["cross_edition_def2024_call2021_const_block"] = compile_and_maybe_run(
            rustc,
            workdir,
            "c3_def24_call21.rs",
            'fn main() { println!("XED={}", ed24_mac::m24!(const { 1 + 2 })); }\n',
            extra_args=["--edition=2021", "--extern", f"ed24_mac={ed24_rlib}"],
        )

        # Recursion limit boundary: nested inside println! (124..127) vs top-level (125..129)
        for n in (124, 125, 126, 127):
            pluses = " ".join(["+"] * n)
            src_rec = (
                "macro_rules! count { () => { 0usize }; (+ $($rest:tt)*) => { 1 + count!($($rest)*) }; }\n"
                f'fn main() {{ println!("REC={n}:{{}}", count!({pluses})); }}\n'
            )
            part_c[f"recursion_nested_println_depth_{n}"] = compile_and_maybe_run(
                rustc, workdir, f"c4_rec_nested_{n}.rs", src_rec, extra_args=["--edition=2021"]
            )

        for n in (125, 126, 127, 128, 129):
            pluses = " ".join(["+"] * n)
            src_rec = (
                "macro_rules! count { () => { 0usize }; (+ $($rest:tt)*) => { 1 + count!($($rest)*) }; }\n"
                f"fn main() {{ let v = count!({pluses}); println!(\"REC_TOP={n}:{{}}\", v); }}\n"
            )
            part_c[f"recursion_toplevel_depth_{n}"] = compile_and_maybe_run(
                rustc, workdir, f"c4_rec_top_{n}.rs", src_rec, extra_args=["--edition=2021"]
            )

        pluses_126 = " ".join(["+"] * 126)
        src_rec_raised = (
            '#![recursion_limit = "256"]\n'
            "macro_rules! count { () => { 0usize }; (+ $($rest:tt)*) => { 1 + count!($($rest)*) }; }\n"
            f'fn main() {{ println!("REC_RAISED=126:{{}}", count!({pluses_126})); }}\n'
        )
        part_c["recursion_nested_println_depth_126_limit_256"] = compile_and_maybe_run(
            rustc, workdir, "c4_rec_raised_126.rs", src_rec_raised, extra_args=["--edition=2021"]
        )

        # ------------------------------------------------------------------
        # Part D: Host-impure vs. pure proc_macro object-file determinism cliff
        # ------------------------------------------------------------------
        pm_env_src = workdir / "pm_env.rs"
        pm_env_src.write_text(
            """
extern crate proc_macro;
use proc_macro::TokenStream;

#[proc_macro]
pub fn emit_env_nonce(_input: TokenStream) -> TokenStream {
    let v: u64 = std::env::var("PROBE_BUILD_NONCE")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    format!("#[unsafe(no_mangle)] pub extern \\"C\\" fn nonce() -> u64 {{ {v}u64 }}")
        .parse()
        .unwrap()
}

#[proc_macro]
pub fn emit_pure_const(_input: TokenStream) -> TokenStream {
    "#[unsafe(no_mangle)] pub extern \\"C\\" fn pure_val() -> u64 { 0xCAFE_BABEu64 }"
        .parse()
        .unwrap()
}
""",
            encoding="utf-8",
        )
        pm_env_so = workdir / "libpm_env.so"
        pm_env_build = run_cmd(
            [
                rustc,
                "--color=never",
                "--crate-type=proc-macro",
                "--crate-name=pm_env",
                "--edition=2021",
                str(pm_env_src),
                "-o",
                str(pm_env_so),
            ],
            workdir,
        )

        impure_consumer = workdir / "d_impure.rs"
        impure_consumer.write_text("pm_env::emit_env_nonce!();\n", encoding="utf-8")
        pure_consumer = workdir / "d_pure.rs"
        pure_consumer.write_text("pm_env::emit_pure_const!();\n", encoding="utf-8")

        def build_obj(src: Path, out_name: str, nonce: str) -> dict[str, Any]:
            obj_path = workdir / out_name
            env = os.environ.copy()
            env["PROBE_BUILD_NONCE"] = nonce
            r = run_cmd(
                [
                    rustc,
                    "--color=never",
                    "--crate-type=lib",
                    "--crate-name=det_probe",
                    "--edition=2024",
                    "-C",
                    "codegen-units=1",
                    "-C",
                    "debuginfo=0",
                    "-C",
                    "opt-level=2",
                    f"--remap-path-prefix={workdir}=/remap",
                    "--emit=obj",
                    "--extern",
                    f"pm_env={pm_env_so}",
                    str(src),
                    "-o",
                    str(obj_path),
                ],
                workdir,
                env=env,
            )
            entry: dict[str, Any] = {"rc": r["rc"]}
            if r["rc"] == 0 and obj_path.is_file():
                digest, nbytes = sha256_file(obj_path)
                entry["sha256"] = digest
                entry["bytes"] = nbytes
            else:
                entry["stderr"] = r["stderr"]
            return entry

        runs = {
            "impure_run1_nonce_111111": build_obj(impure_consumer, "d1.o", "111111"),
            "impure_run2_nonce_111111": build_obj(impure_consumer, "d2.o", "111111"),
            "impure_run3_nonce_222222": build_obj(impure_consumer, "d3.o", "222222"),
            "pure_run1_nonce_111111": build_obj(pure_consumer, "p1.o", "111111"),
            "pure_run2_nonce_222222": build_obj(pure_consumer, "p2.o", "222222"),
        }
        part_d = {
            "proc_macro_build_rc": pm_env_build["rc"],
            "runs": runs,
            "same_env_bit_exact": (
                runs["impure_run1_nonce_111111"].get("sha256")
                == runs["impure_run2_nonce_111111"].get("sha256")
            ),
            "diff_env_breaks_reproducibility": (
                runs["impure_run1_nonce_111111"].get("sha256")
                != runs["impure_run3_nonce_222222"].get("sha256")
            ),
            "pure_proc_macro_env_invariant": (
                runs["pure_run1_nonce_111111"].get("sha256")
                == runs["pure_run2_nonce_222222"].get("sha256")
            ),
        }

        return {
            "observed_at_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": rustc_version,
            "rustc_commit_hash": commit_hash,
            "part_a_three_way_hygiene_matrix": part_a,
            "part_b_cross_crate_dollar_crate_vs_decl_macro": part_b,
            "part_c_edition2021_vs_2024_expr_and_recursion_limit": part_c,
            "part_d_proc_macro_nondeterminism_repro_cliff": part_d,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Write JSON output to file")
    args = parser.parse_args()
    rustc = find_rustc()
    result = run_probe(rustc)
    text = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
