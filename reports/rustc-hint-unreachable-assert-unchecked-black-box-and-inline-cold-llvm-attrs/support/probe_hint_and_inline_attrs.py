#!/usr/bin/env python3
"""Reproducible compiler, MIR, LLVM IR, and Miri empirical probe for
core::hint::{unreachable_unchecked, assert_unchecked, black_box} and #[inline]/#[cold] attrs.
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
OUT_PATH = HERE / "probe_results.json"


def build_env() -> dict[str, str]:
    env = dict(os.environ)
    cargo_bin = str(pathlib.Path.home() / ".cargo" / "bin")
    env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    return env


def sanitize(text: str, tmp_dir: pathlib.Path) -> str:
    home = str(pathlib.Path.home())
    out = text.replace(str(tmp_dir), "<tmp>")
    out = out.replace(home, "<home>")
    out = re.sub(r"thread '([^']+)' \(\d+\) panicked", r"thread '\1' (<tid>) panicked", out)
    return out


def extract_llvm_functions(ir_text: str, fn_names: list[str]) -> tuple[dict[str, list[str]], dict[str, str], list[str]]:
    lines = ir_text.splitlines()
    attr_defs: dict[str, str] = {}
    for line in lines:
        m = re.match(r"^attributes (#\d+) = (.+)$", line)
        if m:
            attr_defs[m.group(1)] = line

    by_fn: dict[str, list[str]] = {}
    resolved_attrs: dict[str, str] = {}
    decls: list[str] = []

    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("define "):
            matched = [fn for fn in fn_names if f"@{fn}(" in line or re.search(rf"@{re.escape(fn)}[^a-zA-Z0-9_]", line) or (fn in line and "define " in line)]
            # Prefer exact @fn or mangled symbol containing fn cleanly
            hit = None
            for fn in fn_names:
                if f"@{fn}(" in line or re.search(rf"\d+{re.escape(fn)}[(E]", line):
                    hit = fn
                    break
            if hit is not None:
                block = [line]
                m_attr = re.search(r"\s(#\d+)\b", line)
                if m_attr and m_attr.group(1) in attr_defs:
                    resolved_attrs[hit] = attr_defs[m_attr.group(1)]
                i += 1
                while i < len(lines):
                    block.append(lines[i])
                    if lines[i] == "}":
                        break
                    i += 1
                by_fn[hit] = block
        elif line.startswith("declare "):
            for fn in fn_names:
                if f"@{fn}(" in line or "llvm.assume" in line or re.search(rf"\d+{re.escape(fn)}[(E]", line):
                    if line not in decls:
                        decls.append(line)
                    break
        i += 1

    return by_fn, resolved_attrs, decls


def run_rustc_binary(src: str, extra_args: list[str], env: dict[str, str]) -> dict:
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        rs = td / "probe.rs"
        exe = td / "probe"
        rs.write_text(src, encoding="utf-8")
        c = subprocess.run(
            ["rustc", "--edition=2024", *extra_args, "-o", str(exe), str(rs)],
            capture_output=True,
            text=True,
            env=env,
        )
        res = {
            "edition": "2024",
            "extra_args": extra_args,
            "compile_returncode": c.returncode,
            "compile_stdout": sanitize(c.stdout, td).strip(),
            "compile_stderr": sanitize(c.stderr, td).strip(),
        }
        if c.returncode == 0:
            r = subprocess.run([str(exe)], capture_output=True, text=True, env=env)
            res["run_returncode"] = r.returncode
            res["run_stdout"] = sanitize(r.stdout, td).strip()
            res["run_stderr"] = sanitize(r.stderr, td).strip()
        return res


def run_rustc_ir(src: str, extra_args: list[str], fn_names: list[str], env: dict[str, str]) -> dict:
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        rs = td / "probe.rs"
        ll = td / "probe.ll"
        rs.write_text(src, encoding="utf-8")
        c = subprocess.run(
            ["rustc", "--edition=2024", *extra_args, "--emit=llvm-ir", "-o", str(ll), str(rs)],
            capture_output=True,
            text=True,
            env=env,
        )
        out = {
            "edition": "2024",
            "extra_args": extra_args,
            "compile_returncode": c.returncode,
            "compile_stderr": sanitize(c.stderr, td).strip(),
        }
        if c.returncode == 0:
            ir = ll.read_text(encoding="utf-8")
            by_fn, resolved_attrs, decls = extract_llvm_functions(ir, fn_names)
            out["llvm_ir_by_fn"] = by_fn
            out["resolved_attributes"] = resolved_attrs
            out["llvm_decls"] = decls
        return out


def run_miri_probe(main_rs: str, env: dict[str, str], cargo_miri_flags: str | None = None) -> dict:
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        (td / "Cargo.toml").write_text(
            '[package]\nname = "miri_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        src_dir = td / "src"
        src_dir.mkdir()
        (src_dir / "main.rs").write_text(main_rs, encoding="utf-8")
        run_env = dict(env)
        if cargo_miri_flags is not None:
            run_env["MIRIFLAGS"] = cargo_miri_flags
        r = subprocess.run(
            ["cargo", "miri", "run", "--offline"],
            cwd=td,
            capture_output=True,
            text=True,
            env=run_env,
        )
        return {
            "edition": "2024",
            "command": "cargo miri run --offline",
            "miriflags": cargo_miri_flags,
            "returncode": r.returncode,
            "stdout": sanitize(r.stdout, td).strip(),
            "stderr": sanitize(r.stderr, td).strip(),
        }


def run_mir_dump_probe(src: str, extra_args: list[str], env: dict[str, str]) -> dict:
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        rs = td / "probe.rs"
        dump_dir = td / "mir_dump"
        dump_dir.mkdir()
        rs.write_text(src, encoding="utf-8")
        c = subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                *extra_args,
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={dump_dir}",
                "--emit=mir",
                "-o",
                str(td / "out.mir"),
                str(rs),
            ],
            capture_output=True,
            text=True,
            env=env,
        )
        wanted_prefixes = (
            "probe.lower_assume.",
            "probe.lower_unreachable.",
            "probe.prune_unreachable_branch.",
            "probe.black_box_const_op.",
        )
        wanted_stages = (
            ".LowerIntrinsics.after.mir",
            ".Inline.after.mir",
            ".UnreachablePropagation.after.mir",
            ".InstSimplify-after-simplifycfg.after.mir",
            ".SimplifyConstCondition-after-inst-simplify.after.mir",
            ".runtime-optimized.after.mir",
        )
        stages: dict[str, str] = {}
        for p in sorted(dump_dir.iterdir()):
            if p.name.startswith(wanted_prefixes) and p.name.endswith(wanted_stages):
                stages[p.name] = p.read_text(encoding="utf-8").strip()
        return {
            "edition": "2024",
            "extra_args": extra_args,
            "compile_returncode": c.returncode,
            "selected_mir_stages": stages,
        }


def run_cross_crate_probe(up_src: str, down_src: str, up_args: list[str], down_args: list[str], down_fns: list[str], env: dict[str, str]) -> dict:
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        up_rs = td / "up.rs"
        up_rlib = td / "libup.rlib"
        down_rs = td / "down.rs"
        down_ll = td / "down.ll"
        up_rs.write_text(up_src, encoding="utf-8")
        down_rs.write_text(down_src, encoding="utf-8")

        cu = subprocess.run(
            ["rustc", "--edition=2024", "--crate-type=rlib", *up_args, "-o", str(up_rlib), str(up_rs)],
            capture_output=True,
            text=True,
            env=env,
        )
        cd = subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                *down_args,
                "--extern",
                f"up={up_rlib}",
                "--emit=llvm-ir",
                "-o",
                str(down_ll),
                str(down_rs),
            ],
            capture_output=True,
            text=True,
            env=env,
        )
        res = {
            "edition": "2024",
            "up_args": up_args,
            "down_args": down_args,
            "up_returncode": cu.returncode,
            "up_stderr": sanitize(cu.stderr, td).strip(),
            "down_returncode": cd.returncode,
            "down_stderr": sanitize(cd.stderr, td).strip(),
        }
        if cu.returncode == 0 and cd.returncode == 0:
            ir = down_ll.read_text(encoding="utf-8")
            by_fn, resolved, decls = extract_llvm_functions(ir, down_fns)
            res["down_llvm_ir_by_fn"] = by_fn
            res["down_resolved_attributes"] = resolved
            res["down_llvm_decls"] = decls
        return res


def run_incremental_mir_inline_probe(env: dict[str, str]) -> dict:
    src = """
#![crate_type = "lib"]
#[inline(always)]
fn helper(x: i32) -> i32 { x.wrapping_add(7) }

#[unsafe(no_mangle)]
pub fn caller(x: i32) -> i32 { helper(x) }
"""
    results = {}
    for label, use_incr in [("non_incremental_opt2", False), ("incremental_opt2", True)]:
        with tempfile.TemporaryDirectory() as td_str:
            td = pathlib.Path(td_str)
            rs = td / "incr.rs"
            dump_dir = td / "mir_dump"
            dump_dir.mkdir()
            rs.write_text(src, encoding="utf-8")
            cmd = [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Zdump-mir=caller",
                f"-Zdump-mir-dir={dump_dir}",
                "--emit=mir",
                "-o",
                str(td / "out.mir"),
            ]
            if use_incr:
                incr_dir = td / "incr_cache"
                incr_dir.mkdir()
                cmd.append(f"-Cincremental={incr_dir}")
            cmd.append(str(rs))
            c = subprocess.run(cmd, capture_output=True, text=True, env=env)
            inline_stages = {}
            for p in sorted(dump_dir.iterdir()):
                if ".Inline." in p.name or ".runtime-optimized." in p.name:
                    inline_stages[p.name] = p.read_text(encoding="utf-8").strip()
            results[label] = {
                "compile_returncode": c.returncode,
                "mir_stages": inline_stages,
            }
    return results


def main() -> int:
    env = build_env()
    rv = subprocess.run(["rustc", "-Vv"], capture_output=True, text=True, check=True, env=env).stdout.strip()
    mv = subprocess.run(["cargo", "miri", "--version"], capture_output=True, text=True, check=True, env=env).stdout.strip()

    unreach_src = """
fn main() {
    if std::hint::black_box(true) {
        unsafe { core::hint::unreachable_unchecked() };
    }
    println!("REACHED");
}
"""
    assert_false_src = """
fn main() {
    let cond = std::hint::black_box(false);
    unsafe { core::hint::assert_unchecked(cond) };
    println!("ASSERT_OK");
}
"""
    guarded_safe_src = """
#[inline(never)]
fn compute(x: u32) -> u32 {
    if x == 0 {
        return 25;
    }
    unsafe { core::hint::assert_unchecked(x != 0) };
    x * 5
}

fn main() {
    let a = compute(std::hint::black_box(0));
    let b = compute(std::hint::black_box(5));
    println!("GUARDED_OK={a},{b}");
}
"""

    a_exec = {
        "unreachable_unchecked_opt0_debug_on": run_rustc_binary(unreach_src, ["-Copt-level=0", "-Cdebug-assertions=on"], env),
        "unreachable_unchecked_opt0_debug_off": run_rustc_binary(unreach_src, ["-Copt-level=0", "-Cdebug-assertions=off"], env),
        "unreachable_unchecked_opt0_debug_off_ub_no": run_rustc_binary(unreach_src, ["-Copt-level=0", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "unreachable_unchecked_opt1_debug_off_ub_no": run_rustc_binary(unreach_src, ["-Copt-level=1", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "unreachable_unchecked_opt2_debug_off_ub_no": run_rustc_binary(unreach_src, ["-Copt-level=2", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "assert_unchecked_false_opt0_debug_on": run_rustc_binary(assert_false_src, ["-Copt-level=0", "-Cdebug-assertions=on"], env),
        "assert_unchecked_false_opt0_debug_off": run_rustc_binary(assert_false_src, ["-Copt-level=0", "-Cdebug-assertions=off"], env),
        "assert_unchecked_false_opt0_debug_off_ub_no": run_rustc_binary(assert_false_src, ["-Copt-level=0", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "assert_unchecked_false_opt2_debug_off_ub_no": run_rustc_binary(assert_false_src, ["-Copt-level=2", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "guarded_safe_release_ub_no": run_rustc_binary(guarded_safe_src, ["-Copt-level=2", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "miri_unreachable_unchecked_ub": run_miri_probe('fn main() {\n    if core::hint::black_box(true) {\n        unsafe { core::hint::unreachable_unchecked() };\n    }\n}\n', env),
        "miri_assert_unchecked_false_ub": run_miri_probe('fn main() {\n    let cond = core::hint::black_box(false);\n    unsafe { core::hint::assert_unchecked(cond) };\n}\n', env),
        "miri_assert_unchecked_true_ok": run_miri_probe('fn main() {\n    let cond = core::hint::black_box(true);\n    unsafe { core::hint::assert_unchecked(cond) };\n    println!("MIRI_TRUE_OK");\n}\n', env),
    }

    mir_ir_src = """
#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub unsafe fn lower_assume(cond: bool) {
    unsafe { core::hint::assert_unchecked(cond) };
}

#[unsafe(no_mangle)]
pub unsafe fn lower_unreachable() -> ! {
    unsafe { core::hint::unreachable_unchecked() }
}

#[unsafe(no_mangle)]
pub fn prune_assert_unchecked_branch(x: i32) -> bool {
    unsafe { core::hint::assert_unchecked(x != 0) };
    x == 0
}

#[unsafe(no_mangle)]
pub fn prune_unreachable_branch(x: i32) -> i32 {
    if x == 0 {
        unsafe { core::hint::unreachable_unchecked() };
    }
    x.wrapping_add(1)
}

#[unsafe(no_mangle)]
pub fn black_box_const_op() -> i32 {
    core::hint::black_box(2) + core::hint::black_box(3)
}
"""
    ir_fn_names = [
        "lower_assume",
        "lower_unreachable",
        "prune_assert_unchecked_branch",
        "prune_unreachable_branch",
        "black_box_const_op",
    ]
    mir_dumps = {
        "opt2_debug_off_ub_no": run_mir_dump_probe(mir_ir_src, ["-Copt-level=2", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
        "opt0_debug_off_ub_no": run_mir_dump_probe(mir_ir_src, ["-Copt-level=0", "-Cdebug-assertions=off", "-Zub-checks=no"], env),
    }

    # Trace first LLVM pass creating range(i32 2, 1) on prune_unreachable_branch
    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        rs = td / "range_trace.rs"
        rs.write_text(mir_ir_src, encoding="utf-8")
        rt = subprocess.run(
            [
                "rustc",
                "--edition=2024",
                "--crate-type=lib",
                "-Copt-level=2",
                "-Cdebug-assertions=off",
                "-Zub-checks=no",
                "--emit=llvm-ir",
                "-Cllvm-args=-print-after-all",
                "-Cllvm-args=-filter-print-funcs=prune_unreachable_branch",
                "-o",
                str(td / "rt.ll"),
                str(rs),
            ],
            capture_output=True,
            text=True,
            env=env,
        )
        prev_hdr = ""
        first_range_pass = None
        first_range_define = None
        for line in rt.stderr.splitlines():
            if "IR Dump After" in line:
                prev_hdr = line.strip()
            elif "define " in line and "prune_unreachable_branch" in line and "range(" in line:
                first_range_pass = prev_hdr
                first_range_define = line.strip()
                break

    llvm_ir_matrix = {
        "opt0_debug_off_ub_no": run_rustc_ir(mir_ir_src, ["-Copt-level=0", "-Cdebug-assertions=off", "-Zub-checks=no"], ir_fn_names, env),
        "opt1_debug_off_ub_no": run_rustc_ir(mir_ir_src, ["-Copt-level=1", "-Cdebug-assertions=off", "-Zub-checks=no", "-Zmerge-functions=disabled"], ir_fn_names, env),
        "opt2_debug_on": run_rustc_ir(mir_ir_src, ["-Copt-level=2", "-Cdebug-assertions=on", "-Zmerge-functions=disabled"], ir_fn_names, env),
        "opt2_debug_off_ub_no": run_rustc_ir(mir_ir_src, ["-Copt-level=2", "-Cdebug-assertions=off", "-Zub-checks=no", "-Zmerge-functions=disabled"], ir_fn_names, env),
        "range_attr_pass_attribution": {
            "pass_header": first_range_pass,
            "define_line": first_range_define,
        },
    }

    attrs_src = """
#![crate_type = "lib"]
#![feature(optimize_attribute)]

#[cold]
#[inline(never)]
#[unsafe(no_mangle)]
pub fn fn_attr_cold_never(x: i32) -> i32 { x + 1 }

#[cold]
pub fn fn_attr_cold_internal(x: i32) -> i32 { x + 10 }

#[inline]
pub fn fn_attr_hint_internal(x: i32) -> i32 { x + 4 }

#[inline(never)]
#[unsafe(no_mangle)]
pub fn fn_attr_never(x: i32) -> i32 { x + 2 }

#[inline(always)]
pub fn fn_attr_always_internal(x: i32) -> i32 { x + 3 }

#[optimize(none)]
#[unsafe(no_mangle)]
pub fn fn_attr_opt_none(x: i32) -> i32 { x + 6 }

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn fn_attr_hint_avx2(x: i32) -> i32 { x + 7 }

#[unsafe(no_mangle)]
pub fn call_internal_attrs(x: i32) -> i32 {
    let a = core::hint::black_box(fn_attr_cold_internal as fn(i32) -> i32)(x);
    let b = core::hint::black_box(fn_attr_hint_internal as fn(i32) -> i32)(x);
    let c = core::hint::black_box(fn_attr_always_internal as fn(i32) -> i32)(x);
    let d = unsafe { core::hint::black_box(fn_attr_hint_avx2 as unsafe fn(i32) -> i32)(x) };
    a + b + c + d
}

#[unsafe(no_mangle)]
pub fn black_box_no_fold() -> i32 {
    core::hint::black_box(2) + core::hint::black_box(3)
}

#[unsafe(no_mangle)]
pub fn black_box_zst() {
    core::hint::black_box(())
}

#[unsafe(no_mangle)]
pub fn plain_fold() -> i32 {
    2 + 3
}
"""
    attr_fn_names = [
        "fn_attr_cold_never",
        "fn_attr_cold_internal",
        "fn_attr_hint_internal",
        "fn_attr_never",
        "fn_attr_always_internal",
        "fn_attr_opt_none",
        "fn_attr_hint_avx2",
        "black_box_no_fold",
        "black_box_zst",
        "plain_fold",
    ]
    b_attrs_and_bb = {
        "llvm_ir_black_box_and_attrs": run_rustc_ir(
            attrs_src,
            ["-Copt-level=2", "-Zmerge-functions=disabled"],
            attr_fn_names,
            env,
        ),
        "black_box_const_eval_and_exec": run_rustc_binary(
            'const C: i32 = core::hint::black_box(3 + 4);\nfn main() {\n    let r = core::hint::black_box(2) + core::hint::black_box(3);\n    println!("CONST_BB={C} RT_BB={r}");\n}\n',
            ["-Copt-level=2"],
            env,
        ),
        "black_box_const_eval_and_miri": run_miri_probe(
            'const C: i32 = core::hint::black_box(3 + 4);\nfn main() {\n    let r = core::hint::black_box(2) + core::hint::black_box(3);\n    println!("CONST_BB={C} RT_BB={r}");\n}\n',
            env,
        ),
    }

    up_src = """
#[inline(always)]
pub fn up_inline_always(x: i32) -> i32 { x + 22 }

#[inline]
pub fn up_inline_hint(x: i32) -> i32 { x + 11 }

#[inline(never)]
pub fn up_inline_never(x: i32) -> i32 { x + 33 }

#[cold]
pub fn up_cold_only(x: i32) -> i32 { x + 44 }

pub fn up_unannotated_leaf(x: i32) -> i32 { x + 55 }

#[inline(never)]
fn non_leaf_helper(x: i32) -> i32 { x + 1 }

pub fn up_unannotated_with_call(x: i32) -> i32 { non_leaf_helper(x) + 2 }

pub fn up_unannotated_large(x: i32) -> i32 {
    let mut acc = x;
    let mut i = 0;
    while i < 64 {
        acc = acc.wrapping_mul(3).wrapping_add(i);
        i += 1;
    }
    acc
}
"""
    down_src = """
#[unsafe(no_mangle)]
pub fn call_up_inline_always(x: i32) -> i32 { up::up_inline_always(x) }

#[unsafe(no_mangle)]
pub fn call_up_inline_hint(x: i32) -> i32 { up::up_inline_hint(x) }

#[unsafe(no_mangle)]
pub fn call_up_inline_never(x: i32) -> i32 { up::up_inline_never(x) }

#[unsafe(no_mangle)]
pub fn call_up_cold_only(x: i32) -> i32 { up::up_cold_only(x) }

#[unsafe(no_mangle)]
pub fn call_up_unannotated_leaf(x: i32) -> i32 { up::up_unannotated_leaf(x) }

#[unsafe(no_mangle)]
pub fn call_up_unannotated_with_call(x: i32) -> i32 { up::up_unannotated_with_call(x) }

#[unsafe(no_mangle)]
pub fn call_up_unannotated_large(x: i32) -> i32 { up::up_unannotated_large(x) }
"""
    down_fns = [
        "call_up_inline_always",
        "call_up_inline_hint",
        "call_up_inline_never",
        "call_up_cold_only",
        "call_up_unannotated_leaf",
        "call_up_unannotated_with_call",
        "call_up_unannotated_large",
    ]
    c_cross_and_diags = {
        "cross_crate_opt2_no_lto": run_cross_crate_probe(
            up_src,
            down_src,
            ["-Copt-level=2"],
            ["-Copt-level=2", "-Zmerge-functions=disabled"],
            down_fns + ["up_inline_never", "up_unannotated_with_call"],
            env,
        ),
        "cross_crate_opt0_always_inline": run_cross_crate_probe(
            up_src,
            down_src,
            ["-Copt-level=0"],
            ["-Copt-level=0"],
            down_fns + ["up_inline_never", "up_inline_hint", "up_cold_only", "up_unannotated_leaf", "up_unannotated_with_call"],
            env,
        ),
        "no_mangle_inline_always_warning": run_rustc_ir(
            '#[inline(always)]\n#[unsafe(no_mangle)]\npub extern "C" fn exp_always(x: i32) -> i32 { x + 1 }\n',
            ["--crate-type=lib", "-Copt-level=2"],
            ["exp_always"],
            env,
        ),
        "target_feature_inline_always_error": run_rustc_ir(
            '#[inline(always)]\n#[target_feature(enable = "avx2")]\npub unsafe fn bad_always_tf(x: i32) -> i32 { x + 1 }\n',
            ["--crate-type=lib", "-Copt-level=2"],
            ["bad_always_tf"],
            env,
        ),
        "conflicting_always_then_never": run_rustc_ir(
            '#[inline(always)]\n#[inline(never)]\npub fn f(x: i32) -> i32 { x + 1 }\n#[unsafe(no_mangle)]\npub fn use_f(x: i32) -> i32 { core::hint::black_box(f as fn(i32) -> i32)(x) }\n',
            ["--crate-type=lib", "-Copt-level=2"],
            ["f", "use_f"],
            env,
        ),
        "conflicting_never_then_always": run_rustc_ir(
            '#[inline(never)]\n#[inline(always)]\npub fn f(x: i32) -> i32 { x + 1 }\n#[unsafe(no_mangle)]\npub fn use_f(x: i32) -> i32 { core::hint::black_box(f as fn(i32) -> i32)(x) }\n',
            ["--crate-type=lib", "-Copt-level=2"],
            ["f", "use_f"],
            env,
        ),
        "conflicting_always_then_never_deny_warnings": run_rustc_ir(
            '#[inline(always)]\n#[inline(never)]\npub fn f(x: i32) -> i32 { x + 1 }\n',
            ["--crate-type=lib", "-Copt-level=2", "-Dwarnings"],
            ["f"],
            env,
        ),
        "mir_inline_incremental_vs_non_incremental": run_incremental_mir_inline_probe(env),
    }

    payload = {
        "rustc_version": rv,
        "miri_version": mv,
        "experiments": {
            "a_unreachable_unchecked_and_assert_unchecked": a_exec,
            "b_mir_dumps": mir_dumps,
            "c_llvm_ir_opt_level_matrix": llvm_ir_matrix,
            "d_black_box_and_llvm_attrs": b_attrs_and_bb,
            "e_cross_crate_and_diagnostics": c_cross_and_diags,
        },
    }
    OUT_PATH.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")
    print(f"Wrote {OUT_PATH} ({OUT_PATH.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
