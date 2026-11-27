#!/usr/bin/env python3
"""Compile verbatim library/std/src/sys/sync/mutex/futex.rs inside a minimal
#![no_std] shim crate and measure exact Runtime(PostCleanup) MIR across
-Cpanic=abort, -Cpanic=unwind, normal cfgs, and --cfg test.
"""
import argparse
import difflib
import json
import pathlib
import re
import subprocess
import tempfile


def discover_rust_src(toolchain: str) -> pathlib.Path:
    cmd = ["rustc"]
    if toolchain:
        cmd.append(toolchain)
    cmd.extend(["--print", "sysroot"])
    sysroot = pathlib.Path(subprocess.check_output(cmd, text=True).strip())
    return sysroot / "lib/rustlib/src/rust/library"


def make_shim(with_rustc_attrs: bool) -> str:
    feats = ["#![feature(generic_atomic)]"]
    if with_rustc_attrs:
        feats.append("#![feature(rustc_attrs)]")
    return f"""#![no_std]
#![allow(internal_features, dead_code, unused_imports)]
{chr(10).join(feats)}
pub mod time {{
    pub use core::time::Duration;
}}
pub mod hint {{
    pub use core::hint::spin_loop;
}}
pub mod sync {{
    pub mod atomic {{
        pub use core::sync::atomic::{{Atomic, Ordering}};
    }}
}}
pub mod sys {{
    pub mod futex {{
        pub type SmallPrimitive = u32;
        pub type SmallFutex = crate::sync::atomic::Atomic<SmallPrimitive>;
        pub type Primitive = u32;
        pub type Futex = crate::sync::atomic::Atomic<Primitive>;
        #[inline(never)]
        pub fn futex_wait(
            _futex: &SmallFutex,
            _expected: SmallPrimitive,
            _timeout: Option<crate::time::Duration>,
        ) -> bool {{
            true
        }}
        #[inline(never)]
        pub fn futex_wake(_futex: &SmallFutex) -> bool {{
            true
        }}
    }}
}}
#[path = "futex_verbatim.rs"]
pub mod futex_target;
"""


def parse_fn_mir(fn_text: str) -> dict:
    header = fn_text.splitlines()[0].strip()
    raw_name = header.split("(")[0].strip()
    fn_name = re.sub(r"::<impl at [^>]+>", "::Mutex", raw_name)
    bbs = re.findall(r"^\s+bb(\d+)( \(cleanup\))?:", fn_text, re.M)
    local_lines = [l.strip() for l in fn_text.splitlines() if re.match(r"^\s+let (?:mut )?_\d+:", l)]
    calls = []
    for m in re.finditer(r"(?:_[0-9]+\s*=\s*)?([^\n=]+?)\([^()\n]*\)\s*->\s*\[return:\s*bb\d+,\s*unwind\s+([^\]]+)\]", fn_text):
        callee = re.sub(r"\s+", " ", m.group(1).strip())
        calls.append({"callee": callee, "unwind": m.group(2).strip()})
    stmts = []
    for line in fn_text.splitlines():
        s = line.strip()
        if not s or s.startswith("//") or s.startswith("debug ") or s.startswith("let ") or s.startswith("scope ") or s.startswith("bb") or s in ("{", "}"):
            continue
        if re.search(r"->\s*\[|^(?:goto ->|switchInt\(|return;|unreachable;|assert\(|drop\()", s):
            continue
        if s.endswith(";"):
            stmts.append(s)
    return {
        "fn": fn_name,
        "basic_blocks": len(bbs),
        "cleanup_blocks": sum(1 for _, c in bbs if c),
        "locals_excluding_params": len(local_lines),
        "statement_count": len(stmts),
        "has_drop": bool(re.search(r"^\s+drop\(", fn_text, re.M)),
        "has_assert": bool(re.search(r"^\s+assert\(", fn_text, re.M)),
        "has_place_mention": any(s.startswith("PlaceMention(") for s in stmts),
        "has_discriminant": any("discriminant(" in s for s in stmts),
        "has_downcast_field": any(" as " in s for s in stmts),
        "has_struct_aggregate": any("Mutex { futex:" in s for s in stmts),
        "has_option_none_aggregate": any("Option::<Duration>::None" in s for s in stmts),
        "has_ordering_aggregate": any("Ordering::" in s for s in stmts),
        "calls": calls,
    }


def run_variant(toolchain: str, rust_src: pathlib.Path, panic_mode: str, extra_cfg: list[str], with_rustc_attrs: bool) -> dict:
    futex_rs = rust_src / "std/src/sys/sync/mutex/futex.rs"
    with tempfile.TemporaryDirectory() as td:
        td_path = pathlib.Path(td)
        (td_path / "futex_verbatim.rs").write_text(futex_rs.read_text())
        shim = td_path / "shim.rs"
        shim.write_text(make_shim(with_rustc_attrs))
        dump_dir = td_path / "dump"
        dump_dir.mkdir()
        mir_out = td_path / "out.mir"
        cmd = ["rustc"]
        if toolchain:
            cmd.append(toolchain)
        cmd.extend([
            str(shim),
            "--edition=2024",
            "--crate-type=lib",
            "--crate-name=futex_shim",
            "-Zmir-preserve-ub",
            "-Copt-level=0",
            "-Cdebug-assertions=no",
            "-Coverflow-checks=no",
            f"-Cpanic={panic_mode}",
            "-Zdump-mir=runtime-post-cleanup",
            f"-Zdump-mir-dir={dump_dir}",
            "--emit=mir",
            "-o",
            str(mir_out),
        ])
        cmd.extend(extra_cfg)
        res = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if res.returncode != 0:
            return {"rc": res.returncode, "stderr": res.stderr}
        post_files = sorted(dump_dir.glob("*futex_target*runtime-post-cleanup.after.mir"))
        joined = "\n".join(p.read_text() for p in post_files)
        # Normalize temporary directory path in spans for structural diffing
        norm = re.sub(r"/tmp/[^/]+/futex_verbatim\.rs", "futex_verbatim.rs", joined)
        fns = [parse_fn_mir(sec) for sec in re.split(r"(?m)^fn ", norm)[1:]]
        return {
            "rc": 0,
            "file_count": len(post_files),
            "functions": fns,
            "normalized_mir": norm,
        }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--toolchain", default="+nightly-2026-05-31")
    ap.add_argument("--out", default="-")
    args = ap.parse_args()

    rust_src = discover_rust_src(args.toolchain)
    ver = subprocess.check_output(
        ["rustc"] + ([args.toolchain] if args.toolchain else []) + ["--version"],
        text=True,
    ).strip()
    abort_normal = run_variant(args.toolchain, rust_src, "abort", [], True)
    unwind_normal = run_variant(args.toolchain, rust_src, "unwind", [], True)
    abort_cfg_test = run_variant(args.toolchain, rust_src, "abort", ["--cfg", "test"], False)
    unwind_cfg_test = run_variant(args.toolchain, rust_src, "unwind", ["--cfg", "test"], False)

    diff_abort_vs_unwind = list(difflib.unified_diff(
        abort_cfg_test["normalized_mir"].splitlines(),
        unwind_cfg_test["normalized_mir"].splitlines(),
        fromfile="abort_cfg_test",
        tofile="unwind_cfg_test",
        n=0,
    ))
    summary = {
        "rustc_version": ver,
        "target_file": "library/std/src/sys/sync/mutex/futex.rs",
        "variants": {
            "abort_normal": {k: v for k, v in abort_normal.items() if k != "normalized_mir"},
            "unwind_normal": {k: v for k, v in unwind_normal.items() if k != "normalized_mir"},
            "abort_cfg_test": {k: v for k, v in abort_cfg_test.items() if k != "normalized_mir"},
            "unwind_cfg_test": {k: v for k, v in unwind_cfg_test.items() if k != "normalized_mir"},
        },
        "abort_normal_eq_abort_cfg_test": abort_normal.get("normalized_mir") == abort_cfg_test.get("normalized_mir"),
        "unwind_normal_eq_unwind_cfg_test": unwind_normal.get("normalized_mir") == unwind_cfg_test.get("normalized_mir"),
        "abort_vs_unwind_diff_hunks": [l for l in diff_abort_vs_unwind if l.startswith(("+", "-", "@@"))],
    }
    txt = json.dumps(summary, indent=2) + "\n"
    if args.out == "-":
        print(txt)
    else:
        pathlib.Path(args.out).write_text(txt)


if __name__ == "__main__":
    main()
