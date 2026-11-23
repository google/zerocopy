#!/usr/bin/env python3
"""Live rustc & Miri differential probe suite for:
  (A) Inline `const { ... }` blocks, `required_consts`, cross-crate inlinability,
      and two-stage PME timing (--emit=metadata vs --crate-type=lib/bin across -O0/-O2);
  (B) `&const { ... }` static promotion vs InteriorMutable (`Cell`) and `NeedsDrop`
      stack-temporary rules (`E0515`), including `&[HasDrop; 0]` / `&mut []` exceptions;
  (C) `TyKind::Pat` (`#![feature(pattern_types, pattern_type_macro)]`) layout niches,
      LLVM `range(...)` metadata optimization, CTFE `E0080`, Miri SB/TB validity UB,
      and `ConstructorSet::Unlistable` exhaustiveness.
"""

from __future__ import annotations

import getpass
import json
import os
import pathlib
import re
import socket
import subprocess
import sys
import tempfile
from typing import Any


def sanitize(text: str, tmp_dir: str) -> str:
    home = str(pathlib.Path.home())
    text = text.replace(tmp_dir, "<tmp>")
    text = text.replace(home, "<home>")
    text = text.replace(socket.gethostname(), "<host>")
    user = getpass.getuser()
    if user:
        text = text.replace(user, "<user>")
    text = re.sub(r"/rustc(?:-dev)?/[0-9a-f]{40}/", "/<rustc-src>/", text)
    return text


def run_cmd(cmd: list[str], cwd: str, env: dict[str, str] | None = None, tmp_dir: str = "") -> dict[str, Any]:
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    return {
        "cmd": [sanitize(c, tmp_dir or cwd) for c in cmd],
        "returncode": proc.returncode,
        "stdout": sanitize(proc.stdout.strip(), tmp_dir or cwd),
        "stderr": sanitize(proc.stderr.strip(), tmp_dir or cwd),
    }


def compile_rustc_snippet(code: str, flags: list[str], filename: str = "probe.rs") -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="r11_probe_") as d:
        src = pathlib.Path(d) / filename
        src.write_text(code, encoding="utf-8")
        res = run_cmd(["rustc", str(src), "--edition=2021", *flags], cwd=d, tmp_dir=d)
        return res


def extract_llvm_fn(ll_text: str, fn_name: str) -> str:
    clean_name = fn_name.lstrip("@").rstrip("(")
    pat = re.compile(rf"^define\b[^\n]*@{re.escape(clean_name)}\(", re.MULTILINE)
    m = pat.search(ll_text)
    if not m:
        alias_pat = re.compile(
            rf"^@{re.escape(clean_name)}\s*=[^\n]*\balias\b[^\n]*",
            re.MULTILINE,
        )
        am = alias_pat.search(ll_text)
        return am.group(0) if am else ""
    start = m.start()
    end = ll_text.find("\n}\n", start)
    if end == -1:
        end = ll_text.find("\n}", start)
        if end == -1:
            return ""
        return ll_text[start : end + 2]
    return ll_text[start : end + 3]


def run_suite_a() -> dict[str, Any]:
    cases = {
        "mono_dead_pub": """pub fn mono_dead_const() -> u32 {
    if false {
        const { 1u32 / 0 }
    } else {
        0
    }
}
""",
        "mono_dead_noinline": """#[inline(never)]
pub fn mono_dead_const() -> u32 {
    if false {
        const { 1u32 / 0 }
    } else {
        0
    }
}
""",
        "mono_dead_bin": """fn mono_dead_const() -> u32 {
    if false {
        const { 1u32 / 0 }
    } else {
        0
    }
}
fn main() {
    let _ = std::hint::black_box(mono_dead_const());
}
""",
        "mono_live_pub": """pub fn mono_live_const() -> u32 {
    const { 1u32 / 0 }
}
""",
        "after_return_unreachable": """pub fn after_return() -> u32 {
    return 7;
    #[allow(unreachable_code)]
    {
        const { 1u32 / 0 }
    }
}
""",
        "generic_uninstantiated_dead": """pub fn gen_dead_const<T>() -> usize {
    if false {
        const { 1usize / (core::mem::size_of::<T>() * 0) }
    } else {
        1
    }
}
""",
        "generic_uninstantiated_live_param": """pub fn gen_live_param<T>() -> usize {
    const { 1usize / (core::mem::size_of::<T>() * 0) }
}
""",
        "generic_uninstantiated_live_nonparam": """pub fn gen_live_nonparam<T>() -> u32 {
    const { 1u32 / 0 }
}
""",
        "generic_instantiated_dead": """pub fn gen_dead_const<T>() -> usize {
    if false {
        const { 1usize / (core::mem::size_of::<T>() * 0) }
    } else {
        1
    }
}
pub fn trigger() -> usize {
    gen_dead_const::<u8>()
}
""",
        "generic_instantiated_dead_noinline": """pub fn gen_dead_const<T>() -> usize {
    if false {
        const { 1usize / (core::mem::size_of::<T>() * 0) }
    } else {
        1
    }
}
#[inline(never)]
pub fn trigger() -> usize {
    gen_dead_const::<u8>()
}
""",
        "promoted_dead_rvalue": """pub fn dead_rvalue() -> u32 {
    if false {
        let r = &(1u32 / 0);
        *r
    } else {
        0
    }
}
""",
        "promoted_dead_inline_const": """pub fn dead_inline_const_ref() -> u32 {
    if false {
        let r = &const { 1u32 / 0 };
        *r
    } else {
        0
    }
}
""",
    }

    flag_profiles: dict[str, list[str]] = {
        "emit_metadata": ["--crate-type=lib", "--emit=metadata"],
        "lib_opt0": ["--crate-type=lib", "-Copt-level=0"],
        "lib_opt2": ["--crate-type=lib", "-Copt-level=2"],
        "lib_opt2_miropt0": ["--crate-type=lib", "-Copt-level=2", "-Zmir-opt-level=0"],
    }

    out: dict[str, Any] = {}
    for name, src in cases.items():
        if name == "mono_dead_bin":
            out[name] = {
                "emit_metadata": compile_rustc_snippet(src, ["--crate-type=bin", "--emit=metadata"]),
                "bin_opt0": compile_rustc_snippet(src, ["--crate-type=bin", "-Copt-level=0"]),
                "bin_opt2": compile_rustc_snippet(src, ["--crate-type=bin", "-Copt-level=2"]),
            }
        else:
            out[name] = {
                mode: compile_rustc_snippet(src, fl) for mode, fl in flag_profiles.items()
            }
    return out


def run_suite_b() -> dict[str, Any]:
    pos_src = r"""use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);

struct HasDrop(u32);
impl Drop for HasDrop {
    fn drop(&mut self) {
        DROPS.fetch_add(1, Ordering::Relaxed);
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn promoted_const_block() -> &'static u32 {
    &const { 10 + 20 }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn promoted_empty_drop_array() -> &'static [HasDrop; 0] {
    &[]
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn promoted_const_block_empty_drop_array() -> &'static [HasDrop; 0] {
    &const { [] }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn non_promoted_cell_const_block() -> u32 {
    let r: &Cell<u32> = &const { Cell::new(5) };
    r.set(r.get() + 1);
    r.get()
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn non_promoted_drop_const_block() -> (u32, usize) {
    let before = DROPS.load(Ordering::Relaxed);
    let val = {
        let r: &HasDrop = &const { HasDrop(7) };
        r.0
    };
    let after = DROPS.load(Ordering::Relaxed);
    (val, after - before)
}

fn main() {
    let p = promoted_const_block();
    let e = promoted_empty_drop_array();
    let ec = promoted_const_block_empty_drop_array();
    let c = non_promoted_cell_const_block();
    let (dv, dcnt) = non_promoted_drop_const_block();
    println!("PROM={} EMPTY={} EMPTY_C={} CELL={} DROP_VAL={} DROPS={}", *p, e.len(), ec.len(), c, dv, dcnt);
}
"""
    pos_result: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="r11_b_pos_") as d:
        root = pathlib.Path(d)
        (root / "Cargo.toml").write_text(
            '[package]\nname = "probe_b"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (root / "src").mkdir()
        (root / "src" / "main.rs").write_text(pos_src, encoding="utf-8")

        # Native -O0 and -O2 builds + runs
        for opt in ("0", "2"):
            bin_name = f"bin_o{opt}"
            ll_name = f"out_o{opt}.ll"
            pos_result[f"rustc_opt{opt}"] = run_cmd(
                ["rustc", "src/main.rs", "--edition=2021", f"-Copt-level={opt}", "-o", bin_name],
                cwd=d,
                tmp_dir=d,
            )
            pos_result[f"native_opt{opt}"] = run_cmd([f"./{bin_name}"], cwd=d, tmp_dir=d)
            run_cmd(
                ["rustc", "src/main.rs", "--edition=2021", f"-Copt-level={opt}", "--emit=llvm-ir", "-o", ll_name],
                cwd=d,
                tmp_dir=d,
            )
            ll_txt = (root / ll_name).read_text(encoding="utf-8")
            pos_result[f"llvm_ir_opt{opt}"] = {
                fn: sanitize(extract_llvm_fn(ll_txt, fn), d)
                for fn in (
                    "promoted_const_block",
                    "promoted_empty_drop_array",
                    "promoted_const_block_empty_drop_array",
                    "non_promoted_cell_const_block",
                    "non_promoted_drop_const_block",
                )
            }

        # Dump MIR for post-cleanup and runtime-optimized
        mir_dir = root / "mir_dump"
        run_cmd(
            [
                "rustc",
                "src/main.rs",
                "--edition=2021",
                "-Copt-level=0",
                "-Zdump-mir=promoted_const_block | promoted_empty_drop_array | promoted_const_block_empty_drop_array | non_promoted_cell_const_block | non_promoted_drop_const_block",
                f"-Zdump-mir-dir={mir_dir}",
            ],
            cwd=d,
            tmp_dir=d,
        )
        mir_excerpts: dict[str, str] = {}
        for fn in (
            "promoted_const_block",
            "promoted_empty_drop_array",
            "promoted_const_block_empty_drop_array",
            "non_promoted_cell_const_block",
            "non_promoted_drop_const_block",
        ):
            for phase in ("runtime-post-cleanup.after.mir", "runtime-optimized.after.mir"):
                matches = sorted(mir_dir.glob(f"*.{fn}.*{phase}"))
                if matches:
                    mir_excerpts[f"{fn}.{phase}"] = sanitize(matches[0].read_text(encoding="utf-8"), d)
        pos_result["mir_excerpts"] = mir_excerpts

        # Miri runs (Stacked Borrows default + Tree Borrows)
        pos_result["miri_stacked_borrows"] = run_cmd(["cargo", "miri", "run"], cwd=d, tmp_dir=d)
        env_tb = {**os.environ, "MIRIFLAGS": "-Zmiri-tree-borrows"}
        pos_result["miri_tree_borrows"] = run_cmd(["cargo", "miri", "run"], cwd=d, env=env_tb, tmp_dir=d)

    neg_cases = {
        "negative_interior_mutable_cell_static": (
            "use core::cell::Cell;\npub fn bad() -> &'static Cell<u32> {\n    &const { Cell::new(5) }\n}\n"
        ),
        "negative_needs_drop_const_block_static": (
            "pub struct HasDrop(u32);\nimpl Drop for HasDrop { fn drop(&mut self) {} }\npub fn bad() -> &'static HasDrop {\n    &const { HasDrop(1) }\n}\n"
        ),
        "negative_needs_drop_rvalue_static": (
            "pub struct HasDrop(u32);\nimpl Drop for HasDrop { fn drop(&mut self) {} }\npub fn bad() -> &'static HasDrop {\n    &HasDrop(1)\n}\n"
        ),
        "negative_mut_const_block_static": (
            "pub fn bad() -> &'static mut u32 {\n    &mut const { 5u32 }\n}\n"
        ),
        "positive_mut_empty_drop_array_literal_static": (
            "pub struct HasDrop(u32);\nimpl Drop for HasDrop { fn drop(&mut self) {} }\npub fn ok() -> &'static mut [HasDrop; 0] {\n    &mut []\n}\n"
        ),
        "positive_mut_empty_drop_array_const_block_static": (
            "pub struct HasDrop(u32);\nimpl Drop for HasDrop { fn drop(&mut self) {} }\npub fn ok() -> &'static mut [HasDrop; 0] {\n    &mut const { [] }\n}\n"
        ),
    }

    neg_results = {
        name: compile_rustc_snippet(src, ["--crate-type=lib"]) for name, src in neg_cases.items()
    }

    return {"positive_and_miri": pos_result, "lifetime_promotion_matrix": neg_results}


def run_suite_c() -> dict[str, Any]:
    runtime_src = r"""#![feature(pattern_types, pattern_type_macro)]

type Small = pattern_type!(u32 is 1..=10);
type OneTwo = pattern_type!(u8 is 1..=2);
type NonZeroI8 = pattern_type!(i8 is -128..=-1 | 1..=127);

#[unsafe(no_mangle)]
pub extern "C" fn unwrap_opt_small(o: Option<Small>) -> u32 {
    match o {
        Some(v) => unsafe { core::mem::transmute(v) },
        None => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn range_check_after_small(v: Small) -> bool {
    let raw: u32 = unsafe { core::mem::transmute(v) };
    raw >= 1 && raw <= 10
}

#[unsafe(no_mangle)]
pub extern "C" fn impossible_check_after_small(v: Small) -> bool {
    let raw: u32 = unsafe { core::mem::transmute(v) };
    raw == 0 || raw == 11
}

fn main() {
    let arg = std::env::args().nth(1).unwrap_or_else(|| "ok".to_string());
    let ok: Small = unsafe { core::mem::transmute(5u32) };
    let ok_val = unwrap_opt_small(Some(ok));
    let none_val = unwrap_opt_small(None);
    let sz = core::mem::size_of::<Small>();
    let opt_sz = core::mem::size_of::<Option<Small>>();
    let opt_onetwo_sz = core::mem::size_of::<Option<OneTwo>>();
    let opt2_onetwo_sz = core::mem::size_of::<Option<Option<OneTwo>>>();
    let opt_nzi8_sz = core::mem::size_of::<Option<NonZeroI8>>();
    let in_range = range_check_after_small(ok);
    let impossible = impossible_check_after_small(ok);

    if arg == "zero" {
        let bad: Small = unsafe { core::mem::transmute(0u32) };
        std::hint::black_box(bad);
    } else if arg == "eleven" {
        let bad: Small = unsafe { core::mem::transmute(11u32) };
        std::hint::black_box(bad);
    }

    println!(
        "OK={} NONE={} SZ={} OPT_SZ={} OPT_OT={} OPT2_OT={} OPT_NZI8={} IN_RANGE={} IMPOSSIBLE={}",
        ok_val, none_val, sz, opt_sz, opt_onetwo_sz, opt2_onetwo_sz, opt_nzi8_sz, in_range, impossible
    );
}
"""
    rt_result: dict[str, Any] = {"native_runs_opt2": {}, "miri_runs": {}, "llvm_ir": {}}
    with tempfile.TemporaryDirectory(prefix="r11_c_rt_") as d:
        root = pathlib.Path(d)
        (root / "Cargo.toml").write_text(
            '[package]\nname = "probe_c"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (root / "src").mkdir()
        (root / "src" / "main.rs").write_text(runtime_src, encoding="utf-8")

        run_cmd(["rustc", "src/main.rs", "--edition=2021", "-Copt-level=2", "-o", "bin_o2"], cwd=d, tmp_dir=d)
        for arg in ("ok", "zero", "eleven"):
            rt_result["native_runs_opt2"][arg] = run_cmd(["./bin_o2", arg], cwd=d, tmp_dir=d)

        for opt in ("0", "2"):
            ll_name = f"c_o{opt}.ll"
            run_cmd(
                ["rustc", "src/main.rs", "--edition=2021", f"-Copt-level={opt}", "--emit=llvm-ir", "-o", ll_name],
                cwd=d,
                tmp_dir=d,
            )
            ll_txt = (root / ll_name).read_text(encoding="utf-8")
            rt_result["llvm_ir"][f"opt_{opt}"] = {
                fn: sanitize(extract_llvm_fn(ll_txt, f"@{fn}("), d)
                for fn in ("unwrap_opt_small", "range_check_after_small", "impossible_check_after_small")
            }

        for mode_name, miriflags in (("stacked_borrows", ""), ("tree_borrows", "-Zmiri-tree-borrows")):
            env = {**os.environ}
            if miriflags:
                env["MIRIFLAGS"] = miriflags
            for arg in ("ok", "zero", "eleven"):
                rt_result["miri_runs"][f"{mode_name}__{arg}"] = run_cmd(
                    ["cargo", "miri", "run", "--", arg], cwd=d, env=env, tmp_dir=d
                )

    compile_cases = {
        "ctfe_const_bad_zero": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub const BAD: pattern_type!(u32 is 1..=10) = unsafe { core::mem::transmute(0u32) };\n"
        ),
        "ctfe_const_bad_eleven": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub const BAD: pattern_type!(u32 is 1..=10) = unsafe { core::mem::transmute(11u32) };\n"
        ),
        "ctfe_const_bad_or_zero": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub const BAD: pattern_type!(i8 is -128..=-1 | 1..=127) = unsafe { core::mem::transmute(0i8) };\n"
        ),
        "ctfe_const_good_five": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub const GOOD: pattern_type!(u32 is 1..=10) = unsafe { core::mem::transmute(5u32) };\n"
        ),
        "exhaustiveness_empty_pat_match_unlistable": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub type EmptyPat = pattern_type!(u32 is 1..=0);\n"
            "pub fn m(x: EmptyPat) -> u32 { match x {} }\n"
        ),
        "layout_empty_pat_size_of_wrap_error": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub type EmptyPat = pattern_type!(u32 is 1..=0);\n"
            "pub const SZ: usize = core::mem::size_of::<EmptyPat>();\n"
        ),
        "exhaustiveness_wild_only_ok": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub type Small = pattern_type!(u32 is 1..=10);\n"
            "pub fn m(x: Small) -> u32 { match x { _ => 42 } }\n"
        ),
        "match_const_pat_non_structural": (
            "#![feature(pattern_types, pattern_type_macro)]\n"
            "pub type Small = pattern_type!(u32 is 1..=10);\n"
            "pub const C1: Small = unsafe { core::mem::transmute(1u32) };\n"
            "pub fn m(x: Small) -> u32 { match x { C1 => 1, _ => 0 } }\n"
        ),
        "const_generic_pat_rejected": (
            "#![feature(pattern_types, pattern_type_macro, adt_const_params)]\n"
            "pub type Small = pattern_type!(u32 is 1..=10);\n"
            "pub struct K<const X: Small>;\n"
        ),
    }
    compile_matrix = {
        name: compile_rustc_snippet(src, ["--crate-type=lib"]) for name, src in compile_cases.items()
    }
    return {"runtime_llvm_miri": rt_result, "compile_and_exhaustiveness_matrix": compile_matrix}


def main() -> int:
    support_dir = pathlib.Path(__file__).resolve().parent
    out_dir = support_dir / "probe_output"
    out_dir.mkdir(parents=True, exist_ok=True)

    rustc_ver = run_cmd(["rustc", "-Vv"], cwd=str(support_dir))["stdout"]
    miri_ver = run_cmd(["cargo", "miri", "--version"], cwd=str(support_dir))["stdout"]

    commit_match = re.search(r"commit-hash:\s*([0-9a-f]{40})", rustc_ver)
    results = {
        "rustc_version": rustc_ver,
        "rustc_commit_sha": commit_match.group(1) if commit_match else "unknown",
        "miri_version": miri_ver,
        "a_inline_const_required_consts_pme_timing": run_suite_a(),
        "b_const_block_promotion_and_lifetime_extension": run_suite_b(),
        "c_pattern_type_valtree_niche_and_unlistable": run_suite_c(),
    }
    out_file = out_dir / "probe_results.json"
    out_file.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_file} ({out_file.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
