#!/usr/bin/env python3
"""Live rustc and Miri differential probe for phase-transition MIR desugarings:
1. Derefer + EraseDerefTemps (CopyForDeref -> Rvalue::Use(_, WithRetag::No))
2. Custom MIR aliasing discriminator: WithRetag::No vs WithRetag::Yes under
   Miri Stacked Borrows and Tree Borrows
3. Subtyper (CastKind::Subtype insertion after region erasure & anonymization)
   plus -Zvalidate-mir pass-disabling checks
4. Visibility-scoped uninhabited call-return target pruning (is_inhabited_from)
   and borrowck definite-initialization (E0381) gate

All results are produced strictly from live rustc / cargo miri invocations;
no measurements are hardcoded.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

RUSTC_DEV_RE = re.compile(r"/" + r"rustc-dev/[0-9a-f]{40}/")
HOME_RE = re.compile(re.escape(str(Path.home())))
TMP_WS_RE = re.compile(r"/tmp/[A-Za-z0-9_.-]+")


def sanitize_text(text: str, workdir: Path) -> str:
    """Strip host-specific paths and build-host compiler source prefixes."""
    out = RUSTC_DEV_RE.sub("<rustc-src>/", text)
    out = out.replace(str(workdir), "<probe-dir>")
    out = HOME_RE.sub("<home>", out)
    out = TMP_WS_RE.sub("<tmp>", out)
    return out


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env_extra: dict[str, str] | None = None,
    timeout: int = 120,
) -> tuple[int, str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in env.get("PATH", ""):
        env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    env["RUSTC_ICE"] = "0"
    if env_extra:
        env.update(env_extra)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


def read_glob_first(directory: Path, pattern: str) -> str:
    matches = sorted(directory.glob(pattern))
    if not matches:
        return ""
    return matches[0].read_text(encoding="utf-8", errors="replace")


def count_nested_deref_in_body(mir_text: str) -> int:
    """Count occurrences of nested `(*(*` in MIR statements/terminators (outside debug info)."""
    count = 0
    for line in mir_text.splitlines():
        stripped = line.strip()
        if stripped.startswith("debug ") or stripped.startswith("//"):
            continue
        if "(*(*" in stripped:
            count += 1
    return count


def probe_derefer_and_miri_retag(workdir: Path) -> dict:
    crate_dir = workdir / "derefer_miri"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "derefer_miri"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )

    src_rs = r"""#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::mir::*;

#[inline(never)]
fn nested_mut_raw_split(pp: &mut &mut (u32, u32)) -> u32 {
    unsafe {
        let p0: *mut u32 = &raw mut (*(*pp)).0;
        *p0 = 11;
        let p1: *mut u32 = &raw mut (*(*pp)).1;
        *p1 = 22;
        *p0 = *p0 + *p1;
        *p0
    }
}

#[inline(never)]
fn nested_mut_triple_deref(ppp: &mut &mut &mut (u32, u32)) -> u32 {
    (*(*(*ppp))).0 += 5;
    (*(*(*ppp))).1 += 7;
    (*(*(*ppp))).0 + (*(*(*ppp))).1
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
unsafe fn custom_with_retag_yes(pp: &mut &mut (u32, u32)) -> u32 {
    mir! {
        let t1: &mut (u32, u32);
        let t2: &mut (u32, u32);
        let p0: *mut u32;
        let p1: *mut u32;
        let v0: u32;
        let v1: u32;
        {
            t1 = *pp;
            p0 = &raw mut (*t1).0;
            (*p0) = 11_u32;
            t2 = *pp;
            p1 = &raw mut (*t2).1;
            (*p1) = 22_u32;
            v0 = *p0;
            v1 = *p1;
            (*p0) = v0 + v1;
            RET = *p0;
            Return()
        }
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "no-retag".to_string());
    if mode == "no-retag" {
        let mut tup = (1u32, 2u32);
        let mut r = &mut tup;
        let split_res = nested_mut_raw_split(&mut r);
        let mut tup3 = (10u32, 20u32);
        let mut r1 = &mut tup3;
        let mut r2 = &mut r1;
        let triple_res = nested_mut_triple_deref(&mut r2);
        println!("NESTED_MUT_DEREF={split_res} TRIPLE_DEREF={triple_res}");
    } else {
        let mut tup2 = (1u32, 2u32);
        let mut r2 = &mut tup2;
        let res = unsafe { custom_with_retag_yes(&mut r2) };
        println!("RETAG_YES={res}");
    }
}
"""
    main_rs = crate_dir / "src" / "main.rs"
    main_rs.write_text(src_rs, encoding="utf-8")

    mir_dir = workdir / "mir_derefer"
    bin_path = workdir / "bin_derefer"
    compile_rc, _, compile_err = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "-Zvalidate-mir",
            "-Zdump-mir=nested_mut_raw_split|nested_mut_triple_deref|custom_with_retag_yes",
            f"-Zdump-mir-dir={mir_dir}",
            str(main_rs),
            "-o",
            str(bin_path),
        ]
    )

    native_rc, native_out, _ = run_cmd([str(bin_path), "no-retag"]) if compile_rc == 0 else (-1, "", "")

    # Inspect MIR counts for both nested_mut_raw_split and nested_mut_triple_deref
    split_before = read_glob_first(mir_dir, "*nested_mut_raw_split*Derefer.before.mir")
    split_derefer = read_glob_first(mir_dir, "*nested_mut_raw_split*Derefer.after.mir")
    split_erase = read_glob_first(mir_dir, "*nested_mut_raw_split*EraseDerefTemps.after.mir")
    split_post = read_glob_first(mir_dir, "*nested_mut_raw_split*runtime-post-cleanup.after.mir")

    triple_before = read_glob_first(mir_dir, "*nested_mut_triple_deref*Derefer.before.mir")
    triple_derefer = read_glob_first(mir_dir, "*nested_mut_triple_deref*Derefer.after.mir")
    triple_erase = read_glob_first(mir_dir, "*nested_mut_triple_deref*EraseDerefTemps.after.mir")

    custom_post = read_glob_first(mir_dir, "*custom_with_retag_yes*runtime-post-cleanup.after.mir")

    # Run Miri Stacked Borrows & Tree Borrows on no-retag and retag-yes
    sb_no_rc, sb_no_out, sb_no_err = run_cmd(
        ["cargo", "miri", "run", "--quiet", "--", "no-retag"], cwd=crate_dir
    )
    tb_no_rc, tb_no_out, tb_no_err = run_cmd(
        ["cargo", "miri", "run", "--quiet", "--", "no-retag"],
        cwd=crate_dir,
        env_extra={"MIRIFLAGS": "-Zmiri-tree-borrows"},
    )
    sb_yes_rc, sb_yes_out, sb_yes_err = run_cmd(
        ["cargo", "miri", "run", "--quiet", "--", "retag-yes"], cwd=crate_dir
    )
    tb_yes_rc, tb_yes_out, tb_yes_err = run_cmd(
        ["cargo", "miri", "run", "--quiet", "--", "retag-yes"],
        cwd=crate_dir,
        env_extra={"MIRIFLAGS": "-Zmiri-tree-borrows"},
    )

    def extract_ub_lines(stderr: str) -> list[str]:
        lines = []
        for ln in sanitize_text(stderr, workdir).splitlines():
            s = ln.strip()
            if s.startswith("error: Undefined Behavior:") or s.startswith("help:") or s.startswith("= help: the accessed tag"):
                lines.append(s)
        return lines

    def extract_assign_lines(mir_text: str, needle: str) -> list[str]:
        return [ln.strip() for ln in mir_text.splitlines() if needle in ln]

    return {
        "compile_rc": compile_rc,
        "compile_stderr_excerpt": sanitize_text(compile_err, workdir).splitlines()[:10],
        "native_rc": native_rc,
        "native_stdout": native_out.strip(),
        "nested_mut_raw_split": {
            "nested_deref_before_derefer": count_nested_deref_in_body(split_before),
            "nested_deref_after_derefer": count_nested_deref_in_body(split_derefer),
            "deref_copy_after_derefer": split_derefer.count("deref_copy "),
            "deref_copy_after_erase": split_erase.count("deref_copy "),
            "no_retag_copy_after_erase": split_erase.count("no_retag copy "),
            "no_retag_copy_in_runtime_post_cleanup": split_post.count("no_retag copy "),
            "deref_copy_lines": extract_assign_lines(split_derefer, "deref_copy "),
            "no_retag_lines": extract_assign_lines(split_erase, "no_retag copy "),
        },
        "nested_mut_triple_deref": {
            "nested_deref_before_derefer": count_nested_deref_in_body(triple_before),
            "nested_deref_after_derefer": count_nested_deref_in_body(triple_derefer),
            "deref_copy_after_derefer": triple_derefer.count("deref_copy "),
            "deref_copy_after_erase": triple_erase.count("deref_copy "),
            "no_retag_copy_after_erase": triple_erase.count("no_retag copy "),
            "deref_copy_lines": extract_assign_lines(triple_derefer, "deref_copy "),
            "no_retag_lines": extract_assign_lines(triple_erase, "no_retag copy "),
        },
        "custom_with_retag_yes_mir_excerpt": [
            ln.strip() for ln in custom_post.splitlines() if "copy (*_1)" in ln or "&raw mut" in ln
        ],
        "miri_with_retag_no": {
            "stacked_borrows_rc": sb_no_rc,
            "stacked_borrows_stdout": sb_no_out.strip(),
            "tree_borrows_rc": tb_no_rc,
            "tree_borrows_stdout": tb_no_out.strip(),
        },
        "miri_with_retag_yes_counterexample": {
            "stacked_borrows_rc": sb_yes_rc,
            "stacked_borrows_ub_lines": extract_ub_lines(sb_yes_err),
            "tree_borrows_rc": tb_yes_rc,
            "tree_borrows_ub_lines": extract_ub_lines(tb_yes_err),
        },
    }


def probe_subtyper_and_validator(workdir: Path) -> dict:
    crate_dir = workdir / "subtyper_miri"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "subtyper_miri"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )

    src_rs = r"""use core::any::TypeId;

#[inline(never)]
fn id_ref<'a>(x: &'a u8) -> &'a u8 {
    x
}

#[inline(never)]
fn hrtb_tuple_coerce(v: &'static u8) -> (u8, u32) {
    let f: for<'a> fn(&'a u8) -> &'a u8 = id_ref;
    let pair: (fn(&'static u8) -> &'static u8, u32) = (f, 7);
    (*pair.0(v), pair.1)
}

#[inline(never)]
fn hrtb_binder_collapse(a: &u8, b: &u8) -> u8 {
    fn first<'a, 'b>(x: &'a u8, _y: &'b u8) -> &'a u8 {
        x
    }
    let f: for<'a, 'b> fn(&'a u8, &'b u8) -> &'a u8 = first;
    let g: for<'c> fn(&'c u8, &'c u8) -> &'c u8 = f;
    *g(a, b)
}

#[inline(never)]
fn id_of<T: 'static>(_x: T) -> TypeId {
    TypeId::of::<T>()
}

#[inline(never)]
fn hrtb_typeid_split(f: for<'a> fn(&'a u8) -> &'a u8) -> bool {
    let g: fn(&'static u8) -> &'static u8 = f;
    id_of(f) != id_of(g)
}

#[inline(never)]
fn plain_region_variance<'a>(x: &'static u8) -> &'a u8 {
    let y: &'a u8 = x;
    y
}

fn main() {
    static V: u8 = 99;
    let (out, k) = hrtb_tuple_coerce(&V);
    let col = hrtb_binder_collapse(&V, &V);
    let tid_diff = hrtb_typeid_split(id_ref);
    let var = *plain_region_variance(&V);
    println!("SUBTYPER={out} K={k} COLLAPSE={col} TYPEID_DIFF={tid_diff} VAR={var}");
}
"""
    main_rs = crate_dir / "src" / "main.rs"
    main_rs.write_text(src_rs, encoding="utf-8")

    mir_dir = workdir / "mir_subtyper"
    bin_path = workdir / "bin_subtyper"
    compile_rc, _, compile_err = run_cmd(
        [
            "rustc",
            "--edition=2024",
            "-Zvalidate-mir",
            "-Zdump-mir=hrtb_tuple_coerce|hrtb_binder_collapse|hrtb_typeid_split|plain_region_variance",
            f"-Zdump-mir-dir={mir_dir}",
            str(main_rs),
            "-o",
            str(bin_path),
        ]
    )

    native_rc, native_out, _ = run_cmd([str(bin_path)]) if compile_rc == 0 else (-1, "", "")
    miri_rc, miri_out, _ = run_cmd(["cargo", "miri", "run", "--quiet"], cwd=crate_dir)

    fn_stats = {}
    for fn_name in [
        "hrtb_tuple_coerce",
        "hrtb_binder_collapse",
        "hrtb_typeid_split",
        "plain_region_variance",
    ]:
        pre = read_glob_first(mir_dir, f"*.{fn_name}.*analysis-post-cleanup.after.mir")
        sub_after = read_glob_first(mir_dir, f"*.{fn_name}.*Subtyper.after.mir")
        rt_post = read_glob_first(mir_dir, f"*.{fn_name}.*runtime-post-cleanup.after.mir")
        subtype_lines = [ln.strip() for ln in sub_after.splitlines() if "(Subtype);" in ln]
        fn_stats[fn_name] = {
            "subtype_cast_in_analysis_post_cleanup": pre.count("(Subtype);"),
            "subtype_cast_in_subtyper_after": sub_after.count("(Subtype);"),
            "subtype_cast_in_runtime_post_cleanup": rt_post.count("(Subtype);"),
            "subtype_cast_lines": subtype_lines,
        }

    # Test -Zvalidate-mir when disabling passes via -Zmir-enable-passes (1.98.0-nightly pre-PassPolicy::Required behavior)
    dis_results = {}
    for pass_name in ["Derefer", "EraseDerefTemps", "Subtyper"]:
        out_bin = workdir / f"bin_dis_{pass_name}"
        rc, _, err = run_cmd(
            [
                "rustc",
                "--edition=2024",
                "-Zvalidate-mir",
                f"-Zmir-enable-passes=-{pass_name}",
                str(main_rs),
                "-o",
                str(out_bin),
            ]
        )
        sanitized_lines = sanitize_text(err, workdir).splitlines()
        ice_excerpt = [ln for ln in sanitized_lines if "broken MIR" in ln or "has deref as a later" in ln or "CopyForDeref" in ln or "DerefTemp" in ln or "incompatible types" in ln][:4]
        dis_results[f"disable_{pass_name}"] = {
            "rc": rc,
            "validate_mir_rejected": rc != 0,
            "diagnostic_excerpt": ice_excerpt,
        }

    return {
        "compile_rc": compile_rc,
        "native_rc": native_rc,
        "native_stdout": native_out.strip(),
        "miri_rc": miri_rc,
        "miri_stdout": miri_out.strip(),
        "functions": fn_stats,
        "disable_pass_under_validate_mir": dis_results,
    }


def probe_visibly_uninhabited(workdir: Path) -> dict:
    uninh_dir = workdir / "uninhabited"
    uninh_dir.mkdir(parents=True, exist_ok=True)

    cases_src = {
        "visibly_uninhabited_pub_void": (
            "use_pub_void",
            r"""pub mod m {
    pub enum PublicVoid {}
    #[inline(never)]
    pub fn make_pub_void() -> PublicVoid {
        loop {}
    }
}

pub fn use_pub_void() -> u32 {
    let x: u32;
    m::make_pub_void();
    x
}

fn main() {}
""",
        ),
        "privately_uninhabited_outside_mod": (
            "use_priv_void_outside",
            r"""pub mod m {
    enum PrivateVoid {}
    pub struct OpaqueUninhabited(PrivateVoid);
    #[inline(never)]
    pub fn make_priv_void() -> OpaqueUninhabited {
        loop {}
    }
}

pub fn use_priv_void_outside() -> u32 {
    let x: u32;
    m::make_priv_void();
    x
}

fn main() {}
""",
        ),
        "privately_uninhabited_inside_mod_and_child": (
            "use_inside_",
            r"""pub mod m {
    enum PrivateVoid {}
    pub struct OpaqueUninhabited(PrivateVoid);
    #[inline(never)]
    pub fn make_priv_void() -> OpaqueUninhabited {
        loop {}
    }

    pub fn use_inside_mod() -> u32 {
        let x: u32;
        make_priv_void();
        x
    }

    pub mod child {
        pub fn use_inside_child() -> u32 {
            let x: u32;
            super::make_priv_void();
            x
        }
    }
}

fn main() {}
""",
        ),
        "opsem_uninhabited_but_visibility_inhabited_ref": (
            "use_ref_void",
            r"""pub enum PublicVoid {}
#[inline(never)]
pub fn make_ref_void() -> &'static PublicVoid {
    loop {}
}

pub fn use_ref_void() -> u32 {
    let x: u32;
    make_ref_void();
    x
}

fn main() {}
""",
        ),
        "enclosing_uninhabited_return_lint_suppression": (
            "outer_uninh",
            r"""pub enum PublicVoid {}
#[inline(never)]
pub fn make_pub_void() -> PublicVoid {
    loop {}
}

pub fn outer_uninh() -> PublicVoid {
    let x: u32;
    make_pub_void();
    let _ = x;
    loop {}
}

fn main() {}
""",
        ),
    }

    results = {}
    for name, (dump_filter, code) in cases_src.items():
        rs_path = uninh_dir / f"{name}.rs"
        rs_path.write_text(code, encoding="utf-8")
        mir_dir = uninh_dir / f"mir_{name}"
        bin_path = uninh_dir / f"bin_{name}"
        rc, _, err = run_cmd(
            [
                "rustc",
                "--edition=2024",
                f"-Zdump-mir={dump_filter}",
                f"-Zdump-mir-dir={mir_dir}",
                str(rs_path),
                "-o",
                str(bin_path),
            ]
        )
        sanitized_err = sanitize_text(err, workdir)
        warnings = [ln.strip() for ln in sanitized_err.splitlines() if ln.startswith("warning:")]
        errors = [ln.strip() for ln in sanitized_err.splitlines() if ln.startswith("error")]

        call_terminators = []
        for mir_file in sorted(mir_dir.glob("*.built.after.mir")):
            for ln in mir_file.read_text(encoding="utf-8", errors="replace").splitlines():
                if "make_" in ln and "->" in ln:
                    call_terminators.append(ln.strip())

        has_return_edge = any("[return:" in t for t in call_terminators)
        results[name] = {
            "rc": rc,
            "warnings": warnings,
            "errors": errors,
            "built_after_call_terminators": call_terminators,
            "call_has_return_target": has_return_edge,
        }

    return results


def main() -> int:
    out_path = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    with tempfile.TemporaryDirectory(prefix="probe_deref_sub_uninh_") as tmp:
        workdir = Path(tmp)
        _, rustc_ver, _ = run_cmd(["rustc", "--version", "--verbose"])
        _, miri_ver, _ = run_cmd(["cargo", "miri", "--version"])
        payload = {
            "rustc_version": rustc_ver.strip(),
            "miri_version": miri_ver.strip(),
            "cases": {
                "derefer_and_erase_deref_temps": probe_derefer_and_miri_retag(workdir),
                "subtyper_hrtb_cast": probe_subtyper_and_validator(workdir),
                "lint_and_remove_uninhabited_visibility_split": probe_visibly_uninhabited(workdir),
            },
        }
    encoded = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    if out_path is not None:
        out_path.write_text(encoded, encoding="utf-8")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
