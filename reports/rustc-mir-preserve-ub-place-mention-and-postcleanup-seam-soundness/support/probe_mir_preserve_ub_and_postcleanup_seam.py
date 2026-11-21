#!/usr/bin/env python3
"""Self-contained empirical probe for `-Zmir-preserve-ub`, `PlaceMention`,
`RemovePlaceMention`, `SimplifyCfg::PreOptimizations`, `-Zub-checks=yes`, and
`google/zerocopy` `Runtime(PostCleanup)` MIR censuses.

Runs isolated compilations and Miri executions inside a temporary directory
(assigning distinct `CARGO_TARGET_DIR` paths per `MIRIFLAGS` configuration so
Cargo never reuses stale MIR across flag changes) and emits scrubbed JSON
with relative tokens instead of local filesystem paths.
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

HERE = Path(__file__).resolve().parent


def scrub_text(text: str, replacements: list[tuple[str, str]] | None = None) -> str:
    if replacements:
        for old, new in sorted(replacements, key=lambda kv: len(kv[0]), reverse=True):
            if old:
                text = text.replace(old, new)
    text = re.sub(r"/home/[^/\s\"']+", "$HOME", text)
    text = re.sub(r"/Users/[^/\s\"']+", "$HOME", text)
    text = re.sub(r"/tmp/[^/\s\"']+", "$TMP", text)
    return text


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 180,
) -> dict:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=timeout,
    )
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout.decode("utf-8", "replace"),
        "stderr": proc.stderr.decode("utf-8", "replace"),
    }


def first_ub_line(stderr: str) -> str | None:
    for line in stderr.splitlines():
        if "Undefined Behavior:" in line:
            return line.strip()
    return None


def find_mir_file(dump_dir: Path, fn_fragment: str, pass_fragment: str) -> Path | None:
    if not dump_dir.exists():
        return None
    matches = sorted(dump_dir.glob(f"*.{fn_fragment}.*.{pass_fragment}.mir"))
    if matches:
        return matches[0]
    matches = sorted(dump_dir.glob(f"*{fn_fragment}*{pass_fragment}*.mir"))
    if matches:
        return matches[0]
    return None


def parse_switch_targets(line: str) -> list[str]:
    m = re.search(r"-> \[(.*)\]", line)
    if not m:
        return []
    targets = []
    for part in m.group(1).split(","):
        if ":" in part:
            targets.append(part.split(":", 1)[1].strip())
    return targets


def is_equal_target_switch_line(line: str) -> tuple[bool, bool]:
    """Return (all_targets_equal, is_otherwise_only) for a `switchInt` MIR line."""
    targets = parse_switch_targets(line)
    if not targets:
        return False, False
    uniq = set(targets)
    return (len(uniq) == 1), (len(targets) == 1 and "otherwise:" in line)


def analyze_mir_text(mir_text: str) -> dict:
    lines = mir_text.splitlines()
    placemention_lines = [l.strip() for l in lines if "PlaceMention(" in l]
    switch_lines = [l.strip() for l in lines if "switchInt(" in l]
    equal_target_switches = [
        l for l in switch_lines if is_equal_target_switch_line(l)[0]
    ]
    otherwise_only_switches = [
        l for l in switch_lines if is_equal_target_switch_line(l)[1]
    ]
    ubcheck_lines = [
        l.strip()
        for l in lines
        if any(
            k in l
            for k in (
                "UbChecks(",
                "assert(move",
                "is_nonnull",
                "is_aligned",
                "NullPointerDereference",
                "MisalignedPointerDereference",
            )
        )
    ]
    return {
        "placemention_count": len(placemention_lines),
        "placemention_lines": placemention_lines,
        "switchint_count": len(switch_lines),
        "switchint_lines": switch_lines,
        "equal_target_switchint_count": len(equal_target_switches),
        "equal_target_switchint_lines": equal_target_switches,
        "otherwise_only_switchint_count": len(otherwise_only_switches),
        "ubcheck_lines": ubcheck_lines,
    }


SPECIMENS: dict[str, dict] = {
    "c01_null_pair_field1_place_mention": {
        "description": "let _ = (*null_pair).1 (offset 8 inbounds pointer-arithmetic UB erased by default RemovePlaceMention, missed by -Zub-checks=yes)",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
fn check(p: *const Pair) -> u32 {
    unsafe { let _ = (*p).1; }
    42
}

fn main() {
    let r = check(core::ptr::null());
    assert_eq!(r, 42);
}
""",
        "check_native_ub_checks": True,
    },
    "c02a_null_pair_field0_place_mention": {
        "description": "let _ = (*null_pair).0 (offset 0 short-circuits in check_and_deref_ptr -> defined even with -Zmir-preserve-ub=yes)",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
fn check(p: *const Pair) -> u32 {
    unsafe { let _ = (*p).0; }
    42
}

fn main() {
    let r = check(core::ptr::null());
    assert_eq!(r, 42);
}
""",
    },
    "c02b_block_value_field0_read_control": {
        "description": "let _ = unsafe { (*null_pair).0 } (block-value syntax emits real Rvalue::Use(Copy) load, NOT pure PlaceMention)",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
fn check(p: *const Pair) -> u32 {
    let _ = unsafe { (*p).0 };
    42
}

fn main() {
    let _ = check(core::ptr::null());
}
""",
    },
    "c03_rfc2582_raw_u64_unaligned_place_mention": {
        "description": "let _ = *unaligned_raw_u64 (RFC 2582 raw place creation without read/alignment check -> defined under Miri)",
        "mir_fn": "check",
        "code": """
#[inline(never)]
#[unsafe(no_mangle)]
fn check(p: *const u64) -> u32 {
    unsafe { let _ = *p; }
    42
}

fn main() {
    let buf = [0u8; 16];
    let p = unsafe { buf.as_ptr().add(1).cast::<u64>() };
    assert_eq!(check(p), 42);
}
""",
    },
    "c04_oob_small_alloc_field1_place_mention": {
        "description": "let _ = (*one_byte_ptr).1 (offset 8 past 1-byte allocation triggers Miri inbounds UB under preserve-ub, erased under -Zmir-preserve-ub=no)",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
fn check(p: *const Pair) -> u32 {
    unsafe { let _ = (*p).1; }
    42
}

fn main() {
    let small = 7u8;
    let p = (&small as *const u8).cast::<Pair>();
    assert_eq!(check(p), 42);
}
""",
    },
    "c05a_derefer_chained_deref_inner_uninit": {
        "description": "let _ = (*(*pp)).1 with uninit *pp: Derefer (PassPolicy::Required) hoists _tmp = copy (*pp), so inner uninit UB survives RemovePlaceMention",
        "mir_fn": "check",
        "code": """
use core::mem::MaybeUninit;

#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
unsafe fn check(pp: *const *const Pair) -> u32 {
    unsafe { let _ = (*(*pp)).1; }
    42
}

fn main() {
    let slot = MaybeUninit::<*const Pair>::uninit();
    unsafe { check(slot.as_ptr()); }
}
""",
    },
    "c05b_derefer_chained_deref_inner_null": {
        "description": "let _ = (*(*pp)).1 with *pp = null: hoisted _tmp = copy (*pp) reads null cleanly, while outer PlaceMention((*_tmp).1) UB is erased under -Zmir-preserve-ub=no",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
unsafe fn check(pp: *const *const Pair) -> u32 {
    unsafe { let _ = (*(*pp)).1; }
    42
}

fn main() {
    let p: *const Pair = core::ptr::null();
    unsafe { check(&p); }
}
""",
    },
    "c06_equal_target_switchint_uninit_u8_loop": {
        "description": "match uninit_union.byte { 0 => continue, _ => continue } lowers to PlaceMention + equal-target SwitchInt -> erased under -Zmir-preserve-ub=no",
        "mir_fn": "check",
        "code": """
#[repr(C)]
union UninitU8 {
    byte: u8,
    empty: (),
}

#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    let u = UninitU8 { empty: () };
    let mut i = 0u8;
    loop {
        if i > 0 {
            return 42;
        }
        i += 1;
        unsafe {
            match u.byte {
                0 => continue,
                _ => continue,
            }
        }
    }
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
    "c07_custom_mir_pure_equal_target_switchint_zero_pm": {
        "description": "#[custom_mir] switchInt(copy uninit_u8) -> [0: bb1, otherwise: bb1] with ZERO PlaceMentions isolates SimplifyCfg::PreOptimizations preserve_switch_reads erasure",
        "mir_fn": "check",
        "code": """
#![feature(custom_mir, core_intrinsics)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    mir! {
        let x: u8;
        {
            StorageLive(x);
            match x {
                0 => bb1,
                _ => bb1,
            }
        }
        bb1 = {
            StorageDead(x);
            RET = 42;
            Return()
        }
    }
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
    "c08_mir_opt_level_help_string_mismatch": {
        "description": "Tests options.rs docstring ('implies -Zmir-opt-level=0') vs session.rs mir_opt_level() on constant-condition dead branch",
        "mir_fn": "branch_fold",
        "skip_miri": True,
        "code": """
#[inline(never)]
#[unsafe(no_mangle)]
pub fn branch_fold(x: u32) -> u32 {
    if false { x + 55 } else { x + 1 }
}

fn main() {
    let _ = branch_fold(core::hint::black_box(3));
}
""",
    },
    "c09_empty_arms_not_equal_target_switchint": {
        "description": "match uninit_u8 { 0 => (), _ => () } emits distinct empty blocks bb1/bb2 before SimplifyCfg-pre-optimizations, so switchInt survives even with -Zmir-preserve-ub=no",
        "mir_fn": "check",
        "code": """
use core::mem::MaybeUninit;

#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    let u = MaybeUninit::<u8>::uninit();
    let p = u.as_ptr();
    let _ = match unsafe { *p } {
        0 => (),
        _ => (),
    };
    42
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
    "c10_uninit_bool_switchint_erasure": {
        "description": "#[custom_mir] switchInt on uninit bool collapsing equal targets [0: bb1, otherwise: bb1] removes UB under -Zmir-preserve-ub=no",
        "mir_fn": "check",
        "code": """
#![feature(custom_mir, core_intrinsics)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "analysis", phase = "post-cleanup")]
#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    mir! {
        let b: bool;
        {
            StorageLive(b);
            match b {
                false => bb1,
                _ => bb1,
            }
        }
        bb1 = {
            StorageDead(b);
            RET = 42;
            Return()
        }
    }
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
    "c11a_dangling_safe_ref_place_mention": {
        "description": "let _ = *dangling_safe_ref at offset 0 on 1.98.0-nightly (14210df0e): PlaceMention((*_3)) is emitted and exits 0 (confirming 14210df0e eval_place lacked 3ef0c22cdb place.rs ref dereferenceability check)",
        "mir_fn": "check",
        "extra_miri_variants": [
            ("miri_no_sb_preserve_ub_yes", "-Zmiri-disable-stacked-borrows -Zmir-preserve-ub=yes -Zmir-opt-level=0"),
            ("miri_no_sb_preserve_ub_no", "-Zmiri-disable-stacked-borrows -Zmir-preserve-ub=no -Zmir-opt-level=0"),
        ],
        "code": """
#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    let raw = Box::into_raw(Box::new(7u64));
    let r: &'static u64 = unsafe { &*raw };
    unsafe { drop(Box::from_raw(raw)); }
    let _ = *r;
    42
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
    "c11b_dangling_safe_ref_field1_place_mention": {
        "description": "let _ = (*dangling_safe_ref).1 at offset 8: Miri triggers dangling pointer arithmetic UB under preserve-ub, erased by -Zmir-preserve-ub=no",
        "mir_fn": "check",
        "code": """
#[repr(C)]
struct Pair(u64, u64);

#[inline(never)]
#[unsafe(no_mangle)]
fn check() -> u32 {
    let raw = Box::into_raw(Box::new(Pair(1, 2)));
    let r: &'static Pair = unsafe { &*raw };
    unsafe { drop(Box::from_raw(raw)); }
    let _ = (*r).1;
    42
}

fn main() {
    assert_eq!(check(), 42);
}
""",
    },
}


def run_specimens(tmp_root: Path) -> dict:
    crate_dir = tmp_root / "probe_crate"
    src_dir = crate_dir / "src" / "bin"
    src_dir.mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        '[package]\nname = "preserve_ub_probe"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )

    for name, spec in SPECIMENS.items():
        (src_dir / f"{name}.rs").write_text(spec["code"].lstrip(), encoding="utf-8")

    # Pre-fetch / warm Cargo metadata check cleanly inside empty workspace
    replacements = [(str(tmp_root), "$TMP_PROBE")]

    results: dict[str, dict] = {}
    env_base = dict(os.environ)

    target_miri_def = tmp_root / "target_miri_def"
    target_miri_npub = tmp_root / "target_miri_npub"

    for idx, (name, spec) in enumerate(SPECIMENS.items(), start=1):
        rs_path = src_dir / f"{name}.rs"
        fn_frag = spec["mir_fn"]
        entry: dict = {
            "description": spec["description"],
        }

        # 1. MIR comparison: default vs -Zmir-preserve-ub=yes -Zmir-opt-level=0
        mir_cases: dict[str, dict] = {}
        for mode_name, extra_flags in [
            ("default_postcleanup", []),
            ("preserve_ub_opt0", ["-Zmir-preserve-ub=yes", "-Zmir-opt-level=0"]),
            ("preserve_ub_alone", ["-Zmir-preserve-ub=yes"]),
        ]:
            dump_dir = tmp_root / f"mir_{name}_{mode_name}"
            dump_dir.mkdir(parents=True, exist_ok=True)
            out_rlib = tmp_root / f"{name}_{mode_name}.mir"
            cmd = [
                "rustc",
                "--edition",
                "2024",
                "--emit=mir",
                "-o",
                str(out_rlib),
                f"-Zdump-mir={fn_frag}",
                f"-Zdump-mir-dir={dump_dir}",
            ] + extra_flags + [str(rs_path)]
            res = run_cmd(cmd, cwd=tmp_root, env=env_base)
            runtime_init = find_mir_file(dump_dir, fn_frag, "runtime.after")
            pre_opt = find_mir_file(dump_dir, fn_frag, "SimplifyCfg-pre-optimizations.after")
            post_cleanup = find_mir_file(dump_dir, fn_frag, "runtime-post-cleanup.after")
            opt_final = find_mir_file(dump_dir, fn_frag, "runtime-optimized.after")
            derefer_after = find_mir_file(dump_dir, fn_frag, "Derefer.after")
            before_rpm = find_mir_file(dump_dir, fn_frag, "RemovePlaceMention.before")
            mode_info = {
                "compile_rc": res["returncode"],
                "runtime_initial": analyze_mir_text(runtime_init.read_text("utf-8"))
                if runtime_init
                else None,
                "derefer_after": analyze_mir_text(derefer_after.read_text("utf-8"))
                if derefer_after
                else None,
                "pre_optimizations_after": analyze_mir_text(pre_opt.read_text("utf-8"))
                if pre_opt
                else None,
                "runtime_post_cleanup": analyze_mir_text(post_cleanup.read_text("utf-8"))
                if post_cleanup
                else None,
                "remove_place_mention_before": analyze_mir_text(before_rpm.read_text("utf-8"))
                if before_rpm
                else None,
                "runtime_optimized_after": analyze_mir_text(opt_final.read_text("utf-8"))
                if opt_final
                else None,
            }
            if out_rlib.exists():
                out_rlib.unlink()
            shutil.rmtree(dump_dir, ignore_errors=True)
            mir_cases[mode_name] = mode_info

        entry["mir"] = mir_cases

        if not spec.get("skip_miri"):
            # 2. Miri default (-Zmir-preserve-ub=yes -Zmir-opt-level=0 implied by MIRI_DEFAULT_ARGS)
            env_def = dict(env_base, CARGO_TARGET_DIR=str(target_miri_def))
            env_def.pop("MIRIFLAGS", None)
            r_def = run_cmd(
                ["cargo", "miri", "run", "--quiet", "--bin", name],
                cwd=crate_dir,
                env=env_def,
            )
            entry["miri_default"] = {
                "returncode": r_def["returncode"],
                "ub_summary": first_ub_line(r_def["stderr"]),
                "stderr_scrubbed": scrub_text(r_def["stderr"], replacements),
            }

            # 3. Miri -Zmir-preserve-ub=no -Zmir-opt-level=0 (isolated CARGO_TARGET_DIR!)
            env_npub = dict(
                env_base,
                CARGO_TARGET_DIR=str(target_miri_npub),
                MIRIFLAGS="-Zmir-preserve-ub=no -Zmir-opt-level=0",
            )
            r_npub = run_cmd(
                ["cargo", "miri", "run", "--quiet", "--bin", name],
                cwd=crate_dir,
                env=env_npub,
            )
            entry["miri_no_preserve_ub_opt0"] = {
                "returncode": r_npub["returncode"],
                "ub_summary": first_ub_line(r_npub["stderr"]),
                "stderr_scrubbed": scrub_text(r_npub["stderr"], replacements),
            }

        for var_idx, (var_name, mflags) in enumerate(spec.get("extra_miri_variants", []), start=1):
            tdir = tmp_root / f"target_miri_var_{var_name}"
            env_var = dict(env_base, CARGO_TARGET_DIR=str(tdir), MIRIFLAGS=mflags)
            r_var = run_cmd(
                ["cargo", "miri", "run", "--quiet", "--bin", name],
                cwd=crate_dir,
                env=env_var,
            )
            entry[var_name] = {
                "miriflags": mflags,
                "returncode": r_var["returncode"],
                "ub_summary": first_ub_line(r_var["stderr"]),
                "stderr_scrubbed": scrub_text(r_var["stderr"], replacements),
            }

        # 4. Native -Zub-checks=yes test if requested
        if spec.get("check_native_ub_checks"):
            native_modes: dict[str, dict] = {}
            for mname, flags in [
                ("ub_checks_default", ["-Zub-checks=yes"]),
                ("ub_checks_preserve_ub_opt0", ["-Zub-checks=yes", "-Zmir-preserve-ub=yes", "-Zmir-opt-level=0"]),
            ]:
                bin_path = tmp_root / f"{name}_{mname}"
                ddir = tmp_root / f"mir_ubchk_{name}_{mname}"
                ddir.mkdir(parents=True, exist_ok=True)
                comp = run_cmd(
                    [
                        "rustc",
                        "--edition",
                        "2024",
                        "-o",
                        str(bin_path),
                        f"-Zdump-mir={fn_frag}",
                        f"-Zdump-mir-dir={ddir}",
                    ]
                    + flags
                    + [str(rs_path)],
                    cwd=tmp_root,
                    env=env_base,
                )
                chk_null = find_mir_file(ddir, fn_frag, "CheckNull.after")
                chk_align = find_mir_file(ddir, fn_frag, "CheckAlignment.after")
                run_res = run_cmd([str(bin_path)], cwd=tmp_root, env=env_base) if comp["returncode"] == 0 else None
                native_modes[mname] = {
                    "compile_rc": comp["returncode"],
                    "exec_rc": run_res["returncode"] if run_res else None,
                    "check_null_ubchecks": analyze_mir_text(chk_null.read_text("utf-8")) if chk_null else None,
                    "check_alignment_ubchecks": analyze_mir_text(chk_align.read_text("utf-8")) if chk_align else None,
                }
                if bin_path.exists():
                    bin_path.unlink()
                shutil.rmtree(ddir, ignore_errors=True)
            entry["native_ub_checks"] = native_modes

        results[name] = entry

    return results


def classify_placemention_line(stmt_line: str) -> str:
    if "*" in stmt_line:
        return "deref"
    if "[" in stmt_line:
        return "index"
    if "." in stmt_line or " as " in stmt_line:
        return "field_or_cast"
    return "plain_local"


def run_zerocopy_census(zerocopy_dir: Path, tmp_root: Path) -> dict:
    census: dict = {}
    env_base = dict(os.environ)
    feature_configs = [
        ("default_features", []),
        ("no_default_features", ["--no-default-features"]),
        ("all_features", ["--all-features"]),
    ]

    for cfg_name, cargo_flags in feature_configs:
        target_dir = tmp_root / f"zc_target_{cfg_name}"
        cfg_data: dict = {}
        for mode_name, extra_args in [
            ("default", []),
            ("preserve_ub_opt0", ["-Zmir-preserve-ub=yes", "-Zmir-opt-level=0"]),
        ]:
            mir_dir = tmp_root / f"zc_mir_{cfg_name}_{mode_name}"
            if mir_dir.exists():
                shutil.rmtree(mir_dir)
            mir_dir.mkdir(parents=True, exist_ok=True)
            # Clean only the `zerocopy` crate between flag modes while keeping
            # compiled proc-macro dependencies (`zerocopy-derive`, etc.) cached.
            run_cmd(
                ["cargo", "clean", "-p", "zerocopy"],
                cwd=zerocopy_dir,
                env=dict(env_base, CARGO_TARGET_DIR=str(target_dir)),
                timeout=60,
            )
            env = dict(env_base, CARGO_TARGET_DIR=str(target_dir))
            rustc_after_args = [
                "--emit=metadata",
                "-Zdump-mir=SimplifyCfg-pre-optimizations",
                f"-Zdump-mir-dir={mir_dir}",
            ] + extra_args
            print(f"[zerocopy] {cfg_name} / {mode_name}...", file=sys.stderr, flush=True)
            res = run_cmd(
                ["cargo", "rustc", "--lib"] + cargo_flags + ["--"] + rustc_after_args,
                cwd=zerocopy_dir,
                env=env,
                timeout=300,
            )
            if res["returncode"] != 0:
                cfg_data[mode_name] = {
                    "compile_rc": res["returncode"],
                    "stderr_scrubbed": scrub_text(res["stderr"][:2000], [(str(zerocopy_dir), "$ZEROCOPY_ROOT")]),
                }
                shutil.rmtree(mir_dir, ignore_errors=True)
                continue

            # Summarize dumped runtime-post-cleanup MIR bodies
            post_files = sorted(
                mir_dir.glob("*SimplifyCfg-pre-optimizations.after.mir")
            )
            pm_total = 0
            pm_bodies = 0
            pm_deref = 0
            pm_deref_with_field = 0
            pm_index = 0
            pm_plain_local = 0
            pm_field_or_cast = 0
            sw_total = 0
            sw_eq_total = 0
            sw_eq_bodies = 0
            sw_otherwise_only = 0
            top_pm_bodies: list[tuple[int, str]] = []
            sample_deref_pms: list[dict] = []
            sample_eq_switches: list[dict] = []

            for f in post_files:
                txt = f.read_text("utf-8", errors="replace")
                fn_name = f.name.split(".SimplifyCfg-pre-optimizations")[0]
                pms = [l.strip() for l in txt.splitlines() if "PlaceMention(" in l]
                sws = [l.strip() for l in txt.splitlines() if "switchInt(" in l]
                if pms:
                    pm_bodies += 1
                    pm_total += len(pms)
                    top_pm_bodies.append((len(pms), fn_name))
                    for l in pms:
                        cls = classify_placemention_line(l)
                        if cls == "deref":
                            pm_deref += 1
                            if "." in l:
                                pm_deref_with_field += 1
                            if len(sample_deref_pms) < 20:
                                sample_deref_pms.append({"fn": fn_name, "stmt": l})
                        elif cls == "index":
                            pm_index += 1
                        elif cls == "field_or_cast":
                            pm_field_or_cast += 1
                        else:
                            pm_plain_local += 1
                sw_total += len(sws)
                eq_here = [l for l in sws if is_equal_target_switch_line(l)[0]]
                oth_here = [l for l in sws if is_equal_target_switch_line(l)[1]]
                if eq_here:
                    sw_eq_bodies += 1
                    sw_eq_total += len(eq_here)
                    for l in eq_here:
                        if len(sample_eq_switches) < 12:
                            sample_eq_switches.append({"fn": fn_name, "term": l})
                sw_otherwise_only += len(oth_here)

            top_pm_bodies.sort(reverse=True)
            cfg_data[mode_name] = {
                "compile_rc": 0,
                "postcleanup_bodies": len(post_files),
                "placemention_total": pm_total,
                "placemention_bodies": pm_bodies,
                "placemention_breakdown": {
                    "deref": pm_deref,
                    "deref_with_field": pm_deref_with_field,
                    "index": pm_index,
                    "field_or_cast": pm_field_or_cast,
                    "plain_local": pm_plain_local,
                },
                "switchint_total": sw_total,
                "equal_target_switchint_total": sw_eq_total,
                "equal_target_switchint_bodies": sw_eq_bodies,
                "otherwise_only_switchint_total": sw_otherwise_only,
                "top_placemention_bodies": [
                    {"fn": fn, "count": cnt} for cnt, fn in top_pm_bodies[:10]
                ],
                "sample_deref_placementions": sample_deref_pms,
                "sample_equal_target_switches": sample_eq_switches,
            }
            shutil.rmtree(mir_dir, ignore_errors=True)
        shutil.rmtree(target_dir, ignore_errors=True)
        census[cfg_name] = cfg_data

    return census


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=str(HERE / "probe_results.json"))
    ap.add_argument(
        "--zerocopy-dir",
        default="",
        help="Optional path to a local google/zerocopy checkout for live Rust/MIR census",
    )
    args = ap.parse_args()

    cargo_bin = Path.home() / ".cargo" / "bin"
    if cargo_bin.is_dir() and str(cargo_bin) not in os.environ.get("PATH", "").split(os.pathsep):
        os.environ["PATH"] = f"{cargo_bin}{os.pathsep}{os.environ.get('PATH', '')}"

    rustc_ver = run_cmd(["rustc", "-Vv"])["stdout"].strip()
    miri_ver = run_cmd(["cargo", "miri", "--version"])["stdout"].strip()

    with tempfile.TemporaryDirectory(prefix="mir_preserve_ub_probe_") as tmp_str:
        tmp_root = Path(tmp_str)
        specimens_data = run_specimens(tmp_root)
        zc_data = None
        if args.zerocopy_dir:
            zc_path = Path(args.zerocopy_dir).resolve()
            if (zc_path / "Cargo.toml").exists():
                zc_data = run_zerocopy_census(zc_path, tmp_root)

    payload = {
        "schema": "mir-preserve-ub-probe/1",
        "observed_on": datetime.date.today().isoformat(),
        "rustc_version": scrub_text(rustc_ver),
        "miri_version": scrub_text(miri_ver),
        "specimens": specimens_data,
        "zerocopy_live_census": zc_data,
    }
    Path(args.out).write_text(
        json.dumps(payload, indent=1, sort_keys=False) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {args.out} ({len(specimens_data)} specimens)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
