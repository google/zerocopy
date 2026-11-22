#!/usr/bin/env python3
"""Empirical rustc + Miri probe for:
  1. `ergonomic_clones` (`x.use`, `use ||`, `UseCloned`) operational divergence
     between `Runtime(PostCleanup)` / `optimized_mir` (Miri Stacked & Tree
     Borrows) and `rustc_codegen_ssa::mir::optimize_use_clone` (native binaries
     at `-C opt-level=0 -Z mir-opt-level=0`, `-C opt-level=0`, and `-O`).
  2. `TerminatorKind::Call { unwind: UnwindAction::Unreachable, call_source: CallSource::Use }`
     safe-code panic/unwind behavior across Miri vs. native codegen (`-C opt-level=0`
     and `-O`).
  3. Edition 2021 vs. Edition 2024 RPIT lifetime-capture defaults (`E0597`),
     precise capturing `use<...>` (`ParamNotCaptured`, `LifetimeNotCaptured`,
     `LifetimesMustBeFirst`, `DuplicatePreciseCapture`, invariant variance),
     non-`UseCloned` `.use` move semantics (`E0382`), and opaque hidden-type
     generic-parameter injectivity (`E0792`).

All outputs are captured live from invoking `rustc`, compiled native binaries,
and `cargo miri`. Zero results are hardcoded.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


PART_A_SOURCE = r'''#![forbid(unsafe_code)]
#![feature(ergonomic_clones)]

use std::clone::UseCloned;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

static CLONE_CALLS: AtomicUsize = AtomicUsize::new(0);

#[derive(Copy, Debug, Eq, PartialEq)]
struct SneakyCopy(u32);

impl Clone for SneakyCopy {
    fn clone(&self) -> Self {
        CLONE_CALLS.fetch_add(1, Ordering::SeqCst);
        SneakyCopy(self.0 + 100)
    }
}

impl UseCloned for SneakyCopy {}

#[inline(never)]
fn generic_dup<T: UseCloned>(x: T) -> (T, T) {
    (x.use, x)
}

#[inline(never)]
fn generic_closure_dup<T: UseCloned>(x: T) -> (T, T) {
    let f = use || x;
    (f(), x)
}

#[inline(never)]
fn concrete_dup(x: SneakyCopy) -> (SneakyCopy, SneakyCopy) {
    (x.use, x)
}

#[inline(never)]
fn concrete_closure_dup(x: SneakyCopy) -> (SneakyCopy, SneakyCopy) {
    let f = use || x;
    (f(), x)
}

fn main() {
    CLONE_CALLS.store(0, Ordering::SeqCst);
    let (g1, g2) = generic_dup(SneakyCopy(7));
    let calls_g = CLONE_CALLS.load(Ordering::SeqCst);

    CLONE_CALLS.store(0, Ordering::SeqCst);
    let (gc1, gc2) = generic_closure_dup(SneakyCopy(7));
    let calls_gc = CLONE_CALLS.load(Ordering::SeqCst);

    CLONE_CALLS.store(0, Ordering::SeqCst);
    let (c1, c2) = concrete_dup(SneakyCopy(7));
    let calls_c = CLONE_CALLS.load(Ordering::SeqCst);

    CLONE_CALLS.store(0, Ordering::SeqCst);
    let (cc1, cc2) = concrete_closure_dup(SneakyCopy(7));
    let calls_cc = CLONE_CALLS.load(Ordering::SeqCst);

    let rc = Rc::new(42u32);
    let rc2 = rc.use;
    let f_rc = use || *rc + 1;
    let rc_out = f_rc();
    let rc_cnt = Rc::strong_count(&rc);
    drop(rc2);

    let s = String::from("hello");
    let moved = s.use;
    let moved_len = moved.len();

    println!(
        "GENERIC=({},{}) CALLS_G={} GENERIC_CLOSURE=({},{}) CALLS_GC={} CONCRETE=({},{}) CALLS_C={} CONCRETE_CLOSURE=({},{}) CALLS_CC={} RC_OUT={} RC_CNT={} MOVED_LEN={}",
        g1.0, g2.0, calls_g,
        gc1.0, gc2.0, calls_gc,
        c1.0, c2.0, calls_c,
        cc1.0, cc2.0, calls_cc,
        rc_out, rc_cnt, moved_len
    );
}
'''

PART_B_PANIC_COPY_SOURCE = r'''#![forbid(unsafe_code)]
#![feature(ergonomic_clones)]

use std::clone::UseCloned;

#[derive(Copy, Debug)]
struct PanicCopy(u32);

impl Clone for PanicCopy {
    fn clone(&self) -> Self {
        panic!("PanicCopy::clone invoked");
    }
}

impl UseCloned for PanicCopy {}

#[inline(never)]
fn generic_dup<T: UseCloned>(x: T) -> (T, T) {
    (x.use, x)
}

fn main() {
    let res = std::panic::catch_unwind(|| generic_dup(PanicCopy(7)));
    match res {
        Ok((a, b)) => println!("OK=({},{})", a.0, b.0),
        Err(_) => println!("CAUGHT_PANIC"),
    }
}
'''

PART_B_PANIC_NONCOPY_SOURCE = r'''#![forbid(unsafe_code)]
#![feature(ergonomic_clones)]

use std::clone::UseCloned;

#[derive(Debug)]
struct PanicNonCopy(u32);

impl Clone for PanicNonCopy {
    fn clone(&self) -> Self {
        panic!("PanicNonCopy::clone invoked");
    }
}

impl UseCloned for PanicNonCopy {}

#[inline(never)]
fn generic_dup<T: UseCloned>(x: T) -> (T, T) {
    (x.use, x)
}

fn main() {
    let res = std::panic::catch_unwind(|| generic_dup(PanicNonCopy(7)));
    match res {
        Ok((a, b)) => println!("OK=({},{})", a.0, b.0),
        Err(_) => println!("CAUGHT_PANIC"),
    }
}
'''

PART_C_CASES: list[dict[str, Any]] = [
    {
        "name": "edition2021_rpit_omits_unmentioned_lifetime_by_default",
        "edition": "2021",
        "expect_rc": 0,
        "code": r'''fn rpit_default<'a>(_: &'a u32) -> impl Sized {
    0u32
}

pub fn return_detached() -> impl Sized {
    let local = 1u32;
    rpit_default(&local)
}
''',
    },
    {
        "name": "edition2024_rpit_captures_lifetime_by_default_e0597",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''fn rpit_default<'a>(_: &'a u32) -> impl Sized {
    0u32
}

pub fn return_detached() -> impl Sized {
    let local = 1u32;
    rpit_default(&local)
}
''',
    },
    {
        "name": "edition2024_rpit_overcapture_note_in_local_block_e0597",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''fn rpit_default<'a>(_: &'a u32) -> impl Sized {
    0u32
}

pub fn hold_past_local_drop() {
    let held = {
        let local = 1u32;
        rpit_default(&local)
    };
    let _ = held;
}
''',
    },
    {
        "name": "edition2024_rpit_use_empty_opts_out_of_lifetime_capture",
        "edition": "2024",
        "expect_rc": 0,
        "code": r'''fn rpit_use_empty<'a>(_: &'a u32) -> impl Sized + use<> {
    0u32
}

pub fn return_detached() -> impl Sized {
    let local = 1u32;
    rpit_use_empty(&local)
}
''',
    },
    {
        "name": "non_use_cloned_string_moved_by_dot_use_e0382",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''#![feature(ergonomic_clones)]

pub fn moved_twice(s: String) -> (String, String) {
    (s.use, s)
}
''',
    },
    {
        "name": "rpit_use_omitting_in_scope_type_param_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''pub fn bad_omit_ty<'a, T>(_: &'a u32, _: T) -> impl Sized + use<'a> {
    0u32
}
''',
    },
    {
        "name": "rpit_use_omitting_in_scope_const_param_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''pub fn bad_omit_const<'a, const N: usize>(_: &'a u32) -> impl Sized + use<'a> {
    0u32
}
''',
    },
    {
        "name": "rpit_use_retaining_all_ty_params_and_omitting_lifetime_accepted",
        "edition": "2024",
        "expect_rc": 0,
        "code": r'''fn good_keep_ty<'a, T>(_: &'a u32, _: T) -> impl Sized + use<T> {
    0u32
}

pub fn caller<T>(v: T) -> impl Sized + use<T> {
    let local = 1u32;
    good_keep_ty(&local, v)
}
''',
    },
    {
        "name": "rpit_use_captures_lifetime_invariantly_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''fn mk<'a>() -> impl Sized + use<'a>
where
    'a: 'a,
{
    0u32
}

pub fn check_opaque_invariant<'a>(cond: bool) {
    let mut slot = mk::<'static>();
    if cond {
        slot = mk::<'a>();
    }
    let _ = slot;
}
''',
    },
    {
        "name": "rpit_use_omitted_lifetime_is_bivariant_accepted",
        "edition": "2024",
        "expect_rc": 0,
        "code": r'''fn mk<'a>() -> impl Sized + use<>
where
    'a: 'a,
{
    0u32
}

pub fn check_opaque_bivariant<'a>(cond: bool) {
    let mut slot = mk::<'static>();
    if cond {
        slot = mk::<'a>();
    }
    let _ = slot;
}
''',
    },
    {
        "name": "rpit_use_lifetimes_must_be_first_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''pub fn bad_order<'a, T>(_: &'a u32, _: T) -> impl Sized + use<T, 'a> {
    0u32
}
''',
    },
    {
        "name": "rpit_use_duplicate_param_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''pub fn bad_dup<'a>(_: &'a u32) -> impl Sized + use<'a, 'a> {
    0u32
}
''',
    },
    {
        "name": "rpit_use_omitting_bound_mentioned_lifetime_rejected",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''pub fn bad_bound<'a>(x: &'a u32) -> impl Sized + 'a + use<> {
    x
}
''',
    },
    {
        "name": "tait_non_generic_param_rejected_e0792",
        "edition": "2024",
        "expect_rc": 1,
        "code": r'''#![feature(type_alias_impl_trait)]

type Opaque<T> = impl Sized;

#[define_opaque(Opaque)]
pub fn bad_non_generic() -> Opaque<u32> {
    0u32
}
''',
    },
]


def run_cmd(
    cmd: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )


def sanitize_text(text: str, tmp_dir: Path, rustc_sysroot: Path) -> str:
    out = text.replace(str(tmp_dir), "<TMP>")
    out = out.replace(str(rustc_sysroot), "<TOOLCHAIN_SYSROOT>")
    home_str = str(Path.home())
    if home_str:
        out = out.replace(home_str, "<HOME>")
    # Strip transient PID from panic output for determinism across reruns.
    out = re.sub(r"thread 'main' \(\d+\) panicked", "thread 'main' (<PID>) panicked", out)
    # Strip cargo timing lines for deterministic diffs.
    out = re.sub(r"in \d+\.\d+s", "in <DURATION>", out)
    return out


def prepare_miri_env(tmp_dir: Path, rustc_bin: str) -> tuple[dict[str, str], Path]:
    """Return environment suitable for running `cargo miri` plus rustc sysroot."""
    sysroot_res = run_cmd([rustc_bin, "--print", "sysroot"])
    if sysroot_res.returncode != 0:
        raise RuntimeError(f"rustc --print sysroot failed: {sysroot_res.stderr}")
    rustc_sysroot = Path(sysroot_res.stdout.strip())
    toolchain_bin = rustc_sysroot / "bin"

    env = os.environ.copy()
    env["PATH"] = f"{toolchain_bin}:{env.get('PATH', '')}"

    if env.get("MIRI_SYSROOT") and Path(env["MIRI_SYSROOT"]).is_dir():
        return env, rustc_sysroot

    miri_sysroot = tmp_dir / "miri_sysroot"
    miri_sysroot.mkdir(parents=True, exist_ok=True)
    rust_src_vendor = rustc_sysroot / "lib/rustlib/src/rust/library/vendor"

    setup_env = env.copy()
    setup_env["MIRI_SYSROOT"] = str(miri_sysroot)
    if rust_src_vendor.is_dir():
        cargo_home = tmp_dir / "cargo_home"
        fake_home = tmp_dir / "fake_home"
        (fake_home / ".cargo").mkdir(parents=True, exist_ok=True)
        cargo_home.mkdir(parents=True, exist_ok=True)
        cfg = (
            "[net]\noffline = true\n\n"
            "[source.crates-io]\nreplace-with = \"vendored-sources\"\n\n"
            f"[source.vendored-sources]\ndirectory = \"{rust_src_vendor}\"\n"
        )
        (cargo_home / "config.toml").write_text(cfg, encoding="utf-8")
        (fake_home / ".cargo" / "config.toml").write_text(cfg, encoding="utf-8")
        setup_env["CARGO_HOME"] = str(cargo_home)
        setup_env["HOME"] = str(fake_home)
        if "RUSTUP_HOME" not in setup_env and Path.home().joinpath(".rustup").is_dir():
            setup_env["RUSTUP_HOME"] = str(Path.home() / ".rustup")

    cargo_bin = str(toolchain_bin / "cargo")
    setup_res = run_cmd(
        [cargo_bin, "miri", "setup", "--print-sysroot"],
        cwd=tmp_dir,
        env=setup_env,
        timeout=300,
    )
    if setup_res.returncode != 0:
        raise RuntimeError(
            f"cargo miri setup failed (rc={setup_res.returncode}):\n"
            f"stdout={setup_res.stdout}\nstderr={setup_res.stderr}"
        )
    resolved_sysroot = setup_res.stdout.strip().splitlines()[-1].strip()
    setup_env["MIRI_SYSROOT"] = resolved_sysroot
    return setup_env, rustc_sysroot


def run_miri_crate(
    tmp_dir: Path,
    rustc_sysroot: Path,
    crate_name: str,
    source: str,
    miri_env: dict[str, str],
    miriflags: str,
) -> dict[str, Any]:
    crate_dir = tmp_dir / f"miri_{crate_name}"
    (crate_dir / "src").mkdir(parents=True, exist_ok=True)
    (crate_dir / "Cargo.toml").write_text(
        f'[package]\nname = "{crate_name}"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (crate_dir / "src" / "main.rs").write_text(source, encoding="utf-8")

    env = miri_env.copy()
    if miriflags:
        env["MIRIFLAGS"] = miriflags
    else:
        env.pop("MIRIFLAGS", None)

    res = run_cmd(["cargo", "miri", "run"], cwd=crate_dir, env=env, timeout=180)
    return {
        "rc": res.returncode,
        "stdout": sanitize_text(res.stdout, tmp_dir, rustc_sysroot).strip(),
        "stderr": sanitize_text(res.stderr, tmp_dir, rustc_sysroot).strip(),
    }


def compile_and_run_native(
    tmp_dir: Path,
    rustc_sysroot: Path,
    rustc_bin: str,
    name: str,
    source: str,
    extra_flags: list[str],
) -> dict[str, Any]:
    src_path = tmp_dir / f"{name}.rs"
    bin_path = tmp_dir / f"{name}_bin"
    src_path.write_text(source, encoding="utf-8")

    comp = run_cmd(
        [rustc_bin, "--edition=2024", *extra_flags, str(src_path), "-o", str(bin_path)],
        cwd=tmp_dir,
    )
    out: dict[str, Any] = {
        "flags": extra_flags,
        "compile_rc": comp.returncode,
        "compile_stderr": sanitize_text(comp.stderr, tmp_dir, rustc_sysroot).strip(),
    }
    if comp.returncode == 0:
        run = run_cmd([str(bin_path)], cwd=tmp_dir)
        out["run_rc"] = run.returncode
        out["stdout"] = sanitize_text(run.stdout, tmp_dir, rustc_sysroot).strip()
        out["stderr"] = sanitize_text(run.stderr, tmp_dir, rustc_sysroot).strip()
    return out


def extract_mir_function(mir_text: str, fn_marker: str) -> str:
    lines = mir_text.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if line.startswith(f"fn {fn_marker}"):
            start = idx
            break
    if start is None:
        return ""
    buf = [lines[start]]
    depth = lines[start].count("{") - lines[start].count("}")
    for line in lines[start + 1 :]:
        buf.append(line)
        depth += line.count("{") - line.count("}")
        if depth <= 0 and line.strip() == "}":
            break
    return "\n".join(buf)


def extract_llvm_define(ll_text: str, symbol_substr: str) -> str:
    lines = ll_text.splitlines()
    start = None
    for idx, line in enumerate(lines):
        if line.startswith("define ") and symbol_substr in line:
            start = idx
            break
    if start is None:
        return ""
    buf = [lines[start]]
    for line in lines[start + 1 :]:
        buf.append(line)
        if line.strip() == "}":
            break
    return "\n".join(buf)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional path to write JSON results (defaults to stdout only).",
    )
    args = parser.parse_args()

    rustc_bin = shutil.which("rustc")
    if not rustc_bin:
        cargo_bin_rustc = Path.home() / ".cargo" / "bin" / "rustc"
        if cargo_bin_rustc.exists():
            rustc_bin = str(cargo_bin_rustc)
        else:
            raise SystemExit("rustc not found on PATH")

    rustc_vv = run_cmd([rustc_bin, "-vV"]).stdout.strip()
    miri_ver = run_cmd([str(Path(rustc_bin).parent / "cargo"), "miri", "--version"])
    miri_ver_str = miri_ver.stdout.strip() if miri_ver.returncode == 0 else "unknown"

    with tempfile.TemporaryDirectory(prefix="probe_ergonomic_clones_") as td:
        tmp_dir = Path(td)
        miri_env, rustc_sysroot = prepare_miri_env(tmp_dir, rustc_bin)

        # Part A: Native vs Miri divergence + MIR / LLVM IR inspection
        part_a_native_opt0_mir0 = compile_and_run_native(
            tmp_dir, rustc_sysroot, rustc_bin, "part_a_opt0_mir0", PART_A_SOURCE,
            ["-C", "opt-level=0", "-Z", "mir-opt-level=0"],
        )
        part_a_native_opt0 = compile_and_run_native(
            tmp_dir, rustc_sysroot, rustc_bin, "part_a_opt0", PART_A_SOURCE,
            ["-C", "opt-level=0"],
        )
        part_a_native_opt3 = compile_and_run_native(
            tmp_dir, rustc_sysroot, rustc_bin, "part_a_opt3", PART_A_SOURCE,
            ["-O"],
        )
        part_a_miri_sb = run_miri_crate(
            tmp_dir, rustc_sysroot, "part_a_sb", PART_A_SOURCE, miri_env, ""
        )
        part_a_miri_tb = run_miri_crate(
            tmp_dir, rustc_sysroot, "part_a_tb", PART_A_SOURCE, miri_env, "-Zmiri-tree-borrows"
        )

        # Dump MIR and LLVM IR at -C opt-level=0 -Z mir-opt-level=0
        ir_src = tmp_dir / "part_a_ir.rs"
        ir_src.write_text(PART_A_SOURCE, encoding="utf-8")
        mir_out = tmp_dir / "part_a_ir.mir"
        ll_out = tmp_dir / "part_a_ir.ll"
        run_cmd(
            [rustc_bin, "--edition=2024", "-C", "opt-level=0", "-Z", "mir-opt-level=0",
             "--emit=mir", str(ir_src), "-o", str(mir_out)],
            cwd=tmp_dir,
        )
        run_cmd(
            [rustc_bin, "--edition=2024", "-C", "opt-level=0", "-Z", "mir-opt-level=0",
             "--emit=llvm-ir", str(ir_src), "-o", str(ll_out)],
            cwd=tmp_dir,
        )
        mir_text = sanitize_text(
            mir_out.read_text(encoding="utf-8") if mir_out.exists() else "",
            tmp_dir, rustc_sysroot,
        )
        ll_text = sanitize_text(
            ll_out.read_text(encoding="utf-8") if ll_out.exists() else "",
            tmp_dir, rustc_sysroot,
        )

        mir_snippets = {
            "generic_dup": extract_mir_function(mir_text, "generic_dup"),
            "generic_closure_dup": extract_mir_function(mir_text, "generic_closure_dup"),
            "concrete_dup": extract_mir_function(mir_text, "concrete_dup"),
            "concrete_closure_dup": extract_mir_function(mir_text, "concrete_closure_dup"),
        }
        ll_generic_dup = extract_llvm_define(ll_text, "generic_dup")
        ll_generic_closure_dup = extract_llvm_define(ll_text, "generic_closure_dup")
        ll_calls_clone_in_generic_dup = bool(
            re.search(r"call\b[^\n]*clone", ll_generic_dup, re.IGNORECASE)
        )
        ll_calls_clone_in_generic_closure_dup = bool(
            re.search(r"call\b[^\n]*clone", ll_generic_closure_dup, re.IGNORECASE)
        )

        # Part B: UnwindAction::Unreachable panic hazard on CallSource::Use
        part_b_noncopy_ll_src = tmp_dir / "part_b_noncopy_ir.rs"
        part_b_noncopy_ll_src.write_text(PART_B_PANIC_NONCOPY_SOURCE, encoding="utf-8")
        part_b_noncopy_ll_out = tmp_dir / "part_b_noncopy_ir.ll"
        run_cmd(
            [rustc_bin, "--edition=2024", "-C", "opt-level=0", "-Z", "mir-opt-level=0",
             "--emit=llvm-ir", str(part_b_noncopy_ll_src), "-o", str(part_b_noncopy_ll_out)],
            cwd=tmp_dir,
        )
        part_b_noncopy_ll_text = sanitize_text(
            part_b_noncopy_ll_out.read_text(encoding="utf-8") if part_b_noncopy_ll_out.exists() else "",
            tmp_dir, rustc_sysroot,
        )

        part_b = {
            "panic_copy_native_opt0": compile_and_run_native(
                tmp_dir, rustc_sysroot, rustc_bin, "part_b_panic_copy_opt0", PART_B_PANIC_COPY_SOURCE,
                ["-C", "opt-level=0", "-Z", "mir-opt-level=0"],
            ),
            "panic_copy_native_opt3": compile_and_run_native(
                tmp_dir, rustc_sysroot, rustc_bin, "part_b_panic_copy_opt3", PART_B_PANIC_COPY_SOURCE,
                ["-O"],
            ),
            "panic_copy_miri_sb": run_miri_crate(
                tmp_dir, rustc_sysroot, "part_b_panic_copy_sb", PART_B_PANIC_COPY_SOURCE, miri_env, ""
            ),
            "panic_copy_miri_tb": run_miri_crate(
                tmp_dir, rustc_sysroot, "part_b_panic_copy_tb", PART_B_PANIC_COPY_SOURCE, miri_env, "-Zmiri-tree-borrows"
            ),
            "panic_noncopy_native_opt0": compile_and_run_native(
                tmp_dir, rustc_sysroot, rustc_bin, "part_b_panic_noncopy_opt0", PART_B_PANIC_NONCOPY_SOURCE,
                ["-C", "opt-level=0", "-Z", "mir-opt-level=0"],
            ),
            "panic_noncopy_native_opt3": compile_and_run_native(
                tmp_dir, rustc_sysroot, rustc_bin, "part_b_panic_noncopy_opt3", PART_B_PANIC_NONCOPY_SOURCE,
                ["-O"],
            ),
            "panic_noncopy_miri_sb": run_miri_crate(
                tmp_dir, rustc_sysroot, "part_b_panic_noncopy_sb", PART_B_PANIC_NONCOPY_SOURCE, miri_env, ""
            ),
            "panic_noncopy_llvm_ir_generic_dup": extract_llvm_define(
                part_b_noncopy_ll_text, "generic_dup"
            ),
        }

        # Part C: Edition 2024 precise capturing (`use<...>`) & ergonomic-clone move gates
        part_c: dict[str, Any] = {}
        for case in PART_C_CASES:
            src_path = tmp_dir / f"{case['name']}.rs"
            src_path.write_text(case["code"], encoding="utf-8")
            res = run_cmd(
                [
                    rustc_bin,
                    f"--edition={case['edition']}",
                    "--crate-type=lib",
                    "--emit=metadata",
                    "-o",
                    str(tmp_dir / f"{case['name']}.rmeta"),
                    str(src_path),
                ],
                cwd=tmp_dir,
            )
            part_c[case["name"]] = {
                "edition": case["edition"],
                "expected_rc": case["expect_rc"],
                "rc": res.returncode,
                "matched_expectation": res.returncode == case["expect_rc"],
                "stderr": sanitize_text(res.stderr, tmp_dir, rustc_sysroot).strip(),
            }

        result = {
            "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "host_arch": f"{platform.system()} {platform.machine()}",
            "rustc_version": rustc_vv,
            "miri_version": miri_ver_str,
            "part_a_ergonomic_clones_native_vs_miri_divergence": {
                "native_opt0_mir0": part_a_native_opt0_mir0,
                "native_opt0": part_a_native_opt0,
                "native_opt3": part_a_native_opt3,
                "miri_stacked_borrows": part_a_miri_sb,
                "miri_tree_borrows": part_a_miri_tb,
                "mir_snippets_opt0_mir0": mir_snippets,
                "llvm_ir_opt0_mir0_generic_dup": ll_generic_dup,
                "llvm_ir_opt0_mir0_generic_closure_dup": ll_generic_closure_dup,
                "llvm_ir_generic_dup_calls_clone": ll_calls_clone_in_generic_dup,
                "llvm_ir_generic_closure_dup_calls_clone": ll_calls_clone_in_generic_closure_dup,
            },
            "part_b_call_source_use_unwind_unreachable_hazard": part_b,
            "part_c_precise_capturing_and_ergonomic_clone_gates": part_c,
        }

    rendered = json.dumps(result, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
