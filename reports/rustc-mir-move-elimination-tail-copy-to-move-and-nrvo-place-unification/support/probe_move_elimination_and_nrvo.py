#!/usr/bin/env python3
"""Reproducible probe for rustc `-Z mir-move-elimination` (MIR passes `TailCopyToMove`
and `MoveElimination`) against the default pipeline (`DestinationPropagation`).

What it does
------------
Part A  `nrvo_and_swap.rs`: a borrowed-local array return and a pair swap.  For each
        arm it records the final optimized MIR, the x86-64 assembly of
        `make_borrowed_array_nrvo` (CFA high-water mark, `memcpy`/`memset` calls, stack
        probes), the `.stack_sizes` entry, the native output and Miri results.
Part B  `address_and_alias_controls.rs`: controls that must behave identically in both
        arms (an unborrowed array return, an in-place swap, two address-observed locals
        that are live together, a return tail containing an indirect read).
Part C  Normalised comparison of this run's default arm with the preserved capture
        `captured_rustc_1_102_move_elimination.json` (same directory).
Part D  Per-pass MIR census over the zerocopy crate.

Arms
----
`default`               : rustc -Copt-level=2
`mir_move_elimination`  : rustc -Copt-level=2 -Zmir-move-elimination=yes

The second arm runs only if the selected rustc accepts the flag.  When it does not
(the flag does not exist in older nightlies) the probe records the rejection message
and still runs the default arm and every control.

Run
---
    python3 support/probe_move_elimination_and_nrvo.py --out support/probe_results.json

Options: `--zerocopy-lib-rs PATH` (path to zerocopy's `src/lib.rs`), `--skip-zerocopy`,
`--skip-miri`.  The toolchain is whatever `rustc` resolves to on PATH (with
`~/.cargo/bin` prepended); override with `RUSTUP_TOOLCHAIN`.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

NRVO_AND_SWAP_RS = """\
use std::hint::black_box;

#[inline(never)]
fn fill_buf(buf: &mut [u8; 8192], seed: u8) {
    buf[0] = seed;
    buf[8191] = seed.wrapping_add(1);
}

#[inline(never)]
fn make_borrowed_array_nrvo(seed: u8) -> [u8; 8192] {
    let mut buf = [0u8; 8192];
    fill_buf(&mut buf, seed);
    buf
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct BigPair {
    a: [u64; 4],
    b: [u64; 4],
}

#[inline(never)]
fn swap_big_pair_fields(mut p: BigPair) -> BigPair {
    let q = BigPair { a: p.b, b: p.a };
    p = q;
    p
}

fn main() {
    let r = make_borrowed_array_nrvo(7);
    assert_eq!((r[0], r[1], r[8191]), (7, 0, 8));
    let p = BigPair { a: [1, 2, 3, 4], b: [5, 6, 7, 8] };
    let q = swap_big_pair_fields(black_box(p));
    assert_eq!(q, BigPair { a: [5, 6, 7, 8], b: [1, 2, 3, 4] });
    println!("NRVO_AND_SWAP_OK");
}
"""

CONTROLS_RS = """\
use std::hint::black_box;

// Control 1: the array is never borrowed, so the default pipeline already builds it
// in the return place.
#[inline(never)]
fn make_unborrowed_array_nrvo(seed: u8) -> [u8; 8192] {
    let mut buf = [0u8; 8192];
    buf[0] = seed;
    buf[8191] = seed.wrapping_add(1);
    buf
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct BigPair {
    a: [u64; 4],
    b: [u64; 4],
}

// Control 2: the swapped aggregate is assigned straight back into its own source.
#[inline(never)]
fn swap_big_pair_in_place(mut p: BigPair) -> BigPair {
    p = BigPair { a: p.b, b: p.a };
    p
}

#[inline(never)]
fn observe(p: &mut [u8; 64]) -> usize {
    p[0] = p[0].wrapping_add(1);
    black_box(p as *mut [u8; 64] as usize)
}

// Control 3: `a` and `b` are both address-observed, are connected by a copy, and are
// live at the same time.  They must keep distinct addresses in every arm.
#[inline(never)]
fn two_borrowed_locals_overlap(seed: u8) -> (bool, u8, u8) {
    let mut a = [seed; 64];
    let pa = observe(&mut a);
    let mut b = a;
    let pb = observe(&mut b);
    let pa2 = observe(&mut a);
    (pa != pb && pa == pa2, a[0], b[0])
}

// Control 4: the copy of `a` is followed by a read through an opaque raw pointer to
// `a` (the `black_box` keeps the read indirect in optimized MIR), so the copy is not a
// final use and must stay a copy.
#[inline(never)]
fn return_after_indirect_read(seed: u8) -> ([u8; 64], u8) {
    let mut a = [seed; 64];
    let p = black_box(&mut a as *mut [u8; 64]);
    observe(unsafe { &mut *p });
    let r = a;
    let last = unsafe { (*p)[0] };
    (r, last)
}

fn main() {
    let u = make_unborrowed_array_nrvo(black_box(9));
    assert_eq!((u[0], u[1], u[8191]), (9, 0, 10));
    let p = BigPair { a: [1, 2, 3, 4], b: [5, 6, 7, 8] };
    let q = swap_big_pair_in_place(black_box(p));
    assert_eq!(q, BigPair { a: [5, 6, 7, 8], b: [1, 2, 3, 4] });
    let (distinct, a0, b0) = two_borrowed_locals_overlap(black_box(40));
    assert!(distinct, "address-observed locals that are live together must not share an address");
    assert_eq!((a0, b0), (42, 42));
    let (r, last) = return_after_indirect_read(black_box(3));
    assert_eq!((r[0], r[63], last), (4, 3, 4));
    println!("CONTROLS_OK distinct={distinct}");
}
"""

NRVO_FUNCS = ["make_borrowed_array_nrvo", "swap_big_pair_fields"]
CONTROL_FUNCS = [
    "make_unborrowed_array_nrvo",
    "swap_big_pair_in_place",
    "two_borrowed_locals_overlap",
    "return_after_indirect_read",
]

MOVE_ELIM_FLAG = "-Zmir-move-elimination=yes"
DUMP_PASSES = "DestinationPropagation|TailCopyToMove|MoveElimination|SimplifyLocals-final"

CAST_SUFFIX_RE = re.compile(
    r" \((IntToInt|FloatToInt|IntToFloat|FloatToFloat|PtrToPtr|FnPtrToPtr|Transmute|"
    r"PointerCoercion|PointerExposeProvenance|PointerWithExposedProvenance|Subtype)[^;]*\);$"
)
LOCAL_DECL_RE = re.compile(r"^\s+let (mut )?_\d+: ")
STORAGE_RE = re.compile(r"^\s+Storage(Live|Dead)\(_\d+\);")
ASSIGN_RE = re.compile(r"^\s+(\(?\*?_\d+\S*.*?) = (.*;)$")


def build_env() -> dict[str, str]:
    env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    parts = [p for p in env.get("PATH", "").split(os.pathsep) if p]
    if cargo_bin not in parts:
        parts.insert(0, cargo_bin)
    env["PATH"] = os.pathsep.join(parts)
    env["RUST_BACKTRACE"] = "0"
    return env


def scrub(text: str, extra: list[tuple[str, str]] | None = None) -> str:
    """Remove machine-specific paths from text that is stored in the result file."""
    out = text
    for raw, repl in extra or []:
        if raw:
            out = out.replace(raw, repl)
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/[A-Za-z0-9._/-]+", "<TMP>", out)
    out = re.sub(r"(/[A-Za-z0-9._-]+){3,}/", "<PATH>/", out)
    return out


def run_cmd(
    cmd: list[str], cwd: Path, env: dict[str, str], timeout: int = 600
) -> tuple[int, str, str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )
    return proc.returncode, proc.stdout, proc.stderr


def asm_function(asm: str, fn_name: str) -> str:
    """Extract one function (v0-mangled symbol ending in <len><name>) from an .s file."""
    tag = f"{len(fn_name)}{fn_name}"
    lines = asm.splitlines()
    start = None
    for i, line in enumerate(lines):
        if re.match(rf"^_R\w*{re.escape(tag)}:\s*$", line):
            start = i
            break
    if start is None:
        return ""
    out = []
    for line in lines[start:]:
        out.append(line)
        if line.strip() == ".cfi_endproc":
            break
    return "\n".join(out) + "\n"


def asm_metrics(fn_asm: str) -> dict[str, Any]:
    """CFA high-water mark and call counts for one function's assembly text."""
    cfa = 8
    max_cfa = 8
    for line in fn_asm.splitlines():
        m = re.search(r"\.cfi_def_cfa_offset\s+(\d+)", line)
        if m:
            cfa = int(m.group(1))
        m = re.search(r"\.cfi_adjust_cfa_offset\s+(-?\d+)", line)
        if m:
            cfa += int(m.group(1))
        max_cfa = max(max_cfa, cfa)
    body = [ln.strip() for ln in fn_asm.splitlines()]
    return {
        "found": bool(fn_asm),
        "max_cfa_offset_bytes": max_cfa,
        "memcpy_calls": sum(1 for ln in body if ln.startswith("call") and "memcpy" in ln),
        "memset_calls": sum(1 for ln in body if ln.startswith("call") and "memset" in ln),
        "stack_probe_steps_4096": sum(1 for ln in body if re.match(r"subq\s+\$4096, %rsp", ln)),
        "pushq_count": sum(1 for ln in body if ln.startswith("pushq")),
        "instruction_lines": sum(
            1 for ln in body if ln and not ln.startswith(".") and not ln.endswith(":")
        ),
    }


def normalise_asm(fn_asm: str) -> str:
    """Erase the crate disambiguator hash and local label numbers."""
    out = re.sub(r"_RNvCs[0-9A-Za-z]+_", "_RNvCsHASH_", fn_asm)
    out = re.sub(r"\.Lfunc_end\d+", ".Lfunc_endN", out)
    return out


def parse_stack_sizes(readobj_out: str) -> dict[str, int]:
    sizes: dict[str, int] = {}
    for m in re.finditer(r"Functions:\s*\[([^\]]*)\]\s*Size:\s*(0x[0-9A-Fa-f]+|\d+)", readobj_out):
        size = int(m.group(2), 0)
        for sym in m.group(1).split(","):
            sym = sym.strip()
            if sym:
                sizes[sym] = size
    return sizes


def final_mir(mir_dir: Path, crate: str, fn_name: str, pass_name: str, when: str) -> str:
    files = sorted(mir_dir.glob(f"{crate}.{fn_name}.*.{pass_name}.{when}.mir"))
    return files[0].read_text(encoding="utf-8") if files else ""


def flag_supported(env: dict[str, str], td: Path) -> tuple[bool, str]:
    src = td / "flag_probe.rs"
    src.write_text("pub fn f() {}\n", encoding="utf-8")
    rc, _, err = run_cmd(
        ["rustc", "--edition=2021", "--crate-type=lib", MOVE_ELIM_FLAG, "--emit=metadata",
         "-o", str(td / "flag_probe.rmeta"), str(src)],
        cwd=td,
        env=env,
    )
    return rc == 0, scrub(err.strip(), [(str(td), "<PROBE_DIR>")])


def miri_modes(arm_flags: list[str]) -> dict[str, list[str]]:
    return {
        # Miri's own default: MIR optimisations off.
        "miri_default": [],
        # The arm's optimised MIR, interpreted by Miri.
        "miri_mir_opt_level_2": ["-Zmir-opt-level=2", *arm_flags],
        # Same, asking rustc to keep UB-relevant statements.
        "miri_mir_opt_level_2_preserve_ub": ["-Zmir-preserve-ub=yes", "-Zmir-opt-level=2", *arm_flags],
    }


def run_program_arm(
    env: dict[str, str],
    td: Path,
    crate: str,
    source: str,
    funcs: list[str],
    arm: str,
    arm_flags: list[str],
    asm_funcs: list[str],
    miri: tuple[str, str] | None,
) -> dict[str, Any]:
    work = td / f"{crate}_{arm}"
    work.mkdir(parents=True, exist_ok=True)
    rs = work / f"{crate}.rs"
    rs.write_text(source, encoding="utf-8")
    mir_dir = work / "mir_dump"
    common = ["rustc", "--edition=2021", "-Copt-level=2", "-Csymbol-mangling-version=v0", *arm_flags]

    rc, _, err = run_cmd(
        [*common, f"--crate-name={crate}", "--emit=asm,link", f"-Zdump-mir={DUMP_PASSES}",
         f"-Zdump-mir-dir={mir_dir}", "--out-dir", str(work), str(rs)],
        cwd=work,
        env=env,
    )
    result: dict[str, Any] = {
        "rustc_flags": common[1:],
        "compile_rc": rc,
        "compile_stderr_head": scrub(err, [(str(work), "<WORK>")]).splitlines()[:6],
    }
    if rc != 0:
        return result

    rc_run, out_run, err_run = run_cmd([str(work / crate)], cwd=work, env=env)
    result["native_rc"] = rc_run
    result["native_stdout"] = out_run.strip()
    result["native_stderr_head"] = scrub(err_run, [(str(work), "<WORK>")]).splitlines()[:4]

    passes_present = sorted(
        {
            m.group(1)
            for f in mir_dir.glob("*.mir")
            for m in [re.search(r"\.([A-Za-z-]+)\.(?:before|after)\.mir$", f.name)]
            if m
        }
    )
    result["dumped_passes"] = passes_present

    per_fn: dict[str, Any] = {}
    for fn in funcs:
        entry: dict[str, Any] = {
            "final_mir": final_mir(mir_dir, crate, fn, "SimplifyLocals-final", "after"),
        }
        for pass_name in ("DestinationPropagation", "TailCopyToMove", "MoveElimination"):
            before = final_mir(mir_dir, crate, fn, pass_name, "before")
            after = final_mir(mir_dir, crate, fn, pass_name, "after")
            if before or after:
                changed = "\n".join(before.splitlines()[1:]) != "\n".join(after.splitlines()[1:])
                entry[f"{pass_name}_changed_body"] = changed
                if changed:
                    entry[f"{pass_name}_after_mir"] = after
        per_fn[fn] = entry
    result["functions"] = per_fn

    asm_text = (work / f"{crate}.s").read_text(encoding="utf-8", errors="replace")
    asm_out: dict[str, Any] = {}
    for fn in asm_funcs:
        fn_asm = asm_function(asm_text, fn)
        asm_out[fn] = {"asm": fn_asm, "metrics": asm_metrics(fn_asm)}
    result["asm"] = asm_out

    # .stack_sizes section of a relocatable object.
    obj = work / f"{crate}.o"
    rc_o, _, err_o = run_cmd(
        [*common, "--emit=obj", "-Zemit-stack-sizes", "-o", str(obj), str(rs)], cwd=work, env=env
    )
    stack_sizes: dict[str, Any] = {"compile_rc": rc_o}
    if rc_o == 0:
        _, sysroot, _ = run_cmd(["rustc", "--print", "sysroot"], cwd=work, env=env)
        _, host, _ = run_cmd(["rustc", "--print", "host-tuple"], cwd=work, env=env)
        host = host.strip() or "x86_64-unknown-linux-gnu"
        readobj = Path(sysroot.strip()) / "lib" / "rustlib" / host / "bin" / "llvm-readobj"
        if readobj.is_file():
            rc_r, out_r, _ = run_cmd([str(readobj), "--stack-sizes", str(obj)], cwd=work, env=env)
            sizes = parse_stack_sizes(out_r) if rc_r == 0 else {}
            picked = {}
            for fn in asm_funcs:
                tag = f"{len(fn)}{fn}"
                for sym, size in sizes.items():
                    if sym.endswith(tag):
                        picked[fn] = size
            stack_sizes["llvm_readobj_rc"] = rc_r
            stack_sizes["bytes_by_function"] = picked
        else:
            stack_sizes["llvm_readobj"] = "not installed (rustup component llvm-tools)"
    else:
        stack_sizes["compile_stderr_head"] = scrub(err_o, [(str(work), "<WORK>")]).splitlines()[:4]
    result["stack_sizes_section"] = stack_sizes

    if miri is not None:
        miri_bin, miri_sysroot = miri
        miri_out: dict[str, Any] = {}
        for mode, flags in miri_modes(arm_flags).items():
            rc_m, out_m, err_m = run_cmd(
                [miri_bin, "--edition=2021", "--sysroot", miri_sysroot, *flags, str(rs)],
                cwd=work,
                env=env,
            )
            err_s = scrub(err_m, [(str(work), "<WORK>")])
            miri_out[mode] = {
                "flags": flags,
                "rc": rc_m,
                "stdout": out_m.strip(),
                "undefined_behavior_reported": "Undefined Behavior" in err_m,
                "mir_opt_warning_emitted": "explicitly enabled MIR optimizations" in err_m,
                "diag_head": [ln for ln in err_s.splitlines() if ln.startswith(("error", "warning"))][:4],
            }
        result["miri"] = miri_out
    return result


def count_mir(files: list[Path]) -> dict[str, int]:
    """Text counters over MIR dump files.

    bodies       : number of files
    locals       : `let [mut] _N: T;` declarations
    assigns      : `<place> = <rvalue>;` statements (terminators with `->` excluded)
    copy_assigns : assigns whose rvalue is exactly `copy <place>`
    move_assigns : assigns whose rvalue is exactly `[no_retag ]move <place>`
    storage_ops  : `StorageLive(_N);` and `StorageDead(_N);`
    """
    tot = dict(bodies=0, locals=0, assigns=0, copy_assigns=0, move_assigns=0, storage_ops=0)
    for f in files:
        tot["bodies"] += 1
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            if LOCAL_DECL_RE.match(line):
                tot["locals"] += 1
                continue
            if STORAGE_RE.match(line):
                tot["storage_ops"] += 1
                continue
            if " -> " in line:
                continue
            m = ASSIGN_RE.match(line)
            if not m:
                continue
            tot["assigns"] += 1
            rhs = m.group(2)
            if rhs.startswith("no_retag "):
                rhs = rhs[len("no_retag "):]
            if CAST_SUFFIX_RE.search(rhs):
                continue
            if rhs.startswith("copy "):
                tot["copy_assigns"] += 1
            elif rhs.startswith("move "):
                tot["move_assigns"] += 1
    return tot


def census_pass(mir_dir: Path, pass_name: str) -> dict[str, Any] | None:
    before = sorted(mir_dir.glob(f"*.{pass_name}.before.mir"))
    after = sorted(mir_dir.glob(f"*.{pass_name}.after.mir"))
    if not before:
        return None
    b, a = count_mir(before), count_mir(after)
    changed = 0
    after_by_name = {f.name.replace(".after.mir", ""): f for f in after}
    for f in before:
        g = after_by_name.get(f.name.replace(".before.mir", ""))
        if g is None:
            continue
        bt = "\n".join(f.read_text(encoding="utf-8", errors="replace").splitlines()[1:])
        at = "\n".join(g.read_text(encoding="utf-8", errors="replace").splitlines()[1:])
        changed += int(bt != at)
    return {
        "before": b,
        "after": a,
        "delta": {k: a[k] - b[k] for k in b},
        "bodies_changed_by_pass": changed,
    }


def find_zerocopy_lib() -> Path | None:
    override = os.environ.get("ZEROCOPY_LIB_RS")
    if override and Path(override).is_file():
        return Path(override)
    candidates = [
        Path.cwd() / "zerocopy" / "src" / "lib.rs",
        Path.cwd() / "src" / "lib.rs",
    ]
    projects = Path.home() / "Projects"
    if projects.is_dir():
        for child in sorted(projects.iterdir()):
            candidates.append(child / "zerocopy" / "zerocopy" / "src" / "lib.rs")
    for c in candidates:
        if c.is_file() and "zerocopy" in c.read_text(encoding="utf-8", errors="replace")[:4000]:
            return c
    return None


def run_zerocopy_census(
    env: dict[str, str], td: Path, lib_rs: Path, arms: dict[str, list[str]]
) -> dict[str, Any]:
    cargo_toml = lib_rs.parent.parent / "Cargo.toml"
    pkg_version = "unknown"
    if cargo_toml.is_file():
        m = re.search(r'^version\s*=\s*"([^"]+)"', cargo_toml.read_text(encoding="utf-8"), re.M)
        if m:
            pkg_version = m.group(1)
    rc_g, out_g, _ = run_cmd(["git", "rev-parse", "HEAD"], cwd=lib_rs.parent, env=env)
    git_rev = out_g.strip() if rc_g == 0 else "unknown"
    rc_d, out_d, _ = run_cmd(["git", "status", "--porcelain", "--", "."], cwd=lib_rs.parent, env=env)
    dirty = bool(out_d.strip()) if rc_d == 0 else None

    _, ver_out, _ = run_cmd(["rustc", "--version"], cwd=td, env=env)
    ver_m = re.search(r"rustc\s+(\d+)\.(\d+)\.", ver_out)
    extra_cfgs: list[str] = []
    if ver_m and (int(ver_m.group(1)), int(ver_m.group(2))) < (1, 100):
        extra_cfgs = ["--cfg", "no_zerocopy_allocator_api_1_100_0"]

    zc_env = env.copy()
    zc_env["CARGO_PKG_VERSION"] = pkg_version
    out: dict[str, Any] = {
        "zerocopy_package_version": pkg_version,
        "zerocopy_git_revision": git_rev,
        "zerocopy_src_dirty": dirty,
        "extra_cfgs": extra_cfgs,
        "counter_definitions": count_mir.__doc__,
        "arms": {},
    }
    for arm, arm_flags in arms.items():
        work = td / f"zerocopy_{arm}"
        work.mkdir(parents=True, exist_ok=True)
        mir_dir = work / "mir_dump"
        flags = ["--edition=2021", "--crate-name=zerocopy", "--crate-type=lib", "-Copt-level=2",
                 "-Zmir-opt-level=2", *arm_flags, *extra_cfgs]
        rc, _, err = run_cmd(
            ["rustc", *flags, f"-Zdump-mir={DUMP_PASSES}", f"-Zdump-mir-dir={mir_dir}",
             "--emit=mir", "-o", str(work / "zerocopy.mir"), str(lib_rs)],
            cwd=work,
            env=zc_env,
            timeout=900,
        )
        arm_out: dict[str, Any] = {"rustc_flags": flags, "compile_rc": rc}
        if rc != 0:
            arm_out["compile_stderr_head"] = scrub(err, [(str(work), "<WORK>")]).splitlines()[:6]
        else:
            for pass_name in ("DestinationPropagation", "TailCopyToMove", "MoveElimination",
                              "SimplifyLocals-final"):
                c = census_pass(mir_dir, pass_name)
                if c is not None:
                    arm_out[pass_name] = c
        out["arms"][arm] = arm_out
    return out


def compare_with_capture(part_a: dict[str, Any], capture_path: Path) -> dict[str, Any]:
    if not capture_path.is_file():
        return {"capture_present": False}
    cap = json.loads(capture_path.read_text(encoding="utf-8"))
    cap_a = cap["part_a_nrvo_and_swap"]
    out: dict[str, Any] = {
        "capture_present": True,
        "capture_rustc": cap["provenance"]["rustc_version_verbose"].splitlines()[0],
    }
    pairs = {"default": "default_no_move_elim", "mir_move_elimination": "enabled_move_elim"}
    for arm, cap_key in pairs.items():
        mine = part_a.get(arm)
        if not mine or mine.get("compile_rc") != 0:
            out[arm] = {"compared": False, "reason": "arm not run by this probe"}
            continue
        theirs = cap_a[cap_key]
        my_asm = mine["asm"]["make_borrowed_array_nrvo"]["asm"]
        out[arm] = {
            "compared": True,
            "nrvo_final_mir_identical": mine["functions"]["make_borrowed_array_nrvo"]["final_mir"]
            == theirs["nrvo_final_mir"],
            "swap_final_mir_identical": mine["functions"]["swap_big_pair_fields"]["final_mir"]
            == theirs["swap_final_mir"],
            "nrvo_asm_identical_modulo_crate_hash_and_labels": normalise_asm(my_asm)
            == normalise_asm(theirs["nrvo_asm"]),
            "capture_nrvo_asm_metrics": asm_metrics(theirs["nrvo_asm"]),
        }
    # Metrics of the captured arms, recomputed by this script's own parser.
    out["capture_metrics_recomputed"] = {
        cap_key: asm_metrics(cap_a[cap_key]["nrvo_asm"]) for cap_key in pairs.values()
    }
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("--zerocopy-lib-rs", type=Path, default=None)
    parser.add_argument("--skip-zerocopy", action="store_true")
    parser.add_argument("--skip-miri", action="store_true")
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    env = build_env()
    rc_v, rustc_vv, err_v = run_cmd(["rustc", "--version", "-v"], cwd=Path.cwd(), env=env)
    if rc_v != 0:
        raise RuntimeError(f"rustc --version -v failed: {err_v}")

    miri: tuple[str, str] | None = None
    miri_note = ""
    if not args.skip_miri:
        _, sysroot_out, _ = run_cmd(["rustc", "--print", "sysroot"], cwd=Path.cwd(), env=env)
        miri_bin = Path(sysroot_out.strip()) / "bin" / "miri"
        if miri_bin.is_file():
            rc_ms, ms_out, ms_err = run_cmd(
                ["cargo", "miri", "setup", "--print-sysroot"], cwd=Path.cwd(), env=env, timeout=900
            )
            if rc_ms == 0:
                miri = (str(miri_bin), ms_out.strip())
            else:
                miri_note = "cargo miri setup failed: " + scrub(ms_err).splitlines()[-1]
        else:
            miri_note = "miri component not installed"

    with tempfile.TemporaryDirectory(prefix="probe_move_elim_") as td_str:
        td = Path(td_str)
        supported, flag_err = flag_supported(env, td)
        arms: dict[str, list[str]] = {"default": []}
        if supported:
            arms["mir_move_elimination"] = [MOVE_ELIM_FLAG]

        part_a = {
            arm: run_program_arm(env, td, "nrvo_and_swap", NRVO_AND_SWAP_RS, NRVO_FUNCS, arm, flags,
                                 ["make_borrowed_array_nrvo", "swap_big_pair_fields"], miri)
            for arm, flags in arms.items()
        }
        part_b = {
            arm: run_program_arm(env, td, "address_and_alias_controls", CONTROLS_RS, CONTROL_FUNCS,
                                 arm, flags, ["make_unborrowed_array_nrvo"], miri)
            for arm, flags in arms.items()
        }
        part_c = compare_with_capture(
            part_a, Path(__file__).resolve().parent / "captured_rustc_1_102_move_elimination.json"
        )

        part_d: dict[str, Any] | None = None
        if not args.skip_zerocopy:
            lib_rs = args.zerocopy_lib_rs or find_zerocopy_lib()
            if lib_rs is None or not lib_rs.is_file():
                part_d = {"skipped": "zerocopy src/lib.rs not found; pass --zerocopy-lib-rs"}
            else:
                part_d = run_zerocopy_census(env, td, lib_rs, arms)

    payload: dict[str, Any] = {
        "rustc_version_verbose": rustc_vv.strip(),
        "mir_move_elimination_flag": {
            "flag": MOVE_ELIM_FLAG,
            "accepted_by_this_rustc": supported,
            "rejection_message": "" if supported else flag_err,
        },
        "arms_run": list(arms),
        "miri_available": miri is not None,
        "miri_note": miri_note,
        "sources": {
            "nrvo_and_swap.rs": NRVO_AND_SWAP_RS,
            "address_and_alias_controls.rs": CONTROLS_RS,
        },
        "part_a_nrvo_and_swap": part_a,
        "part_b_address_and_alias_controls": part_b,
        "part_c_comparison_with_preserved_capture": part_c,
    }
    if part_d is not None:
        payload["part_d_zerocopy_pass_census"] = part_d

    text = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
        print(f"wrote {args.out.name} ({len(text)} bytes); arms run: {', '.join(arms)}")
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
