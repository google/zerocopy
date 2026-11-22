#!/usr/bin/env python3
"""Live rustc differential probe for four MIR semantic and migration lints:
  1. CheckCallRecursion & CheckDropRecursion (`unconditional_recursion`),
     including the TriColorDepthFirstSearch back-edge false negative and
     `#![feature(explicit_tail_calls)]` (`become`) TailCall asymmetry.
  2. KnownPanicsLint (`unconditional_panic`, `arithmetic_overflow`),
     including DummyMachine const-prop boundaries (cross-block mutation,
     coro skip, static/const skip, Repeat vs Aggregate, dead-branch folding,
     shift overflow with symbolic LHS, release-mode overflow checks).
  3. FunctionItemReferences (`function_item_references`),
     comparing `&FnDef` vs `fn()` cast across `fmt::Pointer` (`{:p}`),
     `core::mem::transmute`, raw pointers, generic wrappers, and macros.
  4. LintTailExprDropOrder (`tail_expr_drop_order`),
     comparing Edition 2021 diagnostics + runtime drop order vs Edition 2024
     runtime drop order, plus non-significant-dtor and `_0` exclusions.

Self-contained: uses only the Python 3.10+ standard library and invokes `rustc`
from PATH (or `--rustc`). Writes all temporary files inside a cleaned
`tempfile.TemporaryDirectory`.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def resolve_rustc(explicit: str | None) -> str:
    if explicit:
        return explicit
    found = shutil.which("rustc")
    if found:
        return found
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise FileNotFoundError("rustc not found in PATH or ~/.cargo/bin/rustc")


def run_cmd(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )


def parse_rustc_json_stderr(stderr: str) -> list[dict[str, Any]]:
    diags: list[dict[str, Any]] = []
    for line in stderr.splitlines():
        line = line.strip()
        if not line or not line.startswith("{"):
            continue
        try:
            obj = json.loads(line)
        except json.JSONDecodeError:
            continue
        if obj.get("$message_type") != "diagnostic":
            continue
        code_obj = obj.get("code")
        code = code_obj.get("code") if isinstance(code_obj, dict) else None
        spans = []
        for sp in obj.get("spans", []):
            spans.append(
                {
                    "line_start": sp.get("line_start"),
                    "line_end": sp.get("line_end"),
                    "is_primary": sp.get("is_primary"),
                    "label": sp.get("label"),
                    "suggested_replacement": sp.get("suggested_replacement"),
                }
            )
        diags.append(
            {
                "level": obj.get("level"),
                "code": code,
                "message": obj.get("message"),
                "spans": spans,
            }
        )
    return diags


def compile_json(
    rustc: str,
    workdir: Path,
    name: str,
    source: str,
    extra_args: list[str],
    crate_type: str = "lib",
) -> dict[str, Any]:
    src_path = workdir / f"{name}.rs"
    out_path = workdir / (f"{name}.out" if crate_type == "bin" else f"lib{name}.rlib")
    src_path.write_text(source, encoding="utf-8")
    cmd = [
        rustc,
        "--error-format=json",
        f"--crate-type={crate_type}",
        "--crate-name",
        name,
        "-o",
        str(out_path),
        *extra_args,
        str(src_path),
    ]
    proc = run_cmd(cmd, workdir)
    diags = parse_rustc_json_stderr(proc.stderr)
    summary_diags = [d for d in diags if d["code"] is not None]
    result: dict[str, Any] = {
        "crate": name,
        "extra_args": extra_args,
        "returncode": proc.returncode,
        "diagnostics": summary_diags,
        "all_messages": [d["message"] for d in diags],
    }
    if crate_type == "bin" and proc.returncode == 0 and out_path.exists():
        run_proc = run_cmd([str(out_path)], workdir)
        result["exec_returncode"] = run_proc.returncode
        result["exec_stdout"] = run_proc.stdout.strip()
        result["exec_stderr"] = run_proc.stderr.strip()
    return result


# ---------------------------------------------------------------------------
# Probe 1: CheckCallRecursion & CheckDropRecursion (plus loop back-edge FN)
# ---------------------------------------------------------------------------
SRC_RECURSION = r"""#![allow(dead_code)]

// Case 1: Straight-line direct unconditional recursion -> MUST WARN
pub fn direct_recurse(x: u32) -> u32 {
    direct_recurse(x)
}

// Case 2: Bounded terminating loop before unconditional recursion -> FALSE NEGATIVE
// TriColorDepthFirstSearch sees back-edge (`Some(NodeStatus::Visited)`) -> Break(NonRecursive)
pub fn bounded_loop_then_recurse(x: u32) -> u32 {
    let mut i = 0u32;
    while i < 1 {
        i += 1;
    }
    bounded_loop_then_recurse(x.wrapping_add(i))
}

// Case 3: Genuine infinite loop without recursion -> MUST NOT WARN
pub fn pure_infinite_loop() -> ! {
    loop {}
}

// Case 4: Branch with Return escape -> MUST NOT WARN
pub fn base_case_recurse(n: u32) -> u32 {
    if n == 0 {
        return 0;
    }
    base_case_recurse(n - 1)
}

// Case 5: Direct Drop recursion -> MUST WARN via CheckDropRecursion
pub struct BadDrop(pub u32);
impl Drop for BadDrop {
    fn drop(&mut self) {
        let _ = BadDrop(self.0);
    }
}

// Case 6: Bounded loop before Drop recursion -> FALSE NEGATIVE via CheckDropRecursion
pub struct LoopBadDrop(pub u32);
impl Drop for LoopBadDrop {
    fn drop(&mut self) {
        let mut i = 0u32;
        while i < 1 {
            i += 1;
        }
        let _ = LoopBadDrop(self.0.wrapping_add(i));
    }
}

// Case 7: Mutual recursion across function boundaries -> NOT DETECTED (FIXME #57965)
pub fn mutual_a(x: u32) -> u32 {
    mutual_b(x)
}
pub fn mutual_b(x: u32) -> u32 {
    mutual_a(x)
}

// Case 8: Recursive call on both branches of `if` (no loop) -> MUST WARN, 2 call_sites
pub fn both_branches_recurse(b: bool, x: u32) -> u32 {
    if b {
        both_branches_recurse(false, x)
    } else {
        both_branches_recurse(true, x)
    }
}

// Case 9: Trait default method calling concrete different impl -> MUST NOT WARN
pub trait RecurseTrait {
    fn work(&self) -> u32 {
        <u8 as RecurseTrait>::work(&0u8)
    }
}
impl RecurseTrait for u8 {
    fn work(&self) -> u32 {
        1
    }
}
"""


# ---------------------------------------------------------------------------
# Probe 2: Explicit TailCall (`become`) asymmetry + non-recursive become FP!
# ---------------------------------------------------------------------------
SRC_TAIL_CALL = r"""#![feature(explicit_tail_calls)]
#![allow(dead_code, incomplete_features)]

// Case T1: Pure self tail-call recursion -> 0 warnings (`reachable_recursive_calls.is_empty()`)
pub fn pure_become(x: u32) -> u32 {
    become pure_become(x)
}

// Case T2: Mixed `become` self + normal `Call` self -> 1 warning, highlights ONLY `else` Call!
pub fn mixed_become_and_call(b: bool, x: u32) -> u32 {
    if b {
        become mixed_become_and_call(!b, x)
    } else {
        mixed_become_and_call(!b, x)
    }
}

// Case T3: Non-recursive `become helper` + recursive `else` Call (matching signature)!
// Because `node_examined` returns `Continue(())` for ALL `TerminatorKind::TailCall`
// without checking whether the tail callee is `self`, does this fire a FALSE POSITIVE?
pub fn non_recursive_helper(_b: bool, x: u32) -> u32 {
    x + 1
}

pub fn become_other_or_self_call(b: bool, x: u32) -> u32 {
    if b {
        become non_recursive_helper(b, x)
    } else {
        become_other_or_self_call(true, x)
    }
}
"""

SRC_TAIL_CALL_FP_BIN = r"""#![feature(explicit_tail_calls)]
#![allow(incomplete_features)]

fn non_recursive_helper(_b: bool, x: u32) -> u32 {
    x + 1
}

fn become_other_or_self_call(b: bool, x: u32) -> u32 {
    if b {
        become non_recursive_helper(b, x)
    } else {
        become_other_or_self_call(true, x)
    }
}

fn main() {
    let r_true = become_other_or_self_call(true, 41);
    let r_false = become_other_or_self_call(false, 41);
    println!("R_TRUE={} R_FALSE={}", r_true, r_false);
}
"""


# ---------------------------------------------------------------------------
# Probe 3: KnownPanicsLint (`DummyMachine` const-prop domain & boundaries)
# ---------------------------------------------------------------------------
SRC_KNOWN_PANICS = r"""#![allow(dead_code, unused_variables)]

// K1: Straight-line division by zero -> unconditional_panic
pub fn div_zero_straight() -> u32 {
    let d = 1u32 - 1u32;
    42u32 / d
}

// K2: Straight-line array OOB -> unconditional_panic
pub fn array_oob_straight() -> u32 {
    let arr = [10u32, 20, 30];
    let idx = 3usize;
    arr[idx]
}

// K3: Straight-line arithmetic overflow -> arithmetic_overflow (even with overflow-checks=off!)
pub fn add_overflow_straight() -> u8 {
    let x = 255u8;
    x + 1u8
}

// K4: Shift overflow with SYMBOLIC (unknown) LHS -> arithmetic_overflow!
pub fn shift_overflow_symbolic_lhs(x: u32) -> u32 {
    let s = 32u32;
    x << s
}

// K5: Unary Neg overflow (i8::MIN) -> arithmetic_overflow
pub fn neg_overflow_straight() -> i8 {
    let x = i8::MIN;
    -x
}

// K6: Signed division overflow (i32::MIN / -1) -> unconditional_panic (AssertKind::Overflow(Div))
pub fn div_overflow_signed() -> i32 {
    let a = i32::MIN;
    let b = -1i32;
    a / b
}

// K7: Cross-block mutated local -> ConstPropMode::OnlyInsideOwnBlock -> cleared at block exit -> 0 warnings!
pub fn cross_block_mut_div_zero(cond: bool) -> u32 {
    let mut d = 1u32;
    if cond {
        d = 0u32;
    } else {
        d = 0u32;
    }
    42u32 / d
}

// K8: Single-assignment local across branch -> ConstPropMode::FullConstProp -> STILL WARNS!
pub fn cross_block_ssa_div_zero(cond: bool) -> u32 {
    let d = 1u32 - 1u32;
    let mut sink = 0u32;
    if cond {
        sink = 1;
    }
    42u32 / d + sink
}

// K9: Dead constant branch (`if false`) -> SwitchInt folds constant -> 0 warnings!
pub fn dead_const_branch_div_zero() -> u32 {
    if false {
        42u32 / (1u32 - 1u32)
    } else {
        7u32
    }
}

// K10: Runtime conditional branch (`if cond`) -> SwitchInt visits all successors -> WARNS!
pub fn runtime_branch_div_zero(cond: bool) -> u32 {
    if cond {
        42u32 / (1u32 - 1u32)
    } else {
        7u32
    }
}

// K11: Async fn (coroutine) -> skipped by `tcx.is_coroutine(def_id)` -> 0 warnings!
pub async fn async_coro_div_zero() -> u32 {
    let d = 1u32 - 1u32;
    42u32 / d
}

// K12: Repeat rvalue `[0u32; 4]` -> `Rvalue::Repeat` returns `None` -> 0 warnings!
pub fn repeat_array_div_zero() -> u32 {
    let a = [0u32; 4];
    42u32 / a[0]
}

// K13: Aggregate array `[0u32, 1, 2, 3]` -> `Rvalue::Aggregate` propagates -> WARNS!
pub fn aggregate_array_div_zero() -> u32 {
    let a = [0u32, 1, 2, 3];
    42u32 / a[0]
}

// K14: Address-taken local (`&d`) -> `CanConstProp` sets `NoPropagation` -> 0 warnings!
pub fn addr_taken_div_zero() -> u32 {
    let d = 0u32;
    let _r = &d;
    42u32 / d
}

// K15: Union local -> `ty.is_union()` sets `NoPropagation` -> 0 warnings!
#[repr(C)]
pub union U {
    pub a: u32,
    pub b: i32,
}
pub fn union_div_zero() -> u32 {
    let u = U { a: 0 };
    unsafe { 42u32 / u.a }
}

// K16: Large aggregate >= MAX_ALLOC_LIMIT (1024 bytes) -> `NoPropagation` -> 0 warnings!
pub struct Big {
    pub d: u32,
    pub pad: [u8; 1020],
}
pub fn large_local_div_zero() -> u32 {
    let b = Big { d: 0, pad: [0u8; 1020] };
    42u32 / b.d
}
"""


# ---------------------------------------------------------------------------
# Probe 4: FunctionItemReferences (`&FnDef` vs `fn()` cast)
# ---------------------------------------------------------------------------
SRC_FN_ITEM_REFS = r"""#![allow(dead_code, unused_variables)]

pub fn sample_fn(x: u32) -> u32 {
    x + 1
}

pub fn generic_fn<T>(x: T) -> T {
    x
}

fn accept_ptr<P: core::fmt::Pointer>(p: P) -> usize {
    let _ = format!("{p:p}");
    core::mem::size_of::<P>()
}

// F1: Formatting `&sample_fn` via `{:p}` (fmt::Pointer macro expansion) -> WARNS!
pub fn fmt_fn_item_ref() -> String {
    format!("{:p}", &sample_fn)
}

// F2: Formatting `sample_fn as fn(u32) -> u32` via `{:p}` -> 0 warnings!
pub fn fmt_fn_ptr_cast() -> String {
    format!("{:p}", sample_fn as fn(u32) -> u32)
}

// F3: Passing `&sample_fn` to user generic `P: fmt::Pointer` -> WARNS!
pub fn generic_pointer_bound() -> usize {
    accept_ptr(&sample_fn)
}

// F4: Transmuting `&sample_fn` -> WARNS!
pub fn transmute_fn_item_ref() -> usize {
    unsafe { core::mem::transmute::<&_, usize>(&sample_fn) }
}

// F5: Transmuting `sample_fn as fn(u32) -> u32` -> 0 warnings!
pub fn transmute_fn_ptr_cast() -> usize {
    unsafe { core::mem::transmute::<fn(u32) -> u32, usize>(sample_fn as fn(u32) -> u32) }
}

// F6: Transmuting raw pointer `&raw const sample_fn` (`*const FnDef`) -> WARNS!
pub fn transmute_fn_item_raw_ptr() -> usize {
    let f = sample_fn;
    let p: *const _ = &f;
    unsafe { core::mem::transmute::<*const _, usize>(p) }
}

// F7: Generic function item `&generic_fn::<u64>` -> WARNS with turbofish suggestion!
pub fn fmt_generic_fn_item_ref() -> String {
    format!("{:p}", &generic_fn::<u64>)
}
"""


# ---------------------------------------------------------------------------
# Probe 4b: Runtime pointer-value contrast (`&FnDef` ZST address vs `fn()` code address)
# ---------------------------------------------------------------------------
SRC_FN_ITEM_ADDR_BIN = r"""#[inline(never)]
fn fn_alpha(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[inline(never)]
fn fn_beta(x: u32) -> u32 {
    x.wrapping_add(2)
}

fn main() {
    let ref_alpha = format!("{:p}", &fn_alpha);
    let ref_beta = format!("{:p}", &fn_beta);
    let ptr_alpha = format!("{:p}", fn_alpha as fn(u32) -> u32);
    let ptr_beta = format!("{:p}", fn_beta as fn(u32) -> u32);
    let zst_size = core::mem::size_of_val(&fn_alpha);
    let ptr_size = core::mem::size_of::<fn(u32) -> u32>();
    println!(
        "ZST_SIZE={} PTR_SIZE={} REF_EQUAL={} PTR_EQUAL={} REF_ALPHA={} REF_BETA={} PTR_ALPHA={} PTR_BETA={}",
        zst_size,
        ptr_size,
        ref_alpha == ref_beta,
        ptr_alpha == ptr_beta,
        ref_alpha,
        ref_beta,
        ptr_alpha,
        ptr_beta,
    );
}
"""


# ---------------------------------------------------------------------------
# Probe 5: LintTailExprDropOrder (Edition 2021 vs 2024 + exclusions)
# ---------------------------------------------------------------------------
SRC_TAIL_DROP_BIN = r"""use std::cell::RefCell;

struct Guard<'a>(&'static str, &'a RefCell<Vec<&'static str>>);
impl Drop for Guard<'_> {
    fn drop(&mut self) {
        self.1.borrow_mut().push(self.0);
    }
}
impl Guard<'_> {
    fn val(&self) -> u32 {
        42
    }
}

fn f(log: &RefCell<Vec<&'static str>>) -> u32 {
    let _local = Guard("local", log);
    Guard("temp", log).val()
}

fn main() {
    let log = RefCell::new(Vec::new());
    let v = f(&log);
    println!("V={} ORDER={:?}", v, log.borrow());
}
"""

SRC_TAIL_DROP_EXCLUSIONS = r"""#![allow(dead_code)]

pub struct Significant(&'static str);
impl Drop for Significant {
    fn drop(&mut self) {
        let _ = self.0;
    }
}
impl Significant {
    fn val(&self) -> u32 {
        1
    }
}

// E1: Both temp and local have significant Drop -> WARNS in Edition 2021
pub fn sig_temp_and_sig_local() -> u32 {
    let _local = Significant("local");
    Significant("temp").val()
}

// E2: Local has NO significant Drop (plain Copy/Box-free struct) -> 0 warnings
pub struct Trivial(pub u32);
pub fn sig_temp_trivial_local() -> u32 {
    let _local = Trivial(1);
    Significant("temp").val()
}

// E3: Temp has NO significant Drop -> 0 warnings
impl Trivial {
    fn val(&self) -> u32 {
        self.0
    }
}
pub fn trivial_temp_sig_local() -> u32 {
    let _local = Significant("local");
    Trivial(2).val()
}

// E4: Local is moved into return place `_0` (not dropped before temp) -> 0 warnings
pub fn moved_local_no_drop() -> Significant {
    let local = Significant("moved");
    let _ = Significant("temp").val();
    local
}

// E5: Closure capture local (`ty::CAPTURE_STRUCT_LOCAL`) is excluded -> 0 warnings
pub fn closure_capture_excluded() -> impl FnOnce() -> u32 {
    let cap = Significant("cap");
    move || {
        let _ = &cap;
        Significant("temp").val()
    }
}
"""


# ---------------------------------------------------------------------------
# Probe 6: PassPolicy::optional(true) verification via -Zmir-enable-passes
# ---------------------------------------------------------------------------
SRC_PASS_TOGGLE = r"""#![allow(dead_code)]
pub fn direct_recurse(x: u32) -> u32 {
    direct_recurse(x)
}
pub fn div_zero() -> u32 {
    42u32 / (1u32 - 1u32)
}
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default=None, help="Path to rustc binary")
    parser.add_argument("--out", default=None, help="Optional JSON output file path")
    args = parser.parse_args()

    rustc = resolve_rustc(args.rustc)
    ver_proc = subprocess.run(
        [rustc, "--version", "--verbose"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=True,
    )

    with tempfile.TemporaryDirectory(prefix="probe_mir_lints_") as td:
        wd = Path(td)
        results: dict[str, Any] = {
            "rustc_path": os.path.basename(rustc),
            "rustc_version_verbose": ver_proc.stdout.strip(),
            "platform": f"{platform.system()} {platform.machine()}",
            "probes": {},
        }

        results["probes"]["recursion_and_drop"] = compile_json(
            rustc, wd, "probe_recursion", SRC_RECURSION, ["--edition=2021"]
        )
        results["probes"]["tail_call_recursion"] = compile_json(
            rustc, wd, "probe_tail_call", SRC_TAIL_CALL, ["--edition=2021"]
        )
        results["probes"]["tail_call_fp_bin"] = compile_json(
            rustc,
            wd,
            "probe_tail_call_fp_bin",
            SRC_TAIL_CALL_FP_BIN,
            ["--edition=2021"],
            crate_type="bin",
        )
        results["probes"]["known_panics_warn_mode"] = compile_json(
            rustc,
            wd,
            "probe_known_panics_warn",
            SRC_KNOWN_PANICS,
            ["--edition=2021", "-W", "unconditional_panic", "-W", "arithmetic_overflow"],
        )
        results["probes"]["known_panics_debug"] = compile_json(
            rustc,
            wd,
            "probe_known_panics_dbg",
            SRC_KNOWN_PANICS,
            ["--edition=2021", "-C", "overflow-checks=on"],
        )
        results["probes"]["known_panics_release_no_overflow_checks"] = compile_json(
            rustc,
            wd,
            "probe_known_panics_rel",
            SRC_KNOWN_PANICS,
            ["--edition=2021", "-C", "opt-level=3", "-C", "overflow-checks=off"],
        )
        results["probes"]["function_item_references"] = compile_json(
            rustc, wd, "probe_fn_item_refs", SRC_FN_ITEM_REFS, ["--edition=2021"]
        )
        results["probes"]["function_item_addr_bin"] = compile_json(
            rustc,
            wd,
            "probe_fn_item_addr",
            SRC_FN_ITEM_ADDR_BIN,
            ["--edition=2021"],
            crate_type="bin",
        )
        results["probes"]["tail_drop_bin_ed2021"] = compile_json(
            rustc,
            wd,
            "probe_tedo_2021",
            SRC_TAIL_DROP_BIN,
            ["--edition=2021", "-W", "tail-expr-drop-order"],
            crate_type="bin",
        )
        results["probes"]["tail_drop_bin_ed2024"] = compile_json(
            rustc,
            wd,
            "probe_tedo_2024",
            SRC_TAIL_DROP_BIN,
            ["--edition=2024", "-W", "tail-expr-drop-order"],
            crate_type="bin",
        )
        results["probes"]["tail_drop_exclusions_ed2021"] = compile_json(
            rustc,
            wd,
            "probe_tedo_excl",
            SRC_TAIL_DROP_EXCLUSIONS,
            ["--edition=2021", "-W", "tail-expr-drop-order"],
        )
        results["probes"]["pass_toggle_default"] = compile_json(
            rustc, wd, "probe_toggle_def", SRC_PASS_TOGGLE, ["--edition=2021"]
        )
        results["probes"]["pass_toggle_disabled"] = compile_json(
            rustc,
            wd,
            "probe_toggle_off",
            SRC_PASS_TOGGLE,
            [
                "--edition=2021",
                "-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint",
            ],
        )

    output_text = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(output_text, encoding="utf-8")
    else:
        sys.stdout.write(output_text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
