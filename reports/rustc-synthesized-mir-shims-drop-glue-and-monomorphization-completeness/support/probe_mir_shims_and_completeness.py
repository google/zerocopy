#!/usr/bin/env python3
"""Empirical probe for rustc synthesized MIR shims, pass-pipeline divergence,
and whole-crate monomorphization completeness.

Compiles a self-contained two-crate Rust specimen (`dep_generics` + `shim_probe`)
plus focused `#![no_std]` library specimens for `ClosureOnceShim` (with owned
destructor cleanup) and `-Zsanitizer=kcfi` (`ReifyReason::FnPtr` vs
`ReifyReason::Vtable` separation) using real `rustc` inside a temporary directory.

Captures:
1. Local `mir_keys` bodies (`--emit=mir` and `built.after.mir` dumps);
2. User-defined mono-item statistics (`-Zdump-mono-stats` JSON), verifying the
   exact identity `|print_mono_items| - sum(dump_mono_stats) == |shim_mono_items|`;
3. Full `collect_and_partition_mono_items` output (`-Zprint-mono-items=yes`),
   partitioning executable `MonoItem::Fn` instances into local HIR items, local ADT
   constructors, foreign generic/inline instantiations, foreign ADT constructors,
   and synthesized MIR shims (`DropGlue`, `Clone`, `Reify`, `FnPtr`, `ClosureOnce`,
   `VTable`, `FnPtrAddr`);
4. Exact `make_shim` MIR before and after `SimplifyCfg-make_shim`, pass-snapshot
   divergence between `optimized_mir` and `mir_shims`, LLVM IR ABI arity + v0
   symbol mangling of `#[track_caller]` vs `Reify` shims, KCFI `ReifyReason`
   separation, and runtime execution of direct vs reified `#[track_caller]` calls
   and mid-tuple partial-clone unwind cleanup.

All temporary directory paths are scrubbed to `<PROBE_DIR>` in emitted JSON.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


DEP_CRATE_RS = """\
#![crate_name = "dep_generics"]
#![crate_type = "rlib"]

pub struct GenericPair<A, B>(pub A, pub B);

pub fn map_first<A, B, C, F>(pair: GenericPair<A, B>, f: F) -> GenericPair<C, B>
where
    F: FnOnce(A) -> C,
{
    GenericPair(f(pair.0), pair.1)
}

#[inline]
pub fn inline_mix_u64(x: u64, y: u64) -> u64 {
    x.wrapping_mul(6364136223846793005).wrapping_add(y)
}
"""

MAIN_CRATE_RS = """\
#![allow(internal_features)]
#![feature(unsized_fn_params)]
#![feature(fn_ptr_trait)]
#![crate_name = "shim_probe"]

extern crate dep_generics;

use std::marker::FnPtr;
use std::panic::{self, AssertUnwindSafe, Location};
use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_LOG: AtomicUsize = AtomicUsize::new(0);
static CLONE_STEP: AtomicUsize = AtomicUsize::new(0);

pub struct NeedsDrop(pub u32);

impl Drop for NeedsDrop {
    #[inline(never)]
    fn drop(&mut self) {
        DROP_LOG.fetch_add((self.0 as usize) + 100, Ordering::SeqCst);
    }
}

impl Clone for NeedsDrop {
    #[inline(never)]
    fn clone(&self) -> Self {
        let step = CLONE_STEP.fetch_add(1, Ordering::SeqCst);
        if self.0 == 999 && step >= 1 {
            panic!("mid-tuple clone failure");
        }
        NeedsDrop(self.0 + 10)
    }
}

// 1. Multi-field ADT without custom Drop -> pure 3-field DropGlue ladder
pub struct CompositeDrop3(pub NeedsDrop, pub NeedsDrop, pub NeedsDrop);

// 2. Multi-field ADT WITH custom Drop -> custom Drop::drop runs first, unwinding into field ladder
pub struct CustomPlusFieldsDrop(pub NeedsDrop, pub NeedsDrop);

impl Drop for CustomPlusFieldsDrop {
    #[inline(never)]
    fn drop(&mut self) {
        DROP_LOG.fetch_add(1000, Ordering::SeqCst);
    }
}

// 3. Local tuple struct constructor (DefKind::Ctor -> build_adt_ctor)
pub struct LocalTupleCtor(pub u32, pub u64);

// 4. Trait without #[track_caller] implemented by a #[track_caller] method -> Reify(Vtable)
pub trait UntrackedAction {
    fn act(&self, x: u32) -> (u32, u32);
}

pub struct TrackedReceiver(pub u32);

impl UntrackedAction for TrackedReceiver {
    #[track_caller]
    #[inline(never)]
    fn act(&self, x: u32) -> (u32, u32) {
        let loc = Location::caller();
        (loc.line(), self.0.wrapping_add(x))
    }
}

// 5. Trait with by-value `self: Self` -> VTableShim (*mut Self deref) when coerced to dyn
pub trait ByValueDyn {
    fn consume_val(self, bias: u32) -> u32;
}

impl ByValueDyn for u32 {
    #[inline(never)]
    fn consume_val(self, bias: u32) -> u32 {
        self.wrapping_add(bias)
    }
}

// 6. Standalone #[track_caller] function -> Reify(FnPtr) when coerced to fn pointer
#[track_caller]
#[inline(never)]
pub fn tracked_standalone(x: u32) -> (u32, u32) {
    let loc = Location::caller();
    (loc.line(), x.wrapping_mul(2))
}

#[inline(never)]
pub fn plain_two_arg(a: u32, b: u64) -> u64 {
    (a as u64).wrapping_add(b)
}

#[inline(never)]
pub fn invoke_fn_ref<F: Fn(u32, u64) -> u64>(f: &F, a: u32, b: u64) -> u64 {
    f(a, b)
}

#[inline(never)]
pub fn invoke_fn_once<F: FnOnce(u32) -> u32>(f: F, a: u32) -> u32 {
    f(a)
}

#[inline(never)]
pub fn exercise_all_shims() -> u64 {
    DROP_LOG.store(0, Ordering::SeqCst);
    CLONE_STEP.store(0, Ordering::SeqCst);

    // A. Exercise CompositeDrop3, CustomPlusFieldsDrop, and [NeedsDrop; 2] array DropGlue
    {
        let _c = CompositeDrop3(NeedsDrop(1), NeedsDrop(2), NeedsDrop(3));
        let _d = CustomPlusFieldsDrop(NeedsDrop(4), NeedsDrop(5));
        let _arr = [NeedsDrop(6), NeedsDrop(7)];
    }

    // B. Exercise Tuple CloneShim (3-tuple with prefix unwind cleanup) vs Array SpecArrayClone
    let tup = (NeedsDrop(1), NeedsDrop(2), 42_u64);
    let tup_cloned = tup.clone();
    let arr_src = [NeedsDrop(8), NeedsDrop(9)];
    let arr_cloned = arr_src.clone();

    // C. Exercise Reify(FnPtr) vs direct #[track_caller] call
    let direct_res = tracked_standalone(5);
    let reified_ptr: fn(u32) -> (u32, u32) = tracked_standalone;
    let indirect_res = reified_ptr(5);

    // D. Exercise Reify(Vtable) via &dyn UntrackedAction and Virtual Reify
    let recv = TrackedReceiver(10);
    let dyn_act: &dyn UntrackedAction = &recv;
    let vtable_res = dyn_act.act(7);
    static STATIC_RECV: TrackedReceiver = TrackedReceiver(10);
    let static_dyn: &(dyn UntrackedAction + 'static) = &STATIC_RECV;
    let virtual_reified: fn(_, u32) -> (u32, u32) =
        <dyn UntrackedAction as UntrackedAction>::act;
    let virtual_res = virtual_reified(static_dyn, 8);

    // E. Exercise VTableShim via &dyn ByValueDyn vtable construction
    let val_box: &dyn ByValueDyn = &77_u32;
    let vtable_ptr = core::ptr::from_ref(val_box);

    // F. Exercise FnPtrShim (<fn(u32, u64) -> u64 as Fn>::call) and FnPtr::addr shim
    let fp: fn(u32, u64) -> u64 = plain_two_arg;
    let fn_ptr_call_res = invoke_fn_ref(&fp, 3, 9);
    let fp_addr = FnPtr::addr(fp) as usize as u64;

    // G. Exercise ClosureOnceShim: move FnMut closure owning NeedsDrop upvar passed to FnOnce
    let guard = NeedsDrop(20);
    let mut acc = 0_u32;
    let mut fn_mut_closure = move |x: u32| -> u32 {
        acc = acc.wrapping_add(x).wrapping_add(guard.0);
        acc
    };
    let _first_mut_call = fn_mut_closure(1);
    let closure_once_res = invoke_fn_once(fn_mut_closure, 2);

    // H. Local & foreign ADT constructors + cross-crate generics
    let local_ctor_fn: fn(u32, u64) -> LocalTupleCtor = LocalTupleCtor;
    let lt = local_ctor_fn(11, 22);
    let foreign_ctor_fn: fn(u32, u64) -> dep_generics::GenericPair<u32, u64> =
        dep_generics::GenericPair;
    let gp = foreign_ctor_fn(lt.0, lt.1);
    let gp2 = dep_generics::map_first(gp, |v| v as u64 + 1);
    let mixed = dep_generics::inline_mix_u64(gp2.0, gp2.1);

    // I. Mid-tuple panic unwind test on CloneShim: (NeedsDrop(50), NeedsDrop(999), 7_u64)
    DROP_LOG.store(0, Ordering::SeqCst);
    CLONE_STEP.store(0, Ordering::SeqCst);
    let failing_tuple = (NeedsDrop(50), NeedsDrop(999), 7_u64);
    let unwind_caught = panic::catch_unwind(AssertUnwindSafe(|| {
        let _ = failing_tuple.clone();
    }))
    .is_err();
    let drop_log_after_failed_clone = DROP_LOG.load(Ordering::SeqCst) as u64;

    (tup_cloned.2)
        .wrapping_add(arr_cloned[0].0 as u64)
        .wrapping_add(direct_res.0 as u64)
        .wrapping_add(indirect_res.0 as u64)
        .wrapping_add(vtable_res.0 as u64)
        .wrapping_add(virtual_res.1 as u64)
        .wrapping_add(vtable_ptr.addr() as u64 & 0)
        .wrapping_add(fn_ptr_call_res)
        .wrapping_add(fp_addr & 0)
        .wrapping_add(closure_once_res as u64)
        .wrapping_add(mixed & 0xffff)
        .wrapping_add(if unwind_caught { 10000 } else { 0 })
        .wrapping_add(drop_log_after_failed_clone)
}

fn main() {
    let direct_line = tracked_standalone(1).0;
    let fn_ptr: fn(u32) -> (u32, u32) = tracked_standalone;
    let reified_fn_ptr_line = fn_ptr(1).0;

    let recv = TrackedReceiver(3);
    let direct_trait_line = recv.act(1).0;
    let dyn_ref: &dyn UntrackedAction = &recv;
    let reified_vtable_line = dyn_ref.act(1).0;

    DROP_LOG.store(0, Ordering::SeqCst);
    CLONE_STEP.store(0, Ordering::SeqCst);
    let failing_tuple = (NeedsDrop(50), NeedsDrop(999), 7_u64);
    let caught = panic::catch_unwind(AssertUnwindSafe(|| {
        let _ = failing_tuple.clone();
    }))
    .is_err();
    let prefix_cleanup_drop_delta = DROP_LOG.load(Ordering::SeqCst);
    drop(failing_tuple);

    let total = exercise_all_shims();
    println!(
        r#"{{"direct_line":{},"reified_fn_ptr_line":{},"direct_trait_line":{},"reified_vtable_line":{},"partial_clone_unwind_caught":{},"prefix_cleanup_drop_delta":{},"exercise_total":{}}}"#,
        direct_line,
        reified_fn_ptr_line,
        direct_trait_line,
        reified_vtable_line,
        caught,
        prefix_cleanup_drop_delta,
        total
    );
}
"""

# Dedicated minimal library with exactly ONE `FnOnce::call_once` (`ClosureOnceShim` with owned Drop upvar)
# so `-Zdump-mir=all` does not overwrite `core.ops-function-FnOnce-call_once.*.mir` with `lang_start`!
CLOSURE_ONCE_ISOLATED_RS = """\
#![crate_name = "closure_once_iso"]
#![crate_type = "lib"]

pub struct OwnedHandle(pub u32);

impl Drop for OwnedHandle {
    #[inline(never)]
    fn drop(&mut self) {}
}

#[inline(never)]
pub fn run_once<F: FnOnce(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

pub fn trigger_closure_once(h: OwnedHandle) -> u32 {
    let mut count = 0_u32;
    let mut c = move |x: u32| -> u32 {
        count = count.wrapping_add(x).wrapping_add(h.0);
        count
    };
    let _ = c(1);
    run_once(c, 2)
}
"""

# Dedicated `#![no_std]` library compiled with `-Zsanitizer=kcfi -Cpanic=abort` to observe
# `ReifyReason::FnPtr` vs `ReifyReason::Vtable` separation on the exact same method!
KCFI_REIFY_RS = """\
#![no_std]
#![crate_name = "kcfi_reify_probe"]
#![crate_type = "lib"]

pub trait DynAction {
    fn step(&self, x: u32) -> u32;
}

pub struct Actor(pub u32);

impl DynAction for Actor {
    #[track_caller]
    #[inline(never)]
    fn step(&self, x: u32) -> u32 {
        let _loc = core::panic::Location::caller();
        self.0.wrapping_add(x)
    }
}

pub fn take_both_vtable_and_fnptr(a: &Actor) -> (usize, fn(&Actor, u32) -> u32) {
    let dyn_ref: &dyn DynAction = a;
    let raw_meta = core::ptr::from_ref(dyn_ref) as *const () as usize;
    let fn_ptr: fn(&Actor, u32) -> u32 = <Actor as DynAction>::step;
    (raw_meta, fn_ptr)
}
"""


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and shutil.which(env_rustc):
        return shutil.which(env_rustc)  # type: ignore[return-value]
    for candidate in [
        shutil.which("rustc"),
        str(Path.home() / ".cargo" / "bin" / "rustc"),
    ]:
        if candidate and os.path.isfile(candidate) and os.access(candidate, os.X_OK):
            return candidate
    raise RuntimeError("unable to locate executable `rustc`")


def run_checked(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"command failed (exit {proc.returncode}): {' '.join(cmd)}\n"
            f"--- stdout ---\n{proc.stdout}\n--- stderr ---\n{proc.stderr}"
        )
    return proc


def scrub_text(text: str, work_dir: Path) -> str:
    scrubbed = text.replace(str(work_dir), "<PROBE_DIR>")
    tmp_root = re.escape(tempfile.gettempdir().rstrip("/"))
    home_root = re.escape(str(Path.home()).rstrip("/"))
    scrubbed = re.sub(rf"{tmp_root}/[^\s:\"')>]+", "<TMP_PATH>", scrubbed)
    scrubbed = re.sub(rf"{home_root}/[^\s:\"')>]+", "<HOME_PATH>", scrubbed)
    return scrubbed


def classify_mono_item(line: str) -> str:
    """Classify a `MONO_ITEM ...` line from `-Zprint-mono-items=yes`."""
    body = line[len("MONO_ITEM ") :].split(" @@ ")[0].strip()
    if body.startswith("static ") or body.startswith("global_asm "):
        return "static_or_global_asm"
    assert body.startswith("fn "), f"unexpected MONO_ITEM prefix: {line}"
    fn_desc = body[len("fn ") :]

    # `ClosureOnceShim` prints as `...::call_once - shim` (without parentheses),
    # whereas `DropGlue`, `Clone`, `Reify`, `VTable`, `FnPtr`, and `FnPtrAddr`
    # print as `... - shim(...)`.
    if fn_desc.endswith(" - shim"):
        return "shim_closure_once"

    if " - shim(" in fn_desc:
        callee_part, shim_part = fn_desc.split(" - shim(", 1)
        shim_tag = shim_part.rstrip(")")
        if "drop_in_place" in callee_part or "drop_glue" in callee_part:
            return "shim_drop_glue"
        if "::clone" in callee_part and "Clone>" in callee_part:
            return "shim_clone"
        if shim_tag.startswith("reify"):
            return "shim_reify"
        if shim_tag == "vtable":
            return "shim_vtable"
        if "FnPtr>::addr" in callee_part or "FnAddr>::as_ptr" in callee_part:
            return "shim_fn_ptr_addr"
        if (
            "std::ops::Fn<" in callee_part
            or "std::ops::FnMut<" in callee_part
            or "std::ops::FnOnce<" in callee_part
            or "core::ops::Fn<" in callee_part
            or "core::ops::FnMut<" in callee_part
            or "core::ops::FnOnce<" in callee_part
        ):
            return "shim_fn_ptr"
        return "shim_other"

    if fn_desc == "LocalTupleCtor":
        return "item_local_adt_ctor"
    if fn_desc.startswith("dep_generics::GenericPair"):
        return "item_foreign_adt_ctor"

    exact_local_impl_items = {
        "<NeedsDrop as std::ops::Drop>::drop",
        "<NeedsDrop as std::clone::Clone>::clone",
        "<CustomPlusFieldsDrop as std::ops::Drop>::drop",
        "<TrackedReceiver as UntrackedAction>::act",
        "<u32 as ByValueDyn>::consume_val",
        "main",
        "exercise_all_shims",
        "tracked_standalone",
        "plain_two_arg",
        "plain_two_arg",
    }
    local_fn_prefixes = (
        "invoke_fn_ref::",
        "invoke_fn_once::",
        "exercise_all_shims::",
        "main::",
    )
    if fn_desc in exact_local_impl_items or any(fn_desc.startswith(p) for p in local_fn_prefixes):
        return "item_local_hir_body"
    return "item_foreign_generic_or_inline"


def extract_mir_headers_from_emit_mir(mir_text: str) -> list[str]:
    headers: list[str] = []
    for line in mir_text.splitlines():
        if line.startswith("fn ") and line.endswith("{"):
            headers.append(line[:-2].strip())
    return headers


def extract_llvm_tracked_blocks(ll_text: str) -> list[dict[str, str]]:
    """Extract multi-line LLVM IR function headers + first call instruction for
    `tracked_standalone` and `TrackedReceiver::act` and their `{shim:reify#0}` wrappers."""
    lines = ll_text.splitlines()
    blocks: list[dict[str, str]] = []
    for i, line in enumerate(lines):
        if line.startswith("; shim_probe::tracked_standalone") or (
            line.startswith("; ") and "TrackedReceiver" in line and "UntrackedAction" in line
        ):
            comment = line[2:].strip()
            define_lines: list[str] = []
            body_preview: list[str] = []
            j = i + 1
            in_body = False
            while j < min(len(lines), i + 18):
                cur = lines[j]
                if cur.startswith("define "):
                    define_lines.append(cur)
                    if "{" in cur:
                        in_body = True
                elif define_lines and not in_body:
                    define_lines.append(cur)
                    if "{" in cur:
                        in_body = True
                elif in_body:
                    if cur.strip() == "}":
                        break
                    body_preview.append(cur)
                    if len(body_preview) >= 5:
                        break
                j += 1
            if define_lines:
                blocks.append(
                    {
                        "demangled_comment": comment,
                        "llvm_define": " ".join(s.strip() for s in define_lines),
                        "entry_instructions": "\n".join(body_preview),
                    }
                )
    return blocks


def run_probe() -> dict[str, Any]:
    rustc = find_rustc()
    ver_proc = subprocess.run([rustc, "--version", "-v"], text=True, capture_output=True, check=True)
    rustc_version_verbose = ver_proc.stdout.strip()

    with tempfile.TemporaryDirectory(prefix="mir_shims_probe_") as tmp_str:
        work_dir = Path(tmp_str)
        dep_rs = work_dir / "dep_generics.rs"
        main_rs = work_dir / "shim_probe.rs"
        closure_rs = work_dir / "closure_once_iso.rs"
        kcfi_rs = work_dir / "kcfi_reify_probe.rs"
        mir_dump_dir = work_dir / "mir_dump"
        closure_mir_dir = work_dir / "closure_mir_dump"
        stats_dir = work_dir / "mono_stats"
        mir_dump_dir.mkdir()
        closure_mir_dir.mkdir()
        stats_dir.mkdir()

        dep_rs.write_text(DEP_CRATE_RS, encoding="utf-8")
        main_rs.write_text(MAIN_CRATE_RS, encoding="utf-8")
        closure_rs.write_text(CLOSURE_ONCE_ISOLATED_RS, encoding="utf-8")
        kcfi_rs.write_text(KCFI_REIFY_RS, encoding="utf-8")

        # 1. Compile upstream `dep_generics` crate as rlib
        run_checked(
            [
                rustc,
                "--edition=2021",
                "-Copt-level=0",
                str(dep_rs),
                "-o",
                str(work_dir / "libdep_generics.rlib"),
            ],
            cwd=work_dir,
        )

        # 2. Compile `shim_probe`
        compile_proc = run_checked(
            [
                rustc,
                "--edition=2021",
                "-Copt-level=0",
                "-Ccodegen-units=1",
                "--extern",
                f"dep_generics={work_dir / 'libdep_generics.rlib'}",
                "--emit=mir,llvm-ir,link",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={mir_dump_dir}",
                "-Zprint-mono-items=yes",
                f"-Zdump-mono-stats={stats_dir}",
                "-Zdump-mono-stats-format=json",
                str(main_rs),
            ],
            cwd=work_dir,
        )

        # 3. Compile isolated `closure_once_iso` library to capture unobstructed 5-block
        #    `ClosureOnceShim` MIR (before/after `SimplifyCfg-make_shim`)
        run_checked(
            [
                rustc,
                "--edition=2021",
                "-Copt-level=0",
                "-Ccodegen-units=1",
                "--emit=obj",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={closure_mir_dir}",
                str(closure_rs),
                "-o",
                str(work_dir / "closure_once_iso.o"),
            ],
            cwd=work_dir,
        )

        # 4. Compile `#![no_std]` KCFI library to observe `ReifyReason::FnPtr` vs
        #    `ReifyReason::Vtable` separation on `<Actor as DynAction>::step`
        kcfi_proc = run_checked(
            [
                rustc,
                "--edition=2021",
                "--target=x86_64-unknown-linux-gnu",
                "-Copt-level=0",
                "-Ccodegen-units=1",
                "-Cpanic=abort",
                "-Zsanitizer=kcfi",
                "-Cunsafe-allow-abi-mismatch=sanitizer",
                "--emit=obj",
                "-Zprint-mono-items=yes",
                str(kcfi_rs),
                "-o",
                str(work_dir / "kcfi_reify_probe.o"),
            ],
            cwd=work_dir,
        )
        kcfi_mono_items = [
            scrub_text(line.split(" @@ ")[0].strip(), work_dir)
            for line in kcfi_proc.stdout.splitlines()
            if line.startswith("MONO_ITEM ")
        ]

        # 5. Execute the compiled `shim_probe` binary
        exec_proc = run_checked([str(work_dir / "shim_probe")], cwd=work_dir)
        runtime_observations = json.loads(exec_proc.stdout.strip())

        # 6. Parse `--emit=mir` (`tcx.mir_keys(())`)
        emit_mir_text = (work_dir / "shim_probe.mir").read_text(encoding="utf-8")
        mir_keys_fn_headers = [
            scrub_text(h, work_dir) for h in extract_mir_headers_from_emit_mir(emit_mir_text)
        ]

        # 7. Parse `-Zdump-mono-stats` JSON (`MonoItem::is_user_defined()` only!)
        mono_stats_path = stats_dir / "shim_probe.mono_items.json"
        mono_stats_entries = json.loads(mono_stats_path.read_text(encoding="utf-8"))
        dump_mono_stats_distinct_defs = len(mono_stats_entries)
        dump_mono_stats_total_instantiations = sum(
            int(entry["instantiation_count"]) for entry in mono_stats_entries
        )

        # 8. Parse `-Zprint-mono-items=yes` stdout lines
        mono_lines = [
            line.strip()
            for line in compile_proc.stdout.splitlines()
            if line.startswith("MONO_ITEM ")
        ]
        category_counts: dict[str, int] = {
            "item_local_hir_body": 0,
            "item_local_adt_ctor": 0,
            "item_foreign_generic_or_inline": 0,
            "item_foreign_adt_ctor": 0,
            "shim_drop_glue": 0,
            "shim_clone": 0,
            "shim_reify": 0,
            "shim_vtable": 0,
            "shim_fn_ptr": 0,
            "shim_fn_ptr_addr": 0,
            "shim_closure_once": 0,
            "shim_other": 0,
            "static_or_global_asm": 0,
        }
        shim_mono_items: list[str] = []
        local_and_ctor_mono_items: list[str] = []
        dep_generics_mono_items: list[str] = []

        for line in mono_lines:
            cat = classify_mono_item(line)
            category_counts[cat] = category_counts.get(cat, 0) + 1
            clean_item = scrub_text(line.split(" @@ ")[0], work_dir)
            if cat.startswith("shim_"):
                shim_mono_items.append(clean_item)
            elif cat in ("item_local_hir_body", "item_local_adt_ctor"):
                local_and_ctor_mono_items.append(clean_item)
            elif "dep_generics" in clean_item:
                dep_generics_mono_items.append(clean_item)

        total_fn_mono_items = sum(
            v for k, v in category_counts.items() if k != "static_or_global_asm"
        )
        total_shim_fn_mono_items = sum(
            v for k, v in category_counts.items() if k.startswith("shim_")
        )
        # Verify exact accounting identity: `dump_mono_stats` omits precisely the synthesized shims!
        omitted_by_dump_mono_stats = len(mono_lines) - dump_mono_stats_total_instantiations
        assert total_shim_fn_mono_items == omitted_by_dump_mono_stats, (
            f"shim count mismatch: classified {total_shim_fn_mono_items} shims vs "
            f"{omitted_by_dump_mono_stats} omitted by dump_mono_stats"
        )
        assert category_counts["shim_other"] == 0, (
            f"unclassified shims present: {shim_mono_items}"
        )

        total_local_mir_keys_fn_mono_items = (
            category_counts["item_local_hir_body"] + category_counts["item_local_adt_ctor"]
        )
        non_mir_keys_fn_mono_items = total_fn_mono_items - total_local_mir_keys_fn_mono_items

        # 9. Inspect `-Zdump-mir=all` files
        dump_files = sorted(p.name for p in mir_dump_dir.iterdir() if p.is_file())
        by_item_passes: dict[str, list[str]] = {}
        for fname in dump_files:
            parts = fname.split(".")
            if len(parts) >= 5:
                key = f"{parts[0]}.{parts[1]}"
                pass_stage = ".".join(parts[2:-1])
                by_item_passes.setdefault(key, []).append(pass_stage)

        make_shim_items = sorted(
            k
            for k, passes in by_item_passes.items()
            if any("SimplifyCfg-make_shim" in p for p in passes)
        )
        full_pipeline_items = sorted(
            k
            for k, passes in by_item_passes.items()
            if any("ElaborateDrops" in p for p in passes)
        )

        wanted_mir_patterns = [
            "ptr-drop_glue.CompositeDrop3.",
            "ptr-drop_glue.CustomPlusFieldsDrop.",
            "ptr-drop_glue.[NeedsDrop;2].",
            "clone-Clone-clone.",
            "tracked_standalone",
            "UntrackedAction-act",
            "ByValueDyn-consume_val",
            "ops-function-Fn-call.",
            "marker-FnPtr-addr.",
            "LocalTupleCtor",
        ]
        golden_mir_dumps: dict[str, str] = {}
        for fname in dump_files:
            if any(pat in fname for pat in wanted_mir_patterns):
                if (
                    "SimplifyCfg-make_shim." in fname
                    or fname.endswith("runtime-optimized.after.mir")
                    or fname.endswith("built.after.mir")
                ):
                    text = (mir_dump_dir / fname).read_text(encoding="utf-8")
                    golden_mir_dumps[fname] = scrub_text(text, work_dir)

        # Add isolated 5-block ClosureOnceShim MIR excerpts
        for p in sorted(closure_mir_dir.iterdir()):
            if "ops-function-FnOnce-call_once." in p.name and (
                "SimplifyCfg-make_shim." in p.name
                or p.name.endswith("runtime-optimized.after.mir")
            ):
                golden_mir_dumps[f"closure_once_iso::{p.name}"] = scrub_text(
                    p.read_text(encoding="utf-8"), work_dir
                )

        # Extract `LocalTupleCtor` MIR from `--emit=mir`
        for chunk in emit_mir_text.split("\n\nfn "):
            if "LocalTupleCtor(" in chunk[:80]:
                ctor_mir = ("fn " + chunk if not chunk.startswith("fn ") else chunk).split("\nfn ")[0]
                golden_mir_dumps["emit_mir::LocalTupleCtor"] = scrub_text(
                    ctor_mir.strip() + "\n", work_dir
                )

        # 10. Extract multi-line LLVM IR blocks for `tracked_standalone` and `TrackedReceiver::act`
        ll_text = (work_dir / "shim_probe.ll").read_text(encoding="utf-8")
        llvm_tracked_blocks = [
            {k: scrub_text(v, work_dir) for k, v in blk.items()}
            for blk in extract_llvm_tracked_blocks(ll_text)
        ]

        return {
            "rustc_version_verbose": rustc_version_verbose,
            "mono_item_accounting": {
                "total_mono_items_all_kinds": len(mono_lines),
                "total_fn_mono_items": total_fn_mono_items,
                "local_mir_keys_emitted_fn_bodies_count": len(mir_keys_fn_headers),
                "local_mir_keys_reachable_fn_mono_items": total_local_mir_keys_fn_mono_items,
                "non_mir_keys_fn_mono_items": non_mir_keys_fn_mono_items,
                "non_mir_keys_fn_share_pct": round(
                    100.0 * non_mir_keys_fn_mono_items / max(total_fn_mono_items, 1), 2
                ),
                "synthesized_shim_fn_mono_items": total_shim_fn_mono_items,
                "synthesized_shim_fn_share_pct": round(
                    100.0 * total_shim_fn_mono_items / max(total_fn_mono_items, 1), 2
                ),
                "dump_mono_stats_distinct_user_defs": dump_mono_stats_distinct_defs,
                "dump_mono_stats_user_fn_and_static_instantiations": dump_mono_stats_total_instantiations,
                "dump_mono_stats_omitted_shim_items": omitted_by_dump_mono_stats,
                "category_breakdown": category_counts,
            },
            "mir_keys_emitted_headers": mir_keys_fn_headers,
            "local_and_ctor_mono_items": local_and_ctor_mono_items,
            "dep_generics_mono_items": dep_generics_mono_items,
            "synthesized_shim_mono_items": shim_mono_items,
            "kcfi_reify_reason_mono_items": kcfi_mono_items,
            "pass_pipeline_comparison": {
                "full_analysis_to_runtime_items": full_pipeline_items,
                "make_shim_abbreviated_items": make_shim_items,
                "sample_full_item_pass_snapshots_plain_two_arg": by_item_passes[
                    "shim_probe.plain_two_arg"
                ],
                "sample_make_shim_pass_snapshots_clone": by_item_passes["core.clone-Clone-clone"],
                "dump_mir_stem_collision_tracked_standalone_count": len(
                    by_item_passes["shim_probe.tracked_standalone"]
                ),
                "dump_mir_pure_item_plain_two_arg_count": len(
                    by_item_passes["shim_probe.plain_two_arg"]
                ),
            },
            "llvm_ir_track_caller_vs_reify_blocks": llvm_tracked_blocks,
            "runtime_execution_verification": runtime_observations,
            "golden_mir_excerpts": golden_mir_dumps,
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional path to write JSON probe output",
    )
    args = parser.parse_args()
    result = run_probe()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(encoded, encoding="utf-8")
        acct = result["mono_item_accounting"]
        print(
            f"wrote {args.out} "
            f"(total_fn_mono_items={acct['total_fn_mono_items']}, "
            f"local_mir_keys_fns={acct['local_mir_keys_reachable_fn_mono_items']}, "
            f"non_mir_keys_share={acct['non_mir_keys_fn_share_pct']}%, "
            f"shims={acct['synthesized_shim_fn_mono_items']} [{acct['synthesized_shim_fn_share_pct']}%])"
        )
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
