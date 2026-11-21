#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe evaluating `SpecConeCollector` v1 (`Adt`-only field walk)
versus v2 (full `ty.walk()`, `Ref`/`RawPtr`/`Slice`/`Array`/`Tuple`/`FnPtr`
pointee closure, stepwise `PlaceRef::ty`, and `GlobalAlloc::Static` foreign/mut
closure) across an 18-vector indirect specification-tampering suite (`V01`..`V18`,
all with 100% byte-identical `hot_ref` tokens) and 4 benign controls (`C01`..`C04`)."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any

HOT_REF_FN = """pub fn hot_ref(
    hdr: &PacketHdr,
    badge: BoundedByte,
    ref_niche: &RefBoundedByte,
    pair_slice: &[SlicePair],
    raw_ptr: *const RawTarget,
    arr_wrap: [ArrInner; 4],
    tup_wrap: (TupInner, u8, u8),
    cb: HookFn,
    nn: core::ptr::NonNull<SmartTarget>,
    view: &BufView<'_>,
    guard: ScopeGuard,
) -> (u64, PaddedPair) {
    let _g = guard;
    let lut: &[u8; 4] = &[PROMOTED_K0, 2, 3, 4];
    let slice: &[u8] = &*view;
    let _reborrow = &*ref_niche;
    let slice_ptr_nonnull = (pair_slice as *const [SlicePair] as *const u8 as usize != 0) as u64;
    let ext_addr = (&raw const EXT_COUNTER) as usize;
    let mut acc = <FastPolicy as AccPolicy>::SEED;
    acc = acc.wrapping_add(hdr.tag as u64).wrapping_add(hdr.len as u64);
    acc = acc.wrapping_add(badge.as_u8() as u64);
    acc = acc.wrapping_add(lut[0] as u64);
    acc = acc.wrapping_add(<FastPolicy as AccPolicy>::TABLE[0] as u64);
    acc = acc.wrapping_add(slice_ptr_nonnull);
    acc = acc.wrapping_add((raw_ptr as usize == 0) as u64);
    acc = acc.wrapping_add((ext_addr == 0) as u64);
    let _ = (arr_wrap, tup_wrap, cb, nn);
    if !slice.is_empty() {
        acc = <FastPolicy as AccPolicy>::combine(acc, slice[0]);
    }
    acc = mix_step(acc);
    let pair = make_padded_pair(hdr.tag, hdr.len);
    (acc, pair)
}"""


def build_driver_v2(tc: str, driver_src: Path, out_dir: Path) -> tuple[Path, str]:
    sysroot = subprocess.check_output(
        ["rustup", "run", tc, "rustc", "--print", "sysroot"], text=True
    ).strip()
    version_line = (
        subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
        .strip()
        .splitlines()[0]
    )
    extra_cfgs: list[str] = []
    if "1.98." in version_line:
        extra_cfgs = ["--cfg", "anneal_rustc_1_98"]
    elif "1.102." in version_line:
        extra_cfgs = ["--cfg", "anneal_rustc_1_102"]

    drv_bin = out_dir / f"anneal_driver_v2_{tc.replace('/', '_')}"
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    subprocess.run(
        [
            "rustup",
            "run",
            tc,
            "rustc",
            "--edition=2021",
            "-O",
            f"-Clink-arg=-Wl,-rpath,{sysroot}/lib",
            *extra_cfgs,
            str(driver_src),
            "-o",
            str(drv_bin),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )
    return drv_bin, sysroot


def render_crate(overrides: dict[str, str]) -> str:
    defaults = {
        "prefix_lines": "",
        "promoted_k0": "const PROMOTED_K0: u8 = 1;",
        "table_data": "const TABLE_DATA: [u32; 4] = [10, 20, 30, 40];",
        "packet_hdr": """#[repr(C)]
pub struct PacketHdr {
    pub tag: u8,
    pub len: u32,
}""",
        "padded_pair": """#[repr(C)]
pub struct PaddedPair {
    pub a: u8,
    pub b: u32,
}
pub fn make_padded_pair(a: u8, b: u32) -> PaddedPair {
    PaddedPair { a, b }
}""",
        "bounded_byte": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct BoundedByte(u8);
impl BoundedByte {
    pub fn as_u8(self) -> u8 { self.0 }
}""",
        "ref_bounded_byte": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct RefBoundedByte(pub u8);""",
        "slice_pair": """#[repr(C)]
pub struct SlicePair {
    pub a: u8,
    pub b: u32,
}""",
        "raw_target": """#[repr(C)]
pub struct RawTarget {
    pub tag: u8,
    pub payload: u32,
}""",
        "arr_inner": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct ArrInner(pub u8);""",
        "tup_inner": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct TupInner(pub u8);""",
        "hook_fn": """#[repr(C)]
#[derive(Copy, Clone)]
pub struct FnArgAdt {
    pub a: u8,
    pub b: u32,
}
pub type HookFn = extern "C" fn(FnArgAdt) -> u64;""",
        "extern_static": """#[repr(C)]
pub struct ExtStatVal(pub u32);
extern "C" {
    pub static EXT_COUNTER: ExtStatVal;
}""",
        "smart_target": """#[repr(C)]
pub struct SmartTarget {
    pub a: u8,
    pub b: u32,
}""",
        "scope_guard": """pub static DROP_OBS: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
pub struct ScopeGuard(pub u64);
impl Drop for ScopeGuard {
    fn drop(&mut self) {
        DROP_OBS.fetch_add(self.0, core::sync::atomic::Ordering::Relaxed);
    }
}""",
        "buf_view": """pub struct BufView<'a>(pub &'a [u8]);
impl<'a> core::ops::Deref for BufView<'a> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        self.0
    }
}""",
        "policy_trait_and_impl": """pub trait AccPolicy {
    const SEED: u64 = 7;
    const TABLE: &'static [u32; 4] = &TABLE_DATA;
    fn combine(a: u64, b: u8) -> u64 {
        a.wrapping_add(b as u64)
    }
}
pub struct FastPolicy;
impl AccPolicy for FastPolicy {}""",
        "mix_helpers": """pub fn leaf_mix(x: u64) -> u64 {
    x.wrapping_mul(31)
}
pub fn mix_step(x: u64) -> u64 {
    leaf_mix(x).wrapping_add(3)
}""",
        "hot_ref": HOT_REF_FN,
        "hot_opt_and_extra": """pub unsafe fn hot_opt(mut x: u64) -> u64 {
    core::arch::asm!("add {0:r}, 1", inout(reg) x, options(pure, nomem, nostack));
    x
}
pub fn unrelated_helper(v: u64) -> u64 {
    v ^ 0x55aa
}""",
    }
    cfg = {**defaults, **overrides}
    keys = [
        "prefix_lines",
        "promoted_k0",
        "table_data",
        "packet_hdr",
        "padded_pair",
        "bounded_byte",
        "scope_guard",
        "buf_view",
        "policy_trait_and_impl",
        "mix_helpers",
        "hot_ref",
        "hot_opt_and_extra",
        "ref_bounded_byte",
        "slice_pair",
        "raw_target",
        "arr_inner",
        "tup_inner",
        "hook_fn",
        "extern_static",
        "smart_target",
    ]
    return "\n\n".join(cfg[k] for k in keys) + "\n"


def build_scenarios() -> dict[str, tuple[str, dict[str, str]]]:
    return {
        # --- Original 10 Indirect Tampering Vectors (V01..V10) ---
        "V01_transitive_callee_body": (
            "tamper_orig",
            {
                "mix_helpers": """pub fn leaf_mix(x: u64) -> u64 {
    x.wrapping_mul(33)
}
pub fn mix_step(x: u64) -> u64 {
    leaf_mix(x).wrapping_add(3)
}"""
            },
        ),
        "V02_adt_repr_packed_offsets": (
            "tamper_orig",
            {
                "packet_hdr": """#[repr(C, packed)]
pub struct PacketHdr {
    pub tag: u8,
    pub len: u32,
}"""
            },
        ),
        "V03_adt_uninit_padding_mask": (
            "tamper_orig",
            {
                "padded_pair": """#[repr(C)]
pub struct PaddedPair {
    pub a: u8,
    pub _explicit_pad: [u8; 3],
    pub b: u32,
}
pub fn make_padded_pair(a: u8, b: u32) -> PaddedPair {
    PaddedPair { a, _explicit_pad: [0; 3], b }
}"""
            },
        ),
        "V04_adt_niche_valid_range": (
            "tamper_orig",
            {
                "bounded_byte": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct BoundedByte(core::num::NonZeroU8);
impl BoundedByte {
    pub fn as_u8(self) -> u8 { self.0.get() }
}"""
            },
        ),
        "V05_implicit_drop_glue": (
            "tamper_orig",
            {
                "scope_guard": """pub static DROP_OBS: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
pub struct ScopeGuard(pub u64);
impl Drop for ScopeGuard {
    fn drop(&mut self) {
        DROP_OBS.fetch_add(self.0.wrapping_mul(2), core::sync::atomic::Ordering::Relaxed);
    }
}"""
            },
        ),
        "V06_trait_default_method_override": (
            "tamper_orig",
            {
                "policy_trait_and_impl": """pub trait AccPolicy {
    const SEED: u64 = 7;
    const TABLE: &'static [u32; 4] = &TABLE_DATA;
    fn combine(a: u64, b: u8) -> u64 {
        a.wrapping_add(b as u64)
    }
}
pub struct FastPolicy;
impl AccPolicy for FastPolicy {
    fn combine(a: u64, b: u8) -> u64 {
        a ^ (b as u64)
    }
}"""
            },
        ),
        "V07_const_allocation_bytes": (
            "tamper_orig",
            {"table_data": "const TABLE_DATA: [u32; 4] = [99, 20, 30, 40];"},
        ),
        "V08_deref_coercion_impl": (
            "tamper_orig",
            {
                "buf_view": """pub struct BufView<'a>(pub &'a [u8]);
impl<'a> core::ops::Deref for BufView<'a> {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        if self.0.len() > 1 { &self.0[1..] } else { self.0 }
    }
}"""
            },
        ),
        "V09_callee_abi_and_target_feature": (
            "tamper_orig",
            {
                "mix_helpers": """pub fn leaf_mix(x: u64) -> u64 {
    x.wrapping_mul(31)
}
#[target_feature(enable = "sse4.2")]
pub unsafe fn mix_step_inner(x: u64) -> u64 {
    leaf_mix(x).wrapping_add(3)
}
pub extern "C" fn mix_step(x: u64) -> u64 {
    leaf_mix(x).wrapping_add(3)
}"""
            },
        ),
        "V10_promoted_const_array_element": (
            "tamper_orig",
            {"promoted_k0": "const PROMOTED_K0: u8 = 77;"},
        ),
        # --- 8 New Pointee / Compound / FnPtr / Extern-Static / Smart-Ptr Vectors (V11..V18) ---
        "V11_niche_behind_shared_ref": (
            "tamper_new_closure",
            {
                "ref_bounded_byte": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct RefBoundedByte(pub core::num::NonZeroU8);"""
            },
        ),
        "V12_slice_elem_padding_mask": (
            "tamper_new_closure",
            {
                "slice_pair": """#[repr(C)]
pub struct SlicePair {
    pub a: u8,
    pub _pad: [u8; 3],
    pub b: u32,
}"""
            },
        ),
        "V13_raw_ptr_pointee_packing": (
            "tamper_new_closure",
            {
                "raw_target": """#[repr(C, packed)]
pub struct RawTarget {
    pub tag: u8,
    pub payload: u32,
}"""
            },
        ),
        "V14_array_wrapper_inner_niche": (
            "tamper_new_closure",
            {
                "arr_inner": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct ArrInner(pub core::num::NonZeroU8);"""
            },
        ),
        "V15_tuple3_wrapper_inner_niche": (
            "tamper_new_closure",
            {
                "tup_inner": """#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct TupInner(pub core::num::NonZeroU8);"""
            },
        ),
        "V16_fn_ptr_arg_abi_passmode": (
            "tamper_new_closure",
            {
                "hook_fn": """#[repr(C)]
#[derive(Copy, Clone)]
pub struct FnArgAdt {
    pub a: u8,
    pub b: u64,
    pub c: u64,
    pub d: u64,
}
pub type HookFn = extern "C" fn(FnArgAdt) -> u64;"""
            },
        ),
        "V17_extern_static_type_and_mutability": (
            "tamper_new_closure",
            {
                "extern_static": """#[repr(C)]
pub struct ExtStatVal(pub u64);
extern "C" {
    #[link_name = "alt_ext_counter"]
    pub static EXT_COUNTER: ExtStatVal;
}"""
            },
        ),
        "V18_nonnull_smart_ptr_pointee_drop": (
            "tamper_new_closure",
            {
                "smart_target": """#[repr(C)]
pub struct SmartTarget {
    pub a: u8,
    pub _pad: [u8; 3],
    pub b: u32,
}
impl Drop for SmartTarget {
    fn drop(&mut self) {
        DROP_OBS.fetch_add(9, core::sync::atomic::Ordering::Relaxed);
    }
}"""
            },
        ),
        # --- 4 Benign Controls (C01..C04) ---
        "C01_optimize_hot_opt_asm": (
            "benign",
            {
                "hot_opt_and_extra": """fn opt_private_helper(z: u64) -> u64 { z.rotate_left(5) }
pub unsafe fn hot_opt(mut x: u64) -> u64 {
    x = opt_private_helper(x);
    core::arch::asm!("lea {0:r}, [{0:r} + 9]", inout(reg) x, options(pure, nomem, nostack));
    x
}
pub fn unrelated_helper(v: u64) -> u64 {
    v ^ 0x55aa
}"""
            },
        ),
        "C02_unrelated_module_and_types": (
            "benign",
            {
                "hot_opt_and_extra": """pub unsafe fn hot_opt(mut x: u64) -> u64 {
    core::arch::asm!("add {0:r}, 1", inout(reg) x, options(pure, nomem, nostack));
    x
}
pub fn unrelated_helper(v: u64) -> u64 {
    v.wrapping_mul(99991)
}
pub mod extra_mod {
    #[repr(C)]
    pub struct ExtraType { pub x: u128, pub y: u8 }
    pub static EXTRA_STATIC: u64 = 12345;
}"""
            },
        ),
        "C03_comments_and_50_line_shift": (
            "benign",
            {"prefix_lines": "\n".join(f"// comment line {i}" for i in range(50))},
        ),
        "C04_local_variable_alpha_rename": (
            "benign",
            {
                "hot_ref": HOT_REF_FN.replace("mut acc", "mut total_sum")
                .replace("acc =", "total_sum =")
                .replace("acc.", "total_sum.")
                .replace("(acc,", "(total_sum,")
                .replace("combine(acc,", "combine(total_sum,")
                .replace("mix_step(acc)", "mix_step(total_sum)")
                .replace("lut", "k_table")
                .replace("let slice:", "let bytes_ref:")
                .replace("!slice.", "!bytes_ref.")
                .replace("combine(total_sum, slice[0])", "combine(total_sum, bytes_ref[0])")
                .replace("_g", "_guard_slot")
                .replace("_reborrow", "_rb_slot")
                .replace("slice_ptr_nonnull", "has_slice_ptr")
                .replace("ext_addr", "ext_sym_addr")
                .replace("let pair =", "let out_pair =")
                .replace(", pair)", ", out_pair)")
            },
        ),
        "C05_unrelated_items_inserted_above_hot_ref": (
            "benign",
            {
                "prefix_lines": """#[repr(C)]
pub struct AboveUnrelated {
    pub x: u64,
    pub y: u64,
}
pub fn above_unused_fn(v: u64) -> u64 {
    v.wrapping_add(17)
}"""
            },
        ),
    }


def run_speccone(
    drv_bin: Path,
    sysroot: str,
    src_code: str,
    name: str,
    closure_mode: str,
    work: Path,
) -> dict[str, Any]:
    rs_file = work / f"{name}_{closure_mode}.rs"
    out_json = work / f"{name}_{closure_mode}_cone.json"
    out_rlib = work / f"lib{name}_{closure_mode}.rlib"
    rs_file.write_text(src_code)

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env["ANNEAL_SYSROOT"] = sysroot
    env["ANNEAL_ASM_WRAP_MODE"] = "debug_tombstone_cr"
    env["ANNEAL_SPECCONE_FN"] = "hot_ref"
    env["ANNEAL_SPECCONE_CLOSURE"] = closure_mode
    env["ANNEAL_SPECCONE_OUT"] = str(out_json)

    proc = subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=speccone_case",
            "--crate-type=rlib",
            "-C",
            "opt-level=2",
            str(rs_file),
            "-o",
            str(out_rlib),
        ],
        env=env,
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"SpecCone ({closure_mode}) compile failed for {name}:\n{proc.stderr}"
        )
    return json.loads(out_json.read_text())


def extract_hot_ref_tokens(src: str) -> str:
    idx = src.index("pub fn hot_ref(")
    end = src.index("\npub unsafe fn hot_opt(")
    chunk = src[idx:end]
    if "\nfn opt_private_helper" in chunk:
        chunk = chunk[: chunk.index("\nfn opt_private_helper")]
    return chunk.strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--toolchains",
        nargs="+",
        default=["nightly-2026-06-01", "1.99.1", "nightly"],
    )
    parser.add_argument("--out", type=str, default="")
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    driver_src = here / "anneal_driver_v2.rs"
    scenarios = build_scenarios()

    results: dict[str, Any] = {"toolchains": {}}
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        base_src = render_crate({})
        base_tokens = extract_hot_ref_tokens(base_src)
        base_token_sha = hashlib.sha256(base_tokens.encode("utf-8")).hexdigest()[:16]

        for tc in args.toolchains:
            tc_w = work / tc.replace("/", "_")
            tc_w.mkdir(exist_ok=True)
            drv_bin, sysroot = build_driver_v2(tc, driver_src, tc_w)
            ver = (
                subprocess.check_output(
                    ["rustup", "run", tc, "rustc", "-vV"], text=True
                )
                .strip()
                .splitlines()[0]
            )

            base_v1 = run_speccone(drv_bin, sysroot, base_src, "baseline", "v1", tc_w)
            base_v2 = run_speccone(drv_bin, sysroot, base_src, "baseline", "v2", tc_w)

            case_outcomes: dict[str, Any] = {}
            v1_detected_orig = 0
            v1_detected_new = 0
            v2_detected_orig = 0
            v2_detected_new = 0
            v1_fp = 0
            v2_fp = 0
            token_detected = 0

            for sc_name, (kind, ov) in scenarios.items():
                sc_src = render_crate(ov)
                sc_tokens = extract_hot_ref_tokens(sc_src)
                sc_token_sha = hashlib.sha256(sc_tokens.encode("utf-8")).hexdigest()[:16]
                if kind != "benign" and sc_tokens != base_tokens:
                    raise AssertionError(f"{sc_name} mutated hot_ref source tokens!")

                cone_v1 = run_speccone(drv_bin, sysroot, sc_src, sc_name, "v1", tc_w)
                cone_v2 = run_speccone(drv_bin, sysroot, sc_src, sc_name, "v2", tc_w)
                c_v1 = cone_v1["spec_cone_hash"] != base_v1["spec_cone_hash"]
                c_v2 = cone_v2["spec_cone_hash"] != base_v2["spec_cone_hash"]
                tok_c = sc_token_sha != base_token_sha

                if kind == "tamper_orig":
                    v1_detected_orig += int(c_v1)
                    v2_detected_orig += int(c_v2)
                    token_detected += int(tok_c)
                elif kind == "tamper_new_closure":
                    v1_detected_new += int(c_v1)
                    v2_detected_new += int(c_v2)
                    token_detected += int(tok_c)
                else:
                    v1_fp += int(c_v1)
                    v2_fp += int(c_v2)

                case_outcomes[sc_name] = {
                    "kind": kind,
                    "hot_ref_tokens_byte_identical": sc_tokens == base_tokens,
                    "naive_token_hash_changed": tok_c,
                    "v1_adt_only_changed": c_v1,
                    "v2_full_closure_changed": c_v2,
                    "v1_num_types": cone_v1["num_types"],
                    "v2_num_types": cone_v2["num_types"],
                    "v2_num_instances": cone_v2["num_instances"],
                    "v2_spec_cone_hash_16": cone_v2["spec_cone_hash"][:16],
                }

            results["toolchains"][tc] = {
                "rustc_version": ver,
                "v1_baseline_num_instances": base_v1["num_instances"],
                "v1_baseline_num_types": base_v1["num_types"],
                "v2_baseline_num_instances": base_v2["num_instances"],
                "v2_baseline_num_types": base_v2["num_types"],
                "v2_baseline_num_allocs": base_v2["num_allocs"],
                "v2_baseline_hash_16": base_v2["spec_cone_hash"][:16],
                "v1_detected_orig_10": v1_detected_orig,
                "v1_detected_new_8": v1_detected_new,
                "v1_total_detected_18": v1_detected_orig + v1_detected_new,
                "v2_detected_orig_10": v2_detected_orig,
                "v2_detected_new_8": v2_detected_new,
                "v2_total_detected_18": v2_detected_orig + v2_detected_new,
                "naive_token_detected_18": token_detected,
                "v1_benign_false_positives_5": v1_fp,
                "v2_benign_false_positives_5": v2_fp,
                "cases": case_outcomes,
            }
            assert v2_detected_orig + v2_detected_new == 18, (tc, v2_detected_orig, v2_detected_new)
            assert v2_fp == 0, (tc, v2_fp)

    out_json = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(out_json)
    print(out_json)


if __name__ == "__main__":
    main()
