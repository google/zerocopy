#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe evaluating the `TyCtxt`-driven `SpecConeHash` collector against a
10-vector indirect specification-tampering suite (where `hot_ref` source tokens remain
100% byte-for-byte identical) and 4 benign code-evolution controls."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from probe_driver_cgu_and_invariance import build_driver

HOT_REF_FN = """pub fn hot_ref(
    hdr: &PacketHdr,
    badge: BoundedByte,
    view: &BufView<'_>,
    guard: ScopeGuard,
) -> (u64, PaddedPair) {
    let _g = guard;
    let lut: &[u8; 4] = &[PROMOTED_K0, 2, 3, 4];
    let slice: &[u8] = &*view;
    let mut acc = <FastPolicy as AccPolicy>::SEED;
    acc = acc.wrapping_add(hdr.tag as u64).wrapping_add(hdr.len as u64);
    acc = acc.wrapping_add(badge.as_u8() as u64);
    acc = acc.wrapping_add(lut[0] as u64);
    acc = acc.wrapping_add(<FastPolicy as AccPolicy>::TABLE[0] as u64);
    if !slice.is_empty() {
        acc = <FastPolicy as AccPolicy>::combine(acc, slice[0]);
    }
    acc = mix_step(acc);
    let pair = make_padded_pair(hdr.tag, hdr.len);
    (acc, pair)
}"""


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
    return "\n\n".join(
        [
            cfg["prefix_lines"],
            cfg["promoted_k0"],
            cfg["table_data"],
            cfg["packet_hdr"],
            cfg["padded_pair"],
            cfg["bounded_byte"],
            cfg["scope_guard"],
            cfg["buf_view"],
            cfg["policy_trait_and_impl"],
            cfg["mix_helpers"],
            cfg["hot_ref"],
            cfg["hot_opt_and_extra"],
        ]
    ) + "\n"


def build_scenarios() -> dict[str, tuple[str, dict[str, str]]]:
    # Each entry maps `scenario_id -> (kind, overrides)` where kind is "tamper" or "benign".
    return {
        "V01_transitive_callee_body": (
            "tamper",
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
            "tamper",
            {
                "packet_hdr": """#[repr(C, packed)]
pub struct PacketHdr {
    pub tag: u8,
    pub len: u32,
}"""
            },
        ),
        "V03_adt_uninit_padding_mask": (
            "tamper",
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
            "tamper",
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
            "tamper",
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
            "tamper",
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
            "tamper",
            {"table_data": "const TABLE_DATA: [u32; 4] = [99, 20, 30, 40];"},
        ),
        "V08_deref_coercion_impl": (
            "tamper",
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
            "tamper",
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
            "tamper",
            {"promoted_k0": "const PROMOTED_K0: u8 = 77;"},
        ),
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
                .replace("slice", "bytes_ref")
                .replace("_g", "_guard_slot")
                .replace("let pair =", "let out_pair =")
                .replace(", pair)", ", out_pair)")
            },
        ),
    }


def run_speccone(
    drv_bin: Path, sysroot: str, src_code: str, name: str, work: Path
) -> dict[str, Any]:
    rs_file = work / f"{name}.rs"
    out_json = work / f"{name}_cone.json"
    out_rlib = work / f"lib{name}.rlib"
    rs_file.write_text(src_code)

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env["ANNEAL_SYSROOT"] = sysroot
    env["ANNEAL_ASM_WRAP_MODE"] = "off"
    env["ANNEAL_SPECCONE_FN"] = "hot_ref"
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
        raise RuntimeError(f"SpecCone compile failed for {name}:\n{proc.stderr}")
    return json.loads(out_json.read_text())


def extract_hot_ref_tokens(src: str) -> str:
    idx = src.index("pub fn hot_ref(")
    end = src.index("\npub unsafe fn hot_opt(")
    # Trim any benign helper right before `hot_opt`.
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
    driver_src = here / "anneal_driver_prototype.rs"
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
            drv_bin, sysroot = build_driver(tc, driver_src, tc_w)
            ver = (
                subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
                .strip()
                .splitlines()[0]
            )

            base_cone = run_speccone(drv_bin, sysroot, base_src, "baseline", tc_w)
            base_hash = base_cone["spec_cone_hash"]

            case_outcomes: dict[str, Any] = {}
            tamper_detected = 0
            tamper_total = 0
            benign_false_positives = 0
            benign_total = 0
            naive_token_detected_tampers = 0

            for sc_name, (kind, ov) in scenarios.items():
                sc_src = render_crate(ov)
                sc_tokens = extract_hot_ref_tokens(sc_src)
                sc_token_sha = hashlib.sha256(sc_tokens.encode("utf-8")).hexdigest()[:16]
                if kind == "tamper" and sc_tokens != base_tokens:
                    raise AssertionError(f"{sc_name} mutated hot_ref source tokens!")

                cone = run_speccone(drv_bin, sysroot, sc_src, sc_name, tc_w)
                changed = cone["spec_cone_hash"] != base_hash
                token_changed = sc_token_sha != base_token_sha

                if kind == "tamper":
                    tamper_total += 1
                    if changed:
                        tamper_detected += 1
                    if token_changed:
                        naive_token_detected_tampers += 1
                else:
                    benign_total += 1
                    if changed:
                        benign_false_positives += 1

                case_outcomes[sc_name] = {
                    "kind": kind,
                    "hot_ref_tokens_byte_identical": sc_tokens == base_tokens,
                    "naive_token_hash_changed": token_changed,
                    "tyctxt_speccone_changed": changed,
                    "spec_cone_hash_16": cone["spec_cone_hash"][:16],
                    "num_instances": cone["num_instances"],
                    "num_types": cone["num_types"],
                    "num_allocs": cone["num_allocs"],
                }

            results["toolchains"][tc] = {
                "rustc_version": ver,
                "baseline_spec_cone_hash_16": base_hash[:16],
                "baseline_num_instances": base_cone["num_instances"],
                "baseline_num_types": base_cone["num_types"],
                "baseline_num_allocs": base_cone["num_allocs"],
                "tamper_detected": tamper_detected,
                "tamper_total": tamper_total,
                "benign_false_positives": benign_false_positives,
                "benign_total": benign_total,
                "naive_token_detected_tampers": naive_token_detected_tampers,
                "cases": case_outcomes,
            }

    out_json = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(out_json)
    print(out_json)


if __name__ == "__main__":
    main()
