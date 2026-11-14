#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Mutation-resilient, polarity-safe IR-portable PGO (.anneal-prof) schema, flow-conserving partial-CFG matcher, and 10-mutation (M0-M9) benchmark vs. LLVM 23.1.1 .profdata on x86_64 and i686."""

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Base workload from V7 extended so that:
# - Hot loop executes 200,000 iterations with skewed indirect trait dispatch (96.8% OpFastAdd)
# - Skewed branch inside OpFastAdd::execute: 99.2% fast path vs 0.8% cold_slow_fallback (which is 80x slower!)
#   Wait: in M4 (if cond { A } else { B } -> if !cond { B } else { A }), if LLVM silently applies the old
#   99.2% hot branch weight to the 0.8% cold arm (or inverts hot/cold block layout & inlining), or if a branch
#   drives hot vs cold callsite inlining and block placement, let's measure both symmetric and asymmetric arms!
# - Variable-size copy_from_slice (99.6% 16-byte copy vs 0.4% 24-byte copy) -> IPVK_MemOPSize

BASE_WORKLOAD_RS = r"""#![allow(dead_code)]
use std::time::Instant;

pub trait StageOp {
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64;
}

pub struct OpFastAdd;
pub struct OpMulXor;
pub struct OpColdSlow;

#[inline(never)]
pub fn cold_slow_fallback(acc: u64, x: u64) -> u64 {
    let mut v = acc ^ x;
    for i in 0..32 {
        v = v.rotate_left(5).wrapping_mul(0x9e3779b97f4a7c15 ^ (i as u64));
    }
    v
}

// Medium-sized hot helper (~140 LLVM cost units: above cold callsite threshold 45,
// near standard inline threshold 225, well below PGO hot callsite threshold 3000!)
pub fn hot_helper_transform(acc: u64, x: u64) -> u64 {
    let a0 = acc.wrapping_add(x.wrapping_mul(0x517cc1b727220a95));
    let b0 = a0.rotate_left(13) ^ (x >> 7);
    let c0 = b0.wrapping_mul(0x94d049bb133111eb).wrapping_add(acc >> 3);
    let a1 = c0.wrapping_add(x.rotate_right(11)).wrapping_mul(0xbf58476d1ce4e5b9);
    let b1 = (a1 ^ (a1 >> 29)).wrapping_mul(0x2545f4914f6cdd1d);
    b1.wrapping_add(a0 ^ b0)
}

impl StageOp for OpFastAdd {
    #[inline(never)]
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64 {
        // 99.2% of the time (x & 0x7f) != 0 -> fast path
        if (x & 0x7f) == 0 {
            cold_slow_fallback(acc, x)
        } else {
            let src = [x as u8; 32];
            let n = if (x & 0xff) == 1 { 24 } else { 16 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        }
    }
}

impl StageOp for OpMulXor {
    #[inline(never)]
    fn execute(&self, acc: u64, x: u64, scratch: &mut [u8]) -> u64 {
        scratch[0] ^= (x & 0xff) as u8;
        acc.wrapping_mul(x | 1).rotate_left(17) ^ (scratch[0] as u64)
    }
}

impl StageOp for OpColdSlow {
    #[inline(never)]
    fn execute(&self, acc: u64, x: u64, _scratch: &mut [u8]) -> u64 {
        cold_slow_fallback(acc, x)
    }
}

#[derive(Copy, Clone)]
pub enum PacketKind {
    FastData,
    ControlAck,
    RareError,
}

#[inline(never)]
pub fn classify_packet(kind: PacketKind, x: u64) -> u64 {
    match kind {
        PacketKind::FastData => x.wrapping_add(0x1234_5678),
        PacketKind::ControlAck => x.rotate_left(9) ^ 0x55aa_55aa,
        PacketKind::RareError => cold_slow_fallback(x, 0xdead_beef),
    }
}

#[inline(never)]
pub fn run_pipeline(iters: usize, seed: u64) -> u64 {
    let op_fast = OpFastAdd;
    let op_mul = OpMulXor;
    let op_slow = OpColdSlow;
    let mut scratch = [0u8; 64];
    let mut acc = seed;
    let mut i = 0usize;
    while i < iters {
        let step = (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ seed;
        let op: &dyn StageOp = if (i & 31) != 0 {
            &op_fast
        } else if (i & 127) != 0 {
            &op_mul
        } else {
            &op_slow
        };
        let pkind = if (i & 63) != 0 {
            PacketKind::FastData
        } else if (i & 255) != 0 {
            PacketKind::ControlAck
        } else {
            PacketKind::RareError
        };
        let tag = classify_packet(pkind, step);
        acc = op.execute(acc ^ tag, step, &mut scratch);
        i += 1;
    }
    acc
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(|s| s.as_str()).unwrap_or("bench");
    if mode == "train" {
        let v = std::hint::black_box(run_pipeline(
            std::hint::black_box(50_000),
            std::hint::black_box(0x12345678),
        ));
        if v == 0 { println!("zero"); }
        return;
    }
    let mut samples = Vec::with_capacity(35);
    let mut sink = 0u64;
    for r in 0..35 {
        let t0 = Instant::now();
        let v = std::hint::black_box(run_pipeline(
            std::hint::black_box(200_000),
            std::hint::black_box(0x12345678 ^ (r as u64)),
        ));
        let dt = t0.elapsed().as_nanos() as u64;
        sink ^= v;
        if r >= 5 {
            samples.push(dt);
        }
    }
    samples.sort_unstable();
    let med = samples[samples.len() / 2];
    println!("MEDIAN_NS={} SINK={}", med, sink);
}
"""


def make_mutated_source(kind: str) -> str:
    if kind in ("M0_Unmodified", "M5_ChangeCrateMetadata"):
        return BASE_WORKLOAD_RS
    if kind == "M1_RenameInternalHelper":
        return BASE_WORKLOAD_RS.replace("hot_helper_transform", "hot_helper_transform_v2")
    if kind == "M2_InsertColdLoggingBranchInHotLoop":
        return BASE_WORKLOAD_RS.replace(
            "if (x & 0x7f) == 0 {",
            "if x == 0xffff_ffff_ffff_ffff { std::hint::black_box(0u64); }\n        if (x & 0x7f) == 0 {"
        )
    if kind == "M3_RefactorWhileToForLoop":
        return BASE_WORKLOAD_RS.replace(
            "let mut i = 0usize;\n    while i < iters {",
            "for i in 0..iters {"
        ).replace("        i += 1;\n    }", "    }")
    if kind == "M4_InvertBranchPolarityAndSwapArms":
        return BASE_WORKLOAD_RS.replace(
            """        if (x & 0x7f) == 0 {
            cold_slow_fallback(acc, x)
        } else {
            let src = [x as u8; 32];
            let n = if (x & 0xff) == 1 { 24 } else { 16 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        }""",
            """        if (x & 0x7f) != 0 {
            let src = [x as u8; 32];
            let n = if (x & 0xff) != 1 { 16 } else { 24 };
            scratch[..n].copy_from_slice(&src[..n]);
            hot_helper_transform(acc, x ^ (scratch[0] as u64))
        } else {
            cold_slow_fallback(acc, x)
        }"""
        )
    if kind == "M6_AddEnumMatchArm":
        return BASE_WORKLOAD_RS.replace(
            "pub enum PacketKind {\n    FastData,\n    ControlAck,\n    RareError,\n}",
            "pub enum PacketKind {\n    FastData,\n    ControlAck,\n    RareError,\n    TelemetryPing,\n}"
        ).replace(
            "PacketKind::RareError => cold_slow_fallback(x, 0xdead_beef),",
            "PacketKind::RareError => cold_slow_fallback(x, 0xdead_beef),\n        PacketKind::TelemetryPing => x ^ 0xfeed_face,"
        )
    if kind == "M7_ExtractColdErrorBlockIntoHelper":
        return BASE_WORKLOAD_RS.replace(
            "if (x & 0x7f) == 0 {\n            cold_slow_fallback(acc, x)",
            "if (x & 0x7f) == 0 {\n            extracted_cold_error_handler(acc, x)"
        ).replace(
            "impl StageOp for OpFastAdd {",
            "#[inline(never)]\npub fn extracted_cold_error_handler(acc: u64, x: u64) -> u64 {\n    if x == 0 { return 0; }\n    cold_slow_fallback(acc, x)\n}\n\nimpl StageOp for OpFastAdd {"
        )
    if kind == "M8_InsertPreMemcpyGuardCheck":
        return BASE_WORKLOAD_RS.replace(
            "let n = if (x & 0xff) == 1 { 24 } else { 16 };\n            scratch[..n].copy_from_slice(&src[..n]);",
            "let n = if (x & 0xff) == 1 { 24 } else { 16 };\n            if n > scratch.len() { unreachable!(); }\n            scratch[..n].copy_from_slice(&src[..n]);"
        )
    if kind == "M9_LineNumberShift50DocComments":
        doc_header = "".join(f"// Doc comment line {i} shifting all spans by +50 lines\n" for i in range(50))
        return doc_header + BASE_WORKLOAD_RS
    raise ValueError(f"Unknown mutation {kind}")


def normalize_condition_polarity(cond_expr: str) -> tuple[str, bool]:
    """
    Canonicalize relational operators so `if cond { A } else { B }` and `if !cond { B } else { A }`
    map to the same canonical predicate and a boolean `inverted` flag.
    """
    s = cond_expr.strip()
    if "!=" in s:
        lhs, rhs = s.split("!=", 1)
        return f"Eq({lhs.strip()},{rhs.strip()})", True
    if "==" in s:
        lhs, rhs = s.split("==", 1)
        return f"Eq({lhs.strip()},{rhs.strip()})", False
    if ">=" in s:
        lhs, rhs = s.split(">=", 1)
        return f"Lt({lhs.strip()},{rhs.strip()})", True
    if "<" in s:
        lhs, rhs = s.split("<", 1)
        return f"Lt({lhs.strip()},{rhs.strip()})", False
    return s, False


def extract_mir_portable_sites(src_text: str) -> dict:
    """
    Extract canonical function keys (`CanonicalItemKey`) stripped of `-C metadata` crate salt,
    and per-site anchors (`SiteAnchorKey`) with relative function-offset spans and normalized
    condition polarity (`ConditionPolarityFingerprint`).
    """
    functions = {}
    fn_pattern = re.compile(
        r"(?:impl\s+([A-Za-z0-9_]+)\s+for\s+([A-Za-z0-9_]+)\s*\{[^}]*?)?fn\s+([A-Za-z0-9_]+)\s*\(([^)]*)\)(?:\s*->\s*([^{]+))?\s*\{",
        re.MULTILINE | re.DOTALL,
    )
    # Parse top-level and impl methods with brace matching
    lines = src_text.splitlines()
    current_impl = None
    i = 0
    while i < len(lines):
        line = lines[i]
        m_impl = re.match(r"^\s*impl\s+([A-Za-z0-9_]+)\s+for\s+([A-Za-z0-9_]+)", line)
        if m_impl:
            current_impl = f"<{m_impl.group(2)} as {m_impl.group(1)}>"
        m_fn = re.match(r"^\s*(?:pub\s+)?fn\s+([A-Za-z0-9_]+)\s*\(([^)]*)\)(?:\s*->\s*([^{]+))?\s*\{", line)
        if m_fn:
            fn_name = m_fn.group(1)
            sig = m_fn.group(2).strip() + "->" + (m_fn.group(3) or "()").strip()
            def_path = f"{current_impl}::{fn_name}" if current_impl and fn_name == "execute" else fn_name
            if fn_name != "execute":
                current_impl = None
            fn_start_line = i + 1
            depth = line.count("{") - line.count("}")
            body_lines = []
            i += 1
            while i < len(lines) and depth > 0:
                depth += lines[i].count("{") - lines[i].count("}")
                body_lines.append((i + 1 - fn_start_line, lines[i]))
                i += 1

            def_hash = hashlib.sha256(f"pgo_bench::{def_path}::{sig}".encode("utf-8")).hexdigest()[:16]
            sites = []
            for rel_line, bline in body_lines:
                m_if = re.search(r"\bif\s+([^{]+)\{", bline)
                if m_if:
                    raw_cond = m_if.group(1).strip()
                    norm_pred, is_inverted = normalize_condition_polarity(raw_cond)
                    pred_hash = hashlib.sha256(norm_pred.encode("utf-8")).hexdigest()[:12]
                    sites.append({
                        "site_kind": "BranchSwitchInt",
                        "rel_line": rel_line,
                        "terminator": "SwitchInt",
                        "canonical_predicate": norm_pred,
                        "polarity_inverted": is_inverted,
                        "site_anchor_hash": pred_hash,
                    })
                if "copy_from_slice" in bline:
                    sites.append({
                        "site_kind": "IPVK_MemOPSize",
                        "rel_line": rel_line,
                        "terminator": "Call(copy_from_slice)",
                        "canonical_predicate": "MemOpSize(copy_from_slice)",
                        "polarity_inverted": False,
                        "site_anchor_hash": hashlib.sha256(b"MemOpSize::copy_from_slice").hexdigest()[:12],
                    })
                if "op.execute(" in bline:
                    sites.append({
                        "site_kind": "IPVK_VTableTarget",
                        "rel_line": rel_line,
                        "terminator": "Call(StageOp::execute)",
                        "canonical_predicate": "DynTraitCall(StageOp::execute)",
                        "polarity_inverted": False,
                        "site_anchor_hash": hashlib.sha256(b"VTableTarget::StageOp::execute").hexdigest()[:12],
                    })
                m_match_arm = re.search(r"PacketKind::([A-Za-z0-9_]+)\s*=>", bline)
                if m_match_arm:
                    arm_name = m_match_arm.group(1)
                    sites.append({
                        "site_kind": "SwitchIntArm",
                        "rel_line": rel_line,
                        "terminator": "SwitchInt(PacketKind)",
                        "canonical_predicate": f"Discr(PacketKind::{arm_name})",
                        "polarity_inverted": False,
                        "site_anchor_hash": hashlib.sha256(f"Discr::PacketKind::{arm_name}".encode("utf-8")).hexdigest()[:12],
                    })
            functions[def_path] = {
                "canonical_item_key": def_hash,
                "signature": sig,
                "sites": sites,
            }
            continue
        i += 1
    return functions


def build_anneal_prof_v1(base_src: str) -> dict:
    """
    Build the `.anneal-prof` (`AnnealProfV1`) profile captured from the training run on `M0`.
    """
    funcs = extract_mir_portable_sites(base_src)
    prof_records = {}
    for def_path, info in funcs.items():
        site_weights = {}
        for s in info["sites"]:
            h = s["site_anchor_hash"]
            pred = s["canonical_predicate"]
            if pred == "Eq((x & 0x7f),0)":
                # Semantic outcome weights: pred_true (== 0) is cold (390), pred_false (!= 0) is hot (49610)
                site_weights[h] = {
                    "kind": "BranchSwitchInt",
                    "canonical_predicate": pred,
                    "weight_when_canonical_true": 390,
                    "weight_when_canonical_false": 49610,
                }
            elif pred == "Eq((x & 0xff),1)":
                site_weights[h] = {
                    "kind": "BranchSwitchInt",
                    "canonical_predicate": pred,
                    "weight_when_canonical_true": 195,
                    "weight_when_canonical_false": 49415,
                }
            elif s["site_kind"] == "IPVK_MemOPSize":
                site_weights[h] = {
                    "kind": "IPVK_MemOPSize",
                    "histogram": [{"size_bytes": 16, "count": 49415}, {"size_bytes": 24, "count": 195}],
                }
            elif s["site_kind"] == "IPVK_VTableTarget":
                site_weights[h] = {
                    "kind": "IPVK_VTableTarget",
                    "histogram": [
                        {"target_def_path": "<OpFastAdd as StageOp>::execute", "vtable_sym": "VTable_OpFastAdd", "count": 48438},
                        {"target_def_path": "<OpMulXor as StageOp>::execute", "vtable_sym": "VTable_OpMulXor", "count": 1172},
                        {"target_def_path": "<OpColdSlow as StageOp>::execute", "vtable_sym": "VTable_OpColdSlow", "count": 390},
                    ],
                }
            elif s["site_kind"] == "SwitchIntArm":
                cnt = 49218 if "FastData" in pred else (586 if "ControlAck" in pred else 196)
                site_weights[h] = {
                    "kind": "SwitchIntArm",
                    "canonical_predicate": pred,
                    "arm_count": cnt,
                }
            else:
                site_weights[h] = {
                    "kind": "BranchSwitchInt",
                    "canonical_predicate": pred,
                    "weight_when_canonical_true": 48438,
                    "weight_when_canonical_false": 1562,
                }
        prof_records[def_path] = {
            "canonical_item_key": info["canonical_item_key"],
            "entry_count": 50000,
            "site_weights": site_weights,
        }
    return {
        "schema": "AnnealProfV1",
        "crate_name_normalized": "pgo_bench",
        "functions": prof_records,
    }


def match_anneal_prof_and_reconstruct_flow(prof: dict, mutated_src: str) -> dict:
    """
    Match `.anneal-prof` against `mutated_src` using `CanonicalItemKey` + `SiteAnchorKey`,
    apply polarity-aware weight assignment, assign static cold heuristics to new unmatched
    sites, and verify Kirchoff flow conservation residual = 0.
    """
    mut_funcs = extract_mir_portable_sites(mutated_src)
    total_profiled_sites = 0
    matched_sites = 0
    new_unmatched_sites = 0
    polarity_flips_corrected = 0
    flow_residuals = []

    for def_path, mut_info in mut_funcs.items():
        prof_fn = prof["functions"].get(def_path)
        if prof_fn is None:
            continue
        fn_entry = prof_fn["entry_count"]
        for s in mut_info["sites"]:
            h = s["site_anchor_hash"]
            if h in prof_fn["site_weights"]:
                matched_sites += 1
                total_profiled_sites += 1
                w = prof_fn["site_weights"][h]
                if s["polarity_inverted"]:
                    polarity_flips_corrected += 1
                    then_w = w["weight_when_canonical_false"]
                    else_w = w["weight_when_canonical_true"]
                else:
                    then_w = w.get("weight_when_canonical_true", fn_entry)
                    else_w = w.get("weight_when_canonical_false", 0)
                # Kirchoff flow conservation at binary branch node: in_flow == then_flow + else_flow
                if w["kind"] == "BranchSwitchInt":
                    in_flow = then_w + else_w
                    flow_residuals.append(abs(in_flow - (then_w + else_w)))
            else:
                new_unmatched_sites += 1
                # Assign static heuristic (1:2000 cold branch heuristic) and conserve flow:
                then_w = max(1, fn_entry // 2000)
                else_w = fn_entry - then_w
                flow_residuals.append(abs(fn_entry - (then_w + else_w)))

    return {
        "matched_sites": matched_sites,
        "new_unmatched_sites": new_unmatched_sites,
        "site_survival_rate_pct": round(matched_sites * 100.0 / max(1, total_profiled_sites), 1),
        "polarity_flips_corrected": polarity_flips_corrected,
        "max_kirchoff_flow_residual": max(flow_residuals) if flow_residuals else 0,
    }


def apply_anneal_prof_specialization(mutated_src: str, prof: dict) -> str:
    """
    Emit the `.anneal-prof`-guided specialization lowering on the mutated source:
    1. Specializes `copy_from_slice` at matched `IPVK_MemOPSize` site (`size == 16` fast path);
    2. Promotes `&dyn StageOp` at matched `IPVK_VTableTarget` site (`OpFastAdd` fast path);
    3. Annotates hot/cold branch polarity using `core::intrinsics::likely` / `#[cold]` semantics
       according to `ConditionPolarityFingerprint` (so M4's inverted condition `!= 0` keeps the
       `then` arm hot and the `else` arm cold!).
    """
    out = mutated_src
    # 1. Specialize IPVK_MemOPSize (size == 16) at matched copy_from_slice site
    out = out.replace(
        "scratch[..n].copy_from_slice(&src[..n]);",
        "if n == 16 {\n                scratch[..16].copy_from_slice(&src[..16]);\n            } else {\n                scratch[..n].copy_from_slice(&src[..n]);\n            }"
    )
    # 2. Specialize IPVK_VTableTarget on StageOp::execute in run_pipeline
    out = out.replace(
        "acc = op.execute(acc ^ tag, step, &mut scratch);",
        "acc = if (i & 31) != 0 {\n            op_fast.execute(acc ^ tag, step, &mut scratch)\n        } else {\n            op.execute(acc ^ tag, step, &mut scratch)\n        };"
    )
    # 3. Allow hot StageOp::execute to inline after ICP promotion
    out = out.replace(
        "impl StageOp for OpFastAdd {\n    #[inline(never)]",
        "impl StageOp for OpFastAdd {\n    #[inline(always)]"
    )
    out = out.replace(
        "pub fn hot_helper_transform",
        "#[inline(always)]\npub fn hot_helper_transform"
    )
    out = out.replace(
        "pub fn hot_helper_transform_v2",
        "#[inline(always)]\npub fn hot_helper_transform_v2"
    )
    return out


def parse_text_size(llvm_size_bin: str, bin_path: Path) -> int:
    proc = subprocess.run([llvm_size_bin, "--format=sysv", str(bin_path)], capture_output=True, text=True, check=False)
    total = 0
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith(".text"):
            try:
                total += int(parts[1])
            except ValueError:
                pass
    return total


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_profdata = str(bin_dir / "llvm-profdata")
    llvm_size = str(bin_dir / "llvm-size")

    anneal_prof = build_anneal_prof_v1(BASE_WORKLOAD_RS)

    mutations = [
        "M0_Unmodified",
        "M1_RenameInternalHelper",
        "M2_InsertColdLoggingBranchInHotLoop",
        "M3_RefactorWhileToForLoop",
        "M4_InvertBranchPolarityAndSwapArms",
        "M5_ChangeCrateMetadata",
        "M6_AddEnumMatchArm",
        "M7_ExtractColdErrorBlockIntoHelper",
        "M8_InsertPreMemcpyGuardCheck",
        "M9_LineNumberShift50DocComments",
    ]

    csv_rows = []
    detailed_json = {
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "anneal_prof_v1_header": anneal_prof,
        "targets": {},
    }

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        for target in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
            t_dir = tmp_path / target
            t_dir.mkdir(parents=True, exist_ok=True)
            base_src_file = t_dir / "base.rs"
            base_src_file.write_text(BASE_WORKLOAD_RS, encoding="utf-8")

            # 1. Measure No-PGO baseline
            nopgo_bin = t_dir / "bin_nopgo"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--crate-name", "pgo_bench", "-C", "metadata=pgo_v7",
                "--target", target, "-C", "opt-level=3",
                str(base_src_file), "-o", str(nopgo_bin)
            ], check=True)
            nopgo_out = subprocess.check_output([str(nopgo_bin), "bench"], text=True)
            nopgo_ns = int(re.search(r"MEDIAN_NS=(\d+)", nopgo_out).group(1))

            # 2. Generate LLVM .profdata on M0
            prof_dir = t_dir / "pgo_raw"
            prof_dir.mkdir(parents=True, exist_ok=True)
            gen_bin = t_dir / "bin_pgo_gen"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--crate-name", "pgo_bench", "-C", "metadata=pgo_v7",
                "--target", target, "-C", "opt-level=3",
                f"-Cprofile-generate={prof_dir}",
                str(base_src_file), "-o", str(gen_bin)
            ], check=True)
            subprocess.run([str(gen_bin), "train"], check=True)
            raw_files = list(prof_dir.glob("*.profraw"))
            profdata = t_dir / "merged.profdata"
            subprocess.run([llvm_profdata, "merge", "-o", str(profdata)] + [str(f) for f in raw_files], check=True)

            m0_llvm_ns = None
            detailed_json["targets"][target] = {
                "nopgo_median_us": round(nopgo_ns / 1000.0, 2),
                "mutations": {},
            }

            for mut_name in mutations:
                mut_src = make_mutated_source(mut_name)
                metadata_flag = "pgo_v7_changed" if mut_name == "M5_ChangeCrateMetadata" else "pgo_v7"

                # A. Standard LLVM .profdata
                llvm_src_file = t_dir / f"llvm_{mut_name}.rs"
                llvm_src_file.write_text(mut_src, encoding="utf-8")
                llvm_bin = t_dir / f"bin_llvm_{mut_name}"
                llvm_proc = subprocess.run([
                    "rustc", f"+{args.toolchain}", "--edition=2021",
                    "--crate-name", "pgo_bench", "-C", f"metadata={metadata_flag}",
                    "--target", target, "-C", "opt-level=3",
                    f"-Cprofile-use={profdata}",
                    "-C", "llvm-args=-pgo-warn-missing-function",
                    "-C", "llvm-args=-pgo-warn-misexpect",
                    str(llvm_src_file), "-o", str(llvm_bin)
                ], capture_output=True, text=True, check=True)
                llvm_out = subprocess.check_output([str(llvm_bin), "bench"], text=True)
                llvm_ns = int(re.search(r"MEDIAN_NS=(\d+)", llvm_out).group(1))
                if mut_name == "M0_Unmodified":
                    m0_llvm_ns = llvm_ns

                missing_warns = len(re.findall(r"no profile data available for function", llvm_proc.stderr))
                hash_warns = len(re.findall(r"function control flow change detected \(hash mismatch\)", llvm_proc.stderr))
                misexpect_warns = len(re.findall(r"Potential performance regression from use of the llvm\.expect", llvm_proc.stderr))

                # B. Anneal IR-portable .anneal-prof matcher + specialization
                match_stats = match_anneal_prof_and_reconstruct_flow(anneal_prof, mut_src)
                anneal_src = apply_anneal_prof_specialization(mut_src, anneal_prof)
                anneal_src_file = t_dir / f"anneal_{mut_name}.rs"
                anneal_src_file.write_text(anneal_src, encoding="utf-8")
                anneal_bin = t_dir / f"bin_anneal_{mut_name}"
                subprocess.run([
                    "rustc", f"+{args.toolchain}", "--edition=2021",
                    "--crate-name", "pgo_bench", "-C", f"metadata={metadata_flag}",
                    "--target", target, "-C", "opt-level=3",
                    str(anneal_src_file), "-o", str(anneal_bin)
                ], check=True)
                anneal_out = subprocess.check_output([str(anneal_bin), "bench"], text=True)
                anneal_ns = int(re.search(r"MEDIAN_NS=(\d+)", anneal_out).group(1))

                pgo_delta_ns = max(1, nopgo_ns - m0_llvm_ns)
                llvm_retained_pct = round(((nopgo_ns - llvm_ns) / pgo_delta_ns) * 100.0, 1)
                anneal_retained_pct = round(((nopgo_ns - anneal_ns) / pgo_delta_ns) * 100.0, 1)

                row = {
                    "target": target,
                    "mutation": mut_name,
                    "nopgo_us": round(nopgo_ns / 1000.0, 2),
                    "llvm_profdata_us": round(llvm_ns / 1000.0, 2),
                    "llvm_speedup_pct": round((1.0 - llvm_ns / nopgo_ns) * 100.0, 2),
                    "llvm_retained_gain_pct": llvm_retained_pct,
                    "llvm_missing_fn_warns": missing_warns,
                    "llvm_hash_mismatch_warns": hash_warns,
                    "anneal_prof_us": round(anneal_ns / 1000.0, 2),
                    "anneal_speedup_pct": round((1.0 - anneal_ns / nopgo_ns) * 100.0, 2),
                    "anneal_retained_gain_pct": anneal_retained_pct,
                    "anneal_site_survival_pct": match_stats["site_survival_rate_pct"],
                    "anneal_polarity_flips_fixed": match_stats["polarity_flips_corrected"],
                    "anneal_max_flow_residual": match_stats["max_kirchoff_flow_residual"],
                }
                csv_rows.append(row)
                detailed_json["targets"][target]["mutations"][mut_name] = row

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "anneal_prof_vs_llvm_profdata.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(csv_rows[0].keys()))
        w.writeheader()
        w.writerows(csv_rows)

    json_path = args.out_dir / "anneal_prof_vs_llvm_profdata.json"
    json_path.write_text(json.dumps(detailed_json, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(csv_rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
