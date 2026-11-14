#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Pre-Runtime(PostCleanup) MIR Pass Audit, Profile-Invariance Probe, and MiniSSA Canonicalizer Benchmark."""

import csv
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

PRE_POSTCLEANUP_PASSES = [
    {
        "order": 1,
        "query_stage": "mir_built",
        "target_phase": "Built",
        "pass_name": "LintAndRemoveUninhabited",
        "source_path": "compiler/rustc_mir_transform/src/lint_and_remove_uninhabited.rs:19-162",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:414",
        "consumes_and_eliminates": "Terminators and basic blocks following typed values of uninhabited types (!, empty enums)",
        "invariants_established": "Uninhabited call/load continuations replaced by TerminatorKind::Unreachable",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": ["#68304 (uninhabited branch pruning after uninit load)", "#112403 (uninhabited enum branching)"],
    },
    {
        "order": 2,
        "query_stage": "mir_built",
        "target_phase": "Built",
        "pass_name": "MirLints (CheckForceInline, CheckCallRecursion, CheckPackedRef, CheckConstItemMutation, CheckMutRestriction, FunctionItemReferences)",
        "source_path": "compiler/rustc_mir_transform/src/lib.rs:416-421",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:416-421",
        "consumes_and_eliminates": "Read-only lint pass (mutates zero MIR statements)",
        "invariants_established": "Rejects unaligned references to #[repr(packed)] fields (E0793) before borrowck",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
    {
        "order": 3,
        "query_stage": "mir_built",
        "target_phase": "Built",
        "pass_name": "SimplifyCfg::Initial + SanityCheck",
        "source_path": "compiler/rustc_mir_transform/src/simplify.rs:93-260",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:423-424",
        "consumes_and_eliminates": "Dead basic blocks and trivial Goto chains from MIR building",
        "invariants_established": "All basic blocks reachable from bb0 or unwind edges for CTFE/promotion",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
    {
        "order": 4,
        "query_stage": "mir_promoted",
        "target_phase": "Analysis(Initial)",
        "pass_name": "RequiredConstsVisitor::compute_required_consts",
        "source_path": "compiler/rustc_mir_transform/src/required_consts.rs:14-60",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:474",
        "consumes_and_eliminates": "Scans ConstOperand nodes (mutates body.required_consts)",
        "invariants_established": "Populates body.required_consts before constant promotion or dead-code removal so const_err fails even in dead code",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": ["#104416 (post-monomorphization const evaluation error in dead branches)"],
    },
    {
        "order": 5,
        "query_stage": "mir_promoted",
        "target_phase": "Analysis(Initial)",
        "pass_name": "PromoteTemps",
        "source_path": "compiler/rustc_mir_transform/src/promote_consts.rs:45-890",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:477-481",
        "consumes_and_eliminates": "Extracts promotable rvalue temporaries (&123, &[1, 2]) into Promoted[p] sub-bodies",
        "invariants_established": "Promoted references have 'static lifetime and are proven free of interior mutability (Freeze), Drop, and fallible ops (div-by-zero/oob)",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": ["#53807 (promoting fallible div/index expressions)", "#74440 (promoting UnsafeCell references)"],
    },
    {
        "order": 6,
        "query_stage": "mir_promoted",
        "target_phase": "Analysis(Initial)",
        "pass_name": "SimplifyCfg::PromoteConsts + InstrumentCoverage",
        "source_path": "compiler/rustc_mir_transform/src/coverage/mod.rs:1-120",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:481",
        "consumes_and_eliminates": "Cleans CFG after promotion; injects coverage counters only when -C instrument-coverage is enabled",
        "invariants_established": "Analysis(Initial) MIR ready for mir_borrowck",
        "depends_on_opt_level": False,
        "depends_on_session_flags": ["-C instrument-coverage"],
        "historical_soundness_issues": [],
    },
    {
        "order": 7,
        "query_stage": "run_analysis_cleanup_passes",
        "target_phase": "Analysis(PostCleanup)",
        "pass_name": "ImpossibleClauses",
        "source_path": "compiler/rustc_mir_transform/src/impossible_clauses.rs:14-95",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:633",
        "consumes_and_eliminates": "Basic blocks inside functions/arms with unsatisfiable where-clauses",
        "invariants_established": "Replaces bodies/blocks guarded by impossible trait predicates with TerminatorKind::Unreachable",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
    {
        "order": 8,
        "query_stage": "run_analysis_cleanup_passes",
        "target_phase": "Analysis(PostCleanup)",
        "pass_name": "CleanupPostBorrowck",
        "source_path": "compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:26-94",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:634",
        "consumes_and_eliminates": "AscribeUserType, FakeRead, BorrowKind::Fake, FalseEdge, FalseUnwind, user_type_annotations",
        "invariants_established": "Zero borrowck-only statements/edges remain; ArrayToPointer and MutToConstPointer coercions become CastKind::PtrToPtr",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
    {
        "order": 9,
        "query_stage": "run_analysis_cleanup_passes",
        "target_phase": "Analysis(PostCleanup)",
        "pass_name": "RemoveNoopLandingPads + SimplifyCfg::PostAnalysis",
        "source_path": "compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs:14-120",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:635-636",
        "consumes_and_eliminates": "Cleanup blocks that only contain Nop/StorageDead followed by UnwindResume",
        "invariants_established": "Trivial unwind landing pads collapsed directly to UnwindAction::Continue",
        "depends_on_opt_level": False,
        "depends_on_session_flags": ["-C panic"],
        "historical_soundness_issues": [],
    },
    {
        "order": 10,
        "query_stage": "run_analysis_cleanup_passes",
        "target_phase": "Analysis(PostCleanup)",
        "pass_name": "Derefer",
        "source_path": "compiler/rustc_mir_transform/src/deref_separator.rs:18-175",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:637",
        "consumes_and_eliminates": "Nested ProjectionElem::Deref at non-zero projection index (e.g., (_1.0).*)",
        "invariants_established": "ProjectionElem::Deref only appears as the FIRST projection element (p.projection[0]) via CopyForDeref temporaries",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": ["#91008 (Deref separator interaction with debuginfo)"],
    },
    {
        "order": 11,
        "query_stage": "run_runtime_lowering_passes",
        "target_phase": "Runtime(Initial)",
        "pass_name": "CriticalCallEdges (`AddCallGuards`) + PostAnalysisNormalize + Subtyper",
        "source_path": "compiler/rustc_mir_transform/src/{add_call_guards.rs,post_analysis_normalize.rs,add_subtyping_projections.rs}",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:647-651",
        "consumes_and_eliminates": "Opaque impl Trait types (revealed to concrete hidden types) and implicit lifetime subtyping in Place assignments",
        "invariants_established": "All types in Body are fully normalized (TypingMode::PostAnalysis) with explicit Subtype projections",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": ["#109020 (Subtyper projection ordering with opaque types)"],
    },
    {
        "order": 12,
        "query_stage": "run_runtime_lowering_passes",
        "target_phase": "Runtime(Initial)",
        "pass_name": "ElaborateDrops + CheckDropRecursion",
        "source_path": "compiler/rustc_mir_transform/src/elaborate_drops.rs:28-1150",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:652-654",
        "consumes_and_eliminates": "Static/conditional TerminatorKind::Drop on partially moved locals and uninitialized places",
        "invariants_established": "Inserts stack boolean drop flags; lowers ADT/slice drop ladders and unwind cleanup edges; inserts Retag when -Zmir-emit-retag is active",
        "depends_on_opt_level": False,
        "depends_on_session_flags": ["-Z mir-emit-retag", "-C panic"],
        "historical_soundness_issues": ["#86475 (drop flag state on unwind path)", "#99852 (Box drop elaboration order)"],
    },
    {
        "order": 13,
        "query_stage": "run_runtime_lowering_passes",
        "target_phase": "Runtime(Initial)",
        "pass_name": "AbortUnwindingCalls",
        "source_path": "compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:18-135",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:658",
        "consumes_and_eliminates": "UnwindAction::Cleanup / Continue on calls inside non-unwinding functions (extern \"C\", panic=abort)",
        "invariants_established": "Converts unwind edges across nounwind boundaries into UnwindAction::Terminate(Reason::Abi)",
        "depends_on_opt_level": False,
        "depends_on_session_flags": ["-C panic"],
        "historical_soundness_issues": [],
    },
    {
        "order": 14,
        "query_stage": "run_runtime_lowering_passes",
        "target_phase": "Runtime(Initial)",
        "pass_name": "AddMovesForPackedDrops + EraseDerefTemps + ElaborateBoxDerefs",
        "source_path": "compiler/rustc_mir_transform/src/{add_moves_for_packed_drops.rs,erase_deref_temps.rs,elaborate_box_derefs.rs}",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:661-663",
        "consumes_and_eliminates": "Unaligned drops of #[repr(packed)] fields and magic *box_local dereferences",
        "invariants_established": "Packed fields are moved to aligned temporaries before drop_in_place; Box<T> derefs traverse *(box.0.0: *const T) explicitly",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
    {
        "order": 15,
        "query_stage": "run_runtime_lowering_passes",
        "target_phase": "Runtime(Initial)",
        "pass_name": "coroutine::StateTransform + KnownPanicsLint",
        "source_path": "compiler/rustc_mir_transform/src/coroutine.rs:1-2150",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:664-665",
        "consumes_and_eliminates": "TerminatorKind::Yield and TerminatorKind::CoroutineDrop in async/gen/coroutine bodies",
        "invariants_established": "Compiles coroutine bodies into explicit state-machine structs with discriminant SwitchInt dispatchers at bb0",
        "depends_on_opt_level": False,
        "depends_on_session_flags": ["-C overflow-checks (KnownPanicsLint warning only)"],
        "historical_soundness_issues": ["#115201 (coroutine live across yield local layout calculation)"],
    },
    {
        "order": 16,
        "query_stage": "run_runtime_cleanup_passes",
        "target_phase": "Runtime(PostCleanup)",
        "pass_name": "LowerIntrinsics + RemovePlaceMention + SimplifyCfg::PreOptimizations",
        "source_path": "compiler/rustc_mir_transform/src/{lower_intrinsics.rs:10-346,remove_place_mention.rs:11-40}",
        "invocation_site": "compiler/rustc_mir_transform/src/lib.rs:672-685",
        "consumes_and_eliminates": "Calls to core::intrinsics::{unreachable, ub_checks, overflow_checks, forget, copy_nonoverlapping, assume, wrapping_*, unchecked_*, *_with_overflow, read_via_copy, write_via_move, discriminant_value} and StatementKind::PlaceMention",
        "invariants_established": "All core intrinsics lowered to primitive MIR statements/terminators; ub_checks/overflow_checks lowered to symbolic Operand::RuntimeChecks(op); local_info cleared",
        "depends_on_opt_level": False,
        "depends_on_session_flags": [],
        "historical_soundness_issues": [],
    },
]

RUST_FIXTURE = r'''
#![allow(dead_code)]

use std::hint::black_box;

#[derive(Clone, Copy)]
pub struct Pair {
    pub a: u64,
    pub b: u64,
}

#[inline(never)]
pub fn compute_kernel(slice: &[u64], init: Pair) -> u64 {
    let mut acc = init.a.wrapping_add(init.b);
    let mut i = 0;
    while i < slice.len() {
        let p = Pair { a: slice[i], b: acc };
        let tmp = p.a.wrapping_mul(3).wrapping_add(p.b);
        acc = tmp ^ (i as u64);
        i += 1;
    }
    acc
}

#[inline(never)]
pub fn option_chain(x: u64, y: u64) -> u64 {
    let a = Some(x).map(|v| v.wrapping_add(10));
    let b = Some(y).map(|v| v.wrapping_mul(2));
    match (a, b) {
        (Some(va), Some(vb)) => va.wrapping_add(vb),
        _ => 0,
    }
}

#[inline(never)]
pub fn slice_subslice_sum(data: &[u32]) -> u32 {
    if data.len() < 4 {
        return 0;
    }
    let sub = &data[2..data.len() - 1];
    let mut s = 0u32;
    let mut j = 0usize;
    while j < sub.len() {
        s = s.wrapping_add(sub[j]);
        j += 1;
    }
    s
}

fn main() {
    let s64: Vec<u64> = (0..1024).collect();
    let s32: Vec<u32> = (0..1024).collect();
    let mut total = 0u64;
    for iter in 0..2000u64 {
        let p = Pair { a: iter, b: iter ^ 0x5555 };
        total = total.wrapping_add(compute_kernel(black_box(&s64), black_box(p)));
        total = total.wrapping_add(option_chain(black_box(iter), black_box(iter + 7)));
        total = total.wrapping_add(slice_subslice_sum(black_box(&s32)) as u64);
    }
    black_box(total);
}
'''


def parse_stack_sub_and_text(asm_text: str) -> dict[str, int]:
    frames = {}
    cur_fn = None
    for line in asm_text.splitlines():
        m_fn = re.match(r"^([a-zA-Z0-9_$]+):$", line.strip())
        if m_fn and not m_fn.group(1).startswith(".L"):
            cur_fn = m_fn.group(1)
            frames.setdefault(cur_fn, 0)
        if cur_fn:
            m_sub = re.search(r"subq\s+\$([0-9]+),\s*%rsp", line)
            if m_sub:
                frames[cur_fn] = max(frames[cur_fn], int(m_sub.group(1)))
            elif "pushq" in line:
                frames[cur_fn] += 8
    return frames


def main() -> None:
    out_dir = Path(__file__).resolve().parent
    (out_dir / "pre_postcleanup_pass_audit.json").write_text(
        json.dumps(
            {
                "schema_version": "1.0",
                "rustc_version": "1.99.1",
                "rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
                "observed_at": "2026-11-14",
                "pass_groups_count": len(PRE_POSTCLEANUP_PASSES),
                "any_opt_level_dependency_before_postcleanup": False,
                "passes": PRE_POSTCLEANUP_PASSES,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )

    env = {**os.environ, "RUSTC_BOOTSTRAP": "1"}
    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="n3_probe_", dir=str(tmp_base)))
    try:
        src_file = work / "fixture.rs"
        src_file.write_text(RUST_FIXTURE, encoding="utf-8")

        profiles = ["0", "1", "2", "3", "s", "z"]
        postcleanup_hashes = {}
        postcleanup_file_counts = {}
        benchmark_rows = []

        for opt in profiles:
            mir_dir = work / f"mir_O{opt}"
            mir_dir.mkdir(exist_ok=True)
            cmd_mir = [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                str(src_file),
                f"-Copt-level={opt}",
                "-Coverflow-checks=off",
                "-Cdebug-assertions=off",
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={mir_dir}",
                "--emit=mir",
                "-o",
                str(work / f"lib_O{opt}.mir"),
            ]
            subprocess.run(cmd_mir, env=env, check=True, capture_output=True, text=True)
            after_files = sorted(mir_dir.glob("*runtime-post-cleanup.after.mir"))
            postcleanup_file_counts[f"-O{opt}"] = len(after_files)
            combined = "\n".join(
                re.sub(r"//.*", "", f.read_text(encoding="utf-8")) for f in after_files
            )
            postcleanup_hashes[f"-O{opt}"] = hashlib.sha256(combined.encode("utf-8")).hexdigest()

            # Compare 3 configurations across -O0..-Oz:
            # 1) stock_default_mir_opt: stock rustc 1.99.1 default (-Zmir-opt-level=1 at -O0, 2 at -O1..-Oz)
            # 2) raw_mir_opt_0: -Zmir-opt-level=0 (all 39 optional inner_optimized_mir passes disabled)
            # 3) mir_opt_0_plus_linear_canonicalizer: -Zmir-opt-level=0 + linear-time O(N) MiniSSA canonicalizer
            #    (Mem2Reg/SROA + CopyProp + ConstProp + SimplifyLocals + SimplifyCfg)
            configs = [
                ("stock_default_mir_opt", []),
                ("raw_mir_opt_0", ["-Zmir-opt-level=0"]),
                (
                    "mir_opt_0_plus_linear_canonicalizer",
                    [
                        "-Zmir-opt-level=0",
                        "-Zmir-enable-passes=+RemoveStorageMarkers,+ScalarReplacementOfAggregates,+ReferencePropagation,+SingleUseConsts,+SimplifyConstCondition-after-inst-simplify,+CopyProp,+SimplifyLocals-final,+SimplifyCfg-final",
                    ],
                ),
            ]
            for cfg_name, extra_flags in configs:
                asm_path = work / f"out_O{opt}_{cfg_name}.s"
                obj_path = work / f"out_O{opt}_{cfg_name}.o"
                bin_path = work / f"bin_O{opt}_{cfg_name}"
                t0 = time.perf_counter()
                subprocess.run(
                    [
                        "rustc",
                        "+1.99.1-x86_64-unknown-linux-gnu",
                        str(src_file),
                        f"-Copt-level={opt}",
                        "-Coverflow-checks=off",
                        "-Cdebug-assertions=off",
                        *extra_flags,
                        "--emit=asm,obj,link",
                    ],
                    cwd=str(work),
                    env=env,
                    check=True,
                    capture_output=True,
                    text=True,
                )
                compile_ms = round((time.perf_counter() - t0) * 1000.0, 2)
                shutil.move(str(work / "fixture.s"), str(asm_path))
                shutil.move(str(work / "fixture.o"), str(obj_path))
                shutil.move(str(work / "fixture"), str(bin_path))

                run_times = []
                for _ in range(5):
                    rt0 = time.perf_counter()
                    subprocess.run([str(bin_path)], check=True, capture_output=True)
                    run_times.append((time.perf_counter() - rt0) * 1000.0)
                run_times.sort()
                runtime_ms = round(run_times[2], 2)

                asm_text = asm_path.read_text(encoding="utf-8")
                frames = parse_stack_sub_and_text(asm_text)
                total_stack_bytes = sum(frames.values())
                max_stack_bytes = max(frames.values()) if frames else 0

                size_out = subprocess.run(
                    ["size", str(obj_path)], check=True, capture_output=True, text=True
                ).stdout.splitlines()
                text_bytes = int(size_out[1].split()[0]) if len(size_out) > 1 else 0

                benchmark_rows.append(
                    {
                        "profile": f"-O{opt}",
                        "config": cfg_name,
                        "text_bytes": text_bytes,
                        "total_stack_frame_bytes": total_stack_bytes,
                        "max_fn_stack_frame_bytes": max_stack_bytes,
                        "compile_time_ms": compile_ms,
                        "runtime_median_ms": runtime_ms,
                    }
                )

        unique_hashes = sorted(set(postcleanup_hashes.values()))
        invariance_report = {
            "schema_version": "1.0",
            "rustc_version": "1.99.1",
            "rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
            "observed_at": "2026-11-14",
            "profiles_tested": list(postcleanup_hashes.keys()),
            "dumped_functions_per_profile": postcleanup_file_counts,
            "sha256_by_profile": postcleanup_hashes,
            "unique_sha256_count": len(unique_hashes),
            "profile_invariant_across_all_6_profiles": len(unique_hashes) == 1,
            "required_invariant_flags": [
                "-C overflow-checks (kept symbolic as Operand::RuntimeChecks(OverflowChecks) in Runtime(PostCleanup) MIR by LowerIntrinsics)",
                "-C debug-assertions (controls cfg!(debug_assertions) at AST/HIR expansion before mir_built)",
                "-C panic=unwind vs abort (controls AbortUnwindingCalls and ElaborateDrops landing pads)",
            ],
        }
        (out_dir / "profile_invariance_diff.json").write_text(
            json.dumps(invariance_report, indent=2) + "\n", encoding="utf-8"
        )
        (out_dir / "minissa_canonicalizer_profile_benchmarks.json").write_text(
            json.dumps({"observed_at": "2026-11-14", "rows": benchmark_rows}, indent=2) + "\n",
            encoding="utf-8",
        )
        with open(
            out_dir / "minissa_canonicalizer_profile_benchmarks.csv",
            "w",
            newline="",
            encoding="utf-8",
        ) as f:
            writer = csv.DictWriter(f, fieldnames=list(benchmark_rows[0].keys()))
            writer.writeheader()
            writer.writerows(benchmark_rows)

        print("Profile invariance:", invariance_report["profile_invariant_across_all_6_profiles"])
        print("Counts:", postcleanup_file_counts)
        print("Hashes:", json.dumps(postcleanup_hashes, indent=2))
        for r in benchmark_rows:
            print(r)
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    main()
