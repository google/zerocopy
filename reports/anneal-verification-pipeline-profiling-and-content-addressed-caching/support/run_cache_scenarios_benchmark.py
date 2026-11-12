#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""End-to-end benchmark runner for the 6 developer/CI verification caching scenarios on starnix."""

import copy
import json
import pathlib
import shutil
import time

from cached_verify_prototype import (
    BASELINE_ARTIFACTS,
    CAPTURE,
    LEAN,
    MVP_SRC,
    STARNIX_FIXTURE,
    SUPPORT_DIR,
    SYSROOT,
    VerificationCache,
    run_cached_verify,
    sha256_file,
    sha256_json,
)

TRACK6_DIR = pathlib.Path("/tmp/ref_research_stack221_perf/track6")
BASELINE_OLEANS_DIR = SUPPORT_DIR / "baseline_oleans"


def prepare_clean_workspace(dest: pathlib.Path):
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(STARNIX_FIXTURE, dest)


def seed_baseline_oleans_into_cache(workspace: pathlib.Path, cache: VerificationCache):
    """Pre-seed Level 3 .olean cache from the freshly compiled baseline_oleans directory
    so we don't redundantly re-compile unchanged Endianness/ProductionSteps before warm tests,
    while recording exact cold compile times from pipeline_profile.json.
    """
    adm = cache.admit_toolchain_and_locks(fast_stat=True)
    profile = json.loads((SUPPORT_DIR / "pipeline_profile.json").read_text())
    compile_flags = ["-j1", "-M2048", "-t0", "-DElab.async=false", "-Ddebug.skipKernelTC=false"]

    imports_map = {}
    for m_entry in profile["per_module_compile"]:
        mod_name = m_entry["module"]
        imps = [
            {"module": imp, "importAll": False, "isExported": True, "isMeta": False}
            for imp in m_entry["imports"]
        ]
        imports_map[mod_name] = imps

    audit_req = json.loads((BASELINE_ARTIFACTS / "audit-request.json").read_text())
    src_sha_by_mod = {m["module"]: m["expectedSha256"] for m in audit_req["modules"]}

    # Seed header cache
    for mod_name, imps in imports_map.items():
        k_hdr = sha256_json({
            "level": "header:v1",
            "lean_sha256": adm["lean_sha256"],
            "trusted_boundary_sha256": adm["trusted_boundary_sha256"],
            "foundation_lock_sha256": adm["foundation_lock_sha256"],
            "module": mod_name,
            "source_sha256": src_sha_by_mod[mod_name],
        })
        (cache.header_dir / f"{k_hdr}.json").write_text(json.dumps(imps))

    # Seed olean cache in topological order
    dep_part_digests = dict(adm["foundation_part_shas"])
    dep_part_digests.update(adm["library_part_shas"])
    graph = dict(adm["foundation_graph"])
    graph.update(adm["library_graph"])

    def get_transitive_dep_digests(mod_name: str) -> dict:
        visited = set()
        stack = [e["module"] for e in imports_map[mod_name]]
        result = {}
        while stack:
            d = stack.pop()
            if d in visited:
                continue
            visited.add(d)
            result[d] = dep_part_digests[d]
            for edge in graph.get(d, []):
                stack.append(edge["module"])
        return {k: result[k] for k in sorted(result.keys())}

    for m_entry in profile["per_module_compile"]:
        mod_name = m_entry["module"]
        rel = mod_name.replace(".", "/")
        olean_src = BASELINE_OLEANS_DIR / f"{rel}.olean"
        o_sha = sha256_file(olean_src)
        assert o_sha == m_entry["olean_sha256"]
        trans_deps = get_transitive_dep_digests(mod_name)
        k_module = sha256_json({
            "level": "olean:v1",
            "lean_sha256": adm["lean_sha256"],
            "compile_flags": compile_flags,
            "module": mod_name,
            "is_module": False,
            "source_sha256": src_sha_by_mod[mod_name],
            "imports": imports_map[mod_name],
            "transitive_dep_artifacts": trans_deps,
        })
        shutil.copy2(olean_src, cache.olean_dir / f"{k_module}.olean")
        (cache.olean_dir / f"{k_module}.json").write_text(
            json.dumps({"module": mod_name, "olean_sha256": o_sha, "k_module": k_module})
        )
        dep_part_digests[mod_name] = {"olean": o_sha}
        graph[mod_name] = imports_map[mod_name]


def create_sharded_workspace(dest: pathlib.Path) -> list[str]:
    """Create a starnix workspace where ProductionSteps.lean is sharded into K=8 per-path modules."""
    prepare_clean_workspace(dest)
    import sys
    sys.path.insert(0, str(dest / "proof"))
    import generate_steps

    captured = json.loads((BASELINE_ARTIFACTS / "capture/capture.json").read_text())
    body = captured["program"]["bodies"][0]

    proof_dir = dest / "proof"
    steps_dir = proof_dir / "ProductionSteps"
    steps_dir.mkdir(parents=True, exist_ok=True)
    # Remove monolithic ProductionSteps.lean
    (proof_dir / "ProductionSteps.lean").unlink()

    shard_modules = []
    for flag in (0, 1):
        for width in range(4):
            part_src, _ = generate_steps.produce(body, flag, width)
            label = ("Be" if flag else "Le") + str(8 << width)
            mod_name = f"ProductionSteps.{label}"
            shard_modules.append(mod_name)
            shard_path = steps_dir / f"{label}.lean"
            shard_content = (
                generate_steps.HEADER
                + "prelude\nimport InitialCache\n\n"
                + f"namespace {mod_name}\n\n"
                + "open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction\n\n"
                + part_src
                + f"end {mod_name}\n"
            )
            shard_path.write_text(shard_content)

    # Update ProductionClaims.lean to import all 8 shards
    claims_path = proof_dir / "ProductionClaims.lean"
    claims_text = claims_path.read_text()
    imports_block = "\n".join(f"import {m}" for m in shard_modules)
    opens_block = " ".join(shard_modules)
    claims_text = claims_text.replace("import ProductionSteps", imports_block)
    claims_text = claims_text.replace(
        "open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction ProductionSteps",
        f"open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction {opens_block}",
    )
    claims_path.write_text(claims_text)

    # Update request.json to list the 8 shard modules instead of monolithic ProductionSteps
    req_path = dest / "request.json"
    req = json.loads(req_path.read_text())
    new_sources = [s for s in req["proof"]["sources"] if s["module"] != "ProductionSteps"]
    for m in shard_modules:
        rel_p = m.replace(".", "/") + ".lean"
        new_sources.append({"module": m, "path": rel_p, "role": "proof"})
    new_sources.sort(key=lambda x: x["module"])
    req["proof"]["sources"] = new_sources
    req_path.write_text(json.dumps(req, indent=2))
    return shard_modules


def main():
    cache_dir = TRACK6_DIR / "cache_store"
    if cache_dir.exists():
        shutil.rmtree(cache_dir)
    cache = VerificationCache(cache_dir)
    cache.ensure_native_inspector()

    ws = TRACK6_DIR / "work_starnix"
    prepare_clean_workspace(ws)

    # Seed the 17 baseline .oleans into cache (already measured cold in pipeline_profile.json)
    seed_baseline_oleans_into_cache(ws, cache)
    profile = json.loads((SUPPORT_DIR / "pipeline_profile.json").read_text())
    baseline_res = json.loads((BASELINE_ARTIFACTS / "result.json").read_text())

    results = {}

    # Scenario 1: Cold Cache (Full Baseline Run)
    # Combine measured cold timings from pipeline_profile.json and baseline result.json
    cold_capture_ms = baseline_res["timing_ms"]["capture"]
    cold_admission_ms = profile["tool_admission"]["total_tool_admission_ms"] + profile["admit_libraries"]["admit_libraries_ms"]
    cold_headers_ms = profile["headers_inspect_ms"]
    cold_compile_ms = profile["total_module_compile_ms"]
    cold_audit_ms = profile["target_audit_ms"]
    cold_total_ms = cold_capture_ms + cold_admission_ms + cold_headers_ms + cold_compile_ms + cold_audit_ms
    results["scenario1_cold_baseline"] = {
        "description": "Cold cache (full baseline run, 0% cache hit)",
        "cargo_anneal_baseline_result_json_ms": baseline_res["timing_ms"],
        "instrumented_stage_breakdown_ms": {
            "capture_ms": round(cold_capture_ms, 2),
            "admission_ms": round(cold_admission_ms, 2),
            "headers_ms": round(cold_headers_ms, 2),
            "lean_compile_ms": round(cold_compile_ms, 2),
            "target_audit_ms": round(cold_audit_ms, 2),
            "total_ms": round(cold_total_ms, 2),
        },
        "compiled_modules_count": 17,
    }
    print("Scenario 1 (Cold baseline):", json.dumps(results["scenario1_cold_baseline"], indent=2))

    # Populate Level 1 capture cache and Level 4 audit cache with one warm-up run
    print("\nPopulating Level 1 (Capture) and Level 4 (TargetAudit) cache entries...")
    warmup_4a_native = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-native")
    warmup_4a_interp = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-interp")

    # Scenario 2: Warm Cache — No-op Re-verify (100% cache hit across all levels)
    s2_4b = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B")
    s2_4b_strict_adm = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B", fast_admission=False)
    results["scenario2_warm_noop"] = {
        "description": "Warm cache — No-op re-verify (100% cache hit)",
        "mode_4B_receipt_cache": s2_4b,
        "mode_4B_full_sha256_admission": s2_4b_strict_adm,
        "mode_4A_native_audit_replay": warmup_4a_native,
        "mode_4A_interp_audit_replay": warmup_4a_interp,
    }
    print("Scenario 2 (Warm no-op):", json.dumps(results["scenario2_warm_noop"], indent=2))

    # Scenario 3: Warm Cache — Comment / Unrelated Rust Function Edit in verifier.rs
    prepare_clean_workspace(ws)
    verifier_rs = ws / "source/verifier.rs"
    v_orig = verifier_rs.read_text()
    v_mod = v_orig.replace(
        "fn popcount_u64(mut x: u64) -> usize {",
        "// Edited comment in verifier.rs\nfn popcount_u64(mut x: u64) -> usize {\n    let _unrelated_local = x.wrapping_add(123);",
        1,
    )
    assert v_mod != v_orig
    verifier_rs.write_text(v_mod)

    # First run with Mode 4B (K_capture misses -> capture runs -> Captured.lean identical -> early cutoff -> Level 3 & Level 4 hit!)
    s3_4b = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B")
    # Also measure Mode 4A-native on the same edit (clearing just the new K_capture entry so capture runs again)
    for d in cache.capture_dir.iterdir():
        if d.is_dir():
            # Keep only the original clean capture entry if we want, or clear capture_dir and re-seed clean
            pass
    # Restore clean capture only, re-apply edit, and measure 4A-native
    shutil.rmtree(cache.capture_dir)
    cache.capture_dir.mkdir(parents=True, exist_ok=True)
    verifier_rs.write_text(v_orig)
    _ = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B")
    verifier_rs.write_text(v_mod)
    s3_4a_native = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-native")

    results["scenario3_unrelated_rust_edit"] = {
        "description": "Warm cache — Comment & unrelated function body edit in verifier.rs (early cutoff via Captured.lean SHA-256)",
        "mode_4B_receipt_cache": s3_4b,
        "mode_4A_native_audit_replay": s3_4a_native,
    }
    print("Scenario 3 (Unrelated Rust edit):", json.dumps(results["scenario3_unrelated_rust_edit"], indent=2))

    # Restore clean workspace and capture cache
    prepare_clean_workspace(ws)
    _ = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B")

    # Scenario 4: Warm Cache — Proof.lean-Only Edit
    proof_lean = ws / "proof/Proof.lean"
    p_orig = proof_lean.read_text()
    p_mod = p_orig.replace(
        "have same : sourceBody = body := Option.some.inj found",
        "have same : sourceBody = body := by exact Option.some.inj found",
        1,
    )
    assert p_mod != p_orig
    proof_lean.write_text(p_mod)
    s4_4a_native = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-native")
    # Also measure second run after Proof.lean edit is cached (4B hit)
    s4_4b_second_run = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4B")
    results["scenario4_proof_lean_only_edit"] = {
        "description": "Warm cache — Proof.lean-only edit (16/17 modules hit .olean cache; only Proof.lean recompiles + TargetAudit runs)",
        "first_run_after_edit_mode_4A_native": s4_4a_native,
        "second_run_cached_mode_4B": s4_4b_second_run,
    }
    print("Scenario 4 (Proof.lean edit):", json.dumps(results["scenario4_proof_lean_only_edit"], indent=2))

    # Restore clean workspace
    prepare_clean_workspace(ws)

    # Scenario 5: Warm Cache — Single Basic-Block Proof Edit (ProductionSteps sharded into K=8 modules)
    ws_sharded = TRACK6_DIR / "work_starnix_sharded"
    shard_mods = create_sharded_workspace(ws_sharded)
    print(f"\nWarming K=8 sharded workspace ({len(shard_mods)} shards)...")
    t_shard_warm0 = time.perf_counter()
    sharded_warmup = run_cached_verify(ws_sharded, cache, enable_cache=True, audit_mode="4A-native")
    print(f"Sharded warm-up compiled {sharded_warmup['cache_stats']['compiled_modules_count']} modules in {sharded_warmup['timing_ms']['lean_compile_ms']:.2f} ms")

    # Edit 1 shard: ProductionSteps.Le8 (small shard)
    le8_path = ws_sharded / "proof/ProductionSteps/Le8.lean"
    le8_orig = le8_path.read_text()
    le8_mod = le8_orig.replace("= by rfl", "= rfl", 1)
    assert le8_mod != le8_orig
    le8_path.write_text(le8_mod)
    s5_le8_4a_native = run_cached_verify(ws_sharded, cache, enable_cache=True, audit_mode="4A-native")
    le8_path.write_text(le8_orig)

    # Edit 1 shard: ProductionSteps.Be64 (largest 64-bit byte-swap shard, 90+ statements)
    be64_path = ws_sharded / "proof/ProductionSteps/Be64.lean"
    be64_orig = be64_path.read_text()
    be64_mod = be64_orig.replace("= by rfl", "= rfl", 1)
    assert be64_mod != be64_orig
    be64_path.write_text(be64_mod)
    s5_be64_4a_native = run_cached_verify(ws_sharded, cache, enable_cache=True, audit_mode="4A-native")
    be64_path.write_text(be64_orig)

    results["scenario5_single_shard_proof_edit"] = {
        "description": "Warm cache — Single basic-block path proof edit with ProductionSteps sharded into K=8 modules (7/8 shards + Endianness + Model + Capture hit .olean cache; only 1 shard + ProductionClaims + Proof recompile)",
        "sharded_initial_population": sharded_warmup,
        "edit_small_shard_Le8_mode_4A_native": s5_le8_4a_native,
        "edit_largest_shard_Be64_mode_4A_native": s5_be64_4a_native,
    }
    print("Scenario 5 (Single basic-block shard edit):", json.dumps(results["scenario5_single_shard_proof_edit"], indent=2))

    # Scenario 6: Warm Cache — Spec.lean Edit
    prepare_clean_workspace(ws)
    spec_lean = ws / "proof/Spec.lean"
    s_orig = spec_lean.read_text()
    s_mod = s_orig + "\n-- Additional doc comment in Spec.lean\n"
    spec_lean.write_text(s_mod)
    s6a_4a_native = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-native")

    s_semantic = s_orig.replace(
        "def specs : Specs :=",
        "def safetyTag : Prop := True\n\ndef specs : Specs :=",
        1,
    )
    spec_lean.write_text(s_semantic)
    s6b_4a_native = run_cached_verify(ws, cache, enable_cache=True, audit_mode="4A-native")
    spec_lean.write_text(s_orig)

    results["scenario6_spec_lean_edit"] = {
        "description": "Warm cache — Spec.lean edit (Model, Captured, Endianness, Inputs, SourceInputs, InitialCache, ProductionSteps, ProductionClaims all hit .olean cache; only Spec, Expected, Proof recompile + TargetAudit runs)",
        "comment_edit_olean_early_cutoff_mode_4A_native": s6a_4a_native,
        "semantic_edit_spec_expected_proof_recompile_mode_4A_native": s6b_4a_native,
    }
    print("Scenario 6 (Spec.lean edit):", json.dumps(results["scenario6_spec_lean_edit"], indent=2))

    out_path = SUPPORT_DIR / "scenarios_benchmark_results.json"
    out_path.write_text(json.dumps(results, indent=2))
    print("\nSaved complete benchmark results to", out_path)


if __name__ == "__main__":
    main()
