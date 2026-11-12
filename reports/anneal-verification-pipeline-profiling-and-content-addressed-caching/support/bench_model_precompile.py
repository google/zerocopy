#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Experiment 2A: Pre-compiling Trusted.Mvp.* and Anneal.Mvp.* into pre-built .olean / library-lock."""

import copy
import json
import shutil
from pathlib import Path

from lean_pipeline_harness import (
    BUNDLED_MODULES,
    PARTS,
    REACHABLE_BUNDLED,
    TRACK2_DIR,
    admit_reachable_libraries,
    collect_module_artifacts,
    ensure_baseline_artifacts,
    inspect_headers,
    load_admitted_base,
    resolve_local_source_path,
    run_target_audit,
    sha256_file,
    topo_sort_modules,
    write_setup_and_compile,
)


def measure_and_cache_bundled(sample_work: Path) -> tuple[list[dict], dict]:
    cache_dir = TRACK2_DIR / "prebuilt_model_cache"
    if cache_dir.exists():
        shutil.rmtree(cache_dir)
    cache_dir.mkdir(parents=True, exist_ok=True)
    lib_dir = cache_dir / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)

    base_state = load_admitted_base()
    sources = [(m, sample_work / rel) for m, rel, _ in BUNDLED_MODULES]
    t_hdr, imports_map = inspect_headers(cache_dir, base_state, sources)
    all_imp_names = [e["module"] for edges in imports_map.values() for e in edges]
    admit_reachable_libraries(base_state, all_imp_names)

    results = []
    prebuilt_meta = {
        "headers_wall_s": t_hdr["wall_s"],
        "modules": {},
    }

    for mod_name, rel_src, role in BUNDLED_MODULES:
        src_path = sample_work / rel_src
        src_bytes = src_path.stat().st_size
        src_lines = len(src_path.read_text().splitlines())
        src_sha = sha256_file(src_path)
        edges = imports_map[mod_name]

        trials = []
        mod_arts = None
        for _ in range(3):
            t_comp, mod_arts = write_setup_and_compile(
                cache_dir,
                lib_dir,
                base_state,
                mod_name,
                src_path,
                edges,
                allow_async=False,
                threads=1,
            )
            trials.append(t_comp)

        base_state["artifacts"][mod_name] = mod_arts
        base_state["graph"][mod_name] = edges

        rel_mod = mod_name.replace(".", "/")
        part_stats = {}
        for part in PARTS:
            p = lib_dir / f"{rel_mod}.{part}"
            if p.is_file():
                part_stats[part] = {
                    "bytes": p.stat().st_size,
                    "sha256": sha256_file(p),
                }

        wall_runs = [r["wall_s"] for r in trials]
        cpu_runs = [r["cpu_s"] for r in trials]
        entry = {
            "module": mod_name,
            "path": rel_src,
            "role": role,
            "reachable_from_targets": mod_name in REACHABLE_BUNDLED,
            "src_bytes": src_bytes,
            "src_lines": src_lines,
            "src_sha256": src_sha,
            "imports": edges,
            "wall_s_runs": wall_runs,
            "wall_s_mean": sum(wall_runs) / len(wall_runs),
            "wall_s_min": min(wall_runs),
            "cpu_s_mean": sum(cpu_runs) / len(cpu_runs),
            "parts": part_stats,
        }
        results.append(entry)
        prebuilt_meta["modules"][mod_name] = {
            "role": role,
            "src_sha256": src_sha,
            "imports": edges,
            "artifacts": mod_arts,
            "parts": part_stats,
        }

    return results, prebuilt_meta


def run_fixture_variant(
    fixture_name: str,
    work_dir: Path,
    prebuilt_meta: dict,
    variant: str,
) -> dict:
    stage_dir = TRACK2_DIR / "runs_exp2a" / f"{fixture_name}_{variant}"
    if stage_dir.exists():
        shutil.rmtree(stage_dir)
    stage_dir.mkdir(parents=True, exist_ok=True)
    lib_dir = stage_dir / "target-lib"
    lib_dir.mkdir(parents=True, exist_ok=True)

    orig_req = json.loads((work_dir / "audit-request.json").read_text())
    bundled_names = {m[0] for m in BUNDLED_MODULES}

    # Resolve all modules in orig_req
    all_mod_entries = []
    for m in orig_req["modules"]:
        local_src = resolve_local_source_path(work_dir, m)
        all_mod_entries.append({
            "module": m["module"],
            "source": str(local_src),
            "expectedSha256": m["expectedSha256"],
            "role": m["role"],
        })

    state = load_admitted_base()

    if variant == "2A-0_baseline":
        active_entries = all_mod_entries
        compile_entries = active_entries
    elif variant == "2A-1_pruned":
        active_entries = [
            m
            for m in all_mod_entries
            if (m["module"] not in bundled_names) or (m["module"] in REACHABLE_BUNDLED)
        ]
        compile_entries = active_entries
    elif variant == "2A-2_prebuilt_olean":
        active_entries = [
            m
            for m in all_mod_entries
            if (m["module"] not in bundled_names) or (m["module"] in REACHABLE_BUNDLED)
        ]
        # Only compile non-bundled target modules; register reachable bundled from prebuilt_meta
        compile_entries = [m for m in active_entries if m["module"] not in bundled_names]
        for b_mod in ["Trusted.Mvp.Syntax", "Trusted.Mvp.Semantics", "Trusted.Mvp", "Anneal.Mvp.Execution"]:
            b_info = prebuilt_meta["modules"][b_mod]
            admit_reachable_libraries(state, [e["module"] for e in b_info["imports"]])
            state["artifacts"][b_mod] = b_info["artifacts"]
            state["graph"][b_mod] = b_info["imports"]
    elif variant == "2A-3_library_lock":
        # Admit Anneal.Mvp.Execution into library_modules (library-lock.json)
        # while keeping Trusted.Mvp.{Syntax,Semantics,Mvp} as pre-built TargetRole::Model
        # so TrustedBoundary.lean's (canonicalRoot, TargetRole.model) and modelClosure
        # checks remain 100% intact.
        active_entries = [
            m
            for m in all_mod_entries
            if (m["module"] not in bundled_names)
            or (m["module"] in {"Trusted.Mvp.Syntax", "Trusted.Mvp.Semantics", "Trusted.Mvp"})
        ]
        compile_entries = [m for m in active_entries if m["module"] not in bundled_names]
        for lib_mod in ["Anneal.Mvp.Execution"]:
            b_info = prebuilt_meta["modules"][lib_mod]
            admit_reachable_libraries(state, [e["module"] for e in b_info["imports"]])
            state["artifacts"][lib_mod] = b_info["artifacts"]
            state["graph"][lib_mod] = b_info["imports"]
            state["library_modules"].add(lib_mod)
        for mod_m in ["Trusted.Mvp.Syntax", "Trusted.Mvp.Semantics", "Trusted.Mvp"]:
            m_info = prebuilt_meta["modules"][mod_m]
            admit_reachable_libraries(state, [e["module"] for e in m_info["imports"]])
            state["artifacts"][mod_m] = m_info["artifacts"]
            state["graph"][mod_m] = m_info["imports"]
    else:
        raise ValueError(variant)

    # Step 1: Inspect headers for compile_entries
    hdr_sources = [(m["module"], Path(m["source"])) for m in compile_entries]
    t_hdr, imports_map = inspect_headers(stage_dir, state, hdr_sources)
    all_imp_names = [e["module"] for edges in imports_map.values() for e in edges]
    admit_reachable_libraries(state, all_imp_names)

    # Step 2: Topological sort and compile
    pending_names = {m["module"] for m in compile_entries}
    entry_by_name = {m["module"]: m for m in compile_entries}
    waves = topo_sort_modules(pending_names, imports_map)
    order = [m for w in waves for m in w]

    mod_timings = []
    compile_wall_s = 0.0
    compile_cpu_s = 0.0
    for mod_name in order:
        m_entry = entry_by_name[mod_name]
        edges = imports_map[mod_name]
        t_comp, mod_arts = write_setup_and_compile(
            stage_dir,
            lib_dir,
            state,
            mod_name,
            Path(m_entry["source"]),
            edges,
            allow_async=False,
            threads=1,
        )
        state["artifacts"][mod_name] = mod_arts
        state["graph"][mod_name] = edges
        mod_timings.append({
            "module": mod_name,
            "role": m_entry["role"],
            "wall_s": t_comp["wall_s"],
            "cpu_s": t_comp["cpu_s"],
        })
        compile_wall_s += t_comp["wall_s"]
        compile_cpu_s += t_comp["cpu_s"]

    # Step 3: Run TargetAudit
    target_req = copy.deepcopy(orig_req)
    target_req["modules"] = active_entries
    t_audit, audit_res = run_target_audit(stage_dir, state, target_req)

    total_wall_s = t_hdr["wall_s"] + compile_wall_s + t_audit["wall_s"]
    total_cpu_s = t_hdr["cpu_s"] + compile_cpu_s + t_audit["cpu_s"]

    return {
        "fixture": fixture_name,
        "variant": variant,
        "headers_wall_s": t_hdr["wall_s"],
        "headers_cpu_s": t_hdr["cpu_s"],
        "compile_wall_s": compile_wall_s,
        "compile_cpu_s": compile_cpu_s,
        "audit_wall_s": t_audit["wall_s"],
        "audit_cpu_s": t_audit["cpu_s"],
        "total_lean_wall_s": total_wall_s,
        "total_lean_cpu_s": total_cpu_s,
        "compiled_module_count": len(order),
        "waves": waves,
        "module_timings": mod_timings,
        "audit_summary": {
            "replayedDeclarations": audit_res["replayedDeclarations"],
            "modelClosure_count": len(audit_res["modelClosure"]),
            "specificationClosure_count": len(audit_res["specificationClosure"]),
            "axioms": audit_res["axioms"],
            "replay": audit_res["replay"],
            "exactType": audit_res["exactType"],
        },
        "audit_full": audit_res,
    }


def main() -> None:
    print("Ensuring baseline artifacts for scalar, spin, starnix...")
    baselines = {}
    for fx in ["scalar", "spin", "starnix"]:
        baselines[fx] = ensure_baseline_artifacts(fx)
        print(f"  {fx}: {baselines[fx]}")

    print("\nMeasuring bundled Model & Theory modules (3 trials each)...")
    bundled_stats, prebuilt_meta = measure_and_cache_bundled(baselines["scalar"])
    total_bundled_wall = 0.0
    reachable_bundled_wall = 0.0
    for b in bundled_stats:
        total_bundled_wall += b["wall_s_mean"]
        if b["reachable_from_targets"]:
            reachable_bundled_wall += b["wall_s_mean"]
        olean_kb = b["parts"].get("olean", {}).get("bytes", 0) / 1024.0
        server_kb = b["parts"].get("olean.server", {}).get("bytes", 0) / 1024.0
        priv_kb = b["parts"].get("olean.private", {}).get("bytes", 0) / 1024.0
        ir_kb = b["parts"].get("ir", {}).get("bytes", 0) / 1024.0
        print(
            f"  {b['module']:24s} ({b['role']:5s}, reach={str(b['reachable_from_targets']):5s}): "
            f"{b['src_lines']:4d}L ({b['src_bytes']:6d}B) | "
            f"wall={b['wall_s_mean']*1000:7.1f} ms | "
            f".olean={olean_kb:6.1f} KiB, .server={server_kb:5.1f} KiB, .priv={priv_kb:6.1f} KiB, .ir={ir_kb:6.1f} KiB"
        )
    print(
        f"  Total bundled wall: {total_bundled_wall*1000:.1f} ms "
        f"(reachable 4: {reachable_bundled_wall*1000:.1f} ms, "
        f"unreachable 3: {(total_bundled_wall - reachable_bundled_wall)*1000:.1f} ms)"
    )

    variants = [
        "2A-0_baseline",
        "2A-1_pruned",
        "2A-2_prebuilt_olean",
    ]
    all_runs = []
    for fx in ["scalar", "spin", "starnix"]:
        print(f"\n=== Benchmarking fixture: {fx} ===")
        fx_runs = {}
        base_audit = None
        for var in variants:
            # Run 2 trials for scalar/spin and 1 trial for starnix
            n_trials = 1 if fx == "starnix" else 2
            trials = [run_fixture_variant(fx, baselines[fx], prebuilt_meta, var) for _ in range(n_trials)]
            r0 = trials[0]
            r0["headers_wall_s"] = sum(t["headers_wall_s"] for t in trials) / n_trials
            r0["compile_wall_s"] = sum(t["compile_wall_s"] for t in trials) / n_trials
            r0["audit_wall_s"] = sum(t["audit_wall_s"] for t in trials) / n_trials
            r0["total_lean_wall_s"] = sum(t["total_lean_wall_s"] for t in trials) / n_trials
            r0["total_lean_cpu_s"] = sum(t["total_lean_cpu_s"] for t in trials) / n_trials
            for idx_m in range(len(r0["module_timings"])):
                r0["module_timings"][idx_m]["wall_s"] = (
                    sum(t["module_timings"][idx_m]["wall_s"] for t in trials) / n_trials
                )
                r0["module_timings"][idx_m]["cpu_s"] = (
                    sum(t["module_timings"][idx_m]["cpu_s"] for t in trials) / n_trials
                )

            fx_runs[var] = r0
            if var == "2A-0_baseline":
                base_audit = r0["audit_full"]
            base_wall = fx_runs["2A-0_baseline"]["total_lean_wall_s"]
            base_comp = fx_runs["2A-0_baseline"]["compile_wall_s"]
            saved_ms = (base_wall - r0["total_lean_wall_s"]) * 1000.0
            comp_saved_ms = (base_comp - r0["compile_wall_s"]) * 1000.0
            pct_saved = (saved_ms / (base_wall * 1000.0)) * 100.0 if base_wall > 0 else 0.0
            comp_speedup = base_comp / r0["compile_wall_s"] if r0["compile_wall_s"] > 0 else 1.0
            total_speedup = base_wall / r0["total_lean_wall_s"] if r0["total_lean_wall_s"] > 0 else 1.0

            # Check closure match against 2A-0_baseline
            cur_audit = r0["audit_full"]
            closure_eq = (
                cur_audit["replayedDeclarations"] == base_audit["replayedDeclarations"]
                and cur_audit["modelClosure"] == base_audit["modelClosure"]
                and cur_audit["specificationClosure"] == base_audit["specificationClosure"]
                and cur_audit["axioms"] == base_audit["axioms"]
            )
            r0["exact_audit_closure_match_vs_baseline"] = closure_eq
            r0["compile_speedup_vs_baseline"] = comp_speedup
            r0["total_speedup_vs_baseline"] = total_speedup
            del r0["audit_full"]

            all_runs.append(r0)
            print(
                f"  {var:20s}: total={r0['total_lean_wall_s']*1000:7.1f} ms "
                f"(hdr={r0['headers_wall_s']*1000:6.1f} ms, "
                f"comp={r0['compile_wall_s']*1000:7.1f} ms [{r0['compiled_module_count']:2d} mods, {comp_speedup:4.2f}x], "
                f"audit={r0['audit_wall_s']*1000:6.1f} ms) | "
                f"saved={saved_ms:+7.1f} ms (comp {comp_saved_ms:+7.1f} ms, {pct_saved:+5.1f}%, {total_speedup:4.2f}x) | "
                f"replayed={r0['audit_summary']['replayedDeclarations']}, "
                f"modelClosure={r0['audit_summary']['modelClosure_count']}, "
                f"exact_match={closure_eq}"
            )

    out_path = TRACK2_DIR / "support" / "exp2a_results.json"
    out_path.write_text(
        json.dumps(
            {
                "bundled_modules": bundled_stats,
                "pipeline_runs": all_runs,
            },
            indent=2,
        )
    )
    print(f"\nSaved Experiment 2A results to {out_path}")


if __name__ == "__main__":
    main()
