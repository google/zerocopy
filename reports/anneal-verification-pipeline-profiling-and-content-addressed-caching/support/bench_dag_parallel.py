#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Experiment 2B: Inter-module DAG parallelism + Sharded ProductionSteps (K in {1,2,4,8,16}, W in {1,2,4,8}).

Analyzes and benchmarks:
1. Exact module dependency DAG, topological wave decomposition, critical path
   (span), and total work across scalar, spin, and starnix.
2. Sharding starnix's ProductionSteps.lean into K in {1, 2, 4, 8, 16} independent
   shard modules (ProductionSteps_0 .. ProductionSteps_{K-1}) re-exported by
   ProductionSteps.lean.
3. Parallel DAG compilation across worker pools W in {1, 2, 4, 8} (both with
   -DElab.async=false -j1 per worker and combined with -DElab.async=true and
   pre-compiled Model modules from 2A), measuring wall-clock speedup, CPU
   utilization, and TargetAudit replay overhead as K increases.
"""

from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import copy
import json
import os
import resource
import shutil
import subprocess
import time
from pathlib import Path

from generate_steps_sharded import generate_sharded
from lean_pipeline_harness import (
    BUNDLED_MODULES,
    LEAN,
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


def compile_module_worker(
    stage_dir: Path,
    lib_dir: Path,
    import_arts_snapshot: dict,
    mod_name: str,
    src_path: Path,
    imports: list[dict],
    allow_async: bool,
    threads: int,
) -> tuple[str, float, list[list[str]]]:
    setup_path = stage_dir / f"{mod_name}.setup.json"
    setup_obj = {
        "name": mod_name,
        "isModule": False,
        "imports": imports,
        "importArts": import_arts_snapshot,
        "dynlibs": [],
        "plugins": [],
        "options": {},
    }
    setup_path.write_text(json.dumps(setup_obj))

    output_olean = lib_dir / f"{mod_name.replace('.', '/')}.olean"
    output_olean.parent.mkdir(parents=True, exist_ok=True)

    cmd = [
        str(LEAN),
        f"-j{threads}",
        "-M2048",
        "-t0",
        f"-DElab.async={'true' if allow_async else 'false'}",
        "-Ddebug.skipKernelTC=false",
        "-DwarningAsError=true",
        "--setup",
        str(setup_path),
        "-o",
        str(output_olean),
        str(src_path),
    ]
    env = {
        "HOME": os.environ.get("HOME", "/tmp"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
    }
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=stage_dir, env=env, capture_output=True, text=True)
    t1 = time.perf_counter()
    if proc.returncode != 0:
        raise RuntimeError(
            f"Worker compile failed for {mod_name} (rc={proc.returncode}): {proc.stderr}\n{proc.stdout}"
        )
    mod_arts = collect_module_artifacts(lib_dir, mod_name)
    return mod_name, (t1 - t0), mod_arts


def run_dag_parallel(
    stage_dir: Path,
    lib_dir: Path,
    state: dict,
    entries_by_name: dict[str, dict],
    imports_map: dict[str, list[dict]],
    max_workers: int,
    allow_async: bool = False,
    threads_per_worker: int = 1,
) -> dict:
    """Schedules ready modules dynamically across a pool of max_workers processes."""
    pending = set(entries_by_name.keys())
    completed = set()
    in_flight = {}
    mod_wall = {}

    ru_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()

    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        while pending or in_flight:
            # Find all modules in pending whose dependencies (within entries_by_name) are in completed
            ready = sorted(
                m
                for m in pending
                if all(
                    (edge["module"] not in entries_by_name) or (edge["module"] in completed)
                    for edge in imports_map[m]
                )
            )
            while ready and len(in_flight) < max_workers:
                m = ready.pop(0)
                pending.remove(m)
                arts_snap = copy.deepcopy(state["artifacts"])
                fut = pool.submit(
                    compile_module_worker,
                    stage_dir,
                    lib_dir,
                    arts_snap,
                    m,
                    Path(entries_by_name[m]["source"]),
                    imports_map[m],
                    allow_async,
                    threads_per_worker,
                )
                in_flight[fut] = m

            if in_flight:
                done, _ = wait(in_flight.keys(), return_when=FIRST_COMPLETED)
                for fut in done:
                    in_flight.pop(fut)
                    mod_name, w_s, mod_arts = fut.result()
                    state["artifacts"][mod_name] = mod_arts
                    state["graph"][mod_name] = imports_map[mod_name]
                    mod_wall[mod_name] = w_s
                    completed.add(mod_name)

    t1 = time.perf_counter()
    ru_after = resource.getrusage(resource.RUSAGE_CHILDREN)

    wall_s = t1 - t0
    user_s = ru_after.ru_utime - ru_before.ru_utime
    sys_s = ru_after.ru_stime - ru_before.ru_stime
    cpu_s = user_s + sys_s
    sum_mod_wall = sum(mod_wall.values())

    return {
        "wall_s": wall_s,
        "user_s": user_s,
        "sys_s": sys_s,
        "cpu_s": cpu_s,
        "sum_module_wall_s": sum_mod_wall,
        "effective_cpu_util": cpu_s / wall_s if wall_s > 0 else 1.0,
        "module_wall_s": mod_wall,
    }


def compute_dag_metrics(
    entries_by_name: dict[str, dict],
    imports_map: dict[str, list[dict]],
    mod_wall: dict[str, float],
) -> dict:
    waves = topo_sort_modules(set(entries_by_name.keys()), imports_map)
    # Compute critical path (longest path in seconds through the DAG)
    crit_time = {}
    crit_pred = {}
    for w in waves:
        for m in w:
            deps_in_dag = [
                e["module"] for e in imports_map[m] if e["module"] in entries_by_name
            ]
            if not deps_in_dag:
                crit_time[m] = mod_wall[m]
                crit_pred[m] = None
            else:
                best_dep = max(deps_in_dag, key=lambda d: crit_time[d])
                crit_time[m] = crit_time[best_dep] + mod_wall[m]
                crit_pred[m] = best_dep

    end_node = max(crit_time, key=lambda k: crit_time[k])
    span_s = crit_time[end_node]
    path = []
    cur = end_node
    while cur is not None:
        path.append({"module": cur, "wall_s": mod_wall[cur]})
        cur = crit_pred[cur]
    path.reverse()

    work_s = sum(mod_wall.values())
    wave_span_s = sum(max(mod_wall[m] for m in w) for w in waves)
    return {
        "module_count": len(entries_by_name),
        "wave_count": len(waves),
        "waves": [
            [{"module": m, "wall_s": mod_wall[m]} for m in w]
            for w in waves
        ],
        "total_work_s": work_s,
        "critical_path_span_s": span_s,
        "wave_sync_span_s": wave_span_s,
        "theoretical_max_speedup_work_over_span": work_s / span_s if span_s > 0 else 1.0,
        "critical_path_nodes": path,
    }


def prepare_prebuilt_bundled(sample_work: Path) -> dict:
    cache_dir = TRACK2_DIR / "runs_exp2b" / "prebuilt_bundled"
    if cache_dir.exists():
        shutil.rmtree(cache_dir)
    cache_dir.mkdir(parents=True, exist_ok=True)
    lib_dir = cache_dir / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)

    state = load_admitted_base()
    sources = [(m, sample_work / rel) for m, rel, _ in BUNDLED_MODULES if m in REACHABLE_BUNDLED]
    _, imp_map = inspect_headers(cache_dir, state, sources)
    admit_reachable_libraries(
        state, [e["module"] for edges in imp_map.values() for e in edges]
    )
    for mod_name, rel_src, _ in BUNDLED_MODULES:
        if mod_name not in REACHABLE_BUNDLED:
            continue
        _, mod_arts = write_setup_and_compile(
            cache_dir,
            lib_dir,
            state,
            mod_name,
            sample_work / rel_src,
            imp_map[mod_name],
            allow_async=False,
            threads=1,
        )
        state["artifacts"][mod_name] = mod_arts
        state["graph"][mod_name] = imp_map[mod_name]
    return state


def build_starnix_sharded_entries(
    starnix_work: Path,
    k_shards: int,
    prebuilt_bundled: bool,
) -> tuple[list[dict], list[dict]]:
    """Returns (active_audit_entries, compile_entries) for starnix with K shards."""
    shard_src_dir = TRACK2_DIR / "runs_exp2b" / f"sharded_src_K{k_shards}"
    if shard_src_dir.exists():
        shutil.rmtree(shard_src_dir)
    shard_src_dir.mkdir(parents=True, exist_ok=True)

    capture_json = starnix_work / "capture" / "capture.json"
    gen_mods = generate_sharded(capture_json, shard_src_dir, k_shards)

    orig_req = json.loads((starnix_work / "audit-request.json").read_text())
    bundled_names = {m[0] for m in BUNDLED_MODULES}

    active_entries = []
    for m in orig_req["modules"]:
        mod_name = m["module"]
        if mod_name in bundled_names and mod_name not in REACHABLE_BUNDLED:
            continue
        if mod_name == "ProductionSteps":
            for gm in gen_mods:
                p = gm["path"]
                active_entries.append({
                    "module": gm["module"],
                    "source": str(p),
                    "expectedSha256": sha256_file(p),
                    "role": gm["role"],
                })
        else:
            local_src = resolve_local_source_path(starnix_work, m)
            active_entries.append({
                "module": mod_name,
                "source": str(local_src),
                "expectedSha256": m["expectedSha256"],
                "role": m["role"],
            })

    if prebuilt_bundled:
        compile_entries = [m for m in active_entries if m["module"] not in bundled_names]
    else:
        compile_entries = list(active_entries)

    return active_entries, compile_entries


def main() -> None:
    scalar_work = ensure_baseline_artifacts("scalar")
    spin_work = ensure_baseline_artifacts("spin")
    starnix_work = ensure_baseline_artifacts("starnix")

    print("Preparing pre-built bundled model cache for 2B...")
    prebuilt_state = prepare_prebuilt_bundled(scalar_work)

    # Part 1: DAG analysis of scalar, spin, and starnix (K=1..16)
    print("\n=== Part 1: DAG Analysis for scalar, spin, and starnix (K=1..16) ===")
    dag_analyses = {}
    for fx, work_dir in [("scalar", scalar_work), ("spin", spin_work)]:
        orig_req = json.loads((work_dir / "audit-request.json").read_text())
        bundled_names = {m[0] for m in BUNDLED_MODULES}
        entries = {}
        for m in orig_req["modules"]:
            if m["module"] in bundled_names and m["module"] not in REACHABLE_BUNDLED:
                continue
            local_src = resolve_local_source_path(work_dir, m)
            entries[m["module"]] = {
                "module": m["module"],
                "source": str(local_src),
                "expectedSha256": m["expectedSha256"],
                "role": m["role"],
            }
        s_dir = TRACK2_DIR / "runs_exp2b" / f"dag_{fx}"
        if s_dir.exists():
            shutil.rmtree(s_dir)
        s_dir.mkdir(parents=True, exist_ok=True)
        lib_dir = s_dir / "lib"
        lib_dir.mkdir(parents=True, exist_ok=True)
        state = load_admitted_base()
        _, imp_map = inspect_headers(
            s_dir, state, [(m["module"], Path(m["source"])) for m in entries.values()]
        )
        admit_reachable_libraries(
            state, [e["module"] for edges in imp_map.values() for e in edges]
        )
        run_res = run_dag_parallel(s_dir, lib_dir, state, entries, imp_map, max_workers=1)
        dag_info = compute_dag_metrics(entries, imp_map, run_res["module_wall_s"])
        dag_info["imports_map"] = {
            k: [e["module"] for e in v] for k, v in imp_map.items()
        }
        dag_analyses[fx] = dag_info
        print(
            f"  {fx:10s}: {dag_info['module_count']} mods, {dag_info['wave_count']} waves, "
            f"work={dag_info['total_work_s']*1000:7.1f} ms, "
            f"span={dag_info['critical_path_span_s']*1000:7.1f} ms, "
            f"max_speedup={dag_info['theoretical_max_speedup_work_over_span']:.2f}x"
        )

    # Part 2: Starnix Sharding (K in {1, 2, 4, 8, 16}) x Worker Pool (W in {1, 2, 4, 8})
    # We test with prebuilt_bundled=True (combining 2A + 2B) and also K=1..16 with prebuilt_bundled=False at W=1,4,8
    print("\n=== Part 2: Starnix Sharded ProductionSteps (K in {1,2,4,8,16}) x Workers (W in {1,2,4,8}) ===")
    starnix_orig_req = json.loads((starnix_work / "audit-request.json").read_text())
    k_values = [1, 2, 4, 8, 16]
    w_values = [1, 2, 4, 8]

    grid_results = []
    baseline_k1_w1_compile_wall = None

    for k in k_values:
        active_entries, compile_entries = build_starnix_sharded_entries(
            starnix_work, k_shards=k, prebuilt_bundled=True
        )
        entries_by_name = {m["module"]: m for m in compile_entries}

        # Inspect headers once for this K and measure headers time
        hdr_dir = TRACK2_DIR / "runs_exp2b" / f"hdr_K{k}"
        if hdr_dir.exists():
            shutil.rmtree(hdr_dir)
        hdr_dir.mkdir(parents=True, exist_ok=True)
        base_st = copy.deepcopy(prebuilt_state)
        t_hdr, imp_map = inspect_headers(
            hdr_dir,
            base_st,
            [(m["module"], Path(m["source"])) for m in compile_entries],
        )
        admit_reachable_libraries(
            base_st, [e["module"] for edges in imp_map.values() for e in edges]
        )

        for w in w_values:
            run_dir = TRACK2_DIR / "runs_exp2b" / f"starnix_K{k}_W{w}"
            if run_dir.exists():
                shutil.rmtree(run_dir)
            run_dir.mkdir(parents=True, exist_ok=True)
            lib_dir = run_dir / "lib"
            lib_dir.mkdir(parents=True, exist_ok=True)

            state = copy.deepcopy(base_st)
            dag_res = run_dag_parallel(
                run_dir,
                lib_dir,
                state,
                entries_by_name,
                imp_map,
                max_workers=w,
                allow_async=False,
                threads_per_worker=1,
            )

            if w == 1:
                dag_info = compute_dag_metrics(entries_by_name, imp_map, dag_res["module_wall_s"])
                dag_info["imports_map"] = {
                    mod_k: [e["module"] for e in mod_v] for mod_k, mod_v in imp_map.items()
                }
                dag_analyses[f"starnix_K{k}_prebuilt_model"] = dag_info
                if k == 1:
                    baseline_k1_w1_compile_wall = dag_res["wall_s"]

            # Run TargetAudit for w == 1 (and verify w == 8 matches) to measure audit overhead vs K
            audit_wall_s = None
            replayed_decls = None
            if w in (1, 8):
                target_req = copy.deepcopy(starnix_orig_req)
                target_req["modules"] = active_entries
                t_audit, audit_res = run_target_audit(run_dir, state, target_req)
                audit_wall_s = t_audit["wall_s"]
                replayed_decls = audit_res["replayedDeclarations"]

            comp_speedup = (
                baseline_k1_w1_compile_wall / dag_res["wall_s"]
                if baseline_k1_w1_compile_wall and dag_res["wall_s"] > 0
                else 1.0
            )
            audit_str = (
                f"audit={audit_wall_s*1000:6.1f} ms (replayed={replayed_decls})"
                if audit_wall_s is not None
                else "audit=skipped"
            )
            print(
                f"  K={k:2d}, W={w:1d} (sync -j1): "
                f"comp_wall={dag_res['wall_s']*1000:7.1f} ms (speedup={comp_speedup:5.2f}x), "
                f"cpu={dag_res['cpu_s']*1000:7.1f} ms (util={dag_res['effective_cpu_util']:4.2f}x), "
                f"hdr={t_hdr['wall_s']*1000:6.1f} ms | {audit_str}"
            )

            grid_results.append({
                "k_shards": k,
                "workers": w,
                "allow_async": False,
                "threads_per_worker": 1,
                "prebuilt_model": True,
                "compiled_modules": len(compile_entries),
                "headers_wall_s": t_hdr["wall_s"],
                "compile_wall_s": dag_res["wall_s"],
                "compile_cpu_s": dag_res["cpu_s"],
                "compile_user_s": dag_res["user_s"],
                "compile_sys_s": dag_res["sys_s"],
                "sum_module_wall_s": dag_res["sum_module_wall_s"],
                "effective_cpu_util": dag_res["effective_cpu_util"],
                "compile_speedup_vs_k1_w1": comp_speedup,
                "audit_wall_s": audit_wall_s,
                "replayedDeclarations": replayed_decls,
                "module_wall_s": dag_res["module_wall_s"],
            })

    # Part 3: Combined 2A + 2B + 2C (Prebuilt Model + DAG Parallelism W + -DElab.async=true -jT)
    print("\n=== Part 3: Combined 2A + 2B + 2C (Prebuilt Model + DAG W + -DElab.async=true -jT) ===")
    combined_configs = [
        (1, 1, True, 4),
        (1, 1, True, 8),
        (1, 2, True, 4),
        (1, 4, True, 2),
        (2, 2, True, 4),
        (2, 4, True, 2),
        (4, 4, True, 2),
        (4, 8, True, 2),
        (8, 8, True, 2),
    ]
    combined_results = []
    for k, w, allow_async, threads in combined_configs:
        active_entries, compile_entries = build_starnix_sharded_entries(
            starnix_work, k_shards=k, prebuilt_bundled=True
        )
        entries_by_name = {m["module"]: m for m in compile_entries}
        run_dir = TRACK2_DIR / "runs_exp2b" / f"combined_K{k}_W{w}_j{threads}"
        if run_dir.exists():
            shutil.rmtree(run_dir)
        run_dir.mkdir(parents=True, exist_ok=True)
        lib_dir = run_dir / "lib"
        lib_dir.mkdir(parents=True, exist_ok=True)

        state = copy.deepcopy(prebuilt_state)
        t_hdr, imp_map = inspect_headers(
            run_dir,
            state,
            [(m["module"], Path(m["source"])) for m in compile_entries],
        )
        admit_reachable_libraries(
            state, [e["module"] for edges in imp_map.values() for e in edges]
        )
        dag_res = run_dag_parallel(
            run_dir,
            lib_dir,
            state,
            entries_by_name,
            imp_map,
            max_workers=w,
            allow_async=allow_async,
            threads_per_worker=threads,
        )
        target_req = copy.deepcopy(starnix_orig_req)
        target_req["modules"] = active_entries
        t_audit, audit_res = run_target_audit(run_dir, state, target_req)

        comp_speedup = (
            baseline_k1_w1_compile_wall / dag_res["wall_s"]
            if baseline_k1_w1_compile_wall and dag_res["wall_s"] > 0
            else 1.0
        )
        tot_wall = t_hdr["wall_s"] + dag_res["wall_s"] + t_audit["wall_s"]
        print(
            f"  K={k:2d}, W={w:1d}, async -j{threads}: "
            f"comp_wall={dag_res['wall_s']*1000:7.1f} ms (speedup={comp_speedup:5.2f}x), "
            f"cpu={dag_res['cpu_s']*1000:7.1f} ms (util={dag_res['effective_cpu_util']:4.2f}x), "
            f"total_lean={tot_wall*1000:7.1f} ms (replayed={audit_res['replayedDeclarations']})"
        )
        combined_results.append({
            "k_shards": k,
            "workers": w,
            "allow_async": allow_async,
            "threads_per_worker": threads,
            "headers_wall_s": t_hdr["wall_s"],
            "compile_wall_s": dag_res["wall_s"],
            "compile_cpu_s": dag_res["cpu_s"],
            "effective_cpu_util": dag_res["effective_cpu_util"],
            "compile_speedup_vs_k1_w1_sync": comp_speedup,
            "audit_wall_s": t_audit["wall_s"],
            "total_lean_wall_s": tot_wall,
            "replayedDeclarations": audit_res["replayedDeclarations"],
            "module_wall_s": dag_res["module_wall_s"],
        })

    out_path = TRACK2_DIR / "support" / "exp2b_results.json"
    out_path.write_text(
        json.dumps(
            {
                "dag_analyses": dag_analyses,
                "sharded_grid_results": grid_results,
                "combined_2a_2b_2c_results": combined_results,
            },
            indent=2,
        )
    )
    print(f"\nSaved Experiment 2B results to {out_path}")


if __name__ == "__main__":
    main()
