#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Experiment 2C: Intra-file parallel elaboration (-DElab.async=true) across threads.

Benchmarks:
- -DElab.async=false (-j1) vs -DElab.async=true with T in {1, 2, 4, 8}
  on ProductionSteps.lean (starnix), Proof.lean (starnix), Execution.lean,
  Semantics.lean, Endianness.lean (starnix), Canaries.lean, and Proof.lean (spin).
- Verifies SHA-256 determinism of .olean outputs across trials, across thread
  counts, and against synchronous (-DElab.async=false -j1) outputs.
- Verifies that TrustedBoundary.lean's TargetAudit (base.toKernelEnv.replay)
  accepts the -DElab.async=true -j8 .olean modules identically.
"""

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
    ensure_baseline_artifacts,
    inspect_headers,
    load_admitted_base,
    resolve_local_source_path,
    run_target_audit,
    sha256_file,
    topo_sort_modules,
    write_setup_and_compile,
)


def prepare_full_fixture_state(fixture_name: str, work_dir: Path) -> tuple[dict, dict, dict, Path]:
    """Compiles all modules of a fixture once so all dependency importArts are ready."""
    prep_dir = TRACK2_DIR / "runs_exp2c" / f"prep_{fixture_name}"
    if prep_dir.exists():
        shutil.rmtree(prep_dir)
    prep_dir.mkdir(parents=True, exist_ok=True)
    lib_dir = prep_dir / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)

    orig_req = json.loads((work_dir / "audit-request.json").read_text())
    mod_entries = {}
    for m in orig_req["modules"]:
        local_src = resolve_local_source_path(work_dir, m)
        mod_entries[m["module"]] = {
            "module": m["module"],
            "source": local_src,
            "expectedSha256": m["expectedSha256"],
            "role": m["role"],
        }

    state = load_admitted_base()
    hdr_sources = [(m["module"], m["source"]) for m in mod_entries.values()]
    _, imports_map = inspect_headers(prep_dir, state, hdr_sources)
    all_imp_names = [e["module"] for edges in imports_map.values() for e in edges]
    admit_reachable_libraries(state, all_imp_names)

    waves = topo_sort_modules(set(mod_entries.keys()), imports_map)
    for w in waves:
        for mod_name in w:
            m_entry = mod_entries[mod_name]
            edges = imports_map[mod_name]
            _, mod_arts = write_setup_and_compile(
                prep_dir,
                lib_dir,
                state,
                mod_name,
                m_entry["source"],
                edges,
                allow_async=False,
                threads=1,
            )
            state["artifacts"][mod_name] = mod_arts
            state["graph"][mod_name] = edges

    return state, mod_entries, imports_map, orig_req


def main() -> None:
    starnix_work = ensure_baseline_artifacts("starnix")
    spin_work = ensure_baseline_artifacts("spin")
    scalar_work = ensure_baseline_artifacts("scalar")

    print("Preparing dependency environments for starnix, spin, scalar...")
    starnix_state, starnix_entries, starnix_imports, starnix_req = prepare_full_fixture_state(
        "starnix", starnix_work
    )
    spin_state, spin_entries, spin_imports, spin_req = prepare_full_fixture_state(
        "spin", spin_work
    )
    scalar_state, scalar_entries, scalar_imports, scalar_req = prepare_full_fixture_state(
        "scalar", scalar_work
    )

    targets = [
        ("starnix", starnix_state, starnix_entries, starnix_imports, "ProductionSteps"),
        ("starnix", starnix_state, starnix_entries, starnix_imports, "Proof"),
        ("starnix", starnix_state, starnix_entries, starnix_imports, "Anneal.Mvp.Execution"),
        ("starnix", starnix_state, starnix_entries, starnix_imports, "Trusted.Mvp.Semantics"),
        ("starnix", starnix_state, starnix_entries, starnix_imports, "Endianness"),
        ("starnix", starnix_state, starnix_entries, starnix_imports, "Anneal.Mvp.Canaries"),
        ("spin", spin_state, spin_entries, spin_imports, "Proof"),
    ]

    configs = [
        (False, 1),
        (True, 1),
        (True, 2),
        (True, 4),
        (True, 8),
    ]

    bench_root = TRACK2_DIR / "runs_exp2c" / "trials"
    if bench_root.exists():
        shutil.rmtree(bench_root)
    bench_root.mkdir(parents=True, exist_ok=True)

    module_results = []
    for fx, base_state, entries, imports_map, mod_name in targets:
        m_entry = entries[mod_name]
        src_path = m_entry["source"]
        src_lines = len(src_path.read_text().splitlines())
        src_bytes = src_path.stat().st_size
        edges = imports_map[mod_name]
        print(f"\n=== Benchmarking {fx} :: {mod_name} ({m_entry['role']}, {src_lines} lines) ===")

        sync_wall = None
        sync_digests = None
        cfg_list = []

        for allow_async, threads in configs:
            trials = []
            trial_digests = []
            n_trials = 2 if mod_name in ("ProductionSteps", "Proof") and fx == "starnix" else 3
            for t_idx in range(n_trials):
                t_dir = bench_root / f"{fx}_{mod_name.replace('.', '_')}_a{int(allow_async)}_j{threads}_t{t_idx}"
                t_dir.mkdir(parents=True, exist_ok=True)
                t_lib = t_dir / "lib"
                t_lib.mkdir(parents=True, exist_ok=True)

                t_comp, _ = write_setup_and_compile(
                    t_dir,
                    t_lib,
                    base_state,
                    mod_name,
                    src_path,
                    edges,
                    allow_async=allow_async,
                    threads=threads,
                )
                trials.append(t_comp)

                rel_mod = mod_name.replace(".", "/")
                digests = {}
                for part in PARTS:
                    p = t_lib / f"{rel_mod}.{part}"
                    if p.is_file():
                        digests[part] = sha256_file(p)
                trial_digests.append(digests)

            wall_mean = sum(r["wall_s"] for r in trials) / len(trials)
            wall_min = min(r["wall_s"] for r in trials)
            cpu_mean = sum(r["cpu_s"] for r in trials) / len(trials)
            user_mean = sum(r["user_s"] for r in trials) / len(trials)
            sys_mean = sum(r["sys_s"] for r in trials) / len(trials)

            if not allow_async and threads == 1:
                sync_wall = wall_mean
                sync_digests = trial_digests[0]

            speedup = sync_wall / wall_mean if sync_wall and wall_mean > 0 else 1.0
            eff_threads = cpu_mean / wall_mean if wall_mean > 0 else 1.0
            intra_det = all(d == trial_digests[0] for d in trial_digests[1:])
            matches_sync = {
                part: (trial_digests[0].get(part) == sync_digests.get(part))
                for part in trial_digests[0]
            }

            print(
                f"  async={str(allow_async):5s} -j{threads}: "
                f"wall={wall_mean*1000:7.1f} ms (min={wall_min*1000:7.1f} ms), "
                f"cpu={cpu_mean*1000:7.1f} ms (eff={eff_threads:4.2f}x), "
                f"speedup={speedup:5.2f}x | "
                f"intra_det={intra_det}, olean_eq_sync={matches_sync.get('olean')}"
            )

            cfg_list.append({
                "allow_async": allow_async,
                "threads": threads,
                "wall_s_runs": [r["wall_s"] for r in trials],
                "wall_s_mean": wall_mean,
                "wall_s_min": wall_min,
                "cpu_s_mean": cpu_mean,
                "user_s_mean": user_mean,
                "sys_s_mean": sys_mean,
                "effective_parallelism": eff_threads,
                "speedup_vs_sync_j1": speedup,
                "intra_config_deterministic": intra_det,
                "matches_sync_j1_by_part": matches_sync,
                "digests_trial0": trial_digests[0],
            })

        module_results.append({
            "fixture": fx,
            "module": mod_name,
            "role": m_entry["role"],
            "src_lines": src_lines,
            "src_bytes": src_bytes,
            "configs": cfg_list,
        })

    # Also benchmark end-to-end starnix compilation with -DElab.async=true -j4 and -j8
    # (both with and without pre-compiled Model modules from 2A-2) and verify TargetAudit!
    print("\n=== Full Starnix Pipeline with -DElab.async=true (-j4 and -j8) + TargetAudit ===")
    e2e_async_runs = []
    for prebuilt_model, threads in [(False, 8), (True, 1), (True, 2), (True, 4), (True, 8)]:
        if True:
            allow_async = True
            run_label = f"prebuilt={prebuilt_model}_async_j{threads}"
            s_dir = bench_root / f"e2e_starnix_{run_label}"
            s_dir.mkdir(parents=True, exist_ok=True)
            s_lib = s_dir / "lib"
            s_lib.mkdir(parents=True, exist_ok=True)

            state = load_admitted_base()
            bundled_names = {m[0] for m in BUNDLED_MODULES}
            active_entries = [
                m
                for m in starnix_entries.values()
                if (m["module"] not in bundled_names) or (m["module"] in REACHABLE_BUNDLED)
            ]
            if prebuilt_model:
                compile_entries = [m for m in active_entries if m["module"] not in bundled_names]
                for b_mod in REACHABLE_BUNDLED:
                    state["artifacts"][b_mod] = starnix_state["artifacts"][b_mod]
                    state["graph"][b_mod] = starnix_state["graph"][b_mod]
                    admit_reachable_libraries(
                        state, [e["module"] for e in starnix_state["graph"][b_mod]]
                    )
            else:
                compile_entries = active_entries

            hdr_sources = [(m["module"], m["source"]) for m in compile_entries]
            t_hdr, imp_map = inspect_headers(s_dir, state, hdr_sources)
            admit_reachable_libraries(
                state, [e["module"] for edges in imp_map.values() for e in edges]
            )

            waves = topo_sort_modules({m["module"] for m in compile_entries}, imp_map)
            comp_wall = 0.0
            comp_cpu = 0.0
            for w in waves:
                for mod_name in w:
                    m_entry = starnix_entries[mod_name]
                    t_c, mod_arts = write_setup_and_compile(
                        s_dir,
                        s_lib,
                        state,
                        mod_name,
                        m_entry["source"],
                        imp_map[mod_name],
                        allow_async=allow_async,
                        threads=threads,
                    )
                    state["artifacts"][mod_name] = mod_arts
                    state["graph"][mod_name] = imp_map[mod_name]
                    comp_wall += t_c["wall_s"]
                    comp_cpu += t_c["cpu_s"]

            target_req = copy.deepcopy(starnix_req)
            target_req["modules"] = [
                {
                    "module": m["module"],
                    "source": str(m["source"]),
                    "expectedSha256": m["expectedSha256"],
                    "role": m["role"],
                }
                for m in active_entries
            ]
            t_audit, audit_res = run_target_audit(s_dir, state, target_req)
            tot_wall = t_hdr["wall_s"] + comp_wall + t_audit["wall_s"]
            print(
                f"  {run_label:28s}: total={tot_wall*1000:7.1f} ms "
                f"(hdr={t_hdr['wall_s']*1000:5.1f} ms, comp={comp_wall*1000:7.1f} ms, "
                f"audit={t_audit['wall_s']*1000:5.1f} ms) | "
                f"replayed={audit_res['replayedDeclarations']}"
            )
            e2e_async_runs.append({
                "prebuilt_model": prebuilt_model,
                "allow_async": allow_async,
                "threads": threads,
                "headers_wall_s": t_hdr["wall_s"],
                "compile_wall_s": comp_wall,
                "compile_cpu_s": comp_cpu,
                "audit_wall_s": t_audit["wall_s"],
                "total_lean_wall_s": tot_wall,
                "replayedDeclarations": audit_res["replayedDeclarations"],
                "modelClosure_count": len(audit_res["modelClosure"]),
                "specificationClosure_count": len(audit_res["specificationClosure"]),
                "axioms": audit_res["axioms"],
            })

    out_path = TRACK2_DIR / "support" / "exp2c_results.json"
    out_path.write_text(
        json.dumps(
            {
                "module_benchmarks": module_results,
                "e2e_starnix_async_runs": e2e_async_runs,
            },
            indent=2,
        )
    )
    print(f"\nSaved Experiment 2C results to {out_path}")


if __name__ == "__main__":
    main()
