#!/usr/bin/env python3
import hashlib, json, os, shutil, subprocess, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

LEAN = "/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
TB_BIN = "/tmp/ref_research_stack221_perf/track3/bin/trusted-boundary-exp3c-bin"
T3_STAGES = Path("/tmp/ref_research_stack221_perf/track3/stages")
T4_SUP = Path("/tmp/ref_research_stack221_perf/track4/support")
OUT_DIR = Path("/tmp/ref_research_stack221_perf/combined_round2")

def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def compile_mod(stage_dir: Path, mod: str, setup_path: Path, src_path: Path, olean_path: Path, threads: int = 4, async_elab: bool = True):
    cmd = [
        LEAN,
        f"-j{threads}", "-M2048", "-t0",
        f"-DElab.async={'true' if async_elab else 'false'}",
        "-Ddebug.skipKernelTC=false",
        "--setup", str(setup_path),
        "-o", str(olean_path),
        str(src_path),
    ]
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=stage_dir, capture_output=True, text=True)
    dt = (time.perf_counter() - t0) * 1000.0
    if proc.returncode != 0:
        raise RuntimeError(f"Failed {mod}: {proc.stdout}\n{proc.stderr}")
    return mod, dt

def run_starnix_combined():
    stage = OUT_DIR / "stage_starnix_combined"
    if stage.exists():
        shutil.rmtree(stage)
    shutil.copytree(T3_STAGES / "starnix", stage)

    # Replace Endianness.lean and ProductionSteps.lean with Track 4's WHNF-clean versions
    shutil.copy2(T4_SUP / "Endianness_Optimized.lean", stage / "target-src/Endianness.lean")
    shutil.copy2(T4_SUP / "ProductionSteps_Optimized.lean", stage / "target-src/ProductionSteps.lean")

    # Keep pre-compiled Model .oleans (Trusted.Mvp.Syntax, Trusted.Mvp.Semantics, Trusted.Mvp, Anneal.Mvp.Execution)
    # and recompile the 10 target modules in 4 parallel DAG waves with -DElab.async=true -j4
    waves = [
        ["Captured", "Endianness", "Inputs"],
        ["Spec", "SourceInputs", "InitialCache", "ProductionSteps"],
        ["Expected", "ProductionClaims"],
        ["Proof"],
    ]

    wave_timings = []
    mod_timings = {}
    t_dag_start = time.perf_counter()
    for w_idx, wave in enumerate(waves):
        tw0 = time.perf_counter()
        with ThreadPoolExecutor(max_workers=len(wave)) as ex:
            futs = []
            for m in wave:
                rel = m.replace(".", "/")
                setup_p = stage / f"{m}.setup.json"
                src_p = stage / f"target-src/{rel}.lean"
                olean_p = stage / f"target-lib/{rel}.olean"
                if olean_p.exists():
                    olean_p.unlink()
                futs.append(ex.submit(compile_mod, stage, m, setup_p, src_p, olean_p, 4, True))
            for f in futs:
                m, dt = f.result()
                mod_timings[m] = round(dt, 2)
        wave_ms = (time.perf_counter() - tw0) * 1000.0
        wave_timings.append({"wave": w_idx + 1, "modules": wave, "wall_ms": round(wave_ms, 2)})
    total_dag_ms = (time.perf_counter() - t_dag_start) * 1000.0

    # Update expectedSha256 for Endianness and ProductionSteps in request-002-target-audit.json
    req = json.loads((stage / "request-002-target-audit.json").read_text())
    # Also prune the 3 unimported dead modules (Trusted, Anneal, Anneal.Mvp.Canaries)
    dead = set()
    req["target"]["modules"] = [
        m for m in req["target"]["modules"] if m["module"] not in dead
    ]
    for m in req["target"]["modules"]:
        p = Path(m["source"])
        rel = m["module"].replace(".", "/")
        local_p = stage / f"target-src/{rel}.lean"
        m["source"] = str(local_p)
        m["expectedSha256"] = sha256_file(local_p)
    new_art = []
    for k, v in req["artifacts"]:
        if k in dead:
            continue
        olean_p = stage / f"target-lib/{k.replace('.', '/')}.olean"
        if olean_p.exists():
            v = [[str(olean_p)], v[1]]
        new_art.append([k, v])
    req["artifacts"] = new_art
    req["graph"] = {k: v for k, v in req["graph"].items() if k not in dead}

    audit_results = {}
    for label, base_mode, skip_meta in [
        ("native_foundation", "foundation", False),
        ("native_foundation_plus_mvp_no_meta_reload", "foundation+mvp", True),
    ]:
        req_m = dict(req)
        req_m["baseMode"] = base_mode
        req_m["skipRedundantMetadataImport"] = skip_meta
        req_p = stage / f"req_{label}.json"
        out_p = stage / f"out_{label}.json"
        req_p.write_text(json.dumps(req_m))
        t0 = time.perf_counter()
        proc = subprocess.run([TB_BIN, str(req_p), str(out_p)], cwd=stage, capture_output=True, text=True)
        wall_ms = (time.perf_counter() - t0) * 1000.0
        if proc.returncode != 0:
            raise RuntimeError(f"Audit {label} failed: {proc.stdout}\n{proc.stderr}")
        timings = json.loads(Path(str(out_p) + ".timings.json").read_text())
        out_json = json.loads(out_p.read_text())
        audit_results[label] = {
            "wall_ms": round(wall_ms, 2),
            "ok": out_json.get("ok"),
            "exactType": out_json.get("result", {}).get("exactType"),
            "axioms": out_json.get("result", {}).get("axioms"),
            "replayMapSize": timings["auditBreakdown"]["replayMapSize"],
            "kernelReplayTotalMs": round(timings["auditBreakdown"]["phasesMs"]["kernelReplayTotal"], 2),
            "addDeclCoreSumMs": round(timings["auditBreakdown"]["phasesMs"]["kernelReplayAddDeclCoreSum"], 2),
            "phasesMs": timings["auditBreakdown"]["phasesMs"],
        }

    summary = {
        "starnix_combined_cold": {
            "dag_waves": wave_timings,
            "module_compile_ms": mod_timings,
            "total_dag_compile_wall_ms": round(total_dag_ms, 2),
            "sum_module_compile_ms": round(sum(mod_timings.values()), 2),
            "target_audit": audit_results,
        }
    }
    (OUT_DIR / "combined_round2_results.json").write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    run_starnix_combined()

def run_small_combined(fixture_name: str):
    stage = OUT_DIR / f"stage_{fixture_name}_combined"
    if stage.exists():
        shutil.rmtree(stage)
    shutil.copytree(T3_STAGES / fixture_name, stage)

    waves = [
        ["Captured", "Spec"],
        ["Expected"],
        ["Proof"],
    ]
    wave_timings = []
    mod_timings = {}
    t_dag_start = time.perf_counter()
    for w_idx, wave in enumerate(waves):
        tw0 = time.perf_counter()
        with ThreadPoolExecutor(max_workers=len(wave)) as ex:
            futs = []
            for m in wave:
                rel = m.replace(".", "/")
                setup_p = stage / f"{m}.setup.json"
                src_p = stage / f"target-src/{rel}.lean"
                olean_p = stage / f"target-lib/{rel}.olean"
                if olean_p.exists():
                    olean_p.unlink()
                futs.append(ex.submit(compile_mod, stage, m, setup_p, src_p, olean_p, 4, True))
            for f in futs:
                m, dt = f.result()
                mod_timings[m] = round(dt, 2)
        wave_ms = (time.perf_counter() - tw0) * 1000.0
        wave_timings.append({"wave": w_idx + 1, "modules": wave, "wall_ms": round(wave_ms, 2)})
    total_dag_ms = (time.perf_counter() - t_dag_start) * 1000.0

    req = json.loads((stage / "request-002-target-audit.json").read_text())
    for m in req["target"]["modules"]:
        rel = m["module"].replace(".", "/")
        local_p = stage / f"target-src/{rel}.lean"
        m["source"] = str(local_p)
        m["expectedSha256"] = sha256_file(local_p)
    new_art = []
    for k, v in req["artifacts"]:
        olean_p = stage / f"target-lib/{k.replace('.', '/')}.olean"
        if olean_p.exists():
            v = [[str(olean_p)], v[1]]
        new_art.append([k, v])
    req["artifacts"] = new_art

    req["baseMode"] = "foundation+mvp"
    req["skipRedundantMetadataImport"] = True
    req_p = stage / "req_opt.json"
    out_p = stage / "out_opt.json"
    req_p.write_text(json.dumps(req))
    t0 = time.perf_counter()
    proc = subprocess.run([TB_BIN, str(req_p), str(out_p)], cwd=stage, capture_output=True, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    if proc.returncode != 0:
        raise RuntimeError(f"Audit {fixture_name} failed: {proc.stdout}\n{proc.stderr}")
    timings = json.loads(Path(str(out_p) + ".timings.json").read_text())
    out_json = json.loads(out_p.read_text())
    return {
        "dag_waves": wave_timings,
        "module_compile_ms": mod_timings,
        "total_dag_compile_wall_ms": round(total_dag_ms, 2),
        "target_audit": {
            "wall_ms": round(wall_ms, 2),
            "ok": out_json.get("ok"),
            "exactType": out_json.get("result", {}).get("exactType"),
            "replayMapSize": timings["auditBreakdown"]["replayMapSize"],
            "kernelReplayTotalMs": round(timings["auditBreakdown"]["phasesMs"]["kernelReplayTotal"], 2),
        },
    }

if __name__ == "__main__":
    data = json.loads((OUT_DIR / "combined_round2_results.json").read_text())
    data["scalar_combined_cold"] = run_small_combined("scalar")
    data["spin_combined_cold"] = run_small_combined("spin")
    (OUT_DIR / "combined_round2_results.json").write_text(json.dumps(data, indent=2))
    print(json.dumps({"scalar": data["scalar_combined_cold"], "spin": data["spin_combined_cold"]}, indent=2))
