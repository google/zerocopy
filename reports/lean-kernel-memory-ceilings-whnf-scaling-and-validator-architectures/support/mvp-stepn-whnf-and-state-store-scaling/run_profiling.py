#!/usr/bin/env python3
import hashlib
import json
import os
import re
import shutil
import subprocess
import time
from pathlib import Path

SCRATCH = Path("<scratch>/mvp-investigations/task3")
BASELINE_ARTIFACTS = Path("/tmp/anneal-mvp-starnix-bundle-final/baseline-artifacts")
MVP_ROOT = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")
TOOLCHAIN_ROOT = Path("<host-home>/.cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a")
CAPTURE_BIN = TOOLCHAIN_ROOT / "bin/anneal-rustc-capture"
SYSROOT = TOOLCHAIN_ROOT / "rust"
LEAN_BIN = TOOLCHAIN_ROOT / "lean/bin/lean"
LEAN_PREFIX = TOOLCHAIN_ROOT / "lean"

PARTS = ["olean", "olean.server", "olean.private", "ir.sig", "ir"]
OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]

def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()

def parse_time_v(stderr: str) -> dict:
    user_m = re.search(r"User time \(seconds\):\s*([0-9.]+)", stderr)
    sys_m = re.search(r"System time \(seconds\):\s*([0-9.]+)", stderr)
    rss_m = re.search(r"Maximum resident set size \(kbytes\):\s*([0-9]+)", stderr)
    return {
        "user_s": float(user_m.group(1)) if user_m else 0.0,
        "sys_s": float(sys_m.group(1)) if sys_m else 0.0,
        "max_rss_kb": int(rss_m.group(1)) if rss_m else 0,
    }

def run_timed(cmd: list[str], cwd: Path, env: dict[str, str], mode: str = "file") -> dict:
    wrapped = [
        "anneal-lean-run", "--mode", mode, "--concurrency", "4", "--",
        "/usr/bin/time", "-v"
    ] + cmd
    t0 = time.perf_counter()
    res = subprocess.run(wrapped, cwd=cwd, env=env, capture_output=True, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    if res.returncode != 0:
        raise RuntimeError(f"Command failed ({res.returncode}): {' '.join(cmd)}\nstdout: {res.stdout}\nstderr: {res.stderr}")
    stats = parse_time_v(res.stderr)
    stats["wall_ms"] = wall_ms
    stats["stdout"] = res.stdout
    return stats

def main():
    SCRATCH.mkdir(parents=True, exist_ok=True)
    work = SCRATCH / "profile_stage"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    clean_env = {
        "HOME": os.environ.get("HOME", "/root"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "PATH": f"{os.path.expanduser('~/.local/bin')}:/usr/bin:/bin",
    }

    report = {}

    # 1. Measure Rust source staging + hashing + capture
    t_hash0 = time.perf_counter()
    req_data = json.loads((BASELINE_ARTIFACTS / "request.json").read_text())
    rust_stage = work / "rust"
    rust_stage.mkdir(parents=True)
    rust_bytes_total = 0
    for rel in req_data["compilation"]["source_files"]:
        src = BASELINE_ARTIFACTS / "rust" / rel
        b = src.read_bytes()
        rust_bytes_total += len(b)
        _ = hashlib.sha256(b).hexdigest()
        dst = rust_stage / rel
        dst.write_bytes(b)
    cap_bin_sha = sha256_file(CAPTURE_BIN)
    t_rust_stage_ms = (time.perf_counter() - t_hash0) * 1000.0

    capture_dir = work / "capture"
    capture_dir.mkdir()
    cap_env = dict(clean_env)
    cap_env["LD_LIBRARY_PATH"] = str(SYSROOT / "lib")
    if req_data["scope"]["kind"] == "selected_unit":
        cap_cmd = [
            str(CAPTURE_BIN),
            "--crate-root", str(rust_stage / req_data["compilation"]["crate_root"]),
            "--crate-name", req_data["compilation"]["crate_name"],
            "--edition", req_data["compilation"]["edition"],
            "--target", req_data["compilation"]["target"],
            "--out-dir", str(capture_dir),
            "--sysroot", str(SYSROOT),
        ]
        for r in req_data["scope"]["roots"]:
            cap_cmd.extend(["--select", r])
    else:
        cap_cmd = [
            str(CAPTURE_BIN),
            "--crate-root", str(rust_stage / req_data["compilation"]["crate_root"]),
            "--crate-name", req_data["compilation"]["crate_name"],
            "--edition", req_data["compilation"]["edition"],
            "--target", req_data["compilation"]["target"],
            "--out-dir", str(capture_dir),
            "--sysroot", str(SYSROOT),
            "--scope", "crate",
        ]
    for rel in req_data["compilation"]["source_files"]:
        cap_cmd.extend(["--source-file", str(rust_stage / rel)])

    cap_stats = run_timed(cap_cmd, cwd=rust_stage, env=cap_env, mode="file")
    t_cap_hash0 = time.perf_counter()
    cap_json_bytes = (capture_dir / "capture.json").read_bytes()
    _ = hashlib.sha256(cap_json_bytes).hexdigest()
    cap_lean_bytes = (capture_dir / "Captured.lean").read_bytes()
    _ = hashlib.sha256(cap_lean_bytes).hexdigest()
    t_cap_hash_ms = (time.perf_counter() - t_cap_hash0) * 1000.0

    report["capture"] = {
        "rust_stage_and_capture_bin_hash_ms": t_rust_stage_ms,
        "rust_source_files": len(req_data["compilation"]["source_files"]),
        "rust_source_bytes": rust_bytes_total,
        "capture_binary_bytes": CAPTURE_BIN.stat().st_size,
        "capture_exec_wall_ms": cap_stats["wall_ms"],
        "capture_exec_user_s": cap_stats["user_s"],
        "capture_exec_sys_s": cap_stats["sys_s"],
        "capture_exec_max_rss_kb": cap_stats["max_rss_kb"],
        "capture_json_bytes": len(cap_json_bytes),
        "captured_lean_bytes": len(cap_lean_bytes),
        "capture_output_hash_ms": t_cap_hash_ms,
    }
    print("Capture stats:", json.dumps(report["capture"], indent=2))

    # 2. Measure tool_admission & library_lock hashing
    fl = json.loads((BASELINE_ARTIFACTS / "anneal/trusted/lean/foundation-lock.json").read_text())
    ll = json.loads((BASELINE_ARTIFACTS / "anneal/trusted/audit/library-lock.json").read_text())

    t_adm0 = time.perf_counter()
    _ = sha256_file(LEAN_BIN)
    t_lean_bin_hash_ms = (time.perf_counter() - t_adm0) * 1000.0

    ver_stats = run_timed([str(LEAN_BIN), "--version"], cwd=work, env=clean_env)
    pref_stats = run_timed([str(LEAN_BIN), "--print-prefix"], cwd=work, env=clean_env)

    t_fl0 = time.perf_counter()
    fl_files = 0
    fl_bytes = 0
    artifacts_map = {}
    graph_map = dict(fl["graph"])
    for mod, rec in fl["modules"].items():
        rel_mod = mod.replace(".", "/")
        sp = LEAN_PREFIX / "src/lean" / f"{rel_mod}.lean"
        fl_bytes += sp.stat().st_size
        fl_files += 1
        _ = sha256_file(sp)
        avail = {}
        for part in PARTS:
            if rec["parts"][part] is not None:
                pp = LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}"
                fl_bytes += pp.stat().st_size
                fl_files += 1
                _ = sha256_file(pp)
                avail[part] = str(pp)
        artifacts_map[mod] = [
            [avail[p] for p in OLEAN_PARTS if p in avail],
            [avail[p] for p in IR_PARTS if p in avail],
        ]
    t_fl_hash_ms = (time.perf_counter() - t_fl0) * 1000.0

    t_ll0 = time.perf_counter()
    ll_files = 0
    ll_bytes = 0
    for mod, rec in ll["modules"].items():
        rel_mod = mod.replace(".", "/")
        sp = LEAN_PREFIX / "src/lean" / f"{rel_mod}.lean"
        ll_bytes += sp.stat().st_size
        ll_files += 1
        _ = sha256_file(sp)
        avail = {}
        for part in PARTS:
            if rec["parts"][part] is not None:
                pp = LEAN_PREFIX / "lib/lean" / f"{rel_mod}.{part}"
                ll_bytes += pp.stat().st_size
                ll_files += 1
                _ = sha256_file(pp)
                avail[part] = str(pp)
        artifacts_map[mod] = [
            [avail[p] for p in OLEAN_PARTS if p in avail],
            [avail[p] for p in IR_PARTS if p in avail],
        ]
        graph_map[mod] = ll["graph"][mod]
    t_ll_hash_ms = (time.perf_counter() - t_ll0) * 1000.0

    report["admission_and_locks"] = {
        "lean_bin_bytes": LEAN_BIN.stat().st_size,
        "lean_bin_hash_ms": t_lean_bin_hash_ms,
        "lean_version_wall_ms": ver_stats["wall_ms"],
        "lean_print_prefix_wall_ms": pref_stats["wall_ms"],
        "foundation_modules": len(fl["modules"]),
        "foundation_files_hashed": fl_files,
        "foundation_bytes_hashed": fl_bytes,
        "foundation_hash_ms": t_fl_hash_ms,
        "library_modules": len(ll["modules"]),
        "library_files_hashed": ll_files,
        "library_bytes_hashed": ll_bytes,
        "library_hash_ms": t_ll_hash_ms,
    }
    print("Admission stats:", json.dumps(report["admission_and_locks"], indent=2))

    # 3. Stage the 17 target modules and run InspectorRequest::Headers
    audit_req_orig = json.loads((BASELINE_ARTIFACTS / "audit-request.json").read_text())
    target_src_dir = work / "target-src"
    target_modules = []
    headers_sources = []
    for m in audit_req_orig["modules"]:
        mod_name = m["module"]
        role = m["role"]
        orig_p = Path(m["source"])
        rel_from_stage = orig_p.relative_to("/tmp/anneal-verification-s9Ihja")
        src_file = BASELINE_ARTIFACTS / rel_from_stage
        dst_file = target_src_dir / f"{mod_name.replace('.', '/')}.lean"
        dst_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src_file, dst_file)
        target_modules.append({
            "module": mod_name,
            "source": str(dst_file),
            "expectedSha256": m["expectedSha256"],
            "role": role,
        })
        headers_sources.append([mod_name, str(dst_file)])

    inspector_path = work / "TrustedBoundary.lean"
    shutil.copyfile(BASELINE_ARTIFACTS / "anneal/trusted/audit/TrustedBoundary.lean", inspector_path)

    headers_req_path = work / "request-headers.json"
    headers_res_path = work / "request-headers.result.json"
    headers_req_path.write_text(json.dumps({
        "mode": "headers",
        "sysroot": str(LEAN_PREFIX),
        "foundation": sorted(fl["graph"].keys()),
        "sources": headers_sources,
    }))
    headers_stats = run_timed([
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(inspector_path), str(headers_req_path), str(headers_res_path)
    ], cwd=work, env=clean_env)
    headers_res = json.loads(headers_res_path.read_text())["result"]["headers"]
    imports_by_mod = {h["module"]: h["imports"] for h in headers_res}

    report["headers_inspection"] = {
        "wall_ms": headers_stats["wall_ms"],
        "user_s": headers_stats["user_s"],
        "sys_s": headers_stats["sys_s"],
        "max_rss_kb": headers_stats["max_rss_kb"],
    }
    print("Headers inspection stats:", json.dumps(report["headers_inspection"], indent=2))

    # 4. Topological sort of the 17 target modules
    pending = set(m["module"] for m in target_modules)
    topo_order = []
    while pending:
        ready = sorted(n for n in pending if all(e["module"] not in pending for e in imports_by_mod[n]))
        topo_order.extend(ready)
        pending -= set(ready)

    role_by_mod = {m["module"]: m["role"] for m in target_modules}
    src_by_mod = {m["module"]: Path(m["source"]) for m in target_modules}

    # Compile each module in topo_order and measure
    compile_rows = []
    target_lib_dir = work / "target-lib"
    for mod in topo_order:
        setup_path = work / f"{mod}.setup.json"
        setup_obj = {
            "name": mod,
            "isModule": False,
            "imports": imports_by_mod[mod],
            "importArts": artifacts_map,
            "dynlibs": [],
            "plugins": [],
            "options": {},
        }
        setup_path.write_text(json.dumps(setup_obj))
        out_olean = target_lib_dir / f"{mod.replace('.', '/')}.olean"
        out_olean.parent.mkdir(parents=True, exist_ok=True)
        cmd = [
            str(LEAN_BIN),
            "-j1", "-M2048", "-t0",
            "-DElab.async=false", "-Ddebug.skipKernelTC=false",
            "--setup", str(setup_path),
            "-o", str(out_olean),
            str(src_by_mod[mod]),
        ]
        c_stats = run_timed(cmd, cwd=work, env=clean_env)
        stem = out_olean.name[:-len("olean")]
        parent = out_olean.parent
        avail = {}
        part_sizes = {}
        for part in PARTS:
            art = parent / f"{stem}{part}"
            if art.exists():
                avail[part] = str(art)
                part_sizes[part] = art.stat().st_size
        artifacts_map[mod] = [
            [avail[p] for p in OLEAN_PARTS if p in avail],
            [avail[p] for p in IR_PARTS if p in avail],
        ]
        graph_map[mod] = imports_by_mod[mod]
        src_text = src_by_mod[mod].read_text()
        row = {
            "module": mod,
            "role": role_by_mod[mod],
            "imports": [e["module"] for e in imports_by_mod[mod]],
            "source_bytes": src_by_mod[mod].stat().st_size,
            "source_lines": len(src_text.splitlines()),
            "wall_ms": c_stats["wall_ms"],
            "user_s": c_stats["user_s"],
            "sys_s": c_stats["sys_s"],
            "max_rss_kb": c_stats["max_rss_kb"],
            "part_sizes": part_sizes,
            "total_artifact_bytes": sum(part_sizes.values()),
        }
        compile_rows.append(row)
        print(f"Compiled {mod:24s} ({role_by_mod[mod]:13s}): {c_stats['wall_ms']:8.1f} ms | RSS {c_stats['max_rss_kb']/1024:6.1f} MiB | olean {part_sizes.get('olean',0):8d} B")

    report["module_compilations"] = compile_rows

    # 5. Run baseline target-audit
    target_audit_req = dict(audit_req_orig)
    target_audit_req["modules"] = target_modules
    arts_arr = [[k, v] for k, v in sorted(artifacts_map.items())]
    audit_ipc_req = {
        "mode": "target-audit",
        "sysroot": str(LEAN_PREFIX),
        "artifacts": arts_arr,
        "foundation": sorted(fl["graph"].keys()),
        "libraries": sorted(ll["modules"].keys()),
        "graph": graph_map,
        "axioms": fl["axioms"],
        "target": target_audit_req,
    }
    audit_req_path = work / "request-target-audit.json"
    audit_res_path = work / "request-target-audit.result.json"
    audit_req_path.write_text(json.dumps(audit_ipc_req))

    audit_stats = run_timed([
        str(LEAN_BIN), "-j1", "-M2048", "--run",
        str(inspector_path), str(audit_req_path), str(audit_res_path)
    ], cwd=work, env=clean_env)
    report["target_audit_process"] = {
        "wall_ms": audit_stats["wall_ms"],
        "user_s": audit_stats["user_s"],
        "sys_s": audit_stats["sys_s"],
        "max_rss_kb": audit_stats["max_rss_kb"],
    }
    print("Target audit stats:", json.dumps(report["target_audit_process"], indent=2))

    # 6. Post-audit provenance hashing (target.rs lines 375-445)
    t_post0 = time.perf_counter()
    post_files = 0
    post_bytes = 0
    for m in target_modules:
        mod = m["module"]
        for grp in artifacts_map[mod]:
            for p_str in grp:
                pp = Path(p_str)
                post_bytes += pp.stat().st_size
                post_files += 1
                _ = sha256_file(pp)
    res_obj = json.loads(audit_res_path.read_text())["result"]
    seen_closure_mods = set()
    for key in ["modelClosure", "specificationClosure"]:
        for row in res_obj.get(key, []):
            mod = row["module"]
            if mod in seen_closure_mods:
                continue
            seen_closure_mods.add(mod)
            if mod not in role_by_mod:
                sp = LEAN_PREFIX / "src/lean" / f"{mod.replace('.', '/')}.lean"
                post_bytes += sp.stat().st_size
                post_files += 1
                _ = sha256_file(sp)
            for grp in artifacts_map[mod]:
                for p_str in grp:
                    pp = Path(p_str)
                    post_bytes += pp.stat().st_size
                    post_files += 1
                    _ = sha256_file(pp)
    t_post_ms = (time.perf_counter() - t_post0) * 1000.0
    report["post_audit_provenance_hashing"] = {
        "files_hashed": post_files,
        "bytes_hashed": post_bytes,
        "wall_ms": t_post_ms,
    }
    print("Post-audit provenance stats:", json.dumps(report["post_audit_provenance_hashing"], indent=2))

    (SCRATCH / "profile_results.json").write_text(json.dumps(report, indent=2))

if __name__ == "__main__":
    main()
