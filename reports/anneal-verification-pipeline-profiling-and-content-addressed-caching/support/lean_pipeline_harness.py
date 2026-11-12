#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exact Python harness mirroring cargo-anneal's Checker and TargetAudit IPC protocol.

Implements:
- Foundation and Library lock loading (foundation-lock.json, library-lock.json)
- InspectorRequest::Headers via TrustedBoundary.lean
- <module>.setup.json generation and lean --setup compilation
- InspectorRequest::TargetAudit via TrustedBoundary.lean
"""

import hashlib
import json
import os
import resource
import shutil
import subprocess
import time
from pathlib import Path

TRACK2_DIR = Path("/tmp/ref_research_stack221_perf/track2")
MVP_SRC = Path("/tmp/ref_research_stack221_perf/mvp_src")
FIXTURES = Path("/tmp/ref_research_stack221_perf/fixtures")
STARNIX_BASELINE = Path("/tmp/anneal-mvp-starnix-installed-final/baseline-artifacts")

CLI = MVP_SRC / "target/release/cargo-anneal"
CAPTURE = MVP_SRC / "target/release/anneal-rustc-capture"
LEAN = Path("/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
LEAN_PREFIX = LEAN.parent.parent.resolve()
SYSROOT = Path("/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu")

FOUNDATION_LOCK = MVP_SRC / "trusted/lean/foundation-lock.json"
LIBRARY_LOCK = MVP_SRC / "trusted/audit/library-lock.json"
TRUSTED_BOUNDARY = MVP_SRC / "trusted/audit/TrustedBoundary.lean"

OLEAN_PARTS = ["olean", "olean.server", "olean.private"]
IR_PARTS = ["ir.sig", "ir"]
PARTS = ["olean", "olean.server", "olean.private", "ir.sig", "ir"]

BUNDLED_MODULES = [
    ("Trusted.Mvp.Syntax", "anneal/trusted/lean/Trusted/Mvp/Syntax.lean", "model"),
    ("Trusted.Mvp.Semantics", "anneal/trusted/lean/Trusted/Mvp/Semantics.lean", "model"),
    ("Trusted.Mvp", "anneal/trusted/lean/Trusted/Mvp.lean", "model"),
    ("Trusted", "anneal/trusted/lean/Trusted.lean", "model"),
    ("Anneal.Mvp.Execution", "anneal/theory/Anneal/Mvp/Execution.lean", "proof"),
    ("Anneal.Mvp.Canaries", "anneal/theory/Anneal/Mvp/Canaries.lean", "proof"),
    ("Anneal", "anneal/theory/Anneal.lean", "proof"),
]

REACHABLE_BUNDLED = {
    "Trusted.Mvp.Syntax",
    "Trusted.Mvp.Semantics",
    "Trusted.Mvp",
    "Anneal.Mvp.Execution",
}


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def run_timed(cmd: list[str], cwd: Path) -> dict:
    env = {
        "HOME": os.environ.get("HOME", "/tmp"),
        "TMPDIR": os.environ.get("TMPDIR", "/tmp"),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
    }
    ru_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.perf_counter()
    proc = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    t1 = time.perf_counter()
    ru_after = resource.getrusage(resource.RUSAGE_CHILDREN)

    wall_s = t1 - t0
    user_s = ru_after.ru_utime - ru_before.ru_utime
    sys_s = ru_after.ru_stime - ru_before.ru_stime
    return {
        "returncode": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "wall_s": wall_s,
        "user_s": user_s,
        "sys_s": sys_s,
        "cpu_s": user_s + sys_s,
    }


def collect_module_artifacts(base_dir: Path, mod_name: str) -> list[list[str]]:
    rel_mod = mod_name.replace(".", "/")
    olean_group = []
    for part in OLEAN_PARTS:
        p = base_dir / f"{rel_mod}.{part}"
        if p.is_file():
            olean_group.append(str(p))
    if not olean_group:
        raise FileNotFoundError(f"Missing .olean for {mod_name} in {base_dir}")
    ir_group = []
    for part in IR_PARTS:
        p = base_dir / f"{rel_mod}.{part}"
        if p.is_file():
            ir_group.append(str(p))
    return [olean_group, ir_group]


def load_admitted_base() -> dict:
    flock = json.loads(FOUNDATION_LOCK.read_text())
    llock = json.loads(LIBRARY_LOCK.read_text())
    sysroot_lib = LEAN_PREFIX / "lib/lean"

    foundation = sorted(flock["graph"].keys())
    artifacts = {}
    graph = {}
    for mod_name in foundation:
        artifacts[mod_name] = collect_module_artifacts(sysroot_lib, mod_name)
        graph[mod_name] = flock["graph"][mod_name]

    return {
        "prefix": str(LEAN_PREFIX),
        "foundation": foundation,
        "axioms": flock["axioms"],
        "artifacts": artifacts,
        "graph": graph,
        "library_lock": llock,
        "library_modules": set(),
    }


def admit_reachable_libraries(state: dict, root_modules: list[str]) -> None:
    llock = state["library_lock"]
    sysroot_lib = LEAN_PREFIX / "lib/lean"
    queue = list(root_modules)
    while queue:
        mod_name = queue.pop()
        if mod_name in state["graph"]:
            continue
        if mod_name not in llock["modules"]:
            continue
        state["artifacts"][mod_name] = collect_module_artifacts(sysroot_lib, mod_name)
        edges = llock["graph"][mod_name]
        state["graph"][mod_name] = edges
        state["library_modules"].add(mod_name)
        for edge in edges:
            queue.append(edge["module"])


def inspect_headers(stage_dir: Path, state: dict, sources: list[tuple[str, Path]]) -> tuple[dict, dict[str, list[dict]]]:
    if not sources:
        return {"wall_s": 0.0, "user_s": 0.0, "sys_s": 0.0, "cpu_s": 0.0}, {}
    req_path = stage_dir / "request-headers.json"
    res_path = stage_dir / "result-headers.json"
    req_obj = {
        "mode": "headers",
        "sysroot": state["prefix"],
        "foundation": state["foundation"],
        "sources": [[m, str(p)] for m, p in sources],
    }
    req_path.write_text(json.dumps(req_obj))
    cmd = [
        str(LEAN),
        "-j1",
        "-M2048",
        "--run",
        str(TRUSTED_BOUNDARY),
        str(req_path),
        str(res_path),
    ]
    timing = run_timed(cmd, cwd=stage_dir)
    if timing["returncode"] != 0:
        raise RuntimeError(f"Headers failed: {timing['stderr']}\n{timing['stdout']}")
    resp = json.loads(res_path.read_text())
    if not resp.get("ok"):
        raise RuntimeError(f"Headers error response: {resp}")
    imports_map = {}
    for h in resp["result"]["headers"]:
        imports_map[h["module"]] = h["imports"]
    return timing, imports_map


def topo_sort_modules(pending_set: set[str], imports_map: dict[str, list[dict]]) -> list[list[str]]:
    """Returns topological waves (each wave is a sorted list of independent modules)."""
    pending = set(pending_set)
    waves = []
    while pending:
        ready = sorted(
            m for m in pending if all(edge["module"] not in pending for edge in imports_map[m])
        )
        if not ready:
            raise RuntimeError(f"Cycle detected in {pending}")
        waves.append(ready)
        for m in ready:
            pending.remove(m)
    return waves


def write_setup_and_compile(
    stage_dir: Path,
    lib_dir: Path,
    state: dict,
    mod_name: str,
    src_path: Path,
    imports: list[dict],
    allow_async: bool = False,
    threads: int = 1,
) -> tuple[dict, list[list[str]]]:
    setup_path = stage_dir / f"{mod_name}.setup.json"
    setup_obj = {
        "name": mod_name,
        "isModule": False,
        "imports": imports,
        "importArts": state["artifacts"],
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
    timing = run_timed(cmd, cwd=stage_dir)
    if timing["returncode"] != 0:
        raise RuntimeError(
            f"Compile failed for {mod_name} (rc={timing['returncode']}): {timing['stderr']}\n{timing['stdout']}"
        )
    mod_arts = collect_module_artifacts(lib_dir, mod_name)
    return timing, mod_arts


def run_target_audit(stage_dir: Path, state: dict, target_request: dict) -> tuple[dict, dict]:
    req_path = stage_dir / "request-target-audit.json"
    res_path = stage_dir / "result-target-audit.json"
    arts_arr = [[k, v] for k, v in sorted(state["artifacts"].items())]
    libraries = sorted(state["library_modules"])
    req_obj = {
        "mode": "target-audit",
        "sysroot": state["prefix"],
        "artifacts": arts_arr,
        "foundation": state["foundation"],
        "libraries": libraries,
        "graph": state["graph"],
        "axioms": state["axioms"],
        "target": target_request,
    }
    req_path.write_text(json.dumps(req_obj))
    cmd = [
        str(LEAN),
        "-j1",
        "-M2048",
        "--run",
        str(TRUSTED_BOUNDARY),
        str(req_path),
        str(res_path),
    ]
    timing = run_timed(cmd, cwd=stage_dir)
    if timing["returncode"] != 0:
        err_detail = res_path.read_text() if res_path.exists() else timing["stderr"]
        raise RuntimeError(f"TargetAudit failed (rc={timing['returncode']}): {err_detail}")
    resp = json.loads(res_path.read_text())
    if not resp.get("ok"):
        raise RuntimeError(f"TargetAudit error: {resp}")
    return timing, resp["result"]


def ensure_baseline_artifacts(fixture_name: str) -> Path:
    if fixture_name == "starnix" and (STARNIX_BASELINE / "audit-request.json").exists():
        dst = TRACK2_DIR / "work_baselines" / "starnix"
        if not (dst / "audit-request.json").exists():
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copytree(STARNIX_BASELINE, dst, dirs_exist_ok=True)
        return dst

    dst = TRACK2_DIR / "work_baselines" / fixture_name
    if (dst / "audit-request.json").exists():
        return dst

    if dst.exists():
        shutil.rmtree(dst)
    dst.parent.mkdir(parents=True, exist_ok=True)

    req_path = FIXTURES / fixture_name / "request.json"
    cmd = [
        str(CLI),
        "anneal",
        "verify",
        "--request",
        str(req_path),
        "--capture",
        str(CAPTURE),
        "--lean",
        str(LEAN),
        "--sysroot",
        str(SYSROOT),
        "--artifacts",
        str(dst),
    ]
    env = os.environ.copy()
    proc = subprocess.run(cmd, cwd=TRACK2_DIR, env=env, capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f"Failed to capture baseline {fixture_name}: {proc.stderr}\n{proc.stdout}")
    return dst


def resolve_local_source_path(work_dir: Path, mod_entry: dict) -> Path:
    """Maps audit-request.json's temporary /tmp/anneal-verification-XXXX/... path to work_dir."""
    orig = mod_entry["source"]
    # Everything after /tmp/anneal-verification-XXXXXX/ is the relative path in work_dir
    parts = Path(orig).parts
    for idx, p in enumerate(parts):
        if p.startswith("anneal-verification-"):
            rel = Path(*parts[idx + 1 :])
            return work_dir / rel
    raise ValueError(f"Cannot resolve relative path from {orig}")
