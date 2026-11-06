#!/usr/bin/env python3
"""F15: compare direct-final and staged-then-moved Lake project artifacts."""
import argparse
import ast
import hashlib
import json
import os
import select
import shutil
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASELINE = HERE.parents[1] / "anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2/support/probe.py"
BIN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin")
LEAN, LAKE = BIN / "lean", BIN / "lake"
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
PROOF = "import Dep\n#eval selected\ntheorem checked : selected = 7 := by\n  rfl\n#print axioms checked\n"
SOURCES = {
    "lakefile.lean": "import Lake\nopen Lake DSL\npackage reloc_probe\n@[default_target]\nlean_lib Dep\n",
    "lean-toolchain": TOOLCHAIN + "\n",
    "Dep.lean": "def selected : Nat := 7\n",
    "Proof.lean": PROOF,
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def cmd(argv, cwd, env, timeout=30):
    started = time.monotonic()
    try:
        p = subprocess.run([str(a) for a in argv], cwd=cwd, env=env,
                           capture_output=True, text=True, timeout=timeout)
        return {"argv": [str(a) for a in argv], "cwd": str(cwd), "rc": p.returncode,
                "stdout": p.stdout, "stderr": p.stderr,
                "elapsed_ms": round((time.monotonic()-started)*1000, 1)}
    except subprocess.TimeoutExpired as exc:
        return {"argv": [str(a) for a in argv], "cwd": str(cwd), "timeout_s": timeout,
                "stdout": (exc.stdout or b"").decode(errors="replace") if isinstance(exc.stdout, bytes) else exc.stdout,
                "stderr": (exc.stderr or b"").decode(errors="replace") if isinstance(exc.stderr, bytes) else exc.stderr}


def fixture(root):
    root.mkdir()
    for name, content in SOURCES.items():
        (root / name).write_text(content)


def inventory(root, markers):
    rows = []
    for path in sorted((root / ".lake").rglob("*")):
        if not path.is_file():
            continue
        data = path.read_bytes()
        hits = {name: data.count(value.encode()) for name, value in markers.items()}
        rows.append({"path": str(path.relative_to(root)), "bytes": len(data),
                     "sha256": hashlib.sha256(data).hexdigest(),
                     "path_occurrences": {k: v for k, v in hits.items() if v}})
    return rows


def server_client(events, env):
    # The baseline module has an unguarded experiment at module scope. Compile
    # only its LSP client class and two helper functions; never import it.
    tree = ast.parse(BASELINE.read_text())
    nodes = [n for n in tree.body if
             (isinstance(n, ast.FunctionDef) and n.name in ("sha", "log")) or
             (isinstance(n, ast.ClassDef) and n.name == "Server")]
    scope = {"json": json, "os": os, "select": select, "subprocess": subprocess,
             "time": time, "Path": Path, "START": time.monotonic(),
             "EVENTS": events, "SERVERS": [], "LEAN": LEAN, "LAKE": LAKE,
             "ENV": env, "PROOF": PROOF}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(BASELINE), "exec"), scope)
    return scope["Server"]


def oracle(label, root, env, Server):
    setup = cmd([LAKE, "--keep-toolchain", "--no-cache", "setup-file", "Proof.lean"], root, env)
    if setup.get("rc") != 0:
        return {"setup": setup, "server_error": "setup-file failed"}
    server = Server(label, root, "lake-serve")
    try:
        wait = server.open("Proof.lean", PROOF, 1)
        goal = server.goal("Proof.lean", 3, 5)
        diagnostics = server.diags.get((root / "Proof.lean").as_uri())
        server_result = {"wait": wait, "goal": goal, "diagnostics": diagnostics}
    finally:
        server.stop()
    batch = cmd([LAKE, "--keep-toolchain", "--no-cache", "env", LEAN,
                 "--json", "Proof.lean"], root, env)
    return {"setup": setup, "server": server_result, "batch": batch}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scratch", type=Path, required=True)
    args = ap.parse_args()
    scratch = args.scratch.resolve()
    assert scratch.is_dir() and not any(scratch.iterdir())
    assert all(p.is_file() for p in (LEAN, LAKE, BASELINE))
    assert shutil.disk_usage(scratch).free > 10 * 1024**3
    env = dict(os.environ, ELAN_TOOLCHAIN=TOOLCHAIN, LEAN_NUM_THREADS="1",
               LAKE_JOBS="1", LAKE_CACHE_DIR="", LAKE_ARTIFACT_CACHE="false",
               MATHLIB_NO_CACHE_ON_UPDATE="1")
    env["PATH"] = str(BIN) + os.pathsep + env.get("PATH", "")
    events = []
    Server = server_client(events, env)
    final, stage, archive = [scratch / n for n in ("final", "stage", "archived-direct")]
    markers = {"final": str(final), "stage": str(stage)}
    fixture(final)
    direct_build = cmd([LAKE, "--keep-toolchain", "--no-cache", "build", "Dep"], final, env)
    assert direct_build.get("rc") == 0, direct_build
    direct_before = inventory(final, markers)
    direct_oracle = oracle("direct-final", final, env, Server)
    direct_no_build = cmd([LAKE, "--keep-toolchain", "--no-cache", "--no-build", "build", "Dep"], final, env)
    direct_after = inventory(final, markers)
    final.rename(archive)
    fixture(stage)
    stage_build = cmd([LAKE, "--keep-toolchain", "--no-cache", "build", "Dep"], stage, env)
    assert stage_build.get("rc") == 0, stage_build
    stage_before = inventory(stage, markers)
    stage.rename(final)
    moved_before = inventory(final, markers)
    moved_oracle = oracle("stage-moved-final", final, env, Server)
    moved_no_build = cmd([LAKE, "--keep-toolchain", "--no-cache", "--no-build", "build", "Dep"], final, env)
    moved_after = inventory(final, markers)
    result = {"subject": {"lean_sha256": sha(LEAN), "lake_sha256": sha(LAKE),
                          "baseline_probe_sha256": sha(BASELINE),
                          "sources_sha256": {k: hashlib.sha256(v.encode()).hexdigest() for k, v in SOURCES.items()},
                          "toolchain": TOOLCHAIN, "network": "sandbox-exec deny network*",
                          "jobs": 1},
              "direct": {"build": direct_build, "before_oracle": direct_before,
                         "oracle": direct_oracle, "no_build_check": direct_no_build,
                         "after_oracle": direct_after},
              "staged_moved": {"build": stage_build, "at_stage": stage_before,
                               "at_final_before_oracle": moved_before,
                               "oracle": moved_oracle, "no_build_check": moved_no_build,
                               "after_oracle": moved_after},
              "transcript": events}
    raw = json.dumps(result, indent=2, ensure_ascii=False)
    raw = raw.replace(str(scratch), "<SCRATCH>")
    (HERE / "results.json").write_text(raw + "\n")
    print("F15 direct/staged-moved experiment complete")


if __name__ == "__main__":
    main()
