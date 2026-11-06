#!/usr/bin/env python3
"""C03: resend an open proof after replacing an imported Lean artifact."""
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

REFERENCE = Path(__file__).resolve().parents[2]
BASELINE = REFERENCE / "anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2/support/probe.py"
LEAN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean")
PROOF = "import Dep\n#eval selected\ntheorem checked : selected = 7 := by\n  rfl\n"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(argv, cwd, env):
    p = subprocess.run([str(x) for x in argv], cwd=cwd, env=env, text=True,
                       capture_output=True, timeout=20)
    return {"argv": [str(x) for x in argv], "rc": p.returncode,
            "stdout": p.stdout, "stderr": p.stderr}


def goal_and_diagnostics(server, name="Proof.lean"):
    reply = server.goal(name, 3, 5)
    uri = (server.root / name).as_uri()
    return {"goal": reply, "diagnostics": server.diags.get(uri)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scratch", type=Path, required=True)
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    assert scratch.is_dir() and not any(scratch.iterdir()), "private scratch must be empty"
    assert LEAN.is_file() and BASELINE.is_file()
    env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_PATH=str(scratch / "project/.lake/build/lib/lean"))
    env["PATH"] = str(LEAN.parent) + os.pathsep + env.get("PATH", "")
    # Reuse only the prior package's client class. Its module-level probe runs on
    # import, so compile selected AST nodes without executing its main routine.
    tree = ast.parse(BASELINE.read_text())
    nodes = [node for node in tree.body if
             isinstance(node, ast.FunctionDef) and node.name in ("sha", "log") or
             isinstance(node, ast.ClassDef) and node.name == "Server"]
    events = []
    context = {"json": json, "os": os, "select": select, "subprocess": subprocess,
               "time": time, "Path": Path, "START": time.monotonic(),
               "EVENTS": events, "SERVERS": [], "LEAN": LEAN,
               "LAKE": LEAN.with_name("lake"), "ENV": env, "PROOF": PROOF}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(BASELINE), "exec"), context)
    Server = context["Server"]
    source = scratch / "project"
    alt = scratch / "alt"
    source.mkdir(); alt.mkdir()
    artifacts = source / ".lake/build/lib/lean"
    artifacts.mkdir(parents=True)
    (source / "Dep.lean").write_text("def selected : Nat := 7\n")
    (alt / "Dep.lean").write_text("def selected : Nat := 9\n")
    (source / "Proof.lean").write_text(PROOF)
    builds = [command([LEAN, "-o", artifacts / "Dep.olean", "Dep.lean"], source, env),
              command([LEAN, "-o", alt / "Dep.olean", "Dep.lean"], alt, env)]
    assert all(x["rc"] == 0 for x in builds), builds
    hash7, hash9 = sha(artifacts / "Dep.olean"), sha(alt / "Dep.olean")
    assert hash7 != hash9
    server = Server("existing", source, "direct")
    observations = {}
    try:
        observations["initial_wait"] = server.open("Proof.lean", PROOF, 1)
        observations["initial"] = goal_and_diagnostics(server)
        shutil.copy2(alt / "Dep.olean", artifacts / "Dep.olean")
        (source / "Dep.lean").write_text("def selected : Nat := 9\n")
        assert sha(artifacts / "Dep.olean") == hash9
        server.watched("Dep.lean")
        server.watched("artifacts/Dep.olean")
        observations["after_watched"] = goal_and_diagnostics(server)
        observations["same_text_v2_wait"] = server.edit("Proof.lean", PROOF, 2)
        observations["same_text_v2"] = goal_and_diagnostics(server)
        changed = PROOF + "\n"
        observations["whitespace_v3_wait"] = server.edit("Proof.lean", changed, 3)
        observations["whitespace_v3"] = goal_and_diagnostics(server)
        server.close("Proof.lean")
        observations["reopened_wait"] = server.open("Proof.lean", changed, 1)
        observations["reopened"] = goal_and_diagnostics(server)
    finally:
        server.stop()
    fresh = Server("fresh", source, "direct")
    try:
        observations["fresh_wait"] = fresh.open("Proof.lean", PROOF + "\n", 1)
        observations["fresh"] = goal_and_diagnostics(fresh)
    finally:
        fresh.stop()
    batch = command([LEAN, "--json", "Proof.lean"], source, env)
    result = {"lean_sha256": sha(LEAN), "baseline_probe_sha256": sha(BASELINE),
              "source7_sha256": hashlib.sha256(b"def selected : Nat := 7\n").hexdigest(),
              "source9_sha256": hashlib.sha256(b"def selected : Nat := 9\n").hexdigest(),
              "artifact7_sha256": hash7, "artifact9_sha256": hash9,
              "proof_sha256": hashlib.sha256(PROOF.encode()).hexdigest(),
              "builds": builds, "observations": observations, "batch": batch,
              "transcript": events}
    raw = json.dumps(result, indent=2, ensure_ascii=False)
    raw = raw.replace(str(scratch), "<SCRATCH>")
    (Path(__file__).parent / "results.json").write_text(raw + "\n")
    print("C03 probe complete", {k: (v.get("goal", {}).get("result") if isinstance(v, dict) else None)
                                  for k, v in observations.items() if not k.endswith("wait")})


if __name__ == "__main__":
    main()
