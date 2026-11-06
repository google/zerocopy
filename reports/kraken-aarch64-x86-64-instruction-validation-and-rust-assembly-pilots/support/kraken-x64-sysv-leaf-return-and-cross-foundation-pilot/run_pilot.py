"""Check the owned X64 and preserved AArch64 peer proofs and s2n bytes.

Requires an already built Kraken library; installs/builds/downloads nothing.
The x86 ELF code is parsed only and never executed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", required=True)
    parser.add_argument("--kraken-lib", required=True)
    parser.add_argument("--s2n-support", type=Path)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    env = os.environ.copy()
    env["LEAN_PATH"] = str(Path(args.kraken_lib).resolve())
    version = subprocess.run([args.lean, "--version"], text=True, capture_output=True, check=True).stdout.strip()
    results = []
    for name, expected in [("X64Pilot", 18), ("AArch64Peer", 2)]:
        source = here / (name + ".lean")
        command = [args.lean, source.name]
        start = time.perf_counter()
        proc = subprocess.run(command, cwd=here, env=env, text=True, capture_output=True, timeout=45)
        elapsed = time.perf_counter() - start
        output = proc.stdout + proc.stderr
        source.with_suffix(".log").write_text(output)
        closure_lines = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        accepted_axioms = {"propext", "Classical.choice", "Quot.sound"}
        empty_closures = re.findall(r"'([^']+)' does not depend on any axioms", output)
        empty_ok = len(empty_closures) == (1 if name == "X64Pilot" else 0)
        closure_ok = empty_ok and len(closure_lines) == expected and all(set(a.strip() for a in ax.split(",")) == accepted_axioms for _, ax in closure_lines)
        if proc.returncode != 0 or not closure_ok or any(t in output.lower() for t in ["sorryax", "panic", "assertion failed", "error pretty printing"]):
            raise RuntimeError("unexpected proof status or closure; inspect " + name + ".log")
        results.append({"probe": name, "command": ["lean", source.name], "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(), "exit_code": proc.returncode, "wall_seconds_one_sample": elapsed, "checked_declarations_with_foundational_trio": expected, "checked_declarations_without_axioms": len(empty_closures), "axioms_exactly": sorted(accepted_axioms), "log": source.with_suffix(".log").name})
    companion = args.s2n_support or (here.parent.parent / "jasmin-vale-s2n-artifact-and-access-boundaries/support")
    command = [sys.executable, "object_binding.py"]
    proc = subprocess.run(command, cwd=companion, text=True, capture_output=True, timeout=15)
    (here / "s2n/object_binding.json").write_text(proc.stdout)
    (here / "s2n/object_binding.log").write_text(proc.stderr)
    if proc.returncode:
        raise RuntimeError("s2n object comparison failed; inspect its log")
    object_result = json.loads(proc.stdout)
    if not object_result["matches_pinned_proof_literal"] or not all(v["rejected"] for v in object_result["negative_controls"].values()):
        raise RuntimeError("s2n object comparison/control mismatch")
    results.append({"probe": "s2n-object-binding", "command": ["python3", "object_binding.py"], "cwd": "public companion support", "exit_code": 0, "symbol_bytes": object_result["symbol_size"], "symbol_sha256": object_result["symbol_sha256"], "scope": "byte check only, reused assembled object, no HOL replay"})
    output = {"lean": version, "lean_path": "caller-selected KRAKEN_LIB for pinned source", "scope": "one-sample fresh Lean elaboration/checking/import time; not comparable native performance or HOL timing", "results": results}
    (here / "results.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"proof_declarations": 21, "expected_statuses_and_closures": True, "s2n_symbol_bytes": object_result["symbol_size"]}, indent=2))


if __name__ == "__main__":
    main()
