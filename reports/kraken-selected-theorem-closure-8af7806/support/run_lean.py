"""Recheck the owned probes against an already built pinned Kraken library.

Does not download, build Kraken, change Git state, or install a toolchain.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean", required=True)
    parser.add_argument("--kraken-lib", required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    env = os.environ.copy()
    env["LEAN_PATH"] = str(Path(args.kraken_lib).resolve())
    names = ["X64Closure", "AArch64Closure", "NativeAxiom", "AArch64Add", "EffectsProbe", "PermissionInterpretation", "MissingState"]
    version = subprocess.run([args.lean, "--version"], text=True, capture_output=True, check=True).stdout.strip()
    records = []
    for name in names:
        path = here / (name + ".lean")
        result = subprocess.run([args.lean, str(path)], cwd=here, env=env, text=True, capture_output=True, timeout=45)
        log = result.stdout + result.stderr
        (here / (name + ".log")).write_text(log)
        expected = 1 if name == "MissingState" else 0
        records.append({"probe": name, "command": [args.lean, str(path)], "source_sha256": hashlib.sha256(path.read_bytes()).hexdigest(), "exit_code": result.returncode, "expected_exit": expected, "log": name + ".log"})
        if result.returncode != expected or "panic" in log.lower() or "assertion failed" in log.lower():
            raise RuntimeError("unexpected result; inspect " + name + ".log before continuing")
    (here / "results.json").write_text(json.dumps({"lean": version, "lean_path": env["LEAN_PATH"], "probes": records}, indent=2) + "\n")
    print(json.dumps({"lean": version, "probes": len(records), "expected_statuses": True}, indent=2))


if __name__ == "__main__":
    main()
