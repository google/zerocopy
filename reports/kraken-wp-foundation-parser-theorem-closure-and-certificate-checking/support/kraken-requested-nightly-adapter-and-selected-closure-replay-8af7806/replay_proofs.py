"""Replay copied selected proof sources against the fresh requested-nightly library."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parent.parent
toolroot = Path(sys.argv[1]).resolve(strict=True)
lean = toolroot / "bin/lean"
env = dict(os.environ, LEAN_PATH=str(root / "kraken-source/.lake/build/lib/lean") + os.pathsep + str(root / "support"),
           LEAN_SYSROOT=str(toolroot), LEAN_NUM_THREADS="2")
rows = []
for name in ("Adapter", "BindingCertificates", "AArch64Closure", "X64Closure", "AArch64Pilot", "X64Pilot"):
    argv = ["-o", f"support/{name}.olean", f"support/{name}.lean"]
    started = time.monotonic()
    result = subprocess.run([str(lean)] + argv, cwd=root, env=env, capture_output=True, text=True)
    output = result.stdout + result.stderr
    log = "logs/proof-" + name + ".log"
    (root / log).write_text(output)
    closures = []
    for declaration, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S):
        closures.append(dict(declaration=declaration, axioms=[a.strip() for a in axioms.split(",") if a.strip()]))
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", output)
    closures.extend(dict(declaration=name, axioms=[]) for name in no_axioms)
    row = dict(tool="requested-nightly lean", argv=argv, cwd=".", exit=result.returncode,
               log=log, elapsed_seconds=time.monotonic()-started, closures=closures,
               output_sha256=hashlib.sha256(output.encode()).hexdigest())
    rows.append(row)
    (root / "proof-results.json").write_text(json.dumps(rows, indent=2)+"\n")
    print(json.dumps(row), flush=True)
    if result.returncode or re.search(r"(?i)panic|assertion failed", output):
        raise SystemExit("Stopped affected path for diagnosis")
    if name not in {"AArch64Closure", "X64Closure"}:
        extra = [(c["declaration"], a) for c in closures for a in c["axioms"]
                 if a not in {"propext", "Classical.choice", "Quot.sound"}]
        if extra:
            raise SystemExit("Unexpected axiom dependency in owned proof: " + str(extra))
print(json.dumps(dict(status="pass", proof_commands=len(rows), audited_declarations=sum(len(r["closures"]) for r in rows))), flush=True)
