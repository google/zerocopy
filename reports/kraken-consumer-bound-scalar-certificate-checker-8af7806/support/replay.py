"""Replay only the pure Lean dependency/checker proofs, serially, with existing tools.

No certificate file IO or compiled consumer is proved by this helper.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--lean", default="lean")
parser.add_argument("--kraken-lib", required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
if Path.cwd().resolve() != root:
    raise SystemExit("Run from package root")
lean = Path(shutil.which(args.lean) or args.lean).resolve(strict=True)
library = Path(args.kraken_lib).resolve(strict=True)
for name in ("logs", "support"):
    if (root / name).is_symlink():
        raise SystemExit("Symlinked output directory")
    (root / name).mkdir(exist_ok=True)
env = dict(os.environ, LEAN_PATH=str(library)+os.pathsep+str(root/"support"), LEAN_NUM_THREADS="1")
commands, groups = [], []
for name in ("version", "Adapter", "Consumer"):
    argv = ["--version"] if name == "version" else ["-o", f"support/{name}.olean", f"support/{name}.lean"]
    started = time.monotonic()
    result = subprocess.run([str(lean)]+argv, cwd=root, env=env, capture_output=True, text=True)
    output = result.stdout+result.stderr
    logfile = f"logs/{name}.log"
    (root/logfile).write_text(output)
    commands.append(dict(tool="Lean4.34.1", argv=argv, cwd=".", exit=result.returncode,
                         lean_threads=1, elapsed_seconds=time.monotonic()-started, log=logfile,
                         output_sha256=hashlib.sha256(output.encode()).hexdigest()))
    (root/"logs/replay-commands.json").write_text(json.dumps(commands,indent=2)+"\n")
    if result.returncode or re.search(r"(?i)panic|assertion failed",output):
        raise SystemExit("Stopped affected path for diagnosis")
    if name != "version":
        entries=[dict(declaration=d,axioms=[a.strip() for a in aa.split(",") if a.strip()])
                 for d,aa in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",output,re.S)]
        entries += [dict(declaration=d,axioms=[]) for d in re.findall(r"'([^']+)' does not depend on any axioms",output)]
        expected=32 if name=="Adapter" else 37
        if len(entries)!=expected:
            raise SystemExit(f"Closure count for{name}: expected{expected}, got{len(entries)}")
        for row in entries:
            if not set(row["axioms"]) <= {"propext","Classical.choice","Quot.sound"}:
                raise SystemExit("Unexpected axiom: "+json.dumps(row))
        groups.append(dict(subject=name,checked_declarations=len(entries),closures=entries))
result=dict(status="pass",pure_kernel_reduction_instances="concrete_accept plus14 named identity/grammar/policy rejections",
            consumer_declarations=37,adapter_dependency_declarations=32,serial_commands=len(commands),
            all_inputs_theorems=["parse_iff","check_binding","consumer_sound","accepted_sound","closed_grammar"],
            groups=groups,no_compiled_consumer_execution=True,no_native_Rust_execution=True,
            no_install_or_upstream_build=True,remaining_arrows=["compiled consumer correspondence","filesystem/loader",
            "formal Arm reference relation","actual Rust/MiniRust allocation/provenance/borrows/context"])
(root/"logs/replay-results.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(dict(status=result["status"],consumer_declarations=37,adapter_dependency_declarations=32,
                     serial_commands=len(commands),no_extra_axioms=True)))
