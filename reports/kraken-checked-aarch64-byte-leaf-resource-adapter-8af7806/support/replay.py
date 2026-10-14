"""Replay with existing tools only. Builds/runs only the owned safe leaf harness.

Usage: python3 support/replay.py --kraken-lib EXISTING_KRAKEN_OLEAN_ROOT
Optionally pass --lean /path/to/lean --rustc /path/to/rustc.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

from binding import bind_all


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--kraken-lib", required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--rustc", default="rustc")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    if root != Path.cwd().resolve():
        raise SystemExit("Run from the package root")
    for name in ("support", "logs", "artifacts"):
        path = root / name
        if path.is_symlink():
            raise SystemExit("Refusing symlinked output directory")
        path.mkdir(exist_ok=True)
    kraken = Path(args.kraken_lib).resolve(strict=True)
    lean = Path(shutil.which(args.lean) or args.lean).resolve(strict=True)
    # Preserve argv[0]: rustup's rustc symlink dispatches by its invocation name.
    rustc = Path(shutil.which(args.rustc) or args.rustc).absolute()
    rustc.resolve(strict=True)
    env = dict(os.environ, LEAN_PATH=str(kraken) + os.pathsep + str(root / "support"))
    rows = []

    def run(tool, argv, label, native=False):
        actual = {"lean": str(lean), "rustc": str(rustc)}.get(tool, tool)
        started = time.monotonic()
        completed = subprocess.run([actual] + argv, cwd=root, env=env, capture_output=True, text=True)
        stdout, stderr = completed.stdout, completed.stderr
        log = f"logs/{label}.log"
        (root / log).write_text(stdout + stderr)
        row = dict(tool=tool, argv=argv, cwd=".", exit=completed.returncode, log=log,
                   native_execution=native, elapsed_seconds=time.monotonic()-started,
                   output_sha256=hashlib.sha256((stdout + stderr).encode()).hexdigest())
        rows.append(row)
        (root / "logs/replay-commands.json").write_text(json.dumps(rows, indent=2) + "\n")
        if completed.returncode or re.search(r"(?i)panic|assertion failed", stdout + stderr):
            raise SystemExit("Stopped affected path for diagnosis: " + json.dumps(row))
        return stdout

    lean_version = run("lean", ["--version"], "lean-version")
    rustc_version = run("rustc", ["-vV"], "rustc-version")
    private = dict(lean_real_path=str(lean), rustc_invocation_path=str(rustc), rustc_proxy_real_path=str(rustc.resolve()), kraken_olean_root=str(kraken),
                   lean_sha256=hashlib.sha256(lean.read_bytes()).hexdigest(),
                   rustc_sha256=hashlib.sha256(rustc.read_bytes()).hexdigest())
    (root / "logs/tool-identity-private.json").write_text(json.dumps(private, indent=2) + "\n")
    proof = run("lean", ["-o", "support/Adapter.olean", "support/Adapter.lean"], "adapter-proof")
    for opt in (0, 3):
        for kind, suffix in (("obj", ".o"), ("link", ""), ("asm", ".s")):
            run("rustc", ["--edition=2024", "-C", f"opt-level={opt}", "-C", "panic=abort", "-C", "strip=debuginfo",
                          f"--emit={kind}", "support/leaf.rs", "-o", f"artifacts/leaf-O{opt}{suffix}"],
                f"rust-O{opt}-{kind}")
    binding = bind_all(root)
    binding_proof = run("lean", ["support/BindingCertificates.lean"], "binding-proof")
    closures = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", proof + binding_proof)
    if len(closures) != 40:
        raise SystemExit(f"Expected40 audited declarations, got {len(closures)}")
    for name, assumptions in closures:
        axioms = set(x.strip() for x in assumptions.split(",") if x.strip())
        if not axioms <= {"propext", "Classical.choice", "Quot.sound"}:
            raise SystemExit("Unexpected axiom dependency: " + name + ":" + assumptions)
    native_rows = []
    for opt in (0, 3):
        output = run(f"./artifacts/leaf-O{opt}", [], f"native-O{opt}", native=True)
        result = json.loads(output)
        if result != dict(cases=16640, checksum="9369878136d25c80", valid_reference_only=True):
            raise SystemExit("Native result disagrees with preserved corpus")
        native_rows.append(dict(optimization=opt, **result))
    result = dict(status="pass", lean_version=lean_version.strip(), rustc_version=rustc_version.strip(),
                  kernel_checked_declarations=len(closures), admitted_instruction_family_offsets=4096,
                  accepted_leaf_bytes="00004039c0035fd6", compiled_slices=len(binding["artifacts"]),
                  single_byte_mutants_rejected=binding["single_byte_mutants_rejected"], native=native_rows,
                  no_installs_or_upstream_builds=True, no_invalid_or_mutated_native_execution=True,
                  remaining_arrows=["Arm formal-reference relation", "verified Mach-O importer/loader",
                                    "Rust/MiniRust reference/provenance/alias adequacy", "compiler/caller adequacy"])
    (root / "logs/replay-results.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
