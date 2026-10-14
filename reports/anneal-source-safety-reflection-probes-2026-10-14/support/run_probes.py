"""Run owned, bounded probes; never execute the Rust function containing UB."""
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent

def capture(name, argv):
    result = subprocess.run(argv, cwd=HERE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=60)
    (HERE / (name + ".stdout.txt")).write_bytes(result.stdout)
    (HERE / (name + ".stderr.txt")).write_bytes(result.stderr)
    return {"name": name, "argv": argv, "returncode": result.returncode,
            "stdout_file": name + ".stdout.txt", "stderr_file": name + ".stderr.txt"}

commands = [
    ("lean-version", ["lean", "--version"]),
    ("rust-version", ["rustc", "-vV"]),
    ("lean-check", ["lean", "-DwarningAsError=true", "Reflection.lean"]),
]
for level in (0, 3):
    for output in ("asm", "llvm-ir"):
        suffix = "s" if output == "asm" else "ll"
        commands.append((f"rust-o{level}-{suffix}", [
            "rustc", "--edition=2024", "--crate-type=lib", "erased_ub.rs",
            "--emit=" + output, "-C", "opt-level=" + str(level),
            "-C", "debug-assertions=no", "-o", f"erased-ub-o{level}.{suffix}"]))

results = []
for name, argv in commands:
    entry = capture(name, argv)
    results.append(entry)
    if entry["returncode"] != 0:
        (HERE / "results.json").write_text(json.dumps({"commands": results}, indent=2) + "\n")
        raise SystemExit(f"Probe failed: {name}; inspect retained streams")

hashes = {}
for path in sorted(HERE.iterdir()):
    if path.is_file() and path.name != "results.json":
        hashes[path.name] = hashlib.sha256(path.read_bytes()).hexdigest()
(HERE / "results.json").write_text(json.dumps({"commands": results, "sha256": hashes}, indent=2) + "\n")
print(json.dumps({"successful_commands": len(results), "rust_executed": False,
                  "lean_axiom_audit": (HERE / "lean-check.stdout.txt").read_text()}))
