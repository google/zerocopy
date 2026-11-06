#!/usr/bin/env python3
"""Inventory installed Lean/Lake paths using local, read-only commands only."""
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

HERE = Path(__file__).resolve().parent
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
REF = TOOLS / "scratch/20260927-reference-experiments/reference-publish"
ELAN = TOOLS / "elan/toolchains"
NIX = Path("/nix/store")
RELEASE_PIN = TOOLS / "aeneas-release/backends/lean/lean-toolchain"
SOURCE_PIN = TOOLS / "sources/aeneas/backends/lean/lean-toolchain"
V429 = ELAN / "leanprover--lean4---v4.29.0/bin"
V430 = ELAN / "leanprover--lean4---v4.30.0-rc2/bin"
NIX_V430 = NIX / "wf1mr6pak9n88v5bwm6y749d8k19r0mw-lean-toolchain-aarch64-darwin-4.30.0-rc2/bin"

def sha(data):
    return hashlib.sha256(data).hexdigest()

def normalize(s):
    return s.replace(str(TOOLS), "$TOOLS").replace(str(NIX), "$NIX_STORE").replace("/Users/josh", "$USER_HOME")

def run(label, argv, cwd=None):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, timeout=30)
    out = normalize(p.stdout.decode("utf-8", "replace"))
    err = normalize(p.stderr.decode("utf-8", "replace"))
    return {"label": label, "command": shlex.join(map(str, argv)),
            "cwd": str(cwd) if cwd else None, "exit": p.returncode,
            "stdout_normalized": out, "stderr_normalized": err,
            "stdout_normalized_sha256": sha(out.encode()),
            "stderr_normalized_sha256": sha(err.encode())}

def main():
    commands = [
        run("reference_tip", ["git", "rev-parse", "HEAD"], REF),
        run("bundled_toolchain_directories", ["find", str(ELAN), "-mindepth", "1", "-maxdepth", "1", "-type", "d", "-print"]),
        run("home_elan_toolchain_directory", ["test", "-d", "/Users/josh/.elan/toolchains"]),
        run("nix_store_lean_named_directories", ["find", str(NIX), "-maxdepth", "1", "-type", "d", "-iname", "*lean*", "-print"]),
        run("installed_executable_hashes", ["shasum", "-a", "256", str(V429 / "lean"), str(V429 / "lake"),
                                            str(V430 / "lean"), str(V430 / "lake"),
                                            str(NIX_V430 / "lean"), str(NIX_V430 / "lake")]),
        run("aeneas_release_pin", ["cat", str(RELEASE_PIN)]),
        run("aeneas_source_pin", ["cat", str(SOURCE_PIN)]),
    ]
    doc = {"schema": 1, "observed_at": "2026-09-29", "commands": commands}
    (HERE / "inventory.json").write_text(json.dumps(doc, indent=2) + "\n")
    print(json.dumps({"reference_tip": commands[0]["stdout_normalized"].strip(),
                      "bundled": commands[1]["stdout_normalized"].splitlines(),
                      "nix_lean_named": commands[3]["stdout_normalized"].splitlines()}, indent=2))

if __name__ == "__main__":
    main()
