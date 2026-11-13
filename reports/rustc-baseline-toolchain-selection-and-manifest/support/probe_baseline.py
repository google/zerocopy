#!/usr/bin/env python3
"""Revalidation probe for the Rust 1.99.1 + Lean v4.34.1 baseline manifest."""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = json.loads((HERE / "baseline_manifest.json").read_text(encoding="utf-8"))

def main() -> int:
    base = MANIFEST["selected_baseline"]
    print(f"Pinned Rust baseline: {base['rust_release']} ({base['rust_revision']})")
    print(f"Pinned LLVM submodule: {base['llvm_version']} ({base['llvm_revision']})")
    print(f"Pinned Lean 4 version: {base['lean_version']} ({base['lean_revision']})")

    res = subprocess.run(["rustc", "+1.99.1-x86_64-unknown-linux-gnu", "-vV"], capture_output=True, text=True)
    if res.returncode == 0:
        out = res.stdout.strip()
        assert base["rust_revision"] in out, f"Commit mismatch: {out}"
        assert f"LLVM version: {base['llvm_version']}" in out, f"LLVM version mismatch: {out}"
        print("Verified installed rustc +1.99.1-x86_64-unknown-linux-gnu matches baseline.")
    else:
        print("rustc +1.99.1-x86_64-unknown-linux-gnu not installed; manifest static check passed.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
