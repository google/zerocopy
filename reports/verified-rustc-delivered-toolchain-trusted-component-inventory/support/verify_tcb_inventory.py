#!/usr/bin/env python3
"""Revalidation script for the delivered verified rustc toolchain TCB inventory."""
import json
import os
import sys

def main() -> None:
    here = os.path.dirname(os.path.abspath(__file__))
    inv_path = os.path.join(here, "toolchain_tcb_inventory.json")
    with open(inv_path) as f:
        inv = json.load(f)

    assert len(inv["lean_4_34_1_bins"]) >= 11, "Missing Lean 4.34.1 binaries"
    assert len(inv["rust_1_99_1_tier1_targets"]) == 8, "Expected 8 Tier 1 targets"
    for target, data in inv["rust_1_99_1_tier1_targets"].items():
        rlibs = [k for k in data["key_artifacts"] if k.endswith(".rlib")]
        assert any(k.startswith("libcore-") for k in rlibs), f"Missing libcore for {target}"
        assert any(k.startswith("liballoc-") for k in rlibs), f"Missing liballoc for {target}"
        assert any(k.startswith("libstd-") for k in rlibs), f"Missing libstd for {target}"
        assert any(k.startswith("libcompiler_builtins-") for k in rlibs), f"Missing compiler_builtins for {target}"
        assert any(k.startswith("libunwind-") for k in rlibs), f"Missing libunwind for {target}"

    print("OK: Verified TCB inventory across", len(inv["rust_1_99_1_tier1_targets"]), "Tier 1 targets and", len(inv["lean_4_34_1_bins"]), "Lean 4.34.1 binaries.")

if __name__ == "__main__":
    main()
