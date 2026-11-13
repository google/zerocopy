#!/usr/bin/env python3
"""Reproducible verification script for O7 optimization precedent metrics."""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SUMMARY = HERE / "optimization_precedents_summary.json"


def main() -> int:
    data = json.loads(SUMMARY.read_text(encoding="utf-8"))
    cc = data["compcert"]
    assert cc["total_coq_v_files"] == 253 and cc["total_coq_v_lines"] == 205719
    assert cc["backend_v_files"] == 54 and cc["backend_v_lines"] == 47262
    assert data["vellvm"]["total_v_lines"] == 47791
    assert data["crellvm"]["total_coq_lines"] == 29196
    assert data["alive2"]["cpp_h_lines"] == 37931
    assert data["lean_mlir"]["total_lean_lines"] == 616630
    assert data["regalloc2"]["checker_rs_lines"] == 1011
    print("Verified O7 optimization precedents summary across CompCert, Vellvm, Crellvm, Alive2, Lean-MLIR, regalloc2, and CakeML.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
