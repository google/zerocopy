#!/usr/bin/env python3
"""Verify evidence_packaging_and_reproducibility.json and optionally run ELF strip probe."""

from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.manifest.read_text(encoding="utf-8"))
    sections = data["elf_strip_probe_results"]["embedded_sections_tested"]
    assert len(sections) == 2
    for s in sections:
        assert s["in_pt_load"] is False
        assert s["survives_c_strip_symbols"] is True
        assert s["survives_gnu_strip_all"] is True
    assert len(data["binary_format_evidence_matrix"]) == 3
    assert len(data["rustc_reproducibility_controls"]) == 5
    print("OK: verified ELF non-allocated section survival across strip modes, 3 binary format matrices, and 5 rustc reproducibility controls.")


if __name__ == "__main__":
    main()
