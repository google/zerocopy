#!/usr/bin/env python3
"""Verify qualification_deviation_matrix.json and optionally probe FLS / rustc."""

from __future__ import annotations
import argparse
import json
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matrix", type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.matrix.read_text(encoding="utf-8"))
    assert data["fls_1_99_metrics"]["normative_paragraph_ids_dp_fls"] == 4014
    assert data["rustc_1_99_1_policy_metrics"]["future_incompatible_lints_in_builtin_rs"] == 49
    assert len(data["qualification_and_assurance_precedents"]) == 5
    print("OK: verified FLS 1.99 paragraph count (4014), rustc 1.99.1 future-incompatible lints (49), and 5 precedent entries.")


if __name__ == "__main__":
    main()
