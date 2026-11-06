#!/usr/bin/env python3
"""Deterministic, balanced study schedule; no participant observations."""
import csv
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
cases=[c["id"] for c in json.loads((HERE/"stimuli.json").read_text())["cases"]]
assert len(cases)==8 and len(set(cases))==8
with (HERE/"assignments.csv").open("w",newline="") as f:
    w=csv.writer(f)
    w.writerow(["slot_id","experience_stratum","presentation","rotation","case_order"])
    n=0
    for stratum in ["Rust-first","Rust-and-Lean"]:
        for presentation in ["A","B"]:
            for rotation in range(8):
                n+=1
                w.writerow([f"slot-{n:02d}",stratum,presentation,rotation,
                            ";".join(cases[rotation:]+cases[:rotation])])
