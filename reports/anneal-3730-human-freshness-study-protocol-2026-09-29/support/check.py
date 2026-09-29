#!/usr/bin/env python3
"""Check protocol completeness and assignment balance; does not evaluate humans."""
import csv
import json
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
stim=json.loads((HERE/"stimuli.json").read_text())
cases=stim["cases"]
ids=[c["id"] for c in cases]
assert len(ids)==8 and len(set(ids))==8
assert {c["class"] for c in cases}=={
    "stale_model","pending_import","cancelled_work","unsupported_translation",
    "approximate_location","expired_handle","current_editable_control","current_checked_control"}
for c in cases:
    assert len(c["facts"])==3
    assert all(c[k].strip() for k in ["expected_subject","sound_next_step","unsafe_inference","source_basis"])
assert set(stim["presentation_conditions"])=={"A","B"}
rows=list(csv.DictReader((HERE/"assignments.csv").open()))
assert len(rows)==32 and len({r["slot_id"] for r in rows})==32
for stratum in ["Rust-first","Rust-and-Lean"]:
    for variant in ["A","B"]:
        group=[r for r in rows if r["experience_stratum"]==stratum and r["presentation"]==variant]
        assert len(group)==8
        assert {int(r["rotation"]) for r in group}==set(range(8))
        positions=Counter()
        for r in group:
            order=r["case_order"].split(";")
            assert set(order)==set(ids) and len(order)==8
            for pos,case in enumerate(order):positions[(case,pos)]+=1
        assert set(positions.values())=={1} and len(positions)==64
with (HERE/"results-template.csv").open(newline="") as f:
    result_rows=list(csv.reader(f))
assert len(result_rows)==1 and len(result_rows[0])>=18
assert "I141" in (HERE/"issue-scope.md").read_text()
assert "not an approval" in (HERE/"CONSENT_SCRIPT.md").read_text()
print("OK: eight keyed cases; 32 empty participant slots; full order/condition balance; no response rows")
