#!/usr/bin/env python3
"""Summarize mathport's declaration alignment table (Lean 3 name -> Lean 4 name).

Usage: python3 mathport_aligns.py <mathlib-align.json> [<mathlib-alignImport.json>]
"""
import json, sys, collections
a = json.load(open(sys.argv[1]))
same = sum(1 for k, v in a.items() if k == v)
lower_same = sum(1 for k, v in a.items() if k != v and k.replace("_", "").lower() == v.replace("_", "").lower())
print("align_entries", len(a))
print("identical_names", same)
print("renamed", len(a) - same)
print("renamed_only_by_case_or_underscores", lower_same)
print("distinct_lean4_targets", len(set(a.values())))
tgt = collections.Counter(a.values())
print("lean4_targets_with_multiple_lean3_sources", sum(1 for v, c in tgt.items() if c > 1))
if len(sys.argv) > 2:
    b = json.load(open(sys.argv[2]))
    print("alignImport_entries", len(b))
