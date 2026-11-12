#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import copy
import json
import re
from collections import defaultdict
from pathlib import Path

LOG = Path("/tmp/ref_research_stack221_perf/track4/profile_clean_logs/ProductionSteps.prof1.log")
CAPTURE = Path("/tmp/anneal-mvp-starnix-installed-final/baseline-artifacts/capture/capture.json")

def to_ms(val: str, unit: str) -> float:
    return float(val) * (1000.0 if unit == "s" else 1.0)

def trace_path_steps(body, flag, width):
    markers = set()
    for block in body['blocks']:
        for stmt in block['statements']:
            if stmt['kind'] in ('storage_live', 'storage_dead'):
                markers.add(stmt['local'])
    locals_ = [('dead' if i in markers else 'uninit', None)
               for i in range(len(body['local_tys']))]
    locals_[1:4] = [('value', (str(flag), flag)),
                    ('value', (str(width), width)),
                    ('value', ('value', None))]
    block = position = 0
    steps_meta = []

    def operand(op):
        kind = op['kind']
        if kind == 'constant':
            return str(op['bits']), op['bits']
        index = op['local']
        value = locals_[index][1]
        if kind == 'move':
            locals_[index] = ('uninit', None)
        return value

    def rvalue(rv):
        kind = rv['kind']
        if kind == 'use':
            return operand(rv['operand'])
        if kind == 'discriminant':
            index = rv['local']
            value = locals_[index][1][1]
            table = body['local_tys'][index]['discriminants']
            return str(table[value]), table[value]
        left, left_known = operand(rv['left'])
        right, right_known = operand(rv['right'])
        op = rv['op']
        if op == 'bit_and':
            return f'({left} &&& {right})', None
        if op == 'bit_or':
            return f'({left} ||| {right})', None
        amount = right_known % 64
        operator = '<<<' if op == 'shl' else '>>>'
        return f'({left} {operator} ({amount} : Nat))', None

    step_idx = 0
    while True:
        current = body['blocks'][block]
        stmt_count = len(current['statements'])
        if position < stmt_count:
            stmt = current['statements'][position]
            kind = stmt['kind']
            local_idx = stmt.get('local', -1)
            subkind = kind
            if kind == 'assign':
                rv = stmt['value']
                if rv['kind'] == 'binary':
                    subkind = f"assign:binary:{rv['op']}"
                elif rv['kind'] == 'use':
                    subkind = f"assign:use:{rv['operand']['kind']}"
                else:
                    subkind = f"assign:{rv['kind']}"
                result = rvalue(rv)
                locals_[local_idx] = ('value', result)
            elif kind == 'storage_live':
                locals_[local_idx] = ('uninit', None)
            elif kind == 'storage_dead':
                locals_[local_idx] = ('dead', None)
            steps_meta.append({
                "step_idx": step_idx,
                "block": block,
                "position": position,
                "stmt_count_in_block": stmt_count,
                "kind": subkind,
                "local": local_idx,
            })
            position += 1
            step_idx += 1
            continue
        term = current['terminator']
        tkind = term['kind']
        steps_meta.append({
            "step_idx": step_idx,
            "block": block,
            "position": position,
            "stmt_count_in_block": stmt_count,
            "kind": f"terminator:{tkind}",
            "local": 0 if tkind == 'ret' else (term['operand'].get('local', -1) if tkind == 'switch_int' else -1),
        })
        if tkind == 'ret':
            break
        if tkind == 'goto':
            block = term['block']
        else:
            _, key = operand(term['operand'])
            block = dict(term['targets']).get(key, term['otherwise'])
        position = 0
        step_idx += 1
    return steps_meta

def main():
    data = json.loads(CAPTURE.read_text())
    b0 = data["program"]["bodies"][0]

    # Build expected sequence of 254 theorems in declaration order in ProductionSteps.lean
    # For each (flag, width): suffix_{last}, suffix_{last-1}, ..., suffix_0, then <label>
    expected_theorems = []
    for flag in (0, 1):
        for width in range(4):
            label = ('be' if flag else 'le') + str(8 << width)
            meta = trace_path_steps(b0, flag, width)
            for m in reversed(meta):
                expected_theorems.append({
                    "name": f"{label}_suffix{m['step_idx']}",
                    "label": label,
                    **m,
                })
            expected_theorems.append({
                "name": label,
                "label": label,
                "step_idx": -1,
                "block": 0,
                "position": -1,
                "stmt_count_in_block": 2,
                "kind": "initial_state_rfl",
                "local": -1,
            })

    log_lines = LOG.read_text().splitlines()
    eqrefl_vals = []
    tc_vals = []
    for line in log_lines:
        m1 = re.match(r".* Lean\.Parser\.Tactic\.eqRefl took ([0-9.]+)(ms|s)$", line)
        if m1:
            eqrefl_vals.append(to_ms(*m1.groups()))
        m2 = re.match(r"^type checking took ([0-9.]+)(ms|s)$", line)
        if m2:
            tc_vals.append(to_ms(*m2.groups()))

    assert len(expected_theorems) == len(eqrefl_vals) == len(tc_vals) == 254
    for thm, eq_ms, tc_ms in zip(expected_theorems, eqrefl_vals, tc_vals):
        thm["eqrefl_ms"] = round(eq_ms, 3)
        thm["kernel_tc_ms"] = round(tc_ms, 3)
        thm["total_rfl_ms"] = round(eq_ms + tc_ms, 3)

    # Group by kind
    by_kind = defaultdict(list)
    for t in expected_theorems:
        by_kind[t["kind"]].append(t)

    print("=== Attribution by MIR Step / Transition Kind across all 254 Theorems in ProductionSteps.lean ===")
    print(f"{'Kind':28s} | {'Count':5s} | {'Meta eqRefl (ms)':16s} | {'Kernel TC (ms)':14s} | {'Sum (ms)':10s} | {'Mean (ms)':9s} | {'Max (ms)':8s}")
    print("-" * 105)
    total_eq = sum(t["eqrefl_ms"] for t in expected_theorems)
    total_tc = sum(t["kernel_tc_ms"] for t in expected_theorems)
    for k, items in sorted(by_kind.items(), key=lambda kv: -sum(x["total_rfl_ms"] for x in kv[1])):
        s_eq = sum(x["eqrefl_ms"] for x in items)
        s_tc = sum(x["kernel_tc_ms"] for x in items)
        s_tot = s_eq + s_tc
        mean_tot = s_tot / len(items)
        max_tot = max(x["total_rfl_ms"] for x in items)
        print(f"{k:28s} | {len(items):5d} | {s_eq:16.2f} | {s_tc:14.2f} | {s_tot:10.2f} | {mean_tot:9.2f} | {max_tot:8.2f}")
    print("-" * 105)
    print(f"{'TOTAL':28s} | {len(expected_theorems):5d} | {total_eq:16.2f} | {total_tc:14.2f} | {total_eq+total_tc:10.2f} |")

    print("\n=== Top 20 Slowest Individual Step Theorems (excluding 8 initial_state_rfl) ===")
    step_thms = [t for t in expected_theorems if t["kind"] != "initial_state_rfl"]
    for t in sorted(step_thms, key=lambda x: -x["total_rfl_ms"])[:20]:
        print(f"  {t['name']:18s} | bb={t['block']:2d} pos={t['position']:2d} local={t['local']:2d} | {t['kind']:22s} | eqRefl={t['eqrefl_ms']:6.2f}ms + kernel={t['kernel_tc_ms']:6.2f}ms = {t['total_rfl_ms']:6.2f}ms")

    print("\n=== Scaling by Position / Local Index inside Block 4 (be64, 91 statements) ===")
    be64_bb4 = [t for t in step_thms if t["label"] == "be64" and t["block"] == 4]
    be64_bb4.sort(key=lambda x: x["position"])
    for k in ["storage_live", "storage_dead", "assign:use:copy", "assign:binary:bit_and", "assign:binary:shl", "assign:binary:shr", "assign:binary:bit_or"]:
        sub = [t for t in be64_bb4 if t["kind"] == k]
        if sub:
            first, mid, last = sub[0], sub[len(sub)//2], sub[-1]
            print(f"  {k:22s} (n={len(sub):2d}): first(pos={first['position']:2d},loc={first['local']:2d})={first['total_rfl_ms']:5.2f}ms | mid(pos={mid['position']:2d},loc={mid['local']:2d})={mid['total_rfl_ms']:5.2f}ms | last(pos={last['position']:2d},loc={last['local']:2d})={last['total_rfl_ms']:5.2f}ms")

    Path("/tmp/ref_research_stack221_perf/track4/profile_clean_logs/step_attribution.json").write_text(
        json.dumps(expected_theorems, indent=2)
    )

if __name__ == "__main__":
    main()
