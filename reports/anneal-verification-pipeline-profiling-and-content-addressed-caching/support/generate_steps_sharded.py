#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Sharded candidate execution witness generator for ProductionSteps (K in {1, 2, 4, 8, 16}).

Supports two sharding modes (--mode):
- 'trace' (default):
    Partitions the 8 endianness/width trace families (le8..be64) across K shards
    (for K=16, splits each trace at its midpoint into two independent shards).
- 'round_robin':
    Distributes all 94 individual rfl transition/initial/terminal obligations
    (8 initial + 78 step + 8 ret) round-robin across K shards so heavy be64/be32
    transitions are balanced across all K shards, and chains them in O(1) inside
    ProductionSteps.lean without re-running rfl.
"""

import argparse
import copy
import json
from pathlib import Path

HEADER = (
    "-- Copyright 2026 The Fuchsia Authors\n"
    "--\n"
    "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0\n"
    "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT\n"
    "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.\n"
    "-- This file may not be copied, modified, or distributed except according to\n"
    "-- those terms.\n\n"
)


def trace_states(body: dict, flag: int, width: int) -> tuple[str, str, list[tuple[int, int, list]]]:
    markers = set()
    for block in body["blocks"]:
        for stmt in block["statements"]:
            if stmt["kind"] in ("storage_live", "storage_dead"):
                markers.add(stmt["local"])
    locals_ = [
        ("dead" if i in markers else "uninit", None)
        for i in range(len(body["local_tys"]))
    ]
    locals_[1:4] = [
        ("value", (str(flag), flag)),
        ("value", (str(width), width)),
        ("value", ("value", None)),
    ]
    block = position = 0
    states = []

    def operand(op):
        kind = op["kind"]
        if kind == "constant":
            return str(op["bits"]), op["bits"]
        index = op["local"]
        assert locals_[index][0] == "value", (index, locals_[index])
        value = locals_[index][1]
        if kind == "move":
            locals_[index] = ("uninit", None)
        else:
            assert kind == "copy"
        return value

    def rvalue(rv):
        kind = rv["kind"]
        if kind == "use":
            return operand(rv["operand"])
        if kind == "discriminant":
            index = rv["local"]
            assert locals_[index][0] == "value"
            value = locals_[index][1][1]
            table = body["local_tys"][index]["discriminants"]
            return str(table[value]), table[value]
        assert kind == "binary"
        left, _ = operand(rv["left"])
        right, right_known = operand(rv["right"])
        op = rv["op"]
        if op == "bit_and":
            return f"({left} &&& {right})", None
        if op == "bit_or":
            return f"({left} ||| {right})", None
        assert op in ("shl", "shr") and right_known is not None
        amount = right_known % 64
        operator = "<<<" if op == "shl" else ">>>"
        return f"({left} {operator} ({amount} : Nat))", None

    while True:
        states.append((block, position, copy.deepcopy(locals_)))
        current = body["blocks"][block]
        if position < len(current["statements"]):
            stmt = current["statements"][position]
            kind = stmt["kind"]
            if kind == "assign":
                result = rvalue(stmt["value"])
                locals_[stmt["local"]] = ("value", result)
            elif kind == "storage_live":
                locals_[stmt["local"]] = ("uninit", None)
            elif kind == "storage_dead":
                locals_[stmt["local"]] = ("dead", None)
            else:
                assert kind == "nop"
            position += 1
            continue
        term = current["terminator"]
        if term["kind"] == "ret":
            break
        if term["kind"] == "goto":
            block = term["block"]
        else:
            assert term["kind"] == "switch_int"
            _, key = operand(term["operand"])
            assert key is not None
            block = dict(term["targets"]).get(key, term["otherwise"])
        position = 0

    label = ("be" if flag else "le") + str(8 << width)
    if flag:
        output = f"swap{8 << width} value"
    elif width == 3:
        output = "value"
    else:
        output = f"value &&& {(1 << (8 << width)) - 1}"
    return label, output, states


def format_state_literal(b: int, p: int, slots: list) -> str:
    lines = [f"⟨{b}, {p}, ["]
    terms = [f".value {x[1][0]}" if x[0] == "value" else "." + x[0] for x in slots]
    for j in range(0, len(terms), 5):
        row = "    " + ", ".join(terms[j : j + 5])
        if j + 5 < len(terms):
            row += ","
        lines.append(row)
    lines.append("  ]⟩")
    return "\n".join(lines)


def emit_full_trace(flag: int, width: int, label: str, output: str, states: list) -> str:
    source = ""
    for i, (b, p, slots) in enumerate(states):
        lit = format_state_literal(b, p, slots)
        source += f"private def {label}_state{i} (value : Word) : State :=\n  {lit}\n\n"
    last = len(states) - 1
    source += (
        f"private theorem {label}_suffix{last} (value : Word) :\n"
        f"    Executes sourceBody ({label}_state{last} value) ({output}) :=\n"
        f"  .ret (by rfl)\n\n"
    )
    for i in range(last - 1, -1, -1):
        source += (
            f"private theorem {label}_suffix{i} (value : Word) :\n"
            f"    Executes sourceBody ({label}_state{i} value) ({output}) :=\n"
            f"  .next (by rfl) ({label}_suffix{i + 1} value)\n\n"
        )
    source += (
        f"theorem {label} (value : Word) :\n"
        f"    Safe sourceBody [{flag}, {width}, value] ∧\n"
        f"      Returns sourceBody [{flag}, {width}, value] ({output}) := by\n"
        f"  have start : initial sourceBody [{flag}, {width}, value] =\n"
        f"      {label}_state0 value := by rfl\n"
        f"  have execution : Executes sourceBody\n"
        f"      (initial sourceBody [{flag}, {width}, value]) ({output}) := by\n"
        f"    rw [start]\n"
        f"    exact {label}_suffix0 value\n"
        f"  exact ⟨executes_safe execution, executes_returns execution⟩\n\n"
    )
    return source


def emit_split_trace_half0(flag: int, width: int, label: str, states: list, mid: int) -> str:
    source = ""
    for i in range(0, mid + 1):
        b, p, slots = states[i]
        lit = format_state_literal(b, p, slots)
        vis = "" if i in (0, mid) else "private "
        source += f"{vis}def {label}_state{i} (value : Word) : State :=\n  {lit}\n\n"
    source += (
        f"theorem {label}_start (value : Word) :\n"
        f"    initial sourceBody [{flag}, {width}, value] = {label}_state0 value := rfl\n\n"
    )
    for i in range(0, mid):
        source += (
            f"theorem {label}_step{i} (value : Word) :\n"
            f"    step sourceBody ({label}_state{i} value) = .next ({label}_state{i + 1} value) := rfl\n\n"
        )
    return source


def emit_split_trace_half1(label: str, output: str, states: list, mid: int) -> str:
    source = ""
    last = len(states) - 1
    for i in range(mid, last + 1):
        b, p, slots = states[i]
        lit = format_state_literal(b, p, slots)
        name = f"{label}_state{i}_h1" if i == mid else f"{label}_state{i}"
        vis = "" if i == mid else "private "
        source += f"{vis}def {name} (value : Word) : State :=\n  {lit}\n\n"

    def st_name(idx: int) -> str:
        return f"{label}_state{idx}_h1" if idx == mid else f"{label}_state{idx}"

    source += (
        f"private theorem {label}_suffix{last} (value : Word) :\n"
        f"    Executes sourceBody ({st_name(last)} value) ({output}) :=\n"
        f"  .ret (by rfl)\n\n"
    )
    for i in range(last - 1, mid - 1, -1):
        vis = "" if i == mid else "private "
        source += (
            f"{vis}theorem {label}_suffix{i} (value : Word) :\n"
            f"    Executes sourceBody ({st_name(i)} value) ({output}) :=\n"
            f"  .next (by rfl) ({label}_suffix{i + 1} value)\n\n"
        )
    return source


def emit_split_trace_glue(flag: int, width: int, label: str, output: str, mid: int) -> str:
    chain = f"({label}_suffix{mid} value)"
    for i in range(mid - 1, -1, -1):
        chain = f"(.next ({label}_step{i} value) {chain})"
    return (
        f"theorem {label} (value : Word) :\n"
        f"    Safe sourceBody [{flag}, {width}, value] ∧\n"
        f"      Returns sourceBody [{flag}, {width}, value] ({output}) := by\n"
        f"  have execution : Executes sourceBody\n"
        f"      (initial sourceBody [{flag}, {width}, value]) ({output}) := by\n"
        f"    rw [{label}_start value]\n"
        f"    exact {chain}\n"
        f"  exact ⟨executes_safe execution, executes_returns execution⟩\n\n"
    )


def generate_sharded(
    capture_path: Path,
    out_dir: Path,
    k_shards: int,
    mode: str = "trace",
) -> list[dict]:
    """Generates ProductionSteps.lean (and ProductionSteps_0..{K-1}.lean when K > 1) in out_dir."""
    captured = json.loads(capture_path.read_text())
    bodies = captured["program"]["bodies"]
    if len(bodies) != 1:
        raise ValueError("Expected 1 body")
    body = bodies[0]

    traces = []
    for flag in (0, 1):
        for width in range(4):
            label, output, states = trace_states(body, flag, width)
            traces.append((flag, width, label, output, states))

    out_dir.mkdir(parents=True, exist_ok=True)
    mod_preamble = (
        HEADER
        + "prelude\nimport InitialCache\n\nnamespace ProductionSteps\n\n"
        + "open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction\n\n"
    )
    mod_epilogue = "end ProductionSteps\n"

    if k_shards == 1:
        parts = [emit_full_trace(f, w, lbl, out, sts) for f, w, lbl, out, sts in traces]
        p = out_dir / "ProductionSteps.lean"
        p.write_text(mod_preamble + "".join(parts) + mod_epilogue)
        return [{"module": "ProductionSteps", "path": p, "role": "proof"}]

    if mode == "round_robin":
        obligations = []
        for flag, width, label, output, states in traces:
            st0_lit = format_state_literal(*states[0])
            obligations.append(
                f"theorem {label}_start (value : Word) :\n"
                f"    initial sourceBody [{flag}, {width}, value] =\n  {st0_lit} := rfl\n\n"
            )
            last = len(states) - 1
            for i in range(last):
                sti_lit = format_state_literal(*states[i])
                stn_lit = format_state_literal(*states[i + 1])
                obligations.append(
                    f"theorem {label}_step{i} (value : Word) :\n"
                    f"    step sourceBody\n  {sti_lit} =\n    .next\n  {stn_lit} := rfl\n\n"
                )
            stl_lit = format_state_literal(*states[last])
            obligations.append(
                f"theorem {label}_ret (value : Word) :\n"
                f"    step sourceBody\n  {stl_lit} =\n    .ret ({output}) := rfl\n\n"
            )

        buckets: list[list[str]] = [[] for _ in range(k_shards)]
        for idx, ob in enumerate(obligations):
            buckets[idx % k_shards].append(ob)

        generated = []
        imports_lines = []
        for s_idx in range(k_shards):
            mod_name = f"ProductionSteps_{s_idx}"
            p = out_dir / f"{mod_name}.lean"
            p.write_text(mod_preamble + "".join(buckets[s_idx]) + mod_epilogue)
            generated.append({"module": mod_name, "path": p, "role": "proof"})
            imports_lines.append(f"import {mod_name}\n")

        glue = []
        for flag, width, label, output, states in traces:
            last = len(states) - 1
            chain = f"(.ret ({label}_ret value))"
            for i in range(last - 1, -1, -1):
                chain = f"(.next ({label}_step{i} value) {chain})"
            glue.append(
                f"theorem {label} (value : Word) :\n"
                f"    Safe sourceBody [{flag}, {width}, value] ∧\n"
                f"      Returns sourceBody [{flag}, {width}, value] ({output}) := by\n"
                f"  have execution : Executes sourceBody\n"
                f"      (initial sourceBody [{flag}, {width}, value]) ({output}) := by\n"
                f"    rw [{label}_start value]\n"
                f"    exact {chain}\n"
                f"  exact ⟨executes_safe execution, executes_returns execution⟩\n\n"
            )

        agg_path = out_dir / "ProductionSteps.lean"
        agg_path.write_text(
            HEADER
            + "prelude\n"
            + "".join(imports_lines)
            + "\nnamespace ProductionSteps\n\n"
            + "open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction\n\n"
            + "".join(glue)
            + mod_epilogue
        )
        generated.append({"module": "ProductionSteps", "path": agg_path, "role": "proof"})
        return generated

    if k_shards in (2, 4, 8):
        shard_buckets: list[list[str]] = [[] for _ in range(k_shards)]
        for idx, (f, w, lbl, out, sts) in enumerate(traces):
            shard_idx = idx % k_shards
            shard_buckets[shard_idx].append(emit_full_trace(f, w, lbl, out, sts))

        generated = []
        imports_lines = []
        for s_idx in range(k_shards):
            mod_name = f"ProductionSteps_{s_idx}"
            p = out_dir / f"{mod_name}.lean"
            p.write_text(mod_preamble + "".join(shard_buckets[s_idx]) + mod_epilogue)
            generated.append({"module": mod_name, "path": p, "role": "proof"})
            imports_lines.append(f"import {mod_name}\n")

        agg_path = out_dir / "ProductionSteps.lean"
        agg_path.write_text(HEADER + "prelude\n" + "".join(imports_lines))
        generated.append({"module": "ProductionSteps", "path": agg_path, "role": "proof"})
        return generated

    if k_shards == 16:
        generated = []
        imports_lines = []
        glue_parts = []
        for t_idx, (f, w, lbl, out, sts) in enumerate(traces):
            mid = len(sts) // 2
            s0_name = f"ProductionSteps_{2 * t_idx}"
            s1_name = f"ProductionSteps_{2 * t_idx + 1}"
            p0 = out_dir / f"{s0_name}.lean"
            p1 = out_dir / f"{s1_name}.lean"

            p0.write_text(mod_preamble + emit_split_trace_half0(f, w, lbl, sts, mid) + mod_epilogue)
            p1.write_text(mod_preamble + emit_split_trace_half1(lbl, out, sts, mid) + mod_epilogue)

            generated.append({"module": s0_name, "path": p0, "role": "proof"})
            generated.append({"module": s1_name, "path": p1, "role": "proof"})
            imports_lines.append(f"import {s0_name}\n")
            imports_lines.append(f"import {s1_name}\n")
            glue_parts.append(emit_split_trace_glue(f, w, lbl, out, mid))

        agg_path = out_dir / "ProductionSteps.lean"
        agg_text = (
            HEADER
            + "prelude\n"
            + "".join(imports_lines)
            + "\nnamespace ProductionSteps\n\n"
            + "open Trusted.Mvp Anneal.Mvp Endianness ProductionReduction\n\n"
            + "".join(glue_parts)
            + "end ProductionSteps\n"
        )
        agg_path.write_text(agg_text)
        generated.append({"module": "ProductionSteps", "path": agg_path, "role": "proof"})
        return generated

    raise ValueError(f"Unsupported k_shards={k_shards}; expected 1, 2, 4, 8, or 16")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("capture", type=Path, help="Typed capture.json input")
    parser.add_argument("out_dir", type=Path, help="Output directory for ProductionSteps*.lean")
    parser.add_argument("--shards", type=int, default=1, choices=[1, 2, 4, 8, 16])
    parser.add_argument("--mode", default="trace", choices=["trace", "round_robin"])
    args = parser.parse_args()
    mods = generate_sharded(args.capture, args.out_dir, args.shards, mode=args.mode)
    print(f"Generated {len(mods)} modules for K={args.shards} (mode={args.mode}) in {args.out_dir}")


if __name__ == "__main__":
    main()
