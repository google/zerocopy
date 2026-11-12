#!/usr/bin/env python3
import json
import os
import subprocess
import sys

CARGO_ANNEAL = "/tmp/ref_research_stack221_perf/track1/mvp_instrumented/target/release/cargo-anneal"
CAPTURE = "/tmp/ref_research_stack221_perf/mvp_src/target/release/anneal-rustc-capture"
LEAN = "/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
SYSROOT = "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu"
BASE_DIR = "/tmp/ref_research_stack221_perf/track1/support/bb_scaling"

HEADER_RS = """// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

"""

HEADER_LEAN = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""

COMBOS = {
    1: (0, 0),
    10: (3, 0),
    20: (5, 1),
    40: (13, 0),
    86: (27, 1),
}

def simulate_steps(body):
    n_locals = len(body["local_tys"])
    has_marker = set()
    for blk in body["blocks"]:
        for st in blk["statements"]:
            if st["kind"] in ("storage_live", "storage_dead"):
                has_marker.add(st["local"])
    locals_state = []
    for idx in range(n_locals):
        if idx == 1:
            locals_state.append(("sym", "value"))
        elif idx in has_marker:
            locals_state.append(("dead", None))
        else:
            locals_state.append(("uninit", None))
    blk_idx = 0
    stmt_idx = 0
    states = []
    while True:
        states.append((blk_idx, stmt_idx, list(locals_state)))
        blk = body["blocks"][blk_idx]
        if stmt_idx < len(blk["statements"]):
            st = blk["statements"][stmt_idx]
            kind = st["kind"]
            loc = st["local"]
            if kind == "storage_live":
                locals_state[loc] = ("uninit", None)
            elif kind == "storage_dead":
                locals_state[loc] = ("dead", None)
            elif kind == "assign":
                rv = st["value"]
                if rv["kind"] == "unit":
                    locals_state[loc] = ("val", 0)
                elif rv["kind"] == "use":
                    op = rv["operand"]
                    if op["kind"] == "constant":
                        locals_state[loc] = ("val", op["bits"])
                    elif op["kind"] in ("copy", "move"):
                        src = op["local"]
                        val = locals_state[src]
                        if op["kind"] == "move":
                            locals_state[src] = ("uninit", None)
                        locals_state[loc] = val
                elif rv["kind"] == "binary":
                    assert rv["op"] == "eq"
                    l_op = rv["left"]
                    r_op = rv["right"]
                    l_val = locals_state[l_op["local"]]
                    if l_op["kind"] == "move":
                        locals_state[l_op["local"]] = ("uninit", None)
                    assert l_val[0] == "val"
                    res_bit = 1 if l_val[1] == r_op["bits"] else 0
                    locals_state[loc] = ("val", res_bit)
                else:
                    raise RuntimeError(f"unknown rvalue {rv}")
            stmt_idx += 1
        else:
            term = blk["terminator"]
            if term["kind"] == "goto":
                blk_idx = term["block"]
                stmt_idx = 0
            elif term["kind"] == "switch_int":
                op = term["operand"]
                v = locals_state[op["local"]]
                if op["kind"] == "move":
                    locals_state[op["local"]] = ("uninit", None)
                assert v[0] == "val"
                target = term["otherwise"]
                for val_match, tgt in term["targets"]:
                    if v[1] == val_match:
                        target = tgt
                        break
                blk_idx = target
                stmt_idx = 0
            elif term["kind"] == "ret":
                break
            else:
                raise RuntimeError(f"unknown term {term}")
    return states

def format_slot(slot):
    kind, val = slot
    if kind == "dead":
        return ".dead"
    elif kind == "uninit":
        return ".uninit"
    elif kind == "sym":
        return f".value {val}"
    elif kind == "val":
        return f".value {val}"
    raise ValueError(slot)

def generate_fixture(B):
    a, b = COMBOS[B]
    rs_lines = [
        HEADER_RS.rstrip(),
        "",
        "pub fn chain(value: u64) -> u64 {",
        "    let mut tag: u64 = 0;",
        "    let mut acc: u64 = value;",
    ]
    for i in range(a):
        rs_lines.append(f"    if tag == {1000 + i} {{ acc = acc ^ 1; }}")
    for j in range(b):
        rs_lines.append(f"    match tag {{ {2000 + j} => {{ acc = acc ^ 1; }} {3000 + j} => {{ acc = acc ^ 2; }} _ => {{}} }}")
    rs_lines.append("    acc")
    rs_lines.append("}")
    rust_src = "\n".join(rs_lines) + "\n"

    # Run capture once to get capture.json for state generation
    import shutil
    tmp_cap_dir = os.path.join(BASE_DIR, f"_tmp_cap_{B}")
    shutil.rmtree(tmp_cap_dir, ignore_errors=True)
    os.makedirs(tmp_cap_dir, exist_ok=True)
    tmp_rs = os.path.join(tmp_cap_dir, "lib.rs")
    open(tmp_rs, "w").write(rust_src)
    out_cap_dir = os.path.join(tmp_cap_dir, "out")
    os.makedirs(out_cap_dir, exist_ok=True)
    env = {"PATH": "/usr/bin:/bin", "LD_LIBRARY_PATH": f"{SYSROOT}/lib"}
    subprocess.run(
        [CAPTURE, "capture", "--crate-root", tmp_rs, "--crate-name", f"chain_b{B}", "--edition", "2024",
         "--target", "x86_64-unknown-linux-gnu", "--out-dir", out_cap_dir, "--scope", "crate",
         "--sysroot", SYSROOT, "--source-file", tmp_rs],
        env=env, check=True, capture_output=True
    )
    cj = json.load(open(os.path.join(out_cap_dir, "capture.json")))
    body = cj["program"]["bodies"][0]
    assert len(body["blocks"]) == B, f"Expected {B} BBs, got {len(body['blocks'])}"
    states = simulate_steps(body)
    S = len(states)

    spec_lean = HEADER_LEAN + """prelude
import Trusted.Mvp

namespace Spec

open Trusted.Mvp

def preservesValue (program : Program) : Prop :=
  ∀ body, program.bodies[0]? = some body →
    ∀ value : Word, Safe body [value] ∧ Returns body [value] value

def specs : Specs := ⟨fun _ _ => False, preservesValue⟩

end Spec
"""

    # Mode 1: ProductionSteps (per-step `.next (by rfl)` chain, matching starnix)
    steps_dir = os.path.join(BASE_DIR, f"steps_B{B}")
    os.makedirs(os.path.join(steps_dir, "rust"), exist_ok=True)
    os.makedirs(os.path.join(steps_dir, "lean"), exist_ok=True)
    open(os.path.join(steps_dir, "rust", "lib.rs"), "w").write(rust_src)
    open(os.path.join(steps_dir, "lean", "Spec.lean"), "w").write(spec_lean)

    ps_lines = [
        HEADER_LEAN.rstrip(),
        "",
        "prelude",
        "import Captured",
        "import Anneal.Mvp.Execution",
        "",
        "namespace ProductionSteps",
        "",
        "open Trusted.Mvp Anneal.Mvp",
        "",
        "abbrev sourceBody : Body := Captured.program.bodies[0]'(by decide)",
        "",
    ]
    for idx, (blk_i, stmt_i, locs) in enumerate(states):
        slots_str = ", ".join(format_slot(s) for s in locs)
        ps_lines.append(f"private def state{idx} (value : Word) : State :=")
        ps_lines.append(f"  ⟨{blk_i}, {stmt_i}, [{slots_str}]⟩")
        ps_lines.append("")

    for idx in range(S - 1, -1, -1):
        ps_lines.append(f"private theorem suffix{idx} (value : Word) :")
        ps_lines.append(f"    Executes sourceBody (state{idx} value) value :=")
        if idx == S - 1:
            ps_lines.append("  .ret (by rfl)")
        else:
            ps_lines.append(f"  .next (by rfl) (suffix{idx + 1} value)")
        ps_lines.append("")

    ps_lines.extend([
        "theorem chain_exec (value : Word) :",
        "    Safe sourceBody [value] ∧ Returns sourceBody [value] value := by",
        "  have start : initial sourceBody [value] = state0 value := by rfl",
        "  have execution : Executes sourceBody (initial sourceBody [value]) value := by",
        "    rw [start]",
        "    exact suffix0 value",
        "  exact ⟨executes_safe execution, executes_returns execution⟩",
        "",
        "end ProductionSteps",
    ])
    open(os.path.join(steps_dir, "lean", "ProductionSteps.lean"), "w").write("\n".join(ps_lines) + "\n")

    proof_steps_lean = HEADER_LEAN + """prelude
import Expected
import ProductionSteps

namespace Proof

open Trusted.Mvp Anneal.Mvp ProductionSteps

theorem validArgs1_elim (body : Body) (count : body.argCount = 1)
    (p : List Word → Prop) (h : ∀ value : Word, p [value]) :
    ∀ args, argsValid body args → p args := by
  intro args valid
  have len : args.length = 1 := valid.1.trans count
  cases args with
  | nil => contradiction
  | cons v rest =>
    cases rest with
    | nil => exact h v
    | cons _ _ => simp at len

theorem wellFormed : bodyWF sourceBody = true := by decide

theorem baseline (safetyPre : List Word → Prop) :
    BodyVerified sourceBody safetyPre := by
  constructor
  · exact wellFormed
  · intro args valid _
    apply validArgs1_elim sourceBody rfl (Safe sourceBody) _ args valid
    intro value
    exact (chain_exec value).1

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
        have same : sourceBody = selected := Option.some.inj found
        subst selected
        exact baseline _
      | succ id => simp [Captured.program] at found
    · intro selected found value
      have same : sourceBody = selected := Option.some.inj found
      subst selected
      exact chain_exec value

end Proof
"""
    open(os.path.join(steps_dir, "lean", "Proof.lean"), "w").write(proof_steps_lean)

    req_steps = {
        "schema_version": 1,
        "compilation": {
            "source_root": "rust",
            "crate_root": "lib.rs",
            "crate_name": f"chain_b{B}",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": "lean",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "ProductionSteps", "path": "ProductionSteps.lean", "role": "proof"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ],
        },
    }
    open(os.path.join(steps_dir, "request.json"), "w").write(json.dumps(req_steps, indent=2) + "\n")

    # Mode 2: Direct `run body fuel` single-theorem mode
    run_dir = os.path.join(BASE_DIR, f"run_B{B}")
    os.makedirs(os.path.join(run_dir, "rust"), exist_ok=True)
    os.makedirs(os.path.join(run_dir, "lean"), exist_ok=True)
    open(os.path.join(run_dir, "rust", "lib.rs"), "w").write(rust_src)
    open(os.path.join(run_dir, "lean", "Spec.lean"), "w").write(spec_lean)

    proof_run_lean = HEADER_LEAN + f"""prelude
import Expected
import Anneal.Mvp.Execution

namespace Proof

open Trusted.Mvp Anneal.Mvp

abbrev sourceBody : Body := Captured.program.bodies[0]'(by decide)

theorem validArgs1_elim (body : Body) (count : body.argCount = 1)
    (p : List Word → Prop) (h : ∀ value : Word, p [value]) :
    ∀ args, argsValid body args → p args := by
  intro args valid
  have len : args.length = 1 := valid.1.trans count
  cases args with
  | nil => contradiction
  | cons v rest =>
    cases rest with
    | nil => exact h v
    | cons _ _ => simp at len

theorem wellFormed : bodyWF sourceBody = true := by decide

theorem runs (value : Word) :
    run sourceBody {S} (initial sourceBody [value]) = some value := rfl

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
        have same : sourceBody = selected := Option.some.inj found
        subst selected
        refine ⟨wellFormed, ?_⟩
        intro args valid _
        apply validArgs1_elim sourceBody rfl (Safe sourceBody) _ args valid
        intro value
        exact (run_initial_success (runs value)).1
      | succ id => simp [Captured.program] at found
    · intro selected found value
      have same : sourceBody = selected := Option.some.inj found
      subst selected
      exact run_initial_success (runs value)

end Proof
"""
    open(os.path.join(run_dir, "lean", "Proof.lean"), "w").write(proof_run_lean)
    req_run = {
        "schema_version": 1,
        "compilation": {
            "source_root": "rust",
            "crate_root": "lib.rs",
            "crate_name": f"chain_b{B}",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": "lean",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ],
        },
    }
    open(os.path.join(run_dir, "request.json"), "w").write(json.dumps(req_run, indent=2) + "\n")
    print(f"Generated B={B:2d}: steps={S:3d}, locals={len(body['local_tys']):3d}, ProductionSteps.lean={os.path.getsize(os.path.join(steps_dir, 'lean', 'ProductionSteps.lean')):7d}B")

if __name__ == "__main__":
    for B in [1, 10, 20, 40, 86]:
        generate_fixture(B)
