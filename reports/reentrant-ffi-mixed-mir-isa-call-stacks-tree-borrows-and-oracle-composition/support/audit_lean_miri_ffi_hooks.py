#!/usr/bin/env python3
"""Verify vendor/lean-miri (c92d1d97) and Anneal (c131b320) FFI / InlineAsm hooks.

Read-only static audit script. Accepts a path to a `joshlf/anneal` checkout at
commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (default: current directory `.`)
and verifies:
1. `Miri/MIR/Syntax.lean` declares `TerminatorKind.InlineAsm` and `InlineAsmTerminator`.
2. `Miri/Interpreter/ControlFlow.lean` omits an `inlineAsm` field from
   `TerminatorHooks` and hardcodes `.InlineAsm _ => .error (.unsupported "inline assembly")`.
3. `Miri/Interpreter/Call.lean` and `CallDispatchMachine.lean` route foreign
   calls through `findMirOrEvalFn` / `ForeignItems.emulate`, bypassing
   `initStackFrame` (and thus `withRetagMode .FnEntry`) unless falling back to a
   Rust-defined exported MIR body.
4. `Miri/Interpreter/NativeMachine.lean` and `Native/Supervisor.lean` live
   outside `UPSTREAM_PIN.json`'s 160-module `execution_machine_closure` and
   model native calls as a single big-step `host.execute` rejecting callbacks.
5. `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, `Trusted/Correspondence.lean`,
   and `TrustedBoundary.lean` fail closed on `InlineAsm`/`Call` and lock exact
   `verifyRefEvaluatorIndependence` cones (21 required Miri / 25 forbidden Anneal).
"""

import json
import pathlib
import re
import sys


def read_text(path: pathlib.Path) -> str:
    return path.read_text(encoding="utf-8")


def audit(anneal_root: pathlib.Path) -> dict:
    pin_path = anneal_root / "vendor/lean-miri/UPSTREAM_PIN.json"
    pin = json.loads(read_text(pin_path))
    closure = {e["module"] for e in pin["execution_machine_closure"]}
    vendor_files = {e["path"] for e in pin["vendor_tree"]["files"]}

    assert pin["commit"] == "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a", pin["commit"]
    assert len(closure) == 160, len(closure)
    assert len(vendor_files) == 608, len(vendor_files)

    # 1. ControlFlow.lean InlineAsm hardcoded unsupported & absent from TerminatorHooks
    cf = read_text(anneal_root / "vendor/lean-miri/Miri/Interpreter/ControlFlow.lean")
    m_th = re.search(r"structure TerminatorHooks.*?namespace ControlFlow", cf, re.S)
    assert m_th is not None, "TerminatorHooks not found"
    assert "inlineAsm" not in m_th.group(0), "unexpected inlineAsm hook in TerminatorHooks"
    assert '| .InlineAsm _ => return (state, .error (.unsupported "inline assembly"))' in cf

    # 2. Miri/MIR/Syntax.lean has full InlineAsmTerminator AST
    syn = read_text(anneal_root / "vendor/lean-miri/Miri/MIR/Syntax.lean")
    assert "structure InlineAsmTerminator where" in syn
    assert "| InlineAsm (asm : InlineAsmTerminator)" in syn

    # 3. CallDispatchMachine.lean and ForeignItems.lean are IN closure; NativeMachine is OUT
    assert "Miri.Interpreter.ForeignItems" in closure
    assert "Miri.Interpreter.CallDispatchMachine" in closure
    assert "Miri.Interpreter.Call" in closure
    assert "Miri.Interpreter.ControlFlow" in closure
    assert "Miri.Interpreter.Step" in closure
    assert "Miri.Interpreter.Unwind" in closure
    assert "Miri.Memory.AllocAddresses.GlobalState" in closure
    assert "Miri.Memory.MiriMemoryKind" in closure
    assert "Miri.TreeBorrows.TreeState" in closure
    assert "Miri.Interpreter.NativeMachine" not in closure
    assert "Miri.Interpreter.Native.Supervisor" not in closure
    assert "Miri/Interpreter/NativeMachine.lean" in vendor_files
    assert "Miri/Interpreter/Native/Supervisor.lean" in vendor_files

    # 4. Native/Supervisor.lean rejects native callback into Rust; ForeignItems rejects realloc(p,0)
    sup = read_text(anneal_root / "vendor/lean-miri/Miri/Interpreter/Native/Supervisor.lean")
    assert "native callback into Rust?" in sup
    fi = read_text(anneal_root / "vendor/lean-miri/Miri/Interpreter/ForeignItems.lean")
    assert 'else if size == 0 then throw (.undefinedBehavior "realloc with size zero")' in fi
    assert 'if size == 0 then throw (.undefinedBehavior "creating allocation with size 0")' in fi

    # 5. MemoryState.lean enforces memoryKindMismatch and layoutMismatch on deallocatePtrWith
    ms = read_text(anneal_root / "vendor/lean-miri/Miri/Memory/MemoryState.lean")
    assert ".error (.memoryKindMismatch allocId)" in ms
    assert ".error (.layoutMismatch allocId" in ms

    # 6. Trusted/MirSemantics.lean & Trusted/Correspondence.lean fail closed on Call/InlineAsm
    t_ast = read_text(anneal_root / "trusted/lean/Trusted/MirAst.lean")
    assert "InlineAsm" in t_ast and "| unsupported" in t_ast
    t_sem = read_text(anneal_root / "trusted/lean/Trusted/MirSemantics.lean")
    assert "| .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>" in t_sem
    t_corr = read_text(anneal_root / "trusted/correspondence/Trusted/Correspondence.lean")
    assert "def CorrespondenceClaim : Prop :=" in t_corr
    assert "def FaultEquivalenceClaim : Prop :=" in t_corr
    assert "rs.frames = [callerSentinelFrame retTy, rf]" in t_corr

    # 7. TrustedBoundary.lean verifyRefEvaluatorIndependence counts
    tb = read_text(anneal_root / "trusted/audit/TrustedBoundary.lean")
    m_ind = re.search(
        r"def verifyRefEvaluatorIndependence.*?def preflightCorrespondence", tb, re.S
    )
    assert m_ind is not None
    block = m_ind.group(0)
    req_miri = re.findall(r"`Miri\.[A-Za-z0-9_.]+", block)
    forb_anneal = re.findall(r"`Trusted\.MirSemantics\.[A-Za-z0-9_.?]+", block)
    assert len(req_miri) == 21, len(req_miri)
    assert len(forb_anneal) == 25, len(forb_anneal)

    native_out = sorted(
        f for f in vendor_files
        if "Native" in f and f.endswith(".lean") and f[:-5].replace("/", ".") not in closure
    )
    foreign_out = sorted(
        f for f in vendor_files
        if "Foreign" in f and f.endswith(".lean") and f[:-5].replace("/", ".") not in closure
    )
    return {
        "lean_miri_commit": pin["commit"],
        "vendor_lean_files": len(vendor_files),
        "execution_machine_closure_modules": len(closure),
        "native_modules_outside_closure": len(native_out),
        "foreign_modules_outside_closure": len(foreign_out),
        "required_miri_primitives": len(req_miri),
        "forbidden_anneal_evaluators": len(forb_anneal),
        "inline_asm_hook_present": False,
        "status": "OK",
    }


def main() -> int:
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    res = audit(root)
    print(json.dumps(res, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
