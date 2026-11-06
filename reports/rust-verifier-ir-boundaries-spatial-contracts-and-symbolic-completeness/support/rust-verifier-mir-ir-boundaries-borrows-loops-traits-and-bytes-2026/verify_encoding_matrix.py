#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Structured cross-verifier encoding matrix and Lean 4 probe validator.

Validates the 7-verifier x 4-axis semantic encoding matrix (Anneal,
Charon/Aeneas, Creusot/Coma, RefinedRust/Caesium, Verus, Kani/CBMC, and
MiniRust) and audits `support/VerifierEncodingComparison.lean` for required
theorem declarations, zero `sorry` tokens, zero custom `axiom` declarations,
80-column formatting, and optional kernel verification under both
`leanprover/lean4:v4.28.0` and `leanprover/lean4:v4.34.1` via
`anneal-lean-run`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
from typing import Any

AXES: tuple[str, ...] = (
    "axis1_borrows_reborrows_pointers",
    "axis2_loops_joins_canonicalization",
    "axis3_generics_traits_associated_items",
    "axis4_bytes_padding_uninit_transmute",
)

VERIFIER_MATRIX: dict[str, dict[str, Any]] = {
    "anneal": {
        "display_name": "Anneal (Stage 1/2/3)",
        "extraction_boundary": (
            "rustc Runtime(PostCleanup) MIR via mir_drops_elaborated_and_"
            "const_checked before Steal<Body> (-Z mir-preserve-ub)"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "Frame-relative path lens MirVal.refVal(frameId, localIdx, "
                "proj, mutability) with localGens generation check and "
                "immediate root-tree writeback (resolvePlace / writePlace); "
                "fails closed on escaping return refs (returnRefsOk)"
            ),
            "stage3_proof_encoding": (
                "Plan-guided shallow functional translation (LoanEntry with "
                "backward function SymVal -> List SymVal) for non-aliasing "
                "safe borrows; direct path-lens or OwnLoc view reasoning for "
                "unsafe/atomic code"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Stage 2 Memory.lean supports AtomicLoc / non-atomic OwnLoc "
                "timestamped locations; arbitrary sub-object pointer offset "
                "aliasing deferred to byte-addressed AllocId store"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Unstructured first-order basic-block CFG in Stage 2 TCB "
                "(Terminator.goto, Terminator.switchInt); PC canonicalized "
                "to (block := target, stmtIdx := 0) on jump"
            ),
            "join_and_loop_strategy": (
                "Stage 3 in-place dead-local canonicalization (lowerBody / "
                "canonicalizeLocals) or finite-support spine rebuild "
                "(canonMemUpTo) + cut-point induction (wpCut / ExecNormal) "
                "with zero Stage 2 TCB expansion"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Hybrid polymorphic MirBody (MirTy.param idx, MirBody.subst, "
                "evalTyByteSize over tySizes) gated by two-stage PME "
                "admission: ConstsTotal (universal well-formedness) and "
                "MonoAdmitted (per-instantiation ConstSucceeds)"
            ),
            "next_tcb_extensions": [
                "tyAligns alongside tySizes for alignment-sensitive PMEs",
                "CallTarget.traitMethod / dictionary BodyId dispatch",
                "Associated constants in array lengths and transmute checks",
            ],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Hybrid structural MirVal (.usize, .bool, .unit, .adt, .bytes,"
                " .uninit) + paddingBytes and extractTransmuteBits / "
                "constructTransmuteVal; rejects uninit/ref/non-pub-safe ADT "
                "transmutation"
            ),
            "zerocopy_boundary": (
                "Structural MirVal.adt + paddingBytes == 0 suffices for "
                "padding-free IntoBytes/FromBytes; bit-validity masks or "
                "List AbstractByte needed for niche enums and union overlays"
            ),
        },
    },
    "charon_aeneas": {
        "display_name": "Charon + Aeneas",
        "extraction_boundary": (
            "Charon extracts rustc MIR into ULLBC (unstructured) and "
            "reconstructs structured LLBC (if/loop/switch)"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "No in-prover operational MIR TCB; trusts Charon MIR->LLBC "
                "and Aeneas symbolic borrow-projector interpreter "
                "(avalues/aloans/aproj)"
            ),
            "stage3_proof_encoding": (
                "Pure functional Result alpha monad with synthesized backward "
                "functions that thread updated borrowed values back to owners "
                "when loan regions end"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Targets safe Rust; raw pointer provenance, pointer arithmetic,"
                " and UnsafeCell outside core pure translation"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "ULLBC unstructured basic blocks reconstructed into LLBC "
                "structured statements (InterpJoin.ml / "
                "InterpLoopsFixedPoint.ml)"
            ),
            "join_and_loop_strategy": (
                "Abstract environment join (join_ctxs) unifying loans and "
                "fresh symbolic values at joins; fixed-point environment "
                "computation for loops lowered to Lean 4 partial_fixpoint"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Explicit dictionary-passing structures in Lean 4 carrying "
                "associated types, associated constants, parent-trait "
                "clauses, and method implementations"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Pure algebraic datatypes and fixed-width machine scalars "
                "(USize, U32); no byte-level representation, padding bytes, "
                "or uninitialized memory in translated terms"
            ),
            "zerocopy_boundary": (
                "Cannot directly model transmute, padding bytes, or "
                "MaybeUninit without external axiomatization"
            ),
        },
    },
    "creusot": {
        "display_name": "Creusot (fMIR -> Coma + Pearlite)",
        "extraction_boundary": (
            "Post-borrowck MIR + Polonius/NLL borrow resolution lowered to "
            "fMIR, then Coma continuation handlers -> Why3/SMT"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "Prophetic mutable borrows (Bor { cur: *p, final: ^p, id }) "
                "in fMIR/Pearlite; resolver pass inserts final-value "
                "equalities when borrows expire"
            ),
            "stage3_proof_encoding": (
                "First-order Pearlite formulas over current (*p) and final "
                "(^p) values discharged by SMT solvers; nested reborrows "
                "update parent cur and inherit parent final"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Raw pointers and UnsafeCell modeled via trusted ghost "
                "PermCell / PtrOwn permissions axiomatized in Why3/Coma"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Unstructured fMIR blocks compiled into Coma mutual "
                "continuation handlers"
            ),
            "join_and_loop_strategy": (
                "Each Coma basic-block handler is parameterized explicitly "
                "by its modified live variables (&x), automatically Scoping "
                "out dead branch-local temporaries; loops cut by user loop "
                "invariants"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Pre-monomorphization modular verification via trait laws "
                "and refinement of trait contracts in Pearlite/Why3"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Logical mathematical/bitvector values in Why3; no native "
                "byte-level padding or representation layout semantics"
            ),
            "zerocopy_boundary": (
                "Requires axiomatized specs for byte transmutation and "
                "layout intrinsics"
            ),
        },
    },
    "refinedrust": {
        "display_name": "RefinedRust (Radium / Caesium / Iris)",
        "extraction_boundary": (
            "rustc MIR lowered by rr_frontend into Radium/Caesium executable "
            "operational semantics in Rocq/Iris"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "Explicit allocation heap (loc = block_id * Z) with "
                "separation-logic ownership and lifetime inclusion (&uniq, "
                "&shr) in Iris"
            ),
            "stage3_proof_encoding": (
                "Lithium syntax-directed separation-logic type system with "
                "borrow splitting/rejoining and place refinement types"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Full raw pointer arithmetic (loc + offset) and sub-object "
                "aliasing over byte lists in Caesium heap"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Unstructured basic-block map in Radium; frontend marks join "
                "blocks as JoinPoint vs. BleedBlock and loops via LoopInfo"
            ),
            "join_and_loop_strategy": (
                "Join blocks unify live local place types while framing or "
                "initializing dead slots; JCACHED memoizes post-join WP "
                "goals so diamond continuations are proved once"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Rocq polymorphic type representations (TypeRepr) and "
                "refinement-type trait specifications"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Explicit List val_byte (Init u8 prov | Uninit | Poison) "
                "with layout size/alignment constraints and padding "
                "preservation in Radium/Caesium"
            ),
            "zerocopy_boundary": (
                "Models byte-level padding and pointer provenance directly "
                "at the cost of an Iris separation-logic heap in every proof"
            ),
        },
    },
    "verus": {
        "display_name": "Verus (VIR -> AIR -> Z3)",
        "extraction_boundary": (
            "rustc HIR/THIR lowered to mode-checked VIR (exec / proof / spec)"
            " and erased/encoded to AIR for Z3"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "Relies on rustc borrowck for safe &mut T (evaluating old(x) "
                "and new(x) in SST); no general reborrowing or lifetime "
                "logic in VIR"
            ),
            "stage3_proof_encoding": (
                "Pure SMT value updates for simple &mut parameters; linear "
                "tracked ghost tokens (PointsTo<T>, PointsToRaw) for "
                "explicit pointer/cell ownership"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Trusted core axioms over PtrMut<T>, PointsTo<T>, and "
                "PointsToRaw (expose_provenance, with_exposed_provenance)"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Structured SST/VIR control flow lowered to acyclic passive "
                "AIR blocks with Z3 switch/assume guards"
            ),
            "join_and_loop_strategy": (
                "SSA/passive variable versioning at branches; loops cut by "
                "explicit invariants and decreases clauses checked by Z3"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Polymorphic VIR/AIR encoding with fuel-bounded recursive "
                "spec functions and trait-method broadcast axioms"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "PointsToRaw models variable-sized byte ranges combined with "
                "is_no_padding / HasResolved layout axioms"
            ),
            "zerocopy_boundary": (
                "Trusted Rust axioms govern raw byte reinterpretation rather "
                "than kernel-checked operational byte reduction"
            ),
        },
    },
    "kani": {
        "display_name": "Kani (MIR -> CBMC Goto)",
        "extraction_boundary": (
            "Monomorphized rustc Runtime(PostCleanup) MIR compiled to CBMC "
            "Goto-programs and bit-blasted to SAT/SMT"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "CBMC object-offset pointer pair (object_id, byte_offset) "
                "over bit-accurate flat byte arrays"
            ),
            "stage3_proof_encoding": (
                "Bounded symbolic execution / SAT bit-blasting over all "
                "pointer targets"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Supports arbitrary pointer offsets and unions within "
                "bounded object sizes; does not check Stacked/Tree Borrows "
                "aliasing UB"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Goto-program CFG lowered to bounded SSA via loop unwinding"
            ),
            "join_and_loop_strategy": (
                "SSA phi-multiplexing at diamond merges; bounded #[kani::"
                "unwind(N)] or experimental CBMC loop contracts"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Strictly post-monomorphization: verifies concrete "
                "#[kani::proof] harnesses after rustc monomorphization; "
                "cannot prove universally quantified generic library theorems"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Bit-exact byte arrays in CBMC; optional shadow-memory "
                "uninitialized-byte tracking (-Z uninit-checks)"
            ),
            "zerocopy_boundary": (
                "Checks concrete monomorphic instances up to unwind bounds "
                "only"
            ),
        },
    },
    "minirust": {
        "display_name": "MiniRust (Normative Operational Spec)",
        "extraction_boundary": (
            "Normative Markdown/pseudocode operational semantics and "
            "minimize MIR translator"
        ),
        "axis1_borrows_reborrows_pointers": {
            "stage2_tcb_encoding": (
                "ThinPointer (addr: Int, provenance: Option<Provenance>) "
                "over BasicMemory / Tree Borrows state machine (Reserved, "
                "Active, Frozen, Disabled + CallId protectors)"
            ),
            "stage3_proof_encoding": (
                "Reference specification only (not a proof assistant "
                "framework)"
            ),
            "raw_pointer_and_interior_mut_support": (
                "Normative model for pointer provenance, exposed addresses, "
                "UnsafeCell, and Tree Borrows permissions"
            ),
        },
        "axis2_loops_joins_canonicalization": {
            "cfg_representation": (
                "Unstructured basic-block operational machine with explicit "
                "StorageLive / StorageDead allocation and deallocation"
            ),
            "join_and_loop_strategy": (
                "Operational small-step execution only; each live local owns "
                "a distinct memory allocation until StorageDead"
            ),
        },
        "axis3_generics_traits_associated_items": {
            "polymorphism_strategy": (
                "Operates over monomorphic or layout-resolved runtime types"
            ),
            "next_tcb_extensions": [],
        },
        "axis4_bytes_padding_uninit_transmute": {
            "value_and_byte_model": (
                "Normative List<AbstractByte> (Init(u8, Option<Provenance>) "
                "| Uninit) with explicit encode/decode per type layout"
            ),
            "zerocopy_boundary": (
                "Ground-truth semantic reference for byte initialization, "
                "padding resetting, and provenance preservation"
            ),
        },
    },
}

REQUIRED_THEOREMS: tuple[str, ...] = (
    "lens_comp_laws",
    "lens_prophecy_equiv",
    "cross_frame_ref_writeback_sound",
    "escaping_ref_fails_closed",
    "aliased_backward_lenses_clobber",
    "raw_diamond_join_states_ne",
    "asymmetric_storageDead_gen_mismatch",
    "canonicalize_join_unifies",
    "execNormal_from_canonicalJoinState",
    "execNormal_diamond_joined",
    "canonicalize_preserves_return",
    "size_only_insufficient_for_ref_transmute",
    "pme_ref_transmute_sound",
    "intoBytes_iff_paddingFree",
    "padded_transmute_to_int_reads_uninit",
)


def audit_lean_file(lean_path: pathlib.Path) -> dict[str, Any]:
    """Check theorem declarations, forbidden tokens, and line lengths."""
    text = lean_path.read_text(encoding="utf-8")
    lines = text.splitlines()
    sha256 = hashlib.sha256(text.encode("utf-8")).hexdigest()

    declared_theorems = re.findall(
        r"^theorem\s+([A-Za-z0-9_']+)\b", text, flags=re.MULTILINE
    )
    missing_theorems = [
        thm for thm in REQUIRED_THEOREMS if thm not in declared_theorems
    ]

    # Strip comments before scanning for `sorry` or `axiom`.
    no_block_comments = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    code_lines = [
        re.sub(r"--.*$", "", line) for line in no_block_comments.splitlines()
    ]
    code_only = "\n".join(code_lines)

    sorry_matches = re.findall(r"\bsorry\b", code_only)
    axiom_matches = re.findall(r"\baxiom\b", code_only)
    overlong_lines = [
        {"line": idx, "length": len(line)}
        for idx, line in enumerate(lines, start=1)
        if len(line) > 80
    ]

    return {
        "file": lean_path.name,
        "sha256": sha256,
        "line_count": len(lines),
        "declared_theorems": declared_theorems,
        "missing_theorems": missing_theorems,
        "sorry_count": len(sorry_matches),
        "axiom_count": len(axiom_matches),
        "overlong_lines": overlong_lines,
        "valid": (
            not missing_theorems
            and len(sorry_matches) == 0
            and len(axiom_matches) == 0
            and len(overlong_lines) == 0
        ),
    }


def run_lean_toolchain(lean_path: pathlib.Path, toolchain: str) -> dict[str, Any]:
    """Run Lean typechecking via `anneal-lean-run` and `elan`."""
    anneal_runner = shutil.which("anneal-lean-run")
    cmd: list[str] = []
    if anneal_runner:
        cmd.extend([anneal_runner, "--mode", "file", "--concurrency", "2", "--"])
    cmd.extend(
        [
            "elan",
            "run",
            toolchain,
            "lean",
            "-DwarningAsError=true",
            str(lean_path),
        ]
    )
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    return {
        "toolchain": toolchain,
        "exit_code": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip(),
    }


def validate_matrix() -> dict[str, Any]:
    """Validate that all 7 verifiers cover all 4 axes."""
    missing_entries: list[str] = []
    for verifier_id, entry in VERIFIER_MATRIX.items():
        for axis in AXES:
            if axis not in entry or not entry[axis]:
                missing_entries.append(f"{verifier_id}:{axis}")
    return {
        "verifier_count": len(VERIFIER_MATRIX),
        "axes_count": len(AXES),
        "verifiers": list(VERIFIER_MATRIX.keys()),
        "axes": list(AXES),
        "missing_entries": missing_entries,
        "valid": len(missing_entries) == 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--run-lean",
        action="store_true",
        help="Invoke Lean v4.28.0 and v4.34.1 via anneal-lean-run",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON summary",
    )
    args = parser.parse_args()

    support_dir = pathlib.Path(__file__).resolve().parent
    lean_path = support_dir / "VerifierEncodingComparison.lean"

    matrix_res = validate_matrix()
    lean_audit = audit_lean_file(lean_path)
    toolchain_results: list[dict[str, Any]] = []

    if args.run_lean:
        for tc in ("leanprover/lean4:v4.28.0", "leanprover/lean4:v4.34.1"):
            toolchain_results.append(run_lean_toolchain(lean_path, tc))

    overall_ok = (
        matrix_res["valid"]
        and lean_audit["valid"]
        and all(r["exit_code"] == 0 for r in toolchain_results)
    )

    summary = {
        "matrix_validation": matrix_res,
        "lean_static_audit": lean_audit,
        "lean_toolchain_runs": toolchain_results,
        "overall_ok": overall_ok,
    }

    if args.json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print(
            f"Matrix validation: {matrix_res['verifier_count']} verifiers x "
            f"{matrix_res['axes_count']} axes -> "
            f"{'PASS' if matrix_res['valid'] else 'FAIL'}"
        )
        print(
            f"Lean static audit ({lean_audit['file']}): "
            f"{len(lean_audit['declared_theorems'])} theorems, "
            f"sorry={lean_audit['sorry_count']}, "
            f"axiom={lean_audit['axiom_count']}, "
            f"overlong_lines={len(lean_audit['overlong_lines'])}, "
            f"sha256={lean_audit['sha256']} -> "
            f"{'PASS' if lean_audit['valid'] else 'FAIL'}"
        )
        for run in toolchain_results:
            status = "PASS" if run["exit_code"] == 0 else "FAIL"
            print(f"Toolchain {run['toolchain']}: {status}")

    return 0 if overall_ok else 1


if __name__ == "__main__":
    sys.exit(main())
