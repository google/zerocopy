-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteBase
import Trusted.MirSemantics.Contract

/-!
# Negative Refutations for `Trusted.MirSemantics.Contract` Soundness Guards

Exercises every fail-closed contract satisfaction, signature-matching,
non-vacuity, effect-mask, and RB-tree indexing guard in
`Trusted/MirSemantics/Contract.lean`.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Safe (`isUnsafe = false`) zero-argument body returning `()` cleanly. -/
noncomputable def contractOkUnitBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::contract_ok_unit"
}

/-- Program wrapping `contractOkUnitBody`. -/
noncomputable def contractOkUnitProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractOkUnitBody]
}

/-- Safe (`isUnsafe = false`) body that executes `TerminatorKind.unreachable`.
-/
noncomputable def contractSafeUnreachableBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::contract_safe_unreachable"
}

/-- Program wrapping `contractSafeUnreachableBody`. -/
noncomputable def contractSafeUnreachableProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractSafeUnreachableBody]
}

/-- Unsafe (`isUnsafe = true`) zero-argument body that reaches `.unreachable`.
-/
noncomputable def contractUnsafeUnreachableBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := true
  identity := "guard_mutation::contract_unsafe_unreachable"
}

/-- Admitted uninhabited (`MirTy.never`) parameter body whose `ValidEntryArgs`
is empty. -/
noncomputable def contractOkNeverBody : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::contract_ok_never"
}

/-- Ill-formed `MirTy.never` parameter body failing `BodyStaticAdmitted` via an
out-of-bounds `StorageLive 9`. -/
noncomputable def contractBadNeverBody : Body := {
  argumentCount := 1
  locals := [.unit, .never]
  basicBlocks := [{ statements := [.storageLive 9], terminator := .unreachable }]
  isUnsafe := false
  identity := "guard_mutation::contract_bad_never"
}

/-- Program wrapping `contractBadNeverBody`. -/
noncomputable def contractBadNeverProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractBadNeverBody]
}

/-- Aborting safe zero-argument body under `--panic abort` without a local panic
handler: fails `.assert (const false) == true` and terminates as
`.aborted ⟨[]⟩`. -/
noncomputable def contractAbortBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{
    statements := []
    terminator := .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
      true .boundsCheck 0 .unreachable
  }]
  isUnsafe := false
  identity := "guard_mutation::contract_abort"
}

/-- Program wrapping `contractAbortBody` with `panicStrategy := .abort` and
`hasLocalPanicHandler := false`. -/
noncomputable def contractAbortProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [contractAbortBody]
}

/-- Minimal diverging single-block body (`bb0: goto bb0`). -/
noncomputable def contractLoopBody : Body := {
  argumentCount := 0
  locals := [.unit]
  basicBlocks := [{ statements := [], terminator := .goto 0 }]
  isUnsafe := false
  identity := "guard_mutation::contract_loop"
}

/-- Program wrapping `contractLoopBody`. -/
noncomputable def contractLoopProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractLoopBody]
}

private noncomputable def contractLoopInitState : State := {
  frames := [{
    defId := 0
    blockIdx := 0
    stmtIdx := 0
    locals := [.immediate (some .unit)]
  }]
  callerMem := ⟨[]⟩
  mem := entryMemory
}

/-- Body with `locals = [.unit, .bool]` and `argumentCount = 2`, isolating
`Nat.beq body.argumentCount sig.params.length` against a 1-arg signature
because `(body.locals.drop 1).take 2` still equals `[.bool]`. -/
noncomputable def contractArgCountMismatchBody : Body := {
  argumentCount := 2
  locals := [.unit, .bool]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::contract_arg_count_mismatch"
}

/-- Empty-locals body exercising `| [] => false` in
`bodyMatchesContractSignature`. -/
noncomputable def contractEmptyLocalsBody : Body := {
  argumentCount := 0
  locals := []
  basicBlocks := []
  isUnsafe := false
  identity := "guard_mutation::contract_empty_locals"
}

/-- Parameterized `bool -> ()` body for parameter-type mismatch refutation. -/
noncomputable def contractBoolParamBody : Body := {
  argumentCount := 1
  locals := [.unit, .bool]
  basicBlocks := [{ statements := [], terminator := .return_ }]
  isUnsafe := false
  identity := "guard_mutation::contract_bool_param"
}

/-- Two-body program where body `0` succeeds and body `1` diverges. -/
noncomputable def contractOkThenLoopProg : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [contractOkUnitBody, contractLoopBody]
}

private noncomputable def contractOkThenLoopState : State := {
  frames := [{
    defId := 1
    blockIdx := 0
    stmtIdx := 0
    locals := [.immediate (some .unit)]
  }]
  callerMem := ⟨[]⟩
  mem := entryMemory
}

/-- Guard `contract_effective_safety_pre_unsafe_gate`:
`FnContract.effectiveSafetyPre` ignores `safetyPre` when
`body.isUnsafe = false`, so a safe unreachable body still refutes
`BodyContractSatisfied` under `safetyPre := fun _ => False`. -/
theorem refute_contract_effective_safety_pre_unsafe_gate :
    ¬ BodyContractSatisfied contractSafeUnreachableProg 0
        contractSafeUnreachableBody {
          safetyPre := fun _ => False
          effects := EffectMask.totalNormal
        } :=
  fun hSat =>
    have hWf : WellFormed (entryProgForBody contractSafeUnreachableProg 0)
        { args := [] } :=
      (hSat.2.2 [] rfl).1 (fun hFalse => Bool.noConfusion hFalse)
    hWf.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Guard `contract_effective_behavior_pre_safety`:
`FnContract.effectiveBehaviorPre` enforces `effectiveSafetyPre` for unsafe
bodies inside `ContractPreInhabited`. -/
theorem refute_contract_effective_behavior_pre_safety :
    ¬ ContractPreInhabited contractUnsafeUnreachableBody {
      safetyPre := fun _ => False
      behaviorPre := fun _ => True
      effects := EffectMask.totalNormal
    } :=
  fun ⟨_, _, hPre⟩ => hPre.1 rfl

/-- Guard `contract_effective_behavior_pre_behavior`:
`FnContract.effectiveBehaviorPre` enforces `behaviorPre` inside
`ContractPreInhabited`. -/
theorem refute_contract_effective_behavior_pre_behavior :
    ¬ ContractPreInhabited contractOkUnitBody {
      behaviorPre := fun _ => False
      effects := EffectMask.totalNormal
    } :=
  fun ⟨_, _, hPre⟩ => hPre.2

/-- Guard `contract_safety_arg_pre_checks_pre`: `FnContract.safetyArgPre`
delegates to `c.safetyPre`. -/
theorem refute_contract_safety_arg_pre_checks_pre :
    ¬ FnContract.safetyArgPre {
      safetyPre := fun _ => False
      effects := EffectMask.totalNormal
    } [] :=
  fun hPre => hPre

/-- Guard `contract_body_satisfied_binds_body`: `BodyContractSatisfied` binds
`body` to `p.bodies[defId]`, rejecting an unrelated uninhabited stub. -/
theorem refute_contract_body_satisfied_binds_body :
    ¬ BodyContractSatisfied contractSafeUnreachableProg 0 contractOkNeverBody {
      effects := EffectMask.totalNormal
    } :=
  fun hSat =>
    Nat.noConfusion
      (Option.some.inj (congrArg (Option.map Body.argumentCount) hSat.1))

/-- Guard `contract_body_satisfied_static_admitted`: `BodyContractSatisfied`
requires `BodyStaticAdmitted` even when `ValidEntryArgs` is empty. -/
theorem refute_contract_body_satisfied_static_admitted :
    ¬ BodyContractSatisfied contractBadNeverProg 0 contractBadNeverBody {
      effects := EffectMask.totalNormal
    } :=
  fun hSat => Bool.noConfusion hSat.2.1

/-- Guard `contract_body_satisfied_enforces_safety_wf`: `BodyContractSatisfied`
requires `WellFormed` under `effectiveSafetyPre`. -/
theorem refute_contract_body_satisfied_enforces_safety_wf :
    ¬ BodyContractSatisfied contractSafeUnreachableProg 0
        contractSafeUnreachableBody {
          effects := EffectMask.totalNormal
        } :=
  fun hSat =>
    have hWf : WellFormed (entryProgForBody contractSafeUnreachableProg 0)
        { args := [] } :=
      (hSat.2.2 [] rfl).1 (fun _ => trivial)
    hWf.2 .undefined (reachesResult_of_execFault (fuel := 1) rfl)

/-- Guard `contract_body_satisfied_post_return`: `BodyContractSatisfied`
enforces `postReturn` on normal terminal returns. -/
theorem refute_contract_body_satisfied_post_return :
    ¬ BodyContractSatisfied contractOkUnitProg 0 contractOkUnitBody {
      postReturn := fun _ out => out.ret = .bool true
      effects := EffectMask.totalNormal
    } :=
  fun hSat =>
    have hRet : Val.unit = Val.bool true :=
      (hSat.2.2 [] rfl).2 ⟨fun _ => trivial, trivial⟩ |>.1
        (.returned ⟨.unit, ⟨[]⟩⟩) (behavior_of_execDone (fuel := 1) rfl)
    Val.noConfusion hRet

/-- Guard `contract_body_satisfied_forbids_abort`: `BodyContractSatisfied`
forbids `.aborted` outcomes (even under `--panic abort`). -/
theorem refute_contract_body_satisfied_forbids_abort :
    ¬ BodyContractSatisfied contractAbortProg 0 contractAbortBody {
      effects := EffectMask.partialAnyExit
    } :=
  fun hSat =>
    (hSat.2.2 [] rfl).2 ⟨fun _ => trivial, trivial⟩ |>.1
      (.aborted ⟨[]⟩) (behavior_of_execDone (fuel := 1) rfl)

/-- Guard `contract_body_satisfied_terminates`: `BodyContractSatisfied` forbids
divergence when `effects.terminates = true`. -/
theorem refute_contract_body_satisfied_terminates :
    ¬ BodyContractSatisfied contractLoopProg 0 contractLoopBody {
      effects := EffectMask.totalNormal
    } :=
  fun hSat =>
    have hDiv : Diverges (entryProgForBody contractLoopProg 0) queryEmpty :=
      ⟨contractLoopInitState, rfl, fun _ => contractLoopInitState, rfl,
        fun _ => ⟨0, rfl, rfl⟩⟩
    (hSat.2.2 [] rfl).2 ⟨fun _ => trivial, trivial⟩ |>.2 rfl hDiv

/-- Guard `contract_sig_matches_is_unsafe`: `bodyMatchesContractSignature`
rejects `isUnsafe` mismatches. -/
theorem refute_contract_sig_matches_is_unsafe :
    bodyMatchesContractSignature contractUnsafeUnreachableBody {
      isUnsafe := false
      params := []
      ret := .unit
    } = false := rfl

/-- Guard `contract_sig_matches_arg_count`: `bodyMatchesContractSignature`
enforces `Nat.beq body.argumentCount sig.params.length` independently of
`MirTy.beqList`. -/
theorem refute_contract_sig_matches_arg_count :
    bodyMatchesContractSignature contractArgCountMismatchBody {
      isUnsafe := false
      params := [.bool]
      ret := .unit
    } = false := rfl

/-- Guard `contract_sig_matches_params`: `bodyMatchesContractSignature`
rejects parameter type mismatches. -/
theorem refute_contract_sig_matches_params :
    bodyMatchesContractSignature contractBoolParamBody {
      isUnsafe := false
      params := [.int .i8 false]
      ret := .unit
    } = false := rfl

/-- Guard `contract_sig_matches_ret`: `bodyMatchesContractSignature` rejects
return type mismatches. -/
theorem refute_contract_sig_matches_ret :
    bodyMatchesContractSignature contractOkUnitBody {
      isUnsafe := false
      params := []
      ret := .bool
    } = false := rfl

/-- Guard `contract_sig_rejects_empty_locals`: `bodyMatchesContractSignature`
rejects empty `body.locals`. -/
theorem refute_contract_sig_rejects_empty_locals :
    bodyMatchesContractSignature contractEmptyLocalsBody {
      isUnsafe := false
      params := []
      ret := .unit
    } = false := rfl

/-- Guard `contract_entry_matches_identity`: `bodySatisfiesContractEntry`
binds `body.identity = e.identity`. -/
theorem refute_contract_entry_matches_identity :
    ¬ bodySatisfiesContractEntry contractOkUnitProg {
      identity := "guard_mutation::missing"
      contract := { effects := EffectMask.partialAnyExit }
      requireInhabited := false
    } :=
  fun ⟨defId, body, hGet, hId, _⟩ => by
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact Bool.noConfusion hId
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet

/-- Guard `contract_entry_checks_signature`: `bodySatisfiesContractEntry`
enforces `e.signature` agreement when supplied. -/
theorem refute_contract_entry_checks_signature :
    ¬ bodySatisfiesContractEntry contractOkUnitProg {
      identity := "guard_mutation::contract_ok_unit"
      contract := { effects := EffectMask.partialAnyExit }
      signature := some {
        isUnsafe := false
        params := []
        ret := .bool
      }
      requireInhabited := false
    } :=
  fun ⟨defId, body, hGet, _, hSig, _⟩ => by
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact Bool.noConfusion hSig
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet

/-- Guard `contract_entry_require_inhabited`: `bodySatisfiesContractEntry`
enforces `ContractPreInhabited` when `requireInhabited = true`. -/
theorem refute_contract_entry_require_inhabited :
    ¬ bodySatisfiesContractEntry contractOkUnitProg {
      identity := "guard_mutation::contract_ok_unit"
      contract := {
        behaviorPre := fun _ => False
        effects := EffectMask.totalNormal
      }
      requireInhabited := true
    } :=
  fun ⟨defId, body, hGet, _, _, _, hInhab⟩ => by
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      let ⟨_, _, hPre⟩ := hInhab rfl
      exact hPre.2
    | succ _ =>
      dsimp [Trusted.MirSemantics.getElem?] at hGet
      cases hGet

/-- Guard `contract_entries_satisfied_head`: `ContractEntriesSatisfied`
checks the head entry. -/
theorem refute_contract_entries_satisfied_head :
    ¬ ContractEntriesSatisfied contractOkUnitProg [{
      identity := "guard_mutation::missing"
      contract := { effects := EffectMask.partialAnyExit }
      requireInhabited := false
    }] :=
  fun ⟨hHead, _⟩ => refute_contract_entry_matches_identity hHead

/-- Guard `contract_entries_satisfied_tail`: `ContractEntriesSatisfied`
checks subsequent entries in the list after a valid head entry. -/
theorem refute_contract_entries_satisfied_tail :
    ¬ ContractEntriesSatisfied contractOkThenLoopProg [
      {
        identity := "guard_mutation::contract_ok_unit"
        contract := { effects := EffectMask.partialAnyExit }
        requireInhabited := false
      },
      {
        identity := "guard_mutation::contract_loop"
        contract := { effects := EffectMask.totalNormal }
        requireInhabited := false
      }
    ] :=
  fun ⟨_, hTail⟩ => by
    have hLoopEntry : bodySatisfiesContractEntry contractOkThenLoopProg {
        identity := "guard_mutation::contract_loop"
        contract := { effects := EffectMask.totalNormal }
        requireInhabited := false
      } := hTail.1
    let ⟨defId, body, hGet, hId, _, hSat, _⟩ := hLoopEntry
    cases defId with
    | zero =>
      injection hGet with hEq
      subst hEq
      exact Bool.noConfusion hId
    | succ n =>
      cases n with
      | zero =>
        injection hGet with hEq
        subst hEq
        have hDiv : Diverges (entryProgForBody contractOkThenLoopProg 1)
            queryEmpty :=
          ⟨contractOkThenLoopState, rfl, fun _ => contractOkThenLoopState, rfl,
            fun _ => ⟨0, rfl, rfl⟩⟩
        exact (hSat.2.2 [] rfl).2 ⟨fun _ => trivial, trivial⟩ |>.2 rfl hDiv
      | succ _ =>
        dsimp [Trusted.MirSemantics.getElem?] at hGet
        cases hGet

/-- Guard `contract_specs_rejects_bad_identities`: `ContractSpecs` fails
closed (`False`) when entry identities are duplicate or empty. -/
theorem refute_contract_specs_rejects_bad_identities :
    ¬ UnitTheorem {
      program := contractOkUnitProg
      specs := ContractSpecs [
        {
          identity := "guard_mutation::contract_ok_unit"
          contract := { effects := EffectMask.totalNormal }
        },
        {
          identity := "guard_mutation::contract_ok_unit"
          contract := { effects := EffectMask.totalNormal }
        }
      ]
    } :=
  fun hUnit => Bool.noConfusion hUnit.2.2.2.2.2.2.2.1

/-- Guard `contract_specs_safety_dispatch`: `ContractSpecs.safety` applies the
matching entry's `safetyArgPre`. -/
theorem refute_contract_specs_safety_dispatch :
    ¬ (ContractSpecs [{
      identity := "guard_mutation::contract_ok_unit"
      contract := {
        safetyPre := fun _ => False
        effects := EffectMask.totalNormal
      }
    }]).safety "guard_mutation::contract_ok_unit" [] :=
  fun hSafe => hSafe

/-- Guard `contract_specs_checks_entries`: `ContractSpecs.property` enforces
`ContractEntriesSatisfied p entries`. -/
theorem refute_contract_specs_checks_entries :
    ¬ (ContractSpecs [{
      identity := "guard_mutation::missing"
      contract := { effects := EffectMask.partialAnyExit }
      requireInhabited := false
    }]).property contractOkUnitProg :=
  fun ⟨_, hEntries⟩ => refute_contract_entries_satisfied_head hEntries

end GuardMutation
