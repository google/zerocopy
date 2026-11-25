-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:mir_semantics
prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Control.Except
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.OperandMachine
import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Place
import Miri.Interpreter.Rvalue
import Miri.Interpreter.Discriminant
import Miri.Interpreter.Step
import Miri.Interpreter.ControlFlow
import Trusted.MirAst
import Trusted.MirModel
import Trusted.MirSemantics
import Trusted.Correspondence.Codec
import Trusted.Correspondence.State
import Trusted.Correspondence.Config
import Trusted.Correspondence.Eval
import Trusted.Correspondence.Simulation
import Trusted.Correspondence.CanaryFixtures

namespace Trusted.Correspondence

open Trusted.MirAst Trusted.MirSemantics

/-!
# MIR Correspondence Specification (`Trusted.Correspondence`)

**HUMAN COMPREHENSION PRIORITY:**
This module states the top-level MIR correspondence theorems
(`CorrespondenceClaim`, `CorrespondenceAtChoicesClaim`), bidirectional
fault-equivalence theorems (`FaultEquivalenceClaim`,
`FaultEquivalenceAtChoicesClaim`), the Miri move-deinitialization wiring
theorem (`MiriMoveDeinitWiringClaim`), and the one-to-one simulation invariant
(`SimulationInv`) together with all of their adapter definitions. Because this
file is the human-audited specification bridge between `Trusted.MirSemantics`
($M_{\text{anneal}}$) and `vendor/lean-miri/` ($M_{\text{ref}}$), **human
comprehension takes priority over every other concern** across these claims and
all of their transitive dependencies (`Trusted.Correspondence`,
`Trusted.MirSemantics`, and `Trusted.MirAst`).

This module defines five components:

1. **Reference-indexed MIR syntax (`RefProg`):** Mirrors `Miri.MIR.Syntax` by
   replacing inline structural `MirTy` values with `TyId := Nat` indices into a
   single deduplicated program type table `RefProg.types : List MirTy`, while
   carrying explicit `pointerWidthBits : Nat`, `mirProfileVersion : Nat`, and
   `scope : VerificationScope`.
2. **Canonical type-interning codec (`encodeProg` / `decodeProg`):** Interns
   every structural `MirTy` in bottom-up topological order and provides an
   unconditional left-inverse decoder `decodeProg`.
3. **Direct `Miri.Interpreter.ExecutionMachine.step` reference semantics
   ($M_{\text{ref}}$):** Wraps real `Miri.Interpreter.MachineHooks.State Unit
   RefUser` in `RefState`, allocates the caller-owned return place `retPlace`
   in `Miri.Memory.MemoryState` (`refInitMemoryAndRetPlace`), lowers each
   `RefBody` to a real `Miri.MIR.Body` (`toMiriBody`), and drives every
   statement and terminator directly through
   `Miri.Interpreter.ExecutionMachine.step (refExecutionConfig rp) refLimits c
   rs.miri` (`vendor/lean-miri`, pinned at `proofs-rs/lean-miri` commit
   `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `miri` commit
   `7fa591d7d4dd9af8154becbc8332f8096f8323b1`, `rustc` commit
   `8144389c895da997dbdecaa635e41d6a50be6ffd`) with opt-in runtime move
   deinitialization (`deinitMovedPlace := true`) and shallow validation
   (`ValidityMemory.bind` -> `ValidityVisitor.validatePlace`).
4. **Top-level correspondence claims (38 locked Pass 2 claims):** States both
   aggregate (`CorrespondenceClaim`, `FaultEquivalenceClaim`) and
   choice-coupled (`CorrespondenceAtChoicesClaim`,
   `FaultEquivalenceAtChoicesClaim`) correspondence and fault equivalence,
   together with `RefStepSoundForAllowedStepClaim` (tying every non-exhausted
   `RefStep` transition to `RefAllowedStep` / `ExecutionMachine.AllowedStep`),
   `MiriMoveDeinitWiringClaim` (covering both `OperandMachine.evalOperand` and
   `LocalAccess.evalOperand`), `BytesCodecMatchesMiriClaim` (pinning
   $M_{\text{anneal}}$'s byte codec against `lean-miri`'s `Allocation`
   scalar accesses), the 6 codec claims, the 11 simulation/uniqueness claims,
   and canaries `D6`–`D17`.
5. **Fail-closed target, profile, and stack shape:** `initRefState` rejects
   non-64-bit targets, non-v1 MIR profiles, non-empty `callerMem`, out-of-bounds
   storage markers, ill-typed `Discriminant` and `Cast` destinations, and
   unsupported local types, and starts the real `ExecutionMachine` stack with
   the single entry frame (`returnContinuation := .stop false`,
   `returnPlace := .memory retPlace`).
-/

/-! ## Trusted Top-Level Correspondence and Canary Claims -/

/-- Trusted statement of the correspondence theorem between
$M_{\text{anneal}}$ (`Trusted.MirSemantics`) and $M_{\text{ref}}$
(`Trusted.Correspondence`). For every well-formed `(p, q)`:
1. `encodeProg p` is well-formed in $M_{\text{ref}}$ under every step budget
   (UB transfer);
2. both machines exhibit exactly the same terminal behaviors; and
3. `(p, q)` diverges in $M_{\text{anneal}}$ if and only if `encodeProg p`
   diverges in $M_{\text{ref}}$. -/
def CorrespondenceClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q →
    RefWellFormed (encodeProg p) q ∧
    (∀ (out : TerminalOut),
      Behavior p q out ↔ RefBehavior (encodeProg p) q out) ∧
    (Diverges p q ↔ RefDiverges (encodeProg p) q)

/-- Trusted statement of bidirectional fault equivalence for all
`k : FaultKind` (`.undefined` ↔ `.ub` and `.unsupported` ↔ `.blocked`). -/
def FaultEquivalenceClaim : Prop :=
  ∀ (p : Program) (q : Query) (k : FaultKind),
    ReachesResult p q (.fault k) ↔
    ∃ maxSteps,
      RefReachesOutcome (encodeProg p) q maxSteps (faultToRefOutcome k)

/-- Unconditional choice-coupled correspondence claim across every `(p, q)`
(not gated on `WellFormed p q`), preventing cross-branch outcome permutation
when nondeterministic choices are introduced:
1. UB transfer (`WellFormed p q → RefWellFormed (encodeProg p) q`);
2. unconditional forward totality across all valid finite prefixes
   (`RefValidPrefixAtChoices → ValidPrefixAtChoices`);
3. choice-coupled terminal behavior simulation
   (`RefBehaviorAtChoices → BehaviorAtChoices`); and
4. choice-coupled divergence simulation
   (`RefDivergesAtChoices → DivergesAtChoices`). -/
def CorrespondenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    (WellFormed p q → RefWellFormed (encodeProg p) q) ∧
    (∀ (choices : List Choice),
      RefValidPrefixAtChoices (encodeProg p) q choices →
        ValidPrefixAtChoices p q choices) ∧
    (∀ (choices : List Choice) (out : TerminalOut),
      RefBehaviorAtChoices (encodeProg p) q choices out →
        BehaviorAtChoices p q choices out) ∧
    (∀ (choiceStream : Nat → Choice),
      RefDivergesAtChoices (encodeProg p) q choiceStream →
        DivergesAtChoices p q choiceStream)

/-- Unconditional choice-coupled bidirectional fault equivalence for all
`(p, q, choices, k : FaultKind)`. -/
def FaultEquivalenceAtChoicesClaim : Prop :=
  ∀ (p : Program) (q : Query) (choices : List Choice) (k : FaultKind),
    ReachesResultAtChoices p q choices (.fault k) ↔
    ∃ maxSteps : Nat,
      RefReachesOutcomeAtChoices (encodeProg p) q choices maxSteps
        (faultToRefOutcome k)

/-- Trusted statement verifying the direct consumer-side wiring of
`Miri.Interpreter.ExecutionMachine.step` (`Miri.Interpreter.Step.step` over
`Miri.Interpreter.ExecutionMachine.stepHooks`) and `deinitMovedPlace` in
`vendor/lean-miri` (`ExecutionMachine.withValidation`,
`ExecutionMachine.operandHooks`, `OperandMachine.evalOperand`—the live operand
path executed by `evalRefStep`—and `LocalAccess.evalOperand`,
`MachineHooks.{recordPendingMoveDeinit,takeLastPendingMoveDeinit}`, and
`Call.deinitInPlaceArg`). -/
def MiriMoveDeinitWiringClaim : Prop :=
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits)
      (c : C)
      (state : Miri.Interpreter.MachineHooks.State K U),
    Miri.Interpreter.ExecutionMachine.step cfg limits c state =
      let (state', out) := Miri.Interpreter.Step.step
        (Miri.Interpreter.ExecutionMachine.stepHooks cfg limits) c
        { state with
          machine := { state.machine with pendingMoveDeinit := false } }
      ( { state' with
          machine := { state'.machine with pendingMoveDeinit := false } },
        out )) ∧
  (∀ {K U C O X Host : Type} [DecidableEq K]
      (cfg : Miri.Interpreter.ExecutionMachine.Config K U C O X Host)
      (limits : Miri.Interpreter.ExecutionMachine.Limits),
    cfg.deinitMovedPlace = true →
    (Miri.Interpreter.ExecutionMachine.withValidation
        cfg limits).access.deinitMovedPlace = true ∧
    (Miri.Interpreter.ExecutionMachine.operandHooks
        cfg).deinitMovedPlace = true) ∧
  (∀ {K U C : Type}
      (hooks : Miri.Interpreter.OperandMachine.Hooks K U C)
      (c : C) (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (state : Miri.Interpreter.MachineHooks.State K U),
    hooks.deinitMovedPlace = false →
    Miri.Interpreter.OperandMachine.evalOperand hooks c
        (.Move ⟨localId, Array.empty⟩) known state =
      Miri.Interpreter.OperandMachine.evalPlaceToOp hooks c
        ⟨localId, Array.empty⟩ known state) ∧
  (∀ {K U C : Type}
      (hooks : Miri.Interpreter.OperandMachine.Hooks K U C)
      (c : C) (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (state state₁ : Miri.Interpreter.MachineHooks.State K U)
      (frame₁ frame₂ : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
      (imm : Miri.Interpreter.Immediate Miri.Memory.Provenance)
      (layout : Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = true →
    Miri.Interpreter.OperandMachine.evalPlaceToOp hooks c
        ⟨localId, Array.empty⟩ known state =
      .ok ⟨.immediate imm, layout⟩ state₁ →
    state₁.stack.currentFrame? = some frame₁ →
    state₁.stack.frames.isEmpty = false →
    frame₁.replaceLocalValue localId
        (.live (if layout.layout.isZst then .immediate imm
          else .immediate .uninit)) =
      .ok frame₂ →
    Miri.Interpreter.OperandMachine.evalOperand hooks c
        (.Move ⟨localId, Array.empty⟩) known state =
      .ok ⟨.immediate imm, layout⟩
        { state₁ with
          stack := ⟨state₁.stack.frames.pop.push frame₂⟩ }) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame : Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = false →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known) ∧
  (∀ {Prov Extra State : Type}
      (hooks : Miri.Interpreter.LocalAccessHooks Prov Extra State)
      (frame frame₁ frame₂ :
        Miri.Interpreter.Frame Prov Miri.Interpreter.LocalLayout Extra)
      (state state₁ : State)
      (localId : Miri.MIR.LocalId)
      (known : Option Miri.Interpreter.LocalLayout)
      (imm : Miri.Interpreter.Immediate Prov)
      (layout : Miri.Interpreter.LocalLayout),
    hooks.deinitMovedPlace = true →
    Miri.Interpreter.evalPlaceToOp hooks frame state
        ⟨localId, Array.empty⟩ known =
      ⟨frame₁, state₁, .ok ⟨.immediate imm, layout⟩⟩ →
    frame₁.replaceLocalValue localId
        (.live (if layout.layout.isZst then .immediate imm
          else .immediate .uninit)) =
      .ok frame₂ →
    Miri.Interpreter.evalOperand hooks frame state
        (.Move ⟨localId, Array.empty⟩) known =
      ⟨frame₂, state₁, .ok ⟨.immediate imm, layout⟩⟩) ∧
  (∀ {K U : Type}
      (m : Miri.Interpreter.MachineHooks.MachineState K U) (isMove : Bool),
    (Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit
       (Miri.Interpreter.MachineHooks.recordPendingMoveDeinit m isMove)).2 =
      isMove) ∧
  (∀ {P S C E Other Extern FnABI ArgABI : Type}
      (h : Miri.Interpreter.CallHooks P S C E Other Extern FnABI ArgABI)
      (choice : C)
      (place : Miri.Interpreter.MPlaceTy P)
      (snap : Miri.Interpreter.OpTy P),
    Miri.Interpreter.FnArg.copyFnArg (.InPlace place (some snap)) = snap ∧
    Miri.Interpreter.Call.deinitInPlaceArg h choice place (some snap) =
      Bind.bind (h.restoreInPlaceMovedBytes choice snap place)
        (fun _ => h.deinitInPlaceArgument choice place))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.decodeProg_encodeProg`. -/
def DecodeProgEncodeProgClaim : Prop :=
  ∀ (p : Program), decodeProg (encodeProg p) = some p

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeProg_types_canonical`. -/
def EncodeProgTypesCanonicalClaim : Prop :=
  ∀ (p : Program), typesAreCanonical (encodeProg p).types = true

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_no_dormant_noops`. -/
def EncodeStmtNoDormantNoopsClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind),
    encodeStmt ts s = .nop ↔ s = .nop

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_binaryOp_iff`. -/
def EncodeRvalueBinaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : BinOp) (l' r' : RefOperand),
    encodeRvalue ts rv = .binaryOp op l' r' ↔
      ∃ l r : Operand, rv = .binaryOp op l r ∧
        encodeOperand ts l = l' ∧ encodeOperand ts r = r'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeRvalue_unaryOp_iff`. -/
def EncodeRvalueUnaryOpIffClaim : Prop :=
  ∀ (ts : List MirTy) (rv : Rvalue) (op : UnOp) (o' : RefOperand),
    encodeRvalue ts rv = .unaryOp op o' ↔
      ∃ o : Operand, rv = .unaryOp op o ∧ encodeOperand ts o = o'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.encodeStmt_assign_iff`. -/
def EncodeStmtAssignIffClaim : Prop :=
  ∀ (ts : List MirTy) (s : StatementKind) (dst' : RefPlace) (rv' : RefRvalue),
    encodeStmt ts s = .assign dst' rv' ↔
      ∃ (dst : Place) (rv : Rvalue), s = .assign dst rv ∧
        encodePlace ts dst = dst' ∧ encodeRvalue ts rv = rv'

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.state_unique_of_simulationInv`. -/
def StateUniqueOfSimulationInvClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s₁ s₂ : State} {rs : RefState},
    SimulationInv rp p s₁ rs → SimulationInv rp p s₂ rs → s₁ = s₂

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refState_unique_of_simulationInv`.

With multi-frame states, `SimulationInv` no longer pins two pieces of
`lean-miri` bookkeeping that it pinned for a single frame:
`refTopRelevanceValid` admits both `none` and `some 0` for the
`topUserRelevantFrame` thread cache (part of `machine.threads`) when one frame
is live, and per-frame local `layout` caches may be filled or
empty. Uniqueness is therefore stated up to equal `machine.threads` and equal
per-frame `layout.isSome` shapes, in addition to equal step counters and
control state. This is weaker than the single-frame form, which needed only
the step counters and control state. -/
def RefStateUniqueOfSimulationInvClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs₁ rs₂ : RefState},
    SimulationInv rp p s rs₁ → SimulationInv rp p s rs₂ →
    rs₁.stepsExecuted = rs₂.stepsExecuted →
    rs₁.maxSteps = rs₂.maxSteps →
    rs₁.miri.machine.user.control = rs₂.miri.machine.user.control →
    rs₁.miri.machine.threads = rs₂.miri.machine.threads →
    (rs₁.miri.stack.frames.map
        (fun fr => fr.locals.map (fun l => l.layout.isSome))) =
      (rs₂.miri.stack.frames.map
        (fun fr => fr.locals.map (fun l => l.layout.isSome))) →
    rs₁ = rs₂

/-- Trusted claim for `Anneal.MirCorrespondenceProof.initRefState_sim`. -/
def InitRefStateSimClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {q : Query} (maxSteps : Nat),
    decodeProg rp = some p →
    (∀ k, initState p q = .error k → initRefState rp q maxSteps = .error k) ∧
    (∀ s₀, initState p q = .ok s₀ →
      ∃ rs₀, initRefState rp q maxSteps = .ok rs₀ ∧
        SimulationInv rp p s₀ rs₀ ∧
        rs₀.stepsExecuted = 0 ∧
        rs₀.maxSteps = maxSteps)

/-- Trusted claim for `Anneal.MirCorrespondenceProof.evalRefStep_eq`. -/
def EvalRefStepEqClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs : RefState}
    {f : FrameState} {callers : List FrameState} {body : Body}
    {rbody : RefBody},
    decodeProg rp = some p →
    SimulationInv rp p s rs →
    s.frames = f :: callers →
    activeFrameBody p f = some body →
    activeRefFrameBody rp f = some rbody →
    Nat.blt rs.stepsExecuted rs.maxSteps = true →
    ∀ (c : Choice),
      evalRefStep rp c rs =
        stepResultToRefOutcome (mapStepRes rp body rbody f rs
          (evalStep p c s))

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refStep`. -/
def SimOfRefStepClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s : State} {rs rs' : RefState},
    decodeProg rp = some p →
    SimulationInv rp p s rs →
    RefStep rp rs (.running rs') →
    ∃ s' : State, Step p s (.step s') ∧ SimulationInv rp p s' rs'

/-- Trusted claim for `Anneal.MirCorrespondenceProof.sim_of_refReaches`. -/
def SimOfRefReachesClaim : Prop :=
  ∀ {rp : RefProg} {p : Program} {s₀ : State} {rs₀ rs : RefState},
    decodeProg rp = some p →
    SimulationInv rp p s₀ rs₀ →
    RefReaches rp rs₀ rs →
    ∃ s : State, Reaches p s₀ s ∧ SimulationInv rp p s rs

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refWellFormed_of_wellFormed`. -/
def RefWellFormedOfWellFormedClaim : Prop :=
  ∀ (p : Program) (q : Query),
    WellFormed p q → RefWellFormed (encodeProg p) q

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refBehavior_of_behavior`. -/
def RefBehaviorOfBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out → RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_of_refBehavior`. -/
def BehaviorOfRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    RefBehavior (encodeProg p) q out → Behavior p q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.behavior_iff_refBehavior`. -/
def BehaviorIffRefBehaviorClaim : Prop :=
  ∀ (p : Program) (q : Query) (out : TerminalOut),
    Behavior p q out ↔ RefBehavior (encodeProg p) q out

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.diverges_iff_refDiverges`. -/
def DivergesIffRefDivergesClaim : Prop :=
  ∀ (p : Program) (q : Query),
    Diverges p q ↔ RefDiverges (encodeProg p) q

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D6_use_after_move_ub`. -/
def CanaryD6UseAfterMoveUbClaim : Prop :=
  ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .unsupported) ∧
  ¬ WellFormed progUseAfterMoveD6 queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progUseAfterMoveD6)
    queryU32_42 maxSteps .ub)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7a_binop_copy_then_move_ok`. -/
def CanaryD7aBinopCopyThenMoveOkClaim : Prop :=
  WellFormed progBinOpCopyThenMoveD7a queryU32_42 ∧
  Behavior progBinOpCopyThenMoveD7a queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 ∧
  RefBehavior (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
    (.returned ⟨u32Val 84, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7b_binop_move_then_copy_ub`. -/
def CanaryD7bBinopMoveThenCopyUbClaim : Prop :=
  ReachesResult progBinOpMoveThenCopyD7b queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenCopyD7b queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenCopyD7b queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenCopyD7b)
    queryU32_42 maxSteps .ub)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D7c_binop_move_then_move_ub`. -/
def CanaryD7cBinopMoveThenMoveUbClaim : Prop :=
  ReachesResult progBinOpMoveThenMoveD7c queryU32_42 (.fault .undefined) ∧
  ¬ ReachesResult progBinOpMoveThenMoveD7c queryU32_42
    (.fault .unsupported) ∧
  ¬ WellFormed progBinOpMoveThenMoveD7c queryU32_42 ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progBinOpMoveThenMoveD7c)
    queryU32_42 maxSteps .ub)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D8_self_move_ok`. -/
def CanaryD8SelfMoveOkClaim : Prop :=
  WellFormed progSelfMoveD8 queryU32_42 ∧
  Behavior progSelfMoveD8 queryU32_42 (.returned ⟨u32Val 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progSelfMoveD8) queryU32_42 ∧
  RefBehavior (encodeProg progSelfMoveD8) queryU32_42
    (.returned ⟨u32Val 42, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D9_move_unit_zst_ok`. -/
def CanaryD9MoveUnitZstOkClaim : Prop :=
  WellFormed progMoveUnitZstD9 queryEmpty ∧
  Behavior progMoveUnitZstD9 queryEmpty (.returned ⟨.unit, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progMoveUnitZstD9) queryEmpty ∧
  RefBehavior (encodeProg progMoveUnitZstD9) queryEmpty
    (.returned ⟨.unit, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D10_add_unchecked_overflow_ub`. -/
def CanaryD10AddUncheckedOverflowUbClaim : Prop :=
  ReachesResult progAddUncheckedU32 queryU32MaxPlusOne
    (.fault .undefined) ∧
  ¬ WellFormed progAddUncheckedU32 queryU32MaxPlusOne ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progAddUncheckedU32)
    queryU32MaxPlusOne maxSteps .ub) ∧
  Behavior progAddU32 queryU32MaxPlusOne (.returned ⟨u32Val 0, ⟨[]⟩⟩) ∧
  RefBehavior (encodeProg progAddU32) queryU32MaxPlusOne
    (.returned ⟨u32Val 0, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D11_enum_discriminant_and_const_ok`:
exercises explicit-repr `#[repr(u8)]` non-index enum constant tag decoding +
`u8` `Rvalue.discriminant` and signed `i8` -> `isize` tag sign-extension in
both $M_{\text{anneal}}$ and $M_{\text{ref}}$ (`Miri.Interpreter.Discriminant`).
-/
def CanaryD11EnumDiscriminantAndConstOkClaim : Prop :=
  WellFormed progEnumExplicitReprU8 queryEmpty ∧
  Behavior progEnumExplicitReprU8 queryEmpty
    (.returned ⟨u8Val 20, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progEnumExplicitReprU8) queryEmpty ∧
  RefBehavior (encodeProg progEnumExplicitReprU8) queryEmpty
    (.returned ⟨u8Val 20, ⟨[]⟩⟩) ∧
  WellFormed progEnumSignedTagIsize queryEmpty ∧
  Behavior progEnumSignedTagIsize queryEmpty
    (.returned ⟨scalarNatVal .isize true (Nat.pow 2 64 - 1), ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progEnumSignedTagIsize) queryEmpty ∧
  RefBehavior (encodeProg progEnumSignedTagIsize) queryEmpty
    (.returned ⟨scalarNatVal .isize true (Nat.pow 2 64 - 1), ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D12_zst_enum_move_and_discr_ok`:
exercises 1-variant inhabited ZST enum implicit return, non-deinitializing
`Operand.move`, `ConstLit.zeroSized`, and `Variants.Single 0`
`Rvalue.discriminant` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$. -/
def CanaryD12ZstEnumMoveAndDiscrOkClaim : Prop :=
  WellFormed progZstSingleEnumImplicitRet queryEmpty ∧
  Behavior progZstSingleEnumImplicitRet queryEmpty
    (.returned ⟨.enumVal canarySingleZstEnumTy 0, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progZstSingleEnumImplicitRet) queryEmpty ∧
  RefBehavior (encodeProg progZstSingleEnumImplicitRet) queryEmpty
    (.returned ⟨.enumVal canarySingleZstEnumTy 0, ⟨[]⟩⟩) ∧
  WellFormed progZstSingleEnumMoveAndDiscr queryEmpty ∧
  Behavior progZstSingleEnumMoveAndDiscr queryEmpty
    (.returned ⟨scalarNatVal .isize true 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progZstSingleEnumMoveAndDiscr) queryEmpty ∧
  RefBehavior (encodeProg progZstSingleEnumMoveAndDiscr) queryEmpty
    (.returned ⟨scalarNatVal .isize true 42, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D13_enum_invalid_tag_and_uninit_ub`:
exercises invalid constant scalar tag `1` on `ReprU8 { A = 10, B = 20 }` and
reading `Rvalue.discriminant` from an uninitialized scalar-tagged enum local,
both faulting with `.undefined` / `.ub` in $M_{\text{anneal}}$ and
$M_{\text{ref}}$. -/
def CanaryD13EnumInvalidTagAndUninitUbClaim : Prop :=
  ReachesResult progEnumInvalidTagConstUb queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progEnumInvalidTagConstUb queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progEnumInvalidTagConstUb queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progEnumInvalidTagConstUb)
    queryEmpty maxSteps .ub) ∧
  ReachesResult progEnumUninitDiscrUb queryEmpty (.fault .undefined) ∧
  ¬ ReachesResult progEnumUninitDiscrUb queryEmpty (.fault .unsupported) ∧
  ¬ WellFormed progEnumUninitDiscrUb queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progEnumUninitDiscrUb)
    queryEmpty maxSteps .ub)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D14_char_cmp_and_switch_ok`: in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$,
1. `'b'.cmp('a')` (`BinOp.cmp` on `char`,
   `Miri.Interpreter.IntegerOps.binaryChar`) returns
   `core::cmp::Ordering::Greater` through the return place;
2. `Rvalue.discriminant` of `(-1i8).cmp(1i8)` (`Ordering::Less`) returns
   `-1i8` (raw bits `255`); and
3. `switchInt` on the `char` `'a'` takes its matching case and returns
   `1u32`. -/
def CanaryD14CharCmpAndSwitchOkClaim : Prop :=
  WellFormed (mkBinOpProg .cmp .ordering .char .char)
    { args := [charVal 98, charVal 97] } ∧
  Behavior (mkBinOpProg .cmp .ordering .char .char)
    { args := [charVal 98, charVal 97] }
    (.returned ⟨.ordering .greater, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkBinOpProg .cmp .ordering .char .char))
    { args := [charVal 98, charVal 97] } ∧
  RefBehavior (encodeProg (mkBinOpProg .cmp .ordering .char .char))
    { args := [charVal 98, charVal 97] }
    (.returned ⟨.ordering .greater, ⟨[]⟩⟩) ∧
  WellFormed (mkCmpDiscriminantProg i8Ty) { args := [i8Val 255, i8Val 1] } ∧
  Behavior (mkCmpDiscriminantProg i8Ty) { args := [i8Val 255, i8Val 1] }
    (.returned ⟨i8Val 255, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkCmpDiscriminantProg i8Ty))
    { args := [i8Val 255, i8Val 1] } ∧
  RefBehavior (encodeProg (mkCmpDiscriminantProg i8Ty))
    { args := [i8Val 255, i8Val 1] } (.returned ⟨i8Val 255, ⟨[]⟩⟩) ∧
  WellFormed progCharSwitch { args := [charVal 97] } ∧
  Behavior progCharSwitch { args := [charVal 97] }
    (.returned ⟨u32Val 1, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progCharSwitch) { args := [charVal 97] } ∧
  RefBehavior (encodeProg progCharSwitch) { args := [charVal 97] }
    (.returned ⟨u32Val 1, ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D15_int_to_int_cast`: in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$ (`Miri.Interpreter.Cast.cast` and
`Miri.Interpreter.IntegerCast.cast`),
1. `-1i8 as u32` sign-extends and returns `0xFFFF_FFFF`;
2. `200u8 as char` returns `'\u{c8}'`; and
3. `300u32 as char` faults with `.unsupported` (`.blocked` in
   $M_{\text{ref}}$), because only `u8` values convert to `char`. -/
def CanaryD15IntToIntCastClaim : Prop :=
  WellFormed (mkIntToIntCastProg i8Ty u32Ty) { args := [i8Val 255] } ∧
  Behavior (mkIntToIntCastProg i8Ty u32Ty) { args := [i8Val 255] }
    (.returned ⟨u32Val 4294967295, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkIntToIntCastProg i8Ty u32Ty))
    { args := [i8Val 255] } ∧
  RefBehavior (encodeProg (mkIntToIntCastProg i8Ty u32Ty))
    { args := [i8Val 255] } (.returned ⟨u32Val 4294967295, ⟨[]⟩⟩) ∧
  WellFormed (mkIntToIntCastProg u8Ty .char) { args := [u8Val 200] } ∧
  Behavior (mkIntToIntCastProg u8Ty .char) { args := [u8Val 200] }
    (.returned ⟨charVal 200, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg (mkIntToIntCastProg u8Ty .char))
    { args := [u8Val 200] } ∧
  RefBehavior (encodeProg (mkIntToIntCastProg u8Ty .char))
    { args := [u8Val 200] } (.returned ⟨charVal 200, ⟨[]⟩⟩) ∧
  ReachesResult (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
    (.fault .unsupported) ∧
  ¬ ReachesResult (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
    (.fault .undefined) ∧
  ¬ WellFormed (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg (mkIntToIntCastProg u32Ty .char))
    { args := [u32Val 300] } maxSteps .blocked)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D16_with_overflow_ok`: in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$
(`Miri.Interpreter.IntegerOps.binary` and `ScalarOps.finish`'s
`BackendRepr.ScalarPair` result), `BinOp.addWithOverflow` on
`(255u8, 1u8)` returns `(0, true)` and `BinOp.subWithOverflow` on
`(-128i8, 1i8)` returns `(127, true)` through the return place. -/
def CanaryD16WithOverflowOkClaim : Prop :=
  WellFormed (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] } ∧
  Behavior (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty)
    { args := [u8Val 255, u8Val 1] }
    (.returned ⟨.tuple [u8Val 0, .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed
    (encodeProg (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty))
    { args := [u8Val 255, u8Val 1] } ∧
  RefBehavior
    (encodeProg (mkBinOpProg .addWithOverflow (overflowPairTy u8Ty) u8Ty u8Ty))
    { args := [u8Val 255, u8Val 1] }
    (.returned ⟨.tuple [u8Val 0, .bool true], ⟨[]⟩⟩) ∧
  WellFormed (mkBinOpProg .subWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty)
    { args := [i8Val 128, i8Val 1] } ∧
  Behavior (mkBinOpProg .subWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty)
    { args := [i8Val 128, i8Val 1] }
    (.returned ⟨.tuple [i8Val 127, .bool true], ⟨[]⟩⟩) ∧
  RefWellFormed
    (encodeProg (mkBinOpProg .subWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty))
    { args := [i8Val 128, i8Val 1] } ∧
  RefBehavior
    (encodeProg (mkBinOpProg .subWithOverflow (overflowPairTy i8Ty) i8Ty i8Ty))
    { args := [i8Val 128, i8Val 1] }
    (.returned ⟨.tuple [i8Val 127, .bool true], ⟨[]⟩⟩)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.refStep_sound_for_allowedStep_holds`: every
non-exhausted `RefStep` transition (`.running` or `.returned`) is witnessed by
`RefAllowedStep` (instantiating `Miri.Interpreter.ExecutionMachine.AllowedStep`
with `refLimits`). -/
def RefStepSoundForAllowedStepClaim : Prop :=
  ∀ (rp : RefProg) (rs : RefState) (out : RefOutcome),
    Nat.blt rs.stepsExecuted rs.maxSteps = true →
    RefStep rp rs out →
    (∀ rs', out = .running rs' →
      RefAllowedStep rp rs.miri rs'.miri (.ok true)) ∧
    (∀ t, out = .returned t →
      ∃ miri', RefAllowedStep rp rs.miri miri' (.ok true) ∧
        miri'.stack.frames.isEmpty = true ∧
        ∃ retVal,
          refReadReturnVal miri'.machine.memory rs.retTy rs.retPlace =
            .ok retVal ∧
          t = .returned ⟨retVal, miri'.machine.user.callerMem⟩)

/-- Trusted claim for `Anneal.MirCorrespondenceProof.bytes_codec_matches_miri`:
pins $M_{\text{anneal}}$'s byte codec (`Trusted.MirSemantics.encodeVal` and
`decodeVal` at `Trusted.MirSemantics.profileTargetEndian`) against `lean-miri`'s
`Allocation.writeScalar`, `getBytesUnchecked`, `readScalar`, and `writeUninit`
on a fresh `toMiriSize w`-byte allocation under the data layout that
$M_{\text{ref}}$ uses (`RuntimeTargetDataLayout.default.base`), for every
integer width `w`, signedness `s`, and bit pattern `bits`:
0. The fresh allocation exists (`Allocation.tryNew` succeeds), so the
   remaining conjuncts are not vacuous.
1. `encodeVal` produces exactly the bytes that `writeScalar` stores for the
   scalar `miriScalar w bits`, all initialized and without provenance;
   `readScalar` reads the same scalar back; and `decodeVal` decodes those bytes
   to the same well-formed value.
2. After `writeUninit`, `readScalar` faults with `invalidUninitBytes`, and
   `decodeVal` decodes uninitialized bytes to `none`. -/
def BytesCodecMatchesMiriClaim : Prop :=
  ∀ (w : IntWidth) (s : Bool) (bits : BitVec 128),
  (∃ (rawAlloc : Miri.Memory.Allocation Miri.Memory.Provenance Unit),
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
        (toMiriSize w) Miri.ABI.Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc) ∧
  ∀ (rawAlloc : Miri.Memory.Allocation Miri.Memory.Provenance Unit),
    Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
        (toMiriSize w) Miri.ABI.Align.ONE .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok rawAlloc →
    (∃ (raw : List UInt8)
        (after : Miri.Memory.Allocation Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree),
      encodeVal profileTargetEndian (.int w s)
          (.scalar ⟨w, s, truncateBits w bits⟩) =
        .ok (raw.map (fun b => AllocByte.init b none)) ∧
      Miri.Memory.Allocation.writeScalar
          Miri.ABI.RuntimeTargetDataLayout.default.base
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w))
          (.fromScalarInt (miriScalar w bits))
          (rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
            Miri.Memory.BorTag.one (toMiriSize w))) = .ok () after ∧
      after.getBytesUnchecked
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w)) =
        .ok (Array.mk raw) ∧
      after.readScalar Miri.ABI.RuntimeTargetDataLayout.default.base
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w)) false =
        .ok (.fromScalarInt (miriScalar w bits)) ∧
      decodeVal profileTargetEndian (.int w s)
          (raw.map (fun b => AllocByte.init b none)) =
        .ok (some (.scalar ⟨w, s, truncateBits w bits⟩))) ∧
    (∃ (after : Miri.Memory.Allocation Miri.Memory.Provenance
          Miri.TreeBorrows.BorrowTree)
        (info : Option Miri.Memory.BadBytesAccess),
      Miri.Memory.Allocation.writeUninit
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w))
          (Miri.ABI.Size.ofBytes 8)
          (rawAlloc.withExtra (Miri.TreeBorrows.BorrowTree.new
            Miri.Memory.BorTag.one (toMiriSize w))) = .ok () after ∧
      after.readScalar Miri.ABI.RuntimeTargetDataLayout.default.base
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (toMiriSize w)) false =
        .error (.invalidUninitBytes info) ∧
      decodeVal profileTargetEndian (.int w s)
          (List.replicate w.byteSize .uninit) = .ok none)

/-- Trusted claim for
`Anneal.MirCorrespondenceProof.canary_D17_call_and_sysroot_call`: in both
$M_{\text{anneal}}$ and $M_{\text{ref}}$,
1. an intra-crate multi-frame `.call` returns `42u16`;
2. an in-bounds `u16::unchecked_add` `.sysrootCall` returns `42u16`; and
3. an overflowing `u16::unchecked_add` `.sysrootCall` faults with
   `.undefined` / `.ub`. -/
def CanaryD17CallAndSysrootCallClaim : Prop :=
  WellFormed progDirectCallD17 queryU16_19 ∧
  Behavior progDirectCallD17 queryU16_19
    (.returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progDirectCallD17) queryU16_19 ∧
  RefBehavior (encodeProg progDirectCallD17) queryU16_19
    (.returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) ∧
  WellFormed progSysrootUncheckedAddOkD17 queryEmpty ∧
  Behavior progSysrootUncheckedAddOkD17 queryEmpty
    (.returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) ∧
  RefWellFormed (encodeProg progSysrootUncheckedAddOkD17) queryEmpty ∧
  RefBehavior (encodeProg progSysrootUncheckedAddOkD17) queryEmpty
    (.returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) ∧
  ReachesResult progSysrootUncheckedAddUbD17 queryEmpty (.fault .undefined) ∧
  ¬ WellFormed progSysrootUncheckedAddUbD17 queryEmpty ∧
  (∃ maxSteps, RefReachesOutcome (encodeProg progSysrootUncheckedAddUbD17)
    queryEmpty maxSteps .ub)

end Trusted.Correspondence
