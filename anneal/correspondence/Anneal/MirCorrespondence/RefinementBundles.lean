-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.InitAndSim
import Anneal.MirCorrespondence.Canaries

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Safety Refinement and Bidirectional Fault-Equivalence Bundles

Zero-TCB factored correspondence bundles
(`Anneal.MirCorrespondence.RefinementBundles`) over `Trusted.Correspondence` and
`Anneal.MirCorrespondence.InitAndSim` separating the two distinct semantic
surfaces of a reference-interpreter correspondence proof:

1. **Safety refinement (`SafetyRefinementBundle` /
   `SafetyRefinementAtChoicesBundle`):** forward transfer of fault-freedom
   (`WellFormed → RefWellFormed`), backward simulation of terminal behaviors
   (`RefBehavior → Behavior`), and backward reflection of divergence
   (`RefDiverges → Diverges`)—plus choice-prefix reflection
   (`RefValidPrefixAtChoices → ValidPrefixAtChoices`, mirroring
   `CorrespondenceAtChoicesClaim`) in `SafetyRefinementAtChoicesBundle`—matching
   the backward-simulation terminology of `docs/mir-correspondence-design.md`
   and `InitAndSim`. These minimal fields alone rule out unsound acceptance of
   reference faults (`RefReachesOutcome .ub → ¬ WellFormed` and
   `RefReachesOutcome .blocked → ¬ WellFormed`) and transfer partial correctness
   (`SatisfiesPost`), valid/invalid choice prefixes, and termination
   (`¬ Diverges`) from $M_{\text{anneal}}$ to $M_{\text{ref}}$.
2. **Bidirectional fault equivalence (`BiFaultEquivBundle` /
   `BiFaultEquivAtChoicesBundle`):** exact two-way per-fault-kind correspondence
   (`.undefined ↔ .ub` and `.unsupported ↔ .blocked`), licensing both UB
   reflection (`RefReachesOutcome .ub → ReachesResult (.fault .undefined)`) and
   existential fault-refutation transfer.
3. **Strict separation:** a concrete conservative encoding mapping an always-UB
   program to `.blocked` inhabits `SafetyRefinementBundle` and
   `SafetyRefinementAtChoicesBundle` while refuting `BiFaultEquivBundle` and
   `BiFaultEquivAtChoicesBundle`.
-/

/-! ## Section 1: Minimal Safety-Refinement and Fault-Equivalence Bundles -/

/-- Minimal safety-refinement surface for an encoding `encode : Program →
RefProg`: transfers universal well-formedness forward and reflects reference
terminal behaviors and divergence backward to $M_{\text{anneal}}$. -/
structure SafetyRefinementBundle (encode : Program → RefProg) : Prop where
  wellFormed_transfer :
    ∀ (p : Program) (q : Query),
      WellFormed p q → RefWellFormed (encode p) q
  behavior_reflect :
    ∀ (p : Program) (q : Query) (out : TerminalOut),
      RefBehavior (encode p) q out → Behavior p q out
  diverges_reflect :
    ∀ (p : Program) (q : Query),
      RefDiverges (encode p) q → Diverges p q

/-- Minimal choice-coupled safety-refinement surface mirroring
`CorrespondenceAtChoicesClaim`: couples `WellFormed` transfer with backward
reflection of valid choice prefixes (`validPrefix_reflect`), terminal behaviors,
and infinite choice streams. -/
structure SafetyRefinementAtChoicesBundle
    (encode : Program → RefProg) : Prop where
  wellFormed_transfer :
    ∀ (p : Program) (q : Query),
      WellFormed p q → RefWellFormed (encode p) q
  validPrefix_reflect :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      RefValidPrefixAtChoices (encode p) q choices →
        ValidPrefixAtChoices p q choices
  behavior_reflect :
    ∀ (p : Program) (q : Query) (choices : List Choice) (out : TerminalOut),
      RefBehaviorAtChoices (encode p) q choices out →
        BehaviorAtChoices p q choices out
  diverges_reflect :
    ∀ (p : Program) (q : Query) (choiceStream : Nat → Choice),
      RefDivergesAtChoices (encode p) q choiceStream →
        DivergesAtChoices p q choiceStream

/-- Bidirectional fault-equivalence surface capturing exact two-way
correspondence of both `.undefined ↔ .ub` and `.unsupported ↔ .blocked` faults
for `encode : Program → RefProg`. -/
structure BiFaultEquivBundle (encode : Program → RefProg) : Prop where
  ub_iff :
    ∀ (p : Program) (q : Query),
      ReachesResult p q (.fault .undefined) ↔
        ∃ maxSteps : Nat, RefReachesOutcome (encode p) q maxSteps .ub
  unsupported_iff :
    ∀ (p : Program) (q : Query),
      ReachesResult p q (.fault .unsupported) ↔
        ∃ maxSteps : Nat, RefReachesOutcome (encode p) q maxSteps .blocked

/-- Choice-coupled bidirectional fault-equivalence surface for both
`.undefined ↔ .ub` and `.unsupported ↔ .blocked` along explicit choice
sequences. -/
structure BiFaultEquivAtChoicesBundle (encode : Program → RefProg) : Prop where
  ub_iff :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      ReachesResultAtChoices p q choices (.fault .undefined) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeAtChoices (encode p) q choices maxSteps .ub
  unsupported_iff :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      ReachesResultAtChoices p q choices (.fault .unsupported) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeAtChoices (encode p) q choices maxSteps .blocked

/-! ## Section 2: Safety-Refinement and Fault-Equivalence Transfer Theorems -/

/-- Universal safety and postcondition transfer requires only
`SafetyRefinementBundle`: if `SatisfiesPost p q post` holds in
$M_{\text{anneal}}$, then `encode p` is `RefWellFormed` and every reference
terminal outcome satisfies `post`. -/
theorem SafetyRefinementBundle.satisfiesPost_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementBundle encode)
    (p : Program) (q : Query) (post : TerminalOut → Prop)
    (h_sat : SatisfiesPost p q post) :
    RefWellFormed (encode p) q ∧
      ∀ out : TerminalOut, RefBehavior (encode p) q out → post out :=
  ⟨h_ref.wellFormed_transfer p q h_sat.1,
    fun out h_rbeh => h_sat.2 out (h_ref.behavior_reflect p q out h_rbeh)⟩

/-- Universal termination transfer requires only `SafetyRefinementBundle`:
absence of divergence in $M_{\text{anneal}}$ implies absence of divergence in
$M_{\text{ref}}$. -/
theorem SafetyRefinementBundle.terminates_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementBundle encode)
    (p : Program) (q : Query)
    (h_term : ¬ Diverges p q) :
    ¬ RefDiverges (encode p) q :=
  fun h_rdiv => h_term (h_ref.diverges_reflect p q h_rdiv)

/-- Contrapositive UB exclusion from `SafetyRefinementBundle` alone: any finite
step budget reaching `.ub` in $M_{\text{ref}}$ refutes `WellFormed p q` without
requiring `BiFaultEquivBundle`. -/
theorem SafetyRefinementBundle.ref_ub_not_wellFormed
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementBundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_ub : RefReachesOutcome (encode p) q maxSteps .ub) :
    ¬ WellFormed p q :=
  fun h_wf => ((h_ref.wellFormed_transfer p q h_wf) maxSteps).2.1 h_ub

/-- Contrapositive blocked-fault exclusion from `SafetyRefinementBundle` alone:
any finite step budget reaching `.blocked` in $M_{\text{ref}}$ refutes
`WellFormed p q`. -/
theorem SafetyRefinementBundle.ref_blocked_not_wellFormed
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementBundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_blk : RefReachesOutcome (encode p) q maxSteps .blocked) :
    ¬ WellFormed p q :=
  fun h_wf => ((h_ref.wellFormed_transfer p q h_wf) maxSteps).2.2 h_blk

/-- Choice-coupled invalid-prefix transfer from
`SafetyRefinementAtChoicesBundle.validPrefix_reflect`. -/
theorem SafetyRefinementAtChoicesBundle.invalidPrefix_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementAtChoicesBundle encode)
    (p : Program) (q : Query) (choices : List Choice)
    (h_inv : ¬ ValidPrefixAtChoices p q choices) :
    ¬ RefValidPrefixAtChoices (encode p) q choices :=
  fun h_rpre => h_inv (h_ref.validPrefix_reflect p q choices h_rpre)

/-- Choice-coupled termination transfer requires only
`SafetyRefinementAtChoicesBundle`. -/
theorem SafetyRefinementAtChoicesBundle.terminatesAtChoices_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementAtChoicesBundle encode)
    (p : Program) (q : Query) (choiceStream : Nat → Choice)
    (h_term : ¬ DivergesAtChoices p q choiceStream) :
    ¬ RefDivergesAtChoices (encode p) q choiceStream :=
  fun h_rdiv => h_term (h_ref.diverges_reflect p q choiceStream h_rdiv)

/-- `BiFaultEquivBundle` implies UB reflection (`RefReachesOutcome .ub →
ReachesResult (.fault .undefined)`) for any encoding. -/
theorem BiFaultEquivBundle.ub_reflect
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_ref_ub : RefReachesOutcome (encode p) q maxSteps .ub) :
    ReachesResult p q (.fault .undefined) :=
  (h_bi.ub_iff p q).2 ⟨maxSteps, h_ref_ub⟩

/-- `BiFaultEquivBundle` implies blocked-fault reflection
(`RefReachesOutcome .blocked → ReachesResult (.fault .unsupported)`). -/
theorem BiFaultEquivBundle.unsupported_reflect
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_ref_blk : RefReachesOutcome (encode p) q maxSteps .blocked) :
    ReachesResult p q (.fault .unsupported) :=
  (h_bi.unsupported_iff p q).2 ⟨maxSteps, h_ref_blk⟩

/-- Unified `FaultKind`-indexed equivalence derived from `BiFaultEquivBundle`.
-/
theorem BiFaultEquivBundle.fault_iff
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query) (k : FaultKind) :
    ReachesResult p q (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcome (encode p) q maxSteps (faultToRefOutcome k) := by
  cases k with
  | undefined => exact h_bi.ub_iff p q
  | unsupported => exact h_bi.unsupported_iff p q

/-- Construct `BiFaultEquivBundle` from any `FaultKind`-indexed equivalence. -/
theorem BiFaultEquivBundle.of_fault_iff
    (encode : Program → RefProg)
    (h_all : ∀ (p : Program) (q : Query) (k : FaultKind),
      ReachesResult p q (.fault k) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcome (encode p) q maxSteps (faultToRefOutcome k)) :
    BiFaultEquivBundle encode :=
  ⟨fun p q => h_all p q .undefined, fun p q => h_all p q .unsupported⟩

/-- Universal fault-absence reflection from `BiFaultEquivBundle`: any
`WellFormed` program is free of `.ub` and `.blocked` in $M_{\text{ref}}$ across
every step budget. -/
theorem BiFaultEquivBundle.wellFormed_no_ref_fault
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query)
    (h_wf : WellFormed p q) (maxSteps : Nat) :
    ¬ RefReachesOutcome (encode p) q maxSteps .ub ∧
      ¬ RefReachesOutcome (encode p) q maxSteps .blocked :=
  ⟨fun h_ub => h_wf.2 .undefined (h_bi.ub_reflect p q maxSteps h_ub),
    fun h_blk =>
      h_wf.2 .unsupported (h_bi.unsupported_reflect p q maxSteps h_blk)⟩

/-- Existential UB-refutation transfer from `BiFaultEquivBundle`: an
$M_{\text{anneal}}$ `.undefined` fault yields a finite step budget witnessing
`.ub` in $M_{\text{ref}}$ and refutes `RefWellFormed`. -/
theorem BiFaultEquivBundle.ub_refutation_transfer
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query)
    (h_ub : ReachesResult p q (.fault .undefined)) :
    (∃ maxSteps : Nat, RefReachesOutcome (encode p) q maxSteps .ub) ∧
      ¬ RefWellFormed (encode p) q := by
  let ⟨maxSteps, h_ref_ub⟩ := (h_bi.ub_iff p q).1 h_ub
  refine ⟨⟨maxSteps, h_ref_ub⟩, ?_⟩
  intro h_rwf
  exact (h_rwf maxSteps).2.1 h_ref_ub

/-- Existential blocked-fault transfer from `BiFaultEquivBundle`: an
$M_{\text{anneal}}$ `.unsupported` fault yields a finite step budget witnessing
`.blocked` in $M_{\text{ref}}$ and refutes `RefWellFormed`. -/
theorem BiFaultEquivBundle.unsupported_refutation_transfer
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivBundle encode)
    (p : Program) (q : Query)
    (h_unsup : ReachesResult p q (.fault .unsupported)) :
    (∃ maxSteps : Nat, RefReachesOutcome (encode p) q maxSteps .blocked) ∧
      ¬ RefWellFormed (encode p) q := by
  let ⟨maxSteps, h_ref_blk⟩ := (h_bi.unsupported_iff p q).1 h_unsup
  refine ⟨⟨maxSteps, h_ref_blk⟩, ?_⟩
  intro h_rwf
  exact (h_rwf maxSteps).2.2 h_ref_blk

/-- Choice-coupled `BiFaultEquivAtChoicesBundle` implies UB reflection along
explicit choice sequences. -/
theorem BiFaultEquivAtChoicesBundle.ub_reflect
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivAtChoicesBundle encode)
    (p : Program) (q : Query) (choices : List Choice) (maxSteps : Nat)
    (h_ref_ub :
      RefReachesOutcomeAtChoices (encode p) q choices maxSteps .ub) :
    ReachesResultAtChoices p q choices (.fault .undefined) :=
  (h_bi.ub_iff p q choices).2 ⟨maxSteps, h_ref_ub⟩

/-- Choice-coupled `BiFaultEquivAtChoicesBundle` implies blocked-fault
reflection along explicit choice sequences. -/
theorem BiFaultEquivAtChoicesBundle.unsupported_reflect
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivAtChoicesBundle encode)
    (p : Program) (q : Query) (choices : List Choice) (maxSteps : Nat)
    (h_ref_blk :
      RefReachesOutcomeAtChoices (encode p) q choices maxSteps .blocked) :
    ReachesResultAtChoices p q choices (.fault .unsupported) :=
  (h_bi.unsupported_iff p q choices).2 ⟨maxSteps, h_ref_blk⟩

/-- Unified choice-coupled `FaultKind` equivalence derived from
`BiFaultEquivAtChoicesBundle`. -/
theorem BiFaultEquivAtChoicesBundle.fault_iff
    {encode : Program → RefProg}
    (h_bi : BiFaultEquivAtChoicesBundle encode)
    (p : Program) (q : Query) (choices : List Choice) (k : FaultKind) :
    ReachesResultAtChoices p q choices (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeAtChoices (encode p) q choices maxSteps
          (faultToRefOutcome k) := by
  cases k with
  | undefined => exact h_bi.ub_iff p q choices
  | unsupported => exact h_bi.unsupported_iff p q choices

/-- Construct `BiFaultEquivAtChoicesBundle` from any choice-coupled
`FaultKind`-indexed equivalence. -/
theorem BiFaultEquivAtChoicesBundle.of_fault_iff
    (encode : Program → RefProg)
    (h_all : ∀ (p : Program) (q : Query) (choices : List Choice)
        (k : FaultKind),
      ReachesResultAtChoices p q choices (.fault k) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeAtChoices (encode p) q choices maxSteps
            (faultToRefOutcome k)) :
    BiFaultEquivAtChoicesBundle encode :=
  ⟨fun p q choices => h_all p q choices .undefined,
    fun p q choices => h_all p q choices .unsupported⟩

/-! ## Section 3: Reference-Machine (`encodeProg`) Instantiations -/

/-- Proved minimal safety-refinement bundle for `encodeProg`. -/
theorem leanMiri_safetyRefinement : SafetyRefinementBundle encodeProg :=
  ⟨refWellFormed_of_wellFormed_base,
    behavior_of_refBehavior_base,
    fun p q h_rdiv => (diverges_iff_refDiverges_base p q).2 h_rdiv⟩

/-- Proved minimal choice-coupled safety-refinement bundle for `encodeProg`. -/
theorem leanMiri_safetyRefinementAtChoices :
    SafetyRefinementAtChoicesBundle encodeProg :=
  ⟨fun p q => (correspondence_at_choices_claim_holds_base p q).1,
    fun p q => (correspondence_at_choices_claim_holds_base p q).2.1,
    fun p q => (correspondence_at_choices_claim_holds_base p q).2.2.1,
    fun p q => (correspondence_at_choices_claim_holds_base p q).2.2.2⟩

/-- Proved bidirectional fault-equivalence bundle for `encodeProg`. -/
theorem leanMiri_biFaultEquiv : BiFaultEquivBundle encodeProg :=
  BiFaultEquivBundle.of_fault_iff encodeProg
    reachesResult_fault_iff_refReachesOutcome

/-- Proved choice-coupled bidirectional fault-equivalence bundle for
`encodeProg`. -/
theorem leanMiri_biFaultEquivAtChoices :
    BiFaultEquivAtChoicesBundle encodeProg :=
  BiFaultEquivAtChoicesBundle.of_fault_iff encodeProg
    fault_equivalence_at_choices_claim_holds_base

/-! ## Section 4: Strict Separation Between Refinement and Fault Equivalence -/

/-- Zero-argument program reading an uninitialized `u32` local `_1`:
`_0 = copy _1; return`. Initialization succeeds only on empty arguments and
empty caller memory, where step 0 faults with `.fault .undefined`. -/
noncomputable def progReadUninitU32 : Program where
  entryDefId := 0
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [u32Ty, u32Ty]
    basicBlocks := [{
      statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
      terminator := .return_
    }]
  }]

private noncomputable def isU32Ty : MirTy → Bool
  | .int .i32 false => true
  | _ => false

private theorem isU32Ty_eq {ty : MirTy} (h : isU32Ty ty = true) :
    ty = .int .i32 false := by
  cases ty with
  | int w s =>
    cases w with
    | i8 => cases h
    | i16 => cases h
    | i32 =>
      cases s with
      | false => rfl
      | true => cases h
    | i64 => cases h
    | i128 => cases h
    | isize => cases h
  | bool => cases h
  | char => cases h
  | ordering => cases h
  | unit => cases h
  | never => cases h
  | enum _ => cases h
  | tuple _ => cases h
  | ref _ _ => cases h
  | rawPtr _ _ => cases h
  | slice _ => cases h
  | str => cases h
  | array _ _ => cases h
  | vec _ => cases h
  | box _ => cases h
  | rangeTo _ => cases h
  | rangeFrom _ => cases h
  | range _ => cases h
  | option _ => cases h
  | unsupported => cases h

private noncomputable def isCopy1To0Stmt : StatementKind → Bool
  | .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)) => true
  | _ => false

private theorem isCopy1To0Stmt_eq {st : StatementKind}
    (h : isCopy1To0Stmt st = true) :
    st = .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩)) := by
  cases st with
  | nop => cases h
  | storageLive _ => cases h
  | storageDead _ => cases h
  | unsupported => cases h
  | assign dst rv =>
    cases dst with
    | mk dId dProj =>
      cases dId with
      | succ _ => cases h
      | zero =>
        cases dProj with
        | cons _ _ => cases h
        | nil =>
          cases rv with
          | binaryOp _ _ _ => cases h
          | unaryOp _ _ => cases h
          | cast _ _ _ => cases h
          | discriminant _ => cases h
          | aggregateTuple _ => cases h
          | ref _ _ => cases h
          | addressOf _ _ => cases h
          | fakeAddressOf _ => cases h
          | useRetag _ => cases h
          | aggregateRangeTo _ _ => cases h
          | aggregateRangeFrom _ _ => cases h
          | aggregateArray _ _ => cases h
          | repeat_ _ _ _ => cases h
          | aggregateRange _ _ _ => cases h
          | aggregateOption _ _ => cases h
          | unsupported => cases h
          | use op =>
            cases op with
            | move _ => cases h
            | constant _ => cases h
            | copy src =>
              cases src with
              | mk sId sProj =>
                cases sId with
                | zero => cases h
                | succ sId' =>
                  cases sId' with
                  | succ _ => cases h
                  | zero =>
                    cases sProj with
                    | cons _ _ => cases h
                    | nil => rfl

/-- Syntactic recognizer for zero-argument bodies whose entry block begins with
`_0 = copy _1` on `u32` locals `_0, _1` (satisfied by `progReadUninitU32`). -/
noncomputable def isReadUninitU32Shape (p : Program) : Bool :=
  Nat.beq p.entryDefId 0 &&
    match p.bodies with
    | [] => false
    | body :: _ =>
      Nat.beq body.argumentCount 0 &&
        match body.locals, body.basicBlocks with
        | t0 :: t1 :: _, bb :: _ =>
          match bb.statements with
          | st0 :: _ => isU32Ty t0 && isU32Ty t1 && isCopy1To0Stmt st0
          | [] => false
        | _, _ => false

/-- Conservative encoding that coarsens `isReadUninitU32Shape` programs to a
bodyless `RefProg` (rejected at entry with `.blocked`), while forwarding all
other programs to `encodeProg`. -/
noncomputable def encodeConservativeCoarsen (p : Program) : RefProg :=
  if isReadUninitU32Shape p then
    { encodeProg p with bodies := [] }
  else
    encodeProg p

private theorem initRefState_empty_bodies (rp : RefProg) (q : Query)
    (maxSteps : Nat) (h_emp : rp.bodies = []) :
    initRefState rp q maxSteps = .error .unsupported := by
  dsimp only [initRefState]
  rw [h_emp]
  cases (!Nat.beq rp.pointerWidthBits 64 || !Nat.beq rp.mirProfileVersion 1)
  · cases (!q.callerMem.allocations.isEmpty)
    · cases rp.entryDefId <;> rfl
    · rfl
  · rfl

private theorem initState_ok_frame_of_body0 (p : Program) (q : Query)
    (body : Body) (restBodies : List Body) (s₀ : State)
    (h_entry : p.entryDefId = 0)
    (h_bodies : p.bodies = body :: restBodies)
    (h_init : initState p q = .ok s₀) :
    s₀ = {
      frames := [{
        defId := 0
        blockIdx := 0
        stmtIdx := 0
        locals := initLocalsLoop body q.args 0 body.locals
      }]
      callerMem := q.callerMem
      mem := entryMemory
    } := by
  dsimp only [initState] at h_init
  rw [h_entry, h_bodies] at h_init
  dsimp only [MirSemantics.getElem?] at h_init
  cases h1 : (!Nat.beq p.pointerWidthBits 64 || !Nat.beq p.mirProfileVersion 1)
  · rw [h1] at h_init
    cases h2 : (!q.callerMem.allocations.isEmpty)
    · rw [h2] at h_init
      cases h3 : body.basicBlocks.isEmpty
      · rw [h3] at h_init
        cases h4 : (!Nat.blt body.argumentCount body.locals.length)
        · rw [h4] at h_init
          cases h5 : (!storageAnnotationsInBounds body)
          · rw [h5] at h_init
            cases h6 : (!discriminantTypesValid body)
            · rw [h6] at h_init
              cases h7 : (!castTypesValid body)
              · rw [h7] at h_init
                cases h7a : (!assertConditionTypesValid body)
                · rw [h7a] at h_init
                  cases h8 : (!body.locals.all isSupportedScalarOrUnitTy)
                  · rw [h8] at h_init
                    cases hc1 : (!callsAdmitted p body)
                    · rw [hc1] at h_init
                      cases hc2 : (!allCallBodiesStaticAdmitted p body)
                      · rw [hc2] at h_init
                        cases h9 :
                          (!checkArgsMatch q.args
                            ((body.locals.drop 1).take body.argumentCount))
                        · rw [h9] at h_init
                          dsimp only [ite_false_eq, Bool.false_or] at h_init
                          injection h_init with h_eq
                          exact h_eq.symm
                        · rw [h9] at h_init
                          cases h_init
                      · rw [hc2] at h_init
                        cases h_init
                    · rw [hc1] at h_init
                      cases h_init
                  · rw [h8] at h_init
                    cases h_init
                · rw [h7a] at h_init
                  cases h_init
              · rw [h7] at h_init
                cases h_init
            · rw [h6] at h_init
              cases h_init
          · rw [h5] at h_init
            cases h_init
        · rw [h4] at h_init
          cases h_init
      · rw [h3] at h_init
        cases h_init
    · rw [h2] at h_init
      cases h_init
  · rw [h1] at h_init
    cases h_init

private theorem isReadUninitU32Shape_not_wellFormed (p : Program) (q : Query)
    (h_shape : isReadUninitU32Shape p = true) :
    ¬ WellFormed p q := by
  intro h_wf
  let ⟨⟨s₀, h_init, _⟩, h_nofault⟩ := h_wf
  dsimp only [isReadUninitU32Shape] at h_shape
  cases h_entry : p.entryDefId with
  | succ _ =>
    rw [h_entry] at h_shape
    cases h_shape
  | zero =>
    rw [h_entry] at h_shape
    dsimp only [Nat.beq, Bool.true_and] at h_shape
    cases h_bodies : p.bodies with
    | nil =>
      rw [h_bodies] at h_shape
      cases h_shape
    | cons body restBodies =>
      have h_s0 := initState_ok_frame_of_body0 p q body restBodies s₀
        h_entry h_bodies h_init
      rw [h_bodies] at h_shape
      dsimp only at h_shape
      cases h_arg : body.argumentCount with
      | succ _ =>
        rw [h_arg] at h_shape
        cases h_shape
      | zero =>
        rw [h_arg] at h_shape
        dsimp only [Nat.beq, Bool.true_and] at h_shape
        cases h_locs : body.locals with
        | nil =>
          rw [h_locs] at h_shape
          cases h_shape
        | cons t0 l1 =>
          cases l1 with
          | nil =>
            rw [h_locs] at h_shape
            cases h_shape
          | cons t1 restLocs =>
            cases h_bbs : body.basicBlocks with
            | nil =>
              rw [h_locs, h_bbs] at h_shape
              cases h_shape
            | cons bb restBbs =>
              rw [h_locs, h_bbs] at h_shape
              dsimp only at h_shape
              cases h_sts : bb.statements with
              | nil =>
                rw [h_sts] at h_shape
                cases h_shape
              | cons st0 restSts =>
                rw [h_sts] at h_shape
                dsimp only at h_shape
                cases h_u0 : isU32Ty t0 with
                | false =>
                  rw [h_u0] at h_shape
                  cases h_shape
                | true =>
                  cases h_u1 : isU32Ty t1 with
                  | false =>
                    rw [h_u0, h_u1] at h_shape
                    cases h_shape
                  | true =>
                    rw [h_u0, h_u1] at h_shape
                    have ht0 := isU32Ty_eq h_u0
                    have ht1 := isU32Ty_eq h_u1
                    have hst0 := isCopy1To0Stmt_eq h_shape
                    have h_step : evalStep p 0 s₀ = .fault .undefined := by
                      rw [h_s0, h_locs, ht0, ht1]
                      dsimp only [evalStep, initLocalsLoop, activeFrameBody,
                        attachCallers]
                      rw [h_bodies, h_arg]
                      dsimp only [MirSemantics.getElem?, Nat.beq, Nat.ble]
                      rw [h_bbs]
                      dsimp only [MirSemantics.getElem?]
                      rw [h_sts, hst0]
                      dsimp only [MirSemantics.getElem?, evalStatement]
                      rw [h_locs, ht0, ht1]
                      cases hasStorageAnnotation body 1 <;> rfl
                    have h_ub : ReachesResult p q (.fault .undefined) := by
                      dsimp only [ReachesResult]
                      rw [h_init]
                      exact ⟨s₀, Reaches.refl s₀, 0, rfl, h_step⟩
                    exact h_nofault .undefined h_ub

/-- Concrete separation theorem: `encodeConservativeCoarsen` satisfies both
`SafetyRefinementBundle` and `SafetyRefinementAtChoicesBundle` while coarsening
`progReadUninitU32`'s `.fault .undefined` to `.blocked` and refuting both
`BiFaultEquivBundle` and `BiFaultEquivAtChoicesBundle`. -/
theorem safetyRefinement_separates_from_biFaultEquiv :
    SafetyRefinementBundle encodeConservativeCoarsen ∧
    SafetyRefinementAtChoicesBundle encodeConservativeCoarsen ∧
    ReachesResult progReadUninitU32 queryEmpty (.fault .undefined) ∧
    RefReachesOutcome (encodeConservativeCoarsen progReadUninitU32)
      queryEmpty 0 .blocked ∧
    (∀ maxSteps : Nat,
      ¬ RefReachesOutcome (encodeConservativeCoarsen progReadUninitU32)
        queryEmpty maxSteps .ub) ∧
    ¬ BiFaultEquivBundle encodeConservativeCoarsen ∧
    ¬ BiFaultEquivAtChoicesBundle encodeConservativeCoarsen := by
  have h_ref : SafetyRefinementBundle encodeConservativeCoarsen := by
    refine ⟨?_, ?_, ?_⟩
    · intro p q h_wf
      dsimp only [encodeConservativeCoarsen]
      cases h_sh : isReadUninitU32Shape p
      · exact leanMiri_safetyRefinement.wellFormed_transfer p q h_wf
      · exact False.elim (isReadUninitU32Shape_not_wellFormed p q h_sh h_wf)
    · intro p q out h_rbeh
      dsimp only [encodeConservativeCoarsen] at h_rbeh
      cases h_sh : isReadUninitU32Shape p
      · rw [h_sh] at h_rbeh
        exact leanMiri_safetyRefinement.behavior_reflect p q out h_rbeh
      · rw [h_sh] at h_rbeh
        let ⟨maxSteps, h_ro⟩ := h_rbeh
        dsimp only [RefReachesOutcome] at h_ro
        rw [initRefState_empty_bodies _ q maxSteps rfl] at h_ro
        cases h_ro
    · intro p q h_rdiv
      dsimp only [encodeConservativeCoarsen] at h_rdiv
      cases h_sh : isReadUninitU32Shape p
      · rw [h_sh] at h_rdiv
        exact leanMiri_safetyRefinement.diverges_reflect p q h_rdiv
      · rw [h_sh] at h_rdiv
        let ⟨rs₀, h_init, _⟩ := h_rdiv
        rw [initRefState_empty_bodies _ q 0 rfl] at h_init
        cases h_init
  have h_ref_c : SafetyRefinementAtChoicesBundle encodeConservativeCoarsen := by
    refine ⟨h_ref.wellFormed_transfer, ?_, ?_, ?_⟩
    · intro p q choices h_pref
      dsimp only [encodeConservativeCoarsen] at h_pref
      cases h_sh : isReadUninitU32Shape p
      · rw [h_sh] at h_pref
        exact leanMiri_safetyRefinementAtChoices.validPrefix_reflect
          p q choices h_pref
      · rw [h_sh] at h_pref
        let ⟨maxSteps, rs₀, _, h_init, _⟩ := h_pref
        rw [initRefState_empty_bodies _ q maxSteps rfl] at h_init
        cases h_init
    · intro p q choices out h_rbeh
      dsimp only [encodeConservativeCoarsen] at h_rbeh
      cases h_sh : isReadUninitU32Shape p
      · rw [h_sh] at h_rbeh
        exact leanMiri_safetyRefinementAtChoices.behavior_reflect
          p q choices out h_rbeh
      · rw [h_sh] at h_rbeh
        let ⟨maxSteps, h_ro⟩ := h_rbeh
        dsimp only [RefReachesOutcomeAtChoices] at h_ro
        rw [initRefState_empty_bodies _ q maxSteps rfl] at h_ro
        cases h_ro.2
    · intro p q cs h_rdiv
      dsimp only [encodeConservativeCoarsen] at h_rdiv
      cases h_sh : isReadUninitU32Shape p
      · rw [h_sh] at h_rdiv
        exact leanMiri_safetyRefinementAtChoices.diverges_reflect p q cs h_rdiv
      · rw [h_sh] at h_rdiv
        let ⟨rs₀, h_init, _⟩ := h_rdiv
        rw [initRefState_empty_bodies _ q 0 rfl] at h_init
        cases h_init
  have h_ub : ReachesResult progReadUninitU32 queryEmpty (.fault .undefined) :=
    ⟨_, Reaches.refl _, 0, rfl, rfl⟩
  have h_ub_c :
      ReachesResultAtChoices progReadUninitU32 queryEmpty [0]
        (.fault .undefined) :=
    ⟨[], 0, _, rfl, ReachesAtChoices.nil _, rfl, rfl⟩
  have h_blk :
      RefReachesOutcome (encodeConservativeCoarsen progReadUninitU32)
        queryEmpty 0 .blocked := by
    change RefReachesOutcome { encodeProg progReadUninitU32 with bodies := [] }
      queryEmpty 0 .blocked
    dsimp only [RefReachesOutcome]
    rw [initRefState_empty_bodies _ queryEmpty 0 rfl]
    rfl
  have h_no_ub :
      ∀ maxSteps : Nat,
        ¬ RefReachesOutcome (encodeConservativeCoarsen progReadUninitU32)
          queryEmpty maxSteps .ub := by
    intro maxSteps h_rub
    change RefReachesOutcome { encodeProg progReadUninitU32 with bodies := [] }
      queryEmpty maxSteps .ub at h_rub
    dsimp only [RefReachesOutcome] at h_rub
    rw [initRefState_empty_bodies _ queryEmpty maxSteps rfl] at h_rub
    cases h_rub
  have h_not_bi : ¬ BiFaultEquivBundle encodeConservativeCoarsen := by
    intro h_bi
    let ⟨maxSteps, h_rub⟩ := (h_bi.ub_iff progReadUninitU32 queryEmpty).1 h_ub
    exact h_no_ub maxSteps h_rub
  have h_not_bi_c :
      ¬ BiFaultEquivAtChoicesBundle encodeConservativeCoarsen := by
    intro h_bi_c
    let ⟨maxSteps, h_rub⟩ :=
      (h_bi_c.ub_iff progReadUninitU32 queryEmpty [0]).1 h_ub_c
    change RefReachesOutcomeAtChoices
      { encodeProg progReadUninitU32 with bodies := [] }
      queryEmpty [0] maxSteps .ub at h_rub
    dsimp only [RefReachesOutcomeAtChoices] at h_rub
    rw [initRefState_empty_bodies _ queryEmpty maxSteps rfl] at h_rub
    cases h_rub.2
  exact ⟨h_ref, h_ref_c, h_ub, h_blk, h_no_ub, h_not_bi, h_not_bi_c⟩

/-! ## Section 5: Concrete `CanaryFixtures` Transfer Witnesses -/

private theorem diverges_of_divergesAtChoices {p : Program} {q : Query}
    {choiceStream : Nat → Choice}
    (h_div : DivergesAtChoices p q choiceStream) :
    Diverges p q := by
  let ⟨s₀, h_init, trace, h_t0, h_step⟩ := h_div
  exact ⟨s₀, h_init, trace, h_t0,
    fun n => ⟨choiceStream n, (h_step n).1, (h_step n).2⟩⟩

/-- Concrete witness 1 (positive specification, prefix, termination, and
safety-only fault-absence transfer on `D7a` `progBinOpCopyThenMoveD7a`):
invokes `satisfiesPost_transfer` with non-trivial postcondition
`fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩`, `behavior_reflect`,
`validPrefix_reflect`, `terminates_transfer`, `terminatesAtChoices_transfer`,
and safety-only `(h_rwf maxSteps).2`. -/
theorem witness_safetyRefinement_D7a :
    RefWellFormed (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 ∧
    (∀ out : TerminalOut,
      RefBehavior (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 out →
        out = .returned ⟨u32Val 84, ⟨[]⟩⟩) ∧
    Behavior progBinOpCopyThenMoveD7a queryU32_42
      (.returned ⟨u32Val 84, ⟨[]⟩⟩) ∧
    ValidPrefixAtChoices progBinOpCopyThenMoveD7a queryU32_42 [] ∧
    ¬ RefDiverges (encodeProg progBinOpCopyThenMoveD7a) queryU32_42 ∧
    (∀ choiceStream : Nat → Choice,
      ¬ RefDivergesAtChoices (encodeProg progBinOpCopyThenMoveD7a)
        queryU32_42 choiceStream) ∧
    (∀ maxSteps : Nat,
      ¬ RefReachesOutcome (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
          maxSteps .ub ∧
      ¬ RefReachesOutcome (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
          maxSteps .blocked) := by
  have h_wp : Anneal.MirWp.wpProg progBinOpCopyThenMoveD7a 2 queryU32_42
      (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, h_ndiv, _⟩ := Anneal.MirWp.wellFormed_and_spec_of_wp
    progBinOpCopyThenMoveD7a queryU32_42 2
    (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) h_wp
  let ⟨h_rwf, h_rpost⟩ :=
    leanMiri_safetyRefinement.satisfiesPost_transfer
      progBinOpCopyThenMoveD7a queryU32_42
      (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) h_sat
  let ⟨_, _, _, h_rbeh⟩ := canary_D7a_binop_copy_then_move_ok_base
  have h_beh := leanMiri_safetyRefinement.behavior_reflect
    progBinOpCopyThenMoveD7a queryU32_42 _ h_rbeh
  let ⟨rs₀, h_init_r, _⟩ := (h_rwf 0).1
  have h_vpre : ValidPrefixAtChoices progBinOpCopyThenMoveD7a queryU32_42 [] :=
    leanMiri_safetyRefinementAtChoices.validPrefix_reflect
      progBinOpCopyThenMoveD7a queryU32_42 []
      ⟨0, rs₀, rs₀, h_init_r, RefReachesAtChoices.nil rs₀⟩
  have h_nterm := leanMiri_safetyRefinement.terminates_transfer
    progBinOpCopyThenMoveD7a queryU32_42 h_ndiv
  have h_nterm_c :
      ∀ choiceStream : Nat → Choice,
        ¬ RefDivergesAtChoices (encodeProg progBinOpCopyThenMoveD7a)
          queryU32_42 choiceStream :=
    fun cs =>
      leanMiri_safetyRefinementAtChoices.terminatesAtChoices_transfer
        progBinOpCopyThenMoveD7a queryU32_42 cs
        (fun h_dc => h_ndiv (diverges_of_divergesAtChoices h_dc))
  have h_nofault :
      ∀ maxSteps : Nat,
        ¬ RefReachesOutcome (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
            maxSteps .ub ∧
        ¬ RefReachesOutcome (encodeProg progBinOpCopyThenMoveD7a) queryU32_42
            maxSteps .blocked :=
    fun maxSteps => (h_rwf maxSteps).2
  exact ⟨h_rwf, h_rpost, h_beh, h_vpre, h_nterm, h_nterm_c, h_nofault⟩

/-- Concrete witness 1b (`BiFaultEquivBundle.wellFormed_no_ref_fault` on `D8`
`progSelfMoveD8`): universal fault-absence reflection via `BiFaultEquivBundle`.
-/
theorem witness_biFaultEquiv_wellFormed_D8 (maxSteps : Nat) :
    ¬ RefReachesOutcome (encodeProg progSelfMoveD8) queryU32_42 maxSteps .ub ∧
      ¬ RefReachesOutcome (encodeProg progSelfMoveD8) queryU32_42
          maxSteps .blocked :=
  leanMiri_biFaultEquiv.wellFormed_no_ref_fault
    progSelfMoveD8 queryU32_42 canary_D8_self_move_ok_base.1 maxSteps

/-- Concrete witness 2 (existential UB refutation, reflection, and
contrapositive `WellFormed` exclusion on `D6` `progUseAfterMoveD6`): invokes
`ub_refutation_transfer`, `ub_reflect`, and `ref_ub_not_wellFormed`. -/
theorem witness_biFaultEquiv_ub_D6 :
    (∃ maxSteps : Nat,
      RefReachesOutcome (encodeProg progUseAfterMoveD6) queryU32_42
        maxSteps .ub) ∧
    ¬ RefWellFormed (encodeProg progUseAfterMoveD6) queryU32_42 ∧
    ¬ WellFormed progUseAfterMoveD6 queryU32_42 ∧
    ReachesResult progUseAfterMoveD6 queryU32_42 (.fault .undefined) := by
  let ⟨h_ub, _, _, _⟩ := canary_D6_use_after_move_ub_base
  let ⟨⟨maxSteps, h_ref_ub⟩, h_nrwf⟩ :=
    leanMiri_biFaultEquiv.ub_refutation_transfer
      progUseAfterMoveD6 queryU32_42 h_ub
  exact ⟨⟨maxSteps, h_ref_ub⟩, h_nrwf,
    leanMiri_safetyRefinement.ref_ub_not_wellFormed
      progUseAfterMoveD6 queryU32_42 maxSteps h_ref_ub,
    leanMiri_biFaultEquiv.ub_reflect
      progUseAfterMoveD6 queryU32_42 maxSteps h_ref_ub⟩

/-- Concrete witness 3 (`.unsupported ↔ .blocked` separation from `.ub` on `D15`
`300u32 as char`): invokes `unsupported_refutation_transfer`,
`SafetyRefinementBundle.ref_blocked_not_wellFormed`,
`BiFaultEquivBundle.unsupported_reflect`, `BiFaultEquivBundle.fault_iff`, and
`ub_reflect` to prove `.blocked` reachability, `¬ RefWellFormed`,
`¬ WellFormed`, blocked-fault reflection, and `.ub`-freedom across all step
budgets. -/
theorem witness_biFaultEquiv_blocked_not_ub_D15 :
    (∃ maxSteps : Nat,
      RefReachesOutcome (encodeProg (mkIntToIntCastProg u32Ty .char))
        { args := [u32Val 300] } maxSteps .blocked) ∧
    ¬ RefWellFormed (encodeProg (mkIntToIntCastProg u32Ty .char))
        { args := [u32Val 300] } ∧
    ¬ WellFormed (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } ∧
    ReachesResult (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
      (.fault .unsupported) ∧
    (ReachesResult (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
      (.fault .unsupported) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcome (encodeProg (mkIntToIntCastProg u32Ty .char))
          { args := [u32Val 300] } maxSteps .blocked) ∧
    ∀ maxSteps : Nat,
      ¬ RefReachesOutcome (encodeProg (mkIntToIntCastProg u32Ty .char))
        { args := [u32Val 300] } maxSteps .ub := by
  let ⟨_, _, _, _, _, _, _, _, h_unsup, h_nub, _, _⟩ :=
    canary_D15_int_to_int_cast_base
  let ⟨⟨maxSteps, h_ref_blk⟩, h_nrwf⟩ :=
    leanMiri_biFaultEquiv.unsupported_refutation_transfer _ _ h_unsup
  have h_nwf := leanMiri_safetyRefinement.ref_blocked_not_wellFormed
    (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } maxSteps h_ref_blk
  have h_refl := leanMiri_biFaultEquiv.unsupported_reflect
    (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } maxSteps h_ref_blk
  have h_fiff := leanMiri_biFaultEquiv.fault_iff
    (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } .unsupported
  refine ⟨⟨maxSteps, h_ref_blk⟩, h_nrwf, h_nwf, h_refl, h_fiff, ?_⟩
  intro ms h_ref_ub
  exact h_nub
    ((leanMiri_biFaultEquiv.fault_iff _ _ .undefined).2 ⟨ms, h_ref_ub⟩)

/-- Concrete witness 4 (choice-coupled UB refutation and reflection on `D6`
along choice prefix `[0, 0]`): invokes `BiFaultEquivAtChoicesBundle.fault_iff`
and `ub_reflect`. -/
theorem witness_biFaultEquivAtChoices_ub_D6 :
    (∃ maxSteps : Nat,
      RefReachesOutcomeAtChoices (encodeProg progUseAfterMoveD6) queryU32_42
        [0, 0] maxSteps .ub) ∧
    ReachesResultAtChoices progUseAfterMoveD6 queryU32_42 [0, 0]
      (.fault .undefined) := by
  have h_res_c :
      ReachesResultAtChoices progUseAfterMoveD6 queryU32_42 [0, 0]
        (.fault .undefined) := by
    unfold ReachesResultAtChoices
    cases h_init : initState progUseAfterMoveD6 queryU32_42 with
    | error k => cases h_init
    | ok s₀ =>
      cases h_step : evalStep progUseAfterMoveD6 0 s₀ with
      | done _ =>
        injection h_init with h_s0
        subst h_s0
        cases h_step
      | fault _ =>
        injection h_init with h_s0
        subst h_s0
        cases h_step
      | step s₁ =>
        refine ⟨[0], 0, s₁, rfl,
          ReachesAtChoices.cons rfl h_step (ReachesAtChoices.nil s₁), rfl, ?_⟩
        injection h_init with h_s0
        subst h_s0
        injection h_step with h_s1
        subst h_s1
        rfl
  let ⟨maxSteps, h_ref_ub⟩ :=
    (leanMiri_biFaultEquivAtChoices.fault_iff
      progUseAfterMoveD6 queryU32_42 [0, 0] .undefined).1 h_res_c
  exact ⟨⟨maxSteps, h_ref_ub⟩,
    leanMiri_biFaultEquivAtChoices.ub_reflect _ _ _ maxSteps h_ref_ub⟩

/-- Concrete witness 5 (choice-coupled `.unsupported ↔ .blocked` transfer and
reflection on `D15` `300u32 as char` along choice prefix `[0]`): invokes
`BiFaultEquivAtChoicesBundle.fault_iff` and `unsupported_reflect`. -/
theorem witness_biFaultEquivAtChoices_blocked_D15 :
    (∃ maxSteps : Nat,
      RefReachesOutcomeAtChoices (encodeProg (mkIntToIntCastProg u32Ty .char))
        { args := [u32Val 300] } [0] maxSteps .blocked) ∧
    ReachesResultAtChoices (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 300] } [0] (.fault .unsupported) ∧
    ¬ (∃ maxSteps : Nat,
      RefReachesOutcomeAtChoices (encodeProg (mkIntToIntCastProg u32Ty .char))
        { args := [u32Val 300] } [0] maxSteps .ub) := by
  have h_res_c :
      ReachesResultAtChoices (mkIntToIntCastProg u32Ty .char)
        { args := [u32Val 300] } [0] (.fault .unsupported) := by
    unfold ReachesResultAtChoices
    cases h_init : initState (mkIntToIntCastProg u32Ty .char)
        { args := [u32Val 300] } with
    | error k => cases h_init
    | ok s₀ =>
      refine ⟨[], 0, s₀, rfl, ReachesAtChoices.nil s₀, rfl, ?_⟩
      injection h_init with h_s0
      subst h_s0
      rfl
  let ⟨maxSteps, h_ref_blk⟩ :=
    (leanMiri_biFaultEquivAtChoices.fault_iff
      (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } [0]
      .unsupported).1 h_res_c
  have h_refl :=
    leanMiri_biFaultEquivAtChoices.unsupported_reflect
      (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } [0]
      maxSteps h_ref_blk
  refine ⟨⟨maxSteps, h_ref_blk⟩, h_refl, ?_⟩
  intro h_ub_ex
  have h_ub_c :=
    (leanMiri_biFaultEquivAtChoices.fault_iff
      (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] } [0]
      .undefined).2 h_ub_ex
  unfold ReachesResultAtChoices at h_ub_c
  cases h_init : initState (mkIntToIntCastProg u32Ty .char)
      { args := [u32Val 300] } with
  | error k => cases h_init
  | ok s₀ =>
    rw [h_init] at h_ub_c
    let ⟨pre, c, s, h_eq, h_reach, _, h_ev⟩ := h_ub_c
    cases pre with
    | nil =>
      injection h_eq with hc
      subst hc
      cases h_reach with
      | nil =>
        injection h_init with h_s0
        subst h_s0
        cases h_ev
    | cons p0 pt =>
      cases pt with
      | nil => cases h_eq
      | cons _ _ => cases h_eq

end Anneal.MirCorrespondence
