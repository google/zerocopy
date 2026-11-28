-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Profile v2 `evalStepV2` / `CallerMemory` Correspondence Against `lean-miri`

Zero-TCB mechanized correspondence between Anneal's Profile v2 semantics
(`Trusted.MirSemantics.initStateV2`, `evalStepV2`, `WellFormedV2`,
`BehaviorV2`, `DivergesV2`, `BodyVerifiedV2`, `ProgramVerifiedV2`,
`CrateTheoremV2`, `UnitTheoremV2`) and the independent `lean-miri` Profile v2
reference machine (`Anneal.MirCorrespondence.ProfileV2RefMachine`), driving
real `Miri.Interpreter.ExecutionMachine.step`:

1. **Section 1 — `OracleCertificate`-Ready Factored Bundles & Transfer
   Theorems:**
   - `SafetyRefinementV2On`, `SafetyRefinementV2Bundle`,
     `SafetyRefinementV2AtChoicesBundle`, `BiFaultEquivV2On`,
     `BiFaultEquivV2Bundle`, and `BiFaultEquivV2AtChoicesBundle`.
   - Because Profile v2 $M_{\text{anneal}}$ is strictly conservative relative
     to `lean-miri` on three documented edges, safety refinement guards
     `behavior_reflect` and `diverges_reflect` with `WellFormedV2 p q`.
     On any domain `D` containing a verified program's `entryProgForBody`
     queries, `SafetyRefinementV2On` transfers `SatisfiesPostV2`, termination
     (`¬ DivergesV2`), contrapositive `.ub`/`.blocked` exclusion,
     `BodyVerifiedV2`, `ProgramVerifiedV2`, `CrateTheoremV2`, and
     `UnitTheoremV2`.
   - The unquantified universal bundles (`SafetyRefinementV2Bundle`,
     `SafetyRefinementV2AtChoicesBundle`, `BiFaultEquivV2Bundle`,
     `BiFaultEquivV2AtChoicesBundle`, i.e., `D := True`) represent the global
     specification interfaces: `BiFaultEquivV2Bundle encodeProg` is proved
     false, and `SafetyRefinementV2Bundle encodeProg` is uninstantiated
     because `evalStepV2` and `ProfileV2RefMachine` currently diverge or lack a
     universal simulation proof on newer Profile v2 extensions (fixed-array
     aggregate/repeat rvalues, constant rodata, `constantIndex`, `unsize`,
     `intToLeBytes`, `arrayEq`, fixed-array `[T; N]` validity classification,
     `assertConditionTypesValid` admission, `refDereferenceOpV2`'s eager
     `refValidateRefInMiriV2` hook, and arbitrary `--panic abort` assertions
     outside verified canary/regression witnesses).
2. **Section 2 — Corresponded-Fragment Layout, Little-Endian Codec,
   `CallerMemory`, and Structural Bridge Laws (`inCorrespondedTyV2` /
   `inCorrespondedValV2`):**
   - Exact size & natural-alignment agreement between `layoutOfTyV2` and
     `refLayoutDataForTyV2` across every type in the corresponded Profile v2
     layout fragment (`inCorrespondedLayoutTyV2`) whose byte size fits in
     `u64` (`< 2^64`; modulo `2^64` unconditionally).
   - Fragment-guarded agreement (and unconditional `ProfileV2RefMachine`
     admissibility soundness) of `validCallerMemory`, `isSupportedV2LocalTy`,
     `checkValV2`, `checkArgsMatchV2`, `refAccessSpans` (under
     `tyLayoutsFitU64V2`), `spansPairwiseDisjoint`, and `refsStayInCallerMem`
     against `Trusted.MirSemantics` without universal `rfl` assertions over
     future `MirTy`/`Val` extensions.
   - `Trusted.MirSemantics`-side little-endian byte codec round-trips
     (`encodeValV2` / `decodeValV2` at `profileV2TargetEndian = .little`) for
     integers, thin pointers (with provenance), and wide slice fat pointers,
     plus `targetUIntBytesMirror`, plain-init `CallerMemory` materialization and
     extraction (`refAllocToMiriV2_plainInit_spec`,
     `refExtractOneCallerAllocV2_of_allocByteSliceRel`), and callee-stack
     framing lemmas against `Miri.Memory.Allocation` /
     `Miri.Memory.MemoryState`.
3. **Section 3 — Deterministic Execution Adequacy & Exclusivity Bridges:**
   - Fuel-bounded Anneal adequacy/exclusivity (`execFaultProgV2`,
     `fault_and_exclusive_of_execFaultV2`, complementing
     `Anneal.MirWp.spec_and_behaviorV2_of_exec_eq`) and
     $M_{\text{ref}}^{\text{v2}}$ multi-step adequacy (`refCoreExecV2`,
     `ref_ok_of_coreExec`, `ref_ub_of_coreExec`, `ref_ub_of_init_error`).
4. **Companion Proof Modules:**
   - `ProfileV2Witnesses`: symbolic stepping lemmas for `ExecutionMachine.step`,
     `copyRuntimePlace`, and `ValidityVisitor.validatePlace`.
   - `ProfileV2EdgeWitnesses`: three conservative-edge separation witnesses
     (zero-offset `BinOp.offset` on OOB pointer, null ZST deref, and
     `*const u32 as *mut u32`), with Edge 1 witnessing
     `not_biFaultEquivV2_encodeProg`.
   - `ProfileV2Canaries`, `ProfileV2PosCanaries`, `ProfileV2PosCanariesC1`, and
     `ProfileV2C3AndBundles`: canary definitions (`V2_C1`–`V2_C6`, counting
     `V2_C4a`/`V2_C4b`), end-to-end locksteps, and concrete
     `SafetyRefinementV2On` / `BiFaultEquivV2On` domain bundles.
-/

/-! ## Section 1: Profile v2 Choice Predicates, Factored Bundles & Transfers -/

/-- Choice-coupled finite-step reachability in Profile v2 $M_{\text{anneal}}$.
-/
inductive ReachesAtChoicesV2 (p : Program) :
    State → List Choice → State → Prop where
  | nil (s : State) : ReachesAtChoicesV2 p s [] s
  | cons {s₁ s₂ s₃ : State} {c : Choice} {cs : List Choice} :
      ValidChoice p s₁ c →
      evalStepV2Choice p c s₁ = .step s₂ →
      ReachesAtChoicesV2 p s₂ cs s₃ →
      ReachesAtChoicesV2 p s₁ (c :: cs) s₃

/-- Choice-coupled finite prefix admissibility in Profile v2. -/
def ValidPrefixAtChoicesV2 (p : Program) (q : Query)
    (choices : List Choice) : Prop :=
  ∃ s₀ s : State,
    initStateV2 p q = .ok s₀ ∧ ReachesAtChoicesV2 p s₀ choices s

/-- Choice-coupled outcome reachability in Profile v2. -/
def ReachesResultAtChoicesV2 (p : Program) (q : Query)
    (choices : List Choice) (res : StepResult State TerminalOut) : Prop :=
  match initStateV2 p q with
  | .error k => choices = [] ∧ res = .fault k
  | .ok s₀ =>
    ∃ (prefixChoices : List Choice) (c : Choice) (s : State),
      choices = prefixChoices ++ [c] ∧
      ReachesAtChoicesV2 p s₀ prefixChoices s ∧
      ValidChoice p s c ∧
      evalStepV2Choice p c s = res

/-- Choice-coupled observable terminal behavior in Profile v2. -/
def BehaviorAtChoicesV2 (p : Program) (q : Query)
    (choices : List Choice) (out : TerminalOut) : Prop :=
  ReachesResultAtChoicesV2 p q choices (.done out)

/-- Choice-coupled divergence in Profile v2. -/
def DivergesAtChoicesV2 (p : Program) (q : Query)
    (choiceStream : Nat → Choice) : Prop :=
  ∃ s₀ : State,
    initStateV2 p q = .ok s₀ ∧
    ∃ trace : Nat → State,
      trace 0 = s₀ ∧
      ∀ n : Nat,
        ValidChoice p (trace n) (choiceStream n) ∧
        evalStepV2Choice p (choiceStream n) (trace n) = .step (trace (n + 1))

/-- Domain-relativized Profile v2 safety-refinement bundle over
`D : Program → Query → Prop` and `encode : Program → RefProg`:
1. `wellFormed_transfer`: fault-freedom in $M_{\text{anneal}}^{\text{v2}}$
   transfers to `RefWellFormedV2`;
2. `behavior_reflect`: whenever `(p, q)` is `WellFormedV2`, every reference
   terminal outcome `(retVal, postCallerMem)` is a Profile v2 `BehaviorV2`;
3. `diverges_reflect`: whenever `(p, q)` is `WellFormedV2`, reference
   divergence reflects to `DivergesV2`.

Guarding backward reflection by `WellFormedV2` matches conservative
over-approximation of faults (when $M_{\text{anneal}}^{\text{v2}}$ faults
conservatively, $M_{\text{ref}}^{\text{v2}}$ may return normally) while still
licensing all soundness transfers (`SatisfiesPostV2`, termination,
`BodyVerifiedV2`, `ProgramVerifiedV2`, `CrateTheoremV2`, `UnitTheoremV2`). -/
structure SafetyRefinementV2On (D : Program → Query → Prop)
    (encode : Program → RefProg) : Prop where
  wellFormed_transfer :
    ∀ (p : Program) (q : Query),
      D p q → WellFormedV2 p q → RefWellFormedV2 (encode p) q
  behavior_reflect :
    ∀ (p : Program) (q : Query) (out : TerminalOut),
      D p q → WellFormedV2 p q →
        RefBehaviorV2 (encode p) q out → BehaviorV2 p q out
  diverges_reflect :
    ∀ (p : Program) (q : Query),
      D p q → WellFormedV2 p q →
        RefDivergesV2 (encode p) q → DivergesV2 p q

/-- Universal (`D := fun _ _ => True`) Profile v2 safety-refinement interface
specification. Uninstantiated for `encodeProg` while `ProfileV2RefMachine`
still blocks on array, constant-rodata, `constantIndex`, `unsize`, and
byte/array core-call extensions accepted by `evalStepV2`; see
`SafetyRefinementV2On` for the proved domain-relativized theorems. -/
structure SafetyRefinementV2Bundle (encode : Program → RefProg) : Prop where
  wellFormed_transfer :
    ∀ (p : Program) (q : Query),
      WellFormedV2 p q → RefWellFormedV2 (encode p) q
  behavior_reflect :
    ∀ (p : Program) (q : Query) (out : TerminalOut),
      WellFormedV2 p q →
        RefBehaviorV2 (encode p) q out → BehaviorV2 p q out
  diverges_reflect :
    ∀ (p : Program) (q : Query),
      WellFormedV2 p q →
        RefDivergesV2 (encode p) q → DivergesV2 p q

/-- Universal choice-coupled Profile v2 safety-refinement interface
specification (left uninstantiated for `encodeProg`; see
`SafetyRefinementV2On`). -/
structure SafetyRefinementV2AtChoicesBundle
    (encode : Program → RefProg) : Prop where
  wellFormed_transfer :
    ∀ (p : Program) (q : Query),
      WellFormedV2 p q → RefWellFormedV2 (encode p) q
  validPrefix_reflect :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      WellFormedV2 p q →
        RefValidPrefixAtChoicesV2 (encode p) q choices →
        ValidPrefixAtChoicesV2 p q choices
  behavior_reflect :
    ∀ (p : Program) (q : Query) (choices : List Choice) (out : TerminalOut),
      WellFormedV2 p q →
        RefBehaviorAtChoicesV2 (encode p) q choices out →
        BehaviorAtChoicesV2 p q choices out
  diverges_reflect :
    ∀ (p : Program) (q : Query) (choiceStream : Nat → Choice),
      WellFormedV2 p q →
        RefDivergesAtChoicesV2 (encode p) q choiceStream →
        DivergesAtChoicesV2 p q choiceStream

/-- Domain-relativized Profile v2 bidirectional fault-equivalence bundle:
exact two-way `.undefined ↔ .ub` and `.unsupported ↔ .blocked` on `D`. -/
structure BiFaultEquivV2On (D : Program → Query → Prop)
    (encode : Program → RefProg) : Prop where
  ub_iff :
    ∀ (p : Program) (q : Query),
      D p q →
      (ReachesResultV2 p q (.fault .undefined) ↔
        ∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .ub)
  unsupported_iff :
    ∀ (p : Program) (q : Query),
      D p q →
      (ReachesResultV2 p q (.fault .unsupported) ↔
        ∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .blocked)

/-- Universal Profile v2 bidirectional fault-equivalence interface
specification (provably false for `encodeProg`; see
`not_biFaultEquivV2_encodeProg`). -/
structure BiFaultEquivV2Bundle (encode : Program → RefProg) : Prop where
  ub_iff :
    ∀ (p : Program) (q : Query),
      ReachesResultV2 p q (.fault .undefined) ↔
        ∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .ub
  unsupported_iff :
    ∀ (p : Program) (q : Query),
      ReachesResultV2 p q (.fault .unsupported) ↔
        ∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .blocked

/-- Universal choice-coupled Profile v2 bidirectional fault-equivalence
interface specification. -/
structure BiFaultEquivV2AtChoicesBundle
    (encode : Program → RefProg) : Prop where
  ub_iff :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      ReachesResultAtChoicesV2 p q choices (.fault .undefined) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeAtChoicesV2 (encode p) q choices maxSteps .ub
  unsupported_iff :
    ∀ (p : Program) (q : Query) (choices : List Choice),
      ReachesResultAtChoicesV2 p q choices (.fault .unsupported) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeAtChoicesV2 (encode p) q choices maxSteps .blocked

/-- Restrict a universal `SafetyRefinementV2Bundle` to any domain `D`. -/
theorem SafetyRefinementV2Bundle.toOn {encode : Program → RefProg}
    (h : SafetyRefinementV2Bundle encode) (D : Program → Query → Prop) :
    SafetyRefinementV2On D encode :=
  ⟨fun p q _ => h.wellFormed_transfer p q,
    fun p q out _ => h.behavior_reflect p q out,
    fun p q _ => h.diverges_reflect p q⟩

/-- Domain-relativized postcondition transfer from `SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.satisfiesPostV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (q : Query) (post : TerminalOut → Prop)
    (h_dom : D p q) (h_sat : SatisfiesPostV2 p q post) :
    RefWellFormedV2 (encode p) q ∧
      ∀ out : TerminalOut, RefBehaviorV2 (encode p) q out → post out :=
  ⟨h_ref.wellFormed_transfer p q h_dom h_sat.1,
    fun out h_rbeh =>
      h_sat.2 out (h_ref.behavior_reflect p q out h_dom h_sat.1 h_rbeh)⟩

/-- Domain-relativized termination transfer from `SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.terminatesV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (q : Query) (h_dom : D p q)
    (h_wf : WellFormedV2 p q) (h_term : ¬ DivergesV2 p q) :
    ¬ RefDivergesV2 (encode p) q :=
  fun h_rdiv => h_term (h_ref.diverges_reflect p q h_dom h_wf h_rdiv)

/-- Domain-relativized contrapositive `.ub` exclusion from
`SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.ref_ub_not_wellFormedV2
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_dom : D p q)
    (h_ub : RefReachesOutcomeV2 (encode p) q maxSteps .ub) :
    ¬ WellFormedV2 p q :=
  fun h_wf => ((h_ref.wellFormed_transfer p q h_dom h_wf) maxSteps).2.1 h_ub

/-- Domain-relativized contrapositive `.blocked` exclusion from
`SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.ref_blocked_not_wellFormedV2
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_dom : D p q)
    (h_blk : RefReachesOutcomeV2 (encode p) q maxSteps .blocked) :
    ¬ WellFormedV2 p q :=
  fun h_wf => ((h_ref.wellFormed_transfer p q h_dom h_wf) maxSteps).2.2 h_blk

/-- Domain-relativized `BodyVerifiedV2` transfer under `SafetyRefinementV2On`:
every in-domain Profile v2 entry query satisfying an `unsafe` body's
precondition is `RefWellFormedV2` in `lean-miri`. -/
theorem SafetyRefinementV2On.bodyVerifiedV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (defId : DefId) (body : Body) (safetyPre : Query → Prop)
    (h_dom : ∀ q : Query,
      ValidEntryArgsV2 body q →
      (body.isUnsafe = true → safetyPre q) →
      D (entryProgForBody p defId) q)
    (h_bv : BodyVerifiedV2 p defId body safetyPre) :
    MirSemantics.getElem? p.bodies defId = some body ∧
    BodyStaticAdmittedV2 p body = true ∧
    ∀ q : Query,
      ValidEntryArgsV2 body q →
      (body.isUnsafe = true → safetyPre q) →
      RefWellFormedV2 (encode (entryProgForBody p defId)) q :=
  ⟨h_bv.1, h_bv.2.1, fun q h_args h_pre =>
    h_ref.wellFormed_transfer (entryProgForBody p defId) q
      (h_dom q h_args h_pre) (h_bv.2.2 q h_args h_pre)⟩

/-- Domain-relativized `ProgramVerifiedV2` transfer under
`SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.programVerifiedV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode)
    (p : Program) (specs : SpecsV2)
    (h_dom : ∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? p.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → specs.safety body.identity q) →
        D (entryProgForBody p defId) q)
    (h_pv : ProgramVerifiedV2 p specs) :
    Nat.beq p.pointerWidthBits 64 = true ∧
    Nat.beq p.mirProfileVersion 2 = true ∧
    !p.bodies.isEmpty = true ∧
    Nat.blt p.entryDefId p.bodies.length = true ∧
    bodiesHaveUniqueIdentities p.bodies = true ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? p.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody p defId)) q) ∧
    specs.property p := by
  let ⟨h1, h2, h3, h4, h5, h_bodies, h_prop⟩ := h_pv
  refine ⟨h1, h2, h3, h4, h5, ?_, h_prop⟩
  intro defId body h_get q h_args h_pre
  exact (h_ref.bodyVerifiedV2_transfer p defId body
    (specs.safety body.identity) (h_dom defId body h_get)
    (h_bodies defId body h_get)).2.2 q h_args h_pre

/-- Domain-relativized `CrateTheoremV2` transfer under
`SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.crateTheoremV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode) (c : MirSemantics.CrateV2)
    (h_dom : ∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        D (entryProgForBody c.program defId) q)
    (h_ct : MirSemantics.CrateTheoremV2 c) :
    c.program.scope = VerificationScope.crate ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody c.program defId)) q) ∧
    c.specs.property c.program :=
  let h_pv := h_ref.programVerifiedV2_transfer c.program c.specs h_dom h_ct.2
  ⟨h_ct.1, h_pv.2.2.2.2.2.1, h_pv.2.2.2.2.2.2⟩

/-- Domain-relativized `UnitTheoremV2` transfer under `SafetyRefinementV2On`. -/
theorem SafetyRefinementV2On.unitTheoremV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2On D encode) (c : MirSemantics.CrateV2)
    (h_dom : ∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        D (entryProgForBody c.program defId) q)
    (h_ut : MirSemantics.UnitTheoremV2 c) :
    c.program.scope = VerificationScope.unit ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody c.program defId)) q) ∧
    c.specs.property c.program :=
  let h_pv := h_ref.programVerifiedV2_transfer c.program c.specs h_dom h_ut.2
  ⟨h_ut.1, h_pv.2.2.2.2.2.1, h_pv.2.2.2.2.2.2⟩

/-- Universal Profile v2 postcondition transfer (both return value and
post-state `CallerMemory`) from `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.satisfiesPostV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (q : Query) (post : TerminalOut → Prop)
    (h_sat : SatisfiesPostV2 p q post) :
    RefWellFormedV2 (encode p) q ∧
      ∀ out : TerminalOut, RefBehaviorV2 (encode p) q out → post out :=
  (h_ref.toOn (fun _ _ => True)).satisfiesPostV2_transfer p q post trivial h_sat

/-- Universal Profile v2 termination transfer from `SafetyRefinementV2Bundle`.
-/
theorem SafetyRefinementV2Bundle.terminatesV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (q : Query)
    (h_wf : WellFormedV2 p q) (h_term : ¬ DivergesV2 p q) :
    ¬ RefDivergesV2 (encode p) q :=
  (h_ref.toOn (fun _ _ => True)).terminatesV2_transfer p q trivial h_wf h_term

/-- Contrapositive `.ub` exclusion from `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.ref_ub_not_wellFormedV2
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_ub : RefReachesOutcomeV2 (encode p) q maxSteps .ub) :
    ¬ WellFormedV2 p q :=
  (h_ref.toOn (fun _ _ => True)).ref_ub_not_wellFormedV2 p q maxSteps trivial h_ub

/-- Contrapositive `.blocked` exclusion from `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.ref_blocked_not_wellFormedV2
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (q : Query) (maxSteps : Nat)
    (h_blk : RefReachesOutcomeV2 (encode p) q maxSteps .blocked) :
    ¬ WellFormedV2 p q :=
  (h_ref.toOn (fun _ _ => True)).ref_blocked_not_wellFormedV2 p q maxSteps
    trivial h_blk

/-- Top-level `BodyVerifiedV2` transfer under `SafetyRefinementV2Bundle`:
every valid Profile v2 entry query satisfying an `unsafe` body's precondition
is `RefWellFormedV2` in `lean-miri`. -/
theorem SafetyRefinementV2Bundle.bodyVerifiedV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (defId : DefId) (body : Body) (safetyPre : Query → Prop)
    (h_bv : BodyVerifiedV2 p defId body safetyPre) :
    MirSemantics.getElem? p.bodies defId = some body ∧
    BodyStaticAdmittedV2 p body = true ∧
    ∀ q : Query,
      ValidEntryArgsV2 body q →
      (body.isUnsafe = true → safetyPre q) →
      RefWellFormedV2 (encode (entryProgForBody p defId)) q :=
  (h_ref.toOn (fun _ _ => True)).bodyVerifiedV2_transfer p defId body safetyPre
    (fun _ _ _ => trivial) h_bv

/-- Top-level `ProgramVerifiedV2` transfer under `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.programVerifiedV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode)
    (p : Program) (specs : SpecsV2)
    (h_pv : ProgramVerifiedV2 p specs) :
    Nat.beq p.pointerWidthBits 64 = true ∧
    Nat.beq p.mirProfileVersion 2 = true ∧
    !p.bodies.isEmpty = true ∧
    Nat.blt p.entryDefId p.bodies.length = true ∧
    bodiesHaveUniqueIdentities p.bodies = true ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? p.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody p defId)) q) ∧
    specs.property p :=
  (h_ref.toOn (fun _ _ => True)).programVerifiedV2_transfer p specs
    (fun _ _ _ _ _ _ => trivial) h_pv

/-- Top-level `CrateTheoremV2` transfer under `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.crateTheoremV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode) (c : MirSemantics.CrateV2)
    (h_ct : MirSemantics.CrateTheoremV2 c) :
    c.program.scope = VerificationScope.crate ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody c.program defId)) q) ∧
    c.specs.property c.program :=
  (h_ref.toOn (fun _ _ => True)).crateTheoremV2_transfer c
    (fun _ _ _ _ _ _ => trivial) h_ct

/-- Top-level `UnitTheoremV2` transfer under `SafetyRefinementV2Bundle`. -/
theorem SafetyRefinementV2Bundle.unitTheoremV2_transfer
    {encode : Program → RefProg}
    (h_ref : SafetyRefinementV2Bundle encode) (c : MirSemantics.CrateV2)
    (h_ut : MirSemantics.UnitTheoremV2 c) :
    c.program.scope = VerificationScope.unit ∧
    (∀ (defId : DefId) (body : Body),
      MirSemantics.getElem? c.program.bodies defId = some body →
      ∀ q : Query,
        ValidEntryArgsV2 body q →
        (body.isUnsafe = true → c.specs.safety body.identity q) →
        RefWellFormedV2 (encode (entryProgForBody c.program defId)) q) ∧
    c.specs.property c.program :=
  (h_ref.toOn (fun _ _ => True)).unitTheoremV2_transfer c
    (fun _ _ _ _ _ _ => trivial) h_ut

/-- Unified `FaultKind`-indexed equivalence from `BiFaultEquivV2On`. -/
theorem BiFaultEquivV2On.fault_iff {D : Program → Query → Prop}
    {encode : Program → RefProg} (h_bi : BiFaultEquivV2On D encode)
    (p : Program) (q : Query) (k : FaultKind) (h_dom : D p q) :
    ReachesResultV2 p q (.fault k) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeV2 (encode p) q maxSteps (faultToRefOutcome k) := by
  cases k with
  | undefined => exact h_bi.ub_iff p q h_dom
  | unsupported => exact h_bi.unsupported_iff p q h_dom

/-- Existential UB-refutation transfer from `BiFaultEquivV2On`. -/
theorem BiFaultEquivV2On.ub_refutationV2_transfer {D : Program → Query → Prop}
    {encode : Program → RefProg} (h_bi : BiFaultEquivV2On D encode)
    (p : Program) (q : Query) (h_dom : D p q)
    (h_ub : ReachesResultV2 p q (.fault .undefined)) :
    (∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .ub) ∧
      ¬ RefWellFormedV2 (encode p) q := by
  let ⟨ms, h_rub⟩ := (h_bi.ub_iff p q h_dom).1 h_ub
  exact ⟨⟨ms, h_rub⟩, fun h_rwf => (h_rwf ms).2.1 h_rub⟩

/-- Existential blocked-fault refutation transfer from `BiFaultEquivV2On`. -/
theorem BiFaultEquivV2On.unsupported_refutationV2_transfer
    {D : Program → Query → Prop} {encode : Program → RefProg}
    (h_bi : BiFaultEquivV2On D encode)
    (p : Program) (q : Query) (h_dom : D p q)
    (h_unsup : ReachesResultV2 p q (.fault .unsupported)) :
    (∃ maxSteps : Nat, RefReachesOutcomeV2 (encode p) q maxSteps .blocked) ∧
      ¬ RefWellFormedV2 (encode p) q := by
  let ⟨ms, h_rblk⟩ := (h_bi.unsupported_iff p q h_dom).1 h_unsup
  exact ⟨⟨ms, h_rblk⟩, fun h_rwf => (h_rwf ms).2.2 h_rblk⟩

/-- Restrict a universal `BiFaultEquivV2Bundle` to any domain `D`. -/
theorem BiFaultEquivV2Bundle.toOn {encode : Program → RefProg}
    (h : BiFaultEquivV2Bundle encode) (D : Program → Query → Prop) :
    BiFaultEquivV2On D encode :=
  ⟨fun p q _ => h.ub_iff p q, fun p q _ => h.unsupported_iff p q⟩

/-- Universal `WellFormedV2` fault-absence reflection from
`BiFaultEquivV2Bundle`. -/
theorem BiFaultEquivV2Bundle.wellFormedV2_no_ref_fault
    {encode : Program → RefProg} (h_bi : BiFaultEquivV2Bundle encode)
    (p : Program) (q : Query) (h_wf : WellFormedV2 p q) (maxSteps : Nat) :
    ¬ RefReachesOutcomeV2 (encode p) q maxSteps .ub ∧
      ¬ RefReachesOutcomeV2 (encode p) q maxSteps .blocked :=
  ⟨fun h_ub => h_wf.2 .undefined ((h_bi.ub_iff p q).2 ⟨maxSteps, h_ub⟩),
    fun h_blk =>
      h_wf.2 .unsupported ((h_bi.unsupported_iff p q).2 ⟨maxSteps, h_blk⟩)⟩

/-! ## Section 2: Corresponded-Fragment Layout, Codec & `CallerMemory` Laws -/

/-- Corresponded Profile v2 fixed-size data types (`[T; N]` over scalars,
`bool`, `char`, `Ordering`, `()`, `!`, and fieldless enums); types outside this
fragment fail closed to `false`. -/
noncomputable def inCorrespondedDataTyV2 : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum _ => true
  | .array elem _ => inCorrespondedDataTyV2 elem
  | _ => false

/-- Corresponded Profile v2 pointee types (integer slices `[int]` and
corresponded fixed-size data types). -/
noncomputable def inCorrespondedPointeeTyV2 : MirTy → Bool
  | .slice (.int _ _) => true
  | pt => inCorrespondedDataTyV2 pt

/-- Corresponded Profile v2 sized types with a
`Trusted.MirSemantics.layoutOfTyV2` layout descriptor (`bool`, integers, `char`,
`Ordering`, `()`, `!`, fieldless enums, thin/wide pointers & references to
corresponded pointees, `RangeTo`/`RangeFrom<usize>`, overflow pairs
`(int, bool)`, and corresponded arrays). -/
noncomputable def inCorrespondedLayoutTyV2 : MirTy → Bool
  | .bool | .int _ _ | .char | .ordering | .unit | .never => true
  | .enum _ => true
  | .rawPtr _ pt | .ref _ pt => inCorrespondedPointeeTyV2 pt
  | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => true
  | .array elem _ => inCorrespondedDataTyV2 elem
  | .tuple [.int _ _, .bool] => true
  | _ => false

mutual
  /-- Corresponded Profile v2 Stage-2 local types; any `MirTy` constructors
  outside this Stage-2 fragment return `false`. -/
  noncomputable def inCorrespondedTyV2 : MirTy → Bool
    | .bool | .int _ _ | .char | .ordering | .unit | .never => true
    | .enum _ => true
    | .array elem _ => inCorrespondedDataTyV2 elem
    | .rawPtr _ pt | .ref _ pt => inCorrespondedPointeeTyV2 pt
    | .rangeTo (.int .isize false) | .rangeFrom (.int .isize false) => true
    | .tuple fs => inCorrespondedTyListV2 fs
    | _ => false

  /-- Pointwise `inCorrespondedTyV2` check across tuple/parameter type lists. -/
  noncomputable def inCorrespondedTyListV2 : List MirTy → Bool
    | [] => true
    | t :: ts => inCorrespondedTyV2 t && inCorrespondedTyListV2 ts
end

/-- Combined corresponded Profile v2 fragment covering both local types and
corresponded pointee types (including unsized `.slice (.int _ _)`). -/
noncomputable def inCorrespondedFragmentTyV2 (ty : MirTy) : Bool :=
  inCorrespondedTyV2 ty || inCorrespondedPointeeTyV2 ty

mutual
  /-- Corresponded Profile v2 runtime values; any `Val` constructors outside
  this Stage-2 fragment return `false`. -/
  noncomputable def inCorrespondedValV2 : Val → Bool
    | .scalar _ | .ptr _ | .slicePtr _ _ | .rangeTo _ | .rangeFrom _
    | .bool _ | .char _ | .ordering _ | .unit | .enumVal _ _ => true
    | .array vs | .tuple vs => inCorrespondedValListV2 vs
    | _ => false

  /-- Pointwise `inCorrespondedValV2` check across value lists. -/
  noncomputable def inCorrespondedValListV2 : List Val → Bool
    | [] => true
    | v :: vs => inCorrespondedValV2 v && inCorrespondedValListV2 vs
end

mutual
  private inductive CorrespondedValV2View : Val → Prop where
    | scalar (sv : _) : CorrespondedValV2View (.scalar sv)
    | ptr (pv : _) : CorrespondedValV2View (.ptr pv)
    | slicePtr (pv : _) (len : _) : CorrespondedValV2View (.slicePtr pv len)
    | rangeTo (e : _) : CorrespondedValV2View (.rangeTo e)
    | rangeFrom (s : _) : CorrespondedValV2View (.rangeFrom s)
    | bool (b : _) : CorrespondedValV2View (.bool b)
    | char (c : _) : CorrespondedValV2View (.char c)
    | ordering (o : _) : CorrespondedValV2View (.ordering o)
    | unit : CorrespondedValV2View .unit
    | enumVal (e : _) (i : _) : CorrespondedValV2View (.enumVal e i)
    | array (vs : List Val) :
        CorrespondedValListV2View vs → CorrespondedValV2View (.array vs)
    | tuple (vs : List Val) :
        CorrespondedValListV2View vs → CorrespondedValV2View (.tuple vs)

  private inductive CorrespondedValListV2View : List Val → Prop where
    | nil : CorrespondedValListV2View []
    | cons (v : Val) (vs : List Val) :
        CorrespondedValV2View v → CorrespondedValListV2View vs →
        CorrespondedValListV2View (v :: vs)
end

mutual
  private theorem inCorrespondedValV2_view :
      ∀ (v : Val), inCorrespondedValV2 v = true → CorrespondedValV2View v
    | v, h => by
      cases v with
      | scalar sv => exact .scalar sv
      | ptr pv => exact .ptr pv
      | slicePtr pv len => exact .slicePtr pv len
      | rangeTo e => exact .rangeTo e
      | rangeFrom s => exact .rangeFrom s
      | bool b => exact .bool b
      | char c => exact .char c
      | ordering o => exact .ordering o
      | unit => exact .unit
      | enumVal e i => exact .enumVal e i
      | array vs => exact .array vs (inCorrespondedValListV2_view vs h)
      | tuple vs => exact .tuple vs (inCorrespondedValListV2_view vs h)
      | _ => cases h

  private theorem inCorrespondedValListV2_view :
      ∀ (vs : List Val),
        inCorrespondedValListV2 vs = true → CorrespondedValListV2View vs
    | [], _ => .nil
    | v :: vs, h => by
      dsimp only [inCorrespondedValListV2] at h
      cases hv : inCorrespondedValV2 v with
      | false => rw [hv, Bool.false_and] at h; cases h
      | true =>
        rw [hv, Bool.true_and] at h
        exact .cons v vs (inCorrespondedValV2_view v hv)
          (inCorrespondedValListV2_view vs h)
end

private inductive CorrespondedDataTyV2View : MirTy → Prop where
  | bool : CorrespondedDataTyV2View .bool
  | int (w : _) (s : _) : CorrespondedDataTyV2View (.int w s)
  | char : CorrespondedDataTyV2View .char
  | ordering : CorrespondedDataTyV2View .ordering
  | unit : CorrespondedDataTyV2View .unit
  | never : CorrespondedDataTyV2View .never
  | enum (e : _) : CorrespondedDataTyV2View (.enum e)
  | array (elem : MirTy) (len : Nat) :
      CorrespondedDataTyV2View elem → CorrespondedDataTyV2View (.array elem len)

private theorem inCorrespondedDataTyV2_view :
    ∀ (ty : MirTy), inCorrespondedDataTyV2 ty = true →
      CorrespondedDataTyV2View ty
  | ty, h => by
    cases ty with
    | bool => exact .bool
    | int w s => exact .int w s
    | char => exact .char
    | ordering => exact .ordering
    | unit => exact .unit
    | never => exact .never
    | enum e => exact .enum e
    | array elem len =>
      exact .array elem len (inCorrespondedDataTyV2_view elem h)
    | _ => cases h

private inductive CorrespondedPointeeTyV2View : MirTy → Prop where
  | sliceInt (w : _) (s : _) : CorrespondedPointeeTyV2View (.slice (.int w s))
  | data (pt : MirTy) :
      CorrespondedDataTyV2View pt → CorrespondedPointeeTyV2View pt

private theorem inCorrespondedPointeeTyV2_view
    (pt : MirTy) (h : inCorrespondedPointeeTyV2 pt = true) :
    CorrespondedPointeeTyV2View pt := by
  cases pt with
  | slice elem =>
    cases elem with
    | int w s => exact .sliceInt w s
    | _ => cases h
  | _ => exact .data _ (inCorrespondedDataTyV2_view _ h)

private inductive CorrespondedLayoutTyV2View : MirTy → Prop where
  | bool : CorrespondedLayoutTyV2View .bool
  | int (w : _) (s : _) : CorrespondedLayoutTyV2View (.int w s)
  | char : CorrespondedLayoutTyV2View .char
  | ordering : CorrespondedLayoutTyV2View .ordering
  | unit : CorrespondedLayoutTyV2View .unit
  | never : CorrespondedLayoutTyV2View .never
  | enum (e : _) : CorrespondedLayoutTyV2View (.enum e)
  | rawPtr (m : _) (pt : MirTy) :
      CorrespondedPointeeTyV2View pt →
      CorrespondedLayoutTyV2View (.rawPtr m pt)
  | ref (m : _) (pt : MirTy) :
      CorrespondedPointeeTyV2View pt →
      CorrespondedLayoutTyV2View (.ref m pt)
  | rangeTo : CorrespondedLayoutTyV2View (.rangeTo (.int .isize false))
  | rangeFrom : CorrespondedLayoutTyV2View (.rangeFrom (.int .isize false))
  | array (elem : MirTy) (len : Nat) :
      CorrespondedDataTyV2View elem →
      CorrespondedLayoutTyV2View (.array elem len)
  | overflowPair (w : _) (s : _) :
      CorrespondedLayoutTyV2View (.tuple [.int w s, .bool])

private theorem inCorrespondedLayoutTyV2_view
    (ty : MirTy) (h : inCorrespondedLayoutTyV2 ty = true) :
    CorrespondedLayoutTyV2View ty := by
  cases ty with
  | bool => exact .bool
  | int w s => exact .int w s
  | char => exact .char
  | ordering => exact .ordering
  | unit => exact .unit
  | never => exact .never
  | enum e => exact .enum e
  | rawPtr m pt => exact .rawPtr m pt (inCorrespondedPointeeTyV2_view pt h)
  | ref m pt => exact .ref m pt (inCorrespondedPointeeTyV2_view pt h)
  | rangeTo inner =>
    cases inner with
    | int w s =>
      cases w <;> first
        | (cases s <;> first | exact .rangeTo | cases h)
        | cases h
    | _ => cases h
  | rangeFrom inner =>
    cases inner with
    | int w s =>
      cases w <;> first
        | (cases s <;> first | exact .rangeFrom | cases h)
        | cases h
    | _ => cases h
  | array elem len =>
    exact .array elem len (inCorrespondedDataTyV2_view elem h)
  | tuple fs =>
    cases fs with
    | nil => cases h
    | cons a fs1 =>
      cases a with
      | int w s =>
        cases fs1 with
        | nil => cases h
        | cons b fs2 =>
          cases b with
          | bool =>
            cases fs2 with
            | nil => exact .overflowPair w s
            | cons _ _ => cases h
          | _ => cases h
      | _ => cases h
  | _ => cases h

mutual
  private inductive CorrespondedTyV2View : MirTy → Prop where
    | bool : CorrespondedTyV2View .bool
    | int (w : _) (s : _) : CorrespondedTyV2View (.int w s)
    | char : CorrespondedTyV2View .char
    | ordering : CorrespondedTyV2View .ordering
    | unit : CorrespondedTyV2View .unit
    | never : CorrespondedTyV2View .never
    | enum (e : _) : CorrespondedTyV2View (.enum e)
    | array (elem : MirTy) (len : Nat) :
        CorrespondedDataTyV2View elem → CorrespondedTyV2View (.array elem len)
    | rawPtr (m : _) (pt : MirTy) :
        CorrespondedPointeeTyV2View pt → CorrespondedTyV2View (.rawPtr m pt)
    | ref (m : _) (pt : MirTy) :
        CorrespondedPointeeTyV2View pt → CorrespondedTyV2View (.ref m pt)
    | rangeTo : CorrespondedTyV2View (.rangeTo (.int .isize false))
    | rangeFrom : CorrespondedTyV2View (.rangeFrom (.int .isize false))
    | tuple (fs : List MirTy) :
        CorrespondedTyListV2View fs → CorrespondedTyV2View (.tuple fs)

  private inductive CorrespondedTyListV2View : List MirTy → Prop where
    | nil : CorrespondedTyListV2View []
    | cons (t : MirTy) (ts : List MirTy) :
        CorrespondedTyV2View t → CorrespondedTyListV2View ts →
        CorrespondedTyListV2View (t :: ts)
end

mutual
  private theorem inCorrespondedTyV2_view :
      ∀ (ty : MirTy), inCorrespondedTyV2 ty = true → CorrespondedTyV2View ty
    | ty, h => by
      cases ty with
      | bool => exact .bool
      | int w s => exact .int w s
      | char => exact .char
      | ordering => exact .ordering
      | unit => exact .unit
      | never => exact .never
      | enum e => exact .enum e
      | array elem len =>
        exact .array elem len (inCorrespondedDataTyV2_view elem h)
      | rawPtr m pt =>
        exact .rawPtr m pt (inCorrespondedPointeeTyV2_view pt h)
      | ref m pt =>
        exact .ref m pt (inCorrespondedPointeeTyV2_view pt h)
      | rangeTo inner =>
        cases inner with
        | int w s =>
          cases w <;> first
            | (cases s <;> first | exact .rangeTo | cases h)
            | cases h
        | _ => cases h
      | rangeFrom inner =>
        cases inner with
        | int w s =>
          cases w <;> first
            | (cases s <;> first | exact .rangeFrom | cases h)
            | cases h
        | _ => cases h
      | tuple fs => exact .tuple fs (inCorrespondedTyListV2_view fs h)
      | _ => cases h

  private theorem inCorrespondedTyListV2_view :
      ∀ (fs : List MirTy),
        inCorrespondedTyListV2 fs = true → CorrespondedTyListV2View fs
    | [], _ => .nil
    | t :: ts, h => by
      dsimp only [inCorrespondedTyListV2] at h
      cases ht : inCorrespondedTyV2 t with
      | false => rw [ht, Bool.false_and] at h; cases h
      | true =>
        rw [ht, Bool.true_and] at h
        exact .cons t ts (inCorrespondedTyV2_view t ht)
          (inCorrespondedTyListV2_view ts h)
end

private theorem inCorrespondedDataTyV2_implies_inCorrespondedPointeeTyV2
    (pt : MirTy) (h : inCorrespondedDataTyV2 pt = true) :
    inCorrespondedPointeeTyV2 pt = true := by
  cases inCorrespondedDataTyV2_view pt h <;> exact h

private theorem isUnsizedTy_false_of_dataView
    {ty : MirTy} (hd : CorrespondedDataTyV2View ty) :
    isUnsizedTy ty = false := by
  cases hd <;> rfl

private theorem ptrRefLayout_thin_of_dataView (m : Trusted.MirAst.Mutability)
    {pt : MirTy} (hd : CorrespondedDataTyV2View pt) :
    refLayoutDataForTyV2 (.rawPtr m pt) = refThinPtrLayoutDataV2 ∧
    refLayoutDataForTyV2 (.ref m pt) = refThinPtrLayoutDataV2 := by
  cases hd <;> exact ⟨rfl, rfl⟩

private theorem isUnsizedTy_eq_refIsUnsizedTyV2_of_pointee
    (pt : MirTy) (h : inCorrespondedPointeeTyV2 pt = true) :
    refIsUnsizedTyV2 pt = isUnsizedTy pt := by
  cases inCorrespondedPointeeTyV2_view pt h with
  | sliceInt _ _ => rfl
  | data _ hd => cases hd <;> rfl

private theorem isUnsizedTy_eq_refIsUnsizedTyV2_of_local
    (ty : MirTy) (h : inCorrespondedTyV2 ty = true) :
    refIsUnsizedTyV2 ty = isUnsizedTy ty := by
  cases inCorrespondedTyV2_view ty h <;> rfl

/-- Exact agreement between `isUnsizedTy` and `refIsUnsizedTyV2` on the
corresponded Profile v2 fragment (`inCorrespondedFragmentTyV2`). -/
theorem isUnsizedTy_eq_refIsUnsizedTyV2_of_corresponded (ty : MirTy)
    (h_cor : inCorrespondedFragmentTyV2 ty = true) :
    refIsUnsizedTyV2 ty = isUnsizedTy ty := by
  dsimp only [inCorrespondedFragmentTyV2] at h_cor
  cases h_l : inCorrespondedTyV2 ty with
  | true => exact isUnsizedTy_eq_refIsUnsizedTyV2_of_local ty h_l
  | false =>
    rw [h_l, Bool.false_or] at h_cor
    exact isUnsizedTy_eq_refIsUnsizedTyV2_of_pointee ty h_cor

/-- Exact integer layout size and natural alignment agreement between
`Trusted.MirSemantics.intLayout` and `refScalarLayoutDataV2`. -/
theorem intLayout_eq_refScalarLayoutDataV2 (w : IntWidth) (s : Bool) :
    (refScalarLayoutDataV2 w s).size.bytes.toNat = (intLayout w).size ∧
    (refScalarLayoutDataV2 w s).align.abi.pow2 = (intLayout w).alignLog2 := by
  cases w <;> exact ⟨rfl, rfl⟩

/-- Exact overflow-pair layout size and natural alignment agreement between
`Trusted.MirSemantics.overflowPairLayout` and `refOverflowPairLayoutDataV2`. -/
theorem overflowPairLayout_eq_refOverflowPairLayoutDataV2 (w : IntWidth)
    (s : Bool) :
    (refOverflowPairLayoutDataV2 w s).size.bytes.toNat =
      (overflowPairLayout w).size ∧
    (refOverflowPairLayoutDataV2 w s).align.abi.pow2 =
      (overflowPairLayout w).alignLog2 := by
  cases w <;> exact ⟨rfl, rfl⟩

private theorem layoutOfArrayV2_eq_layoutOfTyV2_of_corresponded
    (ty : MirTy) (h : inCorrespondedLayoutTyV2 ty = true) :
    layoutOfArrayV2 ty = layoutOfTyV2 ty := by
  cases inCorrespondedLayoutTyV2_view ty h with
  | enum _ =>
    unfold layoutOfTyV2
    dsimp only [layoutOfArrayV2, layoutOfTy]
  | array _ _ _ =>
    unfold layoutOfTyV2
    rfl
  | _ =>
    first
    | rfl
    | (unfold layoutOfTyV2; rfl)

private theorem layoutOfArrayV2_mod_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      ∀ (lay : Trusted.MirSemantics.LayoutData),
        layoutOfArrayV2 ty = some lay →
        (refLayoutDataForTyV2 ty).size.bytes.toNat =
          Nat.mod lay.size (Nat.pow 2 64) ∧
        (refLayoutDataForTyV2 ty).align.abi.pow2 = lay.alignLog2
  | _, .bool, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | _, .int w s, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq
    have h_int := intLayout_eq_refScalarLayoutDataV2 w s
    refine ⟨h_int.1.trans ?_, h_int.2⟩
    cases w <;> rfl
  | _, .char, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | _, .ordering, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | _, .unit, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | _, .never, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | _, .enum ety, lay, h_lay => by
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    cases h_adm : enumAdmitted ety with
    | false => rw [h_adm] at h_lay; cases h_lay
    | true =>
      rw [h_adm] at h_lay
      cases h_tr : ety.tagRepr with
      | zeroSized =>
        rw [h_tr] at h_lay
        injection h_lay with h_eq; subst h_eq
        dsimp only [refLayoutDataForTyV2, refEnumLayoutDataV2]
        rw [h_tr]; exact ⟨rfl, rfl⟩
      | scalar tagW tagS =>
        rw [h_tr] at h_lay
        injection h_lay with h_eq; subst h_eq
        dsimp only [refLayoutDataForTyV2, refEnumLayoutDataV2]
        rw [h_tr]; cases tagW <;> exact ⟨rfl, rfl⟩
  | _, .array elem len hel, lay, h_lay => by
    dsimp only [layoutOfArrayV2] at h_lay
    cases h_el : layoutOfArrayV2 elem with
    | none => rw [h_el] at h_lay; cases h_lay
    | some elemLay =>
      rw [h_el] at h_lay
      injection h_lay with h_eq; subst h_eq
      have h_ih := layoutOfArrayV2_mod_dataView hel elemLay h_el
      dsimp only [refLayoutDataForTyV2, refBaseLayoutDataV2]
      refine ⟨?_, h_ih.2⟩
      change Nat.mod (len * (refLayoutDataForTyV2 elem).size.bytes.toNat)
        (Nat.pow 2 64) = Nat.mod (len * elemLay.size) (Nat.pow 2 64)
      rw [h_ih.1]
      change HMod.hMod (len * HMod.hMod elemLay.size (Nat.pow 2 64))
          (Nat.pow 2 64) =
        HMod.hMod (len * elemLay.size) (Nat.pow 2 64)
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- Modulo-`2^64` byte-size and exact natural-alignment agreement between
`layoutOfArrayV2` and `refLayoutDataForTyV2` on every type in the corresponded
Profile v2 layout fragment (`inCorrespondedLayoutTyV2`). -/
private theorem layoutOfArrayV2_mod_eq_refLayoutDataForTyV2_of_corresponded
    (ty : MirTy) (lay : Trusted.MirSemantics.LayoutData)
    (h_cor : inCorrespondedLayoutTyV2 ty = true)
    (h_lay : layoutOfArrayV2 ty = some lay) :
    (refLayoutDataForTyV2 ty).size.bytes.toNat =
      Nat.mod lay.size (Nat.pow 2 64) ∧
    (refLayoutDataForTyV2 ty).align.abi.pow2 = lay.alignLog2 := by
  cases inCorrespondedLayoutTyV2_view ty h_cor with
  | bool => exact layoutOfArrayV2_mod_dataView .bool lay h_lay
  | int w s => exact layoutOfArrayV2_mod_dataView (.int w s) lay h_lay
  | char => exact layoutOfArrayV2_mod_dataView .char lay h_lay
  | ordering => exact layoutOfArrayV2_mod_dataView .ordering lay h_lay
  | unit => exact layoutOfArrayV2_mod_dataView .unit lay h_lay
  | never => exact layoutOfArrayV2_mod_dataView .never lay h_lay
  | enum ety => exact layoutOfArrayV2_mod_dataView (.enum ety) lay h_lay
  | array elem len hel =>
    exact layoutOfArrayV2_mod_dataView (.array elem len hel) lay h_lay
  | rawPtr m pt h_pt =>
    cases h_pt with
    | sliceInt w s =>
      dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
      injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
    | data pt hd =>
      dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
      rw [isUnsizedTy_false_of_dataView hd] at h_lay
      injection h_lay with h_eq; subst h_eq
      rw [(ptrRefLayout_thin_of_dataView m hd).1]; exact ⟨rfl, rfl⟩
  | ref m pt h_pt =>
    cases h_pt with
    | sliceInt w s =>
      dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
      injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
    | data pt hd =>
      dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
      rw [isUnsizedTy_false_of_dataView hd] at h_lay
      injection h_lay with h_eq; subst h_eq
      rw [(ptrRefLayout_thin_of_dataView m hd).2]; exact ⟨rfl, rfl⟩
  | rangeTo =>
    dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | rangeFrom =>
    dsimp only [layoutOfArrayV2, layoutOfTy, layoutOfPtrOrRangeV2] at h_lay
    injection h_lay with h_eq; subst h_eq; exact ⟨rfl, rfl⟩
  | overflowPair w s =>
    dsimp only [layoutOfArrayV2, layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq
    have h_op := overflowPairLayout_eq_refOverflowPairLayoutDataV2 w s
    refine ⟨h_op.1.trans ?_, h_op.2⟩
    cases w <;> rfl

/-- Corresponded-fragment Profile v2 layout agreement: every `MirTy` in
`inCorrespondedLayoutTyV2` admitted by `layoutOfTyV2` whose byte size fits in
64 bits (`< 2^64`) agrees in both byte size and natural ABI alignment
(`alignLog2 = align.abi.pow2`) with `refLayoutDataForTyV2`. -/
theorem layoutOfTyV2_eq_refLayoutDataForTyV2_of_corresponded (ty : MirTy)
    (lay : Trusted.MirSemantics.LayoutData)
    (h_cor : inCorrespondedLayoutTyV2 ty = true)
    (h_lay : layoutOfTyV2 ty = some lay)
    (h_fit : Nat.blt lay.size (Nat.pow 2 64) = true) :
    (refLayoutDataForTyV2 ty).size.bytes.toNat = lay.size ∧
    (refLayoutDataForTyV2 ty).align.abi.pow2 = lay.alignLog2 := by
  rw [← layoutOfArrayV2_eq_layoutOfTyV2_of_corresponded ty h_cor] at h_lay
  have h_m :=
    layoutOfArrayV2_mod_eq_refLayoutDataForTyV2_of_corresponded ty lay h_cor
      h_lay
  exact ⟨h_m.1.trans (Nat.mod_eq_of_lt (Nat.blt_eq.mp h_fit)), h_m.2⟩

private theorem refNatNotElem_eq_natNotElem (x : Nat) :
    ∀ (xs : List Nat), refNatNotElem x xs = natNotElem x xs
  | [] => rfl
  | y :: ys => by
    dsimp only [refNatNotElem, natNotElem]
    rw [refNatNotElem_eq_natNotElem x ys]

/-- Every allocation in `cm.allocations` has a non-zero 64-bit `AllocId`. -/
theorem refAllocIdFitsU64V2_of_lt {aid : Trusted.MirAst.AllocId}
    (h_nz : aid ≠ 0) (h_lt : aid < Nat.pow 2 64) :
    refAllocIdFitsU64V2 aid = true := by
  have h_u64 : (UInt64.ofNat aid).toNat = aid := u64_ofNat_toNat_of_lt h_lt
  have h_nbeq : (!Nat.beq aid 0) = true := by
    cases h_z : Nat.beq aid 0 with
    | false => rfl
    | true => exact False.elim (h_nz (Nat.eq_of_beq_eq_true h_z))
  dsimp only [refAllocIdFitsU64V2]
  rw [h_nbeq, h_u64, Nat.beq_refl]
  rfl

/-- `refAllocIdsValidV2` implies `Trusted.MirSemantics.allocIdsValid`. -/
theorem refAllocIdsValidV2_implies_allocIdsValid :
    ∀ (seen : List Trusted.MirAst.AllocId)
      (allocs : List Trusted.MirSemantics.Allocation),
      refAllocIdsValidV2 seen allocs = true →
      allocIdsValid seen allocs = true
  | _, [], _ => rfl
  | seen, a :: rest, h => by
    dsimp only [refAllocIdsValidV2, refAllocIdFitsU64V2] at h
    simp only [Bool.and_eq_true] at h
    have h_r := refAllocIdsValidV2_implies_allocIdsValid (a.allocId :: seen)
      rest h.2
    dsimp only [allocIdsValid, isizeMaxBytes]
    rw [h.1.1.1.1.1, ← refNatNotElem_eq_natNotElem a.allocId seen, h.1.1.1.2,
      h.1.1.2, h.1.2, h_r]
    rfl

/-- `refValidCallerMemoryV2` implies `Trusted.MirSemantics.validCallerMemory`.
-/
theorem refValidCallerMemoryV2_implies_validCallerMemory (cm : CallerMemory)
    (h : refValidCallerMemoryV2 cm = true) :
    validCallerMemory cm = true :=
  refAllocIdsValidV2_implies_allocIdsValid [] cm.allocations h

/-- Exact agreement between `allocIdsValid` and `refAllocIdsValidV2` whenever
every allocation ID fits in `UInt64`. -/
theorem allocIdsValid_eq_refAllocIdsValidV2_of_fit :
    ∀ (seen : List Trusted.MirAst.AllocId)
      (allocs : List Trusted.MirSemantics.Allocation),
      (∀ a, a ∈ allocs → Nat.blt a.allocId (Nat.pow 2 64) = true) →
      refAllocIdsValidV2 seen allocs = allocIdsValid seen allocs
  | _, [], _ => rfl
  | seen, a :: rest, h_fit => by
    have h_a_lt : a.allocId < Nat.pow 2 64 :=
      Nat.blt_eq.mp (h_fit a (List.Mem.head rest))
    have h_u64 : (UInt64.ofNat a.allocId).toNat = a.allocId :=
      u64_ofNat_toNat_of_lt h_a_lt
    have h_round : Nat.beq (UInt64.ofNat a.allocId).toNat a.allocId = true := by
      rw [h_u64, Nat.beq_refl]
    dsimp only [refAllocIdsValidV2, refAllocIdFitsU64V2, allocIdsValid,
      isizeMaxBytes]
    rw [h_round, Bool.and_true, refNatNotElem_eq_natNotElem a.allocId seen,
      allocIdsValid_eq_refAllocIdsValidV2_of_fit (a.allocId :: seen) rest
        (fun x hx => h_fit x (List.Mem.tail a hx))]

/-- Exact agreement between `validCallerMemory` and `refValidCallerMemoryV2`
whenever every caller allocation ID fits in `UInt64`. -/
theorem validCallerMemory_eq_refValidCallerMemoryV2_of_fit (cm : CallerMemory)
    (h_fit : ∀ a, a ∈ cm.allocations →
      Nat.blt a.allocId (Nat.pow 2 64) = true) :
    refValidCallerMemoryV2 cm = validCallerMemory cm :=
  allocIdsValid_eq_refAllocIdsValidV2_of_fit [] cm.allocations h_fit

/-- Exact agreement between `maxAllocId` and `refMaxAllocIdV2`. -/
theorem maxAllocId_eq_refMaxAllocIdV2 :
    ∀ (allocs : List Trusted.MirSemantics.Allocation),
      refMaxAllocIdV2 allocs = maxAllocId allocs
  | [] => rfl
  | a :: rest => by
    dsimp only [refMaxAllocIdV2, maxAllocId]
    rw [maxAllocId_eq_refMaxAllocIdV2 rest]

/-- Exact agreement between `refHasAllocIdV2` and
`(findAllocation id _).isSome`. -/
theorem refHasAllocIdV2_eq_findAllocation_isSome
    (id : Trusted.MirAst.AllocId) :
    ∀ (allocs : List Trusted.MirSemantics.Allocation),
      refHasAllocIdV2 id allocs = (findAllocation id allocs).isSome
  | [] => rfl
  | a :: rest => by
    dsimp only [refHasAllocIdV2, findAllocation]
    cases h_eq : Nat.beq a.allocId id with
    | true => rfl
    | false => exact refHasAllocIdV2_eq_findAllocation_isSome id rest

private theorem refIsSupportedDataTyV2_eq_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      refIsSupportedDataTyV2 ty = isSupportedV2DataTy ty
  | _, .bool | _, .int _ _ | _, .char | _, .ordering | _, .unit
  | _, .never => rfl
  | _, .enum _ => refEnumAdmitted_eq _
  | _, .array _ _ hel => by
    dsimp only [refIsSupportedDataTyV2, isSupportedV2DataTy]
    exact refIsSupportedDataTyV2_eq_dataView hel

/-- On `inCorrespondedDataTyV2`, `refIsSupportedDataTyV2` agrees identically
with `Trusted.MirSemantics.isSupportedV2DataTy`. -/
theorem refIsSupportedDataTyV2_eq_of_corresponded
    {ty : MirTy} (h : inCorrespondedDataTyV2 ty = true) :
    refIsSupportedDataTyV2 ty = isSupportedV2DataTy ty :=
  refIsSupportedDataTyV2_eq_dataView (inCorrespondedDataTyV2_view ty h)

private theorem refIsSupportedDataTyV2_sound_aux :
    ∀ (ty : MirTy), refIsSupportedDataTyV2 ty = true →
      inCorrespondedDataTyV2 ty = true ∧ isSupportedV2DataTy ty = true
  | ty, h => by
    cases ty with
    | bool => exact ⟨rfl, rfl⟩
    | int _ _ => exact ⟨rfl, rfl⟩
    | char => exact ⟨rfl, rfl⟩
    | ordering => exact ⟨rfl, rfl⟩
    | unit => exact ⟨rfl, rfl⟩
    | never => exact ⟨rfl, rfl⟩
    | enum ety =>
      exact ⟨rfl, (refIsSupportedDataTyV2_eq_dataView (.enum ety)).symm.trans h⟩
    | array elem _ =>
      exact refIsSupportedDataTyV2_sound_aux elem h
    | _ => cases h

/-- Unconditional soundness of `refIsSupportedDataTyV2`: any `MirTy` admitted
by `ProfileV2RefMachine` belongs to `inCorrespondedDataTyV2` and is admitted
by `Trusted.MirSemantics.isSupportedV2DataTy`. -/
theorem refIsSupportedDataTyV2_implies_isSupportedV2DataTy
    {ty : MirTy} (h : refIsSupportedDataTyV2 ty = true) :
    inCorrespondedDataTyV2 ty = true ∧ isSupportedV2DataTy ty = true :=
  refIsSupportedDataTyV2_sound_aux ty h

/-- On `inCorrespondedPointeeTyV2`, `refIsSupportedPointeeTyV2` agrees
identically with Profile v2's pointee admission rule. -/
theorem refIsSupportedPointeeTyV2_eq_of_corresponded
    {pt : MirTy} (h : inCorrespondedPointeeTyV2 pt = true) :
    refIsSupportedPointeeTyV2 pt =
      match pt with
      | .slice (.int _ _) => true
      | _ => isSupportedV2DataTy pt := by
  cases inCorrespondedPointeeTyV2_view pt h with
  | sliceInt _ _ => rfl
  | data _ hd =>
    cases hd with
    | bool | int _ _ | char | ordering | unit | never => rfl
    | enum _ => exact refEnumAdmitted_eq _
    | array _ _ hel =>
      dsimp only [refIsSupportedPointeeTyV2, refIsSupportedDataTyV2,
        isSupportedV2DataTy]
      exact refIsSupportedDataTyV2_eq_dataView hel

private theorem refIsSupportedPointeeTyV2_sound_aux
    (pt : MirTy) (h : refIsSupportedPointeeTyV2 pt = true) :
    inCorrespondedPointeeTyV2 pt = true := by
  cases pt with
  | slice elem =>
    cases elem with
    | int _ _ => rfl
    | _ => cases h
  | _ =>
    exact inCorrespondedDataTyV2_implies_inCorrespondedPointeeTyV2 _
      (refIsSupportedDataTyV2_implies_isSupportedV2DataTy h).1

/-- Unconditional soundness of `refIsSupportedPointeeTyV2`: any pointee type
admitted by `ProfileV2RefMachine` belongs to `inCorrespondedPointeeTyV2`. -/
theorem refIsSupportedPointeeTyV2_implies_corresponded
    {pt : MirTy} (h : refIsSupportedPointeeTyV2 pt = true) :
    inCorrespondedPointeeTyV2 pt = true :=
  refIsSupportedPointeeTyV2_sound_aux pt h

private theorem isSupportedV2LocalTy_ptr_dataView
    (m : Trusted.MirAst.Mutability) {pt : MirTy}
    (hd : CorrespondedDataTyV2View pt) :
    refIsSupportedLocalTyV2 (.ref m pt) = isSupportedV2LocalTy (.ref m pt) ∧
    refIsSupportedLocalTyV2 (.rawPtr m pt) =
      isSupportedV2LocalTy (.rawPtr m pt) := by
  have h_pt := refIsSupportedDataTyV2_eq_dataView hd
  cases hd with
  | enum _ =>
    dsimp only [refIsSupportedLocalTyV2, refIsSupportedPointeeTyV2,
      refIsSupportedDataTyV2, isSupportedV2LocalTy, isSupportedV2PointeeTy,
      isSizedNoRefV2Ty, isSupportedV2DataTy, isOverflowPairTy,
      isSupportedScalarOrUnitTy] at h_pt
    dsimp only [refIsSupportedLocalTyV2, refIsSupportedPointeeTyV2,
      refIsSupportedDataTyV2, isSupportedV2LocalTy, isSupportedV2PointeeTy,
      isSizedNoRefV2Ty, isSupportedV2DataTy, isOverflowPairTy,
      isSupportedScalarOrUnitTy]
    rw [Bool.not_false, Bool.true_and] at h_pt
    rw [Bool.not_false, Bool.true_and, Bool.or_self]
    exact ⟨h_pt, h_pt⟩
  | _ => exact ⟨h_pt, h_pt⟩

mutual
  private theorem isSupportedV2LocalTy_eq_tyView :
      ∀ {ty : MirTy}, CorrespondedTyV2View ty →
        refIsSupportedLocalTyV2 ty = isSupportedV2LocalTy ty
    | _, .bool | _, .int _ _ | _, .char | _, .ordering
    | _, .unit | _, .never | _, .rangeTo | _, .rangeFrom => rfl
    | _, .enum _ => refEnumAdmitted_eq _
    | _, .array _ _ hel => by
      dsimp only [refIsSupportedLocalTyV2, isSupportedV2LocalTy]
      exact refIsSupportedDataTyV2_eq_dataView hel
    | _, .rawPtr m _ hpt => by
      cases hpt with
      | sliceInt _ _ => rfl
      | data _ hd => exact (isSupportedV2LocalTy_ptr_dataView m hd).2
    | _, .ref m _ hpt => by
      cases hpt with
      | sliceInt _ _ => rfl
      | data _ hd => exact (isSupportedV2LocalTy_ptr_dataView m hd).1
    | _, .tuple _ hfs => isSupportedV2LocalTyList_eq_tyListView hfs

  private theorem isSupportedV2LocalTyList_eq_tyListView :
      ∀ {fs : List MirTy}, CorrespondedTyListV2View fs →
        refIsSupportedLocalTyListV2 fs = isSupportedV2LocalTyList fs
    | _, .nil => rfl
    | _, .cons _ _ ht hts => by
      dsimp only [refIsSupportedLocalTyListV2, isSupportedV2LocalTyList]
      rw [isSupportedV2LocalTy_eq_tyView ht,
        isSupportedV2LocalTyList_eq_tyListView hts]
end

/-- On `inCorrespondedTyV2`, `isSupportedV2LocalTy` and
`refIsSupportedLocalTyV2` agree identically. -/
theorem isSupportedV2LocalTy_eq_refIsSupportedLocalTyV2_of_corresponded
    {ty : MirTy} (h : inCorrespondedTyV2 ty = true) :
    refIsSupportedLocalTyV2 ty = isSupportedV2LocalTy ty :=
  isSupportedV2LocalTy_eq_tyView (inCorrespondedTyV2_view ty h)

/-- Pointwise `inCorrespondedTyListV2`-guarded agreement between
`isSupportedV2LocalTyList` and `refIsSupportedLocalTyListV2`. -/
theorem isSupportedV2LocalTyList_eq_refIsSupportedLocalTyListV2_of_corresponded
    {fs : List MirTy} (h : inCorrespondedTyListV2 fs = true) :
    refIsSupportedLocalTyListV2 fs = isSupportedV2LocalTyList fs :=
  isSupportedV2LocalTyList_eq_tyListView (inCorrespondedTyListV2_view fs h)

private theorem isSupportedV2LocalTy_eq_rawPtr_of_pointee
    (m : Trusted.MirAst.Mutability) {pt : MirTy}
    (h_pt : inCorrespondedPointeeTyV2 pt = true) :
    refIsSupportedLocalTyV2 (.rawPtr m pt) =
      isSupportedV2LocalTy (.rawPtr m pt) :=
  @isSupportedV2LocalTy_eq_refIsSupportedLocalTyV2_of_corresponded
    (.rawPtr m pt) h_pt

private theorem isSupportedV2LocalTy_eq_ref_of_pointee
    (m : Trusted.MirAst.Mutability) {pt : MirTy}
    (h_pt : inCorrespondedPointeeTyV2 pt = true) :
    refIsSupportedLocalTyV2 (.ref m pt) = isSupportedV2LocalTy (.ref m pt) :=
  @isSupportedV2LocalTy_eq_refIsSupportedLocalTyV2_of_corresponded
    (.ref m pt) h_pt

mutual
  private theorem refIsSupportedLocalTyV2_sound_aux :
      ∀ (ty : MirTy), refIsSupportedLocalTyV2 ty = true →
        inCorrespondedTyV2 ty = true ∧ isSupportedV2LocalTy ty = true
    | ty, h => by
      cases ty with
      | bool => exact ⟨rfl, rfl⟩
      | int _ _ => exact ⟨rfl, rfl⟩
      | char => exact ⟨rfl, rfl⟩
      | ordering => exact ⟨rfl, rfl⟩
      | unit => exact ⟨rfl, rfl⟩
      | never => exact ⟨rfl, rfl⟩
      | enum ety =>
        exact ⟨rfl, (isSupportedV2LocalTy_eq_tyView (.enum ety)).symm.trans h⟩
      | array elem _ =>
        exact refIsSupportedDataTyV2_implies_isSupportedV2DataTy h
      | rawPtr m pt =>
        have h_pt := refIsSupportedPointeeTyV2_implies_corresponded h
        exact ⟨h_pt, by
          rw [← isSupportedV2LocalTy_eq_rawPtr_of_pointee m h_pt]; exact h⟩
      | ref m pt =>
        have h_pt := refIsSupportedPointeeTyV2_implies_corresponded h
        exact ⟨h_pt, by
          rw [← isSupportedV2LocalTy_eq_ref_of_pointee m h_pt]; exact h⟩
      | rangeTo inner =>
        cases inner with
        | int w s =>
          cases w <;> first
            | (cases s <;> first | exact ⟨rfl, rfl⟩ | cases h)
            | cases h
        | _ => cases h
      | rangeFrom inner =>
        cases inner with
        | int w s =>
          cases w <;> first
            | (cases s <;> first | exact ⟨rfl, rfl⟩ | cases h)
            | cases h
        | _ => cases h
      | tuple fs =>
        exact refIsSupportedLocalTyListV2_implies_isSupportedV2LocalTyList h
      | _ => cases h

  /-- Pointwise soundness of `refIsSupportedLocalTyListV2`. -/
  theorem refIsSupportedLocalTyListV2_implies_isSupportedV2LocalTyList :
      ∀ {fs : List MirTy}, refIsSupportedLocalTyListV2 fs = true →
        inCorrespondedTyListV2 fs = true ∧ isSupportedV2LocalTyList fs = true
    | [], _ => ⟨rfl, rfl⟩
    | f :: rest, h => by
      dsimp only [refIsSupportedLocalTyListV2] at h
      cases hf : refIsSupportedLocalTyV2 f with
      | false => rw [hf, Bool.false_and] at h; cases h
      | true =>
        rw [hf, Bool.true_and] at h
        have h_f := refIsSupportedLocalTyV2_sound_aux f hf
        have h_r :=
          refIsSupportedLocalTyListV2_implies_isSupportedV2LocalTyList h
        exact ⟨by dsimp only [inCorrespondedTyListV2]; rw [h_f.1, h_r.1]; rfl,
          by dsimp only [isSupportedV2LocalTyList]; rw [h_f.2, h_r.2]; rfl⟩
end

/-- Unconditional soundness of `refIsSupportedLocalTyV2`: any `MirTy`
admitted by `ProfileV2RefMachine` belongs to `inCorrespondedTyV2` and
satisfies `Trusted.MirSemantics.isSupportedV2LocalTy`. -/
theorem refIsSupportedLocalTyV2_implies_isSupportedV2LocalTy
    {ty : MirTy} (h : refIsSupportedLocalTyV2 ty = true) :
    inCorrespondedTyV2 ty = true ∧ isSupportedV2LocalTy ty = true :=
  refIsSupportedLocalTyV2_sound_aux ty h

private theorem refCheckValUniformV2_congr_view (f g : Val → Bool) :
    ∀ {vs : List Val}, CorrespondedValListV2View vs →
      (∀ x, CorrespondedValV2View x → f x = g x) →
      refCheckValUniformV2 f vs = checkValUniformV2 g vs
  | _, .nil, _ => rfl
  | _, .cons v vs hv hvs, h => by
    dsimp only [refCheckValUniformV2, checkValUniformV2]
    rw [h v hv, refCheckValUniformV2_congr_view f g hvs h]

private theorem isUnsizedTy_eq_refIsUnsizedTyV2_pointeeView :
    ∀ {pt : MirTy}, CorrespondedPointeeTyV2View pt →
      refIsUnsizedTyV2 pt = isUnsizedTy pt
  | _, .sliceInt _ _ => rfl
  | _, .data _ hd => by cases hd <;> rfl

private theorem checkValV2_slicePtr_dataView (pv : PtrVal) (len : UInt64)
    (m : Trusted.MirAst.Mutability) {pt : MirTy}
    (hd : CorrespondedDataTyV2View pt) :
    checkRefValV2 (.slicePtr pv len) (.rawPtr m pt) =
      checkValV2 (.slicePtr pv len) (.rawPtr m pt) ∧
    checkRefValV2 (.slicePtr pv len) (.ref m pt) =
      checkValV2 (.slicePtr pv len) (.ref m pt) := by
  cases hd <;> exact ⟨rfl, rfl⟩

private theorem checkValV2_eq_checkRefValV2_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      ∀ {v : Val}, CorrespondedValV2View v →
        checkRefValV2 v ty = checkValV2 v ty
  | _, .bool, _, hv => by
    cases hv <;> first | exact checkRefVal_eq (.bool _) .bool | rfl
  | _, .int _ _, _, hv => by
    cases hv <;> first | exact checkRefVal_eq (.scalar _) (.int _ _) | rfl
  | _, .char, _, hv => by
    cases hv <;> first | exact checkRefVal_eq (.char _) .char | rfl
  | _, .ordering, _, hv => by cases hv <;> rfl
  | _, .unit, _, hv => by cases hv <;> rfl
  | _, .never, _, hv => by cases hv <;> rfl
  | _, .enum _, _, hv => by
    cases hv <;> first | exact checkRefVal_eq (.enumVal _ _) (.enum _) | rfl
  | _, .array el _ hel, _, hv => by
    cases hv with
    | array vs hvs =>
      dsimp only [checkRefValV2, checkValV2]
      rw [refCheckValUniformV2_congr_view (fun x => checkRefValV2 x el)
        (fun x => checkValV2 x el) hvs (fun _ hx =>
          checkValV2_eq_checkRefValV2_dataView hel hx)]
    | _ => rfl

mutual
  private theorem checkValV2_eq_checkRefValV2_tyView :
      ∀ {ty : MirTy}, CorrespondedTyV2View ty →
        ∀ {v : Val}, CorrespondedValV2View v →
          checkRefValV2 v ty = checkValV2 v ty
    | _, .bool, _, hv => checkValV2_eq_checkRefValV2_dataView .bool hv
    | _, .int w s, _, hv =>
      checkValV2_eq_checkRefValV2_dataView (.int w s) hv
    | _, .char, _, hv => checkValV2_eq_checkRefValV2_dataView .char hv
    | _, .ordering, _, hv =>
      checkValV2_eq_checkRefValV2_dataView .ordering hv
    | _, .unit, _, hv => checkValV2_eq_checkRefValV2_dataView .unit hv
    | _, .never, _, hv => checkValV2_eq_checkRefValV2_dataView .never hv
    | _, .enum e, _, hv =>
      checkValV2_eq_checkRefValV2_dataView (.enum e) hv
    | _, .array el len hel, _, hv =>
      checkValV2_eq_checkRefValV2_dataView (.array el len hel) hv
    | _, .rawPtr m _ hpt, _, hv => by
      cases hv with
      | ptr _ =>
        dsimp only [checkRefValV2, checkValV2]
        rw [isUnsizedTy_eq_refIsUnsizedTyV2_pointeeView hpt]
      | slicePtr pv len =>
        cases hpt with
        | sliceInt _ _ => rfl
        | data _ hd => exact (checkValV2_slicePtr_dataView pv len m hd).1
      | _ => rfl
    | _, .ref m _ hpt, _, hv => by
      cases hv with
      | ptr _ =>
        dsimp only [checkRefValV2, checkValV2]
        rw [isUnsizedTy_eq_refIsUnsizedTyV2_pointeeView hpt]
      | slicePtr pv len =>
        cases hpt with
        | sliceInt _ _ => rfl
        | data _ hd => exact (checkValV2_slicePtr_dataView pv len m hd).2
      | _ => rfl
    | _, .rangeTo, _, hv => by cases hv <;> rfl
    | _, .rangeFrom, _, hv => by cases hv <;> rfl
    | _, .tuple _ hfs, _, hv => by
      cases hv with
      | tuple _ hvs =>
        exact checkValV2List_eq_checkRefValListV2_tyListView hfs hvs
      | _ => rfl

  private theorem checkValV2List_eq_checkRefValListV2_tyListView :
      ∀ {ts : List MirTy}, CorrespondedTyListV2View ts →
        ∀ {vs : List Val}, CorrespondedValListV2View vs →
          checkRefValListV2 vs ts = checkValV2List vs ts
    | _, .nil, _, .nil => rfl
    | _, .cons _ _ _ _, _, .nil => rfl
    | _, .nil, _, .cons _ _ _ _ => rfl
    | _, .cons _ _ ht hts, _, .cons _ _ hv hvs => by
      dsimp only [checkRefValListV2, checkValV2List]
      rw [checkValV2_eq_checkRefValV2_tyView ht hv,
        checkValV2List_eq_checkRefValListV2_tyListView hts hvs]
end

/-- On `inCorrespondedValV2` × `inCorrespondedTyV2`, `checkValV2` and
`checkRefValV2` agree identically. -/
theorem checkValV2_eq_checkRefValV2_of_corresponded
    (v : Val) (ty : MirTy)
    (h_v : inCorrespondedValV2 v = true)
    (h_t : inCorrespondedTyV2 ty = true) :
    checkRefValV2 v ty = checkValV2 v ty :=
  checkValV2_eq_checkRefValV2_tyView (inCorrespondedTyV2_view ty h_t)
    (inCorrespondedValV2_view v h_v)

/-- Pointwise `inCorrespondedValListV2` × `inCorrespondedTyListV2` agreement
between `checkValV2List` and `checkRefValListV2`. -/
theorem checkValV2List_eq_checkRefValListV2_of_corresponded
    (vs : List Val) (ts : List MirTy)
    (h_v : inCorrespondedValListV2 vs = true)
    (h_t : inCorrespondedTyListV2 ts = true) :
    checkRefValListV2 vs ts = checkValV2List vs ts :=
  checkValV2List_eq_checkRefValListV2_tyListView
    (inCorrespondedTyListV2_view ts h_t) (inCorrespondedValListV2_view vs h_v)

private theorem checkValV2List_eq_checkArgsMatchV2 :
    ∀ (vs : List Val) (tys : List MirTy),
      checkValV2List vs tys = checkArgsMatchV2 vs tys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | v :: vs, t :: ts => by
    dsimp only [checkValV2List, checkArgsMatchV2]
    rw [checkValV2List_eq_checkArgsMatchV2 vs ts]

/-- Corresponded-fragment agreement between `checkArgsMatchV2` and
`checkRefArgsMatchV2`. -/
theorem checkArgsMatchV2_eq_checkRefArgsMatchV2_of_corresponded
    (vs : List Val) (tys : List MirTy)
    (h_v : inCorrespondedValListV2 vs = true)
    (h_t : inCorrespondedTyListV2 tys = true) :
    checkRefArgsMatchV2 vs tys = checkArgsMatchV2 vs tys := by
  dsimp only [checkRefArgsMatchV2]
  rw [checkValV2List_eq_checkRefValListV2_of_corresponded vs tys h_v h_t,
    checkValV2List_eq_checkArgsMatchV2]

mutual
  private theorem checkRefValUniform_implies_inCorresponded (elem : MirTy) :
      ∀ (vs : List Val),
        refCheckValUniformV2 (fun x => checkRefValV2 x elem) vs = true →
        inCorrespondedValListV2 vs = true
    | [], _ => rfl
    | v :: vs, h => by
      dsimp only [refCheckValUniformV2] at h
      cases h0 : checkRefValV2 v elem with
      | false => rw [h0, Bool.false_and] at h; cases h
      | true =>
        rw [h0, Bool.true_and] at h
        dsimp only [inCorrespondedValListV2]
        rw [checkRefValV2_in_aux v elem h0,
          checkRefValUniform_implies_inCorresponded elem vs h]
        rfl

  private theorem checkRefValListV2_implies_inCorresponded :
      ∀ (vs : List Val) (ts : List MirTy),
        checkRefValListV2 vs ts = true →
        inCorrespondedValListV2 vs = true
    | [], _, _ => rfl
    | _ :: _, [], h => by cases h
    | v :: vs, t :: ts, h => by
      dsimp only [checkRefValListV2] at h
      cases h0 : checkRefValV2 v t with
      | false => rw [h0, Bool.false_and] at h; cases h
      | true =>
        rw [h0, Bool.true_and] at h
        dsimp only [inCorrespondedValListV2]
        rw [checkRefValV2_in_aux v t h0,
          checkRefValListV2_implies_inCorresponded vs ts h]
        rfl

  private theorem checkRefValV2_in_aux :
      ∀ (v : Val) (ty : MirTy), checkRefValV2 v ty = true →
        inCorrespondedValV2 v = true
    | v, ty, h => by
      cases v with
      | scalar _ => rfl
      | ptr _ => rfl
      | slicePtr _ _ => rfl
      | rangeTo _ => rfl
      | rangeFrom _ => rfl
      | bool _ => rfl
      | char _ => rfl
      | ordering _ => rfl
      | unit => rfl
      | enumVal _ _ => rfl
      | array vs =>
        cases ty with
        | array elem _ =>
          dsimp only [checkRefValV2] at h
          rw [Bool.and_eq_true] at h
          exact checkRefValUniform_implies_inCorresponded elem vs h.2
        | _ => cases h
      | tuple vs =>
        cases ty with
        | tuple ts => exact checkRefValListV2_implies_inCorresponded vs ts h
        | _ => cases h
      | _ => first | cases h | (cases ty <;> cases h)
end

/-- Unconditional fragment membership: any value accepted by
`checkRefValV2` belongs to `inCorrespondedValV2`. -/
theorem checkRefValV2_implies_inCorrespondedValV2
    (v : Val) (ty : MirTy) (h : checkRefValV2 v ty = true) :
    inCorrespondedValV2 v = true :=
  checkRefValV2_in_aux v ty h

/-- Unconditional soundness of `checkRefValV2` on corresponded types: any
value accepted at `ty` (`inCorrespondedTyV2 ty = true`) satisfies
`Trusted.MirSemantics.checkValV2 v ty`. -/
theorem checkRefValV2_implies_checkValV2 (v : Val) (ty : MirTy)
    (h_t : inCorrespondedTyV2 ty = true) (h_ck : checkRefValV2 v ty = true) :
    inCorrespondedValV2 v = true ∧ checkValV2 v ty = true := by
  have h_inV := checkRefValV2_implies_inCorrespondedValV2 v ty h_ck
  exact ⟨h_inV, by
    rw [← checkValV2_eq_checkRefValV2_of_corresponded v ty h_inV h_t]; exact h_ck⟩

/-- Unconditional soundness of `checkRefArgsMatchV2` on corresponded argument
type lists. -/
theorem checkRefArgsMatchV2_implies_checkArgsMatchV2 :
    ∀ (vs : List Val) (tys : List MirTy),
      inCorrespondedTyListV2 tys = true →
      checkRefArgsMatchV2 vs tys = true →
      inCorrespondedValListV2 vs = true ∧ checkArgsMatchV2 vs tys = true
  | [], [], _, _ => ⟨rfl, rfl⟩
  | _ :: _, [], _, h => by cases h
  | [], _ :: _, _, h => by cases h
  | v :: vs, t :: ts, h_t, h => by
    dsimp only [inCorrespondedTyListV2] at h_t
    dsimp only [checkRefArgsMatchV2, checkRefValListV2] at h
    cases ht0 : inCorrespondedTyV2 t with
    | false => rw [ht0, Bool.false_and] at h_t; cases h_t
    | true =>
      rw [ht0, Bool.true_and] at h_t
      cases hv0 : checkRefValV2 v t with
      | false => rw [hv0, Bool.false_and] at h; cases h
      | true =>
        rw [hv0, Bool.true_and] at h
        have h_v := checkRefValV2_implies_checkValV2 v t ht0 hv0
        have h_r :=
          checkRefArgsMatchV2_implies_checkArgsMatchV2 vs ts h_t h
        exact ⟨by dsimp only [inCorrespondedValListV2]; rw [h_v.1, h_r.1]; rfl,
          by dsimp only [checkArgsMatchV2]; rw [h_v.2, h_r.2]; rfl⟩

/-- Exact agreement between `spanDisjoint` and `refSpanDisjointV2`. -/
theorem spanDisjoint_eq_refSpanDisjointV2
    (a b : Bool × Trusted.MirAst.AllocId × Nat × Nat) :
    refSpanDisjointV2 a b = spanDisjoint a b := rfl

/-- Exact agreement between `spansPairwiseDisjoint` and
`refSpansPairwiseDisjointV2`. -/
theorem spansPairwiseDisjoint_eq_refSpansPairwiseDisjointV2 :
    ∀ (xs : List (Bool × Trusted.MirAst.AllocId × Nat × Nat)),
      refSpansPairwiseDisjointV2 xs = spansPairwiseDisjoint xs
  | [] => rfl
  | a :: rest => by
    have h_w :
        ∀ ys, refSpanDisjointWithV2 a ys = spanDisjointWith a ys := by
      intro ys
      induction ys with
      | nil => rfl
      | cons y yr ih =>
        dsimp only [refSpanDisjointWithV2, spanDisjointWith]
        rw [spanDisjoint_eq_refSpanDisjointV2, ih]
    dsimp only [refSpansPairwiseDisjointV2, spansPairwiseDisjoint]
    rw [h_w rest, spansPairwiseDisjoint_eq_refSpansPairwiseDisjointV2 rest]

private theorem refAllocIdsArray_congr_view (elem : MirTy)
    (h_elem : ∀ {v : Val}, CorrespondedValV2View v →
      refRefAllocIdsV2 elem v = refAllocIds elem v) :
    ∀ {vs : List Val}, CorrespondedValListV2View vs →
      refRefAllocIdsArrayV2 elem vs = refAllocIdsArray elem vs
  | _, .nil => rfl
  | _, .cons v _ hv hvs => by
    dsimp only [refRefAllocIdsArrayV2, refAllocIdsArray]
    rw [h_elem hv, refAllocIdsArray_congr_view elem h_elem hvs]

private theorem refAllocIds_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      ∀ {v : Val}, CorrespondedValV2View v →
        refRefAllocIdsV2 ty v = refAllocIds ty v
  | _, .bool, _, hv | _, .int _ _, _, hv | _, .char, _, hv
  | _, .ordering, _, hv | _, .unit, _, hv | _, .never, _, hv
  | _, .enum _, _, hv => by cases hv <;> rfl
  | _, .array elem _ hel, _, hv => by
    cases hv with
    | array _ hvs =>
      dsimp only [refRefAllocIdsV2, refAllocIds]
      exact refAllocIdsArray_congr_view elem
        (fun hx => refAllocIds_dataView hel hx) hvs
    | _ => rfl

private theorem refAllocIds_ref_dataView (m : Trusted.MirAst.Mutability)
    {pt : MirTy} (hd : CorrespondedDataTyV2View pt)
    {v : Val} (hv : CorrespondedValV2View v) :
    refRefAllocIdsV2 (.ref m pt) v = refAllocIds (.ref m pt) v := by
  cases hd <;> cases hv <;> rfl

mutual
  private theorem refAllocIds_tyView :
      ∀ {ty : MirTy}, CorrespondedTyV2View ty →
        ∀ {v : Val}, CorrespondedValV2View v →
          refRefAllocIdsV2 ty v = refAllocIds ty v
    | _, .bool, _, hv => refAllocIds_dataView .bool hv
    | _, .int w s, _, hv => refAllocIds_dataView (.int w s) hv
    | _, .char, _, hv => refAllocIds_dataView .char hv
    | _, .ordering, _, hv => refAllocIds_dataView .ordering hv
    | _, .unit, _, hv => refAllocIds_dataView .unit hv
    | _, .never, _, hv => refAllocIds_dataView .never hv
    | _, .enum e, _, hv => refAllocIds_dataView (.enum e) hv
    | _, .array el len hel, _, hv =>
      refAllocIds_dataView (.array el len hel) hv
    | _, .rawPtr _ _ _, _, hv => by cases hv <;> rfl
    | _, .ref m _ hpt, _, hv => by
      cases hpt with
      | sliceInt _ _ => cases hv <;> rfl
      | data _ hd => exact refAllocIds_ref_dataView m hd hv
    | _, .rangeTo, _, hv => by cases hv <;> rfl
    | _, .rangeFrom, _, hv => by cases hv <;> rfl
    | _, .tuple _ hfs, _, hv => by
      cases hv with
      | tuple _ hvs => exact refAllocIdsList_tyListView hfs hvs
      | _ => rfl

  private theorem refAllocIdsList_tyListView :
      ∀ {ts : List MirTy}, CorrespondedTyListV2View ts →
        ∀ {vs : List Val}, CorrespondedValListV2View vs →
          refRefAllocIdsListV2 ts vs = refAllocIdsList ts vs
    | _, .nil, _, .nil => rfl
    | _, .nil, _, .cons _ _ _ _ => rfl
    | _, .cons _ _ _ _, _, .nil => rfl
    | _, .cons _ _ ht hts, _, .cons _ _ hv hvs => by
      dsimp only [refRefAllocIdsListV2, refAllocIdsList]
      rw [refAllocIds_tyView ht hv, refAllocIdsList_tyListView hts hvs]
end

/-- On `inCorrespondedTyV2` × `inCorrespondedValV2`, `refAllocIds` and
`refRefAllocIdsV2` agree identically. -/
theorem refAllocIds_eq_refRefAllocIdsV2_of_corresponded
    (ty : MirTy) (v : Val)
    (h_t : inCorrespondedTyV2 ty = true)
    (h_v : inCorrespondedValV2 v = true) :
    refRefAllocIdsV2 ty v = refAllocIds ty v :=
  refAllocIds_tyView (inCorrespondedTyV2_view ty h_t)
    (inCorrespondedValV2_view v h_v)

/-- Pointwise `inCorrespondedTyListV2` × `inCorrespondedValListV2` agreement
between `refAllocIdsList` and `refRefAllocIdsListV2`. -/
theorem refAllocIdsList_eq_refRefAllocIdsListV2_of_corresponded
    (ts : List MirTy) (vs : List Val)
    (h_t : inCorrespondedTyListV2 ts = true)
    (h_v : inCorrespondedValListV2 vs = true) :
    refRefAllocIdsListV2 ts vs = refAllocIdsList ts vs :=
  refAllocIdsList_tyListView (inCorrespondedTyListV2_view ts h_t)
    (inCorrespondedValListV2_view vs h_v)

/-- Element-wise `inCorrespondedTyV2` × `inCorrespondedValListV2` agreement
between `refAllocIdsArray` and `refRefAllocIdsArrayV2`. -/
theorem refAllocIdsArray_eq_refRefAllocIdsArrayV2_of_corresponded
    (elem : MirTy) (vs : List Val)
    (h_t : inCorrespondedTyV2 elem = true)
    (h_v : inCorrespondedValListV2 vs = true) :
    refRefAllocIdsArrayV2 elem vs = refAllocIdsArray elem vs :=
  refAllocIdsArray_congr_view elem
    (fun hv => refAllocIds_tyView (inCorrespondedTyV2_view elem h_t) hv)
    (inCorrespondedValListV2_view vs h_v)

/-- Corresponded-fragment agreement between `refsStayInCallerMem` and
`refRefsStayInCallerMemV2`. -/
theorem refsStayInCallerMem_eq_refRefsStayInCallerMemV2_of_corresponded
    (cm : CallerMemory) (ty : MirTy) (v : Val)
    (h_t : inCorrespondedTyV2 ty = true)
    (h_v : inCorrespondedValV2 v = true) :
    refRefsStayInCallerMemV2 cm ty v = refsStayInCallerMem cm ty v := by
  dsimp only [refRefsStayInCallerMemV2, refsStayInCallerMem]
  rw [refAllocIds_eq_refRefAllocIdsV2_of_corresponded ty v h_t h_v]
  induction refAllocIds ty v with
  | nil => rfl
  | cons aid rest ih =>
    dsimp only [List.all]
    rw [refHasAllocIdV2_eq_findAllocation_isSome aid cm.allocations, ih]

private theorem layoutOfArrayV2_eq_layoutOfTyV2_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      layoutOfArrayV2 ty = layoutOfTyV2 ty
  | _, .enum _ => by
    unfold layoutOfTyV2
    dsimp only [layoutOfArrayV2, layoutOfTy]
  | _, .array _ _ _ => by
    unfold layoutOfTyV2
    rfl
  | _, .bool | _, .int _ _ | _, .char | _, .ordering
  | _, .unit | _, .never => rfl

private theorem layoutOfTyV2_isSome_dataView :
    ∀ {pt : MirTy}, CorrespondedDataTyV2View pt →
      isSupportedV2DataTy pt = true → ∃ lay, layoutOfTyV2 pt = some lay
  | _, .bool, _ => ⟨⟨1, 0⟩, rfl⟩
  | _, .int w _, _ => ⟨intLayout w, rfl⟩
  | _, .char, _ => ⟨⟨4, 2⟩, rfl⟩
  | _, .ordering, _ => ⟨⟨1, 0⟩, rfl⟩
  | _, .unit, _ => ⟨⟨0, 0⟩, rfl⟩
  | _, .never, _ => ⟨⟨0, 0⟩, rfl⟩
  | _, .enum ety, h => by
    have h_adm : enumAdmitted ety = true := h
    unfold layoutOfTyV2
    dsimp only [layoutOfTy]
    rw [h_adm]
    cases ety.tagRepr with
    | zeroSized => exact ⟨⟨0, 0⟩, rfl⟩
    | scalar tagW _ => exact ⟨intLayout tagW, rfl⟩
  | _, .array elem len hel, h => by
    dsimp only [isSupportedV2DataTy] at h
    let ⟨elemLay, h_el⟩ := layoutOfTyV2_isSome_dataView hel h
    rw [← layoutOfArrayV2_eq_layoutOfTyV2_dataView hel] at h_el
    unfold layoutOfTyV2
    dsimp only [layoutOfTy]
    rw [h_el]
    exact ⟨⟨len * elemLay.size, elemLay.alignLog2⟩, rfl⟩

/-- Every corresponded Profile v2 fixed-size data type
(`inCorrespondedDataTyV2 pt = true` and `isSupportedV2DataTy pt = true`) has a
layout in `layoutOfTyV2`. -/
theorem layoutOfTyV2_isSome_of_correspondedDataTy
    {pt : MirTy}
    (h_c : inCorrespondedDataTyV2 pt = true)
    (h : isSupportedV2DataTy pt = true) :
    ∃ lay, layoutOfTyV2 pt = some lay :=
  layoutOfTyV2_isSome_dataView (inCorrespondedDataTyV2_view pt h_c) h

/-- Every corresponded Profile v2 sized pointee type admitted by
`isSupportedV2DataTy pt` has a layout in `layoutOfTyV2`. -/
theorem layoutOfTyV2_isSome_of_correspondedPointee {pt : MirTy}
    (h_c : inCorrespondedDataTyV2 pt = true)
    (h : isSupportedV2DataTy pt = true) :
    ∃ lay, layoutOfTyV2 pt = some lay :=
  layoutOfTyV2_isSome_of_correspondedDataTy h_c h

mutual
  /-- Whether every fixed-size array (directly or under `.ref`) in `ty` has
  byte size `< 2^64`, matching 64-bit `Miri.ABI.Size`. -/
  noncomputable def tyLayoutsFitU64V2 : MirTy → Bool
    | .array elem len =>
      match layoutOfTyV2 (.array elem len) with
      | some lay => Nat.blt lay.size (Nat.pow 2 64)
      | none => true
    | .ref _ pt | .rawPtr _ pt => tyLayoutsFitU64V2 pt
    | .tuple fs => tyListLayoutsFitU64V2 fs
    | _ => true

  /-- Pointwise `tyLayoutsFitU64V2` check across tuple field types. -/
  noncomputable def tyListLayoutsFitU64V2 : List MirTy → Bool
    | [] => true
    | t :: ts => tyLayoutsFitU64V2 t && tyListLayoutsFitU64V2 ts
end

private theorem refAccessSpansArray_nil_congr_view (elem : MirTy)
    (h_elem : ∀ {v : Val}, CorrespondedValV2View v →
      refAccessSpans elem v = []) :
    ∀ {vs : List Val}, CorrespondedValListV2View vs →
      refAccessSpansArray elem vs = []
  | _, .nil => rfl
  | _, .cons _ _ hv hvs => by
    dsimp only [refAccessSpansArray]
    rw [h_elem hv, refAccessSpansArray_nil_congr_view elem h_elem hvs]
    rfl

private theorem refAccessSpans_nil_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      ∀ {v : Val}, CorrespondedValV2View v →
        refAccessSpans ty v = []
  | _, .bool, _, hv | _, .int _ _, _, hv | _, .char, _, hv
  | _, .ordering, _, hv | _, .unit, _, hv | _, .never, _, hv
  | _, .enum _, _, hv => by cases hv <;> rfl
  | _, .array elem _ hel, _, hv => by
    cases hv with
    | array _ hvs =>
      dsimp only [refAccessSpans]
      exact refAccessSpansArray_nil_congr_view elem
        (fun hx => refAccessSpans_nil_dataView hel hx) hvs
    | _ => rfl

private theorem refAccessSpansArrayV2_nil_congr_view (elem : MirTy)
    (h_elem : ∀ {v : Val}, CorrespondedValV2View v →
      refAccessSpansV2 elem v = []) :
    ∀ {vs : List Val}, CorrespondedValListV2View vs →
      refAccessSpansArrayV2 elem vs = []
  | _, .nil => rfl
  | _, .cons _ _ hv hvs => by
    dsimp only [refAccessSpansArrayV2]
    rw [h_elem hv, refAccessSpansArrayV2_nil_congr_view elem h_elem hvs]
    rfl

private theorem refAccessSpansV2_nil_dataView :
    ∀ {ty : MirTy}, CorrespondedDataTyV2View ty →
      ∀ {v : Val}, CorrespondedValV2View v →
        refAccessSpansV2 ty v = []
  | _, .bool, _, hv | _, .int _ _, _, hv | _, .char, _, hv
  | _, .ordering, _, hv | _, .unit, _, hv | _, .never, _, hv
  | _, .enum _, _, hv => by cases hv <;> rfl
  | _, .array elem _ hel, _, hv => by
    cases hv with
    | array _ hvs =>
      dsimp only [refAccessSpansV2]
      exact refAccessSpansArrayV2_nil_congr_view elem
        (fun hx => refAccessSpansV2_nil_dataView hel hx) hvs
    | _ => rfl

private theorem layoutOfTyV2_lt_u64_of_dataView :
    ∀ {pt : MirTy}, CorrespondedDataTyV2View pt →
      ∀ (lay : Trusted.MirSemantics.LayoutData),
        isSupportedV2DataTy pt = true →
        tyLayoutsFitU64V2 pt = true →
        layoutOfTyV2 pt = some lay →
        Nat.blt lay.size (Nat.pow 2 64) = true
  | _, .bool, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; rfl
  | _, .int w _, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; cases w <;> rfl
  | _, .char, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; rfl
  | _, .ordering, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; rfl
  | _, .unit, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; rfl
  | _, .never, lay, _, _, h_lay => by
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    injection h_lay with h_eq; subst h_eq; rfl
  | _, .enum ety, lay, h_d, _, h_lay => by
    have h_adm : enumAdmitted ety = true := h_d
    unfold layoutOfTyV2 at h_lay; dsimp only [layoutOfTy] at h_lay
    rw [h_adm] at h_lay
    cases h_tr : ety.tagRepr with
    | zeroSized =>
      rw [h_tr] at h_lay; injection h_lay with h_eq; subst h_eq; rfl
    | scalar tagW _ =>
      rw [h_tr] at h_lay; injection h_lay with h_eq; subst h_eq
      cases tagW <;> rfl
  | _, .array _ _ _, _, _, h_fit, h_lay => by
    dsimp only [tyLayoutsFitU64V2] at h_fit
    rw [h_lay] at h_fit
    exact h_fit

private theorem refAccessSpans_ref_dataView
    (reqMut : Trusted.MirAst.Mutability) {pt : MirTy}
    (hd : CorrespondedDataTyV2View pt)
    (h_d : isSupportedV2DataTy pt = true)
    (h_f : tyLayoutsFitU64V2 pt = true)
    {v : Val} (hv : CorrespondedValV2View v) :
    refAccessSpansV2 (.ref reqMut pt) v = refAccessSpans (.ref reqMut pt) v := by
  cases hv with
  | ptr pv =>
    let ⟨lay, h_lay⟩ := layoutOfTyV2_isSome_dataView hd h_d
    have h_pt_fit := layoutOfTyV2_lt_u64_of_dataView hd lay h_d h_f h_lay
    have h_la : layoutOfArrayV2 pt = some lay := by
      rw [layoutOfArrayV2_eq_layoutOfTyV2_dataView hd]; exact h_lay
    have h_mod := layoutOfArrayV2_mod_dataView hd lay h_la
    have h_sz : (refLayoutDataForTyV2 pt).size.bytes.toNat = lay.size :=
      h_mod.1.trans (Nat.mod_eq_of_lt (Nat.blt_eq.mp h_pt_fit))
    cases hd <;> (
      dsimp only [refAccessSpansV2, refAccessSpans]
      rw [h_lay]
      cases pv.allocId with
      | none => rfl
      | some _ => dsimp only; rw [h_sz]; rfl)
  | _ => cases hd <;> rfl

private theorem isSupportedV2DataTy_of_ref_dataView
    (reqMut : Trusted.MirAst.Mutability) {pt : MirTy}
    (hd : CorrespondedDataTyV2View pt)
    (h : isSupportedV2LocalTy (.ref reqMut pt) = true) :
    isSupportedV2DataTy pt = true := by
  cases hd with
  | enum _ =>
    dsimp only [isSupportedV2LocalTy, isSupportedV2PointeeTy,
      isSizedNoRefV2Ty, isSupportedV2DataTy, isOverflowPairTy,
      isSupportedScalarOrUnitTy] at h
    dsimp only [isSupportedV2DataTy, isOverflowPairTy,
      isSupportedScalarOrUnitTy]
    rw [Bool.not_false, Bool.true_and, Bool.or_self] at h
    rw [Bool.not_false, Bool.true_and]
    exact h
  | _ => exact h

mutual
  private theorem refAccessSpans_tyView :
      ∀ {ty : MirTy}, CorrespondedTyV2View ty →
        ∀ {v : Val}, CorrespondedValV2View v →
          isSupportedV2LocalTy ty = true →
          tyLayoutsFitU64V2 ty = true →
          refAccessSpansV2 ty v = refAccessSpans ty v
    | _, .bool, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView .bool hv).trans
        (refAccessSpans_nil_dataView .bool hv).symm
    | _, .int w s, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView (.int w s) hv).trans
        (refAccessSpans_nil_dataView (.int w s) hv).symm
    | _, .char, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView .char hv).trans
        (refAccessSpans_nil_dataView .char hv).symm
    | _, .ordering, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView .ordering hv).trans
        (refAccessSpans_nil_dataView .ordering hv).symm
    | _, .unit, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView .unit hv).trans
        (refAccessSpans_nil_dataView .unit hv).symm
    | _, .never, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView .never hv).trans
        (refAccessSpans_nil_dataView .never hv).symm
    | _, .enum e, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView (.enum e) hv).trans
        (refAccessSpans_nil_dataView (.enum e) hv).symm
    | _, .array elem len hel, _, hv, _, _ =>
      (refAccessSpansV2_nil_dataView (.array elem len hel) hv).trans
        (refAccessSpans_nil_dataView (.array elem len hel) hv).symm
    | _, .rawPtr _ _ _, _, hv, _, _ => by cases hv <;> rfl
    | _, .ref reqMut _ hpt, _, hv, h_ty, h_fit => by
      cases hpt with
      | sliceInt w s =>
        cases hv with
        | slicePtr pv _ =>
          have h_lay : layoutOfTyV2 (.int w s) = some (intLayout w) := by
            unfold layoutOfTyV2
            rfl
          dsimp only [refAccessSpansV2, refAccessSpans]
          rw [h_lay]
          cases pv.allocId with
          | none => rfl
          | some _ =>
            have h_sz : (toMiriSize w).bytes.toNat = (intLayout w).size := by
              cases w <;> rfl
            dsimp only [refLayoutDataForTyV2, refScalarLayoutDataV2,
              refBaseLayoutDataV2]
            rw [h_sz]
        | _ => rfl
      | data _ hd =>
        exact refAccessSpans_ref_dataView reqMut hd
          (isSupportedV2DataTy_of_ref_dataView reqMut hd h_ty) h_fit hv
    | _, .rangeTo, _, hv, _, _ => by cases hv <;> rfl
    | _, .rangeFrom, _, hv, _, _ => by cases hv <;> rfl
    | _, .tuple _ hts, _, hv, h_ty, h_fit => by
      cases hv with
      | tuple _ hvs =>
        exact refAccessSpansList_tyListView hts hvs h_ty h_fit
      | _ => rfl

  private theorem refAccessSpansList_tyListView :
      ∀ {tys : List MirTy}, CorrespondedTyListV2View tys →
        ∀ {vs : List Val}, CorrespondedValListV2View vs →
          isSupportedV2LocalTyList tys = true →
          tyListLayoutsFitU64V2 tys = true →
          refAccessSpansListV2 tys vs = refAccessSpansList tys vs
    | _, .nil, _, .nil, _, _ => rfl
    | _, .nil, _, .cons _ _ _ _, _, _ => rfl
    | _, .cons _ _ _ _, _, .nil, _, _ => rfl
    | _, .cons _ _ ht hts, _, .cons _ _ hv hvs, h_all, h_fit => by
      dsimp only [isSupportedV2LocalTyList] at h_all
      dsimp only [tyListLayoutsFitU64V2] at h_fit
      cases htl : isSupportedV2LocalTy _ with
      | false => rw [htl] at h_all; cases h_all
      | true =>
        cases hf : tyLayoutsFitU64V2 _ with
        | false => rw [hf] at h_fit; cases h_fit
        | true =>
          rw [htl, Bool.true_and] at h_all
          rw [hf, Bool.true_and] at h_fit
          dsimp only [refAccessSpansListV2, refAccessSpansList]
          rw [refAccessSpans_tyView ht hv htl hf,
            refAccessSpansList_tyListView hts hvs h_all h_fit]
end

/-- Corresponded-fragment agreement between `refAccessSpans` and
`refAccessSpansV2` on every `inCorrespondedTyV2` × `inCorrespondedValV2`
local type (`isSupportedV2LocalTy ty = true`) whose array sizes fit in 64 bits
(`tyLayoutsFitU64V2 ty = true`). -/
theorem refAccessSpans_eq_refAccessSpansV2_of_corresponded
    (ty : MirTy) (v : Val)
    (h_c : inCorrespondedTyV2 ty = true)
    (h_v : inCorrespondedValV2 v = true)
    (h_ty : isSupportedV2LocalTy ty = true)
    (h_fit : tyLayoutsFitU64V2 ty = true) :
    refAccessSpansV2 ty v = refAccessSpans ty v :=
  refAccessSpans_tyView (inCorrespondedTyV2_view ty h_c)
    (inCorrespondedValV2_view v h_v) h_ty h_fit

/-- Corresponded-fragment agreement between `refAccessSpansList` and
`refAccessSpansListV2` on lists of Profile v2 local types. -/
theorem refAccessSpansList_eq_refAccessSpansListV2_of_corresponded
    (tys : List MirTy) (vs : List Val)
    (h_c : inCorrespondedTyListV2 tys = true)
    (h_v : inCorrespondedValListV2 vs = true)
    (h_all : isSupportedV2LocalTyList tys = true)
    (h_fit : tyListLayoutsFitU64V2 tys = true) :
    refAccessSpansListV2 tys vs = refAccessSpansList tys vs :=
  refAccessSpansList_tyListView (inCorrespondedTyListV2_view tys h_c)
    (inCorrespondedValListV2_view vs h_v) h_all h_fit

/-! ### Little-Endian Byte Codec & `Miri.Memory` Round-Trips (Profile v2) -/

private theorem provMatch_uniform (p : Option Trusted.MirAst.AllocId) :
    ∀ (raw : List UInt8),
      provMatch p (raw.map (fun b => AllocByte.init b p)) = some p
  | [] => rfl
  | _ :: rest => by
    dsimp only [List.map, provMatch]
    cases p with
    | none => exact provMatch_uniform none rest
    | some aid =>
      dsimp only
      rw [Nat.beq_refl]
      exact provMatch_uniform (some aid) rest

/-- `readPtrProv?` recovers uniform provenance `p` from any non-empty byte list
tagged uniformly with `p`. -/
theorem readPtrProv?_map_uniform (p : Option Trusted.MirAst.AllocId)
    (b : UInt8) (rest : List UInt8) :
    readPtrProv? ((b :: rest).map (fun x => AllocByte.init x p)) = some p :=
  provMatch_uniform p rest

/-- `initBytes?` ignores uniform provenance and recovers raw bytes. -/
theorem initBytes?_map_init_prov (p : Option Trusted.MirAst.AllocId) :
    ∀ (raw : List UInt8),
      initBytes? (raw.map (fun b => AllocByte.init b p)) = some raw
  | [] => rfl
  | b :: rest => by
    dsimp only [List.map, initBytes?]
    rw [initBytes?_map_init_prov p rest]

/-- Profile v2 little-endian integer encode/decode round-trip across every
`IntWidth`, signedness, and bit pattern. -/
theorem encodeValV2_decodeValV2_int_little (w : IntWidth) (s : Bool)
    (bits : BitVec 128) :
    let v : Val := .scalar ⟨w, s, truncateBits w bits⟩
    let enc := (leBytesOfNat w.byteSize (truncateBits w bits).toNat).map
      (fun b => AllocByte.init b none)
    encodeValV2 profileV2TargetEndian (.int w s) v = .ok enc ∧
    decodeValV2 profileV2TargetEndian (.int w s) enc = .ok (some v) := by
  intro v enc
  have h_wf : (ScalarVal.mk w s (truncateBits w bits)).wf = true := by
    dsimp only [ScalarVal.wf]
    rw [truncateBits_idem]
    exact beq_self_eq_true _
  have h_ck : checkVal v (.int w s) = true := by
    dsimp only [v, checkVal, Val.ty?]
    rw [h_wf, mem_ite_true_eq]
    dsimp only [MirTy.beq]
    rw [IntWidth.beq_refl, beq_self_eq_true]
    rfl
  have h_ck2 : checkValV2 v (.int w s) = true := by
    dsimp only [v, checkValV2]
    exact h_ck
  have h_enc : encodeValV2 profileV2TargetEndian (.int w s) v = .ok enc := by
    dsimp only [encodeValV2, encodeVal]
    rw [h_ck2, h_ck]
    rfl
  refine ⟨h_enc, ?_⟩
  have h_len : enc.length = w.byteSize := by
    dsimp only [enc]
    rw [List.length_map, leBytesOfNat_length]
  have h_sz : (intLayout w).size = w.byteSize := by cases w <;> rfl
  have h_nz : Nat.beq w.byteSize 0 = false := by cases w <;> rfl
  have h_pow : Nat.pow 2 w.bitWidth = HPow.hPow 256 w.byteSize := by
    cases w <;> rfl
  have h_lt : (truncateBits w bits).toNat < HPow.hPow 256 w.byteSize := by
    rw [toNat_truncateBits, ← h_pow]
    exact Nat.mod_lt _ (intWidth_modulus_pos w)
  have h_dec :
      decodeUInt profileV2TargetEndian
          (leBytesOfNat w.byteSize (truncateBits w bits).toNat) =
        (truncateBits w bits).toNat := by
    change natOfLeBytes (leBytesOfNat w.byteSize (truncateBits w bits).toNat) = _
    rw [natOfLeBytes_leBytesOfNat]
    exact Nat.mod_eq_of_lt h_lt
  dsimp only [decodeValV2, decodeVal]
  have h_lay : layoutOfTy (.int w s) = some (intLayout w) := rfl
  rw [h_lay]
  dsimp only
  rw [h_len, h_sz, Nat.beq_refl, h_nz]
  dsimp only [enc]
  rw [initBytes?_map_init]
  dsimp only
  rw [h_dec, bitVec128_ofNat_toNat]
  dsimp only [evalConstLit]
  rw [truncateBits_idem, bne_self_eq_false]
  rfl

private theorem decodeValV2_rawPtr_ne_str
    (endian : TargetEndian) (m : Trusted.MirAst.Mutability)
    {pt : MirTy} (h_sized : isUnsizedTy pt = false) (bytes : List AllocByte) :
    decodeValV2 endian (.rawPtr m pt) bytes = decodePtrLikeV2 endian pt bytes := by
  cases pt with
  | str => cases h_sized
  | _ => rfl

/-- Profile v2 little-endian thin-pointer encode/decode round-trip (preserving
both 64-bit offset and `allocId` provenance). -/
theorem encodeValV2_decodeValV2_thinPtr_little (m : Trusted.MirAst.Mutability)
    (pt : MirTy) (pv : PtrVal)
    (h_sized : isUnsizedTy pt = false) (h_w : pv.width = .isize) :
    let enc := (leBytesOfNat 8 pv.offsetBytes.toNat).map
      (fun b => AllocByte.init b pv.allocId)
    encodeValV2 profileV2TargetEndian (.rawPtr m pt) (.ptr pv) = .ok enc ∧
    decodeValV2 profileV2TargetEndian (.rawPtr m pt) enc = .ok (some (.ptr pv))
    := by
  intro enc
  have h_off_lt : pv.offsetBytes.toNat < HPow.hPow 256 8 :=
    u64_toNat_lt_pow64 pv.offsetBytes
  have h_nat : natOfLeBytes (leBytesOfNat 8 pv.offsetBytes.toNat) =
      pv.offsetBytes.toNat := by
    rw [natOfLeBytes_leBytesOfNat, Nat.mod_eq_of_lt h_off_lt]
  have h_u64 : UInt64.ofNat pv.offsetBytes.toNat = pv.offsetBytes :=
    u64_eq_of_toNat_eq (u64_ofNat_toNat_of_lt (u64_toNat_lt_pow64 pv.offsetBytes))
  have h_pv_eq :
      PtrVal.mk pv.allocId (UInt64.ofNat pv.offsetBytes.toNat) .isize = pv := by
    cases pv with
    | mk aid off w =>
      dsimp only at h_w h_u64
      subst h_w
      rw [h_u64]
  have h_ck : checkValV2 (.ptr pv) (.rawPtr m pt) = true := by
    dsimp only [checkValV2]
    rw [h_sized, h_w]
    rfl
  refine ⟨?_, ?_⟩
  · dsimp only [encodeValV2]
    rw [h_ck, h_sized]
    rfl
  · rw [decodeValV2_rawPtr_ne_str profileV2TargetEndian m h_sized]
    dsimp only [decodePtrLikeV2]
    rw [h_sized]
    have h_len : enc.length = 8 := by
      dsimp only [enc]
      rw [List.length_map, leBytesOfNat_length]
    rw [h_len]
    dsimp only [enc]
    rw [initBytes?_map_init_prov]
    have h_prov :
        readPtrProv? ((leBytesOfNat 8 pv.offsetBytes.toNat).map
          (fun b => AllocByte.init b pv.allocId)) = some pv.allocId :=
      readPtrProv?_map_uniform pv.allocId _ _
    rw [h_prov]
    dsimp only [decodeUInt, profileV2TargetEndian]
    rw [h_nat, h_pv_eq]
    rfl

/-- Profile v2 little-endian wide slice fat-pointer `(ptr, len)` encode/decode
round-trip (preserving provenance on the 8 pointer bytes and plain LE bytes on
the 8 length bytes). -/
theorem encodeValV2_decodeValV2_wideSlicePtr_little
    (m : Trusted.MirAst.Mutability) (elem : MirTy) (pv : PtrVal) (len : UInt64)
    (h_w : pv.width = .isize) :
    let pBytes := (leBytesOfNat 8 pv.offsetBytes.toNat).map
      (fun b => AllocByte.init b pv.allocId)
    let lBytes := (leBytesOfNat 8 len.toNat).map
      (fun b => AllocByte.init b none)
    encodeValV2 profileV2TargetEndian (.rawPtr m (.slice elem))
        (.slicePtr pv len) = .ok (pBytes ++ lBytes) ∧
    decodeValV2 profileV2TargetEndian (.rawPtr m (.slice elem))
        (pBytes ++ lBytes) = .ok (some (.slicePtr pv len)) := by
  intro pBytes lBytes
  have h_pLen : pBytes.length = 8 := by
    dsimp only [pBytes]; rw [List.length_map, leBytesOfNat_length]
  have h_lLen : lBytes.length = 8 := by
    dsimp only [lBytes]; rw [List.length_map, leBytesOfNat_length]
  have h_totLen : (pBytes ++ lBytes).length = 16 := by
    rw [List.length_append, h_pLen, h_lLen]
  have h_take : (pBytes ++ lBytes).take 8 = pBytes := by
    rw [← h_pLen, List.take_left]
  have h_drop : (pBytes ++ lBytes).drop 8 = lBytes := by
    rw [← h_pLen, List.drop_left]
  have h_pNat : natOfLeBytes (leBytesOfNat 8 pv.offsetBytes.toNat) =
      pv.offsetBytes.toNat := by
    rw [natOfLeBytes_leBytesOfNat,
      Nat.mod_eq_of_lt (u64_toNat_lt_pow64 pv.offsetBytes)]
  have h_lNat : natOfLeBytes (leBytesOfNat 8 len.toNat) = len.toNat := by
    rw [natOfLeBytes_leBytesOfNat, Nat.mod_eq_of_lt (u64_toNat_lt_pow64 len)]
  have h_u64_p : UInt64.ofNat pv.offsetBytes.toNat = pv.offsetBytes :=
    u64_eq_of_toNat_eq (u64_ofNat_toNat_of_lt (u64_toNat_lt_pow64 pv.offsetBytes))
  have h_u64_l : UInt64.ofNat len.toNat = len :=
    u64_eq_of_toNat_eq (u64_ofNat_toNat_of_lt (u64_toNat_lt_pow64 len))
  have h_pv_eq :
      PtrVal.mk pv.allocId (UInt64.ofNat pv.offsetBytes.toNat) .isize = pv := by
    cases pv with
    | mk aid off w =>
      dsimp only at h_w h_u64_p
      subst h_w
      rw [h_u64_p]
  have h_ck : checkValV2 (.slicePtr pv len) (.rawPtr m (.slice elem)) = true := by
    dsimp only [checkValV2]
    rw [h_w]
    rfl
  refine ⟨?_, ?_⟩
  · dsimp only [encodeValV2]
    rw [h_ck]
    rfl
  · dsimp only [decodeValV2, decodePtrLikeV2]
    change (if !Nat.beq (pBytes ++ lBytes).length 16 then
        Except.error FaultKind.unsupported
      else
        let pB := (pBytes ++ lBytes).take 8
        let lB := (pBytes ++ lBytes).drop 8
        match initBytes? pB, readPtrProv? pB, initBytes? lB with
        | some pRaw, some prov, some lRaw =>
          Except.ok (some (Val.slicePtr
            ⟨prov, UInt64.ofNat (natOfLeBytes pRaw), .isize⟩
            (UInt64.ofNat (natOfLeBytes lRaw))))
        | _, _, _ => Except.ok none) = _
    rw [h_totLen, h_take, h_drop]
    dsimp only [pBytes, lBytes]
    rw [initBytes?_map_init_prov, initBytes?_map_init]
    have h_prov :
        readPtrProv? ((leBytesOfNat 8 pv.offsetBytes.toNat).map
          (fun b => AllocByte.init b pv.allocId)) = some pv.allocId :=
      readPtrProv?_map_uniform pv.allocId _ _
    rw [h_prov]
    dsimp only
    rw [h_pNat, h_lNat, h_pv_eq, h_u64_l]
    rfl

private theorem list_range'_succ_end_v2 (s k : Nat) :
    List.range' s (k + 1) 1 = List.range' s k 1 ++ [s + k] := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    change s :: List.range' (s + 1) (k + 1) 1 =
      s :: (List.range' (s + 1) k 1 ++ [s + (k + 1)])
    rw [ih (s + 1), Nat.add_assoc, Nat.add_comm 1 k]

private theorem forIn_append_ok_v2 {ε α β : Type}
    (xs ys : List α) (init mid final : β)
    (f : α → β → Except ε (ForInStep β))
    (h1 : forIn (m := Except ε) xs init f = .ok mid)
    (h2 : forIn (m := Except ε) ys mid f = .ok final)
    (h_yield : ∀ a b, ∃ b', f a b = .ok (.yield b')) :
    forIn (m := Except ε) (xs ++ ys) init f = .ok final := by
  induction xs generalizing init with
  | nil =>
    rw [List.nil_append]
    rw [List.forIn_nil] at h1
    injection h1 with h_eq
    subst h_eq
    exact h2
  | cons a rest ih =>
    let ⟨b', h_step⟩ := h_yield a init
    rw [List.cons_append, List.forIn_cons]
    rw [List.forIn_cons] at h1
    dsimp only [bind, Bind.bind, Except.bind] at h1
    dsimp only [bind, Bind.bind, Except.bind]
    rw [h_step] at h1
    rw [h_step]
    exact ih b' h1

/-- Exact little-endian byte agreement between `Miri.Memory.Allocation`'s
`targetUIntBytesMirror refRuntimeLayoutV2.base` and `leBytesOfNat`. -/
theorem targetUIntBytesMirror_le_eq_leBytesOfNat (n : Nat) (hn : n ≤ 16)
    (d : Miri.ABI.U128) :
    targetUIntBytesMirror refRuntimeLayoutV2.base
        (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) d =
      .ok (Array.mk (leBytesOfNat n d.toNat)) := by
  have h_n_lt : n < HPow.hPow (2 : Nat) 64 := Nat.lt_of_le_of_lt hn (by decide)
  have h_sz_nat :
      (Miri.ABI.Size.ofBytes (UInt64.ofNat n)).bytes.toNat = n := by
    change HMod.hMod n (HPow.hPow (2 : Nat) 64) = n
    exact Nat.mod_eq_of_lt h_n_lt
  have h_not_gt :
      ¬ ((Miri.ABI.Size.ofBytes (UInt64.ofNat n)).bytes > 16) := by
    change ¬ (16 < (Miri.ABI.Size.ofBytes (UInt64.ofNat n)).bytes.toNat)
    rw [h_sz_nat]
    exact Nat.not_lt.mpr hn
  have h_endian :
      (refRuntimeLayoutV2.base.endian == Miri.ABI.Endian.little) = true := rfl
  have h_loop : ∀ k,
      forIn (m := Except Miri.Memory.AllocError) (List.range' 0 k 1)
        (Array.mk [] : Array UInt8)
        (fun index acc =>
          pure (ForInStep.yield
            (acc.push (UInt8.ofNat
              (HMod.hMod (HDiv.hDiv d.toNat (HPow.hPow 2 (8 * index))) 256))))) =
        .ok (Array.mk (leBytesOfNat k d.toNat)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [list_range'_succ_end_v2]
      refine forIn_append_ok_v2 _ _ _ (Array.mk (leBytesOfNat k d.toNat)) _ _
        ih ?_ (fun _ _ => ⟨_, rfl⟩)
      rw [List.forIn_cons]
      dsimp only [bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
      rw [List.forIn_nil]
      dsimp only [pure, Pure.pure, Except.pure, Nat.zero_add]
      apply congrArg Except.ok
      apply Array.toList_inj.mp
      rw [Array.toList_push]
      dsimp only
      rw [Nat.zero_add]
      apply List.ext_getElem?
      intro j
      cases Nat.lt_or_ge j (k + 1) with
      | inl h_lt =>
        rw [leBytesOfNat_getElem? (k + 1) d.toNat j h_lt]
        cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h_lt) with
        | inl h_jk =>
          have h_len : j < (leBytesOfNat k d.toNat).length := by
            rw [leBytesOfNat_length]; exact h_jk
          rw [List.getElem?_append_left h_len,
            leBytesOfNat_getElem? k d.toNat j h_jk]
        | inr h_eq =>
          rw [h_eq]
          have h_len : (leBytesOfNat k d.toNat).length = k :=
            leBytesOfNat_length k d.toNat
          rw [List.getElem?_append_right (Nat.le_of_eq h_len), h_len,
            Nat.sub_self, List.getElem?_cons_zero]
          have h_p2 : HPow.hPow (2 : Nat) (8 * k) = HPow.hPow (256 : Nat) k := by
            rw [Nat.pow_mul]
          rw [h_p2]
      | inr h_ge =>
        have h_l1 : (leBytesOfNat k d.toNat ++ [UInt8.ofNat
            (HMod.hMod (HDiv.hDiv d.toNat (HPow.hPow 2 (8 * k))) 256)]).length ≤
            j := by
          rw [List.length_append, leBytesOfNat_length]; exact h_ge
        have h_l2 : (leBytesOfNat (k + 1) d.toNat).length ≤ j := by
          rw [leBytesOfNat_length]; exact h_ge
        rw [List.getElem?_eq_none h_l1, List.getElem?_eq_none h_l2]
  dsimp only [targetUIntBytesMirror]
  rw [ite_neg_eq h_not_gt]
  simp only [h_endian, ite_true, h_sz_nat,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change Except.bind
    (forIn (m := Except Miri.Memory.AllocError) (List.range' 0 n 1)
      (Array.mk [] : Array UInt8)
      (fun index acc =>
        pure (ForInStep.yield
          (acc.push (UInt8.ofNat
            (HMod.hMod (HDiv.hDiv d.toNat (HPow.hPow 2 (8 * index))) 256))))))
    Except.ok = .ok (Array.mk (leBytesOfNat n d.toNat))
  rw [h_loop n]
  rfl

/-! ### `CallerMemory` Materialization, Extraction & Stack Framing -/

/-- `refPlainInitBytesV2?` succeeds on any plain initialized byte list. -/
theorem refPlainInitBytesV2?_map_init :
    ∀ (raw : List UInt8),
      refPlainInitBytesV2? (raw.map (fun b => AllocByte.init b none)) = some raw
  | [] => rfl
  | b :: rest => by
    dsimp only [List.map, refPlainInitBytesV2?]
    rw [refPlainInitBytesV2?_map_init rest]

/-- `ofMiriMutV2 (toMiriMutV2 m) = m`. -/
theorem ofMiriMutV2_toMiriMutV2 (m : Trusted.MirAst.Mutability) :
    ofMiriMutV2 (toMiriMutV2 m) = m := by
  cases m <;> rfl

/-- `toMiriMutV2` agrees with `MiriMemoryBridge.toMiriMutability`. -/
theorem toMiriMutV2_eq_toMiriMutability (m : Trusted.MirAst.Mutability) :
    toMiriMutV2 m = toMiriMutability m := by
  cases m <;> rfl

/-- Materializing any live, plain-initialized caller allocation via
`refAllocToMiriV2` succeeds via `Allocation.fromBytes` and satisfies
`MiriMemoryBridge.AllocByteSliceRel`. -/
theorem refAllocToMiriV2_plainInit_spec
    (a : Trusted.MirSemantics.Allocation) (raw : List UInt8)
    (h_live : a.live = true)
    (h_bytes : a.bytes = raw.map (fun b => AllocByte.init b none))
    (h_al : a.alignLog2 ≤ 29)
    (h_sz : raw.length < Nat.pow 2 64) :
    ∃ ma : RefMiriAlloc,
      refAllocToMiriV2 a = .ok ma ∧
      AllocByteSliceRel raw a ma := by
  let ⟨rawAlloc, h_fb, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Miri.Memory.Provenance) (Array.mk raw) ⟨a.alignLog2⟩
    (toMiriMutV2 a.mutability)
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
      (Miri.ABI.Size.ofBytes (UInt64.ofNat raw.length)))
    h_sz h_al
  refine ⟨rawAlloc.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
        (Miri.ABI.Size.ofBytes (UInt64.ofNat raw.length))), ?_, ?_⟩
  · dsimp only [refAllocToMiriV2]
    rw [h_bytes, refPlainInitBytesV2?_map_init]
    dsimp only
    rw [h_fb]
    have h_len : (raw.map (fun b => AllocByte.init b none)).length = raw.length :=
      List.length_map _
    rw [h_len]
  · refine ⟨h_live, h_al, by rw [h_bytes, List.length_map]; exact h_sz,
      h_bytes, rawAlloc, _, ?_, rfl⟩
    rw [← toMiriMutV2_eq_toMiriMutability]
    exact h_fb

private theorem refReadAllocBytesLoopV2_plain (alloc : RefMiriAlloc)
    (raw : Array UInt8)
    (h_pmap : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new)
    (h_imask : alloc.initializationMask =
      Miri.Memory.InitMask.new (Miri.ABI.Size.ofBytes (UInt64.ofNat raw.size))
        true) :
    ∀ (rem idx : Nat), idx + rem = raw.size →
      refReadAllocBytesLoopV2 alloc raw idx rem =
        (raw.toList.drop idx).map (fun b => AllocByte.init b none)
  | 0, idx, h_sum => by
    dsimp only [refReadAllocBytesLoopV2]
    have h_ge : raw.toList.length ≤ idx := by
      rw [Array.length_toList]
      exact Nat.le_of_eq h_sum.symm
    rw [List.drop_eq_nil_of_le h_ge]
    rfl
  | rem + 1, idx, h_sum => by
    have h_idx_lt : idx < raw.size := by
      have h1 : idx + 1 ≤ idx + (rem + 1) :=
        Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le rem)) idx
      rw [h_sum] at h1
      exact h1
    have h_im :
        alloc.initializationMask.get
          (Miri.ABI.Size.ofBytes (UInt64.ofNat idx)) = .ok true := by
      rw [h_imask]
      rfl
    have h_bp : refByteProvAtV2 alloc.provenanceMap idx = none := by
      rw [h_pmap]
      rfl
    have h_get : raw[idx]? =
        some (@GetElem.getElem (List UInt8) Nat UInt8 _ _ raw.toList idx
          (by rw [Array.length_toList]; exact h_idx_lt)) := by
      rw [← Array.getElem?_toList,
        List.getElem?_eq_getElem (by rw [Array.length_toList]; exact h_idx_lt)]
    have h_drop :
        raw.toList.drop idx =
          @GetElem.getElem (List UInt8) Nat UInt8 _ _ raw.toList idx
            (by rw [Array.length_toList]; exact h_idx_lt) ::
            raw.toList.drop (idx + 1) :=
      List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact h_idx_lt)
    dsimp only [refReadAllocBytesLoopV2]
    rw [h_im, h_bp, h_get, h_drop]
    dsimp only [Option.getD, ite_true_eq, List.map]
    exact congrArg (AllocByte.init _ none :: ·)
      (refReadAllocBytesLoopV2_plain alloc raw h_pmap h_imask rem (idx + 1)
        (by rw [Nat.add_assoc, Nat.add_comm 1 rem]; exact h_sum))

/-- Extracting a live plain-initialized caller allocation from `RefMiriMem`
recovers the exact `Trusted.MirSemantics.Allocation` whenever
`AllocByteSliceRel` holds. -/
theorem refExtractOneCallerAllocV2_of_allocByteSliceRel
    (memory : RefMiriMem) (orig cur : Trusted.MirSemantics.Allocation)
    (raw : List UInt8) (mid : Miri.Memory.AllocId)
    (entry : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (h_id : cur.allocId = orig.allocId)
    (h_mid : refExactAllocIdV2 orig.allocId = some mid)
    (h_find : memory.live.find? (fun e => e.1 == mid) = some (mid, entry))
    (h_rel : AllocByteSliceRel raw cur entry.allocation) :
    refExtractOneCallerAllocV2 memory orig = cur := by
  let ⟨h_live, h_al, _, h_bytes, rawAlloc, extra, h_fb, h_ma⟩ := h_rel
  have h_raw_lt : raw.length < Nat.pow 2 64 := by
    have h_len : cur.bytes.length < Nat.pow 2 64 := h_rel.2.2.1
    rw [h_bytes, List.length_map] at h_len
    exact h_len
  let ⟨rawAlloc', h_fb', _, h_bsz', h_al', h_mut', h_pmap', h_imask',
      h_gb'⟩ :=
    miriAlloc_fromBytes_spec (Prov := Miri.Memory.Provenance) (Array.mk raw)
      ⟨cur.alignLog2⟩ (toMiriMutability cur.mutability) extra h_raw_lt h_al
  rw [h_fb] at h_fb'
  injection h_fb' with h_ra_eq
  subst h_ra_eq
  have h_gb0 := (h_gb' 0 raw.length (by rw [Nat.zero_add]; exact Nat.le_refl _)).1
  have h_ext_all : (Array.mk raw).extract 0 (0 + raw.length) = Array.mk raw := by
    apply Array.toList_inj.mp
    rw [array_extract_toList, List.drop_zero, Nat.zero_add, Nat.sub_zero]
    exact List.take_of_length_le (Nat.le_refl _)
  rw [h_ext_all] at h_gb0
  have h_bsz_toNat :
      (rawAlloc.withExtra extra).byteSize.bytes.toNat = raw.length := by
    rw [h_bsz']
    exact u64_ofNat_toNat_of_lt h_raw_lt
  dsimp only [refExtractOneCallerAllocV2]
  rw [h_mid]
  dsimp only
  rw [h_find]
  dsimp only
  rw [h_ma]
  rw [h_bsz']
  have h_sz_mk : (Array.mk raw).size = raw.length := rfl
  have h_sz0 : Miri.ABI.Size.ZERO = Miri.ABI.Size.ofBytes (UInt64.ofNat 0) := rfl
  rw [h_sz_mk, h_sz0, h_gb0]
  dsimp only [Miri.ABI.Size.ofBytes]
  rw [u64_ofNat_toNat_of_lt h_raw_lt,
    refReadAllocBytesLoopV2_plain (rawAlloc.withExtra extra) (Array.mk raw)
      h_pmap' h_imask' raw.length 0 (Nat.zero_add _),
    List.drop_zero, h_al', h_mut', ← toMiriMutV2_eq_toMiriMutability,
    ofMiriMutV2_toMiriMutV2]
  cases cur with
  | mk cid cal cmut cbytes clive =>
    dsimp only at h_id h_bytes h_live
    subst h_id; subst h_bytes; subst h_live
    rfl

private theorem allocId_ofUInt64_value {u : UInt64} {mid : Miri.Memory.AllocId}
    (h_mid : Miri.Memory.AllocId.ofUInt64 u = some mid) :
    mid.value = u := by
  dsimp only [Miri.Memory.AllocId.ofUInt64] at h_mid
  cases h_z : decide (u = 0) with
  | true =>
    rw [dite_pos_eq (of_decide_eq_true h_z)] at h_mid
    cases h_mid
  | false =>
    have h_nz : ¬ (u = 0) := of_decide_eq_false h_z
    rw [dite_eq_right_of_eq_false (eq_false h_nz)] at h_mid
    injection h_mid with h_eq
    rw [← h_eq]

private theorem refExactAllocIdV2_value {aid : Trusted.MirAst.AllocId}
    {mid : Miri.Memory.AllocId} (h_mid : refExactAllocIdV2 aid = some mid) :
    mid.value = UInt64.ofNat aid := by
  dsimp only [refExactAllocIdV2] at h_mid
  cases h_fit : refAllocIdFitsU64V2 aid with
  | false => rw [h_fit] at h_mid; cases h_mid
  | true =>
    rw [h_fit] at h_mid
    exact allocId_ofUInt64_value h_mid

/-- Stack framing for `refExtractCallerMemoryV2`: pushing a fresh callee stack
allocation whose `allocId` does not occur in `orig.allocations` leaves
`refExtractCallerMemoryV2 orig memory` bit-for-bit unchanged. -/
theorem refExtractCallerMemoryV2_push_fresh_stack
    (orig : CallerMemory) (memory : RefMiriMem)
    (stackId : Miri.Memory.AllocId)
    (stackEntry : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (h_fresh : ∀ a, a ∈ orig.allocations →
      UInt64.ofNat a.allocId ≠ stackId.value) :
    refExtractCallerMemoryV2 orig
        { memory with live := memory.live.push (stackId, stackEntry) } =
      refExtractCallerMemoryV2 orig memory := by
  dsimp only [refExtractCallerMemoryV2]
  apply congrArg CallerMemory.mk
  have h_map : ∀ (xs : List Trusted.MirSemantics.Allocation),
      (∀ a, a ∈ xs → UInt64.ofNat a.allocId ≠ stackId.value) →
      xs.map (refExtractOneCallerAllocV2
        { memory with live := memory.live.push (stackId, stackEntry) }) =
      xs.map (refExtractOneCallerAllocV2 memory) := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro h_fr
      dsimp only [List.map]
      have h_ne : UInt64.ofNat a.allocId ≠ stackId.value :=
        h_fr a (List.Mem.head rest)
      have h_one :
          refExtractOneCallerAllocV2
              { memory with live := memory.live.push (stackId, stackEntry) } a =
            refExtractOneCallerAllocV2 memory a := by
        dsimp only [refExtractOneCallerAllocV2]
        cases h_mid : refExactAllocIdV2 a.allocId with
        | none => rfl
        | some mid =>
          have h_mid_val := refExactAllocIdV2_value h_mid
          have h_beq_false : (stackId == mid) = false := by
            cases h_eq : (stackId == mid) with
            | false => rfl
            | true =>
              have h_id_eq : stackId = mid := eq_of_beq h_eq
              exact False.elim (h_ne (h_mid_val.symm.trans
                (congrArg Miri.Memory.AllocId.value h_id_eq.symm)))
          have h_find_eq :
              (memory.live.push (stackId, stackEntry)).find?
                  (fun e => e.1 == mid) =
                memory.live.find? (fun e => e.1 == mid) := by
            rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_push]
            induction memory.live.toList with
            | nil =>
              dsimp only [List.nil_append, List.find?]
              rw [h_beq_false]
            | cons r rs ih_l =>
              dsimp only [List.cons_append, List.find?]
              cases r.1 == mid with
              | true => rfl
              | false => exact ih_l
          dsimp only
          rw [h_find_eq]
      rw [h_one, ih (fun x hx => h_fr x (List.Mem.tail a hx))]
  exact h_map orig.allocations h_fresh

/-- Stack deallocation framing for `refExtractCallerMemoryV2`: removing a
non-caller stack allocation from `memory.live` leaves
`refExtractCallerMemoryV2 orig memory` bit-for-bit unchanged. -/
theorem refExtractCallerMemoryV2_filter_stack
    (orig : CallerMemory) (memory : RefMiriMem)
    (stackId : Miri.Memory.AllocId)
    (dead' : Array Miri.Memory.DeadAllocation)
    (h_fresh : ∀ a, a ∈ orig.allocations →
      UInt64.ofNat a.allocId ≠ stackId.value) :
    refExtractCallerMemoryV2 orig
        { memory with
          live := memory.live.filter (fun e => e.1 != stackId)
          dead := dead' } =
      refExtractCallerMemoryV2 orig memory := by
  dsimp only [refExtractCallerMemoryV2]
  apply congrArg CallerMemory.mk
  have h_map : ∀ (xs : List Trusted.MirSemantics.Allocation),
      (∀ a, a ∈ xs → UInt64.ofNat a.allocId ≠ stackId.value) →
      xs.map (refExtractOneCallerAllocV2
        { memory with
          live := memory.live.filter (fun e => e.1 != stackId)
          dead := dead' }) =
      xs.map (refExtractOneCallerAllocV2 memory) := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro h_fr
      dsimp only [List.map]
      have h_ne : UInt64.ofNat a.allocId ≠ stackId.value :=
        h_fr a (List.Mem.head rest)
      have h_one :
          refExtractOneCallerAllocV2
              { memory with
                live := memory.live.filter (fun e => e.1 != stackId)
                dead := dead' } a =
            refExtractOneCallerAllocV2 memory a := by
        dsimp only [refExtractOneCallerAllocV2]
        cases h_mid : refExactAllocIdV2 a.allocId with
        | none => rfl
        | some mid =>
          have h_mid_val := refExactAllocIdV2_value h_mid
          have h_find_eq :
              (memory.live.filter (fun e => e.1 != stackId)).find?
                  (fun e => e.1 == mid) =
                memory.live.find? (fun e => e.1 == mid) := by
            rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_filter]
            induction memory.live.toList with
            | nil => rfl
            | cons r rs ih_l =>
              dsimp only [List.filter, List.find?]
              cases h_neq : (r.1 != stackId) with
              | true =>
                dsimp only [List.find?]
                cases r.1 == mid with
                | true => rfl
                | false => exact ih_l
              | false =>
                have h_eq_s : r.1 = stackId := by
                  dsimp only [bne] at h_neq
                  cases h_b : (r.1 == stackId) with
                  | false => rw [h_b] at h_neq; cases h_neq
                  | true => exact eq_of_beq h_b
                have h_beq_a : (r.1 == mid) = false := by
                  rw [h_eq_s]
                  cases h_b : (stackId == mid) with
                  | false => rfl
                  | true =>
                    exact False.elim (h_ne (h_mid_val.symm.trans
                      (congrArg Miri.Memory.AllocId.value (eq_of_beq h_b).symm)))
                rw [h_beq_a]
                exact ih_l
          dsimp only
          rw [h_find_eq]
      rw [h_one, ih (fun x hx => h_fr x (List.Mem.tail a hx))]
  exact h_map orig.allocations h_fresh

/-! ## Section 3: Deterministic Execution Adequacy & Exclusivity Bridges -/

/-- Fuel-bounded Profile v2 fault-execution predicate over `evalStepV2`. -/
def execFaultProgV2 (p : Program) (fuel : Nat) (q : Query)
    (expected : FaultKind) : Prop :=
  match initStateV2 p q with
  | .error k => k = expected
  | .ok s₀ =>
    Anneal.MirWp.execOutcomeStateV2 p (fun _ => False) (fun k => k = expected)
      fuel s₀

/-- Fault adequacy and exclusivity for `execFaultProgV2`: proves fault
reachability, rules out all other faults, normal termination, divergence, and
`WellFormedV2`. -/
theorem fault_and_exclusive_of_execFaultV2 {p : Program} {q : Query}
    {fuel : Nat} {expected : FaultKind}
    (h_exec : execFaultProgV2 p fuel q expected) :
    ReachesResultV2 p q (.fault expected) ∧
    (∀ k : FaultKind, k ≠ expected → ¬ ReachesResultV2 p q (.fault k)) ∧
    (∀ out : TerminalOut, ¬ BehaviorV2 p q out) ∧
    ¬ DivergesV2 p q ∧
    ¬ WellFormedV2 p q := by
  dsimp only [execFaultProgV2] at h_exec
  cases h_init : initStateV2 p q with
  | error k =>
    rw [h_init] at h_exec
    subst h_exec
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [ReachesResultV2]; rw [h_init]
    · intro k' h_ne h_r
      dsimp only [ReachesResultV2] at h_r
      rw [h_init] at h_r
      injection h_r with h_eq
      exact h_ne h_eq
    · intro out h_b
      dsimp only [BehaviorV2, ReachesResultV2] at h_b
      rw [h_init] at h_b
      cases h_b
    · intro h_div
      let ⟨s₀, h_ok, _⟩ := h_div
      rw [h_init] at h_ok
      cases h_ok
    · intro h_wf
      let ⟨⟨s₀, h_ok, _⟩, _⟩ := h_wf
      rw [h_init] at h_ok
      cases h_ok
  | ok s₀ =>
    rw [h_init] at h_exec
    have h_reach_f : ReachesResultV2 p q (.fault expected) := by
      let ⟨s_end, res, h_r, h_st, h_res⟩ :=
        Anneal.MirWp.exists_terminal_of_execOutcomeStateV2 h_exec
      cases res with
      | step _ => exact False.elim h_res
      | done _ => exact False.elim h_res
      | fault k =>
        dsimp only at h_res
        subst h_res
        dsimp only [ReachesResultV2]
        rw [h_init]
        exact ⟨s_end, h_r, h_st⟩
    have h_excl_f : ∀ k : FaultKind, k ≠ expected →
        ¬ ReachesResultV2 p q (.fault k) := by
      intro k h_ne h_r
      dsimp only [ReachesResultV2] at h_r
      rw [h_init] at h_r
      let ⟨s, h_reach, _, _, h_ev⟩ := h_r
      let ⟨fuel', h_e'⟩ := Anneal.MirWp.execOutcomeStateV2_of_reaches h_exec h_reach
      cases fuel' with
      | zero => exact False.elim h_e'
      | succ f' =>
        have h_ev' : evalStepV2 p s = .fault k := h_ev
        change (match evalStepV2 p s with
          | .step st' =>
            Anneal.MirWp.execOutcomeStateV2 p (fun _ => False)
              (fun k => k = expected) f' st'
          | .done _ => False
          | .fault k => k = expected) at h_e'
        rw [h_ev'] at h_e'
        exact h_ne h_e'
    have h_no_beh : ∀ out : TerminalOut, ¬ BehaviorV2 p q out := by
      intro out h_b
      dsimp only [BehaviorV2, ReachesResultV2] at h_b
      rw [h_init] at h_b
      let ⟨s, h_reach, _, _, h_ev⟩ := h_b
      let ⟨fuel', h_e'⟩ := Anneal.MirWp.execOutcomeStateV2_of_reaches h_exec h_reach
      cases fuel' with
      | zero => exact False.elim h_e'
      | succ f' =>
        have h_ev' : evalStepV2 p s = .done out := h_ev
        change (match evalStepV2 p s with
          | .step st' =>
            Anneal.MirWp.execOutcomeStateV2 p (fun _ => False)
              (fun k => k = expected) f' st'
          | .done _ => False
          | .fault k => k = expected) at h_e'
        rw [h_ev'] at h_e'
        exact h_e'
    have h_ndiv : ¬ DivergesV2 p q := by
      intro h_div
      let ⟨s₀', h_ok, trace, h_t0, h_st⟩ := h_div
      rw [h_init] at h_ok
      injection h_ok with h_eq
      subst h_eq
      rw [← h_t0] at h_exec
      exact Anneal.MirWp.not_infinite_trace_of_execOutcomeStateV2 trace h_exec h_st
    exact ⟨h_reach_f, h_excl_f, h_no_beh, h_ndiv,
      fun h_wf => h_wf.2 expected h_reach_f⟩

/-- Budget-independent single-step core outcome of `evalRefStepV2 rp 0`. -/
inductive RefCoreOutcome where
  | running (miri' : RefMiriState)
  | returned (out : TerminalOut)
  | ub
  | blocked

/-- Single-step core transition of `evalRefStepV2 rp 0` (independent of
`stepsExecuted`/`maxSteps`), directly calling
`Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)`. -/
noncomputable def evalRefCoreV2 (rp : RefProg) (retTy : MirTy)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (miri : RefMiriState) : RefCoreOutcome :=
  match Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 miri with
  | (miri', .ok true) =>
    if miri'.stack.frames.isEmpty then
      let origCm := miri'.machine.user.callerMem
      match refReadReturnValV2 miri'.machine.memory origCm retTy retPlace with
      | .ok retVal =>
        .returned (.returned ⟨retVal,
          refExtractCallerMemoryV2 origCm miri'.machine.memory⟩)
      | .error .undefined => .ub
      | .error .unsupported => .blocked
    else
      .running miri'
  | (_, .ok false) => .blocked
  | (miri', .error (.termination (.abort _))) =>
    .returned (.aborted
      (refExtractCallerMemoryV2 miri'.machine.user.callerMem
        miri'.machine.memory))
  | (_, .error (.undefinedBehavior _)) => .ub
  | (_, .error (.stack (.localExpectedLive _))) => .ub
  | (_, .error _) => .blocked

/-- Lift a `RefCoreOutcome` into a `RefOutcome` for a `RefState` with positive
remaining step budget. -/
noncomputable def liftCoreOutcome (rs : RefState) :
    RefCoreOutcome → RefOutcome
  | .running miri' =>
    .running { rs with miri := miri', stepsExecuted := rs.stepsExecuted + 1 }
  | .returned out => .returned out
  | .ub => .ub
  | .blocked => .blocked

/-- Whenever `rs.stepsExecuted < rs.maxSteps`, `evalRefStepV2 rp 0 rs` agrees
identically with `liftCoreOutcome rs (evalRefCoreV2 ...)`. -/
theorem evalRefStepV2_eq_liftCore_of_lt (rp : RefProg) (rs : RefState)
    (h_lt : Nat.blt rs.stepsExecuted rs.maxSteps = true) :
    evalRefStepV2 rp 0 rs =
      liftCoreOutcome rs
        (evalRefCoreV2 rp rs.retTy rs.retPlace rs.miri) := by
  dsimp only [evalRefStepV2, evalRefCoreV2]
  rw [h_lt, Bool.not_true, ite_false_eq]
  cases Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 rs.miri with
  | mk miri' res =>
    cases res with
    | ok b =>
      cases b with
      | false => rfl
      | true =>
        dsimp only
        cases miri'.stack.frames.isEmpty with
        | false => rfl
        | true =>
          dsimp only [ite_true_eq]
          cases refReadReturnValV2 miri'.machine.memory
              miri'.machine.user.callerMem rs.retTy rs.retPlace with
          | ok _ => rfl
          | error k => cases k <;> rfl
    | error e =>
      cases e with
      | undefinedBehavior _ => rfl
      | stack se => cases se <;> rfl
      | termination te => cases te <;> rfl
      | invalidProgram _ | unsupported _ | resourceExhaustion _
      | machineStop _ | invalidBlock _ | frameIndexChanged
      | expectedMirLocation | retagWriteToReadOnly | callback _ => rfl

/-- Whenever `rs.stepsExecuted ≥ rs.maxSteps`, `evalRefStepV2 rp 0 rs` returns
`.exhaustedStepLimit`. -/
theorem evalRefStepV2_eq_exhausted_of_ge (rp : RefProg) (rs : RefState)
    (h_ge : Nat.blt rs.stepsExecuted rs.maxSteps = false) :
    evalRefStepV2 rp 0 rs = .exhaustedStepLimit := by
  dsimp only [evalRefStepV2]
  rw [h_ge]
  rfl

/-- Fuel-bounded execution predicate over `evalRefCoreV2` (driving real
`Miri.Interpreter.ExecutionMachine.step`). -/
def refCoreExecV2 (rp : RefProg) (retTy : MirTy)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (onRet : TerminalOut → Prop) (onUb onBlk : Prop)
    (fuel : Nat) (miri : RefMiriState) : Prop :=
  @Nat.rec (fun _ => RefMiriState → Prop)
    (fun _ => False)
    (fun _ ih m =>
      match evalRefCoreV2 rp retTy retPlace m with
      | .running m' => ih m'
      | .returned out => onRet out
      | .ub => onUb
      | .blocked => onBlk)
    fuel miri

private theorem refCoreExecV2_of_reaches {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop}
    {rs₁ rs₂ : RefState} {fuel : Nat}
    (h_rt : rs₁.retTy = rt) (h_rpl : rs₁.retPlace = rpl)
    (h_exec : refCoreExecV2 rp rt rpl onRet onUb onBlk fuel rs₁.miri)
    (h_reach : RefReachesV2 rp rs₁ rs₂) :
    rs₂.retTy = rt ∧ rs₂.retPlace = rpl ∧
    ∃ fuel', refCoreExecV2 rp rt rpl onRet onUb onBlk fuel' rs₂.miri := by
  induction h_reach with
  | refl => exact ⟨h_rt, h_rpl, fuel, h_exec⟩
  | @tail rsMid rsNext _ h_step ih =>
    let ⟨h_rtM, h_rplM, fuel₁, h_e₁⟩ := ih
    cases fuel₁ with
    | zero => exact False.elim h_e₁
    | succ fuel₂ =>
      let ⟨c, h_c, h_ev⟩ := h_step
      have hc0 : c = 0 := h_c
      subst hc0
      cases h_blt : Nat.blt rsMid.stepsExecuted rsMid.maxSteps with
      | false =>
        rw [evalRefStepV2_eq_exhausted_of_ge rp rsMid h_blt] at h_ev
        cases h_ev
      | true =>
        rw [evalRefStepV2_eq_liftCore_of_lt rp rsMid h_blt] at h_ev
        rw [h_rtM, h_rplM] at h_ev
        cases h_core : evalRefCoreV2 rp rt rpl rsMid.miri with
        | returned _ => rw [h_core] at h_ev; cases h_ev
        | ub => rw [h_core] at h_ev; cases h_ev
        | blocked => rw [h_core] at h_ev; cases h_ev
        | running m' =>
          rw [h_core] at h_ev
          dsimp only [liftCoreOutcome] at h_ev
          injection h_ev with h_eq
          subst h_eq
          change (match evalRefCoreV2 rp rt rpl rsMid.miri with
            | .running m'' => refCoreExecV2 rp rt rpl onRet onUb onBlk fuel₂ m''
            | .returned out => onRet out
            | .ub => onUb
            | .blocked => onBlk) at h_e₁
          rw [h_core] at h_e₁
          exact ⟨h_rtM, h_rplM, fuel₂, h_e₁⟩

private theorem refReachesV2_head {rp : RefProg} {rs₁ rs₂ rs₃ : RefState}
    (h_first : RefStepV2 rp rs₁ (.running rs₂))
    (h_rest : RefReachesV2 rp rs₂ rs₃) :
    RefReachesV2 rp rs₁ rs₃ := by
  induction h_rest with
  | refl => exact RefReachesV2.tail (RefReachesV2.refl rs₁) h_first
  | tail _ h_last ih => exact RefReachesV2.tail ih h_last

private theorem nat_blt_true_of_lt {a b : Nat} (h : a < b) :
    Nat.blt a b = true :=
  (nat_ble_true_iff (a + 1) b).2 h

private theorem refCoreExecV2_reaches_terminal {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} :
    ∀ {fuel : Nat} (m : RefMiriState) (stepsExec : Nat),
      refCoreExecV2 rp rt rpl onRet onUb onBlk fuel m →
      ∃ rs_end out,
        RefReachesV2 rp
          { miri := m, retTy := rt, retPlace := rpl,
            stepsExecuted := stepsExec, maxSteps := stepsExec + fuel }
          rs_end ∧
        RefStepV2 rp rs_end out ∧
        match out with
        | .running _ | .exhaustedStepLimit => False
        | .returned o => onRet o
        | .ub => onUb
        | .blocked => onBlk
  | 0, _, _, h_exec => False.elim h_exec
  | fuel + 1, m, stepsExec, h_exec => by
    change (match evalRefCoreV2 rp rt rpl m with
      | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk fuel m'
      | .returned out => onRet out
      | .ub => onUb
      | .blocked => onBlk) at h_exec
    have h_lt : Nat.blt stepsExec (stepsExec + (fuel + 1)) = true :=
      nat_blt_true_of_lt (Nat.lt_add_of_pos_right (Nat.succ_pos fuel))
    let rs0 : RefState := {
      miri := m, retTy := rt, retPlace := rpl,
      stepsExecuted := stepsExec, maxSteps := stepsExec + (fuel + 1)
    }
    cases h_core : evalRefCoreV2 rp rt rpl m with
    | running m' =>
      rw [h_core] at h_exec
      have h_st : RefStepV2 rp rs0
          (.running {
            miri := m', retTy := rt, retPlace := rpl,
            stepsExecuted := stepsExec + 1,
            maxSteps := (stepsExec + 1) + fuel
          }) := by
        refine ⟨0, rfl, ?_⟩
        rw [evalRefStepV2_eq_liftCore_of_lt rp rs0 h_lt]
        dsimp only [rs0]
        rw [h_core]
        dsimp only [liftCoreOutcome]
        have h_add : stepsExec + (fuel + 1) = (stepsExec + 1) + fuel := by
          rw [Nat.add_assoc, Nat.add_comm 1 fuel]
        rw [h_add]
      let ⟨rs_end, out, h_r, h_end, h_ok⟩ :=
        refCoreExecV2_reaches_terminal m' (stepsExec + 1) h_exec
      exact ⟨rs_end, out, refReachesV2_head h_st h_r, h_end, h_ok⟩
    | returned out =>
      rw [h_core] at h_exec
      refine ⟨rs0, .returned out, RefReachesV2.refl rs0, ⟨0, rfl, ?_⟩, h_exec⟩
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs0 h_lt]
      dsimp only [rs0]
      rw [h_core]
      rfl
    | ub =>
      rw [h_core] at h_exec
      refine ⟨rs0, .ub, RefReachesV2.refl rs0, ⟨0, rfl, ?_⟩, h_exec⟩
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs0 h_lt]
      dsimp only [rs0]
      rw [h_core]
      rfl
    | blocked =>
      rw [h_core] at h_exec
      refine ⟨rs0, .blocked, RefReachesV2.refl rs0, ⟨0, rfl, ?_⟩, h_exec⟩
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs0 h_lt]
      dsimp only [rs0]
      rw [h_core]
      rfl

private theorem not_refDiverges_of_coreExec {rp : RefProg} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} :
    ∀ {fuel : Nat} (trace : Nat → RefState) (base : Nat),
      (trace 0).retTy = rt →
      (trace 0).retPlace = rpl →
      refCoreExecV2 rp rt rpl onRet onUb onBlk fuel (trace 0).miri →
      (∀ n : Nat,
        RefStepV2 rp
          { trace n with stepsExecuted := base + n, maxSteps := base + n + 1 }
          (.running
            { trace (n + 1) with
              stepsExecuted := base + n + 1, maxSteps := base + n + 1 })) →
      False
  | 0, _, _, _, _, h_exec, _ => h_exec
  | fuel + 1, trace, base, h_rt, h_rpl, h_exec, h_steps => by
    let ⟨c, hc, h_ev⟩ := h_steps 0
    have hc0 : c = 0 := hc
    subst hc0
    have h_lt : Nat.blt (base + 0) (base + 0 + 1) = true :=
      nat_blt_true_of_lt (Nat.lt_succ_self (base + 0))
    rw [evalRefStepV2_eq_liftCore_of_lt rp _ h_lt] at h_ev
    dsimp only at h_ev
    rw [h_rt, h_rpl] at h_ev
    change (match evalRefCoreV2 rp rt rpl (trace 0).miri with
      | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk fuel m'
      | .returned out => onRet out
      | .ub => onUb
      | .blocked => onBlk) at h_exec
    cases h_core : evalRefCoreV2 rp rt rpl (trace 0).miri with
    | returned _ => rw [h_core] at h_ev; cases h_ev
    | ub => rw [h_core] at h_ev; cases h_ev
    | blocked => rw [h_core] at h_ev; cases h_ev
    | running m' =>
      rw [h_core] at h_ev h_exec
      dsimp only [liftCoreOutcome] at h_ev
      injection h_ev with h_eq
      have h_m1 : (trace 1).miri = m' :=
        (congrArg RefState.miri h_eq).symm
      have h_rt1 : (trace 1).retTy = rt :=
        (congrArg RefState.retTy h_eq).symm
      have h_rpl1 : (trace 1).retPlace = rpl :=
        (congrArg RefState.retPlace h_eq).symm
      rw [← h_m1] at h_exec
      exact not_refDiverges_of_coreExec (fun n => trace (n + 1)) (base + 1)
        h_rt1 h_rpl1 h_exec (fun n => by
          have h_sn := h_steps (n + 1)
          have h_add : base + (n + 1) = (base + 1) + n := by
            rw [Nat.add_assoc, Nat.add_comm 1 n, ← Nat.add_assoc]
          rw [h_add] at h_sn
          exact h_sn)

private theorem not_refDiverges_of_init_coreExec {rp : RefProg} {q : Query}
    {m₀ : RefMiriState} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} {fuel : Nat}
    (h_init : ∀ ms : Nat, initRefStateV2 rp q ms =
      .ok { miri := m₀, retTy := rt, retPlace := rpl,
            stepsExecuted := 0, maxSteps := ms })
    (h_exec : refCoreExecV2 rp rt rpl onRet onUb onBlk fuel m₀) :
    ¬ RefDivergesV2 rp q := by
  intro ⟨rs₀, h_ok, trace, h_t0, h_steps⟩
  rw [h_init 0] at h_ok
  injection h_ok with h_eq
  subst h_eq
  have h_m0 : (trace 0).miri = m₀ := congrArg RefState.miri h_t0
  have h_rt0 : (trace 0).retTy = rt := congrArg RefState.retTy h_t0
  have h_rpl0 : (trace 0).retPlace = rpl := congrArg RefState.retPlace h_t0
  rw [← h_m0] at h_exec
  exact not_refDiverges_of_coreExec trace 0 h_rt0 h_rpl0 h_exec (fun n => by
    have h_sn := h_steps n
    rw [Nat.zero_add]
    exact h_sn)

private def refCoreOutcomePred (onRet : TerminalOut → Prop)
    (onUb onBlk : Prop) : RefOutcome → Prop
  | .running _ | .exhaustedStepLimit => True
  | .returned o => onRet o
  | .ub => onUb
  | .blocked => onBlk

private theorem ref_outcome_of_coreExec_reaches {rp : RefProg} {q : Query}
    {m₀ : RefMiriState} {rt : MirTy}
    {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {onRet : TerminalOut → Prop} {onUb onBlk : Prop} {fuel ms : Nat}
    {out : RefOutcome}
    (h_init : initRefStateV2 rp q ms =
      .ok { miri := m₀, retTy := rt, retPlace := rpl,
            stepsExecuted := 0, maxSteps := ms })
    (h_exec : refCoreExecV2 rp rt rpl onRet onUb onBlk fuel m₀)
    (h_ro : RefReachesOutcomeV2 rp q ms out) :
    refCoreOutcomePred onRet onUb onBlk out := by
  dsimp only [RefReachesOutcomeV2] at h_ro
  rw [h_init] at h_ro
  let ⟨rs, h_reach, c, hc, h_ev⟩ := h_ro
  have hc0 : c = 0 := hc
  subst hc0
  let ⟨h_rt, h_rpl, fuel', h_e'⟩ :=
    refCoreExecV2_of_reaches rfl rfl h_exec h_reach
  cases fuel' with
  | zero => exact False.elim h_e'
  | succ f' =>
    cases h_blt : Nat.blt rs.stepsExecuted rs.maxSteps with
    | false =>
      rw [evalRefStepV2_eq_exhausted_of_ge rp rs h_blt] at h_ev
      rw [← h_ev]
      exact True.intro
    | true =>
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs h_blt, h_rt, h_rpl] at h_ev
      change (match evalRefCoreV2 rp rt rpl rs.miri with
        | .running m' => refCoreExecV2 rp rt rpl onRet onUb onBlk f' m'
        | .returned o => onRet o
        | .ub => onUb
        | .blocked => onBlk) at h_e'
      cases h_core : evalRefCoreV2 rp rt rpl rs.miri with
      | running _ => rw [h_core] at h_ev; rw [← h_ev]; exact True.intro
      | returned o =>
        rw [h_core] at h_ev h_e'
        dsimp only [liftCoreOutcome] at h_ev
        rw [← h_ev]
        exact h_e'
      | ub => rw [h_core] at h_ev h_e'; rw [← h_ev]; exact h_e'
      | blocked => rw [h_core] at h_ev h_e'; rw [← h_ev]; exact h_e'

/-- Adequacy for normal termination in $M_{\text{ref}}^{\text{v2}}$: a single
`refCoreExecV2` witness establishes universal `RefWellFormedV2` (across all
`maxSteps`), `RefBehaviorV2`, outcome uniqueness, and `¬ RefDivergesV2`. -/
theorem ref_ok_of_coreExec {rp : RefProg} {q : Query} {m₀ : RefMiriState}
    {rt : MirTy} {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fuel : Nat} {out : TerminalOut}
    (h_init : ∀ ms : Nat, initRefStateV2 rp q ms =
      .ok { miri := m₀, retTy := rt, retPlace := rpl,
            stepsExecuted := 0, maxSteps := ms })
    (h_exec : refCoreExecV2 rp rt rpl (fun o => o = out) False False fuel m₀) :
    RefWellFormedV2 rp q ∧
    RefBehaviorV2 rp q out ∧
    (∀ out', RefBehaviorV2 rp q out' → out' = out) ∧
    ¬ RefDivergesV2 rp q := by
  refine ⟨fun ms => ⟨⟨_, h_init ms, fun _ _ => ⟨0, rfl⟩⟩,
      fun h_ro => ref_outcome_of_coreExec_reaches (h_init ms) h_exec h_ro,
      fun h_ro => ref_outcome_of_coreExec_reaches (h_init ms) h_exec h_ro⟩,
    ?_, fun out' ⟨ms, h_ro⟩ =>
      ref_outcome_of_coreExec_reaches (h_init ms) h_exec h_ro,
    not_refDiverges_of_init_coreExec h_init h_exec⟩
  let ⟨rs_end, res, h_r, h_st, h_ok⟩ :=
    refCoreExecV2_reaches_terminal m₀ 0 h_exec
  cases res with
  | running _ | exhaustedStepLimit | ub | blocked => exact False.elim h_ok
  | returned out' =>
    dsimp only at h_ok
    subst h_ok
    refine ⟨0 + fuel, ?_⟩
    dsimp only [RefReachesOutcomeV2]
    rw [h_init (0 + fuel)]
    exact ⟨rs_end, h_r, h_st⟩

/-- Adequacy for UB reachability in $M_{\text{ref}}^{\text{v2}}$ from an
in-body `refCoreExecV2` witness. -/
theorem ref_ub_of_coreExec {rp : RefProg} {q : Query} {m₀ : RefMiriState}
    {rt : MirTy} {rpl : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance}
    {fuel : Nat}
    (h_init : ∀ ms : Nat, initRefStateV2 rp q ms =
      .ok { miri := m₀, retTy := rt, retPlace := rpl,
            stepsExecuted := 0, maxSteps := ms })
    (h_exec : refCoreExecV2 rp rt rpl (fun _ => False) True False fuel m₀) :
    (∃ ms : Nat, RefReachesOutcomeV2 rp q ms .ub) ∧
    ¬ RefWellFormedV2 rp q ∧
    (∀ ms : Nat, ¬ RefReachesOutcomeV2 rp q ms .blocked) ∧
    (∀ out : TerminalOut, ¬ RefBehaviorV2 rp q out) ∧
    ¬ RefDivergesV2 rp q := by
  have h_ub : ∃ ms : Nat, RefReachesOutcomeV2 rp q ms .ub := by
    let ⟨rs_end, res, h_r, h_st, h_ok⟩ :=
      refCoreExecV2_reaches_terminal m₀ 0 h_exec
    cases res with
    | running _ | exhaustedStepLimit | returned _ | blocked =>
      exact False.elim h_ok
    | ub =>
      refine ⟨0 + fuel, ?_⟩
      dsimp only [RefReachesOutcomeV2]
      rw [h_init (0 + fuel)]
      exact ⟨rs_end, h_r, h_st⟩
  refine ⟨h_ub, fun h_rwf => let ⟨ms, h_u⟩ := h_ub; (h_rwf ms).2.1 h_u,
    fun ms h_ro => ref_outcome_of_coreExec_reaches (h_init ms) h_exec h_ro,
    fun _ ⟨ms, h_ro⟩ => ref_outcome_of_coreExec_reaches (h_init ms) h_exec h_ro,
    not_refDiverges_of_init_coreExec h_init h_exec⟩

/-- Adequacy for entry-time UB in $M_{\text{ref}}^{\text{v2}}$
(`initRefStateV2 rp q ms = .error .undefined`). -/
theorem ref_ub_of_init_error {rp : RefProg} {q : Query}
    (h_init : ∀ ms : Nat, initRefStateV2 rp q ms = .error .undefined) :
    (∃ ms : Nat, RefReachesOutcomeV2 rp q ms .ub) ∧
    ¬ RefWellFormedV2 rp q ∧
    (∀ ms : Nat, ¬ RefReachesOutcomeV2 rp q ms .blocked) ∧
    (∀ out : TerminalOut, ¬ RefBehaviorV2 rp q out) ∧
    ¬ RefDivergesV2 rp q := by
  have h_ub : RefReachesOutcomeV2 rp q 0 .ub := by
    dsimp only [RefReachesOutcomeV2]; rw [h_init 0]; rfl
  refine ⟨⟨0, h_ub⟩, fun h_rwf => (h_rwf 0).2.1 h_ub, ?_, ?_, ?_⟩
  · intro ms h_blk
    dsimp only [RefReachesOutcomeV2] at h_blk
    rw [h_init ms] at h_blk
    cases h_blk
  · intro out ⟨ms, h_r⟩
    dsimp only [RefReachesOutcomeV2] at h_r
    rw [h_init ms] at h_r
    cases h_r
  · intro ⟨rs₀, h_ok, _⟩
    rw [h_init 0] at h_ok
    cases h_ok

end Anneal.MirCorrespondence
