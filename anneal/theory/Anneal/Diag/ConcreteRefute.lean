-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.NotationExtra
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp.Core
public import Anneal.MirWp.Execution

public section

namespace Anneal.Diag.ConcreteRefute

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-!
# Pass-1 Concrete Refutation and Non-Vacuity Helpers

Provides Pass-1 (`0`-TCB, zero banned tactics) combinators for dual-polar
specification adequacy checks:

1. **Non-vacuity witnesses** (`PreInhabited`, `PreInhabitedV2`,
   `preInhabited_of_witness`, `contractPreInhabited_of_witness`): witness
   valid entry inputs satisfying the safety precondition of `unsafe` bodies
   (for safe bodies, `PreInhabited` only requires valid entry arguments).
2. **Concrete deterministic refutation** (`behavior_unique_of_exec`,
   `refute_bodyVerified_of_execFault`,
   `refute_bodyContractSatisfied_of_execReturn`,
   `refute_bodyContractSatisfied_of_execAbort`,
   `refute_unitTheorem_of_fault`, `refute_unitTheorem_of_not_property`,
   `refute_bodySatisfiesSafeContractV2_of_execReturn`, ...): witness-driven
   kernel refutations (`¬ Expected.claim`) on mutated Rust bodies.
-/

/-- Profile v1 value-entry precondition non-vacuity for `body`. -/
@[expose] noncomputable def PreInhabited (safety : List Val → Prop)
    (body : Body) : Prop :=
  ∃ args : List Val,
    ValidEntryArgs body args ∧ (body.isUnsafe = true → safety args)

/-- Witness `PreInhabited safety body` from explicit valid entry arguments. -/
theorem preInhabited_of_witness {safety : List Val → Prop} {body : Body}
    (args : List Val) (h_args : ValidEntryArgs body args)
    (h_safety : body.isUnsafe = true → safety args) :
    PreInhabited safety body :=
  ⟨args, h_args, h_safety⟩

/-- Witness `ContractPreInhabited body c` from valid entry arguments. -/
theorem contractPreInhabited_of_witness {body : Body} {c : FnContract}
    (args : List Val) (h_args : ValidEntryArgs body args)
    (h_safety : body.isUnsafe = true → c.safetyPre { args := args })
    (h_beh : c.behaviorPre { args := args }) :
    ContractPreInhabited body c :=
  ⟨args, h_args, h_safety, h_beh⟩

/-- Profile v2 precondition non-vacuity for `body`. -/
@[expose] noncomputable def PreInhabitedV2 (safety : Query → Prop)
    (body : Body) : Prop :=
  ∃ q : Query, ValidEntryArgsV2 body q ∧ (body.isUnsafe = true → safety q)

/-- Witness `PreInhabitedV2 safety body` from an explicit entry query. -/
theorem preInhabitedV2_of_witness {safety : Query → Prop} {body : Body}
    (q : Query) (h_valid : ValidEntryArgsV2 body q)
    (h_safety : body.isUnsafe = true → safety q) :
    PreInhabitedV2 safety body :=
  ⟨q, h_valid, h_safety⟩

/-- Structural indexed-list universal quantifier avoiding explicit arithmetic
index rewrites in Pass 1. -/
@[expose] noncomputable def AllBodiesAt (P : Nat → Body → Prop)
    (bs : List Body) : Prop :=
  @List.rec Body (fun _ => (Nat → Body → Prop) → Prop) (fun _ => True)
    (fun b _ rest Q => Q 0 b ∧ rest (fun i x => Q (i + 1) x)) bs P

/-- Specification-level safety-precondition non-vacuity across all bodies of
`p`: every body admits a valid entry argument list that, when the body is
`unsafe`, satisfies `specs.safety body.identity`. For safe bodies this only
requires valid entry arguments; contract `behaviorPre` is not constrained. -/
@[expose] noncomputable def SpecsPreInhabited (specs : Specs) (p : Program) :
    Prop :=
  AllBodiesAt (fun _ body => PreInhabited (specs.safety body.identity) body)
    p.bodies

/-- Profile v2 specification-level entry precondition non-vacuity across all
bodies of `p`. -/
@[expose] noncomputable def SpecsPreInhabitedV2 (specs : SpecsV2)
    (p : Program) : Prop :=
  AllBodiesAt (fun _ body => PreInhabitedV2 (specs.safety body.identity) body)
    p.bodies

/-- Concrete `execProg` pins any Profile v1 `Behavior` to that exact
outcome, across both single-body and multi-call programs. -/
theorem behavior_unique_of_exec {p : Program} {q : Query} {fuel : Nat}
    {out out' : TerminalOut}
    (h_exec : execProg p fuel q (fun o => o = out))
    (h_beh : Behavior p q out') :
    out' = out :=
  ((spec_and_behavior_of_wp_eq (wpProg_of_execProg h_exec)).2.2.2
    (fun o => o = out) rfl).2 out' h_beh

/-- Specialization of `behavior_unique_of_exec` to normal return values. -/
theorem behavior_returned_unique {p : Program} {q : Query} {fuel : Nat}
    {out : Out} {out' : TerminalOut}
    (h_exec : execProg p fuel q (fun o => o = .returned out))
    (h_beh : Behavior p q out') :
    out' = .returned out :=
  behavior_unique_of_exec h_exec h_beh

/-- Any concrete `execFaultProg` witness refutes `WellFormed p q`. -/
theorem execFault_not_wellFormed {p : Program} {q : Query} {fuel : Nat}
    {expected : FaultKind} (h_fault : execFaultProg p fuel q expected) :
    ¬ WellFormed p q := by
  let ⟨_, _, _, _, h_nwf⟩ :=
    reaches_fault_and_exclusive_of_wpFault_base p q fuel expected
      (wpFaultProg_of_execFaultProg h_fault)
  exact h_nwf

/-- Refute `BodyVerified p defId body safetyPre` when concrete execution
faults. -/
theorem refute_bodyVerified_of_execFault {p : Program} {defId : DefId}
    {body : Body} {safetyPre : List Val → Prop} {fuel : Nat}
    {args : List Val} {expected : FaultKind}
    (h_args : ValidEntryArgs body args)
    (h_safe : body.isUnsafe = true → safetyPre args)
    (h_fault : execFaultProg (entryProgForBody p defId) fuel
      { args := args } expected) :
    ¬ BodyVerified p defId body safetyPre := by
  intro h_bv
  exact execFault_not_wellFormed h_fault (h_bv.2.2 args h_args h_safe)

/-- Refute `BodyContractSatisfied p defId body c` when concrete execution
returns an output `retOut` violating `c.postReturn`. -/
theorem refute_bodyContractSatisfied_of_execReturn {p : Program}
    {defId : DefId} {body : Body} {c : FnContract} {fuel : Nat}
    {args : List Val} {retOut : Out}
    (h_args : ValidEntryArgs body args)
    (h_pre : c.effectiveBehaviorPre body.isUnsafe { args := args })
    (h_exec : execProg (entryProgForBody p defId) fuel { args := args }
      (fun o => o = .returned retOut))
    (h_bad : ¬ c.postReturn { args := args } retOut) :
    ¬ BodyContractSatisfied p defId body c := by
  intro h_sat
  let ⟨_, h_beh, _, _⟩ := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_exec)
  exact h_bad (((h_sat.2.2 args h_args).2 h_pre).1 (.returned retOut) h_beh)

/-- Refute `BodyContractSatisfied p defId body c` when concrete execution aborts
under `--panic abort` (`EffectMask` forbids `.aborted`). -/
theorem refute_bodyContractSatisfied_of_execAbort {p : Program}
    {defId : DefId} {body : Body} {c : FnContract} {fuel : Nat}
    {args : List Val} {cm : CallerMemory}
    (h_args : ValidEntryArgs body args)
    (h_pre : c.effectiveBehaviorPre body.isUnsafe { args := args })
    (h_exec : execProg (entryProgForBody p defId) fuel { args := args }
      (fun o => o = .aborted cm)) :
    ¬ BodyContractSatisfied p defId body c := by
  intro h_sat
  let ⟨_, h_beh, _, _⟩ := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_exec)
  exact ((h_sat.2.2 args h_args).2 h_pre).1 (.aborted cm) h_beh

/-- Refute `BodyContractSatisfied p defId body c` when concrete execution
unwinds outside the allowed `effects` / `postUnwind`. -/
theorem refute_bodyContractSatisfied_of_execUnwind {p : Program}
    {defId : DefId} {body : Body} {c : FnContract} {fuel : Nat}
    {args : List Val} {cm : CallerMemory}
    (h_args : ValidEntryArgs body args)
    (h_pre : c.effectiveBehaviorPre body.isUnsafe { args := args })
    (h_exec : execProg (entryProgForBody p defId) fuel { args := args }
      (fun o => o = .unwound cm))
    (h_bad :
      ¬ (c.effects.noUnwind = false ∧ c.postUnwind { args := args } cm)) :
    ¬ BodyContractSatisfied p defId body c := by
  intro h_sat
  let ⟨_, h_beh, _, _⟩ := spec_and_behavior_of_wp_eq (wpProg_of_execProg h_exec)
  exact h_bad (((h_sat.2.2 args h_args).2 h_pre).1 (.unwound cm) h_beh)

/-- Refute `BodyContractSatisfied p defId body c` when concrete execution
faults. -/
theorem refute_bodyContractSatisfied_of_execFault {p : Program}
    {defId : DefId} {body : Body} {c : FnContract} {fuel : Nat}
    {args : List Val} {expected : FaultKind}
    (h_args : ValidEntryArgs body args)
    (h_safe : c.effectiveSafetyPre body.isUnsafe { args := args })
    (h_fault : execFaultProg (entryProgForBody p defId) fuel
      { args := args } expected) :
    ¬ BodyContractSatisfied p defId body c := by
  intro h_sat
  exact execFault_not_wellFormed h_fault ((h_sat.2.2 args h_args).1 h_safe)

private theorem forall_getElem?_of_allBodiesAt :
    ∀ (bs : List Body) (P : Nat → Body → Prop) (idx : Nat) (body : Body),
      AllBodiesAt P bs →
      Trusted.MirSemantics.getElem? bs idx = some body →
      P idx body
  | [], _, _, _, _, h_get => by cases h_get
  | _ :: _, _, 0, _, h_all, h_get => by
    injection h_get with h_eq
    subst h_eq
    exact h_all.1
  | _ :: bs, P, idx + 1, body, h_all, h_get =>
    forall_getElem?_of_allBodiesAt bs (fun i x => P (i + 1) x) idx body
      h_all.2 h_get

/-- Bridge `SpecsPreInhabited` (`AllBodiesAt`) to the `Trusted.*`-only
indexed-body non-vacuity statement checked by `ci/audit_spec.py`. -/
theorem specsPreInhabited_forall_getElem? {specs : Specs} {p : Program}
    (h : SpecsPreInhabited specs p) :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? p.bodies defId = some body →
      ∃ args : List Val,
        ValidEntryArgs body args ∧
        (body.isUnsafe = true → specs.safety body.identity args) :=
  fun defId body h_get =>
    forall_getElem?_of_allBodiesAt p.bodies _ defId body h h_get

/-- Bridge `SpecsPreInhabitedV2` (`AllBodiesAt`) to the `Trusted.*`-only
Profile v2 indexed-body non-vacuity statement checked by `ci/audit_spec.py`. -/
theorem specsPreInhabitedV2_forall_getElem? {specs : SpecsV2} {p : Program}
    (h : SpecsPreInhabitedV2 specs p) :
    ∀ (defId : DefId) (body : Body),
      Trusted.MirSemantics.getElem? p.bodies defId = some body →
      ∃ q : Query,
        ValidEntryArgsV2 body q ∧
        (body.isUnsafe = true → specs.safety body.identity q) :=
  fun defId body h_get =>
    forall_getElem?_of_allBodiesAt p.bodies _ defId body h h_get

/-- Refute `bodySatisfiesContractEntry p e` across every entry in `p.bodies` via
`AllBodiesAt`: non-matching bodies discharge `stringBeq` by `rfl`. -/
theorem refute_bodySatisfiesContractEntry_of_allBodiesAt {p : Program}
    {e : ContractEntry}
    (h_all : AllBodiesAt
      (fun idx body => stringBeq body.identity e.identity = true →
        ¬ BodyContractSatisfied p idx body e.contract)
      p.bodies) :
    ¬ bodySatisfiesContractEntry p e :=
  fun ⟨defId, body, h_get, h_id, _, h_sat, _⟩ =>
    forall_getElem?_of_allBodiesAt p.bodies _ defId body h_all h_get h_id h_sat

/-- Refute `ContractEntriesSatisfied p (e :: rest)` from the head entry. -/
theorem refute_contractEntriesSatisfied_head {p : Program}
    {e : ContractEntry} {rest : List ContractEntry}
    (h_head : ¬ bodySatisfiesContractEntry p e) :
    ¬ ContractEntriesSatisfied p (e :: rest) :=
  fun h => h_head h.1

/-- Lift refutation of `ContractEntriesSatisfied` tail to the cons list. -/
theorem refute_contractEntriesSatisfied_tail {p : Program}
    {e : ContractEntry} {rest : List ContractEntry}
    (h_tail : ¬ ContractEntriesSatisfied p rest) :
    ¬ ContractEntriesSatisfied p (e :: rest) :=
  fun h => h_tail h.2

/-- Refute `(ContractSpecs entries).property p` from
`¬ ContractEntriesSatisfied p entries`. -/
theorem refute_contractSpecs_of_not_entries {p : Program}
    {entries : List ContractEntry}
    (h_not : ¬ ContractEntriesSatisfied p entries) :
    ¬ (ContractSpecs entries).property p := by
  unfold ContractSpecs
  cases identityRbBuildAux
      (fun (e : ContractEntry) => e.identity) id entries .empty with
  | none => exact fun h => h_not h.2
  | some _ => exact fun h => h_not h.2

/-- Refute `UnitTheorem c` from a fault in body `defId`. -/
theorem refute_unitTheorem_of_fault {c : Crate} {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {expected : FaultKind}
    (h_body : Trusted.MirSemantics.getElem? c.program.bodies defId = some body)
    (h_args : ValidEntryArgs body args)
    (h_safe : body.isUnsafe = true → c.specs.safety body.identity args)
    (h_fault : execFaultProg (entryProgForBody c.program defId) fuel
      { args := args } expected) :
    ¬ UnitTheorem c := by
  intro h_ut
  let ⟨_, _, _, _, _, h_bodies, _⟩ := h_ut.2
  exact refute_bodyVerified_of_execFault h_args h_safe h_fault
    (h_bodies defId body h_body)

/-- Refute `CrateTheorem c` from a fault in body `defId`. -/
theorem refute_crateTheorem_of_fault {c : Crate} {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {expected : FaultKind}
    (h_body : Trusted.MirSemantics.getElem? c.program.bodies defId = some body)
    (h_args : ValidEntryArgs body args)
    (h_safe : body.isUnsafe = true → c.specs.safety body.identity args)
    (h_fault : execFaultProg (entryProgForBody c.program defId) fuel
      { args := args } expected) :
    ¬ CrateTheorem c := by
  intro h_ct
  let ⟨_, _, _, _, _, h_bodies, _⟩ := h_ct.2
  exact refute_bodyVerified_of_execFault h_args h_safe h_fault
    (h_bodies defId body h_body)

/-- Refute `UnitTheorem c` directly from `¬ c.specs.property c.program`. -/
theorem refute_unitTheorem_of_not_property {c : Crate}
    (h_not : ¬ c.specs.property c.program) :
    ¬ UnitTheorem c := by
  intro h_ut
  let ⟨_, _, _, _, _, _, h_prop⟩ := h_ut.2
  exact h_not h_prop

/-- Refute `CrateTheorem c` directly from `¬ c.specs.property c.program`. -/
theorem refute_crateTheorem_of_not_property {c : Crate}
    (h_not : ¬ c.specs.property c.program) :
    ¬ CrateTheorem c := by
  intro h_ct
  let ⟨_, _, _, _, _, _, h_prop⟩ := h_ct.2
  exact h_not h_prop

/-- Profile v2 deterministic outcome uniqueness via `execProgV2`. -/
theorem behaviorV2_unique_of_exec {p : Program} {q : Query} {fuel : Nat}
    {out out' : TerminalOut}
    (h_exec : execProgV2 p fuel q (fun o => o = out))
    (h_beh : BehaviorV2 p q out') :
    out' = out :=
  ((spec_and_behaviorV2_of_exec_eq h_exec).2.2.2
    (fun o => o = out) rfl).2 out' h_beh

/-- Refute Profile v2 `BodySatisfiesSafeContractV2 p defId body contract` from
an observed return value violating `contract.postReturn`. -/
theorem refute_bodySatisfiesSafeContractV2_of_execReturn {p : Program}
    {defId : DefId} {body : Body} {contract : SafeContractV2}
    {fuel : Nat} {q : Query} {retOut : Out}
    (h_valid : ValidEntryArgsV2 body q)
    (h_pre : contract.behaviorPre q)
    (h_exec : execProgV2 (entryProgForBody p defId) fuel q
      (fun o => o = .returned retOut))
    (h_bad : ¬ contract.postReturn q retOut) :
    ¬ BodySatisfiesSafeContractV2 p defId body contract := by
  intro h_sat
  let ⟨_, h_beh, _, _⟩ := spec_and_behaviorV2_of_exec_eq h_exec
  have h_post := (h_sat.2.2 q h_valid h_pre).2 (.returned retOut) h_beh
  exact h_bad h_post

/-- Refute `UnitTheoremV2 c` directly from `¬ c.specs.property c.program`. -/
theorem refute_unitTheoremV2_of_not_property {c : CrateV2}
    (h_not : ¬ c.specs.property c.program) :
    ¬ UnitTheoremV2 c := by
  intro h_ut
  let ⟨_, _, _, _, _, _, h_prop⟩ := h_ut.2
  exact h_not h_prop

/-- Refute `CrateTheoremV2 c` directly from `¬ c.specs.property c.program`. -/
theorem refute_crateTheoremV2_of_not_property {c : CrateV2}
    (h_not : ¬ c.specs.property c.program) :
    ¬ CrateTheoremV2 c := by
  intro h_ct
  let ⟨_, _, _, _, _, _, h_prop⟩ := h_ct.2
  exact h_not h_prop

end Anneal.Diag.ConcreteRefute

end
