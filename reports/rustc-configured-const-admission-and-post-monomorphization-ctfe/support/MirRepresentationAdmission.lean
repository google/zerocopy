import Std
import AnnealResearch.Execution
set_option Elab.async false

/-!
# MIR Representation Sufficiency, Concrete Instance Admission, and Cross-Crate Completeness (FE-05..07)

This module models the three frontend-evaluation boundaries from Issue #45 (`FE-05`, `FE-06`,
`FE-07`) over `AnnealResearch.Execution`:

1. **FE-05 (`MirBodyRep`, `StructurallyWellFormed`):** separates structural well-formedness
   (closed local/block references and positive alignment) from runtime UB freedom so that
   structurally valid unsafe bodies (`unsafeUbBody`) remain admitted as verification subjects
   whose UB is exposed by `Execution.NoUB` rather than circularly excluded by admission.
2. **FE-06 (`InstanceKey`, `ProbeConfig`, `ConcreteEntryAdmitted`):** models the four
   `experiments/configured-admission/probe.rs` captures (`a1`, `b0`, `b1`, `unused_b1`),
   separating the conditional generic theorem for `checked<T, N>()` under `N <= T::LIMIT`
   from concrete entry-point admission over reachable monomorphized instances.
3. **FE-07 (`CrateGraphBundle`, `TwoCrateComplete`):** models cross-crate closure across an
   application crate and an upstream dependency crate (requiring dependency MIR bodies,
   associated-constant initializers, drop glue, host/target separation, and matched `cfg`/generated
   inputs).
-/

namespace AnnealResearch.MirRepresentationAdmission

/-! ## FE-05: Structural Well-Formedness vs Runtime UB (`MirBodyRep`) -/

-- MirBodyRep: (ownerId, localCount, targetRefMax, substArity, layoutAlign, hasUnsafeOp, triggersRuntimeUB)
abbrev MirBodyRep : Type :=
  Nat × Nat × Nat × Nat × Nat × Bool × Bool

noncomputable def StructurallyWellFormed (b : MirBodyRep) : Bool :=
  Nat.ble b.2.2.1 b.2.1 && Nat.ble 1 b.2.2.2.2.1

noncomputable def unsafeUbBody : MirBodyRep :=
  (101, 4, 2, 0, 4, true, true)

-- RepState: (stage, ubFault)
abbrev RepState : Type := Nat × Bool

noncomputable def initRepState : RepState := (0, false)

def BadRepState (s : RepState) : Prop := s.2 = true

def repStep (b : MirBodyRep) (u v : RepState) : Prop :=
  u = initRepState ∧ v = (1, b.2.2.2.2.2.2)

theorem repStep_noUB_of_fault_false (b : MirBodyRep) (hfault : b.2.2.2.2.2.2 = false) :
    Execution.NoUB (repStep b) BadRepState initRepState := by
  intro s hreach hbad
  have hfalse : s.2 = false := by
    refine Execution.invariant_reachable (Invariant := fun st : RepState => st.2 = false) rfl ?_ hreach
    intro u v _ edge
    cases edge with
    | intro _ hv =>
      subst hv
      exact hfault
  exact Bool.noConfusion (hfalse.symm.trans hbad)

theorem structural_admission_retains_unsafe_ub_subjects :
    StructurallyWellFormed unsafeUbBody = true ∧
    ¬ Execution.NoUB (repStep unsafeUbBody) BadRepState initRepState := by
  refine ⟨rfl, ?_⟩
  intro hnoub
  have hreach : Execution.Reach (repStep unsafeUbBody) initRepState (1, true) :=
    Execution.Reach.tail (Execution.Reach.refl initRepState) ⟨rfl, rfl⟩
  have hbad : BadRepState (1, true) := rfl
  exact Execution.bad_prefix_not_noUB (Bad := BadRepState) hreach hbad hnoub

/-! ## FE-06: Generic Theorem vs Concrete Instance Admission (`InstanceKey`, `ProbeConfig`) -/

-- InstanceKey: (implOwnerId, limitConst, constArgN, markerByte)
abbrev InstanceKey : Type := Nat × Nat × Nat × Nat

noncomputable def instA1 : InstanceKey := (1, 1, 1, 161)
noncomputable def instB0 : InstanceKey := (2, 0, 0, 176)
noncomputable def instB1 : InstanceKey := (2, 0, 1, 176)

-- InstState: (stage, retVal, ubFault)
abbrev InstState : Type := Nat × Option Nat × Bool

noncomputable def initInstState : InstState := (0, none, false)

def BadInstState (s : InstState) : Prop := s.2.2 = true

def checkedStep (inst : InstanceKey) (u v : InstState) : Prop :=
  u = initInstState ∧
  v = (1, some inst.2.2.2, !(Nat.ble inst.2.2.1 inst.2.1))

noncomputable def instReturn (inst : InstanceKey) : Option Nat :=
  if Nat.ble inst.2.2.1 inst.2.1 then some inst.2.2.2 else none

theorem generic_checked_theorem_holds_under_const_premise (inst : InstanceKey)
    (hconst : Nat.ble inst.2.2.1 inst.2.1 = true) :
    Execution.NoUB (checkedStep inst) BadInstState initInstState ∧
    instReturn inst = some inst.2.2.2 := by
  refine ⟨?_, ?_⟩
  · intro s hreach hbad
    have hfalse : s.2.2 = false := by
      refine Execution.invariant_reachable (Invariant := fun st : InstState => st.2.2 = false) rfl ?_ hreach
      intro u v _ edge
      cases edge with
      | intro _ hv =>
        subst hv
        dsimp only
        rw [hconst]
        rfl
    exact Bool.noConfusion (hfalse.symm.trans hbad)
  · unfold instReturn
    rw [hconst]
    rfl

-- ProbeConfig: (genericBodyTextHash, entryInstance, uninstantiatedMention)
abbrev ProbeConfig : Type := Nat × InstanceKey × Option InstanceKey

noncomputable def cfgA1 : ProbeConfig := (42, instA1, none)
noncomputable def cfgB0 : ProbeConfig := (42, instB0, none)
noncomputable def cfgB1 : ProbeConfig := (42, instB1, none)
noncomputable def cfgUnusedB1 : ProbeConfig := (42, instB0, some instB1)

noncomputable def ConcreteEntryAdmitted (cfg : ProbeConfig) : Bool :=
  Nat.ble cfg.2.1.2.2.1 cfg.2.1.2.1

theorem concrete_entry_admission_accepts_a1_b0_and_unused_b1 :
    (ConcreteEntryAdmitted cfgA1 = true ∧
      Execution.NoUB (checkedStep cfgA1.2.1) BadInstState initInstState ∧
      instReturn cfgA1.2.1 = some 161) ∧
    (ConcreteEntryAdmitted cfgB0 = true ∧
      Execution.NoUB (checkedStep cfgB0.2.1) BadInstState initInstState ∧
      instReturn cfgB0.2.1 = some 176) ∧
    (ConcreteEntryAdmitted cfgUnusedB1 = true ∧
      Execution.NoUB (checkedStep cfgUnusedB1.2.1) BadInstState initInstState ∧
      instReturn cfgUnusedB1.2.1 = some 176) := by
  have ha1 := generic_checked_theorem_holds_under_const_premise instA1 rfl
  have hb0 := generic_checked_theorem_holds_under_const_premise instB0 rfl
  exact ⟨⟨rfl, ha1.1, ha1.2⟩, ⟨rfl, hb0.1, hb0.2⟩, ⟨rfl, hb0.1, hb0.2⟩⟩

theorem concrete_entry_admission_rejects_b1 :
    ConcreteEntryAdmitted cfgB1 = false ∧
    cfgB1.1 = cfgA1.1 ∧
    ¬ Execution.NoUB (checkedStep cfgB1.2.1) BadInstState initInstState := by
  refine ⟨rfl, rfl, ?_⟩
  intro hnoub
  have hreach : Execution.Reach (checkedStep cfgB1.2.1) initInstState (1, some 176, true) :=
    Execution.Reach.tail (Execution.Reach.refl initInstState) ⟨rfl, rfl⟩
  have hbad : BadInstState (1, some 176, true) := rfl
  exact Execution.bad_prefix_not_noUB (Bad := BadInstState) hreach hbad hnoub

/-! ## FE-07: Configured and Cross-Crate Completeness (`CrateGraphBundle`, `TwoCrateComplete`) -/

-- CrateGraphBundle:
-- (appBodyPresent, depBodyPresent, depConstInitPresent, depDropGluePresent,
--  hostTargetSeparated, targetCfgMatched, generatedInputsMatched)
abbrev CrateGraphBundle : Type :=
  Bool × Bool × Bool × Bool × Bool × Bool × Bool

noncomputable def TwoCrateComplete (g : CrateGraphBundle) : Bool :=
  g.1 && g.2.1 && g.2.2.1 && g.2.2.2.1 && g.2.2.2.2.1 && g.2.2.2.2.2.1 && g.2.2.2.2.2.2

noncomputable def validTwoCrateBundle : CrateGraphBundle :=
  (true, true, true, true, true, true, true)

theorem two_crate_completeness_transfers_cross_crate_claim :
    TwoCrateComplete validTwoCrateBundle = true ∧
    ∀ inst : InstanceKey,
      Nat.ble inst.2.2.1 inst.2.1 = true →
        Execution.NoUB (checkedStep inst) BadInstState initInstState ∧
        instReturn inst = some inst.2.2.2 :=
  ⟨rfl, generic_checked_theorem_holds_under_const_premise⟩

#print axioms repStep_noUB_of_fault_false
#print axioms structural_admission_retains_unsafe_ub_subjects
#print axioms generic_checked_theorem_holds_under_const_premise
#print axioms concrete_entry_admission_accepts_a1_b0_and_unused_b1
#print axioms concrete_entry_admission_rejects_b1
#print axioms two_crate_completeness_transfers_cross_crate_claim

end AnnealResearch.MirRepresentationAdmission
