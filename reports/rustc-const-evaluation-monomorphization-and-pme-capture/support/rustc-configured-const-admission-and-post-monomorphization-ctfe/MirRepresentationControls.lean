import AnnealResearch.MirRepresentationAdmission
set_option Elab.async false

/-!
# Negative Controls for MIR Representation, Instance Admission, and Cross-Crate Closure (FE-05..07)

This module establishes the six negative controls for `FE-05`, `FE-06`, and `FE-07`:
1. `same_name_different_owner_collision_control`: same symbol name (`symbolId = 7`) with distinct
   `OwnerDefId`s (`101` safe vs `202` UB-faulting).
2. `vacuous_admission_excluding_unsafe_ub_control`: an over-strong admission gate that excludes
   `triggersRuntimeUB = true` makes `NoUB` hold vacuously by dropping `unsafeUbBody` from the
   subject domain rather than diagnosing its UB.
3. `generic_mir_text_only_gate_accepts_failing_b1_control`: inspecting only the uninstantiated
   generic `fn checked()` text (`genericBodyTextHash = 42`) cannot distinguish `cfgA1` from
   `cfgB1` and falsely admits `cfgB1`.
4. `naive_all_mentions_gate_falsely_rejects_unused_b1_control`: requiring `N <= T::LIMIT` on
   unmonomorphized dead mentions (`never_instantiated<U>()`) falsely rejects `cfgUnusedB1`.
5. `rmeta_check_only_missing_dep_body_control`: a `cargo check` `.rmeta` bundle missing dependency
   MIR bodies and const initializers passes an interface-only check while failing
   `TwoCrateComplete`.
6. `host_target_pointer_width_confusion_control`: conflating 64-bit host pointer width (`8`) with
   32-bit target pointer width (`4`) violates `hostTargetSeparated` and fails `TwoCrateComplete`.
-/

namespace AnnealResearch.MirRepresentationControls

open AnnealResearch.MirRepresentationAdmission

/-! ## Control 1: Same Symbol Name with Different `OwnerDefId` (`FE-05`) -/

noncomputable def safeOwnerBody : MirBodyRep :=
  (101, 4, 2, 0, 4, false, false)

noncomputable def ubOwnerBody : MirBodyRep :=
  (202, 4, 2, 0, 4, true, true)

theorem same_name_different_owner_collision_control :
    safeOwnerBody.1 ≠ ubOwnerBody.1 ∧
    Execution.NoUB (repStep safeOwnerBody) BadRepState initRepState ∧
    ¬ Execution.NoUB (repStep ubOwnerBody) BadRepState initRepState := by
  refine ⟨?_, repStep_noUB_of_fault_false safeOwnerBody rfl, ?_⟩
  · intro h
    change 101 = 202 at h
    nomatch h
  · intro hnoub
    have hreach : Execution.Reach (repStep ubOwnerBody) initRepState (1, true) :=
      Execution.Reach.tail (Execution.Reach.refl initRepState) ⟨rfl, rfl⟩
    have hbad : BadRepState (1, true) := rfl
    exact Execution.bad_prefix_not_noUB (Bad := BadRepState) hreach hbad hnoub

/-! ## Control 2: Vacuous Admission Excluding Unsafe UB Subjects (`FE-05`) -/

noncomputable def VacuousSafeOnlyAdmission (b : MirBodyRep) : Bool :=
  StructurallyWellFormed b && !b.2.2.2.2.2.2

theorem vacuous_admission_excluding_unsafe_ub_control :
    StructurallyWellFormed unsafeUbBody = true ∧
    VacuousSafeOnlyAdmission unsafeUbBody = false ∧
    ∀ b : MirBodyRep,
      VacuousSafeOnlyAdmission b = true →
        Execution.NoUB (repStep b) BadRepState initRepState := by
  refine ⟨rfl, rfl, ?_⟩
  intro b hvac
  unfold VacuousSafeOnlyAdmission at hvac
  cases htrig : b.2.2.2.2.2.2 with
  | false =>
    exact repStep_noUB_of_fault_false b htrig
  | true =>
    rw [htrig] at hvac
    cases hswf : StructurallyWellFormed b with
    | false =>
      rw [hswf] at hvac
      change false = true at hvac
      nomatch hvac
    | true =>
      rw [hswf] at hvac
      change false = true at hvac
      nomatch hvac

/-! ## Control 3: Generic MIR Text-Only Gate Falsely Admits `b1` (`FE-06`) -/

noncomputable def GenericTextOnlyGate (cfg : ProbeConfig) : Bool :=
  Nat.beq cfg.1 42

theorem generic_mir_text_only_gate_accepts_failing_b1_control :
    GenericTextOnlyGate cfgA1 = true ∧
    GenericTextOnlyGate cfgB1 = true ∧
    ConcreteEntryAdmitted cfgB1 = false ∧
    ¬ Execution.NoUB (checkedStep cfgB1.2.1) BadInstState initInstState :=
  ⟨rfl, rfl, rfl, concrete_entry_admission_rejects_b1.2.2⟩

/-! ## Control 4: Naive Whole-File Mention Gate Falsely Rejects `unused_b1` (`FE-06`) -/

noncomputable def NaiveAllMentionsGate (cfg : ProbeConfig) : Bool :=
  ConcreteEntryAdmitted cfg &&
    match cfg.2.2 with
    | none => true
    | some u => Nat.ble u.2.2.1 u.2.1

theorem naive_all_mentions_gate_falsely_rejects_unused_b1_control :
    NaiveAllMentionsGate cfgUnusedB1 = false ∧
    ConcreteEntryAdmitted cfgUnusedB1 = true ∧
    Execution.NoUB (checkedStep cfgUnusedB1.2.1) BadInstState initInstState :=
  ⟨rfl, rfl, concrete_entry_admission_accepts_a1_b0_and_unused_b1.2.2.2.1⟩

/-! ## Control 5: `.rmeta` Metadata-Only Bundle Missing Dependency Bodies (`FE-07`) -/

noncomputable def rmetaOnlyBundle : CrateGraphBundle :=
  (true, false, false, true, true, true, true)

noncomputable def InterfaceOnlyCheck (g : CrateGraphBundle) : Bool :=
  g.1 && g.2.2.2.2.2.1

theorem rmeta_check_only_missing_dep_body_control :
    InterfaceOnlyCheck rmetaOnlyBundle = true ∧
    TwoCrateComplete rmetaOnlyBundle = false :=
  ⟨rfl, rfl⟩

/-! ## Control 6: Host vs Target Pointer-Width Confusion (`FE-07`) -/

noncomputable def hostPtrWidth : Nat := 8
noncomputable def targetPtrWidth : Nat := 4

noncomputable def hostConfusedBundle : CrateGraphBundle :=
  (true, true, true, true, false, true, true)

theorem host_target_pointer_width_confusion_control :
    hostPtrWidth ≠ targetPtrWidth ∧
    TwoCrateComplete hostConfusedBundle = false ∧
    TwoCrateComplete validTwoCrateBundle = true := by
  refine ⟨?_, rfl, rfl⟩
  intro h
  change 8 = 4 at h
  nomatch h

#print axioms same_name_different_owner_collision_control
#print axioms vacuous_admission_excluding_unsafe_ub_control
#print axioms generic_mir_text_only_gate_accepts_failing_b1_control
#print axioms naive_all_mentions_gate_falsely_rejects_unused_b1_control
#print axioms rmeta_check_only_missing_dep_body_control
#print axioms host_target_pointer_width_confusion_control

end AnnealResearch.MirRepresentationControls
