import Lean
import PromoteTempsInfallibleZstMutAndConstMutationSoundness

/-!
# Kernel and Axiom Audit of `PromoteTempsInfallibleZstMutAndConstMutationSoundness`

Compiled against `PromoteTempsInfallibleZstMutAndConstMutationSoundness.olean` by
`support/check_lean.py`. Verifies that every constant in the module:
- is not an `axiom`, `opaque` constant, `quot` constant, or non-`safe` definition;
- does not contain `_unsafe_rec` in its name;
- depends on no axioms outside `[propext, Quot.sound]`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_promote_temps" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `PromoteTempsInfallibleZstMutAndConstMutationSoundness
    | throwError "module PromoteTempsInfallibleZstMutAndConstMutationSoundness is not imported"
  let mut theorems := 0
  let mut definitions := 0
  let mut inductives := 0
  let mut constructors := 0
  let mut recursors := 0
  let mut total := 0
  let mut violations : Array String := #[]
  let mut axiomsSeen : Array Name := #[]
  let mut axiomFree := 0
  for (n, ci) in env.constants.map₁.toList do
    if env.getModuleIdxFor? n != some modIdx then continue
    total := total + 1
    if (n.toString.splitOn "_unsafe_rec").length > 1 then
      violations := violations.push s!"unsafe_rec helper: {n}"
    match ci with
    | .axiomInfo _ => violations := violations.push s!"axiom: {n}"
    | .opaqueInfo _ => violations := violations.push s!"opaque constant: {n}"
    | .quotInfo _ => violations := violations.push s!"quot constant: {n}"
    | .defnInfo d =>
      definitions := definitions + 1
      if d.safety != .safe then violations := violations.push s!"non-safe definition: {n}"
    | .thmInfo _ =>
      theorems := theorems + 1
      let axs ← collectAxioms n
      if axs.isEmpty then axiomFree := axiomFree + 1
      for a in axs do
        if !axiomsSeen.contains a then axiomsSeen := axiomsSeen.push a
        if !allowedAxioms.contains a then
          violations := violations.push s!"theorem {n} depends on axiom {a}"
    | .inductInfo _ => inductives := inductives + 1
    | .ctorInfo _ => constructors := constructors + 1
    | .recInfo _ => recursors := recursors + 1
  let axiomNames := axiomsSeen.toList.map (fun a => s!"\"{a}\"")
  let json := "{" ++ s!"\"constants\": {total}, \"theorems\": {theorems}, " ++
    s!"\"theorems_without_axioms\": {axiomFree}, \"definitions\": {definitions}, " ++
    s!"\"inductive_types\": {inductives}, \"constructors\": {constructors}, " ++
    s!"\"recursors\": {recursors}, \"axioms_used\": [{", ".intercalate axiomNames}], " ++
    s!"\"violations\": {violations.size}" ++ "}"
  logInfo m!"AUDIT {json}"
  unless violations.isEmpty do
    throwError "audit failed:\n{"\n".intercalate violations.toList}"

#audit_promote_temps

#print axioms PromoteTempsSoundness.collector_ignores_non_temps
#print axioms PromoteTempsSoundness.collector_drop_and_storage_noop
#print axioms PromoteTempsSoundness.collector_unpromotable_absorbing
#print axioms PromoteTempsSoundness.collector_double_init_unpromotable
#print axioms PromoteTempsSoundness.collector_mutBorrow_increments_uses
#print axioms PromoteTempsSoundness.collector_defined_after_single_init
#print axioms PromoteTempsSoundness.qualifHasMutInterior_optionNone_unsafeCellZst_false
#print axioms PromoteTempsSoundness.qualifHasMutInterior_unsafeCellZst_true
#print axioms PromoteTempsSoundness.validator_implies_ctfe_infallible
#print axioms PromoteTempsSoundness.promoteTemps_runtime_and_drop_trace_preserved
#print axioms PromoteTempsSoundness.promoteTemps_infallible_preserves_semantics_iff
#print axioms PromoteTempsSoundness.ce_div_zero_dead_branch_breaks_ctfe
#print axioms PromoteTempsSoundness.ce_signed_min_div_neg1_breaks_ctfe
#print axioms PromoteTempsSoundness.ce_copy_index_oob_rejected_vs_place_index_base_promoted
#print axioms PromoteTempsSoundness.ce_needsDrop_promotion_drops_side_effect
#print axioms PromoteTempsSoundness.ce_addWithOverflow_dead_branch_keepOriginal_sound
#print axioms PromoteTempsSoundness.ce_non_zst_move_deinit_preserved
#print axioms PromoteTempsSoundness.zst_mut_borrow_promoted_rodata_sound
#print axioms PromoteTempsSoundness.dual_protected_zst_mut_borrows_rodata_sound
#print axioms PromoteTempsSoundness.nonzst_mut_borrow_rodata_ub_counterexample
#print axioms PromoteTempsSoundness.zst_mut_promoted_write_oob_ub
#print axioms PromoteTempsSoundness.validateRef_mut_syntactic_conservatism_and_unsafecell_zst_witness
#print axioms PromoteTempsSoundness.constMutation_unobservable_iff_no_needsDrop
#print axioms PromoteTempsSoundness.checkConstItemMutation_visitRvalue_false_positive_witness
#print axioms PromoteTempsSoundness.observed_drops_sum_eq_75
#print axioms PromoteTempsSoundness.checkConstItemMutation_nestedDrop_198_vs_1102_witness
#print axioms PromoteTempsSoundness.lintRepaired_exact_soundness_and_completeness
