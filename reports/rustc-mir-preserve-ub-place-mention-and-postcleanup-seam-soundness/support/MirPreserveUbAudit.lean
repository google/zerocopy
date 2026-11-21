import Lean
import MirPreserveUbAndPlaceMentionSeam

/-!
# Kernel and Axiom Audit of `MirPreserveUbAndPlaceMentionSeam`

Compiled against `MirPreserveUbAndPlaceMentionSeam.olean` by `support/check_lean.py`.
Checks every constant declared in `MirPreserveUbAndPlaceMentionSeam` and fails if any:
- is an `axiom`, `opaque` constant, `quot` constant, or non-`safe` definition;
- contains `_unsafe_rec` in its name;
- is a theorem depending on any axiom outside `[propext, Quot.sound]`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_mir_preserve_ub" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `MirPreserveUbAndPlaceMentionSeam
    | throwError "module MirPreserveUbAndPlaceMentionSeam is not imported"
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

#audit_mir_preserve_ub

#print axioms MirPreserveUbSeam.evalPlaceMPlace_raw_deref_zero_offset_ok
#print axioms MirPreserveUbSeam.evalPlaceMPlace_null_nonzero_field_ub
#print axioms MirPreserveUbSeam.evalPlaceMPlace_safeRef_null_ub
#print axioms MirPreserveUbSeam.evalBody_runtimePostCleanup_preserveUb_true_exact_noNops
#print axioms MirPreserveUbSeam.evalBody_runtimePostCleanup_preserveUb_true_complete
#print axioms MirPreserveUbSeam.evalPlaceMPlace_ok_of_safeToErasePlaceMention
#print axioms MirPreserveUbSeam.evalBody_removePlaceMention_exact_of_localOnly
#print axioms MirPreserveUbSeam.evalBody_postCleanup_false_exact_of_traceCertified
#print axioms MirPreserveUbSeam.Examples.ce1_null_nonzero_field_place_mention_ub_erased_in_default_postcleanup
#print axioms MirPreserveUbSeam.Examples.ce1b_null_zero_offset_field0_defined_both_modes
#print axioms MirPreserveUbSeam.Examples.ce2_uninit_local_equal_target_switchint_ub_erased_in_default_postcleanup
#print axioms MirPreserveUbSeam.Examples.ce3_naive_full_read_semantics_for_place_mention_falsely_rejects_rfc2582_raw_deref
#print axioms MirPreserveUbSeam.Examples.ce4_derefer_chained_deref_inner_uninit_survives_while_outer_field_ub_erased
#print axioms MirPreserveUbSeam.Examples.runtimePostCleanup_preserveUb_false_unsound
