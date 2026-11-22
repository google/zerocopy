import Lean
import ColdBlocksAndNoUnwindSoundness

/-!
# Kernel and Axiom Audit of `ColdBlocksAndNoUnwindSoundness`

Compiled against `ColdBlocksAndNoUnwindSoundness.olean` by `support/check_lean.py`.
Checks every constant declared in `ColdBlocksAndNoUnwindSoundness` and fails if any:
- is an `axiom`, `opaque` constant, `quot` constant, or non-`safe` definition;
- contains `_unsafe_rec` in its name;
- is a theorem depending on any axiom outside `[propext, Quot.sound]`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_cold_blocks_and_nounwind" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `ColdBlocksAndNoUnwindSoundness
    | throwError "module ColdBlocksAndNoUnwindSoundness is not imported"
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

#audit_cold_blocks_and_nounwind

#print axioms ColdBlocksAndNoUnwind.findColdBlocksPass_sound
#print axioms ColdBlocksAndNoUnwind.findColdBlocks_sound_and_dag_complete
#print axioms ColdBlocksAndNoUnwind.coldPath_erasure_preserves_behavior
#print axioms ColdBlocksAndNoUnwind.optimize_attr_s_vs_z_default
#print axioms ColdBlocksAndNoUnwind.optimize_attr_size_speed_none_overrides
#print axioms ColdBlocksAndNoUnwind.fnCanUnwind_precedence_characterization
#print axioms ColdBlocksAndNoUnwind.abortUnwindingCalls_sound_for_call
#print axioms ColdBlocksAndNoUnwind.fnCanUnwind_nounwind_soundness
#print axioms ColdBlocksAndNoUnwind.ce1_single_pass_postorder_misses_cyclic_cold_loop_header
#print axioms ColdBlocksAndNoUnwind.ce2_marking_foreign_c_unwind_nounwind_under_panic_abort_skips_terminate_pad
#print axioms ColdBlocksAndNoUnwind.ce3_conflating_public_drop_in_place_with_lang_drop_glue_under_panic_in_drop_abort
