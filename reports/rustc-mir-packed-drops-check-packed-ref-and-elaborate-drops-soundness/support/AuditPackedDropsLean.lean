import Lean
import PackedDropsCheckPackedRefAndElaborateDropsSoundness

/-!
# Kernel Environment Audit for `PackedDropsCheckPackedRefAndElaborateDropsSoundness`

Walks every constant declared by `PackedDropsCheckPackedRefAndElaborateDropsSoundness`
in the Lean 4 kernel environment and verifies:
- 0 `axiom`, `opaque`, or `quot` declarations;
- 0 non-`.safe` definitions (rejects non-terminating / compiler-internal helpers);
- 0 `_unsafe_rec` constants;
- Every theorem depends exclusively on axioms within `[propext, Quot.sound]`
  (rejecting `sorryAx`, `Classical.choice`, and `Lean.ofReduceBool`).
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_packed_drops" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `PackedDropsCheckPackedRefAndElaborateDropsSoundness
    | throwError "module PackedDropsCheckPackedRefAndElaborateDropsSoundness is not imported"
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

#audit_packed_drops

#print axioms PackedDropsSoundness.checkPackedRef_implies_all_borrows_aligned
#print axioms PackedDropsSoundness.addMovesForPackedDrops_eliminates_unaligned_drop_self_ub
#print axioms PackedDropsSoundness.drop_in_place_ub_checks_gap_counterexample
#print axioms PackedDropsSoundness.elaborateDrops_drop_each_live_leaf_once
#print axioms PackedDropsSoundness.removeUninitDrops_preserves_semantics
#print axioms PackedDropsSoundness.full_packed_drop_pipeline_soundness
#print axioms PackedDropsSoundness.pipeline_order_counterexample
