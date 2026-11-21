import Lean
import CleanupPostBorrowckAndAbortCalls

/-!
# Audit of `CleanupPostBorrowckAndAbortCalls`

Run after compiling `CleanupPostBorrowckAndAbortCalls.lean` to an `.olean` (see `check_lean.py`).
Inspects every constant declared in `CleanupPostBorrowckAndAbortCalls` and fails if any of them:

* is an axiom, `opaque` constant, `quot` constant, or definition whose safety is not `safe`;
* has a name containing `_unsafe_rec`;
* is a theorem whose proof depends on any axiom other than `propext` and `Quot.sound`
  (rejecting `sorryAx`, `Classical.choice`, and `Lean.ofReduceBool` / `Lean.trustCompiler`).

On success it prints one JSON summary line `AUDIT {...}` and prints kernel axioms for every
public theorem in `MirCleanupLowering`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Quot.sound]

elab "#audit_cleanup_post_borrowck" : command => do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `CleanupPostBorrowckAndAbortCalls
    | throwError "module CleanupPostBorrowckAndAbortCalls is not imported"
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

#audit_cleanup_post_borrowck

#print axioms MirCleanupLowering.cleanupPostBorrowck_syntax_valid
#print axioms MirCleanupLowering.cleanupPostBorrowck_unguarded_exact_equiv
#print axioms MirCleanupLowering.cleanupPostBorrowck_certified_equiv
#print axioms MirCleanupLowering.cleanupPostBorrowck_certified_iff
#print axioms MirCleanupLowering.placeMention_ignores_invalid_pointee
#print axioms MirCleanupLowering.assignCopy_rejects_invalid_pointee
#print axioms MirCleanupLowering.placeMention_checks_pointer_local
#print axioms MirCleanupLowering.execStmtList_removePlaceMention_refines
#print axioms MirCleanupLowering.abortRewriteOnly_nonpanicking_equiv
#print axioms MirCleanupLowering.abortRewriteOnly_exact_analysis_equiv
#print axioms MirCleanupLowering.compactReachableBody_bisim
#print axioms MirCleanupLowering.unreachable_blocks_dropped_by_compaction
#print axioms MirCleanupLowering.abortUnwindingCalls_exact_analysis_equiv
#print axioms MirCleanupLowering.abortUnwindingCalls_nonpanicking_equiv
#print axioms MirCleanupLowering.full_analysis_to_runtime_lowering_sound
#print axioms MirCleanupLowering.ce1a_uncertified_fakeread_uninit_scrutinee
#print axioms MirCleanupLowering.ce1b_uncertified_fakeread_invalid_discriminant
#print axioms MirCleanupLowering.ce1c_guard_mutation_bypasses_erased_fake_borrow
#print axioms MirCleanupLowering.ce2_mutant_cleanup_to_continue_causes_abi_ub
#print axioms MirCleanupLowering.ce3_nounwind_violation_hits_unreachable_ub
