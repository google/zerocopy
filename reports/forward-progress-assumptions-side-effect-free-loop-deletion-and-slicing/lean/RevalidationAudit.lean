/-
Revalidation audit program. It is not part of the `Toy` library target; run it after
`lake build` from this directory with

    lake env lean RevalidationAudit.lean

It prints one line `REVALIDATE_JSON {...}` containing
* `decls`: every declaration of the `Toy` library with the axioms it depends on
  (computed by `Lean.collectAxioms`), and
* `stmts`: for every Lean name referenced by `results.json`, the `repr` of its type (the
  statement) and its definition closure: one line `name : type [:= value]` for every
  constant of the `Toy` library reachable from the statement, with theorem bodies omitted,
  sorted.
The SHA-256 of the statement text and of the newline-joined closure lines are the values
recorded in `audit/statements.json`.
-/
import Lean
import Toy
open Lean Elab Command

private def roots : List Name := [`Toy]
private def wanted : List Name := [`Toy.Progress.classicSlice_preserves_terminating_traces,
  `Toy.Progress.classicSlice_preserves_terminating_traces_needs_slice,
  `Toy.Progress.classicSlice_preserves_terminating_traces_nonvacuous,
  `Toy.Progress.classicSlice_refines_forwardProgress,
  `Toy.Progress.classicSlice_refines_forwardProgress_needs_slice,
  `Toy.Progress.classicSlice_refines_forwardProgress_nonvacuous,
  `Toy.Progress.classicSlice_silentlyDiverges_or_obsBeh_iff,
  `Toy.Progress.classicSlice_spin_terminates_while_original_diverges,
  `Toy.Progress.deadAfterPrefix_example_not_deadAtEntry,
  `Toy.Progress.deadAfterPrefix_of_deadAtEntry,
  `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff,
  `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_divergenceObservable_iff_terminates,
  `Toy.Progress.deleteEmitFreeLoop_withDeadWrites_refines_forwardProgress,
  `Toy.Progress.deleteLoop_divergenceObservable_iff_needs_deadWrites,
  `Toy.Progress.deleteLoop_divergenceObservable_iff_needs_emitFree,
  `Toy.Progress.deleteLoop_forwardProgress_needs_deadWrites,
  `Toy.Progress.deleteLoop_forwardProgress_needs_emitFree,
  `Toy.Progress.deleteLoop_hypotheses_nonvacuous,
  `Toy.Progress.deleteLoop_iff_terminates_needs_continuation_not_silent,
  `Toy.Progress.deleteLoop_iff_terminates_needs_deadWrites,
  `Toy.Progress.deleteLoop_iff_terminates_needs_emitFree,
  `Toy.Progress.deleteLoop_iff_terminates_nonvacuous,
  `Toy.Progress.deleteLoop_refines_divergenceObservable_without_termination,
  `Toy.Progress.exists_head_silentlyIterates,
  `Toy.Progress.fpBeh_of_mixedBeh,
  `Toy.Progress.inlineDroppingAttr_callerLoop_nonvacuous,
  `Toy.Progress.inlineDroppingAttr_hazard_defined,
  `Toy.Progress.inlineDroppingAttr_refines_linked,
  `Toy.Progress.inlineUnmarked_divergenceObservableCallee_not_refines,
  `Toy.Progress.isClassicSlice_refl,
  `Toy.Progress.isTerminationSensitiveSlice_drops_terminating_loop,
  `Toy.Progress.isTerminationSensitiveSlice_refl,
  `Toy.Progress.loopDeletion_spin_not_refines_divergenceObservable,
  `Toy.Progress.loopDeletion_spin_refines_forwardProgress,
  `Toy.Progress.mixedBeh_flaggedOverUnflagged,
  `Toy.Progress.mixedBeh_markAll_false_iff_obsBeh,
  `Toy.Progress.mixedBeh_markAll_nonvacuous,
  `Toy.Progress.mixedBeh_markAll_restricts,
  `Toy.Progress.mixedBeh_markAll_true_iff_fpBeh,
  `Toy.Progress.noSilentK_admits_emit_then_spin,
  `Toy.Progress.not_isTerminationSensitiveSlice_spin,
  `Toy.Progress.not_progressViolation_flaggedOverUnflagged,
  `Toy.Progress.obsBeh_exists,
  `Toy.Progress.obsBeh_unique,
  `Toy.Progress.progressViolation_unflaggedOverFlagged,
  `Toy.Progress.refines_divergenceObservable_example,
  `Toy.Progress.refines_divergenceObservable_not_imp_refines_mixed,
  `Toy.Progress.refines_forwardProgress_needs_hypothesis,
  `Toy.Progress.refines_forwardProgress_of_refines_divergenceObservable,
  `Toy.Progress.refines_forwardProgress_of_refines_divergenceObservable_strict,
  `Toy.Progress.refines_fpBeh_iff_silentlyDiverges_or_obsBeh_iff,
  `Toy.Progress.refines_obsBeh_iff_equiv,
  `Toy.Progress.silentlyDiverges_of_progressViolation,
  `Toy.Progress.slice_partial_fwd,
  `Toy.Progress.terminationSensitiveSlice_needs_terminationSensitivity,
  `Toy.Progress.terminationSensitiveSlice_preserves_obsBeh,
  `Toy.Progress.terminationSensitiveSlice_preserves_obsBeh_nonvacuous]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in wanted do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := closure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("REVALIDATE_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
