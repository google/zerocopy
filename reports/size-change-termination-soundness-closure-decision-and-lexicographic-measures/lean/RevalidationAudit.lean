/-
Revalidation audit for the result cards of this package. Not part of the `Toy` library target.
Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints `#print axioms` for every declaration named in a result card's structured Lean fields
(`lean`, `nonvacuity_witness_lean`, `positive_control_lean`, hypothesis `counterexample`), then one line
`REVALIDATION_AUDIT_JSON {...}` containing, for every library declaration, the axioms it depends
on, and, for every card-referenced declaration, `repr` of its type and its definition closure:
the sorted lines `name : repr type := repr value` (value omitted for theorems) of every library
constant reachable from the type through types and definition bodies. Hashing these with SHA-256
reproduces `audit/statements.json`.
-/
import Lean
import Toy

open Lean Elab Command

#print axioms Toy.SCT.ackProg_unbounded_finite_runs
#print axioms Toy.SCT.alt_generatorCriterion_counterexample
#print axioms Toy.SCT.checkSCT_eq_true_of_closureCriterion
#print axioms Toy.SCT.checker_correct_nonvacuous
#print axioms Toy.SCT.checker_premise_contrast
#print axioms Toy.SCT.closureCriterion_of_checkSCT_eq_true
#print axioms Toy.SCT.closureCriterion_of_lexProjDecreases
#print axioms Toy.SCT.closureCriterion_of_sizeChangeTerminating
#print axioms Toy.SCT.closure_criterion_exact_nonvacuous
#print axioms Toy.SCT.closure_criterion_sound_model_nonvacuous
#print axioms Toy.SCT.closure_criterion_sound_nonvacuous
#print axioms Toy.SCT.closure_iff_sct_nonvacuous
#print axioms Toy.SCT.consistent_nat_run_of_not_closureCriterion
#print axioms Toy.SCT.countUp_size_norm_positive_control
#print axioms Toy.SCT.countUp_terminates_and_no_sound_prog_passes
#print axioms Toy.SCT.decLoop_closureCriterion_consistent_int_run
#print axioms Toy.SCT.decLoop_int_model_counterexample
#print axioms Toy.SCT.forget_composition_rejects_mutProg
#print axioms Toy.SCT.idLoop_decLoop_contrast
#print axioms Toy.SCT.idLoop_no_lexProjDecreases_not_criterion
#print axioms Toy.SCT.idLoop_runStep_counterexample
#print axioms Toy.SCT.idempotence_needed_for_converse
#print axioms Toy.SCT.infinite_functions_counterexample
#print axioms Toy.SCT.infinite_params_converse_exactness_counterexample
#print axioms Toy.SCT.infinite_params_soundness_counterexample
#print axioms Toy.SCT.infinite_ramsey_nonvacuous
#print axioms Toy.SCT.infinite_ramsey_pairs_of_finite_colors
#print axioms Toy.SCT.lex_implies_closure_criterion_nonvacuous
#print axioms Toy.SCT.loop_guard_needed_for_converse
#print axioms Toy.SCT.misfit_graphs_counterexample
#print axioms Toy.SCT.no_consistent_nat_run_of_closureCriterion
#print axioms Toy.SCT.no_consistent_nat_run_of_sizeChangeTerminating
#print axioms Toy.SCT.no_run_length_bound_positive_control
#print axioms Toy.SCT.overStrict_composition_counterexample
#print axioms Toy.SCT.ramsey_infinite_colors_counterexample
#print axioms Toy.SCT.sct_incomplete_positive_control
#print axioms Toy.SCT.sct_not_lex_positive_control
#print axioms Toy.SCT.sct_sound_nat_nonvacuous
#print axioms Toy.SCT.sizeChangeTerminating_of_closureCriterion
#print axioms Toy.SCT.stall_weakSelfArcCriterion_counterexample
#print axioms Toy.SCT.swapDec_closureCriterion_and_no_lexProjDecreases
#print axioms Toy.SCT.terminates_of_stepRespects_of_closureCriterion

private def auditRoots : List Name := [`Toy]
private def auditNames : List Name := [`Toy.SCT.ackProg_unbounded_finite_runs,
  `Toy.SCT.alt_generatorCriterion_counterexample,
  `Toy.SCT.checkSCT_eq_true_of_closureCriterion,
  `Toy.SCT.checker_correct_nonvacuous,
  `Toy.SCT.checker_premise_contrast,
  `Toy.SCT.closureCriterion_of_checkSCT_eq_true,
  `Toy.SCT.closureCriterion_of_lexProjDecreases,
  `Toy.SCT.closureCriterion_of_sizeChangeTerminating,
  `Toy.SCT.closure_criterion_exact_nonvacuous,
  `Toy.SCT.closure_criterion_sound_model_nonvacuous,
  `Toy.SCT.closure_criterion_sound_nonvacuous,
  `Toy.SCT.closure_iff_sct_nonvacuous,
  `Toy.SCT.consistent_nat_run_of_not_closureCriterion,
  `Toy.SCT.countUp_size_norm_positive_control,
  `Toy.SCT.countUp_terminates_and_no_sound_prog_passes,
  `Toy.SCT.decLoop_closureCriterion_consistent_int_run,
  `Toy.SCT.decLoop_int_model_counterexample,
  `Toy.SCT.forget_composition_rejects_mutProg,
  `Toy.SCT.idLoop_decLoop_contrast,
  `Toy.SCT.idLoop_no_lexProjDecreases_not_criterion,
  `Toy.SCT.idLoop_runStep_counterexample,
  `Toy.SCT.idempotence_needed_for_converse,
  `Toy.SCT.infinite_functions_counterexample,
  `Toy.SCT.infinite_params_converse_exactness_counterexample,
  `Toy.SCT.infinite_params_soundness_counterexample,
  `Toy.SCT.infinite_ramsey_nonvacuous,
  `Toy.SCT.infinite_ramsey_pairs_of_finite_colors,
  `Toy.SCT.lex_implies_closure_criterion_nonvacuous,
  `Toy.SCT.loop_guard_needed_for_converse,
  `Toy.SCT.misfit_graphs_counterexample,
  `Toy.SCT.no_consistent_nat_run_of_closureCriterion,
  `Toy.SCT.no_consistent_nat_run_of_sizeChangeTerminating,
  `Toy.SCT.no_run_length_bound_positive_control,
  `Toy.SCT.overStrict_composition_counterexample,
  `Toy.SCT.ramsey_infinite_colors_counterexample,
  `Toy.SCT.sct_incomplete_positive_control,
  `Toy.SCT.sct_not_lex_positive_control,
  `Toy.SCT.sct_sound_nat_nonvacuous,
  `Toy.SCT.sizeChangeTerminating_of_closureCriterion,
  `Toy.SCT.stall_weakSelfArcCriterion_counterexample,
  `Toy.SCT.swapDec_closureCriterion_and_no_lexProjDecreases,
  `Toy.SCT.terminates_of_stepRespects_of_closureCriterion]

private def inLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => auditRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def defClosure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLib env n then defClosure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => defClosure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      defClosure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inLib env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in auditNames do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := defClosure env (ci.type.getUsedConstants.toList) {}
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
  IO.println ("REVALIDATION_AUDIT_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
