import Lean
import ToySim

/-!
Statement and closure audit for every Lean name recorded in `../audit/statements.json`
(not part of the library target).  Run from this directory after `lake build`:
`lake env lean StatementAudit.lean`.  It prints one line `REVALIDATE_JSON {...}` with,
per declaration of the library, its axioms (via `collectAxioms`), and, per recorded
name, the `repr` of its type and the sorted `repr` texts of its definition closure.
-/
open Lean Elab Command

private def roots : List Name := [`ToySim]
private def wanted : List Name := [`Toy.Sim.Cex.cex_bsim_without_final_clause, `Toy.Sim.Cex.cex_bsim_without_initExists, `Toy.Sim.Cex.cex_bsim_without_initMatch, `Toy.Sim.Cex.cex_bsim_without_progress, `Toy.Sim.Cex.cex_bsim_without_step_diagram, `Toy.Sim.Cex.cex_bsim_without_wf, `Toy.Sim.Cex.cex_compOrd_wf_needs_both, `Toy.Sim.Cex.cex_comp_naive_lex_order_fails, `Toy.Sim.Cex.cex_comp_without_first_final, `Toy.Sim.Cex.cex_comp_without_first_init, `Toy.Sim.Cex.cex_comp_without_first_step_diagram, `Toy.Sim.Cex.cex_comp_without_first_wf, `Toy.Sim.Cex.cex_comp_without_second_final, `Toy.Sim.Cex.cex_comp_without_second_init, `Toy.Sim.Cex.cex_comp_without_second_step_diagram, `Toy.Sim.Cex.cex_comp_without_second_wf, `Toy.Sim.Cex.cex_flip_nonreceptive_source, `Toy.Sim.Cex.cex_flip_target_event_labels_mismatch, `Toy.Sim.Cex.cex_flip_target_final_state_steps, `Toy.Sim.Cex.cex_flip_target_labels_mismatch, `Toy.Sim.Cex.cex_flip_target_not_functional, `Toy.Sim.Cex.cex_flip_target_two_initial_states, `Toy.Sim.Cex.cex_flip_target_two_results, `Toy.Sim.Cex.cex_flip_without_final_clause, `Toy.Sim.Cex.cex_flip_without_init_clause, `Toy.Sim.Cex.cex_flip_without_step_diagram, `Toy.Sim.Cex.cex_flip_without_wf, `Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved, `Toy.Sim.Cex.cex_fsim_without_final_clause, `Toy.Sim.Cex.cex_fsim_without_init_clause, `Toy.Sim.Cex.cex_fsim_without_init_clause_diverges, `Toy.Sim.Cex.cex_fsim_without_step_diagram, `Toy.Sim.Cex.cex_fsim_without_step_diagram_diverges, `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved, `Toy.Sim.Cex.cex_improves_antisymm_needs_both, `Toy.Sim.Cex.cex_improves_not_symmetric, `Toy.Sim.Cex.cex_improves_trans_needs_both, `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong, `Toy.Sim.Cex.cex_inclusion_without_refinement, `Toy.Sim.Cex.cex_inclusion_without_target_behavior, `Toy.Sim.Cex.cex_partial_run_from_non_initial_state, `Toy.Sim.Cex.cex_partial_run_without_source_run, `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch, `Toy.Sim.Cex.cex_pipeline_last_final_state_steps, `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch, `Toy.Sim.Cex.cex_pipeline_last_not_functional, `Toy.Sim.Cex.cex_pipeline_last_two_initial_states, `Toy.Sim.Cex.cex_pipeline_last_two_results, `Toy.Sim.Cex.cex_pipeline_nonreceptive_first, `Toy.Sim.Cex.cex_pipeline_preserves_without_chain, `Toy.Sim.Cex.cex_pipeline_without_chain, `Toy.Sim.Cex.cex_preservation_without_source_behavior, `Toy.Sim.Cex.cex_refinedBy_not_symmetric, `Toy.Sim.Cex.cex_refinedBy_trans_needs_both, `Toy.Sim.Examples.fsimChain_neg, `Toy.Sim.Examples.fsimChain_pos, `Toy.Sim.Examples.isForwardSim_neg, `Toy.Sim.Examples.isForwardSim_pos, `Toy.Sim.Examples.nonvacuous_backwardSim, `Toy.Sim.Examples.nonvacuous_comp, `Toy.Sim.Examples.nonvacuous_comp_transGen, `Toy.Sim.Examples.nonvacuous_deterministic_target, `Toy.Sim.Examples.nonvacuous_flip, `Toy.Sim.Examples.nonvacuous_flip_with_conclusion, `Toy.Sim.Examples.nonvacuous_isForwardSim_preserves, `Toy.Sim.Examples.nonvacuous_partial_run_simulated, `Toy.Sim.Examples.nonvacuous_pipeline, `Toy.Sim.Examples.nonvacuous_pipeline_behaviors_iff, `Toy.Sim.Examples.nonvacuous_pipeline_preserves, `Toy.Sim.Examples.nonvacuous_preorder, `Toy.Sim.Examples.nonvacuous_preserve_diverges, `Toy.Sim.Examples.nonvacuous_preserve_terminates, `Toy.Sim.Examples.nonvacuous_refinement_inclusion, `Toy.Sim.Examples.positive_control_diverges, `Toy.Sim.Examples.positive_control_flip, `Toy.Sim.Improves.antisymm, `Toy.Sim.Improves.refl, `Toy.Sim.Improves.trans, `Toy.Sim.RefinedBy.refl, `Toy.Sim.RefinedBy.trans, `Toy.Sim.Unfolded.backward_sim_gives_refinement, `Toy.Sim.Unfolded.flip_forward_to_backward, `Toy.Sim.Unfolded.partial_run_simulated, `Toy.Sim.Unfolded.pipeline_end_to_end_refinement, `Toy.Sim.Unfolded.silent_divergence_preserved, `Toy.Sim.Unfolded.step_diagrams_compose, `Toy.Sim.Unfolded.terminating_behaviours_preserved, `Toy.Sim.backwardSim_gives_refinedBy, `Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset, `Toy.Sim.compOrd_wf, `Toy.Sim.forwardSim_deterministic_target_gives_backwardSim, `Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim, `Toy.Sim.fsimChain_collapse, `Toy.Sim.fsimChain_deterministic_last_gives_refinedBy, `Toy.Sim.fsimChain_of_isForwardSim, `Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors, `Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy, `Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff, `Toy.Sim.fsimFinal_comp, `Toy.Sim.fsimInit_comp, `Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates, `Toy.Sim.fsimInit_fsimStep_partial_run_simulated, `Toy.Sim.fsimStep_comp, `Toy.Sim.improves_goesWrong_nil, `Toy.Sim.isForwardSim_comp, `Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors, `Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset, `Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges]

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
