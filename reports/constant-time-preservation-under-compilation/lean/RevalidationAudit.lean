/-
Stand-alone audit program for this package (not part of the `ToyCT` library target).

Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `AUDIT_JSON {...}` containing
* `decls`: every declaration of the `ToyCT` modules with the axioms it depends on
  (computed by `Lean.collectAxioms`);
* `stmts`: for every Lean name referenced by `results.json`, the `repr` of its type
  (`type_repr`) and its definition closure (`closure`): one line
  `name : repr(type)[ := repr(value)]` for every `ToyCT` constant reachable from the
  statement through types, non-theorem values, and inductive constructors (theorem
  bodies are excluded), sorted.
The statement hash is SHA-256 of `type_repr`; the closure hash is SHA-256 of the
closure lines joined with newlines.
-/
import Lean
import ToyCT
open Lean Elab Command

private def roots : List Name := [`ToyCT]
private def wanted : List Name := [
  `Toy.CT.StepLeakSim.toOutputFree,
  `Toy.CT.branchingSelect_trace_length,
  `Toy.CT.branchless_lowering_preserves_ct,
  `Toy.CT.constantTime_not_refinement_closed,
  `Toy.CT.determinized_target_sim_positive_control,
  `Toy.CT.exists_ld_iff_drop_src_ct_counterexample,
  `Toy.CT.exists_ld_iff_drop_tgt_traceUnique_counterexample,
  `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique,
  `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_false,
  `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_both_sides_true,
  `Toy.CT.exists_leakage_determined_iff_of_ct_traceUnique_nonvacuous,
  `Toy.CT.exists_secretDependentLeakageDetermined_of_traceUnique_haltAgree,
  `Toy.CT.functional_correctness_does_not_preserve_ct,
  `Toy.CT.leakage_determined_comp,
  `Toy.CT.leakage_determined_comp_drop_first_counterexample,
  `Toy.CT.leakage_determined_comp_drop_second_counterexample,
  `Toy.CT.leakage_determined_comp_nonvacuous,
  `Toy.CT.leakage_determined_drop_ct_counterexample,
  `Toy.CT.leakage_determined_preserves_ct,
  `Toy.CT.leakage_determined_preserves_ct_nonvacuous,
  `Toy.CT.leakyLoop_constantTime_despite_diverging_step_leak,
  `Toy.CT.nondeterministic_target_sim_breaks_leakage_determined,
  `Toy.CT.option_stutter_sim_breaks_ct,
  `Toy.CT.outputFree_step_leakage_sim_det_target_implies_leakage_determined,
  `Toy.CT.secretDependentLeakageDetermined_const_sec_iff,
  `Toy.CT.secret_dependent_leak_map_breaks_ct,
  `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined,
  `Toy.CT.step_leakage_sim_det_target_implies_leakage_determined_nonvacuous,
  `Toy.CT.step_sim_drop_sim_counterexample,
  `Toy.CT.step_sim_drop_src_init_counterexample,
  `Toy.CT.step_sim_drop_src_safe_counterexample,
  `Toy.CT.step_sim_drop_tgt_halted_nostep_counterexample,
  `Toy.CT.step_sim_drop_tgt_init_det_counterexample,
  `Toy.CT.step_sim_drop_tgt_step_state_det_counterexample,
  `Toy.CT.terminates_and_constantTime_unconstrained_diverging_branch,
  `Toy.CT.unmeasured_stutter_sim_breaks_leakage_determined,
  `Toy.CT.weakLeakageDetermined_fails_without_traceUnique,
  `Toy.CT.weakLeakageDetermined_preserves_ct_of_traceUnique]

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
  IO.println ("AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
