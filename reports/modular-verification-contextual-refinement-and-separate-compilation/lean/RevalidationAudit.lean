/-
Revalidation audit program for this package (not part of the `ToyLink` library target).

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `AUDIT_JSON {...}` containing
* `decls`: every non-internal declaration of the `ToyLink` modules with the axioms it
  depends on (computed by `Lean.collectAxioms`);
* `stmts`: for every name with a recorded hash in `audit/statements.json`, the text whose
  SHA-256 is the statement hash (`type_repr`: the `repr` of the declaration's type) and the
  lines whose newline-joined SHA-256 is the closure hash (`closure`: for each `ToyLink`
  constant reachable from the type through types, definition bodies and constructors, the
  line `name : repr(type)` followed by ` := repr(value)` for non-theorems; sorted).
-/
import Lean
import ToyLink
open Lean Elab Command

private def wanted : List Name := [
  `Toy.Link.Cex.cex_add_fresh_helper_not_ctxRefines,
  `Toy.Link.Cex.cex_ag_partial_without_moduleVerified,
  `Toy.Link.Cex.cex_ag_partial_without_specsImplemented,
  `Toy.Link.Cex.cex_ag_total_unsound_without_measure,
  `Toy.Link.Cex.cex_ag_total_without_moduleVerifiedTotal,
  `Toy.Link.Cex.cex_ag_total_without_specsImplemented,
  `Toy.Link.Cex.cex_ag_total_without_wf,
  `Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement,
  `Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines,
  `Toy.Link.Cex.cex_collapse_without_closed_side,
  `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth,
  `Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence,
  `Toy.Link.Cex.cex_ctxRefines_trans_without_first,
  `Toy.Link.Cex.cex_ctxRefines_trans_without_second,
  `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines,
  `Toy.Link.Cex.cex_link_congr_without_first_refines,
  `Toy.Link.Cex.cex_link_congr_without_linkable,
  `Toy.Link.Cex.cex_link_congr_without_second_refines,
  `Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec,
  `Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines,
  `Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable,
  `Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc,
  `Toy.Link.Cex.cex_sep_comp_ctx_without_linkable,
  `Toy.Link.Cex.cex_sep_comp_without_first_verified,
  `Toy.Link.Cex.cex_sep_comp_without_preservesDefines,
  `Toy.Link.Cex.cex_sep_comp_without_preservesVerified,
  `Toy.Link.Cex.cex_sep_comp_without_second_verified,
  `Toy.Link.Cex.cex_sep_comp_without_specsImplemented,
  `Toy.Link.Cex.cex_spec_refinement_without_callee_correct,
  `Toy.Link.Cex.cex_spec_refinement_without_caller_verified,
  `Toy.Link.Cex.cex_spec_refinement_without_linkable,
  `Toy.Link.Cex.cex_spec_refinement_without_strengthensPost,
  `Toy.Link.Cex.cex_spec_refinement_without_weakensPre,
  `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural,
  `Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller,
  `Toy.Link.Cex.independent_measures_do_not_compose,
  `Toy.Link.Cex.inlPass_not_preservesVerified,
  `Toy.Link.Examples.cex_ctxRefines_not_symm,
  `Toy.Link.Examples.closed_source_open_target_collapse_witness,
  `Toy.Link.Examples.collapse_closed_target_ctxRefines,
  `Toy.Link.Examples.empty_module_ag_total,
  `Toy.Link.Examples.evenOddProg_partial_correct,
  `Toy.Link.Examples.evenOddProg_total_correct,
  `Toy.Link.Examples.nonvacuous_ag_partial_correctness,
  `Toy.Link.Examples.nonvacuous_ag_total_correctness,
  `Toy.Link.Examples.nonvacuous_collapse_closed_target,
  `Toy.Link.Examples.nonvacuous_ctxRefines_link_congr,
  `Toy.Link.Examples.nonvacuous_ctxRefines_refl,
  `Toy.Link.Examples.nonvacuous_ctxRefines_reflects_mayDiverge,
  `Toy.Link.Examples.nonvacuous_ctxRefines_sameDom,
  `Toy.Link.Examples.nonvacuous_ctxRefines_trans,
  `Toy.Link.Examples.nonvacuous_recursive_spec_refinement,
  `Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary,
  `Toy.Link.Examples.nonvacuous_separate_compilation,
  `Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines,
  `Toy.Link.Examples.passCtxRefines_pos,
  `Toy.Link.Examples.positive_control_ag_total_with_wf_measure,
  `Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural,
  `Toy.Link.Examples.positive_control_in_place_export_optimization,
  `Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement,
  `Toy.Link.Examples.positive_control_spec_refinement_link,
  `Toy.Link.ag_partial_correctness,
  `Toy.Link.ag_total_correctness_of_wf_call_measure,
  `Toy.Link.caller_spec_unsat_on_own_symbols,
  `Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target,
  `Toy.Link.ctxRefines_link_congr,
  `Toy.Link.ctxRefines_link_left,
  `Toy.Link.ctxRefines_link_right,
  `Toy.Link.ctxRefines_refl,
  `Toy.Link.ctxRefines_reflects_mayDiverge,
  `Toy.Link.ctxRefines_sameDom,
  `Toy.Link.ctxRefines_trans,
  `Toy.Link.link_ag_partial_correctness,
  `Toy.Link.link_ag_total_correctness_of_wf_call_measure,
  `Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines,
  `Toy.Link.separate_compilation_partial_correct_of_preserves_verified,
  `Toy.Link.separate_compilation_preserves_partial_correctness_of_pass_ctxRefines,
  `Toy.Link.verified_flat_caller_links_with_refined_callee,
  `Toy.Link.verified_recursive_caller_links_with_refined_callee]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`ToyLink).isPrefixOf env.header.moduleNames[idx.toNat]!
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
      decls := decls.push (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString))])
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
