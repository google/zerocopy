/-
Stand-alone audit program for this package (not part of the `ToyHoare` library target).

Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line starting with `REVALIDATION_AUDIT_JSON ` followed by a JSON object with
* `decls`: every declaration of the `ToyHoare` library with the axioms it depends on
  (computed by `Lean.collectAxioms`), and
* `stmts`: for each name listed below (every Lean name referenced by `results.json`, plus the
  boundary theorems quoted in the report), the `repr` of its type (`type_repr`) and its definition
  closure (`closure`): for every `ToyHoare` constant reachable from the type, the line
  `name : repr(type)` followed by ` := repr(value)` for definitions (theorem bodies excluded),
  sorted. The SHA-256 of `type_repr` is the statement hash and the SHA-256 of the closure lines
  joined by newlines is the closure hash recorded in `../audit/statements.json`.
-/
import Lean
import ToyHoare
open Lean Elab Command

private def auditRoots : List Name := [`ToyHoare]

private def auditNames : List Name := [
  `Toy.Hoare.LAssn.eventually_const_on_affineLine,
  `Toy.Hoare.alternating_hyp_tight,
  `Toy.Hoare.alternating_needs_affine,
  `Toy.Hoare.deriv_anyAssn_iff_valid,
  `Toy.Hoare.deriv_wlp_needs_admissible,
  `Toy.Hoare.deriv_wlp_of_wlpAdmissibleFor,
  `Toy.Hoare.erase_annotWlp,
  `Toy.Hoare.eventually_const_needs_affine,
  `Toy.Hoare.exLoopGhost_linDef_control,
  `Toy.Hoare.exLoop_deriv_anyAssn,
  `Toy.Hoare.exLoop_linDef_control_pre_zero,
  `Toy.Hoare.exLoop_linDef_control_weak_post,
  `Toy.Hoare.exLoop_no_linDef_invariant,
  `Toy.Hoare.exLoop_valid,
  `Toy.Hoare.exPost_linDef,
  `Toy.Hoare.exPre_linDef,
  `Toy.Hoare.hoare_relatively_complete_of_wlpAdmissibleFor,
  `Toy.Hoare.hoare_sound,
  `Toy.Hoare.hoare_sound_deriv_tight,
  `Toy.Hoare.linear_qf_hoare_incomplete,
  `Toy.Hoare.linear_qf_not_expressive_wlp_exLoop,
  `Toy.Hoare.ncAnnLin_verifies,
  `Toy.Hoare.nonvacuity_eventually_const_and_alternating,
  `Toy.Hoare.nonvacuity_hoare_sound,
  `Toy.Hoare.nonvacuity_relcomp,
  `Toy.Hoare.nonvacuity_semantic_iff,
  `Toy.Hoare.nonvacuity_total_sound,
  `Toy.Hoare.nonvacuity_vcgen_linear_qf_incomplete,
  `Toy.Hoare.nonvacuity_vcgen_sound,
  `Toy.Hoare.nonvacuity_vcs_annotWlp,
  `Toy.Hoare.nonvacuity_wlp_exLoop_nontrivial,
  `Toy.Hoare.not_linDef_of_alternating_on_affineLine,
  `Toy.Hoare.parity_not_linDef,
  `Toy.Hoare.relcomp_valid_tight,
  `Toy.Hoare.relcomp_wlp_admissible_tight,
  `Toy.Hoare.semantic_iff_needs_anyAssn,
  `Toy.Hoare.total_sound_of_bounded_variant,
  `Toy.Hoare.unbounded_variant_unsound,
  `Toy.Hoare.valid_iff_deriv_wlpInvented,
  `Toy.Hoare.valid_iff_vcs_annotWlp,
  `Toy.Hoare.vcgen_annotWlp,
  `Toy.Hoare.vcgen_erase_hyp_tight,
  `Toy.Hoare.vcgen_ghost_linDef_control,
  `Toy.Hoare.vcgen_invsIn_hyp_tight,
  `Toy.Hoare.vcgen_linDef_control_pre_zero,
  `Toy.Hoare.vcgen_linDef_control_weak_post,
  `Toy.Hoare.vcgen_linear_qf_annotations_incomplete,
  `Toy.Hoare.vcgen_reachable_noninductive_annotation_fails,
  `Toy.Hoare.vcgen_sound,
  `Toy.Hoare.vcgen_sound_pre_tight,
  `Toy.Hoare.vcgen_sound_vcs_tight,
  `Toy.Hoare.wlp_exLoop_anyAssn,
  `Toy.Hoare.wlp_exLoop_st2_iff,
  `Toy.Hoare.wlp_exLoop_weak_post_linDef,
  `Toy.Hoare.lassn_eventually_const_one_sided,
  `Toy.Hoare.linDef_forall_wlp_iff_tautology,
  `Toy.Hoare.ncInv_not_k_inductive,
  `Toy.Hoare.vcgen_linDef_verifies_quad_seq_but_not_deriv_linDef,
  `Toy.Hoare.vcgen_side_conditions_ignore_branch_guards,
  `Toy.Hoare.wlpAdmissibleFor_not_necessary,
  `Toy.Hoare.wlpAdmissibleFor_of_expressive,
  `Toy.Hoare.wlpAdmissibleFor_of_forall_wlp]

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
      decls := decls.push (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString))])
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
