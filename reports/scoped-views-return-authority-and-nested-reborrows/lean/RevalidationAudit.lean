/-
Revalidation audit program (not part of the `ToyViews` library target, so `lake build` does not
build it). Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `AUDIT_JSON {...}` containing, for every declaration of the `ToyViews` library,
the axioms it depends on (`Lean.collectAxioms`), and, for every Lean name referenced by
`results.json`, the `repr` of its statement (type) and the sorted text of its definition closure:
the types and values of every package-local constant reachable from the statement, with theorem
bodies excluded. SHA-256 hashes of these texts are recorded in `audit/statements.json`.
-/
import Lean
import ToyViews
open Lean Elab Command

private def roots : List Name := [`ToyViews]
private def wanted : List Name := [`Toy.Views.Ex.borrow_scope_nonvacuous,
  `Toy.Views.Ex.canWrite_iff_needs_depthCounts,
  `Toy.Views.Ex.canWrite_iff_needs_isActive,
  `Toy.Views.Ex.canWrite_iff_needs_own,
  `Toy.Views.Ex.canWrite_iff_nonvacuous,
  `Toy.Views.Ex.closedViews_not_necessary_for_returnAuthority,
  `Toy.Views.Ex.closedViews_of_borrow_scope_needs_inner_closed,
  `Toy.Views.Ex.closedViews_of_scopedRun_needs_scopedRun,
  `Toy.Views.Ex.closedViews_of_share_scope_needs_inner_closed,
  `Toy.Views.Ex.closedViews_trans_needs_both,
  `Toy.Views.Ex.closedViews_trans_nonvacuous,
  `Toy.Views.Ex.depthCounts_survives_naive_shared_end_while_writeExclusive_fails,
  `Toy.Views.Ex.endRaw_inv_needs_depthCounts,
  `Toy.Views.Ex.endRaw_inv_needs_exclChildLoaned,
  `Toy.Views.Ex.endRaw_inv_needs_parentCoversActive,
  `Toy.Views.Ex.endRaw_inv_needs_returnAuthority,
  `Toy.Views.Ex.endRaw_inv_needs_sharedChildBelowOwn,
  `Toy.Views.Ex.endRaw_inv_needs_sharedChildrenShared,
  `Toy.Views.Ex.endRaw_inv_nonvacuous_nested,
  `Toy.Views.Ex.endRaw_inv_nonvacuous_shared,
  `Toy.Views.Ex.endRaw_writeExclusive_needs_parentLt,
  `Toy.Views.Ex.endRaw_writeExclusive_needs_rootsDisjoint,
  `Toy.Views.Ex.fresh_scope_needs_end_of_fresh_view,
  `Toy.Views.Ex.fresh_scope_needs_open_step,
  `Toy.Views.Ex.loanTree_laws_nonvacuous,
  `Toy.Views.Ex.localCheck_end_needs_sharedChildBelowOwn,
  `Toy.Views.Ex.localCheck_end_needs_sharedChildrenShared,
  `Toy.Views.Ex.localCheck_needs_depthCounts,
  `Toy.Views.Ex.localCheck_needs_exclChildLoaned,
  `Toy.Views.Ex.localCheck_needs_localReturnCheck,
  `Toy.Views.Ex.localCheck_needs_parentCoversActive,
  `Toy.Views.Ex.localCheck_nonvacuous,
  `Toy.Views.Ex.naive_end_breaks_safety_of_nested_exclusive_reborrow,
  `Toy.Views.Ex.naive_end_breaks_safety_of_nested_shared_reborrow,
  `Toy.Views.Ex.naive_end_safe_without_nested_reborrow,
  `Toy.Views.Ex.naive_end_safe_without_nested_shared_reborrow,
  `Toy.Views.Ex.parent_counter_zero_means_no_reader_without_nesting,
  `Toy.Views.Ex.returnAuthority_closedViews_nonvacuous,
  `Toy.Views.Ex.returnAuthority_lost_without_activityStable,
  `Toy.Views.Ex.returnAuthority_lost_without_domainsStable,
  `Toy.Views.Ex.returnAuthority_lost_without_newViewsInactive,
  `Toy.Views.Ex.returnAuthority_lost_without_parentsExist,
  `Toy.Views.Ex.returnAuthority_lost_without_parentsStable,
  `Toy.Views.Ex.returnAuthority_needed_before_scope,
  `Toy.Views.Ex.scopedRun_authority_tightness,
  `Toy.Views.Ex.scopedRun_nonvacuous,
  `Toy.Views.Ex.scoped_end_needs_local_laws,
  `Toy.Views.Ex.scoped_end_nonvacuous,
  `Toy.Views.Ex.share_scope_nonvacuous,
  `Toy.Views.Ex.writeExclusive_needs_depthCounts,
  `Toy.Views.Ex.writeExclusive_needs_exclChildLoaned,
  `Toy.Views.Ex.writeExclusive_needs_parentCoversActive,
  `Toy.Views.Ex.writeExclusive_needs_parentLt,
  `Toy.Views.Ex.writeExclusive_needs_rootsDisjoint,
  `Toy.Views.Ex.writeExclusive_needs_sharedChildBelowOwn,
  `Toy.Views.Ex.writeExclusive_needs_sharedChildrenShared,
  `Toy.Views.Ex.write_nonvacuous,
  `Toy.Views.canWrite_iff_excl_and_no_active_shared_children_of_depthCounts,
  `Toy.Views.closedViews_of_borrow_scope,
  `Toy.Views.closedViews_of_fresh_scope,
  `Toy.Views.closedViews_of_scopedRun,
  `Toy.Views.closedViews_of_share_scope,
  `Toy.Views.closedViews_of_write,
  `Toy.Views.closedViews_refl,
  `Toy.Views.closedViews_trans,
  `Toy.Views.endRaw_preserves_loanTreeInv_and_noResurrection_of_returnAuthority,
  `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_localReturnCheck,
  `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority,
  `Toy.Views.endRaw_preserves_localLoanLaws_and_noResurrection_of_returnAuthority_before_closedViews,
  `Toy.Views.endRaw_writeExclusive_of_loanTree_laws_of_returnAuthority,
  `Toy.Views.returnAuthority_of_closedViews_of_parentCoversActive,
  `Toy.Views.returnAuthority_of_closedViews_of_parentsExist,
  `Toy.Views.returnAuthority_of_localReturnCheck_of_parentCoversActive_exclChildLoaned_depthCounts,
  `Toy.Views.returnAuthority_of_scopedRun_of_parentCoversActive,
  `Toy.Views.writeExclusive_of_loanTree_laws]

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
