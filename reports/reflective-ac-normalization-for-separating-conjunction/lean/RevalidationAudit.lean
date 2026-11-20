/-
Standalone axiom and statement-closure audit for `Toy.SepAC`.
Outside the `Toy` library target; run from `lean/` with:
  lake build && lake env lean RevalidationAudit.lean
-/
import Lean
import Toy

open Lean Elab Command

private def allowedRoots : List Name := [`Toy]
private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private def wantedNames : List Name := [
  ``Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm,
  ``Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_iff,
  ``Toy.SepAC.ac_denote_eq_of_unitCount_eq_of_isPerm_nonvacuous,
  ``Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm,
  ``Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_iff,
  ``Toy.SepAC.ac_denote_eq_of_unitFree_of_isPerm_nonvacuous,
  ``Toy.SepAC.ac_laws_of_unitCount_denote_eq_of_isPerm,
  ``Toy.SepAC.ac_laws_of_unitFree_denote_eq_of_isPerm,
  ``Toy.SepAC.acu_denote_eq_of_isPerm,
  ``Toy.SepAC.acu_denote_eq_of_isPerm_iff,
  ``Toy.SepAC.acu_denote_eq_of_isPerm_nonvacuous,
  ``Toy.SepAC.acu_entails_of_cancelAtoms_nonvacuous,
  ``Toy.SepAC.acu_entails_of_cancelAtoms_of_sepMonoRight,
  ``Toy.SepAC.acu_entails_of_common_perm_nonvacuous,
  ``Toy.SepAC.acu_entails_of_common_perm_of_sepMonoRight,
  ``Toy.SepAC.acu_laws_of_denote_eq_of_isPerm,
  ``Toy.SepAC.affineCellEntails_residual_holds,
  ``Toy.SepAC.assoc_units_of_denote_eq_denoteAtoms,
  ``Toy.SepAC.atMostTwo_comm_unital_sepAssoc,
  ``Toy.SepAC.bag_dupAtomTree_denote_ne_singleAtomTree,
  ``Toy.SepAC.bag_tight_denote_eq,
  ``Toy.SepAC.bientails_acu_entails_of_cancelAtoms_nonvacuous,
  ``Toy.SepAC.bientails_acu_entails_of_cancelAtoms_of_trans_sepMonoRight,
  ``Toy.SepAC.bientails_acu_entails_of_common_perm_nonvacuous,
  ``Toy.SepAC.bientails_acu_entails_of_common_perm_of_trans_sepMonoRight,
  ``Toy.SepAC.boolAndFalse_tight_bientails_cancelAtoms_rightUnit,
  ``Toy.SepAC.boolAndFalse_tight_bientails_commonPerm_rightUnit,
  ``Toy.SepAC.boolAndFalse_tight_cancelAtoms_rightUnit,
  ``Toy.SepAC.boolAndFalse_tight_commonPerm_rightUnit,
  ``Toy.SepAC.boolAndFalse_tight_isPerm_rightUnit,
  ``Toy.SepAC.boolAndFalse_tight_unitCount_eq,
  ``Toy.SepAC.boolAndFalse_tight_unitCount_perm,
  ``Toy.SepAC.boolAndFalse_tight_unitFree_left,
  ``Toy.SepAC.boolAndFalse_tight_unitFree_perm,
  ``Toy.SepAC.boolAndFalse_tight_unitFree_right,
  ``Toy.SepAC.boolAndTrue_tight_isPerm_perm,
  ``Toy.SepAC.boolAnd_affine_cancelAtoms_converse_fails,
  ``Toy.SepAC.boolOr_linear_cancelAtoms_converse_fails,
  ``Toy.SepAC.boolOr_sepIdem,
  ``Toy.SepAC.cancelAtoms_count,
  ``Toy.SepAC.cancelAtoms_disjoint,
  ``Toy.SepAC.cancelAtoms_spec,
  ``Toy.SepAC.capOne_not_sepMonoRight,
  ``Toy.SepAC.capOne_tight_bientails_cancelAtoms_sepMonoRight,
  ``Toy.SepAC.capOne_tight_bientails_commonPerm_sepMonoRight,
  ``Toy.SepAC.capOne_tight_commonPerm_sepMonoRight,
  ``Toy.SepAC.cellModel_affine_cancelAtoms_converse_fails,
  ``Toy.SepAC.cellModel_cancelAtoms_converse_fails,
  ``Toy.SepAC.cellModel_conflict_idemElem_incomplete,
  ``Toy.SepAC.cellModel_incomplete_without_sepIdem,
  ``Toy.SepAC.checkPermSort_eq_isPerm_and_size_bounds,
  ``Toy.SepAC.checkPermSort_nonvacuous,
  ``Toy.SepAC.denote_eq_and_isPerm_false_of_idemElem,
  ``Toy.SepAC.denote_eq_and_isPerm_false_of_sepIdem,
  ``Toy.SepAC.denote_eq_denoteAtoms_iff_assoc_units,
  ``Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units,
  ``Toy.SepAC.denote_eq_denoteAtoms_of_assoc_units_nonvacuous,
  ``Toy.SepAC.idempotent_bool_acu_incomplete,
  ``Toy.SepAC.isPerm_iff_bag_denote_eq,
  ``Toy.SepAC.isPerm_iff_forall_acu_denote_eq,
  ``Toy.SepAC.isPerm_of_bag_denote_eq,
  ``Toy.SepAC.isPerm_of_bag_denote_eq_nonvacuous,
  ``Toy.SepAC.leftProj_tight_flattening_leftUnit,
  ``Toy.SepAC.listAppend_tight_bientails_cancelAtoms_sepComm,
  ``Toy.SepAC.listAppend_tight_bientails_commonPerm_sepComm,
  ``Toy.SepAC.listAppend_tight_cancelAtoms_sepComm,
  ``Toy.SepAC.listAppend_tight_commonPerm_sepComm,
  ``Toy.SepAC.listAppend_tight_isPerm_sepComm,
  ``Toy.SepAC.listAppend_tight_unitCount_sepComm,
  ``Toy.SepAC.listAppend_tight_unitFree_sepComm,
  ``Toy.SepAC.natAdd_tight_bientails_cancelAtoms_residual,
  ``Toy.SepAC.natAdd_tight_bientails_commonPerm_leftPerm,
  ``Toy.SepAC.natAdd_tight_bientails_commonPerm_residual,
  ``Toy.SepAC.natAdd_tight_bientails_commonPerm_rightPerm,
  ``Toy.SepAC.natAdd_tight_cancelAtoms_residual,
  ``Toy.SepAC.natAdd_tight_commonPerm_leftPerm,
  ``Toy.SepAC.natAdd_tight_commonPerm_residual,
  ``Toy.SepAC.natAdd_tight_commonPerm_rightPerm,
  ``Toy.SepAC.nonAssoc_tight_bientails_cancelAtoms_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_bientails_commonPerm_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_cancelAtoms_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_commonPerm_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_flattening_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_isPerm_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_unitCount_sepAssoc,
  ``Toy.SepAC.nonAssoc_tight_unitFree_sepAssoc,
  ``Toy.SepAC.optBag_absorbing_but_complete,
  ``Toy.SepAC.partial_cancellation_succeeds_where_cancelAtoms_fails,
  ``Toy.SepAC.rightProj_tight_flattening_rightUnit,
  ``Toy.SepAC.stepByTwo_nonPreorder_satisfies_cancel_hypotheses,
  ``Toy.SepAC.tagDistLeOne_tight_bientails_cancelAtoms_trans,
  ``Toy.SepAC.tagDistLeOne_tight_bientails_commonPerm_trans,
  ``Toy.SepAC.twoCellModel_affine_cancelAtoms_converse_fails,
  ``Toy.SepAC.twoCellModel_conflict_distinct_atoms_incomplete,
  ``Toy.SepAC.unitCount_converse_hypothesis_nonvacuous,
  ``Toy.SepAC.unitCount_eq_and_isPerm_of_forall_ac_denote_eq,
  ``Toy.SepAC.unitCount_eq_not_necessary_in_fixed_model
]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => allowedRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
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
  let mut declCount : Nat := 0
  let mut axPairs : Array (String × Json) := #[]
  for (n, ci) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      declCount := declCount + 1
      match ci with
      | .axiomInfo _ => throwError m!"unexpected axiom declaration: {n}"
      | .opaqueInfo _ => throwError m!"unexpected opaque declaration: {n}"
      | _ => pure ()
      let axs ← collectAxioms n
      let bad := axs.toList.filter (fun a => !allowedAxioms.contains a)
      unless bad.isEmpty do
        throwError m!"disallowed axioms on {n}: {bad}"
      let sortedAxs := (axs.map Name.toString).qsort (· < ·)
      axPairs := axPairs.push (n.toString, toJson sortedAxs)
  IO.println ("AXIOM_JSON " ++ (Json.mkObj [("count", toJson declCount), ("declarations", Json.mkObj axPairs.toList)]).compress)
  for n in wantedNames do
    match env.find? n with
    | none => throwError m!"missing declaration: {n}"
    | some ci =>
      let cl := closure env ci.type.getUsedConstants.toList {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      IO.println ("STATEMENT_JSON " ++ (Json.mkObj [
        ("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))
      ]).compress)
