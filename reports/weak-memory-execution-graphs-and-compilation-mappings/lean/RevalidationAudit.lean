/-
Revalidation audit program (not part of the `ToyWMM` library target).

Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints `#print axioms` for every Lean name referenced by `../results.json`, then one line
`STATEMENTS_JSON {...}` containing, for each of those names, the `repr` of its type and its
definition closure: the type and (for definitions, not theorems) the value of every constant
from the `ToyWMM` modules reachable from the type. SHA-256 of the type text is the statement
hash; SHA-256 of the sorted closure lines joined by newlines is the closure hash (see
`audit/statements.json`).
-/
import Lean
import ToyWMM
open Lean Elab Command

#print axioms Toy.WMM.Exec.coTrans_of_perLocSC
#print axioms Toy.WMM.Exec.rfFunctional_of_perLocSC
#print axioms Toy.WMM.Litmus.iriw_weak_tso_forbidden_sc_forbidden
#print axioms Toy.WMM.Litmus.lb_weak_tso_forbidden_sc_forbidden
#print axioms Toy.WMM.Litmus.mp_weak_tso_forbidden_sc_forbidden
#print axioms Toy.WMM.Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden
#print axioms Toy.WMM.Litmus.r_weak_tso_allowed_sc_forbidden
#print axioms Toy.WMM.Litmus.sbFenced_weak_tso_forbidden_sc_forbidden
#print axioms Toy.WMM.Litmus.sb_weak_tso_allowed_sc_forbidden
#print axioms Toy.WMM.Litmus.w22_weak_tso_forbidden_sc_forbidden
#print axioms Toy.WMM.Rel.acyclicB_eq_true_iff
#print axioms Toy.WMM.Rel.warshall_iff_path
#print axioms Toy.WMM.acyclic_example_neg
#print axioms Toy.WMM.acyclic_example_neg_self
#print axioms Toy.WMM.acyclic_example_pos
#print axioms Toy.WMM.coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds
#print axioms Toy.WMM.conflictsWRFencedEither_does_not_imply_sc
#print axioms Toy.WMM.exists_sc_execution_hb_unordered_needs_conflict
#print axioms Toy.WMM.exists_sc_execution_hb_unordered_of_conflict
#print axioms Toy.WMM.exists_sc_source_execution_of_tso_fenceAfterStores
#print axioms Toy.WMM.fenceAfterStores_needs_execOf
#print axioms Toy.WMM.fenceAfterStores_needs_perLocSC
#print axioms Toy.WMM.fenceAfterStores_needs_rfSameLoc
#print axioms Toy.WMM.fenceAfterStores_needs_tsoGhbAcyclic
#print axioms Toy.WMM.fenceAfterStores_sbProg
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_coSameLoc
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_fenceBetweenBothSharedWR
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_perLocSC
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_poTotal
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_poTrans
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_poWithinThread
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_rfSameLoc
#print axioms Toy.WMM.fenceBetweenBothSharedWR_needs_tsoGhbAcyclic
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_coKinds
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_fenceBetweenSharedWR
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_perLocSC
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_poTotal
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_poTrans
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_poWithinThread
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_rfSameLoc
#print axioms Toy.WMM.fenceBetweenSharedWR_needs_tsoGhbAcyclic
#print axioms Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced
#print axioms Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced_needs_conflictsWRFenced
#print axioms Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced_needs_execOf
#print axioms Toy.WMM.fenceBetweenWR_needs_fenceBetweenWR
#print axioms Toy.WMM.fenceBetweenWR_needs_perLocSC
#print axioms Toy.WMM.fenceBetweenWR_needs_poTotal
#print axioms Toy.WMM.fenceBetweenWR_needs_rfSameLoc
#print axioms Toy.WMM.fenceBetweenWR_needs_tsoGhbAcyclic
#print axioms Toy.WMM.forall_prog_exists_wf_sc_exec
#print axioms Toy.WMM.hbRaceFree_sc_executions_iff_noConflict
#print axioms Toy.WMM.keepSameLocWR_example_pos
#print axioms Toy.WMM.localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR
#print axioms Toy.WMM.noUnfencedWRIncident_vacuous_example
#print axioms Toy.WMM.nonvacuity_exists_sc_source_execution_of_tso_fenceAfterStores
#print axioms Toy.WMM.nonvacuity_scConsistentErased_of_tso_fenceAfterStores
#print axioms Toy.WMM.nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR
#print axioms Toy.WMM.nonvacuity_scConsistentErased_of_tso_of_fenceBetweenWR
#print axioms Toy.WMM.nonvacuity_scConsistent_of_scConsistentErased
#print axioms Toy.WMM.nonvacuity_scConsistent_of_tso_of_conflictsWRFenced
#print axioms Toy.WMM.nonvacuity_straightLine_race_characterizations
#print axioms Toy.WMM.nonvacuity_tsoConsistent_of_scConsistent
#print axioms Toy.WMM.not_forall_wf_tsoConsistent_scConsistent
#print axioms Toy.WMM.raceFreeEither_sc_executions_iff_conflictsWRFencedEither
#print axioms Toy.WMM.raceFree_sc_executions_iff_conflictsWRFenced
#print axioms Toy.WMM.sbFencedSC_source_execution
#print axioms Toy.WMM.sbFencedWeak_needs_fenceOrd
#print axioms Toy.WMM.sbOneFence_execution_tso_not_scErased
#print axioms Toy.WMM.scConsistentErased_of_scConsistent
#print axioms Toy.WMM.scConsistentErased_of_tso_fenceAfterStores
#print axioms Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenBothSharedWR
#print axioms Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenSharedWR
#print axioms Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenWR
#print axioms Toy.WMM.scConsistent_of_scConsistentErased
#print axioms Toy.WMM.scConsistent_of_scConsistentErased_needs_coKinds
#print axioms Toy.WMM.scConsistent_of_scConsistentErased_needs_poIrrefl
#print axioms Toy.WMM.scConsistent_of_scConsistentErased_needs_poTrans
#print axioms Toy.WMM.scConsistent_of_scConsistentErased_needs_rfKinds
#print axioms Toy.WMM.scConsistent_of_scConsistentErased_needs_scErased
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_coKinds
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_conflictsWRFenced
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_execOf
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_rfKinds
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_rfSameLoc
#print axioms Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_tso
#print axioms Toy.WMM.sourceExec_needs_execOf
#print axioms Toy.WMM.sourceExec_needs_rfCoWf
#print axioms Toy.WMM.sourceExec_needs_tso
#print axioms Toy.WMM.storeFenceExtraRfOnInserted_check
#print axioms Toy.WMM.tsoConsistent_example_pos
#print axioms Toy.WMM.tsoConsistent_of_scConsistent
#print axioms Toy.WMM.tsoConsistent_of_scConsistent_needs_sc
#print axioms Toy.WMM.tsoConsistent_of_tsoConsistentKeepSameLocWR
#print axioms Toy.WMM.tsoConsistent_of_tsoConsistentKeepSameLocWR_needs_keep
#print axioms Toy.WMM.wf_example_pos

private def auditRoots : List Name := [`ToyWMM]
private def auditNames : List Name := [`Toy.WMM.Exec.coTrans_of_perLocSC, `Toy.WMM.Exec.rfFunctional_of_perLocSC, `Toy.WMM.Litmus.iriw_weak_tso_forbidden_sc_forbidden, `Toy.WMM.Litmus.lb_weak_tso_forbidden_sc_forbidden, `Toy.WMM.Litmus.mp_weak_tso_forbidden_sc_forbidden, `Toy.WMM.Litmus.n6_weak_tso_allowed_keepSameLocWR_forbidden, `Toy.WMM.Litmus.r_weak_tso_allowed_sc_forbidden, `Toy.WMM.Litmus.sbFenced_weak_tso_forbidden_sc_forbidden, `Toy.WMM.Litmus.sb_weak_tso_allowed_sc_forbidden, `Toy.WMM.Litmus.w22_weak_tso_forbidden_sc_forbidden, `Toy.WMM.Rel.acyclicB_eq_true_iff, `Toy.WMM.Rel.warshall_iff_path, `Toy.WMM.acyclic_example_neg, `Toy.WMM.acyclic_example_neg_self, `Toy.WMM.acyclic_example_pos, `Toy.WMM.coBetweenReadsSameLoc_separates_coSameLoc_from_coKinds, `Toy.WMM.conflictsWRFencedEither_does_not_imply_sc, `Toy.WMM.exists_sc_execution_hb_unordered_needs_conflict, `Toy.WMM.exists_sc_execution_hb_unordered_of_conflict, `Toy.WMM.exists_sc_source_execution_of_tso_fenceAfterStores, `Toy.WMM.fenceAfterStores_needs_execOf, `Toy.WMM.fenceAfterStores_needs_perLocSC, `Toy.WMM.fenceAfterStores_needs_rfSameLoc, `Toy.WMM.fenceAfterStores_needs_tsoGhbAcyclic, `Toy.WMM.fenceAfterStores_sbProg, `Toy.WMM.fenceBetweenBothSharedWR_needs_coSameLoc, `Toy.WMM.fenceBetweenBothSharedWR_needs_fenceBetweenBothSharedWR, `Toy.WMM.fenceBetweenBothSharedWR_needs_perLocSC, `Toy.WMM.fenceBetweenBothSharedWR_needs_poTotal, `Toy.WMM.fenceBetweenBothSharedWR_needs_poTrans, `Toy.WMM.fenceBetweenBothSharedWR_needs_poWithinThread, `Toy.WMM.fenceBetweenBothSharedWR_needs_rfSameLoc, `Toy.WMM.fenceBetweenBothSharedWR_needs_tsoGhbAcyclic, `Toy.WMM.fenceBetweenSharedWR_needs_coKinds, `Toy.WMM.fenceBetweenSharedWR_needs_fenceBetweenSharedWR, `Toy.WMM.fenceBetweenSharedWR_needs_perLocSC, `Toy.WMM.fenceBetweenSharedWR_needs_poTotal, `Toy.WMM.fenceBetweenSharedWR_needs_poTrans, `Toy.WMM.fenceBetweenSharedWR_needs_poWithinThread, `Toy.WMM.fenceBetweenSharedWR_needs_rfSameLoc, `Toy.WMM.fenceBetweenSharedWR_needs_tsoGhbAcyclic, `Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced, `Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced_needs_conflictsWRFenced, `Toy.WMM.fenceBetweenSharedWR_of_conflictsWRFenced_needs_execOf, `Toy.WMM.fenceBetweenWR_needs_fenceBetweenWR, `Toy.WMM.fenceBetweenWR_needs_perLocSC, `Toy.WMM.fenceBetweenWR_needs_poTotal, `Toy.WMM.fenceBetweenWR_needs_rfSameLoc, `Toy.WMM.fenceBetweenWR_needs_tsoGhbAcyclic, `Toy.WMM.forall_prog_exists_wf_sc_exec, `Toy.WMM.hbRaceFree_sc_executions_iff_noConflict, `Toy.WMM.keepSameLocWR_example_pos, `Toy.WMM.localWRProg_not_conflictsWRFenced_but_fenceBetweenSharedWR, `Toy.WMM.noUnfencedWRIncident_vacuous_example, `Toy.WMM.nonvacuity_exists_sc_source_execution_of_tso_fenceAfterStores, `Toy.WMM.nonvacuity_scConsistentErased_of_tso_fenceAfterStores, `Toy.WMM.nonvacuity_scConsistentErased_of_tso_of_fenceBetweenBothSharedWR, `Toy.WMM.nonvacuity_scConsistentErased_of_tso_of_fenceBetweenWR, `Toy.WMM.nonvacuity_scConsistent_of_scConsistentErased, `Toy.WMM.nonvacuity_scConsistent_of_tso_of_conflictsWRFenced, `Toy.WMM.nonvacuity_straightLine_race_characterizations, `Toy.WMM.nonvacuity_tsoConsistent_of_scConsistent, `Toy.WMM.not_forall_wf_tsoConsistent_scConsistent, `Toy.WMM.raceFreeEither_sc_executions_iff_conflictsWRFencedEither, `Toy.WMM.raceFree_sc_executions_iff_conflictsWRFenced, `Toy.WMM.sbFencedSC_source_execution, `Toy.WMM.sbFencedWeak_needs_fenceOrd, `Toy.WMM.sbOneFence_execution_tso_not_scErased, `Toy.WMM.scConsistentErased_of_scConsistent, `Toy.WMM.scConsistentErased_of_tso_fenceAfterStores, `Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenBothSharedWR, `Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenSharedWR, `Toy.WMM.scConsistentErased_of_tso_of_fenceBetweenWR, `Toy.WMM.scConsistent_of_scConsistentErased, `Toy.WMM.scConsistent_of_scConsistentErased_needs_coKinds, `Toy.WMM.scConsistent_of_scConsistentErased_needs_poIrrefl, `Toy.WMM.scConsistent_of_scConsistentErased_needs_poTrans, `Toy.WMM.scConsistent_of_scConsistentErased_needs_rfKinds, `Toy.WMM.scConsistent_of_scConsistentErased_needs_scErased, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_coKinds, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_conflictsWRFenced, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_execOf, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_rfKinds, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_rfSameLoc, `Toy.WMM.scConsistent_of_tso_of_conflictsWRFenced_needs_tso, `Toy.WMM.sourceExec_needs_execOf, `Toy.WMM.sourceExec_needs_rfCoWf, `Toy.WMM.sourceExec_needs_tso, `Toy.WMM.storeFenceExtraRfOnInserted_check, `Toy.WMM.tsoConsistent_example_pos, `Toy.WMM.tsoConsistent_of_scConsistent, `Toy.WMM.tsoConsistent_of_scConsistent_needs_sc, `Toy.WMM.tsoConsistent_of_tsoConsistentKeepSameLocWR, `Toy.WMM.tsoConsistent_of_tsoConsistentKeepSameLocWR_needs_keep, `Toy.WMM.wf_example_pos]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => auditRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
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
  let mut stmts : Array Json := #[]
  for n in auditNames do
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
  IO.println ("STATEMENTS_JSON " ++ (Json.arr stmts).compress)
