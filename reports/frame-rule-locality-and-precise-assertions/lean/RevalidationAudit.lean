/-
Revalidation audit for this package (not part of the `Toy` library target).
Run from this directory after `lake build`:  lake env lean RevalidationAudit.lean
1. `#print axioms` for every Lean name referenced by `results.json`.
2. One line `AUDIT_JSON {...}`: for every package declaration its axioms, and for every
   card-referenced name the `repr` of its statement and its definition closure (the
   strings whose SHA-256 values are recorded in `audit/statements.json`).
-/
import Lean
import Toy
open Lean Elab Command

private def roots : List Name := [`Toy]
private def wanted : List Name := [`Toy.Sep.allocAtBlock_local_and_blocks_when_taken, `Toy.Sep.allocAtBlock_safetyMono_and_frameProp, `Toy.Sep.allocAt_frameProp, `Toy.Sep.allocAt_frameProp_and_framed_triple_fails, `Toy.Sep.allocAt_not_safetyMono, `Toy.Sep.allocInto_safetyMono_and_frameProp, `Toy.Sep.allocLeast_fqTriple_someCell, `Toy.Sep.allocLeast_frame_rule_for_emp_frame_and_not_local, `Toy.Sep.allocLeast_not_frameProp, `Toy.Sep.allocLeast_not_safetyMono_and_frameProp, `Toy.Sep.allocLeast_safetyMono, `Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails, `Toy.Sep.allocLeast_triple_and_not_fqTriple, `Toy.Sep.alloc_frameProp, `Toy.Sep.alloc_not_alwaysAllocatesAt_and_frameProp, `Toy.Sep.alloc_safetyMono_and_frameProp, `Toy.Sep.assertAlloc_faults_and_safetyMono, `Toy.Sep.assertAlloc_frameProp, `Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails, `Toy.Sep.assertAlloc_safetyMono, `Toy.Sep.assocGap_unionAssocRev_and_fqTriple_frame_fails, `Toy.Sep.boundary_witnesses_nonvacuous, `Toy.Sep.cancel_coincide_nonvacuous, `Toy.Sep.commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails, `Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm, `Toy.Sep.conjDistrib_iff_uniqueFrame, `Toy.Sep.conjDistrib_iff_uniqueFrame_nonvacuous, `Toy.Sep.conjDistrib_of_precise_of_rightCancel, `Toy.Sep.conjDistrib_of_precise_of_rightCancel_nonvacuous, `Toy.Sep.detAllocInto_fresh_nonvacuous, `Toy.Sep.detAllocInto_not_frameProp_of_fresh, `Toy.Sep.detAllocInto_self_frameProp, `Toy.Sep.detAllocOnEmp_frameProp, `Toy.Sep.detAllocOnEmp_not_runsWhenOccupied_and_frameProp, `Toy.Sep.detAlloc_not_frameProp, `Toy.Sep.emptyDisj_degenerate, `Toy.Sep.emptyDisj_disjSymm_unionComm_no_unit_and_fqTriple_adequacy_fails, `Toy.Sep.emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails, `Toy.Sep.faultOrSet0_not_safe_and_frameProp, `Toy.Sep.forkR_conjDistrib_and_not_precise, `Toy.Sep.fork_isSepAlgebra, `Toy.Sep.fork_not_leftCancel, `Toy.Sep.fork_not_rightCancel, `Toy.Sep.fqTriple_frame_nonvacuous, `Toy.Sep.fqTriple_frame_of_disjSymm_of_unionAssoc, `Toy.Sep.fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc, `Toy.Sep.fqTriple_frame_of_unionAssoc_of_unionAssocRev, `Toy.Sep.fqTriple_frame_premise_tight, `Toy.Sep.frameRuleAtSingletons_assertAlloc, `Toy.Sep.frameRuleForPreciseFrames_nonvacuous, `Toy.Sep.frameRuleSound_iff_nonvacuous, `Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp, `Toy.Sep.frame_rule_of_safetyMono_of_frameProp, `Toy.Sep.frame_rule_of_safetyMono_of_frameProp_nonvacuous, `Toy.Sep.free_safetyMono_and_frameProp, `Toy.Sep.heap_commands_framed_runs_nonvacuous, `Toy.Sep.heap_empty_all_commands_local, `Toy.Sep.heap_fqTriple_frame, `Toy.Sep.heap_leftCancel, `Toy.Sep.heap_leftCancel_and_oneCell_not_precise, `Toy.Sep.heap_precise_iff_atMostOneSubheap, `Toy.Sep.heap_precise_iff_conjDistrib, `Toy.Sep.heap_precise_iff_conjDistrib_nonvacuous, `Toy.Sep.heap_rightCancel, `Toy.Sep.heap_rightCancel_and_oneCell_not_conjDistrib, `Toy.Sep.heap_triple_of_fqTriple, `Toy.Sep.isAllocTest_not_frameProp, `Toy.Sep.isAllocTest_safetyMono, `Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails, `Toy.Sep.isAllocTest_self_frameProp, `Toy.Sep.leftCancel_iff_rightCancel_of_disjSymm_of_unionComm, `Toy.Sep.leftCancel_of_disjSymm_of_unionComm_of_rightCancel, `Toy.Sep.leftDisjCommUnit_unionComm_unitLaw_and_fqTriple_adequacy_fails, `Toy.Sep.lookup_safetyMono_and_frameProp, `Toy.Sep.mutate_safetyMono_and_frameProp, `Toy.Sep.not_frameProp_of_alwaysAllocatesAt_nonvacuous, `Toy.Sep.not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied, `Toy.Sep.not_safetyMono_of_safe_emp_of_faults, `Toy.Sep.oneCell_conjDistrib_fails, `Toy.Sep.oneCell_not_precise, `Toy.Sep.onePair_true_precise, `Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails, `Toy.Sep.orAlg_disjSymm_unionComm_not_leftCancel, `Toy.Sep.orAlg_disjSymm_unionComm_not_rightCancel, `Toy.Sep.orAlg_isSepAlgebra, `Toy.Sep.orAlg_not_leftCancel, `Toy.Sep.orAlg_not_rightCancel, `Toy.Sep.orAlg_true_precise_and_not_conjDistrib, `Toy.Sep.orDisjLeft_unionComm_rightCancel_not_leftCancel, `Toy.Sep.orDisjRight_unionComm_and_not_conjDistrib_iff_conjDistribLeft, `Toy.Sep.orDisjRight_unionComm_and_not_precise_iff_preciseLeft, `Toy.Sep.orDisjRight_unionComm_leftCancel_not_rightCancel, `Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm, `Toy.Sep.precise_of_conjDistrib_of_leftCancel, `Toy.Sep.precise_of_conjDistrib_of_leftCancel_nonvacuous, `Toy.Sep.projLeft_disjSymm_and_not_precise_iff_preciseLeft, `Toy.Sep.projLeft_disjSymm_rightCancel_not_leftCancel, `Toy.Sep.projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm, `Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft, `Toy.Sep.projRight_disjSymm_and_not_conjDistrib_iff_conjDistribLeft, `Toy.Sep.projRight_disjSymm_leftCancel_not_rightCancel, `Toy.Sep.projRight_disjSymm_unitLaw_and_fqTriple_adequacy_fails, `Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft, `Toy.Sep.ptAny_precise, `Toy.Sep.rightCancel_of_disjSymm_of_unionComm_of_leftCancel, `Toy.Sep.rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw, `Toy.Sep.safetyMono_and_frameProp_of_frameRuleAtSingletons, `Toy.Sep.safetyMono_and_frameProp_of_frameRuleForPreciseFrames, `Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty, `Toy.Sep.skip_local_and_framed_triple_fails, `Toy.Sep.skip_occupied_base_and_frameProp, `Toy.Sep.skip_safe_emp_and_safetyMono, `Toy.Sep.someCellAllocated_conjDistrib_fails, `Toy.Sep.someCellAllocated_not_precise, `Toy.Sep.symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails, `Toy.Sep.triple_conj, `Toy.Sep.triple_conj_nonvacuous, `Toy.Sep.triple_conj_premise1_tight, `Toy.Sep.triple_conj_premise2_tight, `Toy.Sep.triple_of_fqTriple_nonvacuous, `Toy.Sep.triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw, `Toy.Sep.triple_of_fqTriple_of_rightUnitLaw, `Toy.Sep.triple_of_fqTriple_premise_tight, `Toy.Sep.unionAssocRev_of_disjSymm_of_unionAssoc, `Toy.Sep.unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc]

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

#print axioms Toy.Sep.allocAtBlock_local_and_blocks_when_taken
#print axioms Toy.Sep.allocAtBlock_safetyMono_and_frameProp
#print axioms Toy.Sep.allocAt_frameProp
#print axioms Toy.Sep.allocAt_frameProp_and_framed_triple_fails
#print axioms Toy.Sep.allocAt_not_safetyMono
#print axioms Toy.Sep.allocInto_safetyMono_and_frameProp
#print axioms Toy.Sep.allocLeast_fqTriple_someCell
#print axioms Toy.Sep.allocLeast_frame_rule_for_emp_frame_and_not_local
#print axioms Toy.Sep.allocLeast_not_frameProp
#print axioms Toy.Sep.allocLeast_not_safetyMono_and_frameProp
#print axioms Toy.Sep.allocLeast_safetyMono
#print axioms Toy.Sep.allocLeast_safetyMono_and_framed_triple_fails
#print axioms Toy.Sep.allocLeast_triple_and_not_fqTriple
#print axioms Toy.Sep.alloc_frameProp
#print axioms Toy.Sep.alloc_not_alwaysAllocatesAt_and_frameProp
#print axioms Toy.Sep.alloc_safetyMono_and_frameProp
#print axioms Toy.Sep.assertAlloc_faults_and_safetyMono
#print axioms Toy.Sep.assertAlloc_frameProp
#print axioms Toy.Sep.assertAlloc_local_and_framed_weakTriple_fails
#print axioms Toy.Sep.assertAlloc_safetyMono
#print axioms Toy.Sep.assocGap_unionAssocRev_and_fqTriple_frame_fails
#print axioms Toy.Sep.boundary_witnesses_nonvacuous
#print axioms Toy.Sep.cancel_coincide_nonvacuous
#print axioms Toy.Sep.commOneWay_unionComm_unionAssoc_and_fqTriple_frame_fails
#print axioms Toy.Sep.conjDistrib_iff_conjDistribLeft_of_disjSymm_of_unionComm
#print axioms Toy.Sep.conjDistrib_iff_uniqueFrame
#print axioms Toy.Sep.conjDistrib_iff_uniqueFrame_nonvacuous
#print axioms Toy.Sep.conjDistrib_of_precise_of_rightCancel
#print axioms Toy.Sep.conjDistrib_of_precise_of_rightCancel_nonvacuous
#print axioms Toy.Sep.detAllocInto_fresh_nonvacuous
#print axioms Toy.Sep.detAllocInto_not_frameProp_of_fresh
#print axioms Toy.Sep.detAllocInto_self_frameProp
#print axioms Toy.Sep.detAllocOnEmp_frameProp
#print axioms Toy.Sep.detAllocOnEmp_not_runsWhenOccupied_and_frameProp
#print axioms Toy.Sep.detAlloc_not_frameProp
#print axioms Toy.Sep.emptyDisj_degenerate
#print axioms Toy.Sep.emptyDisj_disjSymm_unionComm_no_unit_and_fqTriple_adequacy_fails
#print axioms Toy.Sep.emptyDisj_no_rightUnit_and_fqTriple_adequacy_fails
#print axioms Toy.Sep.faultOrSet0_not_safe_and_frameProp
#print axioms Toy.Sep.forkR_conjDistrib_and_not_precise
#print axioms Toy.Sep.fork_isSepAlgebra
#print axioms Toy.Sep.fork_not_leftCancel
#print axioms Toy.Sep.fork_not_rightCancel
#print axioms Toy.Sep.fqTriple_frame_nonvacuous
#print axioms Toy.Sep.fqTriple_frame_of_disjSymm_of_unionAssoc
#print axioms Toy.Sep.fqTriple_frame_of_disjSymm_of_unionComm_of_unionAssoc
#print axioms Toy.Sep.fqTriple_frame_of_unionAssoc_of_unionAssocRev
#print axioms Toy.Sep.fqTriple_frame_premise_tight
#print axioms Toy.Sep.frameRuleAtSingletons_assertAlloc
#print axioms Toy.Sep.frameRuleForPreciseFrames_nonvacuous
#print axioms Toy.Sep.frameRuleSound_iff_nonvacuous
#print axioms Toy.Sep.frameRuleSound_iff_safetyMono_and_frameProp
#print axioms Toy.Sep.frame_rule_of_safetyMono_of_frameProp
#print axioms Toy.Sep.frame_rule_of_safetyMono_of_frameProp_nonvacuous
#print axioms Toy.Sep.free_safetyMono_and_frameProp
#print axioms Toy.Sep.heap_commands_framed_runs_nonvacuous
#print axioms Toy.Sep.heap_empty_all_commands_local
#print axioms Toy.Sep.heap_fqTriple_frame
#print axioms Toy.Sep.heap_leftCancel
#print axioms Toy.Sep.heap_leftCancel_and_oneCell_not_precise
#print axioms Toy.Sep.heap_precise_iff_atMostOneSubheap
#print axioms Toy.Sep.heap_precise_iff_conjDistrib
#print axioms Toy.Sep.heap_precise_iff_conjDistrib_nonvacuous
#print axioms Toy.Sep.heap_rightCancel
#print axioms Toy.Sep.heap_rightCancel_and_oneCell_not_conjDistrib
#print axioms Toy.Sep.heap_triple_of_fqTriple
#print axioms Toy.Sep.isAllocTest_not_frameProp
#print axioms Toy.Sep.isAllocTest_safetyMono
#print axioms Toy.Sep.isAllocTest_safetyMono_and_framed_triple_fails
#print axioms Toy.Sep.isAllocTest_self_frameProp
#print axioms Toy.Sep.leftCancel_iff_rightCancel_of_disjSymm_of_unionComm
#print axioms Toy.Sep.leftCancel_of_disjSymm_of_unionComm_of_rightCancel
#print axioms Toy.Sep.leftDisjCommUnit_unionComm_unitLaw_and_fqTriple_adequacy_fails
#print axioms Toy.Sep.lookup_safetyMono_and_frameProp
#print axioms Toy.Sep.mutate_safetyMono_and_frameProp
#print axioms Toy.Sep.not_frameProp_of_alwaysAllocatesAt_nonvacuous
#print axioms Toy.Sep.not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied
#print axioms Toy.Sep.not_safetyMono_of_safe_emp_of_faults
#print axioms Toy.Sep.oneCell_conjDistrib_fails
#print axioms Toy.Sep.oneCell_not_precise
#print axioms Toy.Sep.onePair_true_precise
#print axioms Toy.Sep.oneWayAssoc_unionAssoc_and_fqTriple_frame_fails
#print axioms Toy.Sep.orAlg_disjSymm_unionComm_not_leftCancel
#print axioms Toy.Sep.orAlg_disjSymm_unionComm_not_rightCancel
#print axioms Toy.Sep.orAlg_isSepAlgebra
#print axioms Toy.Sep.orAlg_not_leftCancel
#print axioms Toy.Sep.orAlg_not_rightCancel
#print axioms Toy.Sep.orAlg_true_precise_and_not_conjDistrib
#print axioms Toy.Sep.orDisjLeft_unionComm_rightCancel_not_leftCancel
#print axioms Toy.Sep.orDisjRight_unionComm_and_not_conjDistrib_iff_conjDistribLeft
#print axioms Toy.Sep.orDisjRight_unionComm_and_not_precise_iff_preciseLeft
#print axioms Toy.Sep.orDisjRight_unionComm_leftCancel_not_rightCancel
#print axioms Toy.Sep.precise_iff_preciseLeft_of_disjSymm_of_unionComm
#print axioms Toy.Sep.precise_of_conjDistrib_of_leftCancel
#print axioms Toy.Sep.precise_of_conjDistrib_of_leftCancel_nonvacuous
#print axioms Toy.Sep.projLeft_disjSymm_and_not_precise_iff_preciseLeft
#print axioms Toy.Sep.projLeft_disjSymm_rightCancel_not_leftCancel
#print axioms Toy.Sep.projLeft_disjSymm_unionAssoc_unionAssocRev_not_unionComm
#print axioms Toy.Sep.projLeft_rightCancel_precise_not_conjDistribLeft
#print axioms Toy.Sep.projRight_disjSymm_and_not_conjDistrib_iff_conjDistribLeft
#print axioms Toy.Sep.projRight_disjSymm_leftCancel_not_rightCancel
#print axioms Toy.Sep.projRight_disjSymm_unitLaw_and_fqTriple_adequacy_fails
#print axioms Toy.Sep.projRight_leftCancel_precise_not_conjDistrib_not_preciseLeft
#print axioms Toy.Sep.ptAny_precise
#print axioms Toy.Sep.rightCancel_of_disjSymm_of_unionComm_of_leftCancel
#print axioms Toy.Sep.rightUnitLaw_of_disjSymm_of_unionComm_of_unitLaw
#print axioms Toy.Sep.safetyMono_and_frameProp_of_frameRuleAtSingletons
#print axioms Toy.Sep.safetyMono_and_frameProp_of_frameRuleForPreciseFrames
#print axioms Toy.Sep.skipOnEmp_local_and_no_outcome_on_nonempty
#print axioms Toy.Sep.skip_local_and_framed_triple_fails
#print axioms Toy.Sep.skip_occupied_base_and_frameProp
#print axioms Toy.Sep.skip_safe_emp_and_safetyMono
#print axioms Toy.Sep.someCellAllocated_conjDistrib_fails
#print axioms Toy.Sep.someCellAllocated_not_precise
#print axioms Toy.Sep.symmAssocGap_disjSymm_unionComm_and_fqTriple_frame_fails
#print axioms Toy.Sep.triple_conj
#print axioms Toy.Sep.triple_conj_nonvacuous
#print axioms Toy.Sep.triple_conj_premise1_tight
#print axioms Toy.Sep.triple_conj_premise2_tight
#print axioms Toy.Sep.triple_of_fqTriple_nonvacuous
#print axioms Toy.Sep.triple_of_fqTriple_of_disjSymm_of_unionComm_of_unitLaw
#print axioms Toy.Sep.triple_of_fqTriple_of_rightUnitLaw
#print axioms Toy.Sep.triple_of_fqTriple_premise_tight
#print axioms Toy.Sep.unionAssocRev_of_disjSymm_of_unionAssoc
#print axioms Toy.Sep.unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc
