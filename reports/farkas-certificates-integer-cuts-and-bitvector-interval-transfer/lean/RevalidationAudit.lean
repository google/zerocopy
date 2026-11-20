/-
Revalidation audit for this package (not part of the `ToyFarkas` library target).

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `REVALIDATION_AUDIT_JSON {...}` containing
* `decls`: every declaration of the `ToyFarkas` modules with the axioms it depends on
  (computed with `Lean.collectAxioms`);
* `stmts`: for every Lean name referenced by `results.json`, the `repr` of its type
  (the statement) and its definition closure: one line `name : type := value` for every
  package constant reachable from the statement (theorem bodies are excluded).
The SHA-256 of the statement text and of the newline-joined, sorted closure lines are the
`statement_sha256` and `closure_sha256` values recorded in `audit/statements.json`.
-/
import Lean
import ToyFarkas
open Lean Elab Command

private def roots : List Name := [`ToyFarkas]
private def wanted : List Name := [
  `Toy.Farkas.SparseVec.eval_eq_denseDotOn_coeff_of_nodup_of_keys_mem,
  `Toy.Farkas.SparseVec.eval_eq_denseDot_coeff_of_keys_lt,
  `Toy.Farkas.SparseVec.isZero_iff_coeff_eq_zero,
  `Toy.Farkas.bv_sle_slt_iff_int_of_inSignedRange,
  `Toy.Farkas.bv_sle_slt_iff_int_of_noWrapS,
  `Toy.Farkas.bv_ule_ult_iff_int_of_inUnsignedRange,
  `Toy.Farkas.bv_ule_ult_iff_int_of_noWrapU,
  `Toy.Farkas.ce_bv_reading_mismatch,
  `Toy.Farkas.ce_bv_rearrangement_unsound,
  `Toy.Farkas.ce_bv_sle_lhs_out_of_range,
  `Toy.Farkas.ce_bv_sle_noWrapS_lhs,
  `Toy.Farkas.ce_bv_sle_noWrapS_rhs,
  `Toy.Farkas.ce_bv_sle_rhs_out_of_range,
  `Toy.Farkas.ce_bv_ule_lhs_out_of_range,
  `Toy.Farkas.ce_bv_ule_noWrapU_lhs,
  `Toy.Farkas.ce_bv_ule_noWrapU_rhs,
  `Toy.Farkas.ce_bv_ule_rhs_out_of_range,
  `Toy.Farkas.ce_cgCut_div_one_unsound_over_rat,
  `Toy.Farkas.ce_cgCut_negative_divisor,
  `Toy.Farkas.ce_cgCut_negative_multiplier,
  `Toy.Farkas.ce_cgCut_not_divisible,
  `Toy.Farkas.ce_cgCut_point_not_solution,
  `Toy.Farkas.ce_cgCut_unsound_over_rat,
  `Toy.Farkas.ce_cgDerive_rejected,
  `Toy.Farkas.ce_checkCutCert_rejects_satisfiable,
  `Toy.Farkas.ce_checkCutCert_unsound_over_rat,
  `Toy.Farkas.ce_checkFarkasTightened_rejects_satisfiable,
  `Toy.Farkas.ce_checkFarkas_bvS_lhs_out_of_range,
  `Toy.Farkas.ce_checkFarkas_bvS_rhs_out_of_range,
  `Toy.Farkas.ce_checkFarkas_bvU_lhs_out_of_range,
  `Toy.Farkas.ce_checkFarkas_bvU_rhs_out_of_range,
  `Toy.Farkas.ce_checkFarkas_refutes_bv_rejected,
  `Toy.Farkas.ce_checkFarkas_rejected_satisfiable,
  `Toy.Farkas.ce_eval_eq_denseDotOn_duplicate_index_list,
  `Toy.Farkas.ce_eval_eq_denseDotOn_missing_index,
  `Toy.Farkas.ce_eval_eq_denseDot_index_out_of_range,
  `Toy.Farkas.ce_farkas_complete_feasible_system,
  `Toy.Farkas.ce_farkas_denominator_zero,
  `Toy.Farkas.ce_farkas_incomplete_int,
  `Toy.Farkas.ce_farkas_lhs_not_vanishing,
  `Toy.Farkas.ce_farkas_negative_multiplier,
  `Toy.Farkas.ce_farkas_rhs_not_contradicting,
  `Toy.Farkas.ce_farkas_strict_flag_from_zero_weight,
  `Toy.Farkas.ce_farkas_strictness_ignored,
  `Toy.Farkas.ce_noWrap_not_needed_for_wrapping_eval,
  `Toy.Farkas.ce_tightening_unsound_over_rat,
  `Toy.Farkas.ce_zero_test_first_match,
  `Toy.Farkas.ce_zero_test_first_match_dupfree_inputs,
  `Toy.Farkas.ce_zero_test_index_blind,
  `Toy.Farkas.cgCut_sound_int_of_nonneg_of_div_pos_of_divisible,
  `Toy.Farkas.cgDerive_sound_int,
  `Toy.Farkas.checkCutCert_sound_int,
  `Toy.Farkas.checkFarkasTightened_sound_int,
  `Toy.Farkas.checkFarkas_refutes_bvS_posSupport_of_lhs_lt_of_rhs_ge,
  `Toy.Farkas.checkFarkas_refutes_bvU_posSupport_of_lhs_lt_of_rhs_nonneg,
  `Toy.Farkas.checkFarkas_sound_int,
  `Toy.Farkas.checkFarkas_sound_int_posSupport,
  `Toy.Farkas.checkFarkas_sound_scaled,
  `Toy.Farkas.checkFarkas_sound_scaled_posSupport,
  `Toy.Farkas.combineLhs_coeff,
  `Toy.Farkas.combineLhs_eval,
  `Toy.Farkas.farkas_complete_scaled,
  `Toy.Farkas.farkas_sound_scaled_of_nonneg_of_lhsVanishes_of_rhsContradicts,
  `Toy.Farkas.nv_bv_sle_slt_noWrapS,
  `Toy.Farkas.nv_bv_sle_slt_transfer,
  `Toy.Farkas.nv_bv_ule_ult_noWrapU,
  `Toy.Farkas.nv_bv_ule_ult_transfer,
  `Toy.Farkas.nv_cgCut_sound_int,
  `Toy.Farkas.nv_checkCutCert_sound_int,
  `Toy.Farkas.nv_checkFarkasTightened,
  `Toy.Farkas.nv_checkFarkas_refutes_bvS,
  `Toy.Farkas.nv_checkFarkas_refutes_bvU,
  `Toy.Farkas.nv_checkFarkas_refutes_bv_two_sided,
  `Toy.Farkas.nv_checkFarkas_sound,
  `Toy.Farkas.nv_checkFarkas_sound_posSupport,
  `Toy.Farkas.nv_checkFarkas_sound_scaled,
  `Toy.Farkas.nv_combineLhs_coeff,
  `Toy.Farkas.nv_combineLhs_eval,
  `Toy.Farkas.nv_eval_eq_denseDot,
  `Toy.Farkas.nv_eval_eq_denseDotOn,
  `Toy.Farkas.nv_farkas_complete_scaled,
  `Toy.Farkas.nv_farkas_sound_structured,
  `Toy.Farkas.nv_isZero_iff,
  `Toy.Farkas.sysHalf_refuted_by_case_split
]

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
  IO.println ("REVALIDATION_AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
