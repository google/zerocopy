/-
Stand-alone revalidation audit for this package (not part of the `Toy` library target).

Run from the `lean/` directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `REVALIDATION_AUDIT_JSON {...}` containing
- `decls`: every non-internal declaration of the `Toy` library with the axioms it depends on
  (computed with `Lean.collectAxioms`);
- `stmts`: for every Lean name referenced by `results.json`, the `repr` of its type
  (`type_repr`) and its definition closure (`closure`): one line per package-local constant
  reachable from the statement, `name : repr(type)` followed by ` := repr(value)` for
  non-theorems, sorted. The SHA-256 of `type_repr` and of the newline-joined `closure` are
  the `statement_sha256` and `closure_sha256` recorded in `audit/statements.json`.
-/
import Lean
import Toy
open Lean Elab Command

private def auditRoots : List Name := [`Toy]
private def auditNames : List Name := [
  `Toy.MachInt.castFromSigned_toInt_eq_of_widthLe,
  `Toy.MachInt.castFromUnsigned_toNat_eq_mod,
  `Toy.MachInt.castFromUnsigned_widened_toNat_eq_mod,
  `Toy.MachInt.castFromUnsigned_widened_toNat_eq_mod_forall_iff,
  `Toy.MachInt.castFromUnsigned_widened_toNat_eq_mod_of_source_le,
  `Toy.MachInt.cast_roundTrip_widen_then_narrow_of_widthLe,
  `Toy.MachInt.cast_u32_to_u8_to_u32_eq_mod_256,
  `Toy.MachInt.ce_castFromSigned_drop_widthLe,
  `Toy.MachInt.ce_castFromUnsigned_widened_drop_widthLe,
  `Toy.MachInt.ce_cast_roundTrip_drop_widthLe,
  `Toy.MachInt.ce_cast_roundTrip_drop_widthLe_canonical,
  `Toy.MachInt.ce_cast_roundTrip_narrow_then_widen,
  `Toy.MachInt.ce_checkedSDivEuclid_drop_noSDivOverflow,
  `Toy.MachInt.ce_checkedSDivEuclid_drop_nonZeroDiv,
  `Toy.MachInt.ce_checkedSDiv_drop_noSDivOverflow,
  `Toy.MachInt.ce_checkedSDiv_drop_nonZeroDiv,
  `Toy.MachInt.ce_checkedSRemEuclid_drop_noSDivOverflow,
  `Toy.MachInt.ce_checkedSRemEuclid_drop_nonZeroDiv,
  `Toy.MachInt.ce_checkedSRem_drop_noSDivOverflow,
  `Toy.MachInt.ce_checkedSRem_drop_nonZeroDiv,
  `Toy.MachInt.ce_checkedSRem_intMin_drop_posWidth,
  `Toy.MachInt.ce_checkedSRem_intMin_drop_posWidth_canonical,
  `Toy.MachInt.ce_checkedS_add_sub_intermediate_overflow,
  `Toy.MachInt.ce_checkedShl_drops_high_bits_without_none,
  `Toy.MachInt.ce_checkedUDiv_drop_nonZeroDiv,
  `Toy.MachInt.ce_checkedU_add_sub_intermediate_overflow,
  `Toy.MachInt.ce_checked_add_sub_intermediate_overflow,
  `Toy.MachInt.ce_evalCheckedS_sound_drop_some,
  `Toy.MachInt.ce_evalCheckedU_sound_drop_some,
  `Toy.MachInt.ce_evalWrap_eq_drop_intRingIdentity,
  `Toy.MachInt.ce_evalWrap_eq_not_imp_intRingIdentity,
  `Toy.MachInt.ce_sdiv_srem_ne_int_ediv_emod,
  `Toy.MachInt.ce_slt_add_right_both_wrap,
  `Toy.MachInt.ce_slt_add_right_drop_hlt,
  `Toy.MachInt.ce_slt_add_right_drop_noSAddOverflow_left,
  `Toy.MachInt.ce_slt_add_right_drop_noSAddOverflow_right,
  `Toy.MachInt.ce_slt_add_right_iff_drop_hlt,
  `Toy.MachInt.ce_sshiftRight_ne_sdiv_twoPow,
  `Toy.MachInt.ce_tdiv_overflow_iff_drop_posWidth,
  `Toy.MachInt.ce_tdiv_overflow_iff_drop_posWidth_canonical,
  `Toy.MachInt.ce_ult_add_right_both_wrap,
  `Toy.MachInt.ce_ult_add_right_drop_hlt,
  `Toy.MachInt.ce_ult_add_right_drop_noUAddOverflow,
  `Toy.MachInt.ce_ult_add_right_iff_drop_hlt,
  `Toy.MachInt.ce_wrappingShl_drop_shiftInBounds_canonical,
  `Toy.MachInt.ce_wrappingShl_mod_ne_and_mask_nonPowTwo,
  `Toy.MachInt.ce_wrappingShl_overshift_ne_mul_twoPow,
  `Toy.MachInt.ce_wrappingShr_drop_shiftInBounds_canonical,
  `Toy.MachInt.ce_wrappingShr_overshift,
  `Toy.MachInt.checkedSDivEuclid_eq_some_and_toInt_eq_ediv,
  `Toy.MachInt.checkedSDiv_eq_some_and_toInt_eq_tdiv,
  `Toy.MachInt.checkedSRemEuclid_eq_some_and_toInt_eq_emod,
  `Toy.MachInt.checkedSRem_eq_some_and_toInt_eq_tmod,
  `Toy.MachInt.checkedSRem_intMin_negOne_eq_none,
  `Toy.MachInt.checkedSRem_intMin_negOne_eq_none_unconditional,
  `Toy.MachInt.checkedUDiv_and_checkedURem_eq_nat_div_mod,
  `Toy.MachInt.evalCheckedS_complete,
  `Toy.MachInt.evalCheckedS_isSome_iff_subexprsInRange,
  `Toy.MachInt.evalCheckedS_sound,
  `Toy.MachInt.evalCheckedU_complete,
  `Toy.MachInt.evalCheckedU_isSome_iff_subexprsInRange,
  `Toy.MachInt.evalCheckedU_sound,
  `Toy.MachInt.evalWrap_eq_of_intRingIdentity,
  `Toy.MachInt.evalWrap_toInt_eq_bmod,
  `Toy.MachInt.evalWrap_toNat_eq_emod,
  `Toy.MachInt.inSignedRange_iff_two_pow_of_posWidth,
  `Toy.MachInt.mod_eq_and_mask_forall_iff_isPowerOfTwo,
  `Toy.MachInt.mod_twoPow_eq_and_mask,
  `Toy.MachInt.noUAddOverflow_of_ult_of_noUAddOverflow,
  `Toy.MachInt.not_slt_add_one_sMax,
  `Toy.MachInt.not_slt_intMax_add_one,
  `Toy.MachInt.not_ult_add_one_uMax,
  `Toy.MachInt.not_ult_allOnes_add_one,
  `Toy.MachInt.nv_castFromSigned_toInt_eq_of_widthLe,
  `Toy.MachInt.nv_castFromUnsigned_toNat_eq_mod,
  `Toy.MachInt.nv_castFromUnsigned_widened_toNat_eq_mod,
  `Toy.MachInt.nv_cast_roundTrip_widen_then_narrow_of_widthLe,
  `Toy.MachInt.nv_cast_u32_to_u8_to_u32_eq_mod_256,
  `Toy.MachInt.nv_checkedSDivEuclid_eq_some_and_toInt_eq_ediv,
  `Toy.MachInt.nv_checkedSDiv_eq_some_and_toInt_eq_tdiv,
  `Toy.MachInt.nv_checkedSRemEuclid_eq_some_and_toInt_eq_emod,
  `Toy.MachInt.nv_checkedSRem_eq_some_and_toInt_eq_tmod,
  `Toy.MachInt.nv_checkedSRem_intMin_negOne_eq_none,
  `Toy.MachInt.nv_checkedUDiv_and_checkedURem_eq_nat_div_mod,
  `Toy.MachInt.nv_evalCheckedS_complete,
  `Toy.MachInt.nv_evalCheckedS_isSome_iff_subexprsInRange,
  `Toy.MachInt.nv_evalCheckedS_sound,
  `Toy.MachInt.nv_evalCheckedU_complete,
  `Toy.MachInt.nv_evalCheckedU_isSome_iff_subexprsInRange,
  `Toy.MachInt.nv_evalCheckedU_sound,
  `Toy.MachInt.nv_evalWrap_eq_of_intRingIdentity,
  `Toy.MachInt.nv_evalWrap_toInt_eq_bmod,
  `Toy.MachInt.nv_evalWrap_toNat_eq_emod,
  `Toy.MachInt.nv_not_slt_intMax_add_one,
  `Toy.MachInt.nv_not_ult_allOnes_add_one,
  `Toy.MachInt.nv_reinterpretCast_characterization,
  `Toy.MachInt.nv_slt_add_right_iff_saddOverflow_eq,
  `Toy.MachInt.nv_slt_add_right_of_noSAddOverflow,
  `Toy.MachInt.nv_tdiv_iff_both_false,
  `Toy.MachInt.nv_tdiv_iff_width_one,
  `Toy.MachInt.nv_tdiv_not_inSignedRange_iff_intMin_negOne,
  `Toy.MachInt.nv_ult_add_right_iff_uaddOverflow_eq,
  `Toy.MachInt.nv_ult_add_right_of_noUAddOverflow,
  `Toy.MachInt.nv_wrappingShl_eq_mul_twoPow_of_shiftInBounds,
  `Toy.MachInt.nv_wrappingUShr_and_wrappingSShr_of_shiftInBounds,
  `Toy.MachInt.pc_slt_add_one_of_lt_sMax,
  `Toy.MachInt.pc_ult_add_one_of_lt_uMax,
  `Toy.MachInt.reinterpretCast_characterization,
  `Toy.MachInt.slt_add_one_iff_ne_intMax,
  `Toy.MachInt.slt_add_right_iff_saddOverflow_eq,
  `Toy.MachInt.slt_add_right_of_noSAddOverflow,
  `Toy.MachInt.slt_intMax_add_one_intMax_of_posWidth,
  `Toy.MachInt.tdiv_not_inSignedRange_iff_intMin_negOne,
  `Toy.MachInt.ult_add_one_iff_ne_allOnes,
  `Toy.MachInt.ult_add_right_iff_uaddOverflow_eq,
  `Toy.MachInt.ult_add_right_of_noUAddOverflow,
  `Toy.MachInt.ult_allOnes_add_one_allOnes_of_posWidth,
  `Toy.MachInt.widened_identity_holds_without_widthLe,
  `Toy.MachInt.wrappingShl_eq_mul_twoPow_of_shiftInBounds,
  `Toy.MachInt.wrappingUShr_and_wrappingSShr_of_shiftInBounds
]

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
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
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
  IO.println ("REVALIDATION_AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
