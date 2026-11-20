import Lean
import Toy

/-!
# Standalone Kernel Axiom and Statement-Closure Audit (`RevalidationAudit`)

Outside the `Toy` library target (`lakefile.toml` builds only `Toy`), this file
can be run directly via `lake env lean RevalidationAudit.lean` after `lake build`
to emit a single JSON line (`REVALIDATE_JSON {...}`) containing:
1. `decls`: every non-internal declaration in the `Toy` module hierarchy together
   with its transitive kernel dependencies from `Lean.collectAxioms`; and
2. `stmts`: for each of the 81 card-referenced declarations, the `repr` string of
   its kernel type (`type_repr`) and the sorted `Toy.*` definition closure
   (`closure`, excluding theorem proof bodies).
-/

open Lean Elab Command

private def roots : List Name := [`Toy]

private def wanted : List Name := [
  `Toy.Layout.ce_aligned_size_drop_fields_pow2,
  `Toy.Layout.ce_aligned_size_drop_n_pow2,
  `Toy.Layout.ce_dst_trailing_padding_breaks_naive_prefix_cast,
  `Toy.Layout.ce_heterogeneous_u16_u8_has_trailing_padding,
  `Toy.Layout.ce_heterogeneous_u8_u16_has_padding,
  `Toy.Layout.ce_homogeneous_no_padding_iff_drop_align_pos,
  `Toy.Layout.ce_maxSliceElems_none_drop_elem_pos,
  `Toy.Layout.ce_naive_agrees_fails_short_buffer,
  `Toy.Layout.ce_naive_agrees_fails_zst,
  `Toy.Layout.ce_packed_noop_drop_ge,
  `Toy.Layout.ce_reprCEnum_align_drop_tag_pow2,
  `Toy.Layout.ce_reprCEnum_align_drop_vars_pow2,
  `Toy.Layout.ce_reprCEnum_geometry_drop_vars_pow2,
  `Toy.Layout.ce_reprCEnum_tag_sizing_divergence,
  `Toy.Layout.ce_reprCEnum_tag_sizing_divergence_aligns,
  `Toy.Layout.ce_reprCStruct_align_dvd_drop_fields_pow2,
  `Toy.Layout.ce_reprCStruct_align_dvd_drop_mod_pow2,
  `Toy.Layout.ce_reprCStruct_eq_iff_drop_fields_align_pos,
  `Toy.Layout.ce_reprCStruct_eq_iff_drop_pack_pos,
  `Toy.Layout.ce_reprCStruct_invariants_drop_fields_align_pos,
  `Toy.Layout.ce_reprCStruct_invariants_drop_pack_pos,
  `Toy.Layout.ce_reprIntEnum_align_eq_drop_nonempty,
  `Toy.Layout.ce_reprIntEnum_geometry_drop_nonempty,
  `Toy.Layout.ce_reprIntEnum_geometry_drop_vars_align_pos,
  `Toy.Layout.ce_reprIntEnum_lt_reprCEnum_u8,
  `Toy.Layout.ce_reprInt_le_reprC_drop_tag_pow2,
  `Toy.Layout.ce_reprInt_le_reprC_drop_vars_pow2,
  `Toy.Layout.dstInstantiated_eq_closed_form,
  `Toy.Layout.dstSize_eq_phase_normal_form,
  `Toy.Layout.dstSize_eq_unphased_normal_form_of_dvd,
  `Toy.Layout.dst_no_trailing_padding_all_iff,
  `Toy.Layout.ex_homogeneous_non_dvd_has_padding,
  `Toy.Layout.ex_packed_non_pow2_increases_size,
  `Toy.Layout.maxSliceElems_eq_naive_of_no_trailing_padding,
  `Toy.Layout.maxSliceElems_eq_phase_normal_form_capacity,
  `Toy.Layout.maxSliceElems_none_iff_of_elem_size_pos,
  `Toy.Layout.maxSliceElems_some_iff,
  `Toy.Layout.nv_dstInstantiated_eq_closed_form,
  `Toy.Layout.nv_dst_no_trailing_padding_all_iff,
  `Toy.Layout.nv_maxSliceElems_none_iff_of_elem_size_pos,
  `Toy.Layout.nv_maxSliceElems_some_iff,
  `Toy.Layout.nv_reprCEnum_align_valid_of_pow2,
  `Toy.Layout.nv_reprCEnum_geometry_of_vars_pow2,
  `Toy.Layout.nv_reprCStruct_align_pow2_divides,
  `Toy.Layout.nv_reprCStruct_aligned_preserves_offsets,
  `Toy.Layout.nv_reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2,
  `Toy.Layout.nv_reprCStruct_eq_iff_of_align_pos,
  `Toy.Layout.nv_reprCStruct_homogeneous_no_padding_iff_of_align_pos,
  `Toy.Layout.nv_reprCStruct_invariants_of_align_pos,
  `Toy.Layout.nv_reprCStruct_no_padding_iff,
  `Toy.Layout.nv_reprCStruct_packed_align_le,
  `Toy.Layout.nv_reprCStruct_packed_ge_fields_noop,
  `Toy.Layout.nv_reprCStruct_packed_one_no_padding,
  `Toy.Layout.nv_reprIntEnum_align_eq_reprCEnum_align_of_nonempty,
  `Toy.Layout.nv_reprIntEnum_geometry_of_nonempty_align_pos,
  `Toy.Layout.nv_reprIntEnum_size_le_reprCEnum_size_of_pow2,
  `Toy.Layout.nv_zst_tail_no_max_fitting_elems,
  `Toy.Layout.orderedNonOverlapping_implies_monotone_and_disjoint,
  `Toy.Layout.orderedNonOverlapping_without_length_not_monotone,
  `Toy.Layout.pc_zst_tail_no_max_fitting_elems,
  `Toy.Layout.reprCEnum_align_valid_of_pow2,
  `Toy.Layout.reprCEnum_geometry_of_vars_pow2,
  `Toy.Layout.reprCEnum_tagOffset_zero,
  `Toy.Layout.reprCStruct_align_pow2_divides,
  `Toy.Layout.reprCStruct_aligned_preserves_offsets,
  `Toy.Layout.reprCStruct_aligned_size_eq_alignUp_base_size_of_pow2,
  `Toy.Layout.reprCStruct_eq_iff_of_align_pos,
  `Toy.Layout.reprCStruct_homogeneous_no_padding_iff_of_align_pos,
  `Toy.Layout.reprCStruct_invariants_of_align_pos,
  `Toy.Layout.reprCStruct_no_padding_iff_size_eq_sum,
  `Toy.Layout.reprCStruct_packed_align_le,
  `Toy.Layout.reprCStruct_packed_ge_fields_noop,
  `Toy.Layout.reprCStruct_packed_one_no_padding,
  `Toy.Layout.reprIntEnum_align_eq_reprCEnum_align_of_nonempty,
  `Toy.Layout.reprIntEnum_all_variants_tag_at_zero,
  `Toy.Layout.reprIntEnum_geometry_of_nonempty_align_pos,
  `Toy.Layout.reprIntEnum_size_le_reprCEnum_size_of_pow2,
  `Toy.Layout.reprIntEnum_tagOffset_zero,
  `Toy.Layout.struct_invariants_mutually_independent,
  `Toy.Layout.zst_tail_bounded_max_exists,
  `Toy.Layout.zst_tail_no_max_fitting_elems
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
  IO.println ("REVALIDATE_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
