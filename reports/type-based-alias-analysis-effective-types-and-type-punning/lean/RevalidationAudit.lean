/-
Revalidation audit program (not part of the `ToyTbaa` library target).
Run from this directory after `lake build`:  lake env lean RevalidationAudit.lean
It prints one line `REVALIDATE_JSON {...}` with the axioms of every library declaration and,
for every name recorded in `../audit/statements.json`, the `repr` of its type and the sorted
closure lines that are hashed (see REPORT.md, Evidence and Revalidation).
-/
import Lean
import ToyTbaa
open Lean Elab Command

private def roots : List Name := [`ToyTbaa]
private def wanted : List Name := [`Toy.Tbaa.AllocatedOn,
  `Toy.Tbaa.Allows,
  `Toy.Tbaa.Beh,
  `Toy.Tbaa.Byte,
  `Toy.Tbaa.Cell,
  `Toy.Tbaa.Companions.sink_load_below_store_witness_runs,
  `Toy.Tbaa.Companions.store_store_swap_witness_runs,
  `Toy.Tbaa.Companions.store_swap_scheme_fails_at_zero,
  `Toy.Tbaa.Companions.valsAt_unallocated_example,
  `Toy.Tbaa.Compat,
  `Toy.Tbaa.CopyBytesOk,
  `Toy.Tbaa.DeclOk,
  `Toy.Tbaa.DeclaredOn,
  `Toy.Tbaa.ECfg,
  `Toy.Tbaa.Eff,
  `Toy.Tbaa.Eff.isDecl,
  `Toy.Tbaa.Eff.tag,
  `Toy.Tbaa.Examples.allocatedOn_admits,
  `Toy.Tbaa.Examples.allocatedOn_rejects,
  `Toy.Tbaa.Examples.byte_loop_copy_does_not_transfer_effective_type,
  `Toy.Tbaa.Examples.declaredOn_admits,
  `Toy.Tbaa.Examples.declaredOn_rejects,
  `Toy.Tbaa.Examples.erase_example,
  `Toy.Tbaa.Examples.f32_valid_any_pattern,
  `Toy.Tbaa.Examples.memcpyLoadOk_admits,
  `Toy.Tbaa.Examples.memcpyLoadOk_rejects,
  `Toy.Tbaa.Examples.noCommonLeaf_admits,
  `Toy.Tbaa.Examples.noCommonLeaf_non_u8_struct_instances,
  `Toy.Tbaa.Examples.noCommonLeaf_rejects,
  `Toy.Tbaa.Examples.noCommonLeaf_table,
  `Toy.Tbaa.Examples.ones4,
  `Toy.Tbaa.Examples.pair_byte4_not_u32,
  `Toy.Tbaa.Examples.pair_layout,
  `Toy.Tbaa.Examples.punIntoDeclSt,
  `Toy.Tbaa.Examples.rangesDisjoint_admits,
  `Toy.Tbaa.Examples.rangesDisjoint_rejects,
  `Toy.Tbaa.Examples.readableAt_admits,
  `Toy.Tbaa.Examples.readableAt_rejects,
  `Toy.Tbaa.Examples.receivesAt_admits,
  `Toy.Tbaa.Examples.receivesAt_rejects,
  `Toy.Tbaa.Examples.refines_admits,
  `Toy.Tbaa.Examples.refines_rejects,
  `Toy.Tbaa.Examples.reorderSound_admits,
  `Toy.Tbaa.Examples.reorderSound_rejects,
  `Toy.Tbaa.Examples.stdCompat_admits,
  `Toy.Tbaa.Examples.stdCompat_rejects,
  `Toy.Tbaa.Examples.stepE_allocated_retype_defined,
  `Toy.Tbaa.Examples.stepE_byte_read_defined,
  `Toy.Tbaa.Examples.stepE_declared_store_mismatch_ub,
  `Toy.Tbaa.Examples.stepE_memcpy_copies_type_defined,
  `Toy.Tbaa.Examples.stepE_memcpy_copy_punning_ub,
  `Toy.Tbaa.Examples.stepE_memcpy_into_declared_defined,
  `Toy.Tbaa.Examples.stepE_pair_load_from_member_stores_defined,
  `Toy.Tbaa.Examples.stepE_pair_member_access,
  `Toy.Tbaa.Examples.stepE_punning_ub,
  `Toy.Tbaa.Examples.stepE_same_type_defined,
  `Toy.Tbaa.Examples.stepE_unallocated_ub,
  `Toy.Tbaa.Examples.stepU_punning_defined,
  `Toy.Tbaa.Examples.stepU_unallocated_ub,
  `Toy.Tbaa.Examples.strictCompat_admits,
  `Toy.Tbaa.Examples.strictCompat_rejects_byte,
  `Toy.Tbaa.Examples.typeFaults_admits,
  `Toy.Tbaa.Examples.typeFaults_rejects,
  `Toy.Tbaa.Examples.typeFaults_same_type_nonstandard_cfg,
  `Toy.Tbaa.Examples.u32_invalid_short,
  `Toy.Tbaa.Examples.uDefined_admits,
  `Toy.Tbaa.Examples.uDefined_rejects,
  `Toy.Tbaa.Examples.valsAt_example,
  `Toy.Tbaa.Fault,
  `Toy.Tbaa.Final,
  `Toy.Tbaa.Final.outcome,
  `Toy.Tbaa.Instr,
  `Toy.Tbaa.Instr.isLoad,
  `Toy.Tbaa.Mem,
  `Toy.Tbaa.MemcpyLoadOk,
  `Toy.Tbaa.NoCommonLeaf,
  `Toy.Tbaa.Outcome,
  `Toy.Tbaa.Outcome.trace,
  `Toy.Tbaa.RangesDisjoint,
  `Toy.Tbaa.ReadableAt,
  `Toy.Tbaa.ReceivesAt,
  `Toy.Tbaa.Refines,
  `Toy.Tbaa.Reg,
  `Toy.Tbaa.ReorderSound,
  `Toy.Tbaa.ReorderSoundFrom,
  `Toy.Tbaa.Results.agreement_needs_no_type_fault,
  `Toy.Tbaa.Results.allocHoistSrc,
  `Toy.Tbaa.Results.allocHoistTgt,
  `Toy.Tbaa.Results.behE_eq_behU_iff,
  `Toy.Tbaa.Results.behE_eq_behU_iff_nonvacuous,
  `Toy.Tbaa.Results.behE_eq_behU_iff_not_typeFaults_of_uDefined,
  `Toy.Tbaa.Results.behE_eq_behU_nonvacuous,
  `Toy.Tbaa.Results.behE_eq_behU_of_not_typeFaults,
  `Toy.Tbaa.Results.behE_not_refines_behU_iff,
  `Toy.Tbaa.Results.behE_not_refines_behU_iff_typeFaults_of_uDefined,
  `Toy.Tbaa.Results.behE_not_refines_behU_of_uDefined_nonvacuous,
  `Toy.Tbaa.Results.behE_not_refines_behU_without_uDefined,
  `Toy.Tbaa.Results.behE_refines_behU_masked_instance,
  `Toy.Tbaa.Results.behU_erase_refines_behE,
  `Toy.Tbaa.Results.behU_refines_behE_strict_instance,
  `Toy.Tbaa.Results.byte_copy_defined_forces_byte_hoist_unsound,
  `Toy.Tbaa.Results.byte_copy_defined_nonvacuous,
  `Toy.Tbaa.Results.byte_copy_u8_case_is_same_type,
  `Toy.Tbaa.Results.byte_dichotomy_not_exclusive_for_pair,
  `Toy.Tbaa.Results.byte_hoist_refines_with_unchecked_memcpy,
  `Toy.Tbaa.Results.copyIntoDeclF32,
  `Toy.Tbaa.Results.declPairThenFresh,
  `Toy.Tbaa.Results.declared_and_allocated_preconditions_incomparable,
  `Toy.Tbaa.Results.declared_store_mismatch_diverges_without_loads,
  `Toy.Tbaa.Results.hoist_E_needs_distinct_registers,
  `Toy.Tbaa.Results.hoist_E_needs_load_ne_u8,
  `Toy.Tbaa.Results.hoist_E_needs_noCommonLeaf,
  `Toy.Tbaa.Results.hoist_E_needs_store_ne_u8,
  `Toy.Tbaa.Results.hoist_E_needs_store_ne_u8_on_declared,
  `Toy.Tbaa.Results.hoist_E_nonvacuous,
  `Toy.Tbaa.Results.hoist_E_nonvacuous_struct,
  `Toy.Tbaa.Results.hoist_U_disjoint_instance,
  `Toy.Tbaa.Results.hoist_U_needs_disjoint_ranges,
  `Toy.Tbaa.Results.hoist_U_needs_distinct_registers,
  `Toy.Tbaa.Results.hoist_U_witness_refines_under_E_or_disjoint,
  `Toy.Tbaa.Results.hoist_load_above_store_same_addr_unsound_U,
  `Toy.Tbaa.Results.hoist_load_above_store_sound_E_of_noCommonLeaf_of_ne_u8,
  `Toy.Tbaa.Results.hoist_load_above_store_sound_U_of_disjoint_ranges,
  `Toy.Tbaa.Results.hoist_unsound_U_instance,
  `Toy.Tbaa.Results.memcpy_corollary_nonvacuous,
  `Toy.Tbaa.Results.memcpy_overlap_defined_examples,
  `Toy.Tbaa.Results.memcpy_then_load_needs_readable_source,
  `Toy.Tbaa.Results.memcpy_then_load_needs_receiving_destination,
  `Toy.Tbaa.Results.memcpy_then_load_nonvacuous,
  `Toy.Tbaa.Results.memcpy_then_typed_load_defined_E_iff,
  `Toy.Tbaa.Results.memcpy_then_typed_load_defined_E_of_readable_of_receives,
  `Toy.Tbaa.Results.mixedCompat,
  `Toy.Tbaa.Results.no_type_criterion_at_one_site_needs_premise,
  `Toy.Tbaa.Results.no_type_criterion_licenses_same_addr_hoist_U,
  `Toy.Tbaa.Results.no_type_criterion_licenses_same_addr_hoist_U_at_one_site,
  `Toy.Tbaa.Results.no_type_criterion_needs_premise,
  `Toy.Tbaa.Results.no_type_criterion_premises_satisfiable,
  `Toy.Tbaa.Results.ones4,
  `Toy.Tbaa.Results.partialOverlapPunSt,
  `Toy.Tbaa.Results.readable_source_not_necessary,
  `Toy.Tbaa.Results.same_register_premise_refutes_disjoint_hoist_U,
  `Toy.Tbaa.Results.sink_declared_needs_distinct_registers,
  `Toy.Tbaa.Results.sink_declared_needs_load_ne_u8,
  `Toy.Tbaa.Results.sink_declared_needs_noCommonLeaf,
  `Toy.Tbaa.Results.sink_declared_needs_store_ne_u8,
  `Toy.Tbaa.Results.sink_declared_nonvacuous,
  `Toy.Tbaa.Results.sink_declared_nonvacuous_struct,
  `Toy.Tbaa.Results.sink_load_below_store_not_sound_E,
  `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_declared_of_noCommonLeaf_of_ne_u8,
  `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_disjoint_ranges,
  `Toy.Tbaa.Results.sink_load_below_store_sound_E_of_store_range_declared,
  `Toy.Tbaa.Results.sink_needs_declared_storage,
  `Toy.Tbaa.Results.store_store_declared_needs_first_ne_u8,
  `Toy.Tbaa.Results.store_store_declared_needs_noCommonLeaf,
  `Toy.Tbaa.Results.store_store_declared_needs_second_ne_u8,
  `Toy.Tbaa.Results.store_store_declared_nonvacuous,
  `Toy.Tbaa.Results.store_store_declared_nonvacuous_struct,
  `Toy.Tbaa.Results.store_store_needs_declared_storage,
  `Toy.Tbaa.Results.store_store_reorder_not_sound_E,
  `Toy.Tbaa.Results.store_store_reorder_sound_E_of_declared_of_noCommonLeaf_of_ne_u8,
  `Toy.Tbaa.Results.store_store_reorder_sound_E_of_disjoint_ranges,
  `Toy.Tbaa.Results.store_store_reorder_sound_E_of_second_declared,
  `Toy.Tbaa.Results.store_swap_scheme_nonvacuous,
  `Toy.Tbaa.Results.store_swap_scheme_sound_on_declared_not_on_allocated,
  `Toy.Tbaa.Results.strict_copy_ub_and_byte_hoist_refines,
  `Toy.Tbaa.Results.strict_typed_load_above_byte_store_not_refines,
  `Toy.Tbaa.Results.twos4,
  `Toy.Tbaa.Results.typeFault_masked_by_later_base_fault,
  `Toy.Tbaa.Results.typeFault_unmasked_despite_later_base_fault,
  `Toy.Tbaa.Results.uWit,
  `Toy.Tbaa.Scalar,
  `Toy.Tbaa.St,
  `Toy.Tbaa.St.withRegs,
  `Toy.Tbaa.Step,
  `Toy.Tbaa.TagsOk,
  `Toy.Tbaa.Ty,
  `Toy.Tbaa.Ty.Valid,
  `Toy.Tbaa.Ty.leafAt,
  `Toy.Tbaa.Ty.leaves,
  `Toy.Tbaa.Ty.size,
  `Toy.Tbaa.TypeFaults,
  `Toy.Tbaa.UDefined,
  `Toy.Tbaa.UMem,
  `Toy.Tbaa.USt,
  `Toy.Tbaa.Val,
  `Toy.Tbaa.copyCell,
  `Toy.Tbaa.copyFrom,
  `Toy.Tbaa.declPairSt,
  `Toy.Tbaa.declSt,
  `Toy.Tbaa.erase,
  `Toy.Tbaa.exec,
  `Toy.Tbaa.freshAt,
  `Toy.Tbaa.memcpyLoadCheck,
  `Toy.Tbaa.objSt,
  `Toy.Tbaa.readRange,
  `Toy.Tbaa.regs2,
  `Toy.Tbaa.reorderSound_refl,
  `Toy.Tbaa.runFrom,
  `Toy.Tbaa.stdCfg,
  `Toy.Tbaa.stdCompat,
  `Toy.Tbaa.stepE,
  `Toy.Tbaa.stepU,
  `Toy.Tbaa.storeCell,
  `Toy.Tbaa.strictCompat,
  `Toy.Tbaa.typeFaultsB,
  `Toy.Tbaa.updRange,
  `Toy.Tbaa.updReg,
  `Toy.Tbaa.valsAt]

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
