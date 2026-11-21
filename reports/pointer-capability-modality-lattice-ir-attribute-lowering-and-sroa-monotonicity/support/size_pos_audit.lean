/-
Kernel dependency audit: for each listed theorem, whether its proof depends,
transitively through constants of the package, on the structure field
`Toy.Modality.Shape.size_pos` (positive pointee size), used either as a
constant or as a structure projection.

Run from the Lake project directory `lean/`:
  lake env lean ../support/size_pos_audit.lean
-/
import Lean
import Toy
open Lean Elab Command

def valOf : ConstantInfo → Option Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | _ => none

partial def usesSizePos (env : Environment) : List Name → NameSet → Bool
  | [], _ => false
  | n :: rest, seen =>
    if seen.contains n then usesSizePos env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => usesSizePos env rest seen
    | some ci =>
      let isSP : Expr → Bool := fun x => match x with
        | .proj `Toy.Modality.Shape 2 _ => true
        | .const c _ => c == `Toy.Modality.Shape.size_pos
        | _ => false
      let hit := (ci.type.find? isSP).isSome ||
        (match valOf ci with | some v => (v.find? isSP).isSome | none => false)
      if hit then true else
      let cs := ci.type.getUsedConstants ++
        (match valOf ci with | some v => v.getUsedConstants | none => #[])
      let cs := cs.toList.filter (fun c => (`Toy).isPrefixOf c)
      usesSizePos env (cs ++ rest) seen

elab "#size_pos_audit" ids:ident* : command => do
  let env ← getEnv
  for i in ids do
    let full := `Toy.Modality ++ i.getId
    logInfo m!"SIZE_POS_AUDIT {i.getId} {usesSizePos env [full] {}}"

#size_pos_audit mod_bounded_lattice cl_closure_operator_and_closed_sublattice den_antitone den_sup_iff
  den_cl_iff den_subset_iff_le_cl den_subset_iff_le_of_closed kindBase_best tRelax_best
  transformers_respect_den transformer_dropped_atoms_can_fail compSound_iff_transformerSound_and_deep
  compSound_on_docTy_not_imply_transformerSound shallow_relaxer_leaves_nested_promises
  comp_tRelax_deep_eq_req lower_sound lower_best_iff lower_unique
  alphaSet_gammaDual_galois_and_lower_eq_alphaSet_den polarity_galois lower_no_left_adjoint_and_arg_no_right_adjoint
  stronger_arg_lowerings_counterexamples refFull_arg_lowering_not_sound_at_return
  entry_deref_of_tCell_refFull_not_sound_at_return tRelax_arg_lowering_eq_ret_lowering
  liftOpt_sound_of_noneVal_zero liftOpt_best_iff liftOpt_sound_iff_noneVal_eq_zero_of_isNiche
  liftOpt_unsound_at_niche_one lift_nonnull_dereferenceable_unsound_at_null
  scalarize_refines_iff_declared_le_posMod sroa_hoist_out_of_manuallyDrop_counterexample
  repairs_sound repairs_exact_and_retype_total repair_policies_acceptance_hierarchy
