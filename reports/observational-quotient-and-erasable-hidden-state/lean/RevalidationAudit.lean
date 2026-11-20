/-
Revalidation audit program for this package.

This file is not part of the `Toy` library target: `lake build` does not compile
it, and nothing in `Toy` imports it. Run it from this directory after
`lake build`:

    lake env lean RevalidationAudit.lean

It prints a single line `REVALIDATION_JSON {...}` whose JSON object has two
fields:

* `decls`: for every non-internal declaration in a module of the `Toy` library
  (module `Toy` or any module whose name starts with `Toy.`), its name, its
  declaration kind, and the axioms it depends on, as computed by
  `Lean.collectAxioms`;
* `stmts`: for every Lean name recorded in `../audit/statements.json`, the
  statement text `toString (repr ci.type)` and the sorted definition-closure
  lines (`name : repr type`, followed by ` := repr value` for non-theorems with a
  value). `REPORT.md` (Evidence, "Statement and closure hashes") defines these
  texts and the SHA-256 fingerprints computed from them.

The program only reads the environment; it declares nothing in `Toy`.
-/
import Lean
import Toy

open Lean Elab Command

/-- Library root modules whose declarations are audited. -/
private def auditRoots : List Name := [`Toy]

/-- Every Lean name recorded in `../audit/statements.json` (65 names). -/
private def recordedNames : List Name := [
  `Toy.Obs.behIgnoresHidden_iff_coversHidden_obsEq,
  `Toy.Obs.behIgnoresHidden_iff_erasable,
  `Toy.Obs.behIgnoresHidden_iff_exists_unwinding_bisim,
  `Toy.Obs.behIgnoresHidden_iff_stepwise_of_obsInjectiveFst,
  `Toy.Obs.bisim_subset_obsEq,
  `Toy.Obs.ce_bisim_subset_obsEq_no_out,
  `Toy.Obs.ce_bisim_subset_obsEq_no_step,
  `Toy.Obs.ce_erase_empty_hidden,
  `Toy.Obs.ce_hom_to_final_no_out,
  `Toy.Obs.ce_hom_to_final_no_step,
  `Toy.Obs.ce_minimal_iso_no_initBeh,
  `Toy.Obs.ce_minimal_iso_no_inj1,
  `Toy.Obs.ce_minimal_iso_no_inj2,
  `Toy.Obs.ce_minimal_iso_no_reach1,
  `Toy.Obs.ce_minimal_iso_no_reach2,
  `Toy.Obs.ce_reachable_maps_onto_minimal_no_initBeh,
  `Toy.Obs.ce_reachable_maps_onto_minimal_no_reach,
  `Toy.Obs.ce_stepwise_erase_no_out,
  `Toy.Obs.ce_stepwise_erase_no_stepFst,
  `Toy.Obs.ce_stepwise_iff_no_obsInjectiveFst,
  `Toy.Obs.ce_stepwise_no_out,
  `Toy.Obs.ce_stepwise_no_stepFst,
  `Toy.Obs.ce_unwinding_no_coversHidden,
  `Toy.Obs.ce_unwinding_no_out,
  `Toy.Obs.ce_unwinding_no_step,
  `Toy.Obs.delayedChannel2_erasable_for_each_fixed_h,
  `Toy.Obs.delayedChannel2_leaks_at_step_two,
  `Toy.Obs.finalMachine_is_final,
  `Toy.Obs.gatedLeak_reachable_erasable_but_not_global,
  `Toy.Obs.hom_to_final_eq_beh,
  `Toy.Obs.isBisim_sameFst_iff,
  `Toy.Obs.iso_without_reachability,
  `Toy.Obs.minimalMachine_spec,
  `Toy.Obs.no_leak_under_stepwise_nondependence,
  `Toy.Obs.no_machine_independent_horizon_certifies_behIgnoresHidden,
  `Toy.Obs.nv_behIgnoresHidden_iff_erasable,
  `Toy.Obs.nv_behIgnoresHidden_iff_exists_unwinding_bisim,
  `Toy.Obs.nv_behIgnoresHidden_iff_stepwise_of_obsInjectiveFst,
  `Toy.Obs.nv_bisim_subset_obsEq,
  `Toy.Obs.nv_delayedChannel2_nontrivial,
  `Toy.Obs.nv_finalMachine_is_final,
  `Toy.Obs.nv_hom_to_final_eq_beh,
  `Toy.Obs.nv_isBisim_sameFst_iff,
  `Toy.Obs.nv_minimalMachine_spec,
  `Toy.Obs.nv_no_leak_under_stepwise_nondependence,
  `Toy.Obs.nv_no_machine_independent_horizon,
  `Toy.Obs.nv_obsEq_is_greatest_bisim,
  `Toy.Obs.nv_reachable_behInjective_iso,
  `Toy.Obs.nv_reachable_maps_onto_minimalMachine,
  `Toy.Obs.nv_redundantTagMachine_nontrivial,
  `Toy.Obs.nv_stepwise_nondependence_implies_behIgnoresHidden,
  `Toy.Obs.nv_stepwise_nondependence_preserves_beh,
  `Toy.Obs.nv_unwinding_bisim_implies_behIgnoresHidden,
  `Toy.Obs.obsEq_is_greatest_bisim,
  `Toy.Obs.pc_bounded_horizon_with_step_consistency,
  `Toy.Obs.pc_leak_when_stepFst_dropped,
  `Toy.Obs.pc_machine_dependent_horizon_detects_leak,
  `Toy.Obs.reachable_behInjective_iso,
  `Toy.Obs.reachable_maps_onto_minimalMachine,
  `Toy.Obs.redundantTagMachine_erasable_despite_step_dependence,
  `Toy.Obs.redundantTag_has_other_hom,
  `Toy.Obs.stepwise_nondependence_implies_behIgnoresHidden,
  `Toy.Obs.stepwise_nondependence_preserves_beh,
  `Toy.Obs.toMinimalQuotient_injective_iff,
  `Toy.Obs.unwinding_bisim_implies_behIgnoresHidden
]

/-- Whether `n` is declared in a module of the audited library. -/
private def inLibrary (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => auditRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

/-- Definition closure: library constants reachable from `todo` through types,
values of non-theorems, and constructors of inductive types. -/
private partial def libClosure (env : Environment) (todo : List Name) (acc : NameSet) :
    NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLibrary env n then libClosure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => libClosure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      libClosure env (cs ++ rest) acc

/-- One closure line: `name : repr type`, plus ` := repr value` for a
non-theorem with a value. -/
private def closureLine (env : Environment) (c : Name) : String :=
  match env.find? c with
  | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
      (match cc.value? (allowOpaque := true) with
       | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
       | none => "")
  | none => c.toString

private def declKind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, ci) in env.constants.toList do
    if inLibrary env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString),
        ("kind", toJson (declKind ci)), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in recordedNames do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := libClosure env ci.type.getUsedConstants.toList {}
      let lines := (cl.toList.map (closureLine env)).toArray.qsort (· < ·)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))), ("closure", toJson lines)])
  IO.println ("REVALIDATION_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
