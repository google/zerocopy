import Lean
import ToyTransmute

/-!
# Revalidation audit (standalone; not part of the library)

Run from the project root after `lake build`:

    lake env lean support/RevalidationAudit.lean

It prints one line `REVALIDATION_JSON {...}` with

* `decls`: every declaration of every `ToyTransmute` module with the axioms it depends on
  (as computed by `Lean.collectAxioms`), and
* `stmts`: for every Lean name referenced by a result card in `results.json` (main theorems,
  counterexamples, non-vacuity witnesses and positive controls), the `repr` of its type and its
  definition closure: one line `name : repr type [:= repr value]` for each package constant
  reachable from that type (definition values included, theorem proofs excluded), sorted.

The statement hash of a name is the SHA-256 of its `type_repr`; the closure hash is the SHA-256
of its closure lines joined by newlines; the closure size is the number of lines. The
`Revalidation` section of the report gives a short Python program that recomputes these hashes
and compares them, and the axiom lists, with `audit/statements.json` and `audit/axioms.json`.
-/

open Lean Elab Command

private def revalRoots : List Name := [`ToyTransmute]

private def revalNames : List Name := [
  `Toy.Transmute.boolV_to_byteV_im_sound_without_writes_unsound_with_dst_writes,
  `Toy.Transmute.boolV_to_byteV_mut_violating_run,
  `Toy.Transmute.boolV_to_byteV_value_and_shared_sound,
  `Toy.Transmute.byteV_to_boolV_unsound_even_by_value,
  `Toy.Transmute.checkedSound_mutProtocol_iff_satisfiable_meet_imp_includes_rev,
  `Toy.Transmute.checkedSound_mut_escapes_impossibility,
  `Toy.Transmute.checkedSound_mut_needs_includes_rev,
  `Toy.Transmute.checkedSound_mut_nonvacuous,
  `Toy.Transmute.checkedSound_mut_rhs_needs_satisfiable_meet_guard,
  `Toy.Transmute.checkedSound_sharedIM_iff_satisfiable_meet_imp_srcWrites_includes_and_dstWrites_includes_rev,
  `Toy.Transmute.checkedSound_sharedIM_needs_dstWrites_includes_rev,
  `Toy.Transmute.checkedSound_sharedIM_needs_srcWrites_includes,
  `Toy.Transmute.checkedSound_sharedIM_nonvacuous,
  `Toy.Transmute.checkedSound_sharedIM_rhs_needs_dstWrites_guard,
  `Toy.Transmute.checkedSound_sharedIM_rhs_needs_satisfiable_meet_guard,
  `Toy.Transmute.checkedSound_sharedIM_rhs_needs_srcWrites_guard,
  `Toy.Transmute.checkedSound_sharedProtocol,
  `Toy.Transmute.checkedSound_sharedProtocol_nonvacuous,
  `Toy.Transmute.checkedSound_valueProtocol,
  `Toy.Transmute.checkedSound_valueProtocol_nonvacuous,
  `Toy.Transmute.mutSound_boolV_boolV',
  `Toy.Transmute.mutSound_eq_needs_satisfiable,
  `Toy.Transmute.mutSound_eq_nonvacuous,
  `Toy.Transmute.mutSound_exact_nonvacuous,
  `Toy.Transmute.mutSound_from_meet_fails_example,
  `Toy.Transmute.mutSound_from_meet_left_iff_includes_of_satisfiable_meet,
  `Toy.Transmute.mutSound_from_meet_needs_joint_satisfiable,
  `Toy.Transmute.mutSound_from_meet_needs_satisfiable,
  `Toy.Transmute.mutSound_from_meet_nonvacuous,
  `Toy.Transmute.mutSound_iff_includes_and_satisfiable_imp_includes_rev,
  `Toy.Transmute.mutSound_iff_sharedIMSound_dstWrites,
  `Toy.Transmute.mutSound_iff_sharedIM_needs_dstWrites,
  `Toy.Transmute.mutSound_iff_sharedIM_nonvacuous,
  `Toy.Transmute.mutSound_iff_validityEq_of_satisfiable,
  `Toy.Transmute.mutSound_needs_includes_rev,
  `Toy.Transmute.mutSound_rhs_needs_satisfiable_guard,
  `Toy.Transmute.mutSound_symm_needs_mutSound,
  `Toy.Transmute.mutSound_symm_needs_satisfiable,
  `Toy.Transmute.mutSound_symm_nonvacuous,
  `Toy.Transmute.mutSound_symm_of_satisfiable,
  `Toy.Transmute.mutSound_to_join_left_iff_includes_rev_of_satisfiable,
  `Toy.Transmute.mutSound_to_join_needs_includes_rev,
  `Toy.Transmute.mutSound_to_join_needs_satisfiable,
  `Toy.Transmute.mutSound_to_join_nonvacuous,
  `Toy.Transmute.mutSound_trans,
  `Toy.Transmute.mutSound_trans_needs_first,
  `Toy.Transmute.mutSound_trans_needs_second,
  `Toy.Transmute.mutSound_trans_nonvacuous,
  `Toy.Transmute.mutSound_trans_uninhabited_nonvacuous,
  `Toy.Transmute.not_mutSound_needs_not_validityEq,
  `Toy.Transmute.not_mutSound_needs_satisfiable,
  `Toy.Transmute.not_mutSound_nonvacuous,
  `Toy.Transmute.not_mutSound_of_satisfiable_of_not_validityEq,
  `Toy.Transmute.not_mutSound_positive_control_weaker_casts,
  `Toy.Transmute.not_sharedSound_byteV_boolV,
  `Toy.Transmute.not_valueSound_byteV_boolV,
  `Toy.Transmute.sharedIMSound_dstWrites_iff_validityEq_of_satisfiable,
  `Toy.Transmute.sharedIMSound_eq_needs_dstWrites,
  `Toy.Transmute.sharedIMSound_eq_needs_satisfiable,
  `Toy.Transmute.sharedIMSound_eq_nonvacuous,
  `Toy.Transmute.sharedIMSound_exact_nonvacuous,
  `Toy.Transmute.sharedIMSound_iff_includes_and_dstWrites_imp_satisfiable_imp_includes_rev,
  `Toy.Transmute.sharedIMSound_needs_includes,
  `Toy.Transmute.sharedIMSound_needs_includes_canonical,
  `Toy.Transmute.sharedIMSound_needs_includes_rev_canonical,
  `Toy.Transmute.sharedIMSound_noDstWrites_iff_includes,
  `Toy.Transmute.sharedIMSound_noDst_needs_noDstWrites,
  `Toy.Transmute.sharedIMSound_noDst_nonvacuous,
  `Toy.Transmute.sharedIMSound_noDst_trans_strict_nonvacuous,
  `Toy.Transmute.sharedIMSound_rhs_needs_dstWrites_guard,
  `Toy.Transmute.sharedIMSound_rhs_needs_satisfiable_guard,
  `Toy.Transmute.sharedIMSound_trans,
  `Toy.Transmute.sharedIMSound_trans_needs_first,
  `Toy.Transmute.sharedIMSound_trans_needs_second,
  `Toy.Transmute.sharedIMSound_trans_nonvacuous,
  `Toy.Transmute.sharedIMSound_trans_uninhabited_nonvacuous,
  `Toy.Transmute.sharedSound_boolV_byteV,
  `Toy.Transmute.sharedSound_from_meet_left,
  `Toy.Transmute.sharedSound_from_meet_left_nonvacuous,
  `Toy.Transmute.sharedSound_from_meet_right,
  `Toy.Transmute.sharedSound_from_meet_right_nonvacuous,
  `Toy.Transmute.sharedSound_iff_includes,
  `Toy.Transmute.sharedSound_iff_includes_nonvacuous,
  `Toy.Transmute.sharedSound_join_iff,
  `Toy.Transmute.sharedSound_join_iff_needs_left,
  `Toy.Transmute.sharedSound_join_iff_needs_right,
  `Toy.Transmute.sharedSound_join_iff_nonvacuous,
  `Toy.Transmute.sharedSound_meet_iff,
  `Toy.Transmute.sharedSound_meet_iff_needs_left,
  `Toy.Transmute.sharedSound_meet_iff_needs_right,
  `Toy.Transmute.sharedSound_meet_iff_nonvacuous,
  `Toy.Transmute.sharedSound_of_mutSound,
  `Toy.Transmute.sharedSound_of_valueSound,
  `Toy.Transmute.sharedSound_to_join_left,
  `Toy.Transmute.sharedSound_to_join_left_nonvacuous,
  `Toy.Transmute.sharedSound_to_join_right,
  `Toy.Transmute.sharedSound_to_join_right_nonvacuous,
  `Toy.Transmute.sharedSound_trans,
  `Toy.Transmute.sharedSound_trans_needs_first,
  `Toy.Transmute.sharedSound_trans_needs_second,
  `Toy.Transmute.sharedSound_trans_nonvacuous,
  `Toy.Transmute.valueSound_boolV_byteV,
  `Toy.Transmute.valueSound_iff_includes,
  `Toy.Transmute.valueSound_iff_includes_nonvacuous,
  `Toy.Transmute.valueSound_of_sharedSound,
  `Toy.Transmute.valueSound_trans,
  `Toy.Transmute.valueSound_trans_needs_first,
  `Toy.Transmute.valueSound_trans_needs_second,
  `Toy.Transmute.valueSound_trans_nonvacuous
]

private def revalInPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    revalRoots.any (fun r => r.isPrefixOf m)
  | none => false

private partial def revalClosure (env : Environment) (todo : List Name) (acc : NameSet) :
    NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !revalInPkg env n then revalClosure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => revalClosure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      revalClosure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if revalInPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in revalNames do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := revalClosure env (ci.type.getUsedConstants.toList) {}
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
  IO.println ("REVALIDATION_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
