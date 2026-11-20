/-
Revalidation audit for the `ToySemType` library (not part of the library target).

Run from this directory after `lake build`:

    lake env lean RevalidationAudit.lean

It prints one line `REVALIDATION_AUDIT_JSON {...}` containing
  * `decls`: every non-internal declaration of the `ToySemType` modules with the
    axioms it depends on (computed by `Lean.collectAxioms`);
  * `stmts`: for every Lean name referenced by `results.json` (`cards`) and for the
    supporting boundary theorems cited in the cards' prose (`boundary`), the Lean
    `repr` of its type and its definition closure: the type (and, for
    non-theorems, the value) of every `ToySemType` constant reachable from the
    statement, with theorem bodies excluded, one `name : type [:= value]` line
    per constant, sorted.
The statement hash is the SHA-256 of the type `repr`; the closure hash is the
SHA-256 of the sorted closure lines joined by newlines.
-/
import Lean
import ToySemType
open Lean Elab Command

private def pkgRoots : List Name := [`ToySemType]
private def cardNames : List Name := [
  `Toy.SemType.V_std_mono,
  `Toy.SemType.V_std_mono_hyp_tight,
  `Toy.SemType.V_std_mono_nonvacuous,
  `Toy.SemType.V_std_mono_val_hyp_tight,
  `Toy.SemType.adequacy_nil_ctx_hyp_tight,
  `Toy.SemType.adequacy_nonvacuous,
  `Toy.SemType.adequacy_semTyped_hyp_tight,
  `Toy.SemType.adequacy_semTyped_nil_safe,
  `Toy.SemType.anyLoc_breaks_fundamental,
  `Toy.SemType.cast_literal_safe_but_not_semTyped,
  `Toy.SemType.cast_of_int_var_not_semTyped,
  `Toy.SemType.cast_of_int_var_not_semTyped_nonvacuous,
  `Toy.SemType.cast_of_int_var_not_semTyped_of_closureEnforcesValues_of_hasInvalidRef,
  `Toy.SemType.cast_of_int_var_semTyped_anyLoc_ref,
  `Toy.SemType.cast_of_int_var_semTyped_safetyOnly,
  `Toy.SemType.checkedRead_applied_semTyped,
  `Toy.SemType.checkedRead_client_hyp_tight,
  `Toy.SemType.checkedRead_hasType_clients_safe,
  `Toy.SemType.checkedRead_not_hasType,
  `Toy.SemType.checkedRead_semTyped,
  `Toy.SemType.checkedRead_single_var_ctx_tight,
  `Toy.SemType.client_hyp_tight,
  `Toy.SemType.forgedRead_unsafe_ill_typed,
  `Toy.SemType.fundamental_hasType_hyp_tight,
  `Toy.SemType.fundamental_hasType_semTyped,
  `Toy.SemType.fundamental_nonvacuous,
  `Toy.SemType.hasType_client_semTyped_lib_nonvacuous,
  `Toy.SemType.hasType_client_semTyped_lib_safe,
  `Toy.SemType.hasType_closed_safe,
  `Toy.SemType.lib_hyp_tight,
  `Toy.SemType.linking_interface_match_tight,
  `Toy.SemType.linking_lib_nil_ctx_tight,
  `Toy.SemType.linking_single_var_ctx_tight,
  `Toy.SemType.linking_structure_nonvacuous,
  `Toy.SemType.nonKripke_breaks_closed_encapsulation,
  `Toy.SemType.nonKripke_breaks_monotonicity_and_fundamental,
  `Toy.SemType.safetyOnly_breaks_fundamental_and_encapsulation,
  `Toy.SemType.safetyOnly_breaks_let_compat,
  `Toy.SemType.safetyOnly_nil_ctx_hyp_tight,
  `Toy.SemType.safetyOnly_semTyped_nil_iff_safe,
  `Toy.SemType.safetyOnly_semTyped_nil_iff_safe_nonvacuous,
  `Toy.SemType.semTyped_client_semTyped_lib_safe,
  `Toy.SemType.semTyped_let_compat,
  `Toy.SemType.semTyped_let_compat_nonvacuous,
  `Toy.SemType.synVal_rejects_checkedRead,
  `Toy.SemType.typing_relation_deriving_cast_of_int_var_unsound,
  `Toy.SemType.typing_relation_hyp_tight,
  `Toy.SemType.typing_relation_nonvacuous,
  `Toy.SemType.valuesOnly_adequacy_fails]
private def boundaryNames : List Name := [
  `Toy.SemType.V_std_rejects_open_dead_lam,
  `Toy.SemType.captureRef_safeAndIn_synVal,
  `Toy.SemType.cellBoundRead_callWith7_safe,
  `Toy.SemType.cellBoundRead_not_semTyped,
  `Toy.SemType.checkedClient_semTyped_safe_not_hasType,
  `Toy.SemType.probeCellZero_not_semTyped_nonKripke_nil,
  `Toy.SemType.read_cast_zero_semTyped_ref_ctx,
  `Toy.SemType.restrictedCastRule_sound,
  `Toy.SemType.safe_of_reaches_value,
  `Toy.SemType.semTyped_nil_open_dead_var,
  `Toy.SemType.sizeZeroOrForged_safe_nil_not_semTyped,
  `Toy.SemType.synVal_pos,
  `Toy.SemType.uncheckedRead_not_semTyped,
  `Toy.SemType.semTyped_lam_compat_needs_closedAt,
  `Toy.SemType.nonKripke_semTyped_client_nil_safe,
  `Toy.SemType.nonKripke_breaks_open_let_compat,
  `Toy.SemType.synVal_iff_isValue_and_hasTypeStore,
  `Toy.SemType.cast_of_int_var_not_semTyped_anyLoc_nonRef]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => pkgRoots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
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

private def stmtJson (env : Environment) (role : String) (n : Name) : Json :=
  match env.find? n with
  | none => Json.mkObj [("name", toJson n.toString), ("role", toJson role), ("missing", toJson true)]
  | some ci =>
    let cl := closure env (ci.type.getUsedConstants.toList) {}
    let clTxt := cl.toList.map (fun c =>
      match env.find? c with
      | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
          (match cc.value? (allowOpaque := true) with
           | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
           | none => "")
      | none => c.toString)
    Json.mkObj [("name", toJson n.toString), ("role", toJson role),
      ("type_repr", toJson (toString (repr ci.type))),
      ("closure", toJson (clTxt.toArray.qsort (· < ·)))]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString),
        ("axioms", toJson ((axs.map Name.toString).qsort (· < ·)))])
  let stmts := (cardNames.map (stmtJson env "cards") ++ boundaryNames.map (stmtJson env "boundary")).toArray
  IO.println ("REVALIDATION_AUDIT_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
