/-
Axiom and statement audit (not part of the library build)
=========================================================

Run from the `lean/` directory of the package, after `lake build`:

    lake env lean scripts/audit/Audit.lean > /tmp/lens_audit.out
    python3 scripts/audit/check_audit.py /tmp/lens_audit.out ../audit

The program

* fails unless every declaration of the library (modules under `Toy`) depends
  only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and no
  declaration of the library is an axiom or an opaque constant;
* prints, for every Lean name referenced by `../results.json` (results,
  counterexamples, non-vacuity witnesses, positive controls), the axioms it
  depends on, the `repr` of its statement, and the statements and definition
  bodies of all library constants its statement reaches (its definition
  closure; proofs of theorems are not part of the closure).

`check_audit.py` hashes the printed statements and closures with SHA-256 and
compares them, and the per-declaration axiom lists, with the recorded
`audit/statements.json` and `audit/axioms.json`.
-/
import Lean
import Toy

open Lean Elab Command

namespace Toy.Lens.Audit

private def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

private def inLib (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Toy).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inLib env n then closure env rest acc else
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

private def strs (j : Json) : List String :=
  match j with
  | .str s => [s]
  | .arr a => a.toList.filterMap fun x => match x with | .str s => some s | _ => none
  | _ => []

private def cardNames (card : Json) : List String := Id.run do
  let mut out : List String := []
  for k in ["lean", "lean_names", "nonvacuity_witness_lean", "positive_control_lean"] do
    out := out ++ strs (card.getObjValD k)
  match card.getObjValD "hypotheses" with
  | .arr hs => for h in hs do out := out ++ strs (h.getObjValD "counterexample")
  | _ => pure ()
  return out

#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "../results.json"
  let cards ← match Json.parse txt with
    | .ok (.arr a) => pure a
    | _ => throwError "results.json is not a JSON array"
  let names := (cards.toList.flatMap cardNames).eraseDups
  let mut decls : Array Json := #[]
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    if inLib env n && !n.isInternal then
      let axs ← collectAxioms n
      for ax in axs do
        unless allowedAxioms.contains ax do bad := bad.push s!"{n}: {ax}"
      if kindOf ci == "axiom" || kindOf ci == "opaque" then bad := bad.push s!"{n}: declared {kindOf ci}"
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson (kindOf ci)),
        ("axioms", toJson (axs.map Name.toString))])
  unless bad.isEmpty do
    throwError "AUDIT FAILED: {bad}"
  let mut stmts : Array Json := #[]
  for s in names do
    let n := s.toName
    match env.find? n with
    | none => throwError "AUDIT FAILED: results.json names a missing declaration {s}"
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
        ("axioms", toJson ((← collectAxioms n).map Name.toString)),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("LENS_AUDIT_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
  logInfo m!"AUDIT OK: {decls.size} library declarations use only propext, Classical.choice, \
    Quot.sound; {stmts.size} referenced names resolved."

end Toy.Lens.Audit
