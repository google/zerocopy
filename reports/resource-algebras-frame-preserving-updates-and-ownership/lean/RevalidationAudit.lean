import Lean
import Toy

/-!
# Self-Contained Axiom and Statement-Closure Audit (`RevalidationAudit`)

Standalone Lean 4 audit script outside the `Toy` library target. When invoked
from `lean/` after `lake build`:

    lake env lean RevalidationAudit.lean

it inspects the compiled `Toy` environment using `Lean.collectAxioms`, verifies
that every declaration in `Toy` depends only on `propext`, `Classical.choice`,
and `Quot.sound`, and recomputes the SHA-256 hashes (in Python or via the JSON
emitted on stdout) of the kernel `Expr` statement representation and package
definition closure for every Lean name referenced in `../results.json` and
`../audit/statements.json`.
-/

open Lean Elab Command

private def pkgRoots : List Name := [`Toy]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    pkgRoots.any (fun r => r.isPrefixOf m)
  | none => false

private partial def defClosure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then defClosure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => defClosure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      defClosure env (cs ++ rest) acc

private def strToName (s : String) : Name :=
  (s.splitOn ".").foldl Name.str Name.anonymous

private def addJsonStrings (j : Json) (acc : List String) : List String :=
  match j with
  | .str s => s :: acc
  | .arr xs => xs.foldl (fun a x => addJsonStrings x a) acc
  | _ => acc

private def collectCardNames (cardsJson : Json) : List String :=
  let fields := ["lean", "lean_names", "nonvacuity_witness_lean",
                 "positive_control_lean", "scope_witnesses_lean", "corollaries_lean"]
  match cardsJson with
  | .arr cards =>
    cards.foldl (fun acc card =>
      let acc := fields.foldl (fun a f =>
        match card.getObjVal? f with
        | .ok v => addJsonStrings v a
        | .error _ => a) acc
      match card.getObjVal? "hypotheses" with
      | .ok (.arr hyps) =>
        hyps.foldl (fun a h =>
          match h.getObjVal? "counterexample" with
          | .ok v => addJsonStrings v a
          | .error _ => a) acc
      | _ => acc) []
  | _ => []

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut wantedStrs : List String := []
  if (← System.FilePath.pathExists "../results.json") then
    let txt ← IO.FS.readFile "../results.json"
    if let .ok j := Json.parse txt then
      wantedStrs := collectCardNames j ++ wantedStrs
  if (← System.FilePath.pathExists "../audit/statements.json") then
    let txt ← IO.FS.readFile "../audit/statements.json"
    if let .ok j := Json.parse txt then
      if let .ok (.obj kvs) := j.getObjVal? "statements" then
        wantedStrs := kvs.toList.map Prod.fst ++ wantedStrs
  let uniqueStrs := (wantedStrs.toArray.qsort (· < ·)).toList.eraseReps
  let wantedNames := uniqueStrs.map strToName

  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [
        ("name", toJson n.toString),
        ("axioms", toJson (axs.map Name.toString))
      ])

  let mut stmts : Array Json := #[]
  for n in wantedNames do
    match env.find? n with
    | none =>
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := defClosure env (ci.type.getUsedConstants.toList) {}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [
        ("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))
      ])
  IO.println ("REVALIDATION_AUDIT_JSON " ++
    (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
