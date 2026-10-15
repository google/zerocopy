/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import DropJson
public meta import Lean
public section

/-!
Read the compiler's complete snapshot, rather than a caller-supplied list of
ownership events. The command selects exactly one native function, quotes its
entire body as data, and asks the kernel to check that the pure decoder and
ownership checker accept it. The metaprogram supplies only data and reflexivity;
it cannot substitute a successful native computation for a proof.

The Python driver freezes the bytes it inspected into a fresh proof directory.
Its report binds that snapshot to the original compiler input. This command
does not claim that JSON import proves the correctness of rustc or Charon.
-/

open Lean Meta Elab Command

namespace AeneasSpecs.DropAudit

private meta partial def quoteJson (value : Json) : MetaM Expr := do
  match value with
  | .null => return mkConst ``Json.null
  | .bool value => return mkApp (mkConst ``Json.bool) (toExpr value)
  | .num value =>
    let number := mkApp2 (mkConst ``JsonNumber.mk)
      (toExpr value.mantissa) (toExpr value.exponent)
    return mkApp (mkConst ``Json.num) number
  | .str value => return mkApp (mkConst ``Json.str) (toExpr value)
  | .arr values =>
    return mkApp (mkConst ``Json.arr)
      (← mkArrayLit (mkConst ``Json) (← values.mapM quoteJson).toList)
  | .obj fields =>
    let pairs ← fields.toArray.mapM fun (key, value) => do
      mkAppM ``Prod.mk #[toExpr key, ← quoteJson value]
    let pairType := mkApp2 (mkConst ``Prod [.zero, .zero])
      (mkConst ``String) (mkConst ``Json)
    return mkApp (mkConst ``Json.mkObj) (← mkListLit pairType pairs.toList)

/-- Emit a kernel-checked acceptance theorem for one exact compiler body. -/
elab "certify_empty_drops " index:num : command => do
  let some source ← IO.getEnv "AENEAS_DROP_SNAPSHOT"
    | throwError "Missing frozen compiler snapshot for drop admission"
  let .ok snapshot := Json.parse (← IO.FS.readFile source)
    | throwError "Malformed compiler snapshot for drop admission"
  unless (snapshot.getObjValAs? Bool "has_errors").toOption == some false do
    throwError "Drop admission requires a successful compiler snapshot"
  let .ok translated := snapshot.getObjVal? "translated"
    | throwError "Missing translated compiler crate"
  let .ok functions := translated.getObjValAs? (Array Json) "fun_decls"
    | throwError "Missing native function inventory"
  let functionId := index.getNat
  let selected := functions.filter fun function =>
    (function.getObjValAs? Nat "def_id").toOption == some functionId
  unless selected.size == 1 do
    throwError "Missing or ambiguous native function {functionId}"
  let .ok body := selected[0]!.getObjVal? "body"
    | throwError "Native function {functionId} has no body"
  let bodyExpr ← liftTermElabM <| quoteJson body
  let proposition ← liftTermElabM <| mkEq
    (mkApp (mkConst ``DropJson.acceptBody) bodyExpr) (toExpr true)
  -- The kernel must reduce acceptBody on the actual quoted body to true.
  -- No native_decide, axiom, or computed Boolean is used as a proof premise.
  let proof ← liftTermElabM <| mkEqRefl (toExpr true)
  let theoremName := Name.mkSimple s!"empty_drop_body_{functionId}"
  liftCoreM <| addDecl <| .thmDecl {
    name := theoremName, levelParams := [], type := proposition, value := proof }
  logInfo m!"Kernel checked empty drops in native function {functionId}"

end AeneasSpecs.DropAudit
