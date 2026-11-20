/- Probe A5: is bv_decide's verified LRAT checker kernel-evaluable if we bypass the `partial`
   LRAT parser?  We parse the certificate at meta level, embed the parsed `Array IntAction` as a
   closed term, and ask `decide +kernel` to evaluate
   `LRAT.check actions (AIG.toCNF expr.bitblast.relabelNat) = true`
   (`LRAT.check_sound` would turn that into `cnf.Unsat` without any native axiom). -/
import Std.Tactic.BVDecide
import Lean
open Lean Meta Elab Command Std.Tactic.BVDecide Std.Tactic.BVDecide.LRAT Std.Sat

set_option Elab.async false

def actTy : Expr := mkApp2 (mkConst ``Action [0, 0]) (toTypeExpr (Array Int)) (mkConst ``Nat)

def actToExpr : IntAction → Expr
  | .addEmpty id h => mkApp4 (mkConst ``Action.addEmpty [0,0]) (toTypeExpr (Array Int)) (mkConst ``Nat) (toExpr id) (toExpr h)
  | .addRup id c h => mkApp5 (mkConst ``Action.addRup [0,0]) (toTypeExpr (Array Int)) (mkConst ``Nat) (toExpr id) (toExpr c) (toExpr h)
  | .addRat id c p h r => mkAppN (mkConst ``Action.addRat [0,0]) #[toTypeExpr (Array Int), mkConst ``Nat, toExpr id, toExpr c, toExpr p, toExpr h, toExpr r]
  | .del ids => mkApp3 (mkConst ``Action.del [0,0]) (toTypeExpr (Array Int)) (mkConst ``Nat) (toExpr ids)

syntax (name := lratDef) "#lrat_def " ident ident : command
@[command_elab lratDef] def elabLratDef : CommandElab := fun stx => do
  let certDef := stx[1].getId
  let dst := stx[2].getId
  let some ci := (← getEnv).find? certDef | throwError "unknown"
  let some (.lit (.strVal s)) := ci.value? | throwError "cert is not a string literal"
  match parseLRATProof s.toUTF8 with
  | .error e => throwError e
  | .ok acts =>
    let e := mkApp2 (mkConst ``List.toArray [0]) actTy
      (acts.toList.foldr (fun a acc => mkApp3 (mkConst ``List.cons [0]) actTy (actToExpr a) acc)
        (mkApp (mkConst ``List.nil [0]) actTy))
    let ty := mkApp (mkConst ``Array [0]) actTy
    let d : DefinitionVal := { name := dst, levelParams := [], type := ty, value := e, hints := .abbrev, safety := .safe }
    liftCoreM <| addDecl (.defnDecl d)
    logInfo m!"{dst}: {acts.size} LRAT actions"

theorem a5_xor4 (x y : BitVec 8) : (x ^^^ y) ^^^ y = x := by bv_decide
run_cmd do
  for (n, _) in (← getEnv).constants.map₂.toList do
    if (`a5_xor4).isPrefixOf n then logInfo m!"{n}"
#lrat_def a5_xor4._cert_def_1 a5_xor4_acts

set_option maxRecDepth 100000 in
theorem a5_xor4_check :
    LRAT.check a5_xor4_acts (AIG.toCNF (a5_xor4._expr_def_1).bitblast.relabelNat) = true := by
  decide +kernel
#print axioms a5_xor4_check
