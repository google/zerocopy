/- Probe A4: "kernelize" a bv_decide proof.  Take the proof term bv_decide produced, replace
   the per-invocation native axiom `<thm>._native.bv_decide.ax_*` (whose type is
   `verifyBVExpr e c = true`) by `Eq.refl true`, and ask the KERNEL to check the result.
   This forces the kernel to evaluate bv_decide's verified bitblaster + LRAT checker
   (`Std.Tactic.BVDecide.Reflect.verifyBVExpr`) on the stored certificate. -/
import Std.Tactic.BVDecide
import Lean
open Lean Meta Elab Command

set_option Elab.async false

syntax (name := kernelize) "#kernelize " ident ident : command

@[command_elab kernelize] def elabKernelize : CommandElab := fun stx => do
  let src := stx[1].getId
  let dst := stx[2].getId
  let env ← getEnv
  let some ci := env.find? src | throwError "unknown {src}"
  let some v := ci.value? (allowOpaque := true) | throwError "no value"
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let v' := v.replace fun e => match e with
    | .const n _ => if (n.toString.splitOn "_native").length > 1 then some refl else none
    | _ => none
  let t0 ← IO.monoMsNow
  liftCoreM <| addDecl (.thmDecl { name := dst, levelParams := ci.levelParams, type := ci.type, value := v' })
  let t1 ← IO.monoMsNow
  logInfo m!"kernel accepted {dst} in {t1 - t0} ms"

theorem a4_xor8 (x y : BitVec 8) : (x ^^^ y) ^^^ y = x := by bv_decide
#kernelize a4_xor8 a4_xor8_k
#print axioms a4_xor8_k

theorem a4_xor64 (x y : BitVec 64) : (x ^^^ y) ^^^ y = x := by bv_decide
#kernelize a4_xor64 a4_xor64_k
#print axioms a4_xor64_k

theorem a4_add_and_or16 (x y : BitVec 16) : (x &&& y) + (x ||| y) = x + y := by bv_decide
#kernelize a4_add_and_or16 a4_add_and_or16_k
#print axioms a4_add_and_or16_k

theorem a4_mul3_8 (x : BitVec 8) : x * 3 = x + x + x := by bv_decide
#kernelize a4_mul3_8 a4_mul3_8_k
#print axioms a4_mul3_8_k
