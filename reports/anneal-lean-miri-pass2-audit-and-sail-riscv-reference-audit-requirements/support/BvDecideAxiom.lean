/-
Probe: what a successful `bv_decide` proof depends on (Lean v4.34.1).
Run: lean BvDecideAxiom.lean
Shows (1) `#print axioms` lists a fresh per-proof axiom `<thm>._native.bv_decide.ax_*`,
not `Lean.ofReduceBool`; (2) the theorem value directly references that axiom and
does not directly reference `Lean.ofReduceBool`, so a denylist of `Lean.ofReduceBool`
alone misses it while an axiom allowlist rejects it.
-/
import Std.Tactic.BVDecide
import Lean.Elab.Command
open Lean Elab Command

theorem bv_probe (x y : BitVec 8) : x ^^^ y ^^^ y = x := by bv_decide

#print axioms bv_probe

#eval show CommandElabM Unit from do
  let env := (← getEnv).setExporting false
  -- walk constants named under `bv_probe` (the theorem and its auxiliaries)
  let mut todo := #[``bv_probe]; let mut seen : NameSet := {}
  let mut anyOfReduceBool := false
  while h : todo.size > 0 do
    let n := todo.back; todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    if used.contains ``Lean.ofReduceBool then anyOfReduceBool := true
    for u in used do
      -- follow constants declared in this file (not imported)
      if (env.getModuleIdxFor? u).isNone then todo := todo.push u
    logInfo m!"{n}: hasValue={(ci.value? (allowOpaque := true)).isSome} used={used.size}"
    logInfo m!"{n} [{if ci.isAxiom then "axiom" else if ci matches .thmInfo _ then "theorem" else "other"}] direct axiom refs: {(used.filter fun u => (env.find? u).any (·.isAxiom)).toList}"
  logInfo m!"any bv_probe.* constant directly references Lean.ofReduceBool: {anyOfReduceBool}"
