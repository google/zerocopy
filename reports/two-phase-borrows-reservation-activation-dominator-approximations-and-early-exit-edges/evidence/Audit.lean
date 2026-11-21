import Lean
import ToyTwoPhase
open Lean Elab Command

/-! Axiom audit: prints every theorem declared in the `ToyTwoPhase` modules with the axioms its
proof depends on (`Lean.collectAxioms`), sorted by name, then a summary line. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut bad := 0
  for (n, ci) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      if (`ToyTwoPhase).isPrefixOf m && !n.isInternal && ci.isTheorem then
        let axs ← collectAxioms n
        let axs := axs.qsort (fun a b => a.toString < b.toString)
        for a in axs do
          if !([`propext, `Classical.choice, `Quot.sound].contains a) then bad := bad + 1
        rows := rows.push s!"{n}: {axs.toList}"
    | none => pure ()
  for r in rows.qsort (· < ·) do IO.println r
  IO.println s!"theorems: {rows.size}; non-standard axiom uses: {bad}"
