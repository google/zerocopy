/-
Axiom audit (not part of the library; run with `lake env lean Audit.lean`
after `lake build`). Fails unless every declaration of the `Toy` library
depends only on the axioms `propext`, `Quot.sound`, `Classical.choice`.
-/
import Lean
import Toy

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let standard : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let mut bad : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Toy).isPrefixOf modName do continue
    checked := checked + 1
    for ax in (← Lean.collectAxioms n) do
      unless standard.contains ax do
        bad := bad.push (n, ax)
  unless bad.isEmpty do
    throwError "AUDIT FAILED: non-standard axioms: {bad}"
  logInfo m!"AUDIT OK: {checked} declarations checked; only propext, Quot.sound, Classical.choice."
