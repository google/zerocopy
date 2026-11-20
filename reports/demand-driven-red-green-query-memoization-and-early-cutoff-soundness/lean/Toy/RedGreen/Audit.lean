/-
Toy.RedGreen.Audit
==================

Build-time axiom audit.  This module fails to compile unless every
declaration of this project (outside this module) depends only on the
standard axioms `propext`, `Quot.sound`, `Classical.choice`.  In particular no
declaration depends on `sorryAx`, so every main result, definition example,
tightness counterexample, non-vacuity witness, and supporting lemma is fully
proved.
-/
import Lean
import Toy.RedGreen.Basic
import Toy.RedGreen.Examples
import Toy.RedGreen.Lemmas
import Toy.RedGreen.Frame
import Toy.RedGreen.ValueSound
import Toy.RedGreen.ExecLog
import Toy.RedGreen.DefExamples
import Toy.RedGreen.Soundness
import Toy.RedGreen.Replay
import Toy.RedGreen.Necessity
import Toy.RedGreen.Minimal
import Toy.RedGreen.Witnesses

open Lean Elab Command

namespace Toy.RedGreen.Audit

/-- Axioms a declaration of this project may depend on. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

run_cmd do
  let env ← getEnv
  let mut otherAxioms : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Toy).isPrefixOf modName do continue
    if modName == `Toy.RedGreen.Audit then continue
    checked := checked + 1
    let axs ← Lean.collectAxioms n
    for ax in axs do
      unless standardAxioms.contains ax do
        otherAxioms := otherAxioms.push (n, ax)
  unless otherAxioms.isEmpty do
    throwError "AUDIT FAILED: non-standard axioms used: {otherAxioms}"
  logInfo m!"AUDIT OK: {checked} declarations checked; all depend only on propext, Quot.sound, Classical.choice."

end Toy.RedGreen.Audit
