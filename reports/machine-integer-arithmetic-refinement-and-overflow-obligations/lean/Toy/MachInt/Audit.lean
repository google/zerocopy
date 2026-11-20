/-
Toy.MachInt.Audit
=================

Build-time axiom audit for `Toy.MachInt`. This module fails to compile unless every
declaration of this project (outside this module) depends only on the three standard
axioms `propext`, `Quot.sound`, and `Classical.choice`. In particular, no declaration
depends on `sorryAx` (an unfinished proof) or on `Lean.ofReduceBool` (`native_decide`).
-/
import Lean
import Toy.MachInt.Defs
import Toy.MachInt.Examples
import Toy.MachInt.Lemmas
import Toy.MachInt.Statements
import Toy.MachInt.Counterexamples
import Toy.MachInt.Witnesses
import Toy.MachInt.Supplements

open Lean Elab Command

namespace Toy.MachInt.Audit

/-- Axioms a declaration of this project may depend on. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

run_cmd do
  let env ← getEnv
  let mut otherAxioms : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Toy).isPrefixOf modName do continue
    if modName == `Toy.MachInt.Audit then continue
    checked := checked + 1
    if ci matches .thmInfo _ then theorems := theorems + 1
    let axs ← Lean.collectAxioms n
    for ax in axs do
      if !standardAxioms.contains ax then
        otherAxioms := otherAxioms.push (n, ax)
  unless otherAxioms.isEmpty do
    throwError "AUDIT FAILED: non-standard axioms used: {otherAxioms}"
  logInfo m!"AUDIT OK: {checked} declarations checked ({theorems} theorems); \
    every one depends only on propext, Quot.sound, and Classical.choice."

end Toy.MachInt.Audit
