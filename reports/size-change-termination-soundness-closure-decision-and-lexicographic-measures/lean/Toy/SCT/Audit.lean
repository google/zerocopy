/-
Toy.SCT.Audit
=============

Build-time audit. This module fails to compile unless

* no declaration of this project depends on `sorryAx` (`allowedSorry` is empty);
* no declaration of this project depends on an axiom other than `propext`, `Quot.sound`,
  `Classical.choice`.

In particular every main result, definition example, tightness counterexample, non-vacuity
witness, positive control and counterexample result is `sorry`-free.
-/
import Lean
import Toy.SCT.Graph
import Toy.SCT.Semantics
import Toy.SCT.Check
import Toy.SCT.Fixtures
import Toy.SCT.Examples
import Toy.SCT.Results
import Toy.SCT.Counterexamples
import Toy.SCT.Infinite
import Toy.SCT.Ramsey
import Toy.SCT.Threads
import Toy.SCT.Enum
import Toy.SCT.Soundness
import Toy.SCT.Exactness
import Toy.SCT.CheckCorrect

open Lean Elab Command

namespace Toy.SCT.Audit

/-- Declarations allowed to depend on `sorryAx`: none (every result is fully proved). -/
def allowedSorry : List Name := []

/-- Axioms a `sorry`-free declaration of this project may depend on. -/
def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

run_cmd do
  let env ← getEnv
  let mut usesSorry : Array Name := #[]
  let mut otherAxioms : Array (Name × Name) := #[]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`Toy.SCT).isPrefixOf modName do continue
    if modName == `Toy.SCT.Audit then continue
    checked := checked + 1
    let axs ← Lean.collectAxioms n
    for ax in axs do
      if ax == ``sorryAx then
        usesSorry := usesSorry.push n
      else if !standardAxioms.contains ax then
        otherAxioms := otherAxioms.push (n, ax)
  let unexpected := usesSorry.filter fun n => !allowedSorry.contains n
  let missing := allowedSorry.filter fun n => !usesSorry.contains n
  unless otherAxioms.isEmpty do
    throwError "AUDIT FAILED: non-standard axioms used: {otherAxioms}"
  unless unexpected.isEmpty do
    throwError "AUDIT FAILED: sorryAx used outside the allowed main results: {unexpected}"
  unless missing.isEmpty do
    throwError "AUDIT FAILED: expected to depend on sorryAx but does not: {missing}"
  logInfo m!"AUDIT OK: {checked} declarations checked; {usesSorry.size} depend on sorryAx; no non-standard axioms."

end Toy.SCT.Audit
