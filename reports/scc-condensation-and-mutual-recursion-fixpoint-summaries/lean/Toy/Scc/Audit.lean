/-
Toy.Scc.Audit
=============

Build-time audit.  This module fails to compile unless

* the declarations of this project that depend on `sorryAx` are *exactly* the
  statements listed in `allowedSorry` (currently none: every result is fully proved);
* no declaration of this project depends on an axiom other than `propext`,
  `Quot.sound`, `Classical.choice` (and `sorryAx` for the listed statements).

In particular every definition example, every tightness counterexample, every
non-vacuity witness, and every counterexample result is `sorry`-free.
-/
import Lean
import Toy.Scc.Graph
import Toy.Scc.Lattice
import Toy.Scc.BottomUp
import Toy.Scc.Decomp
import Toy.Scc.Fixpoint
import Toy.Scc.Transfer
import Toy.Scc.Termination
import Toy.Scc.Checks

open Lean Elab Command

namespace Toy.Scc.Audit

/-- The main-result statements whose proofs are deferred: none (every result is fully
proved). -/
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
    unless (`Toy).isPrefixOf modName do continue
    if modName == `Toy.Scc.Audit then continue
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
  logInfo m!"AUDIT OK: {checked} declarations checked; exactly {usesSorry.size} depend on sorryAx, all of them allowed main results; no non-standard axioms."

end Toy.Scc.Audit
