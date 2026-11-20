import Lean
import ToyTransmute.Basic
import ToyTransmute.Tools
import ToyTransmute.Examples
import ToyTransmute.Results
import ToyTransmute.Counterexamples

/-!
# Axiom audit (standalone; not part of the library)

Run from the project root after `lake build`:

    lake env lean support/Audit.lean

It is kept out of the `ToyTransmute` library so that importing the library does not pull in
the `Lean` metaprogramming environment. It fails unless every declaration of every
`ToyTransmute` module (definitions, examples, proof tools, main results, counterexamples,
non-vacuity witnesses and positive controls) depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. In particular, no declaration may depend on `sorryAx`.
On success it prints the number of audited declarations and the axioms used by each main
result in `ToyTransmute.Results`.
-/

open Lean Elab Command

private def auditStdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut mainLines : Array String := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    match env.getModuleIdxFor? n with
    | none => continue
    | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      unless (`ToyTransmute).isPrefixOf m do continue
      count := count + 1
      let axs ← collectAxioms n
      for a in axs do
        unless auditStdAxioms.contains a do
          bad := bad.push s!"{n} depends on non-standard axiom {a}"
      if m == `ToyTransmute.Results then
        let axNames := (axs.map toString).qsort (· < ·)
        mainLines := mainLines.push s!"{n}: {axNames.toList}"
  if !bad.isEmpty then
    throwError m!"axiom audit failed:\n{String.intercalate "\n" bad.toList}"
  let lines := (mainLines.qsort (· < ·)).toList
  logInfo m!"axiom audit passed: {count} declarations, all within propext, Classical.choice, Quot.sound; {mainLines.size} declarations in ToyTransmute.Results:\n{String.intercalate "\n" lines}"
