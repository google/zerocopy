import Lean
import XrayAttrOverrideAndCoverageBranchSoundness

/-!
Whole-module audit of `XrayAttrOverrideAndCoverageBranchSoundness`.

Run from a second file so that the audited constants are *imported*: they are
then exactly the entries of `env.constants.map₁` whose defining module is the
audited one. (Inside the audited file itself those constants would live in
`map₂`, and `map₁` would only hold the prelude.)

The command below fails, giving a non-zero exit status, if any constant of the
audited module

* has a name containing the suffix that Lean gives to executable auxiliary
  definitions of recursive functions (spelled in two pieces below, so that a
  plain text search of this directory for that suffix finds only real hits),
* is unsafe, partial, an axiom, or an opaque constant, or
* depends, transitively, on any axiom other than `propext` and `Quot.sound`.
  The allow-list has exactly those two entries, so the choice axiom, the
  placeholder-proof axiom and the compiler-trusting axioms are all rejected.
-/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let modName := `XrayAttrOverrideAndCoverageBranchSoundness
  let some modIdx := env.getModuleIdx? modName
    | throwError "module {modName} is not imported"
  let mine := env.constants.map₁.toList.filter
    (fun (n, _) => env.getModuleIdxFor? n == some modIdx)
  if mine.isEmpty then throwError "no constants found for module {modName}"
  let needle := "_unsafe" ++ "_rec"
  let hasSub (n : Name) : Bool := (n.toString.splitOn needle).length > 1
  let auxRec := mine.filter (fun (n, _) => hasSub n)
  let unsafeOrPartial := mine.filter (fun (_, ci) => ci.isUnsafe || ci.isPartial)
  let axiomsOrOpaque := mine.filter (fun (_, ci) =>
    match ci with
    | .axiomInfo _ => true
    | .opaqueInfo _ => true
    | _ => false)
  let theorems := mine.filter (fun (_, ci) => match ci with | .thmInfo _ => true | _ => false)
  let defs := mine.filter (fun (_, ci) => match ci with | .defnInfo _ => true | _ => false)
  let allowed : List Name := [``propext, ``Quot.sound]
  let mut used : Array Name := #[]
  let mut offenders : Array (Name × Name) := #[]
  for (n, _) in mine do
    for ax in (← collectAxioms n) do
      unless used.contains ax do used := used.push ax
      unless allowed.contains ax do offenders := offenders.push (n, ax)
  logInfo m!"module constants examined (from env.constants.map₁): {mine.length}"
  logInfo m!"theorems: {theorems.length}; definitions: {defs.length}"
  logInfo m!"names containing {needle}: {auxRec.length}"
  logInfo m!"unsafe or partial constants: {unsafeOrPartial.length}"
  logInfo m!"axiom or opaque constants declared by the module: {axiomsOrOpaque.length}"
  logInfo m!"axioms used anywhere in the module: {used.qsort (fun a b => a.toString < b.toString)}"
  logInfo m!"dependencies on axioms outside [propext, Quot.sound]: {offenders.size}"
  unless auxRec.isEmpty do
    throwError "{needle} constants: {auxRec.map (·.1)}"
  unless unsafeOrPartial.isEmpty do
    throwError "unsafe/partial constants: {unsafeOrPartial.map (·.1)}"
  unless axiomsOrOpaque.isEmpty do
    throwError "axiom/opaque constants: {axiomsOrOpaque.map (·.1)}"
  unless offenders.isEmpty do
    throwError "forbidden axiom dependencies: {offenders}"
  logInfo m!"AUDIT PASSED"
