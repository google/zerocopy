import Lean
import LintCapAndForbidUnsafeSoundness

/-!
# Environment audit for `LintCapAndForbidUnsafeSoundness`

Loads the compiled module and inspects every constant it declares:

* the module declares no axiom and no opaque constant (a definition that the
  kernel cannot unfold, which is what a non-terminating-by-fiat definition
  compiles to);
* no constant is marked unsafe and no auxiliary constant carries the suffix that
  the compiler uses for the unchecked copy of a recursive definition;
* the axioms reachable from each theorem and definition are within the allowed
  list below (anything else, including the axiom behind an unfinished proof and
  the axiom behind compiled-code evaluation, fails the audit).

The suffix is assembled from two fragments so that a plain text search of this
directory for it only finds genuine occurrences.
-/

open Lean Elab Command

/-- Axioms a constant of the audited module may depend on. -/
def allowedAxioms : List Name := [``propext, ``Quot.sound]

def uncheckedRecSuffix : String := "_unsafe" ++ "_rec"

def nameHasUncheckedRecSuffix (n : Name) : Bool :=
  n.components.any fun c => c.toString == uncheckedRecSuffix

run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? `LintCapAndForbidUnsafeSoundness
    | throwError "audited module is not loaded"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut theorems := 0
  let mut definitions := 0
  let mut inductives := 0
  let mut others := 0
  let mut used : Array Name := #[]
  let mut axiomFree := 0
  let mut problems : Array String := #[]
  for n in names do
    let some ci := env.find? n | throwError "constant {n} not found"
    if ci.isUnsafe then problems := problems.push s!"unsafe constant: {n}"
    if nameHasUncheckedRecSuffix n then problems := problems.push s!"unchecked recursive copy: {n}"
    match ci with
    | .axiomInfo _ => problems := problems.push s!"module declares an axiom: {n}"
    | .opaqueInfo _ => problems := problems.push s!"module declares an opaque constant: {n}"
    | .thmInfo _ => theorems := theorems + 1
    | .defnInfo _ => definitions := definitions + 1
    | .inductInfo _ => inductives := inductives + 1
    | _ => others := others + 1
    let axs ← collectAxioms n
    for a in axs do
      unless allowedAxioms.contains a do
        problems := problems.push s!"constant {n} depends on disallowed axiom {a}"
      unless used.contains a do
        used := used.push a
    if ci matches .thmInfo _ then
      if axs.isEmpty then axiomFree := axiomFree + 1
  unless problems.isEmpty do
    throwError "ENV_AUDIT_FAILED {problems.size} problem(s): {problems.toList}"
  logInfo m!"ENV_AUDIT_OK constants={names.size} theorems={theorems} definitions={definitions} inductives={inductives} other={others} axiom_free_theorems={axiomFree} axioms_used={used.toList}"
