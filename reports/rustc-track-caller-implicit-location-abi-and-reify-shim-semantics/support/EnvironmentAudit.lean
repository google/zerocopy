import Lean
import TrackCallerAbiAndReifySoundness

/-!
# Environment audit for `TrackCallerAbiAndReifySoundness`

Checks properties of the compiled module that `#print axioms` on selected theorems cannot show:
it walks every constant the module declares and fails (the file does not compile) unless

* the module declares no axiom, no opaque constant, no unsafe or partial constant, and none of
  the compiled recursion helpers that Lean's code generator emits for computable recursive
  definitions (their names carry the suffix assembled in `helperSuffix` below);
* no definition or theorem of the module uses `Acc.rec` or a constant under `WellFounded`
  (all recursion is structural);
* the axioms reachable from any constant of the module are among `propext` and `Quot.sound`.

Usage, from the directory that holds both files:

```
lean -o TrackCallerAbiAndReifySoundness.olean TrackCallerAbiAndReifySoundness.lean
LEAN_PATH=. lean EnvironmentAudit.lean
```

Delete the `.olean` afterwards; it is a build product.
-/

open Lean Elab Command

/-- Does the term use `Acc.rec` or any constant under `WellFounded` (`WellFounded.fix`,
`WellFounded.Nat.fix`, ...), the building blocks of well-founded recursion? -/
private def usesWellFoundedRecursion (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => (`WellFounded).isPrefixOf c || c == ``Acc.rec

/-- Suffix of the unsafe helper constants emitted for compiled recursive definitions. -/
private def helperSuffix : String := "_unsafe" ++ "_rec"

run_cmd do
  let env ← getEnv
  let some moduleIdx := env.getModuleIdx? `TrackCallerAbiAndReifySoundness
    | throwError "TrackCallerAbiAndReifySoundness is not imported"
  let allowed : List Name := [``propext, ``Quot.sound]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut inductives : Nat := 0
  let mut problems : Array String := #[]
  let mut axioms : Array Name := #[]
  let constants := env.constants.map₁.fold (init := #[]) fun acc name info => acc.push (name, info)
  for (name, info) in constants do
    unless env.getModuleIdxFor? name == some moduleIdx do continue
    if (name.toString.splitOn helperSuffix).length > 1 then
      problems := problems.push s!"{name}: compiled recursion helper"
    if info.isUnsafe then problems := problems.push s!"{name}: unsafe"
    if info.isPartial then problems := problems.push s!"{name}: partial"
    match info with
    | .axiomInfo _ => problems := problems.push s!"{name}: axiom"
    | .opaqueInfo _ => problems := problems.push s!"{name}: opaque"
    | .thmInfo _ => theorems := theorems + 1
    | .defnInfo _ => definitions := definitions + 1
    | .inductInfo _ => inductives := inductives + 1
    | _ => pure ()
    if let some value := info.value? then
      if usesWellFoundedRecursion value then
        problems := problems.push s!"{name}: well-founded recursion"
    match info with
    | .thmInfo _ | .defnInfo _ =>
      for ax in (← collectAxioms name) do
        unless axioms.contains ax do axioms := axioms.push ax
        unless allowed.contains ax do
          problems := problems.push s!"{name}: depends on axiom {ax}"
    | _ => pure ()
  logInfo m!"module constants audited: {theorems} theorems, {definitions} definitions, {inductives} inductive types"
  logInfo m!"axioms reachable from the module: {axioms.qsort (fun a b => a.toString < b.toString)}"
  unless problems.isEmpty do
    throwError "audit failed:\n{String.intercalate "\n" problems.toList}"
  logInfo "audit passed: no axiom, opaque, unsafe or partial constant; no compiled recursion helper; no well-founded recursion; axioms within [propext, Quot.sound]"
