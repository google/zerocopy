import Lean
import FnDefZstFnPtrNicheAndReifyShimSoundness

/-!
# Environment Audit for `FnDefZstFnPtrNicheAndReifyShimSoundness`

Verifies via Lean MetaM across every constant declared in
`FnDefZstFnPtrNicheAndReifyShimSoundness`:
- zero axioms, zero opaque constants, zero unsafe constants, zero partial constants;
- zero `_unsafe_rec` compiled recursion helpers (`0` computable recursive `def`s);
- zero uses of `Acc.rec` or `WellFounded.*` (strictly structural recursion);
- zero forbidden axioms (`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`);
- all theorem and definition dependencies strictly within `[propext, Quot.sound]`.
-/

open Lean Elab Command

private def usesWellFoundedRecursion (e : Expr) : Bool :=
  e.getUsedConstants.any fun c => (`WellFounded).isPrefixOf c || c == ``Acc.rec

private def helperSuffix : String := "_unsafe" ++ "_rec"

run_cmd do
  let env ← getEnv
  let some moduleIdx := env.getModuleIdx? `FnDefZstFnPtrNicheAndReifyShimSoundness
    | throwError "FnDefZstFnPtrNicheAndReifyShimSoundness is not imported"
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
      problems := problems.push s!"{name}: compiled recursion helper (_unsafe_rec)"
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
          problems := problems.push s!"{name}: depends on forbidden axiom {ax}"
    | _ => pure ()
  logInfo m!"module constants audited: {theorems} theorems, {definitions} definitions, {inductives} inductive types"
  logInfo m!"axioms reachable from the module: {axioms.qsort (fun a b => a.toString < b.toString)}"
  unless problems.isEmpty do
    throwError "audit failed:\n{String.intercalate "\n" problems.toList}"
  logInfo "audit passed: 0 _unsafe_rec; 0 axiom/opaque/unsafe/partial; 0 WellFounded/Acc.rec; 0 Classical.choice/sorryAx/ofReduceBool"
