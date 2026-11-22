import Lean
import MirUbChecksRuntimeChecksAndCheckEnumsSoundness

open Lean

/-!
Standalone purity and axiom auditor for `MirUbChecksRuntimeChecksAndCheckEnumsSoundness`.

Inspects `env.constants.map₁` (imported `.olean` module declarations) for:
- `0` `_unsafe_rec` compiler-generated helpers,
- `0` `unsafe` declarations,
- `0` forbidden axioms (only `propext` and `Quot.sound` allowed; rejects
  `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`).
-/

#eval show MetaM Unit from do
  let env ← getEnv
  let prefixStr := "MirUbChecksRuntimeChecksAndCheckEnumsSoundness"
  let mut totalConsts := 0
  let mut theoremCount := 0
  let mut unsafeRecs : Array Name := #[]
  let mut unsafeDecls : Array Name := #[]
  let mut allAxiomsUsed : Array Name := #[]
  let mut forbiddenAxioms : Array (Name × Name) := #[]
  let allowedAxioms : List Name := [`propext, `Quot.sound]
  for (n, ci) in env.constants.map₁.toList do
    let s := n.toString
    if s.startsWith prefixStr then
      totalConsts := totalConsts + 1
      if (s.splitOn "_unsafe_rec").length > 1 then
        unsafeRecs := unsafeRecs.push n
      if ci.isUnsafe then
        unsafeDecls := unsafeDecls.push n
      match ci with
      | .thmInfo _ =>
        theoremCount := theoremCount + 1
        let axs ← Lean.collectAxioms n
        for ax in axs do
          if !allAxiomsUsed.contains ax then
            allAxiomsUsed := allAxiomsUsed.push ax
          if !allowedAxioms.contains ax then
            forbiddenAxioms := forbiddenAxioms.push (n, ax)
      | _ => pure ()
  IO.println s!"AUDIT_TOTAL_CONSTS={totalConsts}"
  IO.println s!"AUDIT_THEOREMS={theoremCount}"
  IO.println s!"AUDIT_ALL_AXIOMS_USED={allAxiomsUsed}"
  IO.println s!"AUDIT_UNSAFE_RECS={unsafeRecs.size} {unsafeRecs}"
  IO.println s!"AUDIT_UNSAFE_DECLS={unsafeDecls.size} {unsafeDecls}"
  IO.println s!"AUDIT_FORBIDDEN_AXIOMS={forbiddenAxioms.size} {forbiddenAxioms}"
  if totalConsts == 0 || unsafeRecs.size > 0 || unsafeDecls.size > 0 || forbiddenAxioms.size > 0 then
    throwError "PURITY AUDIT FAILED"
