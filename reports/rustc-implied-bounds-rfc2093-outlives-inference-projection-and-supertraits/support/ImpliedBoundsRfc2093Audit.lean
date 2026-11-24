import Lean
import ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness

/-!
Kernel-level environment auditor for `ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness`.

Loads the compiled `.olean` of `ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness` and checks every
constant declared by that module:
- 0 `axiom` declarations,
- 0 `opaque` declarations,
- 0 non-`safe` (`unsafe` or `partial`) definitions,
- 0 `._unsafe_rec` compiler helpers (checked across full constant name substrings),
- Every theorem's transitive axiom dependencies lie strictly within
  `{propext, Quot.sound}` (specifically 0 `Classical.choice`, 0 `sorryAx`,
  0 `Lean.ofReduceBool`, 0 `Lean.trustCompiler`).
-/

open Lean

def allowedAxioms : List Name := [`propext, `Quot.sound]

def containsUnsafeRec (s : String) : Bool :=
  (s.splitOn "_unsafe_rec").length > 1

def auditModule : CoreM Unit := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness
    | throwError "module ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness not found in environment"
  let modData := env.header.moduleData[modIdx.toNat]!
  let constNames := modData.constNames

  let mut totalConsts : Nat := 0
  let mut theoremCount : Nat := 0
  let mut zeroAxiomTheorems : Nat := 0
  let mut defCount : Nat := 0
  let mut indCount : Nat := 0
  let mut unsafeRecCount : Nat := 0
  let mut violations : Array String := #[]
  let mut usedAxioms : NameSet := {}

  for name in constNames do
    totalConsts := totalConsts + 1
    if name.toString.endsWith "._unsafe_rec" || containsUnsafeRec name.toString then
      unsafeRecCount := unsafeRecCount + 1
      violations := violations.push s!"forbidden _unsafe_rec helper: {name}"
    let some info := env.find? name
      | do
        violations := violations.push s!"missing constant info: {name}"
        continue
    match info with
    | .axiomInfo _ =>
      violations := violations.push s!"forbidden axiom declaration: {name}"
    | .opaqueInfo _ =>
      violations := violations.push s!"forbidden opaque declaration: {name}"
    | .defnInfo d =>
      defCount := defCount + 1
      if d.safety != .safe then
        violations := violations.push s!"non-safe definition ({repr d.safety}): {name}"
    | .thmInfo _ =>
      theoremCount := theoremCount + 1
      let axioms ← Lean.collectAxioms name
      if axioms.isEmpty then
        zeroAxiomTheorems := zeroAxiomTheorems + 1
      for ax in axioms do
        usedAxioms := usedAxioms.insert ax
        if !allowedAxioms.contains ax then
          violations := violations.push s!"theorem {name} depends on forbidden axiom {ax}"
    | .inductInfo _ =>
      indCount := indCount + 1
    | _ => pure ()

  let axList := usedAxioms.toList.map Name.toString
  IO.println s!"AUDIT_TOTAL_CONSTANTS={totalConsts}"
  IO.println s!"AUDIT_THEOREMS={theoremCount}"
  IO.println s!"AUDIT_ZERO_AXIOM_THEOREMS={zeroAxiomTheorems}"
  IO.println s!"AUDIT_DEFS={defCount}"
  IO.println s!"AUDIT_INDUCTIVES={indCount}"
  IO.println s!"AUDIT_UNSAFE_REC={unsafeRecCount}"
  IO.println s!"AUDIT_AXIOMS={axList}"
  IO.println s!"AUDIT_VIOLATIONS={violations.size}"
  for v in violations do
    IO.println s!"VIOLATION: {v}"
  if !violations.isEmpty then
    throwError s!"Audit failed with {violations.size} violation(s)"

#eval auditModule
