import Lean
import TraitUpcastingVtableSegmentsAndBoxDropSoundness

/-!
Kernel-level MetaM environment auditor for `TraitUpcastingVtableSegmentsAndBoxDropSoundness`.

Inspects both `modData.constNames` and the full kernel environment constant map
`env.constants.map₁` to verify:
- 0 `axiom` declarations,
- 0 `opaque` declarations,
- 0 non-`safe` (`unsafe` or `partial`) definitions,
- 0 `._unsafe_rec` compiler-generated auxiliary constants (via both `modData.constNames`
  and `env.constants.map₁` lookup),
- Every theorem's transitive axiom dependencies lie strictly within `{propext, Quot.sound}`
  (0 `Classical.choice`, 0 `sorryAx`, 0 `Lean.ofReduceBool`, 0 `Lean.trustCompiler`).
-/

open Lean

def allowedAxioms : List Name := [`propext, `Quot.sound]

def auditModule : CoreM Unit := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `TraitUpcastingVtableSegmentsAndBoxDropSoundness
    | throwError "module TraitUpcastingVtableSegmentsAndBoxDropSoundness not found in environment"
  let modData := env.header.moduleData[modIdx.toNat]!
  let constNames := modData.constNames

  let mut totalConsts : Nat := 0
  let mut theoremCount : Nat := 0
  let mut zeroAxiomTheorems : Nat := 0
  let mut defCount : Nat := 0
  let mut indCount : Nat := 0
  let mut violations : Array String := #[]
  let mut usedAxioms : NameSet := {}

  for name in constNames do
    totalConsts := totalConsts + 1
    if name.toString.endsWith "._unsafe_rec" then
      violations := violations.push s!"forbidden _unsafe_rec helper in modData: {name}"
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

  -- Direct `env.constants.map₁` scan for `_unsafe_rec` belonging to this module or namespace
  let mut map1Total : Nat := 0
  let mut map1ModConsts : Nat := 0
  let mut map1ModUnsafeRec : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    map1Total := map1Total + 1
    let inModule := (env.getModuleIdxFor? name) == some modIdx
    let inNamespace := name.toString.startsWith "TraitUpcastingVtableSoundness"
    if inModule || inNamespace then
      map1ModConsts := map1ModConsts + 1
      if name.toString.endsWith "._unsafe_rec" || (name.toString.splitOn "_unsafe_rec").length > 1 then
        map1ModUnsafeRec := map1ModUnsafeRec + 1
        violations := violations.push s!"forbidden _unsafe_rec in env.constants.map₁: {name}"

  let axList := usedAxioms.toList.map Name.toString
  IO.println s!"AUDIT_TOTAL_CONSTANTS={totalConsts}"
  IO.println s!"AUDIT_THEOREMS={theoremCount}"
  IO.println s!"AUDIT_ZERO_AXIOM_THEOREMS={zeroAxiomTheorems}"
  IO.println s!"AUDIT_DEFS={defCount}"
  IO.println s!"AUDIT_INDUCTIVES={indCount}"
  IO.println s!"AUDIT_MAP1_TOTAL={map1Total}"
  IO.println s!"AUDIT_MAP1_MODULE_CONSTS={map1ModConsts}"
  IO.println s!"AUDIT_MAP1_MODULE_UNSAFE_REC={map1ModUnsafeRec}"
  IO.println s!"AUDIT_AXIOMS={axList}"
  IO.println s!"AUDIT_VIOLATIONS={violations.size}"
  for v in violations do
    IO.println s!"VIOLATION: {v}"
  if !violations.isEmpty then
    throwError s!"Audit failed with {violations.size} violation(s)"

#eval auditModule
