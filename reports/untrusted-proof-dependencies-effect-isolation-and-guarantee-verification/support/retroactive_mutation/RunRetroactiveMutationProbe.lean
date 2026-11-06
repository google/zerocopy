import Lean
import Lean.Replay

open Lean

def runLeanSnippet (label : String) (code : String) : IO Unit := do
  IO.FS.writeFile "TmpSnippet.lean" code
  let out ← IO.Process.output {
    cmd := "sh"
    args := #["-c", "lean TmpSnippet.lean"]
  }
  IO.println s!"--- [{label}] (exitCode={out.exitCode}) ---"
  if !out.stdout.trimAscii.isEmpty then
    IO.println s!"  stdout: {out.stdout.trimAscii}"
  if !out.stderr.trimAscii.isEmpty then
    IO.println s!"  stderr: {out.stderr.trimAscii}"

def inspectProofOlean (modName : Name) (thmName : Name) : IO Unit := do
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let some ci := env.find? thmName
    | throw <| IO.userError s!"missing {thmName} in {modName}"
  let expectedType := mkApp (mkConst `Trusted.CrateTheorem) (mkConst `Mir.crate)
  let matchesExpected := ci.type == expectedType
  -- Replay all non-Init constants through the standalone Lean kernel
  let mut locals : Std.HashMap Name ConstantInfo := {}
  for m in env.header.modules, data in env.header.moduleData do
    if m.module.getRoot != `Init then
      for c in data.constants do
        locals := locals.insert c.name c
  let baseEnv ← importModules #[{ module := `Init.Core }, { module := `Init.Notation }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  let _ ← baseEnv.toKernelEnv.replay locals
  IO.println s!"=== Kernel Inspection of {modName} ({thmName}) ==="
  IO.println s!"  ConstantInfo.type          : {ci.type}"
  IO.println s!"  ConstantInfo.value?        : {ci.value? true}"
  IO.println s!"  Kernel replay succeeded?   : true (replayed {locals.size} non-foundation constants)"
  IO.println s!"  Matches exact target type? : {matchesExpected} (expected: `Trusted.CrateTheorem Mir.crate`)"

def main : IO Unit := do
  initSearchPath (← findSysroot) [System.FilePath.mk "."]

  IO.println "=================================================================="
  IO.println "1. Vector 1: Retroactive [simp], [reducible], [irreducible]"
  IO.println "=================================================================="
  runLeanSnippet "V1a: retroactive `attribute [reducible] Trusted.SafeExec` (default options)"
    "prelude\nimport Trusted\nattribute [reducible] Trusted.SafeExec\n"
  runLeanSnippet "V1b: retroactive `attribute [irreducible] Trusted.SafeExec` (default options)"
    "prelude\nimport Trusted\nattribute [irreducible] Trusted.SafeExec\n"
  runLeanSnippet "V1c: retroactive `attribute [irreducible] Trusted.SafeExec` WITH `allowUnsafeReducibility`"
    "prelude\nimport Trusted\nset_option allowUnsafeReducibility true in\nattribute [irreducible] Trusted.SafeExec\n"
  runLeanSnippet "V1d: effect of TheoryV1 (`[irreducible] Trusted.SafeExec`) on downstream `simp` vs `rfl` (kernel)"
    "prelude\nimport Trusted\nimport TheoryV1\n-- `simp` fails because `Trusted.SafeExec` was retroactively marked `[irreducible]` in `TheoryV1`:\ntheorem test_kernel_rfl : Trusted.SafeExec { entryReturnVal := 1, expectedVal := 1 } = true := rfl\n"

  IO.println "\n=================================================================="
  IO.println "2. Vector 2: Retroactive [implemented_by], [extern], [csimp]"
  IO.println "=================================================================="
  runLeanSnippet "V2a: retroactive `attribute [implemented_by ...]` on imported `Trusted.SafeExec`"
    "prelude\nimport Trusted\ndef fake (_ : Trusted.Crate) : Bool := true\nattribute [implemented_by fake] Trusted.SafeExec\n"
  runLeanSnippet "V2b: retroactive `attribute [extern ...]` on imported `Trusted.SafeExec`"
    "prelude\nimport Trusted\nattribute [extern \"fake_c\"] Trusted.SafeExec\n"
  runLeanSnippet "V2c: `@[csimp]` theorem in Theory replacing `Trusted.SafeExec` when extensionally equal"
    "prelude\nimport Trusted\ndef altSafeExec (c : Trusted.Crate) : Bool := Nat.beq c.entryReturnVal c.expectedVal\n@[csimp] theorem csimp_safe : @Trusted.SafeExec = @altSafeExec := rfl\n"

  IO.println "\n=================================================================="
  IO.println "3. Vector 3: High-priority / LIFO Typeclass Instance Overriding"
  IO.println "=================================================================="
  inspectProofOlean `ProofV3 `Proof.verify_typeclass_stmt
  runLeanSnippet "V3b: Default-priority (no `priority :=` arg, admitted by Phase 1!) LIFO instance shadow"
    "prelude\nimport Trusted\nimport Mir\ninstance : BEq Nat where beq _ _ := true\ntheorem hijacked_beq : (Mir.crate.entryReturnVal == Mir.crate.expectedVal) = true := rfl\n"
  runLeanSnippet "V3c: Does `TheoryV3` affect `Trusted.CrateTheorem Mir.crate` when `Trusted` and `Mir` are already compiled?"
    "prelude\nimport Trusted\nimport Mir\nimport TheoryV3\ntheorem try_prove_crate : Trusted.CrateTheorem Mir.crate := rfl\n"

  IO.println "\n=================================================================="
  IO.println "4. Vector 4: Global `notation` / `macro` / `elab` Overriding"
  IO.println "=================================================================="
  inspectProofOlean `ProofV4 `Proof.verify_crate

  IO.println "\n=================================================================="
  IO.println "5. Vector 5: Namespace & Alias Shadowing (`def Trusted.CrateTheorem` / `Proof.Trusted.CrateTheorem` / `export`)"
  IO.println "=================================================================="
  runLeanSnippet "V5a-1: `def Trusted.CrateTheorem` in Theory when `Trusted` IS imported"
    "prelude\nimport Trusted\ndef Trusted.CrateTheorem (_ : Trusted.Crate) : Prop := True\n"
  runLeanSnippet "V5a-2: `def Trusted.CrateTheorem` in Theory when `Trusted` is NOT imported (caught by Phase 2 `validateLocalConstant`)"
    "prelude\nimport Init.Core\ndef Trusted.CrateTheorem (_ : Nat) : Prop := True\n"
  inspectProofOlean `ProofV5Ns `Proof.verify_crate
  let shadowedName : Name := `Proof.Trusted.CrateTheorem
  IO.println s!"  [Phase 2 check] (`Proof.Trusted.CrateTheorem).getRoot = {shadowedName.getRoot} (is `Trusted? {shadowedName.getRoot == `Trusted})"
  runLeanSnippet "V5c-1: `export FakeShadow (Trusted.CrateTheorem)` followed by top-level `Trusted.CrateTheorem Mir.crate`"
    "prelude\nimport Trusted\nimport Mir\nimport TheoryV5Export\ntheorem top_level_check : Trusted.CrateTheorem Mir.crate := trivial\n"
  runLeanSnippet "V5c-2: `export FakeShadow.Trusted (CrateTheorem)` when `Proof.lean` uses `open Trusted` + unqualified `CrateTheorem`"
    "prelude\nimport Trusted\nimport Mir\nnamespace Fake\ndef CrateTheorem (_ : Trusted.Crate) : Prop := True\nend Fake\nexport Fake (CrateTheorem)\nopen Trusted\ntheorem unqualified_check : CrateTheorem Mir.crate := trivial\n"
  IO.FS.removeFile "TmpSnippet.lean"
