-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import SingleSourceCodegen

/-!
# `.olean` Environment Auditor for Single-Source Artifact Binding

Demonstrates the exact `.olean` check to add to `trusted/audit/TrustedBoundary.lean`:
1. Loads `SingleSourceCodegen.olean` into a `Lean.Environment`.
2. Verifies that `Proof.verify_crate` is a theorem whose kernel-checked type is
   `Trusted.CrateTheorem Mir.crate Prog.x86Crate Prog.asmText`.
3. Extracts the raw string literal `Lean.Expr.lit (.strVal committedAsm)` from
   `Prog.asmText` in the `.olean` environment and checks byte-for-byte equality
   with `Prog.s` on disk.
-/

open Lean

def auditOleanAndAsm (env : Environment) (diskAsm : String) : Except String Unit := do
  let some (.thmInfo thmVal) := env.find? ``Proof.verify_crate
    | throw "missing theorem `Proof.verify_crate` in `.olean` environment"
  let expectedType :=
    mkApp3
      (mkConst ``Trusted.CrateTheorem)
      (mkConst ``Mir.crate)
      (mkConst ``Prog.x86Crate)
      (mkConst ``Prog.asmText)
  if thmVal.type != expectedType then
    throw s!"`Proof.verify_crate` type mismatch: got {repr thmVal.type}"
  let some (.defnInfo asmDef) := env.find? ``Prog.asmText
    | throw "missing definition `Prog.asmText` in `.olean` environment"
  let .lit (.strVal committedAsm) := asmDef.value
    | throw s!"`Prog.asmText` is not a literal string constant: {repr asmDef.value}"
  if committedAsm != diskAsm then
    throw "artifact binding mismatch: disk `.s` does not match `.olean` `Prog.asmText`"
  pure ()

def main (args : List String) : IO UInt32 := do
  match args with
  | ["emit", outPath] =>
    IO.FS.writeFile outPath (Trusted.emitX86CrateAsm Prog.x86Crate)
    IO.println s!"emitted verified assembly to {outPath}"
    return 0
  | ["audit", oleanDir, asmPath] =>
    Lean.searchPathRef.modify fun sp => System.FilePath.mk oleanDir :: sp
    let env ← importModules #[{ module := `SingleSourceCodegen }] {}
    let diskAsm ← IO.FS.readFile asmPath
    match auditOleanAndAsm env diskAsm with
    | .ok () =>
      IO.println s!"audit: ok ({asmPath} matches .olean Prog.asmText and Trusted.CrateTheorem)"
      return 0
    | .error msg =>
      IO.eprintln s!"audit: REJECTED ({msg})"
      return 1
  | _ =>
    IO.eprintln "usage: AuditMain.lean [emit <path> | audit <olean_dir> <asm_path>]"
    return 1
