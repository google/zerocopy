import Lean

open Lean

def main : IO Unit := do
  IO.println "=== Probe(d) Probe: CVE-2026-72711 (#14484), CVE-2026-72844 (#14576), and lean4#14875 in Lean v4.34.1 ==="

  -- =========================================================================
  -- 1. CVE-2026-72711 (`leanprover/lean4#14484`, PR `#14498` `7346219967957ca3dd4302a75a849b67eed1b3cd`)
  --    `environment::add_opaque` missing `check_no_metavar_no_fvar` on `v.get_value()`
  -- =========================================================================
  let src14484 :=
"import Lean
open Lean

private def cachePrimingType : Expr :=
  let falseE := mkConst ``False
  let falseToFalse := .forallE `h falseE falseE .default
  let identity := .lam `h falseE (.bvar 0) .default
  .app (.lam `_ falseToFalse falseE .default) identity

run_meta do
  let name := `opaqueFVarCacheFalse
  addDecl <| .opaqueDecl {
    name
    levelParams := []
    type := cachePrimingType
    value := .fvar { name := .num `_kernel_fresh 2 }
    isUnsafe := false
  }
"
  IO.FS.writeFile "Test14484.lean" src14484
  let out14484 ← IO.Process.output { cmd := "lean", args := #["Test14484.lean"] }
  IO.println s!"[1] Testing CVE-2026-72711 (`lean4#14484`, `add_opaque` with fvar in value) on Lean v4.34.1:"
  IO.println s!"    exitCode = {out14484.exitCode} (expected 1 — FIXED in v4.34.1 via PR #14498 `7346219967`)"
  IO.println s!"    output   = {out14484.stdout.trimAscii}"

  -- =========================================================================
  -- 2. CVE-2026-72844 (`leanprover/lean4#14576`, PR `#14577` `a39eab69e1eee9ad38f4efe507907b1026a77808`)
  --    Nested inductive parameter erasure in `elim_nested_inductive_fn`
  -- =========================================================================
  let src14576 :=
"import Lean
open Lean Elab Command

structure C where b : Bool
inductive W : Type where | mk (p : Bool)
inductive L (α : Type) (b : Bool) : Type where | mk

meta def build : CommandElabM Unit := do
  let w := mkBVar 0
  let Ew := mkApp (mkConst `E) w
  let b := mkProj ``C 0 (mkProj ``C 0 w)
  let l := mkApp2 (mkConst ``L) Ew b
  let Et := mkForall `w .default (mkConst ``W) (mkSort 1)
  let ct := mkForall `w .default (mkConst ``W) <|
    mkForall `l .default l (mkApp (mkConst `E) (mkBVar 1))
  liftCoreM <| addDecl <| .inductDecl [] 1 [{
    name := `E, type := Et, ctors := [{ name := `E.mk, type := ct }] }] false

elab \"mkbug\" : command => build
mkbug
"
  IO.FS.writeFile "Test14576.lean" src14576
  let out14576 ← IO.Process.output { cmd := "lean", args := #["Test14576.lean"] }
  IO.println s!"\n[2] Testing CVE-2026-72844 (`lean4#14576`, `elim_nested_inductive_fn` ill-typed param) on Lean v4.34.1:"
  IO.println s!"    exitCode = {out14576.exitCode} (expected 1 — FIXED in v4.34.1 via PR #14577 `a39eab69e1`)"
  IO.println s!"    output   = {out14576.stdout.trimAscii}"

  -- =========================================================================
  -- 3. `leanprover/lean4#14875` (`public class inductive` + `import all` private leak across `.olean`)
  -- =========================================================================
  -- Module A (`Mod14875A.lean`): defines `private def ClassHidden : Prop := False`.
  let src14875A :=
"module

private def ClassHidden : Prop := False
"
  -- Module B (`Mod14875B.lean`): uses `import all Mod14875A` and declares `public class inductive Leaks : Prop`
  -- with a `private` constructor taking `ClassHidden`, plus `public theorem leaks_imp_false : Leaks → False`.
  -- Because `Environment.addDeclCore` (`Environment.lean:724`) has `if true /- !isPrivateName n-/`,
  -- both `_private.Mod14875B.0.Leaks.mk` and `Leaks.rec` (referencing `_private.Mod14875A.0.ClassHidden`)
  -- are exported into `Mod14875B.olean` (`.exported`), even though `_private.Mod14875A.0.ClassHidden`
  -- is NOT in `Mod14875A.olean` or `Mod14875B.olean`!
  let src14875B :=
"module
import all Mod14875A

public class inductive Leaks : Prop where
  | private mk (h : ClassHidden) : Leaks

public theorem leaks_imp_false (l : Leaks) : False :=
  Leaks.rec (fun h => h) l
"
  IO.FS.writeFile "Mod14875A.lean" src14875A
  IO.FS.writeFile "Mod14875B.lean" src14875B

  let outA ← IO.Process.output { cmd := "lean", args := #["-o", "Mod14875A.olean", "Mod14875A.lean"] }
  let outB ← IO.Process.output { cmd := "lean", args := #["-o", "Mod14875B.olean", "Mod14875B.lean"] }
  IO.println s!"\n[3] Testing `lean4#14875` (`public class inductive` + `import all` private leak in `.olean`) on Lean v4.34.1:"
  IO.println s!"    Compiling Mod14875A.lean: exitCode={outA.exitCode}"
  if outA.exitCode != 0 then IO.println s!"    Mod14875A stdout: {outA.stdout.trimAscii}"
  IO.println s!"    Compiling Mod14875B.lean: exitCode={outB.exitCode}"
  if outB.exitCode != 0 then IO.println s!"    Mod14875B stdout: {outB.stdout.trimAscii}"

  -- Inspect `Mod14875A.olean` (.exported) vs `Mod14875B.olean` (.exported)!
  let (dataA, _) ← readModuleData "Mod14875A.olean"
  let (dataB, _) ← readModuleData "Mod14875B.olean"
  IO.println s!"    Mod14875A.olean (.exported) constNames: {dataA.constNames}"
  IO.println s!"    Mod14875B.olean (.exported) constNames: {dataB.constNames}"
  let privName := (Name.mkNum (Name.mkStr2 "_private" "Mod14875A") 0).str "ClassHidden"
  for ci in dataB.constants do
    if ci.name == `Leaks.rec then
      let leaksPriv := ci.type.getUsedConstants.contains privName
      IO.println s!"    `Leaks.rec` in Mod14875B.olean (.exported) type:\n      {ci.type}"
      IO.println s!"    Does `Leaks.rec` in Mod14875B.olean reference `{privName}` (missing from Mod14875A.olean)? {leaksPriv}"

  -- Now test downstream `Mod14875C.lean` (`module`, `import Mod14875B`):
  -- Because `Mod14875B` only did `import all Mod14875A` (private import) and `Mod14875A.olean` does not contain
  -- `_private.Mod14875A.0.ClassHidden`, what happens if `Mod14875A` is recompiled with `private def ClassHidden : Prop := True`
  -- (which leaves `Mod14875A.olean` byte-for-byte identical, since private defs are omitted from `.olean`!)
  -- and `Mod14875C.lean` (`import Mod14875B`, `import all Mod14875A`) is compiled WITHOUT rebuilding `Mod14875B.olean`,
  -- OR `Mod14875C.lean` defines `_private.Mod14875A.0.ClassHidden := True` and constructs `Leaks`?!
  let src14875C :=
"module
import Mod14875B
public import Lean

open Lean

-- In Mod14875C, `_private.Mod14875A.0.ClassHidden` is NOT in the environment at all!
-- So the kernel allows adding `_private.Mod14875A.0.ClassHidden : Prop := True` as a normal safe definition!
run_elab do
  let privHidden := (Name.mkNum (Name.mkStr2 \"_private\" \"Mod14875A\") 0).str \"ClassHidden\"
  let privMk     := (Name.mkNum (Name.mkStr2 \"_private\" \"Mod14875B\") 0).str \"Leaks\" |>.str \"mk\"
  addDecl <| .defnDecl {
    name := privHidden
    levelParams := []
    type := mkSort .zero
    value := mkConst ``True
    hints := .abbrev
    safety := .safe
  }
  addDecl <| .thmDecl {
    name := `boom14875
    levelParams := []
    type := mkConst ``False
    value := mkApp (mkConst `leaks_imp_false) (mkApp (mkConst privMk) (mkConst ``True.intro))
  }
"
  IO.FS.writeFile "Mod14875C.lean" src14875C
  let outC ← IO.Process.output { cmd := "lean", args := #["-o", "Mod14875C.olean", "Mod14875C.lean"] }
  IO.println s!"    Compiling Mod14875C.lean (proving `boom14875 : False` via leaked private ctor/recursor): exitCode={outC.exitCode} (STILL REPRODUCES IN v4.34.1!)"
  if outC.exitCode != 0 then IO.println s!"    Mod14875C stdout: {outC.stdout.trimAscii}"

  -- Now test `leanchecker` (default incremental mode) vs `leanchecker --fresh` on `Mod14875A`, `Mod14875B`, `Mod14875C`!
  for modName in ["Mod14875A", "Mod14875B", "Mod14875C"] do
    let lcDef ← IO.Process.output { cmd := "leanchecker", args := #[modName] }
    IO.println s!"    Running `leanchecker {modName}` (default mode): exitCode={lcDef.exitCode} {lcDef.stderr.trimAscii}"
  let lcFresh14875 ← IO.Process.output { cmd := "leanchecker", args := #["--fresh", "Mod14875C"] }
  IO.println s!"    Running `leanchecker --fresh Mod14875C`: exitCode={lcFresh14875.exitCode}"
  if lcFresh14875.exitCode != 0 then
    IO.println s!"    leanchecker --fresh stderr: {lcFresh14875.stderr.trimAscii}"
