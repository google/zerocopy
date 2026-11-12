#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical taxonomy probe suite for Lean 4.34.1 cross-import elaboration constructs.

Tests 20 distinct mechanisms across 6 categories in Lean 4.34.1
(`5045d0056413266e57c625dcd7c365b10e377c52`) to determine:
1. Whether each construct crosses an `import` boundary from an imported helper/theory
   module (`Hijack.lean`) into a downstream specification module (`Spec.lean`).
2. What constants (`ModuleData.constNames`) and persistent environment extension
   entries (`ModuleData.entries`) `Hijack.lean` records in its `.olean`.
3. Whether `Spec`'s resulting kernel constants contain any reference to `Hijack`
   in `ConstantInfo.getUsedConstantsAsSet` (`declarationEdges`).
4. Whether `Spec`'s elaborated proposition is silently altered to `True` (or another
   target expression) while keeping zero kernel constant-graph edges to `Hijack`.
"""

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

LEAN_BIN = os.environ.get(
    "LEAN_BIN",
    str(Path.home() / ".cache/anneal/toolchain/e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a/lean/bin/lean"),
)
ANNEAL_LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN",
    shutil.which("anneal-lean-run") or os.path.expanduser("~/.local/bin/anneal-lean-run"),
)


def run_lean(args, cwd, env_extra=None):
    cmd = [ANNEAL_LEAN_RUN, "--mode", "file", "--concurrency", "5", "--", LEAN_BIN] + args
    env = os.environ.copy()
    sysroot = str(Path(LEAN_BIN).resolve().parent.parent)
    env["LEAN_SYSROOT"] = sysroot
    env["PATH"] = f"{Path(LEAN_BIN).resolve().parent}:{env.get('PATH', '')}"
    if env_extra:
        env.update(env_extra)
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False)


BASE_TRUSTED = """\
prelude
import Init

namespace Trusted

structure Program where
  code : Nat

structure Specs where
  safety   : Program → Prop
  property : Program → Prop

def Safe (p : Program) : Prop := p.code = 42
def Valid (p : Program) : Prop := p.code = 42

class Checkable (α : Type) where
  check : α → Prop

instance : Checkable Program where
  check p := p.code = 42

-- A benign constant in `Trusted` that returns `True`, NOT marked `@[instance]`.
def trivialCheckable : Checkable Program := { check := fun _ => True }

structure RawInput where
  code : Nat

instance : Coe RawInput Program where
  coe r := { code := r.code }

-- A benign coercion-shaped constant in `Trusted` that maps any `RawInput` to `{ code := 42 }`.
def forgiveInput : Coe RawInput Program := ⟨fun _ => { code := 42 }⟩

-- A benign constant in a nested `Trusted.TrivialStubs` namespace, not opened by `Spec`.
namespace TrivialStubs
def Safe (_p : Program) : Prop := True
end TrivialStubs

-- A benign `OfNat` constant in `Trusted` that maps any literal to `0`.
def zeroOfNat (n : Nat) : OfNat Nat n := ⟨0⟩

@[noinline] def runtimeFlag : Bool := false

end Trusted
"""


PROBES = [
    {
        "id": "A1_notation_high_prio",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "`notation (priority := high)` shadowing identifier/operator",
        "hijack_code": """\
prelude
import Trusted

notation (priority := high) "Trusted.Safe" p:max => (fun _ => True) p
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A2_infix_eq_override",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "`infix:50 (priority := high) \" = \"` overriding equality",
        "hijack_code": """\
prelude
import Trusted

infix:50 (priority := high) " = " => fun _ _ => True
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := p.code = 42
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A3_macro_high_prio",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "`macro (priority := high)` overriding prefix/application syntax",
        "hijack_code": """\
prelude
import Trusted

macro (priority := high) "Trusted.Valid" _p:term:arg : term => `(True)
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Valid p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A4_macro_rules_retroactive_and",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "Retroactive `macro_rules` on existing `Init.Notation` syntax kind (`«term_∧_»`)",
        "hijack_code": """\
prelude
import Trusted

macro_rules
  | `($_a ∧ $_b) => `(True)
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p ∧ Trusted.Valid p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A5_syntax_and_elab",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "`elab (priority := high)` (paired `syntax` + `elab_rules : term`)",
        "hijack_code": """\
prelude
import Trusted
import Lean

elab (priority := high) "Trusted.Safe" _p:term:arg : term =>
  return Lean.mkConst ``True
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A6_elab_rules_term_retroactive_app",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "Retroactive `elab_rules : term` on built-in `Lean.Parser.Term.app` syntax kind",
        "hijack_code": """\
prelude
import Trusted
import Lean

elab_rules (kind := Lean.Parser.Term.app) : term
  | `(Trusted.Safe $_p) => return Lean.mkConst ``True
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "A7_elab_rules_command_declaration",
        "category": "A. Syntax / Notations / Macros / Elaborators",
        "construct": "Retroactive `@[command_elab Lean.Parser.Command.declaration]` intercepting `def` in `namespace Spec`",
        "hijack_code": """\
prelude
import Trusted
import Lean

open Lean Elab Command in
@[command_elab Lean.Parser.Command.declaration]
def hijackDeclElab : CommandElab := fun stx => do
  if (← getCurrNamespace) == `Spec then
    let progTy := mkConst ``Trusted.Program
    let decl := Declaration.defnDecl {
      name := `Spec.claim
      levelParams := []
      type := mkForall `p .default progTy (mkSort .zero)
      value := mkLambda `p .default progTy (mkConst ``True)
      hints := .abbrev
      safety := .safe
    }
    liftCoreM <| addDecl decl
  else
    elabDeclaration stx
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "B1_new_instance_high_prio",
        "category": "B. Typeclasses / Coercions / Literals",
        "construct": "New `instance (priority := high)` defined in `Hijack` (control: leaves edge unless erased)",
        "hijack_code": """\
prelude
import Trusted

instance (priority := high) hijackInst : Trusted.Checkable Trusted.Program where
  check _ := True
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Checkable.check p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "B2_retroactive_attr_instance_on_trusted",
        "category": "B. Typeclasses / Coercions / Literals",
        "construct": "Retroactive `attribute [instance 10000]` on existing `Trusted` constant (`Lean/Meta/Instances.lean:283`)",
        "hijack_code": """\
prelude
import Trusted

attribute [instance 10000] Trusted.trivialCheckable
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Checkable.check p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "B3_retroactive_default_instance_ofnat",
        "category": "B. Typeclasses / Coercions / Literals",
        "construct": "Retroactive `attribute [instance 10000, default_instance 10000]` on `Trusted.zeroOfNat` overriding numeric literals",
        "hijack_code": """\
prelude
import Trusted

attribute [instance 10000, default_instance 10000] Trusted.zeroOfNat
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := p.code = 42
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "B4_retroactive_coe_instance",
        "category": "B. Typeclasses / Coercions / Literals",
        "construct": "Retroactive `attribute [instance 10000]` on `Trusted.forgiveInput` (`Coe` / `CoeOut`)",
        "hijack_code": """\
prelude
import Trusted

attribute [instance 10000] Trusted.forgiveInput
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (r : Trusted.RawInput) : Prop := Trusted.Safe r
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "C1_scoped_notation_with_open",
        "category": "C. Scoped Constructs / Name Resolution / Binders",
        "construct": "`scoped notation` in `namespace Helper` activated when `Spec` uses `open Helper`",
        "hijack_code": """\
prelude
import Trusted

namespace Helper
def benignHelper (x : Nat) : Nat := x
scoped notation (priority := high) "Safe" p:max => (fun _ => True) p
end Helper
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
open Trusted Helper
def claim (p : Program) : Prop := Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "C2_export_alias_zero_constants",
        "category": "C. Scoped Constructs / Name Resolution / Binders",
        "construct": "`export` into `aliasExtension` (`Lean/ResolveName.lean:60-96`) with zero constants in `Hijack`",
        "hijack_code": """\
prelude
import Trusted

namespace Spec
export Trusted.TrivialStubs (Safe)
end Spec
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
open Trusted
def claim (p : Program) : Prop := Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "C3_enclosing_namespace_shadowing",
        "category": "C. Scoped Constructs / Name Resolution / Binders",
        "construct": "Declaring `Spec.Safe` (or `Trusted.Safe` alias) in `Hijack` shadowing `open Trusted` in `namespace Spec`",
        "hijack_code": """\
prelude
import Trusted

namespace Spec
abbrev Safe (_p : Trusted.Program) : Prop := True
end Spec
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
open Trusted
def claim (p : Program) : Prop := Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "C4_variable_and_autoImplicit_file_scoped",
        "category": "C. Scoped Constructs / Name Resolution / Binders",
        "construct": "`variable` and `set_option autoImplicit` (control: confined to per-file `Command.Scope`, does not cross `import`)",
        "hijack_code": """\
prelude
import Trusted

set_option autoImplicit true
variable (unusedImplicit : Nat)
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "D1_structure_default_field_retroactive",
        "category": "D. Structure Default Field Values",
        "construct": "Retroactive `def Trusted.Specs.safety._default` (`Lean/Structure.lean:288`, inlined by `instantiateStructDefaultValueFn?` with zero edges AND zero extension entries)",
        "hijack_code": """\
prelude
import Trusted

def Trusted.Specs.safety._default : Trusted.Program → Prop :=
  id (fun _ => True)
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def specs : Trusted.Specs := {
  property := Trusted.Valid
}
def claim (p : Trusted.Program) : Prop := specs.safety p
end Spec
""",
        "target_const": "Spec.specs",
    },
    {
        "id": "E1_compiler_attrs_csimp_implemented_by",
        "category": "E. Compiler / Elaborator / Pretty-Printer Attributes",
        "construct": "Retroactive `@[csimp]` and `@[implemented_by]` overriding compiled runtime execution without changing kernel `Expr`",
        "hijack_code": """\
prelude
import Trusted

def runtimeFlagTrue : Bool := true

@[csimp] theorem runtimeFlag_eq_true : @Trusted.runtimeFlag = @runtimeFlagTrue := sorry
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "E2_delab_vs_app_unexpander_pp_spoof",
        "category": "E. Compiler / Elaborator / Pretty-Printer Attributes",
        "construct": "`@[delab]` vs. `@[app_unexpander]` spoofing human-reviewed pretty-printer output even under `pp.all = true` + `pp.notation = false` (`Lean/PrettyPrinter/Delaborator/Basic.lean:457`)",
        "hijack_code": """\
prelude
import Trusted
import Lean

@[app_unexpander False]
def unexpandFalse : Lean.PrettyPrinter.Unexpander
  | `($_) => `(Trusted.Safe p)

@[delab app.False]
def delabFalse : Lean.PrettyPrinter.Delaborator.Delab := do
  `(Trusted.Safe p)
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (_p : Trusted.Program) : Prop := False
end Spec
""",
        "target_const": "Spec.claim",
    },
    {
        "id": "F1_initialize_import_time_exec",
        "category": "F. Import-Time Code Execution",
        "construct": "`initialize` / `@[init]` executing arbitrary `IO` during `lean` compilation of downstream `Spec.lean` (`Lean/Environment.lean:1990-1994`)",
        "hijack_code": """\
prelude
import Trusted

initialize
  IO.FS.writeFile "init_side_effect.txt" "EXECUTED_DURING_SPEC_COMPILATION"
""",
        "spec_code": """\
prelude
import Trusted
import Hijack

namespace Spec
def claim (p : Trusted.Program) : Prop := Trusted.Safe p
end Spec
""",
        "target_const": "Spec.claim",
    },
]


INSPECTOR_LEAN_TEMPLATE = """\
prelude
import Trusted
import Hijack
import Spec
import Lean

open Lean

def exprSummary (e : Expr) : String :=
  toString e

unsafe def inspectTarget (targetConstStr : String) : MetaM Unit := do
  let envExts ← getEnv
  let targetConst := targetConstStr.toName
  let optsStrict : Options := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false

  -- 1. Inspect with loadExts := false (matching TrustedBoundary.lean's withImportModules)
  initSearchPath (← findSysroot) [System.FilePath.mk "."]
  let imports := #[{ module := `Trusted }, { module := `Hijack }, { module := `Spec }]
  let envNoExts ← liftM (m := IO) <| importModules (loadExts := false) imports {} 0
  let hijackIdx? := envNoExts.getModuleIdx? `Hijack
  let specIdx? := envNoExts.getModuleIdx? `Spec
  let hijackData := envNoExts.header.moduleData[hijackIdx?.get!]!
  let specData := envNoExts.header.moduleData[specIdx?.get!]!

  let hijackConsts := hijackData.constNames.toList.map toString
  let hijackExtEntries := hijackData.entries.toList.map fun (extName, ents) =>
    Json.mkObj [("extension", toJson (toString extName)), ("count", toJson ents.size)]

  let ci := envNoExts.find? targetConst |>.get!
  let valExpr := ci.value! (allowOpaque := true)
  let usedConsts := (ci.type.getUsedConstantsAsSet ++ valExpr.getUsedConstantsAsSet).toList.map toString
  let usedModules := (ci.type.getUsedConstantsAsSet ++ valExpr.getUsedConstantsAsSet).toList.filterMap fun c =>
    match envNoExts.getModuleIdxFor? c with
    | some idx => some (toString envNoExts.header.moduleNames[idx.toNat]!)
    | none => if specData.constNames.contains c then some "Spec" else none
  let mentionsHijackInEdges := usedModules.contains "Hijack"

  -- Pretty-print under loadExts := false with pp.all = true, pp.notation = false
  let (ppNoExtsStrict, _) ← liftM (m := IO) <|
    (Meta.ppExpr valExpr).run'.toIO { fileName := "<audit>", fileMap := default, options := optsStrict } { env := envNoExts }

  -- 2. Pretty-print under loadExts := true (envExts)
  let (ppExtsDefault, _) ← liftM (m := IO) <|
    (Meta.ppExpr valExpr).run'.toIO { fileName := "<audit>", fileMap := default } { env := envExts }
  let (ppExtsStrict, _) ← liftM (m := IO) <|
    (Meta.ppExpr valExpr).run'.toIO { fileName := "<audit>", fileMap := default, options := optsStrict } { env := envExts }

  let out := Json.mkObj [
    ("hijackConsts", toJson hijackConsts),
    ("hijackExtEntries", Json.arr hijackExtEntries.toArray),
    ("targetConst", toJson targetConstStr),
    ("targetRawExpr", toJson (exprSummary valExpr)),
    ("usedConstants", toJson usedConsts),
    ("usedModules", toJson usedModules.eraseDups),
    ("mentionsHijackInEdges", toJson mentionsHijackInEdges),
    ("ppExtsDefault", toJson (toString ppExtsDefault)),
    ("ppExtsStrict_ppAll_noNotation", toJson (toString ppExtsStrict)),
    ("ppNoExtsStrict_ppAll_noNotation", toJson (toString ppNoExtsStrict))
  ]
  IO.println out.compress

#eval inspectTarget "__TARGET_CONST__"
"""


def main():
    work_root = Path(__file__).resolve().parent / "work_taxonomy"
    if work_root.exists():
        shutil.rmtree(work_root)
    work_root.mkdir(parents=True)

    # Compile Trusted.lean once in a shared base dir
    base_dir = work_root / "base"
    base_dir.mkdir()
    (base_dir / "Trusted.lean").write_text(BASE_TRUSTED)

    res = run_lean(["-o", "Trusted.olean", "Trusted.lean"], cwd=base_dir)
    if res.returncode != 0:
        print("Failed to compile Trusted.lean:", res.stdout, res.stderr, file=sys.stderr)
        sys.exit(1)

    results = []
    for probe in PROBES:
        pdir = work_root / probe["id"]
        pdir.mkdir()
        shutil.copy2(base_dir / "Trusted.lean", pdir / "Trusted.lean")
        shutil.copy2(base_dir / "Trusted.olean", pdir / "Trusted.olean")
        (pdir / "Inspector.lean").write_text(
            INSPECTOR_LEAN_TEMPLATE.replace("__TARGET_CONST__", probe["target_const"])
        )

        (pdir / "Hijack.lean").write_text(probe["hijack_code"])
        (pdir / "Spec.lean").write_text(probe["spec_code"])

        # Compile Hijack.lean
        res_h = run_lean(["-o", "Hijack.olean", "Hijack.lean"], cwd=pdir, env_extra={"LEAN_PATH": str(pdir)})
        if res_h.returncode != 0:
            print(f"[{probe['id']}] Hijack compile failed:\n{res_h.stdout}\n{res_h.stderr}", file=sys.stderr)
            sys.exit(1)

        # Remove side-effect file before compiling Spec.lean so we measure whether compiling Spec.lean triggers it
        side_effect_file = pdir / "init_side_effect.txt"
        if side_effect_file.exists():
            side_effect_file.unlink()

        res_s = run_lean(["-o", "Spec.olean", "Spec.lean"], cwd=pdir, env_extra={"LEAN_PATH": str(pdir)})
        if res_s.returncode != 0:
            print(f"[{probe['id']}] Spec compile failed:\n{res_s.stdout}\n{res_s.stderr}", file=sys.stderr)
            sys.exit(1)

        spec_compile_triggered_io = side_effect_file.exists()

        res_i = run_lean(["Inspector.lean"], cwd=pdir, env_extra={"LEAN_PATH": str(pdir)})
        if res_i.returncode != 0:
            print(f"[{probe['id']}] Inspector failed:\n{res_i.stdout}\n{res_i.stderr}", file=sys.stderr)
            sys.exit(1)

        data = json.loads(res_i.stdout.strip().splitlines()[-1])
        data["id"] = probe["id"]
        data["category"] = probe["category"]
        data["construct"] = probe["construct"]
        data["spec_compile_triggered_io"] = spec_compile_triggered_io
        results.append(data)
        print(
            f"[PASS] {probe['id']}: edges_to_Hijack={data['mentionsHijackInEdges']} "
            f"exts={[e['extension'] for e in data['hijackExtEntries']]} "
            f"expr={data['targetRawExpr']}"
        )

    out_path = Path(__file__).resolve().parent / "taxonomy_results.json"
    out_path.write_text(json.dumps(results, indent=2) + "\n")
    print(f"\nWrote {len(results)} probe results to {out_path}")


if __name__ == "__main__":
    main()
