#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""End-to-end Starnix `Spec.lean` zero-character-modification hijack probes and
architectural defense comparison against `TrustedBoundary.lean` (`2fb744d6ecb5`).

Demonstrates:
1. How a zero-byte-modified `Spec.lean` in the Starnix `apply_endianness` fixture
   is silently hijacked across `import` boundaries so that a broken Rust program
   (`zeroBody` / `constant_zero`, which always returns `0`) passes unmodified
   `TrustedBoundary.lean` (`exit 0`, `"ok": true`) while leaving:
   - zero constant-graph edges (`declarationEdges`) to the hijacking module, and
   - the exact same `specificationClosure` module and constant list as the
     legitimate Starnix proof (`["Endianness", "Spec", "Trusted.Mvp.Semantics",
     "Trusted.Mvp.Syntax"]`).
2. Empirical evaluation of the three architectural defenses:
   - Defense 1: Strict `Spec` Import & Role Isolation (`checkRoleImports` on
     `data.imports` + `validateLocalConstant` + `._default` ban + pure-syntax
     `SpecDefs` separation from `TheoryProofs`).
   - Defense 2: Environment Extension Diffing (`checkSpecificationExtensions` on
     `ModuleData.entries` across the transitive `import` closure of `Spec`).
   - Defense 3: Kernel-Level Canonical Statement Printing (`loadExts := false`,
     `pp.all = true`, `pp.notation = false`, plus unfolded `Spec.specs` raw
     kernel `Expr` and SHA-256 digest in the TCB audit output).
"""

import hashlib
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
LEAN_SYSROOT = Path(LEAN_BIN).resolve().parent.parent
ANNEAL_LEAN_RUN = os.environ.get(
    "ANNEAL_LEAN_RUN",
    shutil.which("anneal-lean-run") or os.path.expanduser("~/.local/bin/anneal-lean-run"),
)
MVP_ROOT = Path(os.environ.get("ANNEAL_MVP_ROOT", str(Path.home() / "workspace/anneal/.agent-worktrees/joshlf-mvp")))
STARNIX_PROOF_DIR = MVP_ROOT / "trusted/cargo-anneal/tests/fixtures/starnix/proof"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def run_lean(args, cwd, env_extra=None):
    cmd = [ANNEAL_LEAN_RUN, "--mode", "file", "--concurrency", "5", "--", LEAN_BIN] + args
    env = os.environ.copy()
    sysroot = str(Path(LEAN_BIN).resolve().parent.parent)
    env["LEAN_SYSROOT"] = sysroot
    env["PATH"] = f"{Path(LEAN_BIN).resolve().parent}:{env.get('PATH', '')}"
    if env_extra:
        env.update(env_extra)
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, check=False)


# Broken Captured.lean: uses `zeroBody` (`constant_zero` from `SourceInputs.lean`,
# which ignores `be`, `width`, and `value` and always returns `0`).
CAPTURED_ZERO_PROGRAM = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace Captured

open Trusted.Mvp

def zeroBody : Body :=
  { argCount := 3
  , isUnsafe := false
  , localTys := [Ty.int 64 false, Ty.bool, Ty.enum 1363 [0, 1, 2, 3], Ty.int 64 false]
  , blocks :=
      [ { statements :=
            [ Statement.assign 0
                (Rvalue.use (Operand.constant (Ty.int 64 false) 0) true) ]
        , terminator := Terminator.ret } ] }

def program : Program :=
  { scope := .unit
  , bodies := [zeroBody] }

end Captured
"""

EXPECTED_LEAN = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp
import Captured
import Spec

namespace Expected
def claim : Prop := _root_.Trusted.Mvp.UnitTheorem _root_.Captured.program _root_.Spec.specs
end Expected
"""

# Stealth hijack module `BitTheory.lean`:
# Rewrites the inner conjunction in `Spec.lean` (`words = [...] ∧ Endianness.expectedEndianWords ...`)
# into `Endianness.expectedEndianWords ... = Endianness.expectedEndianWords ...` (which is trivially
# `True` by `rfl` while preserving `Endianness.expectedEndianWords` in `Spec.specs`'s kernel `Expr`
# so `specificationClosure` has the EXACT same module and constant list as the genuine Starnix proof!).
BIT_THEORY_STEALTH_HIJACK = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Trusted.Mvp

namespace BitTheory

macro_rules
  | `($lhs ∧ $er:ident $b ∧ $ele:ident $b2 ∧ $inv:ident $b3) =>
    `($lhs ∧ (($er $b ∧ $ele $b2 ∧ $inv $b3) = ($er $b ∧ $ele $b2 ∧ $inv $b3)))

end BitTheory
"""

# Proof that `zeroProgram` (which always returns `0`!) satisfies `Expected.claim`
# once `Spec.specs` has been hijacked by `BitTheory.lean`.
PROOF_FOR_ZERO_PROGRAM = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import SourceInputs

namespace Proof

open Trusted.Mvp Anneal.Mvp Endianness

theorem verify : Expected.claim := by
  refine ⟨rfl, ?_, ?_⟩
  · intro id body found
    change ([Captured.zeroBody] : List Body)[id]? = some body at found
    cases id with
    | zero =>
      injection found with hbody
      subst hbody
      refine bodyVerified_of_finite_runs Captured.zeroBody 1363 rfl rfl rfl rfl ?_ (Spec.specs.safety 0)
      intro flag width value
      exact ⟨2, 0, rfl⟩
    | succ id =>
      cases found
  · exact ⟨Captured.zeroBody, rfl, rfl⟩

end Proof
"""


# Hardened TrustedBoundary.lean combining:
# - Defense 1: Role-Based Import Graph Check (`r.allows d` on `data.imports`) +
#              `validateLocalConstant` (`Trusted` namespace reservation) +
#              `<projFn>._default` / `_inherited_default` / `_autoParam` ban on target modules
# - Defense 2: Environment Extension Diffing (`checkSpecificationExtensions`) on all modules
#              in the import closure of `Spec` (`specification`)
# - Defense 3: Kernel-Level Canonical Statement Printing (`loadExts := false`, `pp.all = true`,
#              `pp.notation = false`, plus unfolded `Spec.specs` raw kernel `Expr` & SHA-256)
HARDENED_PATCH_TARGET = """inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq"""

HARDENED_PATCH_REPLACEMENT = """inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq

instance : ToString TargetRole where
  toString
    | .model => "model"
    | .specification => "specification"
    | .capture => "capture"
    | .expected => "expected"
    | .proof => "proof"

def forbiddenSpecExtensions : List Name :=
  [ `Lean.Parser.parserExtension
  , `Lean.Elab.macroAttribute
  , `Lean.Elab.Term.termElabAttribute
  , `Lean.Elab.Command.commandElabAttribute
  , `Lean.Meta.instanceExtension
  , `Lean.Meta.defaultInstanceExtension
  , `Lean.aliasExtension
  , `Lean.PrettyPrinter.Delaborator.delabAttribute
  , `Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute
  , `Lean.Compiler.ImplementedBy.implementedByAttr
  , `Lean.externAttr
  , `Lean.Compiler.CSimp.ext
  , `Lean.regularInitAttr
  , `Lean.builtinInitAttr ]

def hasDefaultFieldSuffix : Name → Bool
  | .str _ "_default" => true
  | .str _ "_inherited_default" => true
  | .str _ "_autoParam" => true
  | _ => false"""

HARDENED_LOOP_TARGET = """  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    if let .source _ := role then
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      for ci in data.constants do"""

HARDENED_LOOP_REPLACEMENT = """  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    -- Defense 1a: Enforce role authority on module-level `data.imports`
    for imp in data.imports do
      let some impRole := roles.get? imp.module
        | fail s!"foreign target module {imp.module}"
      match role, impRole with
      | .source r, .source d =>
        unless r.allows d do
          fail s!"target import authority violation {m.module} ({r}) imports {imp.module} ({d})"
      | .library, .source _ =>
        fail s!"installed library {m.module} imports target source {imp.module}"
      | .foundation, .library | .foundation, .source _ =>
        fail s!"foundation module {m.module} imports non-foundation {imp.module}"
      | _, _ => pure ()
    -- Defense 2: Environment Extension Diffing on `specification` modules
    if let .source .specification := role then
      for (extName, ents) in data.entries do
        if forbiddenSpecExtensions.contains extName && !ents.isEmpty then
          fail s!"forbidden environment extension {extName} ({ents.size} entries) in specification module {m.module}"
    if let .source r := role then
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      for ci in data.constants do
        -- Defense 1b: Enforce `Trusted` namespace reservation & forbid retroactive structure field `_default` in non-model modules
        if r != .model then
          if (privateToUserName ci.name).getRoot == `Trusted then
            fail s!"non-model module {m.module} defines constant in Trusted namespace: {ci.name}"
          if hasDefaultFieldSuffix (privateToUserName ci.name) then
            fail s!"target module {m.module} defines structure field default hook: {ci.name}\""""

HARDENED_RESULT_TARGET = """  return Json.mkObj [("theorem", toJson theoremName),"""

HARDENED_RESULT_REPLACEMENT = """  -- Defense 3: Kernel-level canonical statement printing under `loadExts := false`
  let specInfo ← lookup specName
  let some specVal := specInfo.value? true | fail "specification has no stored body"
  let optsStrict : Options := ({} : Options).setBool `pp.all true |>.setBool `pp.notation false
  let (ppSpecStrict, _) ←
    (Meta.ppExpr specVal).run'.toIO { fileName := "<audit>", fileMap := default, options := optsStrict } { env := env }
  let (ppExpectedStrict, _) ←
    (Meta.ppExpr theoremInfo.type).run'.toIO { fileName := "<audit>", fileMap := default, options := optsStrict } { env := env }
  return Json.mkObj [("theorem", toJson theoremName),
    ("canonicalSpecPrettyPrint", toJson (toString ppSpecStrict)),
    ("canonicalSpecRawExpr", toJson (toString specVal)),
    ("canonicalTheoremTypePrettyPrint", toJson (toString ppExpectedStrict)),"""


def build_foundation_and_library_admission():
    foundation_lock = json.loads((MVP_ROOT / "trusted/lean/foundation-lock.json").read_text())
    library_lock = json.loads((MVP_ROOT / "trusted/audit/library-lock.json").read_text())
    olean_parts = ["olean", "olean.server", "olean.private"]
    ir_parts = ["ir.sig", "ir"]

    def mod_artifacts(mod_name: str, record: dict):
        rel = mod_name.replace(".", "/")
        op = [
            str(LEAN_SYSROOT / "lib/lean" / f"{rel}.{p}")
            for p in olean_parts
            if record["parts"].get(p) is not None
        ]
        ip = [
            str(LEAN_SYSROOT / "lib/lean" / f"{rel}.{p}")
            for p in ir_parts
            if record["parts"].get(p) is not None
        ]
        return [op, ip]

    artifacts = {}
    graph = {}
    foundation_mods = sorted(foundation_lock["modules"].keys())
    for m in foundation_mods:
        artifacts[m] = mod_artifacts(m, foundation_lock["modules"][m])
        graph[m] = foundation_lock["graph"][m]

    # Admit library closure for Starnix imports
    lib_roots = [
        "Init.Data.BitVec.Basic",
        "Init.Data.List.Basic",
        "Init.Data.BitVec.Lemmas",
        "Init.Data.Option.Lemmas",
    ]
    pending = list(lib_roots)
    needed = set()
    while pending:
        m = pending.pop()
        if m in foundation_lock["modules"] or m not in library_lock["modules"] or m in needed:
            continue
        needed.add(m)
        for edge in library_lock["graph"][m]:
            pending.append(edge["module"])

    library_mods = sorted(needed)
    for m in library_mods:
        artifacts[m] = mod_artifacts(m, library_lock["modules"][m])
        graph[m] = library_lock["graph"][m]

    return {
        "axioms": foundation_lock["axioms"],
        "foundation": foundation_mods,
        "libraries": library_mods,
        "artifacts": artifacts,
        "graph": graph,
    }


def compile_with_setup(mod_name: str, src_path: Path, lib_dir: Path, imports: list, import_arts: dict, work_root: Path):
    rel = mod_name.replace(".", "/")
    olean_out = lib_dir / f"{rel}.olean"
    olean_out.parent.mkdir(parents=True, exist_ok=True)
    setup_obj = {
        "name": mod_name,
        "isModule": False,
        "imports": imports,
        "importArts": import_arts,
        "dynlibs": [],
        "plugins": [],
        "options": {},
    }
    setup_path = work_root / f"{mod_name}.setup.json"
    setup_path.write_text(json.dumps(setup_obj))
    res = run_lean(
        ["--setup", str(setup_path), "-o", str(olean_out), str(src_path)],
        cwd=work_root,
    )
    assert res.returncode == 0, f"Failed to compile {mod_name}:\n{res.stdout}\n{res.stderr}"
    import_arts[mod_name] = [[str(olean_out)], []]
    return olean_out


def main():
    work_root = Path(__file__).resolve().parent / "work_starnix"
    if work_root.exists():
        shutil.rmtree(work_root)
    work_root.mkdir(parents=True)

    src_dir = work_root / "src"
    lib_dir = work_root / "lib"
    src_dir.mkdir()
    lib_dir.mkdir()

    base_adm = build_foundation_and_library_admission()
    import_arts = dict(base_adm["artifacts"])
    full_graph = dict(base_adm["graph"])

    # 1. Stage Trusted.Mvp, Anneal.Mvp.Execution, Unmodified Spec.lean, BitTheory.lean, Endianness.lean, Captured.lean (`zeroBody`), Expected.lean, Proof.lean
    (src_dir / "Trusted/Mvp").mkdir(parents=True)
    for rel in ["Trusted/Mvp/Syntax.lean", "Trusted/Mvp/Semantics.lean", "Trusted/Mvp.lean"]:
        shutil.copy2(MVP_ROOT / "trusted/lean" / rel, src_dir / rel)
    (src_dir / "Anneal/Mvp").mkdir(parents=True)
    shutil.copy2(MVP_ROOT / "theory/Anneal/Mvp/Execution.lean", src_dir / "Anneal/Mvp/Execution.lean")

    orig_spec_path = STARNIX_PROOF_DIR / "Spec.lean"
    orig_spec_text = orig_spec_path.read_text()
    orig_spec_sha = sha256_text(orig_spec_text)
    (src_dir / "Spec.lean").write_text(orig_spec_text)
    shutil.copy2(STARNIX_PROOF_DIR / "Inputs.lean", src_dir / "Inputs.lean")
    shutil.copy2(STARNIX_PROOF_DIR / "SourceInputs.lean", src_dir / "SourceInputs.lean")

    (src_dir / "BitTheory.lean").write_text(BIT_THEORY_STEALTH_HIJACK)
    orig_endianness_text = (STARNIX_PROOF_DIR / "Endianness.lean").read_text()
    hijacked_endianness_text = orig_endianness_text.replace(
        "import Init.Data.BitVec.Lemmas\n",
        "import Init.Data.BitVec.Lemmas\nimport BitTheory\n",
    )
    assert hijacked_endianness_text != orig_endianness_text
    (src_dir / "Endianness.lean").write_text(hijacked_endianness_text)

    (src_dir / "Captured.lean").write_text(CAPTURED_ZERO_PROGRAM)
    (src_dir / "Expected.lean").write_text(EXPECTED_LEAN)
    (src_dir / "Proof.lean").write_text(PROOF_FOR_ZERO_PROGRAM)

    target_mod_specs = [
        ("Trusted.Mvp.Syntax", src_dir / "Trusted/Mvp/Syntax.lean", "model", [{"module": "Init.Data.BitVec.Basic", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Init.Data.List.Basic", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Trusted.Mvp.Semantics", src_dir / "Trusted/Mvp/Semantics.lean", "model", [{"module": "Trusted.Mvp.Syntax", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Trusted.Mvp", src_dir / "Trusted/Mvp.lean", "model", [{"module": "Trusted.Mvp.Syntax", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Trusted.Mvp.Semantics", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Anneal.Mvp.Execution", src_dir / "Anneal/Mvp/Execution.lean", "proof", [{"module": "Trusted.Mvp.Semantics", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Init.Data.BitVec.Lemmas", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Init.Data.Option.Lemmas", "isMeta": False, "isExported": True, "importAll": False}]),
        ("BitTheory", src_dir / "BitTheory.lean", "proof", [{"module": "Trusted.Mvp", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Endianness", src_dir / "Endianness.lean", "specification", [{"module": "Init.Data.BitVec.Lemmas", "isMeta": False, "isExported": True, "importAll": False}, {"module": "BitTheory", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Inputs", src_dir / "Inputs.lean", "proof", [{"module": "Endianness", "isMeta": False, "isExported": True, "importAll": False}]),
        ("SourceInputs", src_dir / "SourceInputs.lean", "proof", [{"module": "Anneal.Mvp.Execution", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Inputs", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Captured", src_dir / "Captured.lean", "capture", [{"module": "Trusted.Mvp", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Spec", src_dir / "Spec.lean", "specification", [{"module": "Trusted.Mvp", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Endianness", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Expected", src_dir / "Expected.lean", "expected", [{"module": "Trusted.Mvp", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Captured", "isMeta": False, "isExported": True, "importAll": False}, {"module": "Spec", "isMeta": False, "isExported": True, "importAll": False}]),
        ("Proof", src_dir / "Proof.lean", "proof", [{"module": "Expected", "isMeta": False, "isExported": True, "importAll": False}, {"module": "SourceInputs", "isMeta": False, "isExported": True, "importAll": False}]),
    ]

    for mod_name, src_path, _role, imps in target_mod_specs:
        compile_with_setup(mod_name, src_path, lib_dir, imps, import_arts, work_root)
        full_graph[mod_name] = imps

    # Verify Spec.lean on disk is STILL byte-for-byte identical to the upstream fixture
    assert sha256_text((src_dir / "Spec.lean").read_text()) == orig_spec_sha

    # 5. Stage Unmodified TrustedBoundary.lean (`2fb744d6ecb5`) and Hardened TrustedBoundary.lean
    orig_tb_text = (MVP_ROOT / "trusted/audit/TrustedBoundary.lean").read_text()
    unmod_tb_path = work_root / "TrustedBoundaryUnmodified.lean"
    unmod_tb_path.write_text(orig_tb_text)

    assert HARDENED_PATCH_TARGET in orig_tb_text
    assert HARDENED_LOOP_TARGET in orig_tb_text
    assert HARDENED_RESULT_TARGET in orig_tb_text
    hardened_tb_text = (
        orig_tb_text.replace(HARDENED_PATCH_TARGET, HARDENED_PATCH_REPLACEMENT, 1)
        .replace(HARDENED_LOOP_TARGET, HARDENED_LOOP_REPLACEMENT, 1)
        .replace(HARDENED_RESULT_TARGET, HARDENED_RESULT_REPLACEMENT, 1)
    )
    hard_tb_path = work_root / "TrustedBoundaryHardened.lean"
    hard_tb_path.write_text(hardened_tb_text)

    # 6. Build target-audit request JSON for two role configurations:
    # Case 2A: BitTheory has role "proof" (imported by Endianness with role "specification")
    # Case 2B: BitTheory has role "specification" (representing a shared helper/theory module allowed in specification closure)
    def make_request(bit_theory_role: str):
        return {
            "mode": "target-audit",
            "sysroot": str(LEAN_SYSROOT),
            "foundation": base_adm["foundation"],
            "libraries": base_adm["libraries"],
            "axioms": base_adm["axioms"],
            "artifacts": [[k, v] for k, v in sorted(import_arts.items())],
            "graph": full_graph,
            "target": {
                "modules": [
                    {
                        "module": m_name,
                        "source": str(m_src),
                        "expectedSha256": sha256_text(m_src.read_text()),
                        "role": (bit_theory_role if m_name == "BitTheory" else m_role),
                    }
                    for m_name, m_src, m_role, _imps in target_mod_specs
                ],
                "theoremModule": "Proof",
                "theoremName": "Proof.verify",
                "expectedModule": "Expected",
                "expectedDeclaration": "Expected.claim",
                "canonicalRoot": "Trusted.Mvp.UnitTheorem",
                "subjectDeclaration": "Captured.program",
                "specificationDeclaration": "Spec.specs",
                "bindings": {
                    "requestSha256": "0" * 64,
                    "captureSha256": "1" * 64,
                    "modelManifestSha256": "2" * 64,
                    "specificationManifestSha256": orig_spec_sha,
                },
            },
        }

    req_proof_role = work_root / "req_bit_theory_proof_role.json"
    req_spec_role = work_root / "req_bit_theory_spec_role.json"
    req_proof_role.write_text(json.dumps(make_request("proof"), indent=2))
    req_spec_role.write_text(json.dumps(make_request("specification"), indent=2))

    # Run Unmodified TrustedBoundary on Case 2A (`BitTheory` = `proof`)
    res_unmod_2a_path = work_root / "res_unmod_2a.json"
    proc_unmod_2a = run_lean(
        ["-j1", "-M2048", "--run", str(unmod_tb_path), str(req_proof_role), str(res_unmod_2a_path)],
        cwd=work_root,
    )
    res_unmod_2a = json.loads(res_unmod_2a_path.read_text())

    # Run Unmodified TrustedBoundary on Case 2B (`BitTheory` = `specification`, which passes `target.rs` import check too!)
    res_unmod_2b_path = work_root / "res_unmod_2b.json"
    proc_unmod_2b = run_lean(
        ["-j1", "-M2048", "--run", str(unmod_tb_path), str(req_spec_role), str(res_unmod_2b_path)],
        cwd=work_root,
    )
    res_unmod_2b = json.loads(res_unmod_2b_path.read_text())

    # Run Hardened TrustedBoundary on Case 2A (`BitTheory` = `proof` -> caught by Defense 1a `checkRoleImports`)
    res_hard_2a_path = work_root / "res_hard_2a.json"
    proc_hard_2a = run_lean(
        ["-j1", "-M2048", "--run", str(hard_tb_path), str(req_proof_role), str(res_hard_2a_path)],
        cwd=work_root,
    )
    res_hard_2a = json.loads(res_hard_2a_path.read_text())

    # Run Hardened TrustedBoundary on Case 2B (`BitTheory` = `specification` -> passes Defense 1a, caught by Defense 2 `checkSpecificationExtensions`)
    res_hard_2b_path = work_root / "res_hard_2b.json"
    proc_hard_2b = run_lean(
        ["-j1", "-M2048", "--run", str(hard_tb_path), str(req_spec_role), str(res_hard_2b_path)],
        cwd=work_root,
    )
    res_hard_2b = json.loads(res_hard_2b_path.read_text())

    # Also test Defense 3 (canonical statement printing on the hijacked `Spec.specs`) by running
    # TrustedBoundary with Defense 3 enabled
    tb_def3_only = orig_tb_text.replace(HARDENED_RESULT_TARGET, HARDENED_RESULT_REPLACEMENT, 1)
    tb_def3_path = work_root / "TrustedBoundaryDef3Only.lean"
    tb_def3_path.write_text(tb_def3_only)
    res_def3_path = work_root / "res_def3.json"
    proc_def3 = run_lean(
        ["-j1", "-M2048", "--run", str(tb_def3_path), str(req_proof_role), str(res_def3_path)],
        cwd=work_root,
    )
    res_def3 = json.loads(res_def3_path.read_text())

    def summarize_closure(closure_list):
        if not closure_list:
            return {}
        non_init = [d for d in closure_list if not d["module"].startswith("Init")]
        return {
            "total_declarations": len(closure_list),
            "non_foundation_modules": sorted({d["module"] for d in non_init}),
            "non_foundation_declarations": non_init,
            "bit_theory_in_specification_closure": any(d["module"] == "BitTheory" for d in closure_list),
        }

    summary = {
        "starnix_spec_lean_sha256_original": orig_spec_sha,
        "starnix_spec_lean_sha256_during_hijack": sha256_text((src_dir / "Spec.lean").read_text()),
        "spec_lean_zero_bytes_modified": orig_spec_sha == sha256_text((src_dir / "Spec.lean").read_text()),
        "subject_program": "Captured.zeroBody (constant_zero: ignores endianness flag, width, and input word; always returns 0)",
        "unmodified_trusted_boundary_2a_bit_theory_proof_role": {
            "exit_code": proc_unmod_2a.returncode,
            "ok": res_unmod_2a.get("ok"),
            "specificationClosure_summary": summarize_closure(res_unmod_2a.get("result", {}).get("specificationClosure", [])),
            "replayedDeclarations": res_unmod_2a.get("result", {}).get("replayedDeclarations"),
        },
        "unmodified_trusted_boundary_2b_bit_theory_specification_role": {
            "exit_code": proc_unmod_2b.returncode,
            "ok": res_unmod_2b.get("ok"),
            "specificationClosure_summary": summarize_closure(res_unmod_2b.get("result", {}).get("specificationClosure", [])),
            "replayedDeclarations": res_unmod_2b.get("result", {}).get("replayedDeclarations"),
        },
        "hardened_defense_1a_import_role_check_on_2a": {
            "exit_code": proc_hard_2a.returncode,
            "response": res_hard_2a,
        },
        "hardened_defense_2_ext_diffing_on_2b_when_import_allowed": {
            "exit_code": proc_hard_2b.returncode,
            "response": res_hard_2b,
        },
        "defense_3_canonical_printing_exposes_hijack": {
            "exit_code": proc_def3.returncode,
            "canonicalSpecPrettyPrint": res_def3.get("result", {}).get("canonicalSpecPrettyPrint"),
            "canonicalSpecRawExpr": res_def3.get("result", {}).get("canonicalSpecRawExpr"),
            "canonicalTheoremTypePrettyPrint": res_def3.get("result", {}).get("canonicalTheoremTypePrettyPrint"),
        },
    }

    out_path = Path(__file__).resolve().parent / "starnix_hijack_and_defenses.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
