#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Adversarial probe suite for TrustedBoundary.lean.

Executes Phase 1 (`preflight`) and Phase 2 (`audit`) of `TrustedBoundary.lean`
across `main` (`24367bd1a8c784f2578535954f9915e24894a56f`), `pr-65`
(`76fad1a1befa2e4c038d88c3a1bbbe873acb1322`), and `mir-to-x86`
(`4f45f0a391a921ced9c9dc773b9a040dbc215d14`) on 12 concrete `.lean` probe
modules.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


def parse_args():
  default_sysroot = os.environ.get(
      "LEAN_SYSROOT",
      str(
          Path.home()
          / ".elan/toolchains/leanprover--lean4---v4.34.1"
      ),
  )
  default_anneal_root = os.environ.get("ANNEAL_ROOT", ".")
  parser = argparse.ArgumentParser(
      description="Run adversarial elaboration and binder probes against TrustedBoundary.lean."
  )
  parser.add_argument(
      "--sysroot",
      type=Path,
      default=Path(default_sysroot),
      help="Path to the Lean 4.34.1 toolchain sysroot.",
  )
  parser.add_argument(
      "--anneal-root",
      type=Path,
      default=Path(default_anneal_root),
      help="Path to the main joshlf/anneal checkout.",
  )
  parser.add_argument(
      "--audit-main",
      type=Path,
      default=None,
      help="Path to TrustedBoundary.lean at main (24367bd1a8c7).",
  )
  parser.add_argument(
      "--audit-pr65",
      type=Path,
      default=None,
      help="Path to TrustedBoundary.lean at pr-65 (76fad1a1befa).",
  )
  parser.add_argument(
      "--audit-mir-to-x86",
      type=Path,
      default=None,
      help="Path to TrustedBoundary.lean at mir-to-x86 (4f45f0a391a9).",
  )
  parser.add_argument(
      "--work-dir",
      type=Path,
      default=None,
      help="Temporary working directory for probe module compilation.",
  )
  parser.add_argument(
      "--out-json",
      type=Path,
      default=Path(__file__).resolve().parent / "audit_probe_results.json",
      help="Output JSON path for probe execution results.",
  )
  return parser.parse_args()


def build_probe_cases(attr_source: str):
  base_trusted = (
      attr_source
      + """
namespace Trusted
@[vetted] structure Crate where
  tag : Nat
@[vetted] def CrateTheorem (c : Crate) : Prop :=
  c.tag = 0
end Trusted
"""
  )

  trusted_without_crate_theorem = (
      attr_source
      + """
namespace Trusted
@[vetted] structure Crate where
  tag : Nat
end Trusted
"""
  )

  base_anneal = """\
prelude
import Trusted
namespace Anneal
def helper : Nat := 0
end Anneal
"""

  base_mir = """\
prelude
import Trusted
namespace Mir
def crate : Trusted.Crate := { tag := 0 }
end Mir
"""

  base_proof = """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Mir.crate := rfl
end Proof
"""

  return [
      {
          "id": "baseline_valid",
          "description": "Valid baseline crate and theorem.",
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": base_mir,
              "Proof.lean": base_proof,
          },
      },
      {
          "id": "probe_a1_variable_proof",
          "description": (
              "Probe A1: `variable (h : False)` in `Proof.lean` used in "
              "`theorem verify_crate : Trusted.CrateTheorem Mir.crate := "
              "False.elim h` (or `def` vs `theorem` auto-binding)."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
def crate : Trusted.Crate := { tag := 999 }
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
variable (h : False)
theorem verify_crate : (let _ := h; Trusted.CrateTheorem Mir.crate) := False.elim h
end Proof
""",
          },
      },
      {
          "id": "probe_a2_variable_implicit_mir",
          "description": (
              "Probe A2: `variable {h : False}` implicitly bound into "
              "`Mir.crate` (`Mir.crate : {h : False} -> Trusted.Crate`)."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
variable {h : False}
def crate : Trusted.Crate := False.elim h
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
variable {h : False}
theorem verify_crate : Trusted.CrateTheorem (@Mir.crate h) := False.elim h
end Proof
""",
          },
      },
      {
          "id": "probe_a3_variable_unused_proof",
          "description": (
              "Probe A3: `variable (h : False)` in `Proof.lean` that is not "
              "referenced in `verify_crate`."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": base_mir,
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
variable (h : False)
theorem verify_crate : Trusted.CrateTheorem Mir.crate := rfl
end Proof
""",
          },
      },
      {
          "id": "probe_b1_local_notation",
          "description": (
              "Probe B1: `local notation` in `Proof.lean` attempting to shadow "
              "`Trusted.CrateTheorem`."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": base_mir,
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
local notation "Spoofed" => Trusted.CrateTheorem Mir.crate
theorem verify_crate : Trusted.CrateTheorem Mir.crate := rfl
end Proof
""",
          },
      },
      {
          "id": "probe_b2_namespace_trusted_spoof_in_anneal",
          "description": (
              "Probe B2: `Anneal.lean` opens `namespace Trusted` and defines "
              "`Trusted.CrateTheorem` trivially (`fun _ => True`) for a buggy crate."
          ),
          "files": {
              "Trusted.lean": trusted_without_crate_theorem,
              "Anneal.lean": """\
prelude
import Trusted
namespace Trusted
def CrateTheorem (_ : Crate) : Prop := True
end Trusted
""",
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
def crate : Trusted.Crate := { tag := 999 }
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Mir.crate := trivial
end Proof
""",
          },
      },
      {
          "id": "probe_b3_root_ident_escape",
          "description": (
              "Probe B3: `Anneal.lean` inside `namespace Anneal` uses "
              "`_root_.Trusted.CrateTheorem` to spoof `Trusted.CrateTheorem`."
          ),
          "files": {
              "Trusted.lean": trusted_without_crate_theorem,
              "Anneal.lean": """\
prelude
import Trusted
namespace Anneal
def _root_.Trusted.CrateTheorem (_ : Trusted.Crate) : Prop := True
end Anneal
""",
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
def crate : Trusted.Crate := { tag := 999 }
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Mir.crate := trivial
end Proof
""",
          },
      },
      {
          "id": "probe_c1_universe_poly_verify_crate",
          "description": (
              "Probe C1a: Universe-polymorphic `theorem verify_crate.{u}` where "
              "`levelParams == [`u]` while `proofCi.type` still equals "
              "`Trusted.CrateTheorem Mir.crate`."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": base_mir,
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate.{u} : Trusted.CrateTheorem Mir.crate :=
  let _ : PUnit.{u} := PUnit.unit
  rfl
end Proof
""",
          },
      },
      {
          "id": "probe_c1b_universe_poly_mir_crate",
          "description": (
              "Probe C1b: Universe-polymorphic `def crate.{u} : Trusted.Crate` "
              "where `mirCrateCi.levelParams == [`u]` while `mirCrateCi.type` "
              "still equals `Trusted.Crate`."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
def crate.{u} : Trusted.Crate :=
  let _ : PUnit.{u} := PUnit.unit
  { tag := 0 }
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Mir.crate.{0} := rfl
end Proof
""",
          },
      },
      {
          "id": "probe_c2_noncomputable_mir_crate_choice",
          "description": (
              "Probe C2: `noncomputable def crate : Trusted.Crate := "
              "(Classical.choice ...).val` in `Mir.lean`."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
def witness : Nonempty { c : Trusted.Crate // c.tag = 0 } :=
  ⟨⟨{ tag := 0 }, rfl⟩⟩
noncomputable def crate : Trusted.Crate :=
  (Classical.choice witness).val
end Mir
""",
              "Proof.lean": """\
prelude
import Trusted
import Anneal
import Mir
namespace Proof
theorem verify_crate : Trusted.CrateTheorem Mir.crate :=
  (Classical.choice Mir.witness).property
end Proof
""",
          },
      },
      {
          "id": "probe_c3_abbrev_mir_crate",
          "description": (
              "Probe C3: `abbrev crate : Trusted.Crate` in `Mir.lean` "
              "(elaborates to `.defnInfo` with `ReducibilityHints.abbrev`)."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": base_anneal,
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
abbrev crate : Trusted.Crate := { tag := 0 }
end Mir
""",
              "Proof.lean": base_proof,
          },
      },
      {
          "id": "probe_d1_mir_to_x86_artifact_disconnect",
          "description": (
              "Probe D1: In `mir-to-x86`, `Mir.crate` contains an `X86Body` "
              "(`tag := 0`, e.g. `ret 0`) that neither comes from "
              "`Anneal.compileStage0` of the source `MirBody` (`tag := 999`, "
              "UB) nor matches `.anneal/Prog.s` (`ud2`)."
          ),
          "files": {
              "Trusted.lean": base_trusted,
              "Anneal.lean": """\
prelude
import Trusted
namespace Anneal
def capturedMirTag : Nat := 999
def compileStage0 (mirTag : Nat) : Trusted.Crate := { tag := mirTag }
end Anneal
""",
              "Mir.lean": """\
prelude
import Trusted
namespace Mir
-- Emitted directly by unverified rustc-capture without calling Anneal.compileStage0:
def crate : Trusted.Crate := { tag := 0 }
end Mir
""",
              "Proof.lean": base_proof,
              "Prog.s": """\
.intel_syntax noprefix
.globl always_ub
always_ub:
  ud2
""",
          },
      },
  ]


PARTS = ["olean", "olean.server", "olean.private", "ir.sig", "ir"]


def load_foundation_context(sysroot: Path, foundation_lock: Path):
  lock = json.loads(foundation_lock.read_text(encoding="utf-8"))
  modules_map = lock["modules"]
  foundation = sorted(modules_map.keys())
  artifacts = {}
  for mod, rec in modules_map.items():
    rel_mod = mod.replace(".", "/")
    parts_obj = rec["parts"]
    available = {}
    for p, val in parts_obj.items():
      if val is not None:
        available[p] = str(sysroot / "lib/lean" / f"{rel_mod}.{p}")
    olean_group = [available[p] for p in PARTS[:3] if p in available]
    ir_group = [available[p] for p in PARTS[3:] if p in available]
    artifacts[mod] = [olean_group, ir_group]
  return {
      "foundation": foundation,
      "artifacts": artifacts,
      "graph": lock["graph"],
      "axioms": lock["axioms"],
  }


def collect_module_artifacts(case_dir: Path, mod: str):
  available = {}
  for p in PARTS:
    cand = case_dir / f"{mod}.{p}"
    if cand.exists():
      available[p] = str(cand)
  olean_group = [available[p] for p in PARTS[:3] if p in available]
  ir_group = [available[p] for p in PARTS[3:] if p in available]
  return [olean_group, ir_group]


def run_cmd(args, env=None, cwd=None):
  proc = subprocess.run(
      args,
      stdout=subprocess.PIPE,
      stderr=subprocess.PIPE,
      text=True,
      env=env,
      cwd=cwd,
      check=False,
  )
  return {
      "returncode": proc.returncode,
      "stdout": proc.stdout.strip(),
      "stderr": proc.stderr.strip(),
  }


def run_inspector(
    lean_bin: str,
    script_path: str,
    req_obj: dict,
    req_file: Path,
    res_file: Path,
    cwd: Path,
):
  if res_file.exists():
    res_file.unlink()
  req_file.write_text(json.dumps(req_obj, indent=2), encoding="utf-8")
  res = run_cmd(
      [
          lean_bin,
          "-j1",
          "-M2048",
          "--run",
          script_path,
          str(req_file),
          str(res_file),
      ],
      cwd=cwd,
  )
  parsed_res = None
  if res_file.exists():
    try:
      parsed_res = json.loads(res_file.read_text(encoding="utf-8"))
    except Exception:
      parsed_res = None
  res["result_json"] = parsed_res
  return res


def evaluate_case(
    case, fctx, sysroot: Path, lean_bin: str, cases_dir: Path, audit_scripts: dict
):
  case_dir = cases_dir / case["id"]
  case_dir.mkdir(parents=True, exist_ok=True)
  for fname, content in case["files"].items():
    (case_dir / fname).write_text(content, encoding="utf-8")

  compile_order = ["Trusted", "Anneal", "Mir", "Proof"]
  env = os.environ.copy()
  env["LEAN_PATH"] = f"{case_dir}:{sysroot / 'lib/lean'}"
  compile_ok = True
  compile_errors = []
  for mod in compile_order:
    mod_path = case_dir / f"{mod}.lean"
    olean_path = case_dir / f"{mod}.olean"
    res = run_cmd(
        [
            lean_bin,
            "-j1",
            "-M2048",
            "-t0",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-o",
            str(olean_path),
            str(mod_path),
        ],
        env=env,
        cwd=case_dir,
    )
    if res["returncode"] != 0:
      compile_ok = False
      compile_errors.append({
          "module": mod,
          "stdout": res["stdout"],
          "stderr": res["stderr"],
      })

  case_result = {
      "id": case["id"],
      "description": case["description"],
      "compile_ok": compile_ok,
      "compile_errors": compile_errors,
      "versions": {},
  }

  base_arts = [[k, v] for k, v in sorted(fctx["artifacts"].items())]
  sources_list = [[mod, str(case_dir / f"{mod}.lean")] for mod in compile_order]

  for ver_name, script_path in audit_scripts.items():
    pf_req = {
        "mode": "preflight",
        "sysroot": str(sysroot),
        "artifacts": base_arts,
        "foundation": fctx["foundation"],
        "graph": fctx["graph"],
        "axioms": fctx["axioms"],
        "sources": sources_list,
    }
    pf_res = run_inspector(
        lean_bin,
        script_path,
        pf_req,
        case_dir / f"pf_{ver_name}.json",
        case_dir / f"pf_{ver_name}.res.json",
        case_dir,
    )

    trust_decls = [
        ["Trusted.Crate", "vetted"],
        ["Trusted.CrateTheorem", "vetted"],
        ["Trusted.candidate", "vetted"],
    ]
    audit_graph = dict(fctx["graph"])
    audit_graph["Trusted"] = [{
        "importAll": False,
        "isExported": True,
        "isMeta": False,
        "module": "Init.NotationExtra",
    }]
    audit_graph["Anneal"] = [{
        "importAll": False,
        "isExported": True,
        "isMeta": False,
        "module": "Trusted",
    }]
    audit_graph["Mir"] = [{
        "importAll": False,
        "isExported": True,
        "isMeta": False,
        "module": "Trusted",
    }]
    audit_graph["Proof"] = [
        {
            "importAll": False,
            "isExported": True,
            "isMeta": False,
            "module": "Trusted",
        },
        {
            "importAll": False,
            "isExported": True,
            "isMeta": False,
            "module": "Anneal",
        },
        {
            "importAll": False,
            "isExported": True,
            "isMeta": False,
            "module": "Mir",
        },
    ]
    if (
        pf_res["result_json"]
        and pf_res["result_json"].get("ok")
        and "result" in pf_res["result_json"]
    ):
      headers = pf_res["result_json"]["result"].get("headers", [])
      extracted = []
      for h in headers:
        mname = h.get("module")
        if mname:
          audit_graph[mname] = h.get("imports", [])
        if mname == "Trusted":
          extracted.extend(h.get("trustDeclarations", []))
      if extracted:
        trust_decls = extracted

    if compile_ok:
      audit_arts = dict(fctx["artifacts"])
      for mod in compile_order:
        audit_arts[mod] = collect_module_artifacts(case_dir, mod)
      audit_req = {
          "mode": "audit",
          "sysroot": str(sysroot),
          "artifacts": [[k, v] for k, v in sorted(audit_arts.items())],
          "foundation": fctx["foundation"],
          "graph": audit_graph,
          "axioms": fctx["axioms"],
          "trusted": ["Trusted"],
          "theory": ["Anneal"],
          "hasCrate": True,
          "trustDeclarations": trust_decls,
      }
      au_res = run_inspector(
          lean_bin,
          script_path,
          audit_req,
          case_dir / f"au_{ver_name}.json",
          case_dir / f"au_{ver_name}.res.json",
          case_dir,
      )
    else:
      au_res = {
          "returncode": -1,
          "stdout": "",
          "stderr": "skipped (lean compilation failed)",
          "result_json": None,
      }

    case_result["versions"][ver_name] = {
        "preflight": pf_res,
        "audit": au_res,
    }

  return case_result


def main():
  args = parse_args()
  sysroot = args.sysroot.resolve()
  lean_bin = str(sysroot / "bin/lean")
  anneal_root = args.anneal_root.resolve()
  foundation_lock = anneal_root / "trusted/lean/foundation-lock.json"
  attributes_lean = anneal_root / "trusted/lean/Trusted/Attributes.lean"

  audit_scripts = {
      "main": str(
          (args.audit_main or (anneal_root / "trusted/audit/TrustedBoundary.lean")).resolve()
      ),
      "pr-65": str(
          (
              args.audit_pr65
              or (anneal_root / ".agent-worktrees/pr-65/trusted/audit/TrustedBoundary.lean")
          ).resolve()
      ),
      "mir-to-x86": str(
          (
              args.audit_mir_to_x86
              or (anneal_root / ".agent-worktrees/mir-to-x86/trusted/audit/TrustedBoundary.lean")
          ).resolve()
      ),
  }

  attr_source = attributes_lean.read_text(encoding="utf-8")
  probe_cases = build_probe_cases(attr_source)
  fctx = load_foundation_context(sysroot, foundation_lock)

  if args.work_dir is not None:
    cases_dir = args.work_dir.resolve() / "probe_cases"
    if cases_dir.exists():
      shutil.rmtree(cases_dir)
    cases_dir.mkdir(parents=True, exist_ok=True)
    with ThreadPoolExecutor(max_workers=6) as pool:
      results = list(
          pool.map(
              lambda c: evaluate_case(
                  c, fctx, sysroot, lean_bin, cases_dir, audit_scripts
              ),
              probe_cases,
          )
      )
  else:
    with tempfile.TemporaryDirectory(prefix="anneal_audit_probes_") as tmp:
      cases_dir = Path(tmp) / "probe_cases"
      cases_dir.mkdir(parents=True, exist_ok=True)
      with ThreadPoolExecutor(max_workers=6) as pool:
        results = list(
            pool.map(
                lambda c: evaluate_case(
                    c, fctx, sysroot, lean_bin, cases_dir, audit_scripts
                ),
                probe_cases,
            )
        )

  out_json = args.out_json.resolve()
  out_json.write_text(json.dumps(results, indent=2), encoding="utf-8")
  print(f"Wrote {out_json}")
  for r in results:
    print(f"=== {r['id']} (compile_ok={r['compile_ok']}) ===")
    if not r["compile_ok"]:
      print(f"  compile_errors: {r['compile_errors']}")
    for ver in ["main", "pr-65", "mir-to-x86"]:
      pf = r["versions"][ver]["preflight"]
      au = r["versions"][ver]["audit"]
      pf_status = "PASS" if pf["returncode"] == 0 else f"FAIL({pf['stderr']})"
      au_status = "PASS" if au["returncode"] == 0 else f"FAIL({au['stderr']})"
      print(f"  [{ver:10s}] preflight={pf_status} | audit={au_status}")


if __name__ == "__main__":
  main()
