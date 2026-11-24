#!/usr/bin/env python3
"""Kernel, purity, MetaM, and axiom audit for StaticAddressIdentityCyclesAndTlsModelsSoundness.lean.

Runs Lean v4.34.1 with `-Ddebug.skipKernelTC=false -DwarningAsError=true -DElab.async=false`
(via `anneal-lean-run` when installed) and executes a Lean MetaM pass inside a temporary
directory to verify across ALL constants and ALL theorems:
  - 0 `sorry` / `sorryAx`
  - 0 `Classical.choice`
  - 0 `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`)
  - 0 `omega` / `bv_decide`
  - 0 `partial def`, 0 `axiom`, 0 `noncomputable section`, 0 `deriving`
  - 0 plain recursive or non-`noncomputable` top-level `def`
  - 0 `._unsafe_rec` constants and 0 `isUnsafe` constants in the compiled kernel `Environment`
  - >= 1,100 source lines

Writes `lean_check_receipt.json` alongside this script (path-sanitized).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

SUPPORT_DIR = Path(__file__).resolve().parent
LEAN_FILE = SUPPORT_DIR / "StaticAddressIdentityCyclesAndTlsModelsSoundness.lean"
RECEIPT_FILE = SUPPORT_DIR / "lean_check_receipt.json"

NAMESPACE = "StaticAddressIdentityCyclesAndTlsModelsSoundness"
MIN_LINES = 1100
BANNED_CODE_PATTERNS = [
    ("sorry", r"\bsorry\b"),
    ("Classical.choice", r"\bClassical\.choice\b"),
    ("classical", r"\bclassical\b"),
    ("omega", r"\bomega\b"),
    ("bv_decide", r"\bbv_decide\b"),
    ("native_decide", r"\bnative_decide\b"),
    ("partial_def", r"\bpartial\s+def\b"),
    ("axiom", r"(?m)^(?:private\s+|protected\s+)?axiom\b"),
    ("noncomputable_section", r"\bnoncomputable\s+section\b"),
    ("deriving", r"\bderiving\b"),
    ("unsafe_kw", r"\bunsafe\b"),
    ("_unsafe_rec_lit", r"\._unsafe_rec\b"),
]


def strip_lean_comments_and_docstrings(text: str) -> str:
    """Strip `--` line comments and nested `/- ... -/` block/doc comments."""
    out: list[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        if depth == 0:
            if not in_str and text[i : i + 2] == "/-":
                depth = 1
                i += 2
                continue
            if not in_str and text[i : i + 2] == "--":
                while i < n and text[i] != "\n":
                    i += 1
                continue
            if text[i] == '"' and (i == 0 or text[i - 1] != "\\"):
                in_str = not in_str
            out.append(text[i])
            i += 1
        else:
            if text[i : i + 2] == "/-":
                depth += 1
                i += 2
            elif text[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
    return "".join(out)


def find_lean_toolchain() -> tuple[Path, Path]:
    env_sysroot = os.environ.get("LEAN_SYSROOT")
    if env_sysroot:
        sysroot = Path(env_sysroot)
    else:
        sysroot = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"
    lean_bin = sysroot / "bin/lean"
    if not lean_bin.is_file():
        which_lean = shutil.which("lean")
        if which_lean:
            lean_bin = Path(which_lean).resolve()
            sysroot = lean_bin.parent.parent
        else:
            raise FileNotFoundError("Could not locate Lean v4.34.1 binary")
    return sysroot, lean_bin


def build_lean_cmd(sysroot: Path, lean_bin: Path, target: Path) -> tuple[list[str], dict[str, str]]:
    env = os.environ.copy()
    env["LEAN_SYSROOT"] = str(sysroot)
    anneal_runner = shutil.which("anneal-lean-run") or str(Path.home() / ".local/bin/anneal-lean-run")
    lean_args = [
        str(lean_bin),
        "-M2048",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        "-DwarningAsError=true",
        str(target),
    ]
    if Path(anneal_runner).is_file():
        return [anneal_runner, "--mode", "file", "--", *lean_args], env
    return lean_args, env


def static_source_audit(source_text: str) -> dict:
    lines = source_text.splitlines()
    code_only = strip_lean_comments_and_docstrings(source_text)
    code_lines = code_only.splitlines()

    banned_hits: dict[str, list[int]] = {}
    for label, pattern in BANNED_CODE_PATTERNS:
        regex = re.compile(pattern)
        hits = [idx + 1 for idx, line in enumerate(code_lines) if regex.search(line)]
        if hits:
            banned_hits[label] = hits

    plain_def_lines = [
        idx + 1
        for idx, line in enumerate(code_lines)
        if re.match(r"^(?:private\s+|protected\s+)?def\b", line.strip())
    ]

    theorems = re.findall(r"^(?:private\s+|protected\s+)?theorem\s+([A-Za-z0-9_.\x27]+)", code_only, re.M)
    noncomp_defs = re.findall(
        r"^(?:private\s+|protected\s+)?noncomputable\s+def\s+([A-Za-z0-9_.\x27]+)",
        code_only,
        re.M,
    )

    return {
        "total_lines": len(lines),
        "nonempty_lines": sum(1 for ln in lines if ln.strip()),
        "code_lines": sum(1 for ln in code_lines if ln.strip()),
        "min_lines_required": MIN_LINES,
        "meets_min_lines": len(lines) >= MIN_LINES,
        "banned_token_hits": banned_hits,
        "plain_def_without_noncomputable_lines": plain_def_lines,
        "theorem_count": len(theorems),
        "noncomputable_def_count": len(noncomp_defs),
        "theorems": theorems,
    }


def main() -> int:
    if not LEAN_FILE.is_file():
        print(f"Missing Lean file: {LEAN_FILE}", file=sys.stderr)
        return 2

    source_text = LEAN_FILE.read_text(encoding="utf-8")
    static_res = static_source_audit(source_text)
    if not static_res["meets_min_lines"]:
        print(f"Line count too small: {static_res['total_lines']} < {MIN_LINES}", file=sys.stderr)
        return 1
    if static_res["banned_token_hits"]:
        print(f"Banned code tokens found: {static_res['banned_token_hits']}", file=sys.stderr)
        return 1
    if static_res["plain_def_without_noncomputable_lines"]:
        print(
            f"Plain defs missing noncomputable: {static_res['plain_def_without_noncomputable_lines']}",
            file=sys.stderr,
        )
        return 1

    sysroot, lean_bin = find_lean_toolchain()

    # 1. Verify the exact standalone file first.
    cmd_direct, env = build_lean_cmd(sysroot, lean_bin, LEAN_FILE)
    proc_ver = subprocess.run(
        [str(lean_bin), "--version"],
        env=env,
        capture_output=True,
        text=True,
        check=True,
    )
    lean_version = proc_ver.stdout.strip().splitlines()[0]

    proc_direct = subprocess.run(cmd_direct, env=env, capture_output=True, text=True, check=False)
    if proc_direct.returncode != 0:
        print("Standalone Lean check failed:", proc_direct.stdout, proc_direct.stderr, file=sys.stderr)
        return 1

    # 2. Run Lean MetaM audit over the full environment and every theorem's axiom footprint.
    ns_prefix = f"{NAMESPACE}."
    theorems = static_res["theorems"]
    thm_array_lit = ", ".join(f"``{NAMESPACE}.{t}" for t in theorems)
    metam_template = r"""
import Lean

__SOURCE_TEXT__

section MetaMAudit
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut unsafeRecs : Array Name := #[]
  let mut unsafeConsts : Array Name := #[]
  let mut partialLike : Array Name := #[]
  let mut userAxioms : Array Name := #[]
  let matchingConsts := env.constants.fold (init := #[]) (fun acc n c =>
      if n.toString.startsWith "__NS_PREFIX__" then acc.push (n, c) else acc)
  for (name, cinfo) in matchingConsts do
    if (name.toString.splitOn "_unsafe_rec").length > 1 then
      unsafeRecs := unsafeRecs.push name
    if cinfo.isUnsafe then
      unsafeConsts := unsafeConsts.push name
    match cinfo with
    | .axiomInfo _ => userAxioms := userAxioms.push name
    | .opaqueInfo _ => partialLike := partialLike.push name
    | _ => pure ()
  let thms : Array Name := #[__THM_ARRAY__]
  let mut nonEmptyClean : Array (String × Array String) := #[]
  let mut badAxiomThms : Array (String × Array String) := #[]
  for thm in thms do
    let axs ← collectAxioms thm
    let axStrs := axs.map (·.toString)
    let bad := axStrs.filter (fun a => a != "propext" && a != "Quot.sound")
    if !bad.isEmpty then
      badAxiomThms := badAxiomThms.push (thm.toString, bad)
    nonEmptyClean := nonEmptyClean.push (thm.toString, axStrs)
  let jsonLine :=
    "METAM_AUDIT_JSON={\"ns_const_count\":" ++ toString matchingConsts.size ++
    ",\"unsafe_rec_count\":" ++ toString unsafeRecs.size ++
    ",\"unsafe_const_count\":" ++ toString unsafeConsts.size ++
    ",\"user_axiom_count\":" ++ toString userAxioms.size ++
    ",\"opaque_count\":" ++ toString partialLike.size ++
    ",\"theorem_checked_count\":" ++ toString thms.size ++
    ",\"bad_axiom_theorem_count\":" ++ toString badAxiomThms.size ++ "}"
  IO.println jsonLine
  if !unsafeRecs.isEmpty then
    throwError "Found _unsafe_rec constants: {unsafeRecs}"
  if !unsafeConsts.isEmpty then
    throwError "Found isUnsafe constants: {unsafeConsts}"
  if !userAxioms.isEmpty then
    throwError "Found user axioms: {userAxioms}"
  if !badAxiomThms.isEmpty then
    throwError "Found banned axioms on theorems: {badAxiomThms}"
  for (tn, axStrs) in nonEmptyClean do
    IO.println ("THM_AXIOMS=" ++ tn ++ "::" ++ String.intercalate "," axStrs.toList)
end MetaMAudit

#print axioms __NAMESPACE__.two_phase_static_acyclicity_soundness
#print axioms __NAMESPACE__.value_cycle_e0391_necessity
#print axioms __NAMESPACE__.mutual_value_cycle_emits_e0391
#print axioms __NAMESPACE__.const_ref_cycle_e0391_contrast
#print axioms __NAMESPACE__.unnamed_addr_dedup_preserves_all_deref_observations
#print axioms __NAMESPACE__.non_unnamed_addr_static_preserves_address_distinctness
#print axioms __NAMESPACE__.exported_static_local_unnamed_addr_still_unmergeable
#print axioms __NAMESPACE__.mixed_merge_downgrades_survivor_and_preserves_static_disjointness
#print axioms __NAMESPACE__.tls_noninterference_trace
#print axioms __NAMESPACE__.tls_write_updates_self_preserves_other_slots_and_threads
#print axioms __NAMESPACE__.ce1_erroneous_unnamed_addr_on_static_breaks_disjointness
#print axioms __NAMESPACE__.ce2_sharing_tls_ptr_across_threads_violates_isolation
"""
    metam_snippet = (
        metam_template.replace("__SOURCE_TEXT__", source_text)
        .replace("__NS_PREFIX__", ns_prefix)
        .replace("__THM_ARRAY__", thm_array_lit)
        .replace("__NAMESPACE__", NAMESPACE)
    )

    metam_summary: dict = {}
    theorem_axioms: dict[str, list[str]] = {}
    with tempfile.TemporaryDirectory() as td:
        driver = Path(td) / "MetaMAuditDriver.lean"
        driver.write_text(metam_snippet, encoding="utf-8")
        cmd_meta, _ = build_lean_cmd(sysroot, lean_bin, driver)
        # Note: driver includes `#eval` diagnostic output so do not set -DwarningAsError=true ONLY on info if needed;
        # `anneal-lean-run` accepts our exact flags and `#eval` outputs info diagnostics, NOT warnings.
        proc_meta = subprocess.run(cmd_meta, env=env, capture_output=True, text=True, check=False)
        if proc_meta.returncode != 0:
            print("MetaM Lean audit failed:", proc_meta.stdout, proc_meta.stderr, file=sys.stderr)
            return 1
        combined = proc_meta.stdout + "\n" + proc_meta.stderr
        for line in combined.splitlines():
            clean_line = line
            if "info: " in clean_line:
                clean_line = clean_line.split("info: ", 1)[1]
            if clean_line.startswith("METAM_AUDIT_JSON="):
                metam_summary = json.loads(clean_line.split("METAM_AUDIT_JSON=", 1)[1])
            elif clean_line.startswith("THM_AXIOMS="):
                rest = clean_line.split("THM_AXIOMS=", 1)[1]
                tname, ax_csv = rest.split("::", 1)
                axs = [x for x in ax_csv.split(",") if x]
                theorem_axioms[tname] = axs

    if not metam_summary or metam_summary.get("theorem_checked_count", 0) != len(theorems):
        print(f"Incomplete MetaM summary: {metam_summary}", file=sys.stderr)
        return 1

    classical_count = sum(1 for axs in theorem_axioms.values() if "Classical.choice" in axs)
    sorry_ax_count = sum(1 for axs in theorem_axioms.values() if "sorryAx" in axs)
    reduce_bool_count = sum(
        1
        for axs in theorem_axioms.values()
        if "Lean.ofReduceBool" in axs or "Lean.trustCompiler" in axs
    )

    receipt = {
        "lean_file": f"support/{LEAN_FILE.name}",
        "lean_version": lean_version,
        "standalone_flags": [
            "-M2048",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-DwarningAsError=true",
        ],
        "standalone_exit_code": proc_direct.returncode,
        "static_audit": {k: v for k, v in static_res.items() if k != "theorems"},
        "metam_audit": metam_summary,
        "axiom_counts_across_all_theorems": {
            "Classical.choice": classical_count,
            "sorryAx": sorry_ax_count,
            "Lean.ofReduceBool_or_trustCompiler": reduce_bool_count,
            "allowed_constructive_only_theorems": sum(
                1 for axs in theorem_axioms.values() if set(axs).issubset({"propext", "Quot.sound"})
            ),
        },
        "theorem_axioms": theorem_axioms,
    }
    RECEIPT_FILE.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"receipt": f"support/{RECEIPT_FILE.name}", **metam_summary, "theorems": len(theorems)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
