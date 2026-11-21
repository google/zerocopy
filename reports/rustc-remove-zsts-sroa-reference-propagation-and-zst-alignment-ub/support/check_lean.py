#!/usr/bin/env python3
"""Kernel-verify support/RemoveZstsSroaAndRefPropSoundness.lean with Lean v4.34.1,
audit axioms via #print axioms, inspect the compiled Lean Environment for unsafe
or ._unsafe_rec declarations, and verify zero forbidden tactics/constructs.

Run:
    python3 support/check_lean.py --out support/lean_check_receipt.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any

MAIN_THEOREMS = [
    "RemoveZstsSroaAndRefPropSoundness.miri_default_args_suppress_checkAlignment_and_run_removeZsts",
    "RemoveZstsSroaAndRefPropSoundness.miri_force_enable_checkAlignment_restores_pass",
    "RemoveZstsSroaAndRefPropSoundness.null_unit_load_and_store_valid",
    "RemoveZstsSroaAndRefPropSoundness.dangling_aligned64_zst_load_and_store_valid",
    "RemoveZstsSroaAndRefPropSoundness.any_init_ptr_zst_align_one_valid",
    "RemoveZstsSroaAndRefPropSoundness.removeZstsStmt_forward_codegen_refinement",
    "RemoveZstsSroaAndRefPropSoundness.removeZsts_indirect_align_one_bidirectional_iff",
    "RemoveZstsSroaAndRefPropSoundness.removeZstsCertifiedStmt_bidirectional_equivalence",
    "RemoveZstsSroaAndRefPropSoundness.ce1_remove_zsts_erases_misaligned_align64_zst_ub",
    "RemoveZstsSroaAndRefPropSoundness.sroaFlattenStmt_exact_bisimulation",
    "RemoveZstsSroaAndRefPropSoundness.sroaFlattenProg_exact_bisimulation",
    "RemoveZstsSroaAndRefPropSoundness.sroa_maybeDangling_exclusion_necessary",
    "RemoveZstsSroaAndRefPropSoundness.refProp_shared_exact_bisimulation",
    "RemoveZstsSroaAndRefPropSoundness.refProp_mut_step_bisimulation",
    "RemoveZstsSroaAndRefPropSoundness.refProp_mut_all_or_nothing_exact_bisimulation",
    "RemoveZstsSroaAndRefPropSoundness.ce2_refprop_into_storage_dead_target_dangling_ub",
    "RemoveZstsSroaAndRefPropSoundness.ce3_partial_mut_refprop_interleaving_aliasing_unsound",
]

FORBIDDEN_PATTERNS = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "omega": r"\bomega\b",
    "bv_decide": r"\bbv_decide\b",
    "native_decide": r"\bnative_decide\b",
    "partial_def": r"\bpartial\s+def\b",
    "unsafe_rec": r"\._unsafe_rec\b",
    "classical_choice": r"\bClassical\.choice\b",
    "axiom_decl": r"^\s*axiom\s+",
    "implemented_by": r"implemented_by",
    "extern_attr": r"@\[extern",
}

FORBIDDEN_AXIOMS = {"Classical.choice", "sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"}

ENV_UNSAFE_AUDIT_SNIPPET = """
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut unsafeDecls : Array String := #[]
  for (nm, ci) in env.constants.map₁.toList do
    let s := nm.toString
    if s.startsWith "RemoveZstsSroaAndRefPropSoundness." then
      if ci.isUnsafe || (s.splitOn "_unsafe_rec").length > 1 then
        unsafeDecls := unsafeDecls.push s
  for (nm, ci) in env.constants.map₂.toList do
    let s := nm.toString
    if s.startsWith "RemoveZstsSroaAndRefPropSoundness." then
      if ci.isUnsafe || (s.splitOn "_unsafe_rec").length > 1 then
        unsafeDecls := unsafeDecls.push s
  IO.println s!"ENV_UNSAFE_DECL_COUNT={unsafeDecls.size} {unsafeDecls}"
"""


def strip_lean_comments(src: str) -> str:
    out = re.sub(r"/-.*?-/", "", src, flags=re.S)
    out = re.sub(r"--[^\n]*", "", out)
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--file",
        type=Path,
        default=Path(__file__).resolve().parent / "RemoveZstsSroaAndRefPropSoundness.lean",
    )
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    lean_file = args.file.resolve()
    src = lean_file.read_text(encoding="utf-8")
    code_only = strip_lean_comments(src)

    token_audit: dict[str, int] = {}
    for key, pat in FORBIDDEN_PATTERNS.items():
        token_audit[key] = len(re.findall(pat, code_only, flags=re.M))

    toolchain = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    lean_bin = toolchain / "bin" / "lean"
    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"

    env = os.environ.copy()
    env["LEAN_SYSROOT"] = str(toolchain)

    ver_proc = subprocess.run([str(lean_bin), "--version"], env=env, capture_output=True, text=True)
    lean_version = ver_proc.stdout.strip()

    def run_lean(target: Path) -> subprocess.CompletedProcess[str]:
        cmd = [
            str(lean_bin),
            "-M2048",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-DwarningAsError=true",
            str(target),
        ]
        if wrapper.exists():
            cmd = [str(wrapper), "--mode", "file", "--", *cmd]
        return subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=180)

    p_main = run_lean(lean_file)

    axioms_by_theorem: dict[str, list[str]] = {}
    forbidden_axioms_found: list[str] = []
    env_unsafe_decl_count: int | None = None

    with tempfile.TemporaryDirectory(prefix="lean_axiom_audit_") as td:
        audit_file = Path(td) / "Audit.lean"
        audit_src = (
            "import Lean\n"
            + src
            + "\n"
            + "\n".join(f"#print axioms {t}" for t in MAIN_THEOREMS)
            + "\n"
            + ENV_UNSAFE_AUDIT_SNIPPET
            + "\n"
        )
        audit_file.write_text(audit_src, encoding="utf-8")
        p_audit = run_lean(audit_file)
        m_unsafe = re.search(r"ENV_UNSAFE_DECL_COUNT=(\d+)", p_audit.stdout)
        if m_unsafe:
            env_unsafe_decl_count = int(m_unsafe.group(1))
        norm_out = re.sub(r"\s+", " ", p_audit.stdout)
        for m in re.finditer(r"'([^']+)' does not depend on any axioms", norm_out):
            axioms_by_theorem[m.group(1)] = []
        for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", norm_out):
            axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
            axioms_by_theorem[m.group(1)] = axs
            for a in axs:
                if a in FORBIDDEN_AXIOMS:
                    forbidden_axioms_found.append(f"{m.group(1)}:{a}")

    all_tokens_zero = all(v == 0 for v in token_audit.values())
    all_theorems_audited = all(t in axioms_by_theorem for t in MAIN_THEOREMS)
    passed = (
        p_main.returncode == 0
        and p_audit.returncode == 0
        and all_tokens_zero
        and all_theorems_audited
        and not forbidden_axioms_found
        and env_unsafe_decl_count == 0
    )

    scrubbed_stderr = p_main.stderr.strip().replace(str(lean_file), lean_file.name)
    scrubbed_audit_stderr = p_audit.stderr.strip()

    receipt: dict[str, Any] = {
        "lean_version": lean_version,
        "file_name": lean_file.name,
        "file_bytes": len(src.encode("utf-8")),
        "file_lines": len(src.splitlines()),
        "file_sha256": hashlib.sha256(src.encode("utf-8")).hexdigest(),
        "flags": ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"],
        "main_exit_code": p_main.returncode,
        "main_stderr": scrubbed_stderr,
        "axiom_audit_exit_code": p_audit.returncode,
        "env_unsafe_decl_count": env_unsafe_decl_count,
        "forbidden_token_counts": token_audit,
        "axioms_by_theorem": axioms_by_theorem,
        "forbidden_axioms_found": forbidden_axioms_found,
        "all_checks_passed": passed,
    }
    if not passed:
        sys_msg = f"MAIN STDOUT/STDERR:\n{p_main.stdout}\n{p_main.stderr}\nAUDIT:\n{p_audit.stdout}\n{scrubbed_audit_stderr}"
        print(sys_msg)

    text = json.dumps(receipt, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
        print(f"wrote {args.out.name} (passed={passed})")
    else:
        print(text)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
