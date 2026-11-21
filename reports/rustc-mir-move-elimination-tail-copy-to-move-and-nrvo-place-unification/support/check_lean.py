#!/usr/bin/env python3
"""Kernel-check support/MoveEliminationAndTailCopySoundness.lean with Lean v4.34.1,
audit the axioms of every headline theorem with `#print axioms`, inspect the
elaborated environment for unsafe or `_unsafe_rec` declarations, and count
forbidden tactics/constructs in the source text.

Run:
    python3 support/check_lean.py --out support/lean_check_receipt.json

The Lean binary is taken from `$LEAN_BIN`, else from an elan toolchain directory
named `leanprover--lean4---v4.34.1`, else from `lean` on PATH. If a resource
wrapper named `anneal-lean-run` is on PATH or in `~/.local/bin`, the check runs
under it; otherwise Lean is invoked directly.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any

NS = "MoveEliminationAndTailCopySoundness"

MAIN_THEOREMS = [
    f"{NS}.Tail.tailCopyToMove_exact_return_value_and_memory_equivalence",
    f"{NS}.Tail.tailCopyToMove_ub_iff",
    f"{NS}.Tail.tailCopyToMove_preserves_return_and_heap",
    f"{NS}.Tail.tailCopyToMove_equivalence_without_borrowed_write_stop",
    f"{NS}.Tail.ce1_tail_copy_to_move_past_indirect_borrow_read_unsound",
    f"{NS}.Tail.tail_rewrites_borrowed_local_return",
    f"{NS}.Tail.tail_stops_at_borrowed_destination",
    f"{NS}.Unify.step_refines",
    f"{NS}.Unify.moveElimination_value_and_address_bisimulation",
    f"{NS}.Unify.moveElimination_original_choices_valid",
    f"{NS}.Unify.moveElimination_return_observation",
    f"{NS}.Unify.Row.disjoint_sound",
    f"{NS}.Unify.early_end_late_start_disjoint",
    f"{NS}.Unify.disjointLiveRanges_sound",
    f"{NS}.Unify.nrvo_model_instance",
    f"{NS}.Unify.nrvo_model_rows_disjoint",
    f"{NS}.Unify.ce2_unifying_overlapping_address_observed_locals_breaks_ptr_inequality",
    f"{NS}.Places.resolve_projectDeeper",
    f"{NS}.Places.resolve_reaches_unmapped",
    f"{NS}.Places.unifyPlaces_idempotent",
    f"{NS}.Places.unifyPlaces_transitive_example",
    f"{NS}.Fixup.aliasFixup_emits_nonoverlapping_copies",
    f"{NS}.Fixup.aliasFixup_pair_matches_specification",
    f"{NS}.Fixup.aliasFixup_self_swap_correct",
    f"{NS}.Fixup.ce3_aggregate_self_swap_without_aliasing_fixup_clobbers_field",
    f"{NS}.Fixup.aliasFixup_three_field_rotation_instance",
    f"{NS}.Fixup.aliasFixup_identity_field_dropped_instance",
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

ENV_UNSAFE_AUDIT_SNIPPET = f"""
open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut unsafeDecls : Array String := #[]
  for (nm, ci) in env.constants.map₁.toList do
    let s := nm.toString
    if s.startsWith "{NS}." then
      if ci.isUnsafe || (s.splitOn "_unsafe_rec").length > 1 then
        unsafeDecls := unsafeDecls.push s
  for (nm, ci) in env.constants.map₂.toList do
    let s := nm.toString
    if s.startsWith "{NS}." then
      if ci.isUnsafe || (s.splitOn "_unsafe_rec").length > 1 then
        unsafeDecls := unsafeDecls.push s
  IO.println s!"ENV_UNSAFE_DECL_COUNT={{unsafeDecls.size}} {{unsafeDecls}}"
"""


def find_lean() -> tuple[Path, Path | None]:
    env_bin = os.environ.get("LEAN_BIN")
    if env_bin and Path(env_bin).is_file():
        return Path(env_bin), None
    toolchain = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    if (toolchain / "bin" / "lean").is_file():
        return toolchain / "bin" / "lean", toolchain
    found = shutil.which("lean")
    if found:
        return Path(found), None
    raise RuntimeError("no Lean binary found; set LEAN_BIN")


def find_wrapper() -> Path | None:
    found = shutil.which("anneal-lean-run")
    if found:
        return Path(found)
    cand = Path.home() / ".local" / "bin" / "anneal-lean-run"
    return cand if cand.is_file() else None


def scrub(text: str, extra: list[tuple[str, str]]) -> str:
    out = text
    for raw, repl in extra:
        if raw:
            out = out.replace(raw, repl)
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/[A-Za-z0-9._/-]+", "<TMP>", out)
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--file",
        type=Path,
        default=Path(__file__).resolve().parent / f"{NS}.lean",
    )
    parser.add_argument("--out", type=Path, default=None)
    args = parser.parse_args()

    lean_file = args.file.resolve()
    src = lean_file.read_text(encoding="utf-8")

    # The token audit deliberately scans the whole file, comments included.
    token_audit = {
        key: len(re.findall(pat, src, flags=re.M)) for key, pat in FORBIDDEN_PATTERNS.items()
    }

    lean_bin, sysroot = find_lean()
    wrapper = find_wrapper()
    env = os.environ.copy()
    if sysroot is not None:
        env["LEAN_SYSROOT"] = str(sysroot)

    ver_proc = subprocess.run([str(lean_bin), "--version"], env=env, capture_output=True, text=True)
    lean_version = ver_proc.stdout.strip()

    flags = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]

    def run_lean(target: Path) -> subprocess.CompletedProcess[str]:
        cmd = [str(lean_bin), *flags, str(target)]
        if wrapper is not None:
            cmd = [str(wrapper), "--mode", "file", "--", *cmd]
        return subprocess.run(
            cmd, env=env, stdin=subprocess.DEVNULL, capture_output=True, text=True, timeout=900
        )

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
        audit_stdout = p_audit.stdout
        audit_stderr = scrub(p_audit.stderr.strip(), [(td, "<AUDIT_DIR>")])

    m_unsafe = re.search(r"ENV_UNSAFE_DECL_COUNT=(\d+)", audit_stdout)
    if m_unsafe:
        env_unsafe_decl_count = int(m_unsafe.group(1))
    norm_out = re.sub(r"\s+", " ", audit_stdout)
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

    main_stderr = scrub(p_main.stderr.strip(), [(str(lean_file), lean_file.name)])
    # Drop resource-wrapper chatter; keep compiler diagnostics only.
    main_stderr = "\n".join(
        ln for ln in main_stderr.splitlines() if not ln.startswith("[anneal-lean-run]")
    )
    main_stdout = scrub(p_main.stdout.strip(), [(str(lean_file), lean_file.name)])

    receipt: dict[str, Any] = {
        "lean_version": lean_version,
        "file_name": lean_file.name,
        "file_bytes": len(src.encode("utf-8")),
        "file_lines": len(src.splitlines()),
        "file_sha256": hashlib.sha256(src.encode("utf-8")).hexdigest(),
        "flags": flags,
        "ran_under_resource_wrapper": wrapper is not None,
        "main_exit_code": p_main.returncode,
        "main_stdout": main_stdout,
        "main_stderr": main_stderr,
        "axiom_audit_exit_code": p_audit.returncode,
        "env_unsafe_decl_count": env_unsafe_decl_count,
        "forbidden_token_counts": token_audit,
        "theorems_audited": len(axioms_by_theorem),
        "axioms_by_theorem": axioms_by_theorem,
        "forbidden_axioms_found": forbidden_axioms_found,
        "all_checks_passed": passed,
    }
    if not passed:
        print("MAIN:\n" + main_stdout + "\n" + main_stderr)
        print("AUDIT:\n" + scrub(audit_stdout, [])[-4000:] + "\n" + audit_stderr[-4000:])

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
