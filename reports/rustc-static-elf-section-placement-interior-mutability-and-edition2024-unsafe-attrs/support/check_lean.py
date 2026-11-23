#!/usr/bin/env python3
"""Standalone kernel & axiom/hygiene verifier for StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean.

Checks:
1. Source-level hygiene: 0 occurrences of `sorry`, `omega`, `bv_decide`, `native_decide`,
   `Classical.choice`, `partial def`, `unsafe def`, plain `def ` (must be `noncomputable def`),
   `deriving `, `axiom `, or `opaque ` in code.
2. Kernel type-checking via `anneal-lean-run --mode file` with:
   `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
3. MetaM `env.constants.map₁` / `env.constants` walk & `#print axioms` across all major
   theorems: 0 `sorryAx`, 0 `Classical.choice`, 0 `Lean.ofReduceBool`, 0 `.isUnsafe`,
   0 `.isPartial`, 0 `._unsafe_rec`, 0 user axioms.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time


NS = "StaticElfSectionPlacementAndUnsafeAttrsSoundness"

BANNED_SOURCE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "omega": re.compile(r"\bomega\b"),
    "bv_decide": re.compile(r"\bbv_decide\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Classical.choice": re.compile(r"\bClassical\.choice\b"),
    "partial_def": re.compile(r"\bpartial\s+def\b"),
    "unsafe_def": re.compile(r"\bunsafe\s+def\b"),
    "plain_def_without_noncomputable": re.compile(r"^(?!noncomputable\s)def\s+", re.MULTILINE),
    "deriving_clause": re.compile(r"\bderiving\b"),
    "user_axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "user_opaque": re.compile(r"^\s*opaque\s+", re.MULTILINE),
}

MAJOR_THEOREMS = [
    f"{NS}.classify_immutable_never_bss",
    f"{NS}.classify_immutable_zero_lands_in_rodata",
    f"{NS}.classify_pic_immut_reloc_is_dataRelRo",
    f"{NS}.classify_static_immut_reloc_is_rodata",
    f"{NS}.classify_interior_mut_always_writable",
    f"{NS}.classify_interior_mut_reloc_is_data",
    f"{NS}.classify_interior_mut_zero_is_bss",
    f"{NS}.classify_bss_iff",
    f"{NS}.classify_nobits_iff_bss",
    f"{NS}.load_preserves_init_bytes",
    f"{NS}.pic_reloc_sym_is_rw_at_load",
    f"{NS}.pic_applyAllRelocs_succeeds",
    f"{NS}.applyRelroProtect_establishes_postRelroMemSafeInv",
    f"{NS}.wellTypedTrace_safe_and_preserves_immutable",
    f"{NS}.ce1_rodata_write_trap_on_unsafecell",
    f"{NS}.ce2_rodata_relocation_trap_on_pic_imm_ref",
    f"{NS}.ce3_bss_data_loss_on_nonzero_init",
    f"{NS}.ce4_link_section_rodata_contaminates_segment",
    f"{NS}.edition2024_gate_requires_unsafe_witness",
    f"{NS}.unsafe_wrapper_rejected_on_normal_attrs",
    f"{NS}.codegen_equivalence_2021_bare_to_2024_unsafe",
    f"{NS}.export_name_precedence_over_no_mangle_both_orders",
    f"{NS}.link_section_alone_does_not_export_c_symbol",
    f"{NS}.ce5_cross_edition_macro_bypass",
    f"{NS}.end_to_end_static_placement_and_attr_soundness",
]


def strip_lean_comments(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        if i + 1 < n and src[i : i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if i + 1 < n and src[i : i + 2] == "-/":
                depth -= 1
                i += 2
            else:
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        if i + 1 < n and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                i += 1
            continue
        out.append(src[i])
        i += 1
    return "".join(out)


def resolve_lean_cmd() -> tuple[list[str], dict[str, str]]:
    env = os.environ.copy()
    toolchain = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    env["LEAN_SYSROOT"] = str(toolchain)
    env["PATH"] = f"{toolchain / 'bin'}:{Path.home() / '.local' / 'bin'}:{env.get('PATH', '')}"
    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"
    lean_bin = str(toolchain / "bin" / "lean")
    if wrapper.is_file():
        return [str(wrapper), "--mode", "file", "--", lean_bin, "-M2048"], env
    return [lean_bin, "-M2048"], env


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    lean_file = support_dir / "StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean"
    receipt_path = support_dir / "lean_check_receipt.json"

    raw_src = lean_file.read_text(encoding="utf-8")
    code_only = strip_lean_comments(raw_src)
    source_hits = {
        key: len(pat.findall(code_only)) for key, pat in BANNED_SOURCE_PATTERNS.items()
    }

    lean_prefix, env = resolve_lean_cmd()
    lean_bin = str(Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1" / "bin" / "lean")
    ver_proc = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, env=env, check=True)
    lean_version = ver_proc.stdout.strip()

    t0 = time.monotonic()
    r_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    tc_proc = subprocess.run(
        [
            *lean_prefix,
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            "-DwarningAsError=true",
            str(lean_file),
        ],
        capture_output=True,
        text=True,
        env=env,
    )
    wall_sec = round(time.monotonic() - t0, 4)
    r_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    maxrss_kib = max(r_before.ru_maxrss, r_after.ru_maxrss)

    if tc_proc.returncode != 0:
        print(tc_proc.stdout, file=sys.stderr)
        print(tc_proc.stderr, file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="staticsec_lean_audit_") as tmp_raw:
        tmp = Path(tmp_raw)
        audit_lines = [
            "import Lean",
            raw_src,
            "open Lean Elab Command in",
            "#eval liftCoreM do",
            "  let env ← getEnv",
            "  let mut nsCount := 0",
            "  let mut unsafeCount := 0",
            "  let mut partialCount := 0",
            "  let mut unsafeRecCount := 0",
            "  let mut userAxiomCount := 0",
            "  for (nm, cinfo) in env.constants.toList do",
            f'    if nm.toString.startsWith "{NS}." then',
            "      nsCount := nsCount + 1",
            "      if cinfo.isUnsafe then unsafeCount := unsafeCount + 1",
            "      if cinfo.isPartial then partialCount := partialCount + 1",
            '      if (nm.toString.splitOn "_unsafe_rec").length > 1 then unsafeRecCount := unsafeRecCount + 1',
            "      if cinfo matches ConstantInfo.axiomInfo _ then userAxiomCount := userAxiomCount + 1",
            '  IO.println s!"ENV_STATS ns={nsCount} unsafe={unsafeCount} partial={partialCount} unsafe_rec={unsafeRecCount} user_axiom={userAxiomCount}"',
        ]
        for thm in MAJOR_THEOREMS:
            audit_lines.append(f"#print axioms {thm}")

        audit_file = tmp / "AuditDriver.lean"
        audit_file.write_text("\n".join(audit_lines) + "\n", encoding="utf-8")

        audit_proc = subprocess.run(
            [
                *lean_prefix,
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                str(audit_file),
            ],
            capture_output=True,
            text=True,
            env=env,
        )
        if audit_proc.returncode != 0:
            print(audit_proc.stdout, file=sys.stderr)
            print(audit_proc.stderr, file=sys.stderr)
            return 1

    audit_out = audit_proc.stdout.strip()
    stats_match = re.search(
        r"ENV_STATS ns=(\d+) unsafe=(\d+) partial=(\d+) unsafe_rec=(\d+) user_axiom=(\d+)",
        audit_out,
    )
    if not stats_match:
        print(f"error: missing ENV_STATS in audit output:\n{audit_out}", file=sys.stderr)
        return 1

    env_stats = {
        "namespace_constants": int(stats_match.group(1)),
        "is_unsafe": int(stats_match.group(2)),
        "is_partial": int(stats_match.group(3)),
        "unsafe_rec_helpers": int(stats_match.group(4)),
        "user_axioms": int(stats_match.group(5)),
    }

    axiom_lines: list[str] = []
    raw_lines = audit_out.splitlines()
    i = 0
    while i < len(raw_lines):
        ln = raw_lines[i].strip()
        if "depends on axioms:" in ln or "does not depend on any axioms" in ln:
            while "depends on axioms:" in ln and "[" in ln and "]" not in ln and i + 1 < len(raw_lines):
                i += 1
                ln = f"{ln} {raw_lines[i].strip()}"
            axiom_lines.append(ln)
        i += 1
    forbidden_axioms_found = any(
        bad in text
        for text in (*axiom_lines, audit_out)
        for bad in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler")
    )

    clean = (
        len(raw_src.splitlines()) >= 900
        and all(v == 0 for v in source_hits.values())
        and env_stats["namespace_constants"] >= 50
        and env_stats["is_unsafe"] == 0
        and env_stats["is_partial"] == 0
        and env_stats["unsafe_rec_helpers"] == 0
        and env_stats["user_axioms"] == 0
        and len(axiom_lines) == len(MAJOR_THEOREMS)
        and not forbidden_axioms_found
    )

    receipt = {
        "lean_version": lean_version,
        "file": "support/StaticElfSectionPlacementAndUnsafeAttrsSoundness.lean",
        "sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest(),
        "line_count": len(raw_src.splitlines()),
        "flags": ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"],
        "wall_clock_sec": wall_sec,
        "max_rss_kib": maxrss_kib,
        "source_banned_token_counts": source_hits,
        "kernel_environment_stats": env_stats,
        "major_theorems_checked": len(MAJOR_THEOREMS),
        "theorem_axiom_footprints": axiom_lines,
        "forbidden_axioms_present": forbidden_axioms_found,
        "all_checks_passed": clean,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
    return 0 if clean else 1


if __name__ == "__main__":
    raise SystemExit(main())
