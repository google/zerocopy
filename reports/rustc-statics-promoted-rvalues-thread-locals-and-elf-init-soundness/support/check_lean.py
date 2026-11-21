#!/usr/bin/env python3
"""Standalone kernel & axiom/hygiene verifier for StaticsPromotedsAndTlsSoundness.lean.

Checks:
1. Source-level hygiene: 0 occurrences of `sorry`, `omega`, `bv_decide`, `native_decide`,
   `Classical.choice`, `partial def`, `unsafe def`, `axiom `, or `opaque ` in code.
2. Kernel type-checking via `anneal-lean-run --mode file lean -M2048 -DElab.async=false
   -Ddebug.skipKernelTC=false -DwarningAsError=true`.
3. Kernel `Environment` inspection (`#print axioms` + `env.constants` walk across all
   `StaticsPromotedsAndTlsSoundness.*` constants): 0 `sorryAx`, 0 `Classical.choice`,
   0 `Lean.ofReduceBool`, 0 `.isUnsafe`, 0 `.isPartial`, 0 `._unsafe_rec`.
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


BANNED_SOURCE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "omega": re.compile(r"\bomega\b"),
    "bv_decide": re.compile(r"\bbv_decide\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Classical.choice": re.compile(r"\bClassical\.choice\b"),
    "partial_def": re.compile(r"\bpartial\s+def\b"),
    "unsafe_def": re.compile(r"\bunsafe\s+def\b"),
    "user_axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "user_opaque": re.compile(r"^\s*opaque\s+", re.MULTILINE),
}

MAJOR_THEOREMS = [
    "StaticsPromotedsAndTlsSoundness.zero_freeze_static_lands_in_rodata_not_bss",
    "StaticsPromotedsAndTlsSoundness.zero_freeze_tls_lands_in_tdata_not_tbss",
    "StaticsPromotedsAndTlsSoundness.pointer_bearing_freeze_static_lands_in_data_rel_ro_under_pic",
    "StaticsPromotedsAndTlsSoundness.relro_writable_during_reloc_and_frozen_at_runtime",
    "StaticsPromotedsAndTlsSoundness.running_trace_preserves_rodata_and_dataRelRo",
    "StaticsPromotedsAndTlsSoundness.canPromoteRef_implies_ctfe_total",
    "StaticsPromotedsAndTlsSoundness.promote_rvalue_observational_equivalence",
    "StaticsPromotedsAndTlsSoundness.pt_tls_instantiate_length",
    "StaticsPromotedsAndTlsSoundness.pt_tls_tdata_prefix_exact",
    "StaticsPromotedsAndTlsSoundness.pt_tls_tbss_zero_exact",
    "StaticsPromotedsAndTlsSoundness.elf_tls_four_models_address_equivalent",
    "StaticsPromotedsAndTlsSoundness.pt_tls_spawn_fresh_template_sound",
    "StaticsPromotedsAndTlsSoundness.pt_tls_cross_thread_noninterference",
    "StaticsPromotedsAndTlsSoundness.tls_dtor_lifo_order_and_reentrant_access_safety",
    "StaticsPromotedsAndTlsSoundness.used_linker_shf_gnu_retain_survives_gc_sections",
    "StaticsPromotedsAndTlsSoundness.init_array_section_survives_gc_sections",
    "StaticsPromotedsAndTlsSoundness.init_array_runs_before_main",
    "StaticsPromotedsAndTlsSoundness.ce1_promoting_unsafecell_into_rodata_unsound",
    "StaticsPromotedsAndTlsSoundness.ce2_used_compiler_dropped_by_linker_gc",
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


def resolve_lean_cmd() -> list[str]:
    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"
    lean_bin = shutil.which("lean") or str(Path.home() / ".elan" / "bin" / "lean")
    if wrapper.is_file():
        return [str(wrapper), "--mode", "file", "lean", "-M2048"]
    return [lean_bin, "-M2048"]


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    lean_file = support_dir / "StaticsPromotedsAndTlsSoundness.lean"
    receipt_path = support_dir / "lean_check_receipt.json"

    raw_src = lean_file.read_text(encoding="utf-8")
    code_only = strip_lean_comments(raw_src)
    source_hits = {
        key: len(pat.findall(code_only)) for key, pat in BANNED_SOURCE_PATTERNS.items()
    }

    env = os.environ.copy()
    env["PATH"] = f"{Path.home() / '.elan' / 'bin'}:{Path.home() / '.local' / 'bin'}:{env.get('PATH', '')}"

    lean_bin = shutil.which("lean", path=env["PATH"]) or str(Path.home() / ".elan" / "bin" / "lean")
    ver_proc = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, env=env, check=True)
    lean_version = ver_proc.stdout.strip()

    lean_prefix = resolve_lean_cmd()
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

    with tempfile.TemporaryDirectory(prefix="tls_statics_lean_audit_") as tmp_raw:
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
            '    if nm.toString.startsWith "StaticsPromotedsAndTlsSoundness." then',
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
            check=True,
        )

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

    axiom_lines = [
        ln.strip()
        for ln in audit_out.splitlines()
        if "depends on axioms:" in ln or "does not depend on any axioms" in ln
    ]
    forbidden_axioms_found = any(
        bad in ln
        for ln in axiom_lines
        for bad in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler")
    )

    clean = (
        all(v == 0 for v in source_hits.values())
        and env_stats["is_unsafe"] == 0
        and env_stats["is_partial"] == 0
        and env_stats["unsafe_rec_helpers"] == 0
        and env_stats["user_axioms"] == 0
        and not forbidden_axioms_found
    )

    receipt = {
        "lean_version": lean_version,
        "file": "support/StaticsPromotedsAndTlsSoundness.lean",
        "sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest(),
        "line_count": len(raw_src.splitlines()),
        "flags": ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"],
        "wall_clock_sec": wall_sec,
        "max_rss_kib": maxrss_kib,
        "source_banned_token_counts": source_hits,
        "kernel_environment_stats": env_stats,
        "theorem_axiom_footprints": axiom_lines,
        "forbidden_axioms_present": forbidden_axioms_found,
        "all_checks_passed": clean,
    }
    receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
    return 0 if clean else 1


if __name__ == "__main__":
    raise SystemExit(main())
