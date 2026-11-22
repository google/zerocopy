#!/usr/bin/env python3
"""Standalone Lean v4.34.1 kernel & purity verifier for
NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean.

Checks:
1. Source hygiene (comments stripped): 0 occurrences of `sorry`, `omega`,
   `bv_decide`, `native_decide`, `Classical.choice`, `partial def`, `unsafe def`,
   `deriving`, `axiom `, `opaque `, or `_unsafe_rec`.
2. Strict kernel type-checking with `-M2048 -DElab.async=false
   -Ddebug.skipKernelTC=false -DwarningAsError=true` (wrapped in
   `anneal-lean-run --mode file` when present).
3. Kernel `Environment` inspection (`env.constants.toList` across all
   `NeverPatternsSoundness.*` declarations + `#print axioms` on all 11 flagship
   and counterexample theorems): 0 `sorryAx`, 0 `Classical.choice`,
   0 `Lean.ofReduceBool`, 0 `Lean.trustCompiler`, 0 `.isUnsafe`, 0 `.isPartial`,
   0 `._unsafe_rec` helpers, 0 user `axiom` declarations.
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
    "deriving": re.compile(r"\bderiving\b"),
    "user_axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "user_opaque": re.compile(r"^\s*opaque\s+", re.MULTILINE),
    "_unsafe_rec": re.compile(r"_unsafe_rec"),
}

MAJOR_THEOREMS = [
    "NeverPatternsSoundness.exhaustiveMatrix_every_valid_value_matched_or_never_read",
    "NeverPatternsSoundness.guardPattern_must_stay_opaque_for_exhaustiveness",
    "NeverPatternsSoundness.threeWay_null_raw_never_split",
    "NeverPatternsSoundness.postfixMatch_temp_drop_order_eq_prefix",
    "NeverPatternsSoundness.anneal_never_param_vacuity_requires_static_admission",
    "NeverPatternsSoundness.ce1_guard_pattern_treated_as_exhaustive_causes_missing_arm",
    "NeverPatternsSoundness.ce2_uninhabited_behind_raw_ptr_without_read_unsound_unreachable",
    "NeverPatternsSoundness.ce3_wildcard_star_null_never_succeeds_while_empty_match_faults",
    "NeverPatternsSoundness.ce4_never_pattern_on_inhabited_variant_rejected",
    "NeverPatternsSoundness.ce5_private_uninhabited_field_hidden_outside_module",
    "NeverPatternsSoundness.ce6_foreign_non_exhaustive_empty_enum_blocks_empty_match",
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


def resolve_lean() -> tuple[list[str], str, dict[str, str]]:
    env = os.environ.copy()
    pinned_tc = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    if (pinned_tc / "bin" / "lean").is_file():
        lean_bin = str(pinned_tc / "bin" / "lean")
        env["LEAN_SYSROOT"] = str(pinned_tc)
    else:
        lean_bin = shutil.which("lean") or str(Path.home() / ".elan" / "bin" / "lean")
    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"
    if wrapper.is_file():
        return [str(wrapper), "--mode", "file", "--", lean_bin], lean_bin, env
    return [lean_bin], lean_bin, env


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    lean_file = support_dir / "NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean"
    receipt_path = support_dir / "lean_check_receipt.json"

    raw_src = lean_file.read_text(encoding="utf-8")
    code_only = strip_lean_comments(raw_src)
    source_hits = {
        key: len(pat.findall(code_only)) for key, pat in BANNED_SOURCE_PATTERNS.items()
    }

    lean_prefix, lean_bin, env = resolve_lean()
    ver_proc = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, env=env, check=True)
    lean_version = ver_proc.stdout.strip()

    with tempfile.TemporaryDirectory(prefix="neverpat_lean_audit_") as tmp_raw:
        tmp = Path(tmp_raw)
        olean = tmp / "NeverPatternsGuardPatternsAndExhaustivenessSoundness.olean"

        t0 = time.monotonic()
        r_before = resource.getrusage(resource.RUSAGE_CHILDREN)
        tc_proc = subprocess.run(
            [
                *lean_prefix,
                "-M2048",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "-R",
                str(support_dir),
                "-o",
                str(olean),
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

        audit_lines = [
            "import Lean",
            "import NeverPatternsGuardPatternsAndExhaustivenessSoundness",
            "open Lean NeverPatternsSoundness",
        ]
        for thm in MAJOR_THEOREMS:
            audit_lines.append(f"#print axioms {thm}")
        audit_lines.extend(
            [
                "#eval show MetaM Unit from do",
                "  let env ← getEnv",
                "  let mut nsCount := 0",
                "  let mut thmCount := 0",
                "  let mut defCount := 0",
                "  let mut unsafeCount := 0",
                "  let mut partialCount := 0",
                "  let mut unsafeRecCount := 0",
                "  let mut userAxiomCount := 0",
                "  for (nm, cinfo) in env.constants.toList do",
                '    if nm.toString.startsWith "NeverPatternsSoundness." then',
                "      nsCount := nsCount + 1",
                "      match cinfo with",
                "      | .thmInfo _ => thmCount := thmCount + 1",
                "      | .defnInfo _ => defCount := defCount + 1",
                "      | .axiomInfo _ => userAxiomCount := userAxiomCount + 1",
                "      | _ => pure ()",
                "      if cinfo.isUnsafe then unsafeCount := unsafeCount + 1",
                "      if cinfo.isPartial then partialCount := partialCount + 1",
                '      if (nm.toString.splitOn "_unsafe_rec").length > 1 then unsafeRecCount := unsafeRecCount + 1',
                '  IO.println s!"ENV_STATS ns={nsCount} thms={thmCount} defs={defCount} unsafe={unsafeCount} partial={partialCount} unsafe_rec={unsafeRecCount} user_axiom={userAxiomCount}"',
            ]
        )
        audit_file = tmp / "AuditDriver.lean"
        audit_file.write_text("\n".join(audit_lines) + "\n", encoding="utf-8")

        audit_env = env.copy()
        sysroot = audit_env.get("LEAN_SYSROOT", "")
        audit_env["LEAN_PATH"] = f"{tmp}:{sysroot}/lib/lean" if sysroot else str(tmp)
        audit_proc = subprocess.run(
            [
                *lean_prefix,
                "-M2048",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                str(audit_file),
            ],
            capture_output=True,
            text=True,
            env=audit_env,
            check=True,
        )

    audit_out = audit_proc.stdout.strip()
    stats_match = re.search(
        r"ENV_STATS ns=(\d+) thms=(\d+) defs=(\d+) unsafe=(\d+) partial=(\d+) unsafe_rec=(\d+) user_axiom=(\d+)",
        audit_out,
    )
    if not stats_match:
        print(f"error: missing ENV_STATS in audit output:\n{audit_out}", file=sys.stderr)
        return 1

    env_stats = {
        "namespace_constants": int(stats_match.group(1)),
        "theorem_constants": int(stats_match.group(2)),
        "def_constants": int(stats_match.group(3)),
        "is_unsafe": int(stats_match.group(4)),
        "is_partial": int(stats_match.group(5)),
        "unsafe_rec_helpers": int(stats_match.group(6)),
        "user_axioms": int(stats_match.group(7)),
    }

    axiom_lines: list[str] = []
    buf: list[str] = []
    for ln in audit_out.splitlines():
        s = ln.strip()
        if s.startswith("'") and ("depends on axioms:" in s or "does not depend on any axioms" in s):
            if buf:
                axiom_lines.append(" ".join(buf))
                buf = []
            buf.append(s)
        elif buf and not s.startswith("ENV_STATS"):
            buf.append(s)
        else:
            if buf:
                axiom_lines.append(" ".join(buf))
                buf = []
    if buf:
        axiom_lines.append(" ".join(buf))

    forbidden_axioms_found = any(
        bad in ln
        for ln in axiom_lines
        for bad in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
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
        "file": "support/NeverPatternsGuardPatternsAndExhaustivenessSoundness.lean",
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
