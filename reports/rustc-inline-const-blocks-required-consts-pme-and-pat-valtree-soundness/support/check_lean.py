#!/usr/bin/env python3
"""Standalone kernel, hygiene, and axiom/auxiliary-constant verifier for
InlineConstRequiredConstsAndPatValtreeSoundness.lean.

Checks:
1. Source-level purity:
   - 0 occurrences of `sorry`, `omega`, `bv_decide`, `native_decide`,
     `Classical.choice`, `partial def`, `unsafe def`, `axiom `, `opaque `
   - 0 bare `def` declarations (every `def` is `noncomputable def`)
   - 0 `deriving` clauses on custom inductives / structures
   - >= 900 lines of Lean code
2. Full kernel type-checking with:
   `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
   (wrapped in `anneal-lean-run --mode file` when present, targeting Lean v4.34.1).
3. Kernel `Environment` constant map walk (`env.constants.map₁`) and
   `#print axioms` across all major theorems inside a temporary directory:
   - 0 `sorryAx`
   - 0 `Classical.choice`
   - 0 `Lean.ofReduceBool` / `Lean.trustCompiler`
   - 0 `.isUnsafe`
   - 0 `.isPartial`
   - 0 `._unsafe_rec`
   - 0 user axioms
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


NS = "InlineConstRequiredConstsAndPatValtreeSoundness"

BANNED_SOURCE_PATTERNS = {
    "sorry": re.compile(r"\bsorry\b"),
    "omega": re.compile(r"\bomega\b"),
    "bv_decide": re.compile(r"\bbv_decide\b"),
    "native_decide": re.compile(r"\bnative_decide\b"),
    "Classical.choice": re.compile(r"\bClassical\.choice\b"),
    "partial_def": re.compile(r"\bpartial\s+def\b"),
    "unsafe_def": re.compile(r"\bunsafe\s+def\b"),
    "bare_def": re.compile(r"^\s*(?:(?:private|protected|nonrec)\s+)*def\s+", re.MULTILINE),
    "deriving": re.compile(r"^\s*deriving\b", re.MULTILINE),
    "user_axiom": re.compile(r"^\s*axiom\s+", re.MULTILINE),
    "user_opaque": re.compile(r"^\s*opaque\s+", re.MULTILINE),
}

MAJOR_THEOREMS = [
    f"{NS}.requiredConsts_captures_deadBranchPreDce",
    f"{NS}.requiredConsts_excludes_prunedAfterReturn",
    f"{NS}.emitMetadata_always_skips_pme",
    f"{NS}.postReturn_unreachable_never_produces_collector_err",
    f"{NS}.monoRoot_deadConst_triggers_pme_at_codegen",
    f"{NS}.uninstantiated_paramGeneric_zero_errors",
    f"{NS}.promotedInlineConst_surfaces_in_libOpt2_despite_ifFalse",
    f"{NS}.gvn_nonparam_generic_divergence",
    f"{NS}.instantiatedGeneric_leafCaller_inlining_deferral_matrix",
    f"{NS}.emptyDropArray_zero_expected_drops",
    f"{NS}.zero_len_array_promotable_both_shared_and_mut",
    f"{NS}.cell_and_drop_non_zero_fail_e0515",
    f"{NS}.promoted_expectedDrops_zero",
    f"{NS}.materializeBorrow_sound",
    f"{NS}.ce_promote_interiorMut_breaks_rodata_soundness",
    f"{NS}.ce_promote_needsDrop_loses_destructor",
    f"{NS}.patToBaseValTree_injective",
    f"{NS}.valtree_roundtrip_iff_valid",
    f"{NS}.base_valtree_zero_invalid_for_smallU32",
    f"{NS}.base_valtree_eleven_invalid_for_smallU32",
    f"{NS}.encodeOptionZeroNiche_lt_modulus",
    f"{NS}.encodeOptionZeroNiche_injective",
    f"{NS}.decode_encode_optionZeroNiche_roundtrip",
    f"{NS}.encodeOpt2OneTwo_fits_u8",
    f"{NS}.decode_encode_opt2OneTwo_roundtrip",
    f"{NS}.option_small_and_nzi8_sound",
    f"{NS}.llvm_range_metadata_sound_for_valid_small",
    f"{NS}.ce_transmute_zero_eleven_ub_and_llvm_divergence",
    f"{NS}.unlistable_rejects_empty_match_and_literal_only_matches",
    f"{NS}.unlistable_accepts_wildcard_and_covers_all",
    f"{NS}.emptyPat_triggers_e0004_before_layout_error",
    f"{NS}.finite_exhaustive_iff_all_covered",
    f"{NS}.anneal_lowering_fail_closed_sound",
    f"{NS}.anneal_blocks_pat_valtree_and_unevaluated_const",
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


def resolve_lean_env_and_cmd() -> tuple[dict[str, str], list[str]]:
    env = os.environ.copy()
    v434 = Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    lean_v434_bin = v434 / "bin" / "lean"
    if v434.is_dir():
        env.setdefault("LEAN_SYSROOT", str(v434))
    env["PATH"] = f"{v434 / 'bin'}:{Path.home() / '.elan' / 'bin'}:{Path.home() / '.local' / 'bin'}:{env.get('PATH', '')}"

    lean_bin = str(lean_v434_bin) if lean_v434_bin.is_file() else (shutil.which("lean", path=env["PATH"]) or "lean")
    wrapper = Path.home() / ".local" / "bin" / "anneal-lean-run"
    if wrapper.is_file():
        return env, [str(wrapper), "--mode", "file", "--", lean_bin, "-M2048"]
    return env, [lean_bin, "-M2048"]


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    lean_file = support_dir / "InlineConstRequiredConstsAndPatValtreeSoundness.lean"
    receipt_path = support_dir / "lean_check_receipt.json"

    raw_src = lean_file.read_text(encoding="utf-8")
    code_only = strip_lean_comments(raw_src)
    line_count = len(raw_src.splitlines())
    source_hits = {
        key: len(pat.findall(code_only)) for key, pat in BANNED_SOURCE_PATTERNS.items()
    }

    env, lean_prefix = resolve_lean_env_and_cmd()
    ver_proc = subprocess.run([*lean_prefix, "--version"], capture_output=True, text=True, env=env, check=True)
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

    # Kernel Environment inspection via `env.constants.map₁` + `#print axioms`
    # executed inside a temporary directory with zero writes to `support/`.
    with tempfile.TemporaryDirectory(prefix="r11_lean_audit_") as tmp_raw:
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
            "  for (nm, cinfo) in (env.constants.map₁.toList ++ env.constants.map₂.toList) do",
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

    axiom_matches = re.findall(
        r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",
        audit_out,
        re.DOTALL,
    )
    axiom_lines = [" ".join(m.split()) for m in axiom_matches]
    forbidden_axioms_found = any(
        bad in ln
        for ln in axiom_lines
        for bad in ("sorryAx", "Classical.choice", "Lean.ofReduceBool", "Lean.trustCompiler")
    )

    clean = (
        line_count >= 900
        and len(axiom_lines) == len(MAJOR_THEOREMS)
        and all(v == 0 for v in source_hits.values())
        and env_stats["namespace_constants"] > 0
        and env_stats["is_unsafe"] == 0
        and env_stats["is_partial"] == 0
        and env_stats["unsafe_rec_helpers"] == 0
        and env_stats["user_axioms"] == 0
        and not forbidden_axioms_found
    )

    receipt = {
        "lean_version": lean_version,
        "file": "support/InlineConstRequiredConstsAndPatValtreeSoundness.lean",
        "sha256": hashlib.sha256(lean_file.read_bytes()).hexdigest(),
        "line_count": line_count,
        "major_theorem_count": len(MAJOR_THEOREMS),
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
