#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Revalidate the mechanized Lean 4 probe and benchmark dataset for this report."""

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
REPORT_DIR = SUPPORT_DIR.parent
REPORT_MD_PATH = REPORT_DIR / "REPORT.md"
REPORT_JSON_PATH = REPORT_DIR / "REPORT.json"
PROBE_PATH = SUPPORT_DIR / "FuelFreeMirLiftingAndLensesProbe.lean"
METRICS_PATH = SUPPORT_DIR / "wireframe_benchmark_metrics.json"

CHECKED_THEOREMS = (
    "FuelFreeMirLiftingProbe.evalFuel_mono",
    "FuelFreeMirLiftingProbe.StepsTo.bind_wp",
    "FuelFreeMirLiftingProbe.checkPureProg_rejects_deref",
    "FuelFreeMirLiftingProbe.stepPure_simulates",
    "FuelFreeMirLiftingProbe.wpConverges_of_pureExec",
    "FuelFreeMirLiftingProbe.liftBlock_diamond_shared",
    "FuelFreeMirLiftingProbe.chained_sets_collapse_rfl",
    "FuelFreeMirLiftingProbe.forRangeUp_induction",
    "FuelFreeMirLiftingProbe.wpConverges_forRangeUp",
    "FuelFreeMirLiftingProbe.stepsTo_of_runToTarget_reached",
    "FuelFreeMirLiftingProbe.wpConverges_of_runToTarget_halted",
    "FuelFreeMirLiftingProbe.runToTarget_mono_bound",
    "FuelFreeMirLiftingProbe.stepsTo_of_runCfgToBlock_reached",
    "FuelFreeMirLiftingProbe.wpConverges_of_runCfgToBlock_halted",
    "FuelFreeMirLiftingProbe.no_uniform_fuel_countUp",
    "FuelFreeMirLiftingProbe.countUp_wpConverges_all_n",
    "FuelFreeMirLiftingProbe.subplaceFieldLens_disjoint",
    "FuelFreeMirLiftingProbe.liftLens_twoBorrowAdd_sound",
    "FuelFreeMirLiftingProbe.signExtendMod_nonneg_id",
    "FuelFreeMirLiftingProbe.pushBaseStack_step_comm",
    "FuelFreeMirLiftingProbe.instantiated_transmute_roundtrip",
    "FuelFreeMirLiftingProbe.subplaceWrite_sibling_preserves_field0",
)

ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})


def _find_lean_cmd() -> list[str]:
    prefix: list[str] = []
    anneal_runner = shutil.which("anneal-lean-run")
    if anneal_runner:
        prefix = [anneal_runner, "--mode", "file", "--concurrency", "1", "--"]

    direct_4341 = (
        Path.home()
        / ".elan"
        / "toolchains"
        / "leanprover--lean4---v4.34.1"
        / "bin"
        / "lean"
    )
    if direct_4341.is_file():
        return prefix + [str(direct_4341)]

    elan = shutil.which("elan")
    if elan:
        probe = subprocess.run(
            [elan, "which", "--toolchain", "leanprover/lean4:v4.34.1", "lean"],
            capture_output=True,
            text=True,
            check=False,
        )
        if probe.returncode == 0:
            return prefix + [elan, "run", "leanprover/lean4:v4.34.1", "lean"]

    lean = shutil.which("lean")
    if lean:
        return prefix + [lean]
    raise RuntimeError("Neither 'elan' nor 'lean' was found on PATH")


_CHAR_LIT_RE = re.compile(
    r"^'(?:[^'\\\n\r]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[^\n\r]))'"
)


def _is_lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in ("_", "'")


def _strip_lean_comments_preserving_strings(src: str) -> str:
    out: list[str] = []
    i = 0
    n = len(src)
    block_depth = 0
    in_string = False
    prev_ch = ""
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    prev_ch = ""
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_string:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(nxt)
                i += 2
                continue
            if ch == '"':
                in_string = False
                prev_ch = ""
            i += 1
            continue
        if ch == '"':
            in_string = True
            out.append(ch)
            i += 1
            prev_ch = ""
            continue
        if ch == "'" and (not prev_ch or not _is_lean_ident_char(prev_ch)):
            m_char = _CHAR_LIT_RE.match(src[i:])
            if m_char:
                lit = m_char.group(0)
                out.append(lit)
                i += len(lit)
                prev_ch = ""
                continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            i += 2
            prev_ch = ""
            continue
        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            prev_ch = ""
            continue
        out.append(ch)
        prev_ch = ch
        i += 1
    return "".join(out)


def verify_lean_probe() -> None:
    sample = "def f (c' : Char) := if c'<'\"' then 'α' else '\\x22' -- hide\nsorry\n"
    sample_stripped = _strip_lean_comments_preserving_strings(sample)
    if "hide" in sample_stripped or not re.search(r"\bsorry\b", sample_stripped):
        raise AssertionError("Comment stripper misparsed identifier prime before char literal")

    text = PROBE_PATH.read_text(encoding="utf-8")
    if "twenty-two exported theorems" not in text:
        raise AssertionError(
            f"{PROBE_PATH.name} header docstring must match CHECKED_THEOREMS count (22)"
        )
    for lineno, line in enumerate(text.splitlines(), start=1):
        if len(line) > 80:
            raise AssertionError(
                f"{PROBE_PATH.name}:{lineno} exceeds 80 columns ({len(line)} cols)"
            )
    stripped = _strip_lean_comments_preserving_strings(text)
    for forbidden in ("sorry", "admit", "axiom ", "native_decide"):
        if re.search(rf"\b{re.escape(forbidden.strip())}\b", stripped):
            raise AssertionError(f"{PROBE_PATH.name} contains forbidden token {forbidden!r}")

    m_countup = re.search(
        r"theorem\s+countUp_wpConverges_all_n\b(.*?)(?=\n(?:structure|def|theorem|end)\s)",
        stripped,
        flags=re.DOTALL,
    )
    if not m_countup:
        raise AssertionError("Could not isolate theorem countUp_wpConverges_all_n in probe")
    leaked_num = re.search(r"\b(?:[2-9]|\d{2,})\b", m_countup.group(1))
    if leaked_num:
        raise AssertionError(
            "countUp_wpConverges_all_n leaked explicit step/fuel numeral "
            f"{leaked_num.group(0)!r}"
        )

    cmd = _find_lean_cmd()
    res = subprocess.run(cmd + [str(PROBE_PATH)], capture_output=True, text=True, check=False)
    if res.returncode != 0 or res.stdout.strip() or res.stderr.strip():
        raise AssertionError(
            f"Lean check failed or emitted diagnostics (exit {res.returncode}):\n"
            f"stdout:\n{res.stdout}\nstderr:\n{res.stderr}"
        )

    # Also verify kernel axiom footprints of all exported theorems via #print axioms.
    axiom_lines = "\n".join(f"#print axioms {thm}" for thm in CHECKED_THEOREMS)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", encoding="utf-8", delete=False
    ) as tmp:
        tmp.write(text + "\n" + axiom_lines + "\n")
        tmp_path = Path(tmp.name)
    try:
        ax_res = subprocess.run(
            cmd + [str(tmp_path)], capture_output=True, text=True, check=False
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    if ax_res.returncode != 0:
        raise AssertionError(f"Axiom audit failed:\n{ax_res.stdout}\n{ax_res.stderr}")

    seen = 0
    for line in ax_res.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        if "does not depend on any axioms" in line:
            seen += 1
            continue
        match = re.search(r"depends on axioms: \[(.*)\]$", line)
        if not match:
            raise AssertionError(f"Unexpected #print axioms output line: {line!r}")
        axioms = {a.strip() for a in match.group(1).split(",") if a.strip()}
        disallowed = axioms - ALLOWED_AXIOMS
        if disallowed:
            raise AssertionError(f"Disallowed axioms {sorted(disallowed)} in: {line}")
        seen += 1

    if seen != len(CHECKED_THEOREMS):
        raise AssertionError(f"Expected {len(CHECKED_THEOREMS)} axiom reports, got {seen}")


def verify_metrics_json() -> None:
    data = json.loads(METRICS_PATH.read_text(encoding="utf-8"))
    suite = data["wireframe_demo_suite"]
    funcs = suite["functions"]
    totals = suite["totals"]

    if len(funcs) != 7:
        raise AssertionError(f"Expected 7 WireframeDemo functions, got {len(funcs)}")

    loc_base = sum(f["loc_manual_blockctx_baseline"] for f in funcs)
    loc_lift = sum(f["loc_normalized_lifted"] for f in funcs)
    hb_init = sum(f["heartbeats_k_initial_lifted"] for f in funcs)
    hb_norm = sum(f["heartbeats_k_normalized_lifted"] for f in funcs)
    bctx_base = sum(f["blockctx_occurrences_baseline"] for f in funcs)
    bctx_lift = sum(f["blockctx_occurrences_lifted"] for f in funcs)
    fuel_lift = sum(f["manual_fuel_numerals_lifted"] for f in funcs)

    assert loc_base == totals["loc_manual_blockctx_baseline"] == 8009
    assert loc_lift == totals["loc_normalized_lifted"] == 1421
    assert loc_lift - loc_base == totals["loc_delta"] == -6588
    assert round((loc_lift - loc_base) * 100.0 / loc_base, 1) == totals["loc_delta_pct"] == -82.3
    assert bctx_base == totals["blockctx_occurrences_baseline"] == 111
    assert bctx_lift == totals["blockctx_occurrences_lifted"] == 0
    assert fuel_lift == totals["manual_fuel_numerals_lifted"] == 0
    assert hb_init == totals["heartbeats_k_initial_lifted"] == 1388934
    assert hb_norm == totals["heartbeats_k_normalized_lifted"] == 665228
    assert hb_norm - hb_init == totals["heartbeats_delta"] == -723706
    assert round((hb_norm - hb_init) * 100.0 / hb_init, 1) == totals["heartbeats_delta_pct"] == -52.1

    for f in funcs:
        assert "uses_mir_lift_rules" in f and "uses_mir_lift_macro" not in f, f["name"]
        d = f["loc_normalized_lifted"] - f["loc_manual_blockctx_baseline"]
        assert d == f["loc_delta"], f["name"]
        pct = round(d * 100.0 / f["loc_manual_blockctx_baseline"], 1)
        assert pct == f["loc_delta_pct"], (f["name"], pct, f["loc_delta_pct"])
        hb_d = f["heartbeats_k_normalized_lifted"] - f["heartbeats_k_initial_lifted"]
        hb_pct = round(hb_d * 100.0 / f["heartbeats_k_initial_lifted"], 1)
        assert hb_pct == f["heartbeats_delta_pct"], (f["name"], hb_pct, f["heartbeats_delta_pct"])

    theory = data["shared_theory_amortization"]
    net_delta = sum(m["delta"] for m in theory["modules"])
    for m in theory["modules"]:
        assert m["loc_after"] - m["loc_before"] == m["delta"], m["module"]
    assert net_delta == theory["net_shared_theory_delta_loc"] == 2972
    ratio = round(net_delta / abs(totals["loc_delta"]), 4)
    assert ratio == theory["amortization_ratio_vs_wireframe_saved_loc"] == 0.4511

    post_loc = data["elaboration_scaling"]["post_integration_module_loc"]
    assert post_loc["theory/Anneal/PureMirExec.lean"] == 20564
    assert post_loc["theory/Anneal/MirLiftCore.lean"] == 4517
    assert post_loc["theory/Anneal/MirLift.lean"] == 730
    assert post_loc["theory/Anneal/MirLoops.lean"] == 692
    assert post_loc["theory/Anneal/SepLogicLenses.lean"] == 13718
    assert post_loc["theory/Anneal/Rustc/V2026_06_01/SymReflect.lean"] == 7314


def verify_report_cross_refs_and_hygiene() -> None:
    probe_lines = PROBE_PATH.read_text(encoding="utf-8").splitlines()
    probe_total = len(probe_lines)
    report_text = REPORT_MD_PATH.read_text(encoding="utf-8")

    expected_header = f"(`support/FuelFreeMirLiftingAndLensesProbe.lean`, {probe_total} lines):"
    if expected_header not in report_text:
        raise AssertionError(
            f"REPORT.md Evidence header out of sync with probe line count ({probe_total})"
        )

    thm_count = len(CHECKED_THEOREMS)
    for phrase in (
        f"all {thm_count} exported theorems",
        f"all {thm_count} mechanized theorems",
    ):
        norm_report = " ".join(report_text.split())
        if phrase not in norm_report:
            raise AssertionError(
                f"REPORT.md out of sync with CHECKED_THEOREMS ({thm_count}): missing {phrase!r}"
            )

    for lineno, line in enumerate(report_text.splitlines(), start=1):
        if line.lstrip().startswith("|"):
            continue
        if len(line) > 80:
            raise AssertionError(
                f"REPORT.md:{lineno} exceeds 80 columns ({len(line)} cols): {line!r}"
            )

    decl_lines: dict[str, int] = {}
    all_decls: dict[str, int] = {}
    for idx, pline in enumerate(probe_lines, start=1):
        m_thm = re.match(r"^theorem\s+([A-Za-z0-9_.']+)\b", pline)
        if m_thm:
            decl_lines[m_thm.group(1)] = idx
        m_any = re.match(r"^(?:theorem|def|inductive|structure)\s+([A-Za-z0-9_.']+)\b", pline)
        if m_any:
            all_decls[m_any.group(1)] = idx

    for full_thm in CHECKED_THEOREMS:
        short = full_thm.removeprefix("FuelFreeMirLiftingProbe.")
        if short not in decl_lines:
            raise AssertionError(f"Missing theorem declaration in probe: {short}")
        if f"`{short}`" not in report_text:
            raise AssertionError(f"REPORT.md does not mention checked theorem `{short}`")

    range_patterns = (
        re.compile(r"FuelFreeMirLiftingAndLensesProbe\.lean:(\d+)-(\d+)"),
        re.compile(r"[Ll]ines\s+(\d+)[–-](\d+)"),
    )
    found_ranges: list[tuple[int, int]] = []
    for pat in range_patterns:
        for m in pat.finditer(report_text):
            lo, hi = int(m.group(1)), int(m.group(2))
            if not (1 <= lo <= hi <= probe_total):
                raise AssertionError(
                    f"Out-of-bounds line range {lo}..{hi} in REPORT.md (probe has {probe_total} lines)"
                )
            found_ranges.append((lo, hi))
    if len(found_ranges) < 10:
        raise AssertionError(
            f"Expected >= 10 probe line citations in REPORT.md, got {len(found_ranges)}"
        )

    for short, dline in decl_lines.items():
        full = f"FuelFreeMirLiftingProbe.{short}"
        if full in CHECKED_THEOREMS and not any(lo <= dline <= hi for lo, hi in found_ranges):
            raise AssertionError(
                f"Checked theorem {short} at line {dline} is not covered by any cited range in REPORT.md"
            )

    # Verify every Evidence probe bullet and inline probe citation actually covers
    # the exact declaration line of each probe identifier named in that citation.
    def _expand_evidence_span(span: str) -> list[str]:
        m_brace = re.fullmatch(r"([A-Za-z0-9_.']+)\.\{([^}]+)\}", span.strip())
        if m_brace:
            prefix = m_brace.group(1)
            parts = [p.strip() for p in m_brace.group(2).split(",") if p.strip()]
            if not parts or not all(re.fullmatch(r"[A-Za-z0-9_.']+", p) for p in parts):
                raise AssertionError(f"Malformed grouped identifier `{span}` in Evidence")
            return [f"{prefix}.{p}" for p in parts]
        if re.fullmatch(r"[A-Za-z0-9_.']+", span.strip()):
            return [span.strip()]
        raise AssertionError(f"Unrecognized backtick span `{span}` in Evidence bullet")

    evidence_bullet_re = re.compile(
        r"^\s*-\s+([^:\n]+(?:\n\s+[^:\n]+)*?)\s*\(Lines\s+(\d+)[–-](\d+)\):",
        flags=re.MULTILINE,
    )
    evidence_bullets = list(evidence_bullet_re.finditer(report_text))
    if len(evidence_bullets) < 5:
        raise AssertionError(f"Expected >= 5 Evidence probe bullets, got {len(evidence_bullets)}")
    for mb in evidence_bullets:
        lo, hi = int(mb.group(2)), int(mb.group(3))
        raw_spans = re.findall(r"`([^`]+)`", mb.group(1))
        if not raw_spans:
            raise AssertionError("Evidence probe bullet listed zero backtick identifiers")
        for span in raw_spans:
            for ident in _expand_evidence_span(span):
                if ident not in all_decls:
                    raise AssertionError(f"Unknown probe identifier `{ident}` in Evidence bullet")
                dline = all_decls[ident]
                if not (lo <= dline <= hi):
                    raise AssertionError(
                        f"Evidence bullet range {lo}..{hi} does not contain `{ident}` (line {dline})"
                    )

    inline_cite_re = re.compile(
        r"`([A-Za-z0-9_.']+)(?:\s+[A-Za-z0-9_]+)*`"
        r"(?:(?:\s*,\s*(?:and\s+)?|\s+(?:and|\+|modeled by)\s*)`[A-Za-z0-9_.']+`)*"
        r"(?:\s*\([^)\n]*?;\s*mechanized\s+in\s+`support/FuelFreeMirLiftingAndLensesProbe\.lean:(\d+)-(\d+)`\)"
        r"|\s*(?:in\s+`support/FuelFreeMirLiftingAndLensesProbe\.lean:(\d+)-(\d+)`"
        r"|,\s*`support/FuelFreeMirLiftingAndLensesProbe\.lean:(\d+)-(\d+)`"
        r"|,\s*lines\s+(\d+)[–-](\d+)))"
    )
    inline_cites = list(inline_cite_re.finditer(report_text))
    if len(inline_cites) < 13:
        raise AssertionError(
            f"Expected >= 13 inline probe declaration citations, got {len(inline_cites)}"
        )
    for mc in inline_cites:
        nums = [int(g) for g in mc.groups()[1:] if g is not None]
        lo, hi = nums[0], nums[1]
        prefix = mc.group(0).split("FuelFreeMirLiftingAndLensesProbe")[0].split("lines")[0]
        checked_any = False
        for span in re.findall(r"`([^`]+)`", prefix):
            first_tok = span.strip().split()[0]
            if first_tok in all_decls:
                checked_any = True
                dline = all_decls[first_tok]
                if not (lo <= dline <= hi):
                    raise AssertionError(
                        f"Inline citation range {lo}..{hi} does not contain `{first_tok}` (line {dline})"
                    )
        if not checked_any:
            raise AssertionError(f"Inline citation matched zero probe declarations: {mc.group(0)!r}")

    leak_parts = (
        "adv/" + "ff-",
        "ff" + "43-",
        "FF-" + "4.",
        "group" + "agent-",
        "/x" + "20/",
        "/google/" + "data/",
    )
    for path in (REPORT_MD_PATH, REPORT_JSON_PATH, PROBE_PATH, METRICS_PATH):
        txt = path.read_text(encoding="utf-8")
        for tok in leak_parts:
            if tok in txt:
                raise AssertionError(f"Non-public token {tok!r} leaked into {path.name}")


def main() -> int:
    env_extra = [
        str(Path.home() / ".elan" / "bin"),
        str(Path.home() / ".cargo" / "bin"),
        str(Path.home() / ".local" / "bin"),
    ]
    os.environ["PATH"] = ":".join(env_extra + [os.environ.get("PATH", "")])
    verify_lean_probe()
    verify_metrics_json()
    verify_report_cross_refs_and_hygiene()
    print(
        "support verification passed: FuelFreeMirLiftingAndLensesProbe.lean "
        f"({len(CHECKED_THEOREMS)} theorems, constructive axioms only) + "
        "wireframe_benchmark_metrics.json (7 functions, 8009 -> 1421 LOC, -82.3%)"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
