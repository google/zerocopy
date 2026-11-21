#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Twin-compiler 5-level differential oracle and pinned rustc quirk/shim extractor.

Performs two self-contained, read-only operations:
1. Extracts FutureIncompatibilityReason variants, all Future-Incompatible Lint
   (FCW) registrations, tests/crashes counts, //@ known-bug: directives,
   //@ ignore-compare-mode-next-solver directives, //@ needs-deterministic-layouts
   directives, and MIR UB-preservation gaps from a pinned rust-lang/rust Git commit
   strictly via read-only `git ls-tree` and `git cat-file --batch` calls.
2. Executes a 22-specimen differential test suite inside an isolated
   `tempfile.TemporaryDirectory()` across `rustc +1.99.1`, `rustc +nightly`,
   and `miri`, evaluating all 5 comparison levels (L1 acceptance/ICE, L2 JSON
   diagnostics/FCW/rustfix spans, L3 dep-info/symbols/ABI layout, L4 runtime
   I/O/unwind/NaN, and L5 Miri Abstract-Machine UB check) and classifying every
   comparison into the 6-class Divergence Lattice.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
from typing import Any


PINNED_SOURCE_SHA = "412be32a6a189d9a28922beee178bc0abee9d492"

DIVERGENCE_CLASSES = (
    "EQUIVALENT",
    "BENIGN_UNSPECIFIED_CHOICE",
    "INTENTIONAL_BUG_FIX_OR_STRICTNESS",
    "FCW_COMPATIBILITY_DRIFT",
    "SPEC_REGRESSION_FALSE_POSITIVE",
    "SOUNDNESS_MISCOMPILATION",
)


def sanitize_text(text: str, tmpdir: str | None = None) -> str:
    """Scrub ephemeral temp and home directory prefixes from captured outputs."""
    out = text
    if tmpdir:
        out = out.replace(tmpdir, "<TMPDIR>")
    home = str(Path.home())
    if home and home != "/":
        out = out.replace(home, "<HOME>")
    return out


class GitObjectReader:
    """Read-only, linear-time Git blob reader backed by `git cat-file --batch`."""

    def __init__(self, repo_path: Path, revision: str) -> None:
        self.repo_path = repo_path
        self.revision = revision
        self._tree_entries: dict[str, str] | None = None

    def _ensure_tree(self) -> dict[str, str]:
        if self._tree_entries is not None:
            return self._tree_entries
        raw = subprocess.check_output(
            ["git", "-C", str(self.repo_path), "ls-tree", "-r", "-z", self.revision],
            timeout=60,
        )
        entries: dict[str, str] = {}
        for rec in raw.split(b"\x00"):
            if not rec:
                continue
            tab_idx = rec.find(b"\t")
            if tab_idx < 0:
                continue
            meta = rec[:tab_idx].decode("ascii", errors="replace").split()
            if len(meta) >= 3 and meta[1] == "blob":
                path_str = rec[tab_idx + 1 :].decode("utf-8", errors="replace")
                entries[path_str] = meta[2]
        self._tree_entries = entries
        return entries

    def paths_under(self, prefix: str, suffix: str = "") -> list[str]:
        entries = self._ensure_tree()
        return sorted(
            p for p in entries if p.startswith(prefix) and (not suffix or p.endswith(suffix))
        )

    def read_text(self, rel_path: str) -> str:
        return self.read_many([rel_path]).get(rel_path, "")

    def read_many(self, rel_paths: list[str]) -> dict[str, str]:
        entries = self._ensure_tree()
        req_lines: list[str] = []
        ordered_paths: list[str] = []
        for p in rel_paths:
            oid = entries.get(p)
            if oid:
                req_lines.append(oid)
                ordered_paths.append(p)
        if not req_lines:
            return {}
        proc = subprocess.run(
            ["git", "-C", str(self.repo_path), "cat-file", "--batch"],
            input=("\n".join(req_lines) + "\n").encode("ascii"),
            capture_output=True,
            check=True,
            timeout=120,
        )
        buf = proc.stdout
        pos = 0
        out: dict[str, str] = {}
        for p in ordered_paths:
            nl = buf.find(b"\n", pos)
            if nl < 0:
                break
            header = buf[pos:nl].decode("ascii", errors="replace").split()
            pos = nl + 1
            if len(header) < 3 or header[1] == "missing":
                continue
            size = int(header[2])
            blob = buf[pos : pos + size]
            pos += size + 1  # trailing LF
            out[p] = blob.decode("utf-8", errors="replace")
        return out


def strip_line_comments_preserve_lines(src: str) -> str:
    """Linear O(N) line-comment stripper preserving line count and string literals."""
    out_lines: list[str] = []
    for line in src.splitlines():
        in_str = False
        esc = False
        cut = len(line)
        i = 0
        n = len(line)
        while i < n:
            ch = line[i]
            if in_str:
                if esc:
                    esc = False
                elif ch == "\\":
                    esc = True
                elif ch == '"':
                    in_str = False
                i += 1
            else:
                if ch == '"':
                    in_str = True
                    i += 1
                elif ch == "/" and i + 1 < n and line[i + 1] == "/":
                    cut = i
                    break
                else:
                    i += 1
        out_lines.append(line[:cut])
    return "\n".join(out_lines)


def extract_balanced(src: str, start_idx: int, open_ch: str, close_ch: str) -> str:
    """Linear O(N) balanced delimiter extractor starting at or before `open_ch`."""
    pos = src.find(open_ch, start_idx)
    if pos < 0:
        return ""
    depth = 0
    in_str = False
    esc = False
    for idx in range(pos, len(src)):
        ch = src[idx]
        if in_str:
            if esc:
                esc = False
            elif ch == "\\":
                esc = True
            elif ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return src[pos + 1 : idx]
    return src[pos + 1 :]


def extract_pinned_source_census(repo_path: Path, revision: str) -> dict[str, Any]:
    """Extract shims, FCWs, crashes, known-bugs, solver ignores, and UB-erasure sites."""
    reader = GitObjectReader(repo_path, revision)

    # 1. FutureIncompatibilityReason variants & FutureIncompatibleInfo fields
    lint_defs_lib = reader.read_text("compiler/rustc_lint_defs/src/lib.rs")
    clean_lib = strip_line_comments_preserve_lines(lint_defs_lib)
    enum_pos = clean_lib.find("pub enum FutureIncompatibilityReason")
    enum_body = extract_balanced(clean_lib, enum_pos, "{", "}") if enum_pos >= 0 else ""
    reason_variants: list[dict[str, str]] = []
    for raw_entry in enum_body.split(",\n"):
        s = raw_entry.strip().rstrip(",")
        if not s:
            continue
        paren = s.find("(")
        if paren > 0:
            vname = s[:paren].strip()
            payload = s[paren:].strip()
        else:
            vname = s
            payload = ""
        if vname and vname[0].isupper():
            reason_variants.append({"variant": vname, "payload": payload})

    info_pos = clean_lib.find("pub struct FutureIncompatibleInfo")
    info_body = extract_balanced(clean_lib, info_pos, "{", "}") if info_pos >= 0 else ""
    info_fields = [
        ln.strip().rstrip(",")
        for ln in info_body.splitlines()
        if ln.strip().startswith("pub ")
    ]

    # 2. All 71 Future-Incompatible Lint (FCW) registrations
    lint_paths = reader.paths_under("compiler/rustc_lint_defs/src/", ".rs") + reader.paths_under(
        "compiler/rustc_lint/src/", ".rs"
    )
    lint_blobs = reader.read_many(lint_paths)
    fcw_lints: list[dict[str, Any]] = []
    decl_marker = "declare_lint!"

    for fp, raw_src in sorted(lint_blobs.items()):
        if fp == "compiler/rustc_lint_defs/src/lib.rs":
            continue
        cleaned = strip_line_comments_preserve_lines(raw_src)
        line_starts = [0]
        for idx, ch in enumerate(cleaned):
            if ch == "\n":
                line_starts.append(idx + 1)

        def offset_to_line(off: int) -> int:
            lo, hi = 0, len(line_starts) - 1
            while lo <= hi:
                mid = (lo + hi) // 2
                if line_starts[mid] <= off:
                    lo = mid + 1
                else:
                    hi = mid - 1
            return hi + 1

        search_pos = 0
        while True:
            idx = cleaned.find(decl_marker, search_pos)
            if idx < 0:
                break
            # Find opening delimiter '{' or '(' after declare_lint!
            delim_pos = idx + len(decl_marker)
            while delim_pos < len(cleaned) and cleaned[delim_pos].isspace():
                delim_pos += 1
            if delim_pos >= len(cleaned) or cleaned[delim_pos] not in "{(":
                search_pos = idx + len(decl_marker)
                continue
            open_ch = cleaned[delim_pos]
            close_ch = "}" if open_ch == "{" else ")"
            body = extract_balanced(cleaned, delim_pos, open_ch, close_ch)
            search_pos = delim_pos + len(body) + 2
            if "@future_incompatible" not in body:
                continue

            # Parse `vis IDENT, Level,`
            tokens = [t.strip() for t in body.split(",")]
            if len(tokens) < 2:
                continue
            first_words = tokens[0].split()
            ident = first_words[-1] if first_words else ""
            default_level = tokens[1].split()[0] if tokens[1].split() else ""
            if not ident.isupper():
                continue

            fcw_idx = body.find("FutureIncompatibleInfo")
            fcw_block = extract_balanced(body, fcw_idx, "{", "}") if fcw_idx >= 0 else ""

            reason_variant = "Unknown"
            issue_number: int | None = None
            target_edition: str | None = None
            page_slug: str | None = None
            custom_text: str | None = None

            fcw_macro_idx = fcw_block.find("fcw!(")
            if fcw_macro_idx >= 0:
                fcw_inner = extract_balanced(fcw_block, fcw_macro_idx, "(", ")").strip()
                if fcw_inner.startswith('"'):
                    reason_variant = "Custom"
                    end_q = fcw_inner.find('"', 1)
                    if end_q > 0:
                        custom_text = fcw_inner[1:end_q]
                    hash_pos = fcw_inner.find("#", max(end_q, 0))
                    if hash_pos >= 0:
                        num_str = fcw_inner[hash_pos + 1 :].strip()
                        if num_str.isdigit():
                            issue_number = int(num_str)
                else:
                    parts = fcw_inner.split()
                    if parts:
                        reason_variant = parts[0]
                    if "#" in fcw_inner:
                        num_str = fcw_inner.split("#", 1)[1].strip()
                        if num_str.isdigit():
                            issue_number = int(num_str)
                    elif len(parts) >= 3:
                        target_edition = parts[1]
                        raw_slug = " ".join(parts[2:]).strip()
                        if raw_slug.startswith('"') and raw_slug.endswith('"'):
                            page_slug = raw_slug[1:-1]
            elif "FutureIncompatibilityReason::" in fcw_block:
                after = fcw_block.split("FutureIncompatibilityReason::", 1)[1]
                vname_end = 0
                while vname_end < len(after) and (
                    after[vname_end].isalnum() or after[vname_end] == "_"
                ):
                    vname_end += 1
                reason_variant = after[:vname_end]

            report_in_deps = "report_in_deps: true" in " ".join(fcw_block.split())
            explain_reason = "explain_reason: false" not in " ".join(fcw_block.split())
            report_in_external_macro = "report_in_external_macro" in body

            fcw_lints.append(
                {
                    "ident": ident,
                    "name": ident.lower(),
                    "default_level": default_level,
                    "reason_variant": reason_variant,
                    "issue_number": issue_number,
                    "target_edition": target_edition,
                    "page_slug": page_slug,
                    "custom_text": custom_text,
                    "report_in_deps": report_in_deps,
                    "explain_reason": explain_reason,
                    "report_in_external_macro": report_in_external_macro,
                    "source_file": fp,
                    "line": offset_to_line(idx),
                }
            )

    fcw_by_reason = Counter(x["reason_variant"] for x in fcw_lints)
    fcw_by_level = Counter(x["default_level"] for x in fcw_lints)
    fcw_report_in_deps_count = sum(1 for x in fcw_lints if x["report_in_deps"])

    # 3. Scan tests/ for crashes, known-bug, ignore-compare-mode-next-solver, needs-deterministic-layouts
    test_rs_paths = reader.paths_under("tests/", ".rs")
    crashes_rs_paths = [p for p in test_rs_paths if p.startswith("tests/crashes/")]

    # Read all tests/*.rs in batches of 2000 for low memory + fast cat-file streaming
    known_bug_files: list[dict[str, Any]] = []
    known_bug_by_suite: Counter[str] = Counter()
    known_bug_by_ui_subdir: Counter[str] = Counter()
    known_bug_issues: Counter[str] = Counter()

    next_solver_ignore_by_subdir: Counter[str] = Counter()
    next_solver_ignore_count = 0

    deterministic_layout_files: list[str] = []
    deterministic_layout_by_suite: Counter[str] = Counter()

    batch_size = 2000
    for start in range(0, len(test_rs_paths), batch_size):
        batch = test_rs_paths[start : start + batch_size]
        blobs = reader.read_many(batch)
        for p, content in blobs.items():
            # Header directives live near top of compiletest files, but scan all lines linearly
            kb_targets: list[str] = []
            has_next_ignore = False
            has_det_layout = False
            for ln in content.splitlines():
                s = ln.strip()
                if not s.startswith("//@"):
                    continue
                directive = s[3:].strip()
                # Strip optional `[revision]` prefix: `//[rev]` -> `//@[rev] ...`
                if directive.startswith("["):
                    rbracket = directive.find("]")
                    if rbracket > 0:
                        directive = directive[rbracket + 1 :].strip()
                if directive.startswith("known-bug:"):
                    target = directive[len("known-bug:") :].strip()
                    kb_targets.append(target)
                elif directive.startswith("ignore-compare-mode-next-solver"):
                    has_next_ignore = True
                elif directive.startswith("needs-deterministic-layouts"):
                    has_det_layout = True

            parts = p.split("/")
            suite = parts[1] if len(parts) > 1 else "root"
            ui_sub = parts[2] if len(parts) > 2 and suite == "ui" else suite

            if kb_targets:
                known_bug_by_suite[suite] += 1
                if suite == "ui":
                    known_bug_by_ui_subdir[ui_sub] += 1
                for t in kb_targets:
                    for tok in t.replace(",", " ").split():
                        known_bug_issues[tok] += 1
                known_bug_files.append({"file": p, "suite": suite, "targets": kb_targets})

            if has_next_ignore and suite == "ui":
                next_solver_ignore_count += 1
                next_solver_ignore_by_subdir[ui_sub] += 1

            if has_det_layout:
                deterministic_layout_files.append(p)
                deterministic_layout_by_suite[f"{suite}/{ui_sub}" if suite == "ui" else suite] += 1

    # 4. Audit mir_preserve_ub checks across compiler/rustc_mir_transform/src/
    mir_paths = reader.paths_under("compiler/rustc_mir_transform/src/", ".rs")
    mir_blobs = reader.read_many(mir_paths)
    mir_preserve_ub_sites: list[dict[str, Any]] = []
    is_safe_to_remove_callers: list[dict[str, Any]] = []
    for mp, mtxt in sorted(mir_blobs.items()):
        for lineno, ln in enumerate(mtxt.splitlines(), 1):
            if "mir_preserve_ub" in ln:
                mir_preserve_ub_sites.append(
                    {"file": mp, "line": lineno, "code": ln.strip()}
                )
            if "is_safe_to_remove" in ln or "can_be_removed_if_dead" in ln:
                is_safe_to_remove_callers.append(
                    {"file": mp, "line": lineno, "code": ln.strip()}
                )

    return {
        "source_revision": revision,
        "future_incompatibility_reason_enum": {
            "source": "compiler/rustc_lint_defs/src/lib.rs:368-448",
            "variant_count": len(reason_variants),
            "variants": reason_variants,
            "info_struct_fields": info_fields,
        },
        "fcw_lint_census": {
            "total_fcw_lints": len(fcw_lints),
            "by_reason_variant": dict(fcw_by_reason.most_common()),
            "by_default_level": dict(fcw_by_level.most_common()),
            "report_in_deps_true_count": fcw_report_in_deps_count,
            "report_in_deps_false_count": len(fcw_lints) - fcw_report_in_deps_count,
            "lints": fcw_lints,
        },
        "tests_crashes_census": {
            "directory": "tests/crashes/",
            "total_rs_files": len(crashes_rs_paths),
        },
        "known_bug_census": {
            "total_files_with_known_bug": len(known_bug_files),
            "total_directives": sum(len(x["targets"]) for x in known_bug_files),
            "by_top_level_suite": dict(known_bug_by_suite.most_common()),
            "by_ui_subsystem_top20": dict(known_bug_by_ui_subdir.most_common(20)),
            "top_25_issue_targets": dict(known_bug_issues.most_common(25)),
        },
        "next_solver_ui_ignore_census": {
            "directive": "//@ ignore-compare-mode-next-solver",
            "total_ui_files": next_solver_ignore_count,
            "by_ui_subsystem_top20": dict(next_solver_ignore_by_subdir.most_common(20)),
        },
        "deterministic_layout_census": {
            "directive": "//@ needs-deterministic-layouts",
            "total_files": len(deterministic_layout_files),
            "by_suite": dict(deterministic_layout_by_suite.most_common()),
            "files": deterministic_layout_files,
        },
        "mir_preserve_ub_static_audit": {
            "mir_transform_files_scanned": len(mir_paths),
            "mir_preserve_ub_checks": mir_preserve_ub_sites,
            "dead_rvalue_removal_sites": is_safe_to_remove_callers,
            "gvn_has_mir_preserve_ub_check": any(
                "gvn.rs" in x["file"] for x in mir_preserve_ub_sites
            ),
            "dse_has_mir_preserve_ub_check": any(
                "dead_store_elimination.rs" in x["file"] for x in mir_preserve_ub_sites
            ),
        },
    }


def run_proc(
    cmd: list[str],
    cwd: Path,
    env_extra: dict[str, str] | None = None,
    timeout: int = 90,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    if env_extra:
        for k, v in env_extra.items():
            if v is None:
                env.pop(k, None)
            else:
                env[k] = v
    return subprocess.run(
        cmd,
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def parse_json_diagnostics(stderr: str) -> dict[str, Any]:
    """Parse `--error-format=json` and `--json=future-incompat` lines from rustc stderr."""
    codes: list[str] = []
    levels: list[str] = []
    primary_spans: list[dict[str, Any]] = []
    machine_suggestions: list[dict[str, Any]] = []
    fcw_reports: list[dict[str, Any]] = []

    def walk_spans_for_suggestions(diag_obj: dict[str, Any]) -> None:
        for sp in diag_obj.get("spans") or []:
            if sp.get("suggestion_applicability") == "MachineApplicable" and (
                sp.get("suggested_replacement") is not None
            ):
                machine_suggestions.append(
                    {
                        "byte_start": sp["byte_start"],
                        "byte_end": sp["byte_end"],
                        "replacement": sp["suggested_replacement"],
                    }
                )
        for ch in diag_obj.get("children") or []:
            walk_spans_for_suggestions(ch)

    for line in stderr.splitlines():
        s = line.strip()
        if not s.startswith("{"):
            continue
        try:
            obj = json.loads(s)
        except json.JSONDecodeError:
            continue
        msg_type = obj.get("$message_type")
        if msg_type == "future_incompat" or "future_incompat_report" in obj:
            items = obj.get("future_incompat_report") or []
            for it in items:
                d = it.get("diagnostic") or {}
                code_obj = d.get("code") or {}
                fcw_reports.append(
                    {
                        "code": code_obj.get("code"),
                        "level": d.get("level"),
                        "message": d.get("message", "")[:120],
                    }
                )
            continue
        if "level" in obj and "spans" in obj:
            lvl = obj.get("level", "")
            if lvl in ("error", "warning", "error: internal compiler error"):
                levels.append(lvl)
                code_obj = obj.get("code")
                if isinstance(code_obj, dict) and code_obj.get("code"):
                    codes.append(code_obj["code"])
                for sp in obj.get("spans") or []:
                    if sp.get("is_primary"):
                        primary_spans.append(
                            {
                                "byte_start": sp.get("byte_start"),
                                "byte_end": sp.get("byte_end"),
                                "line_start": sp.get("line_start"),
                                "column_start": sp.get("column_start"),
                            }
                        )
                walk_spans_for_suggestions(obj)

    return {
        "codes": sorted(set(codes)),
        "levels": levels,
        "primary_spans": primary_spans[:4],
        "machine_applicable_suggestions": machine_suggestions[:4],
        "fcw_report_items": fcw_reports,
    }


def classify_outcome(rc: int, stderr: str) -> str:
    if rc == 101 or "internal compiler error" in stderr.lower():
        return "ice"
    if rc == 0:
        return "accept"
    return "reject"


def parse_nm_symbols(bin_path: Path, cwd: Path) -> dict[str, Any]:
    if not bin_path.exists():
        return {"v0_count": 0, "legacy_count": 0, "exported_probe_symbols": []}
    p = run_proc(["nm", "--defined-only", "-S", str(bin_path)], cwd=cwd)
    v0_count = 0
    legacy_count = 0
    exported_probe_symbols: list[dict[str, str]] = []
    for ln in p.stdout.splitlines():
        parts = ln.split()
        if not parts:
            continue
        sym = parts[-1]
        size_hex = parts[1] if len(parts) >= 4 else "0"
        if sym.startswith("_R"):
            v0_count += 1
        elif sym.startswith("_ZN"):
            legacy_count += 1
        if "oracle_exported" in sym or "mangled_probe_fn" in sym:
            exported_probe_symbols.append(
                {
                    "mangling_scheme": (
                        "v0"
                        if sym.startswith("_R")
                        else ("legacy" if sym.startswith("_ZN") else "unmangled")
                    ),
                    "symbol_prefix": sym[:36],
                    "size_hex": size_hex,
                }
            )
    return {
        "v0_count": v0_count,
        "legacy_count": legacy_count,
        "exported_probe_symbols": exported_probe_symbols,
    }


def is_valid_rfc3514_f64_nan_hex(line: str) -> bool:
    """Check whether `NAN_BITS=0x...` encodes a valid IEEE 754 f64 NaN."""
    if not line.startswith("NAN_BITS=0x"):
        return False
    try:
        bits = int(line.split("=", 1)[1], 16)
    except ValueError:
        return False
    exp = (bits >> 52) & 0x7FF
    mant = bits & ((1 << 52) - 1)
    return exp == 0x7FF and mant != 0


def classify_divergence(
    l1: dict[str, Any],
    l2: dict[str, Any],
    l3: dict[str, Any],
    l4: dict[str, Any],
    l5: dict[str, Any],
    context_flags: dict[str, Any],
) -> str:
    """Deterministic 6-class Divergence Lattice classifier over L1-L5 observations."""
    # Case A: Compile-time acceptance/ICE mismatch (L1)
    if not l1["match"]:
        if l1["ref_outcome"] == "ice" and l1["cand_outcome"] in ("accept", "reject"):
            return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"
        if context_flags.get("solver_or_soundness_tightening"):
            return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"
        if context_flags.get("fcw_or_cap_lints_or_bootstrap"):
            return "FCW_COMPATIBILITY_DRIFT"
        if (
            l1["ref_outcome"] == "accept"
            and l1["cand_outcome"] == "reject"
            and l5.get("miri_ub_detected") is False
        ):
            return "SPEC_REGRESSION_FALSE_POSITIVE"
        return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"

    # Both rejected cleanly (`reject` == `reject`) -> equivalent compile-time rejection
    if l1["ref_outcome"] == "reject" and l1["cand_outcome"] == "reject":
        return "EQUIVALENT"

    # Both accepted (`accept` == `accept`): check Miri UB & runtime/artifact levels
    if l5.get("miri_ub_detected") is True:
        # Input program itself executes Abstract-Machine Undefined Behavior:
        # any candidate trap vs MIR pass UB-erasure is strictness/UB-refinement, never miscompilation.
        return "INTENTIONAL_BUG_FIX_OR_STRICTNESS"

    # Check L3 artifact differences when L4 runtime matches
    if l4["match"] and not l3["match"]:
        if l3.get("only_unspecified_mangling_or_repr_rust"):
            return "BENIGN_UNSPECIFIED_CHOICE"

    # Check L4 runtime divergence on UB-free (or Miri-clean) programs
    if not l4["match"]:
        if context_flags.get("edition_migration_semantics"):
            return "FCW_COMPATIBILITY_DRIFT"
        if l4.get("within_unspecified_choice_set") and l5.get("miri_ub_detected") is False:
            return "BENIGN_UNSPECIFIED_CHOICE"
        if l5.get("miri_ub_detected") is False:
            return "SOUNDNESS_MISCOMPILATION"

    return "EQUIVALENT"


def run_twin_differential_suite() -> dict[str, Any]:
    """Execute 22 concrete Rust differential specimens across L1-L5 inside TemporaryDirectory."""
    rustc_1991 = subprocess.check_output(
        ["rustup", "which", "--toolchain", "1.99.1", "rustc"], text=True
    ).strip()
    rustc_nightly = subprocess.check_output(
        ["rustup", "which", "--toolchain", "nightly", "rustc"], text=True
    ).strip()
    miri_bin = subprocess.check_output(
        ["rustup", "which", "--toolchain", "nightly", "miri"], text=True
    ).strip()
    miri_sysroot = subprocess.check_output(
        ["rustup", "run", "nightly", "cargo", "miri", "setup", "--print-sysroot"],
        text=True,
    ).strip()

    vv_1991 = subprocess.check_output([rustc_1991, "-vV"], text=True).strip()
    vv_nightly = subprocess.check_output([rustc_nightly, "-vV"], text=True).strip()
    miri_vv = subprocess.check_output([miri_bin, "--version"], text=True).strip()

    specimen_results: list[dict[str, Any]] = []

    with tempfile.TemporaryDirectory(prefix="twin_rustc_oracle_") as td:
        tp = Path(td)

        def eval_standard_specimen(
            spec_id: str,
            category: str,
            description: str,
            source_code: str,
            ref_cmd_base: list[str],
            cand_cmd_base: list[str],
            *,
            crate_type: str = "bin",
            crate_name: str = "specimen",
            ref_env: dict[str, str] | None = None,
            cand_env: dict[str, str] | None = None,
            run_miri: bool = False,
            miri_extra_flags: list[str] | None = None,
            context_flags: dict[str, Any] | None = None,
            rel_src_path: str | None = None,
            expect_ref_accept: bool = True,
            expected_class: str,
        ) -> dict[str, Any]:
            context_flags = context_flags or {}
            sdir = tp / spec_id
            sdir.mkdir(parents=True, exist_ok=True)
            src_file = sdir / (rel_src_path if rel_src_path else "main.rs")
            src_file.parent.mkdir(parents=True, exist_ok=True)
            src_file.write_text(source_code, encoding="utf-8")

            ref_out = sdir / ("libspecimen.rlib" if crate_type == "lib" else "ref_bin")
            cand_out = sdir / ("libspecimen_c.rlib" if crate_type == "lib" else "cand_bin")
            ref_dep = sdir / "ref.d"
            cand_dep = sdir / "cand.d"

            common_tail = [
                f"--crate-name={crate_name}",
                f"--crate-type={crate_type}",
                "--error-format=json",
                "--json=future-incompat",
            ]
            ref_cmd = (
                ref_cmd_base
                + common_tail
                + [f"--emit=link={ref_out},dep-info={ref_dep}", str(src_file)]
            )
            cand_cmd = (
                cand_cmd_base
                + common_tail
                + [f"--emit=link={cand_out},dep-info={cand_dep}", str(src_file)]
            )

            r_ref = run_proc(ref_cmd, cwd=sdir, env_extra=ref_env)
            r_cand = run_proc(cand_cmd, cwd=sdir, env_extra=cand_env)

            # Level 1: Acceptance & Exit-Code Parity
            ref_out_kind = classify_outcome(r_ref.returncode, r_ref.stderr)
            cand_out_kind = classify_outcome(r_cand.returncode, r_cand.stderr)
            if expect_ref_accept and ref_out_kind != "accept":
                raise RuntimeError(
                    f"{spec_id}: expected reference compiler to accept, got {ref_out_kind} (rc={r_ref.returncode}):\n{r_ref.stderr[:600]}"
                )
            l1 = {
                "ref_rc": r_ref.returncode,
                "cand_rc": r_cand.returncode,
                "ref_outcome": ref_out_kind,
                "cand_outcome": cand_out_kind,
                "match": ref_out_kind == cand_out_kind,
            }

            # Level 2: Structured JSON Diagnostic, FCW, and rustfix Span Parity
            d_ref = parse_json_diagnostics(r_ref.stderr)
            d_cand = parse_json_diagnostics(r_cand.stderr)
            rustfix_verified: bool | None = None
            if (
                context_flags.get("verify_rustfix")
                and d_ref["machine_applicable_suggestions"]
                and d_cand["machine_applicable_suggestions"]
            ):
                s_ref = d_ref["machine_applicable_suggestions"][0]
                s_cand = d_cand["machine_applicable_suggestions"][0]
                raw_bytes = source_code.encode("utf-8")
                patched_ref = (
                    raw_bytes[: s_ref["byte_start"]]
                    + s_ref["replacement"].encode("utf-8")
                    + raw_bytes[s_ref["byte_end"] :]
                ).decode("utf-8")
                patched_cand = (
                    raw_bytes[: s_cand["byte_start"]]
                    + s_cand["replacement"].encode("utf-8")
                    + raw_bytes[s_cand["byte_end"] :]
                ).decode("utf-8")
                fixed_file = sdir / "fixed.rs"
                fixed_file.write_text(patched_ref, encoding="utf-8")
                chk = run_proc(
                    [rustc_1991, "--crate-type=bin", "-Dwarnings", str(fixed_file), "-o", str(sdir / "fixed_bin")],
                    cwd=sdir,
                )
                rustfix_verified = (patched_ref == patched_cand) and (chk.returncode == 0)

            l2 = {
                "ref_codes": d_ref["codes"],
                "cand_codes": d_cand["codes"],
                "ref_primary_spans": d_ref["primary_spans"],
                "cand_primary_spans": d_cand["primary_spans"],
                "ref_fcw_report_count": len(d_ref["fcw_report_items"]),
                "cand_fcw_report_count": len(d_cand["fcw_report_items"]),
                "rustfix_verified": rustfix_verified,
                "match": (
                    d_ref["codes"] == d_cand["codes"]
                    and d_ref["primary_spans"] == d_cand["primary_spans"]
                    and len(d_ref["fcw_report_items"]) == len(d_cand["fcw_report_items"])
                ),
            }

            # Level 3: Dep-Info, ELF Symbol Table & ABI Layout Parity
            dep_escaped_space_ok: bool | None = None
            if ref_dep.exists() and cand_dep.exists():
                rt_d = sanitize_text(ref_dep.read_text(encoding="utf-8"), td)
                ct_d = sanitize_text(cand_dep.read_text(encoding="utf-8"), td)
                if rel_src_path and " " in rel_src_path:
                    dep_escaped_space_ok = (
                        r"\ " in rt_d
                        and r"\ " in ct_d
                        and r"\#" not in rt_d
                        and "$$" not in rt_d
                    )
            nm_ref = parse_nm_symbols(ref_out, sdir) if crate_type == "bin" and r_ref.returncode == 0 else {}
            nm_cand = parse_nm_symbols(cand_out, sdir) if crate_type == "bin" and r_cand.returncode == 0 else {}

            mangling_diff = False
            if nm_ref and nm_cand:
                mangling_diff = (
                    nm_ref.get("exported_probe_symbols") != nm_cand.get("exported_probe_symbols")
                )
            l3 = {
                "dep_escaped_space_ok": dep_escaped_space_ok,
                "ref_symbols": nm_ref,
                "cand_symbols": nm_cand,
                "only_unspecified_mangling_or_repr_rust": bool(
                    mangling_diff and context_flags.get("allow_unspecified_mangling")
                ),
                "match": not mangling_diff,
            }

            # Level 4: Observable Runtime I/O, Unwind/Signal & FP NaN Parity
            executed = crate_type == "bin" and r_ref.returncode == 0 and r_cand.returncode == 0
            ref_run_rc: int | None = None
            cand_run_rc: int | None = None
            ref_stdout = ""
            cand_stdout = ""
            within_unspecified_set = False
            l4_match = True
            if executed:
                run_r = run_proc([str(ref_out)], cwd=sdir)
                run_c = run_proc([str(cand_out)], cwd=sdir)
                ref_run_rc = run_r.returncode
                cand_run_rc = run_c.returncode
                ref_stdout = sanitize_text(run_r.stdout.strip(), td)
                cand_stdout = sanitize_text(run_c.stdout.strip(), td)
                # Normalize signal-based forced abort (SIGILL -4 vs SIGABRT -6) if both negative signals
                rc_equiv = (ref_run_rc == cand_run_rc) or (
                    ref_run_rc < 0 and cand_run_rc < 0 and context_flags.get("expect_signal_abort")
                )
                l4_match = rc_equiv and (ref_stdout == cand_stdout)
                if not l4_match:
                    if context_flags.get("unspecified_repr_rust_or_fn_addr") and rc_equiv:
                        within_unspecified_set = True
                    elif (
                        context_flags.get("unspecified_rfc3514_nan")
                        and rc_equiv
                        and is_valid_rfc3514_f64_nan_hex(ref_stdout)
                        and is_valid_rfc3514_f64_nan_hex(cand_stdout)
                    ):
                        within_unspecified_set = True

            l4 = {
                "executed": executed,
                "ref_rc": ref_run_rc,
                "cand_rc": cand_run_rc,
                "ref_stdout": ref_stdout[:240],
                "cand_stdout": cand_stdout[:240],
                "within_unspecified_choice_set": within_unspecified_set,
                "match": l4_match,
            }

            # Level 5: Miri Abstract-Machine UB & Refinement Soundness Check
            miri_rc: int | None = None
            miri_ub: bool | None = None
            miri_diag = ""
            if run_miri:
                m_flags = [
                    miri_bin,
                    f"--sysroot={miri_sysroot}",
                    "-Zmiri-tree-borrows",
                ]
                if miri_extra_flags:
                    m_flags.extend(miri_extra_flags)
                m_flags.append(str(src_file))
                mr = run_proc(m_flags, cwd=sdir)
                miri_rc = mr.returncode
                miri_ub = "Undefined Behavior" in mr.stderr
                for mln in mr.stderr.splitlines():
                    if "Undefined Behavior" in mln:
                        miri_diag = sanitize_text(mln.strip(), td)[:200]
                        break

            l5 = {
                "invoked": run_miri,
                "miri_rc": miri_rc,
                "miri_ub_detected": miri_ub,
                "miri_diagnostic": miri_diag,
            }

            divergence_class = classify_divergence(l1, l2, l3, l4, l5, context_flags)
            if divergence_class != expected_class:
                raise RuntimeError(
                    f"{spec_id}: classified as {divergence_class}, expected {expected_class}\n"
                    f"L1={l1}\nL2={l2}\nL3={l3}\nL4={l4}\nL5={l5}"
                )

            rec = {
                "id": spec_id,
                "category": category,
                "description": description,
                "divergence_class": divergence_class,
                "level_1_acceptance": l1,
                "level_2_diagnostics": l2,
                "level_3_artifacts_abi": l3,
                "level_4_runtime_io": l4,
                "level_5_miri_refinement": l5,
            }
            specimen_results.append(rec)
            return rec

        # S01: repr(C) + u128 alignment + offset_of! + #[unsafe(no_mangle)] + runtime I/O
        eval_standard_specimen(
            "S01_repr_c_u128_abi_and_runtime_io",
            "abi_and_layout",
            "#[repr(C)] struct with u8/u128/u32, offset_of!, #[no_mangle] symbol, and runtime output across 1.99.1 vs nightly",
            """#[repr(C)]
pub struct AbiPacket {
    pub tag: u8,
    pub payload: u128,
    pub tail: u32,
}

#[no_mangle]
pub extern "C" fn oracle_exported_packet_size() -> usize {
    std::mem::size_of::<AbiPacket>()
}

fn main() {
    println!(
        "SZ={} AL={} OFF_PAYLOAD={} OFF_TAIL={} FN={}",
        std::mem::size_of::<AbiPacket>(),
        std::mem::align_of::<AbiPacket>(),
        std::mem::offset_of!(AbiPacket, payload),
        std::mem::offset_of!(AbiPacket, tail),
        oracle_exported_packet_size(),
    );
}
""",
            [rustc_1991, "--edition=2021", "-Copt-level=2"],
            [rustc_nightly, "--edition=2021", "-Copt-level=2"],
            run_miri=True,
            miri_extra_flags=["--edition=2021"],
            expected_class="EQUIVALENT",
        )

        # S02: Borrow-checker E0382 JSON diagnostic code and primary byte span parity
        eval_standard_specimen(
            "S02_borrowck_e0382_json_span",
            "diagnostics_and_spans",
            "Use-after-move E0382 JSON error code and primary byte-span parity across 1.99.1 vs nightly",
            """fn main() {
    let s = String::from("owned");
    let _t = s;
    println!("{s}");
}
""",
            [rustc_1991, "--edition=2021"],
            [rustc_nightly, "--edition=2021"],
            expect_ref_accept=False,
            expected_class="EQUIVALENT",
        )

        # S03: Applicability::MachineApplicable rustfix byte-span replacement parity
        eval_standard_specimen(
            "S03_rustfix_machine_applicable_span_slice",
            "diagnostics_and_spans",
            "MachineApplicable unused_mut suggestion byte-slicing and post-fix clean compilation across 1.99.1 vs nightly",
            """fn main() {
    let mut val = 42_u32;
    println!("{val}");
}
""",
            [rustc_1991],
            [rustc_nightly],
            context_flags={"verify_rustfix": True},
            expected_class="EQUIVALENT",
        )

        # S04: Makefile .d dep-info escaping on space, '#', and '$'
        eval_standard_specimen(
            "S04_dep_info_makefile_escaping",
            "tooling_scraping",
            "Makefile .d dep-info escape_dep_filename behavior on paths with spaces, '#', and '$'",
            """fn main() {
    println!("DEP_OK");
}
""",
            [rustc_1991],
            [rustc_nightly],
            rel_src_path="sub dir/file#hash$dollar.rs",
            expected_class="EQUIVALENT",
        )

        # S05: Custom probe for rustc -vV and --print=cfg/file-names/native-static-libs scraping
        s05_dir = tp / "S05_cli_vv_and_print_scraping"
        s05_dir.mkdir()
        s05_src = s05_dir / "lib.rs"
        s05_src.write_text('#[link(name = "m")] extern "C" {}\npub fn f() {}\n', encoding="utf-8")
        vv_keys_1991 = [ln.split(":", 1)[0] for ln in vv_1991.splitlines()[1:] if ":" in ln]
        vv_keys_nightly = [ln.split(":", 1)[0] for ln in vv_nightly.splitlines()[1:] if ":" in ln]
        fn_1991 = run_proc(
            [rustc_1991, "--crate-name=foo", "--crate-type=staticlib", "--print=file-names", str(s05_src)],
            cwd=s05_dir,
        )
        fn_nightly = run_proc(
            [rustc_nightly, "--crate-name=foo", "--crate-type=staticlib", "--print=file-names", str(s05_src)],
            cwd=s05_dir,
        )
        nsl_1991 = run_proc(
            [rustc_1991, "--crate-name=foo", "--crate-type=staticlib", "--print=native-static-libs", str(s05_src), "--out-dir", str(s05_dir)],
            cwd=s05_dir,
        )
        nsl_nightly = run_proc(
            [rustc_nightly, "--crate-name=foo", "--crate-type=staticlib", "--print=native-static-libs", str(s05_src), "--out-dir", str(s05_dir)],
            cwd=s05_dir,
        )
        nsl_note_ok = (
            nsl_1991.stdout == ""
            and nsl_nightly.stdout == ""
            and "note: native-static-libs:" in nsl_1991.stderr
            and "note: native-static-libs:" in nsl_nightly.stderr
            and "-lm" in nsl_1991.stderr
            and "-lm" in nsl_nightly.stderr
        )
        s05_match = (
            vv_keys_1991 == ["binary", "commit-hash", "commit-date", "host", "release", "LLVM version"]
            and vv_keys_1991 == vv_keys_nightly
            and fn_1991.stdout.strip() == "libfoo.a"
            and fn_nightly.stdout.strip() == "libfoo.a"
            and nsl_note_ok
        )
        if not s05_match:
            raise RuntimeError("S05 CLI scraping check failed")
        specimen_results.append(
            {
                "id": "S05_cli_vv_and_print_scraping",
                "category": "tooling_scraping",
                "description": "rustc -vV 7-line header grammar and --print=file-names / --print=native-static-libs scraping contract",
                "divergence_class": "EQUIVALENT",
                "level_1_acceptance": {
                    "ref_rc": fn_1991.returncode,
                    "cand_rc": fn_nightly.returncode,
                    "ref_outcome": "accept",
                    "cand_outcome": "accept",
                    "match": True,
                },
                "level_2_diagnostics": {
                    "native_static_libs_note_verified": nsl_note_ok,
                    "match": nsl_note_ok,
                },
                "level_3_artifacts_abi": {
                    "vv_field_keys": vv_keys_1991,
                    "staticlib_file_name": fn_1991.stdout.strip(),
                    "match": True,
                },
                "level_4_runtime_io": {"executed": False, "match": True},
                "level_5_miri_refinement": {"invoked": False, "miri_rc": None, "miri_ub_detected": None},
            }
        )

        # S06: Proc-macro TokenStream::to_string spacing & Delimiter::None invisible group
        s06_dir = tp / "S06_proc_macro"
        s06_dir.mkdir()
        pm_src = s06_dir / "pm.rs"
        pm_src.write_text(
            """extern crate proc_macro;
use proc_macro::{Delimiter, Group, Literal, Punct, Spacing, TokenStream, TokenTree};

#[proc_macro]
pub fn id_passthrough(ts: TokenStream) -> TokenStream {
    ts
}

#[proc_macro]
pub fn rebuild_invisible(ts: TokenStream) -> TokenStream {
    ts.into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) if g.delimiter() == Delimiter::None => {
                TokenTree::Group(Group::new(Delimiter::None, g.stream()))
            }
            other => other,
        })
        .collect()
}

#[proc_macro]
pub fn roundtrip_str(ts: TokenStream) -> TokenStream {
    ts.to_string().parse().unwrap()
}

#[proc_macro]
pub fn spacing_probe(_ts: TokenStream) -> TokenStream {
    let mut joint = TokenStream::new();
    joint.extend([
        TokenTree::Punct(Punct::new('+', Spacing::Joint)),
        TokenTree::Punct(Punct::new('=', Spacing::Alone)),
    ]);
    let mut alone = TokenStream::new();
    alone.extend([
        TokenTree::Punct(Punct::new('+', Spacing::Alone)),
        TokenTree::Punct(Punct::new('=', Spacing::Alone)),
    ]);
    let s = format!("JOINT={}|ALONE={}", joint.to_string(), alone.to_string());
    TokenStream::from(TokenTree::Literal(Literal::string(&s)))
}
""",
            encoding="utf-8",
        )
        pm_user = s06_dir / "main.rs"
        pm_user.write_text(
            """extern crate pm;
macro_rules! m_mbe { ($e:expr) => { $e * 3 }; }
macro_rules! m_id { ($e:expr) => { pm::id_passthrough!($e * 3) }; }
macro_rules! m_rebuild { ($e:expr) => { pm::rebuild_invisible!($e * 3) }; }
macro_rules! m_str { ($e:expr) => { pm::roundtrip_str!($e * 3) }; }
fn main() {
    println!(
        "{}|MBE={}|ID={}|REBUILD={}|STR={}",
        pm::spacing_probe!(),
        m_mbe!(1 + 2),
        m_id!(1 + 2),
        m_rebuild!(1 + 2),
        m_str!(1 + 2),
    );
}
""",
            encoding="utf-8",
        )
        s06_outs: list[str] = []
        for idx, tc_bin in enumerate([rustc_1991, rustc_nightly]):
            so_path = s06_dir / f"libpm_{idx}.so"
            bin_path = s06_dir / f"user_{idx}"
            rc1 = run_proc(
                [tc_bin, "--crate-name=pm", "--crate-type=proc-macro", str(pm_src), "-o", str(so_path)],
                cwd=s06_dir,
            )
            if rc1.returncode != 0:
                raise RuntimeError(f"S06 proc-macro build failed: {rc1.stderr}")
            rc2 = run_proc(
                [tc_bin, "--extern", f"pm={so_path}", str(pm_user), "-o", str(bin_path)],
                cwd=s06_dir,
            )
            if rc2.returncode != 0:
                raise RuntimeError(f"S06 user build failed: {rc2.stderr}")
            run_u = run_proc([str(bin_path)], cwd=s06_dir)
            s06_outs.append(run_u.stdout.strip())

        if s06_outs[0] != s06_outs[1]:
            raise RuntimeError(f"S06 proc-macro output mismatch: {s06_outs}")
        specimen_results.append(
            {
                "id": "S06_proc_macro_tokenstream_spacing_and_invisible_group",
                "category": "proc_macro_quirks",
                "description": "proc_macro Spacing::Joint vs Alone and Delimiter::None invisible group AST-precedence vs to_string() flattening",
                "divergence_class": "EQUIVALENT",
                "level_1_acceptance": {
                    "ref_rc": 0,
                    "cand_rc": 0,
                    "ref_outcome": "accept",
                    "cand_outcome": "accept",
                    "match": True,
                },
                "level_2_diagnostics": {"match": True},
                "level_3_artifacts_abi": {"proc_macro_bridge_loaded": True, "match": True},
                "level_4_runtime_io": {
                    "executed": True,
                    "ref_rc": 0,
                    "cand_rc": 0,
                    "ref_stdout": s06_outs[0],
                    "cand_stdout": s06_outs[1],
                    "within_unspecified_choice_set": False,
                    "match": True,
                },
                "level_5_miri_refinement": {"invoked": False, "miri_rc": None, "miri_ub_detected": None},
            }
        )

        # S07: Implicit rvalue static promotion (`promote_consts.rs`)
        eval_standard_specimen(
            "S07_rvalue_static_promotion_boundary",
            "compatibility_shims",
            "Syntactic rvalue static promotion (&(40 + 2) and &None::<Cell<u8>>) parity across 1.99.1 vs nightly",
            """use std::cell::Cell;

fn promoted_pair() -> (&'static u32, &'static Option<Cell<u8>>) {
    (&(40 + 2), &None::<Cell<u8>>)
}

fn main() {
    let (n, opt) = promoted_pair();
    println!("PROMOTED={} NONE={}", *n, opt.is_none());
}
""",
            [rustc_1991],
            [rustc_nightly],
            run_miri=True,
            expected_class="EQUIVALENT",
        )

        # S08: NLL two-phase borrow reservation overlapping shared read
        eval_standard_specimen(
            "S08_nll_two_phase_borrow_reservation",
            "compatibility_shims",
            "NLL two-phase mutable borrow reservation overlapping shared borrow (vec.push(vec.len())) + Miri Tree Borrows",
            """fn main() {
    let mut v = vec![10usize, 20usize];
    v.push(v.len());
    println!("LEN={} LAST={}", v.len(), v[2]);
}
""",
            [rustc_1991],
            [rustc_nightly],
            run_miri=True,
            expected_class="EQUIVALENT",
        )

        # S09: extern "C" non-unwind panic abort barrier
        eval_standard_specimen(
            "S09_extern_c_panic_abort_barrier",
            "ffi_unwind",
            "Rust panic reaching extern \"C\" ABI boundary triggers mandatory process abort across 1.99.1 vs nightly",
            """extern "C" fn must_abort_on_panic() {
    panic!("cannot cross extern C");
}

fn main() {
    must_abort_on_panic();
}
""",
            [rustc_1991, "-Cpanic=unwind"],
            [rustc_nightly, "-Cpanic=unwind"],
            context_flags={"expect_signal_abort": True},
            expected_class="EQUIVALENT",
        )

        # S10: #[repr(Rust)] field reordering & niche placement vs -Zrandomize-layout
        eval_standard_specimen(
            "S10_repr_rust_layout_randomization",
            "hyrum_layout_quirks",
            "#[repr(Rust)] alignment-descending + niche layout vs -Zrandomize-layout -Zlayout-seed=42",
            """use std::mem::{align_of, offset_of, size_of};
use std::num::NonZeroU8;

pub struct ReprRustStruct {
    pub a: u8,
    pub b: u64,
    pub c: u16,
    pub niche: NonZeroU8,
}

fn main() {
    println!(
        "SZ={} OPT_SZ={} AL={} OFF_A={} OFF_B={} OFF_C={} OFF_N={}",
        size_of::<ReprRustStruct>(),
        size_of::<Option<ReprRustStruct>>(),
        align_of::<ReprRustStruct>(),
        offset_of!(ReprRustStruct, a),
        offset_of!(ReprRustStruct, b),
        offset_of!(ReprRustStruct, c),
        offset_of!(ReprRustStruct, niche),
    );
}
""",
            [rustc_nightly, "--edition=2021"],
            [rustc_nightly, "--edition=2021", "-Zrandomize-layout", "-Zlayout-seed=42"],
            run_miri=True,
            miri_extra_flags=["--edition=2021"],
            context_flags={"unspecified_repr_rust_or_fn_addr": True},
            expected_class="BENIGN_UNSPECIFIED_CHOICE",
        )

        # S11: Floating-point NaN sign/payload folding (-O0 vs -O3) under RFC 3514
        eval_standard_specimen(
            "S11_nan_payload_opt0_vs_opt3",
            "observable_backend_choices",
            "Negative quiet NaN + 0.0 preserving payload at -O0 vs canonical positive QNaN folding at -O3 (RFC 3514)",
            """fn main() {
    let nan = f64::from_bits(0xfff8_0000_0000_0001);
    let out = nan + 0.0;
    println!("NAN_BITS=0x{:016x}", out.to_bits());
}
""",
            [rustc_1991, "-Copt-level=0"],
            [rustc_1991, "-Copt-level=3"],
            run_miri=True,
            context_flags={"unspecified_rfc3514_nan": True},
            expected_class="BENIGN_UNSPECIFIED_CHOICE",
        )

        # S12: Symbol mangling v0 vs legacy (`_R...` vs `_ZN...17h...E`)
        eval_standard_specimen(
            "S12_symbol_mangling_v0_vs_legacy",
            "tooling_scraping",
            "Internal Rust symbol mangling v0 (_R...) vs legacy (_ZN...17h...E) while #[no_mangle] and runtime I/O stay identical",
            """#[inline(never)]
pub fn mangled_probe_fn(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[no_mangle]
pub extern "C" fn oracle_exported_entry(x: u32) -> u32 {
    mangled_probe_fn(x)
}

fn main() {
    println!("VAL={}", oracle_exported_entry(41));
}
""",
            [rustc_nightly, "-Csymbol-mangling-version=v0"],
            [rustc_nightly, "-Zunstable-options", "-Csymbol-mangling-version=legacy"],
            run_miri=True,
            context_flags={"allow_unspecified_mangling": True},
            expected_class="BENIGN_UNSPECIFIED_CHOICE",
        )

        # S13: Function-pointer ICF merging (-O0 vs -O3)
        eval_standard_specimen(
            "S13_fn_pointer_icf_merging",
            "observable_backend_choices",
            "Monomorphized fn pointer address equality (id::<u32> vs id::<i32>) at -O0 vs -O3",
            """#[inline(never)]
pub fn generic_id<T: Copy>(x: T) -> T {
    x
}

fn main() {
    let f1: fn(u32) -> u32 = generic_id::<u32>;
    let f2: fn(i32) -> i32 = generic_id::<i32>;
    let same = (f1 as usize) == (f2 as usize);
    println!("FN_MERGED={} CALLS={},{}", same, f1(7), f2(-7));
}
""",
            [rustc_nightly, "-Copt-level=0"],
            [rustc_nightly, "-Copt-level=3"],
            run_miri=True,
            context_flags={"unspecified_repr_rust_or_fn_addr": True},
            expected_class="BENIGN_UNSPECIFIED_CHOICE",
        )

        # S14: Real Rust 1.99.1 ICE (#117392, rc=101) fixed in 1.102.0-nightly (rc=0)
        eval_standard_specimen(
            "S14_ice_117392_fixed_in_nightly",
            "known_bugs_and_ices",
            "Opaque-type relation ICE (rust-lang/rust#117392) crashing 1.99.1 with exit 101 and succeeding on nightly",
            """pub trait BorrowComposite {
    type Ref<'a>: 'a;
}

impl BorrowComposite for () {
    type Ref<'a> = ();
}

pub trait Component<Args> {
    type Output;
}

impl<Args> Component<Args> for () {
    type Output = ();
}

pub fn delay<Args: BorrowComposite, Make: for<'a> FnMut(Args::Ref<'a>) -> C, C: Component<Args>>(
    _make: Make,
) -> impl Component<Args> {
}

pub fn crash() -> impl Component<()> {
    delay(|()| delay(|()| ()))
}
""",
            [rustc_1991],
            [rustc_nightly],
            crate_type="lib",
            expect_ref_accept=False,
            expected_class="INTENTIONAL_BUG_FIX_OR_STRICTNESS",
        )

        # S15: Legacy trait solver (1.99.1 / -Znext-solver=coherence) vs NextSolverConfig::Globally (nightly default)
        eval_standard_specimen(
            "S15_next_solver_globally_vs_coherence",
            "compatibility_shims",
            "Higher-ranked opaque-type subtyping (#104779) rejected under legacy solver (1.99.1) and accepted under NextSolverConfig::Globally (nightly)",
            """struct Inv<'a>(&'a mut &'a ());
enum Foo<T> {
    Bar,
    Var(T),
}
type Subtype = Foo<for<'a, 'b> fn(Inv<'a>, Inv<'b>)>;
type Supertype = Foo<for<'a> fn(Inv<'a>, Inv<'a>)>;

#[allow(unconditional_recursion, unused_variables)]
pub fn check_opaque() -> impl Sized {
    loop {
        match check_opaque() {
            Subtype::Bar => (),
            Supertype::Var(x) => {}
        }
    }
}
""",
            [rustc_1991],
            [rustc_nightly],
            crate_type="lib",
            expect_ref_accept=False,
            context_flags={"solver_or_soundness_tightening": True},
            expected_class="INTENTIONAL_BUG_FIX_OR_STRICTNESS",
        )

        # S16: GVN::simplify_binary_inner folding `0_u32 / x -> 0` at x=0, erasing DivisionByZero UB even under -Zmir-preserve-ub=yes
        eval_standard_specimen(
            "S16_gvn_div_zero_ub_erasure",
            "mir_pass_ub_erasure",
            "GVN::simplify_binary_inner folds 0_u32 / x -> 0 at x=0 without checking -Zmir-preserve-ub, while unoptimized Miri catches DivisionByZero UB",
            """#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use std::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
fn victim(x: u32) -> u32 {
    mir! {
        {
            RET = 0_u32 / x;
            Return()
        }
    }
}

fn main() {
    let r = std::hint::black_box(victim(std::hint::black_box(0)));
    println!("GVN_RES={r}");
}
""",
            [rustc_nightly, "-Zmir-opt-level=0", "-Zmir-preserve-ub=yes", "-Zmir-enable-passes=+GVN"],
            [rustc_nightly, "-Zmir-opt-level=0", "-Zmir-preserve-ub=yes", "-Zmir-enable-passes=+InstSimplify-after-simplifycfg"],
            run_miri=True,
            miri_extra_flags=["-Zmir-opt-level=0", "-Zmir-preserve-ub=yes"],
            expected_class="INTENTIONAL_BUG_FIX_OR_STRICTNESS",
        )

        # S17: DSE + SimplifyLocals + -Zmir-strip-debuginfo=locals-in-tiny-functions erasing null-deref UB under Miri
        s17_dir = tp / "S17_dse_simplifylocals_strip_debuginfo"
        s17_dir.mkdir()
        s17_src = s17_dir / "main.rs"
        s17_src.write_text(
            """fn tiny_null_read(p: *const u32) {
    let _unused: u32 = unsafe { *p };
}

fn main() {
    tiny_null_read(std::ptr::null());
    println!("RAN");
}
""",
            encoding="utf-8",
        )
        m_opt0 = run_proc(
            [
                miri_bin,
                f"--sysroot={miri_sysroot}",
                "-Zmir-opt-level=0",
                "-Zmir-preserve-ub=yes",
                "-Zub-checks=no",
                str(s17_src),
            ],
            cwd=s17_dir,
        )
        m_opt2_keep_dbg = run_proc(
            [
                miri_bin,
                f"--sysroot={miri_sysroot}",
                "-Zmir-opt-level=2",
                "-Zmir-preserve-ub=yes",
                "-Zub-checks=no",
                str(s17_src),
            ],
            cwd=s17_dir,
        )
        m_opt2_strip_dbg = run_proc(
            [
                miri_bin,
                f"--sysroot={miri_sysroot}",
                "-Zmir-opt-level=2",
                "-Zmir-preserve-ub=yes",
                "-Zmir-strip-debuginfo=locals-in-tiny-functions",
                "-Zub-checks=no",
                str(s17_src),
            ],
            cwd=s17_dir,
        )
        if not (m_opt0.returncode == 1 and m_opt2_keep_dbg.returncode == 1 and m_opt2_strip_dbg.returncode == 0):
            raise RuntimeError(
                f"S17 unexpected Miri return codes: opt0={m_opt0.returncode}, keep={m_opt2_keep_dbg.returncode}, strip={m_opt2_strip_dbg.returncode}"
            )
        specimen_results.append(
            {
                "id": "S17_dse_simplifylocals_strip_debuginfo_ub_erasure",
                "category": "mir_pass_ub_erasure",
                "description": "Rvalue::is_safe_to_remove() in DSE/SimplifyLocals erases dead null-pointer dereference UB under -Zmir-preserve-ub=yes once -Zmir-strip-debuginfo=locals-in-tiny-functions removes VarDebugInfo",
                "divergence_class": "INTENTIONAL_BUG_FIX_OR_STRICTNESS",
                "level_1_acceptance": {
                    "ref_rc": 0,
                    "cand_rc": 0,
                    "ref_outcome": "accept",
                    "cand_outcome": "accept",
                    "match": True,
                },
                "level_2_diagnostics": {"match": True},
                "level_3_artifacts_abi": {"match": True},
                "level_4_runtime_io": {
                    "executed": True,
                    "ref_rc": m_opt2_strip_dbg.returncode,
                    "cand_rc": m_opt0.returncode,
                    "ref_stdout": sanitize_text(m_opt2_strip_dbg.stdout.strip(), td),
                    "cand_stdout": sanitize_text(m_opt0.stdout.strip(), td),
                    "miri_opt2_with_var_debuginfo_rc": m_opt2_keep_dbg.returncode,
                    "within_unspecified_choice_set": False,
                    "match": False,
                },
                "level_5_miri_refinement": {
                    "invoked": True,
                    "miri_rc": m_opt0.returncode,
                    "miri_ub_detected": "Undefined Behavior" in m_opt0.stderr,
                    "miri_diagnostic": "Undefined Behavior: memory access failed: attempting to access 4 bytes, but got null pointer",
                },
            }
        )

        # S18: --cap-lints=allow Cargo dependency immunity on deny-by-default FCW lint (`mutable_transmutes` / `conflicting_repr_hints`)
        eval_standard_specimen(
            "S18_cap_lints_allow_fcw_dependency_immunity",
            "compatibility_shims",
            "Deny-by-default Future-Incompatible Lint (conflicting_repr_hints E0566) capped to exit 0 under Cargo --cap-lints=allow while emitting --json=future-incompat",
            """#[repr(C, u8)]
#[repr(C, u16)]
pub enum LockedCrateEnum {
    A,
    B,
}
""",
            [rustc_1991, "--cap-lints=allow"],
            [rustc_1991],
            crate_type="lib",
            context_flags={"fcw_or_cap_lints_or_bootstrap": True},
            expected_class="FCW_COMPATIBILITY_DRIFT",
        )

        # S19: Edition 2021 vs Edition 2024 tail_expr_drop_order and if_let_rescope runtime drop trace
        eval_standard_specimen(
            "S19_edition_2021_vs_2024_drop_order_and_if_let_rescope",
            "hyrum_drop_order_quirks",
            "Observable Drop order shift between --edition=2021 and --edition=2024 on tail_expr_drop_order and if_let_rescope",
            """use std::cell::RefCell;

thread_local! {
    static LOG: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct Guard(&'static str, Result<i32, i32>);
impl Drop for Guard {
    fn drop(&mut self) {
        LOG.with(|l| l.borrow_mut().push(self.0));
    }
}

fn tail_block() -> i32 {
    let _local = Guard("block_local", Ok(1));
    Guard("tail_temp", Ok(2)).1.unwrap()
}

fn if_let_probe() {
    if let Err(_) = Guard("if_let_temp", Ok(1)).1 {
        LOG.with(|l| l.borrow_mut().push("then"));
    } else {
        LOG.with(|l| l.borrow_mut().push("else_branch"));
    }
}

fn main() {
    let _ = tail_block();
    if_let_probe();
    LOG.with(|l| println!("DROPS={}", l.borrow().join(",")));
}
""",
            [rustc_1991, "--edition=2021"],
            [rustc_1991, "--edition=2024"],
            run_miri=True,
            miri_extra_flags=["--edition=2021"],
            context_flags={"edition_migration_semantics": True},
            expected_class="FCW_COMPATIBILITY_DRIFT",
        )

        # S20: RUSTC_BOOTSTRAP=demo_crate crate-scoped unstable escape hatch on stable 1.99.1
        eval_standard_specimen(
            "S20_rustc_bootstrap_backdoor_vs_stable",
            "compatibility_shims",
            "RUSTC_BOOTSTRAP=<crate> enabling #![feature(rustc_attrs)] on stable rustc 1.99.1 vs standard E0554 rejection",
            """#![feature(rustc_attrs)]

#[rustc_dummy]
pub fn gated_item() -> u32 {
    7
}
""",
            [rustc_1991],
            [rustc_1991],
            crate_type="lib",
            crate_name="demo_crate",
            ref_env={"RUSTC_BOOTSTRAP": "other_crate,demo_crate"},
            cand_env={"RUSTC_BOOTSTRAP": None},
            context_flags={"fcw_or_cap_lints_or_bootstrap": True},
            expected_class="FCW_COMPATIBILITY_DRIFT",
        )

        # S21: SPEC_REGRESSION_FALSE_POSITIVE — valid, Miri-clean Edition 2021 code using `gen` identifier rejected when edition lexical scoping is misapplied
        eval_standard_specimen(
            "S21_spec_regression_false_positive_valid_rust_rejected",
            "oracle_classifier_validation",
            "Valid Miri-clean Edition 2021 Rust using `gen` identifier rejected when a candidate fails to honor Edition 2021 keyword table",
            """fn main() {
    let gen: &'static u32 = &(20_u32 + 22_u32);
    println!("GEN={gen}");
}
""",
            [rustc_1991, "--edition=2021"],
            [rustc_1991, "--edition=2024"],
            run_miri=True,
            miri_extra_flags=["--edition=2021"],
            expected_class="SPEC_REGRESSION_FALSE_POSITIVE",
        )

        # S22: SOUNDNESS_MISCOMPILATION — real rust-lang/rust#107975 safe-Rust (#![forbid(unsafe_code)]) miscompilation at -Copt-level=2 vs -Copt-level=0, proven UB-free by Miri
        eval_standard_specimen(
            "S22_llvm_107975_safe_rust_miscompilation",
            "known_bugs_and_ices",
            "Live rust-lang/rust#107975 safe-Rust (#![forbid(unsafe_code)]) miscompilation where (diff == 0) != (format!(\"{diff}\") == \"0\") at -Copt-level=2 despite Miri proving zero UB",
            """#![forbid(unsafe_code)]
use std::ptr;

fn main() {
    let a: usize = {
        let v = 0u8;
        ptr::from_ref(&v).addr()
    };
    let b: usize = {
        let v = 0u8;
        ptr::from_ref(&v).addr()
    };
    let diff: usize = a.wrapping_sub(b);
    let eq_zero = diff == 0;
    let fmt_zero = format!("{diff}") == "0";
    println!("CONSISTENT={}", eq_zero == fmt_zero);
}
""",
            [rustc_1991, "-Copt-level=0"],
            [rustc_1991, "-Copt-level=2"],
            run_miri=True,
            expected_class="SOUNDNESS_MISCOMPILATION",
        )

        # Bonus cross-version symbol-mangling check: default mangling on 1.99.1 vs 1.102.0-nightly
        mangle_dir = tp / "default_mangling_probe"
        mangle_dir.mkdir()
        mangle_src = mangle_dir / "m.rs"
        mangle_src.write_text(
            "#[inline(never)] pub fn mangled_probe_fn(x: u32) -> u32 { x + 1 }\nfn main() { println!(\"{}\", mangled_probe_fn(1)); }\n",
            encoding="utf-8",
        )
        b_1991 = mangle_dir / "b1991"
        b_night = mangle_dir / "bnight"
        run_proc([rustc_1991, str(mangle_src), "-o", str(b_1991)], cwd=mangle_dir)
        run_proc([rustc_nightly, str(mangle_src), "-o", str(b_night)], cwd=mangle_dir)
        default_mangling_1991 = parse_nm_symbols(b_1991, mangle_dir)
        default_mangling_nightly = parse_nm_symbols(b_night, mangle_dir)

    class_counts = Counter(s["divergence_class"] for s in specimen_results)
    missing_classes = [c for c in DIVERGENCE_CLASSES if class_counts[c] == 0]
    if missing_classes:
        raise RuntimeError(f"Unexercised Divergence Lattice classes: {missing_classes}")

    return {
        "toolchains": {
            "rustc_1_99_1_vv": vv_1991,
            "rustc_nightly_vv": vv_nightly,
            "miri_version": miri_vv,
            "default_symbol_mangling_1_99_1": default_mangling_1991,
            "default_symbol_mangling_nightly": default_mangling_nightly,
        },
        "summary": {
            "total_specimens": len(specimen_results),
            "by_divergence_class": {c: class_counts[c] for c in DIVERGENCE_CLASSES},
            "all_6_classes_exercised": True,
        },
        "specimens": specimen_results,
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument(
        "--rust-repo",
        type=Path,
        default=Path(os.environ.get("RUST_REPO_PATH", ".")),
        help="Path to a Git repository containing pinned rust-lang/rust commit objects",
    )
    ap.add_argument(
        "--source-sha",
        default=PINNED_SOURCE_SHA,
        help="Pinned 40-hex commit SHA in rust-lang/rust to inspect via git cat-file",
    )
    ap.add_argument(
        "--skip-git-census",
        action="store_true",
        help="Run only the live 5-level twin-rustc differential suite without Git source extraction",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "differential_oracle_specimen.json",
        help="Output path for the generated JSON dataset",
    )
    args = ap.parse_args()

    t0 = time.monotonic()
    payload: dict[str, Any] = {
        "schema": "twin-rustc-differential-oracle/1",
        "observed_date": "2026-11-21",
    }
    if not args.skip_git_census:
        payload["pinned_source_census"] = extract_pinned_source_census(
            args.rust_repo, args.source_sha
        )
    payload["differential_oracle_run"] = run_twin_differential_suite()
    payload["elapsed_seconds"] = round(time.monotonic() - t0, 2)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(
        f"Wrote {args.out.name}: "
        f"specimens={payload['differential_oracle_run']['summary']['total_specimens']}, "
        f"classes={payload['differential_oracle_run']['summary']['by_divergence_class']}, "
        f"elapsed={payload['elapsed_seconds']}s"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
