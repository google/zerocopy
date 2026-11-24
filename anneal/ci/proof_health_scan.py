#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Scan Anneal Lean proofs for hygiene, dead helpers, and burden telemetry.

Implements:
- `--check-hygiene`: Hard G1/G4 anti-golf gates (`<= 100` cols, `0` `*` in
  `simp` lemma lists, `0` `simp_all`, `0` AST evaluators in `simp` lemma lists,
  `0` `local macro` / `macro_rules`, `<= 2` tactic semicolons per line on
  target proofs, and the G1 spec-immutability gate on the change that merging
  `HEAD` into the base ref makes to `zerocopy/proofs/`).
- `--unused-private`: Post-campaign dead-helper mop-up detector for orphaned
  `private` declarations in Lean modules.
- `--telemetry`: Deterministic `anneal-perf-record/v1` `"proof_burden.*"` source
  and optional `.olean` / `Expr` DAG+tree / `kernel_replay_ms` extraction, plus
  Policy `D3` non-blocking review advisories (`tree_to_dag_ratio > 50`,
  `> 20` NB lines in `Proof.lean`, and `> 60` NB lines in `theory/` or
  `correspondence/`).
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys
import tempfile
from typing import Any

MAX_CODE_COLS = 100
MAX_SEMI_PER_LINE = 2
D3_PROOF_THM_NB_ADVISORY = 20
D3_PASS1_THM_NB_ADVISORY = 60
D3_TREE_TO_DAG_RATIO_ADVISORY = 50.0

FORBIDDEN_SIMP_EVALUATORS = (
    "MirTy.beq",
    "IntWidth.beq",
    "Place.beq",
    "evalStep",
    "evalRvalue",
    "evalTerminator",
    "writePlace",
)

DECL_HEADER_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|axiom|opaque|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
PRIVATE_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*private\s+(?:(?:noncomputable|partial|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
SIMP_ALL_RE = re.compile(r"\bsimp_all\b")
# Start of a `simp`-family tactic whose lemma list `_simp_lemma_lists` extracts.
SIMP_CALL_RE = re.compile(r"\b(?:simp|dsimp|simpa|simp_arith|dsimp_arith)\b[?!]?")
SIMP_OPTION_RE = re.compile(r"[+-][A-Za-z_][A-Za-z0-9_.]*|only\b")
LOCAL_MACRO_RE = re.compile(r"\blocal\s+macro\b|\bmacro_rules\b")
IDENT_TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

PROOF_BURDEN_DESCRIPTORS: dict[str, dict[str, Any]] = {
    "proof_burden.zerocopy_suite.hand_proof_loc": {
        "label": "zerocopy/proofs hand Proof.lean LOC (NB)",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.loc",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.scaffold_loc": {
        "label": "zerocopy/proofs AutoScaffold.lean LOC (NB)",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.loc",
        "unit": "count",
        "direction": "informational",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.spec_loc": {
        "label": "zerocopy/proofs Spec.lean LOC (NB)",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.loc",
        "unit": "count",
        "direction": "informational",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.max_thm_loc": {
        "label": "zerocopy/proofs max hand theorem LOC (NB)",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.thm_loc",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.proof_olean_bytes": {
        "label": "zerocopy/proofs compiled proof-module .olean bytes",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.kernel",
        "unit": "B",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.module_union_dag": {
        "label": "zerocopy/proofs Proof Expr union DAG nodes",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.kernel",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.sum_val_tree": {
        "label": "zerocopy/proofs Proof Expr unfolded tree nodes",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.kernel",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.tree_to_dag_ratio": {
        "label": "zerocopy/proofs Proof Expr tree-to-DAG ratio",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.kernel",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.zerocopy_suite.kernel_replay_ms": {
        "label": "zerocopy/proofs isolated kernel replay median",
        "category": "proof_burden",
        "group": "proof_burden.zerocopy_suite.replay",
        "unit": "ms",
        "direction": "lower_is_better",
        "deterministic": False,
    },
    "proof_burden.theory.gt_60_thm_count": {
        "label": "anneal/theory theorems > 60 NB lines",
        "category": "proof_burden",
        "group": "proof_burden.heavy_tail",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.correspondence.gt_60_thm_count": {
        "label": "anneal/correspondence theorems > 60 NB lines",
        "category": "proof_burden",
        "group": "proof_burden.heavy_tail",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
    "proof_burden.correspondence.max_thm_loc": {
        "label": "anneal/correspondence max theorem NB lines",
        "category": "proof_burden",
        "group": "proof_burden.heavy_tail",
        "unit": "count",
        "direction": "lower_is_better",
        "deterministic": True,
    },
}


class HealthScanError(RuntimeError):
    """Raised when a hard hygiene check or filesystem invariant fails."""


def ensure_nonsymlink(path: Path, root: Path | None = None) -> None:
    """Reject a symlink at `path` or at any lexical ancestor strictly below
    `root`; never inspects `root` or anything above it.

    With no `root`, only `path` itself is checked.
    """
    if path.is_symlink():
        raise HealthScanError(f"symlink disallowed: {path}")
    if root is None:
        return
    try:
        rel = path.relative_to(root)
    except ValueError as exc:
        raise HealthScanError(f"path {path} escapes {root}") from exc
    cur = root
    for part in rel.parts[:-1]:
        cur = cur / part
        if cur.is_symlink():
            raise HealthScanError(f"symlink disallowed: {cur}")


def lean_lines(text: str) -> list[str]:
    """Split `text` at `\n` only, like Lean; `str.splitlines` would also split
    at characters such as `\x1e` or `\u2028` that Lean keeps within a line."""
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return [line.removesuffix("\r") for line in lines]


def strip_lean_comments_and_strings(text: str, mask_strings: bool = True) -> list[str]:
    """Strip `--` and nested `/- ... -/` comments (and optionally string/char
    literals) line-by-line while preserving exact line count."""
    out_lines: list[str] = []
    block_depth = 0
    in_string = False
    for raw_line in lean_lines(text):
        chars: list[str] = []
        i = 0
        n = len(raw_line)
        while i < n:
            if in_string:
                if raw_line[i] == "\\" and i + 1 < n:
                    chars.append("  " if mask_strings else raw_line[i : i + 2])
                    i += 2
                elif raw_line[i] == '"':
                    in_string = False
                    chars.append('"' if not mask_strings else " ")
                    i += 1
                else:
                    chars.append(" " if mask_strings else raw_line[i])
                    i += 1
            elif block_depth > 0:
                if raw_line[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                elif raw_line[i : i + 2] == "-/":
                    block_depth -= 1
                    i += 2
                    # A comment separates tokens: `simp/- -/only` is `simp only`.
                    if block_depth == 0 and chars:
                        chars.append(" ")
                else:
                    i += 1
            else:
                if raw_line[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                elif raw_line[i : i + 2] == "--":
                    break
                elif raw_line[i] == '"':
                    in_string = True
                    chars.append('"' if not mask_strings else " ")
                    i += 1
                elif raw_line[i] == "'":
                    prev_ident = i > 0 and (
                        raw_line[i - 1].isalnum() or raw_line[i - 1] in ("_", "'")
                    )
                    char_end: int | None = None
                    if not prev_ident and i + 2 < n:
                        if raw_line[i + 1] == "\\":
                            if raw_line[i + 2] in ("u", "x"):
                                j = i + 3
                                while (
                                    j < n
                                    and j - i <= 12
                                    and raw_line[j] not in ("'", '"', "\\", " ")
                                ):
                                    j += 1
                                if j < n and raw_line[j] == "'":
                                    char_end = j + 1
                            elif i + 3 < n and raw_line[i + 3] == "'":
                                char_end = i + 4
                        elif raw_line[i + 1] != "'" and raw_line[i + 2] == "'":
                            char_end = i + 3
                    if char_end is not None:
                        chars.append(
                            " " * (char_end - i) if mask_strings else raw_line[i:char_end]
                        )
                        i = char_end
                    else:
                        chars.append(raw_line[i])
                        i += 1
                else:
                    chars.append(raw_line[i])
                    i += 1
        out_lines.append("".join(chars))
    return out_lines


def nonblank_code_lines(text: str) -> list[str]:
    return [
        ln.strip()
        for ln in strip_lean_comments_and_strings(text, mask_strings=False)
        if ln.strip()
    ]


def extract_declarations(text: str) -> list[tuple[int, int, str, str, bool]]:
    """Return `(start_line_0, end_line_0, kind, name, is_private)` for top-level decls."""
    code_lines = strip_lean_comments_and_strings(text, mask_strings=True)
    headers: list[tuple[int, str, str, bool]] = []
    for idx, line in enumerate(code_lines):
        if not line or line[0].isspace():
            continue
        s = line.strip()
        m = DECL_HEADER_RE.match(s)
        if m:
            is_priv = PRIVATE_DECL_RE.match(s) is not None
            headers.append((idx, m.group(1), m.group(2), is_priv))
    spans: list[tuple[int, int, str, str, bool]] = []
    total = len(code_lines)
    for pos, (start, kind, name, is_priv) in enumerate(headers):
        end = headers[pos + 1][0] if pos + 1 < len(headers) else total
        spans.append((start, end, kind, name, is_priv))
    return spans


def scan_corpus_stats(paths: list[Path], base_dir: Path | None = None) -> dict[str, Any]:
    """Compute deterministic LOC and theorem-length quantiles over `paths`."""
    total_nb = 0
    thm_locs: list[int] = []
    gt_20: list[dict[str, Any]] = []
    gt_60: list[dict[str, Any]] = []

    for path in sorted(paths):
        ensure_nonsymlink(path, base_dir)
        text = path.read_text(encoding="utf-8")
        code_lines = strip_lean_comments_and_strings(text, mask_strings=False)
        total_nb += sum(1 for ln in code_lines if ln.strip())
        rel = path.relative_to(base_dir).as_posix() if base_dir else str(path)
        for start, end, kind, name, _ in extract_declarations(text):
            if kind not in ("theorem", "lemma"):
                continue
            nb = sum(1 for ln in code_lines[start:end] if ln.strip())
            thm_locs.append(nb)
            entry = {"file": rel, "line": start + 1, "name": name, "nb_loc": nb}
            if nb > D3_PROOF_THM_NB_ADVISORY:
                gt_20.append(entry)
            if nb > D3_PASS1_THM_NB_ADVISORY:
                gt_60.append(entry)

    thm_sorted = sorted(thm_locs)
    n = len(thm_sorted)

    def pct(p: float) -> int:
        if not n:
            return 0
        return thm_sorted[min(n - 1, int(round(p * (n - 1))))]

    return {
        "files": len(paths),
        "nonblank_loc": total_nb,
        "theorem_count": n,
        "thm_loc_p50": float(statistics.median(thm_sorted)) if n else 0.0,
        "thm_loc_p90": pct(0.90),
        "max_thm_loc": max(thm_sorted) if n else 0,
        "gt_20_count": len(gt_20),
        "gt_60_count": len(gt_60),
        "gt_20_theorems": gt_20,
        "gt_60_theorems": gt_60,
    }


def find_unused_private_decls(
    paths: list[Path], base_dir: Path | None = None
) -> list[dict[str, Any]]:
    """Return orphaned `private` theorems/lemmas/defs with 0 external references."""
    unused: list[dict[str, Any]] = []
    for path in sorted(paths):
        ensure_nonsymlink(path, base_dir)
        text = path.read_text(encoding="utf-8")
        code_lines = strip_lean_comments_and_strings(text, mask_strings=True)
        decls = extract_declarations(text)
        rel = path.relative_to(base_dir).as_posix() if base_dir else str(path)
        for start, end, kind, name, is_priv in decls:
            if not is_priv:
                continue
            outside_lines = code_lines[:start] + code_lines[end:]
            outside_tokens = IDENT_TOKEN_RE.findall("\n".join(outside_lines))
            if name not in outside_tokens:
                unused.append({
                    "file": rel,
                    "line": start + 1,
                    "kind": kind,
                    "name": name,
                })
    return unused


def _balanced_end(text: str, start: int) -> int | None:
    """Return the index just past the bracket group opening at `text[start]`."""
    closers = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    stack: list[str] = []
    for i in range(start, len(text)):
        ch = text[i]
        if ch in closers:
            stack.append(closers[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
            if not stack:
                return i + 1
    return None


def _split_top_level_commas(text: str) -> list[str]:
    """Split `text` at commas outside any bracket group."""
    closers = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
    stack: list[str] = []
    items: list[str] = []
    start = 0
    for i, ch in enumerate(text):
        if ch in closers:
            stack.append(closers[ch])
        elif stack and ch == stack[-1]:
            stack.pop()
        elif ch == "," and not stack:
            items.append(text[start:i])
            start = i + 1
    items.append(text[start:])
    return items


def _simp_lemma_lists(code: str) -> list[tuple[int, str]]:
    """Return `(offset, contents)` of every `simp`-family lemma list in `code`.

    Skips `(config := ...)` groups, `+opt`/`-opt` flags, and `only` between the
    tactic name and `[`, and keeps nested brackets inside the list.
    """
    lists: list[tuple[int, str]] = []
    for m in SIMP_CALL_RE.finditer(code):
        i = m.end()
        while True:
            while i < len(code) and code[i].isspace():
                i += 1
            if i < len(code) and code[i] == "(":
                end = _balanced_end(code, i)
                if end is None:
                    break
                i = end
                continue
            opt = SIMP_OPTION_RE.match(code, i)
            if opt is None:
                break
            i = opt.end()
        if i < len(code) and code[i] == "[":
            end = _balanced_end(code, i)
            lists.append((m.start(), code[i + 1 : (end or len(code)) - 1]))
    return lists


def scan_file_hygiene(
    text: str,
    rel_path: str,
    check_semicolons: bool = True,
) -> list[dict[str, Any]]:
    """Check G4 anti-golf syntactic rules on one Lean source string."""
    violations: list[dict[str, Any]] = []
    raw_lines = lean_lines(text)
    code_lines = strip_lean_comments_and_strings(text, mask_strings=True)

    for lineno, (raw, code) in enumerate(zip(raw_lines, code_lines), 1):
        is_single_string_lit = bool(re.match(r'^\s*"(?:\\.|[^"\\])*"\s*$', raw))
        if len(raw) > MAX_CODE_COLS and not is_single_string_lit:
            violations.append({
                "rule": "max_columns",
                "file": rel_path,
                "line": lineno,
                "detail": f"line length {len(raw)} exceeds {MAX_CODE_COLS} columns",
            })
        if SIMP_ALL_RE.search(code):
            violations.append({
                "rule": "forbidden_simp_wildcard",
                "file": rel_path,
                "line": lineno,
                "detail": "forbidden `simp_all`",
            })
        if LOCAL_MACRO_RE.search(code):
            violations.append({
                "rule": "forbidden_local_macro",
                "file": rel_path,
                "line": lineno,
                "detail": "forbidden `local macro` or `macro_rules` compression",
            })
        if check_semicolons and code.count(";") > MAX_SEMI_PER_LINE:
            violations.append({
                "rule": "excessive_semicolons",
                "file": rel_path,
                "line": lineno,
                "detail": (
                    f"line packs {code.count(';')} semicolons "
                    f"(max {MAX_SEMI_PER_LINE})"
                ),
            })

    joined_code = "\n".join(code_lines)
    for offset, body in _simp_lemma_lists(joined_code):
        lineno = joined_code.count("\n", 0, offset) + 1
        if any(item.strip() == "*" for item in _split_top_level_commas(body)):
            violations.append({
                "rule": "forbidden_simp_wildcard",
                "file": rel_path,
                "line": lineno,
                "detail": "forbidden `*` (all hypotheses) in a `simp` lemma list",
            })
        for ev in FORBIDDEN_SIMP_EVALUATORS:
            if re.search(rf"\b{re.escape(ev)}\b", body):
                violations.append({
                    "rule": "simp_only_evaluator",
                    "file": rel_path,
                    "line": lineno,
                    "detail": f"forbidden AST/semantics evaluator `{ev}` in a `simp` lemma list",
                })
    return violations


def _verify_git_ref(repo_root: Path, ref_name: str) -> bool:
    return (
        subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--verify", "--quiet", ref_name],
            capture_output=True,
            check=False,
        ).returncode
        == 0
    )


# The spec-immutability gate covers the proof units only.
SPEC_GATE_SCOPE = "zerocopy/proofs/"
SPEC_CHANGE_KEY = "Spec-Change"
SPEC_CHANGE_KINDS = ("initial", "tightening", "weakening", "refactor")
SPEC_CHANGE_VALUE_RE = re.compile(
    r"([0-9A-Za-z_][0-9A-Za-z_.-]*) (" + "|".join(SPEC_CHANGE_KINDS) + r")"
)
UNIT_FILENAME_RE = re.compile(r"[0-9A-Za-z_][0-9A-Za-z_.-]*")


def _git_bytes(repo_root: Path, *args: str) -> bytes:
    try:
        return subprocess.check_output(
            ["git", "-C", str(repo_root), *args], stderr=subprocess.PIPE
        )
    except subprocess.CalledProcessError as exc:
        detail = exc.stderr.decode("utf-8", "replace").strip()
        raise HealthScanError(f"git {' '.join(args)} failed: {detail}") from exc


def git_merge_base(repo_root: Path, base_ref: str) -> str:
    """Return `git merge-base <base_ref> HEAD`, failing closed if none exists."""
    if not _verify_git_ref(repo_root, base_ref):
        raise HealthScanError(f"git base ref {base_ref!r} not found")
    sha = _git_bytes(repo_root, "merge-base", base_ref, "HEAD").decode().strip()
    if not sha:
        raise HealthScanError(f"no merge base between {base_ref!r} and HEAD")
    return sha


def _strict_json(raw: bytes) -> Any:
    """Parse JSON, rejecting duplicate object keys."""

    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        keys = [k for k, _ in pairs]
        if len(keys) != len(set(keys)):
            raise ValueError(f"duplicate keys in {keys}")
        return dict(pairs)

    return json.loads(raw, object_pairs_hook=no_duplicates)


def _is_regular_file(repo_root: Path, rev: str, path: str) -> bool:
    out = _git_bytes(repo_root, "ls-tree", "-z", rev, "--", path)
    return out.split(b" ", 1)[0] in (b"100644", b"100755")


def _protected_spec_paths(repo_root: Path, rev: str) -> dict[str, str]:
    """Map each protected path of each proof unit at `rev` to its unit name.

    A unit's protected paths are its `request.json` and every source that
    `request.json` (as of `rev`) declares with `"role": "specification"`.
    """
    raw = _git_bytes(
        repo_root, "ls-tree", "-r", "-z", "--name-only", rev, "--", SPEC_GATE_SCOPE
    )
    protected: dict[str, str] = {}
    for path in (f.decode("utf-8", "surrogateescape") for f in raw.split(b"\0") if f):
        parts = path[len(SPEC_GATE_SCOPE):].split("/")
        if len(parts) != 2 or parts[1] != "request.json":
            continue
        unit = parts[0]
        where = f"{rev[:12]}:{path}"
        try:
            request = _strict_json(_git_bytes(repo_root, "show", f"{rev}:{path}"))
        except ValueError as exc:
            raise HealthScanError(f"{where}: invalid JSON: {exc}") from exc
        proof = request.get("proof") if isinstance(request, dict) else None
        sources = proof.get("sources") if isinstance(proof, dict) else None
        if not isinstance(sources, list) or proof.get("source_root") != ".":
            raise HealthScanError(
                f"{where}: expected proof.source_root '.' and a proof.sources list"
            )
        protected[path] = unit
        for source in sources:
            if not isinstance(source, dict):
                raise HealthScanError(f"{where}: proof.sources entry is not an object")
            if source.get("role") == "proof":
                continue
            filename = source.get("path")
            if (
                source.get("role") != "specification"
                or not isinstance(filename, str)
                or not UNIT_FILENAME_RE.fullmatch(filename)
                or filename.startswith(".")
            ):
                raise HealthScanError(
                    f"{where}: unsupported proof source {source!r}"
                )
            protected[f"{SPEC_GATE_SCOPE}{unit}/{filename}"] = unit
    return protected


def _request_spec_view(raw: bytes) -> str | None:
    """Canonical `request.json` content minus its proof-role sources, or
    `None` if it does not parse.

    Two requests with equal views differ only in which proof modules they
    declare, which cannot change the specification.
    """
    try:
        request = _strict_json(raw)
    except ValueError:
        return None
    proof = request.get("proof") if isinstance(request, dict) else None
    if isinstance(proof, dict) and isinstance(proof.get("sources"), list):
        proof["sources"] = [
            src
            for src in proof["sources"]
            if not (isinstance(src, dict) and src.get("role") == "proof")
        ]
    return json.dumps(request, sort_keys=True)


def _request_spec_unchanged(repo_root: Path, old: str, new: str, path: str) -> bool:
    """Whether `path` is a regular-file `request.json` at both revisions whose
    edits are confined to proof-role sources."""
    if not path.endswith("/request.json"):
        return False
    views = []
    for rev in (old, new):
        if not _is_regular_file(repo_root, rev, path):
            return False
        proc = subprocess.run(
            ["git", "-C", str(repo_root), "show", f"{rev}:{path}"],
            capture_output=True,
            check=False,
        )
        if proc.returncode != 0:
            return False
        views.append(_request_spec_view(proc.stdout))
    return views[0] is not None and views[0] == views[1]


def _changed_paths(repo_root: Path, old: str, new: str) -> list[str]:
    """Every path that `old..new` adds, modifies, deletes, or renames (both
    sides of a rename) under `SPEC_GATE_SCOPE`."""
    raw = _git_bytes(
        repo_root,
        "diff-tree",
        "-r",
        "-z",
        "-M",
        "--name-status",
        old,
        new,
        "--",
        SPEC_GATE_SCOPE,
    )
    fields = [f.decode("utf-8", "surrogateescape") for f in raw.split(b"\0") if f]
    paths: list[str] = []
    i = 0
    while i < len(fields):
        width = 3 if fields[i][:1] in ("R", "C") else 2
        paths.extend(fields[i + 1 : i + width])
        i += width
    return paths


def _authorized_spec_changes(
    repo_root: Path, base: str
) -> tuple[set[str], list[str]]:
    """Return the units named by `Spec-Change: <unit> <kind>` trailers on
    commits in `base..HEAD`, plus errors for malformed `Spec-Change`
    trailers.

    Only Git-recognized trailers count; prose that merely mentions
    `Spec-Change:` in a message body is ignored. Records are NUL-separated
    and lines split at `\n` only, since commit messages cannot contain NUL
    but can contain other control characters.
    """
    raw = _git_bytes(
        repo_root,
        "log",
        "-z",
        "--format=%H%n%(trailers:only,unfold)",
        f"{base}..HEAD",
    ).decode("utf-8", "replace")
    units: set[str] = set()
    errors: list[str] = []
    for record in raw.split("\0"):
        if not record.strip():
            continue
        sha, _, trailers = record.partition("\n")
        for line in trailers.split("\n"):
            key, sep, value = line.partition(":")
            if not sep or key.strip().lower() != SPEC_CHANGE_KEY.lower():
                continue
            m = SPEC_CHANGE_VALUE_RE.fullmatch(value.strip())
            if key != SPEC_CHANGE_KEY or not value.startswith(" ") or m is None:
                errors.append(
                    f"commit {sha[:12]}: malformed trailer {line!r}; expected "
                    f"`{SPEC_CHANGE_KEY}: <unit> <{'|'.join(SPEC_CHANGE_KINDS)}>`"
                )
                continue
            units.add(m.group(1))
    return units, errors


def _merge_into_base(repo_root: Path, base: str) -> tuple[str, set[str]]:
    """Return the tree of merging `HEAD` into `base` (`git merge-tree`) and
    the set of conflicted paths.

    A conflicted path need not differ from `base` in the merged tree (for
    example, a modify/delete conflict keeps `base`'s file), so callers must
    treat conflicted paths as changed.
    """
    proc = subprocess.run(
        ["git", "-C", str(repo_root), "merge-tree", "--write-tree", "--name-only",
         "--no-messages", "-z", base, "HEAD"],
        capture_output=True,
        check=False,
    )
    fields = [
        f.decode("utf-8", "surrogateescape") for f in proc.stdout.split(b"\0") if f
    ]
    if proc.returncode not in (0, 1) or not fields:
        raise HealthScanError(
            f"git merge-tree {base} HEAD failed: "
            f"{proc.stderr.decode('utf-8', 'replace').strip()}"
        )
    return fields[0], set(fields[1:])


def check_spec_immutability_git(repo_root: Path, base_ref: str) -> list[str]:
    """Enforce spec immutability on the change that merging `HEAD` into
    `base_ref` would make.

    Fails when the tree diff from `base_ref` to that merge result under
    `zerocopy/proofs/` modifies, deletes, or renames a unit's `request.json`
    or any of its specification-role sources (roles read from `request.json`
    at `base_ref`), unless a commit in `base_ref..HEAD` carries a
    `Spec-Change: <unit> <kind>` trailer for that unit. A merge conflict on
    a protected path also counts as changing it. An in-place `request.json`
    edit that only adds, removes, or changes proof-role sources is allowed.
    Units absent from `base_ref` are not protected.
    """
    if not _verify_git_ref(repo_root, base_ref):
        raise HealthScanError(f"git base ref {base_ref!r} not found")
    base = _git_bytes(repo_root, "rev-parse", f"{base_ref}^{{commit}}").decode().strip()
    merged, conflicted = _merge_into_base(repo_root, base)
    protected = _protected_spec_paths(repo_root, base)
    touched: dict[str, list[str]] = {}
    for path in conflicted:
        unit = protected.get(path)
        if unit is not None:
            touched.setdefault(unit, []).append(path)
    for path in _changed_paths(repo_root, base, merged):
        unit = protected.get(path)
        if unit is not None and not _request_spec_unchanged(
            repo_root, base, merged, path
        ):
            touched.setdefault(unit, []).append(path)
    authorized, errors = _authorized_spec_changes(repo_root, base)
    for unit in sorted(touched):
        if unit not in authorized:
            errors.append(
                f"{SPEC_GATE_SCOPE}{unit}: merging HEAD into {base_ref} "
                f"({base[:12]}) changes protected specification path(s) "
                f"{sorted(set(touched[unit]))} without a "
                f"`{SPEC_CHANGE_KEY}: {unit} <kind>` commit trailer"
            )
    return errors


def check_repo_hygiene(
    repo_root: Path,
    base_rev: str | None = None,
    strict_all: bool = False,
) -> list[dict[str, Any]]:
    """Run G4 syntactic hygiene across `zerocopy/proofs/` (always strict) and
    `anneal/{theory,correspondence}/` (ratcheted against `base_rev` unless
    `strict_all`). Callers pass the merge base of the base branch and `HEAD`,
    so changes that land on the base branch later never fail this tree."""
    violations: list[dict[str, Any]] = []
    proofs_root = repo_root / "zerocopy/proofs"
    if proofs_root.is_dir():
        ensure_nonsymlink(proofs_root, repo_root)
        for p in sorted(proofs_root.rglob("*.lean")):
            ensure_nonsymlink(p, repo_root)
            rel = p.relative_to(repo_root).as_posix()
            violations.extend(
                scan_file_hygiene(
                    p.read_text(encoding="utf-8"),
                    rel,
                    check_semicolons=(p.name != "Spec.lean"),
                )
            )

    pass1_dirs = [repo_root / "anneal/theory", repo_root / "anneal/correspondence"]
    # Map renamed working-tree paths to their `base_rev` paths so a renamed
    # legacy file ratchets against its own base content.
    renamed_from: dict[str, str] = {}
    if base_rev is not None and not strict_all:
        raw = _git_bytes(
            repo_root,
            "diff",
            "-M",
            "--name-status",
            "-z",
            base_rev,
            "--",
            "anneal/theory",
            "anneal/correspondence",
        )
        fields = [f.decode("utf-8", "replace") for f in raw.split(b"\0") if f]
        i = 0
        while i < len(fields):
            if fields[i].startswith(("R", "C")):
                renamed_from[fields[i + 2]] = fields[i + 1]
                i += 3
            else:
                i += 2
    for d in pass1_dirs:
        if not d.is_dir():
            continue
        ensure_nonsymlink(d, repo_root)
        for p in sorted(d.rglob("*.lean")):
            ensure_nonsymlink(p, repo_root)
            rel = p.relative_to(repo_root).as_posix()
            cur_v = scan_file_hygiene(
                p.read_text(encoding="utf-8"),
                rel,
                check_semicolons=True,
            )
            if not cur_v:
                continue
            if strict_all or base_rev is None:
                if strict_all:
                    violations.extend(cur_v)
                else:
                    # Without a git base ref, still fail closed on universally
                    # banned `simp [*]`/`simp_all` and `local macro`.
                    violations.extend(
                        v
                        for v in cur_v
                        if v["rule"]
                        in ("forbidden_simp_wildcard", "forbidden_local_macro")
                    )
                continue
            base_rel = renamed_from.get(rel, rel)
            proc = subprocess.run(
                ["git", "-C", str(repo_root), "show", f"{base_rev}:{base_rel}"],
                capture_output=True,
                text=True,
                check=False,
            )
            if proc.returncode != 0:
                violations.extend(cur_v)
                continue
            base_v = scan_file_hygiene(proc.stdout, rel, check_semicolons=True)
            for rule in {v["rule"] for v in cur_v}:
                cur_rule = [v for v in cur_v if v["rule"] == rule]
                base_count = sum(1 for v in base_v if v["rule"] == rule)
                if len(cur_rule) > base_count:
                    violations.extend(cur_rule[base_count:])
    return violations


PROFILER_LEAN_SRC = r"""import Lean
import Lean.Replay

open Lean

structure ExprStats where
  dagNodes  : Nat
  treeNodes : Nat

partial def measureExpr (root : Expr) : ExprStats :=
  let cap := 100000000
  let rec go (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some cached := (← get).get? e then
      return cached
    let res ← match e with
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ => pure 1
      | .mdata _ b | .proj _ _ b => do
        let t ← go b
        pure (Nat.min cap (1 + t))
      | .app f a => do
        let tf ← go f
        let ta ← go a
        pure (Nat.min cap (1 + tf + ta))
      | .lam _ ty body _ | .forallE _ ty body _ => do
        let tt ← go ty
        let tb ← go body
        pure (Nat.min cap (1 + tt + tb))
      | .letE _ ty val body _ => do
        let tt ← go ty
        let tv ← go val
        let tb ← go body
        pure (Nat.min cap (1 + tt + tv + tb))
    modify (·.insert e res)
    return res
  let (treeN, vis) := (go root).run {}
  { dagNodes := vis.size, treeNodes := treeN }

def main (args : List String) : IO Unit := do
  let (modsCsv, sysroot?) ← match args with
    | [m] => pure (m, none)
    | [m, s] => pure (m, some s)
    | _ => throw (IO.userError "expected <mod1,mod2,...> [sysroot]")
  let targetMods :=
    (modsCsv.splitOn ",").filterMap fun s =>
      let t := s.trimAscii.toString
      if t.isEmpty then none else some t.toName
  if targetMods.isEmpty then
    throw (IO.userError "empty module list")
  let sysroot ← match sysroot? with
    | some s => pure ⟨s⟩
    | none => findSysroot
  initSearchPath sysroot
  let modImports := targetMods.toArray.map fun m => { module := m : Import }
  let env ← importModules modImports {} 0
  let mut sumValTree : Nat := 0
  let mut sumValDag : Nat := 0
  let mut declCount : Nat := 0
  let mut visited : Std.HashSet Expr := {}
  let mut replayPlans : Array (Array Import × Std.HashMap Name ConstantInfo) := #[]
  for targetMod in targetMods do
    let mut modIdx? : Option Nat := none
    for i in Array.range env.header.modules.size do
      if env.header.modules[i]!.module == targetMod then
        modIdx? := some i
    let some modIdx := modIdx? | throw (IO.userError s!"module {targetMod} not found")
    let data := env.header.moduleData[modIdx]!
    let mut modConsts : Std.HashMap Name ConstantInfo := {}
    for i in Array.range data.constNames.size do
      let name := data.constNames[i]!
      let ci := data.constants[i]!
      modConsts := modConsts.insert name ci
      let val? : Option Expr := match ci with
        | .defnInfo v => some v.value
        | .thmInfo v  => some v.value
        | _           => none
      let vs := match val? with
        | some v => measureExpr v
        | none   => { dagNodes := 0, treeNodes := 0 }
      let rec walk (e : Expr) : StateM (Std.HashSet Expr) Unit := do
        if (← get).contains e then return
        modify (·.insert e)
        match e with
        | .mdata _ b | .proj _ _ b => walk b
        | .app f a => walk f; walk a
        | .lam _ t b _ | .forallE _ t b _ => walk t; walk b
        | .letE _ t v b _ => walk t; walk v; walk b
        | _ => pure ()
      let (_, visited') := (walk ci.type).run visited
      visited := visited'
      if let some v := val? then
        let (_, visited'') := (walk v).run visited
        visited := visited''
      declCount := declCount + 1
      sumValTree := sumValTree + vs.treeNodes
      sumValDag := sumValDag + vs.dagNodes
    replayPlans := replayPlans.push (data.imports, modConsts)
  let mut replayTimes : Array Float := #[]
  for _ in Array.range 3 do
    let mut runTotalMs : Float := 0.0
    for (imports, modConsts) in replayPlans do
      let baseEnv ← importModules imports {} 0
      let t0 ← IO.monoNanosNow
      let _ ← baseEnv.toKernelEnv.replay modConsts
      let t1 ← IO.monoNanosNow
      runTotalMs := runTotalMs + ((t1 - t0).toFloat / 1000000.0)
    replayTimes := replayTimes.push runTotalMs
  IO.println <| Json.compress <| Json.mkObj [
    ("compiled_decl_count", toJson declCount),
    ("module_union_dag", toJson visited.size),
    ("sum_val_dag", toJson sumValDag),
    ("sum_val_tree", toJson sumValTree),
    ("kernel_replay_runs_ms", toJson replayTimes)
  ]
"""


def _minimal_lean_env(sysroot: Path, lean_paths: list[Path]) -> dict[str, str]:
    env: dict[str, str] = {}
    for key in ("PATH", "HOME", "TMPDIR", "USER", "LOGNAME", "LANG", "LC_ALL"):
        val = os.environ.get(key)
        if val is not None:
            env[key] = val
    env.setdefault("PATH", "/usr/bin:/bin")
    env["LEAN_SYSROOT"] = str(sysroot)
    env["LEAN_PATH"] = ":".join(str(p) for p in lean_paths)
    return env


def profile_compiled_modules(
    lean_bin: Path, lean_paths: list[Path], mod_names: list[str]
) -> dict[str, Any]:
    """Measure `.olean` bytes, `Expr` DAG/tree nodes, and 3-run `kernel_replay_ms`."""
    unique_mods = list(dict.fromkeys(mod_names))
    if not unique_mods:
        raise ValueError("profile_compiled_modules requires at least one module name")
    print_env = {
        k: v
        for k, v in os.environ.items()
        if k in ("PATH", "HOME", "TMPDIR", "USER", "LOGNAME", "LANG", "LC_ALL")
    }
    print_env.setdefault("PATH", "/usr/bin:/bin")
    prefix_out = subprocess.check_output(
        [str(lean_bin), "--print-prefix"], env=print_env, text=True
    ).strip()
    sysroot = Path(prefix_out).resolve(strict=True)
    stdlib = sysroot / "lib/lean"
    all_paths: list[Path] = []
    for p in list(lean_paths) + [stdlib]:
        if p not in all_paths:
            all_paths.append(p)
    olean_bytes = 0
    for root in lean_paths:
        for mod_name in unique_mods:
            for ext in (".olean", ".olean.server", ".olean.private"):
                cand = root / f"{mod_name.replace('.', '/')}{ext}"
                if cand.is_file() and not cand.is_symlink():
                    olean_bytes += cand.stat().st_size

    env = _minimal_lean_env(sysroot, all_paths)
    with tempfile.TemporaryDirectory(prefix="anneal-kprof-") as td:
        prof = Path(td) / "ProfileMod.lean"
        prof.write_text(PROFILER_LEAN_SRC, encoding="utf-8")
        proc = subprocess.run(
            [
                str(lean_bin),
                "-Ddebug.skipKernelTC=false",
                "--run",
                str(prof),
                ",".join(unique_mods),
                str(sysroot),
            ],
            env=env,
            capture_output=True,
            text=True,
            check=True,
        )
        raw = json.loads(proc.stdout.strip().splitlines()[-1])
    sum_dag = max(1, int(raw["sum_val_dag"]))
    sum_tree = int(raw["sum_val_tree"])
    ratio = round(sum_tree / sum_dag, 2)
    replay_med = round(float(statistics.median(raw["kernel_replay_runs_ms"])), 2)
    return {
        "proof_olean_bytes": olean_bytes,
        "compiled_decl_count": int(raw["compiled_decl_count"]),
        "module_union_dag": int(raw["module_union_dag"]),
        "sum_val_dag": int(raw["sum_val_dag"]),
        "sum_val_tree": sum_tree,
        "tree_to_dag_ratio": ratio,
        "kernel_replay_ms": replay_med,
    }


def profile_compiled_module(
    lean_bin: Path, lean_paths: list[Path], mod_name: str
) -> dict[str, Any]:
    """Measure a single compiled module's `.olean` footprint and kernel replay."""
    return profile_compiled_modules(lean_bin, lean_paths, [mod_name])


def evaluate_d3_advisories(
    proof_stats: dict[str, Any],
    theory_stats: dict[str, Any] | None = None,
    corr_stats: dict[str, Any] | None = None,
    kernel_profile: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Evaluate Policy Decision `D3` non-blocking review advisories."""
    advisories: list[dict[str, Any]] = []
    for thm in proof_stats.get("gt_20_theorems", []):
        advisories.append({
            "kind": "proof_thm_gt_20_nb",
            "detail": (
                f"{thm['file']}:{thm['line']} `{thm['name']}` spans {thm['nb_loc']} "
                f"non-blank lines (> {D3_PROOF_THM_NB_ADVISORY})"
            ),
        })
    for label, st in (("theory", theory_stats), ("correspondence", corr_stats)):
        if st and st.get("gt_60_count", 0) > 0:
            advisories.append({
                "kind": f"{label}_gt_60_heavy_tail",
                "count": st["gt_60_count"],
                "detail": (
                    f"{label} contains {st['gt_60_count']} theorem(s) exceeding "
                    f"{D3_PASS1_THM_NB_ADVISORY} non-blank lines "
                    f"(max {st['max_thm_loc']}L)"
                ),
            })
    if kernel_profile is not None:
        ratio = float(kernel_profile.get("tree_to_dag_ratio", 0.0))
        if ratio > D3_TREE_TO_DAG_RATIO_ADVISORY:
            advisories.append({
                "kind": "expr_tree_to_dag_ratio_high",
                "tree_to_dag_ratio": ratio,
                "detail": (
                    f"tree_to_dag_ratio={ratio} exceeds D3 threshold "
                    f"{D3_TREE_TO_DAG_RATIO_ADVISORY} (missing `let s_k` bindings)"
                ),
            })
    return advisories


def _discover_proof_modules_for_lib(lib_dir: Path, repo_root: Path) -> list[str]:
    """Return compiled proof-role module names present inside `lib_dir`."""
    unit_req = repo_root / "zerocopy/proofs" / lib_dir.parent.name / "request.json"
    if unit_req.is_file() and not unit_req.is_symlink():
        try:
            req = json.loads(unit_req.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            req = None
        if isinstance(req, dict):
            sources = req.get("proof", {}).get("sources", [])
            mods = [
                str(src["module"])
                for src in sources
                if isinstance(src, dict)
                and src.get("role") == "proof"
                and isinstance(src.get("module"), str)
                and (lib_dir / f"{src['module'].replace('.', '/')}.olean").is_file()
            ]
            if mods:
                return list(dict.fromkeys(mods))

    # Fallback: pick top-level proof `.olean` modules excluding framework/spec
    # artifacts (`Spec`, `Captured`, `Expected`, `Model`, `Trusted`, `Anneal`),
    # ordering `AutoScaffold` before `Proof` and any remaining custom modules.
    excluded = {"Spec", "Captured", "Expected", "Model", "Trusted", "Anneal"}
    discovered: list[str] = []
    for preferred in ("AutoScaffold", "Proof"):
        if (lib_dir / f"{preferred}.olean").is_file():
            discovered.append(preferred)
    if lib_dir.is_dir():
        for olean in sorted(lib_dir.glob("*.olean")):
            mod = olean.stem
            if mod not in excluded and mod not in discovered:
                discovered.append(mod)
    return discovered or ["Proof"]


def collect_proof_burden_telemetry(
    repo_root: Path,
    lean_bin: Path | None = None,
    lean_lib_dirs: list[Path] | None = None,
    lib_proof_modules: dict[Path, list[str]] | None = None,
) -> dict[str, Any]:
    """Collect `anneal-perf-record/v1`-compatible `proof_burden.*` metrics."""
    proofs_dir = repo_root / "zerocopy/proofs"
    hand_files = sorted(proofs_dir.glob("*/Proof.lean")) if proofs_dir.is_dir() else []
    scaf_files = (
        sorted(proofs_dir.glob("*/AutoScaffold.lean")) if proofs_dir.is_dir() else []
    )
    spec_files = sorted(proofs_dir.glob("*/Spec.lean")) if proofs_dir.is_dir() else []
    theory_files = sorted((repo_root / "anneal/theory").rglob("*.lean"))
    corr_files = sorted((repo_root / "anneal/correspondence").rglob("*.lean"))

    hand_stats = scan_corpus_stats(hand_files, repo_root)
    scaf_stats = scan_corpus_stats(scaf_files, repo_root)
    spec_stats = scan_corpus_stats(spec_files, repo_root)
    theory_stats = scan_corpus_stats(theory_files, repo_root)
    corr_stats = scan_corpus_stats(corr_files, repo_root)

    metrics: dict[str, Any] = {
        "proof_burden.zerocopy_suite.hand_proof_loc": hand_stats["nonblank_loc"],
        "proof_burden.zerocopy_suite.scaffold_loc": scaf_stats["nonblank_loc"],
        "proof_burden.zerocopy_suite.spec_loc": spec_stats["nonblank_loc"],
        "proof_burden.zerocopy_suite.max_thm_loc": hand_stats["max_thm_loc"],
        "proof_burden.theory.gt_60_thm_count": theory_stats["gt_60_count"],
        "proof_burden.correspondence.gt_60_thm_count": corr_stats["gt_60_count"],
        "proof_burden.correspondence.max_thm_loc": corr_stats["max_thm_loc"],
    }

    kernel_agg: dict[str, Any] | None = None
    if lean_bin is not None and lean_lib_dirs:
        olean_sum = 0
        dag_sum = 0
        val_dag_sum = 0
        tree_sum = 0
        replay_sum = 0.0
        profile_ok = True
        for lib_dir in lean_lib_dirs:
            mods = (
                lib_proof_modules.get(lib_dir)
                if lib_proof_modules is not None
                else None
            ) or _discover_proof_modules_for_lib(lib_dir, repo_root)
            try:
                prof = profile_compiled_modules(lean_bin, [lib_dir], mods)
            except (OSError, subprocess.SubprocessError, ValueError, KeyError) as exc:
                print(
                    f"proof_health_scan: warning: skipping .olean profile for "
                    f"{lib_dir}: {exc}",
                    file=sys.stderr,
                )
                profile_ok = False
                break
            olean_sum += prof["proof_olean_bytes"]
            dag_sum += prof["module_union_dag"]
            val_dag_sum += prof["sum_val_dag"]
            tree_sum += prof["sum_val_tree"]
            replay_sum += prof["kernel_replay_ms"]
        if profile_ok:
            ratio = round(tree_sum / max(1, val_dag_sum), 2)
            kernel_agg = {
                "proof_olean_bytes": olean_sum,
                "module_union_dag": dag_sum,
                "sum_val_tree": tree_sum,
                "tree_to_dag_ratio": ratio,
                "kernel_replay_ms": round(replay_sum, 2),
            }
            metrics.update({
                "proof_burden.zerocopy_suite.proof_olean_bytes": olean_sum,
                "proof_burden.zerocopy_suite.module_union_dag": dag_sum,
                "proof_burden.zerocopy_suite.sum_val_tree": tree_sum,
                "proof_burden.zerocopy_suite.tree_to_dag_ratio": ratio,
                "proof_burden.zerocopy_suite.kernel_replay_ms": round(
                    replay_sum, 2
                ),
            })

    advisories = evaluate_d3_advisories(
        hand_stats,
        theory_stats=theory_stats,
        corr_stats=corr_stats,
        kernel_profile=kernel_agg,
    )
    return {
        "metrics": metrics,
        "advisories": advisories,
        "summary": {
            "zerocopy_hand": hand_stats,
            "zerocopy_scaffold": scaf_stats,
            "theory": {
                k: v for k, v in theory_stats.items() if not k.endswith("_theorems")
            },
            "correspondence": {
                k: v for k, v in corr_stats.items() if not k.endswith("_theorems")
            },
        },
    }


def main(argv: list[str] | None = None) -> int:
    repo_default = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=repo_default,
        help="Path to the `google/zerocopy` checkout root",
    )
    parser.add_argument(
        "--check-hygiene",
        action="store_true",
        help="Enforce hard G1/G4 anti-golf and spec-immutability gates",
    )
    parser.add_argument(
        "--base-ref",
        default=None,
        help="Git base ref for G1 commit checks and Pass-1 legacy hygiene ratchet",
    )
    parser.add_argument(
        "--strict-all",
        action="store_true",
        help="Fail on legacy Pass-1 line/simp-evaluator findings without ratcheting",
    )
    parser.add_argument(
        "--unused-private",
        action="store_true",
        help="Report orphaned `private` theorems/defs with zero external references",
    )
    parser.add_argument(
        "--fail-on-unused-private",
        action="store_true",
        help="Exit non-zero if `--unused-private` finds orphaned declarations",
    )
    parser.add_argument(
        "--paths",
        nargs="*",
        type=Path,
        help="Explicit `.lean` files or directories for `--unused-private`",
    )
    parser.add_argument(
        "--telemetry",
        action="store_true",
        help="Emit `anneal-perf-record/v1` `proof_burden.*` metrics and D3 advisories",
    )
    parser.add_argument("--lean", type=Path, help="Optional Lean binary for `.olean` profiling")
    parser.add_argument(
        "--lean-lib-dir",
        action="append",
        type=Path,
        default=[],
        help="Compiled `lean-lib` directory containing proof-module `.olean`s (repeatable)",
    )
    parser.add_argument("--json-out", type=Path, help="Write JSON report to path")

    args = parser.parse_args(argv)
    if args.json_out is not None:
        ensure_nonsymlink(args.json_out)
    for raw_p in args.paths or ():
        ensure_nonsymlink(raw_p)
        if not raw_p.exists():
            raise HealthScanError(f"missing path: {raw_p}")
    ensure_nonsymlink(args.repo_root)
    repo_root = args.repo_root.resolve(strict=True)

    if not (args.check_hygiene or args.unused_private or args.telemetry):
        args.check_hygiene = True

    report: dict[str, Any] = {}
    failed = False

    if args.check_hygiene:
        base_ref = args.base_ref
        if base_ref is None:
            for cand in ("origin/main", "main"):
                if _verify_git_ref(repo_root, cand):
                    base_ref = cand
                    break
            # CI must never skip the spec-immutability check silently.
            if base_ref is None and os.environ.get("GITHUB_ACTIONS") == "true":
                raise HealthScanError(
                    "no git base ref found (tried 'origin/main', 'main'); "
                    "pass --base-ref explicitly"
                )
        merge_base = git_merge_base(repo_root, base_ref) if base_ref else None
        g1_errors = (
            check_spec_immutability_git(repo_root, base_ref) if base_ref else []
        )
        g4_violations = check_repo_hygiene(
            repo_root, base_rev=merge_base, strict_all=args.strict_all
        )
        report["hygiene"] = {
            "base_ref": base_ref,
            "merge_base": merge_base,
            "spec_immutability_errors": g1_errors,
            "violations": g4_violations,
        }
        if g1_errors or g4_violations:
            failed = True

    if args.unused_private:
        if args.paths:
            scan_files: list[Path] = []
            for p in args.paths:
                rp = p.resolve(strict=True)
                if rp.is_dir():
                    for cand_lean in sorted(rp.rglob("*.lean")):
                        ensure_nonsymlink(cand_lean, rp)
                        scan_files.append(cand_lean)
                else:
                    scan_files.append(rp)
        else:
            scan_files = sorted((repo_root / "zerocopy/proofs").rglob("Proof.lean"))
        unused = find_unused_private_decls(scan_files, repo_root)
        report["unused_private"] = unused
        if unused and args.fail_on_unused_private:
            failed = True

    if args.telemetry:
        resolved_lean: Path | None = None
        if args.lean is not None:
            # Toolchain paths may legitimately be symlinks (elan, Nix); use
            # the resolved target.
            resolved_lean = args.lean.resolve(strict=True)
        resolved_libs: list[Path] = []
        for lib_dir in args.lean_lib_dir:
            ensure_nonsymlink(lib_dir)
            resolved_libs.append(lib_dir.resolve(strict=True))
        report["telemetry"] = collect_proof_burden_telemetry(
            repo_root,
            lean_bin=resolved_lean,
            lean_lib_dirs=resolved_libs,
        )

    rendered = json.dumps(report, indent=2) + "\n"
    if args.json_out is not None:
        ensure_nonsymlink(args.json_out)
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(rendered, encoding="utf-8")
    print(rendered, end="")
    return 1 if failed else 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except HealthScanError as err:
        print(f"proof_health_scan: error: {err}", file=sys.stderr)
        raise SystemExit(1)
