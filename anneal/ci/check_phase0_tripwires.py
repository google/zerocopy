#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""CI and Git-history policy checker for two-phase soundness tripwires.

Enforces three invariants over `anneal/trusted/rustc-capture/src/tripwires.rs`,
optional `anneal/trusted/` runtime/audit fallback annotations, and bound
regression tests:

1. `tree` (invoked in `anneal-ci-tests` via `run_anneal_check.sh ci-tests`):
   Validates every declared `PHASE0_TRIPWIRE` carries a valid canonical
   `bug_id` (`ITREE-*`, `DIFF-*`, `RT-*`, `LMIRI-*`, `MINIRUST-*`), valid
   issue reference (`https://github.com/google/zerocopy/issues/<N>`,
   `"embargoed"` for coordinated private disclosure, or `"selftest"` on
   `SyntheticSelftestOnly`), non-empty `owner`, `scope`, and `rationale`,
   valid ISO `YYYY-MM-DD` `added_date`, and a CI-executed negative regression
   test (`anneal/tests/<member>/tests/*.rs` Cargo target or
   `anneal/ci/test_*.py` unittest module, without `ignore`, `should_panic`, or
   non-`cfg(test)` gating) whose reachable assertion AST/macros check
   `<bug_id>` refusal. Rejects raw `Phase0Tripwire { ... }` structs, multiple
   macro defs, conditional/split `#[cfg(...)]` decoys, unwired production rules,
   and commented-out or disabled tripwire stubs.
2. `phase0-diff` (Git-history tool run locally / pre-PR):
   Requires `--base` and `--head` (or `--diff-files`, which is cross-checked
   against Git's changed paths relative to `--base`, using `--head` when
   supplied or the working tree otherwise). Verifies edits stay isolated to the
   mutable registry region of `tripwires.rs` (keeping `PHASE0_TRIPWIRE!`,
   `check_crate`, `check_mir_body`, existing entries and helpers, and
   `SYNTHETIC_DEMO_TRIPWIRE` intact relative to `--base`) plus dedicated
   `*phase0*`/`*tripwire*` test files, while preserving pre-existing repo-wide
   tripwires cleanly.
3. `phase1-cleanup` (Git-history tool run locally / pre-PR):
   Verifies resolved or removed bug IDs leave zero residual `PHASE0_TRIPWIRE`
   or bug-ID tokens across all of `anneal/trusted/` (`*.rs` and `*.lean`,
   including `#[cfg(test)]`) at `--head`, while keeping the bound regression test
   active, preserving its Phase-0 failing witness input (verified against
   `--base`, `known_bugs` `phase0_sha`/`witness_sha256`/`witness`, or
   `--witness-sha256`), and flipping off `[PHASE0_TRIPWIRE:<bug_id>]` /
   `Unsupported` refusal.

Threat model:
This script is a structural CI hygiene lint catching accidental omissions,
stale markers or helpers, malformed metadata, disabled tests, and obvious
vacuous stubs in contributor-authored PRs. It is not a soundness boundary or an
adversarial malware sandbox against intentionally obfuscated or self-modifying
test code (such as overwriting Cargo-built binaries on disk via `std::fs::write`,
mutating `sys.modules["unittest"]`, custom `__exit__`-swallowing context
managers, `std::hint::black_box(false)` dead witness branches, or deliberate
local-binding identifier collisions), which are enforced by Gate 1, Gate 2
cross-family code review, Gate 5 maintainer approval, and hermetic CI execution.
"""

from __future__ import annotations

import argparse
import ast
from dataclasses import asdict, dataclass
import datetime
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
import sys
import tomllib
from typing import Callable, Iterable, Protocol


TRIPWIRES_REL = "anneal/trusted/rustc-capture/src/tripwires.rs"
TRUSTED_DIR_REL = "anneal/trusted"
MIR_SEMANTICS_DIR_REL = "anneal/trusted/lean/Trusted/MirSemantics"
LEAN_MIR_SEMANTICS_ROOT_REL = "anneal/trusted/lean/Trusted/MirSemantics.lean"


def _is_lean_mir_semantics_rel(rel: str) -> bool:
    """Return True iff `rel` is `Trusted/MirSemantics.lean` or a submodule `.lean` file."""
    return rel == LEAN_MIR_SEMANTICS_ROOT_REL or (
        rel.startswith(f"{MIR_SEMANTICS_DIR_REL}/") and rel.endswith(".lean")
    )
TESTS_PREFIX = "anneal/tests/"
EMBARGOED_ISSUE_TOKEN = "embargoed"
VALID_LAYERS = frozenset(
    {"static_capture", "runtime_semantics", "trusted_comment"}
)

BUG_ID_RE = re.compile(
    r"^(?:ITREE|DIFF|RT|LMIRI|MINIRUST)-[A-Z][A-Z0-9_]*-[0-9a-f]{12}$"
)
BUG_ID_INNER_RE = re.compile(
    r"\b(?:ITREE|DIFF|RT|LMIRI|MINIRUST)-[A-Z][A-Z0-9_]*-[0-9a-f]{12}\b"
)
PUBLIC_ISSUE_URL_RE = re.compile(
    r"^https://github\.com/google/zerocopy/issues/[1-9][0-9]*$"
)
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
REGRESSION_TEST_RE = re.compile(
    r"^((?:anneal/tests/[A-Za-z0-9_.-]+/[A-Za-z0-9_./-]+\.rs"
    r"|anneal/ci/test_[A-Za-z0-9_]+\.py))::([A-Za-z_][A-Za-z0-9_]*)$"
)
PHASE0_TEST_FILE_RE = re.compile(
    r"^(?:anneal/tests/(?:rustc-capture|itree_diff)/tests/"
    r"[A-Za-z0-9_-]*?(?:tripwire|phase0)[A-Za-z0-9_-]*\.rs"
    r"|anneal/ci/test_phase0_[A-Za-z0-9_]+\.py)$"
)
ALLOWED_CI_HOST_CFGS = frozenset(
    {
        "test",
        "unix",
        'target_os="linux"',
        'all(target_os="linux",target_arch="x86_64")',
        'all(target_arch="x86_64",target_os="linux")',
    }
)
VALID_BUG_STATUSES = frozenset(
    {"needs_human_review", "open", "triaged", "mitigated_phase0", "fixed"}
)
MUTABLE_START_MARKER = "// === PHASE 0 MUTABLE REGISTRY START ==="
MUTABLE_END_MARKER = "// === PHASE 0 MUTABLE REGISTRY END ==="

ACTIVE_SLICE_HEADER_RE = re.compile(
    r"pub(?:\(crate\))?\s+const\s+ACTIVE_PHASE0_TRIPWIRES\s*:\s*"
    r"&\s*\[\s*Phase0Tripwire\s*\]\s*=\s*&\["
)
MACRO_CALL_RE = re.compile(r"\bPHASE0_TRIPWIRE\s*!\s*([{\[(])")
SYNTHETIC_DEMO_DECL_RE = re.compile(
    r"(?:^|[;\n}])\s*(?:pub(?:\(crate\))?\s+)?const\s+"
    r"(SYNTHETIC_DEMO(?:_CRATE)?_TRIPWIRE)\s*:\s*Phase0Tripwire\s*=\s*$",
    re.DOTALL,
)
SYNTHETIC_SELFTEST_ALLOWED = {
    "SYNTHETIC_DEMO_TRIPWIRE": "ITREE-DEMO-000000000001",
    "SYNTHETIC_DEMO_CRATE_TRIPWIRE": "ITREE-DEMO_CRATE-000000000001",
}
RUST_COMMENT_TRIPWIRE_START_RE = re.compile(r"(//)\s*PHASE0_TRIPWIRE\s*\(")
LEAN_COMMENT_TRIPWIRE_START_RE = re.compile(r"(--)\s*PHASE0_TRIPWIRE\s*\(")
STRUCT_DEF_RE = re.compile(r"\bstruct\s+Phase0Tripwire\s*\{")
STRUCT_LITERAL_RE = re.compile(r"\bPhase0Tripwire\s*\{")
RAW_STRING_START_RE = re.compile(r'(?:br|cr|r)(?P<hashes>#*)"')
CHAR_LIT_RE = re.compile(
    r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F_]+\}|.)|[^'\\\n])'"
)
PRUNE_DIRS = frozenset({".git", ".lake", "target"})
REFUSAL_TOKENS = (
    "unsupported",
    "Unsupported",
    "CaptureRefused",
    "FaultKind",
    ".fault",
    "is_err()",
    "unwrap_err()",
    "expect_err(",
)
RUST_NONSTRING_DOMAIN_REFUSAL_TOKENS = (
    "FaultKind::Unsupported",
    ".fault .unsupported",
    "CaptureRefused",
    "is_err()",
    "unwrap_err()",
    "expect_err(",
)
PY_NONSTRING_DOMAIN_REFUSAL_TOKENS = (
    "FaultKind::Unsupported",
    ".fault .unsupported",
    "CaptureRefused",
    "unsupported",
    "Unsupported",
)
_PY_SAFE_CLI_FLAG_RE = re.compile(r"^-[IBEsSOPuvq]+$")
RUST_ASSERT_START_RE = re.compile(
    r"\bassert(?:_eq|_ne|_matches)?\s*!\s*([(\[{])"
)
RUST_ERR_CALL_RE = re.compile(
    r"\.(?:unwrap_err|expect_err)\s*\("
)


@dataclass(frozen=True)
class TripwireEntry:
    """Parsed metadata for one Phase-0 tripwire declaration."""

    bug_id: str
    issue: str
    owner: str
    added_date: str
    scope: str
    rationale: str
    regression_test: str
    layer: str  # "static_capture" | "runtime_semantics" | "trusted_comment"
    is_synthetic_selftest: bool
    source_path: str


@dataclass(frozen=True)
class PolicyReport:
    """Structured outcome returned by check modes."""

    ok: bool
    mode: str
    errors: tuple[str, ...]
    warnings: tuple[str, ...]
    active_production_tripwires: tuple[str, ...]
    synthetic_selftest_tripwires: tuple[str, ...]
    isolated_tripwire_surface: bool = False
    requires_full_semantic_review: bool = False

    def to_json(self) -> dict[str, object]:
        return asdict(self)


class RepoView(Protocol):
    """Read-only abstraction over working-tree or Git-object snapshots."""

    def read_text(self, rel_path: str) -> str | None: ...

    def is_regular_file(self, rel_path: str) -> tuple[bool, str | None]: ...

    def list_files(self, prefix: str, suffixes: tuple[str, ...]) -> list[str]: ...


class FilesystemRepoView:
    """RepoView reading checked-out files with symlink rejection."""

    def __init__(self, repo_root: Path) -> None:
        self.repo_root = repo_root

    def _check_ancestors(self, rel_path: str) -> tuple[Path | None, str | None]:
        parts = Path(rel_path).parts
        if ".." in parts or Path(rel_path).is_absolute():
            return None, f"path escapes repository boundary: {rel_path!r}"
        target = self.repo_root / rel_path
        if target.is_symlink():
            return None, f"symlink forbidden: {rel_path}"
        for ancestor in target.parents:
            if ancestor == self.repo_root:
                break
            if ancestor.is_symlink():
                return None, f"symlink ancestor component in {rel_path}"
        return target, None

    def is_regular_file(self, rel_path: str) -> tuple[bool, str | None]:
        target, err = self._check_ancestors(rel_path)
        if err is not None or target is None:
            return False, err
        if not target.is_file():
            return False, f"missing regular file: {rel_path}"
        return True, None

    def read_text(self, rel_path: str) -> str | None:
        ok, _ = self.is_regular_file(rel_path)
        if not ok:
            return None
        return (self.repo_root / rel_path).read_text(encoding="utf-8")

    def list_files(self, prefix: str, suffixes: tuple[str, ...]) -> list[str]:
        base = self.repo_root / prefix
        if not base.is_dir():
            return []
        found: list[str] = []
        for dirpath, dirnames, filenames in os.walk(base, followlinks=False):
            dirnames[:] = sorted(
                d for d in dirnames if d not in PRUNE_DIRS
            )
            cur = Path(dirpath)
            for dname in dirnames:
                sub = cur / dname
                if sub.is_symlink():
                    found.append(str(sub.relative_to(self.repo_root)))
            for fname in sorted(filenames):
                fpath = cur / fname
                rel = str(fpath.relative_to(self.repo_root))
                if fpath.is_symlink() or rel.endswith(suffixes):
                    found.append(rel)
        return sorted(found)


class GitRevRepoView:
    """RepoView reading immutable Git tree/blob objects for `rev`."""

    def __init__(self, repo_root: Path, rev: str) -> None:
        self.repo_root = repo_root
        self.rev = rev
        self._modes: dict[str, str] | None = None

    def _load_tree(self) -> dict[str, str]:
        if self._modes is not None:
            return self._modes
        _validate_git_ref(self.rev)
        raw = _git_output(
            self.repo_root,
            ["ls-tree", "-r", "-z", "--end-of-options", self.rev],
        )
        modes: dict[str, str] = {}
        for rec in raw.split("\0"):
            if not rec:
                continue
            meta, path = rec.split("\t", 1)
            mode = meta.split(" ", 1)[0]
            modes[path] = mode
        self._modes = modes
        return modes

    def is_regular_file(self, rel_path: str) -> tuple[bool, str | None]:
        parts = Path(rel_path).parts
        if ".." in parts or Path(rel_path).is_absolute():
            return False, f"path escapes repository boundary: {rel_path!r}"
        modes = self._load_tree()
        mode = modes.get(rel_path)
        if mode is None:
            return False, f"missing regular file at {self.rev}: {rel_path}"
        if mode in ("120000", "160000"):
            return False, f"forbidden symlink/submodule mode ({mode}): {rel_path}"
        if not mode.startswith("100"):
            return False, f"unexpected Git mode ({mode}): {rel_path}"
        return True, None

    def read_text(self, rel_path: str) -> str | None:
        ok, _ = self.is_regular_file(rel_path)
        if not ok:
            return None
        return _git_show_file(self.repo_root, self.rev, rel_path)

    def list_files(self, prefix: str, suffixes: tuple[str, ...]) -> list[str]:
        modes = self._load_tree()
        norm = prefix.rstrip("/") + "/"
        out: list[str] = []
        for path in sorted(modes):
            if not path.startswith(norm):
                continue
            mode = modes[path]
            if mode in ("120000", "160000") or path.endswith(suffixes):
                out.append(path)
        return out


@dataclass(frozen=True)
class RustScanResult:
    """Comment-stripped Rust source plus collected non-doc comments."""

    code_no_comments: str
    code_no_strings_or_comments: str
    non_doc_comments: tuple[str, ...]
    doc_comments: tuple[str, ...]
    literal_spans: tuple[tuple[int, int], ...]
    line_comment_spans: tuple[tuple[int, int], ...] = ()


def scan_rust_tokens(text: str) -> RustScanResult:
    """Lex Rust comments, strings, raw strings (`r#*"..."#*`), and chars.

    Produces both `code_no_comments` (keeping string literal contents intact so
    field values can be decoded) and `code_no_strings_or_comments` (replacing
    string/char literal payloads with spaces so tokens inside string literals
    cannot masquerade as macro definitions or `#[cfg(test)]` attributes).
    """
    no_comments: list[str] = []
    no_strings: list[str] = []
    non_doc_comments: list[str] = []
    doc_comments: list[str] = []
    literal_spans: list[tuple[int, int]] = []
    line_comment_spans: list[tuple[int, int]] = []

    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        # Line comment (`//...`).
        if ch == "/" and nxt == "/":
            end = text.find("\n", i)
            if end == -1:
                end = n
            comment = text[i:end]
            is_line_doc = (
                comment.startswith("///") and not comment.startswith("////")
            ) or comment.startswith("//!")
            if is_line_doc:
                doc_comments.append(comment)
            else:
                non_doc_comments.append(comment)
                line_comment_spans.append((i, end))
            blank = " " * (end - i)
            no_comments.append(blank)
            no_strings.append(blank)
            i = end
            continue

        # Nested block comment (`/* ... */`).
        if ch == "/" and nxt == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text[j : j + 2] == "/*":
                    depth += 1
                    j += 2
                elif text[j : j + 2] == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            comment = text[i:j]
            is_block_doc = (
                comment.startswith("/**")
                and not comment.startswith(("/**/", "/***"))
            ) or comment.startswith("/*!")
            if is_block_doc:
                doc_comments.append(comment)
            else:
                non_doc_comments.append(comment)
            blank = "".join("\n" if c == "\n" else " " for c in comment)
            no_comments.append(blank)
            no_strings.append(blank)
            i = j
            continue

        # Raw string literal: `r#"..."#`, `br#"..."#`, `cr#"..."#`.
        if ch in ("r", "b", "c") and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")
        ):
            raw_match = RAW_STRING_START_RE.match(text, i)
            if raw_match is not None:
                hashes = raw_match.group("hashes")
                start_body = raw_match.end()
                close_pat = '"' + hashes
                close_idx = text.find(close_pat, start_body)
                end = (close_idx + len(close_pat)) if close_idx != -1 else n
                lit = text[i:end]
                no_comments.append(lit)
                no_strings.append(
                    "".join("\n" if c == "\n" else " " for c in lit)
                )
                literal_spans.append((i, end))
                i = end
                continue

        # Byte/C string literal prefix (`b"..."` or `c"..."`).
        if (
            ch in ("b", "c")
            and nxt == '"'
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))
        ):
            j = i + 2
            while j < n:
                if text[j] == "\\" and j + 1 < n:
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            lit = text[i:j]
            no_comments.append(lit)
            no_strings.append(
                "".join("\n" if c == "\n" else " " for c in lit)
            )
            literal_spans.append((i, j))
            i = j
            continue

        # Byte char literal (`b'...'`).
        if (
            ch == "b"
            and nxt == "'"
            and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_"))
        ):
            j = i + 2
            if j < n and text[j] == "\\":
                j = min(n, j + 2)
                while j < n and text[j] != "'":
                    j += 1
                if j < n:
                    j += 1
            else:
                close = text.find("'", j)
                j = close + 1 if close != -1 else n
            lit = text[i:j]
            no_comments.append(lit)
            no_strings.append(" " * len(lit))
            literal_spans.append((i, j))
            i = j
            continue

        # Standard string literal `"..."`.
        if ch == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\" and j + 1 < n:
                    j += 2
                elif text[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            lit = text[i:j]
            no_comments.append(lit)
            no_strings.append(
                "".join("\n" if c == "\n" else " " for c in lit)
            )
            literal_spans.append((i, j))
            i = j
            continue

        # Character literal (`'x'`, `'\"'`, `'\x7f'`, `'\u{...}'`) vs lifetime.
        if ch == "'":
            char_match = CHAR_LIT_RE.match(text, i)
            if char_match is not None:
                lit = char_match.group(0)
                no_comments.append(lit)
                no_strings.append(" " * len(lit))
                literal_spans.append((i, i + len(lit)))
                i += len(lit)
                continue

        no_comments.append(ch)
        no_strings.append(ch)
        i += 1

    return RustScanResult(
        code_no_comments="".join(no_comments),
        code_no_strings_or_comments="".join(no_strings),
        non_doc_comments=tuple(non_doc_comments),
        doc_comments=tuple(doc_comments),
        literal_spans=tuple(literal_spans),
        line_comment_spans=tuple(line_comment_spans),
    )


def _find_matching_delimiter_in_code(code: str, open_idx: int) -> int | None:
    """Return index of matching `}`/`]`/`)` over already-lexed `code`."""
    open_ch = code[open_idx]
    close_map = {"{": "}", "(": ")", "[": "]"}
    close_ch = close_map[open_ch]
    depth = 0
    for idx in range(open_idx, len(code)):
        ch = code[idx]
        if ch == open_ch:
            depth += 1
        elif ch == close_ch:
            depth -= 1
            if depth == 0:
                return idx
    return None


def _split_top_level_commas(
    text: str, *, keep_literal_only: bool = False
) -> list[str]:
    """Split Rust slice body by top-level commas ignoring strings/brackets."""
    scanned = scan_rust_tokens(text)
    code = scanned.code_no_strings_or_comments
    non_empty_src = text if keep_literal_only else code
    items: list[str] = []
    depth = 0
    start = 0
    for idx, ch in enumerate(code):
        if ch in "{([":
            depth += 1
        elif ch in "})]":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            chunk = text[start:idx]
            if non_empty_src[start:idx].strip():
                items.append(chunk)
            start = idx + 1
    tail = text[start:]
    if non_empty_src[start:].strip():
        items.append(tail)
    return items


def _decode_rust_escapes(raw: str) -> str:
    """Decode Rust string escapes while preserving multi-byte UTF-8 text."""
    simple = {
        '"': '"',
        "'": "'",
        "\\": "\\",
        "n": "\n",
        "r": "\r",
        "t": "\t",
        "0": "\0",
    }

    def _sub(match: re.Match[str]) -> str:
        esc = match.group(1)
        if esc.startswith("\n"):
            return ""
        if esc in simple:
            return simple[esc]
        if esc.startswith("x") and len(esc) == 3:
            return chr(int(esc[1:], 16))
        if esc.startswith("u{") and esc.endswith("}"):
            try:
                return chr(int(esc[2:-1].replace("_", ""), 16))
            except ValueError:
                return match.group(0)
        return match.group(0)

    return re.sub(
        r"\\(\n[ \t]*|u\{[0-9a-fA-F_]+\}|x[0-9a-fA-F]{2}|.)", _sub, raw
    )


def _decode_single_string_literal(raw_expr: str) -> str | None:
    """Decode a single Rust string literal (`"..."` or `r(#*)"..."(#*)`)."""
    s = raw_expr.strip()
    if not s:
        return None
    raw_m = re.match(r'^r(#*)"', s)
    if raw_m is not None:
        close_pat = '"' + raw_m.group(1)
        end = s.find(close_pat, raw_m.end())
        if end == -1 or s[end + len(close_pat) :].strip():
            return None
        return s[raw_m.end() : end]
    if s[0] != '"':
        return None
    j = 1
    n = len(s)
    while j < n:
        if s[j] == "\\" and j + 1 < n:
            j += 2
        elif s[j] == '"':
            if s[j + 1 :].strip():
                return None
            return _decode_rust_escapes(s[1:j])
        else:
            j += 1
    return None


def _decode_single_char_literal(raw_expr: str) -> str | None:
    """Decode a single Rust char or byte-char literal (`'x'` / `b'x'`)."""
    s = raw_expr.strip()
    if s.startswith("b'") and len(s) >= 4:
        s = s[1:]
    if not (s.startswith("'") and s.endswith("'") and len(s) >= 3):
        return None
    inner = s[1:-1]
    if inner.startswith("\\"):
        dec = _decode_rust_escapes(inner)
        return dec if len(dec) == 1 else None
    return inner if len(inner) == 1 else None


def _split_top_level_plus(
    expr_nc: str, expr_ns: str | None = None
) -> list[str]:
    """Split a Rust expression at depth-0 binary `+` outside strings."""
    ns = (
        expr_ns
        if expr_ns is not None
        else scan_rust_tokens(expr_nc).code_no_strings_or_comments
    )
    parts: list[str] = []
    p_d = b_d = br_d = 0
    start = 0
    for idx_c, ch in enumerate(ns):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif ch == "+" and p_d == 0 and b_d == 0 and br_d == 0:
            parts.append(expr_nc[start:idx_c].strip())
            start = idx_c + 1
    if parts:
        parts.append(expr_nc[start:].strip())
        return parts
    return [expr_nc.strip()]


def _rust_format_parts(
    inner_nc: str,
    *,
    resolve_expr_fn: Callable[[str], str],
    resolve_ident_fn: Callable[[str], str],
) -> str:
    """Extract literal and identifier-resolved text from `format!`/`write!` args."""
    args = _split_top_level_commas(inner_nc, keep_literal_only=True)
    if not args:
        return ""
    named_args: set[str] = set()
    arg_exprs: list[str] = []
    for a in args[1:]:
        a_s = a.strip()
        if not a_s:
            continue
        eq_a = _find_rust_top_level_equal(
            scan_rust_tokens(a_s).code_no_strings_or_comments
        )
        if eq_a is not None:
            k_name = a_s[:eq_a].strip()
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", k_name):
                named_args.add(k_name)
            sub_a = a_s[eq_a + 1 :].strip()
        else:
            sub_a = a_s
        if sub_a:
            arg_exprs.append(sub_a)

    chunks: list[str] = []
    fmt_dec = _decode_single_string_literal(args[0])
    if fmt_dec is not None:
        i = 0
        n = len(fmt_dec)
        while i < n:
            if fmt_dec[i : i + 2] == "{{":
                chunks.append("{")
                i += 2
            elif fmt_dec[i : i + 2] == "}}":
                chunks.append("}")
                i += 2
            elif fmt_dec[i] == "{":
                end_b = fmt_dec.find("}", i + 1)
                if end_b == -1:
                    chunks.append(fmt_dec[i:])
                    break
                spec = fmt_dec[i + 1 : end_b].split(":", 1)[0].strip()
                if (
                    spec
                    and spec not in named_args
                    and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", spec)
                ):
                    chunks.append(resolve_ident_fn(spec))
                i = end_b + 1
            else:
                j = i + 1
                while j < n and fmt_dec[j] not in "{}":
                    j += 1
                chunks.append(fmt_dec[i:j])
                i = j
    else:
        chunks.append(resolve_expr_fn(args[0]))
    for sub in arg_exprs:
        chunks.append(resolve_expr_fn(sub))
    return "".join(chunks)


def _parse_key_value_fields(
    body: str, *, sep: str
) -> tuple[dict[str, tuple[str, str]], list[str]]:
    """Parse top-level comma-separated `key <sep> value` fields in source order."""
    fields: dict[str, tuple[str, str]] = {}
    errors: list[str] = []
    sep_pat = r":(?!:)" if sep == ":" else re.escape(sep)
    key_re = re.compile(rf"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*{sep_pat}(.*)$", re.DOTALL)
    for chunk in _split_top_level_commas(body):
        scanned = scan_rust_tokens(chunk)
        match = key_re.match(scanned.code_no_strings_or_comments)
        if match is None:
            errors.append(f"malformed field entry in PHASE0_TRIPWIRE: {chunk.strip()!r}")
            continue
        key = match.group(1)
        if key in fields:
            errors.append(f"duplicate field {key!r} in PHASE0_TRIPWIRE")
            continue
        val_start = match.start(2)
        fields[key] = (
            chunk[val_start:].strip(),
            scanned.code_no_strings_or_comments[val_start:].strip(),
        )
    return fields, errors


def _decode_string_field_from_fields(
    fields: dict[str, tuple[str, str]], key: str
) -> str:
    """Return decoded string value for `key` if present as a string literal."""
    pair = fields.get(key)
    if pair is None:
        return ""
    decoded = _decode_single_string_literal(pair[0])
    return decoded if decoded is not None else ""


def _find_rust_attributes(
    code_ns: str, code_no_comments: str | None = None
) -> list[tuple[int, int, str, bool]]:
    """Locate balanced `# [!][...]` attributes over comment-stripped code."""
    src = code_no_comments if code_no_comments is not None else code_ns
    attrs: list[tuple[int, int, str, bool]] = []
    for m in re.finditer(r"#\s*(!\s*)?\[", code_ns):
        open_br = m.end() - 1
        close_br = _find_matching_delimiter_in_code(code_ns, open_br)
        if close_br is None:
            continue
        attrs.append(
            (m.start(), close_br + 1, src[open_br + 1 : close_br], m.group(1) is not None)
        )
    return attrs


RUST_DECL_ITEM_RE = re.compile(
    r"^(?:pub\s*(?:\([^()]*\))?\s+)?"
    r"(?:default\s+(?:(?:async|unsafe|const|extern)\s+)*(?:fn|type|const)\b"
    r"|(?:(?:async|unsafe|const|extern(?:\s+\"[^\"]*\")?)\s+)*"
    r"(?:mod|fn|struct|enum|union|trait|impl|type|static|const|use|extern|macro_rules\s*!)\b)"
)
LEAN_CHAR_LIT_RE = re.compile(
    r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
)


def _find_rust_item_end_after_attr(code: str, start_idx: int) -> int | None:
    """Find item end (`;` / `{}` or comma-ended field/arm) without escaping blocks."""
    idx = start_idx
    n = len(code)
    # Skip stacked outer attributes `# [...]` preceding the item header.
    while idx < n:
        ws = re.match(r"\s*", code[idx:])
        if ws is not None:
            idx += ws.end()
        if idx < n and code[idx] == "#":
            attr_m = re.match(r"#\s*(?:!\s*)?\[", code[idx:])
            if attr_m is not None:
                close_br = _find_matching_delimiter_in_code(
                    code, idx + attr_m.end() - 1
                )
                if close_br is not None:
                    idx = close_br + 1
                    continue
        break

    item_head = code[idx:]
    is_decl_item = RUST_DECL_ITEM_RE.match(item_head) is not None
    is_let_stmt = (not is_decl_item) and (
        re.match(r"let\b", item_head) is not None
    )
    is_if_expr = (not is_decl_item) and (
        re.match(r"if\b", item_head) is not None
    )
    paren_depth = 0
    bracket_depth = 0
    angle_depth = 0
    while idx < n:
        ch = code[idx]
        two = code[idx : idx + 2]
        if ch == "(":
            paren_depth += 1
        elif ch == ")":
            if paren_depth == 0 and bracket_depth == 0:
                return idx
            if paren_depth > 0:
                paren_depth -= 1
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]":
            if paren_depth == 0 and bracket_depth == 0:
                return idx
            if bracket_depth > 0:
                bracket_depth -= 1
        elif not is_decl_item and paren_depth == 0 and bracket_depth == 0:
            if two == "=>":
                angle_depth = 0
                idx += 2
                continue
            if two in ("->", "<=", ">=") or (
                angle_depth == 0 and two in ("<<", ">>")
            ):
                idx += 2
                continue
            if ch == "<":
                angle_depth += 1
            elif ch == ">" and angle_depth > 0:
                angle_depth -= 1
            elif ch == "," and angle_depth == 0 and not is_let_stmt:
                return idx + 1
        if paren_depth == 0 and bracket_depth == 0:
            if ch == "}":
                return idx
            if ch == ";":
                return idx + 1
            if ch == "{":
                close_idx = _find_matching_delimiter_in_code(code, idx)
                if close_idx is None:
                    return None
                if is_let_stmt:
                    idx = close_idx + 1
                    continue
                end_pos = close_idx + 1
                if is_if_expr:
                    end_pos = _skip_rust_else_chain(code, close_idx)
                if not is_decl_item:
                    trail_m = re.match(r"\s*[;,]", code[end_pos:])
                    if trail_m is not None:
                        return end_pos + trail_m.end()
                return end_pos
        idx += 1
    return None


def _find_active_slice_span(code_ns: str) -> tuple[int, int, int] | None:
    """Find balanced `(body_start, body_end, semi_end)` of `ACTIVE_PHASE0_TRIPWIRES`."""
    matches = list(ACTIVE_SLICE_HEADER_RE.finditer(code_ns))
    if len(matches) != 1:
        return None
    m = matches[0]
    close_br = _find_matching_delimiter_in_code(code_ns, m.end() - 1)
    if close_br is None:
        return None
    semi_m = re.match(r"\s*;", code_ns[close_br + 1 :])
    if semi_m is None:
        return None
    return m.end(), close_br, close_br + 1 + semi_m.end()


def _split_rust_production_section(
    text: str, source_path: str, *, allow_multiple_cfg_test: bool = False
) -> tuple[str, list[str]]:
    """Strip balanced `#[cfg(test)]` items from Rust code fail-closed.

    For `tripwires.rs` (`allow_multiple_cfg_test=False`), enforces zero other
    `cfg`/`cfg_attr` attributes anywhere in production code and at most one
    trailing `#[cfg(test)] mod tests { ... }` at EOF so neither `cfg` splits nor
    decoy `#[cfg(test)]` blocks can hide active rules.
    """
    scanned = scan_rust_tokens(text)
    code = scanned.code_no_strings_or_comments
    attrs = _find_rust_attributes(code)

    errors: list[str] = []
    if not allow_multiple_cfg_test:
        cfg_test_attrs: list[tuple[int, int, str, bool]] = []
        for attr in attrs:
            a_start, a_end, inner, is_inner = attr
            if re.match(r"^\s*(?:cfg|cfg_attr)\b", inner):
                if (
                    not is_inner
                    and re.fullmatch(r"\s*cfg\s*\(\s*test\s*\)\s*", inner)
                ):
                    cfg_test_attrs.append(attr)
                else:
                    errors.append(
                        f"{source_path}: conditional attribute "
                        f"`{code[a_start:a_end].strip()}` forbidden in "
                        "tripwires.rs"
                    )
        if errors:
            return text, errors
        if not cfg_test_attrs:
            return text, []
        if len(cfg_test_attrs) > 1:
            errors.append(
                f"{source_path}: multiple #[cfg(test)] blocks forbidden in "
                "tripwires.rs"
            )
            return text, errors
        a_start, a_end, _inner, _is_inner = cfg_test_attrs[0]
        brace_idx = code.find("{", a_end)
        semi_idx = _find_rust_item_end_after_attr(code, a_end)
        if brace_idx == -1 or semi_idx is None or semi_idx <= brace_idx:
            errors.append(f"{source_path}: #[cfg(test)] must guard a block")
            return text, errors
        header = code[a_end:brace_idx]
        if re.fullmatch(
            r"\s*(?:pub(?:\([^)]*\))?\s+)?mod\s+[A-Za-z_][A-Za-z0-9_]*\s*",
            header,
        ) is None:
            errors.append(
                f"{source_path}: #[cfg(test)] in tripwires.rs may only guard "
                "a trailing mod block"
            )
            return text, errors
        if code[semi_idx:].strip():
            errors.append(
                f"{source_path}: production items cannot appear after #[cfg(test)]"
            )
            return text, errors
        return text[:a_start], []

    # General trusted/*.rs files: strip every balanced #[cfg(test)] /
    # #[cfg(all(test))] item block without stopping on `[u8; 4]` semicolons.
    cfg_test_spans: list[tuple[int, int]] = [
        (s, e)
        for s, e, inner, is_inner in attrs
        if not is_inner
        and re.fullmatch(
            r"\s*cfg\s*\(\s*(?:test|all\s*\(\s*test\s*\))\s*\)\s*", inner
        )
    ]
    if not cfg_test_spans:
        return text, []

    outer_attr_by_end = {
        a_end: (a_start, a_end, inner, is_inner)
        for a_start, a_end, inner, is_inner in attrs
        if not is_inner
    }
    chars = list(text)
    cursor = 0
    for a_start, a_end in cfg_test_spans:
        if a_start < cursor:
            continue
        lead_attr_start, _ = _collect_preceding_attrs(
            code, outer_attr_by_end, a_start
        )
        end = _find_rust_item_end_after_attr(code, a_end)
        if end is None:
            return text, [f"{source_path}: unterminated #[cfg(test)] item"]
        _blank_span(chars, max(cursor, lead_attr_start), end)
        cursor = end
    return "".join(chars), []


def _parse_tripwire_activation(
    act_raw: str,
) -> tuple[bool | None, str | None]:
    """Validate exact `TripwireActivation` expression without substring match."""
    scanned = scan_rust_tokens(act_raw)
    norm = re.sub(r"\s+", " ", scanned.code_no_comments).strip()
    if norm == "TripwireActivation::Always":
        return False, None
    selftest_m = re.fullmatch(
        r"TripwireActivation::SyntheticSelftestOnly\s*\{(.*)\}", norm, re.DOTALL
    )
    if selftest_m is None:
        return None, "unrecognized or non-literal TripwireActivation in PHASE0_TRIPWIRE! block"
    inner_fields, inner_errs = _parse_key_value_fields(selftest_m.group(1), sep=":")
    if inner_errs or set(inner_fields) != {"env_key", "env_value"}:
        return None, "malformed SyntheticSelftestOnly fields in PHASE0_TRIPWIRE! block"
    for fname in ("env_key", "env_value"):
        raw_v = inner_fields[fname][0]
        if (
            _decode_single_string_literal(raw_v) is None
            and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", raw_v) is None
        ):
            return None, f"non-literal {fname} in SyntheticSelftestOnly"
    return True, None


def parse_rust_tripwires(
    text: str, source_path: str = TRIPWIRES_REL
) -> tuple[list[TripwireEntry], list[str]]:
    """Parse `PHASE0_TRIPWIRE!` invocations in production Rust code."""
    prod_text, split_errs = _split_rust_production_section(
        text, source_path, allow_multiple_cfg_test=False
    )
    scanned = scan_rust_tokens(prod_text)
    errors: list[str] = list(split_errs)
    entries: list[TripwireEntry] = []

    # Reject raw `Phase0Tripwire { ... }` literals outside
    # `macro_rules! PHASE0_TRIPWIRE` while allowing the struct definition.
    code_ns = scanned.code_no_strings_or_comments
    macro_def_re = re.compile(r"\bmacro_rules\s*!\s*PHASE0_TRIPWIRE\b")
    macro_def_matches = list(macro_def_re.finditer(code_ns))
    if len(macro_def_matches) > 1:
        errors.append(
            f"{source_path}: multiple macro_rules! PHASE0_TRIPWIRE "
            "definitions forbidden"
        )
    macro_def_spans: list[tuple[int, int]] = []
    for m_def in macro_def_matches:
        m_delim = re.match(r"\s*([{\[(])", code_ns[m_def.end() :])
        if m_delim is not None:
            b_open = m_def.end() + m_delim.end() - 1
            b_close = _find_matching_delimiter_in_code(code_ns, b_open)
            if b_close is not None:
                macro_def_spans.append((m_def.start(), b_close + 1))

    struct_def_spans = {
        m_sd.end() - 1 for m_sd in STRUCT_DEF_RE.finditer(code_ns)
    }
    for sl_m in STRUCT_LITERAL_RE.finditer(code_ns):
        if sl_m.end() - 1 in struct_def_spans:
            continue
        in_macro_def = any(s <= sl_m.start() < e for s, e in macro_def_spans)
        if not in_macro_def:
            errors.append(
                f"{source_path}: direct Phase0Tripwire struct literal forbidden "
                "outside PHASE0_TRIPWIRE! macro"
            )

    # Enforce commented-out/disabled stub bans inside ACTIVE_PHASE0_TRIPWIRES
    # and across non-doc comments in production code.
    active_span = _find_active_slice_span(code_ns)
    active_body_span: tuple[int, int] | None = None
    if active_span is None:
        errors.append(
            f"{source_path}: expected exactly one unconditional "
            "ACTIVE_PHASE0_TRIPWIRES slice"
        )
    else:
        raw_start, raw_end, _semi_end = active_span
        active_body_span = (raw_start, raw_end)
        start_count = prod_text.count(MUTABLE_START_MARKER)
        end_count = prod_text.count(MUTABLE_END_MARKER)
        if start_count != 1 or end_count != 1:
            errors.append(
                f"{source_path}: expected exactly one `{MUTABLE_START_MARKER}` "
                f"and one `{MUTABLE_END_MARKER}`"
            )
        else:
            ms_idx = prod_text.index(MUTABLE_START_MARKER)
            me_idx = prod_text.index(MUTABLE_END_MARKER)
            if not (ms_idx < raw_start and raw_end <= me_idx):
                errors.append(
                    f"{source_path}: ACTIVE_PHASE0_TRIPWIRES must stay inside "
                    "the demarcated Phase-0 mutable registry"
                )
        raw_slice_body = prod_text[raw_start:raw_end]
        raw_slice_scanned = scan_rust_tokens(raw_slice_body)
        for slice_comment in (
            *raw_slice_scanned.non_doc_comments,
            *raw_slice_scanned.doc_comments,
        ):
            if (
                "PHASE0_TRIPWIRE" in slice_comment
                or "bug_id" in slice_comment
                or BUG_ID_INNER_RE.search(slice_comment) is not None
            ):
                first_line = slice_comment.strip().splitlines()[0]
                errors.append(
                    f"{source_path}: commented-out tripwire stub inside "
                    f"ACTIVE_PHASE0_TRIPWIRES: {first_line}"
                )
        for item_chunk in _split_top_level_commas(raw_slice_body):
            item_code = scan_rust_tokens(item_chunk).code_no_strings_or_comments.strip()
            if re.search(r"#\s*\[", item_code):
                errors.append(
                    f"{source_path}: attributes forbidden on ACTIVE_PHASE0_TRIPWIRES element"
                )
            item_start = re.match(r"^PHASE0_TRIPWIRE\s*!\s*([{\[(])", item_code)
            item_valid = False
            if item_start is not None:
                item_close = _find_matching_delimiter_in_code(
                    item_code, item_start.end() - 1
                )
                item_valid = (
                    item_close is not None
                    and not item_code[item_close + 1 :].strip()
                )
            if not item_valid:
                errors.append(
                    f"{source_path}: element in ACTIVE_PHASE0_TRIPWIRES must "
                    "invoke PHASE0_TRIPWIRE!"
                )

    for comment in scanned.non_doc_comments:
        if (
            re.search(r"\bPHASE0_TRIPWIRE\s*(?:!\s*[{\[(]|\()", comment)
            or re.search(r"\bbug_id\s*[:=]", comment)
            or BUG_ID_INNER_RE.search(comment) is not None
        ):
            errors.append(
                f"{source_path}: commented-out PHASE0_TRIPWIRE stub in "
                f"production code: {comment.strip().splitlines()[0]}"
            )
    doc_stub_field_re = re.compile(
        r"\b(?:bug_id|issue|owner|added_date|regression_test|activation|predicate)\s*[:=]"
    )
    for comment in scanned.doc_comments:
        if (
            re.search(r"\bbug_id\s*[:=]", comment)
            or BUG_ID_INNER_RE.search(comment) is not None
            or (
                re.search(r"\bPHASE0_TRIPWIRE\s*(?:!\s*[{\[(]|\()", comment)
                and doc_stub_field_re.search(comment) is not None
            )
        ):
            errors.append(
                f"{source_path}: commented-out PHASE0_TRIPWIRE stub in "
                f"doc comment: {comment.strip().splitlines()[0]}"
            )
    for doc_m in re.finditer(r"#\s*!?\s*\[\s*doc\s*=", scanned.code_no_strings_or_comments):
        b_open = scanned.code_no_strings_or_comments.find("[", doc_m.start())
        b_close = (
            _find_matching_delimiter_in_code(
                scanned.code_no_strings_or_comments, b_open
            )
            if b_open != -1
            else None
        )
        if b_close is None:
            continue
        doc_attr = scanned.code_no_comments[b_open : b_close + 1]
        if (
            re.search(r"\bbug_id\s*[:=]", doc_attr)
            or BUG_ID_INNER_RE.search(doc_attr) is not None
            or (
                re.search(r"\bPHASE0_TRIPWIRE\s*(?:!\s*[{\[(]|\()", doc_attr)
                and doc_stub_field_re.search(doc_attr) is not None
            )
        ):
            errors.append(
                f"{source_path}: #[doc = ...] attribute contains commented-out "
                "PHASE0_TRIPWIRE stub in production code"
            )

    if re.search(
        r"\benabled\s*:\s*false\b|TripwireActivation::Disabled",
        scanned.code_no_strings_or_comments,
    ):
        errors.append(
            f"{source_path}: disabled Phase-0 tripwires are forbidden; delete "
            "resolved tripwires cleanly in Phase 1"
        )

    seen_selftest_consts: set[str] = set()
    for match in MACRO_CALL_RE.finditer(scanned.code_no_strings_or_comments):
        in_macro_def = any(s <= match.start() < e for s, e in macro_def_spans)
        if in_macro_def:
            continue
        open_idx = match.end() - 1
        close_idx = _find_matching_delimiter_in_code(code_ns, open_idx)
        if close_idx is None:
            errors.append(f"{source_path}: unterminated PHASE0_TRIPWIRE! block")
            continue
        block = scanned.code_no_comments[open_idx + 1 : close_idx]
        fields, field_errs = _parse_key_value_fields(block, sep=":")
        for fe in field_errs:
            errors.append(f"{source_path}: {fe}")

        act_pair = fields.get("activation")
        if act_pair is None:
            is_selftest: bool | None = None
            errors.append(
                f"{source_path}: missing activation in PHASE0_TRIPWIRE! block"
            )
        else:
            is_selftest, act_err = _parse_tripwire_activation(act_pair[0])
            if act_err is not None:
                errors.append(f"{source_path}: {act_err}")

        bug_id = _decode_string_field_from_fields(fields, "bug_id")
        issue = _decode_string_field_from_fields(fields, "issue")
        in_active_slice = (
            active_body_span is not None
            and match.start() >= active_body_span[0]
            and close_idx < active_body_span[1]
        )
        if in_active_slice:
            if is_selftest:
                errors.append(
                    f"{source_path}: SyntheticSelftestOnly tripwire must not "
                    "live inside ACTIVE_PHASE0_TRIPWIRES"
                )
        else:
            prefix = code_ns[max(0, match.start() - 160) : match.start()]
            decl_m = SYNTHETIC_DEMO_DECL_RE.search(prefix)
            const_name = decl_m.group(1) if decl_m is not None else ""
            has_semi = re.match(r"\s*;", code_ns[close_idx + 1 :]) is not None
            if (
                decl_m is None
                or is_selftest is not True
                or SYNTHETIC_SELFTEST_ALLOWED.get(const_name) != bug_id
                or not has_semi
                or const_name in seen_selftest_consts
            ):
                errors.append(
                    f"{source_path}: production PHASE0_TRIPWIRE! outside "
                    "ACTIVE_PHASE0_TRIPWIRES is forbidden (only "
                    "SYNTHETIC_DEMO[_CRATE]_TRIPWIRE selftest constants may "
                    "appear outside the slice)"
                )
            else:
                seen_selftest_consts.add(const_name)
        entries.append(
            TripwireEntry(
                bug_id=bug_id,
                issue=issue,
                owner=_decode_string_field_from_fields(fields, "owner"),
                added_date=_decode_string_field_from_fields(fields, "added_date"),
                scope=_decode_string_field_from_fields(fields, "scope"),
                rationale=_decode_string_field_from_fields(fields, "rationale"),
                regression_test=_decode_string_field_from_fields(
                    fields, "regression_test"
                ),
                layer="static_capture",
                is_synthetic_selftest=bool(is_selftest),
                source_path=source_path,
            )
        )
    errors.extend(
        _check_tripwires_unreferenced_helpers(
            prod_text, code_ns, active_body_span, source_path
        )
    )
    return entries, errors


TRIPWIRES_CORE_API_FNS = frozenset(
    {
        "check_crate",
        "check_mir_body",
        "evaluate_crate_tripwires",
        "evaluate_body_tripwires",
    }
)
TRIPWIRES_TOP_ITEM_RE = re.compile(
    r"^(?:pub(?:\s*\([^()]*\))?\s+)?"
    r"(?:(?:async|unsafe|const|extern(?:\s+\"[^\"]*\")?)\s+)*"
    r"(?P<kind>fn|const|static|struct|enum|type|trait|mod|impl|macro_rules\s*!)"
    r"(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*))?\b"
)


def _check_tripwires_unreferenced_helpers(
    prod_text: str,
    code_ns: str,
    active_body_span: tuple[int, int] | None,
    source_path: str,
) -> list[str]:
    """Reject unreferenced/dead non-test helper functions/items in tripwires.rs."""
    if active_body_span is None:
        return []
    ms_idx = (
        prod_text.index(MUTABLE_START_MARKER)
        if prod_text.count(MUTABLE_START_MARKER) == 1
        else -1
    )
    me_idx = (
        prod_text.index(MUTABLE_END_MARKER)
        if prod_text.count(MUTABLE_END_MARKER) == 1
        else -1
    )

    n = len(code_ns)
    idx = 0
    # Each entry: (kind, name, start, end, body_ns, in_mutable)
    top_items: list[tuple[str, str, int, int, str, bool]] = []
    mut_impls: list[tuple[str, str, list[str]]] = []
    root_bodies: list[str] = [code_ns[active_body_span[0] : active_body_span[1]]]

    while idx < n:
        while idx < n and code_ns[idx].isspace():
            idx += 1
        if idx >= n:
            break
        if code_ns[idx] == "#":
            attr_m = re.match(r"#\s*(?:!\s*)?\[", code_ns[idx:])
            if attr_m is not None:
                close_a = _find_matching_delimiter_in_code(
                    code_ns, idx + attr_m.end() - 1
                )
                if close_a is not None:
                    idx = close_a + 1
                    continue
        item_m = TRIPWIRES_TOP_ITEM_RE.match(code_ns[idx:])
        if item_m is None:
            # Skip non-item statement (e.g. `use ...;`) to next `;` / block end.
            end_skip = _find_rust_item_end_after_attr(code_ns, idx)
            if end_skip is None or end_skip <= idx:
                idx += 1
            else:
                idx = end_skip
            continue

        raw_kind = re.sub(r"\s+", "", item_m.group("kind"))
        name = item_m.group("name") or ""
        if raw_kind == "macro_rules!":
            after_pos = idx + item_m.end()
            if not name:
                m_name = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", code_ns[after_pos:])
                if m_name is not None:
                    name = m_name.group(1)
                    after_pos += m_name.end()
            delim_m = re.match(r"\s*([{\[(])", code_ns[after_pos:])
            if delim_m is not None:
                b_open = after_pos + delim_m.end() - 1
                b_close = _find_matching_delimiter_in_code(code_ns, b_open)
                item_end = (b_close + 1) if b_close is not None else n
            else:
                item_end = _find_rust_item_end_after_attr(code_ns, idx) or n
        else:
            item_end = _find_rust_item_end_after_attr(code_ns, idx) or n
        if item_end <= idx:
            idx += 1
            continue

        in_mutable = ms_idx != -1 and me_idx != -1 and ms_idx <= idx < me_idx
        item_ns = code_ns[idx:item_end]
        if raw_kind == "impl":
            brace_pos = item_ns.find("{")
            hdr_ns = item_ns[:brace_pos] if brace_pos != -1 else item_ns
            body_ns = item_ns[brace_pos:] if brace_pos != -1 else ""
            if not in_mutable:
                root_bodies.append(item_ns)
            else:
                methods = re.findall(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\b", body_ns)
                mut_impls.append((hdr_ns, body_ns, methods))
        elif name:
            # Slice body after the declared name so self-mentions in the header
            # are excluded; BFS starts strictly from roots anyway.
            name_end = item_m.end("name") if item_m.end("name") != -1 else item_m.end()
            body_ns = item_ns[name_end:]
            top_items.append((raw_kind, name, idx, item_end, body_ns, in_mutable))
            if (
                (raw_kind == "fn" and name in TRIPWIRES_CORE_API_FNS)
                or (
                    raw_kind == "const"
                    and not in_mutable
                    and name.startswith("SYNTHETIC_DEMO_")
                )
            ):
                root_bodies.append(body_ns)
        idx = item_end

    items_by_name: dict[str, list[str]] = {}
    for _kind, name, _s, _e, body_ns, _in_mut in top_items:
        items_by_name.setdefault(name, []).append(body_ns)

    reachable: set[str] = set(TRIPWIRES_CORE_API_FNS) | {"ACTIVE_PHASE0_TRIPWIRES"}
    queue: list[str] = list(root_bodies)
    seen_impls: set[int] = set()

    while queue:
        chunk = queue.pop()
        for ident in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", chunk):
            if ident in reachable:
                continue
            if ident in items_by_name:
                reachable.add(ident)
                queue.extend(items_by_name[ident])
        for impl_idx, (hdr_ns, body_ns, methods) in enumerate(mut_impls):
            if impl_idx in seen_impls:
                continue
            hdr_idents = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", hdr_ns))
            if hdr_idents & reachable or any(m in reachable for m in methods):
                seen_impls.add(impl_idx)
                reachable.update(methods)
                queue.append(body_ns)

    errors: list[str] = []
    for kind, name, _s, _e, _body, in_mutable in top_items:
        if name == "ACTIVE_PHASE0_TRIPWIRES":
            continue
        if kind == "fn" and name not in reachable:
            errors.append(
                f"{source_path}: unreferenced non-test helper function "
                f"`{name}` must be removed (not reachable from "
                "ACTIVE_PHASE0_TRIPWIRES or tripwire harness entrypoints)"
            )
        elif in_mutable and kind != "fn" and name not in reachable:
            errors.append(
                f"{source_path}: unreferenced Phase-0 mutable-registry item "
                f"`{name}` must be removed (not reachable from "
                "ACTIVE_PHASE0_TRIPWIRES)"
            )
    for impl_idx, (_hdr_ns, _body_ns, methods) in enumerate(mut_impls):
        if impl_idx not in seen_impls:
            label = ", ".join(methods) if methods else "impl"
            errors.append(
                f"{source_path}: unreferenced Phase-0 mutable-registry impl "
                f"`{label}` must be removed"
            )
    return errors


def _mask_non_comments(text: str, *, is_rust: bool) -> str:
    """Keep only top-level line comments at source offsets, blanking blocks."""
    if is_rust:
        scanned = scan_rust_tokens(text)
        chars = [
            ch if ch in ("\n", "\r") else " "
            for ch in text
        ]
        for start, end in scanned.line_comment_spans:
            chars[start:end] = list(text[start:end])
        return "".join(chars)

    # Lean line comments (`--`) outside `"..."` strings and `/- ... -/` blocks.
    chars: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            if ch == "\\" and i + 1 < n:
                chars.extend("\n" if c == "\n" else " " for c in text[i : i + 2])
                i += 2
                continue
            if ch == '"':
                in_string = False
            chars.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                chars.extend([" ", " "])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                chars.extend([" ", " "])
                i += 2
                continue
            chars.append("\n" if ch in ("\n", "\r") else " ")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            chars.extend([" ", " "])
            i += 2
            continue
        if ch == "-" and nxt == "-":
            end = text.find("\n", i)
            if end == -1:
                end = n
            chars.extend(text[i:end])
            i = end
            continue
        if ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!")
        ):
            char_m = LEAN_CHAR_LIT_RE.match(text, i)
            if char_m is not None:
                lit = char_m.group(0)
                chars.extend(" " * len(lit))
                i += len(lit)
                continue
        if ch == '"':
            in_string = True
        chars.append("\n" if ch in ("\n", "\r") else " ")
        i += 1
    return "".join(chars)


def _find_comment_tripwire_spans(
    text: str, source_path: str
) -> tuple[list[tuple[int, int, str]], list[str]]:
    """Extract `(start, end, body)` for top-level line-comment tripwires."""
    is_rust = source_path.endswith(".rs")
    masked = _mask_non_comments(text, is_rust=is_rust)
    start_re = (
        RUST_COMMENT_TRIPWIRE_START_RE
        if is_rust
        else LEAN_COMMENT_TRIPWIRE_START_RE
    )
    spans: list[tuple[int, int, str]] = []
    errors: list[str] = []
    n = len(masked)
    cursor = 0
    while cursor < n:
        match = start_re.search(masked, cursor)
        if match is None:
            break
        prefix = match.group(1)
        idx = match.end()
        depth = 1
        chars: list[str] = []
        in_str = False
        raw_close: str | None = None
        terminated = False
        while idx < n:
            ch = masked[idx]
            if raw_close is not None:
                if masked.startswith(raw_close, idx):
                    chars.append(raw_close)
                    idx += len(raw_close)
                    raw_close = None
                    continue
                chars.append(ch)
                idx += 1
                continue
            if in_str:
                if ch == "\\" and idx + 1 < n:
                    chars.append(masked[idx : idx + 2])
                    idx += 2
                    continue
                if ch == '"':
                    in_str = False
                chars.append(ch)
                idx += 1
                continue
            if ch == "\n":
                chars.append(ch)
                idx += 1
                cont = re.match(rf"[ \t]*{re.escape(prefix)}[ \t]?", masked[idx:])
                if cont is None:
                    break
                idx += cont.end()
                continue
            raw_m = RAW_STRING_START_RE.match(masked, idx)
            if raw_m is not None and (
                idx == 0 or not (masked[idx - 1].isalnum() or masked[idx - 1] == "_")
            ):
                raw_close = '"' + raw_m.group("hashes")
                chars.append(raw_m.group(0))
                idx = raw_m.end()
                continue
            if ch == '"':
                in_str = True
                chars.append(ch)
                idx += 1
                continue
            if ch == "(":
                depth += 1
                chars.append(ch)
                idx += 1
                continue
            if ch == ")":
                depth -= 1
                idx += 1
                if depth == 0:
                    terminated = True
                    break
                chars.append(ch)
                continue
            chars.append(ch)
            idx += 1
        if not terminated:
            errors.append(
                f"{source_path}: unterminated {prefix} PHASE0_TRIPWIRE(...) annotation"
            )
            cursor = idx
        else:
            spans.append((match.start(), idx, "".join(chars)))
            cursor = idx
    return spans, errors


def _parse_comment_tripwires_with_spans(
    text: str, source_path: str
) -> tuple[list[TripwireEntry], list[tuple[int, int]], list[str]]:
    """Parse comment markers along with their source `(start, end)` offsets."""
    entries: list[TripwireEntry] = []
    spans, errors = _find_comment_tripwire_spans(text, source_path)
    layer = (
        "runtime_semantics"
        if _is_lean_mir_semantics_rel(source_path)
        else "trusted_comment"
    )
    for _s, _e, body in spans:
        fields, field_errs = _parse_key_value_fields(body, sep="=")
        for fe in field_errs:
            errors.append(f"{source_path}: {fe}")
        entries.append(
            TripwireEntry(
                bug_id=_decode_string_field_from_fields(fields, "bug_id"),
                issue=_decode_string_field_from_fields(fields, "issue"),
                owner=_decode_string_field_from_fields(fields, "owner"),
                added_date=_decode_string_field_from_fields(fields, "added_date"),
                scope=_decode_string_field_from_fields(fields, "scope"),
                rationale=_decode_string_field_from_fields(fields, "rationale"),
                regression_test=_decode_string_field_from_fields(
                    fields, "regression_test"
                ),
                layer=layer,
                is_synthetic_selftest=False,
                source_path=source_path,
            )
        )
    return entries, [(s, e) for s, e, _b in spans], errors


def _check_trusted_comment_cfg_guards(
    prod_text: str,
    rel: str,
    comment_spans: list[tuple[int, int]],
    *,
    raw_text: str | None = None,
) -> list[str]:
    """Reject trusted Rust comment tripwires on or inside disabled `cfg`."""
    if not comment_spans:
        return []
    src_text = raw_text if raw_text is not None else prod_text
    scanned = scan_rust_tokens(src_text)
    code_ns = scanned.code_no_strings_or_comments
    all_attrs = _find_rust_attributes(code_ns, scanned.code_no_comments)
    outer_attr_by_end = {
        a_end: (a_start, a_end, inner, is_inner)
        for a_start, a_end, inner, is_inner in all_attrs
        if not is_inner
    }
    errors: list[str] = []
    for a_start, a_end, inner, is_inner in all_attrs:
        if not re.match(r"^\s*(?:cfg|cfg_attr)\b", inner):
            continue
        reason = _is_disabling_cfg_attr(
            inner, allow_cfg_test=True, is_inner=is_inner
        )
        is_outer_cfg_test = False
        if reason is None and re.fullmatch(
            r"\s*cfg\s*\(\s*(?:test|all\s*\(\s*test\s*\))\s*\)\s*", inner
        ):
            bang = "!" if is_inner else ""
            norm_in = re.sub(r"\s+", " ", inner).strip()
            reason = f"disabled via #{bang}[{norm_in}]"
            is_outer_cfg_test = not is_inner
        if reason is None:
            continue
        lead_attr_start = a_start
        if is_inner:
            encl = _find_rust_enclosing_delimiters(code_ns, a_start)
            if not encl:
                span_start, span_end = 0, len(src_text)
            else:
                delim, open_pos = encl[-1]
                if delim != "{":
                    continue
                close_pos = _find_matching_delimiter_in_code(code_ns, open_pos)
                span_start = open_pos
                span_end = (
                    (close_pos + 1) if close_pos is not None else len(src_text)
                )
        else:
            lead_attr_start, _ = _collect_preceding_attrs(
                code_ns, outer_attr_by_end, a_start
            )
            lead_start = len(code_ns[:lead_attr_start].rstrip())
            item_end = _find_rust_item_end_after_attr(code_ns, a_end)
            if item_end is None:
                item_end = len(src_text)
            span_start, span_end = lead_start, item_end
        matched = False
        for c_start, c_end in comment_spans:
            if not (span_start <= c_start < span_end):
                continue
            if is_outer_cfg_test and c_end <= lead_attr_start:
                gap_lines = src_text[c_end:lead_attr_start].split("\n")
                if len(gap_lines) >= 3 and any(
                    not ln.strip() for ln in gap_lines[1:-1]
                ):
                    continue
            matched = True
            break
        if matched:
            errors.append(
                f"{rel}: trusted comment PHASE0_TRIPWIRE inside {reason}"
            )
    return errors


LEAN_UNSUPPORTED_GUARD_RE = re.compile(
    r"(?:(?:\bStepResult)?\.fault|\bStepResult\.fault)\s+(?:FaultKind\.|\.)unsupported\b"
    r"|(?:(?:\bExcept)?\.error|\bExcept\.error)\s+(?:FaultKind\.|\.)unsupported\b"
    r"|\bthrow\s+(?:FaultKind\.|\.)unsupported\b"
)
LEAN_NON_GUARD_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*"
    r"(?:theorem|lemma|axiom|structure|inductive|class|instance|namespace"
    r"|section|end|import|open|variable|universe|set_option|attribute|macro"
    r"|syntax|notation|elab|deriving)\b"
)
LEAN_DEF_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:def|abbrev)\b"
)


def _strip_lean_comments_and_strings(text: str) -> str:
    """Replace Lean comments, strings, and char literals with spaces, keeping newlines."""
    chars: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if in_string:
            if ch == "\\" and i + 1 < n:
                chars.extend("\n" if c == "\n" else " " for c in text[i : i + 2])
                i += 2
                continue
            if ch == '"':
                in_string = False
            chars.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                chars.extend([" ", " "])
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                chars.extend([" ", " "])
                i += 2
                continue
            chars.append("\n" if ch in ("\n", "\r") else " ")
            i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            chars.extend([" ", " "])
            i += 2
            continue
        if ch == "-" and nxt == "-":
            end = text.find("\n", i)
            if end == -1:
                end = n
            chars.extend(" " * (end - i))
            i = end
            continue
        if ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'!")
        ):
            char_m = LEAN_CHAR_LIT_RE.match(text, i)
            if char_m is not None:
                lit = char_m.group(0)
                chars.extend(" " * len(lit))
                i += len(lit)
                continue
        if ch == '"':
            in_string = True
            chars.append(" ")
            i += 1
            continue
        chars.append(ch)
        i += 1
    return "".join(chars)


LEAN_CANARY_FIXTURES_REL = f"{MIR_SEMANTICS_DIR_REL}/CanaryFixtures.lean"
LEAN_MIR_SEMANTICS_ROOT_NAMES = frozenset(
    {
        "initState",
        "initStateV2",
        "evalStep",
        "evalStepV2",
        "evalStepV2Choice",
        "forceAllocation",
        "Step",
        "StepV2",
        "Reaches",
        "ReachesV2",
        "ReachesAtChoices",
        "ReachesResult",
        "ReachesResultV2",
        "ReachesResultAtChoices",
        "WellFormed",
        "WellFormedV2",
        "Behavior",
        "BehaviorV2",
        "BehaviorAtChoices",
        "Diverges",
        "DivergesV2",
        "DivergesAtChoices",
        "SatisfiesPost",
        "SatisfiesPostV2",
        "BodyStaticAdmitted",
        "BodyStaticAdmittedV2",
        "BodyVerified",
        "BodyVerifiedV2",
        "ProgramVerified",
        "ProgramVerifiedV2",
        "CrateTheorem",
        "CrateTheoremV2",
        "UnitTheorem",
        "UnitTheoremV2",
        "BodySatisfiesSafeContractV2",
        "BodyContractSatisfied",
        "ContractEntriesSatisfied",
        "ContractSpecs",
        "ValidPrefixAtChoices",
        "EffectMaskV2.noAbort",
    }
)
LEAN_MIR_SEMANTICS_ROOTS = frozenset(
    f"Trusted.MirSemantics.{name}" for name in LEAN_MIR_SEMANTICS_ROOT_NAMES
)
LEAN_ANY_DECL_START_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*"
    r"(?P<mods>(?:(?:public|private|protected|noncomputable|partial|unsafe|local|scoped)\s+)*)"
    r"(?P<kind>def|abbrev|inductive|structure|theorem|lemma|axiom|instance|class)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_.'?]*)"
)
LEAN_IDENT_RE = re.compile(r"(?<![A-Za-z0-9_'?])[A-Za-z_][A-Za-z0-9_'?]*")
LEAN_DOTTED_IDENT_RE = re.compile(
    r"(?<![A-Za-z0-9_'?.])([A-Za-z_][A-Za-z0-9_'?]*(?:\.[A-Za-z_][A-Za-z0-9_'?]*)*)"
)
LEAN_DOT_PROJ_RE = re.compile(r"\.([A-Za-z_][A-Za-z0-9_'?]*)")
LEAN_DEAD_IF_GUARD_RE = re.compile(
    r"^\s*if\s+(?:\(*\s*(?:false|Bool\.false|!\s*true|¬\s*true)\s*\)*)\s+then\b"
)


@dataclass(frozen=True)
class _LeanMirDecl:
    decl_id: tuple[str, str, int]
    rel: str
    name: str
    fq_name: str
    namespace: tuple[str, ...]
    open_namespaces: tuple[str, ...]
    kind: str
    is_private: bool
    start_line: int
    end_line: int
    body_lines: tuple[str, ...]
    live_body: str


@dataclass(frozen=True)
class _LeanMirGraph:
    decls_by_file: dict[str, tuple[_LeanMirDecl, ...]]
    reachable_decl_ids: frozenset[tuple[str, str, int]]
    included_files: frozenset[str]


def _split_lean_top_level_semicolons(line: str) -> list[str]:
    """Split a top-level Lean command line on depth-0 `;` separators."""
    if ";" not in line:
        return [line]
    parts: list[str] = []
    p_d = b_d = br_d = 0
    start = 0
    for idx, ch in enumerate(line):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif ch == ";" and p_d == 0 and b_d == 0 and br_d == 0:
            parts.append(line[start:idx])
            start = idx + 1
    parts.append(line[start:])
    return parts


def _lean_live_body_for_refs(body_lines: list[str]) -> str:
    """Filter out discarded `let _` / unused `let` / `if false then` lines."""
    if not body_lines:
        return ""
    # Replace single-line `if false then <then> else <else>` with `<else>`.
    cleaned: list[str] = []
    for ln in body_lines:
        ln_c = re.sub(
            r"\bif\s+(?:\(*\s*(?:false|Bool\.false|!\s*true|¬\s*true)\s*\)*)\s+then\b[^;\n]*?\belse\b",
            " ",
            ln,
        )
        cleaned.append(ln_c)

    # Identify dead/discarded local `let` bindings (`let _ := ...` or
    # `let v := ...` where `v` is never referenced in subsequent lines).
    kept: list[str] = []
    n = len(cleaned)
    i = 0
    while i < n:
        ln = cleaned[i]
        m = re.match(
            r"^(\s*)(?:let|have)\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_'?]*)(?![A-Za-z0-9_'?])[^:\n]*(?::[^:\n]*)?:=",
            ln,
        )
        if m is not None:
            bind_indent = len(m.group(1))
            var_name = m.group(2)
            # Collect multi-line continuation of this binding RHS.
            end_j = i + 1
            while end_j < n:
                nxt = cleaned[end_j]
                if not nxt.strip():
                    end_j += 1
                    continue
                if len(nxt) - len(nxt.lstrip()) > bind_indent:
                    end_j += 1
                    continue
                break
            tail_text = "\n".join(cleaned[end_j:])
            is_discarded = var_name == "_" or var_name.startswith("_")
            if not is_discarded:
                tail_idents = set(LEAN_IDENT_RE.findall(tail_text))
                is_discarded = var_name not in tail_idents
            if is_discarded:
                i = end_j
                continue
        kept.append(ln)
        i += 1
    return "\n".join(kept)


def _parse_lean_file_decls(text: str, rel: str) -> list[_LeanMirDecl]:
    """Parse runtime `def`/`abbrev`/`inductive`/`structure` decls with namespaces."""
    stripped = _strip_lean_comments_and_strings(text)
    lines = stripped.splitlines()
    decls: list[_LeanMirDecl] = []
    # Scope stack entries: `(kind, name_or_none, opened_namespaces)` where
    # `kind` is `"ns"`, `"section"`, or `"mutual"`.
    scope_stack: list[tuple[str, str | None, list[str]]] = []
    file_opens: list[str] = []
    cur_kind: str | None = None
    cur_name: str | None = None
    cur_fq_name: str | None = None
    cur_ns_snap: tuple[str, ...] = ()
    cur_opens_snap: tuple[str, ...] = ()
    cur_priv = False
    cur_start = 0
    cur_body: list[str] = []

    def _active_ns() -> tuple[str, ...]:
        return tuple(
            name for kind, name, _ops in scope_stack if kind == "ns" and name
        )

    def _active_opens() -> tuple[str, ...]:
        out: list[str] = list(file_opens)
        for _kind, _name, ops in scope_stack:
            out.extend(ops)
        return tuple(out)

    def _in_mutual() -> bool:
        return any(kind == "mutual" for kind, _name, _ops in scope_stack)

    def _qualify_name(raw_name: str, ns_parts: tuple[str, ...]) -> str:
        if raw_name.startswith("_root_."):
            return raw_name[len("_root_.") :]
        if ns_parts:
            return ".".join([*ns_parts, raw_name])
        return raw_name

    def _flush(end_idx: int) -> None:
        nonlocal cur_kind, cur_name, cur_fq_name, cur_ns_snap, cur_opens_snap
        nonlocal cur_priv, cur_start, cur_body
        if cur_name is not None and cur_fq_name is not None and cur_kind in (
            "def",
            "abbrev",
            "inductive",
            "structure",
        ):
            live_b = _lean_live_body_for_refs(cur_body)
            decls.append(
                _LeanMirDecl(
                    decl_id=(rel, cur_fq_name, cur_start),
                    rel=rel,
                    name=cur_name,
                    fq_name=cur_fq_name,
                    namespace=cur_ns_snap,
                    open_namespaces=cur_opens_snap,
                    kind=cur_kind,
                    is_private=cur_priv,
                    start_line=cur_start,
                    end_line=max(cur_start, end_idx),
                    body_lines=tuple(cur_body),
                    live_body=live_b,
                )
            )
        cur_kind = None
        cur_name = None
        cur_fq_name = None
        cur_ns_snap = ()
        cur_opens_snap = ()
        cur_priv = False
        cur_body = []

    def _record_open(open_tail: str, extra_opens: list[str] | None = None) -> None:
        # Collect leading namespace identifiers from `open A B` (stop at
        # `(`, `hiding`, `renaming`, `in`).
        target = extra_opens if extra_opens is not None else (
            scope_stack[-1][2] if scope_stack else file_opens
        )
        for tok in open_tail.split():
            if tok in ("in", "hiding", "renaming") or tok.startswith("("):
                break
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.']*", tok):
                target.append(tok)

    def _process_top_cmd(
        cmd_strip: str, idx: int, *, flush_end: int, cmd_opens: tuple[str, ...] = ()
    ) -> bool:
        nonlocal cur_kind, cur_name, cur_fq_name, cur_ns_snap, cur_opens_snap
        nonlocal cur_priv, cur_start, cur_body
        if not cmd_strip:
            return False

        # Handle `open Foo in <command>` prefix recursively with scoped opens.
        open_in_m = re.match(r"^open\s+(.+?)\s+in\s+([\s\S]+)$", cmd_strip)
        if open_in_m is not None:
            scoped_ops: list[str] = list(cmd_opens)
            _record_open(open_in_m.group(1), extra_opens=scoped_ops)
            return _process_top_cmd(
                open_in_m.group(2).strip(),
                idx,
                flush_end=flush_end,
                cmd_opens=tuple(scoped_ops),
            )

        if re.match(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|noncomputable)\s+)*mutual\b",
            cmd_strip,
        ):
            _flush(flush_end)
            scope_stack.append(("mutual", None, []))
            return True

        ns_m = re.match(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|noncomputable)\s+)*"
            r"namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$",
            cmd_strip,
        )
        if ns_m is not None:
            _flush(flush_end)
            for part in ns_m.group(1).split("."):
                scope_stack.append(("ns", part, []))
            return True

        sec_m = re.match(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|noncomputable)\s+)*"
            r"section(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$",
            cmd_strip,
        )
        if sec_m is not None:
            _flush(flush_end)
            sec_name = sec_m.group(1)
            if sec_name:
                for part in sec_name.split("."):
                    scope_stack.append(("section", part, []))
            else:
                scope_stack.append(("section", None, []))
            return True

        end_m = re.match(
            r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$", cmd_strip
        )
        if end_m is not None:
            _flush(flush_end)
            end_arg = end_m.group(1)
            if end_arg:
                for part in reversed(end_arg.split(".")):
                    # Pop matching namespace/section entry from top of stack.
                    while scope_stack and scope_stack[-1][0] == "mutual":
                        scope_stack.pop()
                    if scope_stack and scope_stack[-1][1] == part:
                        scope_stack.pop()
            elif scope_stack:
                scope_stack.pop()
            return True

        open_m = re.match(
            r"^(?:(?:public|private|protected)\s+)*open\s+(?:scoped\s+)?(.+)$",
            cmd_strip,
        )
        if open_m is not None:
            _flush(flush_end)
            _record_open(open_m.group(1))
            return True

        m = LEAN_ANY_DECL_START_RE.match(cmd_strip)
        if m is not None:
            _flush(flush_end)
            cur_kind = m.group("kind")
            cur_name = m.group("name")
            cur_ns_snap = _active_ns()
            cur_opens_snap = (*_active_opens(), *cmd_opens)
            cur_fq_name = _qualify_name(cur_name, cur_ns_snap)
            cur_priv = "private" in m.group("mods").split()
            cur_start = idx
            cur_body = [cmd_strip[m.end() :]]
            return True

        if re.fullmatch(r"(?:@\[[^\]]*\]\s*)+", cmd_strip) or re.match(
            r"^(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|meta)\s+)*"
            r"(?:import|prelude|module|variable|universe|set_option"
            r"|attribute|syntax|notation|macro|elab|deriving)\b",
            cmd_strip,
        ):
            _flush(flush_end)
            return True
        return False

    for idx, ln in enumerate(lines):
        lstrip = ln.lstrip()
        if not lstrip:
            if cur_name is not None:
                cur_body.append(ln)
            continue
        indent = len(ln) - len(lstrip)
        is_scope_kw = (
            re.match(
                r"^(?:(?:@\[[^\]]*\]\s*)*(?:(?:public|private|noncomputable)\s+)*"
                r"(?:namespace|section|mutual|end)\b)",
                lstrip,
            )
            is not None
        )
        can_be_top_cmd = indent == 0 or is_scope_kw or (_in_mutual() and indent <= 2)
        if can_be_top_cmd:
            segs = [s.strip() for s in _split_lean_top_level_semicolons(lstrip)]
            if len(segs) > 1:
                consumed_any = False
                for seg_i, seg in enumerate(segs):
                    if not seg:
                        continue
                    flush_end = idx if seg_i > 0 else idx - 1
                    if _process_top_cmd(seg, idx, flush_end=flush_end):
                        consumed_any = True
                    elif cur_name is not None:
                        cur_body.append(seg)
                if consumed_any:
                    continue
            else:
                if _process_top_cmd(lstrip, idx, flush_end=idx - 1):
                    continue
        if cur_name is not None:
            cur_body.append(ln)
    _flush(len(lines) - 1)
    return decls


def _collect_lean_submodule_files(
    view: RepoView,
    *,
    root_rel: str,
    dir_rel: str,
    mod_prefix: str,
    exclude_rels: frozenset[str] = frozenset(),
) -> set[str]:
    """Collect Lean submodule files reachable transitively from `root_rel`, or all in `dir_rel`."""
    all_files = {
        rel for rel in view.list_files(dir_rel, (".lean",)) if rel not in exclude_rels
    }
    root_text = view.read_text(root_rel)
    if root_text is None:
        return all_files
    imp_re = re.compile(
        rf"^\s*(?:(?:public|private|meta)\s+)*import\s+"
        rf"{re.escape(mod_prefix)}\.([A-Za-z_][A-Za-z0-9_]*)\b",
        re.M,
    )
    included: set[str] = set()
    queue_texts: list[str] = [_strip_lean_comments_and_strings(root_text)]
    while queue_texts:
        qt = queue_texts.pop()
        for mod in imp_re.findall(qt):
            mod_rel = f"{dir_rel}/{mod}.lean"
            if mod_rel in exclude_rels or mod_rel in included:
                continue
            ok_f, _ = view.is_regular_file(mod_rel)
            if not ok_f:
                continue
            mtxt = view.read_text(mod_rel)
            if mtxt is None:
                continue
            included.add(mod_rel)
            queue_texts.append(_strip_lean_comments_and_strings(mtxt))
    return included


def _build_lean_mir_semantics_graph(view: RepoView) -> _LeanMirGraph:
    """Build namespace-aware runtime call graph across Trusted/MirSemantics/*.lean."""
    included = _collect_lean_submodule_files(
        view,
        root_rel=LEAN_MIR_SEMANTICS_ROOT_REL,
        dir_rel=MIR_SEMANTICS_DIR_REL,
        mod_prefix="Trusted.MirSemantics",
        exclude_rels=frozenset({LEAN_CANARY_FIXTURES_REL}),
    )
    ok_root, _ = view.is_regular_file(LEAN_MIR_SEMANTICS_ROOT_REL)
    if ok_root:
        included.add(LEAN_MIR_SEMANTICS_ROOT_REL)

    decls_by_file: dict[str, tuple[_LeanMirDecl, ...]] = {}
    all_decls: dict[tuple[str, str, int], _LeanMirDecl] = {}
    by_fq_name: dict[str, list[_LeanMirDecl]] = {}
    # Declared `inductive`/`structure`/`abbrev` type fq_names -> decls, and
    # dot-projection methods (`<TypeFq>.<method>`) indexed by short method name.
    # Also load declared `inductive`/`structure`/`abbrev` type fq_names from
    # `Trusted/MirModel.lean`, `Trusted/MirAst.lean`, and their
    # `Trusted/MirAst/*.lean` / `Trusted/MirModel/*.lean` submodules so
    # dot-projection methods resolve only for real types.
    type_decls_by_fq: dict[str, list[_LeanMirDecl]] = {}
    external_type_fqs: set[str] = set()
    ext_type_rels: set[str] = {
        "anneal/trusted/lean/Trusted/MirModel.lean",
        "anneal/trusted/lean/Trusted/MirAst.lean",
    }
    ext_type_rels.update(
        _collect_lean_submodule_files(
            view,
            root_rel="anneal/trusted/lean/Trusted/MirAst.lean",
            dir_rel="anneal/trusted/lean/Trusted/MirAst",
            mod_prefix="Trusted.MirAst",
        )
    )
    ext_type_rels.update(
        _collect_lean_submodule_files(
            view,
            root_rel="anneal/trusted/lean/Trusted/MirModel.lean",
            dir_rel="anneal/trusted/lean/Trusted/MirModel",
            mod_prefix="Trusted.MirModel",
        )
    )
    for ext_rel in sorted(ext_type_rels):
        ok_ext, _ = view.is_regular_file(ext_rel)
        if not ok_ext:
            continue
        ext_txt = view.read_text(ext_rel)
        if ext_txt is None:
            continue
        for ext_d in _parse_lean_file_decls(ext_txt, ext_rel):
            if ext_d.kind in ("inductive", "structure", "abbrev") and not ext_d.is_private:
                external_type_fqs.add(ext_d.fq_name)
    dot_methods_by_short: dict[str, list[tuple[str, _LeanMirDecl]]] = {}

    for rel in sorted(included):
        ok_f, _ = view.is_regular_file(rel)
        if not ok_f:
            continue
        txt = view.read_text(rel)
        if txt is None:
            continue
        f_decls = _parse_lean_file_decls(txt, rel)
        decls_by_file[rel] = tuple(f_decls)
        for d in f_decls:
            all_decls[d.decl_id] = d
            by_fq_name.setdefault(d.fq_name, []).append(d)
            if d.kind in ("inductive", "structure", "abbrev"):
                type_decls_by_fq.setdefault(d.fq_name, []).append(d)

    for d in all_decls.values():
        if "." in d.fq_name:
            owner_fq, short_m = d.fq_name.rsplit(".", 1)
            if owner_fq in type_decls_by_fq or owner_fq in external_type_fqs:
                dot_methods_by_short.setdefault(short_m, []).append((owner_fq, d))

    reachable: set[tuple[str, str, int]] = set()
    reachable_type_fqs: set[str] = set(external_type_fqs)
    bfs_q: list[_LeanMirDecl] = []

    def _mark_reachable(d: _LeanMirDecl) -> None:
        if d.decl_id in reachable:
            return
        reachable.add(d.decl_id)
        if d.kind in ("inductive", "structure", "abbrev"):
            reachable_type_fqs.add(d.fq_name)
        bfs_q.append(d)

    # Seed strictly by exact fully qualified exported declaration identity.
    for d in all_decls.values():
        if not d.is_private and d.fq_name in LEAN_MIR_SEMANTICS_ROOTS:
            _mark_reachable(d)

    def _accessible(tgt: _LeanMirDecl, caller: _LeanMirDecl) -> bool:
        return not tgt.is_private or tgt.rel == caller.rel

    def _resolve_lean_ref(ref: str, caller: _LeanMirDecl) -> list[_LeanMirDecl]:
        if ref.startswith("_root_."):
            fq = ref[len("_root_.") :]
            return [
                tgt
                for tgt in by_fq_name.get(fq, ())
                if _accessible(tgt, caller)
            ]
        # Search enclosing namespace prefixes from innermost to outermost.
        for k in range(len(caller.namespace), -1, -1):
            pref = caller.namespace[:k]
            cand = ".".join([*pref, ref]) if pref else ref
            matches = [
                tgt
                for tgt in by_fq_name.get(cand, ())
                if _accessible(tgt, caller)
            ]
            if matches:
                return matches
        # Search explicitly `open`ed namespaces in scope at `caller`.
        out: list[_LeanMirDecl] = []
        seen_ids: set[tuple[str, str, int]] = set()
        for op_ns in caller.open_namespaces:
            for k in range(len(caller.namespace), -1, -1):
                pref = caller.namespace[:k]
                cand = ".".join([*pref, op_ns, ref]) if pref else f"{op_ns}.{ref}"
                for tgt in by_fq_name.get(cand, ()):
                    if _accessible(tgt, caller) and tgt.decl_id not in seen_ids:
                        seen_ids.add(tgt.decl_id)
                        out.append(tgt)
        return out

    # Track deferred dot-notation calls `(caller, method_name)` so when a
    # declared `inductive`/`structure` type becomes reachable, its `.method`
    # calls from reachable callers also propagate cleanly.
    seen_dot_calls: list[tuple[_LeanMirDecl, str]] = []
    seen_dot_keys: set[tuple[tuple[str, str, int], str]] = set()

    while bfs_q:
        while bfs_q:
            cur = bfs_q.pop()
            for ref in set(LEAN_DOTTED_IDENT_RE.findall(cur.live_body)):
                for tgt in _resolve_lean_ref(ref, cur):
                    if tgt.decl_id != cur.decl_id:
                        _mark_reachable(tgt)
            for proj in set(LEAN_DOT_PROJ_RE.findall(cur.live_body)):
                if proj in dot_methods_by_short:
                    key = (cur.decl_id, proj)
                    if key not in seen_dot_keys:
                        seen_dot_keys.add(key)
                        seen_dot_calls.append((cur, proj))
                    for owner_fq, tgt in dot_methods_by_short[proj]:
                        if (
                            owner_fq in reachable_type_fqs
                            and _accessible(tgt, cur)
                            and tgt.decl_id != cur.decl_id
                        ):
                            _mark_reachable(tgt)
        # Re-check deferred dot calls against newly reachable declared types.
        for caller, proj in seen_dot_calls:
            for owner_fq, tgt in dot_methods_by_short.get(proj, ()):
                if (
                    owner_fq in reachable_type_fqs
                    and _accessible(tgt, caller)
                    and tgt.decl_id != caller.decl_id
                ):
                    _mark_reachable(tgt)

    return _LeanMirGraph(
        decls_by_file=decls_by_file,
        reachable_decl_ids=frozenset(reachable),
        included_files=frozenset(included),
    )


def _count_reachable_lean_unsupported_guards(
    view: RepoView, rel: str
) -> int:
    """Count `.fault .unsupported` / `.error .unsupported` guards in reachable decls."""
    graph = _build_lean_mir_semantics_graph(view)
    count = 0
    for d in graph.decls_by_file.get(rel, ()):
        if d.decl_id in graph.reachable_decl_ids:
            count += len(LEAN_UNSUPPORTED_GUARD_RE.findall(d.live_body))
    return count


def _lean_local_guard_is_dead(
    decl: _LeanMirDecl,
    code_lines: list[str],
    first_code_idx: int,
    first_stripped: str,
    base_indent: int,
) -> str | None:
    """Reject markers attached to unused local `let` or `where` bindings."""
    if LEAN_DEAD_IF_GUARD_RE.match(first_stripped) is not None:
        return "attaches to a statically dead `if false` branch"

    # 1. Local `let <name> := ...` inside a runtime decl.
    let_m = re.match(
        r"^(?:let|have)\s+(?:rec\s+)?([A-Za-z_][A-Za-z0-9_'?]*)(?![A-Za-z0-9_'?])[^:\n]*(?::[^:\n]*)?:=",
        first_stripped,
    )
    if let_m is not None:
        vname = let_m.group(1)
        if vname == "_" or vname.startswith("_"):
            return f"attaches to discarded local binding `{vname}`"
        end_j = first_code_idx + 1
        while end_j <= decl.end_line and end_j < len(code_lines):
            nxt = code_lines[end_j]
            if not nxt.strip():
                end_j += 1
                continue
            if len(nxt) - len(nxt.lstrip()) > base_indent:
                end_j += 1
                continue
            break
        tail_lines = code_lines[end_j : decl.end_line + 1]
        tail_live = _lean_live_body_for_refs(tail_lines)
        if vname not in set(LEAN_IDENT_RE.findall(tail_live)):
            return f"attaches to unused local binding `{vname}` in `{decl.name}`"

    # 2. Local helper inside a `where` block of `decl`.
    where_idx: int | None = None
    where_indent = -1
    for ln_i in range(decl.start_line + 1, first_code_idx):
        if ln_i >= len(code_lines):
            break
        s = code_lines[ln_i].lstrip()
        if re.match(r"^where\b", s):
            w_ind = len(code_lines[ln_i]) - len(s)
            if w_ind <= base_indent:
                where_idx = ln_i
                where_indent = w_ind
    if where_idx is not None and base_indent > where_indent:
        wh_m = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)\b", first_stripped)
        if wh_m is not None and wh_m.group(1) not in (
            "if",
            "match",
            "let",
            "have",
            "do",
            "return",
        ):
            wname = wh_m.group(1)
            # Parse sibling `where` helpers and check reachability from body.
            main_live = _lean_live_body_for_refs(
                code_lines[decl.start_line : where_idx]
            )
            where_helpers: dict[str, list[str]] = {}
            cur_wh: str | None = None
            for ln_i in range(where_idx + 1, decl.end_line + 1):
                if ln_i >= len(code_lines):
                    break
                cl = code_lines[ln_i]
                cs = cl.lstrip()
                if not cs:
                    continue
                ind = len(cl) - len(cs)
                if ind == base_indent:
                    hm = re.match(r"^([A-Za-z_][A-Za-z0-9_']*)\b", cs)
                    if hm is not None:
                        cur_wh = hm.group(1)
                        where_helpers.setdefault(cur_wh, []).append(
                            cs[hm.end() :]
                        )
                        continue
                if cur_wh is not None:
                    where_helpers.setdefault(cur_wh, []).append(cl)
            w_reach: set[str] = set()
            w_q = [main_live]
            while w_q:
                chunk = w_q.pop()
                for tok in set(LEAN_IDENT_RE.findall(chunk)):
                    if tok in where_helpers and tok not in w_reach:
                        w_reach.add(tok)
                        w_q.append(_lean_live_body_for_refs(where_helpers[tok]))
            if wname not in w_reach:
                return (
                    f"attaches to unused `where` helper `{wname}` in `{decl.name}`"
                )
    return None


def _check_lean_runtime_tripwire_guards(
    text: str,
    rel: str,
    entries: list[TripwireEntry],
    comment_spans: list[tuple[int, int]],
    lean_graph: _LeanMirGraph | None = None,
) -> list[str]:
    """Require each Lean MirSemantics `-- PHASE0_TRIPWIRE` to bind a reachable guard."""
    if not comment_spans or not _is_lean_mir_semantics_rel(rel):
        return []
    stripped = _strip_lean_comments_and_strings(text)
    raw_lines = text.splitlines()
    code_lines = stripped.splitlines()
    errors: list[str] = []
    for entry, (_c_start, c_end) in zip(entries, comment_spans):
        end_line_idx = text.count("\n", 0, c_end)
        # Allow consecutive comment-only lines immediately below the marker,
        # but forbid blank-line gaps or non-guard declarations.
        first_code_idx: int | None = None
        for ln_idx in range(end_line_idx + 1, len(raw_lines)):
            code_ln = code_lines[ln_idx] if ln_idx < len(code_lines) else ""
            if code_ln.strip():
                first_code_idx = ln_idx
                break
            raw_ln = raw_lines[ln_idx].strip()
            if not raw_ln:
                break
        if first_code_idx is None:
            errors.append(
                f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE marker "
                "must be immediately attached to a Lean fail-closed "
                "`.fault .unsupported` / `.error .unsupported` guard"
            )
            continue

        first_code = code_lines[first_code_idx]
        first_stripped = first_code.lstrip()
        base_indent = len(first_code) - len(first_stripped)
        if LEAN_NON_GUARD_DECL_RE.match(first_stripped) is not None:
            errors.append(
                f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE marker "
                "cannot attach to a non-guard declaration (must attach "
                "directly to a `.fault .unsupported` / `.error .unsupported` "
                "branch or guard def)"
            )
            continue

        # Collect the immediately attached Lean branch or guard definition
        # (bounded to a tight local guard window so markers cannot ride atop
        # large unrelated definitions that happen to mention `.unsupported`
        # elsewhere).
        is_if_branch = re.match(r"^(?:else\s+)?if\b", first_stripped) is not None
        is_def_decl = LEAN_DEF_DECL_RE.match(first_stripped) is not None
        attached: list[str] = [first_code]
        code_count = 1
        max_guard_lines = 8 if is_def_decl else 10
        for ln_idx in range(first_code_idx + 1, len(code_lines)):
            if code_count >= max_guard_lines:
                break
            cln = code_lines[ln_idx]
            cstrip = cln.lstrip()
            if not cstrip:
                if not raw_lines[ln_idx].strip():
                    break
                continue
            indent = len(cln) - len(cstrip)
            if indent > base_indent:
                attached.append(cln)
                code_count += 1
                continue
            if (
                is_if_branch
                and indent == base_indent
                and re.match(r"^(?:then|else)\b", cstrip) is not None
            ):
                attached.append(cln)
                code_count += 1
                continue
            break

        attached_src = "\n".join(attached)
        if LEAN_UNSUPPORTED_GUARD_RE.search(attached_src) is None:
            errors.append(
                f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE marker "
                "must be structurally attached to adjacent Lean code returning "
                "`.fault .unsupported` / `.error .unsupported` / "
                "`throw .unsupported`"
            )
            continue

        if lean_graph is not None:
            if rel not in lean_graph.included_files:
                errors.append(
                    f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE "
                    "resides in a non-runtime or unimported MirSemantics file"
                )
                continue
            enclosing_decl = next(
                (
                    d
                    for d in lean_graph.decls_by_file.get(rel, ())
                    if d.start_line <= first_code_idx <= d.end_line
                ),
                None,
            )
            if enclosing_decl is None:
                errors.append(
                    f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE guard "
                    "must reside in a runtime MirSemantics def/abbrev "
                    "reachable from runtime semantics entrypoints"
                )
                continue
            if enclosing_decl.decl_id not in lean_graph.reachable_decl_ids:
                errors.append(
                    f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE guard "
                    f"in `{enclosing_decl.fq_name}` is unreachable from "
                    "MirSemantics runtime semantics entrypoints"
                )
                continue
            local_dead = _lean_local_guard_is_dead(
                enclosing_decl,
                code_lines,
                first_code_idx,
                first_stripped,
                base_indent,
            )
            if local_dead is not None:
                errors.append(
                    f"{rel} ({entry.bug_id}): runtime -- PHASE0_TRIPWIRE guard "
                    f"{local_dead}"
                )
    return errors


def collect_repo_tripwires(view: RepoView) -> tuple[list[TripwireEntry], list[str]]:
    """Collect declared Phase-0 tripwires across Rust and Lean trusted trees."""
    entries: list[TripwireEntry] = []
    errors: list[str] = []

    ok, file_err = view.is_regular_file(TRIPWIRES_REL)
    if not ok:
        errors.append(file_err or f"missing tripwire registry: {TRIPWIRES_REL}")
    else:
        rust_text = view.read_text(TRIPWIRES_REL)
        if rust_text is None:
            errors.append(f"unreadable tripwire registry: {TRIPWIRES_REL}")
        else:
            rust_entries, rust_errs = parse_rust_tripwires(
                rust_text, TRIPWIRES_REL
            )
            entries.extend(rust_entries)
            errors.extend(rust_errs)

    lean_graph: _LeanMirGraph | None = None
    for rel in view.list_files(TRUSTED_DIR_REL, (".lean", ".rs")):
        ok, err = view.is_regular_file(rel)
        if not ok:
            if err:
                errors.append(err)
            continue
        if rel == TRIPWIRES_REL:
            continue
        text = view.read_text(rel)
        if text is None:
            continue
        comment_entries, comment_spans, comment_errs = (
            ([], [], []) if rel.endswith(".rs") else _parse_comment_tripwires_with_spans(text, rel)
        )
        if comment_spans and _is_lean_mir_semantics_rel(rel):
            if lean_graph is None:
                lean_graph = _build_lean_mir_semantics_graph(view)
            errors.extend(
                _check_lean_runtime_tripwire_guards(
                    text, rel, comment_entries, comment_spans, lean_graph
                )
            )
        if rel.endswith(".rs"):
            prod_text, split_errs = _split_rust_production_section(
                text, rel, allow_multiple_cfg_test=True
            )
            errors.extend(split_errs)
            other_ns = scan_rust_tokens(prod_text).code_no_strings_or_comments
            if MACRO_CALL_RE.search(other_ns) or STRUCT_LITERAL_RE.search(other_ns):
                errors.append(
                    f"{rel}: PHASE0_TRIPWIRE declarations are permitted only "
                    f"inside {TRIPWIRES_REL}"
                )
            comment_entries, comment_spans, comment_errs = (
                _parse_comment_tripwires_with_spans(prod_text, rel)
            )
            errors.extend(
                _check_trusted_comment_cfg_guards(
                    prod_text, rel, comment_spans, raw_text=text
                )
            )
        entries.extend(comment_entries)
        errors.extend(comment_errs)

    return entries, errors


def _blank_span(chars: list[str], start: int, end: int) -> bool:
    """Replace `chars[start:end]` with spaces, preserving newlines and length."""
    changed = False
    for idx in range(start, end):
        if chars[idx] not in (" ", "\n", "\r", "\t"):
            chars[idx] = " "
            changed = True
    return changed


def _find_rust_nested_block_end(code_ns: str, header_end: int) -> int | None:
    """Find closing `}` of a nested `fn`/`mod` item after `header_end`."""
    paren_depth = 0
    bracket_depth = 0
    idx = header_end
    n = len(code_ns)
    while idx < n:
        ch = code_ns[idx]
        if ch == "(":
            paren_depth += 1
        elif ch == ")" and paren_depth > 0:
            paren_depth -= 1
        elif ch == "[":
            bracket_depth += 1
        elif ch == "]" and bracket_depth > 0:
            bracket_depth -= 1
        elif paren_depth == 0 and bracket_depth == 0:
            if ch == ";":
                return None
            if ch == "{":
                return _find_matching_delimiter_in_code(code_ns, idx)
        idx += 1
    return None


def _skip_rust_else_chain(ns: str, close_idx: int) -> int:
    """Return end index after any trailing `else [if cond] { ... }` chain."""
    n = len(ns)
    pos = close_idx + 1
    furthest = pos
    while pos < n:
        else_m = re.match(r"\s*else\b", ns[pos:])
        if else_m is None:
            break
        q = pos + else_m.end()
        while q < n and ns[q].isspace():
            q += 1
        if q < n and ns[q] == "{":
            close_e = _find_matching_delimiter_in_code(ns, q)
            if close_e is None:
                break
            return close_e + 1
        if re.match(r"if\b", ns[q:]):
            q += 2
            p_d = 0
            b_d = 0
            while q < n:
                ch = ns[q]
                if ch == "(":
                    p_d += 1
                elif ch == ")" and p_d > 0:
                    p_d -= 1
                elif ch == "[":
                    b_d += 1
                elif ch == "]" and b_d > 0:
                    b_d -= 1
                elif p_d == 0 and b_d == 0 and ch in "{;":
                    break
                q += 1
            if q >= n or ns[q] != "{":
                break
            close_e = _find_matching_delimiter_in_code(ns, q)
            if close_e is None:
                break
            furthest = close_e + 1
            pos = furthest
            continue
        break
    return furthest


def _rust_pat_has_top_level_guard(pat_ns: str) -> bool:
    """Return True if a match arm pattern carries a top-level `if` guard."""
    p_d = 0
    b_d = 0
    br_d = 0
    n = len(pat_ns)
    for i, ch in enumerate(pat_ns):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == "i":
            if (
                pat_ns[i : i + 2] == "if"
                and (
                    i == 0
                    or not (pat_ns[i - 1].isalnum() or pat_ns[i - 1] == "_")
                )
                and (
                    i + 2 == n
                    or not (pat_ns[i + 2].isalnum() or pat_ns[i + 2] == "_")
                )
            ):
                return True
    return False


def _find_depth0_fat_arrow(s: str, start: int = 0) -> int | None:
    """Return index of first depth-0 `=>` in `s[start:]`, or None."""
    p_d = 0
    b_d = 0
    br_d = 0
    i = start
    n = len(s)
    while i < n:
        ch = s[i]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and s[i : i + 2] == "=>":
            return i
        i += 1
    return None


def _split_rust_match_arms(
    arms_ns: str,
    early_exit_re: re.Pattern[str],
    _depth: int,
) -> list[tuple[str, str]] | None:
    """Split match body into `(pat_and_guard, rhs)` pairs, or None on error."""
    arms: list[tuple[str, str]] = []
    n = len(arms_ns)
    pos = 0
    while pos < n:
        while pos < n and arms_ns[pos].isspace():
            pos += 1
        if pos >= n:
            break
        while pos < n and arms_ns[pos] == "#":
            attr_m = re.match(r"#\s*\[", arms_ns[pos:])
            if attr_m is None:
                break
            close_a = _find_matching_delimiter_in_code(
                arms_ns, pos + attr_m.end() - 1
            )
            if close_a is None:
                return None
            pos = close_a + 1
            while pos < n and arms_ns[pos].isspace():
                pos += 1
        if pos >= n:
            break
        arrow = _find_depth0_fat_arrow(arms_ns, pos)
        if arrow is None:
            return None
        pat_guard = arms_ns[pos:arrow]
        rhs_start = arrow + 2
        while rhs_start < n and arms_ns[rhs_start].isspace():
            rhs_start += 1
        if rhs_start >= n:
            return None

        ctrl = _rust_ctrl_expr_span_and_diverges(
            arms_ns, rhs_start, n, early_exit_re, _depth + 1
        )
        if ctrl is not None:
            ctrl_end, _ = ctrl
            tail = arms_ns[ctrl_end:]
            comma_m = re.match(r"\s*,", tail)
            if comma_m is not None:
                arms.append((pat_guard, arms_ns[rhs_start:ctrl_end]))
                pos = ctrl_end + comma_m.end()
                continue
            if not tail.strip():
                arms.append((pat_guard, arms_ns[rhs_start:ctrl_end]))
                pos = n
                continue
            next_arrow = _find_depth0_fat_arrow(arms_ns, ctrl_end)
            if next_arrow is not None:
                p_d = b_d = br_d = 0
                has_comma_before = False
                for q in range(ctrl_end, next_arrow):
                    qc = arms_ns[q]
                    if qc == "(":
                        p_d += 1
                    elif qc == ")" and p_d > 0:
                        p_d -= 1
                    elif qc == "[":
                        b_d += 1
                    elif qc == "]" and b_d > 0:
                        b_d -= 1
                    elif qc == "{":
                        br_d += 1
                    elif qc == "}" and br_d > 0:
                        br_d -= 1
                    elif p_d == 0 and b_d == 0 and br_d == 0 and qc == ",":
                        has_comma_before = True
                        break
                if not has_comma_before:
                    arms.append((pat_guard, arms_ns[rhs_start:ctrl_end]))
                    pos = ctrl_end
                    continue

        p_d = 0
        b_d = 0
        br_d = 0
        q = rhs_start
        while q < n:
            qc = arms_ns[q]
            if qc == "(":
                p_d += 1
            elif qc == ")" and p_d > 0:
                p_d -= 1
            elif qc == "[":
                b_d += 1
            elif qc == "]" and b_d > 0:
                b_d -= 1
            elif qc == "{":
                br_d += 1
            elif qc == "}" and br_d > 0:
                br_d -= 1
            elif p_d == 0 and b_d == 0 and br_d == 0 and qc == ",":
                break
            q += 1
        arms.append((pat_guard, arms_ns[rhs_start:q]))
        pos = q + 1 if q < n else n
    return arms


def _rust_expr_diverges(
    expr_ns: str,
    early_exit_re: re.Pattern[str],
    _depth: int = 0,
    expr_code: str | None = None,
) -> bool:
    """Return True if `expr_ns` unconditionally exits or diverges."""
    if _depth > 32:
        return False
    ns_s, code_s = _rust_strip_ws_and_parens_aligned(expr_ns, expr_code)
    if not ns_s:
        return False
    if early_exit_re.match(ns_s) is not None:
        return True
    ctrl = _rust_ctrl_expr_span_and_diverges(
        ns_s, 0, len(ns_s), early_exit_re, _depth + 1, code=code_s
    )
    if ctrl is not None and ctrl[1]:
        return True
    return False


def _rust_strip_ws_and_parens_aligned(
    ns: str, code: str | None = None
) -> tuple[str, str | None]:
    """Strip outer whitespace and balanced parentheses while keeping `code` aligned."""
    aligned = code is not None and len(code) == len(ns)
    lo = 0
    hi = len(ns)
    while lo < hi and ns[lo].isspace():
        lo += 1
    while hi > lo and ns[hi - 1].isspace():
        hi -= 1
    while hi - lo >= 2 and ns[lo] == "(" and ns[hi - 1] == ")":
        close_p = _find_matching_delimiter_in_code(ns[lo:hi], 0)
        if close_p != (hi - lo) - 1:
            break
        lo += 1
        hi -= 1
        while lo < hi and ns[lo].isspace():
            lo += 1
        while hi > lo and ns[hi - 1].isspace():
            hi -= 1
    return ns[lo:hi], (code[lo:hi] if aligned and code is not None else None)


def _eval_cfg_predicate_truth(
    raw_cfg: str, *, allow_cfg_test: bool = True, _depth: int = 0
) -> bool | None:
    """Evaluate known CI-host `cfg(...)` truth (`True`/`False`), else `None`."""
    if _depth > 16:
        return None
    compact = re.sub(r"\s+", "", raw_cfg)
    if not compact:
        return None
    if compact in ("all()", "true", "not(any())"):
        return True
    if compact in ("any()", "false", "not(all())"):
        return False
    if compact in ALLOWED_CI_HOST_CFGS:
        return True if (compact != "test" or allow_cfg_test) else None
    if compact.startswith("not(") and compact.endswith(")"):
        inner_val = _eval_cfg_predicate_truth(
            raw_cfg.strip()[3:].strip()[1:-1],
            allow_cfg_test=allow_cfg_test,
            _depth=_depth + 1,
        )
        return (not inner_val) if inner_val is not None else None
    for comb, short_val, all_val in (("all(", False, True), ("any(", True, False)):
        if compact.startswith(comb) and compact.endswith(")"):
            m_comb = re.match(
                rf"^\s*{comb[:-1]}\s*\((.*)\)\s*$", raw_cfg, re.DOTALL
            )
            if m_comb is None:
                return None
            parts = _split_top_level_commas(m_comb.group(1), keep_literal_only=True)
            if not parts:
                return all_val
            vals = [
                _eval_cfg_predicate_truth(
                    p, allow_cfg_test=allow_cfg_test, _depth=_depth + 1
                )
                for p in parts
            ]
            if any(v is short_val for v in vals):
                return short_val
            if all(v is all_val for v in vals):
                return all_val
            return None
    return None


def _eval_cfg_attr_truth(
    attr_inner: str, *, allow_cfg_test: bool = True
) -> bool | None:
    """Return `True`/`False` for statically known `cfg(...)` attributes, else `None`."""
    stripped = re.sub(r"\s+", " ", attr_inner).strip()
    arg_m = re.match(r"^cfg\s*\((.*)\)$", stripped, re.DOTALL)
    if arg_m is None:
        return None
    return _eval_cfg_predicate_truth(
        arg_m.group(1), allow_cfg_test=allow_cfg_test
    )


def _eval_rust_static_bool_cond(
    cond_ns: str, _depth: int = 0, cond_code: str | None = None
) -> bool | None:
    """Evaluate statically constant Rust boolean conditions (`!false`, `(false)`, `cfg!(...)`)."""
    if _depth > 16:
        return None
    s, s_code = _rust_strip_ws_and_parens_aligned(cond_ns, cond_code)
    if not s:
        return None
    if s == "true":
        return True
    if s == "false":
        return False
    # Handle top-level `||` and `&&` before unary `!`.
    or_spans = _split_top_level_rust_op_spans(s, "||")
    if len(or_spans) > 1:
        vals = [
            _eval_rust_static_bool_cond(
                s[a:b],
                _depth + 1,
                cond_code=(s_code[a:b] if s_code is not None else None),
            )
            for a, b in or_spans
        ]
        if any(v is True for v in vals):
            return True
        if all(v is False for v in vals):
            return False
        return None
    and_spans = _split_top_level_rust_op_spans(s, "&&")
    if len(and_spans) > 1:
        vals = [
            _eval_rust_static_bool_cond(
                s[a:b],
                _depth + 1,
                cond_code=(s_code[a:b] if s_code is not None else None),
            )
            for a, b in and_spans
        ]
        if any(v is False for v in vals):
            return False
        if all(v is True for v in vals):
            return True
        return None
    if s.startswith("!") and not s.startswith("!="):
        inner = _eval_rust_static_bool_cond(
            s[1:],
            _depth + 1,
            cond_code=(s_code[1:] if s_code is not None else None),
        )
        return (not inner) if inner is not None else None
    cfg_m = re.fullmatch(r"cfg\s*!\s*\((.*)\)", s, re.DOTALL)
    if cfg_m is not None:
        raw_cfg = (
            s_code[cfg_m.start(1) : cfg_m.end(1)]
            if s_code is not None
            else cfg_m.group(1)
        )
        return _eval_cfg_predicate_truth(raw_cfg, allow_cfg_test=True)
    eq_m = re.fullmatch(r"([0-9_]+)\s*(==|!=)\s*([0-9_]+)", s)
    if eq_m is not None:
        lhs = int(eq_m.group(1).replace("_", ""))
        rhs = int(eq_m.group(3).replace("_", ""))
        return (lhs == rhs) if eq_m.group(2) == "==" else (lhs != rhs)
    beq_m = re.fullmatch(r"(true|false)\s*(==|!=)\s*(true|false)", s)
    if beq_m is not None:
        lhs_b = beq_m.group(1) == "true"
        rhs_b = beq_m.group(3) == "true"
        return (lhs_b == rhs_b) if beq_m.group(2) == "==" else (lhs_b != rhs_b)
    return None


def _split_top_level_rust_op_spans(code_ns: str, op: str) -> list[tuple[int, int]]:
    """Return `(start, end)` spans splitting Rust `code_ns` on depth-0 `op`."""
    out: list[tuple[int, int]] = []
    p_d = b_d = br_d = 0
    start = 0
    i = 0
    n = len(code_ns)
    while i < n:
        ch = code_ns[i]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif (
            p_d == 0
            and b_d == 0
            and br_d == 0
            and code_ns[i : i + len(op)] == op
        ):
            out.append((start, i))
            i += len(op)
            start = i
            continue
        i += 1
    out.append((start, n))
    return out


def _split_top_level_rust_op_ns(code_ns: str, op: str) -> list[str]:
    """Split already-comment/string-stripped Rust `code_ns` on depth-0 `op`."""
    return [code_ns[a:b] for a, b in _split_top_level_rust_op_spans(code_ns, op)]


def _find_rust_cond_brace(ns: str, start: int, limit: int) -> int | None:
    """Find `{` opening an `if` or `match` body after its header expression."""
    p_d = 0
    b_d = 0
    q = start
    while q < limit:
        ch = ns[q]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif p_d == 0 and b_d == 0:
            if ch == ";" or ns[q : q + 2] == "=>":
                return None
            if ch == "{":
                first_close = _find_matching_delimiter_in_code(ns, q)
                if first_close is None or first_close >= limit:
                    return None
                after = ns[first_close + 1 : limit]
                ws_m = re.match(r"\s*\{", after)
                if ws_m is not None:
                    return first_close + 1 + ws_m.end() - 1
                return q
        q += 1
    return None


def _rust_ctrl_expr_span_and_diverges(
    ns: str,
    idx: int,
    limit: int,
    early_exit_re: re.Pattern[str],
    _depth: int = 0,
    code: str | None = None,
) -> tuple[int, bool] | None:
    """Parse `{...}`, `unsafe`, `loop`, `if`, or `match` and test divergence."""
    if _depth > 32 or idx >= limit:
        return None
    aligned_code = code if (code is not None and len(code) == len(ns)) else None
    tail = ns[idx:limit]
    if ns[idx] == "{" or re.match(r"unsafe\s*\{", tail):
        b_open = idx if ns[idx] == "{" else idx + tail.find("{")
        b_close = _find_matching_delimiter_in_code(ns, b_open)
        if b_close is None or b_close >= limit:
            return None
        div = (
            _rust_block_early_exit_cut(
                ns, b_open, b_close, early_exit_re, _depth + 1, code=aligned_code
            )
            is not None
        )
        return b_close + 1, div

    loop_m = re.match(r"loop\s*\{", tail)
    if loop_m is not None:
        b_open = idx + loop_m.end() - 1
        b_close = _find_matching_delimiter_in_code(ns, b_open)
        if b_close is None or b_close >= limit:
            return None
        cut = _rust_block_early_exit_cut(
            ns, b_open, b_close, early_exit_re, _depth + 1, code=aligned_code
        )
        scan_end = cut if cut is not None else b_close
        div = re.search(r"\bbreak\b", ns[b_open + 1 : scan_end]) is None
        return b_close + 1, div

    if re.match(r"if\b", tail):
        b1_open = _find_rust_cond_brace(ns, idx + 2, limit)
        if b1_open is None:
            return None
        b1_close = _find_matching_delimiter_in_code(ns, b1_open)
        if b1_close is None or b1_close >= limit:
            return None
        cond1_raw = ns[idx + 2 : b1_open]
        cond1_code = (
            aligned_code[idx + 2 : b1_open] if aligned_code is not None else None
        )
        cond1 = cond1_raw.strip()
        cond1_div = _rust_expr_diverges(
            cond1_raw, early_exit_re, _depth + 1, expr_code=cond1_code
        )
        b1_div = (
            _rust_block_early_exit_cut(
                ns, b1_open, b1_close, early_exit_re, _depth + 1, code=aligned_code
            )
            is not None
        )
        cond1_val = _eval_rust_static_bool_cond(cond1_raw, cond_code=cond1_code)
        if cond1_val is True and b1_div:
            return min(_skip_rust_else_chain(ns, b1_close), limit), True
        if cond1_div:
            return min(_skip_rust_else_chain(ns, b1_close), limit), True

        branch_divs = [] if cond1_val is False else [b1_div]
        has_plain_else = False
        cur_end = b1_close + 1
        while cur_end < limit:
            else_m = re.match(r"\s*else\b", ns[cur_end:limit])
            if else_m is None:
                break
            q = cur_end + else_m.end()
            while q < limit and ns[q].isspace():
                q += 1
            if q < limit and ns[q] == "{":
                e_close = _find_matching_delimiter_in_code(ns, q)
                if e_close is None or e_close >= limit:
                    break
                e_div = (
                    _rust_block_early_exit_cut(
                        ns, q, e_close, early_exit_re, _depth + 1, code=aligned_code
                    )
                    is not None
                )
                branch_divs.append(e_div)
                has_plain_else = True
                cur_end = e_close + 1
                break
            if re.match(r"if\b", ns[q:limit]):
                bi_open = _find_rust_cond_brace(ns, q + 2, limit)
                if bi_open is None:
                    break
                bi_close = _find_matching_delimiter_in_code(ns, bi_open)
                if bi_close is None or bi_close >= limit:
                    break
                bi_cond_raw = ns[q + 2 : bi_open]
                bi_cond_code = (
                    aligned_code[q + 2 : bi_open]
                    if aligned_code is not None
                    else None
                )
                bi_val = _eval_rust_static_bool_cond(
                    bi_cond_raw, cond_code=bi_cond_code
                )
                bi_div = (
                    _rust_block_early_exit_cut(
                        ns, bi_open, bi_close, early_exit_re, _depth + 1, code=aligned_code
                    )
                    is not None
                )
                if bi_val is not False:
                    branch_divs.append(bi_div)
                cur_end = bi_close + 1
                if bi_val is True:
                    has_plain_else = True
                    cur_end = min(_skip_rust_else_chain(ns, bi_close), limit)
                    break
                continue
            break
        return cur_end, (has_plain_else and bool(branch_divs) and all(branch_divs))

    if re.match(r"match\b", tail):
        m_open = _find_rust_cond_brace(ns, idx + 5, limit)
        if m_open is None:
            return None
        m_close = _find_matching_delimiter_in_code(ns, m_open)
        if m_close is None or m_close >= limit:
            return None
        scrut = ns[idx + 5 : m_open].strip()
        scrut_code = (
            aligned_code[idx + 5 : m_open] if aligned_code is not None else None
        )
        if _rust_expr_diverges(
            scrut, early_exit_re, _depth + 1, expr_code=scrut_code
        ):
            return m_close + 1, True
        arms = _split_rust_match_arms(
            ns[m_open + 1 : m_close], early_exit_re, _depth + 1
        )
        if not arms:
            return m_close + 1, False
        has_unguarded = any(
            not _rust_pat_has_top_level_guard(pg) for pg, _ in arms
        )
        all_div = all(
            _rust_expr_diverges(rhs, early_exit_re, _depth + 1)
            for _, rhs in arms
        )
        return m_close + 1, (has_unguarded and all_div)

    return None


def _rust_block_early_exit_cut(
    ns: str,
    open_b: int,
    close_b: int,
    early_exit_re: re.Pattern[str],
    _depth: int = 0,
    code: str | None = None,
) -> int | None:
    """Return index inside `(open_b, close_b)` after unconditional early exit."""
    if _depth > 32:
        return None
    aligned_code = code if (code is not None and len(code) == len(ns)) else None
    p_d = 0
    b_d = 0
    br_d = 0
    stmt_start = True
    idx = open_b + 1
    while idx < close_b:
        c = ns[idx]
        if p_d == 0 and b_d == 0 and br_d == 0:
            if c.isspace():
                idx += 1
                continue
            if stmt_start:
                em = early_exit_re.match(ns, idx)
                if em is not None and (idx == 0 or ns[idx - 1] not in (".", ":")):
                    ep_d = 0
                    eb_d = 0
                    ebr_d = 0
                    j = idx
                    while j < close_b:
                        jc = ns[j]
                        if jc == "(":
                            ep_d += 1
                        elif jc == ")" and ep_d > 0:
                            ep_d -= 1
                        elif jc == "[":
                            eb_d += 1
                        elif jc == "]" and eb_d > 0:
                            eb_d -= 1
                        elif jc == "{":
                            ebr_d += 1
                        elif jc == "}" and ebr_d > 0:
                            ebr_d -= 1
                        elif (
                            ep_d == 0
                            and eb_d == 0
                            and ebr_d == 0
                            and jc == ";"
                        ):
                            return j + 1
                        j += 1
                    return close_b

                ctrl = _rust_ctrl_expr_span_and_diverges(
                    ns, idx, close_b, early_exit_re, _depth + 1, code=aligned_code
                )
                if ctrl is not None and ctrl[1]:
                    end_pos = ctrl[0]
                    semi_m = re.match(r"\s*;", ns[end_pos:close_b])
                    if semi_m is not None:
                        end_pos += semi_m.end()
                    return min(end_pos, close_b)

                # Check statement/let RHS or parenthesized diverging expr.
                sp_d = sb_d = sbr_d = 0
                s_end = idx
                while s_end < close_b:
                    sc = ns[s_end]
                    if sc == "(":
                        sp_d += 1
                    elif sc == ")" and sp_d > 0:
                        sp_d -= 1
                    elif sc == "[":
                        sb_d += 1
                    elif sc == "]" and sb_d > 0:
                        sb_d -= 1
                    elif sc == "{":
                        sbr_d += 1
                    elif sc == "}" and sbr_d > 0:
                        sbr_d -= 1
                    elif sp_d == 0 and sb_d == 0 and sbr_d == 0 and sc == ";":
                        break
                    s_end += 1
                stmt_slice = ns[idx:s_end]
                stmt_code_slice = (
                    aligned_code[idx:s_end] if aligned_code is not None else None
                )
                eq_pos = _find_rust_top_level_equal(stmt_slice)
                cand_rhs = (
                    stmt_slice[eq_pos + 1 :].strip()
                    if eq_pos is not None
                    else stmt_slice.strip()
                )
                cand_rhs_raw = (
                    stmt_slice[eq_pos + 1 :] if eq_pos is not None else stmt_slice
                )
                cand_rhs_code = (
                    (
                        stmt_code_slice[eq_pos + 1 :]
                        if eq_pos is not None
                        else stmt_code_slice
                    )
                    if stmt_code_slice is not None
                    else None
                )
                is_closure = bool(
                    re.match(r"^(?:(?:move|async|static)\s+)*\|", cand_rhs)
                )
                if not is_closure and _rust_expr_diverges(
                    cand_rhs_raw,
                    early_exit_re,
                    _depth + 1,
                    expr_code=cand_rhs_code,
                ):
                    return s_end + 1 if s_end < close_b else close_b

                stmt_start = False
        if c == "(":
            p_d += 1
        elif c == ")" and p_d > 0:
            p_d -= 1
        elif c == "[":
            b_d += 1
        elif c == "]" and b_d > 0:
            b_d -= 1
        elif c == "{":
            br_d += 1
        elif c == "}":
            if br_d > 0:
                br_d -= 1
                if p_d == 0 and b_d == 0 and br_d == 0:
                    after = ns[idx + 1 : close_b].lstrip()
                    stmt_start = not re.match(r"else\b", after)
        elif p_d == 0 and b_d == 0 and br_d == 0 and c == ";":
            stmt_start = True
        idx += 1
    return None


def _parse_rust_int_literal(raw: str) -> int | None:
    """Parse an optional-sign Rust integer literal (`0`, `-1i32`, `0x10`)."""
    s = re.sub(r"\s+", "", raw)
    while s.startswith("(") and s.endswith(")"):
        close_p = _find_matching_delimiter_in_code(s, 0)
        if close_p != len(s) - 1:
            break
        s = s[1:-1]
    m = re.fullmatch(
        r"([+-]?)(0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|\d[0-9_]*)"
        r"(?:u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)?",
        s,
    )
    if m is None:
        return None
    sign = -1 if m.group(1) == "-" else 1
    digits = m.group(2).replace("_", "")
    base = (
        16
        if digits.startswith("0x")
        else 2
        if digits.startswith("0b")
        else 8
        if digits.startswith("0o")
        else 10
    )
    return sign * int(digits, base)


def _rust_for_iter_is_statically_empty(iter_nc: str, iter_ns: str) -> bool:
    """Return True if a Rust `for` iterable has 0 static elements."""
    s_ns = iter_ns.strip()
    s_nc = iter_nc.strip()
    while True:
        suf_m = re.search(
            r"\.\s*(?:iter|into_iter|iter_mut)\s*\(\s*\)\s*$", s_ns
        )
        if suf_m is not None:
            s_ns = s_ns[: suf_m.start()].strip()
            s_nc = s_nc[: suf_m.start()].strip()
            continue
        if s_ns.startswith("(") and s_ns.endswith(")"):
            cp = _find_matching_delimiter_in_code(s_ns, 0)
            if cp == len(s_ns) - 1:
                s_ns = s_ns[1:-1].strip()
                s_nc = s_nc[1:-1].strip()
                continue
        break
    compact = re.sub(r"\s+", "", s_ns)
    if compact in (
        "[]",
        "&[]",
        "&mut[]",
        "vec![]",
        "vec!()",
        "None",
        "Option::None",
        "core::option::Option::None",
        "std::option::Option::None",
        "iter::empty()",
        "core::iter::empty()",
        "std::iter::empty()",
    ):
        return True
    str_m = re.match(
        r'^(.*)\.\s*(?:chars|bytes|lines|split_whitespace)\s*\(\s*\)$', s_nc
    )
    if str_m is not None:
        lit = _decode_single_string_literal(str_m.group(1).strip())
        if lit == "":
            return True
    rng_m = re.search(r"\.\.(=?)", s_ns)
    if rng_m is not None:
        inclusive = rng_m.group(1) == "="
        lhs = _parse_rust_int_literal(s_ns[: rng_m.start()])
        rhs = _parse_rust_int_literal(s_ns[rng_m.end() :])
        if lhs is not None and rhs is not None:
            return (lhs > rhs) if inclusive else (lhs >= rhs)
    return False


def _rust_leading_outer_attrs_start(ns: str, pos: int) -> int:
    """Walk backward over contiguous outer `#[...]` attributes before `pos`."""
    cur = pos
    while cur > 1:
        p = cur
        while p > 1 and ns[p - 1].isspace():
            p -= 1
        if p <= 1 or ns[p - 1] != "]":
            break
        depth = 1
        q = p - 2
        while q >= 1 and depth > 0:
            if ns[q] == "]":
                depth += 1
            elif ns[q] == "[":
                depth -= 1
                if depth == 0:
                    break
            q -= 1
        if depth != 0:
            break
        r = q - 1
        while r >= 1 and ns[r].isspace():
            r -= 1
        if r < 1 or ns[r] != "#":
            break
        cur = r
    return cur


def _strip_unreachable_rust_test_code(
    fn_code: str, fn_code_ns: str
) -> tuple[str, str]:
    """Blank nested defs, dead `cfg`, `if/while false`, early returns, `if true` headers."""
    code_chars = list(fn_code)
    ns_chars = list(fn_code_ns)
    nested_macro_re = re.compile(
        r"\bmacro_rules\s*!\s*[A-Za-z_][A-Za-z0-9_]*\s*([{\[(])"
    )
    nested_fn_or_mod_re = re.compile(
        r"\b(?:(?:pub(?:\([^)]*\))?\s+|async\s+|unsafe\s+|const\s+)*)"
        r"(?:fn|mod)\s+[A-Za-z_][A-Za-z0-9_]*\b"
    )
    branch_kw_re = re.compile(r"\b(if|while)\b")
    early_exit_re = re.compile(
        r"return\b"
        r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
        r"process\s*::\s*(?:exit|abort)\s*\("
        r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
        r"(?:panic|unreachable|todo|unimplemented)\s*!\s*[(\[{]"
    )

    changed = True
    while changed:
        changed = False
        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)

        for m in nested_macro_re.finditer(cur_ns, 1):
            close_idx = _find_matching_delimiter_in_code(cur_ns, m.end() - 1)
            if close_idx is None:
                continue
            end_idx = close_idx + 1
            if end_idx < len(cur_ns) and cur_ns[end_idx] == ";":
                end_idx += 1
            start_idx = _rust_leading_outer_attrs_start(cur_ns, m.start())
            changed |= _blank_span(code_chars, start_idx, end_idx)
            changed |= _blank_span(ns_chars, start_idx, end_idx)

        for m in nested_fn_or_mod_re.finditer(cur_ns, 1):
            close_idx = _find_rust_nested_block_end(cur_ns, m.end())
            if close_idx is not None:
                start_idx = _rust_leading_outer_attrs_start(cur_ns, m.start())
                changed |= _blank_span(code_chars, start_idx, close_idx + 1)
                changed |= _blank_span(ns_chars, start_idx, close_idx + 1)

        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)
        for a_start, a_end, inner, is_inner in _find_rust_attributes(
            cur_ns, cur_code
        ):
            if a_start == 0:
                continue
            if (
                _eval_cfg_attr_truth(inner, allow_cfg_test=True) is not False
            ):
                continue
            if is_inner:
                encl = _find_rust_enclosing_delimiters(cur_ns, a_start)
                if not encl:
                    changed |= _blank_span(code_chars, 0, len(code_chars))
                    changed |= _blank_span(ns_chars, 0, len(ns_chars))
                else:
                    _delim, open_pos = encl[-1]
                    close_pos = _find_matching_delimiter_in_code(
                        cur_ns, open_pos
                    )
                    span_end = (
                        (close_pos + 1)
                        if close_pos is not None
                        else len(cur_ns)
                    )
                    if open_pos == 0:
                        changed |= _blank_span(
                            code_chars, 1, max(1, span_end - 1)
                        )
                        changed |= _blank_span(
                            ns_chars, 1, max(1, span_end - 1)
                        )
                    else:
                        changed |= _blank_span(code_chars, open_pos, span_end)
                        changed |= _blank_span(ns_chars, open_pos, span_end)
                continue
            end_idx = _find_rust_item_end_after_attr(cur_ns, a_end)
            if end_idx is not None:
                changed |= _blank_span(code_chars, a_start, end_idx)
                changed |= _blank_span(ns_chars, a_start, end_idx)

        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)
        for m in branch_kw_re.finditer(cur_ns, 1):
            kw = m.group(1)
            brace_idx = _find_rust_cond_brace(cur_ns, m.end(), len(cur_ns))
            if brace_idx is None:
                continue
            cond_raw_ns = cur_ns[m.end() : brace_idx]
            cond_raw_code = cur_code[m.end() : brace_idx]
            cond_ns = cond_raw_ns.strip()
            if re.match(r"^let\b", cond_ns):
                continue
            cond_val = _eval_rust_static_bool_cond(
                cond_raw_ns, cond_code=cond_raw_code
            )
            if cond_val is not False:
                continue
            close_idx = _find_matching_delimiter_in_code(cur_ns, brace_idx)
            if close_idx is None:
                continue
            end_idx = close_idx + 1
            changed |= _blank_span(code_chars, m.start(), end_idx)
            changed |= _blank_span(ns_chars, m.start(), end_idx)
            if kw == "if":
                else_m = re.match(r"\s*(else)\b", cur_ns[end_idx:])
                if else_m is not None:
                    e_start = end_idx + else_m.start(1)
                    e_end = end_idx + else_m.end(1)
                    changed |= _blank_span(code_chars, e_start, e_end)
                    changed |= _blank_span(ns_chars, e_start, e_end)
                else:
                    prev_else = re.search(
                        r"\b(else)\s*$", cur_ns[: m.start()]
                    )
                    if prev_else is not None:
                        changed |= _blank_span(
                            code_chars, prev_else.start(1), prev_else.end(1)
                        )
                        changed |= _blank_span(
                            ns_chars, prev_else.start(1), prev_else.end(1)
                        )

        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)
        for fm in re.finditer(r"\bfor\b", cur_ns[1:]):
            f_start = fm.start() + 1
            b_open = _find_rust_cond_brace(cur_ns, f_start + 3, len(cur_ns))
            if b_open is None:
                continue
            b_close = _find_matching_delimiter_in_code(cur_ns, b_open)
            if b_close is None:
                continue
            hdr_ns = cur_ns[f_start + 3 : b_open]
            in_m = re.search(r"\bin\b", hdr_ns)
            if in_m is None:
                continue
            it_start = f_start + 3 + in_m.end()
            if _rust_for_iter_is_statically_empty(
                cur_code[it_start:b_open], cur_ns[it_start:b_open]
            ):
                changed |= _blank_span(code_chars, f_start, b_close + 1)
                changed |= _blank_span(ns_chars, f_start, b_close + 1)

        # Strip unconditional block exits before unwrapping `if true`.
        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)
        for open_b, ch in enumerate(cur_ns):
            if ch != "{":
                continue
            close_b = _find_matching_delimiter_in_code(cur_ns, open_b)
            if close_b is None:
                continue
            cut = _rust_block_early_exit_cut(
                cur_ns, open_b, close_b, early_exit_re, code=cur_code
            )
            if cut is not None and cut < close_b:
                changed |= _blank_span(code_chars, cut, close_b)
                changed |= _blank_span(ns_chars, cut, close_b)

        cur_code = "".join(code_chars)
        cur_ns = "".join(ns_chars)
        for m in branch_kw_re.finditer(cur_ns, 1):
            if m.group(1) != "if":
                continue
            brace_idx = _find_rust_cond_brace(cur_ns, m.end(), len(cur_ns))
            if brace_idx is None:
                continue
            cond_raw_ns = cur_ns[m.end() : brace_idx]
            cond_raw_code = cur_code[m.end() : brace_idx]
            cond_ns = cond_raw_ns.strip()
            if re.match(r"^let\b", cond_ns):
                continue
            if (
                _eval_rust_static_bool_cond(cond_raw_ns, cond_code=cond_raw_code)
                is not True
            ):
                continue
            close_idx = _find_matching_delimiter_in_code(cur_ns, brace_idx)
            if close_idx is None:
                continue
            prefix_ws = cur_ns[: m.start()].rstrip()
            if re.search(r"\belse$", prefix_ws):
                # `else if true { ... } else { dead }` -> `else { ... }`
                changed |= _blank_span(code_chars, m.start(), brace_idx)
                changed |= _blank_span(ns_chars, m.start(), brace_idx)
            else:
                changed |= _blank_span(code_chars, m.start(), brace_idx + 1)
                changed |= _blank_span(ns_chars, m.start(), brace_idx + 1)
                changed |= _blank_span(code_chars, close_idx, close_idx + 1)
                changed |= _blank_span(ns_chars, close_idx, close_idx + 1)
            else_end = _skip_rust_else_chain(cur_ns, close_idx)
            if else_end > close_idx + 1:
                changed |= _blank_span(code_chars, close_idx + 1, else_end)
                changed |= _blank_span(ns_chars, close_idx + 1, else_end)

    return "".join(code_chars), "".join(ns_chars)


def _find_rust_closure_body_spans(code_ns: str) -> list[tuple[int, int]]:
    """Return `(body_start, body_end)` spans for Rust closures inside `code_ns`."""
    if "|" not in code_ns:
        return []
    spans: list[tuple[int, int]] = []
    n = len(code_ns)
    i = 0
    while i < n:
        if code_ns[i] != "|":
            i += 1
            continue
        p = i - 1
        while p >= 0 and code_ns[p].isspace():
            p -= 1
        starter = False
        if p >= 0:
            if code_ns[p] in "({[,;=:" or (
                p >= 1 and code_ns[p - 1 : p + 1] == "=>"
            ):
                starter = True
            else:
                wm = re.search(r"([A-Za-z_][A-Za-z0-9_]*)$", code_ns[: p + 1])
                if wm and wm.group(1) in (
                    "move",
                    "async",
                    "static",
                    "return",
                    "yield",
                    "break",
                ):
                    starter = True
        if not starter:
            i += 1
            continue

        if i + 1 < n and code_ns[i + 1] == "|":
            param_end = i + 2
        else:
            j = i + 1
            p_d = 0
            b_d = 0
            a_d = 0
            param_end = -1
            while j < n:
                ch = code_ns[j]
                if ch in "{};":
                    break
                if ch == "(":
                    p_d += 1
                elif ch == ")" and p_d > 0:
                    p_d -= 1
                elif ch == "[":
                    b_d += 1
                elif ch == "]" and b_d > 0:
                    b_d -= 1
                elif ch == "<":
                    a_d += 1
                elif ch == ">" and a_d > 0:
                    a_d -= 1
                elif p_d == 0 and b_d == 0 and a_d == 0 and ch == "|":
                    param_end = j + 1
                    break
                j += 1
            if param_end == -1:
                i += 1
                continue

        k = param_end
        while k < n and code_ns[k].isspace():
            k += 1
        has_ret_arrow = False
        if k + 1 < n and code_ns[k : k + 2] == "->":
            has_ret_arrow = True
            k += 2
            tp_d = 0
            tb_d = 0
            ta_d = 0
            while k < n:
                ch = code_ns[k]
                if ch == "(":
                    tp_d += 1
                elif ch == ")" and tp_d > 0:
                    tp_d -= 1
                elif ch == "[":
                    tb_d += 1
                elif ch == "]" and tb_d > 0:
                    tb_d -= 1
                elif ch == "<":
                    ta_d += 1
                elif ch == ">" and ta_d > 0:
                    ta_d -= 1
                elif tp_d == 0 and tb_d == 0 and ta_d == 0:
                    if ch == "{" or ch in ";)]},":
                        break
                k += 1

        if k < n and code_ns[k] == "{":
            close_b = _find_matching_delimiter_in_code(code_ns, k)
            if close_b is not None:
                spans.append((k, close_b + 1))
                i = param_end
                continue
        if has_ret_arrow:
            i += 1
            continue

        # Single-expression closure body `|args| expr`; skip `| A | B =>` arms.
        m = k
        ep_d = 0
        eb_d = 0
        ebr_d = 0
        saw_fat_arrow = False
        while m < n:
            ch = code_ns[m]
            if ep_d == 0 and eb_d == 0 and ebr_d == 0:
                if code_ns[m : m + 2] == "=>":
                    saw_fat_arrow = True
                    break
                if ch in ",;)]}":
                    break
            if ch == "(":
                ep_d += 1
            elif ch == ")":
                if ep_d == 0:
                    break
                ep_d -= 1
            elif ch == "[":
                eb_d += 1
            elif ch == "]":
                if eb_d == 0:
                    break
                eb_d -= 1
            elif ch == "{":
                ebr_d += 1
            elif ch == "}":
                if ebr_d == 0:
                    break
                ebr_d -= 1
            m += 1
        if not saw_fat_arrow and m > k:
            spans.append((k, m))
            i = param_end
            continue
        i += 1
    return spans


@dataclass(frozen=True)
class _RustFileFacts:
    """File-level Rust helper classifications for capture-origin taint."""

    local_fns: frozenset[str] = frozenset()
    local_free_fns: frozenset[str] = frozenset()
    local_types_or_mods: frozenset[str] = frozenset()
    use_aliases: dict[str, frozenset[str]] | None = None
    capture_fns: frozenset[str] = frozenset()
    driver_fns: frozenset[str] = frozenset()
    capture_cmd_fns: frozenset[str] = frozenset()
    driver_cmd_fns: frozenset[str] = frozenset()
    capture_bin_fns: frozenset[str] = frozenset()
    driver_bin_fns: frozenset[str] = frozenset()
    qualified_capture_fns: frozenset[str] = frozenset()
    qualified_driver_fns: frozenset[str] = frozenset()
    qualified_capture_cmd_fns: frozenset[str] = frozenset()
    qualified_driver_cmd_fns: frozenset[str] = frozenset()
    qualified_capture_bin_fns: frozenset[str] = frozenset()
    qualified_driver_bin_fns: frozenset[str] = frozenset()
    method_capture_types: dict[str, frozenset[str]] | None = None
    method_driver_types: dict[str, frozenset[str]] | None = None
    method_capture_cmd_types: dict[str, frozenset[str]] | None = None
    method_driver_cmd_types: dict[str, frozenset[str]] | None = None
    method_capture_bin_types: dict[str, frozenset[str]] | None = None
    method_driver_bin_types: dict[str, frozenset[str]] | None = None
    method_all_types: dict[str, frozenset[str]] | None = None
    passthrough_cmd_fns: dict[str, int] | None = None
    passthrough_cmd_methods: dict[tuple[str, str], int] | None = None
    fn_return_types: dict[str, str] | None = None
    custom_eq_types: frozenset[str] = frozenset()
    extension_overridden_methods: frozenset[str] = frozenset()
    method_override_types: dict[str, frozenset[str]] | None = None
    fn_local_has_custom_eq_impl: bool = False
    fn_returns_untrusted: frozenset[str] = frozenset()
    qualified_fn_returns_untrusted: frozenset[str] = frozenset()
    method_returns_untrusted_types: dict[str, frozenset[str]] | None = None
    may_exit_success_fns: frozenset[str] = frozenset()
    must_exit_success_fns: frozenset[str] = frozenset()
    qualified_may_exit_success_fns: frozenset[str] = frozenset()
    qualified_must_exit_success_fns: frozenset[str] = frozenset()
    method_may_exit_types: dict[str, frozenset[str]] | None = None
    drop_may_exit_types: frozenset[str] = frozenset()
    extern_exit_fns: frozenset[str] = frozenset()
    fn_authority_families: dict[str, str] | None = None
    test_mod_scope: tuple[str, ...] = ()


@dataclass(frozen=True)
class _PyFileFacts:
    """File-level Python import/helper provenance for fail-closed observation."""

    import_aliases: dict[str, str] | None = None
    local_defs: frozenset[str] = frozenset()
    observed_fns: frozenset[str] = frozenset()
    self_observed_methods: frozenset[str] = frozenset()
    class_observed_methods: dict[str, frozenset[str]] | None = None
    class_all_methods: dict[str, frozenset[str]] | None = None
    local_classes: frozenset[str] = frozenset()
    custom_cmp_classes: frozenset[str] = frozenset()
    may_exit_success_fns: frozenset[str] = frozenset()
    self_may_exit_methods: frozenset[str] = frozenset()
    class_may_exit_methods: dict[str, frozenset[str]] | None = None
    may_os_exit_success_fns: frozenset[str] = frozenset()
    self_may_os_exit_methods: frozenset[str] = frozenset()
    class_may_os_exit_methods: dict[str, frozenset[str]] | None = None
    skip_fns: frozenset[str] = frozenset()
    self_skip_methods: frozenset[str] = frozenset()
    class_skip_methods: dict[str, frozenset[str]] | None = None
    fn_authority_families: dict[str, str] | None = None


@dataclass(frozen=True)
class _AssertionItem:
    """Extracted reachable assertion with assignment-provenance context."""

    full_span: str
    tested_expr: str
    is_observed: bool
    origin_kind: str | None = None
    tested_args: tuple[str, ...] = ()
    rust_env: dict[str, str] | None = None
    rust_type_env: dict[str, str] | None = None
    pure_rust_fns: frozenset[str] = frozenset()
    rust_facts: _RustFileFacts | None = None
    rust_str_taint: dict[str, str] | None = None
    rust_const_strs: dict[str, str] | None = None
    rust_exprs: dict[str, str] | None = None
    rust_exprs_nc: dict[str, str] | None = None
    rust_auth_env: dict[str, str] | None = None
    py_env: dict[str, str] | None = None
    py_const_vals: dict[str, object] | None = None
    py_injected_strs: dict[str, str] | None = None
    py_self_attrs: dict[str, str] | None = None
    py_type_env: dict[str, str] | None = None
    py_facts: _PyFileFacts | None = None
    pure_py_fns: frozenset[str] = frozenset()
    py_auth_env: dict[str, str] | None = None
    py_exprs: dict[str, str] | None = None
    is_err_unwrap: bool = False
    err_unwrap_recv: str = ""

    def subexpr_observed(
        self, subexpr: str, *, require_capture: bool = False
    ) -> bool:
        """Return True iff `subexpr` flows from a verified observation."""
        if not self.is_observed:
            return False
        if require_capture and self.origin_kind != "obs_capture":
            return False
        if self.py_env is not None:
            return _py_expr_has_observed_value(
                subexpr,
                env=self.py_env,
                self_attrs=self.py_self_attrs,
                pure_fns=self.pure_py_fns,
                py_facts=self.py_facts,
                const_vals=self.py_const_vals,
                type_env=self.py_type_env,
            )
        if self.rust_env is not None:
            kind = _rust_expr_origin_kind(
                subexpr,
                rust_env=self.rust_env,
                rust_facts=self.rust_facts,
                rust_type_env=self.rust_type_env,
            )
            if require_capture:
                return kind == "obs_capture"
            return kind in ("obs_capture", "obs_driver", "observed")
        return True


@dataclass(frozen=True)
class _CfgSeq:
    nodes: tuple[object, ...]


@dataclass(frozen=True)
class _CfgItem:
    item: _AssertionItem


@dataclass(frozen=True)
class _CfgBranch:
    branches: tuple[object, ...]


@dataclass(frozen=True)
class _CfgExit:
    is_success: bool


@dataclass(frozen=True)
class _CfgLoop:
    body: object
    guaranteed_at_least_once: bool
    is_infinite: bool = False
    orelse: object | None = None
    label: str | None = None
    is_block: bool = False


@dataclass(frozen=True)
class _CfgLoopJump:
    kind: str  # "break" or "continue"
    label: str | None = None


def _merge_jump_maps(
    *maps: dict[str | None, frozenset[int]],
) -> dict[str | None, frozenset[int]]:
    out: dict[str | None, set[int]] = {}
    for mp in maps:
        for k, vals in mp.items():
            if vals:
                out.setdefault(k, set()).update(vals)
    return {k: frozenset(v) for k, v in out.items() if v}


def _eval_cfg_normal_exit_masks(
    root: object,
    item_mask_fn: Callable[[_AssertionItem], int],
) -> frozenset[int]:
    """Return bitmasks of obligations met on every normal (non-failing) exit."""

    def _eval(
        node: object, in_masks: frozenset[int]
    ) -> tuple[
        frozenset[int],
        frozenset[int],
        dict[str | None, frozenset[int]],
        dict[str | None, frozenset[int]],
    ]:
        empty_map: dict[str | None, frozenset[int]] = {}
        if not in_masks:
            empty: frozenset[int] = frozenset()
            return empty, empty, empty_map, empty_map
        if isinstance(node, _CfgItem):
            m_it = item_mask_fn(node.item)
            return (
                frozenset(m | m_it for m in in_masks),
                frozenset(),
                empty_map,
                empty_map,
            )
        if isinstance(node, _CfgExit):
            if node.is_success:
                return frozenset(), in_masks, empty_map, empty_map
            return frozenset(), frozenset(), empty_map, empty_map
        if isinstance(node, _CfgLoopJump):
            if node.kind == "break":
                return (
                    frozenset(),
                    frozenset(),
                    {node.label: in_masks},
                    empty_map,
                )
            return (
                frozenset(),
                frozenset(),
                empty_map,
                {node.label: in_masks},
            )
        if isinstance(node, _CfgSeq):
            cur = in_masks
            early: set[int] = set()
            brk_maps: list[dict[str | None, frozenset[int]]] = []
            cont_maps: list[dict[str | None, frozenset[int]]] = []
            for child in node.nodes:
                if not cur:
                    break
                cur, e, b_mp, c_mp = _eval(child, cur)
                early.update(e)
                if b_mp:
                    brk_maps.append(b_mp)
                if c_mp:
                    cont_maps.append(c_mp)
            return (
                cur,
                frozenset(early),
                _merge_jump_maps(*brk_maps),
                _merge_jump_maps(*cont_maps),
            )
        if isinstance(node, _CfgBranch):
            ft: set[int] = set()
            early = set()
            brk_maps = []
            cont_maps = []
            for br in node.branches:
                f, e, b_mp, c_mp = _eval(br, in_masks)
                ft.update(f)
                early.update(e)
                if b_mp:
                    brk_maps.append(b_mp)
                if c_mp:
                    cont_maps.append(c_mp)
            return (
                frozenset(ft),
                frozenset(early),
                _merge_jump_maps(*brk_maps),
                _merge_jump_maps(*cont_maps),
            )
        if isinstance(node, _CfgLoop):
            iter_in = in_masks
            body_ft_all: set[int] = set()
            early = set()
            brk_here: set[int] = set()
            cont_here_all: set[int] = set()
            outer_brk_maps: list[dict[str | None, frozenset[int]]] = []
            outer_cont_maps: list[dict[str | None, frozenset[int]]] = []
            while True:
                b_ft, b_e, b_b_mp, b_c_mp = _eval(node.body, iter_in)
                early.update(b_e)
                rem_brk: dict[str | None, frozenset[int]] = {}
                for k, vals in b_b_mp.items():
                    if (k is None and not node.is_block) or (
                        node.label is not None and k == node.label
                    ):
                        brk_here.update(vals)
                    else:
                        rem_brk[k] = vals
                if rem_brk:
                    outer_brk_maps.append(rem_brk)
                step_cont_here: set[int] = set()
                rem_cont: dict[str | None, frozenset[int]] = {}
                for k, vals in b_c_mp.items():
                    if not node.is_block and (
                        k is None or (node.label is not None and k == node.label)
                    ):
                        step_cont_here.update(vals)
                        cont_here_all.update(vals)
                    else:
                        rem_cont[k] = vals
                if rem_cont:
                    outer_cont_maps.append(rem_cont)
                body_ft_all.update(b_ft)
                if node.is_block:
                    break
                next_in = iter_in | b_ft | step_cont_here
                if next_in == iter_in:
                    break
                iter_in = next_in
            outer_brk = _merge_jump_maps(*outer_brk_maps)
            outer_cont = _merge_jump_maps(*outer_cont_maps)
            if node.is_infinite:
                normal_done: frozenset[int] = frozenset()
            elif node.guaranteed_at_least_once:
                normal_done = frozenset(body_ft_all | cont_here_all)
            else:
                normal_done = frozenset(in_masks | body_ft_all | cont_here_all)
            if node.orelse is not None:
                o_ft, o_e, o_b_mp, o_c_mp = _eval(node.orelse, normal_done)
                early.update(o_e)
                return (
                    frozenset(o_ft | brk_here),
                    frozenset(early),
                    _merge_jump_maps(outer_brk, o_b_mp),
                    _merge_jump_maps(outer_cont, o_c_mp),
                )
            return (
                frozenset(normal_done | brk_here),
                frozenset(early),
                outer_brk,
                outer_cont,
            )
        return in_masks, frozenset(), empty_map, empty_map

    ft, early, brk_mp, cont_mp = _eval(root, frozenset({0}))
    leftover_brk = set().union(*brk_mp.values()) if brk_mp else set()
    leftover_cont = set().union(*cont_mp.values()) if cont_mp else set()
    return ft | early | frozenset(leftover_brk) | frozenset(leftover_cont)


PURE_RUST_MACROS = frozenset(
    {
        "format",
        "format_args",
        "concat",
        "stringify",
        "include_str",
        "include_bytes",
        "vec",
        "json",
        "assert",
        "assert_eq",
        "assert_ne",
        "assert_matches",
        "matches",
    }
)
PURE_RUST_METHODS = frozenset(
    {
        "to_string",
        "to_owned",
        "into",
        "from",
        "as_str",
        "as_bytes",
        "as_ref",
        "as_mut",
        "deref",
        "trim",
        "trim_start",
        "trim_end",
        "to_lowercase",
        "to_uppercase",
        "to_ascii_lowercase",
        "to_ascii_uppercase",
        "replace",
        "replacen",
        "split",
        "rsplit",
        "lines",
        "contains",
        "starts_with",
        "ends_with",
        "find",
        "rfind",
        "strip_prefix",
        "strip_suffix",
        "len",
        "is_empty",
        "chars",
        "bytes",
        "iter",
        "into_iter",
        "collect",
        "clone",
        "copied",
        "cloned",
        "get",
        "first",
        "last",
        "unwrap",
        "expect",
        "unwrap_or",
        "unwrap_or_default",
        "unwrap_err",
        "expect_err",
        "is_err",
        "is_ok",
        "is_some",
        "is_none",
        "ok",
        "err",
        "map",
        "and_then",
        "filter",
        "any",
        "all",
    }
)
PURE_RUST_TYPE_PREFIXES = frozenset(
    {
        "String",
        "Vec",
        "Box",
        "Cow",
        "Rc",
        "Arc",
        "PathBuf",
        "Path",
        "OsString",
        "OsStr",
        "BTreeMap",
        "HashMap",
        "BTreeSet",
        "HashSet",
        "CStr",
    }
)
PURE_RUST_IDENT_IGNORED = frozenset(
    {
        "true",
        "false",
        "as",
        "ref",
        "mut",
        "const",
        "static",
        "crate",
        "self",
        "super",
        "in",
        "let",
        "if",
        "else",
        "match",
        "loop",
        "for",
        "while",
        "where",
        "unsafe",
        "async",
        "await",
        "move",
        "dyn",
        "impl",
        "fn",
        "type",
        "struct",
        "enum",
        "trait",
        "pub",
        "return",
        "break",
        "continue",
        "bool",
        "char",
        "str",
        "u8",
        "u16",
        "u32",
        "u64",
        "u128",
        "usize",
        "i8",
        "i16",
        "i32",
        "i64",
        "i128",
        "isize",
        "f32",
        "f64",
    }
)


def _strip_rust_numeric_literals(code_ns: str) -> str:
    return re.sub(
        r"\b(?:0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|\d+(?:_\d+)*)"
        r"(?:u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize)?\b",
        " ",
        code_ns,
    )


def _is_std_assert_qualifier(prefix: str) -> bool:
    """Allow bare `assert!` or `std::`/`core::` paths; skip custom paths."""
    m = re.search(
        r"(?P<path>(?:::\s*)?[A-Za-z_][A-Za-z0-9_]*"
        r"(?:\s*::\s*[A-Za-z_][A-Za-z0-9_]*)*)\s*::\s*$",
        prefix,
    )
    if m is None:
        return not re.search(r"::\s*$", prefix)
    norm = re.sub(r"\s+", "", m.group("path")).lstrip(":")
    head = norm.split("::", 1)[0]
    return head in ("core", "std")


def _check_rust_assertion_macro_shadowing(
    code_ns: str, rel_path: str
) -> str | None:
    """Reject local shadowing definitions or imports of Rust assert/env macros."""
    if re.search(
        r"\bmacro_rules\s*!\s*(?:assert|assert_eq|assert_ne|assert_matches|env|option_env)\b"
        r"|\b(?:pub(?:\([^()]*\))?\s+)?macro\s+"
        r"(?:assert|assert_eq|assert_ne|assert_matches|env|option_env)\b",
        code_ns,
    ):
        return (
            f"{rel_path}: shadowing Rust assertion or env macro definition is "
            "forbidden in regression tests"
        )
    if re.search(r"#\s*\[\s*macro_use\b", code_ns):
        return (
            f"{rel_path}: #[macro_use] is forbidden in Phase-0 regression "
            "test files"
        )
    assert_kw_re = re.compile(
        r"\b(?:assert|assert_eq|assert_ne|assert_matches|option_env)\b"
    )
    for m in re.finditer(r"(?:^|[;\n{}\s])(?:pub(?:\([^()]*\))?\s+)?use\s+", code_ns):
        semi = code_ns.find(";", m.end())
        use_body = code_ns[m.end() : semi if semi != -1 else len(code_ns)]
        if re.search(
            r"\bas\s+(?:assert|assert_eq|assert_ne|assert_matches|env|option_env)\b",
            use_body,
        ):
            return (
                f"{rel_path}: renaming import `as assert*`/`as env` is "
                "forbidden in regression test files"
            )
        norm_use = re.sub(r"\s+", "", use_body).lstrip(":")
        root = norm_use.split("::", 1)[0] if "::" in norm_use else norm_use
        if "*" in norm_use and root not in ("core", "std", "super"):
            return (
                f"{rel_path}: non-std glob import `{use_body.strip()}` cannot "
                "guarantee unshadowed assertion macros"
            )
        if assert_kw_re.search(use_body) and root not in ("core", "std"):
            return (
                f"{rel_path}: importing assertion/env macro `{use_body.strip()}` "
                "outside `std`/`core` is forbidden"
            )
    return None


def _find_rust_top_level_equal(stmt_ns: str) -> int | None:
    """Return index of top-level `=` (not `==`, `!=`, `<=`, `>=`, `=>`)."""
    p_d = 0
    b_d = 0
    br_d = 0
    a_d = 0
    n = len(stmt_ns)
    i = 0
    while i < n:
        ch = stmt_ns[i]
        nxt = stmt_ns[i + 1] if i + 1 < n else ""
        prev = stmt_ns[i - 1] if i > 0 else ""
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif ch == "<" and nxt not in ("<", "="):
            a_d += 1
        elif ch == ">" and a_d > 0 and prev not in ("-", "="):
            a_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and a_d == 0 and ch == "=":
            if prev not in ("=", "!", "<", ">") and nxt not in ("=", ">"):
                return i
        i += 1
    return None


def _extract_rust_pattern_idents(pat_ns: str) -> list[str]:
    """Extract lowercase variable bindings from a Rust `let`/LHS pattern."""
    cleaned = pat_ns.strip()
    decl_m = re.match(
        r"^(?:pub(?:\([^()]*\))?\s+)?(?:let|const|static)\b", cleaned
    )
    if decl_m is not None:
        cleaned = cleaned[decl_m.end() :].lstrip()
    # Strip trailing `: Type` annotation at depth 0 before `=`.
    p_d = 0
    b_d = 0
    br_d = 0
    for idx, ch in enumerate(cleaned):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == ":":
            if cleaned[idx : idx + 2] != "::" and (
                idx == 0 or cleaned[idx - 1] != ":"
            ):
                cleaned = cleaned[:idx]
                break
    out: list[str] = []
    for tok in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", cleaned):
        if tok in PURE_RUST_IDENT_IGNORED or tok == "_":
            continue
        if tok[0].islower() or tok[0] == "_":
            out.append(tok)
    return out


def _extract_rust_lhs_type_annotation(pat_ns: str) -> str | None:
    """Extract a simple nominal type name from `let x: Type = ...` if present."""
    cleaned = pat_ns.strip()
    p_d = b_d = br_d = 0
    for idx, ch in enumerate(cleaned):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == ":":
            if cleaned[idx : idx + 2] != "::" and (
                idx == 0 or cleaned[idx - 1] != ":"
            ):
                ty_part = cleaned[idx + 1 :].strip()
                ty_part = re.sub(
                    r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?)+",
                    "",
                    ty_part,
                )
                m = re.match(
                    r"^(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Z][A-Za-z0-9_]*)\b",
                    ty_part,
                )
                return m.group(1) if m is not None else None
    return None


def _parse_rust_use_tree(
    tree_str: str, prefix: str = ""
) -> list[tuple[str, str]]:
    """Flatten a Rust `use` tree into `(local_name, target_path)` pairs."""
    s = tree_str.strip().lstrip(":").strip()
    if not s:
        return []
    brace_pos = -1
    p_d = b_d = 0
    for idx, ch in enumerate(s):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif p_d == 0 and b_d == 0 and ch == "{":
            brace_pos = idx
            break
    if brace_pos != -1:
        close_b = _find_matching_delimiter_in_code(s, brace_pos)
        if close_b is None:
            return []
        head = re.sub(r"\s+", "", s[:brace_pos]).strip(":")
        new_prefix = f"{prefix}::{head}" if (prefix and head) else (head or prefix)
        inner = s[brace_pos + 1 : close_b]
        out: list[tuple[str, str]] = []
        for part in _split_top_level_commas(inner):
            out.extend(_parse_rust_use_tree(part, new_prefix))
        return out
    as_m = re.search(r"\bas\s+([A-Za-z_][A-Za-z0-9_]*)\s*$", s)
    if as_m is not None:
        alias = as_m.group(1)
        target = re.sub(r"\s+", "", s[: as_m.start()]).strip(":")
    else:
        target = re.sub(r"\s+", "", s).strip(":")
        alias = target.rsplit("::", 1)[-1] if target else ""
    if alias == "*":
        glob_root = (
            prefix
            if target == "*"
            else (
                f"{prefix}::{target[:-3]}"
                if prefix and target.endswith("::*")
                else (target[:-3] if target.endswith("::*") else "")
            )
        )
        if glob_root in ("std::process", "core::process"):
            return [("exit", f"{glob_root}::exit"), ("abort", f"{glob_root}::abort")]
        if glob_root == "libc":
            return [
                (fn, f"libc::{fn}")
                for fn in ("exit", "_exit", "_Exit", "quick_exit")
            ]
        return []
    if not target or not alias or alias == "_":
        return []
    if target == "self":
        if not prefix:
            return []
        local_name = prefix.rsplit("::", 1)[-1] if alias == "self" else alias
        return [(local_name, prefix)]
    full_target = f"{prefix}::{target}" if prefix else target
    return [(alias, full_target)]


def _collect_rust_use_aliases(code_ns: str) -> dict[str, frozenset[str]]:
    """Collect `local_name -> target_paths` from all Rust `use ...;` items."""
    raw: dict[str, set[str]] = {}
    for m in re.finditer(
        r"(?:^|[;\n{}\s])(?:pub(?:\([^()]*\))?\s+)?use\s+", code_ns
    ):
        semi = code_ns.find(";", m.end())
        if semi == -1:
            continue
        use_body = code_ns[m.end() : semi]
        for local_name, target_path in _parse_rust_use_tree(use_body):
            raw.setdefault(local_name, set()).add(target_path)
    return {k: frozenset(v) for k, v in raw.items()}


def _collect_rust_local_types_or_mods(code_ns: str) -> frozenset[str]:
    """Collect local `struct`/`enum`/`union`/`type`/`trait`/`mod` names."""
    return frozenset(
        m.group(1)
        for m in re.finditer(
            r"\b(?:struct|enum|union|type|trait|mod)\s+([A-Za-z_][A-Za-z0-9_]*)\b",
            code_ns,
        )
    )


RUST_SPOOFABLE_TRAITS = frozenset(
    {
        "PartialEq",
        "Eq",
        "PartialOrd",
        "Ord",
        "Deref",
        "DerefMut",
        "AsRef",
        "Borrow",
        "Display",
        "Debug",
        "ToString",
    }
)
RUST_ASSERT_SPOOFABLE_METHODS = frozenset(
    {
        "contains",
        "starts_with",
        "ends_with",
        "find",
        "rfind",
        "strip_prefix",
        "strip_suffix",
        "matches",
        "match_indices",
        "is_err",
        "is_ok",
        "is_some",
        "is_none",
        "success",
        "code",
        "eq",
        "ne",
        "as_str",
        "as_bytes",
        "as_ref",
        "to_string",
        "deref",
        "borrow",
        "unwrap_err",
        "expect_err",
    }
)
ITREE_DIFF_VALUE_TYPES_AND_VARIANTS = frozenset(
    {
        "AuthorityRunResult",
        "CallerFrameLaw",
        "CallerFrameSnapshot",
        "CaseCategory",
        "CaseReport",
        "ConservativeRefKind",
        "DifferentialConfig",
        "DifferentialEngine",
        "DifferentialReport",
        "DisclosedGapKind",
        "DisclosedGapSpec",
        "EnvAction",
        "EnvSchedule",
        "ExpectedCaseClass",
        "ExpectedConservativeSpec",
        "ExpectedUbSpec",
        "IntKind",
        "LeanProgramSpec",
        "LeanTraceMode",
        "LeanTraceSession",
        "MetamorphicDualityReceipt",
        "MetamorphicStatus",
        "MetamorphicTwin",
        "ObservableEvent",
        "ObservableSpine",
        "OrderingVal",
        "ResolvedProvenance",
        "ReturnShape",
        "RustcDualResult",
        "ScheduleError",
        "SpineCompareMode",
        "TerminalOutcome",
        "TraceTestCase",
        "TraceVal",
        "TraceVerdict",
        "UbFaultClass",
        "VerdictCounts",
        # TerminalOutcome variants
        "Returned",
        "Unwound",
        "Aborted",
        "Diverged",
        "FaultUb",
        "CaptureRefused",
        # TraceVal variants
        "Scalar",
        "Bool",
        "Char",
        "Ordering",
        "Unit",
        "Enum",
        "Tuple",
        "PaddedBytes",
        # OrderingVal variants
        "Less",
        "Equal",
        "Greater",
        # TraceVerdict variants
        "Agree",
        "DegradedNoMiri",
        "DegradedNoLean",
        "UnsoundAccept",
        "ConservativeOverApprox",
        "DisclosedGapArtifact",
        "ToolError",
        # UbFaultClass variants
        "ScheduledReturnDecode",
        "UnreachableOrNoUnwind",
        "UncheckedShiftOverflow",
        "UncheckedArithOrDivOverflow",
        "PointerOrMemoryAccess",
        "InvalidValueOrUninit",
        "Unclassified",
        # ObservableEvent / EnvAction / ScheduleError / Mode variants
        "CallEnter",
        "CallReturn",
        "CallUnwind",
        "CallerFrameCheck",
        "ReturnBytes",
        "Unwind",
        "Abort",
        "UnconsumedActions",
        "PayloadSizeMismatch",
        "CompositionalITree",
        "StrictVerbatim",
        "ObsErasedCallsOnly",
        "OutcomeOnly",
        "CallerRawPtrAliasing",
        "UnbridgedSemantics",
        "ScheduledAbort",
        "FuzzGenerated",
    }
)
TRUSTED_RUST_VALUE_TYPES = frozenset(
    {
        "__literal__",
        "__primitive__",
        "String",
        "str",
        "Vec",
        "Box",
        "Cow",
        "Rc",
        "Arc",
        "Option",
        "Some",
        "None",
        "Result",
        "Ok",
        "Err",
        "Output",
        "ExitStatus",
        "ExitCode",
        "Value",
        "Path",
        "PathBuf",
        "OsStr",
        "OsString",
        "FaultKind",
        "StepResult",
        "VerifyReceipt",
        "ProcessOutcome",
        "ExecutedRun",
        "bool",
        "char",
        "u8",
        "u16",
        "u32",
        "u64",
        "u128",
        "usize",
        "i8",
        "i16",
        "i32",
        "i64",
        "i128",
        "isize",
        "f32",
        "f64",
    }
) | ITREE_DIFF_VALUE_TYPES_AND_VARIANTS
TRUSTED_RUST_PROJECTION_PREFIXES = frozenset(
    {
        "std",
        "core",
        "alloc",
        "serde_json",
        "String",
        "str",
        "Vec",
        "Box",
        "Cow",
        "Option",
        "Result",
        "Some",
        "None",
        "Ok",
        "Err",
        "Path",
        "PathBuf",
        "OsStr",
        "OsString",
        "Value",
        "FaultKind",
        "StepResult",
        "ExitStatus",
        "ExitCode",
        "Output",
        "anneal_testkit",
        "anneal_rustc_capture",
        "cargo_anneal",
        "anneal_itree_diff",
        "anneal_audit",
    }
) | ITREE_DIFF_VALUE_TYPES_AND_VARIANTS


def _extract_rust_impl_trait_and_target(
    header_ns: str,
) -> tuple[str | None, str | None, frozenset[str], frozenset[str]]:
    """Return `(trait_name, target_type, trait_type_args, generic_params)` for an `impl` header."""
    s = header_ns.strip()
    m = re.match(r"^(?:unsafe\s+)?impl\b", s)
    if m is None:
        return None, None, frozenset(), frozenset()
    rest = s[m.end() :].lstrip()
    generic_params: set[str] = set()
    if rest.startswith("<"):
        depth = 0
        end_g = -1
        for idx, ch in enumerate(rest):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
                if depth == 0:
                    end_g = idx
                    break
        if end_g != -1:
            g_inner = rest[1:end_g]
            for gp in _split_top_level_commas(g_inner):
                gp_s = gp.strip()
                if gp_s.startswith("'"):
                    continue
                gm = re.match(r"^(?:const\s+)?([A-Z][A-Za-z0-9_]*)\b", gp_s)
                if gm is not None:
                    generic_params.add(gm.group(1))
            rest = rest[end_g + 1 :].lstrip()
    where_m = re.search(r"\bwhere\b", rest)
    if where_m is not None:
        rest = rest[: where_m.start()].strip()
    for_pos: int | None = None
    p_d = b_d = a_d = 0
    for idx in range(len(rest)):
        ch = rest[idx]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "<":
            a_d += 1
        elif ch == ">" and a_d > 0:
            a_d -= 1
        elif p_d == 0 and b_d == 0 and a_d == 0 and rest[idx : idx + 3] == "for":
            prev_ok = idx == 0 or not (rest[idx - 1].isalnum() or rest[idx - 1] == "_")
            nxt_ok = idx + 3 == len(rest) or not (
                rest[idx + 3].isalnum() or rest[idx + 3] == "_"
            )
            if prev_ok and nxt_ok:
                for_pos = idx
                break
    trait_name: str | None = None
    trait_args: set[str] = set()
    if for_pos is not None:
        tr_part = rest[:for_pos].strip()
        target_part = rest[for_pos + 3 :].strip()
        tr_head = tr_part.split("<", 1)[0].strip()
        tr_m = re.match(
            r"^(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Z][A-Za-z0-9_]*)",
            tr_head,
        )
        if tr_m is not None:
            trait_name = tr_m.group(1)
        if "<" in tr_part:
            arg_str = tr_part[tr_part.find("<") + 1 :]
            for cap in re.findall(r"\b([A-Z][A-Za-z0-9_]*)\b", arg_str):
                if cap not in generic_params:
                    trait_args.add(cap)
    else:
        target_part = rest.strip()
    target_clean = re.sub(
        r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?)+", "", target_part
    )
    tm = re.match(
        r"^(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Za-z_][A-Za-z0-9_]*)",
        target_clean,
    )
    target_ty = tm.group(1) if tm is not None else None
    return trait_name, target_ty, frozenset(trait_args), frozenset(generic_params)


def _collect_rust_impl_and_extern_facts(
    code_ns: str,
) -> tuple[frozenset[str], frozenset[str], dict[str, frozenset[str]], bool, frozenset[str]]:
    """Collect custom-eq types, overridden assertion methods, and extern exit fns."""
    custom_eq_types: set[str] = set()
    ext_overridden: set[str] = set()
    method_overrides: dict[str, set[str]] = {}
    has_custom_eq_impl = False
    extern_exit_fns: set[str] = set()

    # Detect `extern "C" { fn exit(...); fn _exit(...); }` declarations.
    for em in re.finditer(r"\bextern\b[^{;]*\{", code_ns):
        b_open = em.end() - 1
        b_close = _find_matching_delimiter_in_code(code_ns, b_open)
        if b_close is None:
            continue
        ext_body = code_ns[b_open + 1 : b_close]
        for fm in re.finditer(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", ext_body):
            if fm.group(1) in ("exit", "_exit", "_Exit", "quick_exit"):
                extern_exit_fns.add(fm.group(1))

    # Inspect item-level `impl ... { ... }` blocks (skip `fn f(x: impl T)`).
    for im in re.finditer(r"\bimpl\b", code_ns):
        prev = code_ns[: im.start()].rstrip()
        if prev.endswith((":", "->", "(", ",", "<")):
            continue
        if re.search(r"\b(?:return|let)\s*$", prev):
            continue
        # Scan forward to opening `{` at depth 0 (stop on `;`).
        j = im.end()
        p_d = b_d = a_d = 0
        body_open: int | None = None
        while j < len(code_ns):
            ch = code_ns[j]
            if ch == "(":
                p_d += 1
            elif ch == ")" and p_d > 0:
                p_d -= 1
            elif ch == "[":
                b_d += 1
            elif ch == "]" and b_d > 0:
                b_d -= 1
            elif ch == "<":
                a_d += 1
            elif ch == ">" and a_d > 0:
                a_d -= 1
            elif p_d == 0 and b_d == 0 and a_d == 0:
                if ch == ";":
                    break
                if ch == "{":
                    body_open = j
                    break
            j += 1
        if body_open is None:
            continue
        body_close = _find_matching_delimiter_in_code(code_ns, body_open)
        if body_close is None:
            continue
        hdr = code_ns[im.start() : body_open]
        trait_name, target_ty, trait_args, generic_params = (
            _extract_rust_impl_trait_and_target(hdr)
        )
        body_ns = code_ns[body_open + 1 : body_close]

        if trait_name in RUST_SPOOFABLE_TRAITS:
            has_custom_eq_impl = True
            if (
                target_ty
                and target_ty not in TRUSTED_RUST_VALUE_TYPES
                and target_ty not in generic_params
            ):
                custom_eq_types.add(target_ty)
            for ta in trait_args:
                if ta not in TRUSTED_RUST_VALUE_TYPES:
                    custom_eq_types.add(ta)
            # Blanket `impl<T> PartialEq...` or `impl PartialEq...` on a
            # trusted type can intercept comparisons on trusted values too.
            if target_ty in generic_params:
                custom_eq_types.add("__blanket__")

        # Record any assertion/projection method overrides inside the impl body.
        for fm in re.finditer(
            r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(", body_ns
        ):
            mname = fm.group(1)
            if mname not in RUST_ASSERT_SPOOFABLE_METHODS:
                continue
            if target_ty:
                method_overrides.setdefault(mname, set()).add(target_ty)
                if (
                    target_ty not in TRUSTED_RUST_VALUE_TYPES
                    and target_ty not in generic_params
                ):
                    custom_eq_types.add(target_ty)
            if trait_name is not None and (
                target_ty in TRUSTED_RUST_VALUE_TYPES
                or target_ty in generic_params
                or target_ty is None
            ):
                ext_overridden.add(mname)

    return (
        frozenset(custom_eq_types),
        frozenset(ext_overridden),
        {k: frozenset(v) for k, v in method_overrides.items()},
        has_custom_eq_impl,
        frozenset(extern_exit_fns),
    )


def _extract_rust_fn_return_type(
    sig_after_rparen_ns: str, enclosing_impl: str | None
) -> str | None:
    """Extract nominal return type name from a Rust fn signature tail."""
    arrow_m = re.search(r"->\s*([\s\S]+)$", sig_after_rparen_ns)
    if arrow_m is None:
        return None
    ret = arrow_m.group(1).strip()
    where_m = re.search(r"\bwhere\b", ret)
    if where_m is not None:
        ret = ret[: where_m.start()].strip()
    ret = re.sub(
        r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?)+", "", ret
    )
    if re.match(r"^impl\b", ret):
        return "__opaque_impl__"
    if re.match(r"^dyn\b", ret):
        return "__opaque_dyn__"
    if ret in ("!", "()"):
        return "__primitive__"
    if re.match(
        r"^(?:str|bool|char|u8|u16|u32|u64|u128|usize|i8|i16|i32|i64|i128|isize|f32|f64)\b",
        ret,
    ):
        return "__primitive__"
    tm = re.match(
        r"^(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Z][A-Za-z0-9_]*)", ret
    )
    if tm is None:
        return None
    tname = tm.group(1)
    if tname == "Self":
        return enclosing_impl
    return tname


def _rust_return_sig_mentions_untrusted_type(
    sig_after_rparen_ns: str,
    enclosing_impl: str | None,
    *,
    local_types: frozenset[str],
    custom_eq_types: frozenset[str],
) -> bool:
    """Return True if a Rust fn return type returns a local/custom-eq/opaque type."""
    arrow_m = re.search(r"->\s*([\s\S]+)$", sig_after_rparen_ns)
    if arrow_m is None:
        return False
    ret = arrow_m.group(1).strip()
    where_m = re.search(r"\bwhere\b", ret)
    if where_m is not None:
        ret = ret[: where_m.start()].strip()
    if re.search(r"\b(?:impl|dyn)\b", ret):
        return True
    for cap in re.findall(r"\b([A-Z][A-Za-z0-9_]*)\b", ret):
        resolved = enclosing_impl if cap == "Self" else cap
        if not resolved:
            continue
        if resolved in custom_eq_types:
            return True
        if resolved in local_types and resolved not in TRUSTED_RUST_VALUE_TYPES:
            return True
    return False


def _infer_rust_expr_type(
    expr_nc: str,
    expr_ns: str,
    *,
    type_env: dict[str, str] | None,
    facts: _RustFileFacts,
) -> str | None:
    """Best-effort nominal struct type inference for a Rust RHS expression."""
    s = expr_ns.strip().rstrip(";").strip()
    s_nc = expr_nc.strip().rstrip(";").strip()
    while s.startswith("(") and s.endswith(")"):
        if _find_matching_delimiter_in_code(s, 0) != len(s) - 1:
            break
        s = s[1:-1].strip()
        if s_nc.startswith("(") and s_nc.endswith(")"):
            s_nc = s_nc[1:-1].strip()
    if not s:
        if s_nc and s_nc[0] in ('"', "'", "b", "r", "c"):
            return "__literal__"
        return None
    s = re.sub(r"^(?:&\s*(?:mut\s+)?|\*\s*)+", "", s)
    # Struct literal `Dummy { ... }`
    if s.endswith("}"):
        open_b = _find_matching_open_delimiter(s, len(s) - 1)
        if open_b is not None:
            head = s[:open_b].strip()
            hm = re.fullmatch(
                r"(?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Z][A-Za-z0-9_]*)",
                head,
            )
            if hm is not None:
                return hm.group(1)
    # Associated or free call `Type::new(...)` / `make_harness(...)`
    if s.endswith(")"):
        open_p = _find_matching_open_delimiter(s, len(s) - 1)
        if open_p is not None:
            head = re.sub(r"\s+", "", s[:open_p]).lstrip(":")
            head = re.sub(r"::<[^()]*>$", "", head)
            ret_map = facts.fn_return_types or {}
            if head in ret_map:
                return ret_map[head]
            if "::" in head:
                parts = head.split("::")
                if len(parts) >= 2 and parts[-2][0:1].isupper():
                    short_q = f"{parts[-2]}::{parts[-1]}"
                    if short_q in ret_map:
                        return ret_map[short_q]
                    if parts[-1] in ("new", "default", "from") or parts[-1].startswith(
                        ("with_", "from_")
                    ):
                        return parts[-2]
            if re.fullmatch(r"[A-Z][A-Za-z0-9_]*", head):
                # Tuple struct constructor `Dummy(...)`
                return head
    # Unit struct or variable
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s):
        if type_env is not None and s in type_env:
            return type_env[s]
        if s[0].isupper() and s not in ("Some", "None", "Ok", "Err"):
            return s
    return None


def _find_matching_open_delimiter(code: str, close_idx: int) -> int | None:
    """Find matching opening delimiter for `code[close_idx]` scanning backward."""
    close_ch = code[close_idx]
    pairs = {")": "(", "]": "[", "}": "{"}
    open_ch = pairs.get(close_ch)
    if open_ch is None:
        return None
    depth = 0
    for idx in range(close_idx, -1, -1):
        ch = code[idx]
        if ch == close_ch:
            depth += 1
        elif ch == open_ch:
            depth -= 1
            if depth == 0:
                return idx
    return None


def _infer_rust_receiver_type(
    expr_nc: str,
    expr_ns: str,
    dot_pos: int,
    *,
    type_env: dict[str, str] | None,
    facts: _RustFileFacts,
) -> str | None:
    """Infer nominal receiver type immediately before `expr_ns[dot_pos] == '.'`."""
    j = dot_pos - 1
    while j >= 0 and expr_ns[j].isspace():
        j -= 1
    if j < 0:
        # Check if `expr_nc` had a literal (e.g. `"foo".to_string()`) blanked
        # in `expr_ns`.
        k = min(dot_pos - 1, len(expr_nc) - 1)
        while k >= 0 and expr_nc[k].isspace():
            k -= 1
        if k >= 0 and expr_nc[k] in ('"', "'", "#"):
            return "__literal__"
        return None
    # Check for a string/char literal right between j and dot_pos in expr_nc.
    if dot_pos <= len(expr_nc):
        between_nc = expr_nc[j + 1 : dot_pos].strip()
        if between_nc and between_nc[-1] in ('"', "'", "#"):
            return "__literal__"
    end_pos = j + 1
    ch = expr_ns[j]
    if ch == "}":
        open_b = _find_matching_open_delimiter(expr_ns, j)
        if open_b is None:
            return None
        k = open_b - 1
        while k >= 0 and expr_ns[k].isspace():
            k -= 1
        start_k = k
        while start_k >= 0 and (
            expr_ns[start_k].isalnum() or expr_ns[start_k] in "_:"
        ):
            start_k -= 1
        head = expr_ns[start_k + 1 : k + 1].strip()
        hm = re.fullmatch(
            r"(?:[A-Za-z_][A-Za-z0-9_]*::)*([A-Z][A-Za-z0-9_]*)", head
        )
        return hm.group(1) if hm is not None else None
    if ch == ")":
        open_p = _find_matching_open_delimiter(expr_ns, j)
        if open_p is None:
            return None
        k = open_p - 1
        while k >= 0 and expr_ns[k].isspace():
            k -= 1
        if k < 0 or expr_ns[k] in "(,;=!&|{":
            # Parenthesized expr `(Dummy { ... }).execute()`
            return _infer_rust_expr_type(
                expr_nc[open_p + 1 : j],
                expr_ns[open_p + 1 : j],
                type_env=type_env,
                facts=facts,
            )
        start_k = k
        while start_k >= 0 and (
            expr_ns[start_k].isalnum() or expr_ns[start_k] in "_:<> "
        ):
            if expr_ns[start_k] == " " and start_k > 0 and expr_ns[start_k - 1] not in ":<":
                break
            start_k -= 1
        callee_start = start_k + 1
        if callee_start > 0 and expr_ns[callee_start - 1] == ".":
            return None
        return _infer_rust_expr_type(
            expr_nc[callee_start:end_pos],
            expr_ns[callee_start:end_pos],
            type_env=type_env,
            facts=facts,
        )
    if ch.isalnum() or ch == "_":
        start_k = j
        while start_k >= 0 and (
            expr_ns[start_k].isalnum() or expr_ns[start_k] == "_"
        ):
            start_k -= 1
        ident = expr_ns[start_k + 1 : end_pos]
        if start_k >= 0 and expr_ns[start_k] == ".":
            return None
        if ident in ("true", "false"):
            return "__literal__"
        if type_env is not None and ident in type_env:
            return type_env[ident]
        if ident[0].isupper() and ident not in ("Some", "None", "Ok", "Err"):
            return ident
    return None


def _resolve_rust_qualified_path(
    path: str, facts: _RustFileFacts
) -> list[str]:
    """Expand `path` through `facts.use_aliases` if its leading segment is imported."""
    parts = path.split("::")
    head = parts[0]
    aliases = facts.use_aliases or {}
    if head in aliases:
        rest = parts[1:]
        return ["::".join([tgt, *rest]) for tgt in sorted(aliases[head])]
    return [path]


def _normalize_local_rust_path(path: str, test_mod_scope: tuple[str, ...]) -> list[str]:
    """Return candidate file-relative qualified keys for a local Rust path."""
    p = path.lstrip(":")
    cands: list[str] = [p]
    for prefix in ("crate::", "self::"):
        if p.startswith(prefix):
            cands.append(p[len(prefix) :])
    if p.startswith("super::"):
        up = list(test_mod_scope)
        rem = p
        while rem.startswith("super::"):
            rem = rem[len("super::") :]
            if up:
                up.pop()
        cands.append("::".join([*up, rem]) if up else rem)
    elif test_mod_scope and "::" not in p:
        cands.append("::".join([*test_mod_scope, p]))
    elif test_mod_scope:
        cands.append("::".join([*test_mod_scope, p]))
    return cands


CAPTURE_CARGO_BIN_ENV_RE = re.compile(
    r'^(?:(?:::\s*)?(?:core|std)\s*::\s*)?(?:option_)?env\s*!\s*\(\s*"'
    r'CARGO_BIN_EXE_(?:anneal-rustc-capture(?:-test-bin)?'
    r'|anneal-diff-capture-test-bin'
    r'|cargo-anneal(?:-test-bin)?)'
    r'"\s*\)$'
)
DRIVER_CARGO_BIN_ENV_RE = re.compile(
    r'^(?:(?:::\s*)?(?:core|std)\s*::\s*)?(?:option_)?env\s*!\s*\(\s*"'
    r'CARGO_BIN_EXE_(?:anneal-audit(?:-test-bin)?'
    r'|anneal-mir-eval|itree[-_]diff|anneal-diff)'
    r'"\s*\)$'
)
CAPTURE_INVOCATION_HELPER_RE = re.compile(
    r"\b(build_capture_(?:cargo_)?invocation[A-Za-z0-9_]*)\b"
)
DRIVER_INVOCATION_HELPER_RE = re.compile(
    r"\b(build_(?:lean|mir_eval|miri_run|rustc_run)_invocation[A-Za-z0-9_]*)\b"
)
CAPTURE_HARNESS_FN_RE = re.compile(
    r"^(?:run_capture|try_capture|invoke_capture|exec_capture"
    r"|capture_crate|capture_selected|captures_cleanly)[A-Za-z0-9_]*$"
)
DRIVER_HARNESS_FN_RE = re.compile(
    r"^(?:run_lean|eval_lean|run_mir_eval|run_miri|matches_miri"
    r"|run_differential|run_itree|run_audit|audit_|run_verify)[A-Za-z0-9_]*$"
)
RUST_OBS_STATES = frozenset({"obs_capture", "obs_driver", "observed"})
INDEPENDENT_ORACLE_FAMILIES = frozenset(
    {
        "oracle_miri",
        "oracle_mir_eval",
        "oracle_lean",
        "oracle_rustc",
        "oracle_diff",
    }
)


def _families_establish_oracle_parity(
    l_fam: str | None, r_fam: str | None
) -> bool:
    """Require one capture + independent FaultUb/oracle (or two distinct oracles)."""
    if l_fam is None or r_fam is None:
        return False
    if l_fam == "capture":
        return r_fam in INDEPENDENT_ORACLE_FAMILIES
    if r_fam == "capture":
        return l_fam in INDEPENDENT_ORACLE_FAMILIES
    return (
        l_fam in INDEPENDENT_ORACLE_FAMILIES
        and r_fam in INDEPENDENT_ORACLE_FAMILIES
        and l_fam != r_fam
    )


def _rust_cargo_bin_env_authority_family(raw_expr: str) -> str | None:
    """Classify `env!(\"CARGO_BIN_EXE_...\")` into capture vs independent oracle."""
    s = raw_expr.strip()
    m = re.fullmatch(
        r'(?:(?:::\s*)?(?:core|std)\s*::\s*)?(?:option_)?env\s*!\s*\(\s*"'
        r'CARGO_BIN_EXE_([^"]+)"\s*\)',
        s,
    )
    if m is None:
        return None
    bin_name = m.group(1)
    if bin_name.startswith(("anneal-rustc-capture", "anneal-diff-capture", "cargo-anneal")):
        return "capture"
    if bin_name == "anneal-mir-eval":
        return "oracle_mir_eval"
    if bin_name in ("itree-diff", "itree_diff", "anneal-diff"):
        return "oracle_diff"
    if bin_name.startswith("anneal-audit"):
        return "driver_audit"
    return None


def _rust_harness_name_authority_family(name: str) -> str | None:
    """Classify Rust test harness helper names into capture vs independent oracle."""
    if CAPTURE_HARNESS_FN_RE.fullmatch(name) is not None:
        return "capture"
    if name.startswith(("run_miri", "matches_miri")):
        return "oracle_miri"
    if name.startswith("run_mir_eval"):
        return "oracle_mir_eval"
    if name.startswith(("run_lean", "eval_lean")):
        return "oracle_lean"
    if name.startswith(("run_differential", "run_itree")):
        return "oracle_diff"
    if name.startswith(("run_audit", "audit_", "run_verify")):
        return "driver_audit"
    return None


def _rust_invocation_helper_authority_family(name: str) -> str | None:
    """Classify `build_*_invocation*` helpers into capture vs independent oracle."""
    if CAPTURE_INVOCATION_HELPER_RE.fullmatch(name) is not None:
        return "capture"
    if name.startswith("build_miri_run_invocation"):
        return "oracle_miri"
    if name.startswith("build_mir_eval_invocation"):
        return "oracle_mir_eval"
    if name.startswith("build_lean_invocation"):
        return "oracle_lean"
    if name.startswith("build_rustc_run_invocation"):
        return "oracle_rustc"
    return None


def _rust_qualified_path_authority_family(
    expanded_path: str, facts: _RustFileFacts
) -> str | None:
    """Classify a resolved Rust path into capture vs independent oracle family."""
    ep = expanded_path.lstrip(":")
    fn_map = facts.fn_authority_families or {}
    cands = _normalize_local_rust_path(ep, facts.test_mod_scope)
    for c in (ep, *cands):
        if c in fn_map:
            return fn_map[c]
    if "::" in ep:
        head = ep.split("::", 1)[0]
        if head in facts.local_types_or_mods:
            return None
        if ep.startswith(
            ("anneal_itree_diff::lean_trace_runner::",)
        ) or head == "LeanTraceSession":
            return "oracle_lean"
        if head in ("anneal_rustc_capture", "cargo_anneal"):
            return "capture"
        if head == "MirEvalAdapter":
            return "oracle_mir_eval"
        if head == "MiriRunner":
            return "oracle_miri"
        if head == "RustcRunner":
            return "oracle_rustc"
        if head in ("anneal_itree_diff", "DifferentialEngine"):
            return "oracle_diff"
        if head == "anneal_audit":
            return "driver_audit"
    return None


def _rust_command_new_authority_family(
    expr_nc: str,
    expr_ns: str,
    *,
    rust_auth_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
) -> tuple[str | None, bool]:
    """Classify `Command::new(<arg>)` calls into capture vs independent oracle."""
    facts = rust_facts or _RustFileFacts()
    found: set[str] = set()
    saw_unverified = False
    for m in RUST_COMMAND_NEW_RE.finditer(expr_ns):
        if not _rust_is_std_command_path(m.group(1), facts):
            saw_unverified = True
            continue
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(expr_ns, open_p)
        if close_p is None:
            saw_unverified = True
            continue
        arg_nc = expr_nc[open_p + 1 : close_p].strip()
        arg_ns = expr_ns[open_p + 1 : close_p].strip()
        fam = _rust_cargo_bin_env_authority_family(arg_nc)
        if fam is None:
            lit = _decode_any_rust_string_literal(arg_nc)
            if lit is not None:
                base = PurePosixPath(lit).name
                if base in ("anneal-rustc-capture", "cargo-anneal"):
                    fam = "capture"
                elif base == "anneal-mir-eval":
                    fam = "oracle_mir_eval"
                elif base in ("itree-diff", "itree_diff", "anneal-diff"):
                    fam = "oracle_diff"
                elif base in ("lean", "lake"):
                    fam = "oracle_lean"
                elif base == "miri":
                    fam = "oracle_miri"
                elif base == "rustc":
                    fam = "oracle_rustc"
                elif base == "cargo" and re.search(
                    r'\.\s*(?:arg|args)\s*\([^)]*"miri"', expr_nc[close_p + 1 :]
                ):
                    fam = "oracle_miri"
                elif base == "anneal-audit":
                    fam = "driver_audit"
        if fam is None and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", arg_ns):
            if rust_auth_env is not None:
                fam = rust_auth_env.get(arg_ns)
        if fam is None:
            saw_unverified = True
        else:
            found.add(fam)
    if saw_unverified or len(found) != 1:
        return None, saw_unverified or len(found) > 1
    return next(iter(found)), False


def _rust_expr_authority_family(
    expr_nc: str,
    expr_ns: str | None = None,
    *,
    rust_auth_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
    rust_type_env: dict[str, str] | None = None,
    rust_exprs_nc: dict[str, str] | None = None,
) -> str | None:
    """Return canonical authority family (`capture`, `oracle_*`, etc.) or None."""
    if expr_ns is None:
        scanned = scan_rust_tokens(expr_nc)
        s_nc = scanned.code_no_comments
        s_ns = scanned.code_no_strings_or_comments
    else:
        s_nc = expr_nc
        s_ns = expr_ns
    s_nc, s_ns = _rust_blank_closures_and_fallbacks(s_nc, s_ns)
    facts = rust_facts or _RustFileFacts()
    aliases = facts.use_aliases or {}
    local_free = facts.local_free_fns or facts.local_fns
    fn_map = facts.fn_authority_families or {}
    found: set[str] = set()

    bin_fam = _rust_cargo_bin_env_authority_family(s_nc)
    if bin_fam is not None:
        return bin_fam

    tc_m = re.search(
        r"\.\s*(capture_bin|cargo_anneal_bin|audit_bin|mir_eval_bin)\s*\(\s*\)\s*$",
        s_ns.strip().rstrip(";").strip(),
    )
    if tc_m is not None and "Toolchain" not in facts.local_types_or_mods:
        mname = tc_m.group(1)
        if mname in ("capture_bin", "cargo_anneal_bin"):
            return "capture"
        if mname == "mir_eval_bin":
            return "oracle_mir_eval"
        if mname == "audit_bin":
            return "driver_audit"

    cmd_fam, saw_unverified_cmd = _rust_command_new_authority_family(
        s_nc, s_ns, rust_auth_env=rust_auth_env, rust_facts=facts
    )
    if cmd_fam is not None and not saw_unverified_cmd:
        found.add(cmd_fam)

    for hm in CAPTURE_INVOCATION_HELPER_RE.finditer(s_ns):
        hname = hm.group(1)
        if rust_auth_env and hname in rust_auth_env:
            found.add(rust_auth_env[hname])
        elif hname not in local_free:
            found.add("capture")

    for hm in DRIVER_INVOCATION_HELPER_RE.finditer(s_ns):
        hname = hm.group(1)
        if rust_auth_env and hname in rust_auth_env:
            found.add(rust_auth_env[hname])
        elif hname not in local_free:
            hf = _rust_invocation_helper_authority_family(hname)
            if hf is not None:
                found.add(hf)

    for m in re.finditer(
        r"(?<!\.)\b((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
        r"[A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(",
        s_ns,
    ):
        if m.start() > 0 and s_ns[m.start() - 1] == ".":
            continue
        path = re.sub(r"\s+", "", m.group(1)).lstrip(":")
        if path in PURE_RUST_IDENT_IGNORED:
            continue
        if "::" in path:
            expanded = _resolve_rust_qualified_path(path, facts)
            fams = {
                _rust_qualified_path_authority_family(ep, facts)
                for ep in expanded
            }
            if fams and None not in fams:
                found.update(f for f in fams if f is not None)
        else:
            if rust_auth_env is not None and path in rust_auth_env:
                found.add(rust_auth_env[path])
                continue
            if path in fn_map:
                found.add(fn_map[path])
                continue
            if path in aliases:
                expanded = _resolve_rust_qualified_path(path, facts)
                fams = {
                    _rust_qualified_path_authority_family(ep, facts)
                    for ep in expanded
                }
                if fams and None not in fams:
                    found.update(f for f in fams if f is not None)
                continue
            cands = _normalize_local_rust_path(path, facts.test_mod_scope)
            matched_local = next((fn_map[c] for c in cands if c in fn_map), None)
            if matched_local is not None:
                found.add(matched_local)
            elif path not in local_free and path not in facts.local_types_or_mods:
                hf = _rust_harness_name_authority_family(path)
                if hf is not None:
                    found.add(hf)

    if rust_auth_env is not None:
        stripped = _strip_rust_numeric_literals(s_ns)
        for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\b", stripped):
            ident = m.group(1)
            if ident in PURE_RUST_IDENT_IGNORED or ident in (
                "None",
                "Some",
                "Ok",
                "Err",
            ):
                continue
            before = stripped[: m.start()].rstrip()
            if before.endswith(".") or before.endswith("::"):
                continue
            after = stripped[m.end() :].lstrip()
            if after.startswith(("!", "(", "::")):
                continue
            if ident in rust_auth_env:
                found.add(rust_auth_env[ident])
            elif rust_exprs_nc and ident in rust_exprs_nc and ident not in found:
                rf = _rust_expr_authority_family(
                    rust_exprs_nc[ident],
                    rust_auth_env=rust_auth_env,
                    rust_facts=facts,
                    rust_type_env=rust_type_env,
                    rust_exprs_nc=None,
                )
                if rf is not None:
                    found.add(rf)

    return next(iter(found)) if len(found) == 1 else None
RUST_COMMAND_NEW_RE = re.compile(
    r"(?<!\.)\b((?:(?:::\s*)?(?:std\s*::\s*)?(?:process\s*::\s*))?Command)\s*::\s*new\s*\("
)
RUST_BIN_PATH_WRAPPER_RE = re.compile(
    r"^(?:(?:::\s*)?(?:std|core|alloc)\s*::\s*)?"
    r"(?:(?:path|ffi|string|option)\s*::\s*)?"
    r"(?:(Path)\s*::\s*new|(PathBuf)\s*::\s*from|(OsStr)\s*::\s*new|"
    r"(OsString)\s*::\s*from|(String)\s*::\s*from|(?:(Option)\s*::\s*)?(Some))\s*\("
)
RUST_BIN_TRAILING_ADAPTER_RE = re.compile(
    r"(?:\?\s*$|\.\s*(as_path|as_os_str|as_str|to_path_buf|to_owned|"
    r"to_string|clone|unwrap|expect|as_ref)\s*\([^()]*\)\s*$)"
)
RUST_BIN_MUTATING_METHODS = frozenset(
    {
        "push",
        "push_str",
        "pop",
        "set_file_name",
        "set_extension",
        "clear",
        "truncate",
        "replace_range",
        "insert",
        "insert_str",
        "remove",
        "retain",
        "drain",
        "as_mut_os_string",
        "as_mut_vec",
    }
)


def _rust_invalidate_mutated_bin_vars(
    stmt_ns: str, cur_env: dict[str, str]
) -> None:
    """Drop `bin_capture`/`bin_driver` provenance if a path variable is mutated."""
    bin_vars = [
        k for k, v in cur_env.items() if v in ("bin_capture", "bin_driver")
    ]
    if not bin_vars:
        return
    for v in bin_vars:
        if re.search(rf"&\s*mut\s+{re.escape(v)}\b", stmt_ns) is not None:
            cur_env[v] = "const"
            continue
        for mm in re.finditer(
            rf"\b{re.escape(v)}\s*\.\s*([A-Za-z_][A-Za-z0-9_]*)\s*\(", stmt_ns
        ):
            if mm.group(1) in RUST_BIN_MUTATING_METHODS:
                cur_env[v] = "const"
                break


def _rust_is_std_command_path(cmd_head: str, facts: _RustFileFacts) -> bool:
    """Return True iff `cmd_head` resolves to `std::process::Command` (not shadowed)."""
    norm = re.sub(r"\s+", "", cmd_head).lstrip(":")
    if "Command" in facts.local_types_or_mods:
        return False
    if norm in ("std::process::Command", "process::Command"):
        if norm.startswith("process::") and "process" in (facts.use_aliases or {}):
            return all(
                tgt.lstrip(":") in ("std::process", "process")
                for tgt in (facts.use_aliases or {})["process"]
            )
        return True
    if norm == "Command":
        aliases = facts.use_aliases or {}
        if "Command" in aliases:
            return all(
                tgt.lstrip(":") in ("std::process::Command", "process::Command")
                for tgt in aliases["Command"]
            )
        return True
    return False


def _rust_expr_bin_kind(
    expr_nc: str,
    expr_ns: str | None = None,
    *,
    rust_env: dict[str, str] | None = None,
    rust_type_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
) -> str | None:
    """Return `'bin_capture'` or `'bin_driver'` ONLY for Cargo/authenticated binaries."""
    if expr_ns is None:
        scanned = scan_rust_tokens(expr_nc)
        s_nc = scanned.code_no_comments.strip()
        s_ns = scanned.code_no_strings_or_comments.strip()
    else:
        s_nc = expr_nc.strip()
        s_ns = expr_ns.strip()
    s_nc = s_nc.rstrip(";").strip()
    s_ns = s_ns.rstrip(";").strip()
    facts = rust_facts or _RustFileFacts()
    aliases = facts.use_aliases or {}

    # Unwrap outer parens, `&`/`&mut`, safe path/option wrappers, and
    # non-mutating adapters (never `.join`, `.with_file_name`, `.parent`,
    # `format!`, or `+`).
    for _ in range(8):
        changed = False
        while s_ns.startswith("(") and s_ns.endswith(")"):
            if _find_matching_delimiter_in_code(s_ns, 0) != len(s_ns) - 1:
                break
            s_ns = s_ns[1:-1].strip()
            if s_nc.startswith("(") and s_nc.endswith(")"):
                s_nc = s_nc[1:-1].strip()
            changed = True
        ref_m = re.match(r"^&\s*(?:mut\s+)?", s_ns)
        if ref_m is not None:
            s_ns = s_ns[ref_m.end() :].strip()
            ref_nc = re.match(r"^&\s*(?:mut\s+)?", s_nc)
            if ref_nc is not None:
                s_nc = s_nc[ref_nc.end() :].strip()
            changed = True
        ad_m = RUST_BIN_TRAILING_ADAPTER_RE.search(s_ns)
        if ad_m is not None:
            ad_name = ad_m.group(1)
            if (
                ad_name is None
                or ad_name not in facts.extension_overridden_methods
            ):
                s_ns = s_ns[: ad_m.start()].strip()
                ad_nc = RUST_BIN_TRAILING_ADAPTER_RE.search(s_nc)
                if ad_nc is not None:
                    s_nc = s_nc[: ad_nc.start()].strip()
                changed = True
        wm = RUST_BIN_PATH_WRAPPER_RE.match(s_ns)
        if wm is not None:
            open_p = wm.end() - 1
            if _find_matching_delimiter_in_code(s_ns, open_p) == len(s_ns) - 1:
                w_heads = [g for g in wm.groups() if g]
                w_prefix = re.sub(r"\s+", "", s_ns[:open_p]).lstrip(":")
                w_first = w_prefix.split("::", 1)[0]
                w_shadowed = any(
                    h in facts.local_types_or_mods for h in w_heads
                ) or (w_first in facts.local_types_or_mods)
                if not w_shadowed and w_first in aliases:
                    if not all(
                        tgt.lstrip(":").split("::", 1)[0]
                        in ("std", "core", "alloc", "path", "ffi", "string", "option")
                        for tgt in aliases[w_first]
                    ):
                        w_shadowed = True
                if not w_shadowed:
                    wm_nc = RUST_BIN_PATH_WRAPPER_RE.match(s_nc)
                    if wm_nc is not None:
                        op_nc = wm_nc.end() - 1
                        s_ns = s_ns[open_p + 1 : -1].strip()
                        s_nc = s_nc[op_nc + 1 : -1].strip()
                        changed = True
        if not changed:
            break

    if not s_nc:
        return None
    if CAPTURE_CARGO_BIN_ENV_RE.fullmatch(s_nc) is not None:
        return "bin_capture"
    if DRIVER_CARGO_BIN_ENV_RE.fullmatch(s_nc) is not None:
        return "bin_driver"

    # Plain variable / const binding assigned an authenticated binary.
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s_ns):
        if rust_env is not None:
            st = rust_env.get(s_ns)
            if st in ("bin_capture", "bin_driver"):
                return st
        return None

    # Authenticated testkit Toolchain binary accessor (`toolchain.capture_bin`,
    # `toolchain.cargo_anneal_bin`, `toolchain.audit_bin`).
    tc_m = re.search(
        r"(\.)\s*(capture_bin|cargo_anneal_bin|audit_bin|mir_eval_bin)\s*\(\s*\)\s*$",
        s_ns,
    )
    if tc_m is not None and "Toolchain" not in facts.local_types_or_mods:
        dot_pos = tc_m.start(1)
        mname = tc_m.group(2)
        recv_ty = _infer_rust_receiver_type(
            s_nc, s_ns, dot_pos, type_env=rust_type_env, facts=facts
        )
        if recv_ty is None or recv_ty not in facts.local_types_or_mods:
            if mname not in (facts.method_all_types or {}):
                if mname in ("capture_bin", "cargo_anneal_bin"):
                    return "bin_capture"
                return "bin_driver"

    # Method call returning an authenticated binary path (`self.capture_bin()`).
    m_call = re.search(
        r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\([^()]*\)\s*$",
        s_ns,
    )
    if m_call is not None:
        dot_pos = m_call.start(1)
        mname = m_call.group(2)
        if _rust_method_matches_kind(
            mname,
            s_nc,
            s_ns,
            dot_pos,
            allowed_types=facts.method_capture_bin_types or {},
            all_types=facts.method_all_types or {},
            type_env=rust_type_env,
            facts=facts,
        ):
            return "bin_capture"
        if _rust_method_matches_kind(
            mname,
            s_nc,
            s_ns,
            dot_pos,
            allowed_types=facts.method_driver_bin_types or {},
            all_types=facts.method_all_types or {},
            type_env=rust_type_env,
            facts=facts,
        ):
            return "bin_driver"

    # Free or qualified helper call returning an authenticated binary path.
    fn_m = re.match(
        r"^((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*[A-Za-z_][A-Za-z0-9_]*)"
        r"\s*(?:::\s*<[^;()]*>)?\s*\(",
        s_ns,
    )
    if fn_m is not None:
        open_p = fn_m.end() - 1
        if _find_matching_delimiter_in_code(s_ns, open_p) == len(s_ns) - 1:
            path = re.sub(r"\s+", "", fn_m.group(1)).lstrip(":")
            q_cap_bin = facts.qualified_capture_bin_fns
            q_drv_bin = facts.qualified_driver_bin_fns
            if "::" in path:
                expanded = _resolve_rust_qualified_path(path, facts)
                if expanded and all(
                    any(
                        c in q_cap_bin
                        for c in _normalize_local_rust_path(ep, facts.test_mod_scope)
                    )
                    for ep in expanded
                ):
                    return "bin_capture"
                if expanded and all(
                    any(
                        c in q_drv_bin
                        for c in _normalize_local_rust_path(ep, facts.test_mod_scope)
                    )
                    for ep in expanded
                ):
                    return "bin_driver"
            else:
                if rust_env is not None and path in rust_env:
                    if rust_env[path] in ("bin_capture", "bin_driver"):
                        return rust_env[path]
                    return None
                if path in aliases:
                    expanded = _resolve_rust_qualified_path(path, facts)
                    if expanded and all(
                        any(
                            c in q_cap_bin
                            for c in _normalize_local_rust_path(
                                ep, facts.test_mod_scope
                            )
                        )
                        for ep in expanded
                    ):
                        return "bin_capture"
                    if expanded and all(
                        any(
                            c in q_drv_bin
                            for c in _normalize_local_rust_path(
                                ep, facts.test_mod_scope
                            )
                        )
                        for ep in expanded
                    ):
                        return "bin_driver"
                    return None
                if path in facts.capture_bin_fns or any(
                    c in q_cap_bin
                    for c in _normalize_local_rust_path(path, facts.test_mod_scope)
                ):
                    return "bin_capture"
                if path in facts.driver_bin_fns or any(
                    c in q_drv_bin
                    for c in _normalize_local_rust_path(path, facts.test_mod_scope)
                ):
                    return "bin_driver"
    return None


def _rust_command_new_kind(
    expr_nc: str,
    expr_ns: str,
    *,
    rust_env: dict[str, str] | None = None,
    rust_type_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
) -> tuple[str | None, bool]:
    """Inspect `Command::new(<arg>)` calls in `expr`; return `(kind, saw_unverified)`."""
    facts = rust_facts or _RustFileFacts()
    best_kind: str | None = None
    saw_unverified = False
    for m in RUST_COMMAND_NEW_RE.finditer(expr_ns):
        if not _rust_is_std_command_path(m.group(1), facts):
            saw_unverified = True
            continue
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(expr_ns, open_p)
        if close_p is None:
            saw_unverified = True
            continue
        arg_nc = expr_nc[open_p + 1 : close_p].strip()
        arg_ns = expr_ns[open_p + 1 : close_p].strip()
        bk = _rust_expr_bin_kind(
            arg_nc,
            arg_ns,
            rust_env=rust_env,
            rust_type_env=rust_type_env,
            rust_facts=facts,
        )
        if bk == "bin_capture":
            best_kind = "cmd_capture"
        elif bk == "bin_driver":
            if best_kind != "cmd_capture":
                best_kind = "cmd_driver"
        else:
            saw_unverified = True
    return best_kind, saw_unverified


def _rust_method_matches_kind(
    mname: str,
    expr_nc: str,
    expr_ns: str,
    dot_pos: int,
    *,
    allowed_types: dict[str, frozenset[str]],
    all_types: dict[str, frozenset[str]],
    type_env: dict[str, str] | None,
    facts: _RustFileFacts,
) -> bool:
    """Return True iff `.mname(...)` resolves cleanly to a verified impl."""
    ok_types = allowed_types.get(mname)
    if not ok_types:
        return False
    recv_ty = _infer_rust_receiver_type(
        expr_nc, expr_ns, dot_pos, type_env=type_env, facts=facts
    )
    if recv_ty is not None:
        return recv_ty in ok_types
    if mname in PURE_RUST_METHODS:
        return False
    defined_types = all_types.get(mname, frozenset())
    return bool(defined_types) and defined_types <= ok_types


def _rust_expr_cmd_kind(
    expr_nc: str,
    expr_ns: str,
    *,
    rust_env: dict[str, str] | None = None,
    rust_type_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
    capture_cmd_fns: frozenset[str] = frozenset(),
    driver_cmd_fns: frozenset[str] = frozenset(),
) -> str | None:
    """Return `'cmd_capture'` or `'cmd_driver'` for authenticated command builders."""
    facts = rust_facts or _RustFileFacts(
        capture_cmd_fns=capture_cmd_fns, driver_cmd_fns=driver_cmd_fns
    )
    aliases = facts.use_aliases or {}
    local_free = facts.local_free_fns or facts.local_fns

    cmd_new_kind, saw_unverified_cmd_new = _rust_command_new_kind(
        expr_nc,
        expr_ns,
        rust_env=rust_env,
        rust_type_env=rust_type_env,
        rust_facts=facts,
    )
    if cmd_new_kind == "cmd_capture" and not saw_unverified_cmd_new:
        return "cmd_capture"

    for hm in CAPTURE_INVOCATION_HELPER_RE.finditer(expr_ns):
        hname = hm.group(1)
        if rust_env is not None and hname in rust_env:
            if rust_env[hname] == "cmd_capture":
                return "cmd_capture"
            continue
        if hname in aliases:
            if all(
                tgt.split("::", 1)[0]
                in ("anneal_rustc_capture", "cargo_anneal", "anneal_testkit")
                for tgt in aliases[hname]
            ):
                return "cmd_capture"
            continue
        if hname not in local_free:
            return "cmd_capture"

    cap_mtypes = facts.method_capture_cmd_types or {}
    drv_mtypes = facts.method_driver_cmd_types or {}
    all_mtypes = facts.method_all_types or {}
    pt_methods = facts.passthrough_cmd_methods or {}
    pt_fns = facts.passthrough_cmd_fns or {}
    q_cap_cmd = facts.qualified_capture_cmd_fns or capture_cmd_fns
    q_drv_cmd = facts.qualified_driver_cmd_fns or driver_cmd_fns
    free_cap_cmd = facts.capture_cmd_fns or capture_cmd_fns
    free_drv_cmd = facts.driver_cmd_fns or driver_cmd_fns

    found_driver = cmd_new_kind == "cmd_driver" and not saw_unverified_cmd_new
    # 1. Method calls `.cmd_helper(...)` and passthrough `.command_for(bin)`
    for m in re.finditer(
        r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(", expr_ns
    ):
        dot_pos = m.start(1)
        mname = m.group(2)
        if _rust_method_matches_kind(
            mname,
            expr_nc,
            expr_ns,
            dot_pos,
            allowed_types=cap_mtypes,
            all_types=all_mtypes,
            type_env=rust_type_env,
            facts=facts,
        ):
            return "cmd_capture"
        if _rust_method_matches_kind(
            mname,
            expr_nc,
            expr_ns,
            dot_pos,
            allowed_types=drv_mtypes,
            all_types=all_mtypes,
            type_env=rust_type_env,
            facts=facts,
        ):
            found_driver = True
        recv_ty = _infer_rust_receiver_type(
            expr_nc, expr_ns, dot_pos, type_env=rust_type_env, facts=facts
        )
        pt_idx = pt_methods.get((recv_ty, mname)) if recv_ty is not None else None
        if pt_idx is not None:
            open_p = m.end() - 1
            close_p = _find_matching_delimiter_in_code(expr_ns, open_p)
            if close_p is not None:
                c_args_nc = _split_top_level_commas(
                    expr_nc[open_p + 1 : close_p], keep_literal_only=True
                )
                c_args_ns = _split_top_level_commas(
                    expr_ns[open_p + 1 : close_p], keep_literal_only=True
                )
                if pt_idx < len(c_args_nc) and pt_idx < len(c_args_ns):
                    bk = _rust_expr_bin_kind(
                        c_args_nc[pt_idx],
                        c_args_ns[pt_idx],
                        rust_env=rust_env,
                        rust_type_env=rust_type_env,
                        rust_facts=facts,
                    )
                    if bk == "bin_capture":
                        return "cmd_capture"
                    if bk == "bin_driver":
                        found_driver = True

    # 2. Free or qualified calls
    for m in re.finditer(
        r"(?<!\.)\b((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
        r"[A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(",
        expr_ns,
    ):
        if m.start() > 0 and expr_ns[m.start() - 1] == ".":
            continue
        path = re.sub(r"\s+", "", m.group(1)).lstrip(":")
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(expr_ns, open_p)

        # Check passthrough free/qualified `Command::new(param)` wrapper calls.
        pt_cands = (
            _resolve_rust_qualified_path(path, facts)
            if ("::" in path or path in aliases)
            else [path]
        )
        for ep in pt_cands:
            for norm_c in _normalize_local_rust_path(ep, facts.test_mod_scope):
                if norm_c in pt_fns and close_p is not None:
                    p_idx = pt_fns[norm_c]
                    c_args_nc = _split_top_level_commas(
                        expr_nc[open_p + 1 : close_p], keep_literal_only=True
                    )
                    c_args_ns = _split_top_level_commas(
                        expr_ns[open_p + 1 : close_p], keep_literal_only=True
                    )
                    if p_idx < len(c_args_nc) and p_idx < len(c_args_ns):
                        bk = _rust_expr_bin_kind(
                            c_args_nc[p_idx],
                            c_args_ns[p_idx],
                            rust_env=rust_env,
                            rust_type_env=rust_type_env,
                            rust_facts=facts,
                        )
                        if bk == "bin_capture":
                            return "cmd_capture"
                        if bk == "bin_driver":
                            found_driver = True

        if "::" in path:
            expanded = _resolve_rust_qualified_path(path, facts)
            if expanded and all(
                any(
                    c in q_cap_cmd
                    for c in _normalize_local_rust_path(ep, facts.test_mod_scope)
                )
                for ep in expanded
            ):
                return "cmd_capture"
            if expanded and all(
                any(
                    c in q_drv_cmd
                    for c in _normalize_local_rust_path(ep, facts.test_mod_scope)
                )
                for ep in expanded
            ):
                found_driver = True
        else:
            if rust_env is not None and path in rust_env:
                if rust_env[path] == "cmd_capture":
                    return "cmd_capture"
                if rust_env[path] == "cmd_driver":
                    found_driver = True
                continue
            if path in aliases:
                expanded = _resolve_rust_qualified_path(path, facts)
                if expanded and all(
                    any(
                        c in q_cap_cmd
                        for c in _normalize_local_rust_path(
                            ep, facts.test_mod_scope
                        )
                    )
                    for ep in expanded
                ):
                    return "cmd_capture"
                if expanded and all(
                    any(
                        c in q_drv_cmd
                        for c in _normalize_local_rust_path(
                            ep, facts.test_mod_scope
                        )
                    )
                    for ep in expanded
                ):
                    found_driver = True
                continue
            if path in free_cap_cmd or any(
                c in q_cap_cmd
                for c in _normalize_local_rust_path(path, facts.test_mod_scope)
            ):
                return "cmd_capture"
            if path in free_drv_cmd or any(
                c in q_drv_cmd
                for c in _normalize_local_rust_path(path, facts.test_mod_scope)
            ):
                found_driver = True

    if rust_env is not None:
        for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\b", expr_ns):
            ident = m.group(1)
            before = expr_ns[: m.start()].rstrip()
            if before.endswith(".") or before.endswith("::"):
                continue
            if rust_env.get(ident) == "cmd_capture":
                return "cmd_capture"
            if rust_env.get(ident) == "cmd_driver":
                found_driver = True

    for hm in DRIVER_INVOCATION_HELPER_RE.finditer(expr_ns):
        hname = hm.group(1)
        if rust_env is not None and hname in rust_env:
            if rust_env[hname] == "cmd_driver":
                return "cmd_driver"
            continue
        if hname in aliases:
            if all(
                tgt.split("::", 1)[0]
                in ("anneal_itree_diff", "anneal_audit", "anneal_testkit")
                for tgt in aliases[hname]
            ):
                return "cmd_driver"
            continue
        if hname not in local_free:
            return "cmd_driver"
    return "cmd_driver" if found_driver else None


def _rust_call_is_direct_process_exit(
    path: str,
    arg_ns: str,
    *,
    facts: _RustFileFacts,
) -> str | None:
    """Return `'exit_success'` or `'exit_fail'` if `path(arg_ns)` terminates the process."""
    norm = re.sub(r"\s+", "", path).lstrip(":")
    if norm in ("std::process::abort", "core::process::abort", "process::abort"):
        return "exit_fail"
    expanded = _resolve_rust_qualified_path(norm, facts)
    is_exit_fn = False
    for ep in expanded:
        ep_clean = ep.lstrip(":")
        if ep_clean in (
            "std::process::abort",
            "core::process::abort",
            "process::abort",
        ):
            return "exit_fail"
        if ep_clean in (
            "std::process::exit",
            "core::process::exit",
            "process::exit",
            "libc::exit",
            "libc::_exit",
            "libc::_Exit",
            "libc::quick_exit",
        ):
            is_exit_fn = True
            break
    if not is_exit_fn and "::" not in norm and norm in facts.extern_exit_fns:
        is_exit_fn = True
    if not is_exit_fn:
        return None
    arg = arg_ns.strip()
    if re.fullmatch(r"-?[1-9][0-9_]*(?:[iu](?:8|16|32|64|size))?", arg):
        return "exit_fail"
    return "exit_success"


def _rust_expr_calls_exit_success(
    expr_ns: str,
    *,
    facts: _RustFileFacts,
    local_may_exit_fns: frozenset[str] = frozenset(),
    local_must_exit_fns: frozenset[str] = frozenset(),
    cur_exit_vars: frozenset[str] = frozenset(),
    type_env: dict[str, str] | None = None,
) -> tuple[bool, bool]:
    """Return `(may_exit_success, whole_expr_must_exit_success)` for `expr_ns`."""
    s = expr_ns.strip().rstrip(";").strip()
    if not s:
        return False, False
    may_exit = False
    whole_must = False

    # 1. Check `Drop` bomb types mentioned/constructed in expression.
    if facts.drop_may_exit_types:
        for dt in facts.drop_may_exit_types:
            if re.search(rf"\b{re.escape(dt)}\b", s):
                may_exit = True
                break

    # 2. Method calls `.bail(...)` against `method_may_exit_types`.
    m_exit = facts.method_may_exit_types or {}
    if m_exit:
        for m in re.finditer(
            r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(", s
        ):
            mname = m.group(2)
            bad_types = m_exit.get(mname)
            if not bad_types:
                continue
            recv_ty = _infer_rust_receiver_type(
                s, s, m.start(1), type_env=type_env, facts=facts
            )
            if recv_ty is None or recv_ty in bad_types:
                may_exit = True

    # 3. Free / qualified / closure-var calls.
    aliases = facts.use_aliases or {}
    for m in re.finditer(
        r"(?<!\.)\b((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
        r"[A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(",
        s,
    ):
        if m.start() > 0 and s[m.start() - 1] == ".":
            continue
        path = re.sub(r"\s+", "", m.group(1)).lstrip(":")
        if path in PURE_RUST_IDENT_IGNORED:
            continue
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(s, open_p)
        arg_ns = s[open_p + 1 : close_p] if close_p is not None else ""
        is_whole = m.start() == 0 and close_p == len(s) - 1

        direct_ex = _rust_call_is_direct_process_exit(path, arg_ns, facts=facts)
        if direct_ex == "exit_success":
            may_exit = True
            if is_whole:
                whole_must = True
            continue
        if direct_ex == "exit_fail":
            continue

        if "::" not in path:
            if path in cur_exit_vars:
                may_exit = True
                continue
            if path in local_must_exit_fns:
                may_exit = True
                if is_whole:
                    whole_must = True
                continue
            if path in local_may_exit_fns:
                may_exit = True
                continue

        expanded = (
            _resolve_rust_qualified_path(path, facts)
            if ("::" in path or path in aliases)
            else [path]
        )
        for ep in expanded:
            cands = _normalize_local_rust_path(ep, facts.test_mod_scope)
            if (
                ("::" not in ep and ep in facts.must_exit_success_fns)
                or any(c in facts.qualified_must_exit_success_fns for c in cands)
            ):
                may_exit = True
                if is_whole:
                    whole_must = True
                break
            if (
                ("::" not in ep and ep in facts.may_exit_success_fns)
                or any(c in facts.qualified_may_exit_success_fns for c in cands)
            ):
                may_exit = True
                break

    return may_exit, whole_must


def _rust_body_exit_classification(
    body_nc: str,
    body_ns: str,
    *,
    facts: _RustFileFacts,
    owner_ty: str | None = None,
) -> tuple[bool, bool]:
    """Classify `(may_exit_success, must_exit_success)` for a Rust helper body."""
    wrapped_nc = "{" + body_nc + "}"
    wrapped_ns = "{" + body_ns + "}"
    # First detect any nested `fn` inside this helper that may exit 0.
    nested_may: set[str] = set()
    nested_must: set[str] = set()
    nested_recs: list[tuple[str, str, str]] = []
    for nm in re.finditer(
        r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(", wrapped_ns[1:]
    ):
        n_name = nm.group(1)
        rp = _find_matching_delimiter_in_code(wrapped_ns, nm.end())
        if rp is None:
            continue
        b_open = wrapped_ns.find("{", rp)
        if b_open == -1:
            continue
        b_close = _find_matching_delimiter_in_code(wrapped_ns, b_open)
        if b_close is None:
            continue
        nested_recs.append(
            (n_name, wrapped_nc[b_open + 1 : b_close], wrapped_ns[b_open + 1 : b_close])
        )
    if nested_recs:
        n_changed = True
        while n_changed:
            n_changed = False
            for n_name, nb_nc, nb_ns in nested_recs:
                if n_name in nested_must:
                    continue
                _lc, lns = _strip_unreachable_rust_test_code("{" + nb_nc + "}", "{" + nb_ns + "}")
                n_may, n_must = _rust_expr_calls_exit_success(
                    lns[1:-1],
                    facts=facts,
                    local_may_exit_fns=frozenset(nested_may),
                    local_must_exit_fns=frozenset(nested_must),
                )
                if n_may and n_name not in nested_may:
                    nested_may.add(n_name)
                    n_changed = True
                if n_must and n_name not in nested_must:
                    nested_must.add(n_name)
                    n_changed = True

    _live_c, live_ns = _strip_unreachable_rust_test_code(wrapped_nc, wrapped_ns)
    inner_ns = live_ns[1:-1] if len(live_ns) >= 2 else live_ns
    t_env = {"self": owner_ty} if owner_ty is not None else {}
    may_exit, _ = _rust_expr_calls_exit_success(
        inner_ns,
        facts=facts,
        local_may_exit_fns=frozenset(nested_may),
        local_must_exit_fns=frozenset(nested_must),
        type_env=t_env,
    )
    if not may_exit:
        return False, False
    # Check whether any top-level unconditional statement must exit 0.
    must_exit = False
    for kind, s_s, s_e, _br in _split_rust_top_level_segments(inner_ns):
        if kind != "stmt":
            continue
        _smay, smust = _rust_expr_calls_exit_success(
            inner_ns[s_s:s_e],
            facts=facts,
            local_may_exit_fns=frozenset(nested_may),
            local_must_exit_fns=frozenset(nested_must),
            type_env=t_env,
        )
        if smust:
            must_exit = True
            break
    return True, must_exit


def _rust_helper_eval_statements(
    body_nc: str,
    body_ns: str,
    *,
    base_env: dict[str, str],
    base_types: dict[str, str],
    facts: _RustFileFacts,
    mode: str,
) -> str | None:
    """Evaluate a helper body's returned value (`'bin'`, `'cmd'`, or `'obs'`)."""
    segs = _split_rust_top_level_segments(body_ns)
    if not segs:
        return None
    cur_env = dict(base_env)
    cur_types = dict(base_types)
    ret_exprs: list[tuple[str, str, dict[str, str], dict[str, str]]] = []
    for idx_s, (kind, s_s, s_e, _br) in enumerate(segs):
        seg_nc = body_nc[s_s:s_e]
        seg_ns = body_ns[s_s:s_e]
        stripped_ns = seg_ns.strip()
        is_last = idx_s == len(segs) - 1
        if kind == "stmt":
            ret_m = re.match(r"^return\b([\s\S]*)$", stripped_ns)
            if ret_m is not None:
                ret_nc_m = re.match(r"^\s*return\b([\s\S]*)$", seg_nc)
                r_ns = ret_m.group(1).rstrip(";").strip()
                r_nc = (
                    ret_nc_m.group(1).rstrip(";").strip()
                    if ret_nc_m is not None
                    else r_ns
                )
                ret_exprs.append((r_nc, r_ns, dict(cur_env), dict(cur_types)))
                continue
            eq_pos = _find_rust_top_level_equal(seg_ns)
            if eq_pos is not None:
                lhs = seg_ns[:eq_pos]
                rhs_nc = seg_nc[eq_pos + 1 :].rstrip(";").strip()
                rhs_ns = seg_ns[eq_pos + 1 :].rstrip(";").strip()
                st: str | None = None
                if mode == "obs":
                    st = _rust_expr_origin_kind(
                        rhs_nc,
                        rhs_ns,
                        rust_env=cur_env,
                        rust_facts=facts,
                        rust_type_env=cur_types,
                    )
                if st is None:
                    st = _rust_expr_cmd_kind(
                        rhs_nc,
                        rhs_ns,
                        rust_env=cur_env,
                        rust_type_env=cur_types,
                        rust_facts=facts,
                    )
                if st is None:
                    st = _rust_expr_bin_kind(
                        rhs_nc,
                        rhs_ns,
                        rust_env=cur_env,
                        rust_type_env=cur_types,
                        rust_facts=facts,
                    )
                inferred_ty = _extract_rust_lhs_type_annotation(
                    lhs
                ) or _infer_rust_expr_type(
                    rhs_nc, rhs_ns, type_env=cur_types, facts=facts
                )
                idents = _extract_rust_pattern_idents(lhs)
                for ident in idents:
                    cur_env[ident] = st if st is not None else "const"
                    if len(idents) == 1 and inferred_ty is not None:
                        cur_types[ident] = inferred_ty
                    else:
                        cur_types.pop(ident, None)
                _rust_invalidate_mutated_bin_vars(rhs_ns, cur_env)
                continue
            _rust_invalidate_mutated_bin_vars(stripped_ns, cur_env)
            if is_last and not stripped_ns.endswith(";"):
                ret_exprs.append((seg_nc.strip(), stripped_ns, dict(cur_env), dict(cur_types)))
        elif is_last:
            ret_exprs.append((seg_nc.strip(), stripped_ns, dict(cur_env), dict(cur_types)))

    if not ret_exprs:
        return None
    results: list[str | None] = []
    for r_nc, r_ns, r_env, r_types in ret_exprs:
        if mode == "bin":
            results.append(
                _rust_expr_bin_kind(
                    r_nc,
                    r_ns,
                    rust_env=r_env,
                    rust_type_env=r_types,
                    rust_facts=facts,
                )
            )
        elif mode == "cmd":
            results.append(
                _rust_expr_cmd_kind(
                    r_nc,
                    r_ns,
                    rust_env=r_env,
                    rust_type_env=r_types,
                    rust_facts=facts,
                )
            )
        else:
            results.append(
                _rust_expr_origin_kind(
                    r_nc,
                    r_ns,
                    rust_env=r_env,
                    rust_facts=facts,
                    rust_type_env=r_types,
                )
            )
    if mode == "bin":
        if all(r == "bin_capture" for r in results):
            return "bin_capture"
        if all(r in ("bin_capture", "bin_driver") for r in results):
            return "bin_driver"
        return None
    if mode == "cmd":
        if all(r == "cmd_capture" for r in results):
            return "cmd_capture"
        if all(r in ("cmd_capture", "cmd_driver") for r in results):
            return "cmd_driver"
        return None
    if all(r == "obs_capture" for r in results):
        return "obs_capture"
    if all(r in ("obs_capture", "obs_driver") for r in results):
        return "obs_driver"
    return None


def _rust_helper_eval_authority_family(
    body_nc: str,
    body_ns: str,
    *,
    base_auth_env: dict[str, str],
    base_types: dict[str, str],
    facts: _RustFileFacts,
) -> str | None:
    """Evaluate a helper body's returned authority family if unambiguous."""
    segs = _split_rust_top_level_segments(body_ns)
    if not segs:
        return None
    cur_auth = dict(base_auth_env)
    cur_types = dict(base_types)
    ret_exprs: list[tuple[str, str, dict[str, str], dict[str, str]]] = []
    for idx_s, (kind, s_s, s_e, _br) in enumerate(segs):
        seg_nc = body_nc[s_s:s_e]
        seg_ns = body_ns[s_s:s_e]
        stripped_ns = seg_ns.strip()
        is_last = idx_s == len(segs) - 1
        if kind != "stmt":
            if is_last:
                ret_exprs.append(
                    (seg_nc.strip(), stripped_ns, dict(cur_auth), dict(cur_types))
                )
            continue
        ret_m = re.match(r"^return\b([\s\S]*)$", stripped_ns)
        if ret_m is not None:
            ret_nc_m = re.match(r"^\s*return\b([\s\S]*)$", seg_nc)
            r_ns = ret_m.group(1).rstrip(";").strip()
            r_nc = (
                ret_nc_m.group(1).rstrip(";").strip()
                if ret_nc_m is not None
                else r_ns
            )
            ret_exprs.append((r_nc, r_ns, dict(cur_auth), dict(cur_types)))
            continue
        eq_pos = _find_rust_top_level_equal(seg_ns)
        if eq_pos is not None:
            lhs = seg_ns[:eq_pos]
            rhs_nc = seg_nc[eq_pos + 1 :].rstrip(";").strip()
            rhs_ns = seg_ns[eq_pos + 1 :].rstrip(";").strip()
            fam = _rust_expr_authority_family(
                rhs_nc,
                rhs_ns,
                rust_auth_env=cur_auth,
                rust_facts=facts,
                rust_type_env=cur_types,
            )
            for ident in _extract_rust_pattern_idents(lhs):
                if fam is not None:
                    cur_auth[ident] = fam
                else:
                    cur_auth.pop(ident, None)
            continue
        if is_last and not stripped_ns.endswith(";"):
            ret_exprs.append(
                (seg_nc.strip(), stripped_ns, dict(cur_auth), dict(cur_types))
            )
    if not ret_exprs:
        return None
    fams = [
        _rust_expr_authority_family(
            r_nc, r_ns, rust_auth_env=r_auth, rust_facts=facts, rust_type_env=r_types
        )
        for r_nc, r_ns, r_auth, r_types in ret_exprs
    ]
    if fams and fams[0] is not None and all(f == fams[0] for f in fams):
        return fams[0]
    return None


def _extract_rust_fn_param_names(params_ns: str) -> list[str]:
    """Extract non-`self` parameter names in positional order."""
    out: list[str] = []
    for part in _split_top_level_commas(params_ns):
        s = part.strip()
        if not s:
            continue
        if re.match(
            r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?|mut\s+)?self\b",
            s,
        ):
            continue
        colon = s.find(":")
        lhs = s[:colon].strip() if colon != -1 else s
        lhs = re.sub(r"^(?:mut|ref)\s+", "", lhs).strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", lhs):
            out.append(lhs)
        else:
            out.append("")
    return out


def _collect_rust_file_const_facts(
    file_code_ns: str, file_code_nc: str | None = None
) -> tuple[frozenset[str], dict[str, str], _RustFileFacts]:
    """Collect file-level `const`/`static` bindings, helper provenance, eq/exit facts."""
    code_nc = file_code_nc if file_code_nc is not None else file_code_ns
    use_aliases = _collect_rust_use_aliases(file_code_ns)
    local_types_or_mods = _collect_rust_local_types_or_mods(file_code_ns)
    (
        custom_eq_types,
        extension_overridden_methods,
        method_override_types,
        _file_has_custom_eq,
        extern_exit_fns,
    ) = _collect_rust_impl_and_extern_facts(file_code_ns)

    env: dict[str, str] = {}
    const_auth: dict[str, str] = {}
    base_const_facts = _RustFileFacts(
        local_types_or_mods=local_types_or_mods,
        use_aliases=use_aliases,
    )
    for m in re.finditer(
        r"(?:^|[;\n{}])\s*(?:pub(?:\([^()]*\))?\s+)?(?:const|static)\s+"
        r"(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:",
        file_code_ns,
    ):
        cname = m.group(1)
        semi = file_code_ns.find(";", m.end())
        decl_ns = file_code_ns[m.end() : semi] if semi != -1 else file_code_ns[m.end() :]
        decl_nc = code_nc[m.end() : semi] if semi != -1 else code_nc[m.end() :]
        eq_p = _find_rust_top_level_equal(decl_ns)
        c_status = "const"
        if eq_p is not None:
            bk = _rust_expr_bin_kind(
                decl_nc[eq_p + 1 :],
                decl_ns[eq_p + 1 :],
                rust_env=env,
                rust_facts=base_const_facts,
            )
            if bk is not None:
                c_status = bk
            cfam = _rust_expr_authority_family(
                decl_nc[eq_p + 1 :],
                decl_ns[eq_p + 1 :],
                rust_auth_env=const_auth,
                rust_facts=base_const_facts,
            )
            if cfam is not None:
                const_auth[cname] = cfam
        env[cname] = c_status

    # Record `(qual_key, bare_name, mod_scope, owner_ty, trait_name, is_method,`
    # `params_list, body_nc, body_ns)` triples per parsed function item.
    fn_records: list[
        tuple[
            str,
            str,
            tuple[str, ...],
            str | None,
            str | None,
            bool,
            list[str],
            str,
            str,
        ]
    ] = []
    fn_return_types: dict[str, str] = {}
    fn_returns_untrusted_q: set[str] = set()
    method_returns_untrusted_mut: dict[str, set[str]] = {}
    all_fn_names: set[str] = set()
    local_free_fns: set[str] = set()
    method_all_types_mut: dict[str, set[str]] = {}
    passthrough_cmd_fns: dict[str, int] = {}
    passthrough_cmd_methods: dict[tuple[str, str], int] = {}

    for m in re.finditer(
        r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(", file_code_ns
    ):
        name = m.group(1)
        all_fn_names.add(name)
        rparen = _find_matching_delimiter_in_code(file_code_ns, m.end() - 1)
        if rparen is None:
            continue
        params_ns = file_code_ns[m.end() : rparen].strip()
        is_method = re.match(
            r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?|mut\s+)?self\b",
            params_ns,
        ) is not None
        param_names = _extract_rust_fn_param_names(params_ns)
        j = rparen + 1
        p_d = 0
        b_d = 0
        body_open = None
        while j < len(file_code_ns):
            ch = file_code_ns[j]
            if ch == "(":
                p_d += 1
            elif ch == ")" and p_d > 0:
                p_d -= 1
            elif ch == "[":
                b_d += 1
            elif ch == "]" and b_d > 0:
                b_d -= 1
            elif p_d == 0 and b_d == 0:
                if ch == ";":
                    break
                if ch == "{":
                    body_open = j
                    break
            j += 1
        if body_open is None:
            # Also record trait method declarations without default bodies so
            # method-name collisions with traits fail closed.
            encl_decl = _find_rust_enclosing_delimiters(file_code_ns, m.start())
            for dch, open_pos in encl_decl:
                if dch == "{":
                    bnd = _find_rust_item_boundary_before(file_code_ns, open_pos)
                    hdr = file_code_ns[bnd:open_pos].strip()
                    tr_m = re.match(
                        r"^(?:pub(?:\([^()]*\))?\s+)?(?:unsafe\s+)?trait\s+([A-Za-z_][A-Za-z0-9_]*)\b",
                        hdr,
                    )
                    if tr_m is not None:
                        method_all_types_mut.setdefault(name, set()).add(
                            f"trait:{tr_m.group(1)}"
                        )
            continue
        body_close = _find_matching_delimiter_in_code(file_code_ns, body_open)
        if body_close is None:
            continue

        # Classify enclosing scopes: `mod`, `impl`, `trait`, or nested `fn`.
        encl = _find_rust_enclosing_delimiters(file_code_ns, m.start())
        mod_parts: list[str] = []
        impl_type: str | None = None
        impl_trait_name: str | None = None
        trait_name: str | None = None
        is_nested = False
        for dch, open_pos in encl:
            if dch != "{":
                is_nested = True
                continue
            bnd = _find_rust_item_boundary_before(file_code_ns, open_pos)
            hdr = file_code_ns[bnd:open_pos].strip()
            # Strip leading outer attributes from scope header.
            while hdr.startswith("#"):
                am = re.match(r"#\s*\[", hdr)
                if am is None:
                    break
                cb = _find_matching_delimiter_in_code(hdr, am.end() - 1)
                if cb is None:
                    break
                hdr = hdr[cb + 1 :].lstrip()
            mod_m = re.match(
                r"^(?:pub(?:\([^()]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\b",
                hdr,
            )
            if mod_m is not None:
                mod_parts.append(mod_m.group(1))
                continue
            tr_m = re.match(
                r"^(?:pub(?:\([^()]*\))?\s+)?(?:unsafe\s+)?trait\s+([A-Za-z_][A-Za-z0-9_]*)\b",
                hdr,
            )
            if tr_m is not None:
                trait_name = tr_m.group(1)
                continue
            it_tr, it_ty, _ta, _gp = _extract_rust_impl_trait_and_target(hdr)
            if it_ty is not None:
                impl_type = it_ty
                impl_trait_name = it_tr
                continue
            is_nested = True

        mod_scope = tuple(mod_parts)
        owner_type = impl_type or (f"trait:{trait_name}" if trait_name else None)
        if not is_nested:
            if owner_type is not None:
                method_all_types_mut.setdefault(name, set()).add(owner_type)
            else:
                local_free_fns.add(name)

        scope_chain = [*mod_parts]
        if impl_type is not None:
            scope_chain.append(impl_type)
        elif trait_name is not None:
            scope_chain.append(f"trait:{trait_name}")
        qual_key = "::".join([*scope_chain, name])

        sig_tail = file_code_ns[rparen + 1 : body_open]
        ret_ty = _extract_rust_fn_return_type(sig_tail, impl_type)
        ret_untrusted = _rust_return_sig_mentions_untrusted_type(
            sig_tail,
            impl_type,
            local_types=local_types_or_mods,
            custom_eq_types=custom_eq_types,
        )
        if not is_nested:
            if ret_ty is not None:
                fn_return_types[qual_key] = ret_ty
                if impl_type is not None:
                    fn_return_types.setdefault(f"{impl_type}::{name}", ret_ty)
            if ret_untrusted:
                fn_returns_untrusted_q.add(qual_key)
                if owner_type is not None:
                    method_returns_untrusted_mut.setdefault(name, set()).add(
                        owner_type
                    )
                    fn_returns_untrusted_q.add(f"{owner_type}::{name}")

        if not is_nested:
            body_nc_str = code_nc[body_open + 1 : body_close]
            body_ns_str = file_code_ns[body_open + 1 : body_close]
            # Detect passthrough `Command::new(<param>)` builder helpers.
            for p_idx, pname in enumerate(param_names):
                if not pname:
                    continue
                probe_env = dict(env)
                probe_env[pname] = "bin_capture"
                if (
                    _rust_helper_eval_statements(
                        body_nc_str,
                        body_ns_str,
                        base_env=probe_env,
                        base_types={"self": owner_type} if owner_type else {},
                        facts=base_const_facts,
                        mode="cmd",
                    )
                    == "cmd_capture"
                    and _rust_helper_eval_statements(
                        body_nc_str,
                        body_ns_str,
                        base_env=env,
                        base_types={"self": owner_type} if owner_type else {},
                        facts=base_const_facts,
                        mode="cmd",
                    )
                    is None
                ):
                    if owner_type is not None and is_method:
                        passthrough_cmd_methods[(owner_type, name)] = p_idx
                    elif owner_type is None:
                        passthrough_cmd_fns[qual_key] = p_idx
                    break

            fn_records.append(
                (
                    qual_key,
                    name,
                    mod_scope,
                    owner_type,
                    impl_trait_name,
                    is_method,
                    param_names,
                    body_nc_str,
                    body_ns_str,
                )
            )

    local_fns = frozenset(all_fn_names)
    local_free_frozen = frozenset(local_free_fns)
    method_all_types = {k: frozenset(v) for k, v in method_all_types_mut.items()}

    # Track free-fn name collisions across modules: an unqualified free fn name
    # is safe only if its top-level/module definition is unambiguously capture.
    top_free_names = {
        rec[1] for rec in fn_records if rec[3] is None and not rec[2]
    }
    all_free_by_name: dict[str, set[str]] = {}
    for qk, bname, _ms, owner_ty, _it, _im, _pl, _bnc, _bns in fn_records:
        if owner_ty is None:
            all_free_by_name.setdefault(bname, set()).add(qk)

    free_returns_untrusted = frozenset(
        bname
        for bname, qks in all_free_by_name.items()
        if qks & fn_returns_untrusted_q
    )
    method_returns_untrusted = {
        k: frozenset(v) for k, v in method_returns_untrusted_mut.items()
    }

    def _build_facts(
        cap_q: set[str],
        drv_q: set[str],
        cap_cmd_q: set[str],
        drv_cmd_q: set[str],
        cap_bin_q: set[str],
        drv_bin_q: set[str],
        m_cap: dict[str, set[str]],
        m_drv: dict[str, set[str]],
        m_cap_cmd: dict[str, set[str]],
        m_drv_cmd: dict[str, set[str]],
        m_cap_bin: dict[str, set[str]],
        m_drv_bin: dict[str, set[str]],
        may_exit_q: set[str] | None = None,
        must_exit_q: set[str] | None = None,
        m_may_exit: dict[str, set[str]] | None = None,
        drop_may_exit: set[str] | None = None,
        mod_scope: tuple[str, ...] = (),
        fn_auth_map: dict[str, str] | None = None,
    ) -> _RustFileFacts:
        meq = may_exit_q or set()
        muq = must_exit_q or set()
        mme = m_may_exit or {}
        dme = drop_may_exit or set()
        free_cap = frozenset(
            n
            for n in top_free_names
            if n in cap_q and all_free_by_name.get(n, set()) <= cap_q
        )
        free_drv = frozenset(
            n
            for n in top_free_names
            if n in drv_q and all_free_by_name.get(n, set()) <= (cap_q | drv_q)
        )
        free_cap_cmd = frozenset(
            n
            for n in top_free_names
            if n in cap_cmd_q and all_free_by_name.get(n, set()) <= cap_cmd_q
        )
        free_drv_cmd = frozenset(
            n
            for n in top_free_names
            if n in drv_cmd_q
            and all_free_by_name.get(n, set()) <= (cap_cmd_q | drv_cmd_q)
        )
        free_cap_bin = frozenset(
            n
            for n in top_free_names
            if n in cap_bin_q and all_free_by_name.get(n, set()) <= cap_bin_q
        )
        free_drv_bin = frozenset(
            n
            for n in top_free_names
            if n in drv_bin_q
            and all_free_by_name.get(n, set()) <= (cap_bin_q | drv_bin_q)
        )
        # Fail-closed for exits: ANY matching top-level/local fn may exit.
        free_may_exit = frozenset(
            n for n in top_free_names if n in meq
        )
        free_must_exit = frozenset(
            n
            for n in top_free_names
            if n in muq and all_free_by_name.get(n, set()) <= muq
        )
        return _RustFileFacts(
            local_fns=local_fns,
            local_free_fns=local_free_frozen,
            local_types_or_mods=local_types_or_mods,
            use_aliases=use_aliases,
            capture_fns=free_cap,
            driver_fns=free_drv,
            capture_cmd_fns=free_cap_cmd,
            driver_cmd_fns=free_drv_cmd,
            capture_bin_fns=free_cap_bin,
            driver_bin_fns=free_drv_bin,
            qualified_capture_fns=frozenset(cap_q),
            qualified_driver_fns=frozenset(drv_q),
            qualified_capture_cmd_fns=frozenset(cap_cmd_q),
            qualified_driver_cmd_fns=frozenset(drv_cmd_q),
            qualified_capture_bin_fns=frozenset(cap_bin_q),
            qualified_driver_bin_fns=frozenset(drv_bin_q),
            method_capture_types={k: frozenset(v) for k, v in m_cap.items()},
            method_driver_types={k: frozenset(v) for k, v in m_drv.items()},
            method_capture_cmd_types={
                k: frozenset(v) for k, v in m_cap_cmd.items()
            },
            method_driver_cmd_types={
                k: frozenset(v) for k, v in m_drv_cmd.items()
            },
            method_capture_bin_types={
                k: frozenset(v) for k, v in m_cap_bin.items()
            },
            method_driver_bin_types={
                k: frozenset(v) for k, v in m_drv_bin.items()
            },
            method_all_types=method_all_types,
            passthrough_cmd_fns=dict(passthrough_cmd_fns),
            passthrough_cmd_methods=dict(passthrough_cmd_methods),
            fn_return_types=dict(fn_return_types),
            custom_eq_types=custom_eq_types,
            extension_overridden_methods=extension_overridden_methods,
            method_override_types=method_override_types,
            fn_returns_untrusted=free_returns_untrusted,
            qualified_fn_returns_untrusted=frozenset(fn_returns_untrusted_q),
            method_returns_untrusted_types=method_returns_untrusted,
            may_exit_success_fns=free_may_exit,
            must_exit_success_fns=free_must_exit,
            qualified_may_exit_success_fns=frozenset(meq),
            qualified_must_exit_success_fns=frozenset(muq),
            method_may_exit_types={k: frozenset(v) for k, v in mme.items()},
            drop_may_exit_types=frozenset(dme),
            extern_exit_fns=extern_exit_fns,
            fn_authority_families=dict(fn_auth_map or {}),
            test_mod_scope=mod_scope,
        )

    # 1. Fixed-point authenticated binary-path helper classification.
    cap_bin_q: set[str] = set()
    drv_bin_q: set[str] = set()
    m_cap_bin: dict[str, set[str]] = {}
    m_drv_bin: dict[str, set[str]] = {}
    changed = True
    while changed:
        changed = False
        for qk, bname, mod_scope, owner_ty, _it, _im, _pl, body_nc, body_ns in fn_records:
            cur_facts = _build_facts(
                set(), set(), set(), set(), cap_bin_q, drv_bin_q,
                {}, {}, {}, {}, m_cap_bin, m_drv_bin, mod_scope=mod_scope,
            )
            t_env = {"self": owner_ty} if owner_ty is not None else {}
            bk = _rust_helper_eval_statements(
                body_nc,
                body_ns,
                base_env=env,
                base_types=t_env,
                facts=cur_facts,
                mode="bin",
            )
            if bk == "bin_capture" and qk not in cap_bin_q:
                cap_bin_q.add(qk)
                drv_bin_q.discard(qk)
                if owner_ty is not None:
                    m_cap_bin.setdefault(bname, set()).add(owner_ty)
                    m_drv_bin.get(bname, set()).discard(owner_ty)
                    cap_bin_q.add(f"{owner_ty}::{bname}")
                changed = True
            elif bk == "bin_driver" and qk not in cap_bin_q and qk not in drv_bin_q:
                drv_bin_q.add(qk)
                if owner_ty is not None:
                    m_drv_bin.setdefault(bname, set()).add(owner_ty)
                    drv_bin_q.add(f"{owner_ty}::{bname}")
                changed = True

    # 2. Fixed-point authenticated Command builder classification.
    cap_cmd_q: set[str] = set()
    drv_cmd_q: set[str] = set()
    m_cap_cmd: dict[str, set[str]] = {}
    m_drv_cmd: dict[str, set[str]] = {}
    changed = True
    while changed:
        changed = False
        for qk, bname, mod_scope, owner_ty, _it, _im, _pl, body_nc, body_ns in fn_records:
            cur_facts = _build_facts(
                set(), set(), cap_cmd_q, drv_cmd_q, cap_bin_q, drv_bin_q,
                {}, {}, m_cap_cmd, m_drv_cmd, m_cap_bin, m_drv_bin,
                mod_scope=mod_scope,
            )
            t_env = {"self": owner_ty} if owner_ty is not None else {}
            ck = _rust_helper_eval_statements(
                body_nc,
                body_ns,
                base_env=env,
                base_types=t_env,
                facts=cur_facts,
                mode="cmd",
            )
            if ck == "cmd_capture" and qk not in cap_cmd_q:
                cap_cmd_q.add(qk)
                drv_cmd_q.discard(qk)
                if owner_ty is not None:
                    m_cap_cmd.setdefault(bname, set()).add(owner_ty)
                    m_drv_cmd.get(bname, set()).discard(owner_ty)
                    cap_cmd_q.add(f"{owner_ty}::{bname}")
                changed = True
            elif ck == "cmd_driver" and qk not in cap_cmd_q and qk not in drv_cmd_q:
                drv_cmd_q.add(qk)
                if owner_ty is not None:
                    m_drv_cmd.setdefault(bname, set()).add(owner_ty)
                    drv_cmd_q.add(f"{owner_ty}::{bname}")
                changed = True

    # 3. Fixed-point capture/driver execution helper classification.
    cap_q: set[str] = set()
    drv_q: set[str] = set()
    m_cap: dict[str, set[str]] = {}
    m_drv: dict[str, set[str]] = {}
    changed = True
    while changed:
        changed = False
        for qk, bname, mod_scope, owner_ty, _it, _im, _pl, body_nc, body_ns in fn_records:
            if qk in cap_q:
                continue
            cur_facts = _build_facts(
                cap_q, drv_q, cap_cmd_q, drv_cmd_q, cap_bin_q, drv_bin_q,
                m_cap, m_drv, m_cap_cmd, m_drv_cmd, m_cap_bin, m_drv_bin,
                mod_scope=mod_scope,
            )
            t_env = {"self": owner_ty} if owner_ty is not None else {}
            okind = _rust_helper_eval_statements(
                body_nc,
                body_ns,
                base_env=env,
                base_types=t_env,
                facts=cur_facts,
                mode="obs",
            )
            if okind == "obs_capture":
                cap_q.add(qk)
                drv_q.discard(qk)
                if owner_ty is not None:
                    m_cap.setdefault(bname, set()).add(owner_ty)
                    m_drv.get(bname, set()).discard(owner_ty)
                    cap_q.add(f"{owner_ty}::{bname}")
                changed = True
            elif okind == "obs_driver" and qk not in drv_q:
                drv_q.add(qk)
                if owner_ty is not None:
                    m_drv.setdefault(bname, set()).add(owner_ty)
                    drv_q.add(f"{owner_ty}::{bname}")
                changed = True

    # 4. Fixed-point transitive successful-process-exit helper classification.
    may_exit_q: set[str] = set()
    must_exit_q: set[str] = set()
    m_may_exit: dict[str, set[str]] = {}
    drop_may_exit: set[str] = set()
    changed = True
    while changed:
        changed = False
        for qk, bname, mod_scope, owner_ty, impl_tr, _im, _pl, body_nc, body_ns in fn_records:
            cur_facts = _build_facts(
                cap_q, drv_q, cap_cmd_q, drv_cmd_q, cap_bin_q, drv_bin_q,
                m_cap, m_drv, m_cap_cmd, m_drv_cmd, m_cap_bin, m_drv_bin,
                may_exit_q=may_exit_q,
                must_exit_q=must_exit_q,
                m_may_exit=m_may_exit,
                drop_may_exit=drop_may_exit,
                mod_scope=mod_scope,
            )
            f_may, f_must = _rust_body_exit_classification(
                body_nc, body_ns, facts=cur_facts, owner_ty=owner_ty
            )
            if f_may and qk not in may_exit_q:
                may_exit_q.add(qk)
                if owner_ty is not None:
                    m_may_exit.setdefault(bname, set()).add(owner_ty)
                    may_exit_q.add(f"{owner_ty}::{bname}")
                    if bname == "drop" and impl_tr == "Drop":
                        drop_may_exit.add(owner_ty)
                changed = True
            if f_must and qk not in must_exit_q:
                must_exit_q.add(qk)
                if owner_ty is not None:
                    must_exit_q.add(f"{owner_ty}::{bname}")
                changed = True

    # 5. Fixed-point helper authority-family map (`capture` vs `oracle_*`).
    fn_auth_q: dict[str, str] = dict(const_auth)
    auth_changed = True
    while auth_changed:
        auth_changed = False
        for qk, bname, mod_scope, owner_ty, _it, _im, _pl, body_nc, body_ns in fn_records:
            if qk in fn_auth_q:
                continue
            cur_facts = _build_facts(
                cap_q, drv_q, cap_cmd_q, drv_cmd_q, cap_bin_q, drv_bin_q,
                m_cap, m_drv, m_cap_cmd, m_drv_cmd, m_cap_bin, m_drv_bin,
                may_exit_q=may_exit_q,
                must_exit_q=must_exit_q,
                m_may_exit=m_may_exit,
                drop_may_exit=drop_may_exit,
                mod_scope=mod_scope,
                fn_auth_map=fn_auth_q,
            )
            t_env = {"self": owner_ty} if owner_ty is not None else {}
            fam = _rust_helper_eval_authority_family(
                body_nc,
                body_ns,
                base_auth_env=const_auth,
                base_types=t_env,
                facts=cur_facts,
            )
            if fam is not None:
                fn_auth_q[qk] = fam
                if owner_ty is not None:
                    fn_auth_q[f"{owner_ty}::{bname}"] = fam
                auth_changed = True
    # Only expose unqualified top-level names when all matching defs agree.
    for bname, qks in all_free_by_name.items():
        if bname in top_free_names and qks:
            q_fams = [fn_auth_q.get(qk) for qk in qks]
            if q_fams[0] is not None and all(f == q_fams[0] for f in q_fams):
                fn_auth_q[bname] = q_fams[0]

    final_facts = _build_facts(
        cap_q, drv_q, cap_cmd_q, drv_cmd_q, cap_bin_q, drv_bin_q,
        m_cap, m_drv, m_cap_cmd, m_drv_cmd, m_cap_bin, m_drv_bin,
        may_exit_q=may_exit_q,
        must_exit_q=must_exit_q,
        m_may_exit=m_may_exit,
        drop_may_exit=drop_may_exit,
        fn_auth_map=fn_auth_q,
    )
    pure_fns = local_fns - final_facts.capture_fns - final_facts.driver_fns
    return pure_fns, env, final_facts


def _skip_leading_rust_attrs(text_ns: str) -> int:
    """Return offset past leading outer `#[...]` attributes in `text_ns`."""
    pos = 0
    n = len(text_ns)
    while pos < n:
        while pos < n and text_ns[pos].isspace():
            pos += 1
        if pos < n and text_ns[pos] == "#":
            j = pos + 1
            while j < n and text_ns[j].isspace():
                j += 1
            if j < n and text_ns[j] == "[":
                close_b = _find_matching_delimiter_in_code(text_ns, j)
                if close_b is not None:
                    pos = close_b + 1
                    continue
        break
    return pos


def _split_rust_top_level_segments(
    code_ns: str, start: int = 0, end: int | None = None
) -> list[tuple[str, int, int, int | None]]:
    """Split Rust block interior into `(kind, seg_start, seg_end, brace_open)`."""
    if end is None:
        end = len(code_ns)
    segments: list[tuple[str, int, int, int | None]] = []
    i = start
    while i < end:
        while i < end and code_ns[i].isspace():
            i += 1
        if i >= end:
            break
        seg_start = i
        p_d = 0
        b_d = 0
        br_d = 0
        saw_top_assign = False
        added = False
        while i < end:
            ch = code_ns[i]
            nxt = code_ns[i + 1] if i + 1 < end else ""
            prev = code_ns[i - 1] if i > seg_start else ""
            if ch == "(":
                p_d += 1
            elif ch == ")" and p_d > 0:
                p_d -= 1
            elif ch == "[":
                b_d += 1
            elif ch == "]" and b_d > 0:
                b_d -= 1
            elif p_d == 0 and b_d == 0:
                if (
                    br_d == 0
                    and ch == "="
                    and prev not in ("=", "!", "<", ">")
                    and nxt not in ("=", ">")
                ):
                    saw_top_assign = True
                if br_d == 0 and ch == ";":
                    segments.append(("stmt", seg_start, i + 1, None))
                    i += 1
                    added = True
                    break
                if ch == "{":
                    close_b = _find_matching_delimiter_in_code(code_ns, i)
                    if close_b is not None and close_b < end and br_d == 0:
                        hdr = code_ns[seg_start:i].lstrip()
                        hdr_body = hdr[_skip_leading_rust_attrs(hdr) :].lstrip()
                        lbl_hdr = re.match(
                            r"^'[A-Za-z_][A-Za-z0-9_]*\s*:\s*", hdr_body
                        )
                        hdr_after_lbl = (
                            hdr_body[lbl_hdr.end() :]
                            if lbl_hdr is not None
                            else hdr_body
                        )
                        is_ctrl = bool(
                            re.match(
                                r"^(?:if|else|while|for|loop|match|unsafe)\b",
                                hdr_after_lbl,
                            )
                            or (lbl_hdr is not None and not hdr_after_lbl.strip())
                            or hdr.rstrip().endswith("=>")
                        )
                        if is_ctrl or (not hdr and not saw_top_assign):
                            segments.append(("block", seg_start, close_b + 1, i))
                            i = close_b + 1
                            added = True
                            break
                    br_d += 1
                elif ch == "}" and br_d > 0:
                    br_d -= 1
            i += 1
        if not added and i > seg_start:
            segments.append(("stmt", seg_start, end, None))
    return segments


def _split_rust_match_arm_spans(
    ns: str, start: int, end: int
) -> list[tuple[int, int, int, int]]:
    """Return `(pat_start, pat_end, rhs_start, rhs_end)` match arm spans."""
    spans: list[tuple[int, int, int, int]] = []
    pos = start
    while pos < end:
        while pos < end and ns[pos].isspace():
            pos += 1
        if pos >= end:
            break
        while pos < end and ns[pos] == "#":
            attr_m = re.match(r"#\s*\[", ns[pos:end])
            if attr_m is None:
                break
            close_a = _find_matching_delimiter_in_code(
                ns, pos + attr_m.end() - 1
            )
            if close_a is None or close_a >= end:
                return spans
            pos = close_a + 1
            while pos < end and ns[pos].isspace():
                pos += 1
        if pos >= end:
            break
        rel_arrow = _find_depth0_fat_arrow(ns[pos:end], 0)
        if rel_arrow is None:
            break
        arrow = pos + rel_arrow
        rhs_s = arrow + 2
        while rhs_s < end and ns[rhs_s].isspace():
            rhs_s += 1
        if rhs_s >= end:
            break
        if ns[rhs_s] == "{":
            b_close = _find_matching_delimiter_in_code(ns, rhs_s)
            if b_close is not None and b_close < end:
                after = ns[b_close + 1 : end]
                cm = re.match(r"\s*,", after)
                if cm is not None or not after.strip() or (
                    _find_depth0_fat_arrow(after, 0) is not None
                ):
                    spans.append((pos, arrow, rhs_s, b_close + 1))
                    pos = b_close + 1 + (cm.end() if cm is not None else 0)
                    continue
        p_d = b_d = br_d = 0
        q = rhs_s
        while q < end:
            qc = ns[q]
            if qc == "(":
                p_d += 1
            elif qc == ")" and p_d > 0:
                p_d -= 1
            elif qc == "[":
                b_d += 1
            elif qc == "]" and b_d > 0:
                b_d -= 1
            elif qc == "{":
                br_d += 1
            elif qc == "}" and br_d > 0:
                br_d -= 1
            elif p_d == 0 and b_d == 0 and br_d == 0 and qc == ",":
                break
            q += 1
        spans.append((pos, arrow, rhs_s, q))
        pos = q + 1 if q < end else end
    return spans


def _strip_rust_match_guard(pat_ns: str) -> tuple[str, int | None]:
    """Split `(pat_only, guard_offset)` at a top-level `if` match guard."""
    p_d = b_d = br_d = 0
    n = len(pat_ns)
    for i, ch in enumerate(pat_ns):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == "i":
            if (
                pat_ns[i : i + 2] == "if"
                and (
                    i == 0
                    or not (pat_ns[i - 1].isalnum() or pat_ns[i - 1] == "_")
                )
                and (
                    i + 2 == n
                    or not (pat_ns[i + 2].isalnum() or pat_ns[i + 2] == "_")
                )
            ):
                return pat_ns[:i], i + 2
    return pat_ns, None


def _merge_rust_use_aliases(
    base: dict[str, frozenset[str]] | None,
    extra: dict[str, frozenset[str]],
) -> dict[str, frozenset[str]]:
    merged: dict[str, set[str]] = {
        k: set(v) for k, v in (base or {}).items()
    }
    for k, v in extra.items():
        merged.setdefault(k, set()).update(v)
    return {k: frozenset(v) for k, v in merged.items()}


def _rust_for_iter_is_statically_non_empty(iter_nc: str, iter_ns: str) -> bool:
    """Return True iff a Rust `for` iterable is statically guaranteed >= 1 item."""
    ns = iter_ns.strip()
    nc = iter_nc.strip()
    while ns.startswith("(") and ns.endswith(")"):
        if _find_matching_delimiter_in_code(ns, 0) != len(ns) - 1:
            break
        ns = ns[1:-1].strip()
        nc = nc[1:-1].strip()
    m_incl = re.fullmatch(
        r"(-?\d+(?:_\d+)*)(?:[ui](?:8|16|32|64|128|size))?\s*\.\.=\s*"
        r"(-?\d+(?:_\d+)*)(?:[ui](?:8|16|32|64|128|size))?",
        ns,
    )
    if m_incl is not None:
        return int(m_incl.group(1).replace("_", "")) <= int(
            m_incl.group(2).replace("_", "")
        )
    m_excl = re.fullmatch(
        r"(-?\d+(?:_\d+)*)(?:[ui](?:8|16|32|64|128|size))?\s*\.\.\s*"
        r"(-?\d+(?:_\d+)*)(?:[ui](?:8|16|32|64|128|size))?",
        ns,
    )
    if m_excl is not None:
        return int(m_excl.group(1).replace("_", "")) < int(
            m_excl.group(2).replace("_", "")
        )
    arr_m = re.fullmatch(r"(?:&\s*(?:mut\s+)?)?\[([\s\S]*)\]", ns)
    if arr_m is None:
        arr_m = re.fullmatch(r"(?:vec\s*!)\s*\[([\s\S]*)\]", ns)
    if arr_m is not None:
        inner = arr_m.group(1).strip()
        if not inner:
            return False
        rep_m = re.search(r";\s*(\d+(?:_\d+)*)(?:usize)?\s*$", inner)
        if rep_m is not None:
            return int(rep_m.group(1).replace("_", "")) > 0
        # Non-empty literal element list (check `nc` for string literals too).
        nc_inner_m = re.search(r"\[([\s\S]*)\]", nc)
        return bool(nc_inner_m and nc_inner_m.group(1).strip())
    return False


def _rust_pos_is_conditional_in_span(seg_ns: str, rel_pos: int) -> bool:
    """Return True if `rel_pos` sits under `{...}` or RHS of `&&`/`||`."""
    # Track short-circuit `&&`/`||` per open delimiter level so parenthesized
    # forms like `(false && (assert!(a), assert!(b), true).2)` remain marked
    # conditional while earlier tuple elements `(a && b, assert!(c))` reset at
    # top-level `,` or `;`.
    cond_stack: list[bool] = [False]
    br_d = 0
    i = 0
    while i < rel_pos:
        ch = seg_ns[i]
        if ch in "([{":
            if ch == "{":
                br_d += 1
            cond_stack.append(False)
        elif ch in ")]}":
            if ch == "}" and br_d > 0:
                br_d -= 1
            if len(cond_stack) > 1:
                cond_stack.pop()
        elif ch in ",;":
            cond_stack[-1] = False
        elif seg_ns[i : i + 2] in ("&&", "||"):
            cond_stack[-1] = True
            i += 2
            continue
        i += 1
    return br_d > 0 or any(cond_stack)


def _rust_stmt_is_pure_closure_binding(
    stmt_ns: str, seg_start: int, closure_spans: list[tuple[int, int]]
) -> bool:
    """Return True if `stmt_ns` only binds a closure (`let f = || ...;`) without calling it."""
    eq_pos = _find_rust_top_level_equal(stmt_ns)
    if eq_pos is None:
        return False
    rhs_rel = eq_pos + 1
    while rhs_rel < len(stmt_ns) and stmt_ns[rhs_rel].isspace():
        rhs_rel += 1
    rhs = stmt_ns[rhs_rel:].rstrip("; \t\r\n")
    if not rhs:
        return False
    # Must start with `move |` / `|` and end at the closure body (not `()()`).
    if not re.match(r"^(?:(?:move|async|static)\s+)*\|", rhs):
        return False
    rhs_end_abs = seg_start + rhs_rel + len(rhs)
    return any(
        cs >= seg_start + rhs_rel and ce == rhs_end_abs for cs, ce in closure_spans
    )


def _rust_rhs_creates_exit_callable(
    rhs_ns: str,
    *,
    facts: _RustFileFacts,
    local_may_exit_fns: frozenset[str],
    cur_exit_vars: frozenset[str],
    type_env: dict[str, str],
) -> bool:
    """Return True if `rhs_ns` defines a closure or fn-pointer alias that may exit 0."""
    s = rhs_ns.strip().rstrip(";").strip()
    if not s:
        return False
    # 1. Closure expression `|...| body` whose body may exit 0.
    if re.match(r"^(?:(?:move|async|static)\s+)*\|", s):
        may_ex, _ = _rust_expr_calls_exit_success(
            s,
            facts=facts,
            local_may_exit_fns=local_may_exit_fns,
            cur_exit_vars=cur_exit_vars,
            type_env=type_env,
        )
        return may_ex
    # 2. Function pointer alias (`let f = std::process::exit;` or `bail`).
    p_s = re.sub(r"\s+", "", s).lstrip(":")
    if re.fullmatch(r"(?:[A-Za-z_][A-Za-z0-9_]*::)*[A-Za-z_][A-Za-z0-9_]*", p_s):
        if p_s in cur_exit_vars or p_s in local_may_exit_fns:
            return True
        if p_s in facts.extern_exit_fns:
            return True
        aliases = facts.use_aliases or {}
        expanded = (
            _resolve_rust_qualified_path(p_s, facts)
            if ("::" in p_s or p_s in aliases)
            else [p_s]
        )
        for ep in expanded:
            ep_clean = ep.lstrip(":")
            if ep_clean in (
                "std::process::exit",
                "core::process::exit",
                "process::exit",
                "libc::exit",
                "libc::_exit",
                "libc::_Exit",
                "libc::quick_exit",
            ):
                return True
            cands = _normalize_local_rust_path(ep_clean, facts.test_mod_scope)
            if (
                ("::" not in ep_clean and ep_clean in facts.may_exit_success_fns)
                or any(c in facts.qualified_may_exit_success_fns for c in cands)
            ):
                return True
    return False


def _rust_stmt_exit_or_jump(
    stmt_ns: str,
    seg_start: int,
    closure_spans: list[tuple[int, int]],
    *,
    facts: _RustFileFacts | None = None,
    local_may_exit_fns: frozenset[str] = frozenset(),
    local_must_exit_fns: frozenset[str] = frozenset(),
    cur_exit_vars: frozenset[str] = frozenset(),
    type_env: dict[str, str] | None = None,
    proc_exit_out: list[bool] | None = None,
) -> tuple[object | None, object | None]:
    """Classify `(pre_assert_exit, post_assert_exit)` exits/jumps in a Rust stmt."""
    rfacts = facts or _RustFileFacts()
    chars = list(stmt_ns)
    seg_end = seg_start + len(stmt_ns)
    for cs, ce in closure_spans:
        ov_s = max(cs, seg_start)
        ov_e = min(ce, seg_end)
        if ov_s < ov_e:
            _blank_span(chars, ov_s - seg_start, ov_e - seg_start)
    clean = "".join(chars).strip().rstrip(";").strip()
    if not clean:
        return None, None

    # Check transitive helper / process::exit(0) / libc::exit(0) / Drop bombs.
    # Unlike `return`, `process::exit(0)` inside an invoked/passed closure
    # (e.g. `(|| std::process::exit(0))()` or `.map(|_| bail())`) exits the
    # whole test process; only skip closure bodies on pure `let f = || ...;`.
    scan_for_proc_exit = (
        clean
        if _rust_stmt_is_pure_closure_binding(stmt_ns, seg_start, closure_spans)
        else stmt_ns.strip().rstrip(";").strip()
    )
    proc_may_exit, proc_whole_must = _rust_expr_calls_exit_success(
        scan_for_proc_exit,
        facts=rfacts,
        local_may_exit_fns=local_may_exit_fns,
        local_must_exit_fns=local_must_exit_fns,
        cur_exit_vars=cur_exit_vars,
        type_env=type_env,
    )
    pre_exit: object | None = None
    if proc_whole_must:
        if proc_exit_out is not None:
            proc_exit_out.append(True)
        return _CfgExit(is_success=True), None
    if proc_may_exit:
        if proc_exit_out is not None:
            proc_exit_out.append(True)
        pre_exit = _CfgBranch((_CfgExit(is_success=True), _CfgSeq(())))

    # Unconditional failing exits (`panic!`, `unreachable!`, `abort()`,
    # `return Err(...)`, `exit(nonzero)`).
    if re.match(
        r"^(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
        r"(?:panic|unreachable|todo|unimplemented)\s*!\s*[(\[{]",
        clean,
    ):
        return pre_exit, _CfgExit(is_success=False)
    if re.match(
        r"^(?:(?:::\s*)?(?:std|core)\s*::\s*)?process\s*::\s*abort\s*\(",
        clean,
    ):
        return pre_exit, _CfgExit(is_success=False)
    exit_m = re.match(
        r"^((?:(?:::\s*)?[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*[A-Za-z_][A-Za-z0-9_]*)\s*\(",
        clean,
    )
    if exit_m is not None:
        op_i = exit_m.end() - 1
        cl_i = _find_matching_delimiter_in_code(clean, op_i)
        if cl_i == len(clean) - 1:
            dex = _rust_call_is_direct_process_exit(
                exit_m.group(1), clean[op_i + 1 : cl_i], facts=rfacts
            )
            if dex == "exit_fail":
                return pre_exit, _CfgExit(is_success=False)
            if dex == "exit_success":
                if proc_exit_out is not None:
                    proc_exit_out.append(True)
                return _CfgExit(is_success=True), None
    if re.match(r"^return\b", clean):
        after_ret = clean[len("return") :].strip()
        if re.match(
            r"^(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*Result\s*::\s*)?Err\s*\(",
            after_ret,
        ):
            return pre_exit, _CfgExit(is_success=False)
        return pre_exit, _CfgExit(is_success=True)
    brk_m = re.match(r"^break(?:\s+('[A-Za-z_][A-Za-z0-9_]*))?\b", clean)
    if brk_m is not None:
        return pre_exit, _CfgLoopJump("break", label=brk_m.group(1))
    cnt_m = re.match(r"^continue(?:\s+('[A-Za-z_][A-Za-z0-9_]*))?\b", clean)
    if cnt_m is not None:
        return pre_exit, _CfgLoopJump("continue", label=cnt_m.group(1))

    # Nested conditional early returns/breaks/continues are emitted at their
    # source offsets inside `_collect_in_span` so they precede any later
    # assertions in the same statement (e.g. tuple elements).
    return pre_exit, None


def _rust_if_cond_capture_polarity(
    chdr_ns: str,
    chdr_code: str,
    *,
    rust_env: dict[str, str],
    rust_facts: _RustFileFacts,
    rust_type_env: dict[str, str],
) -> str:
    """Classify Rust `if`-header polarity toward capture success."""
    hm = re.match(r"^\s*(?:else\s+)?if\b([\s\S]+)$", chdr_ns)
    if hm is None:
        return "other"
    off = hm.start(1)
    cond_ns = chdr_ns[off:].strip()
    cond_nc = chdr_code[off:].strip()

    let_m = re.match(r"^let\b([\s\S]+)$", cond_ns)
    if let_m is not None:
        eq_p = _find_rust_top_level_equal(let_m.group(1))
        if eq_p is not None:
            pat_s = let_m.group(1)[:eq_p].strip()
            e_off = let_m.start(1) + eq_p + 1
            rhs_ns = cond_ns[e_off:].strip()
            rhs_nc = cond_nc[e_off:].strip()
            okind = _rust_expr_origin_kind(
                rhs_nc,
                rhs_ns,
                rust_env=rust_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )
            if okind in RUST_OBS_STATES or re.search(
                r"\.\s*(?:status|output|code|success)\b", rhs_ns
            ):
                if re.match(
                    r"^(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*Result\s*::\s*)?Ok\s*\(",
                    pat_s,
                ):
                    return "positive_success"
                if re.match(
                    r"^(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*Result\s*::\s*)?Err\s*\(",
                    pat_s,
                ):
                    return "negated_success"
        return "other"

    def _strip_parens(s: str) -> str:
        cur = s.strip()
        while cur.startswith("(") and cur.endswith(")"):
            if _find_matching_delimiter_in_code(cur, 0) != len(cur) - 1:
                break
            cur = cur[1:-1].strip()
        return cur

    def _classify(expr_s: str) -> str:
        s = _strip_parens(expr_s)
        if not s:
            return "other"
        if s.startswith("!") and not s.startswith("!="):
            inner_pol = _classify(s[1:])
            if inner_pol == "positive_success":
                return "negated_success"
            if inner_pol == "negated_success":
                return "positive_success"
            return "other"
        or_parts = _split_top_level_rust_op(s, "||")
        if len(or_parts) > 1:
            pols = [_classify(p[2]) for p in or_parts]
            if "positive_success" in pols and "negated_success" not in pols:
                return "positive_success"
            if all(p == "negated_success" for p in pols):
                return "negated_success"
            return "other"
        and_parts = _split_top_level_rust_op(s, "&&")
        if len(and_parts) > 1:
            pols = [_classify(p[2]) for p in and_parts]
            if "positive_success" in pols and "negated_success" not in pols:
                return "positive_success"
            if all(p == "negated_success" for p in pols):
                return "negated_success"
            return "other"
        has_obs = bool(
            re.search(r"\.\s*(?:status|code)\s*\(", s)
            or re.search(r"\.\s*status\b", s)
            or _rust_expr_origin_kind(
                s,
                s,
                rust_env=rust_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )
            in RUST_OBS_STATES
        )
        if not has_obs:
            return "other"
        eq_parts = _split_top_level_rust_op(s, "==")
        if len(eq_parts) == 2:
            a, b = _strip_parens(eq_parts[0][2]), _strip_parens(eq_parts[1][2])
            if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)$", a):
                if b == "true":
                    return "positive_success"
                if b == "false":
                    return "negated_success"
            if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)$", b):
                if a == "true":
                    return "positive_success"
                if a == "false":
                    return "negated_success"
            if re.search(r"\.\s*code\s*\(\s*\)$", a):
                if re.fullmatch(r"Some\s*\(\s*0\s*\)", b):
                    return "positive_success"
                if re.fullmatch(r"Some\s*\(\s*[1-9][0-9]*\s*\)|None", b):
                    return "negated_success"
            if re.search(r"\.\s*code\s*\(\s*\)$", b):
                if re.fullmatch(r"Some\s*\(\s*0\s*\)", a):
                    return "positive_success"
                if re.fullmatch(r"Some\s*\(\s*[1-9][0-9]*\s*\)|None", a):
                    return "negated_success"
        ne_parts = _split_top_level_rust_op(s, "!=")
        if len(ne_parts) == 2:
            a, b = _strip_parens(ne_parts[0][2]), _strip_parens(ne_parts[1][2])
            if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)$", a):
                if b == "true":
                    return "negated_success"
                if b == "false":
                    return "positive_success"
            if re.search(r"\.\s*code\s*\(\s*\)$", a) and re.fullmatch(
                r"Some\s*\(\s*0\s*\)", b
            ):
                return "negated_success"
            if re.search(r"\.\s*code\s*\(\s*\)$", b) and re.fullmatch(
                r"Some\s*\(\s*0\s*\)", a
            ):
                return "negated_success"
        if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)$", s):
            return "positive_success"
        if re.search(r"\.\s*is_err\s*\(\s*\)$", s):
            return "negated_success"
        if re.fullmatch(
            r"(?:(?:::\s*)?(?:core|std)\s*::\s*)?matches\s*!\s*\([^,]*\.\s*code\s*\(\s*\)\s*,\s*Some\s*\(\s*0\s*\)\s*\)",
            s,
        ):
            return "positive_success"
        return "other"

    return _classify(cond_ns)


def _rust_match_arm_requires_capture_failure(scrut_ns: str, pat_ns: str) -> bool:
    """Return True if a failing match arm traps positive capture success."""
    if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)", scrut_ns):
        return pat_ns == "true"
    if re.search(r"\.\s*code\s*\(\s*\)", scrut_ns):
        return re.fullmatch(r"Some\s*\(\s*0\s*\)", pat_ns) is not None
    return bool(
        re.match(
            r"^(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*Result\s*::\s*)?Ok\s*\(",
            pat_ns,
        )
    )


def _collect_rust_assertion_items_with_cfg(
    fn_code: str,
    fn_code_ns: str,
    *,
    init_env: dict[str, str] | None = None,
    pure_rust_fns: frozenset[str] = frozenset(),
    rust_facts: _RustFileFacts | None = None,
    test_mod_scope: tuple[str, ...] = (),
    saw_proc_exit: list[bool] | None = None,
    saw_fail_on_success: list[bool] | None = None,
) -> tuple[list[_AssertionItem], object]:
    """Return `(items, cfg_node)` with live reachability, dataflow & CFG."""
    base_facts = rust_facts or _RustFileFacts(local_fns=pure_rust_fns)
    fn_use_aliases = _collect_rust_use_aliases(fn_code_ns)
    fn_local_types = _collect_rust_local_types_or_mods(fn_code_ns)
    (
        fn_custom_eq,
        fn_ext_overrides,
        fn_method_overrides,
        fn_has_custom_eq,
        fn_extern_exits,
    ) = _collect_rust_impl_and_extern_facts(fn_code_ns)
    merged_aliases = _merge_rust_use_aliases(
        base_facts.use_aliases, fn_use_aliases
    )
    merged_types = base_facts.local_types_or_mods | fn_local_types
    merged_custom_eq = base_facts.custom_eq_types | fn_custom_eq
    merged_ext_overrides = base_facts.extension_overridden_methods | fn_ext_overrides
    merged_method_overrides: dict[str, set[str]] = {
        k: set(v) for k, v in (base_facts.method_override_types or {}).items()
    }
    for k, v in fn_method_overrides.items():
        merged_method_overrides.setdefault(k, set()).update(v)
    merged_extern_exits = base_facts.extern_exit_fns | fn_extern_exits

    rust_env: dict[str, str] = dict(init_env or {})
    rust_type_env: dict[str, str] = {}
    rust_auth_env: dict[str, str] = {
        k: v
        for k, v in (base_facts.fn_authority_families or {}).items()
        if "::" not in k and k in rust_env
    }

    # Inspect function-local nested `fn` defs BEFORE stripping them:
    # 1. Prevent local `fn run_capture()` stubs from inheriting harness.
    # 2. Propagate `bin_capture` / `cmd_capture` / `obs_capture`, untrusted
    #    return types, and transitive `process::exit(0)` via nested `fn`s.
    nested_fn_recs: list[tuple[str, str, str, str, str | None]] = []
    for nm in re.finditer(
        r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(", fn_code_ns[1:]
    ):
        n_name = nm.group(1)
        rp = _find_matching_delimiter_in_code(fn_code_ns, nm.end())
        if rp is None:
            continue
        b_open = fn_code_ns.find("{", rp)
        if b_open == -1:
            continue
        b_close = _find_matching_delimiter_in_code(fn_code_ns, b_open)
        if b_close is None:
            continue
        sig_tail = fn_code_ns[rp + 1 : b_open]
        encl_n = _find_rust_enclosing_delimiters(fn_code_ns, nm.start() + 1)
        n_impl_ty: str | None = None
        for dch, op in encl_n:
            if dch == "{":
                bnd = _find_rust_item_boundary_before(fn_code_ns, op)
                _tr, it_ty, _ta, _gp = _extract_rust_impl_trait_and_target(
                    fn_code_ns[bnd:op]
                )
                if it_ty is not None:
                    n_impl_ty = it_ty
        nested_fn_recs.append(
            (
                n_name,
                sig_tail,
                fn_code[b_open + 1 : b_close],
                fn_code_ns[b_open + 1 : b_close],
                n_impl_ty,
            )
        )

    fn_ret_types_merged = dict(base_facts.fn_return_types or {})
    fn_ret_untrusted_merged = set(base_facts.fn_returns_untrusted)
    q_fn_ret_untrusted_merged = set(base_facts.qualified_fn_returns_untrusted)
    for n_name, sig_tail, _nb_nc, _nb_ns, n_impl_ty in nested_fn_recs:
        if n_impl_ty is None:
            rt = _extract_rust_fn_return_type(sig_tail, None)
            if rt is not None:
                fn_ret_types_merged[n_name] = rt
            if _rust_return_sig_mentions_untrusted_type(
                sig_tail,
                None,
                local_types=merged_types,
                custom_eq_types=merged_custom_eq,
            ):
                fn_ret_untrusted_merged.add(n_name)
                q_fn_ret_untrusted_merged.add(n_name)

    base_merged_facts = _RustFileFacts(
        local_fns=base_facts.local_fns | {r[0] for r in nested_fn_recs},
        local_free_fns=base_facts.local_free_fns
        | {r[0] for r in nested_fn_recs if r[4] is None},
        local_types_or_mods=merged_types,
        use_aliases=merged_aliases,
        capture_fns=base_facts.capture_fns,
        driver_fns=base_facts.driver_fns,
        capture_cmd_fns=base_facts.capture_cmd_fns,
        driver_cmd_fns=base_facts.driver_cmd_fns,
        capture_bin_fns=base_facts.capture_bin_fns,
        driver_bin_fns=base_facts.driver_bin_fns,
        qualified_capture_fns=base_facts.qualified_capture_fns,
        qualified_driver_fns=base_facts.qualified_driver_fns,
        qualified_capture_cmd_fns=base_facts.qualified_capture_cmd_fns,
        qualified_driver_cmd_fns=base_facts.qualified_driver_cmd_fns,
        qualified_capture_bin_fns=base_facts.qualified_capture_bin_fns,
        qualified_driver_bin_fns=base_facts.qualified_driver_bin_fns,
        method_capture_types=base_facts.method_capture_types,
        method_driver_types=base_facts.method_driver_types,
        method_capture_cmd_types=base_facts.method_capture_cmd_types,
        method_driver_cmd_types=base_facts.method_driver_cmd_types,
        method_capture_bin_types=base_facts.method_capture_bin_types,
        method_driver_bin_types=base_facts.method_driver_bin_types,
        method_all_types=base_facts.method_all_types,
        passthrough_cmd_fns=base_facts.passthrough_cmd_fns,
        passthrough_cmd_methods=base_facts.passthrough_cmd_methods,
        fn_return_types=fn_ret_types_merged,
        custom_eq_types=merged_custom_eq,
        extension_overridden_methods=merged_ext_overrides,
        method_override_types={
            k: frozenset(v) for k, v in merged_method_overrides.items()
        },
        fn_local_has_custom_eq_impl=fn_has_custom_eq,
        fn_returns_untrusted=frozenset(fn_ret_untrusted_merged),
        qualified_fn_returns_untrusted=frozenset(q_fn_ret_untrusted_merged),
        method_returns_untrusted_types=base_facts.method_returns_untrusted_types,
        may_exit_success_fns=base_facts.may_exit_success_fns,
        must_exit_success_fns=base_facts.must_exit_success_fns,
        qualified_may_exit_success_fns=base_facts.qualified_may_exit_success_fns,
        qualified_must_exit_success_fns=base_facts.qualified_must_exit_success_fns,
        method_may_exit_types=base_facts.method_may_exit_types,
        drop_may_exit_types=base_facts.drop_may_exit_types,
        extern_exit_fns=merged_extern_exits,
        test_mod_scope=test_mod_scope or base_facts.test_mod_scope,
    )

    local_may_exit: set[str] = set()
    local_must_exit: set[str] = set()
    fn_drop_may_exit: set[str] = set(base_facts.drop_may_exit_types)
    fn_m_may_exit: dict[str, set[str]] = {
        k: set(v) for k, v in (base_facts.method_may_exit_types or {}).items()
    }
    if nested_fn_recs:
        ex_changed = True
        while ex_changed:
            ex_changed = False
            cur_ex_facts = _RustFileFacts(
                **{
                    **base_merged_facts.__dict__,
                    "may_exit_success_fns": base_merged_facts.may_exit_success_fns
                    | frozenset(local_may_exit),
                    "must_exit_success_fns": base_merged_facts.must_exit_success_fns
                    | frozenset(local_must_exit),
                    "method_may_exit_types": {
                        k: frozenset(v) for k, v in fn_m_may_exit.items()
                    },
                    "drop_may_exit_types": frozenset(fn_drop_may_exit),
                }
            )
            for n_name, _sig, nb_nc, nb_ns, n_impl_ty in nested_fn_recs:
                n_may, n_must = _rust_body_exit_classification(
                    nb_nc, nb_ns, facts=cur_ex_facts, owner_ty=n_impl_ty
                )
                if n_may:
                    if n_impl_ty is None and n_name not in local_may_exit:
                        local_may_exit.add(n_name)
                        ex_changed = True
                    elif n_impl_ty is not None:
                        if n_impl_ty not in fn_m_may_exit.get(n_name, set()):
                            fn_m_may_exit.setdefault(n_name, set()).add(n_impl_ty)
                            ex_changed = True
                        if n_name == "drop" and n_impl_ty not in fn_drop_may_exit:
                            fn_drop_may_exit.add(n_impl_ty)
                            ex_changed = True
                if n_must and n_impl_ty is None and n_name not in local_must_exit:
                    local_must_exit.add(n_name)
                    ex_changed = True

    facts = _RustFileFacts(
        **{
            **base_merged_facts.__dict__,
            "may_exit_success_fns": base_merged_facts.may_exit_success_fns
            | frozenset(local_may_exit),
            "must_exit_success_fns": base_merged_facts.must_exit_success_fns
            | frozenset(local_must_exit),
            "method_may_exit_types": {
                k: frozenset(v) for k, v in fn_m_may_exit.items()
            },
            "drop_may_exit_types": frozenset(fn_drop_may_exit),
        }
    )

    for n_name, _sig, n_body_nc, n_body_ns, n_impl_ty in nested_fn_recs:
        if n_impl_ty is not None:
            continue
        n_auth = _rust_helper_eval_authority_family(
            n_body_nc,
            n_body_ns,
            base_auth_env=rust_auth_env,
            base_types=rust_type_env,
            facts=facts,
        )
        if n_auth is not None:
            rust_auth_env[n_name] = n_auth
        n_okind = _rust_helper_eval_statements(
            n_body_nc,
            n_body_ns,
            base_env=rust_env,
            base_types=rust_type_env,
            facts=facts,
            mode="obs",
        )
        if n_okind is not None:
            rust_env[n_name] = n_okind
            continue
        n_ckind = _rust_helper_eval_statements(
            n_body_nc,
            n_body_ns,
            base_env=rust_env,
            base_types=rust_type_env,
            facts=facts,
            mode="cmd",
        )
        if n_ckind is not None:
            rust_env[n_name] = n_ckind
            continue
        n_bkind = _rust_helper_eval_statements(
            n_body_nc,
            n_body_ns,
            base_env=rust_env,
            base_types=rust_type_env,
            facts=facts,
            mode="bin",
        )
        rust_env[n_name] = n_bkind if n_bkind is not None else "const"

    local_may_exit_f = frozenset(local_may_exit)
    local_must_exit_f = frozenset(local_must_exit)
    live_code, live_ns = _strip_unreachable_rust_test_code(fn_code, fn_code_ns)
    closure_spans = _find_rust_closure_body_spans(live_ns)

    def _in_closure(pos: int) -> bool:
        return any(cs <= pos < ce for cs, ce in closure_spans)

    def _collect_in_span(
        span_start: int,
        span_end: int,
        cur_env: dict[str, str],
        cur_types: dict[str, str],
        cur_taint: dict[str, str],
        cur_cstrs: dict[str, str],
        cur_exprs: dict[str, str],
        out: list[_AssertionItem],
        cur_exprs_nc: dict[str, str] | None = None,
        cur_auth: dict[str, str] | None = None,
    ) -> list[object]:
        seg_code = live_code[span_start:span_end]
        seg_ns = live_ns[span_start:span_end]
        snapshot = dict(cur_env)
        type_snap = dict(cur_types)
        taint_snap = dict(cur_taint)
        cstr_snap = dict(cur_cstrs)
        expr_snap = dict(cur_exprs)
        expr_nc_snap = dict(cur_exprs_nc) if cur_exprs_nc is not None else None
        auth_snap = dict(cur_auth) if cur_auth is not None else None
        ev_nodes: list[tuple[int, object]] = []
        for m in RUST_ASSERT_START_RE.finditer(seg_ns):
            abs_pos = span_start + m.start()
            if _in_closure(abs_pos):
                continue
            if not _is_std_assert_qualifier(live_ns[:abs_pos]):
                continue
            open_idx = m.end() - 1
            close_idx = _find_matching_delimiter_in_code(seg_ns, open_idx)
            end_idx = close_idx + 1 if close_idx is not None else len(seg_code)
            full_span = seg_code[m.start() : end_idx]
            inner = (
                seg_code[open_idx + 1 : close_idx]
                if close_idx is not None
                else seg_code[open_idx + 1 :]
            )
            inner_ns = (
                seg_ns[open_idx + 1 : close_idx]
                if close_idx is not None
                else seg_ns[open_idx + 1 :]
            )
            args = _split_top_level_commas(inner, keep_literal_only=True)
            args_ns = _split_top_level_commas(inner_ns, keep_literal_only=True)
            macro_head = seg_ns[m.start() : open_idx]
            is_plain_assert = (
                re.search(r"\bassert_(?:eq|ne|matches)\b", macro_head) is None
            )
            if not is_plain_assert:
                tested = ", ".join(args[:2])
                tested_ns = ", ".join(args_ns[:2])
                tested_args = tuple(args[:2])
            else:
                tested = args[0] if args else inner
                tested_ns = args_ns[0] if args_ns else inner_ns
                tested_args = (tested,)
            okind = _rust_expr_origin_kind(
                tested,
                tested_ns,
                rust_env=snapshot,
                rust_facts=facts,
                rust_type_env=type_snap,
            )
            is_obs = okind in RUST_OBS_STATES
            item = _AssertionItem(
                full_span=full_span,
                tested_expr=tested,
                is_observed=is_obs,
                origin_kind=okind,
                tested_args=tested_args,
                rust_env=snapshot,
                rust_type_env=type_snap,
                pure_rust_fns=pure_rust_fns,
                rust_facts=facts,
                rust_str_taint=taint_snap,
                rust_const_strs=cstr_snap,
                rust_exprs=expr_snap,
                rust_exprs_nc=expr_nc_snap,
                rust_auth_env=auth_snap,
            )
            out.append(item)
            is_cond = _rust_pos_is_conditional_in_span(seg_ns, m.start())
            if (
                is_plain_assert
                and not is_cond
                and _eval_rust_static_bool_cond(tested_ns.strip()) is False
            ):
                ev_nodes.append((m.start(), _CfgExit(is_success=False)))
            else:
                node: object = _CfgItem(item)
                if is_cond:
                    node = _CfgBranch((node, _CfgSeq(())))
                ev_nodes.append((m.start(), node))

        for m in RUST_ERR_CALL_RE.finditer(seg_ns):
            abs_pos = span_start + m.start()
            if _in_closure(abs_pos):
                continue
            close_idx = _find_matching_delimiter_in_code(seg_ns, m.end() - 1)
            end_idx = close_idx + 1 if close_idx is not None else len(seg_code)
            start_idx = m.start()
            rp_d = 0
            rb_d = 0
            rbr_d = 0
            pos = m.start() - 1
            while pos >= 0:
                ch = seg_ns[pos]
                if ch == ")":
                    rp_d += 1
                elif ch == "(":
                    if rp_d == 0:
                        start_idx = pos + 1
                        break
                    rp_d -= 1
                elif ch == "]":
                    rb_d += 1
                elif ch == "[":
                    if rb_d == 0:
                        start_idx = pos + 1
                        break
                    rb_d -= 1
                elif ch == "}":
                    rbr_d += 1
                elif ch == "{":
                    if rbr_d == 0:
                        start_idx = pos + 1
                        break
                    rbr_d -= 1
                elif ch == ">" and pos > 0 and seg_ns[pos - 1] == "=":
                    start_idx = pos + 1
                    break
                elif rp_d == 0 and rb_d == 0 and rbr_d == 0 and ch in ";,=":
                    start_idx = pos + 1
                    break
                pos -= 1
            else:
                start_idx = 0
            recv_nc = seg_code[start_idx : m.start()]
            recv_ns = seg_ns[start_idx : m.start()]
            method_name = (
                "expect_err" if "expect_err" in m.group(0) else "unwrap_err"
            )
            # Strip `.expect_err(msg)` panic message and receiver literals so an
            # uninspected panic string or receiver comment cannot satisfy tag or
            # `unsupported` assertions; keep `recv_nc` only for witness slicing.
            err_token = f".{method_name}()"
            okind = _rust_expr_origin_kind(
                recv_nc,
                recv_ns,
                rust_env=snapshot,
                rust_facts=facts,
                rust_type_env=type_snap,
            )
            is_obs = okind in RUST_OBS_STATES
            item = _AssertionItem(
                full_span=err_token,
                tested_expr=err_token,
                is_observed=is_obs,
                origin_kind=okind,
                tested_args=(err_token,),
                rust_env=snapshot,
                rust_type_env=type_snap,
                pure_rust_fns=pure_rust_fns,
                rust_facts=facts,
                rust_str_taint=taint_snap,
                rust_const_strs=cstr_snap,
                rust_exprs=expr_snap,
                rust_exprs_nc=expr_nc_snap,
                rust_auth_env=auth_snap,
                is_err_unwrap=True,
                err_unwrap_recv=recv_nc.strip(),
            )
            out.append(item)
            node = _CfgItem(item)
            if _rust_pos_is_conditional_in_span(seg_ns, start_idx):
                node = _CfgBranch((node, _CfgSeq(())))
            ev_nodes.append((start_idx, node))

        # Emit nested non-Err `return` / `break` / `continue` at their exact
        # source offsets so an inline early exit precedes later assertions in
        # the same statement (e.g. `let _ = (if c { return; }, assert!(...));`).
        for rm in re.finditer(r"\b(return|break|continue)\b", seg_ns):
            if _in_closure(span_start + rm.start()):
                continue
            if not seg_ns[: rm.start()].strip():
                continue
            kw = rm.group(1)
            if kw == "return":
                tail = seg_ns[rm.end() :].lstrip()
                if re.match(
                    r"^(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*Result\s*::\s*)?Err\s*\(",
                    tail,
                ):
                    continue
                ev_nodes.append(
                    (
                        rm.start(),
                        _CfgBranch((_CfgExit(is_success=True), _CfgSeq(()))),
                    )
                )
            else:
                lbl_m = re.match(
                    r"^\s*('[A-Za-z_][A-Za-z0-9_]*)", seg_ns[rm.end() :]
                )
                j_lbl = lbl_m.group(1) if lbl_m is not None else None
                ev_nodes.append(
                    (
                        rm.start(),
                        _CfgBranch((_CfgLoopJump(kw, label=j_lbl), _CfgSeq(()))),
                    )
                )

        ev_nodes.sort(key=lambda pair: pair[0])
        return [nd for _p, nd in ev_nodes]

    def _record_str_mutations(
        code_seg: str,
        ns_seg: str,
        env_in: dict[str, str],
        types_in: dict[str, str],
        taint_io: dict[str, str],
        cstrs_io: dict[str, str],
    ) -> None:
        def _append_var_taint(vname: str, extra: str) -> None:
            if not extra:
                return
            prev_const = cstrs_io.pop(vname, "")
            prev_taint = taint_io.get(vname, "")
            taint_io[vname] = f"{prev_taint}{prev_const}{extra}"

        for mm in re.finditer(
            r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\.\s*(push_str|push|insert_str|replace_range|extend)\s*\(",
            ns_seg,
        ):
            var_name = mm.group(1)
            mname = mm.group(2)
            open_p = mm.end() - 1
            close_p = _find_matching_delimiter_in_code(ns_seg, open_p)
            if close_p is None:
                continue
            args_nc = _split_top_level_commas(
                code_seg[open_p + 1 : close_p], keep_literal_only=True
            )
            arg_target: str | None = None
            if mname in ("push_str", "push", "extend") and args_nc:
                arg_target = args_nc[0]
            elif mname in ("insert_str", "replace_range") and len(args_nc) >= 2:
                arg_target = args_nc[1]
            if arg_target is not None:
                extra = _rust_extract_unobserved_str_parts(
                    arg_target,
                    rust_env=env_in,
                    str_taint=taint_io,
                    const_strs=cstrs_io,
                    facts=facts,
                    type_env=types_in,
                )
                _append_var_taint(var_name, extra)

        for wm in re.finditer(
            r"(?:(?:::\s*)?(?:std|alloc|core)\s*::\s*)?(write(?:ln)?)\s*!\s*([(\[{])",
            ns_seg,
        ):
            open_d = wm.end() - 1
            close_d = _find_matching_delimiter_in_code(ns_seg, open_d)
            if close_d is None:
                continue
            w_args = _split_top_level_commas(
                code_seg[open_d + 1 : close_d], keep_literal_only=True
            )
            if not w_args:
                continue
            dst_s = _rust_strip_outer_parens(w_args[0])
            while dst_s.startswith("&"):
                dst_s = dst_s[1:].lstrip()
                if dst_s.startswith("mut") and (
                    len(dst_s) == 3 or not (dst_s[3].isalnum() or dst_s[3] == "_")
                ):
                    dst_s = dst_s[3:].lstrip()
                dst_s = _rust_strip_outer_parens(dst_s)
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", dst_s):
                continue
            rest_nc = ", ".join(w_args[1:])
            extra = _rust_format_parts(
                rest_nc,
                resolve_expr_fn=lambda sub: _rust_extract_unobserved_str_parts(
                    sub,
                    rust_env=env_in,
                    str_taint=taint_io,
                    const_strs=cstrs_io,
                    facts=facts,
                    type_env=types_in,
                ),
                resolve_ident_fn=lambda ident: _rust_extract_unobserved_str_parts(
                    ident,
                    rust_env=env_in,
                    str_taint=taint_io,
                    const_strs=cstrs_io,
                    facts=facts,
                    type_env=types_in,
                ),
            )
            if wm.group(1) == "writeln":
                extra += "\n"
            _append_var_taint(dst_s, extra)

        for ws in re.finditer(
            r"\b(?:write_str|write_all|write)\s*\(",
            ns_seg,
        ):
            open_p = ws.end() - 1
            close_p = _find_matching_delimiter_in_code(ns_seg, open_p)
            if close_p is None:
                continue
            w_args = _split_top_level_commas(
                code_seg[open_p + 1 : close_p], keep_literal_only=True
            )
            if len(w_args) >= 2:
                dst_m = re.match(
                    r"^(?:&\s*mut\s+)?([A-Za-z_][A-Za-z0-9_]*)$",
                    _rust_strip_outer_parens(w_args[0]),
                )
                if dst_m is not None:
                    extra = _rust_extract_unobserved_str_parts(
                        w_args[1],
                        rust_env=env_in,
                        str_taint=taint_io,
                        const_strs=cstrs_io,
                        facts=facts,
                        type_env=types_in,
                    )
                    _append_var_taint(dst_m.group(1), extra)

    def _apply_stmt_effect(
        stmt_code: str,
        stmt_ns: str,
        cur_env: dict[str, str],
        cur_types: dict[str, str],
        cur_exit_vars: set[str],
        cur_taint: dict[str, str],
        cur_cstrs: dict[str, str],
        cur_exprs: dict[str, str] | None = None,
        cur_exprs_nc: dict[str, str] | None = None,
        cur_auth: dict[str, str] | None = None,
    ) -> None:
        plus_eq_m = re.match(
            r"^\s*\**\s*([A-Za-z_][A-Za-z0-9_]*)\s*\+=", stmt_ns
        )
        if plus_eq_m is not None:
            vname = plus_eq_m.group(1)
            if cur_exprs is not None:
                cur_exprs.pop(vname, None)
            if cur_exprs_nc is not None:
                cur_exprs_nc.pop(vname, None)
            rhs_nc = stmt_code[plus_eq_m.end() :]
            rhs_ns = stmt_ns[plus_eq_m.end() :]
            extra = _rust_extract_unobserved_str_parts(
                rhs_nc,
                rhs_ns,
                rust_env=cur_env,
                str_taint=cur_taint,
                const_strs=cur_cstrs,
                facts=facts,
                type_env=cur_types,
            )
            if extra:
                prev_const = cur_cstrs.pop(vname, "")
                prev_taint = cur_taint.get(vname, "")
                cur_taint[vname] = f"{prev_taint}{prev_const}{extra}"
            _record_str_mutations(
                rhs_nc, rhs_ns, cur_env, cur_types, cur_taint, cur_cstrs
            )
            _rust_invalidate_mutated_bin_vars(stmt_ns, cur_env)
            return

        eq_pos = _find_rust_top_level_equal(stmt_ns)
        if eq_pos is not None:
            lhs = stmt_ns[:eq_pos]
            rhs_nc = stmt_code[eq_pos + 1 :]
            rhs_ns = stmt_ns[eq_pos + 1 :]
            okind = _rust_expr_origin_kind(
                rhs_nc,
                rhs_ns,
                rust_env=cur_env,
                rust_facts=facts,
                rust_type_env=cur_types,
            )
            if okind is not None:
                status = okind
            else:
                ckind = _rust_expr_cmd_kind(
                    rhs_nc,
                    rhs_ns,
                    rust_env=cur_env,
                    rust_type_env=cur_types,
                    rust_facts=facts,
                )
                if ckind is not None:
                    status = ckind
                else:
                    bkind = _rust_expr_bin_kind(
                        rhs_nc,
                        rhs_ns,
                        rust_env=cur_env,
                        rust_type_env=cur_types,
                        rust_facts=facts,
                    )
                    status = bkind if bkind is not None else "const"
            inferred_ty = _extract_rust_lhs_type_annotation(
                lhs
            ) or _infer_rust_expr_type(
                rhs_nc, rhs_ns, type_env=cur_types, facts=facts
            )
            # Block observation taint from flowing through custom-eq / untrusted
            # wrapper types (e.g. `let w = Evil(&output);`).
            if status in RUST_OBS_STATES and (
                (
                    inferred_ty is not None
                    and (
                        inferred_ty in facts.custom_eq_types
                        or inferred_ty in ("__opaque_impl__", "__opaque_dyn__")
                    )
                )
                or not _rust_expr_is_trusted_wrapper_or_capture(
                    rhs_nc,
                    rhs_ns,
                    rust_env=cur_env,
                    type_env=cur_types,
                    facts=facts,
                )
            ):
                status = "const"
            rhs_is_exit_cb = _rust_rhs_creates_exit_callable(
                rhs_ns,
                facts=facts,
                local_may_exit_fns=local_may_exit_f,
                cur_exit_vars=frozenset(cur_exit_vars),
                type_env=cur_types,
            )
            rhs_tup = _split_rust_tuple_elems(rhs_nc.strip().rstrip(";").strip())
            rhs_unobs = _rust_extract_unobserved_str_parts(
                rhs_nc,
                rhs_ns,
                rust_env=cur_env,
                str_taint=cur_taint,
                const_strs=cur_cstrs,
                facts=facts,
                type_env=cur_types,
            )
            rhs_static = _rust_extract_static_const_str(rhs_nc, cur_cstrs)
            idents = _extract_rust_pattern_idents(lhs)
            rhs_auth = (
                _rust_expr_authority_family(
                    rhs_nc,
                    rhs_ns,
                    rust_auth_env=cur_auth,
                    rust_facts=facts,
                    rust_type_env=cur_types,
                    rust_exprs_nc=cur_exprs_nc,
                )
                if cur_auth is not None
                else None
            )
            for idx_id, ident in enumerate(idents):
                if rhs_tup is not None and len(idents) == len(rhs_tup):
                    el_unobs = _rust_extract_unobserved_str_parts(
                        rhs_tup[idx_id],
                        rust_env=cur_env,
                        str_taint=cur_taint,
                        const_strs=cur_cstrs,
                        facts=facts,
                        type_env=cur_types,
                    )
                    el_static = _rust_extract_static_const_str(
                        rhs_tup[idx_id], cur_cstrs
                    )
                else:
                    el_unobs = rhs_unobs
                    el_static = rhs_static
                cur_env[ident] = status
                if cur_auth is not None:
                    if rhs_auth is not None and status != "const":
                        cur_auth[ident] = rhs_auth
                    else:
                        cur_auth.pop(ident, None)
                if cur_exprs is not None:
                    if len(idents) == 1:
                        cur_exprs[ident] = rhs_ns.strip().rstrip(";").strip()
                    else:
                        cur_exprs.pop(ident, None)
                if cur_exprs_nc is not None:
                    if len(idents) == 1:
                        cur_exprs_nc[ident] = rhs_nc.strip().rstrip(";").strip()
                    else:
                        cur_exprs_nc.pop(ident, None)
                if len(idents) == 1 and inferred_ty is not None:
                    cur_types[ident] = inferred_ty
                else:
                    cur_types.pop(ident, None)
                if rhs_is_exit_cb:
                    cur_exit_vars.add(ident)
                else:
                    cur_exit_vars.discard(ident)
                if status in RUST_OBS_STATES:
                    cur_cstrs.pop(ident, None)
                    if el_unobs:
                        cur_taint[ident] = el_unobs
                    else:
                        cur_taint.pop(ident, None)
                else:
                    if el_static is not None:
                        cur_cstrs[ident] = el_static
                        cur_taint.pop(ident, None)
                    elif el_unobs:
                        cur_taint[ident] = el_unobs
                        cur_cstrs.pop(ident, None)
                    else:
                        cur_cstrs.pop(ident, None)
                        cur_taint.pop(ident, None)
            _record_str_mutations(
                rhs_nc, rhs_ns, cur_env, cur_types, cur_taint, cur_cstrs
            )
            _rust_invalidate_mutated_bin_vars(rhs_ns, cur_env)
            return
        _record_str_mutations(
            stmt_code, stmt_ns, cur_env, cur_types, cur_taint, cur_cstrs
        )
        _rust_invalidate_mutated_bin_vars(stmt_ns, cur_env)
        # Out-parameter mutation: `fill_into(&mut buf);` when call is a driver.
        okind = _rust_expr_origin_kind(
            stmt_code,
            stmt_ns,
            rust_env=cur_env,
            rust_facts=facts,
            rust_type_env=cur_types,
        )
        if okind in RUST_OBS_STATES:
            out_auth = (
                _rust_expr_authority_family(
                    stmt_code,
                    stmt_ns,
                    rust_auth_env=cur_auth,
                    rust_facts=facts,
                    rust_type_env=cur_types,
                    rust_exprs_nc=cur_exprs_nc,
                )
                if cur_auth is not None
                else None
            )
            for mut_m in re.finditer(
                r"&\s*mut\s+([A-Za-z_][A-Za-z0-9_]*)\b", stmt_ns
            ):
                cur_env[mut_m.group(1)] = okind
                if cur_exprs is not None:
                    cur_exprs.pop(mut_m.group(1), None)
                if cur_exprs_nc is not None:
                    cur_exprs_nc.pop(mut_m.group(1), None)
                if cur_auth is not None:
                    if out_auth is not None:
                        cur_auth[mut_m.group(1)] = out_auth
                    else:
                        cur_auth.pop(mut_m.group(1), None)

    def _meet_status(vals: list[str | None]) -> str | None:
        if all(v == "obs_capture" for v in vals):
            return "obs_capture"
        if all(v in RUST_OBS_STATES for v in vals):
            return "obs_driver"
        if all(v == "cmd_capture" for v in vals):
            return "cmd_capture"
        if all(v in ("cmd_capture", "cmd_driver") for v in vals):
            return "cmd_driver"
        if all(v == "bin_capture" for v in vals):
            return "bin_capture"
        if all(v in ("bin_capture", "bin_driver") for v in vals):
            return "bin_driver"
        if any(v == "const" for v in vals):
            return "const"
        return None

    def _meet_envs(
        pre: dict[str, str], branch_envs: list[dict[str, str]]
    ) -> dict[str, str]:
        merged = dict(pre)
        for k in list(merged.keys()):
            ms = _meet_status([b.get(k) for b in branch_envs])
            if ms is not None:
                merged[k] = ms
        for k in set().union(*(b.keys() for b in branch_envs)):
            if k not in merged:
                ms = _meet_status([b.get(k) for b in branch_envs])
                if ms in RUST_OBS_STATES or ms in (
                    "cmd_capture",
                    "cmd_driver",
                    "bin_capture",
                    "bin_driver",
                ):
                    merged[k] = ms
        return merged

    def _meet_types(
        pre: dict[str, str], branch_types: list[dict[str, str]]
    ) -> dict[str, str]:
        merged: dict[str, str] = {}
        all_keys = set(pre.keys()) | set().union(
            *(b.keys() for b in branch_types)
        )
        for k in all_keys:
            vals = [b.get(k) for b in branch_types]
            if vals and vals[0] is not None and all(v == vals[0] for v in vals):
                merged[k] = vals[0]
        return merged

    def _meet_str_dicts(
        branch_taints: list[dict[str, str]],
        branch_cstrs: list[dict[str, str]],
    ) -> tuple[dict[str, str], dict[str, str]]:
        merged_cstrs: dict[str, str] = {}
        merged_taints: dict[str, str] = {}
        all_ckeys = set().union(*(c.keys() for c in branch_cstrs)) if branch_cstrs else set()
        for k in all_ckeys:
            vals = [c.get(k) for c in branch_cstrs]
            if vals and vals[0] is not None and all(v == vals[0] for v in vals):
                merged_cstrs[k] = vals[0]
        all_tkeys = (set().union(*(t.keys() for t in branch_taints)) if branch_taints else set()) | (
            all_ckeys - set(merged_cstrs.keys())
        )
        for k in all_tkeys:
            seen: list[str] = []
            for t_d, c_d in zip(branch_taints, branch_cstrs):
                for part in (t_d.get(k, ""), c_d.get(k, "") if k not in merged_cstrs else ""):
                    if part and part not in seen:
                        seen.append(part)
            if seen:
                merged_taints[k] = "\n".join(seen)
        return merged_taints, merged_cstrs

    def _find_rhs_ctrl_span(s_start: int, s_end: int) -> tuple[int, int] | None:
        """If stmt is `let ... = <if/match/loop/while/for/unsafe/{ ... };`, return RHS span."""
        stmt_ns = live_ns[s_start:s_end]
        eq_pos = _find_rust_top_level_equal(stmt_ns)
        if eq_pos is not None:
            rhs_s = s_start + eq_pos + 1
            rhs_e = s_end
        else:
            rhs_s = s_start
            rhs_e = s_end
        while rhs_s < rhs_e and live_ns[rhs_s].isspace():
            rhs_s += 1
        while rhs_e > rhs_s and live_ns[rhs_e - 1] in " \t\r\n;":
            rhs_e -= 1
        while rhs_s < rhs_e and live_ns[rhs_s] == "(" and live_ns[rhs_e - 1] == ")":
            if _find_matching_delimiter_in_code(live_ns, rhs_s) != rhs_e - 1:
                break
            rhs_s += 1
            rhs_e -= 1
            while rhs_s < rhs_e and live_ns[rhs_s].isspace():
                rhs_s += 1
            while rhs_e > rhs_s and live_ns[rhs_e - 1].isspace():
                rhs_e -= 1
        rhs_s += _skip_leading_rust_attrs(live_ns[rhs_s:rhs_e])
        if rhs_s >= rhs_e:
            return None
        if rhs_s == s_start and rhs_e == s_end:
            return None
        sub = live_ns[rhs_s:rhs_e]
        if re.match(
            r"^(?:'[A-Za-z_][A-Za-z0-9_]*\s*:\s*)?(?:if|match|while|for|loop|unsafe)\b",
            sub,
        ) or re.match(r"^(?:'[A-Za-z_][A-Za-z0-9_]*\s*:\s*)?\{", sub):
            return rhs_s, rhs_e
        return None

    def _eval_rust_value_expr(
        expr_nc: str,
        expr_ns: str,
        env_in: dict[str, str],
        types_in: dict[str, str],
    ) -> tuple[str, str | None]:
        """Compute `(status, inferred_ty)` for a Rust value expression."""
        e_nc = expr_nc.strip().rstrip(";").strip()
        e_ns = expr_ns.strip().rstrip(";").strip()
        if not e_ns:
            return "const", None
        okind = _rust_expr_origin_kind(
            e_nc,
            e_ns,
            rust_env=env_in,
            rust_facts=facts,
            rust_type_env=types_in,
        )
        if okind is not None:
            st = okind
        else:
            ckind = _rust_expr_cmd_kind(
                e_nc,
                e_ns,
                rust_env=env_in,
                rust_type_env=types_in,
                rust_facts=facts,
            )
            if ckind is not None:
                st = ckind
            else:
                bkind = _rust_expr_bin_kind(
                    e_nc,
                    e_ns,
                    rust_env=env_in,
                    rust_type_env=types_in,
                    rust_facts=facts,
                )
                st = bkind if bkind is not None else "const"
        inferred_ty = _infer_rust_expr_type(
            e_nc, e_ns, type_env=types_in, facts=facts
        )
        if st in RUST_OBS_STATES and (
            (
                inferred_ty is not None
                and (
                    inferred_ty in facts.custom_eq_types
                    or inferred_ty in ("__opaque_impl__", "__opaque_dyn__")
                )
            )
            or not _rust_expr_is_trusted_wrapper_or_capture(
                e_nc,
                e_ns,
                rust_env=env_in,
                type_env=types_in,
                facts=facts,
            )
        ):
            st = "const"
        return st, inferred_ty

    def _eval_rust_ctrl_rhs_status(
        ctrl_s: int,
        ctrl_e: int,
        env_in: dict[str, str],
        types_in: dict[str, str],
        taint_in: dict[str, str] | None = None,
        cstrs_in: dict[str, str] | None = None,
        _depth: int = 0,
    ) -> tuple[str, str | None, str]:
        """Structurally evaluate a compound RHS (`{...}`, `if`, `match`)."""
        taint_base = dict(taint_in or {})
        cstrs_base = dict(cstrs_in or {})
        if _depth > 8:
            return "const", None, ""
        rs = ctrl_s
        re_end = ctrl_e
        while rs < re_end and live_ns[rs].isspace():
            rs += 1
        while re_end > rs and live_ns[re_end - 1] in " \t\r\n;":
            re_end -= 1
        while rs < re_end and live_ns[rs] == "(" and live_ns[re_end - 1] == ")":
            if _find_matching_delimiter_in_code(live_ns, rs) != re_end - 1:
                break
            rs += 1
            re_end -= 1
            while rs < re_end and live_ns[rs].isspace():
                rs += 1
            while re_end > rs and live_ns[re_end - 1].isspace():
                re_end -= 1
        rs += _skip_leading_rust_attrs(live_ns[rs:re_end])
        if rs >= re_end:
            return "const", None, ""

        # Strip optional leading lifetime label `'blk: ...`.
        lbl_m = re.match(r"^'[A-Za-z_][A-Za-z0-9_]*\s*:\s*", live_ns[rs:re_end])
        has_label = lbl_m is not None
        if lbl_m is not None:
            rs += lbl_m.end()
        sub_ns = live_ns[rs:re_end]

        # 1. Bare or `unsafe` block `{ ... }` (optionally with `.chain()`).
        blk_m = re.match(r"^(?:unsafe\s+)?\{", sub_ns)
        if blk_m is not None:
            b_open = rs + blk_m.end() - 1
            b_close = _find_matching_delimiter_in_code(live_ns, b_open)
            if b_close is None or b_close >= re_end:
                return "const", None, ""
            if has_label and re.search(r"\bbreak\b", live_ns[b_open + 1 : b_close]):
                return "const", None, ""
            b_env = dict(env_in)
            b_types = dict(types_in)
            b_taint = dict(taint_base)
            b_cstrs = dict(cstrs_base)
            b_exits: set[str] = set()
            b_segs = _split_rust_top_level_segments(live_ns, b_open + 1, b_close)
            if not b_segs:
                return "const", None, ""
            for s_idx, (sk, ss, se, _sb) in enumerate(b_segs):
                is_last = s_idx == len(b_segs) - 1
                seg_strip = live_ns[ss:se].strip()
                if is_last and not seg_strip.endswith(";"):
                    if sk == "block":
                        val_st, val_ty, val_taint = _eval_rust_ctrl_rhs_status(
                            ss, se, b_env, b_types, b_taint, b_cstrs, _depth + 1
                        )
                    else:
                        nested = _find_rhs_ctrl_span(ss, se)
                        if nested is not None and _find_rust_top_level_equal(
                            live_ns[ss:se]
                        ) is None:
                            val_st, val_ty, val_taint = _eval_rust_ctrl_rhs_status(
                                nested[0],
                                nested[1],
                                b_env,
                                b_types,
                                b_taint,
                                b_cstrs,
                                _depth + 1,
                            )
                        else:
                            val_st, val_ty = _eval_rust_value_expr(
                                live_code[ss:se], live_ns[ss:se], b_env, b_types
                            )
                            val_taint = _rust_extract_unobserved_str_parts(
                                live_code[ss:se],
                                live_ns[ss:se],
                                rust_env=b_env,
                                str_taint=b_taint,
                                const_strs=b_cstrs,
                                facts=facts,
                                type_env=b_types,
                            )
                    tail_nc = live_code[b_close + 1 : re_end].strip()
                    tail_ns = live_ns[b_close + 1 : re_end].strip()
                    if tail_ns:
                        ch_env = dict(b_env)
                        ch_types = dict(b_types)
                        ch_taint = dict(b_taint)
                        ch_env["__anneal_ctrl_val"] = val_st
                        if val_ty is not None:
                            ch_types["__anneal_ctrl_val"] = val_ty
                        if val_taint:
                            ch_taint["__anneal_ctrl_val"] = val_taint
                        f_st, f_ty = _eval_rust_value_expr(
                            "__anneal_ctrl_val" + tail_nc,
                            "__anneal_ctrl_val" + tail_ns,
                            ch_env,
                            ch_types,
                        )
                        f_taint = _rust_extract_unobserved_str_parts(
                            "__anneal_ctrl_val" + tail_nc,
                            "__anneal_ctrl_val" + tail_ns,
                            rust_env=ch_env,
                            str_taint=ch_taint,
                            const_strs=b_cstrs,
                            facts=facts,
                            type_env=ch_types,
                        )
                        return f_st, f_ty, f_taint
                    return val_st, val_ty, val_taint
                if sk == "stmt":
                    inner_ctrl = _find_rhs_ctrl_span(ss, se)
                    if inner_ctrl is not None:
                        eq_i = _find_rust_top_level_equal(live_ns[ss:se])
                        if eq_i is not None:
                            c_st, c_ty, c_taint = _eval_rust_ctrl_rhs_status(
                                inner_ctrl[0],
                                inner_ctrl[1],
                                b_env,
                                b_types,
                                b_taint,
                                b_cstrs,
                                _depth + 1,
                            )
                            lhs_i = live_ns[ss : ss + eq_i]
                            ids_i = _extract_rust_pattern_idents(lhs_i)
                            lhs_ty = _extract_rust_lhs_type_annotation(lhs_i) or c_ty
                            for ident in ids_i:
                                b_env[ident] = c_st
                                if len(ids_i) == 1 and lhs_ty is not None:
                                    b_types[ident] = lhs_ty
                                else:
                                    b_types.pop(ident, None)
                                if c_taint:
                                    b_taint[ident] = c_taint
                                    b_cstrs.pop(ident, None)
                                else:
                                    b_taint.pop(ident, None)
                    else:
                        _apply_stmt_effect(
                            live_code[ss:se],
                            live_ns[ss:se],
                            b_env,
                            b_types,
                            b_exits,
                            b_taint,
                            b_cstrs,
                        )
                else:
                    _rust_invalidate_mutated_bin_vars(live_ns[ss:se], b_env)
            return "const", None, ""

        # 2. `if ... { ... } else [if ...] { ... }`: meet across all branches.
        if re.match(r"^if\b", sub_ns):
            if_segs = _split_rust_top_level_segments(live_ns, rs, re_end)
            branch_sts: list[str | None] = []
            branch_taints: list[str] = []
            saw_else = False
            last_end = rs
            for sk, ss, se, sbr in if_segs:
                if sk != "block" or sbr is None:
                    return "const", None, ""
                chdr = live_ns[ss + _skip_leading_rust_attrs(live_ns[ss:sbr]) : sbr]
                if branch_sts and not re.match(r"^\s*else\b", chdr):
                    return "const", None, ""
                if re.match(r"^\s*else\s*$", chdr):
                    saw_else = True
                br_st, _, br_taint = _eval_rust_ctrl_rhs_status(
                    sbr, se, env_in, types_in, taint_base, cstrs_base, _depth + 1
                )
                branch_sts.append(br_st)
                if br_taint and br_taint not in branch_taints:
                    branch_taints.append(br_taint)
                last_end = se
            if not saw_else or not branch_sts:
                return "const", None, ""
            met = _meet_status(branch_sts) or "const"
            met_taint = "\n".join(branch_taints)
            tail_nc = live_code[last_end:re_end].strip()
            tail_ns = live_ns[last_end:re_end].strip()
            if tail_ns:
                ch_env = dict(env_in)
                ch_taint = dict(taint_base)
                ch_env["__anneal_ctrl_val"] = met
                if met_taint:
                    ch_taint["__anneal_ctrl_val"] = met_taint
                f_st, f_ty = _eval_rust_value_expr(
                    "__anneal_ctrl_val" + tail_nc,
                    "__anneal_ctrl_val" + tail_ns,
                    ch_env,
                    types_in,
                )
                f_taint = _rust_extract_unobserved_str_parts(
                    "__anneal_ctrl_val" + tail_nc,
                    "__anneal_ctrl_val" + tail_ns,
                    rust_env=ch_env,
                    str_taint=ch_taint,
                    const_strs=cstrs_base,
                    facts=facts,
                    type_env=types_in,
                )
                return f_st, f_ty, f_taint
            return met, None, met_taint

        # 3. `match scrut { pat => arm, ... }`: meet across non-diverging arms.
        if re.match(r"^match\b", sub_ns):
            m_segs = _split_rust_top_level_segments(live_ns, rs, re_end)
            if not m_segs or m_segs[0][0] != "block" or m_segs[0][3] is None:
                return "const", None, ""
            _, _ms, me, mbr = m_segs[0]
            arm_spans = _split_rust_match_arm_spans(live_ns, mbr + 1, me - 1)
            arm_exit_re = re.compile(
                r"return\b"
                r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
                r"process\s*::\s*(?:exit|abort)\s*\("
                r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
                r"(?:panic|unreachable|todo|unimplemented)\s*!\s*[(\[{]"
            )
            arm_sts: list[str | None] = []
            arm_taints: list[str] = []
            for _ps, _pe, a_s, a_e in arm_spans:
                a_slice = live_ns[a_s:a_e].strip()
                if _rust_expr_diverges(a_slice, arm_exit_re):
                    continue
                if a_slice.startswith("{") or re.match(
                    r"^(?:if|match|unsafe)\b", a_slice
                ):
                    ast_st, _, ast_taint = _eval_rust_ctrl_rhs_status(
                        a_s, a_e, env_in, types_in, taint_base, cstrs_base, _depth + 1
                    )
                else:
                    ast_st, _ = _eval_rust_value_expr(
                        live_code[a_s:a_e], live_ns[a_s:a_e], env_in, types_in
                    )
                    ast_taint = _rust_extract_unobserved_str_parts(
                        live_code[a_s:a_e],
                        live_ns[a_s:a_e],
                        rust_env=env_in,
                        str_taint=taint_base,
                        const_strs=cstrs_base,
                        facts=facts,
                        type_env=types_in,
                    )
                arm_sts.append(ast_st)
                if ast_taint and ast_taint not in arm_taints:
                    arm_taints.append(ast_taint)
            if not arm_sts:
                return "const", None, ""
            met = _meet_status(arm_sts) or "const"
            met_taint = "\n".join(arm_taints)
            tail_nc = live_code[me:re_end].strip()
            tail_ns = live_ns[me:re_end].strip()
            if tail_ns:
                ch_env = dict(env_in)
                ch_taint = dict(taint_base)
                ch_env["__anneal_ctrl_val"] = met
                if met_taint:
                    ch_taint["__anneal_ctrl_val"] = met_taint
                f_st, f_ty = _eval_rust_value_expr(
                    "__anneal_ctrl_val" + tail_nc,
                    "__anneal_ctrl_val" + tail_ns,
                    ch_env,
                    types_in,
                )
                f_taint = _rust_extract_unobserved_str_parts(
                    "__anneal_ctrl_val" + tail_nc,
                    "__anneal_ctrl_val" + tail_ns,
                    rust_env=ch_env,
                    str_taint=ch_taint,
                    const_strs=cstrs_base,
                    facts=facts,
                    type_env=types_in,
                )
                return f_st, f_ty, f_taint
            return met, None, met_taint

        return "const", None, ""

    def _walk_region(
        reg_start: int,
        reg_end: int,
        cur_env: dict[str, str],
        cur_types: dict[str, str],
        cur_exit_vars: set[str],
        cur_taint: dict[str, str],
        cur_cstrs: dict[str, str],
        cur_exprs: dict[str, str],
        out: list[_AssertionItem],
        cur_exprs_nc: dict[str, str],
        cur_auth: dict[str, str],
    ) -> object:
        segs = _split_rust_top_level_segments(live_ns, reg_start, reg_end)
        seq_nodes: list[object] = []
        idx = 0
        while idx < len(segs):
            kind, s_start, s_end, br_open = segs[idx]
            if kind == "stmt":
                ctrl_span = _find_rhs_ctrl_span(s_start, s_end)
                if ctrl_span is not None:
                    pre_env = dict(cur_env)
                    pre_types = dict(cur_types)
                    pre_taint = dict(cur_taint)
                    pre_cstrs = dict(cur_cstrs)
                    rhs_env = dict(cur_env)
                    rhs_types = dict(cur_types)
                    rhs_exits = set(cur_exit_vars)
                    rhs_taint = dict(cur_taint)
                    rhs_cstrs = dict(cur_cstrs)
                    rhs_exprs = dict(cur_exprs)
                    rhs_exprs_nc = dict(cur_exprs_nc)
                    rhs_auth = dict(cur_auth)
                    seq_nodes.append(
                        _walk_region(
                            ctrl_span[0],
                            ctrl_span[1],
                            rhs_env,
                            rhs_types,
                            rhs_exits,
                            rhs_taint,
                            rhs_cstrs,
                            rhs_exprs,
                            out,
                            rhs_exprs_nc,
                            rhs_auth,
                        )
                    )
                    cur_exit_vars.update(rhs_exits)
                    eq_p = _find_rust_top_level_equal(live_ns[s_start:s_end])
                    if eq_p is not None:
                        lhs_s = live_ns[s_start : s_start + eq_p]
                        ctrl_st, ctrl_ty, ctrl_taint = _eval_rust_ctrl_rhs_status(
                            ctrl_span[0],
                            ctrl_span[1],
                            pre_env,
                            pre_types,
                            pre_taint,
                            pre_cstrs,
                        )
                        lhs_ty = _extract_rust_lhs_type_annotation(lhs_s) or ctrl_ty
                        if ctrl_st in RUST_OBS_STATES and lhs_ty is not None and (
                            lhs_ty in facts.custom_eq_types
                            or lhs_ty in ("__opaque_impl__", "__opaque_dyn__")
                        ):
                            ctrl_st = "const"
                        idents_c = _extract_rust_pattern_idents(lhs_s)
                        for ident in idents_c:
                            cur_env[ident] = ctrl_st
                            cur_exprs.pop(ident, None)
                            cur_exprs_nc.pop(ident, None)
                            cur_auth.pop(ident, None)
                            if len(idents_c) == 1 and lhs_ty is not None:
                                cur_types[ident] = lhs_ty
                            else:
                                cur_types.pop(ident, None)
                            cur_exit_vars.discard(ident)
                            if ctrl_taint:
                                cur_taint[ident] = ctrl_taint
                            else:
                                cur_taint.pop(ident, None)
                            cur_cstrs.pop(ident, None)
                    idx += 1
                    continue
                pre_exit, post_exit = _rust_stmt_exit_or_jump(
                    live_ns[s_start:s_end],
                    s_start,
                    closure_spans,
                    facts=facts,
                    local_may_exit_fns=local_may_exit_f,
                    local_must_exit_fns=local_must_exit_f,
                    cur_exit_vars=frozenset(cur_exit_vars),
                    type_env=cur_types,
                    proc_exit_out=saw_proc_exit,
                )
                if pre_exit is not None:
                    seq_nodes.append(pre_exit)
                seq_nodes.extend(
                    _collect_in_span(
                        s_start,
                        s_end,
                        cur_env,
                        cur_types,
                        cur_taint,
                        cur_cstrs,
                        cur_exprs,
                        out,
                        cur_exprs_nc,
                        cur_auth,
                    )
                )
                _apply_stmt_effect(
                    live_code[s_start:s_end],
                    live_ns[s_start:s_end],
                    cur_env,
                    cur_types,
                    cur_exit_vars,
                    cur_taint,
                    cur_cstrs,
                    cur_exprs,
                    cur_exprs_nc,
                    cur_auth,
                )
                if post_exit is not None:
                    seq_nodes.append(post_exit)
                idx += 1
                continue

            # Control/loop/bare block, chaining `if ... {} else [if ...] {}`.
            assert br_open is not None
            hdr_raw = live_ns[s_start:br_open]
            hdr_attr_off = _skip_leading_rust_attrs(hdr_raw)
            hdr_start = s_start + hdr_attr_off
            hdr = live_ns[hdr_start:br_open]
            hdr_code = live_code[hdr_start:br_open]
            if re.match(r"^\s*if\b", hdr):
                chain_envs: list[dict[str, str]] = []
                chain_types: list[dict[str, str]] = []
                chain_taints: list[dict[str, str]] = []
                chain_cstrs: list[dict[str, str]] = []
                chain_exprs: list[dict[str, str]] = []
                chain_exprs_nc: list[dict[str, str]] = []
                chain_auths: list[dict[str, str]] = []
                chain_cfgs: list[tuple[str, list[object], object, bool]] = []
                saw_plain_else = False
                while idx < len(segs):
                    k_i, cs, ce, cbr = segs[idx]
                    if k_i != "block" or cbr is None:
                        break
                    chdr_raw = live_ns[cs:cbr]
                    chdr_off = _skip_leading_rust_attrs(chdr_raw)
                    chdr_start = cs + chdr_off
                    chdr = live_ns[chdr_start:cbr]
                    chdr_code = live_code[chdr_start:cbr]
                    if idx > 0 and chain_envs and not re.match(r"^\s*else\b", chdr):
                        break
                    is_plain_else = re.match(r"^\s*else\s*$", chdr) is not None
                    if is_plain_else:
                        saw_plain_else = True
                    cond_nodes: list[object] = []
                    h_pre, h_post = _rust_stmt_exit_or_jump(
                        chdr,
                        chdr_start,
                        closure_spans,
                        facts=facts,
                        local_may_exit_fns=local_may_exit_f,
                        local_must_exit_fns=local_must_exit_f,
                        cur_exit_vars=frozenset(cur_exit_vars),
                        type_env=cur_types,
                        proc_exit_out=saw_proc_exit,
                    )
                    if h_pre is not None:
                        cond_nodes.append(h_pre)
                    cond_nodes.extend(
                        _collect_in_span(
                            chdr_start,
                            cbr,
                            cur_env,
                            cur_types,
                            cur_taint,
                            cur_cstrs,
                            cur_exprs,
                            out,
                            cur_exprs_nc,
                            cur_auth,
                        )
                    )
                    if h_post is not None:
                        cond_nodes.append(h_post)
                    b_env = dict(cur_env)
                    b_types = dict(cur_types)
                    b_exits = set(cur_exit_vars)
                    b_taint = dict(cur_taint)
                    b_cstrs = dict(cur_cstrs)
                    b_exprs = dict(cur_exprs)
                    b_exprs_nc = dict(cur_exprs_nc)
                    b_auth = dict(cur_auth)
                    let_m = re.match(
                        r"^\s*(?:else\s+)?if\s+let\b([\s\S]+)$", chdr
                    )
                    if let_m is not None:
                        eq_p = _find_rust_top_level_equal(let_m.group(1))
                        if eq_p is not None:
                            pat_s = let_m.group(1)[:eq_p]
                            off = let_m.start(1) + eq_p + 1
                            expr_ns = chdr[off:]
                            expr_nc = chdr_code[off:]
                            okind = _rust_expr_origin_kind(
                                expr_nc,
                                expr_ns,
                                rust_env=cur_env,
                                rust_facts=facts,
                                rust_type_env=cur_types,
                            )
                            if okind in RUST_OBS_STATES and not _rust_expr_is_trusted_wrapper_or_capture(
                                expr_nc,
                                expr_ns,
                                rust_env=cur_env,
                                type_env=cur_types,
                                facts=facts,
                            ):
                                okind = None
                            e_unobs = _rust_extract_unobserved_str_parts(
                                expr_nc,
                                expr_ns,
                                rust_env=cur_env,
                                str_taint=cur_taint,
                                const_strs=cur_cstrs,
                                facts=facts,
                                type_env=cur_types,
                            )
                            e_auth = _rust_expr_authority_family(
                                expr_nc,
                                expr_ns,
                                rust_auth_env=cur_auth,
                                rust_facts=facts,
                                rust_type_env=cur_types,
                                rust_exprs_nc=cur_exprs_nc,
                            )
                            for v in _extract_rust_pattern_idents(pat_s):
                                b_env[v] = (
                                    okind if okind is not None else "const"
                                )
                                b_types.pop(v, None)
                                b_exprs.pop(v, None)
                                b_exprs_nc.pop(v, None)
                                if e_auth is not None and okind is not None:
                                    b_auth[v] = e_auth
                                else:
                                    b_auth.pop(v, None)
                                if e_unobs:
                                    b_taint[v] = e_unobs
                                else:
                                    b_taint.pop(v, None)
                                b_cstrs.pop(v, None)
                    b_cfg = _walk_region(
                        cbr + 1,
                        ce - 1,
                        b_env,
                        b_types,
                        b_exits,
                        b_taint,
                        b_cstrs,
                        b_exprs,
                        out,
                        b_exprs_nc,
                        b_auth,
                    )
                    cur_exit_vars.update(b_exits)
                    cond_pol = _rust_if_cond_capture_polarity(
                        chdr,
                        chdr_code,
                        rust_env=cur_env,
                        rust_facts=facts,
                        rust_type_env=cur_types,
                    )
                    if saw_fail_on_success is not None and not _eval_cfg_normal_exit_masks(
                        b_cfg, lambda _it: 0
                    ):
                        if cond_pol == "positive_success" or (
                            is_plain_else
                            and len(chain_cfgs) == 1
                            and chain_cfgs[0][0] == "negated_success"
                        ):
                            saw_fail_on_success.append(True)
                    chain_cfgs.append((cond_pol, cond_nodes, b_cfg, is_plain_else))
                    chain_envs.append(b_env)
                    chain_types.append(b_types)
                    chain_taints.append(b_taint)
                    chain_cstrs.append(b_cstrs)
                    chain_exprs.append(b_exprs)
                    chain_exprs_nc.append(b_exprs_nc)
                    chain_auths.append(b_auth)
                    idx += 1
                    if saw_plain_else:
                        break
                if not saw_plain_else:
                    chain_envs.append(dict(cur_env))
                    chain_types.append(dict(cur_types))
                    chain_taints.append(dict(cur_taint))
                    chain_cstrs.append(dict(cur_cstrs))
                    chain_exprs.append(dict(cur_exprs))
                    chain_exprs_nc.append(dict(cur_exprs_nc))
                    chain_auths.append(dict(cur_auth))
                # Fold `if c1 { B1 } else if c2 { B2 } [else { B3 }]` from back.
                else_node: object = _CfgSeq(())
                for _pol, cond_nodes, b_cfg, is_plain_else in reversed(chain_cfgs):
                    if is_plain_else:
                        else_node = _CfgSeq((*cond_nodes, b_cfg))
                    else:
                        else_node = _CfgSeq(
                            (*cond_nodes, _CfgBranch((b_cfg, else_node)))
                        )
                seq_nodes.append(else_node)
                pre_snap = dict(cur_env)
                cur_env.clear()
                cur_env.update(_meet_envs(pre_snap, chain_envs))
                pre_tsnap = dict(cur_types)
                cur_types.clear()
                cur_types.update(_meet_types(pre_tsnap, chain_types))
                pre_esnap = dict(cur_exprs)
                cur_exprs.clear()
                cur_exprs.update(_meet_types(pre_esnap, chain_exprs))
                pre_encsnap = dict(cur_exprs_nc)
                cur_exprs_nc.clear()
                cur_exprs_nc.update(_meet_types(pre_encsnap, chain_exprs_nc))
                pre_asnap = dict(cur_auth)
                cur_auth.clear()
                cur_auth.update(_meet_types(pre_asnap, chain_auths))
                m_taint, m_cstrs = _meet_str_dicts(chain_taints, chain_cstrs)
                cur_taint.clear()
                cur_taint.update(m_taint)
                cur_cstrs.clear()
                cur_cstrs.update(m_cstrs)
                continue

            match_m = re.match(r"^\s*match\b([\s\S]+)$", hdr)
            if match_m is not None:
                m_pre, m_post = _rust_stmt_exit_or_jump(
                    hdr,
                    hdr_start,
                    closure_spans,
                    facts=facts,
                    local_may_exit_fns=local_may_exit_f,
                    local_must_exit_fns=local_must_exit_f,
                    cur_exit_vars=frozenset(cur_exit_vars),
                    type_env=cur_types,
                    proc_exit_out=saw_proc_exit,
                )
                if m_pre is not None:
                    seq_nodes.append(m_pre)
                seq_nodes.extend(
                    _collect_in_span(
                        hdr_start,
                        br_open,
                        cur_env,
                        cur_types,
                        cur_taint,
                        cur_cstrs,
                        cur_exprs,
                        out,
                        cur_exprs_nc,
                        cur_auth,
                    )
                )
                if m_post is not None:
                    seq_nodes.append(m_post)
                sc_off = match_m.start(1)
                sc_kind = _rust_expr_origin_kind(
                    hdr_code[sc_off:],
                    hdr[sc_off:],
                    rust_env=cur_env,
                    rust_facts=facts,
                    rust_type_env=cur_types,
                )
                if sc_kind in RUST_OBS_STATES and not _rust_expr_is_trusted_wrapper_or_capture(
                    hdr_code[sc_off:],
                    hdr[sc_off:],
                    rust_env=cur_env,
                    type_env=cur_types,
                    facts=facts,
                ):
                    sc_kind = None
                sc_unobs = _rust_extract_unobserved_str_parts(
                    hdr_code[sc_off:],
                    hdr[sc_off:],
                    rust_env=cur_env,
                    str_taint=cur_taint,
                    const_strs=cur_cstrs,
                    facts=facts,
                    type_env=cur_types,
                )
                sc_auth = _rust_expr_authority_family(
                    hdr_code[sc_off:],
                    hdr[sc_off:],
                    rust_auth_env=cur_auth,
                    rust_facts=facts,
                    rust_type_env=cur_types,
                    rust_exprs_nc=cur_exprs_nc,
                )
                sc_status = sc_kind if sc_kind is not None else "const"
                arm_spans = _split_rust_match_arm_spans(
                    live_ns, br_open + 1, s_end - 1
                )
                arm_exit_re = re.compile(
                    r"return\b"
                    r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
                    r"process\s*::\s*(?:exit|abort)\s*\("
                    r"|(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
                    r"(?:panic|unreachable|todo|unimplemented)\s*!\s*[(\[{]"
                )
                arm_envs: list[dict[str, str]] = []
                arm_types: list[dict[str, str]] = []
                arm_taints: list[dict[str, str]] = []
                arm_cstrs: list[dict[str, str]] = []
                arm_exprs: list[dict[str, str]] = []
                arm_exprs_nc: list[dict[str, str]] = []
                arm_auths: list[dict[str, str]] = []
                arm_cfgs: list[object] = []
                for pat_s, pat_e, rhs_s, rhs_e in arm_spans:
                    a_env = dict(cur_env)
                    a_types = dict(cur_types)
                    a_exits = set(cur_exit_vars)
                    a_taint = dict(cur_taint)
                    a_cstrs = dict(cur_cstrs)
                    a_exprs = dict(cur_exprs)
                    a_exprs_nc = dict(cur_exprs_nc)
                    a_auth = dict(cur_auth)
                    arm_nodes: list[object] = []
                    pat_only, g_off = _strip_rust_match_guard(
                        live_ns[pat_s:pat_e]
                    )
                    for v in _extract_rust_pattern_idents(pat_only):
                        a_env[v] = sc_status
                        a_types.pop(v, None)
                        a_exprs.pop(v, None)
                        a_exprs_nc.pop(v, None)
                        if sc_auth is not None and sc_status != "const":
                            a_auth[v] = sc_auth
                        else:
                            a_auth.pop(v, None)
                        if sc_unobs:
                            a_taint[v] = sc_unobs
                        else:
                            a_taint.pop(v, None)
                        a_cstrs.pop(v, None)
                    if g_off is not None:
                        g_pre, g_post = _rust_stmt_exit_or_jump(
                            live_ns[pat_s + g_off : pat_e],
                            pat_s + g_off,
                            closure_spans,
                            facts=facts,
                            local_may_exit_fns=local_may_exit_f,
                            local_must_exit_fns=local_must_exit_f,
                            cur_exit_vars=frozenset(a_exits),
                            type_env=a_types,
                            proc_exit_out=saw_proc_exit,
                        )
                        if g_pre is not None:
                            arm_nodes.append(g_pre)
                        arm_nodes.extend(
                            _collect_in_span(
                                pat_s + g_off,
                                pat_e,
                                a_env,
                                a_types,
                                a_taint,
                                a_cstrs,
                                a_exprs,
                                out,
                                a_exprs_nc,
                                a_auth,
                            )
                        )
                        if g_post is not None:
                            arm_nodes.append(g_post)
                    rhs_slice = live_ns[rhs_s:rhs_e].strip()
                    if (
                        rhs_slice.startswith("{")
                        and _find_matching_delimiter_in_code(rhs_slice, 0)
                        == len(rhs_slice) - 1
                    ):
                        ab_open = live_ns.find("{", rhs_s, rhs_e)
                        ab_close = _find_matching_delimiter_in_code(
                            live_ns, ab_open
                        )
                        if ab_close is not None:
                            arm_nodes.append(
                                _walk_region(
                                    ab_open + 1,
                                    ab_close,
                                    a_env,
                                    a_types,
                                    a_exits,
                                    a_taint,
                                    a_cstrs,
                                    a_exprs,
                                    out,
                                    a_exprs_nc,
                                    a_auth,
                                )
                            )
                    else:
                        rhs_ctrl = _find_rhs_ctrl_span(rhs_s, rhs_e)
                        if rhs_ctrl is not None:
                            arm_nodes.append(
                                _walk_region(
                                    rhs_ctrl[0],
                                    rhs_ctrl[1],
                                    a_env,
                                    a_types,
                                    a_exits,
                                    a_taint,
                                    a_cstrs,
                                    a_exprs,
                                    out,
                                    a_exprs_nc,
                                    a_auth,
                                )
                            )
                        else:
                            a_pre, a_post = _rust_stmt_exit_or_jump(
                                live_ns[rhs_s:rhs_e],
                                rhs_s,
                                closure_spans,
                                facts=facts,
                                local_may_exit_fns=local_may_exit_f,
                                local_must_exit_fns=local_must_exit_f,
                                cur_exit_vars=frozenset(a_exits),
                                type_env=a_types,
                                proc_exit_out=saw_proc_exit,
                            )
                            if a_pre is not None:
                                arm_nodes.append(a_pre)
                            arm_nodes.extend(
                                _collect_in_span(
                                    rhs_s,
                                    rhs_e,
                                    a_env,
                                    a_types,
                                    a_taint,
                                    a_cstrs,
                                    a_exprs,
                                    out,
                                    a_exprs_nc,
                                    a_auth,
                                )
                            )
                            _apply_stmt_effect(
                                live_code[rhs_s:rhs_e],
                                live_ns[rhs_s:rhs_e],
                                a_env,
                                a_types,
                                a_exits,
                                a_taint,
                                a_cstrs,
                                a_exprs,
                                a_exprs_nc,
                                a_auth,
                            )
                            if a_post is not None:
                                arm_nodes.append(a_post)
                    cur_exit_vars.update(a_exits)
                    arm_cfg = _CfgSeq(tuple(arm_nodes))
                    arm_cfgs.append(arm_cfg)
                    if (
                        saw_fail_on_success is not None
                        and g_off is None
                        and not _eval_cfg_normal_exit_masks(arm_cfg, lambda _it: 0)
                        and _rust_match_arm_requires_capture_failure(
                            hdr[sc_off:].strip(), pat_only.strip()
                        )
                    ):
                        saw_fail_on_success.append(True)
                    if not _rust_expr_diverges(rhs_slice, arm_exit_re):
                        arm_envs.append(a_env)
                        arm_types.append(a_types)
                        arm_taints.append(a_taint)
                        arm_cstrs.append(a_cstrs)
                        arm_exprs.append(a_exprs)
                        arm_exprs_nc.append(a_exprs_nc)
                        arm_auths.append(a_auth)
                if arm_cfgs:
                    seq_nodes.append(_CfgBranch(tuple(arm_cfgs)))
                if arm_envs:
                    pre_snap = dict(cur_env)
                    cur_env.clear()
                    cur_env.update(_meet_envs(pre_snap, arm_envs))
                    pre_tsnap = dict(cur_types)
                    cur_types.clear()
                    cur_types.update(_meet_types(pre_tsnap, arm_types))
                    pre_esnap = dict(cur_exprs)
                    cur_exprs.clear()
                    cur_exprs.update(_meet_types(pre_esnap, arm_exprs))
                    pre_encsnap = dict(cur_exprs_nc)
                    cur_exprs_nc.clear()
                    cur_exprs_nc.update(_meet_types(pre_encsnap, arm_exprs_nc))
                    pre_asnap = dict(cur_auth)
                    cur_auth.clear()
                    cur_auth.update(_meet_types(pre_asnap, arm_auths))
                    m_taint, m_cstrs = _meet_str_dicts(arm_taints, arm_cstrs)
                    cur_taint.clear()
                    cur_taint.update(m_taint)
                    cur_cstrs.clear()
                    cur_cstrs.update(m_cstrs)
                idx += 1
                continue

            # Bare `{ ... }` or `unsafe { ... }` block executes unconditionally.
            # Labeled `'blk: { ... }` can `break 'blk` early, so handle labels
            # in the loop/break branch below.
            hdr_strip = hdr.strip()
            if not hdr_strip or hdr_strip == "unsafe":
                b_env = dict(cur_env)
                b_types = dict(cur_types)
                b_exits = set(cur_exit_vars)
                b_taint = dict(cur_taint)
                b_cstrs = dict(cur_cstrs)
                b_exprs = dict(cur_exprs)
                b_exprs_nc = dict(cur_exprs_nc)
                b_auth = dict(cur_auth)
                blk_cfg = _walk_region(
                    br_open + 1,
                    s_end - 1,
                    b_env,
                    b_types,
                    b_exits,
                    b_taint,
                    b_cstrs,
                    b_exprs,
                    out,
                    b_exprs_nc,
                    b_auth,
                )
                cur_exit_vars.update(b_exits)
                seq_nodes.append(blk_cfg)
                pre_snapshot = dict(cur_env)
                cur_env.clear()
                cur_env.update(_meet_envs(pre_snapshot, [pre_snapshot, b_env]))
                pre_tsnap = dict(cur_types)
                cur_types.clear()
                cur_types.update(_meet_types(pre_tsnap, [pre_tsnap, b_types]))
                pre_esnap = dict(cur_exprs)
                cur_exprs.clear()
                cur_exprs.update(_meet_types(pre_esnap, [pre_esnap, b_exprs]))
                pre_encsnap = dict(cur_exprs_nc)
                cur_exprs_nc.clear()
                cur_exprs_nc.update(_meet_types(pre_encsnap, [pre_encsnap, b_exprs_nc]))
                pre_asnap = dict(cur_auth)
                cur_auth.clear()
                cur_auth.update(_meet_types(pre_asnap, [pre_asnap, b_auth]))
                m_taint, m_cstrs = _meet_str_dicts(
                    [dict(cur_taint), b_taint], [dict(cur_cstrs), b_cstrs]
                )
                cur_taint.clear()
                cur_taint.update(m_taint)
                cur_cstrs.clear()
                cur_cstrs.update(m_cstrs)
                idx += 1
                continue

            lbl_m = re.match(r"^\s*('[A-Za-z_][A-Za-z0-9_]*)\s*:\s*", hdr)
            hdr_label = lbl_m.group(1) if lbl_m is not None else None
            if lbl_m is not None:
                hdr_start += lbl_m.end()
                hdr = live_ns[hdr_start:br_open]
                hdr_code = live_code[hdr_start:br_open]
            lh_pre, lh_post = _rust_stmt_exit_or_jump(
                hdr,
                hdr_start,
                closure_spans,
                facts=facts,
                local_may_exit_fns=local_may_exit_f,
                local_must_exit_fns=local_must_exit_f,
                cur_exit_vars=frozenset(cur_exit_vars),
                type_env=cur_types,
                proc_exit_out=saw_proc_exit,
            )
            if lh_pre is not None:
                seq_nodes.append(lh_pre)
            seq_nodes.extend(
                _collect_in_span(
                    hdr_start,
                    br_open,
                    cur_env,
                    cur_types,
                    cur_taint,
                    cur_cstrs,
                    cur_exprs,
                    out,
                    cur_exprs_nc,
                    cur_auth,
                )
            )
            if lh_post is not None:
                seq_nodes.append(lh_post)
            b_env = dict(cur_env)
            b_types = dict(cur_types)
            b_exits = set(cur_exit_vars)
            b_taint = dict(cur_taint)
            b_cstrs = dict(cur_cstrs)
            b_exprs = dict(cur_exprs)
            b_exprs_nc = dict(cur_exprs_nc)
            b_auth = dict(cur_auth)
            is_inf_loop = False
            is_labeled_block = lbl_m is not None and (
                not hdr.strip() or hdr.strip() == "unsafe"
            )
            guar_once = is_labeled_block
            if re.match(r"^\s*loop\b", hdr):
                is_inf_loop = True
                guar_once = True
            else:
                for_m = re.match(
                    r"^\s*(?:while\s+let|for)\b([\s\S]+)$", hdr
                )
                if for_m is not None:
                    body_hdr = for_m.group(1)
                    base_off = for_m.start(1)
                    sep_m = (
                        re.search(r"\bin\b", body_hdr)
                        if hdr.lstrip().startswith("for")
                        else None
                    )
                    if sep_m is not None:
                        pat_s = body_hdr[: sep_m.start()]
                        expr_off = base_off + sep_m.end()
                        guar_once = _rust_for_iter_is_statically_non_empty(
                            hdr_code[expr_off:], hdr[expr_off:]
                        )
                    else:
                        eq_p = _find_rust_top_level_equal(body_hdr)
                        pat_s = body_hdr[:eq_p] if eq_p is not None else ""
                        expr_off = (
                            base_off + eq_p + 1
                            if eq_p is not None
                            else len(hdr)
                        )
                    okind = _rust_expr_origin_kind(
                        hdr_code[expr_off:],
                        hdr[expr_off:],
                        rust_env=cur_env,
                        rust_facts=facts,
                        rust_type_env=cur_types,
                    )
                    it_unobs = _rust_extract_unobserved_str_parts(
                        hdr_code[expr_off:],
                        hdr[expr_off:],
                        rust_env=cur_env,
                        str_taint=cur_taint,
                        const_strs=cur_cstrs,
                        facts=facts,
                        type_env=cur_types,
                    )
                    for v in _extract_rust_pattern_idents(pat_s):
                        b_env[v] = okind if okind is not None else "const"
                        b_types.pop(v, None)
                        b_exprs.pop(v, None)
                        b_exprs_nc.pop(v, None)
                        b_auth.pop(v, None)
                        if it_unobs:
                            b_taint[v] = it_unobs
                        else:
                            b_taint.pop(v, None)
                        b_cstrs.pop(v, None)
                else:
                    while_m = re.match(r"^\s*while\b([\s\S]+)$", hdr)
                    if while_m is not None:
                        if (
                            _eval_rust_static_bool_cond(
                                while_m.group(1),
                                cond_code=hdr_code[while_m.start(1) :],
                            )
                            is True
                        ):
                            is_inf_loop = True
                            guar_once = True
            loop_body = _walk_region(
                br_open + 1,
                s_end - 1,
                b_env,
                b_types,
                b_exits,
                b_taint,
                b_cstrs,
                b_exprs,
                out,
                b_exprs_nc,
                b_auth,
            )
            cur_exit_vars.update(b_exits)
            seq_nodes.append(
                _CfgLoop(
                    body=loop_body,
                    guaranteed_at_least_once=guar_once,
                    is_infinite=is_inf_loop,
                    label=hdr_label,
                    is_block=is_labeled_block,
                )
            )
            pre_snapshot = dict(cur_env)
            cur_env.clear()
            cur_env.update(_meet_envs(pre_snapshot, [pre_snapshot, b_env]))
            pre_tsnap = dict(cur_types)
            cur_types.clear()
            cur_types.update(_meet_types(pre_tsnap, [pre_tsnap, b_types]))
            pre_esnap = dict(cur_exprs)
            cur_exprs.clear()
            cur_exprs.update(_meet_types(pre_esnap, [pre_esnap, b_exprs]))
            pre_encsnap = dict(cur_exprs_nc)
            cur_exprs_nc.clear()
            cur_exprs_nc.update(_meet_types(pre_encsnap, [pre_encsnap, b_exprs_nc]))
            pre_asnap = dict(cur_auth)
            cur_auth.clear()
            cur_auth.update(_meet_types(pre_asnap, [pre_asnap, b_auth]))
            m_taint, m_cstrs = _meet_str_dicts(
                [dict(cur_taint), b_taint], [dict(cur_cstrs), b_cstrs]
            )
            cur_taint.clear()
            cur_taint.update(m_taint)
            cur_cstrs.clear()
            cur_cstrs.update(m_cstrs)
            idx += 1

        return _CfgSeq(tuple(seq_nodes))

    items: list[_AssertionItem] = []
    exit_vars_init: set[str] = set()
    str_taint_init: dict[str, str] = {}
    const_strs_init: dict[str, str] = {}
    exprs_init: dict[str, str] = {}
    exprs_nc_init: dict[str, str] = {}
    inner_start = live_ns.find("{")
    inner_end = live_ns.rfind("}")
    if inner_start != -1 and inner_end > inner_start:
        cfg_root = _walk_region(
            inner_start + 1,
            inner_end,
            rust_env,
            rust_type_env,
            exit_vars_init,
            str_taint_init,
            const_strs_init,
            exprs_init,
            items,
            exprs_nc_init,
            rust_auth_env,
        )
    else:
        cfg_root = _walk_region(
            0,
            len(live_ns),
            rust_env,
            rust_type_env,
            exit_vars_init,
            str_taint_init,
            const_strs_init,
            exprs_init,
            items,
            exprs_nc_init,
            rust_auth_env,
        )
    return items, cfg_root


PURE_PY_CALLS = frozenset(
    {
        "len",
        "bool",
        "int",
        "float",
        "str",
        "bytes",
        "bytearray",
        "memoryview",
        "list",
        "dict",
        "set",
        "tuple",
        "frozenset",
        "repr",
        "ascii",
        "ord",
        "chr",
        "abs",
        "round",
        "min",
        "max",
        "sum",
        "sorted",
        "reversed",
        "enumerate",
        "zip",
        "any",
        "all",
        "format",
        "range",
        "slice",
        "type",
        "isinstance",
        "issubclass",
        "json.dumps",
        "json.loads",
        "re.compile",
        "Path",
        "PurePath",
        "PurePosixPath",
        "SimpleNamespace",
    }
)
PURE_PY_METHODS = frozenset(
    {
        "strip",
        "lstrip",
        "rstrip",
        "lower",
        "upper",
        "title",
        "capitalize",
        "casefold",
        "swapcase",
        "replace",
        "split",
        "rsplit",
        "splitlines",
        "partition",
        "rpartition",
        "join",
        "encode",
        "decode",
        "format",
        "format_map",
        "startswith",
        "endswith",
        "find",
        "rfind",
        "index",
        "rindex",
        "count",
        "get",
        "keys",
        "values",
        "items",
        "copy",
        "as_posix",
    }
)


def _eval_python_static_bool(
    node: ast.expr, const_vals: dict[str, object] | None = None
) -> bool | None:
    """Evaluate static constant/truthy expressions in Python test ASTs."""
    if isinstance(node, ast.Constant):
        return bool(node.value)
    if isinstance(node, ast.Name) and const_vals is not None and node.id in const_vals:
        return bool(const_vals[node.id])
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return bool(node.elts)
    if isinstance(node, ast.Dict):
        if not node.keys:
            return False
        if any(k is not None for k in node.keys):
            return True
        return None
    if isinstance(node, ast.UnaryOp):
        if isinstance(node.op, ast.Not):
            inner = _eval_python_static_bool(node.operand, const_vals)
            return (not inner) if inner is not None else None
        if isinstance(node.op, (ast.UAdd, ast.USub, ast.Invert)):
            try:
                return bool(ast.literal_eval(node))
            except (ValueError, TypeError):
                return None
    if isinstance(node, ast.BoolOp):
        vals = [_eval_python_static_bool(v, const_vals) for v in node.values]
        if isinstance(node.op, ast.And):
            if any(v is False for v in vals):
                return False
            if all(v is True for v in vals):
                return True
            return None
        if isinstance(node.op, ast.Or):
            if any(v is True for v in vals):
                return True
            if all(v is False for v in vals):
                return False
            return None
    return None


def _is_python_assertion_call(node: ast.Call) -> bool:
    """Return True strictly for `self.assert*` / `self.fail*` TestCase calls."""
    func = node.func
    if not isinstance(func, ast.Attribute):
        return False
    if not (func.attr.startswith("assert") or func.attr.startswith("fail")):
        return False
    if isinstance(func.value, ast.Name) and func.value.id == "self":
        return True
    if (
        isinstance(func.value, ast.Call)
        and isinstance(func.value.func, ast.Name)
        and func.value.func.id == "super"
        and not func.value.args
        and not func.value.keywords
    ):
        return True
    return False


def _dotted_python_name(node: ast.AST) -> str | None:
    """Return dotted attribute/name string for simple AST target nodes."""
    parts: list[str] = []
    cur: ast.AST = node
    while isinstance(cur, ast.Attribute):
        parts.append(cur.attr)
        cur = cur.value
    if isinstance(cur, ast.Name):
        parts.append(cur.id)
        return ".".join(reversed(parts))
    return None


PY_SUBPROCESS_CALLS = frozenset(
    {
        "subprocess.run",
        "subprocess.check_output",
        "subprocess.check_call",
        "subprocess.Popen",
        "subprocess.getstatusoutput",
        "subprocess.getoutput",
    }
)
PY_APPROVED_RUNTIME_MOD_RE = re.compile(
    r"^(?:anneal(?:_[A-Za-z0-9_]+)?|check_[A-Za-z0-9_]+|audit_[A-Za-z0-9_]+"
    r"|run_anneal_[A-Za-z0-9_]+|verify_[A-Za-z0-9_]+|lean_[A-Za-z0-9_]+"
    r"|mir_[A-Za-z0-9_]+|itree_[A-Za-z0-9_]+|trusted_[A-Za-z0-9_]+)$"
)
PY_DRIVER_HARNESS_FN_RE = re.compile(
    r"^(?:run_probe|run_lean|eval_lean|run_mir_eval|run_miri|run_audit"
    r"|audit_|run_verify|run_check|run_capture|run_differential|run_itree"
    r"|invoke_audit|invoke_lean|exec_lean|check_phase0|check_guard"
    r"|verify_)[A-Za-z0-9_]*$"
)
PY_DISALLOWED_SUBPROCESS_BINS = frozenset(
    {
        "echo",
        "printf",
        "true",
        "false",
        "cat",
        "head",
        "tail",
        "sed",
        "awk",
        "grep",
        "sh",
        "bash",
        "dash",
        "zsh",
        "fish",
        "env",
        "tee",
        "sleep",
        "test",
        "[",
    }
)
PY_APPROVED_SUBPROCESS_BINS = frozenset(
    {
        "cargo",
        "lake",
        "lean",
        "rustc",
        "rustup",
        "cargo-anneal",
        "anneal-audit",
        "anneal-rustc-capture",
        "anneal-rustc-capture-test-bin",
        "anneal-mir-eval",
        "anneal-lean-run",
        "itree_diff",
        "run_anneal_check.sh",
    }
)


def _record_py_import_aliases(
    stmt: ast.stmt, aliases: dict[str, str]
) -> None:
    """Update `aliases` mapping bound names to canonical imported module/symbol."""
    if isinstance(stmt, ast.Import):
        for al in stmt.names:
            if al.asname:
                aliases[al.asname] = al.name
            else:
                top = al.name.split(".", 1)[0]
                aliases[top] = top
                aliases[al.name] = al.name
    elif isinstance(stmt, ast.ImportFrom):
        mod = stmt.module or ""
        for al in stmt.names:
            if al.name == "*":
                if mod == "os":
                    aliases["_exit"] = "os._exit"
                continue
            bound = al.asname or al.name
            aliases[bound] = f"{mod}.{al.name}" if mod else al.name


def _resolve_py_callee(callee: str, aliases: dict[str, str]) -> str:
    """Resolve `callee` through Python import aliases."""
    if not callee:
        return ""
    if callee in aliases:
        return aliases[callee]
    if "." in callee:
        head, rest = callee.split(".", 1)
        if head in aliases:
            return f"{aliases[head]}.{rest}"
    return callee


def _py_is_approved_module_call(resolved: str) -> bool:
    """Return True iff `resolved` invokes an approved non-stdlib Anneal module."""
    if "." not in resolved:
        return False
    mod_root = resolved.split(".", 1)[0]
    if mod_root in sys.stdlib_module_names:
        return False
    return PY_APPROVED_RUNTIME_MOD_RE.fullmatch(mod_root) is not None


PY_BARE_TOOLCHAIN_BINS = frozenset({"cargo", "lake", "lean", "rustc", "rustup"})
PY_TEMP_PATH_HINTS = ("tmp", "temp", "mkdtemp", "mkstemp", "namedtemporaryfile", "/dev/shm")
PY_REPO_ANCHOR_HINTS = (
    "repo_root",
    "anneal_root",
    "ci_dir",
    "script_path",
    "__file__",
    "anneal/ci/",
    "anneal/target/",
    "anneal/trusted/",
    "ci/check_",
)
PY_CUSTOM_CMP_DUNDERS = frozenset(
    {
        "__eq__",
        "__ne__",
        "__contains__",
        "__bool__",
        "__lt__",
        "__le__",
        "__gt__",
        "__ge__",
        "__str__",
        "__repr__",
    }
)


def _py_bin_name_is_approved(bin_str: str) -> bool:
    """Require bare toolchain command or repo-relative authenticated Anneal path."""
    raw = bin_str.strip()
    if not raw or ".." in PurePosixPath(raw).parts:
        return False
    base = PurePosixPath(raw).name
    if not base or base in PY_DISALLOWED_SUBPROCESS_BINS:
        return False
    # Never trust arbitrary absolute paths like `/tmp/anneal-capture-fake`.
    if raw.startswith("/") or raw.startswith("~"):
        return False
    if "/" not in raw:
        return base in PY_BARE_TOOLCHAIN_BINS
    norm = raw[2:] if raw.startswith("./") else raw
    if not norm.startswith(("anneal/", "ci/")):
        return False
    if base in PY_APPROVED_SUBPROCESS_BINS:
        return True
    return base.startswith(
        ("anneal-", "anneal_", "check_", "audit_", "run_anneal_", "verify_")
    ) or base.endswith((".py", ".sh"))


def _py_script_path_is_approved(script_str: str) -> bool:
    """Require a repo-relative Python script path (reject `/tmp/fake.py`)."""
    raw = script_str.strip()
    if not raw or raw.startswith(("-", "/", "~")) or ".." in PurePosixPath(raw).parts:
        return False
    base = PurePosixPath(raw).name
    if not base or base in PY_DISALLOWED_SUBPROCESS_BINS:
        return False
    norm = raw[2:] if raw.startswith("./") else raw
    return norm.startswith(("anneal/", "ci/")) and norm.endswith(".py")


def _py_expr_path_src_is_approved(expr_src: str) -> bool:
    """Require a repo-anchored path expression (reject temp-dir / shell paths)."""
    low = expr_src.lower()
    if any(
        re.search(rf"\b{re.escape(bad)}\b", low)
        for bad in ("echo", "printf", "bash", "dash", "zsh")
    ):
        return False
    if any(t in low for t in PY_TEMP_PATH_HINTS):
        return False
    return any(a in low for a in PY_REPO_ANCHOR_HINTS)


def _py_is_python_exe_expr(
    node: ast.expr, const_vals: dict[str, object], aliases: dict[str, str]
) -> bool:
    dname = _dotted_python_name(node) or ""
    if dname and _resolve_py_callee(dname, aliases) == "sys.executable":
        return True
    ok, val = _extract_py_static_const(node, const_vals)
    if ok and isinstance(val, str):
        base = PurePosixPath(val).name
        if re.fullmatch(r"python3?(?:\.\d+)?", base):
            return True
    return False


def _py_is_safe_cli_flag(val: object) -> bool:
    """Return True iff `val` is a known zero-argument Python CLI flag (`-I`, `-B`, ...)."""
    return isinstance(val, str) and bool(_PY_SAFE_CLI_FLAG_RE.fullmatch(val))


def _py_subprocess_seq_is_approved(
    elts: list[ast.expr],
    *,
    const_vals: dict[str, object],
    aliases: dict[str, str],
) -> bool:
    if not elts:
        return False
    for elt in elts:
        ok, val = _extract_py_static_const(elt, const_vals)
        if ok and isinstance(val, str) and val in ("-c", "-e"):
            return False
    first = elts[0]
    if _py_is_python_exe_expr(first, const_vals, aliases):
        idx = 1
        while idx < len(elts):
            e_ok, e_val = _extract_py_static_const(elts[idx], const_vals)
            if e_ok and _py_is_safe_cli_flag(e_val):
                idx += 1
                continue
            break
        if idx >= len(elts):
            return False
        target = elts[idx]
        s_ok, s_val = _extract_py_static_const(target, const_vals)
        if s_ok and isinstance(s_val, str):
            return _py_script_path_is_approved(s_val)
        return _py_expr_path_src_is_approved(ast.unparse(target))

    f_ok, f_val = _extract_py_static_const(first, const_vals)
    if f_ok and isinstance(f_val, str):
        return _py_bin_name_is_approved(f_val)
    return _py_expr_path_src_is_approved(ast.unparse(first))


def _py_subprocess_cmd_is_approved(
    cmd_node: ast.expr,
    *,
    env: dict[str, str],
    const_vals: dict[str, object],
    aliases: dict[str, str],
) -> bool:
    """Verify a subprocess command invokes an Anneal/Rust/Lean target, not echo/-c."""
    if isinstance(cmd_node, ast.Name):
        if env.get(cmd_node.id) == "cmd_approved":
            return True
        if cmd_node.id in const_vals:
            cval = const_vals[cmd_node.id]
            if isinstance(cval, (list, tuple)) and cval:
                if any(
                    isinstance(x, str) and x in ("-c", "-e") for x in cval
                ):
                    return False
                if isinstance(cval[0], str):
                    base0 = PurePosixPath(cval[0]).name
                    if re.fullmatch(r"python3?(?:\.\d+)?", base0):
                        idx = 1
                        while idx < len(cval) and _py_is_safe_cli_flag(cval[idx]):
                            idx += 1
                        return (
                            idx < len(cval)
                            and isinstance(cval[idx], str)
                            and _py_script_path_is_approved(cval[idx])
                        )
                    return _py_bin_name_is_approved(cval[0])
            if isinstance(cval, str):
                return _py_bin_name_is_approved(cval)
        return False
    if isinstance(cmd_node, (ast.List, ast.Tuple)):
        return _py_subprocess_seq_is_approved(
            list(cmd_node.elts), const_vals=const_vals, aliases=aliases
        )
    if isinstance(cmd_node, ast.BinOp) and isinstance(cmd_node.op, ast.Add):
        if isinstance(cmd_node.right, (ast.List, ast.Tuple)):
            for elt in cmd_node.right.elts:
                ok, val = _extract_py_static_const(elt, const_vals)
                if ok and isinstance(val, str) and val in ("-c", "-e"):
                    return False
        if isinstance(cmd_node.left, (ast.List, ast.Tuple)) and isinstance(
            cmd_node.right, (ast.List, ast.Tuple)
        ):
            return _py_subprocess_seq_is_approved(
                [*cmd_node.left.elts, *cmd_node.right.elts],
                const_vals=const_vals,
                aliases=aliases,
            )
        return _py_subprocess_cmd_is_approved(
            cmd_node.left, env=env, const_vals=const_vals, aliases=aliases
        )
    ok, val = _extract_py_static_const(cmd_node, const_vals)
    if ok and isinstance(val, str):
        return _py_bin_name_is_approved(val)
    return False


def _py_subprocess_authority_family(
    node: ast.Call,
    *,
    const_vals: dict[str, object],
    aliases: dict[str, str],
) -> str | None:
    """Classify an approved `subprocess.*` call into capture vs oracle."""
    cmd_arg: ast.expr | None = node.args[0] if node.args else None
    if cmd_arg is None:
        for kw in node.keywords:
            if kw.arg == "args":
                cmd_arg = kw.value
                break
    if cmd_arg is None:
        return None
    seq_vals: list[str] = []
    if isinstance(cmd_arg, ast.Name) and cmd_arg.id in const_vals:
        cv = const_vals[cmd_arg.id]
        if isinstance(cv, (list, tuple)) and all(isinstance(x, str) for x in cv):
            seq_vals = list(cv)
        elif isinstance(cv, str):
            seq_vals = [cv]
    elif isinstance(cmd_arg, (ast.List, ast.Tuple)):
        for elt in cmd_arg.elts:
            ok, val = _extract_py_static_const(elt, const_vals)
            if ok and isinstance(val, str):
                seq_vals.append(val)
    elif isinstance(cmd_arg, ast.BinOp) and isinstance(cmd_arg.op, ast.Add):
        for side in (cmd_arg.left, cmd_arg.right):
            if isinstance(side, (ast.List, ast.Tuple)):
                for elt in side.elts:
                    ok, val = _extract_py_static_const(elt, const_vals)
                    if ok and isinstance(val, str):
                        seq_vals.append(val)
    else:
        ok, val = _extract_py_static_const(cmd_arg, const_vals)
        if ok and isinstance(val, str):
            seq_vals = [val]

    if seq_vals:
        b0 = PurePosixPath(seq_vals[0]).name
        rest = seq_vals[1:]
        if b0 in (
            "anneal-rustc-capture",
            "anneal-rustc-capture-test-bin",
            "cargo-anneal",
        ):
            return "capture"
        if b0 == "anneal-mir-eval":
            return "oracle_mir_eval"
        if b0 in ("lean", "lake"):
            return "oracle_lean"
        if b0 == "rustc":
            return "oracle_rustc"
        if b0 == "miri":
            return "oracle_miri"
        if b0 == "cargo" and any(a == "miri" for a in rest):
            return "oracle_miri"
        if b0 == "itree_diff":
            return "oracle_diff"
        if re.fullmatch(r"python3?(?:\.\d+)?", b0):
            joined = " ".join(rest)
            if "itree_diff" in joined:
                return "oracle_diff"
            if "anneal-mir-eval" in joined:
                return "oracle_mir_eval"
            return None

    unp = ast.unparse(cmd_arg)
    if "anneal-mir-eval" in unp:
        return "oracle_mir_eval"
    if "itree_diff" in unp:
        return "oracle_diff"
    if "anneal-rustc-capture" in unp or "cargo-anneal" in unp:
        return "capture"
    return None


def _py_call_authority_family(
    node: ast.Call,
    *,
    auth_env: dict[str, str],
    const_vals: dict[str, object],
    aliases: dict[str, str],
    py_facts: _PyFileFacts,
) -> str | None:
    """Return authority family (`capture`, `oracle_*`, etc.) for Python call."""
    callee = _dotted_python_name(node.func) or ""
    if not callee:
        return None
    resolved = _resolve_py_callee(callee, aliases)
    if resolved in PY_SUBPROCESS_CALLS:
        return _py_subprocess_authority_family(
            node, const_vals=const_vals, aliases=aliases
        )
    if "." not in callee:
        if callee in auth_env:
            return auth_env[callee]
        fn_auth = (py_facts.fn_authority_families or {}).get(callee)
        if fn_auth is not None:
            return fn_auth
        if callee in py_facts.local_defs or callee in py_facts.local_classes:
            return None
        if callee.startswith(
            ("run_capture", "try_capture", "invoke_capture", "exec_capture")
        ):
            return "capture"
        if callee.startswith(("run_miri", "matches_miri")):
            return "oracle_miri"
        if callee.startswith(
            ("run_lean", "eval_lean", "invoke_lean", "exec_lean")
        ):
            return "oracle_lean"
        if callee.startswith("run_mir_eval"):
            return "oracle_mir_eval"
        if callee.startswith(("run_itree", "run_differential")):
            return "oracle_diff"
        return None

    head, tail = callee.split(".", 1)
    if head in ("self", "cls") and "." not in tail:
        return (py_facts.fn_authority_families or {}).get(callee)
    if head in aliases:
        mod_root = resolved.split(".", 1)[0]
        if mod_root.startswith(("anneal_rustc_capture", "cargo_anneal")):
            return "capture"
        if mod_root.startswith("anneal_mir_eval"):
            return "oracle_mir_eval"
        if mod_root.startswith("anneal_itree_diff"):
            return "oracle_diff"
    return None


def _py_expr_authority_family(
    node: ast.AST,
    *,
    auth_env: dict[str, str],
    const_vals: dict[str, object],
    py_facts: _PyFileFacts,
    py_exprs: dict[str, str] | None = None,
    _depth: int = 0,
) -> str | None:
    """Infer authority family flowing into Python AST `node`."""
    aliases = py_facts.import_aliases or {}
    if isinstance(node, ast.Name):
        if node.id in auth_env:
            return auth_env[node.id]
        if _depth < 3 and py_exprs and node.id in py_exprs:
            try:
                parsed = ast.parse(py_exprs[node.id], mode="eval")
            except SyntaxError:
                return None
            return _py_expr_authority_family(
                parsed.body,
                auth_env=auth_env,
                const_vals=const_vals,
                py_facts=py_facts,
                py_exprs=py_exprs,
                _depth=_depth + 1,
            )
        return None
    if isinstance(node, ast.Attribute):
        if isinstance(node.value, ast.Name) and node.value.id == "self":
            skey = f"self.{node.attr}"
            if skey in auth_env:
                return auth_env[skey]
        return _py_expr_authority_family(
            node.value,
            auth_env=auth_env,
            const_vals=const_vals,
            py_facts=py_facts,
            py_exprs=py_exprs,
            _depth=_depth + 1,
        )
    if isinstance(node, ast.Call):
        return _py_call_authority_family(
            node,
            auth_env=auth_env,
            const_vals=const_vals,
            aliases=aliases,
            py_facts=py_facts,
        )
    if isinstance(node, ast.IfExp):
        bf = _py_expr_authority_family(
            node.body,
            auth_env=auth_env,
            const_vals=const_vals,
            py_facts=py_facts,
            py_exprs=py_exprs,
            _depth=_depth + 1,
        )
        ef = _py_expr_authority_family(
            node.orelse,
            auth_env=auth_env,
            const_vals=const_vals,
            py_facts=py_facts,
            py_exprs=py_exprs,
            _depth=_depth + 1,
        )
        return bf if bf is not None and bf == ef else None
    return None


def _py_subprocess_call_is_approved(
    node: ast.Call,
    *,
    env: dict[str, str],
    const_vals: dict[str, object],
    aliases: dict[str, str],
) -> bool:
    """Verify `subprocess.*` executes an approved runtime command without shell=True."""
    for kw in node.keywords:
        if kw.arg == "shell" and _eval_python_static_bool(kw.value, const_vals) is not False:
            return False
    cmd_arg: ast.expr | None = node.args[0] if node.args else None
    if cmd_arg is None:
        for kw in node.keywords:
            if kw.arg == "args":
                cmd_arg = kw.value
                break
    if cmd_arg is None:
        return False
    return _py_subprocess_cmd_is_approved(
        cmd_arg, env=env, const_vals=const_vals, aliases=aliases
    )


def _py_call_is_direct_observation(
    node: ast.Call,
    *,
    env: dict[str, str],
    const_vals: dict[str, object],
    type_env: dict[str, str],
    py_facts: _PyFileFacts,
) -> bool:
    """Return True iff `node` directly invokes an approved runtime/driver/helper."""
    if _is_python_assertion_call(node):
        return False
    aliases = py_facts.import_aliases or {}
    callee = _dotted_python_name(node.func) or ""
    if callee and "." not in callee:
        if callee in env:
            return env[callee] == "observed"
        if callee in aliases:
            resolved = aliases[callee]
            if resolved in PY_SUBPROCESS_CALLS:
                return _py_subprocess_call_is_approved(
                    node, env=env, const_vals=const_vals, aliases=aliases
                )
            return _py_is_approved_module_call(resolved)
        if callee in py_facts.observed_fns:
            return True
        if callee in py_facts.local_defs or callee in py_facts.local_classes:
            return False
        return PY_DRIVER_HARNESS_FN_RE.fullmatch(callee) is not None

    if callee:
        head, tail = callee.split(".", 1)
        if head in ("self", "cls"):
            if "." not in tail and tail in py_facts.self_observed_methods:
                return True
            return False
        if (
            head not in env
            and head not in py_facts.local_defs
            and head not in py_facts.local_classes
        ):
            resolved = _resolve_py_callee(callee, aliases)
            if resolved in PY_SUBPROCESS_CALLS:
                return _py_subprocess_call_is_approved(
                    node, env=env, const_vals=const_vals, aliases=aliases
                )
            if head in aliases and _py_is_approved_module_call(resolved):
                return True

    if isinstance(node.func, ast.Attribute):
        mname = node.func.attr
        recv_cls: str | None = None
        if isinstance(node.func.value, ast.Name):
            if node.func.value.id in py_facts.local_classes:
                recv_cls = node.func.value.id
            elif node.func.value.id in type_env:
                recv_cls = type_env[node.func.value.id]
        elif (
            isinstance(node.func.value, ast.Call)
            and isinstance(node.func.value.func, ast.Name)
            and node.func.value.func.id in py_facts.local_classes
        ):
            recv_cls = node.func.value.func.id
        if recv_cls is not None:
            return mname in (py_facts.class_observed_methods or {}).get(
                recv_cls, frozenset()
            )
    return False


def _py_is_empty_falsy_literal(node: ast.AST) -> bool:
    """Return True for empty falsy fallback literals (`""`, `b""`, `None`, `[]`)."""
    if isinstance(node, ast.Constant):
        return node.value in ("", b"", None, False, 0)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        return len(node.elts) == 0
    if isinstance(node, ast.Dict):
        return len(node.keys) == 0
    return False


def _py_is_benign_sep_const(node: ast.AST) -> bool:
    """Return True for short non-alphanumeric separator literals (`\\n`, `: `)."""
    if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
        val = (
            node.value.decode("utf-8", errors="ignore")
            if isinstance(node.value, bytes)
            else node.value
        )
        return len(val) <= 4 and not any(ch.isalnum() for ch in val)
    return False


def _py_expr_ast_is_observed(
    node: ast.AST,
    *,
    env: dict[str, str],
    self_attrs: dict[str, str],
    pure_fns: frozenset[str],
    local_ignored: frozenset[str] = frozenset(),
    py_facts: _PyFileFacts | None = None,
    const_vals: dict[str, object] | None = None,
    type_env: dict[str, str] | None = None,
    is_assertion_context: bool = False,
) -> bool:
    """Return True iff Python `node` carries verified runtime/driver dataflow."""
    facts = py_facts or _PyFileFacts()
    cvals = const_vals or {}
    tenv = type_env or {}

    def _rec(sub: ast.AST, *, assert_ctx: bool = False) -> bool:
        return _py_expr_ast_is_observed(
            sub,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            local_ignored=local_ignored,
            py_facts=facts,
            const_vals=cvals,
            type_env=tenv,
            is_assertion_context=assert_ctx,
        )

    if isinstance(node, ast.Lambda):
        return False
    if isinstance(node, ast.Constant):
        return False
    if isinstance(node, ast.Name):
        if node.id in local_ignored:
            return False
        return env.get(node.id) == "observed"
    if isinstance(node, ast.Attribute):
        if isinstance(node.value, ast.Name) and node.value.id == "self":
            return self_attrs.get(node.attr) == "observed"
        return _rec(node.value)
    if isinstance(node, ast.Call):
        if _is_python_assertion_call(node):
            return False
        if (
            isinstance(node.func, ast.Name)
            and node.func.id in facts.custom_cmp_classes
        ):
            return False
        if _py_call_is_direct_observation(
            node,
            env=env,
            const_vals=cvals,
            type_env=tenv,
            py_facts=facts,
        ):
            return True
        # Fail closed on unrecognized/stdlib/pure calls (e.g. `copy.copy(...)`):
        # propagate observation strictly from receiver or argument dataflow.
        if isinstance(node.func, ast.Attribute) and not (
            isinstance(node.func.value, ast.Name)
            and (
                node.func.value.id in ("json", "re", "self", "cls")
                or node.func.value.id in (facts.import_aliases or {})
            )
        ):
            if _rec(node.func.value):
                return True
        for arg in node.args:
            if _rec(arg):
                return True
        for kw in node.keywords:
            if _rec(kw.value):
                return True
        return False
    if isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)):
        bound: set[str] = set(local_ignored)
        for gen in node.generators:
            if _py_expr_ast_is_observed(
                gen.iter,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                local_ignored=frozenset(bound),
                py_facts=facts,
                const_vals=cvals,
                type_env=tenv,
            ):
                return True
            for tgt in ast.walk(gen.target):
                if isinstance(tgt, ast.Name):
                    bound.add(tgt.id)
            for cond in gen.ifs:
                if _py_expr_ast_is_observed(
                    cond,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    local_ignored=frozenset(bound),
                    py_facts=facts,
                    const_vals=cvals,
                    type_env=tenv,
                ):
                    return True
        if isinstance(node, ast.DictComp):
            return _py_expr_ast_is_observed(
                node.key,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                local_ignored=frozenset(bound),
                py_facts=facts,
                const_vals=cvals,
                type_env=tenv,
            ) or _py_expr_ast_is_observed(
                node.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                local_ignored=frozenset(bound),
                py_facts=facts,
                const_vals=cvals,
                type_env=tenv,
            )
        return _py_expr_ast_is_observed(
            node.elt,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            local_ignored=frozenset(bound),
            py_facts=facts,
            const_vals=cvals,
            type_env=tenv,
        )
    if isinstance(node, ast.IfExp):
        cond = _eval_python_static_bool(node.test, cvals)
        if cond is True:
            return _rec(node.body, assert_ctx=is_assertion_context)
        if cond is False:
            return _rec(node.orelse, assert_ctx=is_assertion_context)
        return _rec(node.body, assert_ctx=is_assertion_context) and _rec(
            node.orelse, assert_ctx=is_assertion_context
        )
    if isinstance(node, ast.BoolOp):
        if is_assertion_context:
            return any(_rec(v, assert_ctx=True) for v in node.values)
        if not node.values:
            return False
        if isinstance(node.op, ast.Or):
            if all(_rec(v) for v in node.values):
                return True
            return _rec(node.values[0]) and all(
                _py_is_empty_falsy_literal(v) for v in node.values[1:]
            )
        return all(_rec(v) for v in node.values)
    if isinstance(node, ast.Subscript):
        if isinstance(node.value, (ast.List, ast.Tuple)):
            if not node.value.elts:
                return False
            ok, idx_val = _extract_py_static_const(node.slice, cvals)
            if ok and isinstance(idx_val, int) and not isinstance(idx_val, bool):
                if -len(node.value.elts) <= idx_val < len(node.value.elts):
                    return _rec(node.value.elts[idx_val])
                return False
            return all(_rec(e) for e in node.value.elts)
        if isinstance(node.value, ast.Dict):
            ok, key_val = _extract_py_static_const(node.slice, cvals)
            if ok:
                for dk, dv in zip(node.value.keys, node.value.values):
                    if dk is None:
                        continue
                    dok, dkv = _extract_py_static_const(dk, cvals)
                    if dok and dkv == key_val:
                        return _rec(dv)
                return False
            return bool(node.value.values) and all(
                _rec(v) for v in node.value.values
            )
        return _rec(node.value)
    if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
        if is_assertion_context:
            return any(_rec(e) for e in node.elts)
        return bool(node.elts) and all(_rec(e) for e in node.elts)
    if isinstance(node, ast.Dict):
        return bool(node.values) and all(_rec(v) for v in node.values)
    if isinstance(node, ast.JoinedStr):
        return any(
            _rec(v.value)
            for v in node.values
            if isinstance(v, ast.FormattedValue)
        )
    if isinstance(node, ast.FormattedValue):
        return _rec(node.value)
    if isinstance(node, ast.BinOp):
        if isinstance(node.op, ast.Add):
            l_obs = _rec(node.left)
            r_obs = _rec(node.right)
            if l_obs and r_obs:
                return True
            if l_obs and _py_is_benign_sep_const(node.right):
                return True
            if r_obs and _py_is_benign_sep_const(node.left):
                return True
            return False
        return _rec(node.left) and _rec(node.right)
    if isinstance(node, ast.UnaryOp):
        return _rec(node.operand, assert_ctx=is_assertion_context)
    if isinstance(node, ast.Compare):
        return _rec(node.left) or any(_rec(c) for c in node.comparators)
    if isinstance(node, (ast.Await, ast.Starred, ast.NamedExpr)):
        return _rec(node.value, assert_ctx=is_assertion_context)
    return False


def _extract_py_static_const(
    expr: ast.expr, const_vals: dict[str, object]
) -> tuple[bool, object]:
    """Safely evaluate literal/name expressions without runtime calls."""
    if isinstance(expr, ast.Constant):
        return True, expr.value
    if isinstance(expr, ast.Name) and expr.id in const_vals:
        return True, const_vals[expr.id]
    try:
        return True, ast.literal_eval(expr)
    except (ValueError, TypeError):
        return False, None


def _bind_py_target(
    target: ast.AST,
    status: str,
    rhs_const: tuple[bool, object],
    env: dict[str, str],
    const_vals: dict[str, object],
    self_attrs: dict[str, str],
    *,
    type_env: dict[str, str] | None = None,
    rhs_cls: str | None = None,
) -> None:
    if isinstance(target, ast.Name):
        env[target.id] = status
        if status == "const" and rhs_const[0]:
            const_vals[target.id] = rhs_const[1]
        else:
            const_vals.pop(target.id, None)
        if type_env is not None:
            if rhs_cls is not None:
                type_env[target.id] = rhs_cls
            else:
                type_env.pop(target.id, None)
        return
    if (
        isinstance(target, ast.Attribute)
        and isinstance(target.value, ast.Name)
        and target.value.id == "self"
    ):
        self_attrs[target.attr] = status
        return
    if isinstance(target, (ast.Tuple, ast.List)):
        ok, seq = rhs_const
        for idx, elt in enumerate(target.elts):
            if isinstance(elt, ast.Starred):
                _bind_py_target(
                    elt.value,
                    status,
                    (False, None),
                    env,
                    const_vals,
                    self_attrs,
                    type_env=type_env,
                )
            else:
                elt_c = (
                    (True, seq[idx])
                    if ok and isinstance(seq, (tuple, list)) and idx < len(seq)
                    else (False, None)
                )
                _bind_py_target(
                    elt,
                    status,
                    elt_c,
                    env,
                    const_vals,
                    self_attrs,
                    type_env=type_env,
                )


def _collect_py_scoped_defs_and_classes(
    stmts: list[ast.stmt],
) -> tuple[
    list[ast.FunctionDef | ast.AsyncFunctionDef], list[ast.ClassDef]
]:
    """Collect `def`/`class` nodes directly or nested in compound blocks."""
    fns: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    classes: list[ast.ClassDef] = []

    def _walk(body: list[ast.stmt]) -> None:
        for st in body:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
                fns.append(st)
            elif isinstance(st, ast.ClassDef):
                classes.append(st)
            elif isinstance(st, (ast.If, ast.For, ast.AsyncFor, ast.While)):
                _walk(st.body)
                _walk(st.orelse)
            elif isinstance(st, (ast.With, ast.AsyncWith)):
                _walk(st.body)
            elif isinstance(st, ast.Try) or (
                hasattr(ast, "TryStar") and isinstance(st, ast.TryStar)
            ):
                _walk(st.body)
                for h in st.handlers:
                    _walk(h.body)
                _walk(st.orelse)
                _walk(st.finalbody)
            elif hasattr(ast, "Match") and isinstance(st, ast.Match):
                for case in st.cases:
                    _walk(case.body)

    _walk(stmts)
    return fns, classes


def _collect_py_file_facts(
    tree: ast.Module,
    cls_node: ast.ClassDef,
    fn_node: ast.FunctionDef,
    mro_classes: list[ast.ClassDef],
) -> tuple[_PyFileFacts, frozenset[str]]:
    """Collect import aliases, verified runtime helpers, custom-cmp classes, and exit helpers."""
    aliases: dict[str, str] = {}
    for stmt in tree.body:
        _record_py_import_aliases(stmt, aliases)

    free_defs, top_classes = _collect_py_scoped_defs_and_classes(tree.body)
    nested_defs, nested_classes = _collect_py_scoped_defs_and_classes(
        fn_node.body
    )
    all_class_nodes: list[ast.ClassDef] = [*top_classes, *nested_classes]
    local_classes: set[str] = {n.name for n in all_class_nodes}
    local_defs: set[str] = {d.name for d in free_defs} | {
        d.name for d in nested_defs
    }

    class_methods: dict[str, list[ast.FunctionDef | ast.AsyncFunctionDef]] = {}
    class_all_methods: dict[str, set[str]] = {}
    custom_cmp_classes: set[str] = set()
    for n in all_class_nodes:
        ms = [
            m
            for m in n.body
            if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
        ]
        class_methods[n.name] = ms
        m_names = {m.name for m in ms}
        class_all_methods[n.name] = m_names
        if m_names & PY_CUSTOM_CMP_DUNDERS:
            custom_cmp_classes.add(n.name)

    mro_names = [c.name for c in mro_classes]
    observed_fns: set[str] = set()
    class_obs: dict[str, set[str]] = {cname: set() for cname in local_classes}
    may_exit_fns: set[str] = set()
    class_may_exit: dict[str, set[str]] = {cname: set() for cname in local_classes}
    may_os_exit_fns: set[str] = set()
    class_may_os_exit: dict[str, set[str]] = {cname: set() for cname in local_classes}
    skip_fns: set[str] = set()
    class_skip: dict[str, set[str]] = {cname: set() for cname in local_classes}
    fn_auth: dict[str, str] = {}

    def _build_facts() -> _PyFileFacts:
        self_obs: set[str] = set()
        self_ex: set[str] = set()
        self_os_ex: set[str] = set()
        self_sk: set[str] = set()
        for cname in mro_names:
            self_obs.update(class_obs.get(cname, set()))
            self_ex.update(class_may_exit.get(cname, set()))
            self_os_ex.update(class_may_os_exit.get(cname, set()))
            self_sk.update(class_skip.get(cname, set()))
        return _PyFileFacts(
            import_aliases=dict(aliases),
            local_defs=frozenset(local_defs),
            observed_fns=frozenset(observed_fns),
            self_observed_methods=frozenset(self_obs),
            class_observed_methods={
                k: frozenset(v) for k, v in class_obs.items()
            },
            class_all_methods={
                k: frozenset(v) for k, v in class_all_methods.items()
            },
            local_classes=frozenset(local_classes),
            custom_cmp_classes=frozenset(custom_cmp_classes),
            may_exit_success_fns=frozenset(may_exit_fns),
            self_may_exit_methods=frozenset(self_ex),
            class_may_exit_methods={
                k: frozenset(v) for k, v in class_may_exit.items()
            },
            may_os_exit_success_fns=frozenset(may_os_exit_fns),
            self_may_os_exit_methods=frozenset(self_os_ex),
            class_may_os_exit_methods={
                k: frozenset(v) for k, v in class_may_os_exit.items()
            },
            skip_fns=frozenset(skip_fns),
            self_skip_methods=frozenset(self_sk),
            class_skip_methods={
                k: frozenset(v) for k, v in class_skip.items()
            },
            fn_authority_families=dict(fn_auth),
        )

    def _def_authority_family(
        d: ast.FunctionDef | ast.AsyncFunctionDef, cur_facts: _PyFileFacts
    ) -> str | None:
        d_aliases = dict(cur_facts.import_aliases or {})
        d_auth: dict[str, str] = {}
        d_cvals: dict[str, object] = {}
        d_facts = _PyFileFacts(
            **{**cur_facts.__dict__, "import_aliases": d_aliases}
        )
        ret_fams: list[str | None] = []
        for st in d.body:
            _record_py_import_aliases(st, d_aliases)
            if isinstance(st, ast.Assign):
                ok, cv = _extract_py_static_const(st.value, d_cvals)
                if ok:
                    for t in st.targets:
                        if isinstance(t, ast.Name):
                            d_cvals[t.id] = cv
                fam = _py_expr_authority_family(
                    st.value,
                    auth_env=d_auth,
                    const_vals=d_cvals,
                    py_facts=d_facts,
                )
                for t in st.targets:
                    if isinstance(t, ast.Name):
                        if fam is not None:
                            d_auth[t.id] = fam
                        else:
                            d_auth.pop(t.id, None)
            elif isinstance(st, ast.Return) and st.value is not None:
                ret_fams.append(
                    _py_expr_authority_family(
                        st.value,
                        auth_env=d_auth,
                        const_vals=d_cvals,
                        py_facts=d_facts,
                    )
                )
        if ret_fams and ret_fams[0] is not None and all(
            f == ret_fams[0] for f in ret_fams
        ):
            return ret_fams[0]
        return None

    def _def_calls_observed(
        d: ast.FunctionDef | ast.AsyncFunctionDef, cur_facts: _PyFileFacts
    ) -> bool:
        fn_aliases = dict(cur_facts.import_aliases or {})
        fn_env: dict[str, str] = {}
        fn_cvals: dict[str, object] = {}
        fn_tenv: dict[str, str] = {}
        for st in d.body:
            _record_py_import_aliases(st, fn_aliases)
        local_facts = _PyFileFacts(
            **{**cur_facts.__dict__, "import_aliases": fn_aliases}
        )
        for st in d.body:
            if isinstance(st, ast.Assign):
                if _py_subprocess_cmd_is_approved(
                    st.value, env=fn_env, const_vals=fn_cvals, aliases=fn_aliases
                ):
                    for t in st.targets:
                        if isinstance(t, ast.Name):
                            fn_env[t.id] = "cmd_approved"
                else:
                    ok, cv = _extract_py_static_const(st.value, fn_cvals)
                    if ok:
                        for t in st.targets:
                            if isinstance(t, ast.Name):
                                fn_cvals[t.id] = cv
                if (
                    isinstance(st.value, ast.Call)
                    and isinstance(st.value.func, ast.Name)
                    and st.value.func.id in local_classes
                ):
                    for t in st.targets:
                        if isinstance(t, ast.Name):
                            fn_tenv[t.id] = st.value.func.id
            for sub in ast.walk(st):
                if isinstance(sub, ast.Call) and _py_call_is_direct_observation(
                    sub,
                    env=fn_env,
                    const_vals=fn_cvals,
                    type_env=fn_tenv,
                    py_facts=local_facts,
                ):
                    return True
        return False

    def _def_exit_and_skip(
        d: ast.FunctionDef | ast.AsyncFunctionDef, cur_facts: _PyFileFacts
    ) -> tuple[bool, bool, bool]:
        fn_aliases = dict(cur_facts.import_aliases or {})
        fn_cvals: dict[str, object] = {}
        fn_tenv: dict[str, str] = {}
        for st in d.body:
            _record_py_import_aliases(st, fn_aliases)
            if isinstance(st, ast.Assign):
                ok, cv = _extract_py_static_const(st.value, fn_cvals)
                if ok:
                    for t in st.targets:
                        if isinstance(t, ast.Name):
                            fn_cvals[t.id] = cv
                if (
                    isinstance(st.value, ast.Call)
                    and isinstance(st.value.func, ast.Name)
                    and st.value.func.id in local_classes
                ):
                    for t in st.targets:
                        if isinstance(t, ast.Name):
                            fn_tenv[t.id] = st.value.func.id
        local_facts = _PyFileFacts(
            **{**cur_facts.__dict__, "import_aliases": fn_aliases}
        )
        ex_hit = False
        os_ex_hit = False
        sk_hit = False
        for sub in ast.walk(d):
            if isinstance(sub, ast.Raise) and sub.exc is not None:
                exc_name = _dotted_python_name(
                    sub.exc.func if isinstance(sub.exc, ast.Call) else sub.exc
                ) or ""
                if exc_name == "SkipTest" or exc_name.endswith(".SkipTest"):
                    sk_hit = True
            if isinstance(sub, ast.Call):
                cname = _dotted_python_name(sub.func) or ""
                if (
                    (isinstance(sub.func, ast.Attribute) and sub.func.attr == "skipTest")
                    or cname == "SkipTest"
                    or cname.endswith(".SkipTest")
                ):
                    sk_hit = True
                elif cname in local_facts.skip_fns:
                    sk_hit = True
                elif (
                    isinstance(sub.func, ast.Attribute)
                    and isinstance(sub.func.value, ast.Name)
                    and sub.func.value.id in ("self", "cls")
                    and sub.func.attr in local_facts.self_skip_methods
                ):
                    sk_hit = True
                ex_nd = _py_call_exit_kind(
                    sub, fn_cvals, fn_aliases, py_facts=local_facts, type_env=fn_tenv
                )
                if isinstance(ex_nd, _CfgExit) and ex_nd.is_success:
                    ex_hit = True
                elif isinstance(ex_nd, _CfgBranch):
                    ex_hit = True
                if _py_call_exits_os_success(
                    sub, fn_cvals, fn_aliases, py_facts=local_facts, type_env=fn_tenv
                ):
                    os_ex_hit = True
        return ex_hit, os_ex_hit, sk_hit

    changed = True
    while changed:
        changed = False
        cur_facts = _build_facts()
        for d in (*free_defs, *nested_defs):
            if d is fn_node:
                continue
            if d.name not in observed_fns and _def_calls_observed(d, cur_facts):
                observed_fns.add(d.name)
                changed = True
            d_ex, d_os_ex, d_sk = _def_exit_and_skip(d, cur_facts)
            if d_ex and d.name not in may_exit_fns:
                may_exit_fns.add(d.name)
                changed = True
            if d_os_ex and d.name not in may_os_exit_fns:
                may_os_exit_fns.add(d.name)
                changed = True
            if d_sk and d.name not in skip_fns:
                skip_fns.add(d.name)
                changed = True
            if d.name not in fn_auth:
                d_fam = _def_authority_family(d, cur_facts)
                if d_fam is not None:
                    fn_auth[d.name] = d_fam
                    changed = True
        for cname, ms in class_methods.items():
            for m in ms:
                if m is fn_node:
                    continue
                if m.name not in class_obs[cname] and _def_calls_observed(m, cur_facts):
                    class_obs[cname].add(m.name)
                    changed = True
                m_ex, m_os_ex, m_sk = _def_exit_and_skip(m, cur_facts)
                if m_ex and m.name not in class_may_exit[cname]:
                    class_may_exit[cname].add(m.name)
                    changed = True
                if m_os_ex and m.name not in class_may_os_exit[cname]:
                    class_may_os_exit[cname].add(m.name)
                    changed = True
                if m_sk and m.name not in class_skip[cname]:
                    class_skip[cname].add(m.name)
                    changed = True
                if cname in mro_names:
                    for key in (m.name, f"self.{m.name}", f"cls.{m.name}"):
                        if key not in fn_auth:
                            m_fam = _def_authority_family(m, cur_facts)
                            if m_fam is not None:
                                fn_auth[key] = m_fam
                                changed = True

    final_facts = _build_facts()
    all_def_names = local_defs | {
        m.name for anc in mro_classes for m in class_methods.get(anc.name, ())
    }
    pure_fns = all_def_names - final_facts.observed_fns - final_facts.self_observed_methods
    return final_facts, frozenset(pure_fns)


def _py_call_exits_os_success(
    expr: ast.Call,
    const_vals: dict[str, object],
    aliases: dict[str, str],
    *,
    py_facts: _PyFileFacts | None = None,
    type_env: dict[str, str] | None = None,
) -> bool:
    """Return True if `expr` directly or transitively calls `os._exit(0)`."""
    func = expr.func
    callee = _dotted_python_name(func) or ""
    resolved = _resolve_py_callee(callee, aliases)
    if resolved == "os._exit":
        if expr.args:
            ok, val = _extract_py_static_const(expr.args[0], const_vals)
            if ok and (
                (isinstance(val, int) and not isinstance(val, bool) and val != 0)
                or (isinstance(val, str) and bool(val))
            ):
                return False
        return True
    if py_facts is not None:
        if callee and "." not in callee and callee in py_facts.may_os_exit_success_fns:
            return True
        if isinstance(func, ast.Attribute):
            if (
                isinstance(func.value, ast.Name)
                and func.value.id in ("self", "cls")
                and func.attr in py_facts.self_may_os_exit_methods
            ):
                return True
            recv_cls: str | None = None
            if isinstance(func.value, ast.Name):
                if func.value.id in py_facts.local_classes:
                    recv_cls = func.value.id
                elif type_env and func.value.id in type_env:
                    recv_cls = type_env[func.value.id]
            elif (
                isinstance(func.value, ast.Call)
                and isinstance(func.value.func, ast.Name)
                and func.value.func.id in py_facts.local_classes
            ):
                recv_cls = func.value.func.id
            if recv_cls is not None and func.attr in (
                py_facts.class_may_os_exit_methods or {}
            ).get(recv_cls, frozenset()):
                return True
    return False


def _py_call_exit_kind(
    expr: ast.Call,
    const_vals: dict[str, object],
    aliases: dict[str, str],
    *,
    py_facts: _PyFileFacts | None = None,
    type_env: dict[str, str] | None = None,
) -> object | None:
    """Return `_CfgExit` or `_CfgBranch` if `expr` exits or calls an exit-0 helper."""
    func = expr.func
    if isinstance(func, ast.Attribute) and func.attr.startswith("fail"):
        if (isinstance(func.value, ast.Name) and func.value.id == "self") or (
            isinstance(func.value, ast.Call)
            and isinstance(func.value.func, ast.Name)
            and func.value.func.id == "super"
        ):
            return _CfgExit(is_success=False)
    callee = _dotted_python_name(func) or ""
    resolved = _resolve_py_callee(callee, aliases)
    if resolved in ("sys.exit", "os._exit", "builtins.exit", "builtins.quit", "exit", "quit"):
        if expr.args:
            ok, val = _extract_py_static_const(expr.args[0], const_vals)
            if ok and ((isinstance(val, int) and not isinstance(val, bool) and val != 0) or (isinstance(val, str) and bool(val))):
                return _CfgExit(is_success=False)
        return _CfgExit(is_success=True)
    if py_facts is not None:
        if callee and "." not in callee and callee in py_facts.may_exit_success_fns:
            return _CfgBranch((_CfgExit(is_success=True), _CfgSeq(())))
        if isinstance(func, ast.Attribute):
            if (
                isinstance(func.value, ast.Name)
                and func.value.id in ("self", "cls")
                and func.attr in py_facts.self_may_exit_methods
            ):
                return _CfgBranch((_CfgExit(is_success=True), _CfgSeq(())))
            recv_cls: str | None = None
            if isinstance(func.value, ast.Name):
                if func.value.id in py_facts.local_classes:
                    recv_cls = func.value.id
                elif type_env and func.value.id in type_env:
                    recv_cls = type_env[func.value.id]
            if recv_cls is not None and func.attr in (
                py_facts.class_may_exit_methods or {}
            ).get(recv_cls, frozenset()):
                return _CfgBranch((_CfgExit(is_success=True), _CfgSeq(())))
    return None


def _collect_python_expr_assertions(
    expr: ast.AST,
    assertions: list[_AssertionItem],
    *,
    env: dict[str, str],
    self_attrs: dict[str, str],
    pure_fns: frozenset[str],
    const_vals: dict[str, object] | None = None,
    py_facts: _PyFileFacts | None = None,
    type_env: dict[str, str] | None = None,
    obs_calls: list[bool] | None = None,
    proc_exits: list[bool] | None = None,
    injected_strs: dict[str, str] | None = None,
    auth_env: dict[str, str] | None = None,
    py_exprs: dict[str, str] | None = None,
) -> tuple[bool, list[object]]:
    """Collect `_AssertionItem` values & CFG nodes without descending into lambdas."""
    if isinstance(expr, ast.Lambda):
        return False, []
    cvals = const_vals or {}
    facts = py_facts or _PyFileFacts()
    tenv = type_env or {}
    injs = injected_strs or {}
    aliases = facts.import_aliases or {}
    saw_skip = False
    nodes: list[object] = []

    if isinstance(expr, ast.BoolOp):
        for idx, val in enumerate(expr.values):
            v_skip, v_nodes = _collect_python_expr_assertions(
                val,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=cvals,
                py_facts=facts,
                type_env=tenv,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=injs,
                auth_env=auth_env,
                py_exprs=py_exprs,
            )
            saw_skip |= v_skip
            if v_nodes:
                if idx == 0:
                    nodes.extend(v_nodes)
                else:
                    nodes.append(
                        _CfgBranch((_CfgSeq(tuple(v_nodes)), _CfgSeq(())))
                    )
        return saw_skip, nodes

    if isinstance(expr, ast.IfExp):
        t_skip, t_nodes = _collect_python_expr_assertions(
            expr.test,
            assertions,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            const_vals=cvals,
            py_facts=facts,
            type_env=tenv,
            obs_calls=obs_calls,
            proc_exits=proc_exits,
            injected_strs=injs,
            auth_env=auth_env,
            py_exprs=py_exprs,
        )
        saw_skip |= t_skip
        nodes.extend(t_nodes)
        cond = _eval_python_static_bool(expr.test, cvals)
        if cond is True:
            b_skip, b_nodes = _collect_python_expr_assertions(
                expr.body,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=cvals,
                py_facts=facts,
                type_env=tenv,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=injs,
                auth_env=auth_env,
                py_exprs=py_exprs,
            )
            return saw_skip | b_skip, [*nodes, *b_nodes]
        if cond is False:
            o_skip, o_nodes = _collect_python_expr_assertions(
                expr.orelse,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=cvals,
                py_facts=facts,
                type_env=tenv,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=injs,
                auth_env=auth_env,
                py_exprs=py_exprs,
            )
            return saw_skip | o_skip, [*nodes, *o_nodes]
        b_skip, b_nodes = _collect_python_expr_assertions(
            expr.body,
            assertions,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            const_vals=cvals,
            py_facts=facts,
            type_env=tenv,
            obs_calls=obs_calls,
            proc_exits=proc_exits,
            injected_strs=injs,
            auth_env=auth_env,
            py_exprs=py_exprs,
        )
        o_skip, o_nodes = _collect_python_expr_assertions(
            expr.orelse,
            assertions,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            const_vals=cvals,
            py_facts=facts,
            type_env=tenv,
            obs_calls=obs_calls,
            proc_exits=proc_exits,
            injected_strs=injs,
            auth_env=auth_env,
            py_exprs=py_exprs,
        )
        saw_skip |= b_skip | o_skip
        if b_nodes or o_nodes:
            nodes.append(
                _CfgBranch(
                    (_CfgSeq(tuple(b_nodes)), _CfgSeq(tuple(o_nodes)))
                )
            )
        return saw_skip, nodes

    if isinstance(
        expr, (ast.ListComp, ast.SetComp, ast.GeneratorExp, ast.DictComp)
    ):
        for g_idx, gen in enumerate(expr.generators):
            i_skip, i_nodes = _collect_python_expr_assertions(
                gen.iter,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=cvals,
                py_facts=facts,
                type_env=tenv,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=injs,
                auth_env=auth_env,
                py_exprs=py_exprs,
            )
            saw_skip |= i_skip
            if i_nodes:
                if g_idx == 0:
                    nodes.extend(i_nodes)
                else:
                    nodes.append(
                        _CfgBranch((_CfgSeq(tuple(i_nodes)), _CfgSeq(())))
                    )
            for cond_e in gen.ifs:
                c_skip, c_nodes = _collect_python_expr_assertions(
                    cond_e,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=cvals,
                    py_facts=facts,
                    type_env=tenv,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=injs,
                    auth_env=auth_env,
                    py_exprs=py_exprs,
                )
                saw_skip |= c_skip
                if c_nodes:
                    nodes.append(
                        _CfgBranch((_CfgSeq(tuple(c_nodes)), _CfgSeq(())))
                    )
        body_exprs = (
            (expr.key, expr.value)
            if isinstance(expr, ast.DictComp)
            else (expr.elt,)
        )
        for be in body_exprs:
            b_skip, b_nodes = _collect_python_expr_assertions(
                be,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=cvals,
                py_facts=facts,
                type_env=tenv,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=injs,
                auth_env=auth_env,
                py_exprs=py_exprs,
            )
            saw_skip |= b_skip
            if b_nodes:
                nodes.append(
                    _CfgBranch((_CfgSeq(tuple(b_nodes)), _CfgSeq(())))
                )
        return saw_skip, nodes

    if isinstance(expr, ast.Call):
        fn_name = _dotted_python_name(expr.func) or ""
        if (
            (
                isinstance(expr.func, ast.Attribute)
                and expr.func.attr == "skipTest"
            )
            or fn_name == "SkipTest"
            or fn_name.endswith(".SkipTest")
            or fn_name in facts.skip_fns
            or (
                isinstance(expr.func, ast.Attribute)
                and isinstance(expr.func.value, ast.Name)
                and expr.func.value.id in ("self", "cls")
                and expr.func.attr in facts.self_skip_methods
            )
        ):
            saw_skip = True
        else:
            if proc_exits is not None and _py_call_exits_os_success(
                expr, cvals, aliases, py_facts=facts, type_env=tenv
            ):
                proc_exits.append(True)
            if (
                obs_calls is not None
                and not _is_python_assertion_call(expr)
                and _py_call_is_direct_observation(
                    expr,
                    env=env,
                    const_vals=cvals,
                    type_env=tenv,
                    py_facts=facts,
                )
            ):
                obs_calls.append(True)
            exit_nd = _py_call_exit_kind(
                expr, cvals, aliases, py_facts=facts, type_env=tenv
            )
            if exit_nd is not None:
                nodes.append(exit_nd)
            elif _is_python_assertion_call(expr):
                bound_args = _bind_unittest_call_args(expr)
                tested_tuple = ast.Tuple(
                    elts=(
                        [a for a in bound_args if isinstance(a, ast.expr)]
                        if bound_args is not None
                        else [
                            *expr.args,
                            *(kw.value for kw in expr.keywords if kw.arg != "msg"),
                        ]
                    ),
                    ctx=ast.Load(),
                )
                snap_env = dict(env)
                snap_self = dict(self_attrs)
                snap_vals = dict(cvals)
                snap_tenv = dict(tenv)
                snap_injs = dict(injs)
                snap_auth = dict(auth_env) if auth_env is not None else None
                snap_exprs = dict(py_exprs) if py_exprs is not None else None
                is_obs = _py_expr_ast_is_observed(
                    tested_tuple,
                    env=snap_env,
                    self_attrs=snap_self,
                    pure_fns=pure_fns,
                    py_facts=facts,
                    const_vals=snap_vals,
                    type_env=snap_tenv,
                    is_assertion_context=True,
                )
                item = _AssertionItem(
                    full_span=ast.unparse(expr),
                    tested_expr=ast.unparse(tested_tuple),
                    is_observed=is_obs,
                    py_env=snap_env,
                    py_const_vals=snap_vals,
                    py_injected_strs=snap_injs,
                    py_self_attrs=snap_self,
                    py_type_env=snap_tenv,
                    py_facts=facts,
                    pure_py_fns=pure_fns,
                    py_auth_env=snap_auth,
                    py_exprs=snap_exprs,
                )
                assertions.append(item)
                nodes.append(_CfgItem(item))
    for child in ast.iter_child_nodes(expr):
        c_skip, c_nodes = _collect_python_expr_assertions(
            child,
            assertions,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            const_vals=cvals,
            py_facts=facts,
            type_env=tenv,
            obs_calls=obs_calls,
            proc_exits=proc_exits,
            injected_strs=injs,
            auth_env=auth_env,
            py_exprs=py_exprs,
        )
        saw_skip |= c_skip
        nodes.extend(c_nodes)
    return saw_skip, nodes


def _py_iter_is_statically_non_empty(
    node: ast.expr, const_vals: dict[str, object]
) -> bool:
    """Return True iff a Python `for` iterable is statically guaranteed >= 1 item."""
    ok, val = _extract_py_static_const(node, const_vals)
    if (
        ok
        and isinstance(val, (tuple, list, set, frozenset, dict, str, bytes))
        and len(val) > 0
    ):
        return True
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return any(not isinstance(e, ast.Starred) for e in node.elts)
    if isinstance(node, ast.Dict):
        return any(k is not None for k in node.keys)
    if isinstance(node, ast.Call) and not node.keywords:
        callee = _dotted_python_name(node.func) or ""
        if callee in ("range", "builtins.range") and 1 <= len(node.args) <= 3:
            r_args: list[int] = []
            for a in node.args:
                a_ok, a_val = _extract_py_static_const(a, const_vals)
                if (
                    not a_ok
                    or not isinstance(a_val, int)
                    or isinstance(a_val, bool)
                ):
                    return False
                r_args.append(a_val)
            if len(r_args) == 3 and r_args[2] == 0:
                return False
            return len(range(*r_args)) > 0
    return False


def _meet_str_dicts_intersection(
    pre: dict[str, str], branch_maps: list[dict[str, str]]
) -> dict[str, str]:
    """Keep keys bound identically across all live branch maps."""
    if not branch_maps:
        return dict(pre)
    merged: dict[str, str] = {}
    all_keys = set(pre.keys()) | set().union(*(b.keys() for b in branch_maps))
    for k in all_keys:
        vals = [b.get(k) for b in branch_maps]
        if vals and vals[0] is not None and all(v == vals[0] for v in vals):
            merged[k] = vals[0]
    return merged


def _meet_py_state(
    pre: tuple[dict[str, str], dict[str, object], dict[str, str]],
    branches: list[tuple[dict[str, str], dict[str, object], dict[str, str]]],
) -> tuple[dict[str, str], dict[str, object], dict[str, str]]:
    if not branches:
        return dict(pre[0]), dict(pre[1]), dict(pre[2])
    out_env: dict[str, str] = {}
    for k in set().union(*(b[0].keys() for b in branches)):
        if all(b[0].get(k) == "observed" for b in branches):
            out_env[k] = "observed"
        elif all(b[0].get(k) == "cmd_approved" for b in branches):
            out_env[k] = "cmd_approved"
        elif any(b[0].get(k) == "const" for b in branches):
            out_env[k] = "const"
    out_self: dict[str, str] = {}
    for k in set().union(*(b[2].keys() for b in branches)):
        if all(b[2].get(k) == "observed" for b in branches):
            out_self[k] = "observed"
        elif any(b[2].get(k) == "const" for b in branches):
            out_self[k] = "const"
    out_vals: dict[str, object] = {}
    for k in pre[1]:
        if all(k in b[1] and b[1][k] == pre[1][k] for b in branches):
            out_vals[k] = pre[1][k]
    return out_env, out_vals, out_self


def _meet_py_injected_strs(
    branch_injs: list[dict[str, str]],
) -> dict[str, str]:
    if not branch_injs:
        return {}
    out: dict[str, str] = {}
    for k in set().union(*(d.keys() for d in branch_injs)):
        seen: list[str] = []
        for d in branch_injs:
            v = d.get(k, "")
            if v and v not in seen:
                seen.append(v)
        if seen:
            out[k] = "\n".join(seen)
    return out


def _py_iter_is_statically_empty(
    node: ast.expr, const_vals: dict[str, object]
) -> bool:
    """Return True if a Python `for` iterable is statically empty."""
    ok, val = _extract_py_static_const(node, const_vals)
    if (
        ok
        and isinstance(val, (tuple, list, set, frozenset, dict, str, bytes))
        and len(val) == 0
    ):
        return True
    if isinstance(node, ast.Call) and not node.keywords:
        callee = _dotted_python_name(node.func) or ""
        if (
            callee
            in ("tuple", "list", "set", "frozenset", "dict", "str", "bytes")
            and not node.args
        ):
            return True
        if callee in ("range", "builtins.range") and 1 <= len(node.args) <= 3:
            r_args: list[int] = []
            for a in node.args:
                a_ok, a_val = _extract_py_static_const(a, const_vals)
                if (
                    not a_ok
                    or not isinstance(a_val, int)
                    or isinstance(a_val, bool)
                ):
                    return False
                r_args.append(a_val)
            if len(r_args) == 3 and r_args[2] == 0:
                return False
            return len(range(*r_args)) == 0
    return False


def _py_with_item_swallows_assertions(ctx_expr: ast.expr) -> bool:
    """Return True for `with self.assertRaises*(...):` / `suppress(...)`."""
    if not isinstance(ctx_expr, ast.Call):
        return False
    callee = _dotted_python_name(ctx_expr.func) or ""
    tail = (
        ctx_expr.func.attr
        if isinstance(ctx_expr.func, ast.Attribute)
        else callee
    )
    if tail.startswith("assertRaises"):
        return True
    if tail == "suppress" or callee in ("contextlib.suppress", "suppress"):
        return True
    return False


def _py_handler_may_catch_assertion_error(exc_type: ast.expr | None) -> bool:
    """Return True if `except <exc_type>:` can catch `AssertionError`."""
    if exc_type is None:
        return True
    if isinstance(exc_type, ast.Tuple):
        return any(
            _py_handler_may_catch_assertion_error(elt)
            for elt in exc_type.elts
        )
    dname = _dotted_python_name(exc_type)
    if dname is None:
        return True
    short = dname.rsplit(".", 1)[-1]
    return short in (
        "AssertionError",
        "Exception",
        "BaseException",
        "failureException",
    )


def _py_stmts_unconditionally_reraise(stmts: list[ast.stmt]) -> bool:
    """Return True if every execution path through `stmts` raises."""
    for st in stmts:
        if isinstance(st, ast.Raise):
            return True
        if isinstance(st, ast.If):
            if st.orelse and (
                _py_stmts_unconditionally_reraise(st.body)
                and _py_stmts_unconditionally_reraise(st.orelse)
            ):
                return True
    return False


def _extract_py_match_pattern_names(pat: ast.AST) -> list[str]:
    """Return local variable names bound by an `ast.Match` pattern."""
    names: list[str] = []
    match_as = getattr(ast, "MatchAs", None)
    match_star = getattr(ast, "MatchStar", None)
    match_map = getattr(ast, "MatchMapping", None)
    for sub in ast.walk(pat):
        if (
            match_as is not None
            and isinstance(sub, match_as)
            and isinstance(sub.name, str)
        ):
            names.append(sub.name)
        elif (
            match_star is not None
            and isinstance(sub, match_star)
            and isinstance(sub.name, str)
        ):
            names.append(sub.name)
        elif (
            match_map is not None
            and isinstance(sub, match_map)
            and isinstance(sub.rest, str)
        ):
            names.append(sub.rest)
    return names


def _collect_py_assigned_names(stmts: list[ast.stmt]) -> set[str]:
    """Collect variable names reassigned inside `stmts` (same scope, no inner defs)."""
    names: set[str] = set()

    def _add_target(tgt: ast.AST) -> None:
        if isinstance(tgt, ast.Name):
            names.add(tgt.id)
        elif isinstance(tgt, (ast.Tuple, ast.List)):
            for elt in tgt.elts:
                _add_target(elt)
        elif isinstance(tgt, ast.Starred):
            _add_target(tgt.value)

    def _scan_expr(expr: ast.AST | None) -> None:
        if expr is None:
            return
        stack: list[ast.AST] = [expr]
        while stack:
            cur = stack.pop()
            if isinstance(cur, ast.Lambda):
                continue
            if isinstance(cur, ast.NamedExpr):
                _add_target(cur.target)
            stack.extend(ast.iter_child_nodes(cur))

    def _walk(body: list[ast.stmt]) -> None:
        for st in body:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                names.add(st.name)
                continue
            if isinstance(st, (ast.Import, ast.ImportFrom)):
                for al in st.names:
                    if al.name == "*":
                        continue
                    bound = (
                        al.asname or al.name.split(".", 1)[0]
                        if isinstance(st, ast.Import)
                        else (al.asname or al.name)
                    )
                    names.add(bound)
                continue
            if isinstance(st, (ast.Global, ast.Nonlocal)):
                names.update(st.names)
                continue
            if isinstance(st, ast.Assign):
                _scan_expr(st.value)
                for t in st.targets:
                    _add_target(t)
            elif isinstance(st, ast.AugAssign):
                _scan_expr(st.value)
                _add_target(st.target)
            elif isinstance(st, ast.AnnAssign):
                _scan_expr(st.value)
                if st.value is not None:
                    _add_target(st.target)
            elif isinstance(st, ast.Delete):
                for t in st.targets:
                    _add_target(t)
            elif isinstance(st, (ast.For, ast.AsyncFor)):
                _scan_expr(st.iter)
                _add_target(st.target)
                _walk(st.body)
                _walk(st.orelse)
            elif isinstance(st, ast.While):
                _scan_expr(st.test)
                _walk(st.body)
                _walk(st.orelse)
            elif isinstance(st, ast.If):
                _scan_expr(st.test)
                _walk(st.body)
                _walk(st.orelse)
            elif isinstance(st, (ast.With, ast.AsyncWith)):
                for it in st.items:
                    _scan_expr(it.context_expr)
                    if it.optional_vars is not None:
                        _add_target(it.optional_vars)
                _walk(st.body)
            elif isinstance(st, ast.Try) or (
                hasattr(ast, "TryStar") and isinstance(st, ast.TryStar)
            ):
                _walk(st.body)
                for h in st.handlers:
                    if isinstance(h.name, str):
                        names.add(h.name)
                    _walk(h.body)
                _walk(st.orelse)
                _walk(st.finalbody)
            elif hasattr(ast, "Match") and isinstance(st, ast.Match):
                _scan_expr(st.subject)
                for case in st.cases:
                    names.update(_extract_py_match_pattern_names(case.pattern))
                    _scan_expr(case.guard)
                    _walk(case.body)
            else:
                for ch in ast.iter_child_nodes(st):
                    if isinstance(ch, ast.expr):
                        _scan_expr(ch)

    _walk(stmts)
    return names


def _bind_py_auth_and_expr(
    target: ast.AST,
    rhs: ast.expr | None,
    *,
    auth_env: dict[str, str],
    py_exprs: dict[str, str],
    const_vals: dict[str, object],
    py_facts: _PyFileFacts,
) -> None:
    """Propagate Python variable/self.<attr> authority family and AST source."""
    fam = (
        _py_expr_authority_family(
            rhs,
            auth_env=auth_env,
            const_vals=const_vals,
            py_facts=py_facts,
            py_exprs=py_exprs,
        )
        if rhs is not None
        else None
    )
    rhs_src = ast.unparse(rhs) if rhs is not None else None
    if isinstance(target, ast.Name):
        if fam is not None:
            auth_env[target.id] = fam
        else:
            auth_env.pop(target.id, None)
        if rhs_src is not None:
            py_exprs[target.id] = rhs_src
        else:
            py_exprs.pop(target.id, None)
    elif (
        isinstance(target, ast.Attribute)
        and isinstance(target.value, ast.Name)
        and target.value.id == "self"
    ):
        skey = f"self.{target.attr}"
        if fam is not None:
            auth_env[skey] = fam
        else:
            auth_env.pop(skey, None)
    elif isinstance(target, (ast.Tuple, ast.List)):
        for elt in target.elts:
            inner = elt.value if isinstance(elt, ast.Starred) else elt
            for leaf in _iter_py_assign_targets(inner):
                if isinstance(leaf, ast.Name):
                    auth_env.pop(leaf.id, None)
                    py_exprs.pop(leaf.id, None)
                elif (
                    isinstance(leaf, ast.Attribute)
                    and isinstance(leaf.value, ast.Name)
                    and leaf.value.id == "self"
                ):
                    auth_env.pop(f"self.{leaf.attr}", None)


def _collect_python_stmt_assertions(
    stmts: list[ast.stmt],
    assertions: list[_AssertionItem],
    *,
    env: dict[str, str],
    const_vals: dict[str, object],
    self_attrs: dict[str, str],
    pure_fns: frozenset[str],
    py_facts: _PyFileFacts | None = None,
    type_env: dict[str, str] | None = None,
    obs_calls: list[bool] | None = None,
    proc_exits: list[bool] | None = None,
    injected_strs: dict[str, str] | None = None,
    auth_env: dict[str, str] | None = None,
    py_exprs: dict[str, str] | None = None,
) -> tuple[bool, bool, object]:
    """Walk reachable Python statements, tracking skip/exit, dataflow & CFG."""
    saw_skip = False
    base_facts = py_facts or _PyFileFacts()
    cur_aliases = dict(base_facts.import_aliases or {})
    cur_types = type_env if type_env is not None else {}
    cur_inj = injected_strs if injected_strs is not None else {}
    cur_auth = auth_env if auth_env is not None else {}
    cur_exprs = py_exprs if py_exprs is not None else {}

    def _cur_facts() -> _PyFileFacts:
        return _PyFileFacts(
            **{**base_facts.__dict__, "import_aliases": dict(cur_aliases)}
        )

    def _bind_inj(tgt: ast.AST, inj_val: str) -> None:
        if isinstance(tgt, ast.Name):
            if inj_val:
                cur_inj[tgt.id] = inj_val
            else:
                cur_inj.pop(tgt.id, None)
        elif (
            isinstance(tgt, ast.Attribute)
            and isinstance(tgt.value, ast.Name)
            and tgt.value.id == "self"
        ):
            skey = f"self.{tgt.attr}"
            if inj_val:
                cur_inj[skey] = inj_val
            else:
                cur_inj.pop(skey, None)
        elif isinstance(tgt, (ast.Tuple, ast.List)):
            for elt in tgt.elts:
                _bind_inj(elt.value if isinstance(elt, ast.Starred) else elt, inj_val)

    def _rhs_class(expr: ast.expr) -> str | None:
        if (
            isinstance(expr, ast.Call)
            and isinstance(expr.func, ast.Name)
            and expr.func.id in base_facts.local_classes
        ):
            return expr.func.id
        return None

    seq_nodes: list[object] = []
    for stmt in stmts:
        if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            env.pop(stmt.name, None)
            const_vals.pop(stmt.name, None)
            cur_types.pop(stmt.name, None)
            cur_aliases.pop(stmt.name, None)
            cur_inj.pop(stmt.name, None)
            cur_auth.pop(stmt.name, None)
            cur_exprs.pop(stmt.name, None)
            continue
        if isinstance(stmt, (ast.Import, ast.ImportFrom)):
            _record_py_import_aliases(stmt, cur_aliases)
            # Clear any stale `env` entry shadowed by a local import.
            for al in stmt.names:
                if al.name == "*":
                    continue
                bound = (
                    al.asname or al.name.split(".", 1)[0]
                    if isinstance(stmt, ast.Import)
                    else (al.asname or al.name)
                )
                env.pop(bound, None)
                const_vals.pop(bound, None)
                cur_types.pop(bound, None)
                cur_inj.pop(bound, None)
                cur_auth.pop(bound, None)
                cur_exprs.pop(bound, None)
            continue
        if isinstance(stmt, ast.Assert):
            facts_snap = _cur_facts()
            snap_env = dict(env)
            snap_self = dict(self_attrs)
            snap_vals = dict(const_vals)
            snap_tenv = dict(cur_types)
            snap_inj = dict(cur_inj)
            snap_auth = dict(cur_auth)
            snap_exprs = dict(cur_exprs)
            is_obs = _py_expr_ast_is_observed(
                stmt.test,
                env=snap_env,
                self_attrs=snap_self,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=snap_vals,
                type_env=snap_tenv,
                is_assertion_context=True,
            )
            item = _AssertionItem(
                full_span=ast.unparse(stmt),
                tested_expr=ast.unparse(stmt.test),
                is_observed=is_obs,
                py_env=snap_env,
                py_const_vals=snap_vals,
                py_injected_strs=snap_inj,
                py_self_attrs=snap_self,
                py_type_env=snap_tenv,
                py_facts=facts_snap,
                pure_py_fns=pure_fns,
                py_auth_env=snap_auth,
                py_exprs=snap_exprs,
            )
            assertions.append(item)
            e_skip, e_nodes = _collect_python_expr_assertions(
                stmt.test,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= e_skip
            seq_nodes.extend(e_nodes)
            if _eval_python_static_bool(stmt.test, const_vals) is False:
                seq_nodes.append(_CfgExit(is_success=False))
                return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            seq_nodes.append(_CfgItem(item))
            if stmt.msg is not None:
                m_skip, m_nodes = _collect_python_expr_assertions(
                    stmt.msg,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= m_skip
                seq_nodes.extend(m_nodes)
            continue
        if isinstance(stmt, ast.Assign):
            facts_snap = _cur_facts()
            e_skip, e_nodes = _collect_python_expr_assertions(
                stmt.value,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= e_skip
            seq_nodes.extend(e_nodes)
            obs = _py_expr_ast_is_observed(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            )
            if obs:
                status = "observed"
            elif _py_subprocess_cmd_is_approved(
                stmt.value,
                env=env,
                const_vals=const_vals,
                aliases=cur_aliases,
            ):
                status = "cmd_approved"
            else:
                status = "const"
            rc = _extract_py_static_const(stmt.value, const_vals)
            rcls = _rhs_class(stmt.value)
            rhs_inj = (
                _py_expr_unobserved_str_parts(
                    stmt.value,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    const_vals=const_vals,
                    type_env=cur_types,
                    injected_strs=cur_inj,
                )
                if status == "observed"
                else ""
            )
            for tgt in stmt.targets:
                if (
                    isinstance(tgt, (ast.Tuple, ast.List))
                    and isinstance(stmt.value, (ast.Tuple, ast.List))
                    and len(tgt.elts) == len(stmt.value.elts)
                    and not any(isinstance(e, ast.Starred) for e in tgt.elts)
                ):
                    elt_updates: list[tuple[ast.AST, str, tuple[bool, object], str | None, str]] = []
                    for t_elt, v_elt in zip(tgt.elts, stmt.value.elts):
                        e_obs = _py_expr_ast_is_observed(
                            v_elt,
                            env=env,
                            self_attrs=self_attrs,
                            pure_fns=pure_fns,
                            py_facts=facts_snap,
                            const_vals=const_vals,
                            type_env=cur_types,
                        )
                        if e_obs:
                            e_st = "observed"
                        elif _py_subprocess_cmd_is_approved(
                            v_elt,
                            env=env,
                            const_vals=const_vals,
                            aliases=cur_aliases,
                        ):
                            e_st = "cmd_approved"
                        else:
                            e_st = "const"
                        e_inj = (
                            _py_expr_unobserved_str_parts(
                                v_elt,
                                env=env,
                                self_attrs=self_attrs,
                                pure_fns=pure_fns,
                                py_facts=facts_snap,
                                const_vals=const_vals,
                                type_env=cur_types,
                                injected_strs=cur_inj,
                            )
                            if e_st == "observed"
                            else ""
                        )
                        elt_updates.append(
                            (
                                t_elt,
                                e_st,
                                _extract_py_static_const(v_elt, const_vals),
                                _rhs_class(v_elt),
                                e_inj,
                            )
                        )
                    for t_elt, e_st, e_rc, e_rcls, e_inj in elt_updates:
                        _bind_py_target(
                            t_elt,
                            e_st,
                            e_rc,
                            env,
                            const_vals,
                            self_attrs,
                            type_env=cur_types,
                            rhs_cls=e_rcls,
                        )
                        _bind_inj(t_elt, e_inj)
                    for t_elt, v_elt in zip(tgt.elts, stmt.value.elts):
                        _bind_py_auth_and_expr(
                            t_elt,
                            v_elt,
                            auth_env=cur_auth,
                            py_exprs=cur_exprs,
                            const_vals=const_vals,
                            py_facts=facts_snap,
                        )
                    continue
                _bind_py_target(
                    tgt,
                    status,
                    rc,
                    env,
                    const_vals,
                    self_attrs,
                    type_env=cur_types,
                    rhs_cls=rcls,
                )
                _bind_inj(tgt, rhs_inj)
                _bind_py_auth_and_expr(
                    tgt,
                    stmt.value,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                )
            continue
        if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            facts_snap = _cur_facts()
            e_skip, e_nodes = _collect_python_expr_assertions(
                stmt.value,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
            )
            saw_skip |= e_skip
            seq_nodes.extend(e_nodes)
            obs = _py_expr_ast_is_observed(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            )
            if obs:
                status = "observed"
            elif _py_subprocess_cmd_is_approved(
                stmt.value,
                env=env,
                const_vals=const_vals,
                aliases=cur_aliases,
            ):
                status = "cmd_approved"
            else:
                status = "const"
            rc = _extract_py_static_const(stmt.value, const_vals)
            rhs_inj = (
                _py_expr_unobserved_str_parts(
                    stmt.value,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    const_vals=const_vals,
                    type_env=cur_types,
                    injected_strs=cur_inj,
                )
                if status == "observed"
                else ""
            )
            _bind_py_target(
                stmt.target,
                status,
                rc,
                env,
                const_vals,
                self_attrs,
                type_env=cur_types,
                rhs_cls=_rhs_class(stmt.value),
            )
            _bind_inj(stmt.target, rhs_inj)
            _bind_py_auth_and_expr(
                stmt.target,
                stmt.value,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
                const_vals=const_vals,
                py_facts=facts_snap,
            )
            continue
        if isinstance(stmt, ast.AugAssign):
            facts_snap = _cur_facts()
            e_skip, e_nodes = _collect_python_expr_assertions(
                stmt.value,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
            )
            saw_skip |= e_skip
            seq_nodes.extend(e_nodes)
            obs = _py_expr_ast_is_observed(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            ) or _py_expr_ast_is_observed(
                stmt.target,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            )
            if obs:
                status = "observed"
            elif (
                isinstance(stmt.target, ast.Name)
                and env.get(stmt.target.id) == "cmd_approved"
                and not (
                    isinstance(stmt.value, (ast.List, ast.Tuple))
                    and any(
                        _extract_py_static_const(e, const_vals) in ((True, "-c"), (True, "-e"))
                        for e in stmt.value.elts
                    )
                )
            ):
                status = "cmd_approved"
            else:
                status = "const"
            prev_inj = ""
            if isinstance(stmt.target, ast.Name):
                prev_inj = cur_inj.get(stmt.target.id, "") or (
                    str(const_vals[stmt.target.id])
                    if isinstance(const_vals.get(stmt.target.id), str)
                    else ""
                )
            elif (
                isinstance(stmt.target, ast.Attribute)
                and isinstance(stmt.target.value, ast.Name)
                and stmt.target.value.id == "self"
            ):
                prev_inj = cur_inj.get(f"self.{stmt.target.attr}", "")
            add_inj = _py_expr_unobserved_str_parts(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
                injected_strs=cur_inj,
            )
            _bind_py_target(
                stmt.target,
                status,
                (False, None),
                env,
                const_vals,
                self_attrs,
                type_env=cur_types,
            )
            _bind_inj(stmt.target, f"{prev_inj}{add_inj}" if obs else "")
            _bind_py_auth_and_expr(
                stmt.target,
                None,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
                const_vals=const_vals,
                py_facts=facts_snap,
            )
            continue
        if isinstance(stmt, ast.Delete):
            for tgt in stmt.targets:
                if isinstance(tgt, ast.Name):
                    env.pop(tgt.id, None)
                    const_vals.pop(tgt.id, None)
                    cur_types.pop(tgt.id, None)
                    cur_inj.pop(tgt.id, None)
                    cur_auth.pop(tgt.id, None)
                    cur_exprs.pop(tgt.id, None)
            continue
        if isinstance(stmt, ast.Break):
            seq_nodes.append(_CfgLoopJump("break"))
            return saw_skip, True, _CfgSeq(tuple(seq_nodes))
        if isinstance(stmt, ast.Continue):
            seq_nodes.append(_CfgLoopJump("continue"))
            return saw_skip, True, _CfgSeq(tuple(seq_nodes))
        if isinstance(stmt, ast.Raise):
            facts_snap = _cur_facts()
            exc_name = ""
            if isinstance(stmt.exc, ast.Call):
                exc_name = _dotted_python_name(stmt.exc.func) or ""
                e_skip, e_nodes = _collect_python_expr_assertions(
                    stmt.exc,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.extend(e_nodes)
            elif stmt.exc is not None:
                exc_name = _dotted_python_name(stmt.exc) or ""
                e_skip, e_nodes = _collect_python_expr_assertions(
                    stmt.exc,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.extend(e_nodes)
            if exc_name == "SkipTest" or exc_name.endswith(".SkipTest"):
                saw_skip = True
            seq_nodes.append(_CfgExit(is_success=False))
            return saw_skip, True, _CfgSeq(tuple(seq_nodes))
        if isinstance(stmt, ast.Return):
            facts_snap = _cur_facts()
            if stmt.value is not None:
                e_skip, e_nodes = _collect_python_expr_assertions(
                    stmt.value,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.extend(e_nodes)
            seq_nodes.append(_CfgExit(is_success=True))
            return saw_skip, True, _CfgSeq(tuple(seq_nodes))
        if isinstance(stmt, ast.If):
            facts_snap = _cur_facts()
            t_skip, t_nodes = _collect_python_expr_assertions(
                stmt.test,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= t_skip
            seq_nodes.extend(t_nodes)
            cond = _eval_python_static_bool(stmt.test, const_vals)
            if cond is True:
                b_skip, b_exit, b_cfg = _collect_python_stmt_assertions(
                    stmt.body,
                    assertions,
                    env=env,
                    const_vals=const_vals,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= b_skip
                seq_nodes.append(b_cfg)
                if b_exit:
                    return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            elif cond is False:
                e_skip, e_exit, e_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    assertions,
                    env=env,
                    const_vals=const_vals,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.append(e_cfg)
                if e_exit:
                    return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            else:
                b_st = (dict(env), dict(const_vals), dict(self_attrs))
                e_st = (dict(env), dict(const_vals), dict(self_attrs))
                b_inj = dict(cur_inj)
                e_inj = dict(cur_inj)
                b_auth = dict(cur_auth)
                e_auth = dict(cur_auth)
                b_exprs = dict(cur_exprs)
                e_exprs = dict(cur_exprs)
                b_skip, b_exit, b_cfg = _collect_python_stmt_assertions(
                    stmt.body,
                    assertions,
                    env=b_st[0],
                    const_vals=b_st[1],
                    self_attrs=b_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=b_inj,
                    auth_env=b_auth,
                    py_exprs=b_exprs,
                )
                e_skip, e_exit, e_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    assertions,
                    env=e_st[0],
                    const_vals=e_st[1],
                    self_attrs=e_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=e_inj,
                    auth_env=e_auth,
                    py_exprs=e_exprs,
                )
                saw_skip |= b_skip | e_skip
                seq_nodes.append(_CfgBranch((b_cfg, e_cfg)))
                if b_exit and e_exit:
                    return saw_skip, True, _CfgSeq(tuple(seq_nodes))
                live_b = [
                    st for st, ex in ((b_st, b_exit), (e_st, e_exit)) if not ex
                ]
                live_inj = [
                    d for d, ex in ((b_inj, b_exit), (e_inj, e_exit)) if not ex
                ]
                live_auth = [
                    d for d, ex in ((b_auth, b_exit), (e_auth, e_exit)) if not ex
                ]
                live_exprs = [
                    d
                    for d, ex in ((b_exprs, b_exit), (e_exprs, e_exit))
                    if not ex
                ]
                m_env, m_vals, m_self = _meet_py_state(
                    (env, const_vals, self_attrs), live_b
                )
                env.clear()
                env.update(m_env)
                const_vals.clear()
                const_vals.update(m_vals)
                self_attrs.clear()
                self_attrs.update(m_self)
                m_inj = _meet_py_injected_strs(live_inj)
                cur_inj.clear()
                cur_inj.update(m_inj)
                pre_asnap = dict(cur_auth)
                cur_auth.clear()
                cur_auth.update(
                    _meet_str_dicts_intersection(pre_asnap, live_auth)
                )
                pre_exsnap = dict(cur_exprs)
                cur_exprs.clear()
                cur_exprs.update(
                    _meet_str_dicts_intersection(pre_exsnap, live_exprs)
                )
            continue
        if isinstance(stmt, ast.While):
            facts_snap = _cur_facts()
            t_skip, t_nodes = _collect_python_expr_assertions(
                stmt.test,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= t_skip
            seq_nodes.extend(t_nodes)
            w_cond = _eval_python_static_bool(stmt.test, const_vals)
            if w_cond is False:
                e_skip, e_exit, e_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    assertions,
                    env=env,
                    const_vals=const_vals,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.append(e_cfg)
                if e_exit:
                    return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            else:
                loop_assigned = _collect_py_assigned_names(stmt.body)
                loop_consts = {
                    k: v
                    for k, v in const_vals.items()
                    if k not in loop_assigned
                }
                w_iter_cond = _eval_python_static_bool(stmt.test, loop_consts)
                pre_st = (dict(env), dict(const_vals), dict(self_attrs))
                b_st = (dict(env), dict(loop_consts), dict(self_attrs))
                pre_inj = dict(cur_inj)
                b_inj = dict(cur_inj)
                pre_auth = dict(cur_auth)
                b_auth = dict(cur_auth)
                pre_exprs = dict(cur_exprs)
                b_exprs = dict(cur_exprs)
                b_skip, _, b_cfg = _collect_python_stmt_assertions(
                    stmt.body,
                    assertions,
                    env=b_st[0],
                    const_vals=b_st[1],
                    self_attrs=b_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=b_inj,
                    auth_env=b_auth,
                    py_exprs=b_exprs,
                )
                e_st = (dict(env), dict(const_vals), dict(self_attrs))
                e_inj = dict(cur_inj)
                e_auth = dict(cur_auth)
                e_exprs = dict(cur_exprs)
                e_skip, _, e_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    assertions,
                    env=e_st[0],
                    const_vals=e_st[1],
                    self_attrs=e_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=e_inj,
                    auth_env=e_auth,
                    py_exprs=e_exprs,
                )
                saw_skip |= b_skip | e_skip
                seq_nodes.append(
                    _CfgLoop(
                        body=b_cfg,
                        guaranteed_at_least_once=(w_cond is True),
                        is_infinite=(w_iter_cond is True),
                        orelse=e_cfg if stmt.orelse else None,
                    )
                )
                m_env, m_vals, m_self = _meet_py_state(pre_st, [pre_st, b_st, e_st])
                env.clear()
                env.update(m_env)
                const_vals.clear()
                const_vals.update(m_vals)
                self_attrs.clear()
                self_attrs.update(m_self)
                m_inj = _meet_py_injected_strs([pre_inj, b_inj, e_inj])
                cur_inj.clear()
                cur_inj.update(m_inj)
                cur_auth.clear()
                cur_auth.update(
                    _meet_str_dicts_intersection(
                        pre_auth, [pre_auth, b_auth, e_auth]
                    )
                )
                cur_exprs.clear()
                cur_exprs.update(
                    _meet_str_dicts_intersection(
                        pre_exprs, [pre_exprs, b_exprs, e_exprs]
                    )
                )
            continue
        if isinstance(stmt, (ast.For, ast.AsyncFor)):
            facts_snap = _cur_facts()
            i_skip, i_nodes = _collect_python_expr_assertions(
                stmt.iter,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= i_skip
            seq_nodes.extend(i_nodes)
            if _py_iter_is_statically_empty(stmt.iter, const_vals):
                e_skip, e_exit, e_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    assertions,
                    env=env,
                    const_vals=const_vals,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= e_skip
                seq_nodes.append(e_cfg)
                if e_exit:
                    return saw_skip, True, _CfgSeq(tuple(seq_nodes))
                continue
            iter_obs = _py_expr_ast_is_observed(
                stmt.iter,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            )
            iter_inj = (
                _py_expr_unobserved_str_parts(
                    stmt.iter,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    const_vals=const_vals,
                    type_env=cur_types,
                    injected_strs=cur_inj,
                )
                if iter_obs
                else ""
            )
            guar_once = _py_iter_is_statically_non_empty(stmt.iter, const_vals)
            pre_st = (dict(env), dict(const_vals), dict(self_attrs))
            b_st = (dict(env), dict(const_vals), dict(self_attrs))
            pre_inj = dict(cur_inj)
            b_inj = dict(cur_inj)
            pre_auth = dict(cur_auth)
            b_auth = dict(cur_auth)
            pre_exprs = dict(cur_exprs)
            b_exprs = dict(cur_exprs)
            for tgt_leaf in ast.walk(stmt.target):
                if isinstance(tgt_leaf, ast.Name):
                    b_auth.pop(tgt_leaf.id, None)
                    b_exprs.pop(tgt_leaf.id, None)
            if isinstance(stmt.target, ast.Name):
                if iter_inj:
                    b_inj[stmt.target.id] = iter_inj
                else:
                    b_inj.pop(stmt.target.id, None)
            _bind_py_target(
                stmt.target,
                "observed" if iter_obs else "const",
                (False, None),
                b_st[0],
                b_st[1],
                b_st[2],
            )
            b_skip, _, b_cfg = _collect_python_stmt_assertions(
                stmt.body,
                assertions,
                env=b_st[0],
                const_vals=b_st[1],
                self_attrs=b_st[2],
                pure_fns=pure_fns,
                py_facts=facts_snap,
                type_env=dict(cur_types),
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=b_inj,
                auth_env=b_auth,
                py_exprs=b_exprs,
            )
            e_st = (dict(env), dict(const_vals), dict(self_attrs))
            e_inj = dict(cur_inj)
            e_auth = dict(cur_auth)
            e_exprs = dict(cur_exprs)
            e_skip, _, e_cfg = _collect_python_stmt_assertions(
                stmt.orelse,
                assertions,
                env=e_st[0],
                const_vals=e_st[1],
                self_attrs=e_st[2],
                pure_fns=pure_fns,
                py_facts=facts_snap,
                type_env=dict(cur_types),
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=e_inj,
                auth_env=e_auth,
                py_exprs=e_exprs,
            )
            saw_skip |= b_skip | e_skip
            seq_nodes.append(
                _CfgLoop(
                    body=b_cfg,
                    guaranteed_at_least_once=guar_once,
                    is_infinite=False,
                    orelse=e_cfg if stmt.orelse else None,
                )
            )
            m_env, m_vals, m_self = _meet_py_state(pre_st, [pre_st, b_st, e_st])
            env.clear()
            env.update(m_env)
            const_vals.clear()
            const_vals.update(m_vals)
            self_attrs.clear()
            self_attrs.update(m_self)
            m_inj = _meet_py_injected_strs([pre_inj, b_inj, e_inj])
            cur_inj.clear()
            cur_inj.update(m_inj)
            cur_auth.clear()
            cur_auth.update(
                _meet_str_dicts_intersection(
                    pre_auth, [pre_auth, b_auth, e_auth]
                )
            )
            cur_exprs.clear()
            cur_exprs.update(
                _meet_str_dicts_intersection(
                    pre_exprs, [pre_exprs, b_exprs, e_exprs]
                )
            )
            continue
        if isinstance(stmt, (ast.With, ast.AsyncWith)):
            facts_snap = _cur_facts()
            swallows_assert = False
            for item in stmt.items:
                if _py_with_item_swallows_assertions(item.context_expr):
                    swallows_assert = True
                c_skip, c_nodes = _collect_python_expr_assertions(
                    item.context_expr,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= c_skip
                seq_nodes.extend(c_nodes)
                if item.optional_vars is not None:
                    ctx_obs = _py_expr_ast_is_observed(
                        item.context_expr,
                        env=env,
                        self_attrs=self_attrs,
                        pure_fns=pure_fns,
                        py_facts=facts_snap,
                        const_vals=const_vals,
                        type_env=cur_types,
                    )
                    _bind_py_target(
                        item.optional_vars,
                        "observed" if ctx_obs else "const",
                        (False, None),
                        env,
                        const_vals,
                        self_attrs,
                        type_env=cur_types,
                    )
                    _bind_inj(item.optional_vars, "")
                    _bind_py_auth_and_expr(
                        item.optional_vars,
                        item.context_expr,
                        auth_env=cur_auth,
                        py_exprs=cur_exprs,
                        const_vals=const_vals,
                        py_facts=facts_snap,
                    )
            body_assertions = [] if swallows_assert else assertions
            b_skip, b_exit, b_cfg = _collect_python_stmt_assertions(
                stmt.body,
                body_assertions,
                env=env,
                const_vals=const_vals,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= b_skip
            if not swallows_assert:
                seq_nodes.append(b_cfg)
            if b_exit and not swallows_assert:
                return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            continue
        try_star = getattr(ast, "TryStar", None)
        if isinstance(stmt, ast.Try) or (
            try_star is not None and isinstance(stmt, try_star)
        ):
            facts_snap = _cur_facts()
            except_swallows = any(
                _py_handler_may_catch_assertion_error(h.type)
                and not _py_stmts_unconditionally_reraise(h.body)
                for h in stmt.handlers
            )
            finally_aborts = any(
                isinstance(sub, (ast.Return, ast.Break, ast.Continue))
                for fnl in stmt.finalbody
                for sub in ast.walk(fnl)
            )
            try_assertions = (
                [] if (except_swallows or finally_aborts) else assertions
            )
            handler_or_else_assertions = (
                [] if finally_aborts else assertions
            )
            b_st = (dict(env), dict(const_vals), dict(self_attrs))
            b_inj = dict(cur_inj)
            pre_auth = dict(cur_auth)
            b_auth = dict(cur_auth)
            pre_exprs = dict(cur_exprs)
            b_exprs = dict(cur_exprs)
            try_obs_hits: list[bool] = []
            b_skip, b_exit, b_cfg = _collect_python_stmt_assertions(
                stmt.body,
                try_assertions,
                env=b_st[0],
                const_vals=b_st[1],
                self_attrs=b_st[2],
                pure_fns=pure_fns,
                py_facts=facts_snap,
                type_env=dict(cur_types),
                obs_calls=try_obs_hits,
                proc_exits=proc_exits,
                injected_strs=b_inj,
                auth_env=b_auth,
                py_exprs=b_exprs,
            )
            if obs_calls is not None and try_obs_hits:
                obs_calls.append(True)
            saw_skip |= b_skip
            handlers_exit = bool(stmt.handlers)
            handler_sts: list[
                tuple[dict[str, str], dict[str, object], dict[str, str]]
            ] = []
            handler_injs: list[dict[str, str]] = []
            handler_auths: list[dict[str, str]] = []
            handler_exprs: list[dict[str, str]] = []
            handler_cfgs: list[object] = []
            for handler in stmt.handlers:
                h_st = (dict(env), dict(const_vals), dict(self_attrs))
                h_inj = dict(cur_inj)
                h_auth = dict(cur_auth)
                h_exprs = dict(cur_exprs)
                if handler.name:
                    h_st[0][handler.name] = "observed" if try_obs_hits else "const"
                    h_st[1].pop(handler.name, None)
                    h_inj.pop(handler.name, None)
                    h_auth.pop(handler.name, None)
                    h_exprs.pop(handler.name, None)
                h_skip, h_exit, h_cfg = _collect_python_stmt_assertions(
                    handler.body,
                    handler_or_else_assertions,
                    env=h_st[0],
                    const_vals=h_st[1],
                    self_attrs=h_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=h_inj,
                    auth_env=h_auth,
                    py_exprs=h_exprs,
                )
                saw_skip |= h_skip
                handlers_exit &= h_exit
                handler_cfgs.append(h_cfg)
                if not h_exit:
                    handler_sts.append(h_st)
                    handler_injs.append(h_inj)
                    handler_auths.append(h_auth)
                    handler_exprs.append(h_exprs)
            if not b_exit:
                o_skip, o_exit, o_cfg = _collect_python_stmt_assertions(
                    stmt.orelse,
                    handler_or_else_assertions,
                    env=b_st[0],
                    const_vals=b_st[1],
                    self_attrs=b_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=b_inj,
                    auth_env=b_auth,
                    py_exprs=b_exprs,
                )
                saw_skip |= o_skip
            else:
                o_exit = True
                o_cfg = _CfgSeq(())
            live_sts = ([] if (b_exit or o_exit) else [b_st]) + handler_sts
            live_injs = ([] if (b_exit or o_exit) else [b_inj]) + handler_injs
            live_auths = ([] if (b_exit or o_exit) else [b_auth]) + handler_auths
            live_exprs = (
                [] if (b_exit or o_exit) else [b_exprs]
            ) + handler_exprs
            if live_sts:
                m_env, m_vals, m_self = _meet_py_state(
                    (env, const_vals, self_attrs), live_sts
                )
                env.clear()
                env.update(m_env)
                const_vals.clear()
                const_vals.update(m_vals)
                self_attrs.clear()
                self_attrs.update(m_self)
                m_inj = _meet_py_injected_strs(live_injs)
                cur_inj.clear()
                cur_inj.update(m_inj)
                cur_auth.clear()
                cur_auth.update(
                    _meet_str_dicts_intersection(pre_auth, live_auths)
                )
                cur_exprs.clear()
                cur_exprs.update(
                    _meet_str_dicts_intersection(pre_exprs, live_exprs)
                )
            f_skip, f_exit, f_cfg = _collect_python_stmt_assertions(
                stmt.finalbody,
                assertions,
                env=env,
                const_vals=const_vals,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= f_skip
            if finally_aborts:
                seq_nodes.append(f_cfg)
            else:
                normal_try = _CfgSeq(
                    (_CfgSeq(()) if except_swallows else b_cfg, o_cfg)
                )
                try_branch: object = (
                    _CfgBranch((normal_try, *handler_cfgs))
                    if handler_cfgs
                    else normal_try
                )
                seq_nodes.append(_CfgSeq((try_branch, f_cfg)))
            if f_exit or ((b_exit or o_exit) and handlers_exit):
                return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            continue
        match_cls = getattr(ast, "Match", None)
        if match_cls is not None and isinstance(stmt, match_cls):
            facts_snap = _cur_facts()
            s_skip, s_nodes = _collect_python_expr_assertions(
                stmt.subject,
                assertions,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                const_vals=const_vals,
                py_facts=facts_snap,
                type_env=cur_types,
                obs_calls=obs_calls,
                proc_exits=proc_exits,
                injected_strs=cur_inj,
                auth_env=cur_auth,
                py_exprs=cur_exprs,
            )
            saw_skip |= s_skip
            seq_nodes.extend(s_nodes)
            subj_obs = _py_expr_ast_is_observed(
                stmt.subject,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=facts_snap,
                const_vals=const_vals,
                type_env=cur_types,
            )
            subj_inj = (
                _py_expr_unobserved_str_parts(
                    stmt.subject,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    const_vals=const_vals,
                    type_env=cur_types,
                    injected_strs=cur_inj,
                )
                if subj_obs
                else ""
            )
            subj_status = "observed" if subj_obs else "const"
            all_cases_exit = bool(stmt.cases)
            live_cases: list[
                tuple[dict[str, str], dict[str, object], dict[str, str]]
            ] = []
            live_case_injs: list[dict[str, str]] = []
            live_case_auths: list[dict[str, str]] = []
            live_case_exprs: list[dict[str, str]] = []
            case_cfgs: list[object] = []
            for case in stmt.cases:
                c_st = (dict(env), dict(const_vals), dict(self_attrs))
                c_inj = dict(cur_inj)
                c_auth = dict(cur_auth)
                c_exprs = dict(cur_exprs)
                for p_var in _extract_py_match_pattern_names(case.pattern):
                    c_st[0][p_var] = subj_status
                    c_st[1].pop(p_var, None)
                    c_auth.pop(p_var, None)
                    c_exprs.pop(p_var, None)
                    if subj_inj:
                        c_inj[p_var] = subj_inj
                    else:
                        c_inj.pop(p_var, None)
                g_nodes: list[object] = []
                if case.guard is not None:
                    g_skip, g_nodes = _collect_python_expr_assertions(
                        case.guard,
                        assertions,
                        env=c_st[0],
                        self_attrs=c_st[2],
                        pure_fns=pure_fns,
                        const_vals=c_st[1],
                        py_facts=facts_snap,
                        type_env=dict(cur_types),
                        obs_calls=obs_calls,
                        proc_exits=proc_exits,
                        injected_strs=c_inj,
                        auth_env=c_auth,
                        py_exprs=c_exprs,
                    )
                    saw_skip |= g_skip
                c_skip, c_exit, c_cfg = _collect_python_stmt_assertions(
                    case.body,
                    assertions,
                    env=c_st[0],
                    const_vals=c_st[1],
                    self_attrs=c_st[2],
                    pure_fns=pure_fns,
                    py_facts=facts_snap,
                    type_env=dict(cur_types),
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=c_inj,
                    auth_env=c_auth,
                    py_exprs=c_exprs,
                )
                saw_skip |= c_skip
                all_cases_exit &= c_exit
                case_cfgs.append(_CfgSeq((*g_nodes, c_cfg)))
                if not c_exit:
                    live_cases.append(c_st)
                    live_case_injs.append(c_inj)
                    live_case_auths.append(c_auth)
                    live_case_exprs.append(c_exprs)
            has_catchall = any(
                c.guard is None and _py_pattern_is_irrefutable(c.pattern)
                for c in stmt.cases
            )
            if not has_catchall:
                case_cfgs.append(_CfgSeq(()))
            if case_cfgs:
                seq_nodes.append(_CfgBranch(tuple(case_cfgs)))
            if all_cases_exit and has_catchall:
                return saw_skip, True, _CfgSeq(tuple(seq_nodes))
            if live_cases:
                pre_asnap = dict(cur_auth)
                pre_exsnap = dict(cur_exprs)
                m_env, m_vals, m_self = _meet_py_state(
                    (env, const_vals, self_attrs), live_cases
                )
                env.clear()
                env.update(m_env)
                const_vals.clear()
                const_vals.update(m_vals)
                self_attrs.clear()
                self_attrs.update(m_self)
                m_inj = _meet_py_injected_strs(live_case_injs)
                cur_inj.clear()
                cur_inj.update(m_inj)
                auth_live = (
                    live_case_auths
                    if has_catchall
                    else [*live_case_auths, pre_asnap]
                )
                expr_live = (
                    live_case_exprs
                    if has_catchall
                    else [*live_case_exprs, pre_exsnap]
                )
                cur_auth.clear()
                cur_auth.update(
                    _meet_str_dicts_intersection(pre_asnap, auth_live)
                )
                cur_exprs.clear()
                cur_exprs.update(
                    _meet_str_dicts_intersection(pre_exsnap, expr_live)
                )
            continue

        # Track in-place list mutation (`cmd.append("-c")` revokes approval,
        # and `lines.append("...")` propagates injected literal needles).
        if (
            isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Attribute)
            and stmt.value.func.attr in ("append", "extend", "insert")
            and isinstance(stmt.value.func.value, ast.Name)
        ):
            target_id = stmt.value.func.value.id
            if env.get(target_id) == "observed":
                arg_idx = 1 if stmt.value.func.attr == "insert" and len(stmt.value.args) >= 2 else 0
                if arg_idx < len(stmt.value.args):
                    extra_inj = _py_expr_unobserved_str_parts(
                        stmt.value.args[arg_idx],
                        env=env,
                        self_attrs=self_attrs,
                        pure_fns=pure_fns,
                        py_facts=_cur_facts(),
                        const_vals=const_vals,
                        type_env=cur_types,
                        injected_strs=cur_inj,
                    )
                    if extra_inj:
                        cur_inj[target_id] = cur_inj.get(target_id, "") + extra_inj
            if env.get(target_id) == "cmd_approved":
                for arg in stmt.value.args:
                    if _extract_py_static_const(arg, const_vals) in (
                        (True, "-c"),
                        (True, "-e"),
                    ) or (
                        isinstance(arg, (ast.List, ast.Tuple))
                        and any(
                            _extract_py_static_const(e, const_vals)
                            in ((True, "-c"), (True, "-e"))
                            for e in arg.elts
                        )
                    ):
                        env[target_id] = "const"

        facts_snap = _cur_facts()
        for child in ast.iter_child_nodes(stmt):
            if isinstance(child, ast.expr):
                c_skip, c_nodes = _collect_python_expr_assertions(
                    child,
                    assertions,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    const_vals=const_vals,
                    py_facts=facts_snap,
                    type_env=cur_types,
                    obs_calls=obs_calls,
                    proc_exits=proc_exits,
                    injected_strs=cur_inj,
                    auth_env=cur_auth,
                    py_exprs=cur_exprs,
                )
                saw_skip |= c_skip
                seq_nodes.extend(c_nodes)
    return saw_skip, False, _CfgSeq(tuple(seq_nodes))


def _py_pattern_is_irrefutable(pat: ast.AST) -> bool:
    """Return True if a Python `match` pattern matches unconditionally."""
    match_as = getattr(ast, "MatchAs", None)
    match_or = getattr(ast, "MatchOr", None)
    if match_as is not None and isinstance(pat, match_as):
        return pat.pattern is None or _py_pattern_is_irrefutable(pat.pattern)
    if match_or is not None and isinstance(pat, match_or):
        return any(_py_pattern_is_irrefutable(p) for p in pat.patterns)
    return False


PROTECTED_PY_TESTCASE_ATTRS = frozenset(
    {
        "TestCase",
        "FunctionTestCase",
        "SkipTest",
        "run",
        "debug",
        "__init__",
        "__new__",
        "__call__",
        "__getattribute__",
        "__getattr__",
        "__setattr__",
        "__delattr__",
        "__init_subclass__",
        "__unittest_skip__",
        "__unittest_skip_why__",
        "__unittest_expecting_failure__",
        "_testMethodName",
        "_feedErrorsToResult",
        "_outcome",
        "_addSkip",
        "_addExpectedFailure",
        "_addUnexpectedSuccess",
        "_callSetUp",
        "_callTestMethod",
        "_callTearDown",
        "_callCleanup",
        "defaultTestResult",
        "countTestCases",
        "skipTest",
        "subTest",
        "addTypeEqualityFunc",
        "failureException",
        "longMessage",
        "setUp",
        "setUpClass",
        "tearDown",
        "tearDownClass",
    }
)


def _is_protected_py_testcase_attr(name: str) -> bool:
    """Return True if `name` is a protected TestCase method/hook/internal flag."""
    return (
        name.startswith("assert")
        or name.startswith("fail")
        or name.startswith("__unittest_")
        or name in PROTECTED_PY_TESTCASE_ATTRS
    )


def _iter_py_class_body_stmts(stmts: list[ast.stmt]) -> Iterable[ast.stmt]:
    """Yield statements executing at class-body scope (without descending into defs)."""
    try_star = getattr(ast, "TryStar", None)
    match_cls = getattr(ast, "Match", None)
    for st in stmts:
        yield st
        if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            continue
        if isinstance(st, ast.If):
            yield from _iter_py_class_body_stmts(st.body)
            yield from _iter_py_class_body_stmts(st.orelse)
        elif isinstance(st, (ast.For, ast.AsyncFor, ast.While)):
            yield from _iter_py_class_body_stmts(st.body)
            yield from _iter_py_class_body_stmts(st.orelse)
        elif isinstance(st, (ast.With, ast.AsyncWith)):
            yield from _iter_py_class_body_stmts(st.body)
        elif isinstance(st, ast.Try) or (
            try_star is not None and isinstance(st, try_star)
        ):
            yield from _iter_py_class_body_stmts(st.body)
            for h in st.handlers:
                yield from _iter_py_class_body_stmts(h.body)
            yield from _iter_py_class_body_stmts(st.orelse)
            yield from _iter_py_class_body_stmts(st.finalbody)
        elif match_cls is not None and isinstance(st, match_cls):
            for c in st.cases:
                yield from _iter_py_class_body_stmts(c.body)


def _iter_py_assign_targets(tgt: ast.AST) -> Iterable[ast.AST]:
    """Yield leaf assignment target nodes inside tuples/lists/starred items."""
    if isinstance(tgt, (ast.Tuple, ast.List)):
        for elt in tgt.elts:
            yield from _iter_py_assign_targets(elt)
    elif isinstance(tgt, ast.Starred):
        yield from _iter_py_assign_targets(tgt.value)
    else:
        yield tgt


def _collect_unittest_import_facts(
    tree: ast.Module,
) -> tuple[set[str], set[str], set[str], list[ast.Import | ast.ImportFrom]]:
    """Collect `unittest` module/TestCase aliases and their import AST nodes."""
    unittest_mods: set[str] = set()
    testcase_bases: set[str] = set()
    protected_names: set[str] = set()
    import_nodes: list[ast.Import | ast.ImportFrom] = []
    for node in tree.body:
        if isinstance(node, ast.Import):
            matched = False
            for alias in node.names:
                if alias.name == "unittest" or alias.name.startswith(
                    "unittest."
                ):
                    bound = alias.asname or alias.name.split(".", 1)[0]
                    unittest_mods.add(bound)
                    protected_names.add(bound)
                    matched = True
                    if alias.name == "unittest.case" and alias.asname:
                        testcase_bases.add(f"{alias.asname}.TestCase")
            if matched:
                import_nodes.append(node)
        elif isinstance(node, ast.ImportFrom) and node.module in (
            "unittest",
            "unittest.case",
        ):
            matched = False
            for alias in node.names:
                if alias.name == "*":
                    continue
                bound = alias.asname or alias.name
                if alias.name == "TestCase":
                    testcase_bases.add(bound)
                    protected_names.add(bound)
                    matched = True
                elif alias.name == "case":
                    testcase_bases.add(f"{bound}.TestCase")
                    protected_names.add(bound)
                    matched = True
            if matched:
                import_nodes.append(node)
    for mod_alias in unittest_mods:
        testcase_bases.add(f"{mod_alias}.TestCase")
        testcase_bases.add(f"{mod_alias}.case.TestCase")
    return unittest_mods, testcase_bases, protected_names, import_nodes


def _collect_unittest_testcase_names(tree: ast.Module) -> set[str]:
    """Identify local classes descending strictly from `unittest.TestCase`."""
    _mods, testcase_bases, protected_names, import_nodes = (
        _collect_unittest_import_facts(tree)
    )
    for stmt in tree.body:
        if stmt in import_nodes:
            continue
        for pname in list(protected_names):
            if _py_stmt_binds_or_deletes_name(stmt, pname):
                return set()

    top_classes = [n for n in tree.body if isinstance(n, ast.ClassDef)]
    local_testcases: set[str] = set()
    changed = True
    while changed:
        changed = False
        for cls in top_classes:
            if cls.name in local_testcases or cls.keywords or not cls.bases:
                continue
            base_names = [_dotted_python_name(b) for b in cls.bases]
            if all(
                bname is not None
                and (bname in testcase_bases or bname in local_testcases)
                for bname in base_names
            ):
                local_testcases.add(cls.name)
                changed = True
    return local_testcases


def _check_python_monkey_patching(
    tree: ast.Module,
    cls_node: ast.ClassDef,
    fn_node: ast.FunctionDef | ast.AsyncFunctionDef,
    *,
    local_testcases: set[str],
    rel_path: str,
    fn_name: str,
) -> str | None:
    """Reject module/helper monkey-patching or wrapping of `TestCase` checks."""
    unittest_mods, testcase_bases, protected_names, import_nodes = (
        _collect_unittest_import_facts(tree)
    )
    for stmt in tree.body:
        if _py_stmt_binds_or_deletes_name(stmt, "load_tests"):
            return (
                f"{rel_path}::{fn_name} defines `load_tests` protocol hook, "
                "which can suppress unittest discovery"
            )
        if _py_stmt_binds_or_deletes_name(stmt, "setUpModule"):
            if (
                isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef))
                and stmt.name == "setUpModule"
            ):
                if stmt.decorator_list:
                    dec_src = ast.unparse(stmt.decorator_list[0])
                    return (
                        f"{rel_path}::{fn_name} carries forbidden decorator "
                        f"@{dec_src} on `setUpModule`"
                    )
            else:
                return (
                    f"{rel_path}::{fn_name} rebinds or imports `setUpModule` "
                    "outside a plain module-level `def setUpModule()`"
                )
        if stmt in import_nodes:
            continue
        for pname in sorted(protected_names):
            if _py_stmt_binds_or_deletes_name(stmt, pname):
                return (
                    f"{rel_path}::{fn_name} shadows or rebinds `{pname}` in "
                    "regression test module"
                )
    for fn_scope in [
        n
        for n in ast.walk(tree)
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]:
        for stmt in fn_scope.body:
            for pname in sorted(protected_names):
                if _py_stmt_binds_or_deletes_name(stmt, pname):
                    return (
                        f"{rel_path}::{fn_name} rebinds `{pname}` inside "
                        f"`{fn_scope.name}`"
                    )

    cls_by_name = {
        n.name: n for n in tree.body if isinstance(n, ast.ClassDef)
    }
    ancestors: list[ast.ClassDef] = []
    queue = [cls_node]
    seen_cls: set[str] = set()
    while queue:
        cur_cls = queue.pop(0)
        if cur_cls.name in seen_cls:
            continue
        seen_cls.add(cur_cls.name)
        ancestors.append(cur_cls)
        cur_idx = tree.body.index(cur_cls)
        if any(
            _py_stmt_binds_or_deletes_name(later, cur_cls.name)
            for later in tree.body[cur_idx + 1 :]
        ):
            return (
                f"{rel_path}::{fn_name} TestCase class `{cur_cls.name}` is "
                "rebound or deleted later in module"
            )
        for base in cur_cls.bases:
            bname = _dotted_python_name(base)
            if bname in cls_by_name:
                queue.append(cls_by_name[bname])

    for anc in ancestors:
        for sub in ast.walk(anc):
            if isinstance(
                sub, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete)
            ):
                r_tgts = (
                    sub.targets
                    if isinstance(sub, (ast.Assign, ast.Delete))
                    else [sub.target]
                )
                for rt in r_tgts:
                    for leaf in _iter_py_assign_targets(rt):
                        if isinstance(leaf, ast.Name) and leaf.id == "self":
                            return (
                                f"{rel_path}::{fn_name} rebinds or deletes "
                                "`self` inside TestCase"
                            )

    for anc in ancestors:
        for member in _iter_py_class_body_stmts(anc.body):
            if isinstance(member, (ast.FunctionDef, ast.AsyncFunctionDef)):
                if member.name not in (
                    "setUp",
                    "setUpClass",
                    "tearDown",
                    "tearDownClass",
                ) and _is_protected_py_testcase_attr(member.name):
                    return (
                        f"{rel_path}::{fn_name} shadows TestCase method "
                        f"`{member.name}` on `{anc.name}`"
                    )
                if member.name in ("setUp", "setUpClass"):
                    for sdec in member.decorator_list:
                        sdec_src = ast.unparse(sdec)
                        if not (
                            member.name == "setUpClass"
                            and sdec_src == "classmethod"
                        ):
                            return (
                                f"{rel_path}::{fn_name} carries forbidden "
                                f"decorator @{sdec_src} on `{member.name}`"
                            )
            elif isinstance(member, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                raw_tgts = (
                    member.targets
                    if isinstance(member, ast.Assign)
                    else [member.target]
                )
                for rt in raw_tgts:
                    for leaf in _iter_py_assign_targets(rt):
                        if isinstance(leaf, ast.Name) and (
                            _is_protected_py_testcase_attr(leaf.id)
                        ):
                            return (
                                f"{rel_path}::{fn_name} overrides TestCase "
                                f"attribute `{leaf.id}` on `{anc.name}`"
                            )

    for dec in (
        *(d for anc in ancestors for d in anc.decorator_list),
        *fn_node.decorator_list,
    ):
        dec_src = ast.unparse(dec)
        low_dec = dec_src.lower()
        if (
            "skip" in low_dec
            or "expectedfailure" in low_dec
            or "xfail" in low_dec
        ):
            return f"{rel_path}::{fn_name} must not be skipped (@{dec_src})"
        return (
            f"{rel_path}::{fn_name} carries forbidden decorator @{dec_src} "
            "(decorators on bound TestCase classes/methods are disallowed)"
        )

    protected_owners = (
        set(unittest_mods)
        | set(testcase_bases)
        | set(protected_names)
        | set(local_testcases)
        | seen_cls
        | {"unittest", "unittest.case", "unittest.TestCase", "TestCase"}
    )

    for sub in ast.walk(tree):
        if isinstance(
            sub, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.Delete)
        ):
            if isinstance(sub, ast.Assign):
                raw_targets = sub.targets
            elif isinstance(sub, ast.Delete):
                raw_targets = sub.targets
            else:
                raw_targets = [sub.target]
            for rt in raw_targets:
                for tgt in _iter_py_assign_targets(rt):
                    if isinstance(tgt, ast.Attribute):
                        attr = tgt.attr
                        owner = _dotted_python_name(tgt.value) or ""
                        owner_root = owner.split(".", 1)[0] if owner else ""
                        if (
                            attr == fn_name
                            or _is_protected_py_testcase_attr(attr)
                        ):
                            return (
                                f"{rel_path}::{fn_name} monkey-patches or "
                                f"rebinds `{owner or '<expr>'}.{attr}`"
                            )
                        if (
                            owner in protected_owners
                            or owner_root in protected_owners
                        ):
                            return (
                                f"{rel_path}::{fn_name} mutates attribute "
                                f"`{owner}.{attr}` on TestCase/unittest"
                            )
                    elif isinstance(tgt, ast.Subscript):
                        val_src = ast.unparse(tgt.value)
                        if "__dict__" in val_src or val_src.startswith(
                            ("globals(", "vars(", "locals(")
                        ):
                            return (
                                f"{rel_path}::{fn_name} mutates `__dict__` or "
                                "globals in regression test module"
                            )
        elif isinstance(sub, ast.Call):
            callee = _dotted_python_name(sub.func) or ""
            tail = (
                sub.func.attr
                if isinstance(sub.func, ast.Attribute)
                else callee
            )
            if callee in ("exec", "eval", "builtins.exec", "builtins.eval"):
                return (
                    f"{rel_path}::{fn_name} calls `{callee}(...)`, which is "
                    "forbidden in bound regression test modules"
                )
            if callee in (
                "setattr",
                "delattr",
                "builtins.setattr",
                "builtins.delattr",
            ) or tail in ("__setattr__", "__delattr__"):
                return (
                    f"{rel_path}::{fn_name} calls `{callee or tail}(...)`, "
                    "which is forbidden in bound regression test modules"
                )
            if "patch" in callee.split("."):
                return (
                    f"{rel_path}::{fn_name} calls `{callee}(...)`, which is "
                    "forbidden in bound regression test modules"
                )
    return None


def _py_stmt_binds_or_deletes_name(stmt: ast.stmt, name: str) -> bool:
    """Return True if `stmt` defines, rebinds, imports, or deletes `name`."""
    if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
        return stmt.name == name
    if isinstance(stmt, ast.Import):
        return any(
            (a.asname or a.name.split(".", 1)[0]) == name for a in stmt.names
        )
    if isinstance(stmt, ast.ImportFrom):
        return any((a.asname or a.name) == name for a in stmt.names)
    if isinstance(stmt, ast.Delete):
        return any(
            isinstance(sub, ast.Name) and sub.id == name
            for tgt in stmt.targets
            for sub in ast.walk(tgt)
        )
    if isinstance(stmt, ast.Assign):
        return any(
            isinstance(sub, ast.Name) and sub.id == name
            for tgt in stmt.targets
            for sub in ast.walk(tgt)
        )
    if isinstance(stmt, (ast.AnnAssign, ast.AugAssign)):
        return any(
            isinstance(sub, ast.Name) and sub.id == name
            for sub in ast.walk(stmt.target)
        )
    if isinstance(stmt, (ast.For, ast.AsyncFor)):
        if any(
            isinstance(sub, ast.Name) and sub.id == name
            for sub in ast.walk(stmt.target)
        ):
            return True
        return any(
            _py_stmt_binds_or_deletes_name(s, name)
            for s in (*stmt.body, *stmt.orelse)
        )
    if isinstance(stmt, (ast.With, ast.AsyncWith)):
        for it in stmt.items:
            if it.optional_vars is not None and any(
                isinstance(sub, ast.Name) and sub.id == name
                for sub in ast.walk(it.optional_vars)
            ):
                return True
        return any(_py_stmt_binds_or_deletes_name(s, name) for s in stmt.body)
    if isinstance(stmt, ast.If):
        return any(
            _py_stmt_binds_or_deletes_name(s, name)
            for s in (*stmt.body, *stmt.orelse)
        )
    try_star = getattr(ast, "TryStar", None)
    if isinstance(stmt, ast.Try) or (
        try_star is not None and isinstance(stmt, try_star)
    ):
        for h in stmt.handlers:
            if h.name == name:
                return True
            if any(_py_stmt_binds_or_deletes_name(s, name) for s in h.body):
                return True
        return any(
            _py_stmt_binds_or_deletes_name(s, name)
            for s in (*stmt.body, *stmt.orelse, *stmt.finalbody)
        )
    match_cls = getattr(ast, "Match", None)
    if match_cls is not None and isinstance(stmt, match_cls):
        return any(
            _py_stmt_binds_or_deletes_name(s, name)
            for c in stmt.cases
            for s in c.body
        )
    return False


def _py_is_main_guard(stmt: ast.stmt) -> bool:
    """Return True iff `stmt` is an `if __name__ == "__main__":` guard."""
    if not isinstance(stmt, ast.If):
        return False
    t = stmt.test
    if (
        isinstance(t, ast.Compare)
        and len(t.ops) == 1
        and isinstance(t.ops[0], ast.Eq)
    ):
        left, right = t.left, t.comparators[0]
        if (
            isinstance(left, ast.Name)
            and left.id == "__name__"
            and isinstance(right, ast.Constant)
            and right.value == "__main__"
        ) or (
            isinstance(right, ast.Name)
            and right.id == "__name__"
            and isinstance(left, ast.Constant)
            and left.value == "__main__"
        ):
            return True
    return False


def _cfg_can_reach_success_exit(node: object) -> bool:
    """Return True if any reachable path hits `_CfgExit(is_success=True)`."""

    def _walk(cur: object) -> tuple[bool, bool]:
        if isinstance(cur, _CfgExit):
            return cur.is_success, False
        if isinstance(cur, _CfgLoopJump):
            return False, False
        if isinstance(cur, _CfgItem):
            return False, True
        if isinstance(cur, _CfgSeq):
            reached = False
            fall = True
            for ch in cur.nodes:
                if not fall:
                    break
                c_reach, c_fall = _walk(ch)
                reached |= c_reach
                fall = c_fall
            return reached, fall
        if isinstance(cur, _CfgBranch):
            results = [_walk(b) for b in cur.branches]
            return any(r for r, _ in results), any(f for _, f in results)
        if isinstance(cur, _CfgLoop):
            b_reach, _b_fall = _walk(cur.body)
            if cur.is_infinite:
                return b_reach, False
            o_reach = False
            if cur.orelse is not None:
                o_reach, _ = _walk(cur.orelse)
            return b_reach or o_reach, True
        return False, True

    return _walk(node)[0]


def _seed_py_scope_env(
    tree: ast.Module,
    mro_classes: list[ast.ClassDef],
    py_facts: _PyFileFacts,
    pure_fns: frozenset[str],
) -> tuple[dict[str, str], dict[str, object], dict[str, str], dict[str, str]]:
    """Seed module-level and class-level bindings for a Python `TestCase` MRO."""
    env: dict[str, str] = {}
    const_vals: dict[str, object] = {}
    self_attrs: dict[str, str] = {}
    type_env: dict[str, str] = {}
    for stmt in [
        *tree.body,
        *(s for anc in reversed(mro_classes) for s in anc.body),
    ]:
        if isinstance(stmt, ast.Assign):
            obs = _py_expr_ast_is_observed(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
            )
            if obs:
                st_kind = "observed"
            elif _py_subprocess_cmd_is_approved(
                stmt.value,
                env=env,
                const_vals=const_vals,
                aliases=py_facts.import_aliases or {},
            ):
                st_kind = "cmd_approved"
            else:
                st_kind = "const"
            rc = _extract_py_static_const(stmt.value, const_vals)
            rcls = (
                stmt.value.func.id
                if (
                    isinstance(stmt.value, ast.Call)
                    and isinstance(stmt.value.func, ast.Name)
                    and stmt.value.func.id in py_facts.local_classes
                )
                else None
            )
            for tgt in stmt.targets:
                _bind_py_target(
                    tgt,
                    st_kind,
                    rc,
                    env,
                    const_vals,
                    self_attrs,
                    type_env=type_env,
                    rhs_cls=rcls,
                )
        elif isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
            obs = _py_expr_ast_is_observed(
                stmt.value,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
            )
            if obs:
                st_kind = "observed"
            elif _py_subprocess_cmd_is_approved(
                stmt.value,
                env=env,
                const_vals=const_vals,
                aliases=py_facts.import_aliases or {},
            ):
                st_kind = "cmd_approved"
            else:
                st_kind = "const"
            rc = _extract_py_static_const(stmt.value, const_vals)
            rcls = (
                stmt.value.func.id
                if (
                    isinstance(stmt.value, ast.Call)
                    and isinstance(stmt.value.func, ast.Name)
                    and stmt.value.func.id in py_facts.local_classes
                )
                else None
            )
            _bind_py_target(
                stmt.target,
                st_kind,
                rc,
                env,
                const_vals,
                self_attrs,
                type_env=type_env,
                rhs_cls=rcls,
            )
    return env, const_vals, self_attrs, type_env


def _py_fn_has_yield_in_own_scope(
    fn_node: ast.FunctionDef | ast.AsyncFunctionDef,
) -> bool:
    """Return True if `fn_node` yields in its own scope (ignoring inner defs)."""
    stack: list[ast.AST] = list(fn_node.body)
    while stack:
        cur = stack.pop()
        if isinstance(cur, (ast.Yield, ast.YieldFrom)):
            return True
        if isinstance(
            cur,
            (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda),
        ):
            continue
        stack.extend(ast.iter_child_nodes(cur))
    return False


def _extract_python_test_assertion_items_with_cfg(
    text: str, rel_path: str, fn_name: str
) -> tuple[str | None, list[_AssertionItem] | None, object | None, str | None]:
    """Parse Python `TestCase` method via AST and return `(raw, items, cfg, err)`."""
    try:
        tree = ast.parse(text, filename=rel_path)
    except SyntaxError as exc:
        return None, None, None, f"{rel_path}: Python syntax error: {exc}"

    local_testcases = _collect_unittest_testcase_names(tree)
    matches: list[tuple[ast.ClassDef, ast.FunctionDef | ast.AsyncFunctionDef]] = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                if (
                    isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and child.name == fn_name
                ):
                    matches.append((node, child))
    if not matches:
        top_level = any(
            isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))
            and n.name == fn_name
            for n in tree.body
        )
        if top_level or not fn_name.startswith("test_"):
            return (
                None,
                None,
                None,
                f"{rel_path}::{fn_name} must be a test_* method inside TestCase",
            )
        return (
            None,
            None,
            None,
            f"missing Python regression test `{fn_name}` in {rel_path}",
        )
    if not fn_name.startswith("test_"):
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} must be a test_* method inside TestCase",
        )
    if len(matches) > 1:
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} has duplicate Python test definitions",
        )

    cls_node, fn_node = matches[0]
    if cls_node.name not in local_testcases:
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} class `{cls_node.name}` must inherit from unittest.TestCase",
        )
    fn_idx = cls_node.body.index(fn_node)
    if any(
        _py_stmt_binds_or_deletes_name(later, fn_name)
        for later in cls_node.body[fn_idx + 1 :]
    ):
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} method is rebound, shadowed, or deleted "
            f"later in `{cls_node.name}`",
        )
    if isinstance(fn_node, ast.AsyncFunctionDef):
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} must be a synchronous def method (async def is ignored by unittest.TestCase)",
        )
    if _py_fn_has_yield_in_own_scope(fn_node):
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} must not be a generator method containing yield (ignored by unittest.TestCase)",
        )
    monkey_err = _check_python_monkey_patching(
        tree,
        cls_node,
        fn_node,
        local_testcases=local_testcases,
        rel_path=rel_path,
        fn_name=fn_name,
    )
    if monkey_err is not None:
        return None, None, None, monkey_err

    cls_by_name = {
        n.name: n for n in tree.body if isinstance(n, ast.ClassDef)
    }

    def _mro_for(cnode: ast.ClassDef) -> list[ast.ClassDef]:
        res: list[ast.ClassDef] = []
        q = [cnode]
        seen: set[str] = set()
        while q:
            cur = q.pop(0)
            if cur.name in seen:
                continue
            seen.add(cur.name)
            res.append(cur)
            for base in cur.bases:
                bname = _dotted_python_name(base)
                if bname in cls_by_name:
                    q.append(cls_by_name[bname])
        return res

    mro_classes = _mro_for(cls_node)
    py_facts, pure_fns = _collect_py_file_facts(
        tree, cls_node, fn_node, mro_classes
    )
    env, const_vals, self_attrs, type_env = _seed_py_scope_env(
        tree, mro_classes, py_facts, pure_fns
    )

    def _collect_py_called_names(stmts: list[ast.stmt]) -> set[str]:
        called: set[str] = set()
        for st in stmts:
            for sub in ast.walk(st):
                if isinstance(sub, ast.Call):
                    cn = _dotted_python_name(sub.func)
                    if cn:
                        called.add(cn)
                        if cn.startswith(("self.", "cls.")):
                            called.add(cn.split(".", 1)[1])
        return called

    helper_defs: dict[str, ast.FunctionDef | ast.AsyncFunctionDef] = {}
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            helper_defs[node.name] = node
    for anc in reversed(mro_classes):
        for m in anc.body:
            if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef)):
                helper_defs[m.name] = m
                helper_defs[f"self.{m.name}"] = m
                helper_defs[f"cls.{m.name}"] = m
    skipping_helpers: set[str] = set()
    for hname, hdef in helper_defs.items():
        h_s, _, _ = _collect_python_stmt_assertions(
            hdef.body,
            [],
            env=dict(env),
            const_vals=dict(const_vals),
            self_attrs=dict(self_attrs),
            pure_fns=pure_fns,
            py_facts=py_facts,
            type_env=dict(type_env),
        )
        if h_s:
            skipping_helpers.add(hname)
    changed_skip = True
    while changed_skip:
        changed_skip = False
        for hname, hdef in helper_defs.items():
            if hname in skipping_helpers:
                continue
            if _collect_py_called_names(hdef.body) & skipping_helpers:
                skipping_helpers.add(hname)
                changed_skip = True

    py_proc_exits: list[bool] = []

    top_stmts: list[ast.stmt] = []
    for st in tree.body:
        if _py_is_main_guard(st):
            assert isinstance(st, ast.If)
            top_stmts.extend(st.orelse)
        else:
            top_stmts.append(st)
    if top_stmts:
        top_proc_exits: list[bool] = []
        _top_skip, top_exit, top_cfg = _collect_python_stmt_assertions(
            top_stmts,
            [],
            env=dict(env),
            const_vals=dict(const_vals),
            self_attrs=dict(self_attrs),
            pure_fns=pure_fns,
            py_facts=py_facts,
            type_env=dict(type_env),
            proc_exits=top_proc_exits,
        )
        if top_proc_exits or top_exit or _cfg_can_reach_success_exit(top_cfg):
            return (
                None,
                None,
                None,
                f"{rel_path} module top-level code may invoke process exit(0) "
                f"before tests run, masking tests in {fn_name}'s suite",
            )

    setup_hooks: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    module_teardowns: list[ast.FunctionDef | ast.AsyncFunctionDef] = []
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            if node.name == "setUpModule":
                setup_hooks.append(node)
            elif node.name == "tearDownModule":
                module_teardowns.append(node)
    for setup_name in ("setUpClass", "setUp"):
        for anc in mro_classes:
            found_hook = next(
                (
                    m
                    for m in anc.body
                    if isinstance(m, (ast.FunctionDef, ast.AsyncFunctionDef))
                    and m.name == setup_name
                ),
                None,
            )
            if found_hook is not None:
                setup_hooks.append(found_hook)
                break
    for hook in setup_hooks:
        setup_assertions: list[_AssertionItem] = []
        setup_env = dict(env)
        setup_vals = dict(const_vals)
        h_skip, h_exit, h_cfg = _collect_python_stmt_assertions(
            hook.body,
            setup_assertions,
            env=setup_env,
            const_vals=setup_vals,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            type_env=dict(type_env),
            proc_exits=py_proc_exits,
        )
        if h_skip or (hook.name in skipping_helpers):
            return (
                None,
                None,
                None,
                f"{rel_path}::{fn_name} must not call skipTest / raise "
                f"SkipTest in `{hook.name}`",
            )
        if py_proc_exits or (
            hook.name == "setUpModule"
            and (h_exit or _cfg_can_reach_success_exit(h_cfg))
        ):
            return (
                None,
                None,
                None,
                f"{rel_path}::{fn_name} `{hook.name}` may invoke process exit(0), "
                "masking failing assertions or sibling tests",
            )

    for td_hook in module_teardowns:
        _td_s, _td_ex, _td_cfg = _collect_python_stmt_assertions(
            td_hook.body,
            [],
            env=dict(env),
            const_vals=dict(const_vals),
            self_attrs=dict(self_attrs),
            pure_fns=pure_fns,
            py_facts=py_facts,
            type_env=dict(type_env),
            proc_exits=py_proc_exits,
        )
        if py_proc_exits:
            return (
                None,
                None,
                None,
                f"{rel_path}::{fn_name} `{td_hook.name}` may invoke os._exit(0), "
                "masking failing assertions or sibling tests",
            )

    assertions: list[_AssertionItem] = []
    fn_auth_env: dict[str, str] = {}
    fn_py_exprs: dict[str, str] = {}
    saw_skip, _exits, cfg_root = _collect_python_stmt_assertions(
        fn_node.body,
        assertions,
        env=env,
        const_vals=const_vals,
        self_attrs=self_attrs,
        pure_fns=pure_fns,
        py_facts=py_facts,
        type_env=type_env,
        proc_exits=py_proc_exits,
        auth_env=fn_auth_env,
        py_exprs=fn_py_exprs,
    )
    if py_proc_exits:
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} may invoke os._exit(0), "
            "masking failing assertions or sibling tests",
        )
    if saw_skip or (fn_node.name in skipping_helpers):
        return (
            None,
            None,
            None,
            f"{rel_path}::{fn_name} must not call skipTest / raise SkipTest",
        )

    for sib_cls in tree.body:
        if (
            not isinstance(sib_cls, ast.ClassDef)
            or sib_cls.name not in local_testcases
        ):
            continue
        sib_mro = _mro_for(sib_cls)
        for sib_m in sib_cls.body:
            if (
                not isinstance(sib_m, ast.FunctionDef)
                or sib_m is fn_node
                or not sib_m.name.startswith(("test_", "setUp", "tearDown"))
            ):
                continue
            sib_facts, sib_pure = _collect_py_file_facts(
                tree, sib_cls, sib_m, sib_mro
            )
            sib_env, sib_vals, sib_self, sib_tenv = _seed_py_scope_env(
                tree, sib_mro, sib_facts, sib_pure
            )
            sib_proc_exits: list[bool] = []
            _collect_python_stmt_assertions(
                sib_m.body,
                [],
                env=sib_env,
                const_vals=sib_vals,
                self_attrs=sib_self,
                pure_fns=sib_pure,
                py_facts=sib_facts,
                type_env=sib_tenv,
                proc_exits=sib_proc_exits,
            )
            if sib_proc_exits:
                return (
                    None,
                    None,
                    None,
                    f"{rel_path}::{sib_m.name} (sibling method in {sib_cls.name}) "
                    f"may invoke os._exit(0), masking failing tests in {fn_name}'s suite",
                )

    raw_fn = ast.get_source_segment(text, fn_node) or ast.unparse(fn_node)
    return raw_fn, assertions, cfg_root, None


def _extract_python_test_assertion_items(
    text: str, rel_path: str, fn_name: str
) -> tuple[str | None, list[_AssertionItem] | None, str | None]:
    """Parse Python `TestCase` method via AST and return assertion items."""
    raw_fn, items, _cfg, err = _extract_python_test_assertion_items_with_cfg(
        text, rel_path, fn_name
    )
    return raw_fn, items, err


def _is_disabling_cfg_attr(
    attr_inner: str, *, allow_cfg_test: bool, is_inner: bool = False
) -> str | None:
    """Allowlist check forbidding `ignore`, `should_panic`, `cfg_attr`, or non-test `cfg`."""
    stripped = re.sub(r"\s+", " ", attr_inner).strip()
    bang = "!" if is_inner else ""
    name_m = re.match(r"^([A-Za-z_][A-Za-z0-9_:]*)", stripped)
    short = name_m.group(1).split("::")[-1] if name_m else ""
    if short == "ignore":
        return "carries ignore/cfg_attr ignore"
    if short == "should_panic":
        return "carries #[should_panic]"
    if short == "cfg_attr":
        if re.search(r"\bignore\b", stripped):
            return "carries ignore/cfg_attr ignore"
        if re.search(r"\bshould_panic\b", stripped):
            return "carries #[should_panic]"
        return f"carries conditional #{bang}[{stripped}]"
    if short == "cfg":
        arg_m = re.match(r"^cfg\s*\((.*)\)$", stripped, re.DOTALL)
        body = re.sub(r"\s+", "", arg_m.group(1)) if arg_m else stripped
        if allow_cfg_test and body in ALLOWED_CI_HOST_CFGS:
            return None
        prefix = "disabled via" if allow_cfg_test else "carries conditional"
        return f"{prefix} #{bang}[{stripped}]"
    if re.search(r"\b(?:ignore|should_panic|cfg|cfg_attr)\b", stripped):
        return f"carries forbidden attribute #{bang}[{stripped}]"
    return None


def _validate_test_target_executed(view: RepoView, rel_path: str) -> str | None:
    """Verify `rel_path` resolves to an actual Cargo nextest or CI unittest target."""
    if rel_path.endswith(".py"):
        if re.fullmatch(r"anneal/ci/test_[A-Za-z0-9_]+\.py", rel_path) is None:
            return (
                f"{rel_path} is not discovered by run_anneal_check.sh "
                "(Python regression tests must live at 'anneal/ci/test_*.py')"
            )
        return None

    ws_text = view.read_text("anneal/Cargo.toml")
    if ws_text is None:
        return (
            f"missing anneal/Cargo.toml while validating Cargo test target "
            f"{rel_path}"
        )
    try:
        ws_cfg = tomllib.loads(ws_text)
    except tomllib.TOMLDecodeError as exc:
        return f"malformed anneal/Cargo.toml: {exc}"
    members = ws_cfg.get("workspace", {}).get("members", [])
    if not isinstance(members, list):
        return "malformed [workspace].members in anneal/Cargo.toml"

    test_members = sorted(
        (m for m in members if isinstance(m, str) and m.startswith("tests/")),
        key=len,
        reverse=True,
    )
    matched_member = next(
        (m for m in test_members if rel_path.startswith(f"anneal/{m}/")), None
    )
    if matched_member is None:
        return (
            f"{rel_path} is not inside any anneal/Cargo.toml [workspace].members "
            "`tests/*` crate"
        )

    pkg_toml_rel = f"anneal/{matched_member}/Cargo.toml"
    pkg_text = view.read_text(pkg_toml_rel)
    if pkg_text is None:
        return f"missing {pkg_toml_rel} for Cargo test target {rel_path}"
    try:
        pkg_cfg = tomllib.loads(pkg_text)
    except tomllib.TOMLDecodeError as exc:
        return f"malformed {pkg_toml_rel}: {exc}"

    sub_rel = rel_path[len(f"anneal/{matched_member}/") :]
    raw_features = pkg_cfg.get("features", {})
    enabled_features: set[str] = set()
    if isinstance(raw_features, dict):
        queue = list(raw_features.get("default", []))
        while queue:
            feat = queue.pop()
            if not isinstance(feat, str) or feat in enabled_features:
                continue
            enabled_features.add(feat)
            expanded = raw_features.get(feat, [])
            if isinstance(expanded, list):
                queue.extend(expanded)

    explicit_tests = pkg_cfg.get("test", [])
    if isinstance(explicit_tests, list):
        for target in explicit_tests:
            if not isinstance(target, dict):
                continue
            raw_t_path = target.get("path")
            if isinstance(raw_t_path, str):
                cand_paths = (raw_t_path,)
            else:
                t_name = target.get("name")
                if not isinstance(t_name, str):
                    continue
                cand_paths = (f"tests/{t_name}.rs", f"tests/{t_name}/main.rs")
            if not any(
                ".." not in PurePosixPath(p).parts
                and PurePosixPath(p).as_posix().lstrip("./") == sub_rel
                for p in cand_paths
            ):
                continue
            if target.get("test") is False:
                return (
                    f"{rel_path} disables test execution (`test = false` in "
                    f"{pkg_toml_rel})"
                )
            if target.get("harness") is False:
                return (
                    f"{rel_path} sets `harness = false` in {pkg_toml_rel}; "
                    "standard #[test] harness execution is disabled"
                )
            req_feats = target.get("required-features", [])
            if isinstance(req_feats, list):
                missing_feats = [
                    f
                    for f in req_feats
                    if not isinstance(f, str) or f not in enabled_features
                ]
                if missing_feats:
                    return (
                        f"{rel_path} requires non-default Cargo feature(s) "
                        f"{missing_feats!r} in {pkg_toml_rel}"
                    )
            return None

    autotests = pkg_cfg.get("package", {}).get("autotests", True)
    if autotests is not False and (
        re.fullmatch(r"tests/[A-Za-z0-9_-]+\.rs", sub_rel) is not None
        or re.fullmatch(r"tests/[A-Za-z0-9_-]+/main\.rs", sub_rel) is not None
    ):
        return None

    return (
        f"{rel_path} is not a Cargo-discovered integration test target under "
        f"anneal/{matched_member}"
    )


def _find_rust_enclosing_delimiters(
    code_ns: str, target_pos: int
) -> list[tuple[str, int]]:
    """Return unclosed `(delim, idx)` pairs enclosing `target_pos`, outer-to-inner."""
    stack: list[tuple[str, int]] = []
    pairs = {"}": "{", ")": "(", "]": "["}
    for idx in range(min(target_pos, len(code_ns))):
        ch = code_ns[idx]
        if ch in "{([":
            stack.append((ch, idx))
        elif ch in "})]":
            expected = pairs[ch]
            if stack and stack[-1][0] == expected:
                stack.pop()
    return stack


def _find_rust_item_boundary_before(code_ns: str, pos: int) -> int:
    """Scan backward from `pos` to previous depth-0 `;`, `{`, `}`, or SOF."""
    paren_depth = 0
    bracket_depth = 0
    idx = pos - 1
    while idx >= 0:
        ch = code_ns[idx]
        if ch == ")":
            paren_depth += 1
        elif ch == "(" and paren_depth > 0:
            paren_depth -= 1
        elif ch == "]":
            bracket_depth += 1
        elif ch == "[" and bracket_depth > 0:
            bracket_depth -= 1
        elif paren_depth == 0 and bracket_depth == 0 and ch in ";{}":
            return idx + 1
        idx -= 1
    return 0


def _collect_preceding_attrs(
    code_ns: str,
    attr_by_end: dict[int, tuple[int, int, str, bool]],
    pos: int,
) -> tuple[int, list[tuple[int, int, str, bool]]]:
    """Collect contiguous attributes directly before `pos`, returning `(start, attrs)`."""
    collected: list[tuple[int, int, str, bool]] = []
    cur = pos
    while cur > 0:
        rstripped = code_ns[:cur].rstrip()
        if not rstripped:
            break
        end_pos = len(rstripped)
        if end_pos in attr_by_end:
            attr = attr_by_end[end_pos]
            collected.append(attr)
            cur = attr[0]
        else:
            break
    collected.reverse()
    return cur, collected


def _find_rust_fn_candidates(
    code: str,
    outer_attr_by_end: dict[int, tuple[int, int, str, bool]],
    inner_attr_by_end: dict[int, tuple[int, int, str, bool]],
    *,
    fn_name: str | None = None,
) -> list[
    tuple[
        str,
        int,
        int,
        int,
        list[tuple[int, int, str, bool]],
        list[tuple[str, int]],
    ]
]:
    """Locate zero-arg Rust function definitions with bodies and preceding attrs."""
    fn_re = (
        re.compile(rf"\bfn\s+({re.escape(fn_name)})\s*\(")
        if fn_name is not None
        else re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(")
    )
    qual_tail_re = re.compile(
        r"(?:pub\s*(?:\([^()]*\))?|async|unsafe|const|default|extern)\s*$"
    )
    candidates: list[
        tuple[
            str,
            int,
            int,
            int,
            list[tuple[int, int, str, bool]],
            list[tuple[str, int]],
        ]
    ] = []
    code_len = len(code)
    for fn_m in fn_re.finditer(code):
        lparen = fn_m.end() - 1
        rparen = _find_matching_delimiter_in_code(code, lparen)
        if rparen is None or code[lparen + 1 : rparen].strip():
            continue
        body_open = None
        p_depth = 0
        b_depth = 0
        scan_idx = rparen + 1
        while scan_idx < code_len:
            sch = code[scan_idx]
            if sch == "(":
                p_depth += 1
            elif sch == ")" and p_depth > 0:
                p_depth -= 1
            elif sch == "[":
                b_depth += 1
            elif sch == "]" and b_depth > 0:
                b_depth -= 1
            elif p_depth == 0 and b_depth == 0:
                if sch == ";":
                    break
                if sch == "{":
                    body_open = scan_idx
                    break
            scan_idx += 1
        if body_open is None:
            continue
        body_close = _find_matching_delimiter_in_code(code, body_open)
        if body_close is None:
            continue

        kw_start = fn_m.start()
        while True:
            prev_chunk = code[:kw_start].rstrip()
            qm = qual_tail_re.search(prev_chunk)
            if qm is None:
                break
            if qm.start() > 0 and (
                prev_chunk[qm.start() - 1].isalnum()
                or prev_chunk[qm.start() - 1] == "_"
            ):
                break
            kw_start = qm.start()

        attr_start, fn_attrs = _collect_preceding_attrs(
            code, outer_attr_by_end, kw_start
        )
        inner_start, _ = _collect_preceding_attrs(
            code, inner_attr_by_end, attr_start
        )
        prefix_ws = code[:inner_start].rstrip()
        if prefix_ws and prefix_ws[-1] not in ";{}":
            continue

        enclosing = _find_rust_enclosing_delimiters(code, attr_start)
        candidates.append(
            (fn_m.group(1), attr_start, body_open, body_close, fn_attrs, enclosing)
        )
    return candidates


def _extract_test_assertion_items(
    view: RepoView,
    test_ref: str,
    *,
    cfg_out: list[object] | None = None,
    fail_on_success_out: list[bool] | None = None,
) -> tuple[str | None, list[_AssertionItem] | None, str | None, bool]:
    """Extract live `_AssertionItem` values with provenance for a test ref."""
    match = REGRESSION_TEST_RE.fullmatch(test_ref)
    if match is None:
        return (
            None,
            None,
            f"regression_test {test_ref!r} must match "
            "'anneal/tests/<crate>/tests/<file>.rs::<test_fn>' or "
            "'anneal/ci/test_<file>.py::test_<fn>'",
            False,
        )
    rel_path, fn_name = match.group(1), match.group(2)
    target_err = _validate_test_target_executed(view, rel_path)
    if target_err is not None:
        return None, None, target_err, rel_path.endswith(".py")

    ok, err = view.is_regular_file(rel_path)
    if not ok:
        return (
            None,
            None,
            err or f"missing regression test file: {rel_path}",
            rel_path.endswith(".py"),
        )
    text = view.read_text(rel_path)
    if text is None:
        return (
            None,
            None,
            f"unreadable regression test file: {rel_path}",
            rel_path.endswith(".py"),
        )

    if rel_path.endswith(".rs"):
        scanned = scan_rust_tokens(text)
        code = scanned.code_no_strings_or_comments
        shadow_err = _check_rust_assertion_macro_shadowing(code, rel_path)
        if shadow_err is not None:
            return None, None, shadow_err, False
        all_attrs = _find_rust_attributes(code, scanned.code_no_comments)
        outer_attr_by_end = {
            a_end: (a_start, a_end, inner, is_inner)
            for a_start, a_end, inner, is_inner in all_attrs
            if not is_inner
        }
        inner_attr_by_end = {
            a_end: (a_start, a_end, inner, is_inner)
            for a_start, a_end, inner, is_inner in all_attrs
            if is_inner
        }

        # Check file-level `#![...]` inner attributes at depth 0.
        for a_start, _a_end, inner, is_inner in all_attrs:
            if is_inner and not _find_rust_enclosing_delimiters(code, a_start):
                reason = _is_disabling_cfg_attr(
                    inner, allow_cfg_test=True, is_inner=True
                )
                if reason is not None:
                    return None, None, f"{rel_path}::{fn_name} file {reason}", False

        candidates = _find_rust_fn_candidates(
            code, outer_attr_by_end, inner_attr_by_end, fn_name=fn_name
        )

        if not candidates:
            return (
                None,
                None,
                f"missing Rust #[test] function `{fn_name}` in {rel_path}",
                False,
            )
        if len(candidates) > 1:
            return (
                None,
                None,
                f"{rel_path}::{fn_name} has duplicate Rust function definitions",
                False,
            )

        _c_name, item_start, body_open, body_close, fn_attrs, enclosing = candidates[0]
        test_attr_re = re.compile(r"(?:(?:core|std)::prelude::v1::)?test")
        if not any(
            test_attr_re.fullmatch(re.sub(r"\s+", "", inner))
            for _s, _e, inner, is_inner in fn_attrs
            if not is_inner
        ):
            return (
                None,
                None,
                f"{rel_path}::{fn_name} lacks #[test] attribute",
                False,
            )
        for _s, _e, inner, is_inner in fn_attrs:
            attr_err = _is_disabling_cfg_attr(
                inner, allow_cfg_test=False, is_inner=is_inner
            )
            if attr_err is not None:
                return None, None, f"{rel_path}::{fn_name} {attr_err}", False

        mod_decl_re = re.compile(
            r"^\s*(?:pub\s*(?:\([^()]*\))?\s+)?mod\s+([A-Za-z_][A-Za-z0-9_]*)\s*$"
        )

        def _check_enclosing_scope(
            target_label: str,
            c_enclosing: list[tuple[str, int]],
            *,
            strict_cfg: bool,
        ) -> tuple[tuple[str, ...] | None, str | None]:
            mod_parts: list[str] = []
            for enc_idx, (delim_ch, open_pos) in enumerate(c_enclosing):
                if delim_ch != "{":
                    return None, (
                        f"{rel_path}::{target_label} nested inside non-module delimiter "
                        f"`{delim_ch}` (only top-level or `mod` #[test] runs)"
                    )
                boundary = _find_rust_item_boundary_before(code, open_pos)
                header = code[boundary:open_pos]
                scope_kind = (
                    "enclosing module"
                    if re.search(r"\bmod\b", header)
                    else "enclosing block"
                )
                outer_end = boundary
                for a_start, a_end, inner, is_inner in all_attrs:
                    if boundary <= a_start < open_pos:
                        if not is_inner:
                            scope_err = _is_disabling_cfg_attr(
                                inner, allow_cfg_test=True, is_inner=False
                            )
                            if scope_err is not None and (
                                strict_cfg or "should_panic" not in scope_err
                            ):
                                return None, f"{rel_path}::{target_label} {scope_kind} {scope_err}"
                        outer_end = max(outer_end, a_end)
                    elif (
                        is_inner
                        and _find_rust_enclosing_delimiters(code, a_start)
                        == c_enclosing[: enc_idx + 1]
                    ):
                        scope_err = _is_disabling_cfg_attr(
                            inner, allow_cfg_test=True, is_inner=True
                        )
                        if scope_err is not None and (
                            strict_cfg or "should_panic" not in scope_err
                        ):
                            return None, f"{rel_path}::{target_label} {scope_kind} {scope_err}"
                mod_decl = code[outer_end:open_pos]
                mod_m = mod_decl_re.fullmatch(mod_decl)
                if mod_m is None:
                    return None, (
                        f"{rel_path}::{target_label} nested inside non-module "
                        f"{scope_kind} (only top-level or `mod` #[test] runs)"
                    )
                mod_parts.append(mod_m.group(1))
            return tuple(mod_parts), None

        test_mod_scope, scope_err = _check_enclosing_scope(
            fn_name, enclosing, strict_cfg=True
        )
        if scope_err is not None or test_mod_scope is None:
            return None, None, scope_err, False

        # Check inner `#![...]` attributes placed directly inside test fn body.
        fn_body_enclosing = [*enclosing, ("{", body_open)]
        for a_start, _a_end, inner, is_inner in all_attrs:
            if (
                is_inner
                and body_open < a_start < body_close
                and _find_rust_enclosing_delimiters(code, a_start)
                == fn_body_enclosing
            ):
                fn_inner_err = _is_disabling_cfg_attr(
                    inner, allow_cfg_test=False, is_inner=True
                )
                if fn_inner_err is not None:
                    return (
                        None,
                        None,
                        f"{rel_path}::{fn_name} {fn_inner_err}",
                        False,
                    )

        pure_rust_fns, init_rust_env, rust_facts = (
            _collect_rust_file_const_facts(code, scanned.code_no_comments)
        )
        raw_fn = text[item_start : body_close + 1]
        fn_code = scanned.code_no_comments[body_open : body_close + 1]
        fn_code_ns = code[body_open : body_close + 1]
        live_fn_c, live_fn_ns = _strip_unreachable_rust_test_code(
            fn_code, fn_code_ns
        )
        for _a_s, _a_e, inner, is_inner in _find_rust_attributes(
            live_fn_ns, live_fn_c
        ):
            stmt_cfg_err = _is_disabling_cfg_attr(
                inner, allow_cfg_test=True, is_inner=is_inner
            )
            if stmt_cfg_err is not None:
                return (
                    None,
                    None,
                    f"{rel_path}::{fn_name} statement {stmt_cfg_err}",
                    False,
                )
        proc_exit_box: list[bool] = []
        fail_on_success_box: list[bool] = []
        items, cfg_root = _collect_rust_assertion_items_with_cfg(
            fn_code,
            fn_code_ns,
            init_env=init_rust_env,
            pure_rust_fns=pure_rust_fns,
            rust_facts=rust_facts,
            test_mod_scope=test_mod_scope,
            saw_proc_exit=proc_exit_box,
            saw_fail_on_success=fail_on_success_box,
        )
        if fail_on_success_box and fail_on_success_out is not None:
            fail_on_success_out.append(True)
        if proc_exit_box:
            return (
                None,
                None,
                f"{rel_path}::{fn_name} may invoke process-level exit(0), "
                "masking failing assertions or sibling tests",
                False,
            )

        # Verify no active sibling `#[test]` in the binary calls `exit(0)`.
        all_candidates = _find_rust_fn_candidates(
            code, outer_attr_by_end, inner_attr_by_end, fn_name=None
        )
        for s_name, _s_as, s_bo, s_bc, s_attrs, s_encl in all_candidates:
            if s_bo == body_open:
                continue
            if not any(
                test_attr_re.fullmatch(re.sub(r"\s+", "", inner))
                for _as, _ae, inner, is_inner in s_attrs
                if not is_inner
            ):
                continue
            if any(
                (err_r := _is_disabling_cfg_attr(
                    inner, allow_cfg_test=True, is_inner=is_inner
                )) is not None
                and "should_panic" not in err_r
                for _as, _ae, inner, is_inner in s_attrs
            ):
                continue
            sib_scope, sib_err = _check_enclosing_scope(
                s_name, s_encl, strict_cfg=False
            )
            if sib_err is not None or sib_scope is None:
                continue
            sib_body_encl = [*s_encl, ("{", s_bo)]
            if any(
                is_inner
                and s_bo < a_start < s_bc
                and _find_rust_enclosing_delimiters(code, a_start) == sib_body_encl
                and (
                    (fn_ir := _is_disabling_cfg_attr(
                        inner, allow_cfg_test=True, is_inner=True
                    )) is not None
                    and "should_panic" not in fn_ir
                )
                for a_start, _a_end, inner, is_inner in all_attrs
            ):
                continue
            sib_exit_box: list[bool] = []
            _collect_rust_assertion_items_with_cfg(
                scanned.code_no_comments[s_bo : s_bc + 1],
                code[s_bo : s_bc + 1],
                init_env=init_rust_env,
                pure_rust_fns=pure_rust_fns,
                rust_facts=rust_facts,
                test_mod_scope=sib_scope,
                saw_proc_exit=sib_exit_box,
            )
            if sib_exit_box:
                return (
                    None,
                    None,
                    f"{rel_path}::{s_name} (sibling #[test] in {rel_path}) "
                    f"may invoke process-level exit(0), masking failing tests "
                    f"in {fn_name}'s binary",
                    False,
                )

        if cfg_out is not None:
            cfg_out.append(cfg_root)
        return raw_fn, items, None, False

    raw_fn, items, py_cfg, py_err = _extract_python_test_assertion_items_with_cfg(
        text, rel_path, fn_name
    )
    if cfg_out is not None and py_cfg is not None:
        cfg_out.append(py_cfg)
    return raw_fn, items, py_err, True


def _extract_test_assertion_items_with_cfg(
    view: RepoView,
    test_ref: str,
    fail_on_success_out: list[bool] | None = None,
) -> tuple[str | None, list[_AssertionItem] | None, object | None, str | None, bool]:
    """Extract live `_AssertionItem` values plus control-flow graph for a test."""
    cfg_box: list[object] = []
    raw_fn, items, err, is_python = _extract_test_assertion_items(
        view,
        test_ref,
        cfg_out=cfg_box,
        fail_on_success_out=fail_on_success_out,
    )
    return raw_fn, items, (cfg_box[0] if cfg_box else None), err, is_python


def _rust_qualified_path_origin_kind(
    expanded_path: str, facts: _RustFileFacts
) -> str | None:
    """Classify a single resolved Rust call path (`::`-separated or local)."""
    ep = expanded_path.lstrip(":")
    if "::" in ep:
        head = ep.split("::", 1)[0]
        tail = ep.rsplit("::", 1)[-1]
        if tail in ("black_box", "identity", "transmute", "forget"):
            return None
        cands = _normalize_local_rust_path(ep, facts.test_mod_scope)
        if any(c in facts.qualified_capture_fns for c in cands):
            return "obs_capture"
        if any(c in facts.qualified_driver_fns for c in cands):
            return "obs_driver"
        if head in facts.local_types_or_mods:
            return None
        if head in (
            "anneal_rustc_capture",
            "cargo_anneal",
            "LeanTraceSession",
            "DifferentialEngine",
        ) or ep.startswith(
            (
                "anneal_itree_diff::lean_trace_runner::",
                "anneal_itree_diff::DifferentialEngine",
            )
        ):
            return "obs_capture"
        if head in (
            "anneal_itree_diff",
            "anneal_audit",
            "MirEvalAdapter",
            "MiriRunner",
            "RustcRunner",
        ):
            return "obs_driver"
        return None
    cands = _normalize_local_rust_path(ep, facts.test_mod_scope)
    if ep in facts.capture_fns or any(
        c in facts.qualified_capture_fns for c in cands
    ):
        return "obs_capture"
    if ep in facts.driver_fns or any(
        c in facts.qualified_driver_fns for c in cands
    ):
        return "obs_driver"
    return None


def _rust_find_call_receiver_start(code_ns: str, dot_pos: int) -> int:
    """Walk backward from `dot_pos` to find the start of a chained receiver."""
    rp = 0
    rb = 0
    rbr = 0
    pos = dot_pos - 1
    while pos >= 0:
        ch = code_ns[pos]
        if ch == ")":
            rp += 1
        elif ch == "(":
            if rp == 0:
                return pos + 1
            rp -= 1
        elif ch == "]":
            rb += 1
        elif ch == "[":
            if rb == 0:
                return pos + 1
            rb -= 1
        elif ch == "}":
            rbr += 1
        elif ch == "{":
            if rbr == 0:
                return pos + 1
            rbr -= 1
        elif rp == 0 and rb == 0 and rbr == 0:
            if ch in ";,=":
                return pos + 1
            if ch in "&|" and pos > 0 and code_ns[pos - 1] == ch:
                return pos + 1
            if ch == ">" and pos > 0 and code_ns[pos - 1] == "=":
                return pos + 1
        pos -= 1
    return 0


def _rust_blank_closures_and_fallbacks(
    expr_nc: str, expr_ns: str
) -> tuple[str, str]:
    """Blank closure bodies and fallback combinator args (e.g. `unwrap_or`)."""
    chars_nc = list(expr_nc)
    chars_ns = list(expr_ns)
    for cs, ce in _find_rust_closure_body_spans(expr_ns):
        _blank_span(chars_ns, cs, ce)
        if ce <= len(chars_nc):
            _blank_span(chars_nc, cs, ce)
    # Also blank argument lists of fallback combinators so an unexecuted
    # fallback (`Command::new("echo").output().unwrap_or(capture())`) cannot
    # launder an unverified primary expression as observed.
    cur_ns = "".join(chars_ns)
    for fm in re.finditer(
        r"\.\s*(?:unwrap_or|unwrap_or_else|or|or_else)\s*\(", cur_ns
    ):
        op = fm.end() - 1
        cl = _find_matching_delimiter_in_code(cur_ns, op)
        if cl is not None and cl > op + 1:
            _blank_span(chars_ns, op + 1, cl)
            if cl <= len(chars_nc):
                _blank_span(chars_nc, op + 1, cl)
    return "".join(chars_nc), "".join(chars_ns)


def _rust_expr_origin_kind(
    tested_expr_nc: str,
    tested_expr_ns: str | None = None,
    *,
    rust_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
    rust_type_env: dict[str, str] | None = None,
) -> str | None:
    """Return `'obs_capture'`, `'obs_driver'`, or None for a Rust expression.

    Observations in bound Rust tests must originate from executing the capture
    or driver under test (or a local helper whose body invokes it) rather than
    arbitrary pure/external calls such as `std::hint::black_box(...)`.
    """
    if tested_expr_ns is None:
        scanned = scan_rust_tokens(tested_expr_nc)
        expr_nc = scanned.code_no_comments
        raw_ns = scanned.code_no_strings_or_comments
    else:
        expr_nc = tested_expr_nc
        raw_ns = tested_expr_ns

    # Peel outer tuple/array literal element selection (`(fake, cap).0` or
    # `[fake, cap][0]`) so discarded elements cannot launder provenance.
    r_nc_s = expr_nc.strip().rstrip(";").strip()
    r_ns_s = raw_ns.strip().rstrip(";").strip()
    tup_idx_m = re.search(r"\.\s*(\d+)\s*$", r_ns_s)
    if tup_idx_m is not None:
        base_ns = r_ns_s[: tup_idx_m.start()].rstrip()
        base_nc = r_nc_s[: len(base_ns)].rstrip()
        if (
            base_ns.startswith("(")
            and base_ns.endswith(")")
            and _find_matching_delimiter_in_code(base_ns, 0) == len(base_ns) - 1
        ):
            elems_ns = _split_top_level_commas(
                base_ns[1:-1], keep_literal_only=True
            )
            elems_nc = _split_top_level_commas(
                base_nc[1:-1], keep_literal_only=True
            )
            idx_val = int(tup_idx_m.group(1))
            if idx_val >= len(elems_ns) or len(elems_ns) != len(elems_nc):
                return None
            return _rust_expr_origin_kind(
                elems_nc[idx_val],
                elems_ns[idx_val],
                rust_env=rust_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )
    arr_idx_m = re.search(r"\[\s*(\d+)\s*\]\s*$", r_ns_s)
    if arr_idx_m is not None:
        base_ns = r_ns_s[: arr_idx_m.start()].rstrip()
        base_nc = r_nc_s[: len(base_ns)].rstrip()
        if (
            base_ns.startswith("[")
            and base_ns.endswith("]")
            and _find_matching_delimiter_in_code(base_ns, 0) == len(base_ns) - 1
        ):
            elems_ns = _split_top_level_commas(
                base_ns[1:-1], keep_literal_only=True
            )
            elems_nc = _split_top_level_commas(
                base_nc[1:-1], keep_literal_only=True
            )
            idx_val = int(arr_idx_m.group(1))
            if idx_val >= len(elems_ns) or len(elems_ns) != len(elems_nc):
                return None
            return _rust_expr_origin_kind(
                elems_nc[idx_val],
                elems_ns[idx_val],
                rust_env=rust_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )

    expr_nc, clean_raw_ns = _rust_blank_closures_and_fallbacks(expr_nc, raw_ns)
    code_ns = _strip_rust_numeric_literals(clean_raw_ns)
    facts = rust_facts or _RustFileFacts()
    aliases = facts.use_aliases or {}
    local_free = facts.local_free_fns or facts.local_fns
    found_driver = False

    # 1. Subprocess `.output()` / `.status()` on a verified capture/driver cmd.
    # Verify empty arg list and inspect ONLY the receiver before `.output()` /
    # `.status()` so `dummy.output(fake)` or `Command::new("sh")...output()`
    # cannot inherit provenance from unrelated sub-expressions.
    for om in re.finditer(r"(\.)\s*(?:output|status)\s*\(", code_ns):
        open_p = om.end() - 1
        close_p = _find_matching_delimiter_in_code(code_ns, open_p)
        if close_p is None or code_ns[open_p + 1 : close_p].strip():
            continue
        recv_start = _rust_find_call_receiver_start(code_ns, om.start(1))
        recv_nc = expr_nc[recv_start : om.start(1)]
        recv_ns = code_ns[recv_start : om.start(1)]
        if not recv_ns.strip():
            continue
        ck = _rust_expr_cmd_kind(
            recv_nc,
            recv_ns,
            rust_env=rust_env,
            rust_type_env=rust_type_env,
            rust_facts=facts,
        )
        if ck == "cmd_capture":
            return "obs_capture"
        if ck == "cmd_driver":
            found_driver = True

    # 2. Method calls to verified local capture/driver helpers (scoped).
    cap_mtypes = facts.method_capture_types or {}
    drv_mtypes = facts.method_driver_types or {}
    all_mtypes = facts.method_all_types or {}
    for m in re.finditer(
        r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(", code_ns
    ):
        dot_pos = m.start(1)
        mname = m.group(2)
        if _rust_method_matches_kind(
            mname,
            expr_nc,
            code_ns,
            dot_pos,
            allowed_types=cap_mtypes,
            all_types=all_mtypes,
            type_env=rust_type_env,
            facts=facts,
        ):
            return "obs_capture"
        if _rust_method_matches_kind(
            mname,
            expr_nc,
            code_ns,
            dot_pos,
            allowed_types=drv_mtypes,
            all_types=all_mtypes,
            type_env=rust_type_env,
            facts=facts,
        ):
            found_driver = True

    # 3. Free or associated calls to capture/driver entrypoints or helpers.
    for m in re.finditer(
        r"(?<!\.)\b((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
        r"[A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(",
        code_ns,
    ):
        if m.start() > 0 and code_ns[m.start() - 1] == ".":
            continue
        path = re.sub(r"\s+", "", m.group(1)).lstrip(":")
        if path in PURE_RUST_IDENT_IGNORED:
            continue
        if "::" in path:
            expanded = _resolve_rust_qualified_path(path, facts)
            kinds = [
                _rust_qualified_path_origin_kind(ep, facts) for ep in expanded
            ]
            if kinds and all(k == "obs_capture" for k in kinds):
                return "obs_capture"
            if kinds and all(k in ("obs_capture", "obs_driver") for k in kinds):
                found_driver = True
        else:
            # Local variable/closure/nested-fn binding takes precedence over
            # external harness heuristics (e.g. `let run_capture = || ...`).
            if rust_env is not None and path in rust_env:
                st = rust_env[path]
                if st == "obs_capture":
                    return "obs_capture"
                if st in ("obs_driver", "observed"):
                    found_driver = True
                continue
            # Imported `use` alias must resolve to a verified target path
            # rather than trusting the alias identifier name.
            if path in aliases:
                expanded = _resolve_rust_qualified_path(path, facts)
                kinds = [
                    _rust_qualified_path_origin_kind(ep, facts)
                    for ep in expanded
                ]
                if kinds and all(k == "obs_capture" for k in kinds):
                    return "obs_capture"
                if kinds and all(
                    k in ("obs_capture", "obs_driver") for k in kinds
                ):
                    found_driver = True
                continue
            cands = _normalize_local_rust_path(path, facts.test_mod_scope)
            if path in facts.capture_fns or any(
                c in facts.qualified_capture_fns for c in cands
            ):
                return "obs_capture"
            if path in facts.driver_fns or any(
                c in facts.qualified_driver_fns for c in cands
            ):
                found_driver = True
            elif path not in local_free and path not in facts.local_types_or_mods:
                if CAPTURE_HARNESS_FN_RE.fullmatch(path) is not None:
                    return "obs_capture"
                if DRIVER_HARNESS_FN_RE.fullmatch(path) is not None:
                    found_driver = True

    # 4. Dataflow propagation from tainted variables in `rust_env`.
    for m in re.finditer(r"\b([A-Za-z_][A-Za-z0-9_]*)\b", code_ns):
        ident = m.group(1)
        if ident in PURE_RUST_IDENT_IGNORED or ident in (
            "None",
            "Some",
            "Ok",
            "Err",
        ):
            continue
        before = code_ns[: m.start()].rstrip()
        if before.endswith(".") or before.endswith("::"):
            continue
        after = code_ns[m.end() :].lstrip()
        if after.startswith(("!", "(", "::")):
            continue
        if rust_env is None:
            if ident[0].islower() or (
                ident[0] == "_" and any(c.islower() for c in ident)
            ):
                found_driver = True
        else:
            st = rust_env.get(ident)
            if st == "obs_capture":
                return "obs_capture"
            if st in ("obs_driver", "observed"):
                found_driver = True

    return "obs_driver" if found_driver else None


def _rust_expr_has_observed_value(
    tested_expr: str,
    *,
    rust_env: dict[str, str] | None = None,
    pure_rust_fns: frozenset[str] = frozenset(),
    rust_facts: _RustFileFacts | None = None,
) -> bool:
    """Return True if Rust `tested_expr` flows from a capture/driver call."""
    facts = rust_facts or _RustFileFacts(local_fns=pure_rust_fns)
    return (
        _rust_expr_origin_kind(
            tested_expr, rust_env=rust_env, rust_facts=facts
        )
        in RUST_OBS_STATES
    )


def _py_expr_has_observed_value(
    tested_expr: str,
    *,
    env: dict[str, str] | None = None,
    self_attrs: dict[str, str] | None = None,
    pure_fns: frozenset[str] = frozenset(),
    py_facts: _PyFileFacts | None = None,
    const_vals: dict[str, object] | None = None,
    type_env: dict[str, str] | None = None,
) -> bool:
    """Return True if Python `tested_expr` references an observed var/call."""
    try:
        tree = ast.parse(tested_expr, mode="eval")
    except SyntaxError:
        return False
    if env is not None:
        return _py_expr_ast_is_observed(
            tree.body,
            env=env,
            self_attrs=self_attrs or {},
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
        )
    ignore = frozenset(
        {
            "True",
            "False",
            "None",
            "len",
            "bool",
            "int",
            "str",
            "bytes",
            "list",
            "dict",
            "set",
            "tuple",
            "repr",
        }
    )
    return any(
        isinstance(sub, ast.Name) and sub.id not in ignore
        for sub in ast.walk(tree)
    )


def _split_top_level_rust_op(
    expr: str, op: str
) -> list[tuple[int, int, str]]:
    """Split `expr` on depth-0 `op` (`'||'` or `'&&'`) outside strings."""
    code_ns = scan_rust_tokens(expr).code_no_strings_or_comments
    out: list[tuple[int, int, str]] = []
    p_d = b_d = br_d = 0
    start = 0
    i = 0
    n = len(code_ns)
    while i < n:
        ch = code_ns[i]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif (
            p_d == 0
            and b_d == 0
            and br_d == 0
            and code_ns[i : i + 2] == op
        ):
            out.append((start, i, expr[start:i]))
            i += 2
            start = i
            continue
        i += 1
    out.append((start, n, expr[start:]))
    return out


def _rust_clause_is_static_false(clause_expr: str) -> bool:
    """Return True if a Rust logical clause is statically `false`."""
    ns = scan_rust_tokens(clause_expr).code_no_strings_or_comments.strip()
    return _eval_rust_static_bool_cond(ns) is False


def _rust_strip_outer_parens(expr: str) -> str:
    """Strip whitespace and balanced outer parentheses from a Rust expression."""
    s = expr.strip()
    while s.startswith("(") and s.endswith(")"):
        ns = scan_rust_tokens(s).code_no_strings_or_comments
        if _find_matching_delimiter_in_code(ns, 0) != len(ns) - 1:
            break
        s = s[1:-1].strip()
    return s


def _rust_expr_is_bool_predicate(expr: str) -> bool:
    """Return True if `expr` is a boolean comparison, logical op, or predicate call."""
    s = _rust_strip_outer_parens(expr)
    if not s:
        return False
    ns = scan_rust_tokens(s).code_no_strings_or_comments.strip()
    if not ns:
        return False
    if ns.startswith("!"):
        return True
    for op in ("==", "!=", "&&", "||", "<=", ">="):
        if len(_split_top_level_rust_op(s, op)) > 1:
            return True
    if re.match(r"^(?:(?:core|std)\s*::\s*)?matches\s*!\s*[(\[{]", ns):
        return True
    if ns.endswith(")"):
        # Match final `(...)` back to its opening `(`.
        depth = 0
        open_p = -1
        for i in range(len(ns) - 1, -1, -1):
            if ns[i] == ")":
                depth += 1
            elif ns[i] == "(":
                depth -= 1
                if depth == 0:
                    open_p = i
                    break
        if open_p > 0:
            prefix = ns[:open_p]
            if re.search(
                r"\.\s*(?:contains|starts_with|ends_with|find|rfind|"
                r"is_ok|is_err|is_some|is_none|is_empty|success|"
                r"any|all|eq|ne)\s*(?:::\s*<[^;()]*>)?\s*$",
                prefix,
            ):
                return True
    return False


def _rust_extract_call_receiver(expr: str, expr_ns: str, dot_pos: int) -> str:
    """Scan backward from `.method(` at `dot_pos` to extract the receiver expr."""
    rp_d = 0
    rb_d = 0
    rbr_d = 0
    pos = dot_pos - 1
    start_idx = 0
    while pos >= 0:
        ch = expr_ns[pos]
        if ch == ")":
            rp_d += 1
        elif ch == "(":
            if rp_d == 0:
                start_idx = pos + 1
                break
            rp_d -= 1
        elif ch == "]":
            rb_d += 1
        elif ch == "[":
            if rb_d == 0:
                start_idx = pos + 1
                break
            rb_d -= 1
        elif ch == "}":
            rbr_d += 1
        elif ch == "{":
            if rbr_d == 0:
                start_idx = pos + 1
                break
            rbr_d -= 1
        elif rp_d == 0 and rb_d == 0 and rbr_d == 0:
            if ch in ";,|":
                start_idx = pos + 1
                break
            if ch == "=" and (pos == 0 or expr_ns[pos - 1] in "=!<>&| \t\n"):
                start_idx = pos + 1
                break
            if ch == ">" and pos > 0 and expr_ns[pos - 1] == "=":
                start_idx = pos + 1
                break
            if ch == "&" and pos > 0 and expr_ns[pos - 1] == "&":
                start_idx = pos + 1
                break
            if ch == "!" and (pos == 0 or expr_ns[pos - 1] not in "A-Za-z0-9_"):
                if not re.search(r"[A-Za-z0-9_]\s*$", expr_ns[:pos]):
                    start_idx = pos + 1
                    break
        pos -= 1
    return expr[start_idx:dot_pos].strip()


def _rust_strip_trailing_adapters(recv: str) -> str:
    """Strip harmless trailing `.iter()` / `.as_str()` / `.to_string()` adapters."""
    s = _rust_strip_outer_parens(recv)
    adapter_re = re.compile(
        r"\.\s*(?:iter|iter_mut|into_iter|as_str|as_bytes|as_slice|as_ref|"
        r"to_string|to_owned|to_lowercase|to_ascii_lowercase|trim|lines|"
        r"chars|bytes|deref|clone)\s*\(\s*\)\s*$"
    )
    while True:
        m = adapter_re.search(s)
        if m is None:
            break
        s = _rust_strip_outer_parens(s[: m.start()])
    return s


def _rust_operand_is_trusted_projection(
    expr_nc: str,
    expr_ns: str | None = None,
    *,
    rust_env: dict[str, str] | None = None,
    type_env: dict[str, str] | None = None,
    facts: _RustFileFacts | None = None,
    allow_direct_capture_struct: bool = False,
    _depth: int = 0,
) -> bool:
    """Require concrete trusted output/string/status projections (reject custom PartialEq/wrappers)."""
    if _depth > 14:
        return False
    rfacts = facts or _RustFileFacts()
    if "__blanket__" in rfacts.custom_eq_types:
        return False
    if expr_ns is None:
        scanned = scan_rust_tokens(expr_nc)
        s_nc = scanned.code_no_comments.strip()
        s_ns = scanned.code_no_strings_or_comments.strip()
    else:
        s_nc = expr_nc.strip()
        s_ns = expr_ns.strip()
    s_nc = s_nc.rstrip(";").strip()
    s_ns = s_ns.rstrip(";").strip()

    # Unwrap outer balanced parens and unary `&`, `&mut`, `*`, `!`, `-`.
    for _ in range(8):
        changed = False
        while s_ns.startswith("(") and s_ns.endswith(")"):
            if _find_matching_delimiter_in_code(s_ns, 0) != len(s_ns) - 1:
                break
            s_ns = s_ns[1:-1].strip()
            if s_nc.startswith("(") and s_nc.endswith(")"):
                s_nc = s_nc[1:-1].strip()
            changed = True
        un_m = re.match(r"^(?:&\s*(?:mut\s+)?|\*\s*|!(?!=)\s*|-\s*)", s_ns)
        if un_m is not None:
            s_ns = s_ns[un_m.end() :].strip()
            un_nc = re.match(r"^(?:&\s*(?:mut\s+)?|\*\s*|!(?!=)\s*|-\s*)", s_nc)
            if un_nc is not None:
                s_nc = s_nc[un_nc.end() :].strip()
            changed = True
        if not changed:
            break

    # Empty `ns` means string/char/byte literal (`"..."`, `b"..."`, `r#"..."#`).
    if not s_ns:
        return True
    # Numeric / boolean literals.
    if s_ns in ("true", "false") or re.fullmatch(
        r"(?:0x[0-9a-fA-F_]+|0b[01_]+|0o[0-7_]+|\d+(?:_\d+)*)"
        r"(?:[ui](?:8|16|32|64|128|size)|f(?:32|64))?",
        s_ns,
    ):
        return True

    # Tuple `(a, b, ...)`
    tup_elems = _split_rust_tuple_elems(s_nc)
    if tup_elems is not None:
        return all(
            _rust_operand_is_trusted_projection(
                el,
                rust_env=rust_env,
                type_env=type_env,
                facts=rfacts,
                allow_direct_capture_struct=allow_direct_capture_struct,
                _depth=_depth + 1,
            )
            for el in tup_elems
        )

    # Array / slice literal `[a, b]`
    if s_ns.startswith("[") and _find_matching_delimiter_in_code(s_ns, 0) == len(s_ns) - 1:
        elems = [
            e.strip()
            for e in _split_top_level_commas(s_nc[1:-1], keep_literal_only=True)
            if e.strip()
        ]
        return all(
            _rust_operand_is_trusted_projection(
                el,
                rust_env=rust_env,
                type_env=type_env,
                facts=rfacts,
                _depth=_depth + 1,
            )
            for el in elems
        )

    # Top-level binary operators (`&&`, `||`, `==`, `!=`, `<=`, `>=`, `+`).
    for op in ("||", "&&", "==", "!=", "<=", ">="):
        parts = _split_top_level_rust_op(s_nc, op)
        if len(parts) > 1:
            return all(
                _rust_operand_is_trusted_projection(
                    p[2],
                    rust_env=rust_env,
                    type_env=type_env,
                    facts=rfacts,
                    _depth=_depth + 1,
                )
                for p in parts
            )

    # Trailing `?` try operator.
    if s_ns.endswith("?"):
        return _rust_operand_is_trusted_projection(
            s_nc[:-1],
            s_ns[:-1],
            rust_env=rust_env,
            type_env=type_env,
            facts=rfacts,
            allow_direct_capture_struct=allow_direct_capture_struct,
            _depth=_depth + 1,
        )

    # Struct literal `Foo { ... }` -> trusted ONLY if `Foo` is trusted.
    if s_ns.endswith("}"):
        open_b = _find_matching_open_delimiter(s_ns, len(s_ns) - 1)
        if open_b is not None and open_b > 0:
            head = s_ns[:open_b].strip()
            hm = re.fullmatch(
                r"(?:(?:::\s*)?[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*([A-Z][A-Za-z0-9_]*)",
                head,
            )
            if hm is not None:
                ty_name = hm.group(1)
                return (
                    ty_name in TRUSTED_RUST_VALUE_TYPES
                    and ty_name not in rfacts.local_types_or_mods
                    and ty_name not in rfacts.custom_eq_types
                )

    # Indexing `base[idx]` -> validate `base` (e.g. `failure["status"]`).
    if s_ns.endswith("]"):
        open_sq = _find_matching_open_delimiter(s_ns, len(s_ns) - 1)
        if open_sq is not None and open_sq > 0:
            pref = s_ns[:open_sq].rstrip()
            if not pref.endswith("!"):
                return _rust_operand_is_trusted_projection(
                    s_nc[:open_sq],
                    s_ns[:open_sq],
                    rust_env=rust_env,
                    type_env=type_env,
                    facts=rfacts,
                    _depth=_depth + 1,
                )

    # Macro calls `format!(...)`, `vec![...]`, `concat!(...)`, `json!(...)`,
    # `matches!(...)`, `env!(...)`, `stringify!(...)`.
    mac_m = re.match(
        r"^(?:(?:::\s*)?(?:core|std|alloc|serde_json)\s*::\s*)?"
        r"([A-Za-z_][A-Za-z0-9_]*)\s*!\s*([(\[{])",
        s_ns,
    )
    if mac_m is not None:
        m_open = mac_m.end() - 1
        if _find_matching_delimiter_in_code(s_ns, m_open) == len(s_ns) - 1:
            mname = mac_m.group(1)
            if mname in ("format", "concat", "vec", "json", "stringify", "env", "option_env"):
                inner_nc = s_nc[m_open + 1 : -1]
                # Ensure no custom-eq or untrusted wrapper hides in macro args.
                for arg in _split_top_level_commas(inner_nc, keep_literal_only=True):
                    a_s = arg.strip()
                    if not a_s or mname in ("json", "stringify", "env", "option_env"):
                        continue
                    # Skip named format args `k = expr` -> check RHS.
                    eq_a = _find_rust_top_level_equal(
                        scan_rust_tokens(a_s).code_no_strings_or_comments
                    )
                    sub_a = a_s[eq_a + 1 :].strip() if eq_a is not None else a_s
                    if sub_a and not _rust_operand_is_trusted_projection(
                        sub_a,
                        rust_env=rust_env,
                        type_env=type_env,
                        facts=rfacts,
                        _depth=_depth + 1,
                    ):
                        return False
                return True
            if mname == "matches":
                inner_nc = s_nc[m_open + 1 : -1]
                m_args = _split_top_level_commas(inner_nc, keep_literal_only=True)
                if m_args:
                    return _rust_operand_is_trusted_projection(
                        m_args[0],
                        rust_env=rust_env,
                        type_env=type_env,
                        facts=rfacts,
                        _depth=_depth + 1,
                    )
                return False

    # Trailing method call `base.method(args...)` (with optional turbofish).
    if s_ns.endswith(")"):
        open_p = _find_matching_open_delimiter(s_ns, len(s_ns) - 1)
        if open_p is not None and open_p > 0:
            before_p = s_ns[:open_p].rstrip()
            # Strip trailing turbofish `::<...>` before `(`.
            tf_m = re.search(r"::\s*<[^;()]*>\s*$", before_p)
            head_no_tf = before_p[: tf_m.start()].rstrip() if tf_m is not None else before_p
            meth_m = re.search(r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*$", head_no_tf)
            if meth_m is not None:
                dot_pos = meth_m.start(1)
                mname = meth_m.group(2)
                if mname in rfacts.extension_overridden_methods:
                    return False
                if mname == "into":
                    return False
                recv_nc = s_nc[:dot_pos].strip()
                recv_ns = s_ns[:dot_pos].strip()
                recv_ty = _infer_rust_receiver_type(
                    s_nc, s_ns, dot_pos, type_env=type_env, facts=rfacts
                )
                if recv_ty is not None and recv_ty in rfacts.custom_eq_types:
                    return False
                ovr_types = (rfacts.method_override_types or {}).get(mname)
                if ovr_types and (recv_ty is None or recv_ty in ovr_types):
                    return False
                unt_mtypes = (rfacts.method_returns_untrusted_types or {}).get(mname)
                if unt_mtypes and (recv_ty is None or recv_ty in unt_mtypes):
                    if not (
                        allow_direct_capture_struct
                        and recv_ty not in rfacts.custom_eq_types
                    ):
                        return False
                # Verified capture/driver method (e.g. `harness.execute()` or
                # `cmd.output()`).
                if mname in ("output", "status") or _rust_method_matches_kind(
                    mname,
                    s_nc,
                    s_ns,
                    dot_pos,
                    allowed_types=rfacts.method_capture_types or {},
                    all_types=rfacts.method_all_types or {},
                    type_env=type_env,
                    facts=rfacts,
                ) or _rust_method_matches_kind(
                    mname,
                    s_nc,
                    s_ns,
                    dot_pos,
                    allowed_types=rfacts.method_driver_types or {},
                    all_types=rfacts.method_all_types or {},
                    type_env=type_env,
                    facts=rfacts,
                ):
                    return True
                # Reject local user-defined helper methods on non-trusted types
                # (e.g. `out.wrap()` via a local extension trait).
                if mname in (rfacts.method_all_types or {}) and mname not in PURE_RUST_METHODS:
                    return False
                if not _rust_operand_is_trusted_projection(
                    recv_nc,
                    recv_ns,
                    rust_env=rust_env,
                    type_env=type_env,
                    facts=rfacts,
                    _depth=_depth + 1,
                ):
                    return False
                # Check method args for custom-eq or wrapper spoofs
                # (e.g. `.eq(&Evil(...))`).
                if mname in ("eq", "ne", "contains", "starts_with", "ends_with", "find", "rfind"):
                    m_args_nc = _split_top_level_commas(
                        s_nc[open_p + 1 : -1], keep_literal_only=True
                    )
                    for ma in m_args_nc:
                        if ma.strip() and not _rust_operand_is_trusted_projection(
                            ma,
                            rust_env=rust_env,
                            type_env=type_env,
                            facts=rfacts,
                            _depth=_depth + 1,
                        ):
                            return False
                return True

            # Free / associated / constructor call `Path(args...)`.
            call_m = re.fullmatch(
                r"(?:(?:::\s*)?[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*[A-Za-z_][A-Za-z0-9_]*",
                head_no_tf,
            )
            if call_m is not None:
                path = re.sub(r"\s+", "", head_no_tf).lstrip(":")
                aliases = rfacts.use_aliases or {}
                expanded = (
                    _resolve_rust_qualified_path(path, rfacts)
                    if ("::" in path or path in aliases)
                    else [path]
                )
                c_args_nc = _split_top_level_commas(
                    s_nc[open_p + 1 : -1], keep_literal_only=True
                )

                # Reject local fns returning custom-eq / opaque / untrusted
                # types.
                for ep in expanded:
                    cands = _normalize_local_rust_path(ep, rfacts.test_mod_scope)
                    ret_ty = (rfacts.fn_return_types or {}).get(ep)
                    if ret_ty is None:
                        for c in cands:
                            if c in (rfacts.fn_return_types or {}):
                                ret_ty = (rfacts.fn_return_types or {})[c]
                                break
                    is_untrusted_ret = (
                        ("::" not in ep and ep in rfacts.fn_returns_untrusted)
                        or any(c in rfacts.qualified_fn_returns_untrusted for c in cands)
                        or (
                            ret_ty is not None
                            and ret_ty not in TRUSTED_RUST_VALUE_TYPES
                        )
                    )
                    if is_untrusted_ret:
                        is_cap_or_drv = _rust_qualified_path_origin_kind(ep, rfacts) in (
                            "obs_capture",
                            "obs_driver",
                        )
                        if not (
                            allow_direct_capture_struct
                            and is_cap_or_drv
                            and ret_ty not in rfacts.custom_eq_types
                            and ret_ty not in ("__opaque_impl__", "__opaque_dyn__")
                        ):
                            return False

                # Check verified capture/driver calls directly.
                if "::" not in path and path not in aliases:
                    if (
                        path in rfacts.capture_fns
                        or path in rfacts.driver_fns
                        or any(
                            c in rfacts.qualified_capture_fns
                            or c in rfacts.qualified_driver_fns
                            for c in _normalize_local_rust_path(
                                path, rfacts.test_mod_scope
                            )
                        )
                        or (
                            path not in (rfacts.local_free_fns or rfacts.local_fns)
                            and path not in rfacts.local_types_or_mods
                            and (
                                CAPTURE_HARNESS_FN_RE.fullmatch(path) is not None
                                or DRIVER_HARNESS_FN_RE.fullmatch(path) is not None
                            )
                        )
                    ):
                        return True
                elif all(
                    _rust_qualified_path_origin_kind(ep, rfacts)
                    in ("obs_capture", "obs_driver")
                    for ep in expanded
                ):
                    return True

                # Uppercase constructor or associated call (`Evil(&out)`,
                # `FakeNeedle("...")`, `Evil::new(&out)`, `Some(1)`,
                # `String::from_utf8_lossy(&out.stdout)`).
                last_seg = path.rsplit("::", 1)[-1]
                has_upper_seg = any(
                    seg and seg[0].isupper() for seg in path.split("::")
                )
                if last_seg[0].isupper() or has_upper_seg:
                    for ep in expanded:
                        segs = ep.lstrip(":").split("::")
                        head_seg = segs[0]
                        if (
                            head_seg in rfacts.local_types_or_mods
                            or head_seg in rfacts.custom_eq_types
                        ):
                            return False
                        for seg in segs:
                            if seg and seg[0].isupper():
                                if (
                                    seg in rfacts.local_types_or_mods
                                    or seg in rfacts.custom_eq_types
                                    or seg not in TRUSTED_RUST_PROJECTION_PREFIXES
                                ):
                                    return False
                        if head_seg not in TRUSTED_RUST_PROJECTION_PREFIXES:
                            return False
                    return all(
                        _rust_operand_is_trusted_projection(
                            a,
                            rust_env=rust_env,
                            type_env=type_env,
                            facts=rfacts,
                            _depth=_depth + 1,
                        )
                        for a in c_args_nc
                        if a.strip()
                    )

                # Lowercase helper call (e.g. `parse_status(&out)`,
                # `decode_reason(&out)`, `serde_json::from_slice(&out.stdout)`).
                for ep in expanded:
                    ep_clean = ep.lstrip(":")
                    head_seg = ep_clean.split("::", 1)[0]
                    cands = _normalize_local_rust_path(
                        ep_clean, rfacts.test_mod_scope
                    )
                    is_local_ok = (
                        ("::" not in ep_clean and ep_clean in (rfacts.local_free_fns or rfacts.local_fns))
                        or any(c in (rfacts.fn_return_types or {}) for c in cands)
                    )
                    if not is_local_ok and head_seg not in TRUSTED_RUST_PROJECTION_PREFIXES:
                        return False
                return all(
                    _rust_operand_is_trusted_projection(
                        a,
                        rust_env=rust_env,
                        type_env=type_env,
                        facts=rfacts,
                        _depth=_depth + 1,
                    )
                    for a in c_args_nc
                    if a.strip()
                )

    # Field access `base.field` (e.g. `out.stderr`, `out.status`, `res.reason`).
    fld_m = re.search(r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*|\d+)\s*$", s_ns)
    if fld_m is not None:
        base_nc = s_nc[: fld_m.start(1)].strip()
        base_ns = s_ns[: fld_m.start(1)].strip()
        # Allow projecting a field off a plain non-custom-eq local struct
        # (e.g. `res.stderr`), rejecting custom-eq structs (e.g. `evil.0`).
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", base_ns):
            bty = (type_env or {}).get(base_ns)
            if bty is not None and (
                bty in rfacts.custom_eq_types
                or bty in ("__opaque_impl__", "__opaque_dyn__")
            ):
                return False
            if bty is not None and bty in rfacts.local_types_or_mods:
                return True
        return _rust_operand_is_trusted_projection(
            base_nc,
            base_ns,
            rust_env=rust_env,
            type_env=type_env,
            facts=rfacts,
            _depth=_depth + 1,
        )

    # Path constant or enum variant (`FaultKind::Unsupported`, `Option::None`).
    if re.fullmatch(
        r"(?:(?:::\s*)?[A-Za-z_][A-Za-z0-9_]*\s*::\s*)+[A-Za-z_][A-Za-z0-9_]*",
        s_ns,
    ):
        path = re.sub(r"\s+", "", s_ns).lstrip(":")
        expanded = _resolve_rust_qualified_path(path, rfacts)
        for ep in expanded:
            segs = ep.lstrip(":").split("::")
            head_seg = segs[0]
            if (
                head_seg in rfacts.local_types_or_mods
                or head_seg in rfacts.custom_eq_types
                or head_seg not in TRUSTED_RUST_PROJECTION_PREFIXES
            ):
                return False
        return True

    # Plain identifier (variable or unit struct).
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s_ns):
        if s_ns[0].isupper():
            return (
                s_ns in TRUSTED_RUST_VALUE_TYPES
                and s_ns not in rfacts.local_types_or_mods
                and s_ns not in rfacts.custom_eq_types
            )
        ty = (type_env or {}).get(s_ns)
        if ty is not None:
            if (
                ty in rfacts.custom_eq_types
                or ty in ("__opaque_impl__", "__opaque_dyn__")
                or ty not in TRUSTED_RUST_VALUE_TYPES
            ):
                return False
        return True

    # Fallback: check inferred expression type is not untrusted/custom-eq.
    inf_ty = _infer_rust_expr_type(s_nc, s_ns, type_env=type_env, facts=rfacts)
    if inf_ty is not None and (
        inf_ty in rfacts.custom_eq_types
        or inf_ty in ("__opaque_impl__", "__opaque_dyn__")
        or inf_ty not in TRUSTED_RUST_VALUE_TYPES
    ):
        return False
    return True


def _rust_expr_is_trusted_wrapper_or_capture(
    expr_nc: str,
    expr_ns: str,
    *,
    rust_env: dict[str, str] | None,
    type_env: dict[str, str] | None,
    facts: _RustFileFacts,
) -> bool:
    """Validate RHS in `let x = rhs;` so untrusted wrapper constructors block obs taint."""
    return _rust_operand_is_trusted_projection(
        expr_nc,
        expr_ns,
        rust_env=rust_env,
        type_env=type_env,
        facts=facts,
        allow_direct_capture_struct=True,
    )


def _rust_extract_static_const_str(
    expr_nc: str,
    const_strs: dict[str, str] | None = None,
    _depth: int = 0,
) -> str | None:
    """Evaluate pure literal/constant Rust string expression when statically known."""
    if _depth > 12:
        return None
    s_nc = _rust_strip_outer_parens(expr_nc.strip().rstrip(";").strip())
    while s_nc.startswith("&"):
        s_nc = s_nc[1:].lstrip()
        if s_nc.startswith("mut") and (
            len(s_nc) == 3 or not (s_nc[3].isalnum() or s_nc[3] == "_")
        ):
            s_nc = s_nc[3:].lstrip()
        s_nc = _rust_strip_outer_parens(s_nc)
    if not s_nc:
        return None
    s_nc = _rust_strip_trailing_adapters(s_nc)
    lit = _decode_single_string_literal(s_nc)
    if lit is not None:
        return lit
    if s_nc.startswith('b"') or re.match(r"^br#*", s_nc):
        blit = _decode_single_string_literal(s_nc[1:])
        if blit is not None:
            return blit
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s_nc):
        return (const_strs or {}).get(s_nc)
    plus_parts = _split_top_level_plus(s_nc)
    if len(plus_parts) > 1:
        vals: list[str] = []
        for p in plus_parts:
            v = _rust_extract_static_const_str(p, const_strs, _depth + 1)
            if v is None:
                return None
            vals.append(v)
        return "".join(vals)
    ns = scan_rust_tokens(s_nc).code_no_strings_or_comments.strip()
    mac_m = re.match(
        r"^(?:(?:::\s*)?(?:core|std|alloc)\s*::\s*)?(format|concat)\s*!\s*([(\[{])",
        ns,
    )
    if mac_m is not None:
        m_open = mac_m.end() - 1
        if _find_matching_delimiter_in_code(ns, m_open) == len(ns) - 1:
            inner_nc = s_nc[m_open + 1 : -1]
            if mac_m.group(1) == "concat":
                parts: list[str] = []
                for a in _split_top_level_commas(inner_nc, keep_literal_only=True):
                    if not a.strip():
                        continue
                    v = _rust_extract_static_const_str(a, const_strs, _depth + 1)
                    if v is None:
                        return None
                    parts.append(v)
                return "".join(parts)
            missing = [False]

            def _res_expr(sub: str) -> str:
                v = _rust_extract_static_const_str(sub, const_strs, _depth + 1)
                if v is None:
                    missing[0] = True
                    return ""
                return v

            def _res_id(ident: str) -> str:
                if const_strs and ident in const_strs:
                    return const_strs[ident]
                missing[0] = True
                return ""

            fmt_out = _rust_format_parts(
                inner_nc, resolve_expr_fn=_res_expr, resolve_ident_fn=_res_id
            )
            return None if missing[0] else fmt_out
    if ns.endswith(")"):
        open_p = _find_matching_open_delimiter(ns, len(ns) - 1)
        if open_p is not None and open_p > 0:
            head = re.sub(r"\s+", "", ns[:open_p]).lstrip(":")
            if head in (
                "String::from",
                "std::string::String::from",
                "alloc::string::String::from",
                "Cow::Borrowed",
                "std::borrow::Cow::Borrowed",
                "alloc::borrow::Cow::Borrowed",
                "Box::from",
                "str::from",
                "String::from_utf8_lossy",
            ):
                args = _split_top_level_commas(
                    s_nc[open_p + 1 : -1], keep_literal_only=True
                )
                if len(args) == 1:
                    return _rust_extract_static_const_str(
                        args[0], const_strs, _depth + 1
                    )
    return None


def _rust_extract_unobserved_str_parts(
    expr_nc: str,
    expr_ns: str | None = None,
    *,
    rust_env: dict[str, str] | None = None,
    str_taint: dict[str, str] | None = None,
    const_strs: dict[str, str] | None = None,
    require_capture: bool = False,
    facts: _RustFileFacts | None = None,
    type_env: dict[str, str] | None = None,
    _depth: int = 0,
) -> str:
    """Collect literal/injected/const-var strings carried by a Rust expression."""
    if _depth > 14:
        return ""
    if expr_ns is None:
        scanned = scan_rust_tokens(expr_nc)
        s_nc = scanned.code_no_comments.strip()
        s_ns = scanned.code_no_strings_or_comments.strip()
    else:
        s_nc = expr_nc.strip()
        s_ns = expr_ns.strip()
    s_nc = s_nc.rstrip(";").strip()
    s_ns = s_ns.rstrip(";").strip()

    for _ in range(8):
        changed = False
        while s_ns.startswith("(") and s_ns.endswith(")"):
            if _find_matching_delimiter_in_code(s_ns, 0) != len(s_ns) - 1:
                break
            s_ns = s_ns[1:-1].strip()
            if s_nc.startswith("(") and s_nc.endswith(")"):
                s_nc = s_nc[1:-1].strip()
            changed = True
        un_m = re.match(r"^(?:&\s*(?:mut\s+)?|\*\s*)", s_ns)
        if un_m is not None:
            s_ns = s_ns[un_m.end() :].strip()
            un_nc = re.match(r"^(?:&\s*(?:mut\s+)?|\*\s*)", s_nc)
            if un_nc is not None:
                s_nc = s_nc[un_nc.end() :].strip()
            changed = True
        if not changed:
            break

    if not s_nc:
        return ""
    lit = _decode_single_string_literal(s_nc)
    if lit is not None:
        return lit
    if s_nc.startswith('b"') or re.match(r"^br#*", s_nc):
        blit = _decode_single_string_literal(s_nc[1:])
        if blit is not None:
            return blit
    ch_lit = _decode_single_char_literal(s_nc)
    if ch_lit is not None:
        return ch_lit

    if s_ns.endswith("?"):
        return _rust_extract_unobserved_str_parts(
            s_nc[:-1],
            s_ns[:-1],
            rust_env=rust_env,
            str_taint=str_taint,
            const_strs=const_strs,
            require_capture=require_capture,
            facts=facts,
            type_env=type_env,
            _depth=_depth + 1,
        )

    plus_parts = _split_top_level_plus(s_nc, s_ns)
    if len(plus_parts) > 1:
        return "".join(
            _rust_extract_unobserved_str_parts(
                p,
                rust_env=rust_env,
                str_taint=str_taint,
                const_strs=const_strs,
                require_capture=require_capture,
                facts=facts,
                type_env=type_env,
                _depth=_depth + 1,
            )
            for p in plus_parts
        )

    proj_m = re.search(r"\.\s*(\d+)\s*$", s_ns)
    if proj_m is not None:
        base_s = s_nc[: proj_m.start()].strip()
        tup_elems = _split_rust_tuple_elems(base_s)
        if tup_elems is not None:
            idx = int(proj_m.group(1))
            if 0 <= idx < len(tup_elems):
                return _rust_extract_unobserved_str_parts(
                    tup_elems[idx],
                    rust_env=rust_env,
                    str_taint=str_taint,
                    const_strs=const_strs,
                    require_capture=require_capture,
                    facts=facts,
                    type_env=type_env,
                    _depth=_depth + 1,
                )
            return ""

    tup_elems = _split_rust_tuple_elems(s_nc)
    if tup_elems is not None:
        return "".join(
            _rust_extract_unobserved_str_parts(
                el,
                rust_env=rust_env,
                str_taint=str_taint,
                const_strs=const_strs,
                require_capture=require_capture,
                facts=facts,
                type_env=type_env,
                _depth=_depth + 1,
            )
            for el in tup_elems
        )

    if s_ns.startswith("[") and _find_matching_delimiter_in_code(s_ns, 0) == len(s_ns) - 1:
        elems = [
            e.strip()
            for e in _split_top_level_commas(s_nc[1:-1], keep_literal_only=True)
            if e.strip()
        ]
        return "".join(
            _rust_extract_unobserved_str_parts(
                el,
                rust_env=rust_env,
                str_taint=str_taint,
                const_strs=const_strs,
                require_capture=require_capture,
                facts=facts,
                type_env=type_env,
                _depth=_depth + 1,
            )
            for el in elems
        )

    mac_m = re.match(
        r"^(?:(?:::\s*)?(?:core|std|alloc)\s*::\s*)?(format|format_args|concat|vec)\s*!\s*([(\[{])",
        s_ns,
    )
    if mac_m is not None:
        m_open = mac_m.end() - 1
        if _find_matching_delimiter_in_code(s_ns, m_open) == len(s_ns) - 1:
            mname = mac_m.group(1)
            inner_nc = s_nc[m_open + 1 : -1]
            if mname in ("format", "format_args"):
                return _rust_format_parts(
                    inner_nc,
                    resolve_expr_fn=lambda sub: _rust_extract_unobserved_str_parts(
                        sub,
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    ),
                    resolve_ident_fn=lambda ident: _rust_extract_unobserved_str_parts(
                        ident,
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    ),
                )
            return "".join(
                _rust_extract_unobserved_str_parts(
                    a,
                    rust_env=rust_env,
                    str_taint=str_taint,
                    const_strs=const_strs,
                    require_capture=require_capture,
                    facts=facts,
                    type_env=type_env,
                    _depth=_depth + 1,
                )
                for a in _split_top_level_commas(inner_nc, keep_literal_only=True)
                if a.strip()
            )

    if s_ns.endswith(")"):
        open_p = _find_matching_open_delimiter(s_ns, len(s_ns) - 1)
        if open_p is not None and open_p > 0:
            before_p = s_ns[:open_p].rstrip()
            tf_m = re.search(r"::\s*<[^;()]*>\s*$", before_p)
            head_no_tf = before_p[: tf_m.start()].rstrip() if tf_m is not None else before_p
            meth_m = re.search(r"(\.)\s*([A-Za-z_][A-Za-z0-9_]*)\s*$", head_no_tf)
            if meth_m is not None:
                dot_pos = meth_m.start(1)
                mname = meth_m.group(2)
                recv_nc = s_nc[:dot_pos].strip()
                recv_ns = s_ns[:dot_pos].strip()
                if mname in (
                    "iter",
                    "iter_mut",
                    "into_iter",
                    "as_str",
                    "as_bytes",
                    "as_slice",
                    "as_ref",
                    "to_string",
                    "to_owned",
                    "to_lowercase",
                    "to_ascii_lowercase",
                    "to_uppercase",
                    "to_ascii_uppercase",
                    "trim",
                    "trim_start",
                    "trim_end",
                    "lines",
                    "chars",
                    "bytes",
                    "deref",
                    "clone",
                    "unwrap",
                    "expect",
                    "expect_err",
                    "unwrap_err",
                    "ok",
                    "err",
                    "as_deref",
                    "into_string",
                    "into_boxed_str",
                ):
                    return _rust_extract_unobserved_str_parts(
                        recv_nc,
                        recv_ns,
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    )
                if mname in ("replace", "replacen"):
                    m_args = _split_top_level_commas(
                        s_nc[open_p + 1 : -1], keep_literal_only=True
                    )
                    out_p = _rust_extract_unobserved_str_parts(
                        recv_nc,
                        recv_ns,
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    )
                    if len(m_args) >= 2:
                        out_p += _rust_extract_unobserved_str_parts(
                            m_args[1],
                            rust_env=rust_env,
                            str_taint=str_taint,
                            const_strs=const_strs,
                            require_capture=require_capture,
                            facts=facts,
                            type_env=type_env,
                            _depth=_depth + 1,
                        )
                    return out_p
                if mname in ("join", "concat"):
                    out_p = _rust_extract_unobserved_str_parts(
                        recv_nc,
                        recv_ns,
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    )
                    m_args = _split_top_level_commas(
                        s_nc[open_p + 1 : -1], keep_literal_only=True
                    )
                    if mname == "join" and m_args:
                        out_p += _rust_extract_unobserved_str_parts(
                            m_args[0],
                            rust_env=rust_env,
                            str_taint=str_taint,
                            const_strs=const_strs,
                            require_capture=require_capture,
                            facts=facts,
                            type_env=type_env,
                            _depth=_depth + 1,
                        )
                    return out_p
                return ""
            head_norm = re.sub(r"\s+", "", head_no_tf).lstrip(":")
            if head_norm in (
                "String::from",
                "std::string::String::from",
                "alloc::string::String::from",
                "str::from",
                "Cow::Borrowed",
                "Cow::Owned",
                "std::borrow::Cow::Borrowed",
                "alloc::borrow::Cow::Borrowed",
                "Box::from",
                "ToString::to_string",
                "String::from_utf8_lossy",
                "str::from_utf8",
            ):
                m_args = _split_top_level_commas(
                    s_nc[open_p + 1 : -1], keep_literal_only=True
                )
                if m_args:
                    return _rust_extract_unobserved_str_parts(
                        m_args[0],
                        rust_env=rust_env,
                        str_taint=str_taint,
                        const_strs=const_strs,
                        require_capture=require_capture,
                        facts=facts,
                        type_env=type_env,
                        _depth=_depth + 1,
                    )
            return ""

    if s_ns.endswith("]"):
        open_sq = _find_matching_open_delimiter(s_ns, len(s_ns) - 1)
        if open_sq is not None and open_sq > 0 and not s_ns[:open_sq].rstrip().endswith("!"):
            return _rust_extract_unobserved_str_parts(
                s_nc[:open_sq],
                s_ns[:open_sq],
                rust_env=rust_env,
                str_taint=str_taint,
                const_strs=const_strs,
                require_capture=require_capture,
                facts=facts,
                type_env=type_env,
                _depth=_depth + 1,
            )

    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", s_ns):
        taint = (str_taint or {}).get(s_ns, "")
        obs_kind = _rust_expr_origin_kind(
            s_ns,
            s_ns,
            rust_env=rust_env,
            rust_facts=facts,
            rust_type_env=type_env,
        )
        is_obs = (
            obs_kind == "obs_capture"
            if require_capture
            else obs_kind in ("obs_capture", "obs_driver", "observed")
        )
        if is_obs:
            return taint
        c_val = (const_strs or {}).get(s_ns, "")
        return taint or c_val

    field_m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\s*\.\s*[A-Za-z_][A-Za-z0-9_]*$", s_ns)
    if field_m is not None:
        base_id = field_m.group(1)
        if str_taint and base_id in str_taint:
            return str_taint[base_id]

    return ""


def _rust_receiver_is_clean_observed(
    recv: str,
    needle: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Verify Rust haystack/receiver is genuinely observed without const needle injection."""
    if not _rust_operand_is_trusted_projection(
        recv,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    s = _rust_strip_trailing_adapters(recv)
    while s.startswith("&"):
        s = s[1:].lstrip()
        if s.startswith("mut") and (len(s) == 3 or not (s[3].isalnum() or s[3] == "_")):
            s = s[3:].lstrip()
        s = _rust_strip_trailing_adapters(s)
    if not s:
        return False
    ns = scan_rust_tokens(s).code_no_strings_or_comments.strip()

    # Tuple projection `(a, b).1` -> validate the projected element only.
    proj_m = re.search(r"\.\s*(\d+)\s*$", ns)
    if proj_m is not None:
        base_s = s[: proj_m.start()].strip()
        tup_elems = _split_rust_tuple_elems(base_s)
        if tup_elems is not None:
            idx = int(proj_m.group(1))
            if 0 <= idx < len(tup_elems):
                return _rust_receiver_is_clean_observed(
                    tup_elems[idx], needle, item, require_capture=require_capture
                )
            return False

    if not item.subexpr_observed(s, require_capture=require_capture):
        return False

    # Reject array/slice/vec literal containers `[err, "<const_needle>"]`
    # unless EVERY element is cleanly observed.
    if ns.startswith("[") and _find_matching_delimiter_in_code(ns, 0) == len(ns) - 1:
        elems = [
            e.strip()
            for e in _split_top_level_commas(s[1:-1], keep_literal_only=True)
            if e.strip()
        ]
        return bool(elems) and all(
            _rust_receiver_is_clean_observed(
                el, needle, item, require_capture=require_capture
            )
            for el in elems
        )
    vec_m = re.match(r"^(?:(?:std|alloc)\s*::\s*)?vec\s*!\s*([(\[{])", ns)
    if vec_m is not None:
        open_v = vec_m.end() - 1
        if _find_matching_delimiter_in_code(ns, open_v) == len(ns) - 1:
            inner = s[open_v + 1 : -1]
            elems = [
                e.strip()
                for e in _split_top_level_commas(inner, keep_literal_only=True)
                if e.strip()
            ]
            return bool(elems) and all(
                _rust_receiver_is_clean_observed(
                    el, needle, item, require_capture=require_capture
                )
                for el in elems
            )
    tup_elems = _split_rust_tuple_elems(s)
    if tup_elems is not None:
        return all(
            _rust_receiver_is_clean_observed(
                el, needle, item, require_capture=require_capture
            )
            for el in tup_elems
        )

    # Reject `format!` / `concat!` / `+` / variable-bound / mutated string
    # expressions injecting the literal needle.
    if needle:
        unobs_str = _rust_extract_unobserved_str_parts(
            s,
            ns,
            rust_env=item.rust_env,
            str_taint=item.rust_str_taint,
            const_strs=item.rust_const_strs,
            require_capture=require_capture,
            facts=item.rust_facts,
            type_env=item.rust_type_env,
        )
        if unobs_str and needle in unobs_str:
            return False

    return True


def _rust_needle_occurrence_is_observed(
    tested_expr: str,
    tested_ns: str,
    cs: int,
    pos: int,
    needle: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Verify any enclosing `.contains`/`.find` or receiver literal at `pos` is cleanly observed."""
    # Track enclosing `(` and `[` offsets within `[cs, pos)`.
    paren_stack: list[int] = []
    delim_stack: list[tuple[str, int]] = []
    for idx_c in range(cs, pos):
        ch = tested_ns[idx_c]
        if ch in "([":
            delim_stack.append((ch, idx_c))
            if ch == "(":
                paren_stack.append(idx_c)
        elif ch == ")":
            if paren_stack:
                paren_stack.pop()
            if delim_stack and delim_stack[-1][0] == "(":
                delim_stack.pop()
        elif ch == "]":
            if delim_stack and delim_stack[-1][0] == "[":
                delim_stack.pop()

    # Reject receiver literals (`[err, needle].contains(...)`,
    # `vec![err, needle].contains(...)`, `format!(...).contains(...)`,
    # `(err + " needle").contains(...)`) unless the receiver is observed.
    macro_prefix_re = re.compile(
        r"(?:(?:std|alloc|core)\s*::\s*)?(?:vec|format|concat)\s*!\s*$"
    )
    for d_ch, d_open in reversed(delim_stack):
        d_close = _find_matching_delimiter_in_code(tested_ns, d_open)
        if d_close is None:
            continue
        after_d = tested_ns[d_close + 1 :].lstrip()
        if not after_d.startswith("."):
            continue
        pref = tested_ns[cs:d_open]
        mac_m = macro_prefix_re.search(pref)
        expr_start = cs + mac_m.start() if mac_m is not None else d_open
        if mac_m is None and (
            (d_ch == "[" and re.search(r"[A-Za-z0-9_\])]\s*$", pref))
            or (d_ch == "(" and re.search(r"[A-Za-z0-9_>]\s*$", pref))
        ):
            # Skip genuine indexing or call args `x.find(TAG).is_some()`.
            continue
        recv_sub = tested_expr[expr_start : d_close + 1]
        if not _rust_receiver_is_clean_observed(
            recv_sub, needle, item, require_capture=require_capture
        ):
            return False

    needle_call_re = re.compile(
        r"\.\s*(?:contains|starts_with|ends_with|find|rfind|"
        r"strip_prefix|strip_suffix|matches|match_indices)\s*"
        r"(?:::\s*<[^;()]*>)?\s*$"
    )
    iter_closure_re = re.compile(
        r"\.\s*(?:any|all|find|position|rposition|filter|map|flat_map|"
        r"filter_map|try_for_each|for_each)\s*(?:::\s*<[^;()]*>)?\s*$"
    )
    for open_p in reversed(paren_stack):
        prefix = tested_ns[cs:open_p]
        m = needle_call_re.search(prefix)
        if m is None:
            continue
        dot_pos = cs + m.start()
        recv = _rust_extract_call_receiver(tested_expr, tested_ns, dot_pos)
        # Resolve closure param `|l| l.contains(...)` to outer iterable.
        cur_recv = recv
        cur_open = open_p
        for _ in range(4):
            simple = _rust_strip_trailing_adapters(cur_recv).lstrip("&* ")
            if not re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", simple):
                break
            if item.subexpr_observed(simple, require_capture=require_capture):
                break
            # Find enclosing iterator method whose closure binds `simple`.
            resolved_outer: tuple[str, int] | None = None
            for outer_p in reversed(paren_stack):
                if outer_p >= cur_open:
                    continue
                outer_pref = tested_ns[cs:outer_p]
                im = iter_closure_re.search(outer_pref)
                if im is None:
                    continue
                after_op = tested_ns[outer_p + 1 : cur_open].lstrip()
                if after_op.startswith("move"):
                    after_op = after_op[4:].lstrip()
                cm = re.match(r"^\|([^|]*)\|", after_op)
                if cm is not None and simple in _extract_rust_pattern_idents(
                    cm.group(1)
                ):
                    outer_dot = cs + im.start()
                    outer_recv = _rust_extract_call_receiver(
                        tested_expr, tested_ns, outer_dot
                    )
                    resolved_outer = (outer_recv, outer_p)
                    break
            if resolved_outer is None:
                break
            cur_recv, cur_open = resolved_outer
        if not _rust_receiver_is_clean_observed(
            cur_recv, needle, item, require_capture=require_capture
        ):
            return False
    return True


def _rust_eq_pair_binds_observed_needle(
    lhs: str,
    rhs: str,
    needle: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Verify `lhs == rhs` binds `needle` to concrete trusted observed projections."""
    in_l = needle in lhs
    in_r = needle in rhs
    if not (in_l or in_r):
        return False
    lhs_tup = _split_rust_tuple_elems(lhs)
    rhs_tup = _split_rust_tuple_elems(rhs)
    if (
        lhs_tup is not None
        and rhs_tup is not None
        and len(lhs_tup) == len(rhs_tup)
    ):
        return any(
            _rust_eq_pair_binds_observed_needle(
                a, b, needle, item, require_capture=require_capture
            )
            for a, b in zip(lhs_tup, rhs_tup)
        )
    if not _rust_operand_is_trusted_projection(
        lhs,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ) or not _rust_operand_is_trusted_projection(
        rhs,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    lhs_obs = item.subexpr_observed(lhs, require_capture=require_capture)
    rhs_obs = item.subexpr_observed(rhs, require_capture=require_capture)
    if not (lhs_obs or rhs_obs):
        return False
    if in_l and not lhs_obs:
        if not rhs_obs:
            return False
        if _rust_expr_is_bool_predicate(lhs) or _rust_expr_is_bool_predicate(rhs):
            return False
    if in_r and not rhs_obs:
        if not lhs_obs:
            return False
        if _rust_expr_is_bool_predicate(rhs) or _rust_expr_is_bool_predicate(lhs):
            return False
    if in_l and lhs_obs:
        lhs_ns = scan_rust_tokens(lhs).code_no_strings_or_comments
        if in_r and not rhs_obs and not _rust_receiver_is_clean_observed(
            lhs, needle, item, require_capture=require_capture
        ):
            return False
        p = lhs.find(needle)
        ok_occ = False
        while p != -1:
            if _rust_needle_occurrence_is_observed(
                lhs, lhs_ns, 0, p, needle, item, require_capture=require_capture
            ):
                ok_occ = True
                break
            p = lhs.find(needle, p + len(needle))
        if not ok_occ and not in_r:
            return False
    if in_r and rhs_obs:
        rhs_ns = scan_rust_tokens(rhs).code_no_strings_or_comments
        if in_l and not lhs_obs and not _rust_receiver_is_clean_observed(
            rhs, needle, item, require_capture=require_capture
        ):
            return False
        p = rhs.find(needle)
        ok_occ = False
        while p != -1:
            if _rust_needle_occurrence_is_observed(
                rhs, rhs_ns, 0, p, needle, item, require_capture=require_capture
            ):
                ok_occ = True
                break
            p = rhs.find(needle, p + len(needle))
        if not ok_occ and not in_l:
            return False
    return True


def _rust_matches_pair_binds_observed_needle(
    scrut: str,
    pat: str,
    needle: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Verify `matches!(scrut, pat [if guard])` binds `needle` to observed `scrut`."""
    if not item.subexpr_observed(scrut, require_capture=require_capture):
        return False
    if not _rust_operand_is_trusted_projection(
        scrut,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    pat_ns = scan_rust_tokens(pat).code_no_strings_or_comments
    pat_only_ns, g_off = _strip_rust_match_guard(pat_ns)
    pat_only = pat[:g_off] if g_off is not None else pat
    guard = pat[g_off:].strip() if g_off is not None else ""
    if guard.startswith("if") and (
        len(guard) == 2 or not (guard[2].isalnum() or guard[2] == "_")
    ):
        guard = guard[2:].strip()
    if guard and needle in guard:
        scrut_kind = _rust_expr_origin_kind(
            scrut,
            rust_env=item.rust_env,
            rust_facts=item.rust_facts,
            rust_type_env=item.rust_type_env,
        )
        guard_env = dict(item.rust_env or {})
        for v in _extract_rust_pattern_idents(pat_only_ns):
            guard_env[v] = scrut_kind if scrut_kind is not None else "const"
        guard_okind = _rust_expr_origin_kind(
            guard,
            rust_env=guard_env,
            rust_facts=item.rust_facts,
            rust_type_env=item.rust_type_env,
        )
        guard_item = _AssertionItem(
            full_span=f"assert!({guard})",
            tested_expr=guard,
            is_observed=guard_okind in RUST_OBS_STATES,
            origin_kind=guard_okind,
            tested_args=(guard,),
            rust_env=guard_env,
            rust_type_env=item.rust_type_env,
            pure_rust_fns=item.pure_rust_fns,
            rust_facts=item.rust_facts,
        )
        if _rust_assertion_has_positive_needle(
            guard_item,
            needle,
            require_observed=True,
            require_capture=require_capture,
        ):
            return True
    if needle in pat_only:
        scrut_tup = _split_rust_tuple_elems(scrut)
        pat_tup = _split_rust_tuple_elems(pat_only)
        if (
            scrut_tup is not None
            and pat_tup is not None
            and len(scrut_tup) == len(pat_tup)
        ):
            return any(
                needle in p_el
                and _rust_receiver_is_clean_observed(
                    s_el, needle, item, require_capture=require_capture
                )
                for s_el, p_el in zip(scrut_tup, pat_tup)
            )
        return _rust_receiver_is_clean_observed(
            scrut, needle, item, require_capture=require_capture
        )
    if needle in scrut:
        if (
            _rust_clause_is_static_false(pat_only)
            or _rust_expr_is_option_none(pat_only)
        ):
            return False
        scrut_ns = scan_rust_tokens(scrut).code_no_strings_or_comments
        p = scrut.find(needle)
        while p != -1:
            if _rust_needle_occurrence_is_observed(
                scrut, scrut_ns, 0, p, needle, item, require_capture=require_capture
            ):
                return True
            p = scrut.find(needle, p + len(needle))
        return False
    return False


def _rust_clause_matches_positive_needle(
    tested_expr: str,
    cs: int,
    ce: int,
    clause_text: str,
    needle: str,
    *,
    item: _AssertionItem,
    is_compound: bool,
    require_observed: bool,
    require_capture: bool,
) -> bool:
    """Return True if single conjunction clause `[cs, ce)` asserts `needle`."""
    if item.is_err_unwrap:
        if needle not in ("unwrap_err()", "expect_err(") or needle not in clause_text:
            return False
        if not require_observed:
            return True
        if item.err_unwrap_recv and not _rust_operand_is_trusted_projection(
            item.err_unwrap_recv,
            rust_env=item.rust_env,
            type_env=item.rust_type_env,
            facts=item.rust_facts,
        ):
            return False
        return item.is_observed and (
            not require_capture or item.origin_kind == "obs_capture"
        )
    if needle not in clause_text:
        return False
    if require_observed and not item.subexpr_observed(
        clause_text, require_capture=require_capture
    ):
        return False
    clause_strip = _rust_strip_outer_parens(clause_text)
    if require_observed and not _rust_operand_is_trusted_projection(
        clause_strip,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    if require_observed:
        # Handle single-clause `lhs == rhs` inside `assert!(...)`.
        eq_parts = _split_top_level_rust_op(clause_strip, "==")
        if len(eq_parts) == 2:
            if not _rust_eq_pair_binds_observed_needle(
                eq_parts[0][2],
                eq_parts[1][2],
                needle,
                item,
                require_capture=require_capture,
            ):
                return False
        # Handle `matches!(scrut, pat [if guard])` inside `assert!(...)`.
        clause_ns = scan_rust_tokens(clause_strip).code_no_strings_or_comments
        mm = re.match(
            r"^(?:(?:core|std)\s*::\s*)?matches\s*!\s*([(\[{])", clause_ns
        )
        if mm is not None:
            op_idx = mm.end() - 1
            cl_idx = _find_matching_delimiter_in_code(clause_ns, op_idx)
            if cl_idx == len(clause_ns) - 1:
                m_args = _split_top_level_commas(
                    clause_strip[op_idx + 1 : cl_idx], keep_literal_only=True
                )
                if len(m_args) >= 2:
                    return _rust_matches_pair_binds_observed_needle(
                        m_args[0],
                        ", ".join(m_args[1:]),
                        needle,
                        item,
                        require_capture=require_capture,
                    )
    tested_ns = scan_rust_tokens(tested_expr).code_no_strings_or_comments
    pos = tested_expr.find(needle, cs, ce)
    while pos != -1:
        before = tested_expr[:pos]
        atom = re.split(r"(?:&&|\|\||[;,]|=>|==|\|(?![|]))", before)[-1]
        neg_atom = re.match(r"^\s*!(?!=)", atom) is not None
        neg_eq = re.search(r"!=\s*[^=&|;,]*$", atom) is not None
        unclosed_parens: list[int] = []
        for idx, ch in enumerate(before):
            if ch == "(":
                unclosed_parens.append(idx)
            elif ch == ")" and unclosed_parens:
                unclosed_parens.pop()
        neg_enclosing = any(
            re.search(r"(?:^|[^\w])!(?!=)\s*$", before[:p_idx]) is not None
            for p_idx in unclosed_parens
        )
        after = tested_expr[pos + len(needle) :]
        neg_after = re.match(
            r"\s*[\"']?#*\s*(?:\)\s*\.\s*is_none\s*\("
            r"|==\s*false\b|!=\s*true\b)",
            after,
        )
        neg_none_after = False
        if re.search(
            r"\.\s*(?:find|rfind|strip_prefix|strip_suffix|match_indices|"
            r"position|rposition)\s*(?:::\s*<[^;()]*>)?\s*\([^()]*$",
            before,
        ):
            neg_none_after = (
                re.match(
                    r"\s*[\"']?#*\s*\)+"
                    r"(?:\s*\.\s*next\s*\(\s*\))?"
                    r"\s*(?:==|,)\s*"
                    r"(?:(?:core|std)\s*::\s*option\s*::\s*)?(?:Option\s*::\s*)?None\b",
                    after,
                )
                is not None
            )
            if not neg_none_after:
                neg_none_after = (
                    re.search(
                        r"(?:^|[;,(&|])\s*(?:(?:core|std)\s*::\s*option\s*::\s*)?"
                        r"(?:Option\s*::\s*)?None\s*(?:==|,)\s*[^;,]*$",
                        before,
                    )
                    is not None
                )
        if (
            not neg_atom
            and not neg_eq
            and not neg_enclosing
            and neg_after is None
            and not neg_none_after
            and (
                not require_observed
                or _rust_needle_occurrence_is_observed(
                    tested_expr,
                    tested_ns,
                    cs,
                    pos,
                    needle,
                    item,
                    require_capture=require_capture,
                )
            )
        ):
            return True
        pos = tested_expr.find(needle, pos + len(needle), ce)
    return False


def _split_top_level_rust_or_patterns(pat: str) -> list[str]:
    """Split a Rust pattern on depth-0 single `|` operators."""
    code_ns = scan_rust_tokens(pat).code_no_strings_or_comments
    out: list[str] = []
    p_d = b_d = br_d = 0
    start = 0
    i = 0
    n = len(code_ns)
    while i < n:
        ch = code_ns[i]
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == "|":
            if code_ns[i : i + 2] == "||":
                i += 2
                continue
            if i > start:
                out.append(pat[start:i])
            i += 1
            start = i
            continue
        i += 1
    out.append(pat[start:])
    return [p.strip() for p in out if p.strip()]


def _strip_rust_pat_wrappers(pat_ns: str) -> str:
    """Strip outer non-tuple parens, `&`/`mut`/`ref`, and `ident @`."""
    s = pat_ns.strip()
    changed = True
    while changed:
        changed = False
        while (
            s.startswith("(")
            and s.endswith(")")
            and _find_matching_delimiter_in_code(s, 0) == len(s) - 1
            and _split_rust_tuple_elems(s) is None
        ):
            s = s[1:-1].strip()
            changed = True
        m_ref = re.match(
            r"^(?:&\s*(?:mut\b)?|ref\s+|mut\s+)(.+)$", s, re.DOTALL
        )
        if m_ref is not None:
            s = m_ref.group(1).strip()
            changed = True
            continue
        m_at = re.match(
            r"^[A-Za-z_][A-Za-z0-9_]*\s*@\s*(.+)$", s, re.DOTALL
        )
        if m_at is not None:
            s = m_at.group(1).strip()
            changed = True
    return s


_RUST_OPT_PREF_RE_STR = (
    r"(?:(?:::\s*)?(?:core|std)\s*::\s*option\s*::\s*)?(?:Option\s*::\s*)?"
)
_RUST_RES_PREF_RE_STR = (
    r"(?:(?:::\s*)?(?:core|std)\s*::\s*result\s*::\s*)?(?:Result\s*::\s*)?"
)


def _rust_pat_is_exhaustive(pat_ns: str, _depth: int = 0) -> bool:
    """Return True if a Rust match pattern covers all possible values."""
    if _depth > 8:
        return False
    s = _strip_rust_pat_wrappers(pat_ns)
    if not s:
        return False
    alts = _split_top_level_rust_or_patterns(s)
    if len(alts) >= 2:
        if any(_rust_pat_is_exhaustive(alt, _depth + 1) for alt in alts):
            return True
        has_none = has_some_ex = has_ok_ex = has_err_ex = False
        has_true = has_false = False
        opt_c = _RUST_OPT_PREF_RE_STR.replace(r"\s*", "")
        for alt in alts:
            norm = _strip_rust_pat_wrappers(alt)
            compact = re.sub(r"\s+", "", norm)
            if re.fullmatch(opt_c + r"None", compact):
                has_none = True
            m_some = re.fullmatch(
                _RUST_OPT_PREF_RE_STR + r"Some\s*\((.*)\)", norm, re.DOTALL
            )
            if m_some is not None and _rust_pat_is_exhaustive(
                m_some.group(1), _depth + 1
            ):
                has_some_ex = True
            m_ok = re.fullmatch(
                _RUST_RES_PREF_RE_STR + r"Ok\s*\((.*)\)", norm, re.DOTALL
            )
            if m_ok is not None and _rust_pat_is_exhaustive(
                m_ok.group(1), _depth + 1
            ):
                has_ok_ex = True
            m_err = re.fullmatch(
                _RUST_RES_PREF_RE_STR + r"Err\s*\((.*)\)", norm, re.DOTALL
            )
            if m_err is not None and _rust_pat_is_exhaustive(
                m_err.group(1), _depth + 1
            ):
                has_err_ex = True
            if compact == "true":
                has_true = True
            elif compact == "false":
                has_false = True
        return (
            (has_none and has_some_ex)
            or (has_ok_ex and has_err_ex)
            or (has_true and has_false)
        )
    tup = _split_rust_tuple_elems(s)
    if tup is not None:
        return all(_rust_pat_is_exhaustive(el, _depth + 1) for el in tup)
    if s == "_":
        return True
    return bool(re.fullmatch(r"[a-z_][a-z0-9_]*", s)) and s not in (
        "true",
        "false",
    )


def _rust_status_code_some_irrefutable(scrut_ns: str, pat_only_ns: str) -> bool:
    """Return True if `.code()` is matched only against irrefutable `Some(...)`."""
    if not re.search(r"\.\s*code\s*\(\s*\)", scrut_ns):
        return False
    m_some = re.fullmatch(
        _RUST_OPT_PREF_RE_STR + r"Some\s*\((.*)\)",
        pat_only_ns.strip(),
        re.DOTALL,
    )
    return m_some is not None and _rust_pat_is_exhaustive(m_some.group(1))


def _rust_matches_args(expr: str) -> tuple[str, str, str] | None:
    """Split `matches!(s, pat [if g])` into `(s, pat_only_ns, guard_ns)`."""
    s = scan_rust_tokens(expr).code_no_strings_or_comments.strip()
    if s.endswith(";"):
        s = s[:-1].strip()
    while (
        s.startswith("(")
        and s.endswith(")")
        and _find_matching_delimiter_in_code(s, 0) == len(s) - 1
    ):
        s = s[1:-1].strip()
    mm = re.match(
        r"^(?:(?:::\s*)?(?:core|std)\s*::\s*)?matches\s*!\s*([(\[{])", s
    )
    if mm is None:
        return None
    op_idx = mm.end() - 1
    if _find_matching_delimiter_in_code(s, op_idx) != len(s) - 1:
        return None
    args = _split_top_level_commas(
        s[op_idx + 1 : len(s) - 1], keep_literal_only=True
    )
    tail = [a for a in args[1:] if a.strip()]
    if len(args) < 2 or not tail:
        return None
    pat_expr = ", ".join(tail)
    pat_only_ns, g_off = _strip_rust_match_guard(pat_expr)
    guard_ns = pat_expr[g_off:].strip() if g_off is not None else ""
    return args[0].strip(), pat_only_ns.strip(), guard_ns


def _rust_matches_expr_is_exhaustive(expr: str) -> bool:
    """Return True if `expr` is an unguarded exhaustive `matches!` macro."""
    parsed = _rust_matches_args(expr)
    if parsed is None:
        return False
    _scrut, pat_only_ns, guard_ns = parsed
    if guard_ns and _eval_rust_static_bool_cond(guard_ns) is not True:
        return False
    return _rust_pat_is_exhaustive(pat_only_ns)


def _rust_clause_is_static_true(clause_expr: str) -> bool:
    """Return True if a Rust logical clause is statically `true`."""
    ns = scan_rust_tokens(clause_expr).code_no_strings_or_comments.strip()
    return _eval_rust_static_bool_cond(ns) is True or (
        _rust_matches_expr_is_exhaustive(ns)
    )


def _rust_expr_has_static_true_disjunct(expr: str) -> bool:
    """Return True if `expr` has a top-level (or parenthesized) `true || _`."""
    ns = scan_rust_tokens(expr).code_no_strings_or_comments
    s = 0
    e = len(expr)
    while s < e and expr[s].isspace():
        s += 1
    while e > s and expr[e - 1].isspace():
        e -= 1
    while s < e and ns[s] == "(" and ns[e - 1] == ")":
        if _find_matching_delimiter_in_code(ns, s) != e - 1:
            break
        s += 1
        e -= 1
        while s < e and expr[s].isspace():
            s += 1
        while e > s and expr[e - 1].isspace():
            e -= 1
    parts = _split_top_level_rust_op(expr[s:e], "||")
    if len(parts) <= 1:
        return False
    return any(_rust_clause_is_static_true(p[2]) for p in parts)


def _norm_rust_expr_for_eq(expr: str) -> str:
    """Normalize a Rust expression for structural self-equality comparison."""
    s = _normalize_rust_code_ws(expr)
    while s.startswith("(") and s.endswith(")"):
        ns = scan_rust_tokens(s).code_no_strings_or_comments
        if _find_matching_delimiter_in_code(ns, 0) != len(ns) - 1:
            break
        s = _normalize_rust_code_ws(s[1:-1])
    return s


def _split_rust_tuple_elems(expr: str) -> list[str] | None:
    """If `expr` is a parenthesized tuple `(a, b, ...)`, return its elements."""
    s = expr.strip()
    if not (s.startswith("(") and s.endswith(")")):
        return None
    ns = scan_rust_tokens(s).code_no_strings_or_comments
    if _find_matching_delimiter_in_code(ns, 0) != len(ns) - 1:
        return None
    inner = s[1:-1]
    parts = _split_top_level_commas(inner, keep_literal_only=True)
    if len(parts) < 2 and "," not in inner:
        return None
    return [p.strip() for p in parts if p.strip()]


def _rust_expr_is_option_none(expr: str) -> bool:
    """Return True if `expr` strips to `None` / `Option::None`."""
    s = _rust_strip_outer_parens(expr).lstrip("&* ").strip()
    compact = re.sub(r"\s+", "", s)
    return compact in (
        "None",
        "Option::None",
        "core::option::Option::None",
        "std::option::Option::None",
    )


def _rust_expr_is_option_needle_search(expr: str) -> bool:
    """Return True if `expr` invokes an `Option`-returning search/strip helper."""
    ns = scan_rust_tokens(expr).code_no_strings_or_comments
    return (
        re.search(
            r"\.\s*(?:find|rfind|strip_prefix|strip_suffix|match_indices|"
            r"position|rposition)\s*(?:::\s*<[^;()]*>)?\s*\(",
            ns,
        )
        is not None
    )


def _rust_eq_pair_is_tautological_or_false(
    lhs: str, rhs: str, active_needles: Iterable[str] | None = None
) -> bool:
    """Return True if `lhs == rhs` is self-equality or compares a needle to `false`/`None`."""
    if _norm_rust_expr_for_eq(lhs) == _norm_rust_expr_for_eq(rhs):
        return True
    if _rust_clause_is_static_false(lhs) or _rust_clause_is_static_false(rhs):
        return True
    lhs_none = _rust_expr_is_option_none(lhs)
    rhs_none = _rust_expr_is_option_none(rhs)
    if active_needles is not None:
        nlist = list(active_needles)
        if (rhs_none and any(n in lhs for n in nlist)) or (
            lhs_none and any(n in rhs for n in nlist)
        ):
            return True
    else:
        if (rhs_none and _rust_expr_is_option_needle_search(lhs)) or (
            lhs_none and _rust_expr_is_option_needle_search(rhs)
        ):
            return True
    lhs_tup = _split_rust_tuple_elems(lhs)
    rhs_tup = _split_rust_tuple_elems(rhs)
    if (
        lhs_tup is not None
        and rhs_tup is not None
        and len(lhs_tup) == len(rhs_tup)
    ):
        if all(
            _norm_rust_expr_for_eq(a) == _norm_rust_expr_for_eq(b)
            for a, b in zip(lhs_tup, rhs_tup)
        ):
            return True
        if active_needles is None:
            if all(
                _rust_eq_pair_is_tautological_or_false(a, b)
                for a, b in zip(lhs_tup, rhs_tup)
            ):
                return True
        else:
            needle_list = list(active_needles)
            matched_pair = False
            for a, b in zip(lhs_tup, rhs_tup):
                if any(n in a or n in b for n in needle_list):
                    matched_pair = True
                    if not _rust_eq_pair_is_tautological_or_false(
                        a, b, needle_list
                    ):
                        return False
            if matched_pair:
                return True
    return False


def _rust_item_macro_and_args(
    item: _AssertionItem,
) -> tuple[str, tuple[str, ...]]:
    """Return `(macro_name, tested_args)` for a Rust `_AssertionItem`."""
    macro_head = re.match(
        r"^\s*(?:(?:core|std)\s*::\s*)?(assert(?:_eq|_ne|_matches)?)\s*!",
        item.full_span,
    )
    macro_name = macro_head.group(1) if macro_head else ""
    if item.tested_args:
        return macro_name, item.tested_args
    if macro_name in ("assert_eq", "assert_ne", "assert_matches"):
        parts = _split_top_level_commas(item.tested_expr, keep_literal_only=True)
        return macro_name, tuple(parts[:2])
    return macro_name, (item.tested_expr,)


def _rust_assert_expr_is_inverted_or_tautological(
    expr: str, active_needles: Iterable[str] | None = None
) -> bool:
    """Detect top-level `a == a`, `a == false`, `false == a`, `a != true` in `assert!`."""
    s = expr.strip()
    ns = scan_rust_tokens(s).code_no_strings_or_comments
    while s.startswith("(") and s.endswith(")"):
        if _find_matching_delimiter_in_code(ns, 0) != len(ns) - 1:
            break
        s = s[1:-1].strip()
        ns = scan_rust_tokens(s).code_no_strings_or_comments
    eq_parts = _split_top_level_rust_op(s, "==")
    if len(eq_parts) == 2:
        lhs, rhs = eq_parts[0][2], eq_parts[1][2]
        if _rust_eq_pair_is_tautological_or_false(lhs, rhs, active_needles):
            return True
    ne_parts = _split_top_level_rust_op(s, "!=")
    if len(ne_parts) == 2:
        lhs, rhs = ne_parts[0][2], ne_parts[1][2]
        if _rust_clause_is_static_true(lhs) or _rust_clause_is_static_true(rhs):
            return True
    return False


def _rust_assertion_is_inverted_or_tautological(item: _AssertionItem) -> bool:
    """Reject inverted-polarity or tautological Rust equality/disjunction checks."""
    macro_name, args = _rust_item_macro_and_args(item)
    if macro_name == "assert_ne":
        return True
    if macro_name == "assert_eq" and len(args) >= 2:
        return _rust_eq_pair_is_tautological_or_false(args[0], args[1])
    if _rust_expr_has_static_true_disjunct(item.tested_expr):
        return True
    if macro_name == "assert":
        return _rust_assert_expr_is_inverted_or_tautological(item.tested_expr)
    return False


def _rust_assertion_has_positive_needles(
    item: _AssertionItem,
    needles: Iterable[tuple[str, bool]],
    *,
    require_observed: bool = True,
    require_capture: bool = False,
) -> bool:
    """Verify `(needle, allow_ne)` holds across `&&` (any) and `||` (all)."""
    tested_expr = item.tested_expr
    if require_observed and not item.is_observed:
        return False
    if (
        require_observed
        and require_capture
        and item.origin_kind != "obs_capture"
    ):
        return False
    macro_name, macro_args = _rust_item_macro_and_args(item)
    active_needles = [
        n
        for n, allow_ne in needles
        if n in tested_expr and (macro_name != "assert_ne" or allow_ne)
    ]
    if not active_needles:
        return False
    if macro_name == "assert_matches" and len(macro_args) >= 2:
        if require_observed:
            return any(
                _rust_matches_pair_binds_observed_needle(
                    macro_args[0],
                    macro_args[1],
                    n,
                    item,
                    require_capture=require_capture,
                )
                for n in active_needles
            )
    if macro_name == "assert_eq" and len(macro_args) >= 2:
        lhs, rhs = macro_args[0], macro_args[1]
        if _rust_eq_pair_is_tautological_or_false(lhs, rhs, active_needles):
            return False
        if _rust_assert_expr_is_inverted_or_tautological(
            lhs, active_needles
        ) or _rust_assert_expr_is_inverted_or_tautological(rhs, active_needles):
            return False
        if require_observed:
            active_needles = [
                n
                for n in active_needles
                if _rust_eq_pair_binds_observed_needle(
                    lhs, rhs, n, item, require_capture=require_capture
                )
            ]
            if not active_needles:
                return False
        # `assert_eq!(out.status.code(), Some(0))` asserts success, not refusal.
        norm_l = re.sub(r"\s+", "", lhs)
        norm_r = re.sub(r"\s+", "", rhs)
        if "Some(0)" in (norm_l, norm_r):
            active_needles = [n for n in active_needles if n != "status.code()"]
            if not active_needles:
                return False
    if macro_name == "assert" and re.search(
        r"status(?:\s*\(\s*\))?\.code\s*\(\s*\)\s*==\s*Some\s*\(\s*0\s*\)"
        r"|Some\s*\(\s*0\s*\)\s*==\s*[^&|;,]*status(?:\s*\(\s*\))?\.code\s*\(\s*\)",
        tested_expr,
    ):
        active_needles = [n for n in active_needles if n != "status.code()"]
        if not active_needles:
            return False
    if re.search(
        r"\b(?:false\s*==|==\s*false|true\s*!=|!=\s*true)\b"
        r"|!\s*true\s*==|==\s*!\s*true|!\s*false\s*!=|!=\s*!\s*false",
        tested_expr,
    ):
        return False
    tested_ns = scan_rust_tokens(tested_expr).code_no_strings_or_comments

    def _eval_span(cs: int, ce: int, *, compound: bool) -> bool:
        while cs < ce and tested_expr[cs].isspace():
            cs += 1
        while ce > cs and tested_expr[ce - 1].isspace():
            ce -= 1
        while cs < ce and tested_ns[cs] == "(" and tested_ns[ce - 1] == ")":
            if _find_matching_delimiter_in_code(tested_ns, cs) != ce - 1:
                break
            cs += 1
            ce -= 1
            while cs < ce and tested_expr[cs].isspace():
                cs += 1
            while ce > cs and tested_expr[ce - 1].isspace():
                ce -= 1
        sub = tested_expr[cs:ce]
        or_parts = _split_top_level_rust_op(sub, "||")
        if len(or_parts) > 1:
            if require_observed:
                live = [
                    p
                    for p in or_parts
                    if not _rust_clause_is_static_false(p[2])
                ]
                return bool(live) and all(
                    _eval_span(cs + p[0], cs + p[1], compound=True)
                    for p in live
                )
            return any(
                _eval_span(cs + p[0], cs + p[1], compound=True)
                for p in or_parts
            )
        and_parts = _split_top_level_rust_op(sub, "&&")
        if len(and_parts) > 1:
            return any(
                _eval_span(cs + p[0], cs + p[1], compound=True)
                for p in and_parts
            )
        if _rust_assert_expr_is_inverted_or_tautological(sub, active_needles):
            return False
        return any(
            _rust_clause_matches_positive_needle(
                tested_expr,
                cs,
                ce,
                sub,
                n,
                item=item,
                is_compound=compound,
                require_observed=require_observed,
                require_capture=require_capture,
            )
            for n in active_needles
        )

    return _eval_span(0, len(tested_expr), compound=False)


def _rust_assertion_has_positive_needle(
    item: _AssertionItem,
    needle: str,
    *,
    allow_ne_when_no_needle: bool = False,
    require_observed: bool = True,
    require_capture: bool = False,
) -> bool:
    """Verify `needle` occurs positively (and optionally observed)."""
    return _rust_assertion_has_positive_needles(
        item,
        [(needle, allow_ne_when_no_needle)],
        require_observed=require_observed,
        require_capture=require_capture,
    )


def _py_eq_pair_is_tautological_or_false(
    lhs: ast.AST,
    rhs: ast.AST,
    needles: tuple[str, ...] | None = None,
    const_vals: dict[str, object] | None = None,
) -> bool:
    """Return True if Python equality `lhs == rhs` is self-equality or vs False."""
    if ast.dump(lhs) == ast.dump(rhs):
        return True
    if _eval_python_static_bool(lhs, const_vals) is False or (
        _eval_python_static_bool(rhs, const_vals) is False
    ):
        return True
    if (
        isinstance(lhs, (ast.Tuple, ast.List))
        and isinstance(rhs, (ast.Tuple, ast.List))
        and len(lhs.elts) == len(rhs.elts)
    ):
        if all(ast.dump(a) == ast.dump(b) for a, b in zip(lhs.elts, rhs.elts)):
            return True
        if needles is None:
            if all(
                _py_eq_pair_is_tautological_or_false(
                    a, b, const_vals=const_vals
                )
                for a, b in zip(lhs.elts, rhs.elts)
            ):
                return True
        else:
            matched_pair = False
            for a, b in zip(lhs.elts, rhs.elts):
                sa, sb = ast.unparse(a), ast.unparse(b)
                if any(n in sa or n in sb for n in needles):
                    matched_pair = True
                    if not _py_eq_pair_is_tautological_or_false(
                        a, b, needles, const_vals=const_vals
                    ):
                        return False
            if matched_pair:
                return True
    return False


def _py_compare_is_inverted_or_tautological(
    node: ast.Compare,
    needles: tuple[str, ...],
    const_vals: dict[str, object] | None = None,
) -> bool:
    """Return True if a Python `Compare` negates a needle or is self-equal/vs-False."""
    comp_src = ast.unparse(node)
    if any(n in comp_src for n in needles) and any(
        isinstance(op, (ast.NotIn, ast.NotEq, ast.IsNot)) for op in node.ops
    ):
        return True
    operands = [node.left, *node.comparators]
    for op, left_op, right_op in zip(node.ops, operands, operands[1:]):
        if isinstance(op, (ast.Eq, ast.Is)):
            if _py_eq_pair_is_tautological_or_false(
                left_op, right_op, needles, const_vals=const_vals
            ):
                return True
        elif isinstance(op, (ast.NotEq, ast.IsNot)):
            if _eval_python_static_bool(left_op, const_vals) is True or (
                _eval_python_static_bool(right_op, const_vals) is True
            ):
                return True
    return False


def _py_expr_is_bool_predicate(node: ast.AST) -> bool:
    """Return True if a Python AST expression is a boolean predicate/comparison."""
    if isinstance(node, (ast.Compare, ast.BoolOp)):
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return True
    if isinstance(node, ast.Call):
        cname = _dotted_python_name(node.func) or ""
        tail = (
            node.func.attr
            if isinstance(node.func, ast.Attribute)
            else cname
        )
        if tail in (
            "any",
            "all",
            "bool",
            "startswith",
            "endswith",
            "issubset",
            "issuperset",
            "search",
            "match",
            "fullmatch",
        ):
            return True
    return False


def _py_expr_unobserved_str_parts(
    node: ast.AST,
    *,
    env: dict[str, str],
    self_attrs: dict[str, str],
    pure_fns: frozenset[str],
    py_facts: _PyFileFacts | None,
    const_vals: dict[str, object],
    type_env: dict[str, str],
    injected_strs: dict[str, str] | None,
) -> str:
    """Extract constant/injected unobserved string parts inside a Python expr."""
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.Name):
        inj = (injected_strs or {}).get(node.id, "")
        if _py_expr_ast_is_observed(
            node,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
        ):
            return inj
        if node.id in const_vals and isinstance(const_vals[node.id], str):
            return inj or str(const_vals[node.id])
        return inj
    if isinstance(node, ast.Attribute):
        if isinstance(node.value, ast.Name) and node.value.id == "self":
            return (injected_strs or {}).get(f"self.{node.attr}", "")
        return _py_expr_unobserved_str_parts(
            node.value,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
    if isinstance(node, ast.JoinedStr):
        return "".join(
            _py_expr_unobserved_str_parts(
                v,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
                injected_strs=injected_strs,
            )
            for v in node.values
        )
    if isinstance(node, ast.FormattedValue):
        return _py_expr_unobserved_str_parts(
            node.value,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Mod)):
        left_s = _py_expr_unobserved_str_parts(
            node.left,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
        right_s = _py_expr_unobserved_str_parts(
            node.right,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
        return f"{left_s}{right_s}"
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return "".join(
            _py_expr_unobserved_str_parts(
                el,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
                injected_strs=injected_strs,
            )
            for el in node.elts
        )
    if isinstance(node, ast.Subscript):
        return _py_expr_unobserved_str_parts(
            node.value,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
    if isinstance(node, ast.IfExp):
        cond = _eval_python_static_bool(node.test, const_vals)
        if cond is True:
            return _py_expr_unobserved_str_parts(
                node.body,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
                injected_strs=injected_strs,
            )
        if cond is False:
            return _py_expr_unobserved_str_parts(
                node.orelse,
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
                injected_strs=injected_strs,
            )
        return _py_expr_unobserved_str_parts(
            node.body,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        ) + _py_expr_unobserved_str_parts(
            node.orelse,
            env=env,
            self_attrs=self_attrs,
            pure_fns=pure_fns,
            py_facts=py_facts,
            const_vals=const_vals,
            type_env=type_env,
            injected_strs=injected_strs,
        )
    if isinstance(node, ast.Call):
        if isinstance(node.func, ast.Attribute):
            attr = node.func.attr
            if attr in ("format", "format_map", "join"):
                parts = [
                    _py_expr_unobserved_str_parts(
                        node.func.value,
                        env=env,
                        self_attrs=self_attrs,
                        pure_fns=pure_fns,
                        py_facts=py_facts,
                        const_vals=const_vals,
                        type_env=type_env,
                        injected_strs=injected_strs,
                    )
                ]
                for a in node.args:
                    arg_node = a.value if isinstance(a, ast.Starred) else a
                    parts.append(
                        _py_expr_unobserved_str_parts(
                            arg_node,
                            env=env,
                            self_attrs=self_attrs,
                            pure_fns=pure_fns,
                            py_facts=py_facts,
                            const_vals=const_vals,
                            type_env=type_env,
                            injected_strs=injected_strs,
                        )
                    )
                for kw in node.keywords:
                    parts.append(
                        _py_expr_unobserved_str_parts(
                            kw.value,
                            env=env,
                            self_attrs=self_attrs,
                            pure_fns=pure_fns,
                            py_facts=py_facts,
                            const_vals=const_vals,
                            type_env=type_env,
                            injected_strs=injected_strs,
                        )
                    )
                return "".join(parts)
            if attr == "replace":
                out_p = _py_expr_unobserved_str_parts(
                    node.func.value,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=py_facts,
                    const_vals=const_vals,
                    type_env=type_env,
                    injected_strs=injected_strs,
                )
                if len(node.args) >= 2:
                    out_p += _py_expr_unobserved_str_parts(
                        node.args[1],
                        env=env,
                        self_attrs=self_attrs,
                        pure_fns=pure_fns,
                        py_facts=py_facts,
                        const_vals=const_vals,
                        type_env=type_env,
                        injected_strs=injected_strs,
                    )
                for kw in node.keywords:
                    if kw.arg == "new":
                        out_p += _py_expr_unobserved_str_parts(
                            kw.value,
                            env=env,
                            self_attrs=self_attrs,
                            pure_fns=pure_fns,
                            py_facts=py_facts,
                            const_vals=const_vals,
                            type_env=type_env,
                            injected_strs=injected_strs,
                        )
                return out_p
            if attr in (
                "strip",
                "lstrip",
                "rstrip",
                "lower",
                "upper",
                "casefold",
                "title",
                "capitalize",
                "swapcase",
                "splitlines",
                "split",
                "rsplit",
                "partition",
                "rpartition",
                "removeprefix",
                "removesuffix",
                "decode",
                "encode",
                "zfill",
                "center",
                "ljust",
                "rjust",
            ):
                return _py_expr_unobserved_str_parts(
                    node.func.value,
                    env=env,
                    self_attrs=self_attrs,
                    pure_fns=pure_fns,
                    py_facts=py_facts,
                    const_vals=const_vals,
                    type_env=type_env,
                    injected_strs=injected_strs,
                )
        elif (_dotted_python_name(node.func) or "") in (
            "str",
            "repr",
            "ascii",
            "bytes",
            "bytearray",
        ) and node.args:
            return _py_expr_unobserved_str_parts(
                node.args[0],
                env=env,
                self_attrs=self_attrs,
                pure_fns=pure_fns,
                py_facts=py_facts,
                const_vals=const_vals,
                type_env=type_env,
                injected_strs=injected_strs,
            )
    return ""


def _py_collect_unobserved_str_parts(
    node: ast.AST, item: _AssertionItem
) -> str:
    """Collect constant/unobserved/injected string parts inside a Python expr."""
    return _py_expr_unobserved_str_parts(
        node,
        env=item.py_env or {},
        self_attrs=item.py_self_attrs or {},
        pure_fns=item.pure_py_fns,
        py_facts=item.py_facts,
        const_vals=item.py_const_vals or {},
        type_env=item.py_type_env or {},
        injected_strs=item.py_injected_strs,
    )


def _py_expr_uses_custom_cmp(node: ast.AST, item: _AssertionItem) -> bool:
    """Return True if `node` instantiates or references a custom-cmp local class."""
    facts = item.py_facts
    if facts is None or not facts.custom_cmp_classes:
        return False
    tenv = item.py_type_env or {}
    for sub in ast.walk(node):
        if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name):
            if sub.func.id in facts.custom_cmp_classes:
                return True
        if isinstance(sub, ast.Name) and tenv.get(sub.id) in facts.custom_cmp_classes:
            return True
    return False


def _py_expr_clean_observed_target(
    node: ast.AST,
    needles: tuple[str, ...],
    item: _AssertionItem,
) -> bool:
    """Verify Python haystack/target is genuinely observed without const needle injection."""
    if _py_expr_uses_custom_cmp(node, item):
        return False
    if not item.subexpr_observed(ast.unparse(node)):
        return False
    if isinstance(node, (ast.Tuple, ast.List, ast.Set)):
        return bool(node.elts) and all(
            _py_expr_clean_observed_target(el, needles, item)
            for el in node.elts
        )
    if isinstance(node, ast.Dict):
        return bool(node.keys) and all(
            k is not None and _py_expr_clean_observed_target(k, needles, item)
            for k in node.keys
        )
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or):
        live = [
            v
            for v in node.values
            if _eval_python_static_bool(v, item.py_const_vals) is not False
        ]
        return bool(live) and all(
            _py_expr_clean_observed_target(v, needles, item) for v in live
        )
    if isinstance(node, ast.IfExp):
        cond = _eval_python_static_bool(node.test, item.py_const_vals)
        if cond is True:
            return _py_expr_clean_observed_target(node.body, needles, item)
        if cond is False:
            return _py_expr_clean_observed_target(node.orelse, needles, item)
        return _py_expr_clean_observed_target(
            node.body, needles, item
        ) and _py_expr_clean_observed_target(node.orelse, needles, item)
    if needles:
        unobs = _py_collect_unobserved_str_parts(node, item)
        if unobs and any(n in unobs for n in needles):
            return False
    return True


def _py_in_pair_binds_observed_needle(
    member: ast.AST,
    container: ast.AST,
    needles: tuple[str, ...],
    item: _AssertionItem,
) -> bool:
    """Verify `member in container` / `assertIn(member, container)` binds observed value."""
    mem_src = ast.unparse(member)
    cont_src = ast.unparse(container)
    mem_obs = item.subexpr_observed(mem_src)
    cont_obs = item.subexpr_observed(cont_src)
    if not (mem_obs or cont_obs):
        return False
    in_mem = any(n in mem_src for n in needles)
    in_cont = any(n in cont_src for n in needles)
    if in_mem:
        return _py_expr_clean_observed_target(container, needles, item)
    if in_cont:
        if not mem_obs or _py_expr_is_bool_predicate(member):
            return False
        if isinstance(container, (ast.Tuple, ast.List, ast.Set)):
            if not container.elts:
                return False
            return all(
                any(n in ast.unparse(el) for n in needles)
                for el in container.elts
            )
        return _py_expr_clean_observed_target(container, needles, item)
    if not (in_mem or in_cont) and needles:
        return False
    # Method-name refusal token (`assertIn`) where needle isn't literal in args:
    # if `member` is not observed, `container` must be a clean observed target
    # (blocking `(err, "constant")` tuple spoofs).
    if not mem_obs:
        return _py_expr_clean_observed_target(container, (), item)
    return not _py_expr_is_bool_predicate(member)


def _py_eq_pair_binds_observed_needle(
    lhs: ast.AST,
    rhs: ast.AST,
    needles: tuple[str, ...],
    item: _AssertionItem,
) -> bool:
    """Verify `lhs == rhs` / `assertEqual(lhs, rhs)` binds observed execution to needle."""
    lhs_src = ast.unparse(lhs)
    rhs_src = ast.unparse(rhs)
    in_l = any(n in lhs_src for n in needles)
    in_r = any(n in rhs_src for n in needles)
    if not (in_l or in_r):
        return False
    if (
        isinstance(lhs, (ast.Tuple, ast.List))
        and isinstance(rhs, (ast.Tuple, ast.List))
        and len(lhs.elts) == len(rhs.elts)
    ):
        return any(
            _py_eq_pair_binds_observed_needle(a, b, needles, item)
            for a, b in zip(lhs.elts, rhs.elts)
        )
    if _py_expr_uses_custom_cmp(lhs, item) or _py_expr_uses_custom_cmp(rhs, item):
        return False
    lhs_obs = item.subexpr_observed(lhs_src)
    rhs_obs = item.subexpr_observed(rhs_src)
    if not (lhs_obs or rhs_obs):
        return False
    if in_l and not lhs_obs:
        if not rhs_obs or _py_expr_is_bool_predicate(lhs) or _py_expr_is_bool_predicate(rhs):
            return False
    if in_r and not rhs_obs:
        if not lhs_obs or _py_expr_is_bool_predicate(rhs) or _py_expr_is_bool_predicate(lhs):
            return False
    if in_l and lhs_obs:
        if in_r and not rhs_obs and not _py_expr_clean_observed_target(lhs, needles, item):
            return False
        if not _py_expr_contains_positive_observed_needles(
            lhs, needles, item, require_observed=True
        ):
            if not in_r:
                return False
    if in_r and rhs_obs:
        if in_l and not lhs_obs and not _py_expr_clean_observed_target(rhs, needles, item):
            return False
        if not _py_expr_contains_positive_observed_needles(
            rhs, needles, item, require_observed=True
        ):
            if not in_l:
                return False
    return True


def _py_expr_contains_positive_observed_needles(
    node: ast.AST,
    needles: tuple[str, ...],
    item: _AssertionItem,
    *,
    require_observed: bool = True,
) -> bool:
    """Verify `BoolOp` leaves (`And` -> any, `Or` -> all when observed)."""
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        return any(
            _py_expr_contains_positive_observed_needles(
                v, needles, item, require_observed=require_observed
            )
            for v in node.values
        )
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or):
        if not require_observed:
            return any(
                _py_expr_contains_positive_observed_needles(
                    v, needles, item, require_observed=False
                )
                for v in node.values
            )
        live_vals = [
            v for v in node.values if _eval_python_static_bool(v) is not False
        ]
        if not live_vals:
            return False
        return all(
            _py_expr_contains_positive_observed_needles(
                v, needles, item, require_observed=True
            )
            for v in live_vals
        )
    if isinstance(node, ast.IfExp) and require_observed:
        cond = _eval_python_static_bool(node.test)
        if cond is True:
            return _py_expr_contains_positive_observed_needles(
                node.body, needles, item, require_observed=True
            )
        if cond is False:
            return _py_expr_contains_positive_observed_needles(
                node.orelse, needles, item, require_observed=True
            )
        return _py_expr_contains_positive_observed_needles(
            node.body, needles, item, require_observed=True
        ) and _py_expr_contains_positive_observed_needles(
            node.orelse, needles, item, require_observed=True
        )
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return False
    if isinstance(node, ast.Compare):
        if _py_compare_is_inverted_or_tautological(
            node, needles, const_vals=item.py_const_vals
        ):
            return False
        if require_observed:
            operands = [node.left, *node.comparators]
            for op, left_op, right_op in zip(
                node.ops, operands, operands[1:]
            ):
                if isinstance(op, ast.In):
                    if _py_in_pair_binds_observed_needle(
                        left_op, right_op, needles, item
                    ):
                        return True
                elif isinstance(op, (ast.Eq, ast.Is)):
                    if _py_eq_pair_binds_observed_needle(
                        left_op, right_op, needles, item
                    ):
                        return True
                elif not isinstance(op, (ast.NotIn, ast.NotEq, ast.IsNot)):
                    pair_src = f"{ast.unparse(left_op)} {ast.unparse(right_op)}"
                    if any(n in pair_src for n in needles) and (
                        item.subexpr_observed(ast.unparse(left_op))
                        or item.subexpr_observed(ast.unparse(right_op))
                    ):
                        return True
            return False
    if require_observed and isinstance(node, ast.Call):
        if isinstance(node.func, ast.Attribute) and node.func.attr in (
            "startswith",
            "endswith",
            "find",
            "rfind",
            "index",
            "count",
        ):
            src = ast.unparse(node)
            return any(n in src for n in needles) and _py_expr_clean_observed_target(
                node.func.value, needles, item
            )
        cname = _dotted_python_name(node.func) or ""
        if cname in ("re.search", "re.match", "re.fullmatch", "re.findall") and len(
            node.args
        ) >= 2:
            src = ast.unparse(node)
            return any(n in src for n in needles) and _py_expr_clean_observed_target(
                node.args[1], needles, item
            )
        if cname in ("any", "all") and len(node.args) == 1 and isinstance(
            node.args[0], (ast.GeneratorExp, ast.ListComp)
        ):
            comp = node.args[0]
            if any(
                not _py_expr_clean_observed_target(g.iter, needles, item)
                for g in comp.generators
            ):
                return False
    src = ast.unparse(node)
    return any(n in src for n in needles) and (
        not require_observed or item.subexpr_observed(src)
    )


def _py_expr_contains_positive_observed_needle(
    node: ast.AST,
    needle: str,
    item: _AssertionItem,
    *,
    require_observed: bool = True,
) -> bool:
    """Check single `needle` across Python `BoolOp` (`And` / `Or`) leaves."""
    return _py_expr_contains_positive_observed_needles(
        node, (needle,), item, require_observed=require_observed
    )


def _py_expr_all_or_branches_observed(
    node: ast.AST, item: _AssertionItem
) -> bool:
    """Reject `Or` expressions with static-true or unobserved live branches."""
    if _eval_python_static_bool(node) is True:
        return False
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.Or):
        live = [
            v for v in node.values if _eval_python_static_bool(v) is not False
        ]
        return bool(live) and all(
            _py_expr_all_or_branches_observed(v, item)
            and item.subexpr_observed(ast.unparse(v))
            for v in live
        )
    if isinstance(node, ast.BoolOp) and isinstance(node.op, ast.And):
        return any(
            _py_expr_all_or_branches_observed(v, item)
            and item.subexpr_observed(ast.unparse(v))
            for v in node.values
        )
    return True


_UNITTEST_ASSERT_PARAMS: dict[str, tuple[str, ...]] = {
    "assertTrue": ("expr",),
    "assertFalse": ("expr",),
    "assertIsNone": ("obj",),
    "assertIsNotNone": ("obj",),
    "assertEqual": ("first", "second"),
    "assertNotEqual": ("first", "second"),
    "assertIs": ("expr1", "expr2"),
    "assertIsNot": ("expr1", "expr2"),
    "assertSequenceEqual": ("seq1", "seq2"),
    "assertTupleEqual": ("tuple1", "tuple2"),
    "assertListEqual": ("list1", "list2"),
    "assertDictEqual": ("d1", "d2"),
    "assertSetEqual": ("set1", "set2"),
    "assertCountEqual": ("first", "second"),
    "assertMultiLineEqual": ("first", "second"),
    "assertAlmostEqual": ("first", "second"),
    "assertNotAlmostEqual": ("first", "second"),
    "assertGreater": ("a", "b"),
    "assertGreaterEqual": ("a", "b"),
    "assertLess": ("a", "b"),
    "assertLessEqual": ("a", "b"),
    "assertIn": ("member", "container"),
    "assertNotIn": ("member", "container"),
    "assertRegex": ("text", "expected_regex"),
    "assertNotRegex": ("text", "unexpected_regex"),
}

_UNITTEST_EXTRA_KWARGS: dict[str, frozenset[str]] = {
    "assertSequenceEqual": frozenset({"msg", "seq_type"}),
    "assertAlmostEqual": frozenset({"msg", "places", "delta"}),
    "assertNotAlmostEqual": frozenset({"msg", "places", "delta"}),
}


def _bind_unittest_call_args(call: ast.Call) -> list[ast.AST] | None:
    """Resolve positional/keyword `TestCase.assert*` value arguments in order."""
    if not isinstance(call.func, ast.Attribute):
        return None
    if any(isinstance(a, ast.Starred) for a in call.args) or any(
        kw.arg is None for kw in call.keywords
    ):
        return None
    attr = call.func.attr
    params = _UNITTEST_ASSERT_PARAMS.get(attr)
    if params is None:
        return [
            *call.args,
            *(kw.value for kw in call.keywords if kw.arg != "msg"),
        ]
    max_pos = (
        len(params) + 2
        if attr in ("assertAlmostEqual", "assertNotAlmostEqual")
        else len(params) + 1
    )
    if len(call.args) > max_pos:
        return None
    has_pos_msg = (
        len(call.args) == len(params) + 2
        if attr in ("assertAlmostEqual", "assertNotAlmostEqual")
        else len(call.args) == len(params) + 1
    )
    if has_pos_msg and any(kw.arg == "msg" for kw in call.keywords):
        return None
    if (
        attr in ("assertAlmostEqual", "assertNotAlmostEqual")
        and len(call.args) >= len(params) + 1
        and any(kw.arg == "places" for kw in call.keywords)
    ):
        return None
    bound: list[ast.AST | None] = [None] * len(params)
    for idx, arg in enumerate(call.args[: len(params)]):
        bound[idx] = arg
    allowed_extra = _UNITTEST_EXTRA_KWARGS.get(attr, frozenset({"msg"}))
    for kw in call.keywords:
        if kw.arg in allowed_extra:
            continue
        if kw.arg not in params:
            return None
        idx = params.index(kw.arg)
        if bound[idx] is not None:
            return None
        bound[idx] = kw.value
    if any(v is None for v in bound):
        return None
    return [v for v in bound if v is not None]


def _py_assertion_has_positive_needle(
    item: _AssertionItem,
    needle: str,
    *,
    search_full: bool = False,
    require_observed: bool = True,
) -> bool:
    """Verify Python assertion matches `needle` positively."""
    full_span = item.full_span
    tested_expr = item.tested_expr
    haystack = full_span if search_full else tested_expr
    if needle not in haystack or (require_observed and not item.is_observed):
        return False
    stripped = full_span.strip()
    try:
        tree = ast.parse(stripped, mode="exec")
    except SyntaxError:
        return False
    for node in ast.walk(tree):
        if isinstance(node, ast.Compare):
            if _py_compare_is_inverted_or_tautological(
                node, (needle,), const_vals=item.py_const_vals
            ):
                return False
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            if needle in ast.unparse(node.operand):
                return False
    # Reject negated/inverted methods, self-equality, and mixed branches.
    if len(tree.body) == 1:
        stmt = tree.body[0]
        if isinstance(stmt, ast.Assert):
            if needle in ast.unparse(stmt.test):
                if not _py_expr_contains_positive_observed_needle(
                    stmt.test, needle, item, require_observed=require_observed
                ):
                    return False
            elif require_observed and not _py_expr_all_or_branches_observed(
                stmt.test, item
            ):
                return False
        elif (
            isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Attribute)
        ):
            attr = stmt.value.func.attr
            if attr in (
                "assertNotIn",
                "assertFalse",
                "assertNotRegex",
                "assertIsNone",
            ):
                return False
            if attr in ("assertNotEqual", "assertIsNot") and (
                "unsupported" in tested_expr.lower()
                or "[PHASE0_TRIPWIRE:" in tested_expr
                or "FaultKind::Unsupported" in tested_expr
                or (needle != "assertNotEqual" and needle in tested_expr)
            ):
                return False
            cmp_args = _bind_unittest_call_args(stmt.value)
            if cmp_args is None:
                return False
            if attr in (
                "assertEqual",
                "assertIs",
                "assertSequenceEqual",
                "assertTupleEqual",
                "assertListEqual",
                "assertDictEqual",
                "assertSetEqual",
                "assertCountEqual",
                "assertMultiLineEqual",
            ):
                if len(cmp_args) < 2:
                    return False
                if _py_eq_pair_is_tautological_or_false(
                    cmp_args[0],
                    cmp_args[1],
                    (needle,),
                    const_vals=item.py_const_vals,
                ):
                    return False
                if require_observed and (
                    needle in ast.unparse(cmp_args[0])
                    or needle in ast.unparse(cmp_args[1])
                ):
                    if not _py_eq_pair_binds_observed_needle(
                        cmp_args[0], cmp_args[1], (needle,), item
                    ):
                        return False
            if attr == "assertIn":
                if len(cmp_args) < 2:
                    return False
                if require_observed:
                    if needle == "assertIn":
                        ok_mc, mc_val = _extract_py_static_const(
                            cmp_args[0], item.py_const_vals
                        )
                        in_needles = (
                            (mc_val,)
                            if ok_mc and isinstance(mc_val, str) and mc_val
                            else ()
                        )
                    else:
                        in_needles = (needle,)
                    if not _py_in_pair_binds_observed_needle(
                        cmp_args[0], cmp_args[1], in_needles, item
                    ):
                        return False
            if attr == "assertRegex":
                if len(cmp_args) < 2:
                    return False
                if require_observed:
                    rx_needles: tuple[str, ...] = (
                        () if needle == "assertRegex" else (needle,)
                    )
                    if not rx_needles:
                        ok_rc, rc_val = _extract_py_static_const(
                            cmp_args[1], item.py_const_vals
                        )
                        if ok_rc and isinstance(rc_val, str) and rc_val:
                            rx_needles = (rc_val,)
                    if not _py_expr_clean_observed_target(
                        cmp_args[0], rx_needles, item
                    ):
                        return False
            if attr == "assertTrue":
                if not cmp_args:
                    return False
                arg0 = cmp_args[0]
                if needle in ast.unparse(arg0):
                    if not _py_expr_contains_positive_observed_needle(
                        arg0,
                        needle,
                        item,
                        require_observed=require_observed,
                    ):
                        return False
                elif require_observed and not _py_expr_all_or_branches_observed(
                    arg0, item
                ):
                    return False
            elif require_observed:
                for t_arg in cmp_args:
                    if isinstance(t_arg, ast.BoolOp) and isinstance(
                        t_arg.op, ast.Or
                    ):
                        if not _py_expr_all_or_branches_observed(t_arg, item):
                            return False
    return True


def _py_atomic_expr_refuses_exit(
    node: ast.AST,
    item: _AssertionItem,
    *,
    negated: bool,
) -> bool:
    """Return True iff atomic Python AST node asserts observed non-zero exit/failure."""
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        left, right = node.left, node.comparators[0]
        l_rc = _py_ast_mentions_returncode(left)
        r_rc = _py_ast_mentions_returncode(right)
        if l_rc != r_rc:
            rc_node = left if l_rc else right
            other_node = right if l_rc else left
            if _py_expr_uses_custom_cmp(
                rc_node, item
            ) or not _py_expr_clean_observed_target(rc_node, (), item):
                return False
            ok_v, raw_v = _extract_py_static_const(
                other_node, item.py_const_vals or {}
            )
            if ok_v and type(raw_v) is int:
                val: int | None = raw_v
            else:
                val = _py_const_int(other_node)
            if val is None:
                return False
            if not negated:
                if isinstance(op, ast.NotEq) and val == 0:
                    return True
                if isinstance(op, ast.Eq) and val != 0:
                    return True
                if isinstance(op, ast.Gt) and l_rc and val >= 0:
                    return True
                if isinstance(op, ast.GtE) and l_rc and val >= 1:
                    return True
                if isinstance(op, ast.Lt) and r_rc and val >= 0:
                    return True
                if isinstance(op, ast.LtE) and r_rc and val >= 1:
                    return True
            else:
                if isinstance(op, ast.Eq) and val == 0:
                    return True
                if isinstance(op, ast.LtE) and l_rc and val == 0:
                    return True
                if isinstance(op, ast.GtE) and r_rc and val == 0:
                    return True
    if negated:
        recv: ast.AST | None = None
        if (
            isinstance(node, ast.Call)
            and not node.args
            and not node.keywords
            and isinstance(node.func, ast.Attribute)
            and node.func.attr in ("success", "is_ok")
        ):
            recv = node.func.value
        elif isinstance(node, ast.Attribute) and node.attr in ("success", "is_ok"):
            recv = node.value
        if recv is not None and _py_expr_clean_observed_target(recv, (), item):
            return True
    return False


def _py_bool_expr_refuses(
    node: ast.AST,
    item: _AssertionItem,
    *,
    negated: bool = False,
) -> bool:
    """Verify Python boolean expression proves positive refusal across `and`/`or`."""
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return _py_bool_expr_refuses(node.operand, item, negated=not negated)
    if isinstance(node, ast.BoolOp):
        static_val = _eval_python_static_bool(node, item.py_const_vals)
        is_conj = (isinstance(node.op, ast.And) and not negated) or (
            isinstance(node.op, ast.Or) and negated
        )
        if is_conj:
            return any(
                _py_bool_expr_refuses(v, item, negated=negated)
                for v in node.values
            )
        taut_val = False if negated else True
        if static_val is taut_val:
            return False
        dead_val = True if negated else False
        live = [
            v
            for v in node.values
            if _eval_python_static_bool(v, item.py_const_vals) is not dead_val
        ]
        return bool(live) and all(
            _py_bool_expr_refuses(v, item, negated=negated) for v in live
        )
    if isinstance(node, ast.IfExp):
        cond = _eval_python_static_bool(node.test, item.py_const_vals)
        if cond is True:
            return _py_bool_expr_refuses(node.body, item, negated=negated)
        if cond is False:
            return _py_bool_expr_refuses(node.orelse, item, negated=negated)
        return _py_bool_expr_refuses(
            node.body, item, negated=negated
        ) and _py_bool_expr_refuses(node.orelse, item, negated=negated)
    if (
        not negated
        and _py_expr_contains_positive_observed_needles(
            node, REFUSAL_TOKENS, item, require_observed=True
        )
    ):
        return True
    return _py_atomic_expr_refuses_exit(node, item, negated=negated)


def _py_item_has_observed_refusal(item: _AssertionItem) -> bool:
    """Return True iff a Python assertion checks observed refusal or non-zero exit."""
    if not item.is_observed:
        return False
    try:
        t_ast = ast.parse(item.full_span.strip(), mode="exec")
    except SyntaxError:
        return False
    if len(t_ast.body) != 1:
        return False
    st0 = t_ast.body[0]
    if isinstance(st0, ast.Assert):
        return _py_bool_expr_refuses(st0.test, item, negated=False)
    if not (
        isinstance(st0, ast.Expr)
        and isinstance(st0.value, ast.Call)
        and isinstance(st0.value.func, ast.Attribute)
    ):
        return False
    attr = st0.value.func.attr
    b_args = _bind_unittest_call_args(st0.value)
    if b_args is None:
        return False
    if attr == "assertTrue" and len(b_args) == 1:
        return _py_bool_expr_refuses(b_args[0], item, negated=False)
    if attr == "assertFalse" and len(b_args) == 1:
        return _py_bool_expr_refuses(b_args[0], item, negated=True)
    if attr == "assertNotEqual" and len(b_args) >= 2:
        for rc_node, other_node in (
            (b_args[0], b_args[1]),
            (b_args[1], b_args[0]),
        ):
            if _py_ast_mentions_returncode(rc_node) and not _py_ast_mentions_returncode(
                other_node
            ):
                if (
                    not _py_expr_uses_custom_cmp(rc_node, item)
                    and _py_expr_clean_observed_target(rc_node, (), item)
                ):
                    ok_v, raw_v = _extract_py_static_const(
                        other_node, item.py_const_vals or {}
                    )
                    val = (
                        raw_v
                        if (ok_v and type(raw_v) is int)
                        else _py_const_int(other_node)
                    )
                    if val == 0:
                        return True
        return False
    if attr == "assertEqual" and len(b_args) >= 2:
        for rc_node, other_node in (
            (b_args[0], b_args[1]),
            (b_args[1], b_args[0]),
        ):
            if _py_ast_mentions_returncode(rc_node) and not _py_ast_mentions_returncode(
                other_node
            ):
                if (
                    not _py_expr_uses_custom_cmp(rc_node, item)
                    and _py_expr_clean_observed_target(rc_node, (), item)
                ):
                    ok_v, raw_v = _extract_py_static_const(
                        other_node, item.py_const_vals or {}
                    )
                    val = (
                        raw_v
                        if (ok_v and type(raw_v) is int)
                        else _py_const_int(other_node)
                    )
                    if val is not None and val != 0:
                        return True
    if attr == "assertGreater" and len(b_args) >= 2:
        if (
            _py_ast_mentions_returncode(b_args[0])
            and not _py_ast_mentions_returncode(b_args[1])
            and not _py_expr_uses_custom_cmp(b_args[0], item)
            and _py_expr_clean_observed_target(b_args[0], (), item)
        ):
            ok_v, raw_v = _extract_py_static_const(
                b_args[1], item.py_const_vals or {}
            )
            val = raw_v if (ok_v and type(raw_v) is int) else _py_const_int(b_args[1])
            if val is not None and val >= 0:
                return True
    if attr == "assertLess" and len(b_args) >= 2:
        if (
            _py_ast_mentions_returncode(b_args[1])
            and not _py_ast_mentions_returncode(b_args[0])
            and not _py_expr_uses_custom_cmp(b_args[1], item)
            and _py_expr_clean_observed_target(b_args[1], (), item)
        ):
            ok_v, raw_v = _extract_py_static_const(
                b_args[0], item.py_const_vals or {}
            )
            val = raw_v if (ok_v and type(raw_v) is int) else _py_const_int(b_args[0])
            if val is not None and val >= 0:
                return True
    return any(
        _py_assertion_has_positive_needle(item, tok, search_full=False)
        for tok in REFUSAL_TOKENS
    )


def _rust_is_observed_status_code(
    expr: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Return True if `expr` is an observed `...status.code()` projection."""
    s = _rust_strip_outer_parens(expr)
    while s.startswith("&"):
        s = s[1:].lstrip()
        if s.startswith("mut") and (len(s) == 3 or not (s[3].isalnum() or s[3] == "_")):
            s = s[3:].lstrip()
        s = _rust_strip_outer_parens(s)
    if not s:
        return False
    ns = scan_rust_tokens(s).code_no_strings_or_comments.strip()
    if re.search(r"\.\s*code\s*\(\s*\)\s*$", ns) is None:
        return False
    if _rust_expr_is_bool_predicate(s):
        return False
    if not _rust_operand_is_trusted_projection(
        s,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    return item.subexpr_observed(s, require_capture=require_capture)


def _rust_is_observed_success_or_ok(
    expr: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Return True if `expr` is an observed `...success()` or `...is_ok()` call."""
    s = _rust_strip_outer_parens(expr)
    while s.startswith("&"):
        s = s[1:].lstrip()
        if s.startswith("mut") and (len(s) == 3 or not (s[3].isalnum() or s[3] == "_")):
            s = s[3:].lstrip()
        s = _rust_strip_outer_parens(s)
    if not s:
        return False
    ns = scan_rust_tokens(s).code_no_strings_or_comments.strip()
    if re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)\s*$", ns) is None:
        return False
    if not _rust_operand_is_trusted_projection(
        s,
        rust_env=item.rust_env,
        type_env=item.rust_type_env,
        facts=item.rust_facts,
    ):
        return False
    return item.subexpr_observed(s, require_capture=require_capture)


def _rust_parse_some_int_pattern(expr: str) -> int | None:
    """Parse `Some(<int>)` literal, returning the integer value or None."""
    norm = re.sub(r"\s+", "", _rust_strip_outer_parens(expr))
    while norm.startswith("&"):
        norm = norm[1:]
    m = re.fullmatch(
        r"(?:(?:::)?(?:core|std)::option::Option::)?Some\("
        r"(-?[0-9]+(?:_[0-9]+)*)(?:[iu](?:8|16|32|64|128|size))?"
        r"\)",
        norm,
    )
    if m is None:
        return None
    return int(m.group(1).replace("_", ""))


def _rust_split_pipe_alternatives(pat_only: str) -> list[str]:
    """Split a Rust match pattern on depth-0 single `|` alternatives."""
    ns = scan_rust_tokens(pat_only).code_no_strings_or_comments
    parts: list[str] = []
    p_d = b_d = br_d = 0
    start = 0
    for i, ch in enumerate(ns):
        if ch == "(":
            p_d += 1
        elif ch == ")" and p_d > 0:
            p_d -= 1
        elif ch == "[":
            b_d += 1
        elif ch == "]" and b_d > 0:
            b_d -= 1
        elif ch == "{":
            br_d += 1
        elif ch == "}" and br_d > 0:
            br_d -= 1
        elif p_d == 0 and b_d == 0 and br_d == 0 and ch == "|":
            parts.append(pat_only[start:i].strip())
            start = i + 1
    parts.append(pat_only[start:].strip())
    return [p for p in parts if p]


def _rust_pat_is_nonzero_some(pat: str) -> bool:
    """Return True if a `matches!` pattern strictly excludes `None` and `Some(0)`."""
    pat_ns = scan_rust_tokens(pat).code_no_strings_or_comments
    pat_only_ns, g_off = _strip_rust_match_guard(pat_ns)
    pat_only = pat[:g_off].strip() if g_off is not None else pat.strip()
    if pat_only.endswith("if"):
        pat_only = pat_only[:-2].strip()
    guard = pat[g_off:].strip() if g_off is not None else ""
    if g_off is not None:
        pat_only_re = re.sub(r"\bif\s*$", "", pat[:g_off].strip()).strip()
        if pat_only_re:
            pat_only = pat_only_re
    arms = _rust_split_pipe_alternatives(pat_only)
    if not arms:
        return False
    if not guard:
        for arm in arms:
            val = _rust_parse_some_int_pattern(arm)
            if val is None or val == 0:
                return False
        return True
    if len(arms) != 1:
        return False
    arm_norm = re.sub(r"\s+", "", _rust_strip_outer_parens(arms[0]))
    bm = re.fullmatch(
        r"(?:(?:::)?(?:core|std)::option::Option::)?Some\(([A-Za-z_][A-Za-z0-9_]*)\)",
        arm_norm,
    )
    if bm is None or bm.group(1) == "_":
        return False
    ident = re.escape(bm.group(1))
    g_ns = re.sub(r"\s+", "", guard)
    if re.fullmatch(rf"{ident}!=0|0!={ident}|{ident}>0|0<{ident}", g_ns):
        return True
    eq_m = re.fullmatch(
        rf"(?:{ident}==(-?[0-9]+(?:_[0-9]+)*)|(-?[0-9]+(?:_[0-9]+)*)=={ident})",
        g_ns,
    )
    if eq_m is not None:
        raw_num = eq_m.group(1) or eq_m.group(2)
        return int(raw_num.replace("_", "")) != 0
    return False


def _rust_eq_exit_pair_refuses(
    lhs: str,
    rhs: str,
    item: _AssertionItem,
    *,
    is_ne: bool,
    require_capture: bool,
) -> bool:
    """Return True if `lhs == rhs` (or `!=` when `is_ne`) proves observed non-zero exit."""
    if _norm_rust_expr_for_eq(lhs) == _norm_rust_expr_for_eq(rhs):
        return False
    if not is_ne:
        lhs_tup = _split_rust_tuple_elems(lhs)
        rhs_tup = _split_rust_tuple_elems(rhs)
        if (
            lhs_tup is not None
            and rhs_tup is not None
            and len(lhs_tup) == len(rhs_tup)
        ):
            return any(
                _rust_eq_exit_pair_refuses(
                    a, b, item, is_ne=False, require_capture=require_capture
                )
                for a, b in zip(lhs_tup, rhs_tup)
            )
    for a, b in ((lhs, rhs), (rhs, lhs)):
        if _rust_is_observed_status_code(a, item, require_capture=require_capture):
            val = _rust_parse_some_int_pattern(b)
            if val is not None:
                return (val == 0) if is_ne else (val != 0)
        if _rust_is_observed_success_or_ok(a, item, require_capture=require_capture):
            if is_ne and _rust_clause_is_static_true(b):
                return True
            if not is_ne and _rust_clause_is_static_false(b):
                return True
    return False


def _rust_atomic_clause_refuses_exit(
    sub: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Return True iff single Rust atomic boolean clause proves observed non-zero exit."""
    s = _rust_strip_outer_parens(sub)
    if not s or not item.subexpr_observed(s, require_capture=require_capture):
        return False
    ns = scan_rust_tokens(s).code_no_strings_or_comments.strip()
    if ns.startswith("!") and not ns.startswith("!="):
        inner = s[s.find("!") + 1 :].strip()
        return _rust_is_observed_success_or_ok(
            inner, item, require_capture=require_capture
        )
    eq_parts = _split_top_level_rust_op(s, "==")
    if len(eq_parts) == 2:
        return _rust_eq_exit_pair_refuses(
            eq_parts[0][2],
            eq_parts[1][2],
            item,
            is_ne=False,
            require_capture=require_capture,
        )
    ne_parts = _split_top_level_rust_op(s, "!=")
    if len(ne_parts) == 2:
        return _rust_eq_exit_pair_refuses(
            ne_parts[0][2],
            ne_parts[1][2],
            item,
            is_ne=True,
            require_capture=require_capture,
        )
    mm = re.match(r"^(?:(?:core|std)\s*::\s*)?matches\s*!\s*([(\[{])", ns)
    if mm is not None:
        op_idx = mm.end() - 1
        cl_idx = _find_matching_delimiter_in_code(ns, op_idx)
        if cl_idx == len(ns) - 1:
            m_args = _split_top_level_commas(
                s[op_idx + 1 : cl_idx], keep_literal_only=True
            )
            if len(m_args) >= 2 and _rust_is_observed_status_code(
                m_args[0], item, require_capture=require_capture
            ):
                return _rust_pat_is_nonzero_some(", ".join(m_args[1:]))
    return False


def _rust_expr_has_refusal(
    expr: str,
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Verify Rust `assert!` condition proves refusal or non-zero exit across `&&`/`||`."""
    if _rust_expr_has_static_true_disjunct(expr):
        return False
    expr_ns = scan_rust_tokens(expr).code_no_strings_or_comments
    needle_list = REFUSAL_TOKENS

    def _eval_span(cs: int, ce: int, *, compound: bool) -> bool:
        while cs < ce and expr[cs].isspace():
            cs += 1
        while ce > cs and expr[ce - 1].isspace():
            ce -= 1
        while cs < ce and expr_ns[cs] == "(" and expr_ns[ce - 1] == ")":
            if _find_matching_delimiter_in_code(expr_ns, cs) != ce - 1:
                break
            cs += 1
            ce -= 1
            while cs < ce and expr[cs].isspace():
                cs += 1
            while ce > cs and expr[ce - 1].isspace():
                ce -= 1
        sub = expr[cs:ce]
        or_parts = _split_top_level_rust_op(sub, "||")
        if len(or_parts) > 1:
            live = [
                p
                for p in or_parts
                if not _rust_clause_is_static_false(p[2])
            ]
            return bool(live) and all(
                _eval_span(cs + p[0], cs + p[1], compound=True)
                for p in live
            )
        and_parts = _split_top_level_rust_op(sub, "&&")
        if len(and_parts) > 1:
            return any(
                _eval_span(cs + p[0], cs + p[1], compound=True)
                for p in and_parts
            )
        if _rust_atomic_clause_refuses_exit(
            sub, item, require_capture=require_capture
        ):
            return True
        if _rust_assert_expr_is_inverted_or_tautological(sub, needle_list):
            return False
        return any(
            _rust_clause_matches_positive_needle(
                expr,
                cs,
                ce,
                sub,
                n,
                item=item,
                is_compound=compound,
                require_observed=True,
                require_capture=require_capture,
            )
            for n in needle_list
        )

    return _eval_span(0, len(expr), compound=False)


def _rust_item_has_refusal(
    item: _AssertionItem,
    *,
    require_capture: bool,
) -> bool:
    """Return True iff Rust assertion checks observed refusal or non-zero exit."""
    if not item.is_observed or (
        require_capture and item.origin_kind != "obs_capture"
    ):
        return False
    macro_name, macro_args = _rust_item_macro_and_args(item)
    needle_specs = [(tok, False) for tok in REFUSAL_TOKENS]
    if item.is_err_unwrap:
        return _rust_assertion_has_positive_needles(
            item,
            needle_specs,
            require_observed=True,
            require_capture=require_capture,
        )
    if macro_name == "assert_ne" and len(macro_args) >= 2:
        return _rust_eq_exit_pair_refuses(
            macro_args[0],
            macro_args[1],
            item,
            is_ne=True,
            require_capture=require_capture,
        )
    if macro_name == "assert_eq" and len(macro_args) >= 2:
        if _rust_assertion_has_positive_needles(
            item,
            needle_specs,
            require_observed=True,
            require_capture=require_capture,
        ):
            return True
        return _rust_eq_exit_pair_refuses(
            macro_args[0],
            macro_args[1],
            item,
            is_ne=False,
            require_capture=require_capture,
        )
    if macro_name == "assert_matches" and len(macro_args) >= 2:
        if _rust_assertion_has_positive_needles(
            item,
            needle_specs,
            require_observed=True,
            require_capture=require_capture,
        ):
            return True
        return _rust_is_observed_status_code(
            macro_args[0], item, require_capture=require_capture
        ) and _rust_pat_is_nonzero_some(", ".join(macro_args[1:]))
    return _rust_expr_has_refusal(
        item.tested_expr, item, require_capture=require_capture
    )


def _validate_observed_test_refusal(
    entry: TripwireEntry,
    items: list[_AssertionItem],
    *,
    is_python: bool,
    cfg: object | None = None,
) -> list[str]:
    """Ensure Phase-0 tag and refusal assertions dominate every live test path."""
    errors: list[str] = []
    if entry.layer == "static_capture" and entry.regression_test.endswith(".py") or (
        entry.layer == "static_capture" and ".py::" in entry.regression_test
    ):
        errors.append(
            f"{entry.regression_test}: static_capture tripwire "
            f"{entry.bug_id!r} in {TRIPWIRES_REL} must bind a Cargo .rs "
            "integration test target (ci-tests cannot execute "
            "anneal-rustc-capture)"
        )
        return errors

    need_capture = entry.layer == "static_capture"
    expected_tag = f"[PHASE0_TRIPWIRE:{entry.bug_id}]"

    def _item_has_tag(item: _AssertionItem) -> bool:
        if need_capture:
            return _rust_assertion_has_positive_needle(
                item, expected_tag, require_capture=True
            )
        if is_python:
            if entry.bug_id in item.tested_expr:
                return _py_assertion_has_positive_needle(
                    item, entry.bug_id, search_full=False
                )
            return (
                item.is_observed
                and entry.bug_id in item.full_span
                and any(
                    _py_assertion_has_positive_needle(item, tok, search_full=False)
                    for tok in PY_NONSTRING_DOMAIN_REFUSAL_TOKENS
                )
            )
        if entry.bug_id in item.tested_expr:
            return _rust_assertion_has_positive_needle(item, entry.bug_id)
        if not (
            item.is_observed
            and entry.bug_id in item.full_span
            and not _rust_assertion_is_inverted_or_tautological(item)
        ):
            return False
        _mn, m_args = _rust_item_macro_and_args(item)
        if not all(
            _rust_operand_is_trusted_projection(
                a,
                rust_env=item.rust_env,
                type_env=item.rust_type_env,
                facts=item.rust_facts,
            )
            for a in m_args
            if a.strip()
        ):
            return False
        return _rust_assertion_has_positive_needles(
            item,
            [(tok, False) for tok in RUST_NONSTRING_DOMAIN_REFUSAL_TOKENS],
            require_observed=True,
            require_capture=False,
        )

    def _item_has_refusal(item: _AssertionItem) -> bool:
        if not item.is_observed:
            return False
        if is_python:
            return _py_item_has_observed_refusal(item)
        return _rust_item_has_refusal(item, require_capture=need_capture)

    def _item_mask(item: _AssertionItem) -> int:
        mask = 0
        if _item_has_tag(item):
            mask |= 1
        if _item_has_refusal(item):
            mask |= 2
        return mask

    effective_cfg = (
        cfg if cfg is not None else _CfgSeq(tuple(_CfgItem(it) for it in items))
    )
    exit_masks = _eval_cfg_normal_exit_masks(effective_cfg, _item_mask)
    all_paths_tag = bool(exit_masks) and all((m & 1) == 1 for m in exit_masks)
    all_paths_refusal = bool(exit_masks) and all(
        (m & 2) == 2 for m in exit_masks
    )

    if not all_paths_tag:
        if need_capture:
            errors.append(
                f"{entry.regression_test}: active test assertions must "
                f"positively assert fail-closed refusal token {expected_tag!r} "
                "against an observed capture result on every successful test path"
            )
        else:
            errors.append(
                f"{entry.regression_test}: runtime/comment tripwire test "
                f"assertions must positively bind {entry.bug_id!r} alongside an "
                "observed execution result on every successful test path"
            )
    if not all_paths_refusal:
        errors.append(
            f"{entry.regression_test}: negative regression test assertions "
            "lack an observed positive refusal or unsupported-fault check "
            "on every successful test path"
        )
    return errors


def validate_entry_metadata_and_test(
    view: RepoView, entry: TripwireEntry
) -> list[str]:
    """Validate metadata, issue link, ISO date, and negative regression test."""
    errors: list[str] = []
    if not BUG_ID_RE.fullmatch(entry.bug_id):
        errors.append(
            f"{entry.source_path}: invalid Phase-0 bug_id {entry.bug_id!r} "
            "(expected {ITREE,DIFF,RT,LMIRI,MINIRUST}-<CAT>-<12hex>)"
        )
    if entry.is_synthetic_selftest:
        if entry.issue != "selftest" and not PUBLIC_ISSUE_URL_RE.fullmatch(
            entry.issue
        ):
            errors.append(
                f"{entry.source_path} ({entry.bug_id}): invalid selftest issue "
                f"{entry.issue!r}"
            )
    elif (
        entry.issue != EMBARGOED_ISSUE_TOKEN
        and not PUBLIC_ISSUE_URL_RE.fullmatch(entry.issue)
    ):
        errors.append(
            f"{entry.source_path} ({entry.bug_id}): active tripwire requires "
            "public GitHub issue URL "
            "'https://github.com/google/zerocopy/issues/<N>' or "
            f"{EMBARGOED_ISSUE_TOKEN!r}, got {entry.issue!r}"
        )
    if not entry.owner.strip():
        errors.append(f"{entry.source_path} ({entry.bug_id}): missing owner")
    if not DATE_RE.fullmatch(entry.added_date):
        errors.append(
            f"{entry.source_path} ({entry.bug_id}): invalid added_date "
            f"{entry.added_date!r} (expected YYYY-MM-DD)"
        )
    else:
        try:
            datetime.date.fromisoformat(entry.added_date)
        except ValueError as exc:
            errors.append(
                f"{entry.source_path} ({entry.bug_id}): invalid calendar "
                f"added_date {entry.added_date!r}: {exc}"
            )
    if not entry.scope.strip():
        errors.append(f"{entry.source_path} ({entry.bug_id}): missing scope")
    if not entry.rationale.strip():
        errors.append(f"{entry.source_path} ({entry.bug_id}): missing rationale")

    _raw_fn, items, test_cfg, test_err, is_python = (
        _extract_test_assertion_items_with_cfg(view, entry.regression_test)
    )
    if test_err is not None or items is None:
        errors.append(
            f"{entry.source_path} ({entry.bug_id}): {test_err or 'missing test'}"
        )
        return errors

    errors.extend(
        _validate_observed_test_refusal(
            entry, items, is_python=is_python, cfg=test_cfg
        )
    )
    return errors


def load_known_bugs(path: Path) -> tuple[list[dict[str, object]], list[str]]:
    """Load and validate a known-bugs JSON or JSONL artifact."""
    text = path.read_text(encoding="utf-8").strip()
    errors: list[str] = []
    if not text:
        return [], []
    records: list[dict[str, object]] = []
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError:
        for idx, line in enumerate(text.splitlines(), start=1):
            stripped = line.strip()
            if not stripped:
                continue
            try:
                obj = json.loads(stripped)
            except json.JSONDecodeError as exc:
                errors.append(f"{path}:{idx}: invalid JSON line: {exc}")
                continue
            if not isinstance(obj, dict):
                errors.append(f"{path}:{idx}: expected JSON object")
                continue
            records.append(obj)
        return records, errors

    if isinstance(parsed, dict):
        if "known_bugs" in parsed:
            raw_known = parsed["known_bugs"]
            if not isinstance(raw_known, list):
                return [], [
                    f"{path}: expected JSON list, JSONL, or {{'known_bugs': [...]}}"
                ]
            raw_list = raw_known
        else:
            return [parsed], []
    elif isinstance(parsed, list):
        raw_list = parsed
    else:
        return [], [f"{path}: expected JSON list, JSONL, or {{'known_bugs': [...]}}"]

    for idx, item in enumerate(raw_list):
        if not isinstance(item, dict):
            errors.append(f"{path}[{idx}]: expected JSON object")
            continue
        records.append(item)
    return records, errors


def check_known_bugs_alignment(
    known_bugs: list[dict[str, object]],
    entries: list[TripwireEntry],
    *,
    strict_mitigated_link: bool = False,
) -> tuple[list[str], list[str]]:
    """Validate known-bug lifecycle statuses against active Phase-0 tripwires."""
    errors: list[str] = []
    warnings: list[str] = []
    active_ids = {e.bug_id for e in entries if not e.is_synthetic_selftest}

    for idx, row in enumerate(known_bugs):
        bug_id = str(row.get("bug_id", ""))
        status = str(row.get("status", ""))
        raw_layer = row.get("layer")
        fixed_sha = str(row.get("fixed_sha") or row.get("resolved_by_commit") or "")
        if not BUG_ID_RE.fullmatch(bug_id):
            errors.append(f"known_bugs[{idx}]: invalid bug_id {bug_id!r}")
        if raw_layer is not None and (
            not isinstance(raw_layer, str) or raw_layer not in VALID_LAYERS
        ):
            errors.append(
                f"known_bugs[{idx}] ({bug_id}): invalid layer {raw_layer!r}; "
                f"expected one of {sorted(VALID_LAYERS)}"
            )
        if status not in VALID_BUG_STATUSES:
            errors.append(
                f"known_bugs[{idx}] ({bug_id}): invalid status {status!r}; "
                f"expected one of {sorted(VALID_BUG_STATUSES)}"
            )
        if status == "fixed" and not fixed_sha.strip():
            errors.append(
                f"known_bugs[{idx}] ({bug_id}): status='fixed' requires "
                "non-empty fixed_sha / resolved_by_commit"
            )
        if status == "fixed" and bug_id in active_ids:
            errors.append(
                f"known_bugs[{idx}] ({bug_id}): status='fixed' violates Phase-1 "
                "cleanup while active PHASE0_TRIPWIRE still exists"
            )
        if status == "mitigated_phase0" and bug_id not in active_ids:
            msg = (
                f"known_bugs[{idx}] ({bug_id}): status='mitigated_phase0' has "
                "no active PHASE0_TRIPWIRE in this checkout"
            )
            if strict_mitigated_link:
                errors.append(msg)
            else:
                warnings.append(msg)
    return errors, warnings


def check_tree(
    repo_root: Path,
    *,
    rev: str | None = None,
    known_bugs_path: Path | None = None,
    strict_mitigated_link: bool = False,
) -> PolicyReport:
    """Validate all active Phase-0 tripwires and test bindings on a tree."""
    view: RepoView = (
        GitRevRepoView(repo_root, rev)
        if rev is not None
        else FilesystemRepoView(repo_root)
    )
    try:
        entries, errors = collect_repo_tripwires(view)
    except RuntimeError as exc:
        return PolicyReport(
            ok=False,
            mode="tree",
            errors=(str(exc),),
            warnings=(),
            active_production_tripwires=(),
            synthetic_selftest_tripwires=(),
        )
    warnings: list[str] = []
    seen_ids: dict[str, TripwireEntry] = {}

    for entry in entries:
        if entry.bug_id in seen_ids:
            errors.append(
                f"duplicate PHASE0_TRIPWIRE bug_id {entry.bug_id!r} in "
                f"{seen_ids[entry.bug_id].source_path} and {entry.source_path}"
            )
        else:
            seen_ids[entry.bug_id] = entry
        errors.extend(validate_entry_metadata_and_test(view, entry))

    if known_bugs_path is not None:
        bugs, load_errs = load_known_bugs(known_bugs_path)
        errors.extend(load_errs)
        align_errs, align_warns = check_known_bugs_alignment(
            bugs, entries, strict_mitigated_link=strict_mitigated_link
        )
        errors.extend(align_errs)
        warnings.extend(align_warns)

    prod_ids = tuple(e.bug_id for e in entries if not e.is_synthetic_selftest)
    demo_ids = tuple(e.bug_id for e in entries if e.is_synthetic_selftest)
    return PolicyReport(
        ok=not errors,
        mode="tree",
        errors=tuple(errors),
        warnings=tuple(warnings),
        active_production_tripwires=prod_ids,
        synthetic_selftest_tripwires=demo_ids,
    )


def _hermetic_git_env() -> dict[str, str]:
    """Return an env stripped of ambient `GIT_*` and user Git configs."""
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env["GIT_CONFIG_GLOBAL"] = os.devnull
    env["GIT_CONFIG_SYSTEM"] = os.devnull
    env["GIT_CONFIG_NOSYSTEM"] = "1"
    env["GIT_TERMINAL_PROMPT"] = "0"
    env["LC_ALL"] = "C"
    return env


def _validate_git_ref(ref: str) -> str:
    """Reject empty or option-like Git refs before invoking `git`."""
    if not ref or ref.startswith("-") or "\0" in ref:
        raise RuntimeError(f"invalid Git ref: {ref!r}")
    return ref


def _git_output(repo_root: Path, args: list[str]) -> str:
    res = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "-c",
            "core.fsmonitor=false",
            *args,
        ],
        capture_output=True,
        text=True,
        env=_hermetic_git_env(),
        check=False,
    )
    if res.returncode != 0:
        raise RuntimeError(
            f"git {' '.join(args)} failed ({res.returncode}): "
            f"{res.stderr.strip()}"
        )
    return res.stdout


def _git_merge_base(repo_root: Path, base: str, head: str) -> str:
    """Resolve the merge-base commit between `base` and `head`."""
    _validate_git_ref(base)
    _validate_git_ref(head)
    return _git_output(
        repo_root, ["merge-base", "--end-of-options", base, head]
    ).strip()


def _parse_git_diff_raw_records(raw: str) -> list[tuple[str, str, str]]:
    """Parse `git diff --raw -z` stdout into `(old_mode, new_mode, path)`."""
    if not raw:
        return []
    tokens = raw.split("\0")
    out: list[tuple[str, str, str]] = []
    i = 0
    while i < len(tokens):
        meta = tokens[i]
        if not meta:
            i += 1
            continue
        if i + 1 >= len(tokens):
            raise RuntimeError(f"malformed git diff --raw record: {meta!r}")
        path = tokens[i + 1]
        fields = meta.lstrip(":").split()
        if len(fields) < 5:
            raise RuntimeError(f"malformed git diff --raw header: {meta!r}")
        out.append((fields[0], fields[1], path))
        i += 2
    return out


def _git_changed_raw(
    repo_root: Path, base: str, head: str
) -> list[tuple[str, str, str]]:
    """Return `(old_mode, new_mode, path)` entries across `merge-base..head`."""
    _validate_git_ref(base)
    _validate_git_ref(head)
    merge_base = _git_merge_base(repo_root, base, head)
    raw = _git_output(
        repo_root,
        [
            "diff",
            "--raw",
            "--no-renames",
            "-z",
            "--end-of-options",
            f"{merge_base}..{head}",
            "--",
        ],
    )
    return _parse_git_diff_raw_records(raw)


def _git_working_tree_changed_raw(
    repo_root: Path, base: str
) -> list[tuple[str, str, str]]:
    """Return `(old_mode, new_mode, path)` across `merge-base` to worktree."""
    _validate_git_ref(base)
    merge_base = _git_merge_base(repo_root, base, "HEAD")
    raw = _git_output(
        repo_root,
        [
            "diff",
            "--raw",
            "--no-renames",
            "-z",
            "--end-of-options",
            merge_base,
            "--",
        ],
    )
    records = _parse_git_diff_raw_records(raw)
    seen = {p for _o, _n, p in records}
    untracked = _git_output(
        repo_root, ["ls-files", "--others", "--exclude-standard", "-z"]
    )
    for path in untracked.split("\0"):
        if not path or path in seen:
            continue
        mode = "120000" if (repo_root / path).is_symlink() else "100644"
        records.append(("000000", mode, path))
    return records


def _git_show_file(repo_root: Path, rev: str, rel_path: str) -> str | None:
    _validate_git_ref(rev)
    res = subprocess.run(
        [
            "git",
            "-C",
            str(repo_root),
            "-c",
            "core.fsmonitor=false",
            "show",
            "--end-of-options",
            f"{rev}:{rel_path}",
        ],
        capture_output=True,
        text=True,
        env=_hermetic_git_env(),
        check=False,
    )
    if res.returncode != 0:
        return None
    return res.stdout


def _extract_immutable_tripwires_core(text: str) -> tuple[str | None, str | None]:
    """Return `(prefix_before_mutable_registry, cfg_test_suffix)` or `(None, None)`."""
    if (
        text.count(MUTABLE_START_MARKER) != 1
        or text.count(MUTABLE_END_MARKER) != 1
    ):
        return None, None
    start_idx = text.index(MUTABLE_START_MARKER)
    end_idx = text.index(MUTABLE_END_MARKER)
    if end_idx <= start_idx:
        return None, None
    after_end = end_idx + len(MUTABLE_END_MARKER)
    return text[:start_idx], text[after_end:]


def _normalize_rust_code_ws(text: str) -> str:
    """Normalize non-literal whitespace while keeping literal bytes intact."""
    scanned = scan_rust_tokens(text)
    nc = scanned.code_no_comments
    chunks: list[tuple[bool, str]] = []
    cursor = 0
    for s, e in scanned.literal_spans:
        if s > cursor:
            chunks.append((False, re.sub(r"\s+", " ", nc[cursor:s])))
        chunks.append((True, nc[s:e]))
        cursor = e
    if cursor < len(nc):
        chunks.append((False, re.sub(r"\s+", " ", nc[cursor:])))
    while chunks and not chunks[0][0]:
        trimmed = chunks[0][1].lstrip()
        if not trimmed:
            chunks.pop(0)
        else:
            chunks[0] = (False, trimmed)
            break
    while chunks and not chunks[-1][0]:
        trimmed = chunks[-1][1].rstrip()
        if not trimmed:
            chunks.pop()
        else:
            chunks[-1] = (False, trimmed)
            break
    return "".join(part for _is_lit, part in chunks)


def _extract_mutable_registry_parts(
    text: str,
) -> tuple[str, list[str], str] | None:
    """Split mutable registry into `(before_slice, slice_items, after_slice)`."""
    if (
        text.count(MUTABLE_START_MARKER) != 1
        or text.count(MUTABLE_END_MARKER) != 1
    ):
        return None
    start_idx = text.index(MUTABLE_START_MARKER) + len(MUTABLE_START_MARKER)
    end_idx = text.index(MUTABLE_END_MARKER)
    if end_idx <= start_idx:
        return None
    mutable_body = text[start_idx:end_idx]
    code_ns = scan_rust_tokens(mutable_body).code_no_strings_or_comments
    active_span = _find_active_slice_span(code_ns)
    if active_span is None:
        return None
    body_start, body_end, _semi_end = active_span
    before_slice = _normalize_rust_code_ws(mutable_body[:body_start])
    items = [
        _normalize_rust_code_ws(item)
        for item in _split_top_level_commas(mutable_body[body_start:body_end])
    ]
    after_slice = _normalize_rust_code_ws(mutable_body[body_end:])
    return before_slice, items, after_slice


def check_phase0_diff(
    repo_root: Path,
    *,
    base: str | None = None,
    head: str | None = None,
    diff_files: Iterable[str] | None = None,
    allow_runtime_semantics_fallback: bool = False,
) -> PolicyReport:
    """Verify a PR diff touches only isolated Phase-0 tripwire surfaces.

    Note: passing this structural surface check does NOT exempt the PR from
    repository Pass 1 / Pass 2 `trust-review` rules.
    """
    head_rev = head
    tree_rep = check_tree(repo_root, rev=head_rev)
    errors = list(tree_rep.errors)
    warnings = list(tree_rep.warnings)

    view: RepoView = (
        GitRevRepoView(repo_root, head_rev)
        if head_rev is not None
        else FilesystemRepoView(repo_root)
    )
    try:
        entries, _ = collect_repo_tripwires(view)
    except RuntimeError as exc:
        if str(exc) not in errors:
            errors.append(str(exc))
        return PolicyReport(
            ok=False,
            mode="phase0-diff",
            errors=tuple(errors),
            warnings=tuple(warnings),
            active_production_tripwires=tree_rep.active_production_tripwires,
            synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
        )

    if not base:
        errors.append(
            "phase0-diff requires --base (even when --diff-files is passed)"
        )
        return PolicyReport(
            ok=False,
            mode="phase0-diff",
            errors=tuple(errors),
            warnings=tuple(warnings),
            active_production_tripwires=tree_rep.active_production_tripwires,
            synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
        )

    changed_records: list[tuple[str, str, str]] = []
    if diff_files is not None:
        supplied_list = list(diff_files)
        supplied_set = set(supplied_list)
        try:
            git_records = (
                _git_changed_raw(repo_root, base, head)
                if head
                else _git_working_tree_changed_raw(repo_root, base)
            )
        except RuntimeError as exc:
            errors.append(str(exc))
            git_records = []
        git_by_path = {p: (o, n, p) for o, n, p in git_records}
        missing_paths = sorted(set(git_by_path) - supplied_set)
        extra_paths = sorted(supplied_set - set(git_by_path))
        if missing_paths:
            errors.append(
                f"--diff-files omits Git-changed path(s): {missing_paths}"
            )
        if extra_paths:
            errors.append(
                "--diff-files lists path(s) absent from Git diff: "
                f"{extra_paths}"
            )
        changed_records = list(git_records)
        for path in supplied_list:
            if path not in git_by_path:
                new_m = (
                    "120000"
                    if not head and (repo_root / path).is_symlink()
                    else "100644"
                )
                changed_records.append(("100644", new_m, path))
    else:
        if not head:
            errors.append(
                "phase0-diff requires --head when --diff-files is omitted"
            )
            return PolicyReport(
                ok=False,
                mode="phase0-diff",
                errors=tuple(errors),
                warnings=tuple(warnings),
                active_production_tripwires=tree_rep.active_production_tripwires,
                synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
            )
        try:
            changed_records = _git_changed_raw(repo_root, base, head)
        except RuntimeError as exc:
            errors.append(str(exc))
            changed_records = []

    if not changed_records:
        errors.append("phase0-diff found zero changed files")
    changed_paths = {path for _o, _n, path in changed_records}

    try:
        compare_base = _git_merge_base(repo_root, base, head_rev or "HEAD")
    except RuntimeError:
        compare_base = base
    base_view = GitRevRepoView(repo_root, compare_base)
    try:
        base_entries, _ = collect_repo_tripwires(base_view)
    except RuntimeError as exc:
        errors.append(f"invalid --base revision {base!r}: {exc}")
        return PolicyReport(
            ok=False,
            mode="phase0-diff",
            errors=tuple(errors),
            warnings=tuple(warnings),
            active_production_tripwires=tree_rep.active_production_tripwires,
            synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
        )
    base_by_id: dict[str, TripwireEntry] = {
        e.bug_id: e for e in base_entries if not e.is_synthetic_selftest
    }

    # Restrict dedicated *phase0*/*tripwire* test checks and edits strictly to
    # newly introduced, modified, or touched regression tests so pre-existing
    # rules in other audit/test suites do not block unrelated Phase-0 PRs.
    allowed_test_files: set[str] = set()
    for entry in entries:
        if entry.is_synthetic_selftest:
            continue
        match = REGRESSION_TEST_RE.fullmatch(entry.regression_test)
        if match is None:
            continue
        test_rel = match.group(1)
        is_new_or_changed = (
            entry.bug_id not in base_by_id or entry != base_by_id[entry.bug_id]
            if base_by_id is not None
            else (entry.source_path in changed_paths or test_rel in changed_paths)
        )
        if is_new_or_changed or test_rel in changed_paths:
            if PHASE0_TEST_FILE_RE.fullmatch(test_rel):
                allowed_test_files.add(test_rel)
            else:
                errors.append(
                    f"{entry.source_path} ({entry.bug_id}): Phase-0 diff test "
                    f"file {test_rel!r} must be a dedicated *phase0*/*tripwire* "
                    "file under anneal/tests/{rustc-capture,itree_diff}/tests/ "
                    "or anneal/ci/test_phase0_*.py"
                )

    touches_runtime_lean = False
    for old_mode, new_mode, path in changed_records:
        if "120000" in (old_mode, new_mode) or "160000" in (old_mode, new_mode):
            errors.append(f"forbidden symlink/submodule mode in diff: {path}")
            continue
        if path == TRIPWIRES_REL:
            continue
        if path in allowed_test_files:
            continue
        if (
            allow_runtime_semantics_fallback
            and _is_lean_mir_semantics_rel(path)
        ):
            touches_runtime_lean = True
            new_lean_entries = [
                e
                for e in entries
                if e.source_path == path
                and e.layer == "runtime_semantics"
                and (base_by_id is None or e.bug_id not in base_by_id)
            ]
            if not new_lean_entries:
                errors.append(
                    f"{path}: runtime MirSemantics fallback edit must add a new "
                    "-- PHASE0_TRIPWIRE(...) metadata annotation"
                )
            else:
                base_guards = (
                    _count_reachable_lean_unsupported_guards(base_view, path)
                    if base_view is not None
                    else 0
                )
                head_guards = _count_reachable_lean_unsupported_guards(
                    view, path
                )
                if head_guards < base_guards + len(new_lean_entries):
                    errors.append(
                        f"{path}: runtime MirSemantics fallback edit must add "
                        "a new reachable fail-closed `.fault .unsupported` / "
                        "`.error .unsupported` guard for each new "
                        "-- PHASE0_TRIPWIRE(...) annotation"
                    )
            continue
        errors.append(
            f"path {path!r} is outside isolated Phase-0 tripwire surface "
            "(tripwires.rs mutable registry + dedicated phase0/tripwire tests)"
        )

    if base_view is not None and compare_base is not None and base_by_id is not None:
        base_text = _git_show_file(repo_root, compare_base, TRIPWIRES_REL)
        head_text = view.read_text(TRIPWIRES_REL)
        if base_text is not None and head_text is not None:
            base_pre, base_post = _extract_immutable_tripwires_core(base_text)
            head_pre, head_post = _extract_immutable_tripwires_core(head_text)
            if head_pre is None or head_post is None:
                errors.append(
                    f"{TRIPWIRES_REL}: missing or malformed mutable-registry "
                    "markers"
                )
            elif base_pre is not None and base_post is not None:
                if base_pre != head_pre:
                    errors.append(
                        f"{TRIPWIRES_REL}: immutable harness code above "
                        f"`{MUTABLE_START_MARKER}` must not change in phase0-diff"
                    )
                if base_post != head_post:
                    errors.append(
                        f"{TRIPWIRES_REL}: test module below "
                        f"`{MUTABLE_END_MARKER}` must not change in phase0-diff"
                    )
            if head_pre is not None and head_post is not None:
                base_parts = _extract_mutable_registry_parts(base_text)
                head_parts = _extract_mutable_registry_parts(head_text)
                if head_parts is None:
                    errors.append(
                        f"{TRIPWIRES_REL}: malformed ACTIVE_PHASE0_TRIPWIRES inside "
                        "mutable registry"
                    )
                elif base_parts is not None:
                    base_before, base_items, base_after = base_parts
                    head_before, head_items, head_after = head_parts
                    if head_before != base_before:
                        errors.append(
                            f"{TRIPWIRES_REL}: existing code above "
                            "ACTIVE_PHASE0_TRIPWIRES elements must not change in "
                            "phase0-diff"
                        )
                    if not (
                        head_after == base_after
                        or head_after.startswith(f"{base_after} ")
                    ):
                        errors.append(
                            f"{TRIPWIRES_REL}: existing predicate helpers inside "
                            "mutable registry must not be modified or deleted in "
                            "phase0-diff"
                        )
                    remaining_head_items = list(head_items)
                    for base_item in base_items:
                        if base_item in remaining_head_items:
                            remaining_head_items.remove(base_item)
                        else:
                            errors.append(
                                f"{TRIPWIRES_REL}: existing PHASE0_TRIPWIRE! "
                                "element must not be deleted or weakened in "
                                "phase0-diff"
                            )
        base_prod_ids = set(base_by_id)
        head_prod_ids = set(tree_rep.active_production_tripwires)
        removed = sorted(base_prod_ids - head_prod_ids)
        if removed:
            errors.append(
                "phase0-diff must not delete existing tripwires "
                f"(use phase1-cleanup): {removed}"
            )
        added = sorted(head_prod_ids - base_prod_ids)
        if not added:
            errors.append(
                "phase0-diff must introduce at least one new active PHASE0_TRIPWIRE"
            )
        head_by_id = {
            e.bug_id: e for e in entries if not e.is_synthetic_selftest
        }
        for bid, base_entry in sorted(base_by_id.items()):
            head_entry = head_by_id.get(bid)
            if head_entry is None:
                continue
            if head_entry.regression_test != base_entry.regression_test:
                errors.append(
                    f"{head_entry.source_path} ({bid}): phase0-diff must not "
                    "rebind existing regression_test "
                    f"({base_entry.regression_test!r} -> "
                    f"{head_entry.regression_test!r})"
                )
                continue
            base_match = REGRESSION_TEST_RE.fullmatch(base_entry.regression_test)
            base_test_rel = base_match.group(1) if base_match is not None else None
            if (
                base_test_rel is not None and base_test_rel in changed_paths
            ) or head_entry != base_entry:
                base_bundle = _extract_test_witness_bundle(
                    base_view, base_entry.regression_test, bid
                )
                if base_bundle is None:
                    errors.append(
                        f"{base_entry.regression_test}: unable to extract "
                        f"Phase-0 witness bundle at --base for {bid}"
                    )
                    continue
                head_bundle = _extract_test_witness_bundle(
                    view, head_entry.regression_test, bid
                )
                if head_bundle is None:
                    errors.append(
                        f"{head_entry.regression_test}: unable to extract "
                        f"Phase-0 witness bundle at head for {bid}"
                    )
                    continue
                errors.extend(
                    _compare_witness_bundles(
                        bid,
                        head_entry.regression_test,
                        base_bundle,
                        head_bundle,
                        phase_label="Phase-0 diff",
                    )
                )
    else:
        head_text = view.read_text(TRIPWIRES_REL)
        if head_text is not None:
            head_pre, head_post = _extract_immutable_tripwires_core(head_text)
            if head_pre is None or head_post is None:
                errors.append(
                    f"{TRIPWIRES_REL}: missing or malformed mutable-registry "
                    "markers"
                )

    isolated = not errors and not touches_runtime_lean
    if touches_runtime_lean:
        warnings.append(
            "Diff touches Trusted/MirSemantics/*.lean runtime fallback; "
            "requires full Pass 2 semantic review"
        )
    return PolicyReport(
        ok=not errors,
        mode="phase0-diff",
        errors=tuple(errors),
        warnings=tuple(warnings),
        active_production_tripwires=tree_rep.active_production_tripwires,
        synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
        isolated_tripwire_surface=isolated,
        requires_full_semantic_review=touches_runtime_lean,
    )


PHASE1_UNSUPPORTED_TOKENS = (
    "unsupported",
    "Unsupported",
    "CaptureRefused",
    ".fault .unsupported",
    "FaultKind::Unsupported",
)
PHASE1_EXIT_ONLY_REFUSAL_RE = re.compile(
    r"(?:status(?:\s*\(\s*\))?\s*\.\s*)?code\s*\(\s*\)\s*"
    r"(?:,\s*Some\s*\(\s*[1-9]|==\s*Some\s*\(\s*[1-9]|!=\s*Some\s*\(\s*0\s*\))"
    r"|Some\s*\(\s*[1-9][0-9]*\s*\)\s*(?:,|==)\s*[^,\n]*code\s*\(\s*\)"
    r"|Some\s*\(\s*0\s*\)\s*!=\s*[^,\n]*code\s*\(\s*\)"
    r"|!\s*\(*[^,;!\n]*\.\s*success\s*\(\s*\)"
    r"|!\s*\(*[^,;!\n]*\.\s*is_ok\s*\(\s*\)"
    r"|\.\s*(?:success|is_ok)\s*\(\s*\)\s*(?:==\s*false\b|!=\s*true\b)"
    r"|\b(?:false\s*==|true\s*!=)\s*[^,;!\n]*\.\s*(?:success|is_ok)\s*\(\s*\)"
    r"|\breturncode\b[^,\n]*,\s*[1-9]"
    r"|\breturncode\s*!=\s*0\b"
    r"|\b0\s*!=\s*[^,\n]*\breturncode\b"
    r"|\breturncode\s*==\s*[1-9]"
    r"|\b[1-9][0-9]*\s*==\s*[^,\n]*\breturncode\b"
)
PHASE1_EXIT_REFUSAL_RE = re.compile(
    rf"{PHASE1_EXIT_ONLY_REFUSAL_RE.pattern}|\.(?:unwrap_err|expect_err|is_err)\s*\("
)


def _py_ast_mentions_returncode(node: ast.AST) -> bool:
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and sub.id == "returncode":
            return True
        if isinstance(sub, ast.Attribute) and sub.attr == "returncode":
            return True
    return False


def _py_const_int(node: ast.AST) -> int | None:
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return node.value
    if (
        isinstance(node, ast.UnaryOp)
        and isinstance(node.op, ast.USub)
        and isinstance(node.operand, ast.Constant)
        and type(node.operand.value) is int
    ):
        return -node.operand.value
    return None


def _py_expr_refuses_exit(node: ast.AST, *, negated: bool = False) -> bool:
    """Return True if Python AST `node` asserts non-zero `returncode` / failure."""
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return _py_expr_refuses_exit(node.operand, negated=not negated)
    if isinstance(node, ast.BoolOp):
        return any(
            _py_expr_refuses_exit(v, negated=negated) for v in node.values
        )
    if isinstance(node, ast.Compare) and len(node.ops) == 1:
        op = node.ops[0]
        left, right = node.left, node.comparators[0]
        l_rc = _py_ast_mentions_returncode(left)
        r_rc = _py_ast_mentions_returncode(right)
        if l_rc or r_rc:
            val = _py_const_int(right if l_rc else left)
            if not negated:
                if isinstance(op, ast.NotEq) and val == 0:
                    return True
                if isinstance(op, ast.Eq) and val is not None and val != 0:
                    return True
                if isinstance(op, ast.Gt) and l_rc and val == 0:
                    return True
                if isinstance(op, ast.Lt) and r_rc and val == 0:
                    return True
            else:
                if isinstance(op, ast.Eq) and val == 0:
                    return True
    if negated:
        src = ast.unparse(node)
        if re.search(r"\b(?:success|is_ok)\b", src) is not None:
            return True
    return False


def _phase1_py_item_refuses_exit(item: _AssertionItem) -> bool:
    """AST-based Phase-1 exit-refusal detector for Python assertions."""
    try:
        tree = ast.parse(item.full_span.strip(), mode="exec")
    except SyntaxError:
        return PHASE1_EXIT_ONLY_REFUSAL_RE.search(item.full_span) is not None
    if len(tree.body) != 1:
        return False
    stmt = tree.body[0]
    if isinstance(stmt, ast.Assert):
        return _py_expr_refuses_exit(stmt.test, negated=False)
    if (
        isinstance(stmt, ast.Expr)
        and isinstance(stmt.value, ast.Call)
        and isinstance(stmt.value.func, ast.Attribute)
    ):
        attr = stmt.value.func.attr
        args = _bind_unittest_call_args(stmt.value)
        if not args:
            return False
        if attr == "assertTrue" and args:
            return _py_expr_refuses_exit(args[0], negated=False)
        if attr == "assertFalse" and args:
            return _py_expr_refuses_exit(args[0], negated=True)
        if attr == "assertNotEqual" and len(args) >= 2:
            if (
                _py_ast_mentions_returncode(args[0])
                and _py_const_int(args[1]) == 0
            ) or (
                _py_ast_mentions_returncode(args[1])
                and _py_const_int(args[0]) == 0
            ):
                return True
        if attr == "assertEqual" and len(args) >= 2:
            for a, b in ((args[0], args[1]), (args[1], args[0])):
                if _py_ast_mentions_returncode(a):
                    v = _py_const_int(b)
                    if v is not None and v != 0:
                        return True
        if attr == "assertGreater" and len(args) >= 2:
            if _py_ast_mentions_returncode(args[0]) and _py_const_int(args[1]) == 0:
                return True
        if attr == "assertLess" and len(args) >= 2:
            if _py_ast_mentions_returncode(args[1]) and _py_const_int(args[0]) == 0:
                return True
    return False


def _has_meaningful_phase1_assertion(assertions_text: str) -> bool:
    """Reject empty test bodies or purely constant/tautological assertions."""
    if not assertions_text.strip():
        return False
    for raw_line in assertions_text.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith(("assert ", "assert(", "self.assert", "self.fail")):
            try:
                tree = ast.parse(line, mode="exec")
            except SyntaxError:
                if _rust_expr_has_observed_value(line):
                    return True
                continue
            if len(tree.body) == 1:
                stmt = tree.body[0]
                if isinstance(stmt, ast.Assert):
                    if _py_expr_has_observed_value(ast.unparse(stmt.test)):
                        return True
                    continue
                if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                    tup = ast.Tuple(
                        elts=[
                            *stmt.value.args,
                            *(
                                kw.value
                                for kw in stmt.value.keywords
                                if kw.arg != "msg"
                            ),
                        ],
                        ctx=ast.Load(),
                    )
                    if _py_expr_has_observed_value(ast.unparse(tup)):
                        return True
                    continue
        stripped_rust = re.sub(
            r"\bassert(?:_eq|_ne|_matches)?\s*!", " ", line
        )
        stripped_rust = re.sub(
            r"\.(?:unwrap_err|expect_err|is_err)\s*\(", " ", stripped_rust
        )
        if _rust_expr_has_observed_value(stripped_rust):
            return True
    return False


def _phase1_item_asserts_unsupported(
    item: _AssertionItem, *, is_python: bool
) -> bool:
    """Return True if `item` positively asserts an unsupported refusal."""
    if is_python:
        return any(
            _py_assertion_has_positive_needle(
                item, tok, search_full=False, require_observed=False
            )
            for tok in PHASE1_UNSUPPORTED_TOKENS
        )
    return any(
        _rust_assertion_has_positive_needle(item, tok, require_observed=False)
        for tok in PHASE1_UNSUPPORTED_TOKENS
    )


def _phase1_item_refuses_exit(
    item: _AssertionItem, *, is_python: bool
) -> bool:
    """Return True if `item` positively asserts error/non-zero exit."""
    if is_python:
        if re.search(r"\.(?:unwrap_err|expect_err)\s*\(", item.tested_expr):
            return True
        if re.search(r"\.is_err\s*\(", item.tested_expr) and (
            _py_assertion_has_positive_needle(
                item, "is_err", search_full=False, require_observed=False
            )
        ):
            return True
        return _phase1_py_item_refuses_exit(item)

    if re.search(r"\.(?:unwrap_err|expect_err)\s*\(", item.tested_expr):
        return True
    if re.search(r"\.is_err\s*\(", item.tested_expr):
        norm_full = re.sub(r"\.is_err\s*\(", ".is_err(", item.full_span)
        norm_tested = re.sub(r"\.is_err\s*\(", ".is_err(", item.tested_expr)
        norm_item = _AssertionItem(
            full_span=norm_full,
            tested_expr=norm_tested,
            is_observed=item.is_observed,
            tested_args=tuple(
                re.sub(r"\.is_err\s*\(", ".is_err(", a)
                for a in item.tested_args
            ),
            rust_env=item.rust_env,
            rust_type_env=item.rust_type_env,
            pure_rust_fns=item.pure_rust_fns,
            rust_facts=item.rust_facts,
        )
        if _rust_assertion_has_positive_needle(
            norm_item, "is_err(", require_observed=False
        ):
            return True

    macro_name, macro_args = _rust_item_macro_and_args(item)
    if macro_name == "assert_ne" and len(macro_args) >= 2:
        a0, a1 = macro_args[0], macro_args[1]
        if (
            re.search(r"\.\s*code\s*\(\s*\)", a0)
            and re.search(r"\bSome\s*\(\s*0\s*\)", a1)
        ) or (
            re.search(r"\.\s*code\s*\(\s*\)", a1)
            and re.search(r"\bSome\s*\(\s*0\s*\)", a0)
        ):
            return True
        if (
            re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)", a0)
            and _rust_clause_is_static_true(a1)
        ) or (
            re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)", a1)
            and _rust_clause_is_static_true(a0)
        ):
            return True
        return False

    if macro_name == "assert_eq" and len(macro_args) >= 2:
        a0, a1 = macro_args[0], macro_args[1]
        if (
            re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)", a0)
            and _rust_clause_is_static_false(a1)
        ) or (
            re.search(r"\.\s*(?:success|is_ok)\s*\(\s*\)", a1)
            and _rust_clause_is_static_false(a0)
        ):
            return True
        if (
            re.search(r"\.\s*code\s*\(\s*\)", a0)
            and re.search(r"\bSome\s*\(\s*[1-9][0-9]*\s*\)", a1)
        ) or (
            re.search(r"\.\s*code\s*\(\s*\)", a1)
            and re.search(r"\bSome\s*\(\s*[1-9][0-9]*\s*\)", a0)
        ):
            return True

    if macro_name == "assert_matches" and len(macro_args) >= 2:
        if re.search(r"\.\s*code\s*\(\s*\)", macro_args[0]) and re.search(
            r"\bSome\s*\(\s*[1-9]", macro_args[1]
        ):
            return True

    return PHASE1_EXIT_ONLY_REFUSAL_RE.search(item.tested_expr) is not None


RUST_CLI_PLUMBING_LITERALS = frozenset(
    {
        "capture",
        "session",
        "verify",
        "input.rs",
        "lib.rs",
        "main.rs",
        "output",
        "out",
        "capture.json",
        "Captured.lean",
        "status",
        "unsupported",
        "captured",
        "reason",
        "diagnostics",
        "disabled",
        "--crate-root",
        "--out-dir",
        "--sysroot",
        "--source-file",
        "--env",
    }
)
GENERIC_WITNESS_SETUP_VERBS = frozenset(
    {
        "run_capture",
        "try_capture",
        "invoke_capture",
        "exec_capture",
        "captures_cleanly",
        "captures_cleanly_and_matches_miri_fault_ub",
        "run_lean_step",
        "run_audit",
        "run_probe",
        "matches_miri_fault_ub",
        "parse_status",
        "sysroot",
        "default_rust_sysroot",
        "anneal_testkit",
        "CaptureFixture",
        "Capture",
        "Command",
        "Output",
        "Value",
        "Path",
        "PathBuf",
        "TempDir",
        "String",
        "Vec",
        "Some",
        "None",
        "Ok",
        "Err",
        "FaultKind",
        "Unsupported",
        "std",
        "core",
        "fs",
        "io",
        "env",
        "process",
        "tempfile",
        "tempdir",
        "serde_json",
        "from_slice",
        "from_str",
        "new",
        "command",
        "command_with",
        "command_in",
        "selected_command",
        "arg",
        "args",
        "current_dir",
        "output",
        "status",
        "code",
        "success",
        "unwrap",
        "expect",
        "unwrap_or",
        "unwrap_or_default",
        "unwrap_err",
        "expect_err",
        "is_err",
        "is_ok",
        "is_file",
        "as_str",
        "as_bytes",
        "to_string",
        "to_owned",
        "into",
        "from",
        "clone",
        "join",
        "path",
        "write",
        "read",
        "read_to_string",
        "assert_no_capture_artifacts",
    }
)


def _decode_rust_byte_literal(raw_lit: str) -> bytes | None:
    """Decode Rust `b"..."` / `br(#*)"..."(#*)` literals losslessly into `bytes`."""
    s = raw_lit.strip()
    raw_m = re.match(r'^br(#*)"', s)
    if raw_m is not None:
        close_pat = '"' + raw_m.group(1)
        end = s.find(close_pat, raw_m.end())
        if end == -1 or s[end + len(close_pat) :].strip():
            return None
        try:
            return s[raw_m.end() : end].encode("latin-1")
        except UnicodeEncodeError:
            return None
    if not (s.startswith('b"') and len(s) >= 3):
        return None
    out = bytearray()
    j = 2
    n = len(s)
    simple = {
        '"': ord('"'),
        "'": ord("'"),
        "\\": ord("\\"),
        "n": ord("\n"),
        "r": ord("\r"),
        "t": ord("\t"),
        "0": 0,
    }
    while j < n:
        ch = s[j]
        if ch == '"':
            if s[j + 1 :].strip():
                return None
            return bytes(out)
        if ch == "\\":
            if j + 1 >= n:
                return None
            nxt = s[j + 1]
            if nxt == "\n":
                j += 2
                while j < n and s[j] in (" ", "\t"):
                    j += 1
                continue
            if nxt in simple:
                out.append(simple[nxt])
                j += 2
                continue
            if nxt == "x" and j + 3 < n:
                try:
                    out.append(int(s[j + 2 : j + 4], 16))
                    j += 4
                    continue
                except ValueError:
                    return None
            out.append(ord("\\"))
            out.append(ord(nxt))
            j += 2
            continue
        code = ord(ch)
        if code > 0xFF:
            out.extend(ch.encode("utf-8"))
        else:
            out.append(code)
        j += 1
    return None


@dataclass(frozen=True)
class _WitnessBundle:
    """Extracted Phase-0 witness inputs for preservation checks."""

    witness_literals: frozenset[str] = frozenset()
    witness_bytes: frozenset[bytes] = frozenset()
    fixture_files: dict[str, str] | None = None
    fixture_symbols: frozenset[str] = frozenset()


def _decode_any_rust_string_literal(raw_lit: str) -> str | None:
    """Decode Rust string, raw-string, byte-string, or C-string literals."""
    s = raw_lit.strip()
    if s.startswith(("br", "cr")) and len(s) > 2 and s[2] in ('"', "#"):
        s = s[1:]
    elif s.startswith(('b"', 'c"')):
        s = s[1:]
    return _decode_single_string_literal(s)


def _is_witness_candidate_literal(val: str, bug_id: str) -> bool:
    """Filter out assertion/CLI-plumbing tokens while keeping witness inputs."""
    if not val or not val.strip():
        return False
    if (
        "PHASE0_TRIPWIRE" in val
        or "ANNEAL_PHASE0_TRIPWIRE" in val
        or (bug_id and bug_id in val)
    ):
        return False
    if val in RUST_CLI_PLUMBING_LITERALS:
        return False
    if val.startswith(("--crate-name=", "--target=")):
        return False
    return True


def _is_witness_candidate_bytes(raw: bytes, bug_id: str) -> bool:
    """Filter byte plumbing tokens while keeping binary/byte witness inputs."""
    if not raw or not raw.strip():
        return False
    if (
        b"PHASE0_TRIPWIRE" in raw
        or b"ANNEAL_PHASE0_TRIPWIRE" in raw
        or (bug_id and bug_id.encode("utf-8") in raw)
    ):
        return False
    if raw in {lit.encode("utf-8") for lit in RUST_CLI_PLUMBING_LITERALS}:
        return False
    if raw.startswith((b"--crate-name=", b"--target=")):
        return False
    return True


def _str_to_utf8_bytes_strict(val: str) -> bytes | None:
    """Encode `val` to UTF-8 bytes iff strictly representable (no surrogates)."""
    try:
        return val.encode("utf-8")
    except UnicodeEncodeError:
        return None


def _compare_witness_bundles(
    bug_id: str,
    label: str,
    base_bundle: _WitnessBundle,
    head_bundle: _WitnessBundle,
    *,
    phase_label: str,
) -> list[str]:
    """Verify `head_bundle` preserves fixture files, literals, bytes, and symbols."""
    errors: list[str] = []
    head_files = head_bundle.fixture_files or {}
    for f_path, base_txt in sorted((base_bundle.fixture_files or {}).items()):
        if head_files.get(f_path) != base_txt:
            errors.append(
                f"{label}: {phase_label} modified or dropped Phase-0 witness "
                f"fixture file {f_path!r} for {bug_id}"
            )
    head_lit_bytes = {
        raw_b
        for lit in head_bundle.witness_literals
        if (raw_b := _str_to_utf8_bytes_strict(lit)) is not None
    }
    all_head_bytes = set(head_bundle.witness_bytes) | head_lit_bytes
    missing_lits = [
        lit
        for lit in sorted(base_bundle.witness_literals)
        if lit not in head_bundle.witness_literals
        and (
            (raw_b := _str_to_utf8_bytes_strict(lit)) is None
            or raw_b not in head_bundle.witness_bytes
        )
    ]
    missing_bytes = [
        raw_b
        for raw_b in sorted(base_bundle.witness_bytes)
        if raw_b not in all_head_bytes
    ]
    if missing_lits or missing_bytes:
        errors.append(
            f"{label}: {phase_label} must preserve original Phase-0 failing "
            f"witness input for {bug_id}"
        )
    if (
        not base_bundle.witness_literals
        and not base_bundle.witness_bytes
        and not base_bundle.fixture_files
        and base_bundle.fixture_symbols
    ):
        missing_syms = sorted(
            base_bundle.fixture_symbols - head_bundle.fixture_symbols
        )
        if missing_syms:
            errors.append(
                f"{label}: {phase_label} replaced Phase-0 witness fixture "
                f"{missing_syms!r} for {bug_id}"
            )
    return errors


def _resolve_repo_fixture_path(
    view: RepoView, rel_test_path: str, candidate: str
) -> tuple[str, str] | None:
    """Return `(repo_rel, text)` if `candidate` names a regular repo file."""
    if not candidate or "\n" in candidate or "\0" in candidate:
        return None
    if len(candidate) > 240 or candidate.startswith(("-", "/")):
        return None
    parent = posixpath.dirname(rel_test_path)
    rel_cands: list[str] = []
    for raw in (
        posixpath.join(parent, candidate) if parent else candidate,
        candidate,
    ):
        norm = posixpath.normpath(raw)
        if norm not in rel_cands:
            rel_cands.append(norm)
    for rc in rel_cands:
        if (
            not rc
            or rc == "."
            or ".." in PurePosixPath(rc).parts
            or rc.startswith("/")
        ):
            continue
        ok, _ = view.is_regular_file(rc)
        if ok and rc != rel_test_path and rc != TRIPWIRES_REL:
            txt = view.read_text(rc)
            if txt is not None:
                return rc, txt
    return None


def _blank_rust_assertions_and_panics(
    code_nc: str, code_ns: str
) -> tuple[str, str]:
    """Blank assertion macros, panic/expect messages, and JSON index keys."""
    nc_chars = list(code_nc)
    ns_chars = list(code_ns)
    skip_macro_re = re.compile(
        r"\b(?:assert(?:_eq|_ne|_matches)?|panic|unreachable|todo"
        r"|unimplemented|env)\s*!\s*([(\[{])"
    )
    for m in skip_macro_re.finditer(code_ns):
        open_i = m.end() - 1
        close_i = _find_matching_delimiter_in_code(code_ns, open_i)
        end_i = (close_i + 1) if close_i is not None else len(code_ns)
        _blank_span(nc_chars, m.start(), end_i)
        _blank_span(ns_chars, m.start(), end_i)

    expect_call_re = re.compile(r"\.\s*(?:expect|expect_err)\s*\(")
    for m in expect_call_re.finditer(code_ns):
        open_i = m.end() - 1
        close_i = _find_matching_delimiter_in_code(code_ns, open_i)
        if close_i is not None:
            _blank_span(nc_chars, m.start(), close_i + 1)
            _blank_span(ns_chars, m.start(), close_i + 1)
    return "".join(nc_chars), "".join(ns_chars)


def _prune_unused_rust_local_lets(fn_nc: str, fn_ns: str) -> tuple[str, str]:
    """Blank `let <v> = ...;` statements whose bound locals are never read."""
    nc_chars = list(fn_nc)
    ns_chars = list(fn_ns)
    inner_s = fn_ns.find("{")
    inner_e = fn_ns.rfind("}")
    if inner_s == -1 or inner_e <= inner_s:
        return fn_nc, fn_ns
    segs = _split_rust_top_level_segments(fn_ns, inner_s + 1, inner_e)
    for kind, s_start, s_end, _br in segs:
        if kind != "stmt":
            continue
        stmt_ns = fn_ns[s_start:s_end]
        if not stmt_ns.lstrip().startswith("let"):
            continue
        eq_pos = _find_rust_top_level_equal(stmt_ns)
        if eq_pos is None:
            continue
        lhs_idents = _extract_rust_pattern_idents(stmt_ns[:eq_pos])
        if not lhs_idents:
            _blank_span(nc_chars, s_start, s_end)
            _blank_span(ns_chars, s_start, s_end)
            continue
        tail_ns = fn_ns[s_end:inner_e]
        if not any(
            re.search(rf"\b{re.escape(v)}\b", tail_ns) is not None
            for v in lhs_idents
        ):
            _blank_span(nc_chars, s_start, s_end)
            _blank_span(ns_chars, s_start, s_end)
    return "".join(nc_chars), "".join(ns_chars)


RUST_DECOY_SINK_RE = re.compile(
    r"^(?:(?:::\s*)?(?:std|core)\s*::\s*(?:hint|mem)\s*::\s*)?"
    r"(?:black_box|drop|forget)\s*(?:::\s*<[^;()]*>)?\s*\("
    r"|^(?:(?:::\s*)?(?:std|core)\s*::\s*)?"
    r"(?:dbg|println|eprintln|print|eprint)\s*!"
)


def _rust_ident_set(code_ns: str) -> set[str]:
    """Return non-keyword identifiers occurring in `code_ns`."""
    stripped = _strip_rust_numeric_literals(code_ns)
    return {
        tok
        for tok in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", stripped)
        if tok not in PURE_RUST_IDENT_IGNORED
        and tok not in ("Some", "None", "Ok", "Err")
    }


def _strip_rust_decoy_stmts(code_nc: str, code_ns: str) -> tuple[str, str]:
    """Blank discarded decoy statements (`black_box(...)`, `drop(...)`, `let _ = ...`) in blocks."""
    nc_chars = list(code_nc)
    ns_chars = list(code_ns)

    def _clean_block(b_open: int, b_close: int) -> None:
        segs = _split_rust_top_level_segments(code_ns, b_open + 1, b_close)
        for kind, s_start, s_end, sub_br in segs:
            if kind == "block" and sub_br is not None:
                _clean_block(sub_br, s_end - 1)
                continue
            stmt_ns = code_ns[s_start:s_end].strip()
            if not stmt_ns:
                continue
            # Discarded `;`-terminated statements calling pure decoy sinks.
            if stmt_ns.endswith(";") and RUST_DECOY_SINK_RE.match(stmt_ns):
                _blank_span(nc_chars, s_start, s_end)
                _blank_span(ns_chars, s_start, s_end)
                continue
            eq_pos = _find_rust_top_level_equal(stmt_ns)
            if eq_pos is not None:
                lhs = stmt_ns[:eq_pos]
                if not _extract_rust_pattern_idents(lhs) and stmt_ns.lstrip().startswith("let"):
                    _blank_span(nc_chars, s_start, s_end)
                    _blank_span(ns_chars, s_start, s_end)
                    continue
                # Recurse into block expressions inside RHS `{ ... }`.
                rhs_abs = s_start + code_ns[s_start:s_end].find("=") + 1
                sub_o = code_ns.find("{", rhs_abs, s_end)
                while sub_o != -1 and sub_o < s_end:
                    sub_c = _find_matching_delimiter_in_code(code_ns, sub_o)
                    if sub_c is not None and sub_c < s_end:
                        _clean_block(sub_o, sub_c)
                        sub_o = code_ns.find("{", sub_c + 1, s_end)
                    else:
                        break

    inner_s = code_ns.find("{")
    inner_e = code_ns.rfind("}")
    if inner_s != -1 and inner_e > inner_s:
        _clean_block(inner_s, inner_e)
    return "".join(nc_chars), "".join(ns_chars)


def _blank_unused_rust_helper_call_args(
    chunk_nc: str,
    chunk_ns: str,
    helper_used_params: dict[str, set[int]],
) -> tuple[str, str]:
    """Blank call arguments corresponding to unused helper parameters."""
    if not helper_used_params:
        return chunk_nc, chunk_ns
    nc_chars = list(chunk_nc)
    ns_chars = list(chunk_ns)
    for m in re.finditer(
        r"\b([A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(", chunk_ns
    ):
        callee = m.group(1)
        used = helper_used_params.get(callee)
        if used is None:
            continue
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(chunk_ns, open_p)
        if close_p is None:
            continue
        # Compute top-level comma-separated arg spans in `(open_p+1, close_p)`.
        p_d = b_d = br_d = 0
        arg_start = open_p + 1
        arg_spans: list[tuple[int, int]] = []
        for idx in range(open_p + 1, close_p):
            ch = chunk_ns[idx]
            if ch == "(":
                p_d += 1
            elif ch == ")" and p_d > 0:
                p_d -= 1
            elif ch == "[":
                b_d += 1
            elif ch == "]" and b_d > 0:
                b_d -= 1
            elif ch == "{":
                br_d += 1
            elif ch == "}" and br_d > 0:
                br_d -= 1
            elif p_d == 0 and b_d == 0 and br_d == 0 and ch == ",":
                arg_spans.append((arg_start, idx))
                arg_start = idx + 1
        if arg_start < close_p and chunk_ns[arg_start:close_p].strip():
            arg_spans.append((arg_start, close_p))
        for arg_idx, (a_s, a_e) in enumerate(arg_spans):
            if arg_idx not in used:
                _blank_span(nc_chars, a_s, a_e)
                _blank_span(ns_chars, a_s, a_e)
    return "".join(nc_chars), "".join(ns_chars)


def _extract_inline_observed_rust_calls(
    item: _AssertionItem,
) -> list[tuple[str, str]]:
    """Extract capture/driver call expressions embedded directly inside an assertion."""
    out: list[tuple[str, str]] = []
    # Standalone `.unwrap_err()` / `.expect_err(...)` assertion item: use the
    # saved receiver expression (panic message was stripped from `tested_expr`).
    if item.is_err_unwrap or RUST_ASSERT_START_RE.match(item.full_span.lstrip()) is None:
        recv_nc = item.err_unwrap_recv or item.tested_expr
        recv_ns = scan_rust_tokens(recv_nc).code_no_strings_or_comments
        clean_nc, clean_ns = _blank_rust_assertions_and_panics(recv_nc, recv_ns)
        out.append((clean_nc, clean_ns))
        return out
    expr_nc = item.tested_expr
    scanned = scan_rust_tokens(expr_nc)
    expr_ns = scanned.code_no_strings_or_comments
    for m in re.finditer(
        r"(?<!\.)\b((?:[A-Za-z_][A-Za-z0-9_]*\s*::\s*)*"
        r"[A-Za-z_][A-Za-z0-9_]*)\s*(?:::\s*<[^;()]*>)?\s*\(",
        expr_ns,
    ):
        open_p = m.end() - 1
        close_p = _find_matching_delimiter_in_code(expr_ns, open_p)
        if close_p is None:
            continue
        call_nc = expr_nc[m.start() : close_p + 1]
        call_ns = expr_ns[m.start() : close_p + 1]
        # Extract only calls that invoke capture/driver (not `.contains(...)`).
        okind = _rust_expr_origin_kind(
            call_nc,
            call_ns,
            rust_env={},
            rust_facts=item.rust_facts,
            rust_type_env=item.rust_type_env,
        )
        if okind in RUST_OBS_STATES:
            out.append((call_nc, call_ns))
    return out


def _slice_rust_witness_chunks(
    live_nc: str,
    live_ns: str,
    items: list[_AssertionItem],
) -> list[tuple[str, str]]:
    """Backward-slice Rust statements feeding observed assertions (dropping decoys)."""
    obs_items = [it for it in items if it.is_observed]
    if not obs_items:
        return []
    live_vars: set[str] = set()
    selected_chunks: list[tuple[str, str]] = []
    for it in obs_items:
        seed_src = it.err_unwrap_recv if it.is_err_unwrap else it.tested_expr
        it_ns = scan_rust_tokens(seed_src).code_no_strings_or_comments
        for ident in _rust_ident_set(it_ns):
            if it.rust_env is None or it.rust_env.get(ident) in RUST_OBS_STATES:
                live_vars.add(ident)
        selected_chunks.extend(_extract_inline_observed_rust_calls(it))

    stmts_info: list[tuple[str, str, set[str], set[str]]] = []

    def _collect_stmts(reg_s: int, reg_e: int) -> None:
        for kind, s_start, s_end, br_open in _split_rust_top_level_segments(
            live_ns, reg_s, reg_e
        ):
            if kind == "block" and br_open is not None:
                hdr_nc = live_nc[s_start:br_open]
                hdr_ns = live_ns[s_start:br_open]
                let_m = re.match(
                    r"^\s*(?:else\s+)?(?:if|while)\s+let\b([\s\S]+)$", hdr_ns
                )
                if let_m is not None:
                    eq_p = _find_rust_top_level_equal(let_m.group(1))
                    if eq_p is not None:
                        p_defs = set(
                            _extract_rust_pattern_idents(let_m.group(1)[:eq_p])
                        )
                        off = let_m.start(1) + eq_p + 1
                        stmts_info.append(
                            (
                                hdr_nc[off:],
                                hdr_ns[off:],
                                p_defs,
                                _rust_ident_set(hdr_ns[off:]),
                            )
                        )
                else:
                    for_m = re.match(r"^\s*for\b([\s\S]+)$", hdr_ns)
                    if for_m is not None:
                        sep_m = re.search(r"\bin\b", for_m.group(1))
                        if sep_m is not None:
                            p_defs = set(
                                _extract_rust_pattern_idents(
                                    for_m.group(1)[: sep_m.start()]
                                )
                            )
                            off = for_m.start(1) + sep_m.end()
                            stmts_info.append(
                                (
                                    hdr_nc[off:],
                                    hdr_ns[off:],
                                    p_defs,
                                    _rust_ident_set(hdr_ns[off:]),
                                )
                            )
                    else:
                        match_m = re.match(r"^\s*match\b([\s\S]+)$", hdr_ns)
                        if match_m is not None:
                            sc_off = match_m.start(1)
                            arm_spans = _split_rust_match_arm_spans(
                                live_ns, br_open + 1, s_end - 1
                            )
                            arm_defs: set[str] = set()
                            for pat_s, pat_e, rhs_s, rhs_e in arm_spans:
                                pat_only, _ = _strip_rust_match_guard(
                                    live_ns[pat_s:pat_e]
                                )
                                arm_defs.update(
                                    _extract_rust_pattern_idents(pat_only)
                                )
                                rhs_sl = live_ns[rhs_s:rhs_e].strip()
                                if rhs_sl.startswith("{"):
                                    ao = live_ns.find("{", rhs_s, rhs_e)
                                    ac = _find_matching_delimiter_in_code(
                                        live_ns, ao
                                    )
                                    if ac is not None:
                                        _collect_stmts(ao + 1, ac)
                                else:
                                    _collect_stmts(rhs_s, rhs_e)
                            stmts_info.append(
                                (
                                    hdr_nc[sc_off:],
                                    hdr_ns[sc_off:],
                                    arm_defs,
                                    _rust_ident_set(hdr_ns[sc_off:]),
                                )
                            )
                            continue
                _collect_stmts(br_open + 1, s_end - 1)
                continue

            s_nc = live_nc[s_start:s_end]
            s_ns = live_ns[s_start:s_end]
            s_strip = s_ns.strip()
            if not s_strip:
                continue
            if RUST_ASSERT_START_RE.match(s_strip):
                continue
            if RUST_DECOY_SINK_RE.match(s_strip):
                continue
            eq_pos = _find_rust_top_level_equal(s_ns)
            if eq_pos is not None:
                lhs_ns = s_ns[:eq_pos]
                rhs_nc = s_nc[eq_pos + 1 :]
                rhs_ns = s_ns[eq_pos + 1 :]
                # Clean any discarded decoy statements inside RHS block exprs.
                rhs_nc_clean, rhs_ns_clean = _strip_rust_decoy_stmts(
                    rhs_nc, rhs_ns
                )
                defs = set(_extract_rust_pattern_idents(lhs_ns))
                if not defs and not lhs_ns.lstrip().startswith("let"):
                    root_m = re.match(r"^\s*(?:\*\s*)*([A-Za-z_][A-Za-z0-9_]*)", lhs_ns)
                    if root_m is not None and root_m.group(1) != "_":
                        defs.add(root_m.group(1))
                uses = _rust_ident_set(rhs_ns_clean)
                stmts_info.append((rhs_nc_clean, rhs_ns_clean, defs, uses))
                continue

            defs = set()
            uses = _rust_ident_set(s_ns)
            # Filesystem writes tie path variable(s) to written witness content.
            fs_m = re.search(
                r"\b(?:fs\s*::\s*write|File\s*::\s*create)\s*\(", s_ns
            )
            if fs_m is not None:
                op = fs_m.end() - 1
                cp = _find_matching_delimiter_in_code(s_ns, op)
                if cp is not None:
                    f_args = _split_top_level_commas(
                        s_ns[op + 1 : cp], keep_literal_only=True
                    )
                    if f_args:
                        defs.update(_rust_ident_set(f_args[0]))
            for mut_m in re.finditer(
                r"&\s*mut\s+([A-Za-z_][A-Za-z0-9_]*)\b", s_ns
            ):
                defs.add(mut_m.group(1))
            # Receiver method mutations (`cmd.arg(&src)`, `write_all(...)`).
            recv_m = re.match(
                r"^\s*([A-Za-z_][A-Za-z0-9_]*)\s*\.\s*[A-Za-z_][A-Za-z0-9_]*\s*\(",
                s_ns,
            )
            if recv_m is not None and recv_m.group(1) not in PURE_RUST_IDENT_IGNORED:
                defs.add(recv_m.group(1))
            if defs:
                stmts_info.append((s_nc, s_ns, defs, uses))

    inner_s = live_ns.find("{")
    inner_e = live_ns.rfind("}")
    if inner_s != -1 and inner_e > inner_s:
        _collect_stmts(inner_s + 1, inner_e)
    else:
        _collect_stmts(0, len(live_ns))

    selected_idx: set[int] = set()
    changed = True
    while changed:
        changed = False
        for idx, (_snc, _sns, defs, uses) in enumerate(stmts_info):
            if idx in selected_idx:
                continue
            if defs & live_vars:
                selected_idx.add(idx)
                live_vars.update(uses)
                changed = True

    for idx in sorted(selected_idx):
        s_nc, s_ns, _d, _u = stmts_info[idx]
        selected_chunks.append((s_nc, s_ns))
    return selected_chunks


def _py_load_vars(node: ast.AST) -> set[str]:
    """Return loaded variable and `self.<attr>` names inside Python AST `node`."""
    out: set[str] = set()
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load):
            out.add(sub.id)
        elif (
            isinstance(sub, ast.Attribute)
            and isinstance(sub.ctx, ast.Load)
            and isinstance(sub.value, ast.Name)
            and sub.value.id == "self"
        ):
            out.add(f"self.{sub.attr}")
    return out


def _py_store_vars(target: ast.AST) -> set[str]:
    """Return stored variable and `self.<attr>` names in Python assign target."""
    out: set[str] = set()
    for leaf in _iter_py_assign_targets(target):
        if isinstance(leaf, ast.Name) and leaf.id != "_":
            out.add(leaf.id)
        elif (
            isinstance(leaf, ast.Attribute)
            and isinstance(leaf.value, ast.Name)
            and leaf.value.id == "self"
        ):
            out.add(f"self.{leaf.attr}")
    return out


def _extract_test_witness_bundle(
    view: RepoView, test_ref: str, bug_id: str
) -> _WitnessBundle | None:
    """Extract live witness literals, fixture files, and setup symbols feeding assertions."""
    match = REGRESSION_TEST_RE.fullmatch(test_ref)
    if match is None:
        return None
    rel_path, fn_name = match.group(1), match.group(2)
    text = view.read_text(rel_path)
    if text is None:
        return None

    witness_lits: set[str] = set()
    witness_bytes: set[bytes] = set()
    fixture_files: dict[str, str] = {}
    fixture_syms: set[str] = set()

    if rel_path.endswith(".rs"):
        scanned = scan_rust_tokens(text)
        code_nc = scanned.code_no_comments
        code_ns = scanned.code_no_strings_or_comments
        raw_fn, items, err, _ = _extract_test_assertion_items(view, test_ref)
        if err is not None or raw_fn is None or items is None:
            return None
        fn_scan = scan_rust_tokens(raw_fn)
        fn_body_open = fn_scan.code_no_strings_or_comments.find("{")
        if fn_body_open == -1:
            return None
        live_nc, live_ns = _strip_unreachable_rust_test_code(
            fn_scan.code_no_comments[fn_body_open:],
            fn_scan.code_no_strings_or_comments[fn_body_open:],
        )
        live_nc, live_ns = _prune_unused_rust_local_lets(live_nc, live_ns)
        live_nc, live_ns = _strip_rust_decoy_stmts(live_nc, live_ns)

        # Map file-level const/static and cleaned helper bodies + used params.
        helper_chunks: dict[str, tuple[str, str]] = {}
        helper_used_params: dict[str, set[int]] = {}
        for cm in re.finditer(
            r"(?:^|[;\n{}])\s*(?:pub(?:\([^()]*\))?\s+)?(?:const|static)\s+"
            r"(?:mut\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:[^=;]*=",
            code_ns,
        ):
            cname = cm.group(1)
            semi = code_ns.find(";", cm.end())
            if semi != -1:
                helper_chunks[cname] = (
                    code_nc[cm.end() : semi],
                    code_ns[cm.end() : semi],
                )
        for fm in re.finditer(
            r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(", code_ns
        ):
            hname = fm.group(1)
            if hname == fn_name:
                continue
            rp = _find_matching_delimiter_in_code(code_ns, fm.end() - 1)
            if rp is None:
                continue
            b_open = _find_rust_nested_block_end(code_ns, fm.end())
            if b_open is None:
                continue
            open_brace = code_ns.find("{", rp)
            if open_brace != -1 and open_brace < b_open:
                h_nc = code_nc[open_brace : b_open + 1]
                h_ns = code_ns[open_brace : b_open + 1]
                h_nc, h_ns = _strip_unreachable_rust_test_code(h_nc, h_ns)
                h_nc, h_ns = _prune_unused_rust_local_lets(h_nc, h_ns)
                h_nc, h_ns = _strip_rust_decoy_stmts(h_nc, h_ns)
                helper_chunks[hname] = (h_nc, h_ns)
                # Track non-self param indices referenced in cleaned body.
                raw_params = _split_top_level_commas(
                    code_ns[fm.end() : rp], keep_literal_only=True
                )
                non_self_params = [
                    p
                    for p in raw_params
                    if p.strip()
                    and not re.match(
                        r"^(?:&\s*(?:'[A-Za-z_][A-Za-z0-9_]*\s+)?(?:mut\s+)?|mut\s+)?self\b",
                        p.strip(),
                    )
                ]
                body_idents = _rust_ident_set(h_ns)
                used_idxs: set[int] = set()
                for p_idx, p_decl in enumerate(non_self_params):
                    p_names = _extract_rust_pattern_idents(p_decl)
                    if not p_names:
                        continue
                    if any(
                        not pn.startswith("_") and pn in body_idents
                        for pn in p_names
                    ):
                        used_idxs.add(p_idx)
                helper_used_params[hname] = used_idxs

        raw_selected = _slice_rust_witness_chunks(live_nc, live_ns, items)
        selected_chunks = [
            _blank_unused_rust_helper_call_args(c_nc, c_ns, helper_used_params)
            for c_nc, c_ns in raw_selected
        ]
        regions: list[tuple[str, str]] = list(selected_chunks)
        seen_helpers: set[str] = set()
        queue_ns = [c_ns for _c_nc, c_ns in selected_chunks]
        while queue_ns:
            cur = queue_ns.pop(0)
            for tok in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", cur):
                if tok in helper_chunks and tok not in seen_helpers:
                    seen_helpers.add(tok)
                    h_nc, h_ns = helper_chunks[tok]
                    h_nc, h_ns = _blank_unused_rust_helper_call_args(
                        h_nc, h_ns, helper_used_params
                    )
                    regions.append((h_nc, h_ns))
                    queue_ns.append(h_ns)

        bound_locals: set[str] = set()
        for eq_m in re.finditer(r"\blet\b([^=;]+)=", live_ns):
            bound_locals.update(_extract_rust_pattern_idents(eq_m.group(1)))
        for r_nc, r_ns in regions:
            clean_nc, clean_ns = _blank_rust_assertions_and_panics(r_nc, r_ns)
            reg_scan = scan_rust_tokens(clean_nc)
            for ls, le in reg_scan.literal_spans:
                raw_lit = clean_nc[ls:le]
                raw_b = _decode_rust_byte_literal(raw_lit)
                if raw_b is not None:
                    try:
                        utf8_s = raw_b.decode("utf-8")
                    except UnicodeDecodeError:
                        utf8_s = None
                    if utf8_s is not None:
                        resolved = _resolve_repo_fixture_path(
                            view, rel_path, utf8_s
                        )
                        if resolved is not None:
                            fixture_files[resolved[0]] = resolved[1]
                            continue
                    if _is_witness_candidate_bytes(raw_b, bug_id):
                        witness_bytes.add(raw_b)
                    continue
                decoded = _decode_any_rust_string_literal(raw_lit)
                if decoded is None:
                    continue
                resolved = _resolve_repo_fixture_path(view, rel_path, decoded)
                if resolved is not None:
                    fixture_files[resolved[0]] = resolved[1]
                    continue
                if _is_witness_candidate_literal(decoded, bug_id):
                    witness_lits.add(decoded)

            inner_s = clean_ns.find("{")
            inner_e = clean_ns.rfind("}")
            body_slice = (
                clean_ns[inner_s + 1 : inner_e]
                if inner_s != -1 and inner_e > inner_s
                else clean_ns
            )
            for eq_m in re.finditer(r"\blet\b([^=;]+)=", body_slice):
                bound_locals.update(_extract_rust_pattern_idents(eq_m.group(1)))
            stripped_num = _strip_rust_numeric_literals(body_slice)
            for ident in re.findall(
                r"\b[A-Za-z_][A-Za-z0-9_]*\b", stripped_num
            ):
                if (
                    ident in PURE_RUST_IDENT_IGNORED
                    or ident in GENERIC_WITNESS_SETUP_VERBS
                    or ident in bound_locals
                    or ident == fn_name
                    or ident.startswith("_")
                ):
                    continue
                fixture_syms.add(ident)

        return _WitnessBundle(
            witness_literals=frozenset(witness_lits),
            witness_bytes=frozenset(witness_bytes),
            fixture_files=fixture_files,
            fixture_symbols=frozenset(fixture_syms),
        )

    # Python regression test witness extraction (sliced from observed asserts).
    try:
        tree = ast.parse(text, filename=rel_path)
    except SyntaxError:
        return None
    _raw_py, py_items, py_err = _extract_python_test_assertion_items(
        text, rel_path, fn_name
    )
    if py_err is not None or py_items is None:
        return None
    target_cls: ast.ClassDef | None = None
    target_fn: ast.FunctionDef | None = None
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            for child in node.body:
                if isinstance(child, ast.FunctionDef) and child.name == fn_name:
                    target_cls = node
                    target_fn = child
                    break
    if target_cls is None or target_fn is None:
        return None

    helper_nodes: dict[str, ast.AST] = {}
    for scope_body in (tree.body, target_cls.body):
        for stmt in scope_body:
            if isinstance(stmt, ast.FunctionDef) and stmt is not target_fn:
                helper_nodes[stmt.name] = stmt
            elif isinstance(stmt, ast.Assign):
                for t in stmt.targets:
                    if isinstance(t, ast.Name):
                        helper_nodes[t.id] = stmt.value
            elif isinstance(stmt, ast.AnnAssign) and isinstance(
                stmt.target, ast.Name
            ) and stmt.value is not None:
                helper_nodes[stmt.target.id] = stmt.value

    py_live_vars: set[str] = set()
    py_inline_calls: list[ast.AST] = []
    for it in py_items:
        if not it.is_observed:
            continue
        try:
            a_tree = ast.parse(it.tested_expr, mode="eval")
        except SyntaxError:
            continue
        for v in _py_load_vars(a_tree.body):
            if v.startswith("self."):
                attr = v.split(".", 1)[1]
                if it.py_self_attrs is None or it.py_self_attrs.get(attr) == "observed":
                    py_live_vars.add(v)
            elif it.py_env is None or it.py_env.get(v) == "observed":
                py_live_vars.add(v)
        for sub in ast.walk(a_tree.body):
            if isinstance(sub, ast.Call) and not _is_python_assertion_call(sub):
                if _py_call_is_direct_observation(
                    sub,
                    env=it.py_env or {},
                    const_vals=it.py_const_vals or {},
                    type_env=it.py_type_env or {},
                    py_facts=it.py_facts or _PyFileFacts(),
                ):
                    py_inline_calls.append(sub)

    py_stmts: list[tuple[ast.AST, set[str], set[str]]] = []
    py_bound_locals: set[str] = set()

    def _collect_py_stmts(stmts: list[ast.stmt]) -> None:
        for stmt in stmts:
            if isinstance(
                stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)
            ):
                continue
            if isinstance(stmt, (ast.Return, ast.Raise)):
                break
            if isinstance(stmt, ast.Assert):
                continue
            if (
                isinstance(stmt, ast.Expr)
                and isinstance(stmt.value, ast.Call)
                and _is_python_assertion_call(stmt.value)
            ):
                continue
            if isinstance(stmt, ast.Assign):
                defs: set[str] = set()
                for t in stmt.targets:
                    defs.update(_py_store_vars(t))
                py_bound_locals.update(
                    d for d in defs if not d.startswith("self.")
                )
                if defs:
                    py_stmts.append((stmt.value, defs, _py_load_vars(stmt.value)))
                continue
            if isinstance(stmt, ast.AnnAssign) and stmt.value is not None:
                defs = _py_store_vars(stmt.target)
                py_bound_locals.update(
                    d for d in defs if not d.startswith("self.")
                )
                if defs:
                    py_stmts.append((stmt.value, defs, _py_load_vars(stmt.value)))
                continue
            if isinstance(stmt, ast.AugAssign):
                defs = _py_store_vars(stmt.target)
                if defs:
                    py_stmts.append((stmt.value, defs, _py_load_vars(stmt.value)))
                continue
            if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call):
                if isinstance(stmt.value.func, ast.Attribute):
                    recv_vars = _py_load_vars(stmt.value.func.value)
                    if recv_vars:
                        py_stmts.append(
                            (stmt.value, recv_vars, _py_load_vars(stmt.value))
                        )
                continue
            if isinstance(stmt, (ast.With, ast.AsyncWith)):
                for item in stmt.items:
                    if item.optional_vars is not None:
                        defs = _py_store_vars(item.optional_vars)
                        py_bound_locals.update(
                            d for d in defs if not d.startswith("self.")
                        )
                        if defs:
                            py_stmts.append(
                                (
                                    item.context_expr,
                                    defs,
                                    _py_load_vars(item.context_expr),
                                )
                            )
                _collect_py_stmts(stmt.body)
                continue
            if isinstance(stmt, ast.If):
                _collect_py_stmts(stmt.body)
                _collect_py_stmts(stmt.orelse)
                continue
            if isinstance(stmt, (ast.For, ast.AsyncFor)):
                defs = _py_store_vars(stmt.target)
                py_bound_locals.update(
                    d for d in defs if not d.startswith("self.")
                )
                if defs:
                    py_stmts.append((stmt.iter, defs, _py_load_vars(stmt.iter)))
                _collect_py_stmts(stmt.body)
                _collect_py_stmts(stmt.orelse)
                continue
            if isinstance(stmt, ast.Try):
                _collect_py_stmts(stmt.body)
                for h in stmt.handlers:
                    _collect_py_stmts(h.body)
                _collect_py_stmts(stmt.orelse)
                _collect_py_stmts(stmt.finalbody)

    _collect_py_stmts(target_fn.body)
    py_selected: set[int] = set()
    py_changed = True
    while py_changed:
        py_changed = False
        for idx, (_node, defs, uses) in enumerate(py_stmts):
            if idx in py_selected:
                continue
            if defs & py_live_vars:
                py_selected.add(idx)
                py_live_vars.update(uses)
                py_changed = True

    live_nodes: list[ast.AST] = [
        *py_inline_calls,
        *(py_stmts[idx][0] for idx in sorted(py_selected)),
    ]
    loaded_names = {
        sub.id
        for lnode in live_nodes
        for sub in ast.walk(lnode)
        if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load)
    }

    seen_py_helpers: set[str] = set()
    py_queue = list(loaded_names)
    while py_queue:
        h = py_queue.pop(0)
        if h in helper_nodes and h not in seen_py_helpers:
            seen_py_helpers.add(h)
            hnode = helper_nodes[h]
            live_nodes.append(hnode)
            for sub in ast.walk(hnode):
                if isinstance(sub, ast.Name) and isinstance(sub.ctx, ast.Load):
                    py_queue.append(sub.id)

    for lnode in live_nodes:
        for sub in ast.walk(lnode):
            if isinstance(sub, ast.Call) and _is_python_assertion_call(sub):
                continue
            if isinstance(sub, ast.Constant):
                if isinstance(sub.value, str):
                    resolved = _resolve_repo_fixture_path(
                        view, rel_path, sub.value
                    )
                    if resolved is not None:
                        fixture_files[resolved[0]] = resolved[1]
                    elif _is_witness_candidate_literal(sub.value, bug_id):
                        witness_lits.add(sub.value)
                elif isinstance(sub.value, bytes):
                    raw_b = sub.value
                    try:
                        utf8_s = raw_b.decode("utf-8")
                    except UnicodeDecodeError:
                        utf8_s = None
                    if utf8_s is not None:
                        resolved = _resolve_repo_fixture_path(
                            view, rel_path, utf8_s
                        )
                        if resolved is not None:
                            fixture_files[resolved[0]] = resolved[1]
                            continue
                    if _is_witness_candidate_bytes(raw_b, bug_id):
                        witness_bytes.add(raw_b)
            elif (
                isinstance(sub, ast.Name)
                and isinstance(sub.ctx, ast.Load)
                and sub.id not in py_bound_locals
                and sub.id not in PURE_PY_CALLS
                and sub.id not in GENERIC_WITNESS_SETUP_VERBS
                and sub.id not in ("self", "True", "False", "None", "unittest")
                and not sub.id.startswith("assert")
            ):
                fixture_syms.add(sub.id)

    return _WitnessBundle(
        witness_literals=frozenset(witness_lits),
        witness_bytes=frozenset(witness_bytes),
        fixture_files=fixture_files,
        fixture_symbols=frozenset(fixture_syms),
    )


def _rust_disjuncts_are_complementary(parts: list[str]) -> bool:
    """Return True if two Rust `||` disjuncts are complements (`x` and `!x`)."""
    norms: list[str] = []
    for p in parts:
        norms.append(_norm_rust_expr_for_eq(p))
    norm_set = set(norms)
    for n in norms:
        if n.startswith("!"):
            inner = _norm_rust_expr_for_eq(n[1:])
            if inner in norm_set:
                return True
        eq_p = _split_top_level_rust_op(n, "==")
        if len(eq_p) == 2:
            lhs = _norm_rust_expr_for_eq(eq_p[0][2])
            rhs = _norm_rust_expr_for_eq(eq_p[1][2])
            for other in norms:
                ne_p = _split_top_level_rust_op(other, "!=")
                if len(ne_p) == 2:
                    ol = _norm_rust_expr_for_eq(ne_p[0][2])
                    or_ = _norm_rust_expr_for_eq(ne_p[1][2])
                    if (ol, or_) in ((lhs, rhs), (rhs, lhs)):
                        return True
    return False


def _py_disjuncts_are_complementary(vals: list[ast.expr]) -> bool:
    """Return True if two Python `or` disjuncts are complements (`x` and `not x`)."""
    dumps = {ast.dump(v) for v in vals}
    for v in vals:
        if isinstance(v, ast.UnaryOp) and isinstance(v.op, ast.Not):
            if ast.dump(v.operand) in dumps:
                return True
        if isinstance(v, ast.Compare) and len(v.ops) == 1 and isinstance(v.ops[0], ast.Eq):
            l_d = ast.dump(v.left)
            r_d = ast.dump(v.comparators[0])
            for o in vals:
                if (
                    isinstance(o, ast.Compare)
                    and len(o.ops) == 1
                    and isinstance(o.ops[0], ast.NotEq)
                ):
                    ol_d = ast.dump(o.left)
                    or_d = ast.dump(o.comparators[0])
                    if (ol_d, or_d) in ((l_d, r_d), (r_d, l_d)):
                        return True
    return False


def _rust_expr_is_non_success_metadata_check(expr: str) -> bool:
    """Return True iff `expr` checks capture metadata compatible with failure."""
    s = scan_rust_tokens(expr).code_no_strings_or_comments.strip().rstrip(";").strip()
    while s.startswith("(") and s.endswith(")"):
        if _find_matching_delimiter_in_code(s, 0) != len(s) - 1:
            break
        s = s[1:-1].strip()
    if re.fullmatch(
        r".*\.\s*code\s*\(\s*\)\s*\.\s*(?:is_some|is_none)\s*\(\s*\)", s
    ):
        return True
    if re.fullmatch(
        r".*\.\s*code\s*\(\s*\)\s*!=\s*(?:None|Some\s*\(\s*[1-9][0-9]*\s*\))", s
    ):
        return True
    if re.fullmatch(
        r"(?:None|Some\s*\(\s*[1-9][0-9]*\s*\))\s*!=\s*.*\.\s*code\s*\(\s*\)", s
    ):
        return True
    if re.fullmatch(
        r"(?:(?:::\s*)?(?:core|std)\s*::\s*)?matches\s*!\s*\([^,]*\.\s*code\s*\(\s*\)\s*,\s*Some\s*\(\s*_\s*\)\s*\)",
        s,
    ):
        return True
    parsed_m = _rust_matches_args(s)
    if parsed_m is not None:
        scrut_ns, pat_only_ns, guard_ns = parsed_m
        if not guard_ns or _eval_rust_static_bool_cond(guard_ns) is True:
            if _rust_pat_is_exhaustive(pat_only_ns):
                return True
            if _rust_status_code_some_irrefutable(scrut_ns, pat_only_ns):
                return True
    if re.fullmatch(
        r"!?\s*[A-Za-z_][A-Za-z0-9_.\s&*]*\.\s*(?:stdout|stderr)\s*\.\s*is_empty\s*\(\s*\)",
        s,
    ):
        return True
    if re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_.\s&*]*\.\s*(?:stdout|stderr)\s*\.\s*len\s*\(\s*\)\s*(?:>\s*0|>=\s*1|!=\s*0)",
        s,
    ):
        return True
    return False


def _rust_phase1_conjunction_lacks_success_check(
    expr: str, rust_exprs: dict[str, str] | None = None
) -> bool:
    """Return True if a Rust `assert!` checks only failure-neutral metadata."""
    s = _resolve_rust_status_expr(expr, rust_exprs)
    and_parts = _split_top_level_rust_op(s, "&&")
    if len(and_parts) > 1:
        return all(
            _rust_expr_is_non_success_metadata_check(
                _resolve_rust_status_expr(p[2], rust_exprs)
            )
            for p in and_parts
        )
    return _rust_expr_is_non_success_metadata_check(s)


_RUST_STATUS_META_RE = re.compile(
    r"\.\s*(?:code|success|exit_ok)\s*\(\s*\)"
    r"|\.\s*status\s*\.\s*[A-Za-z_]"
)
_RUST_STATUS_SUBFIELD_RE = re.compile(
    r"\.\s*(?:status|code|success|exit_ok|is_some|is_none|is_ok|is_err)\b"
)
_RUST_OPT_PRED_RE = re.compile(
    r"^(!\s*)?(.+)\.\s*(is_some|is_none|is_ok|is_err)\s*\(\s*\)$"
)


def _strip_rust_outer_parens_ns(expr: str) -> str:
    """Return comment/string-stripped expression with outer parens removed."""
    s = scan_rust_tokens(expr).code_no_strings_or_comments.strip().rstrip(";").strip()
    while s.startswith("(") and s.endswith(")"):
        if _find_matching_delimiter_in_code(s, 0) != len(s) - 1:
            break
        s = s[1:-1].strip()
    return s


def _resolve_rust_status_expr(
    expr: str, rust_exprs: dict[str, str] | None
) -> str:
    """Expand local aliases in `rust_exprs` up to 4 hops while preserving `!`."""
    s = _strip_rust_outer_parens_ns(expr)
    if not rust_exprs:
        return s
    neg = False
    for _ in range(4):
        while s.startswith("!"):
            neg = not neg
            s = _strip_rust_outer_parens_ns(s[1:])
        m_ident = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)(.*)$", s)
        if m_ident is None:
            break
        ident, tail = m_ident.group(1), m_ident.group(2)
        if ident not in rust_exprs or (tail and not tail.lstrip().startswith(".")):
            break
        bound = _strip_rust_outer_parens_ns(rust_exprs[ident])
        if not bound:
            break
        if tail and _RUST_STATUS_SUBFIELD_RE.search(bound) is None:
            break
        s = f"({bound}){tail}" if tail else bound
    while s.startswith("!"):
        neg = not neg
        s = _strip_rust_outer_parens_ns(s[1:])
    return f"!{s}" if neg else s


def _rust_capture_root_ident(expr: str) -> str | None:
    s = _strip_rust_outer_parens_ns(expr)
    m = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\b", s)
    return m.group(1) if m is not None else None


def _split_pure_rust_status_call(expr: str) -> tuple[str, str, bool] | None:
    """Return `(recv, method, neg)` for pure `.success()`/`.code()`/`.exit_ok()`."""
    s = _strip_rust_outer_parens_ns(expr)
    neg = False
    while s.startswith("!"):
        neg = not neg
        s = _strip_rust_outer_parens_ns(s[1:])
    m = re.fullmatch(
        r"(?P<recv>.+?)\.\s*(?P<method>success|code|exit_ok)\s*\(\s*\)", s
    )
    if m is None:
        return None
    recv = _strip_rust_outer_parens_ns(m.group("recv"))
    if not recv or recv.startswith("!"):
        return None
    if re.search(
        r"\.\s*(?:is_some|is_none|is_ok|is_err|code|success|exit_ok)\s*\(\s*\)",
        recv,
    ):
        return None
    for op in ("==", "!=", "&&", "||", ";"):
        if len(_split_top_level_rust_op(recv, op)) > 1:
            return None
    depth = 0
    for ch in recv:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                return None
    if depth != 0:
        return None
    return (recv, m.group("method"), neg)


def _rust_status_operand_authority_family(
    raw_side: str,
    recv_ns: str,
    *,
    rust_exprs_nc: dict[str, str] | None,
    rust_auth_env: dict[str, str] | None,
    rust_facts: _RustFileFacts | None,
    rust_type_env: dict[str, str] | None,
) -> str | None:
    """Resolve the authority family behind a Rust status check operand."""
    root = _rust_capture_root_ident(recv_ns)
    if root is not None and rust_auth_env is not None and root in rust_auth_env:
        return rust_auth_env[root]
    return _rust_expr_authority_family(
        raw_side,
        None,
        rust_auth_env=rust_auth_env,
        rust_facts=rust_facts,
        rust_type_env=rust_type_env,
        rust_exprs_nc=rust_exprs_nc,
    )


def _rust_status_eq_establishes_positive_or_parity(
    lhs: str,
    rhs: str,
    rust_exprs: dict[str, str] | None,
    *,
    rust_exprs_nc: dict[str, str] | None = None,
    rust_auth_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
    rust_type_env: dict[str, str] | None = None,
    keep_permanent_rejection: bool = False,
) -> bool:
    """Allow Phase-1 equalities touching status metadata only on positive/parity."""
    l_res = _resolve_rust_status_expr(lhs, rust_exprs)
    r_res = _resolve_rust_status_expr(rhs, rust_exprs)
    touches_status = bool(
        _RUST_STATUS_META_RE.search(l_res) or _RUST_STATUS_META_RE.search(r_res)
    )
    if not touches_status:
        lm = _RUST_OPT_PRED_RE.fullmatch(l_res)
        rm = _RUST_OPT_PRED_RE.fullmatch(r_res)
        if lm is not None and rm is not None:
            l_neg, l_base, l_fn = bool(lm.group(1)), re.sub(r"\s+", "", lm.group(2)), lm.group(3)
            r_neg, r_base, r_fn = bool(rm.group(1)), re.sub(r"\s+", "", rm.group(2)), rm.group(3)
            comp = {
                ("is_some", "is_none"),
                ("is_none", "is_some"),
                ("is_ok", "is_err"),
                ("is_err", "is_ok"),
            }
            if l_base == r_base and (
                (l_fn == r_fn and l_neg == r_neg)
                or ((l_fn, r_fn) in comp and l_neg != r_neg)
            ):
                return False
        return True

    for side, other in ((l_res, r_res), (r_res, l_res)):
        other_s = re.sub(r"\s+", "", other)
        parsed = _split_pure_rust_status_call(side)
        if parsed is None:
            continue
        _recv, method, neg = parsed
        if other_s == "true" and method == "success" and not neg:
            return True
        if other_s == "false" and method == "success" and neg:
            return True
        if (
            re.fullmatch(r"Some\(0(?:i32|u32|isize|usize)?\)", other_s)
            and method == "code"
            and not neg
        ):
            return True
        if other_s == "Ok(())" and method == "exit_ok" and not neg:
            return True
        if keep_permanent_rejection:
            if other_s == "false" and method == "success" and not neg:
                return True
            if other_s == "true" and method == "success" and neg:
                return True
            if (
                re.fullmatch(
                    r"Some\([1-9][0-9]*(?:i32|u32|isize|usize)?\)", other_s
                )
                and method == "code"
                and not neg
            ):
                return True

    lp = _split_pure_rust_status_call(l_res)
    rp = _split_pure_rust_status_call(r_res)
    if lp is not None and rp is not None:
        l_recv, l_meth, l_neg = lp
        r_recv, r_meth, r_neg = rp
        if l_meth == r_meth and not l_neg and not r_neg:
            l_fam = _rust_status_operand_authority_family(
                lhs,
                l_recv,
                rust_exprs_nc=rust_exprs_nc,
                rust_auth_env=rust_auth_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )
            r_fam = _rust_status_operand_authority_family(
                rhs,
                r_recv,
                rust_exprs_nc=rust_exprs_nc,
                rust_auth_env=rust_auth_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
            )
            return _families_establish_oracle_parity(l_fam, r_fam)
    return False


def _rust_status_ne_establishes_positive(
    lhs: str,
    rhs: str,
    rust_exprs: dict[str, str] | None,
    *,
    keep_permanent_rejection: bool = False,
) -> bool:
    """Allow Phase-1 `!=` on status metadata only when proving `.success()`."""
    l_res = _resolve_rust_status_expr(lhs, rust_exprs)
    r_res = _resolve_rust_status_expr(rhs, rust_exprs)
    if not (_RUST_STATUS_META_RE.search(l_res) or _RUST_STATUS_META_RE.search(r_res)):
        return True
    for side, other in ((l_res, r_res), (r_res, l_res)):
        other_s = re.sub(r"\s+", "", other)
        parsed = _split_pure_rust_status_call(side)
        if parsed is None:
            continue
        _recv, method, neg = parsed
        if other_s == "false" and method == "success" and not neg:
            return True
        if other_s == "true" and method == "success" and neg:
            return True
        if keep_permanent_rejection:
            if (
                re.fullmatch(r"Some\(0(?:i32|u32|isize|usize)?\)", other_s)
                and method == "code"
                and not neg
            ):
                return True
            if other_s == "true" and method in ("success", "exit_ok") and not neg:
                return True
            if other_s == "false" and method in ("success", "exit_ok") and neg:
                return True
    return False


def _rust_clause_eq_ne_positive(
    clause: str,
    rust_exprs: dict[str, str] | None,
    *,
    rust_exprs_nc: dict[str, str] | None = None,
    rust_auth_env: dict[str, str] | None = None,
    rust_facts: _RustFileFacts | None = None,
    rust_type_env: dict[str, str] | None = None,
    keep_permanent_rejection: bool = False,
) -> bool:
    """Validate `==`/`!=` inside a Phase-1 `assert!` clause."""
    and_parts = _split_top_level_rust_op(clause, "&&")
    subclauses = [p[2] for p in and_parts] if len(and_parts) > 1 else [clause]
    for sub in subclauses:
        eq_parts = _split_top_level_rust_op(sub, "==")
        if len(eq_parts) == 2:
            if _norm_rust_expr_for_eq(eq_parts[0][2]) == _norm_rust_expr_for_eq(
                eq_parts[1][2]
            ):
                return False
            if not _rust_status_eq_establishes_positive_or_parity(
                eq_parts[0][2],
                eq_parts[1][2],
                rust_exprs,
                rust_exprs_nc=rust_exprs_nc,
                rust_auth_env=rust_auth_env,
                rust_facts=rust_facts,
                rust_type_env=rust_type_env,
                keep_permanent_rejection=keep_permanent_rejection,
            ):
                return False
        ne_parts = _split_top_level_rust_op(sub, "!=")
        if len(ne_parts) == 2:
            if not _rust_status_ne_establishes_positive(
                ne_parts[0][2],
                ne_parts[1][2],
                rust_exprs,
                keep_permanent_rejection=keep_permanent_rejection,
            ):
                return False
    return True


def _py_is_zero_int_constant(node: ast.expr) -> bool:
    return isinstance(node, ast.Constant) and type(node.value) is int and node.value == 0


def _py_is_plain_returncode_attr(node: ast.expr) -> str | None:
    if (
        isinstance(node, ast.Attribute)
        and node.attr == "returncode"
        and isinstance(node.value, ast.Name)
    ):
        return node.value.id
    return None


def _resolve_py_alias_ast(
    node: ast.expr, py_exprs: dict[str, str] | None, *, _depth: int = 0
) -> ast.expr:
    """Resolve `ast.Name` aliases in `py_exprs` up to 4 hops."""
    if isinstance(node, ast.Name) and _depth < 4 and py_exprs and node.id in py_exprs:
        try:
            parsed = ast.parse(py_exprs[node.id], mode="eval")
        except SyntaxError:
            return node
        return _resolve_py_alias_ast(
            parsed.body, py_exprs, _depth=_depth + 1
        )
    return node


def _py_returncode_recv_node(
    node: ast.expr, py_exprs: dict[str, str] | None = None
) -> ast.expr | None:
    """Return `<recv>` if `node` (or its alias) reads `<recv>.returncode`."""
    res = _resolve_py_alias_ast(node, py_exprs)
    if isinstance(res, ast.Attribute) and res.attr == "returncode":
        return res.value
    return None


def _py_returncode_eq_establishes_positive_or_parity(
    lhs: ast.expr,
    rhs: ast.expr,
    *,
    item: _AssertionItem | None = None,
    keep_permanent_rejection: bool = False,
) -> bool:
    py_exprs = item.py_exprs if item is not None else None
    l_res = _resolve_py_alias_ast(lhs, py_exprs)
    r_res = _resolve_py_alias_ast(rhs, py_exprs)
    if not (
        _py_ast_mentions_returncode(l_res)
        or _py_ast_mentions_returncode(r_res)
    ):
        return True
    for side, other in ((l_res, r_res), (r_res, l_res)):
        if _py_returncode_recv_node(side, py_exprs) is not None:
            val = _py_const_int(other)
            if val == 0 or (
                keep_permanent_rejection and val is not None and val != 0
            ):
                return True
    l_recv = _py_returncode_recv_node(l_res, py_exprs)
    r_recv = _py_returncode_recv_node(r_res, py_exprs)
    if l_recv is not None and r_recv is not None and item is not None:
        l_fam = _py_expr_authority_family(
            l_recv,
            auth_env=item.py_auth_env or {},
            const_vals=item.py_const_vals or {},
            py_facts=item.py_facts or _PyFileFacts(),
            py_exprs=py_exprs,
        )
        r_fam = _py_expr_authority_family(
            r_recv,
            auth_env=item.py_auth_env or {},
            const_vals=item.py_const_vals or {},
            py_facts=item.py_facts or _PyFileFacts(),
            py_exprs=py_exprs,
        )
        return _families_establish_oracle_parity(l_fam, r_fam)
    return False


def _py_returncode_ne_establishes_perm_rejection(
    lhs: ast.expr,
    rhs: ast.expr,
    *,
    item: _AssertionItem | None = None,
) -> bool:
    """Return True iff `lhs != rhs` proves non-zero returncode."""
    py_exprs = item.py_exprs if item is not None else None
    l_res = _resolve_py_alias_ast(lhs, py_exprs)
    r_res = _resolve_py_alias_ast(rhs, py_exprs)
    for side, other in ((l_res, r_res), (r_res, l_res)):
        if (
            _py_returncode_recv_node(side, py_exprs) is not None
            and _py_is_zero_int_constant(other)
        ):
            return True
    return False


def _py_expr_mentions_returncode(
    node: ast.AST, py_exprs: dict[str, str] | None = None
) -> bool:
    """Return True if `node` or any alias in `py_exprs` reads returncode."""
    if _py_ast_mentions_returncode(node):
        return True
    if not py_exprs:
        return False
    if isinstance(node, ast.expr):
        res = _resolve_py_alias_ast(node, py_exprs)
        if res is not node and _py_ast_mentions_returncode(res):
            return True
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and sub.id in py_exprs:
            res = _resolve_py_alias_ast(sub, py_exprs)
            if res is not sub and _py_ast_mentions_returncode(res):
                return True
    return False


def _py_returncode_ord_establishes_perm_rejection(
    lhs: ast.expr,
    op: ast.cmpop,
    rhs: ast.expr,
    *,
    py_exprs: dict[str, str] | None = None,
) -> bool:
    """Return True iff ordering check on `returncode` excludes `0`."""
    l_res = _resolve_py_alias_ast(lhs, py_exprs)
    r_res = _resolve_py_alias_ast(rhs, py_exprs)
    l_rc = _py_returncode_recv_node(l_res, py_exprs) is not None
    r_rc = _py_returncode_recv_node(r_res, py_exprs) is not None
    if l_rc and not r_rc:
        val = _py_const_int(r_res)
        if val is None:
            return False
        if isinstance(op, ast.Gt):
            return val >= 0
        if isinstance(op, ast.GtE):
            return val >= 1
        if isinstance(op, ast.Lt):
            return val <= 0
        if isinstance(op, ast.LtE):
            return val <= -1
        return False
    if r_rc and not l_rc:
        val = _py_const_int(l_res)
        if val is None:
            return False
        if isinstance(op, ast.Lt):
            return val >= 0
        if isinstance(op, ast.LtE):
            return val >= 1
        if isinstance(op, ast.Gt):
            return val <= 0
        if isinstance(op, ast.GtE):
            return val <= -1
        return False
    return False


def _py_compare_returncode_valid(
    cmp_node: ast.Compare,
    *,
    item: _AssertionItem,
    keep_permanent_rejection: bool,
) -> bool:
    """Reject failure-compatible or tautological `returncode` comparisons."""
    py_exprs = item.py_exprs
    operands = [cmp_node.left, *cmp_node.comparators]
    for lhs, op, rhs in zip(operands[:-1], cmp_node.ops, operands[1:]):
        if not (
            _py_expr_mentions_returncode(lhs, py_exprs)
            or _py_expr_mentions_returncode(rhs, py_exprs)
        ):
            continue
        if isinstance(op, (ast.Eq, ast.Is)):
            l_res = _resolve_py_alias_ast(lhs, py_exprs)
            r_res = _resolve_py_alias_ast(rhs, py_exprs)
            if (
                ast.dump(lhs) == ast.dump(rhs)
                or ast.dump(l_res) == ast.dump(r_res)
            ):
                return False
            if not _py_returncode_eq_establishes_positive_or_parity(
                lhs,
                rhs,
                item=item,
                keep_permanent_rejection=keep_permanent_rejection,
            ):
                return False
        elif isinstance(op, (ast.IsNot, ast.NotEq)):
            if not (
                keep_permanent_rejection
                and isinstance(op, ast.NotEq)
                and _py_returncode_ne_establishes_perm_rejection(
                    lhs, rhs, item=item
                )
            ):
                return False
        elif isinstance(op, (ast.Lt, ast.LtE, ast.Gt, ast.GtE)):
            if not (
                keep_permanent_rejection
                and _py_returncode_ord_establishes_perm_rejection(
                    lhs, op, rhs, py_exprs=py_exprs
                )
            ):
                return False
        elif isinstance(op, (ast.In, ast.NotIn)):
            return False
        else:
            return False
    return True


def _py_expr_returncode_valid(
    node: ast.AST,
    *,
    item: _AssertionItem,
    keep_permanent_rejection: bool,
    negated: bool = False,
) -> bool:
    """Validate Python boolean/comparison checks mentioning `returncode`."""
    py_exprs = item.py_exprs
    if not _py_expr_mentions_returncode(node, py_exprs):
        return True
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
        return _py_expr_returncode_valid(
            node.operand,
            item=item,
            keep_permanent_rejection=keep_permanent_rejection,
            negated=not negated,
        )
    if isinstance(node, ast.BoolOp):
        return all(
            _py_expr_returncode_valid(
                v,
                item=item,
                keep_permanent_rejection=keep_permanent_rejection,
                negated=negated,
            )
            for v in node.values
        )
    if isinstance(node, ast.Compare):
        if negated:
            if len(node.ops) != 1:
                return False
            op = node.ops[0]
            lhs, rhs = node.left, node.comparators[0]
            if isinstance(op, (ast.NotEq, ast.IsNot)):
                return _py_returncode_eq_establishes_positive_or_parity(
                    lhs,
                    rhs,
                    item=item,
                    keep_permanent_rejection=keep_permanent_rejection,
                )
            if isinstance(op, (ast.Eq, ast.Is)) and keep_permanent_rejection:
                return _py_returncode_ne_establishes_perm_rejection(
                    lhs, rhs, item=item
                )
            return False
        return _py_compare_returncode_valid(
            node,
            item=item,
            keep_permanent_rejection=keep_permanent_rejection,
        )
    return True


_UNITTEST_COMPARE_OPS: dict[str, ast.cmpop] = {
    "assertEqual": ast.Eq(),
    "assertIs": ast.Is(),
    "assertNotEqual": ast.NotEq(),
    "assertIsNot": ast.IsNot(),
    "assertGreater": ast.Gt(),
    "assertGreaterEqual": ast.GtE(),
    "assertLess": ast.Lt(),
    "assertLessEqual": ast.LtE(),
    "assertIn": ast.In(),
    "assertNotIn": ast.NotIn(),
}


def _phase1_item_is_valid_positive_obs(
    item: _AssertionItem,
    *,
    is_python: bool,
    require_capture: bool,
    keep_permanent_rejection: bool = False,
) -> bool:
    """Return True iff `item` is a non-vacuous observed Phase-1 verification check."""
    if require_capture:
        if item.origin_kind != "obs_capture":
            return False
    elif not item.is_observed:
        return False

    if is_python:
        try:
            tree = ast.parse(item.full_span.strip(), mode="exec")
        except SyntaxError:
            return False
        if len(tree.body) != 1:
            return True
        stmt = tree.body[0]
        if isinstance(stmt, ast.Assert):
            if _eval_python_static_bool(stmt.test, item.py_const_vals) is True:
                return False
            if not _py_expr_all_or_branches_observed(stmt.test, item):
                return False
            if isinstance(stmt.test, ast.BoolOp) and isinstance(
                stmt.test.op, ast.Or
            ):
                if _py_disjuncts_are_complementary(stmt.test.values):
                    return False
            if not _py_expr_returncode_valid(
                stmt.test,
                item=item,
                keep_permanent_rejection=keep_permanent_rejection,
            ):
                return False
            return True
        if (
            isinstance(stmt, ast.Expr)
            and isinstance(stmt.value, ast.Call)
            and isinstance(stmt.value.func, ast.Attribute)
        ):
            attr = stmt.value.func.attr
            args = _bind_unittest_call_args(stmt.value)
            if args is None:
                return False
            if attr in (
                "assertEqual",
                "assertIs",
                "assertSequenceEqual",
                "assertTupleEqual",
                "assertListEqual",
                "assertDictEqual",
                "assertSetEqual",
                "assertCountEqual",
                "assertMultiLineEqual",
            ) and len(args) >= 2:
                if ast.dump(args[0]) == ast.dump(args[1]):
                    return False
                if not _py_returncode_eq_establishes_positive_or_parity(
                    args[0],
                    args[1],
                    item=item,
                    keep_permanent_rejection=keep_permanent_rejection,
                ):
                    return False
            if (
                attr == "assertIsNotNone"
                and args
                and _py_expr_mentions_returncode(args[0], item.py_exprs)
            ):
                return False
            if attr in (
                "assertNotEqual",
                "assertIsNot",
                "assertGreater",
                "assertGreaterEqual",
                "assertLess",
                "assertLessEqual",
                "assertIn",
                "assertNotIn",
            ) and len(args) >= 2:
                synth_cmp = ast.Compare(
                    left=args[0],
                    ops=[_UNITTEST_COMPARE_OPS[attr]],
                    comparators=[args[1]],
                )
                if not _py_compare_returncode_valid(
                    synth_cmp,
                    item=item,
                    keep_permanent_rejection=keep_permanent_rejection,
                ):
                    return False
            if attr == "assertTrue" and args:
                if _eval_python_static_bool(args[0], item.py_const_vals) is True:
                    return False
                if not _py_expr_all_or_branches_observed(args[0], item):
                    return False
                if isinstance(args[0], ast.BoolOp) and isinstance(
                    args[0].op, ast.Or
                ):
                    if _py_disjuncts_are_complementary(args[0].values):
                        return False
                if not _py_expr_returncode_valid(
                    args[0],
                    item=item,
                    keep_permanent_rejection=keep_permanent_rejection,
                ):
                    return False
            if attr == "assertFalse" and args:
                if _eval_python_static_bool(args[0], item.py_const_vals) is False:
                    return False
                if not _py_expr_returncode_valid(
                    args[0],
                    item=item,
                    keep_permanent_rejection=keep_permanent_rejection,
                    negated=True,
                ):
                    return False
        return True

    macro_name, macro_args = _rust_item_macro_and_args(item)
    if macro_name == "assert_ne" and len(macro_args) >= 2:
        lhs, rhs = macro_args[0], macro_args[1]
        for side, other in ((lhs, rhs), (rhs, lhs)):
            if re.search(r"\.\s*code\s*\(\s*\)$", side.strip()) and re.fullmatch(
                r"None|Some\s*\(\s*[1-9][0-9]*\s*\)", other.strip()
            ):
                return False
            if re.search(
                r"\.\s*code\s*\(\s*\)\s*\.\s*is_some\s*\(\s*\)$", side.strip()
            ) and other.strip() == "false":
                return False
        if _norm_rust_expr_for_eq(lhs) == _norm_rust_expr_for_eq(rhs):
            return False
        if not _rust_status_ne_establishes_positive(
            lhs,
            rhs,
            item.rust_exprs,
            keep_permanent_rejection=keep_permanent_rejection,
        ):
            return False
    if macro_name == "assert_matches" and len(macro_args) >= 2:
        pat_ns = scan_rust_tokens(macro_args[1]).code_no_strings_or_comments
        pat_only_ns, g_off = _strip_rust_match_guard(pat_ns)
        guard_ns = pat_ns[g_off:].strip() if g_off is not None else ""
        if not guard_ns or _eval_rust_static_bool_cond(guard_ns) is True:
            if _rust_pat_is_exhaustive(pat_only_ns):
                return False
            if _rust_status_code_some_irrefutable(macro_args[0], pat_only_ns):
                return False
    if macro_name == "assert_eq" and len(macro_args) >= 2:
        lhs, rhs = macro_args[0], macro_args[1]
        for side, other in ((lhs, rhs), (rhs, lhs)):
            s_ns = scan_rust_tokens(side).code_no_strings_or_comments.strip()
            o_ns = scan_rust_tokens(other).code_no_strings_or_comments.strip()
            if (
                re.search(r"\.\s*code\s*\(\s*\)\s*\.\s*is_some\s*\(\s*\)$", s_ns)
                and o_ns == "true"
            ) or (
                re.search(r"\.\s*code\s*\(\s*\)\s*\.\s*is_none\s*\(\s*\)$", s_ns)
                and o_ns == "false"
            ):
                return False
        if not _rust_operand_is_trusted_projection(
            lhs,
            rust_env=item.rust_env,
            type_env=item.rust_type_env,
            facts=item.rust_facts,
        ) or not _rust_operand_is_trusted_projection(
            rhs,
            rust_env=item.rust_env,
            type_env=item.rust_type_env,
            facts=item.rust_facts,
        ):
            return False
        if _norm_rust_expr_for_eq(lhs) == _norm_rust_expr_for_eq(rhs):
            return False
        if not _rust_status_eq_establishes_positive_or_parity(
            lhs,
            rhs,
            item.rust_exprs,
            rust_exprs_nc=item.rust_exprs_nc,
            rust_auth_env=item.rust_auth_env,
            rust_facts=item.rust_facts,
            rust_type_env=item.rust_type_env,
            keep_permanent_rejection=keep_permanent_rejection,
        ):
            return False
        lhs_t = _split_rust_tuple_elems(lhs)
        rhs_t = _split_rust_tuple_elems(rhs)
        if lhs_t is not None and rhs_t is not None and len(lhs_t) == len(rhs_t):
            if all(
                _norm_rust_expr_for_eq(a) == _norm_rust_expr_for_eq(b)
                for a, b in zip(lhs_t, rhs_t)
            ):
                return False
            if not all(
                _rust_status_eq_establishes_positive_or_parity(
                    a,
                    b,
                    item.rust_exprs,
                    rust_exprs_nc=item.rust_exprs_nc,
                    rust_auth_env=item.rust_auth_env,
                    rust_facts=item.rust_facts,
                    rust_type_env=item.rust_type_env,
                    keep_permanent_rejection=keep_permanent_rejection,
                )
                for a, b in zip(lhs_t, rhs_t)
            ):
                return False
        return True
    if macro_name == "assert":
        if not _rust_operand_is_trusted_projection(
            item.tested_expr,
            rust_env=item.rust_env,
            type_env=item.rust_type_env,
            facts=item.rust_facts,
        ):
            return False
        if _rust_expr_has_static_true_disjunct(item.tested_expr):
            return False
        if _rust_clause_is_static_true(item.tested_expr):
            return False
        or_parts = _split_top_level_rust_op(item.tested_expr, "||")
        if len(or_parts) > 1:
            live = [
                p[2] for p in or_parts if not _rust_clause_is_static_false(p[2])
            ]
            if not live or _rust_disjuncts_are_complementary(live):
                return False
            if not all(
                item.subexpr_observed(clause, require_capture=require_capture)
                for clause in live
            ):
                return False
            if any(
                _rust_phase1_conjunction_lacks_success_check(
                    clause, item.rust_exprs
                )
                for clause in live
            ):
                return False
            if not all(
                _rust_clause_eq_ne_positive(
                    clause,
                    item.rust_exprs,
                    rust_exprs_nc=item.rust_exprs_nc,
                    rust_auth_env=item.rust_auth_env,
                    rust_facts=item.rust_facts,
                    rust_type_env=item.rust_type_env,
                    keep_permanent_rejection=keep_permanent_rejection,
                )
                for clause in live
            ):
                return False
        else:
            if _rust_phase1_conjunction_lacks_success_check(
                item.tested_expr, item.rust_exprs
            ):
                return False
            if not _rust_clause_eq_ne_positive(
                item.tested_expr,
                item.rust_exprs,
                rust_exprs_nc=item.rust_exprs_nc,
                rust_auth_env=item.rust_auth_env,
                rust_facts=item.rust_facts,
                rust_type_env=item.rust_type_env,
                keep_permanent_rejection=keep_permanent_rejection,
            ):
                return False
    return True


def _validate_phase1_flipped_items(
    bug_id: str,
    regression_test: str,
    items: list[_AssertionItem],
    *,
    is_python: bool,
    layer: str | None = None,
    cfg: object | None = None,
    fail_on_success: bool = False,
) -> list[str]:
    """Ensure Phase-1 tests flipped off refusal and assert on every live path."""
    errors: list[str] = []
    refusal_token = f"[PHASE0_TRIPWIRE:{bug_id}]"
    joined_full = "\n".join(item.full_span for item in items)
    if refusal_token in joined_full:
        errors.append(
            f"{regression_test}: Phase-1 regression test must flip from "
            f"{refusal_token!r} refusal to positive/UB-parity execution"
        )
    still_unsupported = any(
        _phase1_item_asserts_unsupported(item, is_python=is_python)
        for item in items
    )
    keep_permanent_rejection = layer == "trusted_comment"
    still_refuses_exit = (not keep_permanent_rejection) and (
        fail_on_success
        or any(
            _phase1_item_refuses_exit(item, is_python=is_python)
            for item in items
        )
    )
    if still_unsupported or still_refuses_exit:
        errors.append(
            f"{regression_test}: Phase-1 regression test must flip from "
            "unsupported-fault refusal (or error exit) to positive/UB-parity "
            "execution"
        )
    # Fail closed: require `obs_capture` for Rust tests when layer is
    # `static_capture` or unknown (`None`), and require a non-vacuous positive
    # or UB-parity assertion on EVERY successful test exit path.
    require_capture = layer in ("static_capture", None) and not is_python
    effective_cfg = (
        cfg if cfg is not None else _CfgSeq(tuple(_CfgItem(it) for it in items))
    )
    exit_masks = _eval_cfg_normal_exit_masks(
        effective_cfg,
        lambda it: 1
        if _phase1_item_is_valid_positive_obs(
            it,
            is_python=is_python,
            require_capture=require_capture,
            keep_permanent_rejection=keep_permanent_rejection,
        )
        else 0,
    )
    has_valid_obs_all_paths = bool(exit_masks) and all(
        (m & 1) == 1 for m in exit_masks
    )
    if not has_valid_obs_all_paths:
        errors.append(
            f"{regression_test}: Phase-1 cleanup must retain non-vacuous "
            "positive verification or UB-parity assertions on every "
            "successful test path"
        )
    return errors


def _verify_phase1_witness_preservation(
    repo_root: Path,
    head_view: RepoView,
    bug_id: str,
    regression_test: str,
    *,
    base_view: RepoView | None,
    base_test_ref: str | None,
    known_phase0_sha: str | None = None,
    expected_witness: str | None = None,
    expected_witness_sha256: str | None = None,
) -> list[str]:
    """Verify `head_view` preserves the Phase-0 failing witness input."""
    errors: list[str] = []
    src_view: RepoView | None = base_view if base_test_ref is not None else None
    src_test_ref = base_test_ref
    if src_view is None and known_phase0_sha:
        cand_view = GitRevRepoView(repo_root, known_phase0_sha)
        try:
            cand_entries, _ = collect_repo_tripwires(cand_view)
        except RuntimeError as exc:
            errors.append(
                f"{regression_test}: invalid known_bugs phase0_sha "
                f"{known_phase0_sha!r} for {bug_id}: {exc}"
            )
            return errors
        matched = next(
            (e for e in cand_entries if e.bug_id == bug_id), None
        )
        if matched is None:
            errors.append(
                f"{regression_test}: known_bugs phase0_sha "
                f"{known_phase0_sha!r} does not contain an active "
                f"PHASE0_TRIPWIRE for {bug_id}"
            )
            return errors
        src_view = cand_view
        src_test_ref = matched.regression_test

    has_hash_or_text = bool(expected_witness or expected_witness_sha256)
    if src_view is None and not has_hash_or_text:
        errors.append(
            f"{regression_test}: Phase-1 witness verification for {bug_id} "
            "requires Phase-0 provenance (--base containing the Phase-0 "
            f"tripwire, --witness-sha256 {bug_id}=<sha256>, or known_bugs "
            "phase0_sha/witness_sha256/witness)"
        )
        return errors

    head_bundle = _extract_test_witness_bundle(
        head_view, regression_test, bug_id
    )
    if head_bundle is None:
        errors.append(
            f"{regression_test}: unable to extract Phase-1 witness bundle for "
            f"{bug_id}"
        )
        return errors

    if src_view is not None and src_test_ref is not None:
        base_bundle = _extract_test_witness_bundle(
            src_view, src_test_ref, bug_id
        )
        if base_bundle is None:
            errors.append(
                f"{regression_test}: unable to extract Phase-0 witness bundle "
                f"from {src_test_ref!r} for {bug_id}"
            )
            return errors
        errors.extend(
            _compare_witness_bundles(
                bug_id,
                regression_test,
                base_bundle,
                head_bundle,
                phase_label="Phase-1 cleanup",
            )
        )

    str_candidates = [
        *head_bundle.witness_literals,
        *(head_bundle.fixture_files or {}).values(),
    ]
    byte_candidates = [
        *(c.encode("utf-8") for c in str_candidates),
        *head_bundle.witness_bytes,
    ]
    if expected_witness_sha256:
        norm_hex = expected_witness_sha256.strip().lower()
        if re.fullmatch(r"[0-9a-f]{64}", norm_hex) is None:
            errors.append(
                f"{regression_test}: invalid witness SHA-256 "
                f"{expected_witness_sha256!r} for {bug_id}"
            )
        else:
            digests = {
                hashlib.sha256(b).hexdigest() for b in byte_candidates
            } | {
                hashlib.sha256(b.strip()).hexdigest() for b in byte_candidates
            }
            if norm_hex not in digests:
                errors.append(
                    f"{regression_test}: Phase-1 regression test witness does "
                    f"not match expected witness_sha256 {norm_hex} for {bug_id}"
                )
    if expected_witness:
        exp_b = expected_witness.encode("utf-8")
        if not any(expected_witness in c for c in str_candidates) and not any(
            exp_b in b for b in head_bundle.witness_bytes
        ):
            errors.append(
                f"{regression_test}: Phase-1 regression test must preserve "
                f"expected witness snippet for {bug_id}"
            )
    return errors


def check_phase1_cleanup(
    repo_root: Path,
    *,
    base: str | None = None,
    head: str | None = None,
    resolved_bugs: Iterable[str] = (),
    test_refs: dict[str, str] | None = None,
    witness_hashes: dict[str, str] | None = None,
    known_bugs_path: Path | None = None,
) -> PolicyReport:
    """Enforce complete Phase-1 tripwire deletion and test flip verification."""
    head_rev = head
    tree_rep = check_tree(
        repo_root, rev=head_rev, known_bugs_path=known_bugs_path
    )
    errors = list(tree_rep.errors)
    warnings = list(tree_rep.warnings)

    head_view: RepoView = (
        GitRevRepoView(repo_root, head_rev)
        if head_rev is not None
        else FilesystemRepoView(repo_root)
    )
    try:
        head_entries, _ = collect_repo_tripwires(head_view)
    except RuntimeError as exc:
        if str(exc) not in errors:
            errors.append(str(exc))
        return PolicyReport(
            ok=False,
            mode="phase1-cleanup",
            errors=tuple(errors),
            warnings=tuple(warnings),
            active_production_tripwires=tree_rep.active_production_tripwires,
            synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
        )
    head_ids = {e.bug_id for e in head_entries}

    base_view: RepoView | None = None
    base_info: dict[str, tuple[str | None, str]] = {}
    if base:
        try:
            compare_base = _git_merge_base(repo_root, base, head_rev or "HEAD")
        except RuntimeError:
            compare_base = base
        base_view = GitRevRepoView(repo_root, compare_base)
        try:
            base_entries, _ = collect_repo_tripwires(base_view)
        except RuntimeError as exc:
            errors.append(f"invalid --base revision {base!r}: {exc}")
            return PolicyReport(
                ok=False,
                mode="phase1-cleanup",
                errors=tuple(errors),
                warnings=tuple(warnings),
                active_production_tripwires=tree_rep.active_production_tripwires,
                synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
            )
        for entry in base_entries:
            if not entry.is_synthetic_selftest:
                base_info[entry.bug_id] = (entry.regression_test, entry.layer)

    known_info: dict[str, tuple[str | None, str | None]] = {}
    known_provenance: dict[str, tuple[str | None, str | None, str | None]] = {}
    known_fixed_ids: set[str] = set()
    if known_bugs_path is not None:
        bugs, _ = load_known_bugs(known_bugs_path)
        for row in bugs:
            if row.get("status") == "fixed" and isinstance(row.get("bug_id"), str):
                bid = row["bug_id"]
                known_fixed_ids.add(bid)
                raw_test = row.get("regression_test")
                raw_layer = row.get("layer")
                raw_p0_sha = row.get("phase0_sha")
                raw_wit = row.get("witness")
                raw_wsha = row.get("witness_sha256")
                known_info[bid] = (
                    raw_test if isinstance(raw_test, str) else None,
                    raw_layer
                    if isinstance(raw_layer, str) and raw_layer in VALID_LAYERS
                    else None,
                )
                known_provenance[bid] = (
                    raw_p0_sha.strip()
                    if isinstance(raw_p0_sha, str) and raw_p0_sha.strip()
                    else None,
                    raw_wit if isinstance(raw_wit, str) and raw_wit else None,
                    raw_wsha.strip()
                    if isinstance(raw_wsha, str) and raw_wsha.strip()
                    else None,
                )

    all_target_ids = (
        set(resolved_bugs)
        | {bid for bid in base_info if bid not in head_ids}
        | known_fixed_ids
    )
    resolved_map: dict[str, tuple[str | None, str | None]] = {}
    for bug_id in sorted(all_target_ids):
        base_test, base_layer = base_info.get(bug_id, (None, None))
        known_test, known_layer = known_info.get(bug_id, (None, None))
        override_test = (test_refs or {}).get(bug_id)
        if (
            base_test is not None
            and known_test is not None
            and known_test != base_test
        ):
            errors.append(
                f"Phase-1 verification for {bug_id}: known_bugs regression_test "
                f"{known_test!r} conflicts with --base binding {base_test!r}"
            )
        auth_test = base_test or known_test
        if (
            override_test is not None
            and auth_test is not None
            and override_test != auth_test
        ):
            errors.append(
                f"Phase-1 verification for {bug_id}: --test-ref {override_test!r} "
                f"conflicts with authoritative regression_test binding {auth_test!r}"
            )
        bound_test = auth_test or override_test
        bound_layer = base_layer or known_layer
        resolved_map[bug_id] = (bound_test, bound_layer)

    if not resolved_map:
        errors.append(
            "phase1-cleanup found no resolved/removed bug IDs to verify "
            "(pass --base/--head, --resolved-bug, or --known-bugs)"
        )

    # Scan all trusted Rust/Lean files (production and #[cfg(test)]) at head.
    trusted_full_texts: dict[str, str] = {}
    for rel in head_view.list_files(TRUSTED_DIR_REL, (".rs", ".lean")):
        ok, _ = head_view.is_regular_file(rel)
        if not ok:
            continue
        text = head_view.read_text(rel)
        if text is None:
            continue
        if rel.endswith(".rs"):
            _prod, split_errs = _split_rust_production_section(
                text, rel, allow_multiple_cfg_test=(rel != TRIPWIRES_REL)
            )
            errors.extend(split_errs)
        trusted_full_texts[rel] = text

    for bug_id, (regression_test, layer) in sorted(resolved_map.items()):
        if not BUG_ID_RE.fullmatch(bug_id):
            errors.append(f"invalid resolved bug_id {bug_id!r}")
            continue
        if bug_id in head_ids:
            errors.append(
                f"Phase-1 incomplete for {bug_id}: PHASE0_TRIPWIRE still active"
            )
        for rel, full_text in sorted(trusted_full_texts.items()):
            if bug_id in full_text:
                errors.append(
                    f"Phase-1 incomplete for {bug_id}: residual reference "
                    f"remains in {rel}"
                )

        if regression_test is None:
            errors.append(
                f"Phase-1 verification for {bug_id} requires its regression test "
                "binding (from --base tripwires or --test-ref BUG=path::fn)"
            )
            continue

        fail_on_success_box: list[bool] = []
        _raw_fn, items, test_cfg, test_err, is_python = (
            _extract_test_assertion_items_with_cfg(
                head_view,
                regression_test,
                fail_on_success_out=fail_on_success_box,
            )
        )
        if test_err is not None or items is None:
            errors.append(
                f"Phase-1 cleanup must retain flipped regression test for "
                f"{bug_id}: {test_err}"
            )
            continue

        base_test_ref = base_info[bug_id][0] if bug_id in base_info else None
        k_p0_sha, k_wit, k_wsha = known_provenance.get(
            bug_id, (None, None, None)
        )
        effective_layer = layer
        if effective_layer is None and k_p0_sha:
            try:
                cand_entries, _ = collect_repo_tripwires(
                    GitRevRepoView(repo_root, k_p0_sha)
                )
            except RuntimeError as exc:
                errors.append(
                    f"{regression_test}: invalid known_bugs phase0_sha "
                    f"{k_p0_sha!r} for {bug_id}: {exc}"
                )
                cand_entries = []
            matched_p0 = next(
                (e for e in cand_entries if e.bug_id == bug_id), None
            )
            if matched_p0 is not None:
                effective_layer = matched_p0.layer
        errors.extend(
            _validate_phase1_flipped_items(
                bug_id,
                regression_test,
                items,
                is_python=is_python,
                layer=effective_layer,
                cfg=test_cfg,
                fail_on_success=bool(fail_on_success_box),
            )
        )
        cli_wsha = (witness_hashes or {}).get(bug_id)
        errors.extend(
            _verify_phase1_witness_preservation(
                repo_root,
                head_view,
                bug_id,
                regression_test,
                base_view=base_view,
                base_test_ref=base_test_ref,
                known_phase0_sha=k_p0_sha,
                expected_witness=k_wit,
                expected_witness_sha256=cli_wsha or k_wsha,
            )
        )

    return PolicyReport(
        ok=not errors,
        mode="phase1-cleanup",
        errors=tuple(errors),
        warnings=tuple(warnings),
        active_production_tripwires=tree_rep.active_production_tripwires,
        synthetic_selftest_tripwires=tree_rep.synthetic_selftest_tripwires,
    )


def _find_repo_root(explicit: Path | None) -> Path:
    if explicit is not None:
        return explicit.resolve()
    return Path(__file__).resolve().parents[2]


def _parse_test_refs(raw_refs: list[str]) -> tuple[dict[str, str], list[str]]:
    out: dict[str, str] = {}
    errors: list[str] = []
    for item in raw_refs:
        if "=" not in item:
            errors.append(f"invalid --test-ref {item!r}; expected BUG_ID=path::fn")
            continue
        bug_id, ref = item.split("=", 1)
        out[bug_id.strip()] = ref.strip()
    return out, errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate two-phase soundness tripwires and cleanup rules."
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=None,
        help="Repository root containing anneal/ (defaults to auto-detected root).",
    )
    parser.add_argument(
        "--mode",
        choices=("tree", "phase0-diff", "phase1-cleanup"),
        default="tree",
        help="Validation mode to execute.",
    )
    parser.add_argument("--base", default=None, help="Base Git revision.")
    parser.add_argument("--head", default=None, help="Head Git revision.")
    parser.add_argument(
        "--diff-files",
        nargs="*",
        default=None,
        help="Explicit changed repo-relative paths for phase0-diff mode.",
    )
    parser.add_argument(
        "--allow-runtime-semantics-fallback",
        action="store_true",
        help="Permit annotated Trusted/MirSemantics/*.lean fallback hunks.",
    )
    parser.add_argument(
        "--resolved-bug",
        action="append",
        default=[],
        help="Bug ID resolved in Phase 1 (may repeat).",
    )
    parser.add_argument(
        "--test-ref",
        action="append",
        default=[],
        help="BUG_ID=anneal/tests/...::fn binding for Phase-1 cleanup checks.",
    )
    parser.add_argument(
        "--witness-sha256",
        action="append",
        default=[],
        help="BUG_ID=<64hex> Phase-0 witness SHA-256 for Phase-1 cleanup.",
    )
    parser.add_argument(
        "--known-bugs",
        type=Path,
        default=None,
        help="Optional known-bugs JSON/JSONL file for lifecycle checks.",
    )
    parser.add_argument(
        "--strict-mitigated-link",
        action="store_true",
        help="Fail closed if status='mitigated_phase0' lacks an active tripwire.",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON output.")
    args = parser.parse_args(argv)

    repo_root = _find_repo_root(args.repo_root)
    if args.mode == "tree":
        report = check_tree(
            repo_root,
            rev=args.head,
            known_bugs_path=args.known_bugs,
            strict_mitigated_link=args.strict_mitigated_link,
        )
    elif args.mode == "phase0-diff":
        report = check_phase0_diff(
            repo_root,
            base=args.base,
            head=args.head,
            diff_files=args.diff_files,
            allow_runtime_semantics_fallback=args.allow_runtime_semantics_fallback,
        )
    else:
        test_refs, ref_errs = _parse_test_refs(args.test_ref)
        witness_hashes, wit_errs = _parse_test_refs(args.witness_sha256)
        wit_errs = [
            e.replace("--test-ref", "--witness-sha256").replace(
                "path::fn", "<sha256>"
            )
            for e in wit_errs
        ]
        if ref_errs or wit_errs:
            report = PolicyReport(
                ok=False,
                mode="phase1-cleanup",
                errors=tuple([*ref_errs, *wit_errs]),
                warnings=(),
                active_production_tripwires=(),
                synthetic_selftest_tripwires=(),
            )
        else:
            report = check_phase1_cleanup(
                repo_root,
                base=args.base,
                head=args.head,
                resolved_bugs=args.resolved_bug,
                test_refs=test_refs,
                witness_hashes=witness_hashes,
                known_bugs_path=args.known_bugs,
            )

    if args.json:
        print(json.dumps(report.to_json(), indent=2))
    else:
        status = "OK" if report.ok else "FAILED"
        print(
            f"check_phase0_tripwires ({report.mode}): {status} "
            f"(active={len(report.active_production_tripwires)}, "
            f"selftest={len(report.synthetic_selftest_tripwires)})"
        )
        for warning in report.warnings:
            print(f"warning: {warning}", file=sys.stderr)
        for err in report.errors:
            print(f"error: {err}", file=sys.stderr)
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
