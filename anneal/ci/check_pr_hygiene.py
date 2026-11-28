#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fail fast on mechanical PR-hygiene defects before human or LLM review.

Checks the commits and diff in `merge_base(--base, --head)..--head` plus the
tree at `--head`:

- `commit-message`: subject and 72-column body layout, well-formed
  `Agent-authored-by:` trailers (at most one per user, in the final trailer
  block), and no `gherrit-pr-id` lines or review-round IDs. Only commits
  touching Anneal paths are checked, unless `--skip-commit-messages` (for
  PRs whose authenticated author is a bot) skips them.
- `commit-author` (`--expected-author`): each in-scope commit's author and
  committer.
- `diff-check`: `git diff --check` on Anneal paths.
- `wrap`: added Markdown and comment lines that exceed 80 columns even though
  wrapping could fix them. Inline code spans split across a line wrap are
  reported as warnings.
- `header`: the Fuchsia copyright and license header on new Anneal files.
- `review-round-id`: review-round IDs in added comments and Markdown (code
  may carry them as data, such as Gate 2 finding-ID fixtures).
- `trusted-citation`: unpinned or abbreviated `rust-lang/{rust,reference}`
  citations and rendered-documentation links in `trusted/lean/` and
  `trusted/rustc-capture/`.
- `agents-budget` and `code-review-rules-parity`: the cumulative `AGENTS.md`
  byte budget and the verbatim `Code Review Rules` mirror in
  `.gemini/styleguide.md`.
- `rustc-workaround`: malformed or unresolved (`#PENDING`) upstream `rustc`
  workaround anchors in Anneal source files at `--head` (see
  `docs/rustc-workarounds.md`; `ci/audit_rustc_workarounds.py` prints the
  anchor inventory).
- `pr-body`, `pr-title` (`--pr-body-file`, `--pr-title`): a single-commit PR's
  description and title match its commit message.
- `receipt` (`--receipt-file`): a Review Receipt has a `Human review surface`
  block and one `anneal-receipt:v1` JSON footer that binds the checked
  comparison tuple and tree and lists every changed review-surface path
  (`--emit-receipt-footer` prints it).
- `pr-title-policy` (`--forbid-pr-title-regex`): the PR title, which becomes
  the squash commit subject of a multi-commit PR, does not match a regex
  that the merge queue would reject anyway.
- `skip-pr-hygiene`: waiver trailers are well formed and used.
- `review-size` (advisory): a warning, never a finding, when more than
  `REVIEW_SIZE_BUDGET` changed lines remain after excluding generated, lock,
  vendored, binary, and machine-checked fixture proof files; such changes
  should be split into a linear stack of PRs. `--json` reports the counts
  as `review_size`.

The PR's tip commit may waive every finding of some checks with one or more
single-line trailers in its final trailer block:

    Skip-pr-hygiene: <check>[,<check>...] -- <reason>

Only `commit-message`, `diff-check`, `wrap`, `header`, `review-round-id`,
and `trusted-citation` are waivable; there is no wildcard. The reason needs
at least five non-whitespace characters, every named check must waive at
least one finding, and no other commit in the range may carry the trailer,
because squash merges keep every commit message. Waived findings are
reported as `::warning::` annotations and, when `GITHUB_STEP_SUMMARY` is
set, in a step summary table.

The script only reads Git objects; it never checks out, builds, or executes
candidate content. Reviewers can therefore run a trusted base copy of this
script against an untrusted candidate head. Without `--base`, only the tree
checks run. Exits 0 when no unwaived findings remain, 1 otherwise, and 2 on
usage or Git errors.
"""

from __future__ import annotations

import argparse
import codecs
from dataclasses import dataclass, field
import datetime
import html
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tokenize
from typing import Callable

SCHEMA = "anneal-pr-hygiene/v1"
SUBJECT_LIMIT = 72
BODY_LIMIT = 72
PROSE_LIMIT = 80
AGENTS_BUDGET = 32768
DEFAULT_GLOBAL_AGENTS_BYTES = "1024"

ANNEAL = "anneal/"
# Pinned upstream content keeps its own conventions.
EXCLUDED_PREFIXES = ("anneal/vendor/",)
# Commits touching these paths follow Anneal's commit-message rules.
COMMIT_SCOPE_PREFIXES = (ANNEAL, ".github/workflows/anneal", "zerocopy/proofs/")

CRR_BEGIN = "<!-- code-review-rules:begin -->"
CRR_END = "<!-- code-review-rules:end -->"
CRR_FILES = ("anneal/AGENTS.md", "anneal/.gemini/styleguide.md")

SHA40_RE = re.compile(r"(?<![0-9a-f])[0-9a-f]{40}(?![0-9a-f])")
REVIEW_ROUND_RE = re.compile(r"\bG\d-R\d+\b")
GHERRIT_RE = re.compile(r"^\s*gherrit-pr-id\s*:", re.IGNORECASE)
GITHUB_SQUASH_SUFFIX_RE = re.compile(r" \(#\d+\)$")
AGENT_TRAILER_KEY_RE = re.compile(r"^\s*agent-authored-by\s*:", re.IGNORECASE)
AGENT_TRAILER_RE = re.compile(
    r"^Agent-authored-by: AI agent acting on (\S(?:.*\S)?)'s behalf"
    r"(?: \((content only|commit message only)\))?$"
)
TRAILER_RE = re.compile(r"^[A-Za-z][A-Za-z0-9-]*:[ \t]+\S")
WAIVER_KEY = "Skip-pr-hygiene"
# Any spelling, so a miscased or indented waiver fails instead of being
# ignored.
WAIVER_KEY_RE = re.compile(r"^\s*skip-pr-hygiene\s*:", re.IGNORECASE)
# Checks a waiver may name. Tree invariants, commit identities, PR metadata,
# receipts, and the waiver check itself are never waivable.
WAIVABLE_CHECKS = (
    "commit-message", "diff-check", "wrap", "header", "review-round-id",
    "trusted-citation",
)
WAIVER_MIN_REASON = 5
FENCE_RE = re.compile(r"^([ \t]*)(`{3,}|~{3,})(.*)$")
def _fence(line: str) -> re.Match[str] | None:
    """Match a code fence line; a backtick fence's info has no backticks.

    Without that CommonMark rule, a line starting with an inline span such
    as ```` ```x``` ```` would open a fence that hides the rest of a file.
    """
    m = FENCE_RE.match(line)
    if m and m.group(2)[0] == "`" and "`" in m.group(3):
        return None
    return m


TABLE_DELIM_RE = re.compile(
    r"^\s*\|?\s*:?-{3,}:?\s*(?:\|\s*:?-{3,}:?\s*)+\|?\s*$"
)
URL_SCHEME_RE = re.compile(r"[A-Za-z][A-Za-z0-9+.-]*://")
HEADER_RE = re.compile(
    r"Copyright (\d{4}) The Fuchsia Authors Licensed under a BSD-style license "
    r"<LICENSE-BSD>, Apache License, Version 2\.0 <LICENSE-APACHE or "
    r"https://www\.apache\.org/licenses/LICENSE-2\.0>, or the MIT license "
    r"<LICENSE-MIT or https://opensource\.org/licenses/MIT>, at your option\. "
    r"This file may not be copied, modified, or distributed except according "
    r"to those terms\."
)

# File kinds whose comments (or, for Markdown, prose) follow the 80-column
# rule, and which need the license header when new.
HASH_COMMENT_EXTS = {".py", ".sh", ".toml", ".yml", ".yaml", ".nix"}
SLASH_COMMENT_EXTS = {".rs"}
LEAN_EXTS = {".lean"}
MARKDOWN_EXTS = {".md"}
HEADER_EXTS = (
    HASH_COMMENT_EXTS | SLASH_COMMENT_EXTS | LEAN_EXTS | MARKDOWN_EXTS
)
# Files whose format forbids a leading comment or that are rendered verbatim
# as a package README.
HEADER_EXEMPT_NAMES = {"SKILL.md", "CLAUDE.md"}
HEADER_EXEMPT_PATHS = {"anneal/README.md"}
# The package README keeps one source line per paragraph.
WRAP_EXEMPT_PATHS = {"anneal/README.md"}
LICENSE_LINE_RE = re.compile(
    r"Copyright \d{4} The Fuchsia Authors|<LICENSE-(?:BSD|APACHE|MIT)"
    r"|This file may not be copied, modified, or distributed"
)

TRUSTED_CITATION_PREFIXES = (
    "anneal/trusted/lean/",
    "anneal/trusted/rustc-capture/",
)
UPSTREAM_LINK_RE = re.compile(
    r"github\.com/rust-lang/(rust|reference)/(?:blob|tree|raw|commit|blame)/"
    r"([^/\s)>\]`'\"]+)"
)
UPSTREAM_RAW_RE = re.compile(
    r"raw\.githubusercontent\.com/rust-lang/(rust|reference)/([^/\s)>\]`'\"]+)"
)
RENDERED_DOCS_RE = re.compile(r"\b(doc\.rust-lang\.org|rust-lang\.github\.io)/")
ABBREVIATED_CITE_RE = re.compile(
    r"rust-lang/(?:rust|reference)(?:@|`?\s+(?:at\s+)?(?:commit\s+)?`?)"
    r"([0-9a-f]{7,39})(?![0-9a-zA-Z])"
)

# Human review surface paths (Code Review Rules), relative to `anneal/`.
HRS_ANNEAL_PREFIXES = ("trusted/", "ci/", ".github/", "skills/", "vendor/")
HRS_ANNEAL_FILES = {
    "Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock",
    "META_PRINCIPLES.md", "PRINCIPLES.md", "THREAT_MODEL.md",
    "docs/trust-model.md", "docs/codex-review.md",
    "docs/review-policy-design.md", "docs/rustc-workarounds.md",
    "theory/bundle-manifest.json",
}
# Zerocopy root paths that Anneal audits as part of its boundary, including
# the root `ci/` that holds trusted CI configuration such as
# `ci/checks.toml`.
HRS_ROOT_PREFIXES = (".github/", "skills/", "ci/")
# Editor, agent, toolchain, and build configs anywhere in the repository.
HRS_CONFIG_DIRS = {
    ".agents", ".claude", ".gemini", ".codex", ".cursor", ".vscode",
    ".devcontainer", ".idea", ".zed", ".cargo",
}
HRS_CONFIG_NAMES = {
    "AGENTS.md", "AGENTS.override.md", "CLAUDE.md", "GEMINI.md",
    "lean-toolchain", "lake-manifest.json", ".mcp.json", ".cursorrules",
    ".windsurfrules", ".clinerules", ".envrc", ".gitattributes",
    ".gitmodules",
}
TRUST_TIER_RE = re.compile(r"--\s*anneal-trust-tier:")

# Advisory review-size budget, in changed (added plus deleted) lines. Review
# rounds grow with PR size, and a finding anywhere in a PR blocks all of it,
# so large changes should land as a linear stack of smaller PRs.
REVIEW_SIZE_BUDGET = 800
# Changed lines that reviewers do not read line by line and that the budget
# therefore excludes. These mirror Gate 2's classification: regenerated
# artifacts, lock files, pinned upstream content, and proof modules under
# machine-checked fixture roots. Fixture files are excluded by location
# alone; whether Gate 2 actually reviews one as fixture-light also depends
# on its content.
SIZE_GENERATED_PATHS = frozenset({
    "anneal/trusted/cargo-anneal/src/bundled_resources.rs",
    "anneal/trusted/root-manifest.sha256",
})
SIZE_GENERATED_NAMES = frozenset({"bundled_theory.json"})
SIZE_LOCK_NAMES = frozenset({
    "Cargo.lock", "flake.lock", "lake-manifest.json", "foundation-lock.json",
})
FIXTURE_ROOTS = (
    "anneal/tests/cargo-anneal/tests/fixtures/",
    "anneal/tests/corpora/scalar_specs/",
    "zerocopy/proofs/",
)
FIXTURE_NAME_RE = re.compile(r"^[A-Za-z0-9_]*(?:Proof|Lemmas)\.lean$")
FIXTURE_NEVER_SEGMENT_RE = re.compile(
    r"(?:^|/)(?:[^/]*Spec[^/]*|[^/]*Expected[^/]*|ci|\.github|\.gemini"
    r"|skills|trusted)(?:/|$)"
)
FIXTURE_CORPORA_RE = re.compile(
    r"^anneal/tests/corpora/scalar_specs/[^/]+/Proof\.lean$")
FIXTURE_ZEROCOPY_RE = re.compile(r"^zerocopy/proofs/[^/]+/[^/]+\.lean$")
SIZE_CATEGORIES = ("generated", "lock", "vendor", "fixture", "binary")


class GitError(Exception):
    """A Git command failed; the check cannot complete."""


@dataclass(frozen=True)
class Finding:
    check: str
    message: str
    path: str | None = None
    line: int | None = None

    def render(self) -> str:
        where = ""
        if self.path is not None:
            where = self.path if self.line is None else f"{self.path}:{self.line}"
            where += ": "
        return f"[{self.check}] {where}{self.message}"

    def to_json(self) -> dict[str, object]:
        return {
            "check": self.check,
            "path": self.path,
            "line": self.line,
            "message": self.message,
        }


@dataclass(frozen=True)
class OptOut:
    """One `Skip-pr-hygiene:` trailer on the PR's tip commit."""

    checks: tuple[str, ...]
    reason: str
    commit: str
    line: int

    def to_json(self) -> dict[str, object]:
        return {
            "checks": list(self.checks),
            "reason": self.reason,
            "commit": self.commit,
            "line": self.line,
        }


@dataclass(frozen=True)
class Waived:
    finding: Finding
    reason: str

    def to_json(self) -> dict[str, object]:
        return {**self.finding.to_json(), "reason": self.reason}


@dataclass
class Report:
    findings: list[Finding] = field(default_factory=list)
    warnings: list[Finding] = field(default_factory=list)
    waived: list[Waived] = field(default_factory=list)
    opt_outs: list[OptOut] = field(default_factory=list)


EMPTY_TREE = "4b825dc642cb6eb9a060e54bf8d69288fbee4904"
# Pin every setting that could hide content, change output formats, or run
# code, so neither ambient configuration nor candidate `.gitattributes` can
# weaken a check. Attributes come from the empty tree.
GIT_OPTIONS = (
    "--literal-pathspecs",
    "--no-pager",
    f"--attr-source={EMPTY_TREE}",
    "-c", "core.hooksPath=/dev/null",
    "-c", "core.fsmonitor=false",
    "-c", "core.quotePath=false",
    "-c", "core.attributesFile=/dev/null",
    "-c", "core.whitespace=blank-at-eol,blank-at-eof,space-before-tab",
    "-c", "diff.noprefix=false",
    "-c", "diff.mnemonicPrefix=false",
    "-c", "diff.relative=false",
    "-c", "color.ui=false",
    "-c", "log.showSignature=false",
)


class Git:
    """Read-only access to one repository's objects."""

    def __init__(self, repo: Path):
        self.repo = repo
        self.env = {
            k: v for k, v in os.environ.items() if not k.startswith("GIT_")
        }
        self.env["GIT_CONFIG_NOSYSTEM"] = "1"
        self.env["GIT_CONFIG_GLOBAL"] = os.devnull
        self.env["LC_ALL"] = "C"

    def run(self, *args: str, ok_codes: tuple[int, ...] = (0,),
            stdin: bytes | None = None) -> bytes:
        res = subprocess.run(
            ["git", *GIT_OPTIONS, *args], cwd=self.repo, env=self.env,
            input=stdin, capture_output=True, check=False,
        )
        if res.returncode not in ok_codes:
            stderr = res.stderr.decode("utf-8", "replace").strip()
            raise GitError(f"`git {' '.join(args)}` failed: {stderr}")
        return res.stdout

    def text(self, *args: str, ok_codes: tuple[int, ...] = (0,)) -> str:
        return self.run(*args, ok_codes=ok_codes).decode("utf-8", "replace")

    def toplevel(self) -> Path:
        try:
            return Path(self.text("rev-parse", "--show-toplevel").strip())
        except GitError as e:
            raise GitError(f"not a Git repository: {self.repo}") from e

    def commit(self, ref: str) -> str:
        return self.text("rev-parse", "--verify", "--end-of-options",
                         f"{ref}^{{commit}}").strip()

    def tree(self, commit: str) -> str:
        return self.text("rev-parse", "--verify", f"{commit}^{{tree}}").strip()

    def blob_text(self, commit: str, path: str) -> str | None:
        """Return the file at `commit:path`, or `None` if it is absent."""
        try:
            data = self.run("cat-file", "blob", f"{commit}:{path}")
        except GitError:
            return None
        return data.decode("utf-8", "replace")


# ---------------------------------------------------------------------------
# Line-width analysis shared by commit bodies, Markdown, and comments.


def _code_span_end(text: str, start: int) -> int | None:
    """Return the index just past the code span opening at `start`, if any."""
    run = 0
    while start + run < len(text) and text[start + run] == "`":
        run += 1
    i = start + run
    while i < len(text):
        if text[i] == "`":
            j = i
            while j < len(text) and text[j] == "`":
                j += 1
            if j - i == run:
                return j
            i = j
        else:
            i += 1
    return None


def unmatched_backtick(text: str) -> int | None:
    """Return the length of the first unclosed backtick run in `text`."""
    i = 0
    while i < len(text):
        if text[i] != "`":
            i += 1
            continue
        end = _code_span_end(text, i)
        if end is None:
            run = 0
            while i + run < len(text) and text[i + run] == "`":
                run += 1
            return run
        i = end
    return None


def units(text: str) -> list[tuple[int, int]]:
    """Split `text` into unbreakable units as `(start, end)` index pairs.

    Units are separated by spaces outside inline code spans, so a code span
    (which must not be split across a wrap) is never broken.
    """
    out: list[tuple[int, int]] = []
    i, n = 0, len(text)
    while i < n:
        while i < n and text[i] in " \t":
            i += 1
        if i >= n:
            break
        start = i
        while i < n and text[i] not in " \t":
            if text[i] == "`":
                end = _code_span_end(text, i)
                if end is not None:
                    i = end
                    continue
            i += 1
        out.append((start, i))
    return out


def wrap_violation(line: str, prefix_len: int, limit: int) -> bool:
    """Return whether `line` is too long although wrapping could fix it.

    `prefix_len` is the width of the leading indentation, comment marker, or
    list marker that a continuation line would repeat. A line is exempt when
    the unit crossing the limit starts the line or would not fit on a
    continuation line by itself (for example a long URL or code span).
    """
    line = line.rstrip()
    if len(line) <= limit:
        return False
    body = line[prefix_len:]
    for idx, (start, end) in enumerate(units(body)):
        if prefix_len + end <= limit:
            continue
        if idx == 0:
            return False
        return prefix_len + (end - start) <= limit
    return False


_LIST_MARKER_RE = re.compile(r"^(\s*(?:>\s?)*(?:[-*+]|\d+[.)])\s+)")
_QUOTE_PREFIX_RE = re.compile(r"^(\s*(?:>\s?)+)")


def prose_prefix_len(text: str) -> int:
    """Width of leading whitespace, blockquote markers, and list marker."""
    m = _LIST_MARKER_RE.match(text)
    if m:
        return len(m.group(1))
    m = _QUOTE_PREFIX_RE.match(text)
    if m:
        return len(m.group(1))
    return len(text) - len(text.lstrip(" \t"))


# ---------------------------------------------------------------------------
# Line classification: which lines of a file are prose subject to wrapping.


@dataclass(frozen=True)
class ProseLine:
    """A prose line: `prefix` is the width a continuation line repeats."""

    prefix: int
    text: str
    block: int


def _markdown_prose(lines: list[str]) -> dict[int, ProseLine]:
    out: dict[int, ProseLine] = {}
    skip: set[int] = set()
    n = len(lines)
    i = 0
    if n and lines[0].strip() == "---":
        j = 1
        while j < n and lines[j].strip() != "---":
            j += 1
        skip.update(range(0, min(j + 1, n)))
        i = j + 1
    # Tables: a delimiter row plus contiguous non-blank rows around it.
    for k, line in enumerate(lines):
        if TABLE_DELIM_RE.match(line):
            a = k
            while a > 0 and lines[a - 1].strip():
                a -= 1
            b = k
            while b + 1 < n and lines[b + 1].strip():
                b += 1
            skip.update(range(a, b + 1))
    block = 0
    fence: tuple[str, int] | None = None
    in_list = False
    in_code = False
    prev_blank = True
    while i < n:
        line = lines[i]
        stripped = line.strip()
        if fence is not None:
            m = _fence(line)
            if (m and m.group(2)[0] == fence[0]
                    and len(m.group(2)) >= fence[1] and not m.group(3).strip()):
                fence = None
            i += 1
            continue
        m = _fence(line)
        if m:
            fence = (m.group(2)[0], len(m.group(2)))
            block += 1
            i += 1
            prev_blank = False
            continue
        if not stripped:
            block += 1
            prev_blank = True
            i += 1
            continue
        lead = len(line) - len(line.lstrip(" \t"))
        # An indented code block runs until a non-blank line indented less
        # than four columns.
        in_code = lead >= 4 and (in_code or (prev_blank and not in_list))
        if _LIST_MARKER_RE.match(line):
            in_list = True
        elif prev_blank and lead == 0:
            in_list = False
        indented_code = in_code
        # Headings, tables, HTML, link definitions, and display math cannot
        # be rewrapped without changing their rendering.
        if (i in skip or indented_code
                or stripped.startswith(("#", "|", "<", "$")) or "$$" in line
                or re.match(r"^\s*\[[^\]]+\]:\s*\S", line)):
            block += 1
        else:
            out[i + 1] = ProseLine(prose_prefix_len(line), line, block)
        prev_blank = False
        i += 1
    return out


def _comment_prose(
    lines: list[str], is_comment: list[bool], marker_re: re.Pattern[str]
) -> dict[int, ProseLine]:
    """Prose lines among comment lines, skipping fenced code in doc comments."""
    out: dict[int, ProseLine] = {}
    block = 0
    fence: tuple[str, int] | None = None
    prev_comment = False
    for idx, line in enumerate(lines):
        if not is_comment[idx]:
            fence = None
            if prev_comment:
                block += 1
            prev_comment = False
            continue
        prev_comment = True
        m = marker_re.match(line)
        prefix = m.end() if m else len(line) - len(line.lstrip(" \t"))
        content = line[prefix:]
        fm = _fence(content)
        if fence is not None:
            if fm and fm.group(2)[0] == fence[0] and len(fm.group(2)) >= fence[1]:
                fence = None
            block += 1
            continue
        if fm:
            fence = (fm.group(2)[0], len(fm.group(2)))
            block += 1
            continue
        cs = content.strip()
        if (not cs or cs.startswith(("|", "#", "<"))
                or TABLE_DELIM_RE.match(content)):
            block += 1
            continue
        out[idx + 1] = ProseLine(
            prefix + prose_prefix_len(content), line, block
        )
    return out


_HASH_MARKER_RE = re.compile(r"^\s*#+ ?")
_SLASH_MARKER_RE = re.compile(r"^\s*//[/!]? ?")
_LEAN_MARKER_RE = re.compile(r"^\s*(?:/--?!?|--+)? ?")


def _python_comments(lines: list[str]) -> list[bool]:
    """Mark lines holding only a comment, using Python's own tokenizer."""
    flags = [False] * len(lines)
    source = "".join(ln + "\n" for ln in lines)
    try:
        for tok in tokenize.generate_tokens(io.StringIO(source).readline):
            row, col = tok.start
            if (tok.type == tokenize.COMMENT
                    and not lines[row - 1][:col].strip()
                    and not (row == 1 and tok.string.startswith("#!"))):
                flags[row - 1] = True
    except (tokenize.TokenError, SyntaxError):
        # Unparseable input yields no prose lines rather than guesses.
        return [False] * len(lines)
    return flags


def _hash_comments(lines: list[str], ext: str) -> list[bool]:
    """Mark `#` comment lines, skipping Nix indented strings."""
    if ext == ".py":
        return _python_comments(lines)
    flags: list[bool] = []
    in_string: str | None = None
    for idx, line in enumerate(lines):
        stripped = line.lstrip()
        is_comment = (
            in_string is None
            and stripped.startswith("#")
            and not (idx == 0 and stripped.startswith("#!"))
        )
        flags.append(is_comment)
        if is_comment:
            continue
        if ext == ".nix":
            # `''` delimits indented strings; `'''`, `''$`, and `''\` escape.
            delims = len(re.findall(r"(?<!')''(?![$'\\])", line))
            if delims % 2 == 1:
                in_string = None if in_string else "''"
    return flags


_LEAN_CHAR_RE = re.compile(r"'(?:\\.[0-9a-fA-F]*|[^\\'])'")


def _lean_comments(lines: list[str]) -> list[bool]:
    """Mark lines inside Lean block comments or starting with a comment."""
    flags: list[bool] = []
    depth = 0
    in_string = False
    for line in lines:
        stripped = line.lstrip()
        flags.append(
            depth > 0 or stripped.startswith("--") or stripped.startswith("/-")
        )
        i, n = 0, len(line)
        while i < n:
            two = line[i:i + 2]
            if depth > 0:
                if two == "/-":
                    depth += 1
                    i += 2
                elif two == "-/":
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif in_string:
                if line[i] == "\\":
                    i += 2
                elif line[i] == '"':
                    in_string = False
                    i += 1
                else:
                    i += 1
            elif two == "--":
                break
            elif two == "/-":
                depth += 1
                i += 2
            elif line[i] == '"':
                in_string = True
                i += 1
            elif line[i] == "'" and (m := _LEAN_CHAR_RE.match(line, i)):
                i = m.end()
            else:
                i += 1
        in_string = False
    return flags


_RUST_CHAR_RE = re.compile(r"'(?:\\(?:u\{[0-9a-fA-F]{1,6}\}|x[0-9a-fA-F]{2}|.)|[^\\'])'")
_RUST_RAW_START_RE = re.compile(r"[bc]?r(#*)\"")


def _rust_comments(lines: list[str]) -> list[bool]:
    """Mark Rust lines that start in or with a comment, outside literals.

    `//@` lines are test-harness directives, not prose.
    """
    flags: list[bool] = []
    depth = 0  # nested `/* */` comment depth
    # Closing delimiter of an open string literal, and whether backslash
    # escapes apply (they do not in raw strings, even `r"..."`).
    string: str | None = None
    escapes = False
    for line in lines:
        stripped = line.lstrip()
        flags.append(string is None and (depth > 0 or (
            stripped.startswith("//") and not stripped.startswith("//@"))))
        i, n = 0, len(line)
        while i < n:
            if string is not None:
                if escapes and line[i] == "\\":
                    i += 2
                elif line.startswith(string, i):
                    i += len(string)
                    string = None
                else:
                    i += 1
            elif depth > 0:
                if line.startswith("/*", i):
                    depth += 1
                    i += 2
                elif line.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            elif line.startswith("//", i):
                break
            elif line.startswith("/*", i):
                depth += 1
                i += 2
            elif line[i] == '"':
                string, escapes = '"', True
                i += 1
            elif line[i] == "'" and (m := _RUST_CHAR_RE.match(line, i)):
                i = m.end()
            elif (m := _RUST_RAW_START_RE.match(line, i)) and (
                    i == 0 or not (line[i - 1].isalnum() or line[i - 1] == "_")):
                string, escapes = '"' + m.group(1), False
                i = m.end()
            else:
                i += 1
    return flags


def _markdown_unfenced(lines: list[str]) -> list[bool]:
    """Mark Markdown lines outside fenced code blocks."""
    flags: list[bool] = []
    fence: tuple[str, int] | None = None
    for line in lines:
        m = _fence(line)
        if fence is not None:
            flags.append(False)
            if (m and m.group(2)[0] == fence[0]
                    and len(m.group(2)) >= fence[1] and not m.group(3).strip()):
                fence = None
        elif m:
            flags.append(False)
            fence = (m.group(2)[0], len(m.group(2)))
        else:
            flags.append(True)
    return flags


def text_lines(path: str, content: str) -> set[int]:
    """1-based numbers of comment lines, or unfenced Markdown lines.

    These hold prose that should never cite ephemeral reviews, including
    headings and tables that the wrapping check skips. Code and string
    literals may carry such IDs as data.
    """
    lines = content.split("\n")
    ext = Path(path).suffix
    if ext in MARKDOWN_EXTS:
        flags = _markdown_unfenced(lines)
    elif ext in HASH_COMMENT_EXTS:
        flags = _hash_comments(lines, ext)
    elif ext in SLASH_COMMENT_EXTS:
        flags = _rust_comments(lines)
    elif ext in LEAN_EXTS:
        flags = _lean_comments(lines)
    else:
        return set()
    return {i + 1 for i, f in enumerate(flags) if f}


def prose_lines(path: str, content: str) -> dict[int, ProseLine]:
    """Return the 1-based line numbers of `content` that are wrapped prose."""
    if path in WRAP_EXEMPT_PATHS:
        return {}
    # Git numbers lines by LF only; `str.splitlines` would also split on
    # form feeds and other separators and shift every later line.
    lines = [ln.expandtabs(8) for ln in content.split("\n")]
    ext = Path(path).suffix
    if ext in MARKDOWN_EXTS:
        prose = _markdown_prose(lines)
    elif ext in HASH_COMMENT_EXTS:
        prose = _comment_prose(lines, _hash_comments(lines, ext),
                               _HASH_MARKER_RE)
    elif ext in SLASH_COMMENT_EXTS:
        prose = _comment_prose(lines, _rust_comments(lines), _SLASH_MARKER_RE)
    elif ext in LEAN_EXTS:
        prose = _comment_prose(lines, _lean_comments(lines), _LEAN_MARKER_RE)
    else:
        return {}
    # The license header is verbatim text, whatever its indentation.
    return {
        n: pl for n, pl in prose.items()
        if not LICENSE_LINE_RE.search(pl.text)
    }


def wrap_findings(
    path: str, content: str, added: set[int]
) -> tuple[list[Finding], list[Finding]]:
    """Prose findings and warnings on the added lines of one file.

    Findings cover overlong lines and review-round IDs. Inline code spans
    split across a wrap are warnings only: CommonMark renders them correctly
    and merged Anneal docs use them often, so failing on them would reject
    accepted practice.
    """
    findings: list[Finding] = []
    warnings: list[Finding] = []
    lines = content.split("\n")
    texts = text_lines(path, content)
    for lineno in sorted(added & texts):
        if REVIEW_ROUND_RE.search(lines[lineno - 1]):
            findings.append(Finding(
                "review-round-id",
                "remove the review-round ID; it is meaningless outside the "
                "review that produced it",
                path, lineno,
            ))
    prose = prose_lines(path, content)
    for lineno in sorted(added):
        pl = prose.get(lineno)
        if pl is None:
            continue
        text = pl.text
        if wrap_violation(text, pl.prefix, PROSE_LIMIT):
            findings.append(Finding(
                "wrap",
                f"{len(text.rstrip())} columns; wrap prose at "
                f"{PROSE_LIMIT} columns",
                path, lineno,
            ))
    for lineno, pl in sorted(prose.items()):
        nxt = prose.get(lineno + 1)
        if nxt is None or nxt.block != pl.block:
            continue
        if lineno not in added and lineno + 1 not in added:
            continue
        run = unmatched_backtick(pl.text[pl.prefix:])
        if run is None:
            continue
        closer = unmatched_backtick(nxt.text[nxt.prefix:])
        if closer == run:
            warnings.append(Finding(
                "wrap",
                "inline code span is split across a line wrap; prefer "
                "keeping it on one line",
                path, lineno,
            ))
    return findings, warnings


# ---------------------------------------------------------------------------
# Commit messages and PR descriptions.


def _message_lines(message: str) -> list[str]:
    return [ln.expandtabs(8) for ln in
            message.replace("\r\n", "\n").rstrip("\n").split("\n")]


@dataclass(frozen=True)
class MessageLayout:
    """Where a commit message's final trailer block and code lines are.

    Indices are 0-based into `_message_lines(message)`.
    """

    trailer_start: int
    final_is_trailers: bool
    code_lines: frozenset[int]


def message_layout(lines: list[str]) -> MessageLayout:
    """Locate the final trailer block and the fenced or indented code lines.

    Trailer checks share this so that a commit documenting a trailer's
    syntax in a code block does not trigger them.
    """
    end = len(lines)
    trailer_start = end
    while trailer_start > 1 and lines[trailer_start - 1].strip():
        trailer_start -= 1
    final_is_trailers = trailer_start > 1 and _is_trailer_block(
        lines[trailer_start:end])
    fence: tuple[str, int] | None = None
    prev_blank = True
    code_lines: set[int] = set()
    for idx in range(2, end):
        line = lines[idx]
        m = _fence(line)
        if fence is not None:
            if m and m.group(2)[0] == fence[0] and len(m.group(2)) >= fence[1]:
                fence = None
            code_lines.add(idx)
            prev_blank = False
            continue
        if m:
            fence = (m.group(2)[0], len(m.group(2)))
            code_lines.add(idx)
            prev_blank = False
            continue
        is_code = prev_blank and line.startswith("    ")
        prev_blank = not line.strip() or is_code
        if is_code:
            code_lines.add(idx)
    return MessageLayout(trailer_start, final_is_trailers,
                         frozenset(code_lines))


def commit_message_findings(sha: str, message: str) -> list[Finding]:
    short = sha[:12]
    where = f"commit {short}"
    out: list[Finding] = []

    def add(msg: str, line: int | None = None) -> None:
        out.append(Finding("commit-message", msg, where, line))

    lines = _message_lines(message)
    subject = GITHUB_SQUASH_SUFFIX_RE.sub("", lines[0])
    if not subject.strip():
        add("empty subject line", 1)
    if len(subject) > SUBJECT_LIMIT:
        add(f"subject is {len(subject)} columns (limit {SUBJECT_LIMIT})", 1)
    if subject.rstrip().endswith("."):
        add("subject ends with a period", 1)
    if len(lines) > 1 and lines[1].strip():
        add("separate the subject from the body with one blank line", 2)

    # Trailers in the final paragraph are exempt from wrapping.
    layout = message_layout(lines)
    trailer_start = layout.trailer_start
    final_is_trailers = layout.final_is_trailers
    code_lines = layout.code_lines
    for idx in range(2, len(lines)):
        line = lines[idx]
        lineno = idx + 1
        if GHERRIT_RE.match(line):
            add("remove the `gherrit-pr-id` line", lineno)
        if REVIEW_ROUND_RE.search(line):
            add("remove the review-round ID; commit messages must not "
                "reference ephemeral reviews", lineno)
        if idx in code_lines:
            continue
        is_table = line.lstrip().startswith("|")
        is_trailer = final_is_trailers and idx >= trailer_start
        if is_table or is_trailer:
            continue
        if wrap_violation(line, prose_prefix_len(line), BODY_LIMIT):
            add(f"body line is {len(line.rstrip())} columns; wrap at "
                f"{BODY_LIMIT}", lineno)
    if REVIEW_ROUND_RE.search(lines[0]):
        add("remove the review-round ID from the subject", 1)

    # `authorship-disclosure`: at most one trailer per represented user, in
    # the final trailer block. Examples inside code blocks do not count.
    seen_users: set[str] = set()
    for i, ln in enumerate(lines):
        if i in code_lines or not AGENT_TRAILER_KEY_RE.match(ln):
            continue
        m = AGENT_TRAILER_RE.match(ln)
        if not m:
            add("malformed trailer; use `Agent-authored-by: AI agent acting "
                "on <user>'s behalf` with an optional ` (content only)` or "
                "` (commit message only)` suffix", i + 1)
        elif m.group(1).casefold() in seen_users:
            add(f"use at most one `Agent-authored-by:` trailer for "
                f"{m.group(1)}", i + 1)
        else:
            seen_users.add(m.group(1).casefold())
        if not final_is_trailers or i < trailer_start:
            add("put `Agent-authored-by:` in the final trailer block", i + 1)
    return out


def parse_waivers(
    commits: list[Commit], head: str
) -> tuple[list[OptOut], list[Finding]]:
    """Parse `Skip-pr-hygiene:` trailers across every commit in the range.

    Only the tip commit may waive: a squash merge keeps every commit
    message, so a trailer left on an earlier commit would reach `main`
    without waiving anything. Mentions inside code blocks are ignored, as
    for `Agent-authored-by:`. Problems are `skip-pr-hygiene` findings,
    which no trailer can waive.
    """
    opt_outs: list[OptOut] = []
    errors: list[Finding] = []
    waivable = ", ".join(f"`{c}`" for c in WAIVABLE_CHECKS)
    for c in commits:
        lines = _message_lines(c.message)
        layout = message_layout(lines)
        where = f"commit {c.sha[:12]}"
        for i, ln in enumerate(lines):
            if i in layout.code_lines or not WAIVER_KEY_RE.match(ln):
                continue

            def err(msg: str) -> None:
                errors.append(Finding("skip-pr-hygiene", msg, where, i + 1))

            if c.sha != head:
                err(f"only the PR's tip commit may carry `{WAIVER_KEY}:`; "
                    "remove it here (rebase rather than merging the base "
                    "branch)")
                continue
            if not layout.final_is_trailers or i < layout.trailer_start:
                err(f"put `{WAIVER_KEY}:` in the final trailer block")
                continue
            prefix = f"{WAIVER_KEY}: "
            if not ln.startswith(prefix):
                err(f"spell the trailer exactly `{prefix}<check>[,<check>...]"
                    " -- <reason>`")
                continue
            if i + 1 < len(lines) and lines[i + 1][:1] in (" ", "\t"):
                err(f"keep `{WAIVER_KEY}:` on one line; folded trailers are "
                    "not accepted")
                continue
            names_text, sep, reason = ln[len(prefix):].partition(" -- ")
            if not sep:
                err("separate the checks from the reason with ` -- `")
                continue
            names = [n.strip() for n in names_text.split(",")]
            if any(not n or re.search(r"\s", n) for n in names):
                err("list checks as `<check>[,<check>...]`")
                continue
            bad = [n for n in dict.fromkeys(names) if n not in WAIVABLE_CHECKS]
            if bad:
                err(f"cannot waive {', '.join(f'`{n}`' for n in bad)}; "
                    f"name only {waivable} (there is no wildcard)")
                continue
            if len(re.sub(r"\s", "", reason)) < WAIVER_MIN_REASON:
                err(f"give a reason of at least {WAIVER_MIN_REASON} "
                    "non-whitespace characters")
                continue
            opt_outs.append(OptOut(tuple(dict.fromkeys(names)),
                                   reason.strip(), c.sha, i + 1))
    return opt_outs, errors


def apply_waivers(report: Report, opt_outs: list[OptOut],
                  errors: list[Finding]) -> None:
    """Move waived findings aside and reject waivers that waive nothing."""
    reasons: dict[str, list[str]] = {}
    for o in opt_outs:
        for name in o.checks:
            reasons.setdefault(name, [])
            if o.reason not in reasons[name]:
                reasons[name].append(o.reason)
    kept: list[Finding] = []
    for f in report.findings:
        if f.check in reasons:
            report.waived.append(Waived(f, "; ".join(reasons[f.check])))
        else:
            kept.append(f)
    used = {w.finding.check for w in report.waived}
    unused: list[Finding] = []
    for o in opt_outs:
        for name in o.checks:
            if name not in used:
                unused.append(Finding(
                    "skip-pr-hygiene",
                    f"`{name}` has no findings to waive; remove it from the "
                    "trailer",
                    f"commit {o.commit[:12]}", o.line,
                ))
    report.findings = kept + errors + unused
    report.opt_outs = list(opt_outs)


def pr_title_policy_findings(pattern: re.Pattern[str],
                             title: str) -> list[Finding]:
    """Reject a PR title that the merge queue's message policy would reject.

    A multi-commit PR's title becomes its squash commit subject, so this
    fails on the PR instead of later in the merge queue.
    """
    m = pattern.search(title)
    if m is None:
        return []
    return [Finding(
        "pr-title-policy",
        f"PR title {title.strip()!r} matches the forbidden pattern "
        f"`{pattern.pattern}` at {m.group(0)!r}",
    )]


ISSUE_LINE_RE = re.compile(
    r"^(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?|part of|makes progress on|"
    r"refs?|see)\s+(?:[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+)?#\d+\b",
    re.IGNORECASE,
)
_LIST_RE = re.compile(r"^([ \t]*)(?:[-*+]|\d+[.)])[ \t]+(.*)$")
_HEADING_RE = re.compile(r"^[ \t]*#{1,6}(?:[ \t]|$)")
_HR_RE = re.compile(
    r"^[ \t]*(?:(?:-[ \t]*){3,}|(?:\*[ \t]*){3,}|(?:_[ \t]*){3,})$"
)
_SETEXT_RE = re.compile(r"^[ \t]*(?:=+|-+)[ \t]*$")
_TABLE_RE = re.compile(r"^[ \t]*\|.*\|[ \t]*$")
_LINK_DEF_RE = re.compile(r"^[ \t]*\[[^\]\n]+\]:[ \t]*\S")
_HTML_COMMENT_RE = re.compile(r"^[ \t]*<!--")
_BQ_RE = re.compile(r"^([ \t]*>[ \t]?)(.*)$")


def _is_trailer_block(block: list[str]) -> bool:
    if not block:
        return False
    saw_header = False
    for line in block:
        if TRAILER_RE.match(line) or ISSUE_LINE_RE.match(line):
            saw_header = True
        elif saw_header and line.startswith((" ", "\t")):
            continue
        else:
            return False
    return saw_header


def _is_block_starter(line: str) -> bool:
    return bool(
        _fence(line) or _LIST_RE.match(line) or _HEADING_RE.match(line)
        or _HR_RE.match(line) or _TABLE_RE.match(line)
        or _LINK_DEF_RE.match(line) or _HTML_COMMENT_RE.match(line)
        or ISSUE_LINE_RE.match(line)
    )


def _join(out: list[str], lines: list[str], i: int, end: int,
          stop: Callable[[int], bool]) -> int:
    """Join soft-wrapped lines from `i`, honoring Markdown hard breaks."""
    acc = lines[i]
    i += 1
    while i < end and not stop(i):
        if acc.endswith("  ") or acc.endswith("\\"):
            out.append(acc)
            acc = lines[i]
        else:
            acc = f"{acc.rstrip()} {lines[i].strip()}"
        i += 1
    out.append(acc.rstrip())
    return i


def commit_body_to_pr_body(body: str, prose_disclosure: bool = True) -> str:
    """Unwrap a 72-column commit body into a GitHub PR description.

    Joins soft-wrapped prose in paragraphs, list items, and blockquotes;
    preserves blank lines, code blocks, headings, thematic breaks, tables,
    link definitions, HTML comments, hard breaks, issue-reference lines, and
    the final trailer block; and, with `prose_disclosure`, converts the
    `Agent-authored-by:` trailer into the prose notice that the
    `authorship-disclosure` skill requires in PR descriptions.
    """
    lines = body.replace("\r\n", "\n").splitlines()
    out: list[str] = []
    i, end = 0, len(lines)
    while end > 0 and not lines[end - 1].strip():
        end -= 1
    if end == 0:
        return ""
    trailer_start = end
    while trailer_start > 0 and lines[trailer_start - 1].strip():
        trailer_start -= 1
    final_is_trailers = _is_trailer_block(lines[trailer_start:end])
    list_indent: int | None = None

    while i < end:
        line = lines[i]
        if final_is_trailers and i == trailer_start:
            notices: list[str] = []
            kept: list[str] = []
            for tl in lines[trailer_start:end]:
                m = AGENT_TRAILER_RE.match(tl) if prose_disclosure else None
                if m:
                    if m.group(2) != "content only":
                        notices.append(
                            f"*Authored by an AI agent acting on "
                            f"{m.group(1)}'s behalf.*"
                        )
                else:
                    kept.append(tl)
            out.extend(kept)
            if notices:
                if kept:
                    out.append("")
                out.extend(notices)
            break
        if not line.strip():
            out.append("")
            i += 1
            continue
        m_fence = _fence(line)
        if m_fence:
            fc, fl = m_fence.group(2)[0], len(m_fence.group(2))
            close_re = re.compile(rf"^[ \t]*{re.escape(fc)}{{{fl},}}[ \t]*$")
            out.append(line)
            i += 1
            while i < end:
                out.append(lines[i])
                if close_re.match(lines[i]):
                    i += 1
                    break
                i += 1
            continue
        if ((not out or out[-1] == "") and list_indent is None
                and line.startswith(("    ", "\t"))):
            limit = trailer_start if final_is_trailers else end
            while i < limit and (lines[i].startswith(("    ", "\t"))
                                 or not lines[i].strip()):
                out.append(lines[i])
                i += 1
            continue
        if (_HEADING_RE.match(line) or _HR_RE.match(line)
                or _TABLE_RE.match(line) or _LINK_DEF_RE.match(line)
                or _HTML_COMMENT_RE.match(line) or ISSUE_LINE_RE.match(line)):
            list_indent = None
            out.append(line)
            i += 1
            continue
        m_bq = _BQ_RE.match(line)
        if m_bq and (list_indent is None
                     or len(line) - len(line.lstrip(" ")) < list_indent):
            list_indent = None
            bq: list[str] = []
            while i < end and _BQ_RE.match(lines[i]):
                bq.append(_BQ_RE.match(lines[i]).group(2))
                i += 1
            inner = commit_body_to_pr_body("\n".join(bq), False)
            for il in inner.splitlines():
                out.append(f"> {il}" if il else ">")
            continue

        def stop_item(j: int) -> bool:
            return not lines[j].strip() or _is_block_starter(lines[j])

        m_list = _LIST_RE.match(line)
        if m_list:
            list_indent = len(line) - len(m_list.group(2))
            i = _join(out, lines, i, end, stop_item)
            continue
        lead = len(line) - len(line.lstrip(" "))
        if list_indent is not None and lead >= list_indent:
            i = _join(out, lines, i, end, stop_item)
            continue
        list_indent = None
        if i + 1 < end and _SETEXT_RE.match(lines[i + 1]):
            out.extend([line, lines[i + 1]])
            i += 2
            continue

        def stop_para(j: int) -> bool:
            nxt = lines[j]
            return (not nxt.strip() or _is_block_starter(nxt)
                    or bool(_BQ_RE.match(nxt))
                    or (j + 1 < end and bool(_SETEXT_RE.match(lines[j + 1]))))

        i = _join(out, lines, i, end, stop_para)
    return "\n".join(out).strip() + "\n"


def _normalize_body(text: str) -> list[str]:
    lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    lines = [ln.rstrip() for ln in lines]
    while lines and not lines[-1]:
        lines.pop()
    while lines and not lines[0]:
        lines.pop(0)
    return lines


def pr_body_findings(expected: str, actual: str) -> list[Finding]:
    exp, act = _normalize_body(expected), _normalize_body(actual)
    if exp == act:
        return []
    for idx in range(max(len(exp), len(act))):
        e = exp[idx] if idx < len(exp) else "<end of body>"
        a = act[idx] if idx < len(act) else "<end of body>"
        if e != a:
            return [Finding(
                "pr-body",
                "PR description differs from the unwrapped commit body "
                f"(regenerate it with --emit-pr-body); first difference at "
                f"line {idx + 1}: expected {e!r}, found {a!r}",
            )]
    return []


# ---------------------------------------------------------------------------
# Diff parsing.


@dataclass
class ChangedFile:
    path: str
    status: str
    old_path: str | None = None
    added: set[int] = field(default_factory=set)
    added_text: dict[int, str] = field(default_factory=dict)
    # Whether an added or removed line holds an `-- anneal-trust-tier:`.
    trust_tier_changed: bool = False


def in_anneal_scope(path: str) -> bool:
    return (path.startswith(COMMIT_SCOPE_PREFIXES)
            and not path.startswith(EXCLUDED_PREFIXES))


def _patch_path(token: str, prefix: str = "b/") -> str | None:
    """Decode a `---`/`+++` path from a patch header (`None` for /dev/null).

    Git C-quotes paths with special characters and appends a tab to paths
    containing spaces.
    """
    if token.endswith("\t"):
        token = token[:-1]
    if token.startswith('"') and token.endswith('"') and len(token) >= 2:
        try:
            raw, _ = codecs.escape_decode(
                token[1:-1].encode("utf-8", "surrogateescape"))
        except ValueError as e:
            raise GitError(f"cannot decode patch path {token!r}") from e
        token = raw.decode("utf-8", "surrogateescape")
    if token == "/dev/null":
        return None
    if not token.startswith(prefix):
        raise GitError(f"unexpected patch path {token!r}")
    return token[len(prefix):]


_HUNK_RE = re.compile(r"^@@ -\d+(?:,(\d+))? \+(\d+)(?:,(\d+))? @@")


def changed_files(git: Git, base: str, head: str) -> dict[str, ChangedFile]:
    files: dict[str, ChangedFile] = {}
    raw = git.run("diff", "--no-ext-diff", "--no-textconv", "-M",
                  "--name-status", "-z", base, head, "--")
    parts = raw.decode("utf-8", "surrogateescape").split("\0")
    i = 0
    while i < len(parts) and parts[i]:
        status = parts[i]
        if status[0] in "RC":
            old, path = parts[i + 1], parts[i + 2]
            i += 3
        else:
            old, path = None, parts[i + 1]
            i += 2
        files[path] = ChangedFile(
            path, status[0], old_path=old if status[0] == "R" else None)
    # `--text` keeps binary or `-diff` content visible. Hunk line counts
    # delimit hunks, so added lines that look like headers stay content.
    patch = git.run("diff", "--no-ext-diff", "--no-textconv", "--text", "-M",
                    "-U0", "--no-color", base, head, "--")
    current: ChangedFile | None = None
    # Owner of removed lines: `current`, or the deleted file itself.
    removed_owner: ChangedFile | None = None
    old_left = new_left = 0
    new_line = 0
    for line in patch.decode("utf-8", "surrogateescape").split("\n"):
        if old_left > 0 or new_left > 0:
            tag = line[:1]
            if tag == "+":
                if current is not None:
                    current.added.add(new_line)
                    current.added_text[new_line] = line[1:]
                    if TRUST_TIER_RE.search(line[1:]):
                        current.trust_tier_changed = True
                new_line += 1
                new_left -= 1
            elif tag == "-":
                if (removed_owner is not None
                        and TRUST_TIER_RE.search(line[1:])):
                    removed_owner.trust_tier_changed = True
                old_left -= 1
            elif tag == " ":
                new_line += 1
                old_left -= 1
                new_left -= 1
            elif tag != "\\":
                raise GitError(f"malformed patch line {line[:80]!r}")
            continue
        if line.startswith("diff --git "):
            current = removed_owner = None
        elif line.startswith("--- "):
            old = _patch_path(line[4:], "a/")
            # A deletion is listed under its old path.
            removed_owner = files.get(old) if old is not None else None
        elif line.startswith("+++ "):
            path = _patch_path(line[4:])
            current = files.get(path) if path is not None else None
            if path is not None and current is None:
                raise GitError(f"patch names unlisted path {path!r}")
            if current is not None:
                removed_owner = current
        elif line.startswith("@@"):
            m = _HUNK_RE.match(line)
            if not m:
                raise GitError(f"malformed hunk header {line[:80]!r}")
            old_left = int(m.group(1) or "1")
            new_line = int(m.group(2))
            new_left = int(m.group(3) or "1")
    return files


def size_exclusion(path: str) -> str | None:
    """Return the review-size category that excludes `path`, if any."""
    name = Path(path).name
    if path in SIZE_GENERATED_PATHS or name in SIZE_GENERATED_NAMES:
        return "generated"
    if name in SIZE_LOCK_NAMES:
        return "lock"
    if path.startswith(EXCLUDED_PREFIXES):
        return "vendor"
    if (path.startswith(FIXTURE_ROOTS)
            and ".." not in Path(path).parts and "\\" not in path
            and not FIXTURE_NEVER_SEGMENT_RE.search(path)
            and FIXTURE_NAME_RE.fullmatch(name)
            and (not path.startswith("anneal/tests/corpora/")
                 or FIXTURE_CORPORA_RE.fullmatch(path))
            and (not path.startswith("zerocopy/proofs/")
                 or FIXTURE_ZEROCOPY_RE.fullmatch(path))):
        return "fixture"
    return None


@dataclass(frozen=True)
class ReviewSize:
    """Changed lines in a diff, split into reviewable and excluded lines."""

    reviewable_lines: int
    reviewable_files: int
    # Category -> (lines, files); binary files count files only.
    excluded: dict[str, tuple[int, int]]
    budget: int = REVIEW_SIZE_BUDGET

    @property
    def over_budget(self) -> bool:
        return self.reviewable_lines > self.budget

    def to_json(self) -> dict[str, object]:
        return {
            "budget": self.budget,
            "reviewable_lines": self.reviewable_lines,
            "reviewable_files": self.reviewable_files,
            "excluded": {k: {"lines": v[0], "files": v[1]}
                         for k, v in self.excluded.items()},
            "over_budget": self.over_budget,
        }


def review_size(numstat: list[tuple[str, int | None]],
                budget: int = REVIEW_SIZE_BUDGET) -> ReviewSize:
    """Classify `(path, changed lines or None if binary)` pairs."""
    lines = files = 0
    excluded = {k: (0, 0) for k in SIZE_CATEGORIES}
    for path, changed in numstat:
        category = "binary" if changed is None else size_exclusion(path)
        if category is None:
            lines += changed or 0
            files += 1
        else:
            n, m = excluded[category]
            excluded[category] = (n + (changed or 0), m + 1)
    return ReviewSize(lines, files, excluded, budget)


def diff_numstat(git: Git, base: str, head: str
                 ) -> list[tuple[str, int | None]]:
    """Return `(path, added + deleted lines)` per changed file.

    Binary files report `None`. Renames are detected as in `changed_files`
    and are listed under their new path.
    """
    raw = git.run("diff", "--no-ext-diff", "--no-textconv", "-M",
                  "--numstat", "-z", base, head, "--")
    if not raw:
        return []
    # Every record ends in a NUL, so anything else is truncated output.
    if not raw.endswith(b"\0"):
        raise GitError("truncated numstat output")
    parts = raw[:-1].decode("utf-8", "surrogateescape").split("\0")
    out: list[tuple[str, int | None]] = []
    i = 0
    while i < len(parts):
        fields = parts[i].split("\t", 2)
        if len(fields) != 3:
            raise GitError(f"malformed numstat entry {parts[i][:80]!r}")
        added, deleted, path = fields
        if path:
            i += 1
        else:
            # A rename or copy: the old and new paths follow.
            if (i + 2 >= len(parts) or not parts[i + 1]
                    or not parts[i + 2]):
                raise GitError("truncated numstat rename entry")
            path = parts[i + 2]
            i += 3
        if added == "-" and deleted == "-":
            out.append((path, None))
        elif all(n.isascii() and n.isdecimal() for n in (added, deleted)):
            out.append((path, int(added) + int(deleted)))
        else:
            raise GitError(f"malformed numstat counts for {path!r}")
    return out


def review_size_warning(size: ReviewSize) -> Finding | None:
    """An advisory warning when reviewable lines exceed the budget."""
    if not size.over_budget:
        return None
    parts = [f"{m} binary file(s)" if k == "binary"
             else f"{n} {k} line(s) in {m} file(s)"
             for k, (n, m) in size.excluded.items() if m]
    excluded = ", ".join(parts) if parts else "none"
    return Finding(
        "review-size",
        f"{size.reviewable_lines} reviewable changed lines in "
        f"{size.reviewable_files} file(s) exceed the {size.budget}-line "
        f"review budget (excluded: {excluded}); consider splitting this "
        "change into a linear stack of PRs (`gh stack link --base main "
        "<pr>...`). This is advisory and does not fail the check.",
    )


# ---------------------------------------------------------------------------
# Per-check logic over the diff and tree.


def _leading_comment(path: str, lines: list[str]) -> list[str]:
    """Return the file's leading comment block, after any shebang."""
    ext = Path(path).suffix
    shebang = ext in HASH_COMMENT_EXTS and lines and lines[0].startswith("#!")
    i = 1 if shebang else 0
    while i < len(lines) and not lines[i].strip():
        i += 1
    block: list[str] = []
    if ext in MARKDOWN_EXTS:
        if i < len(lines) and lines[i].lstrip().startswith("<!--"):
            for ln in lines[i:]:
                if "-->" in ln:
                    block.append(ln.split("-->", 1)[0])
                    return block
                block.append(ln)
        # Missing or unclosed: no leading comment.
        return []
    markers = {
        **{e: ("#",) for e in HASH_COMMENT_EXTS},
        **{e: ("//",) for e in SLASH_COMMENT_EXTS},
        **{e: ("--",) for e in LEAN_EXTS},
    }.get(ext, ())
    for ln in lines[i:]:
        if not ln.lstrip().startswith(markers):
            break
        block.append(ln)
    return block


def header_findings(path: str, content: str, max_year: int) -> list[Finding]:
    """Check that a new file opens with the license header as a comment."""
    cleaned = []
    for ln in _leading_comment(path, content.split("\n")):
        ln = re.sub(r"^\s*(?:<!--|//[/!]?|#+|--)", "", ln)
        cleaned.append(ln.replace("-->", "").strip())
    joined = re.sub(r"\s+", " ", " ".join(c for c in cleaned if c))
    m = HEADER_RE.search(joined)
    if not m:
        return [Finding(
            "header",
            "new file does not open with the Fuchsia copyright and license "
            "header comment (see `PRINCIPLES.md`)",
            path, 1,
        )]
    year = int(m.group(1))
    if not 2019 <= year <= max_year:
        return [Finding(
            "header", f"copyright year {year} is not a plausible creation "
            f"year (expected 2019..{max_year})", path, 1,
        )]
    return []


def needs_header(path: str) -> bool:
    name = Path(path).name
    return (
        Path(path).suffix in HEADER_EXTS
        and name not in HEADER_EXEMPT_NAMES
        and path not in HEADER_EXEMPT_PATHS
    )


def trusted_citation_findings(
    path: str, content: str, added_text: dict[int, str]
) -> list[Finding]:
    full_shas = set(SHA40_RE.findall(content))
    out: list[Finding] = []
    for lineno, text in sorted(added_text.items()):
        for rx in (UPSTREAM_LINK_RE, UPSTREAM_RAW_RE):
            for m in rx.finditer(text):
                ref = re.split(r"[#?]", m.group(2))[0].rstrip(".,;:")
                if not re.fullmatch(r"[0-9a-f]{40}", ref):
                    out.append(Finding(
                        "trusted-citation",
                        f"`rust-lang/{m.group(1)}` link pins `{ref}`; "
                        "cite a full 40-hex commit SHA",
                        path, lineno,
                    ))
        for m in RENDERED_DOCS_RE.finditer(text):
            out.append(Finding(
                "trusted-citation",
                f"`{m.group(1)}` serves unpinned rendered docs; quote and "
                "cite `rust-lang/rust` or `rust-lang/reference` at a pinned "
                "commit SHA",
                path, lineno,
            ))
        for m in ABBREVIATED_CITE_RE.finditer(text):
            prefix = m.group(1)
            if not any(sha.startswith(prefix) for sha in full_shas):
                out.append(Finding(
                    "trusted-citation",
                    f"abbreviated upstream SHA `{prefix}` does not resolve "
                    "to a full 40-hex SHA cited in this file",
                    path, lineno,
                ))
    return out


def is_hrs_path(path: str, trust_tier_changed: bool = False) -> bool:
    """Whether `path` is on the Human review surface.

    `trust_tier_changed` says the diff adds or removes an
    `-- anneal-trust-tier:` directive in the file.
    """
    parts = path.split("/")
    name = parts[-1]
    if (any(p in HRS_CONFIG_DIRS for p in parts)
            or name in HRS_CONFIG_NAMES or name.startswith("lakefile")
            or name.startswith("rust-toolchain")
            or (name.endswith(".lean") and trust_tier_changed)):
        return True
    # Proof-unit specifications and requests, which choose the roots,
    # sources, and specification (including the inline specifications a
    # generated one is lowered from); only `Proof.lean` is kernel-checked.
    if path.startswith("zerocopy/proofs/") and (
            name in ("request.json", "spec_sources.json")
            or (name.endswith(".lean")
                and not (name == "Proof.lean" and len(parts) == 4))):
        return True
    if path.startswith(ANNEAL):
        rel = path[len(ANNEAL):]
        return rel.startswith(HRS_ANNEAL_PREFIXES) or rel in HRS_ANNEAL_FILES
    return path.startswith(HRS_ROOT_PREFIXES)


RECEIPT_FOOTER_RE = re.compile(
    r"<!--\s*anneal-receipt:v1\s+(.*?)\s*-->", re.DOTALL)
# Any footer-like marker, so malformed or other-version footers are counted
# rather than ignored.
RECEIPT_MARKER_RE = re.compile(r"<!--\s*anneal-receipt:", re.IGNORECASE)
HTML_COMMENT_RE = re.compile(r"<!--.*?(?:-->|\Z)", re.DOTALL)
RECEIPT_KEYS = ("target_base", "merge_base", "head", "tree",
                "human_review_surface")
SHA40_FULL_RE = re.compile(r"[0-9a-f]{40}")


def receipt_footer(target_base: str, merge_base: str, head: str, tree: str,
                   hrs_paths: list[str]) -> str:
    """Render the machine-checked footer that a Review Receipt carries."""
    data = {"target_base": target_base, "merge_base": merge_base,
            "head": head, "tree": tree,
            "human_review_surface": sorted(hrs_paths)}
    # Escape `>` so no path can close the HTML comment early.
    text = json.dumps(data).replace(">", "\\u003e")
    return f"<!-- anneal-receipt:v1 {text} -->\n"


def _reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict:
    keys = [k for k, _ in pairs]
    dups = sorted({k for k in keys if keys.count(k) > 1})
    if dups:
        raise ValueError(f"duplicate key(s) {', '.join(dups)}")
    return dict(pairs)


def receipt_findings(
    text: str, target_base: str, merge_base: str, head: str, tree: str,
    hrs_paths: list[str], changed_paths: set[str],
) -> list[Finding]:
    """Check a Review Receipt's `anneal-receipt:v1` footer.

    Prose cannot be checked mechanically without guessing at wording such
    as "`ci/` is untouched", so the receipt binds its comparison tuple and
    lists its Human review surface paths in one JSON footer (see
    `--emit-receipt-footer`). Every changed review-surface path must be
    listed, and every listed path must be a path this range changes. The
    prose `Human review surface` block stays for humans to judge.
    """
    def finding(msg: str) -> Finding:
        return Finding("receipt", msg)

    out: list[Finding] = []
    # The prose block must be visible, not inside an HTML comment.
    if not re.search(r"human review surface", HTML_COMMENT_RE.sub("", text),
                     re.IGNORECASE):
        out.append(finding("Review Receipt lacks a visible `Human review "
                           "surface` block"))
    markers = len(RECEIPT_MARKER_RE.findall(text))
    footers = RECEIPT_FOOTER_RE.findall(text)
    if markers != 1 or len(footers) != 1:
        out.append(finding(
            f"Review Receipt has {markers} `anneal-receipt:` marker(s); it "
            "needs exactly one well-formed `anneal-receipt:v1` footer (print "
            "it with --emit-receipt-footer)"))
        return out
    try:
        data = json.loads(footers[0], object_pairs_hook=_reject_duplicate_keys)
    except ValueError as e:
        return out + [finding(f"`anneal-receipt:v1` footer is not valid "
                              f"JSON: {e}")]
    if not isinstance(data, dict) or set(data) != set(RECEIPT_KEYS):
        return out + [finding(
            "`anneal-receipt:v1` footer must be an object with exactly the "
            "keys " + ", ".join(f"`{k}`" for k in RECEIPT_KEYS))]
    expected = {"target_base": target_base, "merge_base": merge_base,
                "head": head, "tree": tree}
    for key, sha in expected.items():
        value = data[key]
        if not (isinstance(value, str) and SHA40_FULL_RE.fullmatch(value)):
            out.append(finding(f"footer `{key}` must be a full 40-hex SHA"))
        elif value != sha:
            out.append(finding(
                f"footer `{key}` is `{value[:12]}`, but the checked "
                f"{key} is `{sha[:12]}`"))
    listed = data["human_review_surface"]
    if not (isinstance(listed, list)
            and all(isinstance(p, str) for p in listed)):
        return out + [finding(
            "footer `human_review_surface` must be a list of paths")]
    missing = sorted(set(hrs_paths) - set(listed))
    if missing:
        out.append(finding(
            "footer `human_review_surface` omits changed review-surface "
            "path(s): " + ", ".join(f"`{p}`" for p in missing)))
    unknown = sorted(set(listed) - changed_paths)
    if unknown:
        out.append(finding(
            "footer `human_review_surface` lists path(s) this range does not "
            "change: " + ", ".join(f"`{p}`" for p in unknown)))
    return out


def agents_budget_findings(git: Git, head: str) -> list[Finding]:
    reserve = os.environ.get("GLOBAL_AGENTS_BYTES", DEFAULT_GLOBAL_AGENTS_BYTES)
    if not (reserve.isascii() and reserve.isdecimal()) or len(
            reserve.lstrip("0") or "0") > 5:
        return [Finding("agents-budget",
                        f"invalid GLOBAL_AGENTS_BYTES: {reserve!r}")]
    listing = git.run("ls-tree", "-r", "-l", "-z", head)
    total = 0
    names = []
    for entry in listing.decode("utf-8", "surrogateescape").split("\0"):
        if not entry:
            continue
        meta, path = entry.split("\t", 1)
        if Path(path).name not in ("AGENTS.md", "AGENTS.override.md"):
            continue
        if "/" in path and not path.startswith(ANNEAL):
            continue
        size = meta.split()[3]
        if size.isdigit():
            total += int(size)
            names.append(path)
    if total + int(reserve) >= AGENTS_BUDGET:
        return [Finding(
            "agents-budget",
            f"{' + '.join(sorted(names))} = {total} B plus the {reserve} B "
            f"global reserve reaches the {AGENTS_BUDGET} B shared instruction "
            "budget (see `docs/review-policy-design.md#drift-checks`)",
        )]
    return []


def _crr_block(text: str) -> tuple[str | None, str | None]:
    lines = text.split("\n")
    begins = [i for i, ln in enumerate(lines) if CRR_BEGIN in ln]
    ends = [i for i, ln in enumerate(lines) if CRR_END in ln]
    if len(begins) != 1 or len(ends) != 1 or ends[0] <= begins[0]:
        return None, (f"expected one `{CRR_BEGIN}` followed by one "
                      f"`{CRR_END}`")
    return "\n".join(lines[begins[0]:ends[0] + 1]), None


def crr_parity_findings(git: Git, head: str) -> list[Finding]:
    blocks = []
    for path in CRR_FILES:
        content = git.blob_text(head, path)
        if content is None:
            return [Finding("code-review-rules-parity", "file is missing",
                            path)]
        block, err = _crr_block(content)
        if err:
            return [Finding("code-review-rules-parity", err, path)]
        blocks.append(block)
    if blocks[0] != blocks[1]:
        a, b = blocks[0].split("\n"), blocks[1].split("\n")
        first = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]),
                     min(len(a), len(b)))
        return [Finding(
            "code-review-rules-parity",
            f"`Code Review Rules` block differs from `{CRR_FILES[0]}` at "
            f"block line {first + 1}; keep the mirrors byte-identical",
            CRR_FILES[1],
        )]
    return []


# ---------------------------------------------------------------------------
# Upstream `rustc` workaround anchors (`docs/rustc-workarounds.md`).

# Split so this file never contains a literal tag for the scan to flag.
WORKAROUND_TAG = "RUSTC-" "WORKAROUND"
WORKAROUND_PENDING = "#PENDING"
# Markdown is out of scope so prose and examples may name the tag freely.
WORKAROUND_MARKERS = {
    ".rs": ("//", "///", "//!"),
    **{e: ("#",) for e in (".py", ".sh", ".nix", ".toml", ".yml", ".yaml")},
    ".lean": ("--",),
}
# Any spelling a typo might produce (`_` or no separator) counts as an
# attempted tag, so a misspelled anchor fails instead of silently vanishing.
WORKAROUND_LIKE_RE = re.compile(r"RUSTC[-_]?WORKAROUND")
WORKAROUND_ANCHOR_RE = re.compile(
    r"^[ \t]*(?P<marker>//[/!]?|#|--)[ \t]" + re.escape(WORKAROUND_TAG)
    + r"\((?P<ref>[^()\s]*)\)(?P<rest>.*)$"
)
WORKAROUND_ISSUE_RE = re.compile(r"#([1-9][0-9]{0,8})")


@dataclass(frozen=True)
class WorkaroundAnchor:
    path: str
    line: int
    issue: int
    summary: str

    def to_json(self) -> dict[str, object]:
        return {"path": self.path, "line": self.line, "issue": self.issue,
                "summary": self.summary}


def workaround_in_scope(path: str) -> bool:
    """Whether the anchor scan covers `path` (relative to the repo root)."""
    return (path.startswith(ANNEAL)
            and not path.startswith(EXCLUDED_PREFIXES)
            and Path(path).suffix in WORKAROUND_MARKERS)


def scan_workarounds(
    path: str, text: str,
) -> tuple[list[WorkaroundAnchor], list[Finding]]:
    """Return one file's well-formed anchors and its malformed tags.

    An anchor is a comment line, in the file's comment syntax, holding the
    tag, a parenthesized positive `#NNNN` issue number, `: `, and a
    non-empty summary. Every other tag-like spelling is a finding,
    including the `#PENDING` placeholder.
    """
    markers = WORKAROUND_MARKERS[Path(path).suffix]
    anchors: list[WorkaroundAnchor] = []
    out: list[Finding] = []
    tag = WORKAROUND_TAG
    for lineno, line in enumerate(text.split("\n"), start=1):
        hits = WORKAROUND_LIKE_RE.findall(line)
        if not hits:
            continue

        def bad(message: str) -> None:
            out.append(Finding("rustc-workaround", message, path, lineno))

        if len(hits) > 1:
            bad(f"more than one `{tag}` tag on one line")
            continue
        m = WORKAROUND_ANCHOR_RE.match(line)
        if m is None:
            bad(f"malformed anchor; expected a comment line `<marker> {tag}"
                "(#NNNN): <summary>` (see `docs/rustc-workarounds.md`)")
            continue
        if m.group("marker") not in markers:
            bad(f"`{m.group('marker')}` is not a comment marker for "
                f"`{Path(path).suffix}` files (use "
                + " or ".join(f"`{c}`" for c in markers) + ")")
            continue
        ref = m.group("ref")
        if ref == WORKAROUND_PENDING:
            bad(f"unresolved `{tag}({WORKAROUND_PENDING})`; file the "
                "tracking issue and cite its number before Gate 1 converges")
            continue
        issue = WORKAROUND_ISSUE_RE.fullmatch(ref)
        if issue is None:
            bad(f"`{ref}` is not an issue reference; cite `#NNNN`")
            continue
        rest = m.group("rest")
        summary = rest[2:].strip() if rest.startswith(": ") else ""
        if not summary:
            bad("anchor needs `: <summary>` after the issue reference")
            continue
        anchors.append(
            WorkaroundAnchor(path, lineno, int(issue.group(1)), summary))
    return anchors, out


def tree_workarounds(
    git: Git, head: str,
) -> tuple[list[WorkaroundAnchor], list[Finding]]:
    """Scan every in-scope regular file in the tree at `head`."""
    listing = git.run("ls-tree", "-r", "-z", "--full-tree", head, "--")
    entries: list[tuple[str, str]] = []
    for entry in listing.decode("utf-8", "surrogateescape").split("\0"):
        if not entry:
            continue
        meta, path = entry.split("\t", 1)
        mode, kind, sha = meta.split()
        # Symlinks and gitlinks hold no source text to scan.
        if (kind == "blob" and mode in ("100644", "100755")
                and workaround_in_scope(path)):
            entries.append((path, sha))
    anchors: list[WorkaroundAnchor] = []
    out: list[Finding] = []
    if not entries:
        return anchors, out
    batch = git.run("cat-file", "--batch", stdin="".join(
        f"{sha}\n" for _, sha in entries).encode())
    pos = 0
    for path, sha in entries:
        nl = batch.find(b"\n", pos)
        header = batch[pos:nl].decode("ascii", "replace").split()
        if (nl < 0 or len(header) != 3 or header[0] != sha
                or header[1] != "blob" or not header[2].isdigit()):
            raise GitError(f"unexpected `git cat-file` output for {path!r}")
        size = int(header[2])
        data = batch[nl + 1:nl + 1 + size]
        pos = nl + 1 + size + 1
        a, f = scan_workarounds(path, data.decode("utf-8", "replace"))
        anchors += a
        out += f
    return anchors, out


# ---------------------------------------------------------------------------
# Driver.


@dataclass
class Commit:
    sha: str
    author: str
    committer: str
    message: str
    paths: list[str]


def load_commits(git: Git, merge_base: str, head: str) -> list[Commit]:
    """Load each commit in the range with NUL-delimited Git output."""
    shas = git.text("rev-list", "--reverse", f"{merge_base}..{head}").split()
    commits: list[Commit] = []
    for sha in shas:
        meta = git.run("show", "-s", "--format=%an <%ae>%x00%cn <%ce>%x00%B",
                       sha).decode("utf-8", "replace")
        author, committer, message = meta.split("\x00", 2)
        names = git.run("diff-tree", "-m", "-r", "--root", "--no-commit-id",
                        "--name-only", "--no-renames", "-z", sha)
        paths = [p for p in names.decode("utf-8", "surrogateescape")
                 .split("\0") if p]
        commits.append(Commit(sha, author, committer, message, paths))
    return commits


def check(
    git: Git, base: str | None, head_ref: str, *,
    pr_body: str | None = None, pr_title: str | None = None,
    receipt: str | None = None, expected_author: str | None = None,
    skip_commit_messages: bool = False,
    forbid_pr_title: tuple[re.Pattern[str], str] | None = None,
) -> tuple[Report, dict[str, object]]:
    """Run every check; `forbid_pr_title` is a (pattern, title) pair."""
    report = Report()
    head = git.commit(head_ref)
    tree = git.tree(head)
    meta: dict[str, object] = {"head": head, "tree": tree}
    report.findings += agents_budget_findings(git, head)
    report.findings += crr_parity_findings(git, head)
    report.findings += tree_workarounds(git, head)[1]
    if forbid_pr_title is not None:
        report.findings += pr_title_policy_findings(*forbid_pr_title)
    if base is None:
        if (pr_body is not None or receipt is not None
                or pr_title is not None or expected_author is not None):
            raise GitError("--pr-body-file, --pr-title, --receipt-file, and "
                           "--expected-author require --base")
        return report, meta

    target_base = git.commit(base)
    merge_base = git.text("merge-base", target_base, head).strip()
    if not merge_base:
        raise GitError("--base and --head share no merge base")
    meta.update(target_base=target_base, merge_base=merge_base)
    # Commit dates are author-controlled, so bound header years by the
    # checker's own clock.
    max_year = datetime.datetime.now(datetime.timezone.utc).year

    commits = load_commits(git, merge_base, head)
    meta["commits"] = [c.sha for c in commits]
    for c in commits:
        if not any(p.startswith(COMMIT_SCOPE_PREFIXES) for p in c.paths):
            report.warnings.append(Finding(
                "commit-message", "skipped: touches no Anneal paths",
                f"commit {c.sha[:12]}",
            ))
            continue
        if expected_author is not None:
            for role, ident in (("author", c.author),
                                ("committer", c.committer)):
                if ident != expected_author:
                    report.findings.append(Finding(
                        "commit-author",
                        f"{role} is `{ident}`, expected `{expected_author}`",
                        f"commit {c.sha[:12]}",
                    ))
        if skip_commit_messages:
            report.warnings.append(Finding(
                "commit-message", "skipped: --skip-commit-messages",
                f"commit {c.sha[:12]}",
            ))
            continue
        report.findings += commit_message_findings(c.sha, c.message)

    files = changed_files(git, merge_base, head)
    scoped = [f for f in files.values() if in_anneal_scope(f.path)]
    check_paths = [f.path for f in scoped if f.status != "D"]
    if check_paths:
        res = git.run(
            "diff", "--no-ext-diff", "--no-textconv", "--check", merge_base,
            head, "--", *check_paths, ok_codes=(0, 2),
        ).decode("utf-8", "replace")
        parsed = 0
        for line in res.splitlines():
            m = re.match(r"^(.+?):(\d+): (.*)$", line)
            if m:
                parsed += 1
                report.findings.append(Finding(
                    "diff-check", m.group(3), m.group(1), int(m.group(2))
                ))
        if res.strip() and not parsed:
            raise GitError(f"unparsed `git diff --check` output: {res[:200]}")

    for f in scoped:
        if f.status == "D":
            continue
        needs_content = (
            Path(f.path).suffix in HEADER_EXTS
            or f.path.startswith(TRUSTED_CITATION_PREFIXES)
        )
        if not needs_content or not (f.added or f.status == "A"):
            continue
        content = git.blob_text(head, f.path)
        if content is None:
            raise GitError(f"cannot read {head[:12]}:{f.path}")
        if f.status == "A" and needs_header(f.path):
            report.findings += header_findings(f.path, content, max_year)
        wrap_errs, wrap_warns = wrap_findings(f.path, content, f.added)
        report.findings += wrap_errs
        report.warnings += wrap_warns
        if f.path.startswith(TRUSTED_CITATION_PREFIXES):
            report.findings += trusted_citation_findings(
                f.path, content, f.added_text)
            if (f.status == "A" and Path(f.path).suffix in (".lean", ".rs")
                    and not SHA40_RE.search(content)):
                report.warnings.append(Finding(
                    "trusted-citation",
                    "new trusted file cites no pinned upstream SHA; code "
                    "modeling Rust semantics or `rustc` structures must "
                    "quote and cite `rust-lang/{rust,reference}`",
                    f.path,
                ))

    single = commits[0] if len(commits) == 1 else None
    if pr_body is not None:
        if single is None:
            report.warnings.append(Finding(
                "pr-body", f"skipped: {len(commits)} commits; compare the "
                "description with the squash message by hand",
            ))
        else:
            body = single.message.split("\n", 1)[1] if "\n" in (
                single.message) else ""
            report.findings += pr_body_findings(
                commit_body_to_pr_body(body), pr_body)
    if pr_title is not None:
        if single is None:
            report.warnings.append(Finding(
                "pr-title", f"skipped: {len(commits)} commits",
            ))
        else:
            subject = single.message.split("\n", 1)[0]
            if pr_title.strip() != subject.strip():
                report.findings.append(Finding(
                    "pr-title",
                    f"PR title {pr_title.strip()!r} differs from the commit "
                    f"subject {subject.strip()!r}",
                ))
    # A rename changes its source too: moving a file out of the review
    # surface changes that surface.
    changed = ({p.path for p in files.values()}
               | {p.old_path for p in files.values() if p.old_path})
    hrs = sorted(
        {p.path for p in files.values()
         if is_hrs_path(p.path, p.trust_tier_changed)}
        | {p.old_path for p in files.values()
           if p.old_path is not None
           and is_hrs_path(p.old_path, p.trust_tier_changed)}
    )
    meta["human_review_surface"] = hrs
    size = review_size(diff_numstat(git, merge_base, head))
    meta["review_size"] = size.to_json()
    size_warning = review_size_warning(size)
    if size_warning is not None:
        report.warnings.append(size_warning)
    if receipt is not None:
        report.findings += receipt_findings(
            receipt, target_base, merge_base, head, tree, hrs, changed)
    apply_waivers(report, *parse_waivers(commits, head))
    return report, meta


def _read(path: str) -> str:
    if path == "-":
        return sys.stdin.read()
    return Path(path).read_text(encoding="utf-8")


def _escape_command_data(text: str) -> str:
    """Escape a GitHub Actions workflow command's message."""
    return (text.replace("%", "%25").replace("\r", "%0D")
            .replace("\n", "%0A"))


def _escape_command_property(text: str) -> str:
    return (_escape_command_data(text).replace(":", "%3A")
            .replace(",", "%2C"))


def waiver_annotation(w: Waived) -> str:
    """Render a waived finding as a `::warning::` workflow command.

    Commit-message findings name a commit rather than a file, so they carry
    no `file` property.
    """
    f = w.finding
    props = ["title=" + _escape_command_property(
        f"PR hygiene waived: {f.check}")]
    if f.path is not None and f.check != "commit-message":
        props.insert(0, "file=" + _escape_command_property(f.path))
        if f.line is not None:
            props.insert(1, f"line={f.line}")
    msg = f"{f.render()} (waived by {WAIVER_KEY}: {w.reason})"
    return f"::warning {','.join(props)}::{_escape_command_data(msg)}"


def _summary_cell(text: str) -> str:
    text = html.escape(" ".join(text.split()), quote=False)
    return text.replace("|", "&#124;")


def waiver_summary(waived: list[Waived]) -> str:
    """Render waived findings as a Markdown step summary table."""
    rows = [
        "",
        f"### PR hygiene: {len(waived)} waived finding(s)",
        "",
        "| Check | Location | Finding | Reason |",
        "| --- | --- | --- | --- |",
    ]
    for w in waived:
        f = w.finding
        where = f.path or ""
        if f.path is not None and f.line is not None:
            where = f"{f.path}:{f.line}"
        rows.append("| " + " | ".join(_summary_cell(t) for t in (
            f.check, where, f.message, w.reason)) + " |")
    return "\n".join(rows) + "\n"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n", 1)[0],
    )
    parser.add_argument("--repo", default=".",
                        help="any path inside the repository (default: .)")
    parser.add_argument("--base", help="target base ref (enables diff, "
                        "commit, PR, and receipt checks)")
    parser.add_argument("--head", default="HEAD", help="head ref to check")
    parser.add_argument("--pr-body-file",
                        help="PR description to compare ('-' for stdin)")
    parser.add_argument("--pr-title", help="PR title to compare")
    parser.add_argument("--forbid-pr-title-regex", metavar="REGEX",
                        help="fail if the PR title (--pr-title, else the "
                        "PR_TITLE environment variable) matches REGEX")
    parser.add_argument("--receipt-file",
                        help="Review Receipt comment to check ('-' for stdin)")
    parser.add_argument("--expected-author", metavar="'NAME <EMAIL>'",
                        help="require this commit author and committer")
    parser.add_argument("--skip-commit-messages", action="store_true",
                        help="skip commit-message checks (for PRs whose "
                        "authenticated author is a bot)")
    parser.add_argument("--emit-pr-body", action="store_true",
                        help="print the expected PR description for --head "
                        "and exit")
    parser.add_argument("--emit-receipt-footer", action="store_true",
                        help="print the `anneal-receipt:v1` footer for "
                        "--base and --head and exit")
    parser.add_argument("--json", action="store_true",
                        help="emit a machine-readable report")
    args = parser.parse_args(argv)

    try:
        repo = Path(args.repo).resolve()
        git = Git(Git(repo).toplevel())
        if args.emit_pr_body:
            head = git.commit(args.head)
            body = git.text("log", "-1", "--format=%b", head)
            sys.stdout.write(commit_body_to_pr_body(body))
            return 0
        # An empty value (say, from an unset shell variable) must fail
        # rather than silently skip a check.
        for flag, value in (("--pr-body-file", args.pr_body_file),
                            ("--receipt-file", args.receipt_file),
                            ("--expected-author", args.expected_author)):
            if value is not None and not value.strip():
                raise GitError(f"{flag} must not be empty")
        pr_body = (_read(args.pr_body_file)
                   if args.pr_body_file is not None else None)
        receipt = (_read(args.receipt_file)
                   if args.receipt_file is not None else None)
        forbid_pr_title = None
        if args.forbid_pr_title_regex is not None:
            if not args.forbid_pr_title_regex:
                raise GitError("--forbid-pr-title-regex must not be empty")
            try:
                pattern = re.compile(args.forbid_pr_title_regex)
            except re.error as e:
                raise GitError(
                    f"invalid --forbid-pr-title-regex: {e}") from e
            title = (args.pr_title if args.pr_title is not None
                     else os.environ.get("PR_TITLE"))
            if title is None or not title.strip():
                raise GitError("--forbid-pr-title-regex needs a non-empty "
                               "PR title in --pr-title or PR_TITLE")
            forbid_pr_title = (pattern, title)
        report, meta = check(
            git, args.base, args.head, pr_body=pr_body,
            pr_title=args.pr_title, receipt=receipt,
            expected_author=args.expected_author,
            skip_commit_messages=args.skip_commit_messages,
            forbid_pr_title=forbid_pr_title,
        )
        if args.emit_receipt_footer:
            if args.base is None:
                raise GitError("--emit-receipt-footer requires --base")
            sys.stdout.write(receipt_footer(
                meta["target_base"], meta["merge_base"], meta["head"],
                meta["tree"], meta["human_review_surface"]))
            return 0
    except (GitError, OSError, UnicodeDecodeError) as e:
        if args.json:
            print(json.dumps({"schema": SCHEMA, "ok": False, "error": str(e)}))
        else:
            print(f"check_pr_hygiene: error: {e}", file=sys.stderr)
        return 2

    ok = not report.findings
    # Waivers are loud: one annotation per waived finding, plus a step
    # summary table in GitHub Actions. With --json, stdout is the report.
    annotations = sys.stderr if args.json else sys.stdout
    for w in report.waived:
        print(waiver_annotation(w), file=annotations)
    # Surface the advisory size budget on the PR without failing the job.
    if os.environ.get("GITHUB_ACTIONS") == "true":
        for w in report.warnings:
            if w.check == "review-size":
                title = _escape_command_property("PR review-size budget")
                print(f"::warning title={title}::"
                      f"{_escape_command_data(w.message)}", file=annotations)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path and report.waived:
        try:
            with open(summary_path, "a", encoding="utf-8") as f:
                f.write(waiver_summary(report.waived))
        except OSError as e:
            print(f"check_pr_hygiene: error: cannot write step summary: {e}",
                  file=sys.stderr)
            return 2
    if args.json:
        print(json.dumps({
            "schema": SCHEMA,
            "ok": ok,
            **meta,
            "findings": [f.to_json() for f in report.findings],
            "warnings": [w.to_json() for w in report.warnings],
            "waived_findings": [w.to_json() for w in report.waived],
            "opt_outs": [o.to_json() for o in report.opt_outs],
        }, indent=2))
    else:
        for w in report.warnings:
            print(f"warning: {w.render()}", file=sys.stderr)
        for f in report.findings:
            print(f.render(), file=sys.stderr)
        waived = (f" ({len(report.waived)} waived)" if report.waived
                  else "")
        if ok:
            print(f"PR hygiene checks passed{waived}.")
        else:
            print(f"{len(report.findings)} PR hygiene finding(s){waived}.",
                  file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
