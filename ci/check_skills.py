#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate repository agent skills, discovery config, and provenance locks."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import string
import subprocess
import sys
from typing import Any, Dict, List, Optional, Sequence, Set, Tuple
import unicodedata
from urllib.parse import unquote


SKILL_NAME_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
COMMIT_SHA_RE = re.compile(r"^[0-9a-f]{40}$")
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
FENCE_RE = re.compile(r"^ {0,3}(`{3,}|~{3,})(.*)$")
ATX_HEADING_RE = re.compile(r"^ {0,3}#{1,6}[ \t]+(.+?)(?:[ \t]+#+[ \t]*)?$")
SETEXT_UNDERLINE_RE = re.compile(r"^ {0,3}(?:=+|-+)[ \t]*$")
THEMATIC_BREAK_RE = re.compile(r"^ {0,3}(?:(?:\*[ \t]*){3,}|(?:-[ \t]*){3,}|(?:_[ \t]*){3,})$")
PARAGRAPH_BREAK_RE = re.compile(
    r"^(?:\s*$| {0,3}(?:>|#{1,6}(?:[ \t]|$)|[-+*] |\d+[.)] )| {4}|\t)"
)
ANGLE_DEST_PATTERN = r"<(?:\\.|[^<>\\\n])*>"
ANGLE_DEST_RE = re.compile(ANGLE_DEST_PATTERN)
REF_DEF_RE = re.compile(
    rf"^ {{0,3}}\[([^\]]+)\]:[ \t]*({ANGLE_DEST_PATTERN}|\S+)(?:[ \t]+.*)?$"
)
INLINE_LINK_END_RE = re.compile(
    r'''(?:\s+(?:"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'|'''
    r"\((?:\\.|[^()\\])*\)))?\s*\)"
)
MARKDOWN_ESCAPE_RE = re.compile(r"\\([" + re.escape(string.punctuation) + r"])")
LINK_LABEL_TOKEN_RE = re.compile(
    MARKDOWN_ESCAPE_RE.pattern + r"|!?\[|\]|\n[ \t]*\n"
)
LINK_DEST_START_RE = re.compile(r"\(\s*")
REF_USE_RE = re.compile(
    r"!?\[((?:[^\[\]\n]|\n(?![ \t]*\n))+)\]\[([^\[\]\n]*)\]"
)

FORBIDDEN_UNICODE_CATEGORIES = frozenset({"Cc", "Cf", "Zl", "Zp"})
REPO_OWNED_ROOT_SKILLS = frozenset(
    {"unsafe-rust", "zerocopy-development", "zerocopy-review"}
)
SKILL_DOCUMENT_SUFFIXES = frozenset({".md", ".txt", ".json", ".yaml", ".yml"})
FORBIDDEN_SKILL_CONFIGS = frozenset(
    {"agents.md", "agents.override.md", "claude.md", "gemini.md",
     "lean-toolchain"}
)
MAX_SKILL_LINES = 300
# Existing repository skills exceeding `MAX_SKILL_LINES` are grandfathered at
# their current line counts so they cannot bloat further.
GRANDFATHERED_SKILL_LINE_CAPS: Dict[str, int] = {
    "anneal/skills/change-review/SKILL.md": 483,
    "anneal/skills/source-control/SKILL.md": 439,
    "anneal/skills/trust-review/SKILL.md": 331,
    "skills/architectural-design/SKILL.md": 462,
    "skills/model-refinement/SKILL.md": 307,
    "skills/research-wheel/SKILL.md": 353,
    "skills/swarm-model-refinement/SKILL.md": 391,
    "skills/unsafe-rust/SKILL.md": 364,
}
# Codex reads `AGENTS.md` from repository root down to cwd within a 32 KiB
# default budget (`project_doc_max_bytes = 32768`), reserving 1024 B for user
# global instructions (see `anneal/development/review-policy-design.md`).
CODEX_AGENTS_MD_BUDGET_BYTES = 31744
AGENTS_SCAN_PRUNE_DIRS = frozenset({".git", ".lake", "target"})
THEORY_TACTIC_KIND_TO_TOKEN: Dict[str, Optional[str]] = {
    "Parser.Term.byTactic": None,
    "Parser.Term.binderTactic": None,
    "Lean.Parser.Tactic.apply": "apply",
    "Lean.Parser.Tactic.cases": "cases",
    "Lean.Parser.Tactic.change": "change",
    "Lean.Parser.Tactic.constructor": "constructor",
    "Lean.Parser.Tactic.decide": "decide",
    "Lean.Parser.Tactic.dsimp": "dsimp",
    "Lean.Parser.Tactic.elimTarget": None,
    "Lean.Parser.Tactic.exact": "exact",
    "Lean.Parser.Tactic.first": "first",
    "Lean.Parser.Tactic.induction": "induction",
    "Lean.Parser.Tactic.inductionAlt": None,
    "Lean.Parser.Tactic.inductionAltLHS": None,
    "Lean.Parser.Tactic.inductionAlts": None,
    "Lean.Parser.Tactic.injection": "injection",
    "Lean.Parser.Tactic.intro": "intro",
    "Lean.Parser.Tactic.left": "left",
    "Lean.Parser.Tactic.location": None,
    "Lean.Parser.Tactic.locationHyp": None,
    "Lean.Parser.Tactic.optConfig": None,
    "Lean.Parser.Tactic.paren": None,
    "Lean.Parser.Tactic.refine": "refine",
    "Lean.Parser.Tactic.revert": "revert",
    "Lean.Parser.Tactic.right": "right",
    "Lean.Parser.Tactic.rwRule": None,
    "Lean.Parser.Tactic.rwRuleSeq": None,
    "Lean.Parser.Tactic.rwSeq": "rw",
    "Lean.Parser.Tactic.simp": "simp",
    "Lean.Parser.Tactic.simpLemma": None,
    "Lean.Parser.Tactic.subst": "subst",
    "Lean.Parser.Tactic.tacticHave__": "have",
    "Lean.Parser.Tactic.tacticLet__": "let",
    "Lean.Parser.Tactic.«tacticNomatch_,,»": "nomatch",
    "Lean.Parser.Tactic.tacticRepeat_": "repeat",
    "Lean.Parser.Tactic.tacticRfl": "rfl",
    "Lean.Parser.Tactic.tacticSeq": None,
    "Lean.Parser.Tactic.tacticSeq1Indented": None,
    "Lean.Parser.Tactic.«tactic_<;>_»": "<;>",
    "Lean.Parser.Tactic.unfold": "unfold",
    "tacticFunext___": "funext",
}
ANNEAL_MODULE_RE = re.compile(r"\b(Anneal(?:\.[A-Z][A-Za-z0-9_]*)+)\b")
BACKTICK_TOKEN_RE = re.compile(r"`([^`\n]+)`")


class SkillCheckError(Exception):
    """Raised when any skill, link, or provenance invariant fails."""


def fail(message: str) -> SkillCheckError:
    return SkillCheckError(message)


def check_safe_path_string(raw: str, context: str) -> PurePosixPath:
    """Validate a relative POSIX path with no traversal or control chars."""
    if not raw or raw.startswith("/") or raw.endswith("/") or "\\" in raw:
        raise fail(f"{context}: invalid relative path {raw!r}")
    if (
        not raw.isascii()
        or any(ord(ch) < 0x20 or ord(ch) >= 0x7F for ch in raw)
        or any(
            unicodedata.category(ch) in FORBIDDEN_UNICODE_CATEGORIES
            for ch in raw
        )
    ):
        raise fail(f"{context}: non-ASCII or control character in path {raw!r}")
    segs = raw.split("/")
    if any(seg in ("", ".", "..") for seg in segs):
        raise fail(f"{context}: invalid path segment in {raw!r}")
    return PurePosixPath(raw)


def decode_clean_utf8(data: bytes, display_path: str) -> str:
    """Decode UTF-8 strictly and reject bidi or invisible control characters."""
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise fail(f"{display_path}: invalid UTF-8 ({exc})") from exc
    for idx, ch in enumerate(text):
        if ch in ("\n", "\t"):
            continue
        cat = unicodedata.category(ch)
        if cat in FORBIDDEN_UNICODE_CATEGORIES:
            raise fail(
                f"{display_path}: forbidden Unicode control/bidi character "
                f"U+{ord(ch):04X} ({cat}) at char offset {idx}"
            )
    return text


def load_strict_json(text: str, display_path: str) -> Any:
    """Parse JSON while rejecting duplicate keys and non-standard constants."""

    def reject_duplicates(pairs: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
        obj: Dict[str, Any] = {}
        for key, value in pairs:
            if key in obj:
                raise fail(f"{display_path}: duplicate JSON key {key!r}")
            obj[key] = value
        return obj

    def reject_constants(token: str) -> Any:
        raise fail(f"{display_path}: forbidden JSON constant {token!r}")

    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicates,
            parse_constant=reject_constants,
        )
    except json.JSONDecodeError as exc:
        raise fail(f"{display_path}: invalid JSON ({exc})") from exc


def assert_symlink_free_within_repo(
    repo_root: Path, target: Path, context: str
) -> None:
    """Ensure `target` stays inside `repo_root` and traverses zero symlinks."""
    try:
        rel_parts = target.relative_to(repo_root).parts
    except ValueError as exc:
        raise fail(
            f"{context}: path escapes repository root: {target}"
        ) from exc
    cur = repo_root
    for part in rel_parts:
        if part in ("", ".", ".."):
            raise fail(f"{context}: unnormalized segment {part!r} in {target}")
        cur = cur / part
        try:
            st = cur.lstat()
        except FileNotFoundError:
            rel_missing = cur.relative_to(repo_root).as_posix()
            raise fail(f"{context}: target does not exist: {rel_missing}")
        if stat.S_ISLNK(st.st_mode):
            rel_link = cur.relative_to(repo_root).as_posix()
            raise fail(f"{context}: symlink forbidden: {rel_link}")


def resolve_relative_within_repo(
    repo_root: Path, base_dir: Path, raw_rel: str, context: str
) -> Path:
    """Stepwise resolve `raw_rel` from `base_dir` inside `repo_root`.

    Checks every traversed segment with `lstat()` before applying subsequent
    `..` steps, preventing `<symlink>/..` escapes and `../<repo_name>/...`
    parent-directory bounces that lexical `os.path.normpath` would collapse.
    """
    assert_symlink_free_within_repo(repo_root, base_dir, context)
    if not raw_rel or raw_rel.startswith("/") or "\\" in raw_rel:
        raise fail(f"{context}: invalid relative path {raw_rel!r}")

    must_be_dir = raw_rel.endswith("/")
    trimmed = raw_rel[:-1] if must_be_dir else raw_rel
    if not trimmed:
        raise fail(f"{context}: invalid relative path {raw_rel!r}")

    segments = trimmed.split("/")
    cur = base_dir
    for idx, seg in enumerate(segments):
        is_last = idx == len(segments) - 1
        if seg == "":
            raise fail(f"{context}: empty path segment in {raw_rel!r}")
        if seg == ".":
            continue
        if seg == "..":
            if cur == repo_root:
                raise fail(
                    f"{context}: path escapes repository root: {raw_rel!r}"
                )
            cur = cur.parent
            continue
        nxt = cur / seg
        try:
            st = nxt.lstat()
        except FileNotFoundError:
            rel_missing = nxt.relative_to(repo_root).as_posix()
            raise fail(f"{context}: target does not exist: {rel_missing}")
        if stat.S_ISLNK(st.st_mode):
            rel_link = nxt.relative_to(repo_root).as_posix()
            raise fail(f"{context}: symlink forbidden: {rel_link}")
        if (not is_last or must_be_dir) and not stat.S_ISDIR(st.st_mode):
            rel_not_dir = nxt.relative_to(repo_root).as_posix()
            raise fail(f"{context}: expected directory at {rel_not_dir}")
        cur = nxt

    if must_be_dir and not stat.S_ISDIR(cur.lstat().st_mode):
        rel_not_dir = cur.relative_to(repo_root).as_posix()
        raise fail(f"{context}: expected directory at {rel_not_dir}")
    return cur


def scan_tree(
    repo_root: Path, tree_root: Path
) -> Tuple[Dict[str, Tuple[Path, os.stat_result]], List[str]]:
    """Walk `tree_root` without following symlinks and enforce path hygiene.

    Returns `(regular_files_by_rel_posix, empty_dirs_by_rel_posix)` relative to
    `tree_root`.
    """
    tree_rel = tree_root.relative_to(repo_root).as_posix()
    assert_symlink_free_within_repo(repo_root, tree_root, tree_rel)
    st_root = tree_root.lstat()
    if not stat.S_ISDIR(st_root.st_mode):
        raise fail(f"{tree_rel}: expected directory")

    files: Dict[str, Tuple[Path, os.stat_result]] = {}
    empty_dirs: List[str] = []
    seen_folded: Dict[str, str] = {}

    def record_collision_check(rel_posix: str) -> None:
        cur = ""
        for seg in PurePosixPath(rel_posix).parts:
            cur = f"{cur}/{seg}" if cur else seg
            folded = unicodedata.normalize("NFC", cur).casefold()
            prev = seen_folded.get(folded)
            if prev is not None and prev != cur:
                raise fail(
                    f"{tree_rel}: case/NFC path collision between "
                    f"{prev!r} and {cur!r}"
                )
            seen_folded[folded] = cur

    def visit(directory: Path, rel_prefix: str) -> bool:
        entries = sorted(os.scandir(directory), key=lambda e: e.name)
        has_children = False
        for entry in entries:
            has_children = True
            rel_posix = (
                f"{rel_prefix}/{entry.name}" if rel_prefix else entry.name
            )
            display = f"{tree_rel}/{rel_posix}"
            check_safe_path_string(rel_posix, display)
            name = entry.name.casefold()
            if (
                name.startswith((".", "rust-toolchain", "lakefile"))
                or name in FORBIDDEN_SKILL_CONFIGS
            ):
                raise fail(f"{display}: forbidden skill path")
            record_collision_check(rel_posix)
            st = entry.stat(follow_symlinks=False)
            if stat.S_ISLNK(st.st_mode):
                raise fail(f"{display}: symlink is forbidden")
            if stat.S_ISDIR(st.st_mode):
                child_non_empty = visit(Path(entry.path), rel_posix)
                if not child_non_empty:
                    empty_dirs.append(rel_posix)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink != 1:
                    raise fail(f"{display}: hard link is forbidden")
                files[rel_posix] = (Path(entry.path), st)
            else:
                raise fail(
                    f"{display}: unsupported non-regular file mode "
                    f"{oct(st.st_mode)}"
                )
        return has_children

    visit(tree_root, "")
    return files, empty_dirs


def git_environment() -> Dict[str, str]:
    """Let Git use the supplied cwd even when called from a hook."""
    local_names = subprocess.check_output(
        ["git", "rev-parse", "--local-env-vars"], text=True,
    ).splitlines()
    environment = os.environ.copy()
    for name in local_names:
        environment.pop(name, None)
    return environment


def query_git_stage_modes(
    repo_root: Path, rel_prefixes: Sequence[str]
) -> Optional[Dict[str, str]]:
    """Return `{repo_rel_posix: mode}` when `repo_root` is a Git worktree."""
    git_cmd = [
        "git",
        "-c",
        "core.hooksPath=/dev/null",
        "-c",
        "core.fsmonitor=false",
    ]
    environment = git_environment()
    probe = subprocess.run(
        git_cmd + ["rev-parse", "--show-toplevel"],
        cwd=repo_root,
        env=environment,
        capture_output=True,
        text=True,
    )
    if probe.returncode != 0 or Path(probe.stdout.strip()).resolve() != repo_root:
        return None
    proc = subprocess.run(
        git_cmd + ["ls-files", "-z", "--stage", "--"] + list(rel_prefixes),
        cwd=repo_root,
        env=environment,
        capture_output=True,
    )
    if proc.returncode != 0:
        err = proc.stderr.decode("utf-8", errors="replace")
        raise fail(f"git ls-files --stage failed: {err}")
    staged: Dict[str, str] = {}
    for record in proc.stdout.split(b"\0"):
        if not record:
            continue
        meta_bytes, sep, path_bytes = record.partition(b"\t")
        if not sep:
            raise fail(f"unexpected git ls-files record: {record!r}")
        mode = meta_bytes.decode("ascii").split()[0]
        rel_path = path_bytes.decode("utf-8")
        if mode not in ("100644", "100755"):
            raise fail(f"{rel_path}: forbidden Git index mode {mode}")
        staged[rel_path] = mode
    return staged


def parse_frontmatter(
    text: str, display_path: str
) -> Tuple[Dict[str, str], str]:
    """Parse strict minimal YAML frontmatter and return `(fields, body)`."""
    if not text.startswith("---\n"):
        raise fail(
            f"{display_path}: missing opening '---' YAML frontmatter delimiter"
        )
    end_idx = text.find("\n---\n", 4)
    if end_idx != -1:
        fm_raw = text[4:end_idx]
        body = text[end_idx + 5 :]
    elif text.endswith("\n---"):
        fm_raw = text[4:-4]
        body = ""
    else:
        raise fail(
            f"{display_path}: missing closing '---' YAML frontmatter delimiter"
        )

    lines = fm_raw.split("\n")
    fields: Dict[str, str] = {}
    i = 0
    while i < len(lines):
        line = lines[i]
        if not line.strip() or line.lstrip(" ").startswith("#"):
            i += 1
            continue
        if "\t" in line:
            raise fail(
                f"{display_path}: tab indentation forbidden in frontmatter"
            )
        if line.startswith(" "):
            raise fail(
                f"{display_path}: unexpected indented frontmatter line {line!r}"
            )
        key, sep, rest = line.partition(":")
        if not sep or not re.match(r"^[A-Za-z0-9_-]+$", key):
            raise fail(f"{display_path}: invalid frontmatter entry {line!r}")
        if key in fields:
            raise fail(f"{display_path}: duplicate frontmatter key {key!r}")
        val = rest.strip()
        i += 1
        if val in (">", ">-", "|", "|-"):
            block_lines: List[str] = []
            indent: Optional[int] = None
            while i < len(lines):
                nxt = lines[i]
                if "\t" in nxt:
                    raise fail(
                        f"{display_path}: tab indentation forbidden in "
                        "frontmatter"
                    )
                if nxt == "":
                    block_lines.append("")
                    i += 1
                    continue
                leading = len(nxt) - len(nxt.lstrip(" "))
                if leading < 2:
                    break
                if indent is None:
                    indent = leading
                elif leading < indent:
                    raise fail(
                        f"{display_path}: inconsistent block indentation "
                        f"under {key!r}"
                    )
                block_lines.append(nxt[indent:])
                i += 1
            if not block_lines or all(b == "" for b in block_lines):
                raise fail(f"{display_path}: empty block scalar for {key!r}")
            joiner = " " if val.startswith(">") else "\n"
            fields[key] = joiner.join(block_lines).strip()
        elif val.startswith('"'):
            if not val.endswith('"') or len(val) < 2:
                raise fail(
                    f"{display_path}: unterminated double-quoted value "
                    f"for {key!r}"
                )
            try:
                parsed = json.loads(val)
            except json.JSONDecodeError as exc:
                raise fail(
                    f"{display_path}: invalid double-quoted string "
                    f"for {key!r} ({exc})"
                ) from exc
            if not isinstance(parsed, str):
                raise fail(f"{display_path}: expected string value for {key!r}")
            fields[key] = parsed
        elif val.startswith("'"):
            if not val.endswith("'") or len(val) < 2:
                raise fail(
                    f"{display_path}: unterminated single-quoted value "
                    f"for {key!r}"
                )
            fields[key] = val[1:-1].replace("''", "'")
        else:
            if not val:
                raise fail(
                    f"{display_path}: empty frontmatter value for {key!r}"
                )
            fields[key] = val

    return fields, body


def mask_fenced_code_blocks(text: str) -> str:
    """Blank out fenced code blocks while preserving line count."""
    out_lines: List[str] = []
    in_fence: Optional[Tuple[str, int]] = None
    for raw_line in text.split("\n"):
        fm = FENCE_RE.match(raw_line)
        if fm:
            ticks, rest = fm.group(1), fm.group(2)
            if in_fence is None:
                # Info strings in backtick fences cannot contain backticks.
                if ticks[0] != "`" or "`" not in rest:
                    in_fence = (ticks[0], len(ticks))
                    out_lines.append("")
                    continue
            elif (
                ticks[0] == in_fence[0]
                and len(ticks) >= in_fence[1]
                and rest.strip() == ""
            ):
                in_fence = None
                out_lines.append("")
                continue
        if in_fence is not None:
            out_lines.append("")
            continue
        out_lines.append(raw_line)
    return "\n".join(out_lines)


def mask_comments_and_code_spans(
    unfenced_text: str, display_path: str, *, keep_code_text: bool = False
) -> str:
    """Mask HTML comments and inline code spans in one left-to-right pass.

    Must run *after* `mask_fenced_code_blocks` so `<!--` inside fenced code is
    ignored, and scans comments alongside backtick runs so `` `<!--` `` inside
    inline code never opens an HTML comment.
    """
    chars = list(unfenced_text)
    n = len(chars)
    i = 0
    while i < n:
        if (
            chars[i] == "<"
            and i + 4 <= n
            and unfenced_text[i : i + 4] == "<!--"
        ):
            end = unfenced_text.find("-->", i + 4)
            if end == -1:
                raise fail(f"{display_path}: unclosed HTML comment '<!--'")
            for k in range(i, end + 3):
                if chars[k] != "\n":
                    chars[k] = " "
            i = end + 3
            continue

        if chars[i] == "`":
            run_start = i
            while i < n and chars[i] == "`":
                i += 1
            tick_len = i - run_start
            j = i
            matched_end = -1
            while j < n:
                # Inline code spans cannot cross a blank line (paragraph break).
                if chars[j] == "\n":
                    k = j + 1
                    while k < n and chars[k] in (" ", "\t"):
                        k += 1
                    if k < n and chars[k] == "\n":
                        break
                    j += 1
                    continue
                if chars[j] != "`":
                    j += 1
                    continue
                close_start = j
                while j < n and chars[j] == "`":
                    j += 1
                if j - close_start == tick_len:
                    matched_end = j
                    break
            if matched_end != -1:
                if keep_code_text:
                    for k in range(run_start, run_start + tick_len):
                        chars[k] = ""
                    for k in range(matched_end - tick_len, matched_end):
                        chars[k] = ""
                else:
                    for k in range(run_start, matched_end):
                        if chars[k] != "\n":
                            chars[k] = " "
                i = matched_end
            continue

        i += 1
    return "".join(chars)


def strip_markdown_code_and_comments(body: str, display_path: str) -> str:
    """Return `body` with fenced blocks, comments, and inline code masked."""
    unfenced = mask_fenced_code_blocks(body)
    return mask_comments_and_code_spans(unfenced, display_path)


def parse_inline_destination(text: str, opening: int) -> Optional[Tuple[str, int]]:
    start = LINK_DEST_START_RE.match(text, opening)
    if start is None:
        return None
    dest_start = start.end()
    if text.startswith("<", dest_start):
        angle = ANGLE_DEST_RE.match(text, dest_start)
        if angle is None:
            return None
        dest_end = angle.end()
    else:
        depth = 0
        dest_end = dest_start
        while dest_end < len(text):
            escape = MARKDOWN_ESCAPE_RE.match(text, dest_end)
            if escape:
                dest_end = escape.end()
                continue
            char = text[dest_end]
            if char.isspace() or (char == ")" and depth == 0):
                break
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
            dest_end += 1
        if depth:
            return None
    end = INLINE_LINK_END_RE.match(text, dest_end)
    if end is None:
        return None
    return text[dest_start:dest_end], end.end()


def inline_links(text: str):
    """Yield the label, raw destination and span of each inline link."""
    labels: List[re.Match[str]] = []
    cursor = 0
    for token in LINK_LABEL_TOKEN_RE.finditer(text):
        if token.start() < cursor or token.group(1) is not None:
            continue
        mark = token.group()
        if mark in ("[", "!["):
            labels.append(token)
        elif mark == "]":
            if not labels:
                continue
            label_start = labels.pop()
            destination = parse_inline_destination(text, token.end())
            if destination is None:
                continue
            raw_dest, cursor = destination
            yield text[label_start.end():token.start()], raw_dest, label_start.start(), cursor
            if label_start.group() == "[":
                labels = [label for label in labels if label.group() == "!["]
        else:
            labels.clear()


def github_heading_slugs(md_text: str, display_path: str) -> Set[str]:
    """Compute GitHub-compatible heading anchor slugs for `md_text`."""
    if md_text.startswith("---\n"):
        end_idx = md_text.find("\n---\n", 4)
        body = md_text[end_idx + 5 :] if end_idx != -1 else md_text
    else:
        body = md_text
    unfenced = mask_fenced_code_blocks(body)
    uncommented = mask_comments_and_code_spans(
        unfenced, display_path, keep_code_text=True
    )
    slugs: Set[str] = set()
    counts: Dict[str, int] = {}
    paragraph: List[str] = []

    for raw_line in uncommented.splitlines():
        hm = ATX_HEADING_RE.match(raw_line)
        if hm:
            heading = hm.group(1).strip()
        elif paragraph and SETEXT_UNDERLINE_RE.match(raw_line):
            heading = " ".join(paragraph)
        else:
            if (
                PARAGRAPH_BREAK_RE.match(raw_line)
                or SETEXT_UNDERLINE_RE.match(raw_line)
                or THEMATIC_BREAK_RE.match(raw_line)
                or REF_DEF_RE.match(raw_line)
            ):
                paragraph.clear()
            else:
                paragraph.append(raw_line.strip())
            continue
        paragraph.clear()
        characters = list(heading)
        for label, _, start, end in inline_links(heading):
            label_start = start + (2 if heading.startswith("![", start) else 1)
            label_end = label_start + len(label)
            characters[start:label_start] = [""] * (label_start - start)
            characters[label_end:end] = [""] * (end - label_end)
        heading = "".join(characters)
        heading = re.sub(r"\[([^\]]+)\]\[[^\]]*\]", r"\1", heading)
        heading = heading.replace("`", "").lower()
        kept: List[str] = []
        for ch in heading:
            cat = unicodedata.category(ch)
            if ch in (" ", "-", "_") or cat.startswith(("L", "N")):
                kept.append(ch)
        base = "".join(kept).replace(" ", "-")
        if base in counts:
            counts[base] += 1
            slug = f"{base}-{counts[base]}"
        else:
            counts[base] = 0
            slug = base
        slugs.add(slug)
    return slugs


def normalize_link_destination(raw_dest: str, context: str) -> str:
    """Extract the URL/path portion from a Markdown inline link destination."""
    dest = raw_dest.strip()
    if not dest:
        raise fail(f"{context}: empty Markdown link destination")
    if dest.startswith("<"):
        angle = ANGLE_DEST_RE.fullmatch(dest)
        if angle is None:
            raise fail(f"{context}: unclosed '<...>' link destination")
        dest = dest[1:-1]
    else:
        # Strip an optional space-separated link title ("..." or '...').
        parts = dest.split(None, 1)
        if len(parts) == 2:
            title = parts[1].strip()
            if (title.startswith('"') and title.endswith('"')) or (
                title.startswith("'") and title.endswith("'")
            ):
                dest = parts[0]
            else:
                raise fail(
                    f"{context}: unescaped whitespace in link {raw_dest!r}"
                )
    if not dest:
        raise fail(f"{context}: empty Markdown link destination")
    return MARKDOWN_ESCAPE_RE.sub(r"\1", dest)


def validate_markdown_links(
    repo_root: Path,
    md_path: Path,
    body_without_frontmatter: str,
    slug_cache: Dict[Path, Set[str]],
) -> None:
    """Validate relative inline/reference links and `#anchor`s in `md_path`."""
    rel_display = md_path.relative_to(repo_root).as_posix()
    masked_doc = strip_markdown_code_and_comments(
        body_without_frontmatter, rel_display
    )

    ref_defs: Dict[str, Tuple[int, str]] = {}
    non_def_lines: List[str] = []
    for lineno, line in enumerate(masked_doc.split("\n"), start=1):
        rm = REF_DEF_RE.match(line)
        if rm:
            label = " ".join(rm.group(1).split()).casefold()
            if label in ref_defs:
                raise fail(
                    f"{rel_display}:{lineno}: duplicate link reference "
                    f"label {label!r}"
                )
            ref_defs[label] = (lineno, rm.group(2))
            non_def_lines.append("")
        else:
            non_def_lines.append(line)

    prose_doc = "\n".join(non_def_lines)
    targets_to_check: List[Tuple[int, str]] = []
    for _label, (lineno, raw_dest) in ref_defs.items():
        targets_to_check.append(
            (
                lineno,
                normalize_link_destination(raw_dest, f"{rel_display}:{lineno}"),
            )
        )

    for _, raw_dest, start, _ in inline_links(prose_doc):
        lineno = 1 + prose_doc.count("\n", 0, start)
        targets_to_check.append(
            (
                lineno,
                normalize_link_destination(
                    raw_dest, f"{rel_display}:{lineno}"
                ),
            )
        )
    for um in REF_USE_RE.finditer(prose_doc):
        lineno = 1 + prose_doc.count("\n", 0, um.start())
        text_label, explicit_ref = um.group(1), um.group(2)
        lookup = " ".join((explicit_ref or text_label).split()).casefold()
        if lookup not in ref_defs:
            raise fail(
                f"{rel_display}:{lineno}: undefined Markdown link "
                f"reference {lookup!r}"
            )

    for lineno, dest in targets_to_check:
        ctx = f"{rel_display}:{lineno}"
        if dest.startswith(("https://", "http://", "mailto:")):
            continue
        if re.match(r"^[a-zA-Z][a-zA-Z0-9+.-]*:", dest) or dest.startswith(
            "//"
        ):
            raise fail(f"{ctx}: unsupported URL scheme in link {dest!r}")
        if dest.startswith("/") or "\\" in dest or "?" in dest:
            raise fail(f"{ctx}: invalid relative link syntax {dest!r}")

        path_part, sep, anchor = dest.partition("#")
        try:
            path_part = unquote(path_part, errors="strict")
            anchor = unquote(anchor, errors="strict")
        except UnicodeDecodeError as exc:
            raise fail(f"{ctx}: invalid UTF-8 in link {dest!r}") from exc
        if any(
            unicodedata.category(ch) in FORBIDDEN_UNICODE_CATEGORIES
            for ch in path_part + anchor
        ):
            raise fail(f"{ctx}: control/bidi character in link {dest!r}")
        if path_part:
            target = resolve_relative_within_repo(
                repo_root, md_path.parent, path_part, ctx
            )
        else:
            target = md_path

        if sep:
            if not anchor:
                raise fail(f"{ctx}: empty '#' anchor in link {dest!r}")
            st = target.lstat()
            if not stat.S_ISREG(st.st_mode) or target.suffix.lower() != ".md":
                raise fail(
                    f"{ctx}: anchor link {dest!r} must target a regular "
                    ".md file"
                )
            slugs = slug_cache.get(target)
            if slugs is None:
                target_rel = target.relative_to(repo_root).as_posix()
                target_text = decode_clean_utf8(target.read_bytes(), target_rel)
                slugs = github_heading_slugs(target_text, target_rel)
                slug_cache[target] = slugs
            if anchor not in slugs:
                target_rel = target.relative_to(repo_root).as_posix()
                raise fail(
                    f"{ctx}: broken heading anchor #{anchor} in {target_rel}"
                )


def validate_vendor_lock(
    repo_root: Path,
    skills_dir: Path,
    root_files: Dict[str, Tuple[Path, os.stat_result]],
    root_empty_dirs: Sequence[str],
    git_modes: Optional[Dict[str, str]],
) -> Set[str]:
    """Validate `skills/vendor-lock.json` against disk and Git index state."""
    lock_path = skills_dir / "vendor-lock.json"
    lock_rel = "skills/vendor-lock.json"
    if "vendor-lock.json" not in root_files:
        raise fail(f"missing {lock_rel}")
    _, lock_st = root_files["vendor-lock.json"]
    if lock_st.st_mode & 0o111:
        raise fail(f"{lock_rel}: lockfile must not be executable")

    lock_text = decode_clean_utf8(lock_path.read_bytes(), lock_rel)
    lock_data = load_strict_json(lock_text, lock_rel)
    if not isinstance(lock_data, dict) or set(lock_data.keys()) != {
        "schema",
        "packages",
    }:
        raise fail(
            f"{lock_rel}: top-level keys must be exact {{'schema', 'packages'}}"
        )
    if type(lock_data["schema"]) is not int or lock_data["schema"] != 1:
        raise fail(f"{lock_rel}: expected integer schema == 1")

    canonical = json.dumps(lock_data, indent=2) + "\n"
    if lock_text != canonical:
        raise fail(
            f"{lock_rel}: non-canonical JSON formatting "
            "(expected 2-space indent + trailing newline)"
        )

    packages = lock_data["packages"]
    if not isinstance(packages, dict) or not packages:
        raise fail(f"{lock_rel}: 'packages' must be a non-empty JSON object")
    pkg_names = list(packages.keys())
    if pkg_names != sorted(pkg_names):
        raise fail(
            f"{lock_rel}: 'packages' keys must be sorted lexicographically"
        )

    empty_dir_set = set(root_empty_dirs)
    lock_is_tracked = git_modes is not None and lock_rel in git_modes

    for pkg_name, meta in packages.items():
        pkg_ctx = f"{lock_rel} [{pkg_name}]"
        if not SKILL_NAME_RE.match(pkg_name):
            raise fail(f"{pkg_ctx}: invalid package name {pkg_name!r}")
        if not isinstance(meta, dict) or set(meta.keys()) != {
            "upstream_repo",
            "upstream_path",
            "upstream_commit",
            "omitted_upstream_paths",
            "local_modifications",
            "files",
        }:
            raise fail(
                f"{pkg_ctx}: package keys must be exact {{'upstream_repo', "
                "'upstream_path', 'upstream_commit', "
                "'omitted_upstream_paths', 'local_modifications', 'files'}}"
            )

        upstream_repo = meta["upstream_repo"]
        if (
            not isinstance(upstream_repo, str)
            or not upstream_repo.startswith("https://github.com/")
            or upstream_repo.endswith("/")
            or any(ch.isspace() for ch in upstream_repo)
        ):
            raise fail(f"{pkg_ctx}: invalid upstream_repo {upstream_repo!r}")

        upstream_path = meta["upstream_path"]
        if not isinstance(upstream_path, str):
            raise fail(f"{pkg_ctx}: upstream_path must be a string")
        check_safe_path_string(upstream_path, f"{pkg_ctx} upstream_path")

        upstream_commit = meta["upstream_commit"]
        if not isinstance(upstream_commit, str) or not COMMIT_SHA_RE.match(
            upstream_commit
        ):
            raise fail(
                f"{pkg_ctx}: upstream_commit must be a 40-char lowercase "
                "hex SHA"
            )

        omitted = meta["omitted_upstream_paths"]
        if not isinstance(omitted, list) or not all(
            isinstance(item, str) for item in omitted
        ):
            raise fail(
                f"{pkg_ctx}: omitted_upstream_paths must be a list of strings"
            )
        for item in omitted:
            check_safe_path_string(item, f"{pkg_ctx} omitted_upstream_paths")
        if omitted != sorted(set(omitted)):
            raise fail(
                f"{pkg_ctx}: omitted_upstream_paths must be unique and sorted"
            )

        local_mods = meta["local_modifications"]
        if not isinstance(local_mods, list) or not all(
            isinstance(note, str) and note == note.strip() and bool(note)
            for note in local_mods
        ):
            raise fail(
                f"{pkg_ctx}: local_modifications must be a list of non-empty "
                "trimmed strings"
            )

        files_list = meta["files"]
        if not isinstance(files_list, list) or not files_list:
            raise fail(f"{pkg_ctx}: 'files' must be a non-empty list")

        locked_by_rel: Dict[str, Dict[str, Any]] = {}
        observed_order: List[str] = []
        for entry in files_list:
            if not isinstance(entry, dict) or set(entry.keys()) != {
                "path",
                "mode",
                "bytes",
                "sha256",
            }:
                raise fail(
                    f"{pkg_ctx}: each file entry must have exact keys "
                    "{'path', 'mode', 'bytes', 'sha256'}"
                )
            rel_file = entry["path"]
            if not isinstance(rel_file, str):
                raise fail(f"{pkg_ctx}: file path must be a string")
            check_safe_path_string(rel_file, f"{pkg_ctx} file")
            if rel_file in locked_by_rel:
                raise fail(f"{pkg_ctx}: duplicate file entry {rel_file!r}")
            if entry["mode"] not in ("100644", "100755"):
                raise fail(
                    f"{pkg_ctx} ({rel_file}): invalid mode {entry['mode']!r}"
                )
            if type(entry["bytes"]) is not int or entry["bytes"] < 0:
                raise fail(
                    f"{pkg_ctx} ({rel_file}): 'bytes' must be a "
                    "non-negative int"
                )
            if not isinstance(entry["sha256"], str) or not SHA256_RE.match(
                entry["sha256"]
            ):
                raise fail(
                    f"{pkg_ctx} ({rel_file}): 'sha256' must be 64 lowercase "
                    "hex chars"
                )
            locked_by_rel[rel_file] = entry
            observed_order.append(rel_file)

        if observed_order != sorted(observed_order):
            raise fail(f"{pkg_ctx}: 'files' must be sorted by path")
        if "SKILL.md" not in locked_by_rel:
            raise fail(f"{pkg_ctx}: 'files' must include 'SKILL.md'")

        pkg_dir = skills_dir / pkg_name
        if not pkg_dir.exists() or pkg_dir.is_symlink() or not pkg_dir.is_dir():
            raise fail(f"{pkg_ctx}: missing directory skills/{pkg_name}")

        pkg_prefix = f"{pkg_name}/"
        disk_by_rel = {
            rel[len(pkg_prefix) :]: info
            for rel, info in root_files.items()
            if rel.startswith(pkg_prefix)
        }
        missing = sorted(set(locked_by_rel.keys()) - set(disk_by_rel.keys()))
        if missing:
            raise fail(f"{pkg_ctx}: missing locked file(s) on disk: {missing}")
        unexpected = sorted(set(disk_by_rel.keys()) - set(locked_by_rel.keys()))
        if unexpected:
            raise fail(
                f"{pkg_ctx}: unexpected/untracked file(s) in "
                f"skills/{pkg_name}: {unexpected}"
            )
        for empty_rel in empty_dir_set:
            if empty_rel == pkg_name or empty_rel.startswith(pkg_prefix):
                raise fail(
                    f"skills/{empty_rel}: empty directory inside locked "
                    "vendored package"
                )

        for rel_file, entry in locked_by_rel.items():
            full_path, st = disk_by_rel[rel_file]
            disk_mode = "100755" if (st.st_mode & 0o111) else "100644"
            if disk_mode != entry["mode"]:
                raise fail(
                    f"skills/{pkg_name}/{rel_file}: on-disk mode {disk_mode} "
                    f"does not match locked mode {entry['mode']}"
                )
            raw_bytes = full_path.read_bytes()
            if len(raw_bytes) != entry["bytes"]:
                raise fail(
                    f"skills/{pkg_name}/{rel_file}: byte count "
                    f"{len(raw_bytes)} does not match locked bytes "
                    f"{entry['bytes']}"
                )
            digest = hashlib.sha256(raw_bytes).hexdigest()
            if digest != entry["sha256"]:
                raise fail(
                    f"skills/{pkg_name}/{rel_file}: sha256 {digest} "
                    f"does not match locked sha256 {entry['sha256']}"
                )

        if git_modes is not None:
            git_pkg_prefix = f"skills/{pkg_name}/"
            tracked_by_rel = {
                path[len(git_pkg_prefix) :]: mode
                for path, mode in git_modes.items()
                if path.startswith(git_pkg_prefix)
            }
            if lock_is_tracked:
                untracked = sorted(
                    set(locked_by_rel.keys()) - set(tracked_by_rel.keys())
                )
                if untracked:
                    raise fail(
                        f"{pkg_ctx}: locked file(s) not tracked in Git: "
                        f"{untracked}"
                    )
                extra_tracked = sorted(
                    set(tracked_by_rel.keys()) - set(locked_by_rel.keys())
                )
                if extra_tracked:
                    raise fail(
                        f"{pkg_ctx}: unexpected Git-tracked file(s): "
                        f"{extra_tracked}"
                    )
            for rel_file, git_mode in tracked_by_rel.items():
                if (
                    rel_file in locked_by_rel
                    and git_mode != locked_by_rel[rel_file]["mode"]
                ):
                    expected_mode = locked_by_rel[rel_file]["mode"]
                    raise fail(
                        f"skills/{pkg_name}/{rel_file}: Git index mode "
                        f"{git_mode} does not match locked mode {expected_mode}"
                    )

    return set(packages.keys())


def validate_skill_tree(
    repo_root: Path,
    skills_root: Path,
    files_map: Dict[str, Tuple[Path, os.stat_result]],
    empty_dirs: Sequence[str],
    *,
    allowed_top_files: Set[str],
    git_modes: Optional[Dict[str, str]],
    slug_cache: Dict[Path, Set[str]],
    require_readme: bool = True,
) -> Set[str]:
    """Validate skill dirs, `SKILL.md` frontmatter, containment, and links."""
    root_rel = skills_root.relative_to(repo_root).as_posix()
    if empty_dirs:
        raise fail(
            f"{root_rel}: empty directory is not allowed: {empty_dirs[0]}"
        )

    if require_readme and "README.md" not in files_map:
        raise fail(f"{root_rel}: missing README.md")

    skill_dirs: Set[str] = set()
    for entry in sorted(os.scandir(skills_root), key=lambda e: e.name):
        st = entry.stat(follow_symlinks=False)
        if stat.S_ISDIR(st.st_mode):
            if not SKILL_NAME_RE.match(entry.name):
                raise fail(
                    f"{root_rel}/{entry.name}: invalid skill directory name"
                )
            skill_dirs.add(entry.name)
        elif stat.S_ISREG(st.st_mode):
            if entry.name not in allowed_top_files:
                raise fail(
                    f"{root_rel}/{entry.name}: unexpected top-level file"
                )
            if st.st_mode & 0o111:
                raise fail(
                    f"{root_rel}/{entry.name}: top-level file must not be "
                    "executable"
                )

    if not skill_dirs:
        raise fail(f"{root_rel}: expected at least one skill directory")

    md_bodies: List[Tuple[Path, str]] = []

    for rel_posix, (full_path, st) in sorted(files_map.items()):
        repo_rel = f"{root_rel}/{rel_posix}"
        raw_bytes = full_path.read_bytes()
        text = decode_clean_utf8(raw_bytes, repo_rel)

        if (
            full_path.suffix.lower() not in SKILL_DOCUMENT_SUFFIXES
            or text.startswith("#!")
            or st.st_mode & 0o111
        ):
            raise fail(
                f"{repo_rel}: only non-executable documentation and data "
                "files are allowed in skill directories"
            )
        if git_modes is not None and git_modes.get(repo_rel) == "100755":
            raise fail(f"{repo_rel}: executable Git mode 100755 is forbidden")

        if full_path.suffix.lower() == ".md":
            slug_cache[full_path] = github_heading_slugs(text, repo_rel)
            parts = PurePosixPath(rel_posix).parts
            if len(parts) == 2 and parts[1] == "SKILL.md":
                if st.st_mode & 0o111:
                    raise fail(f"{repo_rel}: SKILL.md must not be executable")
                skill_name = parts[0]
                fields, body = parse_frontmatter(text, repo_rel)
                fm_name = fields.get("name", "")
                if not SKILL_NAME_RE.match(fm_name):
                    raise fail(
                        f"{repo_rel}: frontmatter name {fm_name!r} must match "
                        f"{SKILL_NAME_RE.pattern}"
                    )
                if fm_name != skill_name:
                    raise fail(
                        f"{repo_rel}: frontmatter name {fm_name!r} does not "
                        f"match directory {skill_name!r}"
                    )
                fm_desc = fields.get("description", "").strip()
                if not fm_desc:
                    raise fail(
                        f"{repo_rel}: frontmatter description must be non-empty"
                    )
                line_count = len(text.splitlines())
                max_lines = GRANDFATHERED_SKILL_LINE_CAPS.get(
                    repo_rel, MAX_SKILL_LINES
                )
                if line_count > max_lines:
                    raise fail(
                        f"{repo_rel}: SKILL.md has {line_count} lines, "
                        f"exceeding limit of {max_lines}"
                    )
                md_bodies.append((full_path, body))
            else:
                md_bodies.append((full_path, text))

    for skill_name in sorted(skill_dirs):
        if f"{skill_name}/SKILL.md" not in files_map:
            raise fail(f"{root_rel}/{skill_name}: missing SKILL.md")

    for md_path, body in md_bodies:
        validate_markdown_links(repo_root, md_path, body, slug_cache)

    return skill_dirs


def validate_anneal_skills_json(repo_root: Path) -> None:
    """Validate `anneal/.agents/skills.json` structure and resolved paths."""
    cfg_rel = "anneal/.agents/skills.json"
    cfg_path = repo_root / cfg_rel
    assert_symlink_free_within_repo(repo_root, cfg_path, cfg_rel)
    st = cfg_path.lstat()
    if not stat.S_ISREG(st.st_mode):
        raise fail(f"{cfg_rel}: expected regular file")
    if st.st_mode & 0o111:
        raise fail(f"{cfg_rel}: config file must not be executable")

    text = decode_clean_utf8(cfg_path.read_bytes(), cfg_rel)
    data = load_strict_json(text, cfg_rel)
    if not isinstance(data, dict) or set(data.keys()) != {"entries"}:
        raise fail(f"{cfg_rel}: top-level keys must be exact {{'entries'}}")
    entries = data["entries"]
    if not isinstance(entries, list) or not entries:
        raise fail(f"{cfg_rel}: 'entries' must be a non-empty list")

    resolved_dirs: List[Path] = []
    for idx, item in enumerate(entries):
        ctx = f"{cfg_rel} entries[{idx}]"
        if not isinstance(item, dict) or set(item.keys()) != {"path"}:
            raise fail(f"{ctx}: entry must have exact key {{'path'}}")
        raw_path = item["path"]
        if (
            not isinstance(raw_path, str)
            or not raw_path
            or raw_path.startswith("/")
            or "\\" in raw_path
        ):
            raise fail(f"{ctx}: invalid relative path {raw_path!r}")
        if any(
            unicodedata.category(ch) in FORBIDDEN_UNICODE_CATEGORIES
            for ch in raw_path
        ):
            raise fail(f"{ctx}: control/bidi char in path {raw_path!r}")
        resolved_target = resolve_relative_within_repo(
            repo_root, cfg_path.parent, raw_path, ctx
        )
        target_st = resolved_target.lstat()
        if not stat.S_ISDIR(target_st.st_mode):
            raise fail(f"{ctx}: resolved path is not a directory: {raw_path!r}")
        if resolved_target in resolved_dirs:
            raise fail(
                f"{ctx}: duplicate resolved skill directory {raw_path!r}"
            )
        resolved_dirs.append(resolved_target)

    expected = [
        repo_root / "anneal" / "skills",
        repo_root / "anneal" / "trusted" / "cargo-anneal" / "skills",
        repo_root / "skills",
    ]
    if resolved_dirs != expected:
        got_rels = [p.relative_to(repo_root).as_posix() for p in resolved_dirs]
        exp_rels = [p.relative_to(repo_root).as_posix() for p in expected]
        raise fail(
            f"{cfg_rel}: expected resolved skill directories {exp_rels}, "
            f"got {got_rels}"
        )


def check_repository(repo_root: Path) -> None:
    """Run all skill, provenance lockfile, link, and discovery checks."""
    resolved_root = repo_root.resolve()
    skills_dir = resolved_root / "skills"
    anneal_skills_dir = resolved_root / "anneal" / "skills"
    cargo_anneal_skills_dir = (
        resolved_root / "anneal" / "trusted" / "cargo-anneal" / "skills"
    )

    root_files, root_empty_dirs = scan_tree(resolved_root, skills_dir)
    anneal_files, anneal_empty_dirs = scan_tree(
        resolved_root, anneal_skills_dir
    )
    cargo_anneal_files, cargo_anneal_empty_dirs = scan_tree(
        resolved_root, cargo_anneal_skills_dir
    )
    git_modes = query_git_stage_modes(
        resolved_root,
        ["skills", "anneal/skills", "anneal/trusted/cargo-anneal/skills"],
    )

    locked_skills = validate_vendor_lock(
        resolved_root, skills_dir, root_files, root_empty_dirs, git_modes
    )

    slug_cache: Dict[Path, Set[str]] = {}
    root_skill_names = validate_skill_tree(
        resolved_root,
        skills_dir,
        root_files,
        root_empty_dirs,
        allowed_top_files={"README.md", "vendor-lock.json"},
        git_modes=git_modes,
        slug_cache=slug_cache,
    )
    anneal_skill_names = validate_skill_tree(
        resolved_root,
        anneal_skills_dir,
        anneal_files,
        anneal_empty_dirs,
        allowed_top_files={"README.md"},
        git_modes=git_modes,
        slug_cache=slug_cache,
    )
    cargo_anneal_skill_names = validate_skill_tree(
        resolved_root,
        cargo_anneal_skills_dir,
        cargo_anneal_files,
        cargo_anneal_empty_dirs,
        allowed_top_files=set(),
        git_modes=git_modes,
        slug_cache=slug_cache,
        require_readme=False,
    )

    missing_locks = sorted(root_skill_names - REPO_OWNED_ROOT_SKILLS - locked_skills)
    if missing_locks:
        raise fail(
            f"skills/vendor-lock.json: unlocked skill directories: {missing_locks}"
        )
    owned_with_locks = sorted(REPO_OWNED_ROOT_SKILLS & locked_skills)
    if owned_with_locks:
        raise fail(
            f"skills/vendor-lock.json: repository-owned skills are locked: {owned_with_locks}"
        )

    skill_roots = (
        ("skills/", root_skill_names),
        ("anneal/skills/", anneal_skill_names),
        ("anneal/trusted/cargo-anneal/skills/", cargo_anneal_skill_names),
    )
    for idx, (label_a, names_a) in enumerate(skill_roots):
        for label_b, names_b in skill_roots[idx + 1 :]:
            overlap = sorted(names_a & names_b)
            if overlap:
                raise fail(
                    f"duplicate skill name(s) across {label_a} and "
                    f"{label_b}: {overlap}"
                )

    validate_anneal_skills_json(resolved_root)
    validate_agents_docs(resolved_root, slug_cache)
    validate_proof_scaling_sync(
        resolved_root, anneal_skill_names, cargo_anneal_skill_names
    )


def _extract_marked_block(text: str, label: str, repo_rel: str) -> str:
    begin = f"<!-- {label}:begin -->"
    end = f"<!-- {label}:end -->"
    if text.count(begin) != 1 or text.count(end) != 1:
        raise fail(
            f"{repo_rel}: expected exactly one {begin!r} and {end!r} marker"
        )
    start = text.find(begin)
    stop = text.find(end)
    if stop < start + len(begin):
        raise fail(f"{repo_rel}: {end!r} appears before {begin!r}")
    return text[start + len(begin) : stop]


LEAN_NAME_TOKEN_RE = re.compile(
    r"`+((?:[A-Za-z0-9_]+|«[^»]+»)(?:\.(?:[A-Za-z0-9_]+|«[^»]+»))*)"
)


ALLOWED_THEORY_TACTIC_START_RE = re.compile(
    r"\bdef\s+allowedTheoryTacticKinds\s*:\s*List\s+Name\s*:=\s*\["
)


def _strip_lean_comments(text: str, tb_rel: str) -> str:
    """Replace Lean `--` and nested `/- ... -/` comments with spaces, preserving newlines."""
    out: List[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    in_guillemet = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
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
            i += 1
            continue
        if in_guillemet:
            out.append(ch)
            if ch == "»":
                in_guillemet = False
            i += 1
            continue
        if ch == "-" and nxt == "-":
            out.extend((" ", " "))
            i += 2
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        if ch == '"':
            in_string = True
        elif ch == "'" and (
            i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_?!")
        ):
            # Lex Lean Char literals like `'"'` or `'\''` without confusing `rfl'`.
            if nxt == "\\" and i + 3 < n and text[i + 3] == "'":
                out.extend(text[i : i + 4])
                i += 4
                continue
            if nxt not in ("", "\n") and i + 2 < n and text[i + 2] == "'":
                out.extend(text[i : i + 3])
                i += 3
                continue
        elif ch == "«":
            in_guillemet = True
        out.append(ch)
        i += 1
    if block_depth != 0:
        raise fail(f"{tb_rel}: unterminated Lean block comment")
    return "".join(out)


def parse_allowed_theory_tactics(tb_path: Path, tb_rel: str) -> Set[str]:
    """Parse `allowedTheoryTacticKinds` from `TrustedBoundary.lean`."""
    tb_text = _strip_lean_comments(
        decode_clean_utf8(tb_path.read_bytes(), tb_rel), tb_rel
    )
    match = ALLOWED_THEORY_TACTIC_START_RE.search(tb_text)
    if match is None:
        raise fail(f"{tb_rel}: missing def allowedTheoryTacticKinds")
    body_start = match.end()
    body_end = tb_text.find("]", body_start)
    if body_end == -1:
        raise fail(f"{tb_rel}: unterminated allowedTheoryTacticKinds list")
    raw_block = tb_text[body_start:body_end]
    leftover = LEAN_NAME_TOKEN_RE.sub("", raw_block).replace(",", "").strip()
    if leftover:
        raise fail(
            f"{tb_rel}: unparsed token(s) in allowedTheoryTacticKinds: {leftover!r}"
        )
    tokens: Set[str] = set()
    for kind in LEAN_NAME_TOKEN_RE.findall(raw_block):
        if kind not in THEORY_TACTIC_KIND_TO_TOKEN:
            raise fail(
                f"{tb_rel}: unmapped allowedTheoryTacticKinds entry {kind!r}; "
                "update THEORY_TACTIC_KIND_TO_TOKEN in ci/check_skills.py"
            )
        mapped = THEORY_TACTIC_KIND_TO_TOKEN[kind]
        if mapped is not None:
            tokens.add(mapped)
    if not tokens:
        raise fail(f"{tb_rel}: parsed empty allowedTheoryTacticKinds set")
    return tokens


def load_bundled_anneal_modules(
    repo_root: Path, manifest_path: Path, rel: str
) -> Set[str]:
    """Load `Anneal.*` module names from `theory/bundle-manifest.json`."""
    data = load_strict_json(decode_clean_utf8(manifest_path.read_bytes(), rel), rel)
    if not isinstance(data, dict) or not isinstance(data.get("modules"), list):
        raise fail(f"{rel}: expected JSON object with 'modules' list")
    modules: Set[str] = set()
    for entry in data["modules"]:
        if not isinstance(entry, dict) or not isinstance(entry.get("path"), str):
            raise fail(f"{rel}: malformed module entry {entry!r}")
        raw_path = entry["path"]
        posix_path = check_safe_path_string(raw_path, f"{rel}: module path")
        posix_str = posix_path.as_posix()
        if not posix_str.startswith("theory/") or not posix_str.endswith(".lean"):
            raise fail(f"{rel}: unexpected module path {raw_path!r}")
        mod_rel = f"anneal/{posix_str}"
        mod_path = repo_root / mod_rel
        if not (mod_path.exists() or mod_path.is_symlink()):
            raise fail(f"{rel}: bundled module file missing at {mod_rel}")
        assert_symlink_free_within_repo(repo_root, mod_path, mod_rel)
        if not mod_path.is_file():
            raise fail(f"{rel}: bundled module path is not a file: {mod_rel}")
        mod = posix_str[len("theory/") : -len(".lean")].replace("/", ".")
        modules.add(mod)
    return modules


def validate_agents_docs(repo_root: Path, slug_cache: Dict[Path, Set[str]]) -> None:
    """Validate root/subtree `AGENTS.md` links, overrides, and Codex size budget."""
    for rel_agents in ("AGENTS.md", "zerocopy/AGENTS.md", "anneal/AGENTS.md"):
        agents_path = repo_root / rel_agents
        if agents_path.exists() or agents_path.is_symlink():
            assert_symlink_free_within_repo(repo_root, agents_path, rel_agents)
            agents_text = decode_clean_utf8(agents_path.read_bytes(), rel_agents)
            slug_cache[agents_path] = github_heading_slugs(agents_text, rel_agents)
            validate_markdown_links(repo_root, agents_path, agents_text, slug_cache)

    anneal_dir = repo_root / "anneal"
    anneal_agents_paths: List[Path] = []
    if anneal_dir.exists() or anneal_dir.is_symlink():
        assert_symlink_free_within_repo(repo_root, anneal_dir, "anneal")
        for dirpath, dirnames, filenames in os.walk(anneal_dir, followlinks=False):
            cur = Path(dirpath)
            kept_dirs: List[str] = []
            for d in sorted(dirnames):
                sub = cur / d
                rel_sub = sub.relative_to(repo_root).as_posix()
                if d in AGENTS_SCAN_PRUNE_DIRS:
                    if sub.is_symlink():
                        assert_symlink_free_within_repo(repo_root, sub, rel_sub)
                    continue
                assert_symlink_free_within_repo(repo_root, sub, rel_sub)
                kept_dirs.append(d)
            dirnames[:] = kept_dirs
            for name in sorted(filenames):
                if name == "AGENTS.override.md":
                    rel = (cur / name).relative_to(repo_root).as_posix()
                    raise fail(
                        f"{rel}: AGENTS.override.md is forbidden under anneal/"
                    )
                if name == "AGENTS.md":
                    p = cur / name
                    rel = p.relative_to(repo_root).as_posix()
                    assert_symlink_free_within_repo(repo_root, p, rel)
                    anneal_agents_paths.append(p)

    root_override = repo_root / "AGENTS.override.md"
    if root_override.exists() or root_override.is_symlink():
        raise fail("AGENTS.override.md: repository-root override is forbidden")

    root_agents = repo_root / "AGENTS.md"
    if not (root_agents.exists() or anneal_agents_paths):
        return

    total_bytes = 0
    if root_agents.exists():
        total_bytes += root_agents.lstat().st_size
    for p in anneal_agents_paths:
        total_bytes += p.lstat().st_size
    if total_bytes >= CODEX_AGENTS_MD_BUDGET_BYTES:
        raise fail(
            f"combined AGENTS.md size {total_bytes} B reaches or exceeds "
            f"Codex budget of {CODEX_AGENTS_MD_BUDGET_BYTES} B"
        )


def validate_proof_scaling_sync(
    repo_root: Path,
    anneal_skill_names: Set[str],
    cargo_anneal_skill_names: Set[str],
) -> None:
    """Keep `proof-scaling` & `cargo-anneal` synced with `TrustedBoundary.lean` and `bundle-manifest.json`."""
    tb_rel = "anneal/trusted/audit/TrustedBoundary.lean"
    manifest_rel = "anneal/theory/bundle-manifest.json"
    tb_path = repo_root / tb_rel
    manifest_path = repo_root / manifest_rel

    bundled_modules: Optional[Set[str]] = None
    if manifest_path.exists() or manifest_path.is_symlink():
        assert_symlink_free_within_repo(repo_root, manifest_path, manifest_rel)
        bundled_modules = load_bundled_anneal_modules(
            repo_root, manifest_path, manifest_rel
        )

    if "cargo-anneal" in cargo_anneal_skill_names:
        ca_rel = "anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md"
        ca_text = decode_clean_utf8((repo_root / ca_rel).read_bytes(), ca_rel)
        ca_mods = sorted(set(ANNEAL_MODULE_RE.findall(ca_text)))
        if ca_mods and bundled_modules is None:
            raise fail(f"{ca_rel}: missing {manifest_rel} to verify bundled modules")
        for mod in ca_mods:
            if mod not in bundled_modules:
                raise fail(
                    f"{ca_rel}: cited {mod!r} is missing from {manifest_rel}"
                )

    if "proof-scaling" not in anneal_skill_names:
        return

    ps_rel = "anneal/skills/proof-scaling/SKILL.md"
    ps_text = decode_clean_utf8((repo_root / ps_rel).read_bytes(), ps_rel)

    if not (tb_path.exists() or tb_path.is_symlink()):
        raise fail(f"{ps_rel}: missing {tb_rel} to verify Pass-1 tactics")
    assert_symlink_free_within_repo(repo_root, tb_path, tb_rel)
    expected_tactics = parse_allowed_theory_tactics(tb_path, tb_rel)
    tactic_block = _extract_marked_block(ps_text, "pass1-tactic-allowlist", ps_rel)
    skill_tactics = set(BACKTICK_TOKEN_RE.findall(tactic_block))
    missing = sorted(expected_tactics - skill_tactics)
    extra = sorted(skill_tactics - expected_tactics)
    if missing or extra:
        raise fail(
            f"{ps_rel}: Pass-1 tactic allowlist out of sync with {tb_rel} "
            f"(missing={missing}, extra={extra})"
        )

    if bundled_modules is None:
        raise fail(f"{ps_rel}: missing {manifest_rel} to verify bundled modules")
    bundled_block = _extract_marked_block(ps_text, "pass1-bundled-modules", ps_rel)
    block_mods = set(ANNEAL_MODULE_RE.findall(bundled_block))
    if not block_mods:
        raise fail(f"{ps_rel}: pass1-bundled-modules block cites no Anneal.* modules")
    bad_bundled = sorted(block_mods - bundled_modules)
    if bad_bundled:
        raise fail(
            f"{ps_rel}: bundled modules missing from {manifest_rel}: {bad_bundled}"
        )
    for mod in sorted(set(ANNEAL_MODULE_RE.findall(ps_text))):
        if mod in bundled_modules:
            continue
        mod_rel = f"anneal/theory/{mod.replace('.', '/')}.lean"
        mod_path = repo_root / mod_rel
        if not (mod_path.exists() or mod_path.is_symlink()):
            raise fail(f"{ps_rel}: cited {mod!r} missing at {mod_rel}")
        assert_symlink_free_within_repo(repo_root, mod_path, mod_rel)
        if not mod_path.is_file():
            raise fail(f"{ps_rel}: cited {mod!r} missing at {mod_rel}")


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to the repository root (defaults to parent of ci/).",
    )
    args = parser.parse_args(argv)
    try:
        check_repository(args.repo_root)
    except SkillCheckError as exc:
        print(f"check_skills.py: error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
