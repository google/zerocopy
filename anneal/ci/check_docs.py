# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate, verify, and build Anneal's public-facing mdBook documentation.

This script enforces the anti-bitrot and containment invariants for
`anneal/book/`:

1. Closed, exact-case file-type allowlist under `anneal/book/`: Only
   `book.toml`, lowercase `.md` files under `book/src/`, and pure example
   artifacts (`case.json`, `.txt`, `.rs`, `.lock`, never `cargo.toml`/
   `cargo.lock`) under `book/examples/` are permitted. Scripts, Cargo
   manifests, Lean files, themes, templates, SVGs, and raw HTML files are
   rejected by default.
2. Default-deny inline code fences and post-build HTML parity: Markdown files
   under `book/src/` may not contain raw `rust`, `rs`, `sh`, `bash`, `shell`,
   `zsh`, or `console` fenced code blocks. Every `{{#include ...}}` /
   `{{#rustdoc_include ...}}` directive must live inside a checked fence and
   target a registered verified artifact of a `case.json` under
   `book/examples/`. All other unescaped `{{#...}}` directives are rejected.
   After `mdbook build`, every rendered `<pre><code class="language-*">` block
   in authored chapters is also verified against the exact verified artifact
   texts, structurally closing CommonMark parser-desync bypasses.
3. Fail-closed anchor and hidden-spec checks: `mdbook v0.5.4` silently exits 0
   with an empty code block on missing `{{#include file:anchor}}` anchors. This
   script parses every include directive itself and rejects missing files,
   symlinks, path escapes, invalid or empty line ranges/anchors, and hidden
   `unsafe` or Anneal specification lines in anchored Rust examples.
4. Closed non-executing `book/book.toml` and HTML/script hygiene: Requires
   canonical `site-url = "/zerocopy/anneal/"`, restricts themes to mdBook's
   built-in themes, forbids `[preprocessor.*]` and custom `[output.*]`, rejects
   raw HTML tags outside comments/code in `book/src/*.md`, enforces exactly one
   `<main>...</main>` pair per rendered HTML page, rejects duplicate HTML
   attributes, disallowed tags (`script`, `iframe`, `svg`, `base`, `meta`,
   `link`, `form`, `object`, `embed`, `style`, `math`, `template`), `on*`
   handlers, and non-HTTP/mailto URL schemes on all URL-bearing attributes.
5. Closed CLI `argv` allowlist, single-sourced governing docs, and link checks:
   Restricts `case.json` `argv` to safe non-network/non-build `cargo-anneal`
   invocations (requiring explicit sandboxing before crate-building subcommands
   are admitted), verifies `display_command` matches `argv`, stages
   `PRINCIPLES.md`, `THREAT_MODEL.md`, and `META_PRINCIPLES.md` from `anneal/`
   with checked relative-link rewrites, and verifies built HTML links/anchors.
"""

from __future__ import annotations

import argparse
import difflib
import hashlib
import html
from html.parser import HTMLParser
import http.client
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import tomllib
from urllib.error import URLError
from urllib.parse import unquote, urlsplit
import urllib.request


MDBOOK_VERSION = "0.5.4"
MDBOOK_TARGET = "x86_64-unknown-linux-musl"
MDBOOK_URL = (
    f"https://github.com/rust-lang/mdBook/releases/download/"
    f"v{MDBOOK_VERSION}/mdbook-v{MDBOOK_VERSION}-{MDBOOK_TARGET}.tar.gz"
)
MDBOOK_SHA256 = (
    "5222beabd3e37dc5be0d18ff99b79058469354db5c220153a1b92db5ba12be89"
)
MDBOOK_BIN_SHA256 = (
    "ef05511c54795f5641c94017495b9e61df9a95652cd7f6e301a135e6e7e7dd9e"
)

SITE_URL_PREFIX = "/zerocopy/anneal/"
GITHUB_ZEROCOPY_PREFIX = "https://github.com/google/zerocopy/"
GITHUB_ANNEAL_BLOB_BASE = (
    "https://github.com/google/zerocopy/blob/main/anneal/"
)

ALLOWED_BOOK_TOML_SECTIONS = frozenset({"book", "output"})
ALLOWED_BOOK_KEYS = frozenset(
    {"title", "description", "authors", "language", "src"}
)
ALLOWED_OUTPUT_SECTIONS = frozenset({"html"})
ALLOWED_OUTPUT_HTML_KEYS = frozenset(
    {
        "site-url",
        "git-repository-url",
        "default-theme",
        "preferred-dark-theme",
        "no-section-label",
    }
)
ALLOWED_MDBOOK_THEMES = frozenset({"light", "rust", "coal", "navy", "ayu"})

# Closed exact-case file-extension allowlist under `anneal/book/examples/`.
ALLOWED_EXAMPLE_SUFFIXES = frozenset({".json", ".txt", ".rs", ".lock"})

CHECKED_FENCE_LANGS = frozenset(
    {"rust", "rs", "sh", "bash", "shell", "zsh", "console"}
)
STRICT_CHAPTER_DIRS = frozenset({"getting-started", "guides", "reference"})

GOVERNING_DOCS = (
    ("PRINCIPLES.md", "foundations/principles.md"),
    ("THREAT_MODEL.md", "foundations/threat-model.md"),
    ("META_PRINCIPLES.md", "foundations/meta-principles.md"),
)

GOVERNING_LINK_REWRITES = {
    "PRINCIPLES.md": "principles.md",
    "THREAT_MODEL.md": "threat-model.md",
    "META_PRINCIPLES.md": "meta-principles.md",
    "docs/design.md": f"{GITHUB_ANNEAL_BLOB_BASE}docs/design.md",
    "docs/architecture.md": f"{GITHUB_ANNEAL_BLOB_BASE}docs/architecture.md",
    "docs/trust-model.md": f"{GITHUB_ANNEAL_BLOB_BASE}docs/trust-model.md",
    "docs/README.md": f"{GITHUB_ANNEAL_BLOB_BASE}docs/README.md",
}

STRICT_INCLUDE_RE = re.compile(
    r"^\{\{#(?P<kind>include|rustdoc_include)\s+(?P<spec>[^}\s\"']+)\}\}$"
)
ANY_DIRECTIVE_RE = re.compile(r"(?<!\\)\{\{#(?P<body>[^}]*)(?P<close>\}\})?")
FENCE_OPEN_RE = re.compile(
    r"^(?P<prefix>(?:[ ]{0,3}>[ ]?)*)(?P<list>(?:[ ]{0,3}(?:[-+*]|\d{1,9}[.)])[ \t]+)?)"
    r"(?P<indent>[ ]{0,3})(?P<fence>`{3,}|~{3,})(?P<info>.*)$"
)
# Any unparsed fence-like sequence outside a recognized fence block (e.g.
# nested containers such as `- > ```rust` or indented 4+ space fences).
STRAY_FENCE_RE = re.compile(r"^\s*(?:>\s*)*(?:(?:[-+*]|\d+[.)])\s+)*(?:`{3,}|~{3,})")
ANCHOR_START_RE = re.compile(r"ANCHOR:\s*([A-Za-z0-9_-]+)\b")
ANCHOR_END_RE = re.compile(r"ANCHOR_END:\s*([A-Za-z0-9_-]+)\b")
MD_LINK_RE = re.compile(r"(?<!!)\[[^\]]*\]\((?P<target>[^)\s]+)(?:\s+\"[^\"]*\")?\)", re.DOTALL)
LOAD_BEARING_RUST_RE = re.compile(
    r"\bunsafe\b|anneal:|#!\[anneal::|#\[anneal::|(?:///|//!)\s*```anneal\b"
)
HTML_COMMENT_RE = re.compile(r"<!--.*?-->", re.DOTALL)
RAW_HTML_TAG_RE = re.compile(r"<(?:[A-Za-z/!])")
UNSAFE_SCHEME_RE = re.compile(r"\b(?:javascript|data|vbscript)\s*:", re.IGNORECASE)

DISALLOWED_MAIN_HTML_TAGS = frozenset(
    {
        "script",
        "iframe",
        "svg",
        "base",
        "meta",
        "link",
        "form",
        "object",
        "embed",
        "style",
        "math",
        "template",
    }
)
URL_ATTRS = frozenset(
    {"href", "src", "action", "formaction", "xlink:href", "srcdoc", "data"}
)


class DocError(Exception):
    """Raised when a documentation check, example verification, or build fails."""


def _is_within(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def _has_symlink_component(path: Path, stop_at: Path) -> bool:
    """Return True if `path` or any ancestor below `stop_at` is a symlink."""
    stop_resolved = stop_at.resolve()
    cur = path
    while True:
        if cur.is_symlink():
            return True
        if cur == stop_resolved or cur == cur.parent:
            break
        try:
            if cur.resolve() == stop_resolved:
                break
        except OSError:
            return True
        cur = cur.parent
    return False


def _ensure_no_symlinks_under(root: Path, label: str, errors: list[str]) -> None:
    if not root.exists():
        errors.append(f"{label}: directory does not exist: {root}")
        return
    if root.is_symlink():
        errors.append(f"{label}: root directory is a symlink: {root}")
        return
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        current = Path(dirpath)
        for name in list(dirnames) + list(filenames):
            candidate = current / name
            if candidate.is_symlink():
                errors.append(f"{label}: symlink is not allowed: {candidate}")


def _strip_quote_prefix(line: str, quote_depth: int) -> str | None:
    """Strip `quote_depth` leading blockquote `>` markers from `line`."""
    rest = line
    for _ in range(quote_depth):
        stripped = rest.lstrip(" ")
        if not stripped.startswith(">"):
            return None
        rest = stripped[1:]
        if rest.startswith(" "):
            rest = rest[1:]
    return rest


def parse_fences(text: str) -> list[dict]:
    """Return all CommonMark fenced code blocks in Markdown `text`."""
    fences: list[dict] = []
    lines = text.splitlines()
    in_fence = False
    fence_char = ""
    fence_len = 0
    fence_info = ""
    fence_start = 0
    quote_depth = 0
    min_close_indent = 0
    max_close_indent = 3
    body_lines: list[tuple[int, str]] = []

    idx = 0
    while idx < len(lines):
        lineno = idx + 1
        line = lines[idx]
        if not in_fence:
            match = FENCE_OPEN_RE.match(line)
            if match:
                fence = match.group("fence")
                info = match.group("info").strip()
                if fence[0] == "`" and "`" in info:
                    idx += 1
                    continue
                in_fence = True
                fence_char = fence[0]
                fence_len = len(fence)
                fence_info = info
                fence_start = lineno
                quote_depth = match.group("prefix").count(">")
                list_prefix = match.group("list")
                if list_prefix:
                    min_close_indent = len(list_prefix)
                    max_close_indent = len(list_prefix) + 3
                else:
                    min_close_indent = 0
                    max_close_indent = 3
                body_lines = []
            idx += 1
        else:
            inner = _strip_quote_prefix(line, quote_depth)
            if inner is None:
                fences.append(
                    {
                        "start_line": fence_start,
                        "end_line": lineno - 1,
                        "info": fence_info,
                        "body": body_lines,
                        "unclosed": True,
                    }
                )
                in_fence = False
                # Re-process this line outside the exited blockquote.
                continue
            stripped = inner.lstrip(" ")
            indent = len(inner) - len(stripped)
            if stripped and indent < min_close_indent:
                # Exiting a list item terminates its fence immediately;
                # re-process the current line at top level.
                fences.append(
                    {
                        "start_line": fence_start,
                        "end_line": lineno - 1,
                        "info": fence_info,
                        "body": body_lines,
                        "unclosed": True,
                    }
                )
                in_fence = False
                continue
            if (
                min_close_indent <= indent <= max_close_indent
                and stripped
                and set(stripped.rstrip()) == {fence_char}
                and len(stripped.rstrip()) >= fence_len
            ):
                fences.append(
                    {
                        "start_line": fence_start,
                        "end_line": lineno,
                        "info": fence_info,
                        "body": body_lines,
                    }
                )
                in_fence = False
            else:
                body_lines.append((lineno, inner))
            idx += 1

    if in_fence:
        fences.append(
            {
                "start_line": fence_start,
                "end_line": len(lines),
                "info": fence_info,
                "body": body_lines,
                "unclosed": True,
            }
        )
    return fences


def _parse_fence_tokens(info: str) -> set[str]:
    """Return lowercase tokens from a fence info string (entity & backslash unescaped)."""
    if not info:
        return set()
    # Unescape CommonMark ASCII punctuation escapes (`\,`, `\\`, etc.) and HTML
    # character references so `rust\,no_run` or `&#114;ust` cannot evade checks.
    unescaped = re.sub(r"\\([!-/:-@\[-`{-~])", r"\1", html.unescape(info))
    tokens: set[str] = set()
    for part in re.split(r"[\s,]+", unescaped.strip()):
        if part:
            tokens.add(part.lower())
    return tokens


def _parse_include_spec(
    spec: str,
) -> tuple[str, str | None, tuple[int | None, int | None] | None]:
    """Parse `<path>`, `<path>:<anchor>`, or `<path>:<start>:<end>`."""
    parts = spec.split(":")
    if len(parts) == 1:
        return parts[0], None, None
    if len(parts) == 2:
        if parts[1].isascii() and parts[1].isdigit():
            line = int(parts[1])
            return parts[0], None, (line, line)
        if not parts[1]:
            raise DocError(f"empty anchor/line specifier: {spec!r}")
        return parts[0], parts[1], None
    if len(parts) == 3:
        for bound in (parts[1], parts[2]):
            if bound and not (bound.isascii() and bound.isdigit()):
                raise DocError(f"non-integer line range in include: {spec!r}")
        start = int(parts[1]) if parts[1] else None
        end = int(parts[2]) if parts[2] else None
        return parts[0], None, (start, end)
    raise DocError(f"malformed include specifier: {spec!r}")


def _extract_anchors(text: str) -> tuple[dict[str, tuple[int, int]], list[str]]:
    """Return `{anchor_name: (start_line_1based, end_line_1based)}` and errors."""
    errors: list[str] = []
    starts: dict[str, int] = {}
    anchors: dict[str, tuple[int, int]] = {}
    for lineno, line in enumerate(text.splitlines(), start=1):
        start_match = ANCHOR_START_RE.search(line)
        if start_match:
            name = start_match.group(1)
            if name in starts or name in anchors:
                errors.append(f"duplicate ANCHOR start `{name}` at line {lineno}")
            else:
                starts[name] = lineno
        end_match = ANCHOR_END_RE.search(line)
        if end_match:
            name = end_match.group(1)
            if name not in starts:
                errors.append(
                    f"ANCHOR_END `{name}` without matching ANCHOR at line {lineno}"
                )
            else:
                start_line = starts.pop(name)
                anchors[name] = (start_line, lineno)
    for name, start_line in sorted(starts.items()):
        errors.append(f"unclosed ANCHOR `{name}` opened at line {start_line}")
    return anchors, errors


def _validate_rust_anchor_coverage(
    rs_path: Path,
    included_ranges: list[tuple[int, int, str]],
    errors: list[str],
) -> None:
    """Reject hidden `unsafe` or Anneal-spec lines outside visible includes."""
    lines = rs_path.read_text(encoding="utf-8").splitlines()
    visible: set[int] = set()
    for start, end, kind in included_ranges:
        for idx in range(start, end + 1):
            if 1 <= idx <= len(lines):
                if kind == "rustdoc_include":
                    stripped = lines[idx - 1].lstrip()
                    if stripped == "#" or stripped.startswith("# "):
                        continue
                visible.add(idx)

    for lineno, line in enumerate(lines, start=1):
        if lineno in visible:
            continue
        stripped = line.strip()
        if not stripped:
            continue
        if (
            stripped.startswith("//")
            and not stripped.startswith(("///", "//!"))
            and "anneal:" not in stripped
        ):
            continue
        if LOAD_BEARING_RUST_RE.search(line):
            errors.append(
                f"{rs_path}:{lineno}: load-bearing Rust/Anneal line is hidden "
                f"outside any visible included anchor: {stripped}"
            )


def _arg_contains_unsafe_path(arg: str) -> bool:
    """Return True if `arg` or its `=`-delimited value escapes relative scope."""
    candidates = [arg]
    if "=" in arg:
        candidates.append(arg.split("=", 1)[1])
    for value in candidates:
        if not value:
            continue
        if (
            value.startswith(("/", "~"))
            or Path(value).is_absolute()
            or ".." in Path(value).parts
        ):
            return True
    return False


def _display_command_matches_argv(display_command: str, argv: list[str]) -> bool:
    """Verify `display_command` matches the executed `cargo-anneal` `argv`."""
    if not display_command.startswith("$ "):
        return False
    try:
        shown = shlex.split(display_command[2:])
    except ValueError:
        return False
    if not shown:
        return False
    if shown[0] == "cargo":
        return len(shown) >= 2 and shown[1] == "anneal" and shown[1:] == argv
    if shown[0] == "cargo-anneal":
        return shown[1:] == argv
    return False


def _validate_cli_argv_allowlist(
    argv: list[str],
    expect_exit: int,
    fresh_cache_env: bool,
    setup_files: dict[str, str],
) -> str | None:
    """Enforce a closed allowlist of safe, offline `cargo-anneal` invocations.

    Rejects bare `setup` (which would attempt remote downloads) and any future
    build/verify subcommand until OS sandboxing (such as `bwrap`) is wired for
    example execution.
    """
    args = argv[1:] if argv and argv[0] == "anneal" else argv
    if args in (
        [],
        ["-h"],
        ["--help"],
        ["-V"],
        ["--version"],
        ["help"],
        ["help", "setup"],
        ["setup", "-h"],
        ["setup", "--help"],
    ):
        return None

    # Allow `setup --local-archive <file>` only against a declared relative
    # setup file inside a fresh cache directory (never touching host state or
    # network).
    if (
        len(args) == 3
        and args[0] == "setup"
        and args[1] == "--local-archive"
        and args[2] in setup_files
        and fresh_cache_env
    ):
        return None

    # Allow explicit argument-parsing negative examples (exit 2) for unknown
    # single-token subcommands (excluding real subcommands such as `setup` or
    # future `verify`).
    if (
        expect_exit == 2
        and len(args) == 1
        and re.fullmatch(r"[a-z][a-z0-9_-]*", args[0]) is not None
        and args[0] not in {"setup", "verify", "help", "check", "build"}
    ):
        return None

    return (
        f"argv {argv!r} is outside the closed offline CLI allowlist; "
        f"sandboxed execution is required before admitting new subcommands"
    )


def _load_example_cases(
    examples_root: Path,
) -> tuple[list[tuple[Path, dict, set[Path]]], list[str]]:
    """Auto-discover and validate all `case.json` manifests under `examples/`."""
    errors: list[str] = []
    cases: list[tuple[Path, dict, set[Path]]] = []
    if not examples_root.exists():
        return cases, [f"examples directory missing: {examples_root}"]
    if examples_root.is_symlink():
        return cases, [f"examples directory may not be a symlink: {examples_root}"]

    case_files = sorted(examples_root.rglob("case.json"))
    if not case_files:
        return cases, [f"no example case.json files found under {examples_root}"]

    allowed_cli_keys = {
        "kind",
        "description",
        "display_command",
        "argv",
        "expect_exit",
        "transcript",
        "setup_files",
        "fresh_cache_env",
        "normalize_tempdir",
    }

    for case_file in case_files:
        if case_file.is_symlink():
            errors.append(f"{case_file}: symlink is not allowed")
            continue
        try:
            data = json.loads(case_file.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            errors.append(f"{case_file}: invalid JSON: {exc}")
            continue
        if not isinstance(data, dict):
            errors.append(f"{case_file}: root JSON value must be an object")
            continue
        kind = data.get("kind")
        if kind != "cli":
            errors.append(f"{case_file}: unsupported example kind: {kind!r}")
            continue

        unknown = set(data.keys()) - allowed_cli_keys
        if unknown:
            errors.append(
                f"{case_file}: unknown fields in cli case: {sorted(unknown)}"
            )
        for req in ("display_command", "argv", "expect_exit", "transcript"):
            if req not in data:
                errors.append(f"{case_file}: missing required field `{req}`")

        argv = data.get("argv")
        argv_ok = isinstance(argv, list) and all(isinstance(a, str) for a in argv)
        if not argv_ok:
            errors.append(f"{case_file}: `argv` must be a list of strings")
        else:
            for arg in argv:
                if _arg_contains_unsafe_path(arg):
                    errors.append(
                        f"{case_file}: `argv` may not contain absolute or "
                        f"parent-traversal paths: {arg!r}"
                    )

        expect_exit = data.get("expect_exit")
        exit_ok = not isinstance(expect_exit, bool) and isinstance(expect_exit, int)
        if not exit_ok:
            errors.append(f"{case_file}: `expect_exit` must be an integer")

        display_command = data.get("display_command")
        if not isinstance(display_command, str) or not display_command.startswith("$ "):
            errors.append(f"{case_file}: `display_command` must start with `$ `")
        elif argv_ok and not _display_command_matches_argv(display_command, argv):
            errors.append(
                f"{case_file}: `display_command` ({display_command!r}) does not "
                f"match `argv` ({argv!r})"
            )

        for bool_field in ("fresh_cache_env", "normalize_tempdir"):
            if bool_field in data and not isinstance(data[bool_field], bool):
                errors.append(f"{case_file}: `{bool_field}` must be a boolean")

        setup_files_clean: dict[str, str] = {}
        if "setup_files" in data:
            setup_files = data["setup_files"]
            if not isinstance(setup_files, dict):
                errors.append(f"{case_file}: `setup_files` must be an object")
            else:
                for rel_name, content in setup_files.items():
                    if not isinstance(rel_name, str) or not isinstance(content, str):
                        errors.append(
                            f"{case_file}: `setup_files` entries must map strings to strings"
                        )
                        continue
                    rel_path = Path(rel_name)
                    if (
                        not rel_name
                        or not rel_path.parts
                        or rel_path.is_absolute()
                        or ".." in rel_path.parts
                    ):
                        errors.append(
                            f"{case_file}: invalid `setup_files` relative path: {rel_name!r}"
                        )
                    else:
                        setup_files_clean[rel_name] = content

        if argv_ok and exit_ok:
            allow_err = _validate_cli_argv_allowlist(
                argv,
                expect_exit,
                data.get("fresh_cache_env") is True,
                setup_files_clean,
            )
            if allow_err is not None:
                errors.append(f"{case_file}: {allow_err}")

        verified_artifacts: set[Path] = set()
        transcript = data.get("transcript")
        if not isinstance(transcript, str) or not transcript:
            errors.append(f"{case_file}: `transcript` must be a relative path")
        else:
            raw_transcript = case_file.parent / transcript
            if _has_symlink_component(raw_transcript, case_file.parent):
                errors.append(f"{case_file}: `transcript` may not traverse symlinks")
            else:
                transcript_path = raw_transcript.resolve()
                if not _is_within(transcript_path, case_file.parent):
                    errors.append(
                        f"{case_file}: `transcript` escapes case directory: {transcript}"
                    )
                elif not transcript_path.is_file():
                    errors.append(
                        f"{case_file}: missing transcript file: {transcript_path}"
                    )
                else:
                    verified_artifacts.add(transcript_path)
        cases.append((case_file, data, verified_artifacts))

    return cases, errors


def _rewrite_governing_doc(
    source_path: Path,
    dest_rel: str,
    anneal_root: Path,
) -> tuple[str, list[str]]:
    """Rewrite root-relative links in a governing doc for staging under book/."""
    text = source_path.read_text(encoding="utf-8")
    errors: list[str] = []

    def replace_link(match: re.Match[str]) -> str:
        raw_target = match.group("target")
        if raw_target.startswith(("http://", "https://", "mailto:", "#")):
            return match.group(0)
        path_part, sep, frag = raw_target.partition("#")
        if path_part in GOVERNING_LINK_REWRITES:
            rewritten = GOVERNING_LINK_REWRITES[path_part]
            if sep:
                rewritten = f"{rewritten}#{frag}"
            return match.group(0).replace(f"({raw_target})", f"({rewritten})", 1)
        errors.append(
            f"{source_path.relative_to(anneal_root)}: unmapped relative link "
            f"`{raw_target}` when staging to `{dest_rel}`; add it to "
            f"GOVERNING_LINK_REWRITES in ci/check_docs.py"
        )
        return match.group(0)

    fences = parse_fences(text)
    fence_ranges = [(f["start_line"], f["end_line"]) for f in fences]
    lines = text.splitlines(keepends=True)

    def line_in_fence(lineno: int) -> bool:
        return any(start <= lineno <= end for start, end in fence_ranges)

    out_chunks: list[str] = []
    prose_buf: list[str] = []

    def flush_prose() -> None:
        if prose_buf:
            out_chunks.append(MD_LINK_RE.sub(replace_link, "".join(prose_buf)))
            prose_buf.clear()

    for lineno, line in enumerate(lines, start=1):
        if line_in_fence(lineno):
            flush_prose()
            out_chunks.append(line)
        else:
            prose_buf.append(line)
    flush_prose()

    return "".join(out_chunks), errors


def _check_book_toml(book_root: Path, anneal_root: Path, errors: list[str]) -> None:
    """Validate `book/book.toml` against a closed non-executing key/value allowlist."""
    toml_path = book_root / "book.toml"
    if toml_path.is_symlink() or not toml_path.is_file():
        errors.append(f"missing book manifest: {toml_path.relative_to(anneal_root)}")
        return
    try:
        config = tomllib.loads(toml_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as exc:
        errors.append(f"book/book.toml: invalid TOML: {exc}")
        return

    unknown_top = set(config.keys()) - ALLOWED_BOOK_TOML_SECTIONS
    if unknown_top:
        errors.append(
            f"book/book.toml: disallowed top-level sections "
            f"(preprocessors and build overrides are forbidden): {sorted(unknown_top)}"
        )

    book_sec = config.get("book")
    if not isinstance(book_sec, dict):
        errors.append("book/book.toml: missing `[book]` table")
    else:
        unknown_book = set(book_sec.keys()) - ALLOWED_BOOK_KEYS
        if unknown_book:
            errors.append(
                f"book/book.toml: disallowed `[book]` keys: {sorted(unknown_book)}"
            )
        src_val = book_sec.get("src", "src")
        if src_val != "src":
            errors.append(
                f'book/book.toml: `[book].src` must be `"src"`, got {src_val!r}'
            )
        for str_key in ("title", "description", "language"):
            if str_key in book_sec and not isinstance(book_sec[str_key], str):
                errors.append(f"book/book.toml: `[book].{str_key}` must be a string")
        if "authors" in book_sec and (
            not isinstance(book_sec["authors"], list)
            or not all(isinstance(a, str) for a in book_sec["authors"])
        ):
            errors.append("book/book.toml: `[book].authors` must be a list of strings")

    output_sec = config.get("output")
    if not isinstance(output_sec, dict):
        errors.append("book/book.toml: missing `[output]` table")
        return
    unknown_out = set(output_sec.keys()) - ALLOWED_OUTPUT_SECTIONS
    if unknown_out:
        errors.append(
            f"book/book.toml: disallowed `[output]` sections: "
            f"{sorted(unknown_out)}"
        )
    html_sec = output_sec.get("html")
    if not isinstance(html_sec, dict):
        errors.append("book/book.toml: missing `[output.html]` table")
        return
    unknown_html = set(html_sec.keys()) - ALLOWED_OUTPUT_HTML_KEYS
    if unknown_html:
        errors.append(
            f"book/book.toml: disallowed `[output.html]` keys: "
            f"{sorted(unknown_html)}"
        )
    if html_sec.get("site-url") != SITE_URL_PREFIX:
        errors.append(
            f"book/book.toml: `[output.html].site-url` must be "
            f"{SITE_URL_PREFIX!r}, got {html_sec.get('site-url')!r}"
        )
    if "git-repository-url" in html_sec:
        repo_url = html_sec["git-repository-url"]
        if not isinstance(repo_url, str) or not repo_url.startswith(
            GITHUB_ZEROCOPY_PREFIX
        ):
            errors.append(
                f"book/book.toml: `[output.html].git-repository-url` "
                f"must start with {GITHUB_ZEROCOPY_PREFIX!r}"
            )
    for theme_key in ("default-theme", "preferred-dark-theme"):
        if theme_key in html_sec and html_sec[theme_key] not in ALLOWED_MDBOOK_THEMES:
            errors.append(
                f"book/book.toml: `[output.html].{theme_key}` must be a built-in "
                f"mdBook theme ({sorted(ALLOWED_MDBOOK_THEMES)}), got "
                f"{html_sec[theme_key]!r}"
            )
    if "no-section-label" in html_sec and not isinstance(
        html_sec["no-section-label"], bool
    ):
        errors.append(
            "book/book.toml: `[output.html].no-section-label` must be a boolean"
        )


def _check_book_file_allowlist(
    book_root: Path, anneal_root: Path, errors: list[str]
) -> None:
    """Enforce a closed, exact-case file-type allowlist across `anneal/book/`."""
    for path in sorted(book_root.rglob("*")):
        rel = path.relative_to(book_root)
        if any(part.startswith(".") for part in rel.parts):
            errors.append(
                f"{path.relative_to(anneal_root)}: hidden file or directory "
                f"is not allowed under anneal/book/"
            )
            continue
        if path.is_dir():
            if rel.parts[0] not in {"src", "examples"}:
                errors.append(
                    f"{path.relative_to(anneal_root)}: disallowed directory "
                    f"under anneal/book/ (only `src/` and `examples/` are permitted)"
                )
            continue
        if not path.is_file():
            continue
        if rel == Path("book.toml"):
            continue
        if rel.parts[0] == "src":
            if path.suffix != ".md":
                errors.append(
                    f"{path.relative_to(anneal_root)}: only lowercase `.md` files "
                    f"are permitted under anneal/book/src/"
                )
        elif rel.parts[0] == "examples":
            if (
                path.name.lower() in {"cargo.toml", "cargo.lock"}
                or path.suffix not in ALLOWED_EXAMPLE_SUFFIXES
            ):
                errors.append(
                    f"{path.relative_to(anneal_root)}: disallowed file inside "
                    f"anneal/book/examples/ (allowed lowercase suffixes: "
                    f"{sorted(ALLOWED_EXAMPLE_SUFFIXES)})"
                )
        else:
            errors.append(
                f"{path.relative_to(anneal_root)}: unexpected top-level file "
                f"inside anneal/book/"
            )


def _strip_inline_code_spans(prose_text: str) -> str:
    """Strip single-line CommonMark inline code spans from Markdown prose.

    Scanning strictly per line (and skipping 4-space or tab-indented lines)
    prevents an indented fence or unclosed backtick on one line from masking
    raw HTML blocks (such as `<script>`) on subsequent lines.
    """
    out_lines: list[str] = []
    for line in prose_text.splitlines():
        if line.startswith(("    ", "\t")):
            out_lines.append(line)
            continue
        # Collect unescaped backtick runs `(start, end, length)` on this line.
        runs: list[tuple[int, int, int]] = []
        i = 0
        n = len(line)
        while i < n:
            if line[i] == "`":
                bs = 0
                b = i - 1
                while b >= 0 and line[b] == "\\":
                    bs += 1
                    b -= 1
                j = i
                while j < n and line[j] == "`":
                    j += 1
                if bs % 2 == 0:
                    runs.append((i, j, j - i))
                i = j
            else:
                i += 1
        # Map each backtick run length to its positions for O(n) matching.
        by_len: dict[int, list[int]] = {}
        for idx, (_s, _e, length) in enumerate(runs):
            by_len.setdefault(length, []).append(idx)

        out: list[str] = []
        cursor = 0
        run_idx = 0
        while run_idx < len(runs):
            start, end, length = runs[run_idx]
            positions = by_len[length]
            # Find the next run of the exact same length after `run_idx`.
            next_match = None
            for pos in positions:
                if pos > run_idx:
                    next_match = pos
                    break
            if next_match is not None:
                close_end = runs[next_match][1]
                out.append(line[cursor:start])
                out.append(" " * (close_end - start))
                cursor = close_end
                run_idx = next_match + 1
            else:
                run_idx += 1
        out.append(line[cursor:])
        out_lines.append("".join(out))
    return "\n".join(out_lines)


def _check_prose_for_raw_html(
    prose_text: str, rel_to_anneal: Path, errors: list[str]
) -> None:
    """Reject raw HTML tags (outside `<!-- ... -->` comments) and unsafe schemes."""
    without_comments = HTML_COMMENT_RE.sub(
        lambda m: "\n" * m.group(0).count("\n"), prose_text
    )
    without_code = _strip_inline_code_spans(without_comments)
    if RAW_HTML_TAG_RE.search(without_code):
        errors.append(
            f"{rel_to_anneal}: raw HTML tags are forbidden in book Markdown "
            f"(only `<!-- ... -->` comments are permitted)"
        )
    if UNSAFE_SCHEME_RE.search(without_code):
        errors.append(
            f"{rel_to_anneal}: disallowed script/data URL scheme in book Markdown"
        )


def _collect_verified_snippet_texts(anneal_root: Path) -> set[str]:
    """Return normalized text bodies of all verified example artifacts."""
    examples_root = anneal_root / "book/examples"
    cases, errors = _load_example_cases(examples_root)
    if errors:
        return set()
    texts: set[str] = set()
    for _case_file, _data, artifacts in cases:
        for artifact in artifacts:
            texts.add(artifact.read_text(encoding="utf-8").strip())
    return texts


def check_sources(anneal_root: Path) -> list[str]:
    """Validate book Markdown sources, fences, directives, examples, and governing docs."""
    errors: list[str] = []
    book_root = anneal_root / "book"
    src_root = book_root / "src"
    examples_root = book_root / "examples"

    _ensure_no_symlinks_under(book_root, "book", errors)
    if errors:
        return errors

    _check_book_toml(book_root, anneal_root, errors)
    _check_book_file_allowlist(book_root, anneal_root, errors)

    cases, case_errors = _load_example_cases(examples_root)
    errors.extend(case_errors)
    all_verified_artifacts: set[Path] = set()
    for _case_file, _data, artifacts in cases:
        all_verified_artifacts.update(artifacts)

    included_paths: set[Path] = set()
    rust_included_ranges: dict[Path, list[tuple[int, int, str]]] = {}

    md_files = sorted(src_root.rglob("*.md"))
    if not md_files:
        errors.append(f"no Markdown files found under {src_root}")
        return errors

    for md_file in md_files:
        rel_to_src = md_file.relative_to(src_root)
        rel_to_anneal = md_file.relative_to(anneal_root)
        top_section = rel_to_src.parts[0] if len(rel_to_src.parts) > 1 else ""
        text = md_file.read_text(encoding="utf-8")

        # 1. Check fenced code blocks against the default-deny policy.
        fences = parse_fences(text)
        checked_fence_lines: set[int] = set()
        all_fence_lines: set[int] = set()
        for fence in fences:
            for ln in range(fence["start_line"], fence["end_line"] + 1):
                all_fence_lines.add(ln)
            if fence.get("unclosed"):
                errors.append(
                    f"{rel_to_anneal}:{fence['start_line']}: unclosed fenced code block"
                )
                continue
            tokens = _parse_fence_tokens(fence["info"])
            matched_langs = sorted(tokens & CHECKED_FENCE_LANGS)
            if not matched_langs:
                continue
            if "conceptual" in tokens:
                if top_section in STRICT_CHAPTER_DIRS:
                    errors.append(
                        f"{rel_to_anneal}:{fence['start_line']}: "
                        f"`conceptual` code fence is forbidden under `{top_section}/`"
                    )
                continue
            non_empty = [
                (ln, body_line.strip())
                for ln, body_line in fence["body"]
                if body_line.strip()
            ]
            if not non_empty or not all(
                STRICT_INCLUDE_RE.match(body_line) for _, body_line in non_empty
            ):
                errors.append(
                    f"{rel_to_anneal}:{fence['start_line']}: "
                    f"raw `{matched_langs[0]}` code fence is not allowed; include a "
                    f"verified artifact from book/examples/ via `{{{{#include ...}}}}`"
                )
            else:
                for ln, _ in non_empty:
                    checked_fence_lines.add(ln)

        # 2. Check all non-fence prose as a whole (catches multi-line raw HTML
        #    tags and attributes) and reject any stray unparsed fence lines.
        lines = text.splitlines()
        prose_only_lines = [
            "" if lineno in all_fence_lines else line
            for lineno, line in enumerate(lines, start=1)
        ]
        _check_prose_for_raw_html(
            "\n".join(prose_only_lines), rel_to_anneal, errors
        )

        for lineno, line in enumerate(lines, start=1):
            if lineno not in all_fence_lines and STRAY_FENCE_RE.match(line):
                errors.append(
                    f"{rel_to_anneal}:{lineno}: nested or indented code fence "
                    f"marker outside a top-level fence is not allowed"
                )

            for match in ANY_DIRECTIVE_RE.finditer(line):
                full_directive = match.group(0)
                strict = STRICT_INCLUDE_RE.match(full_directive)
                if not strict:
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: disallowed or malformed mdBook "
                        f"directive `{full_directive}`; only single-token "
                        f"`{{{{#include <spec>}}}}` and `{{{{#rustdoc_include <spec>}}}}` "
                        f"are permitted"
                    )
                    continue
                if lineno not in checked_fence_lines:
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: `{{{{#{strict.group('kind')} ...}}}}` "
                        f"is only permitted inside a checked code fence"
                    )
                    continue

                kind = strict.group("kind")
                spec = strict.group("spec")
                try:
                    rel_target, anchor, line_range = _parse_include_spec(spec)
                except DocError as exc:
                    errors.append(f"{rel_to_anneal}:{lineno}: {exc}")
                    continue

                raw_target = md_file.parent / rel_target
                if _has_symlink_component(raw_target, book_root):
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: include target traverses a "
                        f"symlink: {rel_target}"
                    )
                    continue
                target = raw_target.resolve()
                if not _is_within(target, examples_root):
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: include target must reside "
                        f"under anneal/book/examples/: {rel_target}"
                    )
                    continue
                if not target.is_file():
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: include target is missing or "
                        f"not a regular file: {rel_target}"
                    )
                    continue
                if target not in all_verified_artifacts:
                    errors.append(
                        f"{rel_to_anneal}:{lineno}: include target is not a "
                        f"registered verified artifact of any case.json: {rel_target}"
                    )
                    continue

                included_paths.add(target)
                target_text = target.read_text(encoding="utf-8")
                target_lines = target_text.splitlines()

                if anchor is not None:
                    anchors, anchor_errors = _extract_anchors(target_text)
                    for err in anchor_errors:
                        errors.append(f"{target.relative_to(anneal_root)}: {err}")
                    if anchor not in anchors:
                        errors.append(
                            f"{rel_to_anneal}:{lineno}: missing anchor `{anchor}` "
                            f"in {rel_target}"
                        )
                        continue
                    start_line, end_line = anchors[anchor]
                    inner = target_lines[start_line : end_line - 1]
                    if not any(item.strip() for item in inner):
                        errors.append(
                            f"{rel_to_anneal}:{lineno}: anchor `{anchor}` in "
                            f"{rel_target} is empty"
                        )
                        continue
                    if target.suffix == ".rs":
                        rust_included_ranges.setdefault(target, []).append(
                            (start_line + 1, end_line - 1, kind)
                        )
                elif line_range is not None:
                    start_opt, end_opt = line_range
                    start = 1 if start_opt is None else start_opt
                    end = len(target_lines) if end_opt is None else end_opt
                    if start < 1 or end > len(target_lines) or start > end:
                        errors.append(
                            f"{rel_to_anneal}:{lineno}: invalid line range "
                            f"`{start}:{end}` for {rel_target} ({len(target_lines)} lines)"
                        )
                        continue
                    if not any(
                        item.strip() for item in target_lines[start - 1 : end]
                    ):
                        errors.append(
                            f"{rel_to_anneal}:{lineno}: line range `{start}:{end}` "
                            f"in {rel_target} is empty"
                        )
                        continue
                    if target.suffix == ".rs":
                        rust_included_ranges.setdefault(target, []).append(
                            (start, end, kind)
                        )
                else:
                    if not target_text.strip():
                        errors.append(
                            f"{rel_to_anneal}:{lineno}: included file is empty: "
                            f"{rel_target}"
                        )
                    if target.suffix == ".rs":
                        rust_included_ranges.setdefault(target, []).append(
                            (1, len(target_lines), kind)
                        )

    # 3. Verify no hidden load-bearing Rust lines in anchored `.rs` includes.
    for rs_path, ranges in sorted(rust_included_ranges.items()):
        _validate_rust_anchor_coverage(rs_path, ranges, errors)

    # 4. Verify every auto-discovered example case has at least one verified
    #    artifact referenced by the book.
    for case_file, _data, artifacts in cases:
        if artifacts and not (artifacts & included_paths):
            errors.append(
                f"{case_file.relative_to(anneal_root)}: example case's verified "
                f"artifact is not included in any book chapter"
            )

    # 5. Verify staged governing docs exist and have no unmapped relative links
    #    or duplicated copies checked into `book/src/foundations/`.
    staged_targets = {dest_rel for _, dest_rel in GOVERNING_DOCS}
    for src_name, dest_rel in GOVERNING_DOCS:
        src_path = anneal_root / src_name
        if not src_path.is_file():
            errors.append(f"missing canonical governing doc: {src_name}")
            continue
        dup_path = src_root / dest_rel
        if dup_path.exists():
            errors.append(
                f"{dup_path.relative_to(anneal_root)}: do not check in a "
                f"duplicate copy of {src_name}; it is staged automatically at "
                f"build time"
            )
        _, link_errors = _rewrite_governing_doc(src_path, dest_rel, anneal_root)
        errors.extend(link_errors)

    # 6. Verify every chapter target listed in `book/src/SUMMARY.md` exists or
    #    is one of the staged governing docs.
    summary_path = src_root / "SUMMARY.md"
    if not summary_path.is_file():
        errors.append(
            f"missing book summary: {summary_path.relative_to(anneal_root)}"
        )
    else:
        summary_text = summary_path.read_text(encoding="utf-8")
        for match in MD_LINK_RE.finditer(summary_text):
            target_rel = match.group("target").split("#", 1)[0]
            if not target_rel or target_rel.startswith(("http://", "https://")):
                continue
            if target_rel in staged_targets:
                continue
            candidate = (src_root / target_rel).resolve()
            if (
                not _is_within(candidate, src_root)
                or not candidate.is_file()
                or candidate.suffix != ".md"
            ):
                errors.append(
                    f"book/src/SUMMARY.md: missing or invalid chapter target `{target_rel}`"
                )

    return errors


def _run_cli_case(
    case_file: Path,
    data: dict,
    cargo_anneal: Path,
    bless: bool,
) -> list[str]:
    """Execute one allowlisted CLI example case against `cargo_anneal`."""
    errors: list[str] = []
    with tempfile.TemporaryDirectory(prefix="anneal-doc-cli-") as tmp_str:
        tmp = Path(tmp_str)
        work_dir = tmp / "work"
        work_dir.mkdir()
        work_resolved = work_dir.resolve()

        setup_files = data.get("setup_files") or {}
        if not isinstance(setup_files, dict):
            return [f"{case_file}: `setup_files` must be an object"]
        for rel_name, content in setup_files.items():
            if not isinstance(rel_name, str) or not isinstance(content, str):
                return [
                    f"{case_file}: `setup_files` entries must map strings to strings"
                ]
            dest = (work_dir / rel_name).resolve()
            if dest == work_resolved or not _is_within(dest, work_dir):
                return [
                    f"{case_file}: setup_files path invalid or escapes workdir: {rel_name}"
                ]
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(content, encoding="utf-8")

        env = {
            "PATH": os.environ.get("PATH", ""),
            "HOME": str(tmp / "home"),
            "TERM": "dumb",
            "NO_COLOR": "1",
        }
        (tmp / "home").mkdir()
        if data.get("fresh_cache_env", False):
            cache_dir = tmp / "cache"
            cache_dir.mkdir()
            env["XDG_CACHE_HOME"] = str(cache_dir)

        proc = subprocess.run(
            [str(cargo_anneal), *data["argv"]],
            cwd=work_dir,
            env=env,
            capture_output=True,
            text=True,
            timeout=60,
            check=False,
        )

        expected_exit = data["expect_exit"]
        if proc.returncode != expected_exit:
            errors.append(
                f"{case_file}: expected exit code {expected_exit}, got "
                f"{proc.returncode}\nstdout:\n{proc.stdout}\nstderr:\n{proc.stderr}"
            )
            return errors

        combined_output = proc.stdout + proc.stderr
        if data.get("normalize_tempdir", False):
            combined_output = (
                combined_output.replace(str(work_resolved), "<WORKDIR>")
                .replace(str(work_dir), "<WORKDIR>")
                .replace(str(tmp.resolve()), "<TMPDIR>")
                .replace(str(tmp), "<TMPDIR>")
            )

        actual_transcript = f"{data['display_command']}\n{combined_output}"
        if not actual_transcript.endswith("\n"):
            actual_transcript += "\n"

        transcript_path = case_file.parent / data["transcript"]
        if bless:
            transcript_path.write_text(actual_transcript, encoding="utf-8")
            return []

        expected_transcript = transcript_path.read_text(encoding="utf-8")
        if actual_transcript != expected_transcript:
            diff = "".join(
                difflib.unified_diff(
                    expected_transcript.splitlines(keepends=True),
                    actual_transcript.splitlines(keepends=True),
                    fromfile=str(transcript_path),
                    tofile="<live cargo-anneal output>",
                )
            )
            errors.append(
                f"{case_file}: transcript mismatch (re-run with `--bless` if "
                f"this CLI change is intentional):\n{diff}"
            )
    return errors


def verify_examples(
    anneal_root: Path,
    cargo_anneal: Path,
    *,
    bless: bool = False,
) -> list[str]:
    """Run all auto-discovered doc examples against `cargo_anneal`."""
    if not cargo_anneal.is_file():
        return [f"cargo-anneal binary does not exist: {cargo_anneal}"]

    examples_root = anneal_root / "book/examples"
    cases, errors = _load_example_cases(examples_root)
    if errors:
        return errors

    for case_file, data, _artifacts in cases:
        if data["kind"] == "cli":
            errors.extend(
                _run_cli_case(case_file, data, cargo_anneal, bless=bless)
            )
        else:
            errors.append(
                f"{case_file}: unsupported example kind: {data['kind']!r}"
            )
    return errors


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(65536), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _download_with_retries(url: str, dest: Path, attempts: int = 3) -> None:
    """Download `url` into `dest` with bounded retries on transient errors."""
    last_exc: Exception | None = None
    for attempt in range(1, attempts + 1):
        try:
            with urllib.request.urlopen(url, timeout=60) as resp:
                dest.write_bytes(resp.read())
            return
        except (URLError, TimeoutError, http.client.HTTPException, OSError) as exc:
            last_exc = exc
            if attempt < attempts:
                time.sleep(attempt)
    raise DocError(
        f"failed to download {url} after {attempts} attempts: {last_exc}"
    )


def ensure_mdbook(
    cache_dir: Path,
    explicit_bin: Path | None = None,
    *,
    url: str = MDBOOK_URL,
    expected_tarball_sha256: str = MDBOOK_SHA256,
    expected_bin_sha256: str = MDBOOK_BIN_SHA256,
) -> Path:
    """Return a verified `mdbook` binary, fetching the pinned release if needed."""
    if explicit_bin is not None:
        if explicit_bin.is_symlink() or not explicit_bin.is_file():
            raise DocError(
                f"explicit --mdbook binary is missing or a symlink: {explicit_bin}"
            )
        return explicit_bin

    if not url.startswith("https://"):
        raise DocError(f"mdBook URL must use https: {url}")

    cache_dir.mkdir(parents=True, exist_ok=True)
    install_dir = cache_dir / f"mdbook-v{MDBOOK_VERSION}-{MDBOOK_TARGET}"
    binary_path = install_dir / "mdbook"

    if (
        not binary_path.is_symlink()
        and binary_path.is_file()
        and _sha256_file(binary_path) == expected_bin_sha256
    ):
        return binary_path

    tarball = cache_dir / f"mdbook-v{MDBOOK_VERSION}-{MDBOOK_TARGET}.tar.gz"
    tmp_tarball = cache_dir / f".mdbook-{os.getpid()}.tar.gz.part"
    try:
        _download_with_retries(url, tmp_tarball)
        actual_sha = _sha256_file(tmp_tarball)
        if actual_sha != expected_tarball_sha256:
            raise DocError(
                f"mdBook tarball SHA-256 mismatch: expected "
                f"{expected_tarball_sha256}, got {actual_sha}"
            )
        tmp_tarball.replace(tarball)
    finally:
        if tmp_tarball.exists():
            tmp_tarball.unlink()

    if install_dir.exists():
        shutil.rmtree(install_dir)
    install_dir.mkdir(parents=True)

    with tarfile.open(tarball, "r:gz") as archive:
        members = archive.getmembers()
        if (
            len(members) != 1
            or members[0].name != "mdbook"
            or not members[0].isfile()
        ):
            raise DocError(
                f"unexpected mdBook tarball contents: {[m.name for m in members]}"
            )
        extracted = archive.extractfile(members[0])
        if extracted is None:
            raise DocError("failed to extract mdbook binary from tarball")
        binary_path.write_bytes(extracted.read())
    actual_bin_sha = _sha256_file(binary_path)
    if actual_bin_sha != expected_bin_sha256:
        binary_path.unlink(missing_ok=True)
        raise DocError(
            f"mdBook binary SHA-256 mismatch: expected {expected_bin_sha256}, "
            f"got {actual_bin_sha}"
        )
    binary_path.chmod(0o755)
    return binary_path


class _HtmlAuditor(HTMLParser):
    """Audit rendered HTML for link targets, `<main>` structure, XSS, and code blocks."""

    def __init__(self) -> None:
        super().__init__()
        self.ids: set[str] = set()
        self.hrefs: list[str] = []
        self.main_depth = 0
        self.main_open_count = 0
        self.main_close_count = 0
        self.pre_depth = 0
        self.in_checked_code = False
        self.current_code_lang = ""
        self.current_code_conceptual = False
        self.current_code_chunks: list[str] = []
        self.checked_code_blocks: list[tuple[str, bool, str]] = []
        self.unsafe_findings: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        tag_l = tag.lower()
        seen_attrs: set[str] = set()
        for raw_name, raw_val in attrs:
            attr_name = raw_name.lower()
            if attr_name in seen_attrs:
                self.unsafe_findings.append(
                    f"duplicate attribute `{attr_name}` on `<{tag_l}>`"
                )
            seen_attrs.add(attr_name)
            if attr_name == "id" and raw_val:
                self.ids.add(raw_val)
            if tag_l == "a" and attr_name == "name" and raw_val:
                self.ids.add(raw_val)
            if tag_l == "a" and attr_name == "href" and raw_val is not None:
                self.hrefs.append(raw_val)
            if self.main_depth > 0:
                if attr_name.startswith("on"):
                    self.unsafe_findings.append(
                        f"disallowed event-handler attribute `{attr_name}` "
                        f"inside rendered `<main>`"
                    )
                if attr_name in URL_ATTRS and raw_val is not None:
                    val_stripped = raw_val.strip()
                    parsed = urlsplit(val_stripped)
                    scheme = parsed.scheme.lower()
                    if attr_name == "srcdoc" or (
                        scheme and scheme not in {"http", "https", "mailto"}
                    ):
                        self.unsafe_findings.append(
                            f"disallowed URL attribute `{attr_name}={raw_val!r}` "
                            f"inside rendered `<main>`"
                        )

        if tag_l == "main":
            self.main_open_count += 1
            self.main_depth += 1
            if self.main_open_count > 1:
                self.unsafe_findings.append("multiple `<main>` elements on page")
        elif self.main_depth > 0:
            if tag_l in DISALLOWED_MAIN_HTML_TAGS:
                self.unsafe_findings.append(
                    f"disallowed `<{tag_l}>` element inside rendered `<main>`"
                )
            if tag_l == "pre":
                self.pre_depth += 1
            elif tag_l == "code" and self.pre_depth > 0:
                classes: set[str] = set()
                for raw_name, raw_val in attrs:
                    if raw_name.lower() == "class" and raw_val:
                        classes.update(raw_val.split())
                for cls in sorted(classes):
                    if cls.startswith("language-"):
                        lang = cls[len("language-") :].lower()
                        if lang in CHECKED_FENCE_LANGS:
                            self.in_checked_code = True
                            self.current_code_lang = lang
                            self.current_code_conceptual = "conceptual" in classes
                            self.current_code_chunks = []
                            break

    def handle_endtag(self, tag: str) -> None:
        tag_l = tag.lower()
        if tag_l == "code" and self.in_checked_code:
            self.checked_code_blocks.append(
                (
                    self.current_code_lang,
                    self.current_code_conceptual,
                    "".join(self.current_code_chunks).strip(),
                )
            )
            self.in_checked_code = False
            self.current_code_lang = ""
            self.current_code_conceptual = False
            self.current_code_chunks = []
        elif tag_l == "pre" and self.pre_depth > 0:
            self.pre_depth -= 1
        elif tag_l == "main":
            self.main_close_count += 1
            if self.main_depth == 0:
                self.unsafe_findings.append("unmatched `</main>` tag on page")
            else:
                self.main_depth -= 1

    def handle_data(self, data: str) -> None:
        if self.in_checked_code:
            self.current_code_chunks.append(data)


def check_built_html_links(
    html_root: Path,
    site_url_prefix: str = SITE_URL_PREFIX,
    *,
    verified_snippets: set[str] | None = None,
) -> list[str]:
    """Verify built HTML links, `#fragments`, `<main>` hygiene, and code parity."""
    errors: list[str] = []
    html_files = sorted(html_root.rglob("*.html"))
    if not html_files:
        return [f"no HTML files generated under {html_root}"]

    page_ids: dict[Path, set[str]] = {}
    page_hrefs: dict[Path, list[str]] = {}
    root_resolved = html_root.resolve()
    skip_code_parity_pages = {
        "foundations/principles.html",
        "foundations/threat-model.html",
        "foundations/meta-principles.html",
        "print.html",
    }

    for html_file in html_files:
        auditor = _HtmlAuditor()
        auditor.feed(html_file.read_text(encoding="utf-8"))
        auditor.close()
        resolved = html_file.resolve()
        rel_page = resolved.relative_to(root_resolved)
        rel_posix = rel_page.as_posix()

        for finding in auditor.unsafe_findings:
            errors.append(f"{rel_page}: {finding}")
        # Require balanced `<main>...</main>` on every page that contains `<main>`
        # (mdBook `toc.html` is a sidebar iframe without `<main>`).
        if auditor.main_open_count != auditor.main_close_count or auditor.main_depth != 0:
            errors.append(
                f"{rel_page}: unbalanced `<main>` tags "
                f"(open={auditor.main_open_count}, close={auditor.main_close_count})"
            )

        # Structural defense against CommonMark parser desyncs: every rendered
        # `CHECKED_FENCE_LANGS` code block in authored chapters must match a
        # verified example artifact (and `conceptual` is forbidden in strict
        # chapters).
        if verified_snippets is not None and rel_posix not in skip_code_parity_pages:
            top_section = rel_page.parts[0] if len(rel_page.parts) > 1 else ""
            for lang, is_conceptual, code_text in auditor.checked_code_blocks:
                if is_conceptual:
                    if top_section in STRICT_CHAPTER_DIRS:
                        errors.append(
                            f"{rel_page}: rendered `conceptual` `{lang}` code block "
                            f"is forbidden under `{top_section}/`"
                        )
                    continue
                if code_text not in verified_snippets:
                    errors.append(
                        f"{rel_page}: rendered `{lang}` code block does not "
                        f"match any verified artifact under anneal/book/examples/"
                    )

        page_ids[resolved] = auditor.ids
        page_hrefs[resolved] = auditor.hrefs

    for page, hrefs in sorted(page_hrefs.items()):
        rel_page = page.relative_to(root_resolved)
        for href in hrefs:
            if not href:
                continue
            parsed = urlsplit(href.strip())
            scheme = parsed.scheme.lower()
            if scheme in {"http", "https", "mailto"}:
                continue
            if scheme:
                errors.append(
                    f"{rel_page}: disallowed URL scheme `{scheme}:` in `{href}`"
                )
                continue
            if parsed.netloc:
                errors.append(
                    f"{rel_page}: scheme-relative URL `{href}` is not allowed"
                )
                continue

            path_part = unquote(parsed.path)
            fragment = unquote(parsed.fragment)

            if not path_part:
                target = page
            elif path_part.startswith(site_url_prefix):
                rel = path_part[len(site_url_prefix) :]
                target = (root_resolved / rel).resolve()
            elif path_part.startswith("/"):
                errors.append(
                    f"{rel_page}: absolute link `{href}` does not start with "
                    f"`{site_url_prefix}`"
                )
                continue
            else:
                target = (page.parent / path_part).resolve()

            if not _is_within(target, root_resolved):
                errors.append(f"{rel_page}: link `{href}` escapes built HTML root")
                continue

            if target.is_dir():
                target = target / "index.html"
            if not target.is_file():
                errors.append(f"{rel_page}: broken internal link `{href}`")
                continue

            if fragment and target.suffix == ".html":
                ids = page_ids.get(target.resolve(), set())
                if fragment not in ids:
                    errors.append(
                        f"{rel_page}: broken anchor `#{fragment}` in link `{href}`"
                    )
    return errors


def build_book(
    anneal_root: Path,
    output_dir: Path,
    *,
    mdbook_bin: Path | None = None,
    cache_dir: Path | None = None,
    skip_source_check: bool = False,
) -> list[str]:
    """Stage governing docs, run `mdbook build`, and verify built HTML."""
    if not skip_source_check:
        source_errors = check_sources(anneal_root)
        if source_errors:
            return source_errors

    verified_snippets = _collect_verified_snippet_texts(anneal_root)
    book_src = anneal_root / "book"
    with tempfile.TemporaryDirectory(prefix="anneal-book-stage-") as stage_str:
        stage_root = Path(stage_str)
        resolved_cache = (
            cache_dir if cache_dir is not None else stage_root / "mdbook-cache"
        )
        mdbook = ensure_mdbook(resolved_cache, explicit_bin=mdbook_bin)

        staged_book = stage_root / "book"
        shutil.copytree(book_src, staged_book, symlinks=False)

        for src_name, dest_rel in GOVERNING_DOCS:
            rewritten, link_errors = _rewrite_governing_doc(
                anneal_root / src_name, dest_rel, anneal_root
            )
            if link_errors:
                return link_errors
            dest_path = staged_book / "src" / dest_rel
            dest_path.parent.mkdir(parents=True, exist_ok=True)
            dest_path.write_text(rewritten, encoding="utf-8")

        output_abs = output_dir.resolve()
        if output_abs.exists():
            shutil.rmtree(output_abs)
        output_abs.parent.mkdir(parents=True, exist_ok=True)

        mdbook_env = {
            "PATH": os.environ.get("PATH", ""),
            "HOME": stage_str,
        }
        proc = subprocess.run(
            [str(mdbook), "build", str(staged_book), "--dest-dir", str(output_abs)],
            env=mdbook_env,
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            return [
                f"mdbook build failed (exit {proc.returncode}):\n"
                f"{proc.stdout}\n{proc.stderr}"
            ]

    return check_built_html_links(
        output_abs, verified_snippets=verified_snippets
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate, verify, and build Anneal public documentation."
    )
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to the anneal/ project root.",
    )
    parser.add_argument(
        "--check-sources",
        action="store_true",
        help="Validate Markdown fences, includes, anchors, examples, and links.",
    )
    parser.add_argument(
        "--verify-examples",
        action="store_true",
        help="Run all examples under book/examples/ against --cargo-anneal.",
    )
    parser.add_argument(
        "--cargo-anneal",
        type=Path,
        help="Path to the cargo-anneal binary for --verify-examples.",
    )
    parser.add_argument(
        "--bless",
        action="store_true",
        help="Overwrite example transcripts with live --cargo-anneal output.",
    )
    parser.add_argument(
        "--build",
        action="store_true",
        help="Stage governing docs, build the mdBook site, and check HTML links.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Destination directory for the built HTML site (required with --build).",
    )
    parser.add_argument(
        "--mdbook",
        type=Path,
        help="Path to an existing mdbook binary (skips downloading pinned release).",
    )
    parser.add_argument(
        "--mdbook-cache",
        type=Path,
        help="Cache directory for downloading the pinned mdBook release.",
    )

    args = parser.parse_args(argv)
    if not (args.check_sources or args.verify_examples or args.build):
        parser.error(
            "specify at least one of --check-sources, --verify-examples, or --build"
        )

    if args.bless and not args.verify_examples:
        parser.error("--bless requires --verify-examples")
    if args.verify_examples and args.cargo_anneal is None:
        parser.error("--verify-examples requires --cargo-anneal")
    if args.build and args.output is None:
        parser.error("--build requires --output")

    anneal_root = args.anneal_root.resolve()
    errors: list[str] = []

    try:
        errors.extend(check_sources(anneal_root))
        if not errors and args.verify_examples:
            errors.extend(
                verify_examples(
                    anneal_root,
                    args.cargo_anneal.resolve(),
                    bless=args.bless,
                )
            )
        if not errors and args.build:
            errors.extend(
                build_book(
                    anneal_root,
                    args.output,
                    mdbook_bin=args.mdbook,
                    cache_dir=args.mdbook_cache,
                    skip_source_check=True,
                )
            )
    except DocError as exc:
        errors.append(str(exc))

    if errors:
        for err in errors:
            print(f"error: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
