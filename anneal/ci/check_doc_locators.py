#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check that design docs cite repository code by symbol, not by line.

A line locator such as `sandbox.rs:467-532` goes stale whenever the cited
file is edited, and keeping it current forces unrelated PRs to edit the doc.
For each checked Markdown doc, outside fenced code blocks, this script:

1. rejects every inline code span containing a `<path>.<ext>:<digits>` line
   locator, except for paths under `EXTERNAL_PATH_PREFIXES`, which name files
   in other repositories; and
2. for every symbol locator, written as a code span holding an identifier
   followed by a parenthesized code span holding a repository path
   (`` `sym` (`path`) ``), requires that `path` be relative and free of `..`,
   that it exist under the Anneal root or the repository root (or, if `path`
   is a file that was split into a directory, that `path` without its
   extension exist as a directory) without traversing a symlink, and that the
   last `::`- or `.`-separated segment of `sym` occur as a whole word in that
   file or under that directory.

Exits 0 when every checked doc passes and 1 otherwise.
"""

import argparse
import os
from pathlib import Path, PurePosixPath
import re
import sys
from typing import NamedTuple


ANNEAL_ROOT = Path(__file__).resolve().parent.parent

# Docs checked when no paths are given, relative to the Anneal root.
DEFAULT_DOCS = ("docs/testing-architecture.md",)

# Path prefixes that name files in other repositories, which may be cited by
# line because this repository cannot edit them. `src/lean/Lean/` is the
# upstream `leanprover/lean4` source tree.
EXTERNAL_PATH_PREFIXES = ("src/lean/Lean/",)

# Extensions that mark a parenthesized code span as a file path.
PATH_EXTENSIONS = frozenset(
    ("c", "h", "json", "lean", "md", "nix", "py", "rs", "sh", "toml", "yaml")
    + ("yml",)
)

# A fence line: indentation, a run of 3+ backticks or tildes, and the rest.
_FENCE = re.compile(r"^[ \t]*(`{3,}|~{3,})(.*)$")
_CODE_SPAN = re.compile(r"(`+)(.+?)(?<!`)\1(?!`)", re.DOTALL)
_LINE_LOCATOR = re.compile(
    r"((?:[\w.-]+/)*[\w.-]+\.[A-Za-z][A-Za-z0-9]*):\d"
)
# Rust and Lean identifiers, including Lean's `'`, `?`, and `!` name
# characters and Rust's macro `!`.
_IDENT = r"[A-Za-z_][\w']*[?!]?"
_SYMBOL = re.compile(rf"{_IDENT}(?:(?:::|\.){_IDENT})*")
_PATH = re.compile(r"/?[\w.-]+(?:/[\w.-]+)*/?")
_BETWEEN_SYMBOL_AND_PATH = re.compile(r"\s*\(")


class Span(NamedTuple):
    start: int
    end: int
    content: str


def _blank_fences(text: str) -> str:
    """Blank the lines of fenced code blocks, keeping line numbers.

    Follows CommonMark: a backtick fence's info string has no backticks (so a
    line starting with an inline span such as ```` ```x``` ```` opens no
    fence), and only a bare run of the opening character at least as long as
    the opening run closes the block.
    """
    out = []
    open_run = None
    for line in text.split("\n"):
        m = _FENCE.match(line)
        if open_run is None:
            if m and not (m.group(1)[0] == "`" and "`" in m.group(2)):
                open_run = m.group(1)
                out.append("")
            else:
                out.append(line)
            continue
        if (
            m
            and m.group(1)[0] == open_run[0]
            and len(m.group(1)) >= len(open_run)
            and not m.group(2).strip()
        ):
            open_run = None
        out.append("")
    return "\n".join(out)


def _code_spans(text: str) -> list[Span]:
    return [
        Span(m.start(), m.end(), m.group(2)) for m in _CODE_SPAN.finditer(text)
    ]


def _line_of(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _is_external(path: str) -> bool:
    return path.startswith(EXTERNAL_PATH_PREFIXES)


def _looks_like_path(path: str) -> bool:
    if not _PATH.fullmatch(path):
        return False
    suffix = PurePosixPath(path.rstrip("/")).suffix.lstrip(".")
    return "/" in path or suffix in PATH_EXTENSIONS


def _is_symbol(sym: str) -> bool:
    if not _SYMBOL.fullmatch(sym):
        return False
    # `foo.rs` names a file, not a symbol.
    return re.split(r"::|\.", sym)[-1] not in PATH_EXTENSIONS


def _confined(root: Path, path: Path, repo_root: Path) -> bool:
    """Whether `path` exists, is reached from `root` without traversing a
    symlink, and resolves inside `repo_root`."""
    current = root
    for part in path.relative_to(root).parts:
        current = current / part
        if current.is_symlink():
            return False
    return path.exists() and path.resolve().is_relative_to(repo_root)


def _search_roots(path: str, roots: tuple[Path, ...]) -> list[Path] | None:
    """Return the files and directories `path` names, or None if none exist.

    `path` is a relative path without `..`; the last root is the repository
    root, which every target must resolve inside.
    """
    repo_root = roots[-1].resolve()
    for root in roots:
        candidate = root / path
        found = []
        if _confined(root, candidate, repo_root) and (
            candidate.is_file() or candidate.is_dir()
        ):
            found.append(candidate)
        split_dir = candidate.with_suffix("")
        if (
            candidate.suffix
            and _confined(root, split_dir, repo_root)
            and split_dir.is_dir()
        ):
            found.append(split_dir)
        if found:
            return found
    return None


def _iter_files(paths: list[Path]):
    for path in paths:
        if path.is_file():
            yield path
            continue
        for dirpath, dirnames, filenames in os.walk(path):
            dirnames.sort()
            for name in sorted(filenames):
                file = Path(dirpath) / name
                if file.is_file() and not file.is_symlink():
                    yield file


def _symbol_occurs(sym: str, paths: list[Path]) -> bool:
    needle = re.split(r"::|\.", sym)[-1]
    # `foo`, `foo'`, `foo?`, and `foo!` are distinct Lean names.
    word = re.compile(rf"(?<![\w']){re.escape(needle)}(?![\w'?!])")
    for file in _iter_files(paths):
        try:
            text = file.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if word.search(text):
            return True
    return False


def check_doc(doc: Path, roots: tuple[Path, ...]) -> list[str]:
    """Return `<doc>:<line>: <message>` findings for `doc`."""
    text = _blank_fences(doc.read_text(encoding="utf-8"))
    spans = _code_spans(text)
    findings: list[tuple[int, str]] = []

    for span in spans:
        if "://" in span.content:
            continue
        for match in _LINE_LOCATOR.finditer(span.content):
            if _is_external(match.group(1)):
                continue
            findings.append(
                (
                    _line_of(text, span.start),
                    f"line locator `{span.content}`; cite a symbol instead, "
                    "as `symbol` (`path/to/file`)",
                )
            )
            break

    for sym_span, path_span in zip(spans, spans[1:]):
        sym, path = sym_span.content, path_span.content
        between = text[sym_span.end : path_span.start]
        if not (
            _BETWEEN_SYMBOL_AND_PATH.fullmatch(between)
            and text.startswith(")", path_span.end)
            and _is_symbol(sym)
            and _looks_like_path(path)
            and not _is_external(path)
        ):
            continue
        line = _line_of(text, sym_span.start)
        pure = PurePosixPath(path)
        if pure.is_absolute() or ".." in pure.parts:
            message = f"symbol locator path `{path}` must be relative"
            findings.append((line, f"{message} and free of `..`"))
            continue
        targets = _search_roots(path, roots)
        if targets is None:
            message = f"symbol locator path `{path}` does not exist"
            findings.append((line, f"{message} (symlinks are not followed)"))
        elif not _symbol_occurs(sym, targets):
            findings.append(
                (line, f"symbol `{sym}` does not occur in `{path}`")
            )

    return [f"{doc}:{line}: {message}" for line, message in sorted(findings)]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=ANNEAL_ROOT,
        help="Anneal root; its parent is the repository root",
    )
    parser.add_argument(
        "docs",
        nargs="*",
        type=Path,
        help=f"Markdown docs to check (default: {', '.join(DEFAULT_DOCS)})",
    )
    args = parser.parse_args(argv)
    anneal_root = args.anneal_root.resolve()
    roots = (anneal_root, anneal_root.parent)
    docs = args.docs or [anneal_root / doc for doc in DEFAULT_DOCS]

    findings = []
    for doc in docs:
        findings.extend(check_doc(doc, roots))
    for finding in findings:
        print(finding, file=sys.stderr)
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
