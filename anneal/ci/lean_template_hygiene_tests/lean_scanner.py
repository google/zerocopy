# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Lean lexing: blank out comments, strings, and character literals, then
report forbidden tokens in Lean sources and directories."""

from pathlib import Path

from .support import FORBIDDEN_TOKEN_RE, HygieneFinding, REPO_ROOT

def _is_lean_ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in ("_", "'")


def _match_lean_char_literal(source: str, i: int) -> int:
    """If `source[i:]` starts a Lean char literal `'...'`, return end index; else -1."""
    n = len(source)
    if source[i] != "'":
        return -1
    if i > 0 and _is_lean_ident_char(source[i - 1]):
        return -1
    j = i + 1
    if j >= n or source[j] in ("\n", "'"):
        return -1
    if source[j] == "\\":
        j += 1
        if j >= n or source[j] == "\n":
            return -1
        esc = source[j]
        j += 1
        if esc == "x":
            for _ in range(2):
                if j >= n or source[j] not in "0123456789abcdefABCDEF":
                    return -1
                j += 1
        elif esc == "u":
            for _ in range(4):
                if j >= n or source[j] not in "0123456789abcdefABCDEF":
                    return -1
                j += 1
    else:
        j += 1
    if j < n and source[j] == "'":
        return j + 1
    return -1


def _match_lean_raw_string(source: str, i: int) -> tuple[int, int] | None:
    """If `source[i:]` starts a Lean raw string `r#*"..."#*`, return `(body_start, hashes)`."""
    n = len(source)
    if source[i] != "r":
        return None
    if i > 0 and _is_lean_ident_char(source[i - 1]):
        return None
    j = i + 1
    hashes = 0
    while j < n and source[j] == "#":
        hashes += 1
        j += 1
    if j < n and source[j] == '"':
        return j + 1, hashes
    return None


def strip_lean_comments_and_strings(source: str) -> str:
    """Replace Lean comments, char literals, raw strings, and plain strings with spaces.

    Preserves code inside interpolated strings (`s!"...{expr}..."`,
    `m!"...{expr}..."`, etc.) so `sorry`/`admit`/`sorryAx` inside
    interpolations remain visible. Newlines are preserved verbatim so line
    numbers remain exact.
    """
    out: list[str] = []
    n = len(source)
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    # Stack of active interpolated-string brace depths. Each entry records the
    # brace nesting depth inside `{ ... }` of an interpolated string; when an
    # entry reaches 0 upon seeing `}`, scanning resumes inside that string.
    interp_stack: list[int] = []
    in_interp_string = False

    def emit_spaces(text: str) -> None:
        for c in text:
            out.append("\n" if c == "\n" else " ")

    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if nxt == "\n" else " ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if in_interp_string:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if nxt == "\n" else " ")
                i += 2
            elif ch == "{":
                # Enter interpolated Lean expression; keep `{` and inner code.
                in_interp_string = False
                interp_stack.append(1)
                out.append("{")
                i += 1
            elif ch == '"':
                in_interp_string = False
                out.append(" ")
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.append("  ")
            i += 2
            continue

        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue

        # Track braces when inside an interpolated string expression `{ ... }`.
        if interp_stack:
            if ch == "{":
                interp_stack[-1] += 1
                out.append("{")
                i += 1
                continue
            if ch == "}":
                interp_stack[-1] -= 1
                out.append("}")
                i += 1
                if interp_stack[-1] == 0:
                    interp_stack.pop()
                    in_interp_string = True
                continue

        # Lean 4 French-quoted identifier `«...»` (cannot span `\n` or `«`).
        # Sanitize non-identifier punctuation inside `«...»` so `def «/-»` or
        # `def «"»` never opens a phantom comment or string state.
        if ch == "\u00ab":
            out.append(" ")
            i += 1
            while i < n and source[i] not in ("\u00bb", "\u00ab", "\n"):
                c = source[i]
                out.append(c if (c.isalnum() or c == "_") else "_")
                i += 1
            if i < n and source[i] == "\u00bb":
                out.append(" ")
                i += 1
            continue

        # Lean char literal: `'a'`, `'"'`, `'\''`, `'\\'`
        char_end = _match_lean_char_literal(source, i)
        if char_end != -1:
            emit_spaces(source[i:char_end])
            i = char_end
            continue

        # Lean raw string literal: `r"..."`, `r#"..."#`
        raw_match = _match_lean_raw_string(source, i)
        if raw_match is not None:
            body_start, hashes = raw_match
            closing = '"' + ("#" * hashes)
            end_idx = source.find(closing, body_start)
            if end_idx == -1:
                emit_spaces(source[i:])
                break
            end_pos = end_idx + len(closing)
            emit_spaces(source[i:end_pos])
            i = end_pos
            continue

        # Lean interpolated string: `s!"..."`, `m!"..."`, `f!"..."` (must be
        # immediately preceded by an identifier character so prefix boolean
        # negation `!"{".isEmpty` is scanned as `!` + plain string literal).
        if (
            ch == "!"
            and nxt == '"'
            and i > 0
            and _is_lean_ident_char(source[i - 1])
        ):
            in_interp_string = True
            out.append("  ")
            i += 2
            continue

        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def scan_lean_source(source: str, display_path: str, base_line: int = 1) -> list[HygieneFinding]:
    """Scan Lean source text (after stripping comments/strings) for forbidden tokens."""
    stripped = strip_lean_comments_and_strings(source)
    raw_lines = source.splitlines()
    findings: list[HygieneFinding] = []
    for idx, stripped_line in enumerate(stripped.splitlines()):
        for match in FORBIDDEN_TOKEN_RE.finditer(stripped_line):
            raw_snippet = raw_lines[idx].strip() if idx < len(raw_lines) else ""
            findings.append(
                HygieneFinding(
                    path=display_path,
                    line=base_line + idx,
                    token=match.group(0),
                    snippet=raw_snippet,
                )
            )
    return findings


def scan_lean_directories(dirs: tuple[Path, ...]) -> tuple[int, list[HygieneFinding]]:
    file_count = 0
    findings: list[HygieneFinding] = []
    for root in dirs:
        if not root.is_dir():
            continue
        for lean_file in sorted(root.rglob("*.lean")):
            file_count += 1
            rel = str(lean_file.relative_to(REPO_ROOT)) if lean_file.is_relative_to(REPO_ROOT) else str(lean_file)
            findings.extend(
                scan_lean_source(lean_file.read_text(encoding="utf-8"), rel)
            )
    return file_count, findings
