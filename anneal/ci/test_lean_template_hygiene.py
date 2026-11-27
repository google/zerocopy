# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Static hygiene checks banning `sorry` / `admit` in Lean proofs and templates."""

import ast
from dataclasses import dataclass
from pathlib import Path
import re
import tomllib
import unittest

try:
    from redteam.lean_ast import strip_lean_comments_and_strings
except ImportError:
    from ci.redteam.lean_ast import strip_lean_comments_and_strings


REPO_ROOT = Path(__file__).resolve().parents[2]
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"
LEAN_SCAN_DIRS = (
    REPO_ROOT / "anneal" / "theory",
    REPO_ROOT / "anneal" / "correspondence",
    REPO_ROOT / "anneal" / "tools" / "anneal-spec" / "tests",
    REPO_ROOT / "zerocopy" / "proofs",
)
RUST_INIT_TEMPLATE = (
    REPO_ROOT / "anneal" / "trusted" / "cargo-anneal" / "src" / "init.rs"
)
RUST_INIT_ASSETS_DIR = (
    REPO_ROOT / "anneal" / "trusted" / "cargo-anneal" / "assets"
)
PYTHON_SCAFFOLD_TEMPLATE = REPO_ROOT / "anneal" / "ci" / "anneal_scaffold.py"

FORBIDDEN_TOKEN_RE = re.compile(
    r"(?<![A-Za-z0-9_])(?:sorry|admit|sorryAx)(?![A-Za-z0-9_'])"
)


@dataclass(frozen=True)
class HygieneFinding:
    path: str
    line: int
    token: str
    snippet: str


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


def _unescape_rust_string(raw: str) -> str:
    """Decode a Rust normal string literal body (including `\\xNN` and `\\u{...}`)."""
    out: list[str] = []
    n = len(raw)
    i = 0
    hex_chars = "0123456789abcdefABCDEF"
    while i < n:
        ch = raw[i]
        if ch != "\\":
            out.append(ch)
            i += 1
            continue
        if i + 1 >= n:
            raise ValueError("trailing backslash in Rust string literal")
        nxt = raw[i + 1]
        if nxt == "\n":
            # Rust string line continuation skips following ASCII whitespace.
            i += 2
            while i < n and raw[i] in (" ", "\t", "\r", "\n"):
                i += 1
            continue
        if nxt == "\r" and i + 2 < n and raw[i + 2] == "\n":
            i += 3
            while i < n and raw[i] in (" ", "\t", "\r", "\n"):
                i += 1
            continue
        escapes = {
            "n": "\n",
            "r": "\r",
            "t": "\t",
            "\\": "\\",
            '"': '"',
            "'": "'",
            "0": "\0",
        }
        if nxt in escapes:
            out.append(escapes[nxt])
            i += 2
            continue
        if nxt == "x":
            if i + 3 >= n or raw[i + 2] not in hex_chars or raw[i + 3] not in hex_chars:
                raise ValueError(f"malformed \\x escape at offset {i}")
            out.append(chr(int(raw[i + 2 : i + 4], 16)))
            i += 4
            continue
        if nxt == "u":
            if i + 2 >= n or raw[i + 2] != "{":
                raise ValueError(f"malformed \\u escape missing '{{' at offset {i}")
            close_brace = raw.find("}", i + 3)
            if close_brace == -1:
                raise ValueError(f"unclosed \\u{{...}} escape at offset {i}")
            inner = raw[i + 3 : close_brace]
            if not inner or inner[0] == "_" or any(
                c not in hex_chars and c != "_" for c in inner
            ):
                raise ValueError(f"invalid digits in \\u{{{inner}}}")
            digits = inner.replace("_", "")
            if not (1 <= len(digits) <= 6):
                raise ValueError(f"out-of-range length in \\u{{{inner}}}")
            cp = int(digits, 16)
            if cp > 0x10FFFF or (0xD800 <= cp <= 0xDFFF):
                raise ValueError(f"invalid Unicode scalar value \\u{{{inner}}}")
            out.append(chr(cp))
            i = close_brace + 1
            continue
        raise ValueError(f"unrecognized Rust string escape \\{nxt}")
    return "".join(out)


_CFG_TEST_ATTR_RE = re.compile(r"#\[\s*cfg\s*\(\s*test\s*\)\s*\]")


def _skip_rust_string_or_comment(source: str, i: int) -> int:
    """If `source[i:]` starts a Rust comment, string, raw string, or char literal,
    return the index immediately after it; else return -1.
    """
    n = len(source)
    ch = source[i]
    nxt = source[i + 1] if i + 1 < n else ""

    # Line comment
    if ch == "/" and nxt == "/":
        j = i + 2
        while j < n and source[j] != "\n":
            j += 1
        return j

    # Nested block comment
    if ch == "/" and nxt == "*":
        depth = 1
        j = i + 2
        while j < n and depth > 0:
            if source[j] == "/" and j + 1 < n and source[j + 1] == "*":
                depth += 1
                j += 2
            elif source[j] == "*" and j + 1 < n and source[j + 1] == "/":
                depth -= 1
                j += 2
            else:
                j += 1
        return j

    # Raw string literal: r#"..."#, br#"..."#, cr#"..."#
    if ch in ("r", "b", "c"):
        j = i + (1 if ch in ("b", "c") and nxt == "r" else 0)
        if j < n and source[j] == "r" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_")):
            k = j + 1
            hashes = 0
            while k < n and source[k] == "#":
                hashes += 1
                k += 1
            if k < n and source[k] == '"':
                closing = '"' + ("#" * hashes)
                end_idx = source.find(closing, k + 1)
                return n if end_idx == -1 else end_idx + len(closing)

    # Normal, byte, or C string literal: "...", b"...", c"..."
    str_quote = -1
    if ch == '"':
        str_quote = i
    elif (
        ch in ("b", "c")
        and nxt == '"'
        and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_"))
    ):
        str_quote = i + 1
    if str_quote != -1:
        j = str_quote + 1
        while j < n:
            if source[j] == "\\" and j + 1 < n:
                j += 2
            elif source[j] == '"':
                return j + 1
            else:
                j += 1
        return n

    # Char or byte-char literal `'a'`, `'\''`, `b'"'` (avoid Rust lifetimes like
    # `'static`).
    quote_pos = -1
    if ch == "'":
        prev_is_ident = i > 0 and (source[i - 1].isalnum() or source[i - 1] == "_")
        prev_is_byte_prefix = (
            i > 0
            and source[i - 1] == "b"
            and (i < 2 or not (source[i - 2].isalnum() or source[i - 2] == "_"))
        )
        if not prev_is_ident or prev_is_byte_prefix:
            quote_pos = i
    elif (
        ch == "b"
        and nxt == "'"
        and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_"))
    ):
        quote_pos = i + 1

    if quote_pos != -1:
        j = quote_pos + 1
        if j < n and source[j] == "\\" and j + 1 < n:
            k = j + 2
            while k < n and source[k] not in ("'", "\n"):
                k += 1
            if k < n and source[k] == "'":
                return k + 1
        elif j + 1 < n and source[j] not in ("'", "\n") and source[j + 1] == "'":
            return j + 2

    return -1


_RUST_ITEM_KEYWORDS = frozenset(
    {
        "fn",
        "mod",
        "struct",
        "enum",
        "union",
        "trait",
        "impl",
        "type",
        "const",
        "static",
        "use",
        "macro_rules",
    }
)


def _rust_cfg_target_is_item(source: str, pos: int) -> bool:
    """Return True if the Rust construct after `#[cfg(test)]` is a Rust item.

    Item targets (`fn`, `mod`, `struct`, `impl`, etc.) terminate at top-level
    `;` or balanced `{...}` so commas in generic lists or `where` clauses do
    not cut stripping short. Non-item targets (struct fields, enum variants,
    match arms, call/array elements) also terminate at top-level `,`.
    """
    n = len(source)
    k = pos

    def skip_ws_and_comments(idx: int) -> int:
        while idx < n:
            if source[idx].isspace():
                idx += 1
            elif source[idx : idx + 2] in ("//", "/*"):
                sk = _skip_rust_string_or_comment(source, idx)
                if sk == -1:
                    break
                idx = sk
            else:
                break
        return idx

    # Skip stacked outer attributes (`#[...]`).
    while True:
        k = skip_ws_and_comments(k)
        if source[k : k + 2] == "#[":
            k += 2
            depth = 1
            while k < n and depth > 0:
                sk = _skip_rust_string_or_comment(source, k)
                if sk != -1:
                    k = sk
                    continue
                if source[k] == "[":
                    depth += 1
                elif source[k] == "]":
                    depth -= 1
                k += 1
            continue
        break

    # Skip leading visibility/item modifiers (`pub[(...)]`, `default`,
    # `unsafe`, `async`, `extern ["..."]`).
    while True:
        k = skip_ws_and_comments(k)
        if k >= n or source[k : k + 2] == "r#":
            return False
        if not (source[k].isalpha() or source[k] == "_"):
            return False
        start = k
        while k < n and (source[k].isalnum() or source[k] == "_"):
            k += 1
        word = source[start:k]
        if word == "pub":
            k2 = skip_ws_and_comments(k)
            if k2 < n and source[k2] == "(":
                k2 += 1
                pdepth = 1
                while k2 < n and pdepth > 0:
                    sk = _skip_rust_string_or_comment(source, k2)
                    if sk != -1:
                        k2 = sk
                        continue
                    if source[k2] == "(":
                        pdepth += 1
                    elif source[k2] == ")":
                        pdepth -= 1
                    k2 += 1
                k = k2
            continue
        if word in ("default", "unsafe", "async"):
            continue
        if word == "extern":
            k2 = skip_ws_and_comments(k)
            if k2 < n and source[k2] == '"':
                sk = _skip_rust_string_or_comment(source, k2)
                if sk != -1:
                    k = sk
            continue
        return word in _RUST_ITEM_KEYWORDS


def strip_rust_cfg_test_items(source: str) -> str:
    """Replace `#[cfg(test)]`-annotated Rust items with spaces, preserving newlines.

    Unlike truncating at the first `#[cfg(test)]`, balanced item stripping keeps
    production templates that appear after an earlier `#[cfg(test)]` helper or
    module intact and preserves exact line numbers.
    """
    out = list(source)
    n = len(source)
    i = 0

    def blank_range(start: int, end: int) -> None:
        for idx in range(start, end):
            if out[idx] != "\n":
                out[idx] = " "

    while i < n:
        skipped = _skip_rust_string_or_comment(source, i)
        if skipped != -1:
            i = skipped
            continue

        if source[i] == "#":
            m = _CFG_TEST_ATTR_RE.match(source, i)
            if m:
                item_start = i
                j = m.end()
                is_item = _rust_cfg_target_is_item(source, j)
                # Advance over whitespace, comments, and stacked attributes
                # until the attached construct ends. Never cross an unmatched
                # enclosing `}`, `)`, or `]` at depth 0, and terminate non-item
                # targets (fields, enum variants, match arms) on top-level `,`.
                paren_depth = 0
                bracket_depth = 0
                brace_depth = 0
                saw_brace = False
                while j < n:
                    sk = _skip_rust_string_or_comment(source, j)
                    if sk != -1:
                        j = sk
                        continue
                    c = source[j]
                    if c == "(":
                        paren_depth += 1
                    elif c == ")":
                        if (
                            paren_depth == 0
                            and bracket_depth == 0
                            and brace_depth == 0
                        ):
                            break
                        if paren_depth > 0:
                            paren_depth -= 1
                    elif c == "[":
                        bracket_depth += 1
                    elif c == "]":
                        if (
                            bracket_depth == 0
                            and paren_depth == 0
                            and brace_depth == 0
                        ):
                            break
                        if bracket_depth > 0:
                            bracket_depth -= 1
                    elif c == "{" and paren_depth == 0 and bracket_depth == 0:
                        brace_depth += 1
                        saw_brace = True
                    elif c == "}" and paren_depth == 0 and bracket_depth == 0:
                        if brace_depth == 0:
                            break
                        brace_depth -= 1
                        if saw_brace and brace_depth == 0:
                            j += 1
                            break
                    elif (
                        c == ";"
                        and paren_depth == 0
                        and bracket_depth == 0
                        and brace_depth == 0
                    ):
                        j += 1
                        break
                    elif (
                        not is_item
                        and c == ","
                        and paren_depth == 0
                        and bracket_depth == 0
                        and brace_depth == 0
                    ):
                        j += 1
                        break
                    j += 1
                blank_range(item_start, j)
                i = j
                continue

        i += 1

    return "".join(out)


def _parse_rust_string_at(source: str, i: int) -> tuple[str | None, int] | None:
    """If `source[i:]` starts a Rust normal or raw string literal, return `(decoded, end_idx)`.

    Returns `(None, end_idx)` when a normal string contains a malformed escape
    so callers fail closed instead of silently dropping characters.
    """
    n = len(source)
    ch = source[i]
    nxt = source[i + 1] if i + 1 < n else ""

    # Raw string literal: r#"..."#, br#"..."#, cr#"..."#
    if ch in ("r", "b", "c"):
        j = i + (1 if ch in ("b", "c") and nxt == "r" else 0)
        if j < n and source[j] == "r":
            if i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_"):
                k = j + 1
                hashes = 0
                while k < n and source[k] == "#":
                    hashes += 1
                    k += 1
                if k < n and source[k] == '"':
                    body_start = k + 1
                    closing = '"' + ("#" * hashes)
                    end_idx = source.find(closing, body_start)
                    if end_idx == -1:
                        return source[body_start:], n
                    return source[body_start:end_idx], end_idx + len(closing)

    # Normal, byte, or C string literal: "...", b"...", or c"..."
    quote_idx = -1
    if ch == '"':
        quote_idx = i
    elif (
        ch in ("b", "c")
        and nxt == '"'
        and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] == "_"))
    ):
        quote_idx = i + 1

    if quote_idx != -1:
        j = quote_idx + 1
        buf: list[str] = []
        end_pos = n
        while j < n:
            c = source[j]
            if c == "\\" and j + 1 < n:
                buf.append(c)
                buf.append(source[j + 1])
                j += 2
            elif c == '"':
                end_pos = j + 1
                break
            else:
                buf.append(c)
                j += 1
        try:
            return _unescape_rust_string("".join(buf)), end_pos
        except ValueError:
            return None, end_pos

    return None


def _skip_rust_ws_and_comments(source: str, i: int) -> int:
    n = len(source)
    while i < n:
        if source[i].isspace():
            i += 1
            continue
        if source[i] == "/" and i + 1 < n and source[i + 1] in ("/", "*"):
            nxt = _skip_rust_string_or_comment(source, i)
            if nxt != -1:
                i = nxt
                continue
        break
    return i


def _parse_rust_concat_at(source: str, i: int) -> tuple[str | None, int] | None:
    """If `source[i:]` starts a `concat!(...)` macro invocation, evaluate it.

    Returns `(combined_string, end_idx)` when all arguments are Rust string
    literals (or nested `concat!(...)`), `(None, end_idx)` when a non-literal
    argument is present (caller must fail closed), or `None` if `source[i:]`
    is not a `concat!` invocation.
    """
    n = len(source)
    if not source.startswith("concat!", i):
        return None
    if i > 0 and (source[i - 1].isalnum() or source[i - 1] == "_"):
        return None
    j = _skip_rust_ws_and_comments(source, i + len("concat!"))
    if j >= n or source[j] not in ("(", "[", "{"):
        return None
    close_delim = {"(": ")", "[": "]", "{": "}"}[source[j]]
    j += 1

    parts: list[str] = []
    valid = True
    while j < n:
        j = _skip_rust_ws_and_comments(source, j)
        if j >= n:
            valid = False
            break
        if source[j] == close_delim:
            j += 1
            return ("".join(parts) if valid else None), j

        nested = _parse_rust_concat_at(source, j)
        if nested is not None:
            nested_val, j = nested
            if nested_val is None:
                valid = False
            else:
                parts.append(nested_val)
        else:
            parsed_str = _parse_rust_string_at(source, j)
            if parsed_str is not None:
                val, j = parsed_str
                if val is None:
                    valid = False
                else:
                    parts.append(val)
            else:
                # Non-literal argument inside `concat!(...)`: consume until `,`
                # or matching closing delimiter and mark non-literal (fail
                # closed).
                valid = False
                depth = 0
                while j < n:
                    sk = _skip_rust_string_or_comment(source, j)
                    if sk != -1:
                        j = sk
                        continue
                    c = source[j]
                    if c in ("(", "[", "{"):
                        depth += 1
                    elif c in (")", "]", "}"):
                        if depth == 0 and c == close_delim:
                            break
                        if depth > 0:
                            depth -= 1
                    elif c == "," and depth == 0:
                        break
                    j += 1

        j = _skip_rust_ws_and_comments(source, j)
        if j < n and source[j] == ",":
            j += 1
            continue
        if j < n and source[j] == close_delim:
            j += 1
            return ("".join(parts) if valid else None), j
        # Unexpected trailing token inside argument expression.
        valid = False
        depth = 0
        while j < n:
            sk = _skip_rust_string_or_comment(source, j)
            if sk != -1:
                j = sk
                continue
            c = source[j]
            if c in ("(", "[", "{"):
                depth += 1
            elif c in (")", "]", "}"):
                if depth == 0 and c == close_delim:
                    j += 1
                    return None, j
                if depth > 0:
                    depth -= 1
            elif c == "," and depth == 0:
                j += 1
                break
            j += 1

    return None, j


def extract_rust_string_literals_and_concats(
    source: str,
) -> tuple[list[tuple[int, str]], list[tuple[int, str]], list[tuple[int, str]]]:
    """Extract `(start_line, decoded)` literals, non-literal `concat!`s, and bad escapes."""
    literals: list[tuple[int, str]] = []
    non_literal_concats: list[tuple[int, str]] = []
    bad_escapes: list[tuple[int, str]] = []
    n = len(source)
    i = 0
    line = 1

    while i < n:
        ch = source[i]
        nxt = source[i + 1] if i + 1 < n else ""

        if ch == "/" and nxt in ("/", "*"):
            end_idx = _skip_rust_string_or_comment(source, i)
            line += source[i:end_idx].count("\n")
            i = end_idx
            continue

        if ch == "'":
            end_idx = _skip_rust_string_or_comment(source, i)
            if end_idx != -1:
                line += source[i:end_idx].count("\n")
                i = end_idx
                continue

        if ch == "c":
            concat_res = _parse_rust_concat_at(source, i)
            if concat_res is not None:
                combined, end_idx = concat_res
                start_line = line
                snippet = source[i:end_idx].splitlines()[0].strip()
                line += source[i:end_idx].count("\n")
                if combined is None:
                    non_literal_concats.append((start_line, snippet))
                else:
                    literals.append((start_line, combined))
                i = end_idx
                continue

        parsed_str = _parse_rust_string_at(source, i)
        if parsed_str is not None:
            decoded, end_idx = parsed_str
            start_line = line
            snippet = source[i:end_idx].splitlines()[0].strip()
            line += source[i:end_idx].count("\n")
            if decoded is None:
                bad_escapes.append((start_line, snippet))
            else:
                literals.append((start_line, decoded))
            i = end_idx
            continue

        if ch == "\n":
            line += 1
        i += 1

    return literals, non_literal_concats, bad_escapes


def scan_rust_template_source(source: str, display_path: str) -> tuple[int, list[HygieneFinding]]:
    """Scan Rust string literals and `concat!(...)` templates for forbidden tokens."""
    non_test_source = strip_rust_cfg_test_items(source)

    literals, non_literal_concats, bad_escapes = (
        extract_rust_string_literals_and_concats(non_test_source)
    )
    lean_like_count = 0
    findings: list[HygieneFinding] = []
    for start_line, snippet in non_literal_concats:
        findings.append(
            HygieneFinding(
                path=display_path,
                line=start_line,
                token="concat!",
                snippet=(
                    "non-literal concat! argument cannot be statically "
                    f"verified: {snippet}"
                ),
            )
        )
    for start_line, snippet in bad_escapes:
        findings.append(
            HygieneFinding(
                path=display_path,
                line=start_line,
                token="escape",
                snippet=f"malformed Rust string escape: {snippet}",
            )
        )
    for start_line, literal in literals:
        if "theorem " in literal or "public import " in literal or "namespace " in literal:
            lean_like_count += 1
        findings.extend(scan_lean_source(literal, display_path, base_line=start_line))
    return lean_like_count, findings


def _reconstruct_joined_str(node: ast.JoinedStr) -> str:
    """Reconstruct a Python f-string (`JoinedStr`) for Lean template scanning.

    Constant string parts (including nested constant `FormattedValue`s) are
    concatenated directly so split forms such as `f"sor{''}ry"` resolve to
    `"sorry"`, while dynamic expressions are replaced with a neutral identifier
    placeholder `__lean_interp__`.
    """
    parts: list[str] = []
    for part in node.values:
        if isinstance(part, ast.Constant) and isinstance(part.value, str):
            parts.append(part.value)
        elif isinstance(part, ast.FormattedValue):
            if (
                isinstance(part.value, ast.Constant)
                and isinstance(part.value.value, str)
                and part.conversion == -1
                and part.format_spec is None
            ):
                parts.append(part.value.value)
            elif (
                isinstance(part.value, ast.JoinedStr)
                and part.conversion == -1
                and part.format_spec is None
            ):
                parts.append(_reconstruct_joined_str(part.value))
            else:
                parts.append("__lean_interp__")
        else:
            parts.append("__lean_interp__")
    return "".join(parts)


def scan_python_scaffold_source(source: str, display_path: str) -> list[HygieneFinding]:
    """Scan Python string literals and f-strings via `ast.parse` for `sorry`/`admit`."""
    try:
        tree = ast.parse(source, filename=display_path)
    except SyntaxError as exc:
        return [
            HygieneFinding(
                path=display_path,
                line=exc.lineno or 1,
                token="SyntaxError",
                snippet=str(exc),
            )
        ]

    findings: list[HygieneFinding] = []

    def visit(node: ast.AST) -> None:
        if isinstance(node, ast.JoinedStr):
            reconstructed = _reconstruct_joined_str(node)
            findings.extend(
                scan_lean_source(
                    reconstructed,
                    display_path,
                    base_line=getattr(node, "lineno", 1),
                )
            )
            for part in node.values:
                if isinstance(part, ast.FormattedValue):
                    visit(part.value)
                    if part.format_spec is not None:
                        visit(part.format_spec)
            return

        if isinstance(node, ast.Constant) and isinstance(node.value, (str, bytes)):
            val = (
                node.value.decode("utf-8", errors="replace")
                if isinstance(node.value, bytes)
                else node.value
            )
            findings.extend(
                scan_lean_source(
                    val,
                    display_path,
                    base_line=getattr(node, "lineno", 1),
                )
            )
            return

        for child in ast.iter_child_nodes(node):
            visit(child)

    visit(tree)
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


class LeanTemplateHygieneTests(unittest.TestCase):
    def test_repo_lean_directories_have_no_sorry_or_admit(self):
        for root in LEAN_SCAN_DIRS:
            self.assertTrue(root.is_dir(), f"Expected Lean directory to exist: {root}")
        file_count, findings = scan_lean_directories(LEAN_SCAN_DIRS)
        self.assertGreater(file_count, 0, "Expected at least one .lean file to scan")
        self.assertEqual(
            findings,
            [],
            "Forbidden sorry/admit tokens found in Lean sources:\n"
            + "\n".join(f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in findings),
        )

    def test_repo_scaffold_templates_have_no_sorry_or_admit(self):
        self.assertTrue(
            RUST_INIT_TEMPLATE.is_file(),
            f"Expected Rust init template source: {RUST_INIT_TEMPLATE}",
        )
        lean_templates, findings = scan_rust_template_source(
            RUST_INIT_TEMPLATE.read_text(encoding="utf-8"),
            str(RUST_INIT_TEMPLATE.relative_to(REPO_ROOT)),
        )
        asset_lean_count = 0
        if RUST_INIT_ASSETS_DIR.is_dir():
            asset_lean_count, asset_findings = scan_lean_directories(
                (RUST_INIT_ASSETS_DIR,)
            )
            findings.extend(asset_findings)

        self.assertGreaterEqual(
            lean_templates + asset_lean_count,
            4,
            "Expected at least 4 Lean templates across init.rs and "
            "cargo-anneal/assets/**/*.lean",
        )
        self.assertEqual(
            findings,
            [],
            "Forbidden sorry/admit/sorryAx tokens found in scaffold templates:\n"
            + "\n".join(f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in findings),
        )

        if PYTHON_SCAFFOLD_TEMPLATE.is_file():
            py_findings = scan_python_scaffold_source(
                PYTHON_SCAFFOLD_TEMPLATE.read_text(encoding="utf-8"),
                str(PYTHON_SCAFFOLD_TEMPLATE.relative_to(REPO_ROOT)),
            )
            self.assertEqual(
                py_findings,
                [],
                "Forbidden sorry/admit tokens found in anneal_scaffold.py:\n"
                + "\n".join(
                    f"  {f.path}:{f.line}: {f.token}: {f.snippet}" for f in py_findings
                ),
            )

    def test_synthetic_sorry_and_admit_detected_in_lean(self):
        src = (
            "module\n"
            "theorem t1 : False := by\n"
            "  sorry\n"
            "theorem t2 : False := by\n"
            "  admit\n"
        )
        findings = scan_lean_source(src, "synthetic.lean")
        self.assertEqual([(f.line, f.token) for f in findings], [(3, "sorry"), (5, "admit")])

    def test_lean_comments_nested_blocks_strings_and_identifiers_ignored(self):
        src = (
            "-- line comment mentioning sorry and admit\n"
            "/- block comment with sorry\n"
            "   /- nested block with admit -/\n"
            "   still inside outer block: sorry\n"
            "-/\n"
            "/-- doc comment: zero `sorry`, admits inputs -/\n"
            'def msg : String := "sorry admit"\n'
            "def BodyStaticAdmitted : Bool := true\n"
            "def sorry_free : Bool := true\n"
            "/- closed block -/ theorem caught : False := by sorry\n"
        )
        findings = scan_lean_source(src, "comments.lean")
        self.assertEqual([(f.line, f.token) for f in findings], [(10, "sorry")])

    def test_rust_template_detects_sorry_and_admit_and_ignores_comments(self):
        rust_src = (
            "// Rust comment: never emit sorry or admit\n"
            "/* block comment /* nested sorry */ admit */\n"
            'const CLEAN: &str = "\\\n'
            "-- Lean comment mentioning sorry and admit\n"
            'public theorem verify : True := True.intro\n";\n'
            'const BAD_NORMAL: &str = "\\\n'
            'public theorem bad1 : False := by\\n  sorry\\n";\n'
            'const BAD_RAW: &str = r#"\n'
            "public theorem bad2 : False := by\n"
            "  admit\n"
            '"#;\n'
            "#[cfg(test)]\n"
            "mod tests {\n"
            '    const TEST_ONLY: &str = "theorem ignored : False := sorry";\n'
            "}\n"
        )
        _, findings = scan_rust_template_source(rust_src, "synthetic_init.rs")
        self.assertEqual([f.token for f in findings], ["sorry", "admit"])

    def test_lean_char_raw_string_interpolation_and_sorry_ax(self):
        src = (
            'def q : Char := \'"\'\n'
            "theorem after_char : False := by sorry\n"
            'def esc : Char := \'\\\'\'\n'
            'def raw_backslash : String := r"\\"\n'
            "theorem after_raw : False := by admit\n"
            'def raw_hash : String := r#"still " raw "#\n'
            'def interp_s : String := s!"val={sorry}"\n'
            'def interp_m : String := m!"ok {if true then admit else 0} lit sorry"\n'
            "def direct_ax : False := sorryAx False false\n"
        )
        findings = scan_lean_source(src, "lexer_edges.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [
                (2, "sorry"),
                (5, "admit"),
                (7, "sorry"),
                (8, "admit"),
                (9, "sorryAx"),
            ],
        )

    def test_lean_prefix_negation_before_string_with_brace_not_interp(self):
        src = (
            'def x : Bool := !"{".isEmpty\n'
            "theorem bad : False := by sorry\n"
            'def y : Bool := (!"{".isEmpty)\n'
            "theorem bad2 : False := by admit\n"
        )
        findings = scan_lean_source(src, "neg_string.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (4, "admit")],
        )

    def test_lean_french_quoted_identifiers_do_not_swallow_following_sorry(self):
        src = (
            "def «/-» : Nat := 0\n"
            "theorem after_french_comment_open : False := by sorry\n"
            'def «"» : Nat := 0\n'
            "theorem after_french_quote : False := by admit\n"
            "def unclosed «\"/- \n"
            "theorem after_unclosed_french : False := sorryAx False false\n"
        )
        findings = scan_lean_source(src, "french_ident.lean")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (4, "admit"), (6, "sorryAx")],
        )

    def test_rust_template_after_earlier_cfg_test_block_is_still_scanned(self):
        rust_src = (
            "#[cfg(test)]\n"
            "mod early_tests {\n"
            '    const TEST_ONLY: &str = "theorem ignored : False := by sorry";\n'
            "}\n"
            'const PROD_AFTER_TEST: &str = "\\\n'
            'public theorem verify : False := by\\n  sorry\\n";\n'
        )
        lean_count, findings = scan_rust_template_source(
            rust_src, "early_cfg_test.rs"
        )
        self.assertEqual(lean_count, 1)
        self.assertEqual([(f.line, f.token) for f in findings], [(6, "sorry")])

    def test_rust_cfg_test_fields_variants_match_arms_and_generics(self):
        rust_src = (
            "struct Cfg {\n"
            "    #[cfg(test)]\n"
            "    debug: bool,\n"
            "    #[cfg(test)]\n"
            "    pub extra: bool,\n"
            "}\n"
            'const PROD_AFTER_STRUCT: &str = "theorem t1 : False := by sorry";\n'
            "enum Mode {\n"
            "    A,\n"
            "    #[cfg(test)]\n"
            "    B,\n"
            "}\n"
            'const PROD_AFTER_ENUM: &str = "theorem t2 : False := by admit";\n'
            "fn pick(x: u8) -> &'static str {\n"
            "    match x {\n"
            '        #[cfg(test)] 0 => "theorem ignored_arm : False := by sorry",\n'
            '        _ => "theorem t3 : False := by sorry",\n'
            "    }\n"
            "}\n"
            "fn pick_last(x: u8) -> &'static str {\n"
            "    match x {\n"
            '        0 => "ok",\n'
            '        #[cfg(test)] _ => "theorem ignored_last : False := by sorry"\n'
            "    }\n"
            "}\n"
            'const PROD_AFTER_MATCH: &str = "theorem t4 : False := by admit";\n'
            "#[cfg(test)]\n"
            "pub fn generic_test<T, U>() where T: Copy, U: Copy {\n"
            '    const X: &str = "public theorem ignored_fn : False := by sorry";\n'
            "}\n"
            'const PROD_AFTER_GENERIC_FN: &str = "theorem t5 : False := by sorry";\n'
        )
        lean_count, findings = scan_rust_template_source(
            rust_src, "cfg_test_variants.rs"
        )
        self.assertEqual(lean_count, 5)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [
                (7, "sorry"),
                (13, "admit"),
                (17, "sorry"),
                (26, "admit"),
                (31, "sorry"),
            ],
        )

    def test_rust_concat_macro_evaluated_and_non_literal_fails_closed(self):
        rust_src = (
            'const OK: &str = concat!("-- no sorry\\n", "public theorem ok : True := True.intro\\n");\n'
            'const SPLIT_SORRY: &str = concat!("theorem bad1 : False := by sor", "ry\\n");\n'
            'const SPLIT_ADMIT: &str = concat!(r#"theorem bad2 : False := by ad"#, "mit\\n");\n'
            'const DYNAMIC: &str = concat!("theorem bad3 : False := ", DYNAMIC_TOKEN);\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "concat_init.rs")
        self.assertGreaterEqual(lean_count, 3)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(4, "concat!"), (2, "sorry"), (3, "admit")],
        )

    def test_rust_char_literal_quote_does_not_hide_following_sorry(self):
        rust_src = (
            "fn q() -> char { '\"' }\n"
            "const B: u8 = b'\"';\n"
            'const T: &str = "theorem t : False := by sorry";\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "char_quote.rs")
        self.assertEqual(lean_count, 1)
        self.assertEqual([(f.line, f.token) for f in findings], [(3, "sorry")])

    def test_rust_c_raw_and_c_string_literals_handled(self):
        rust_src = (
            'const X: &core::ffi::CStr = cr#"foo\\"#;\n'
            'const Y: &str = "theorem t : False := by sorry";\n'
            'const Z: &core::ffi::CStr = c"theorem t2 : False := by admit";\n'
        )
        lean_count, findings = scan_rust_template_source(rust_src, "c_strings.rs")
        self.assertEqual(lean_count, 2)
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(2, "sorry"), (3, "admit")],
        )

    def test_checks_toml_anneal_ci_tests_inputs_cover_scanned_trees(self):
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        self.assertIn("anneal-ci-tests", checks)
        includes = {
            pat
            for inp in checks["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        for required in ("anneal/**", "zerocopy/proofs/**", "ci/checks.toml"):
            self.assertIn(required, includes)

    def test_rust_hex_and_unicode_escapes_decoded_and_malformed_rejected(self):
        rust_src = (
            'const HEX: &str = "theorem bad1 : False := by \\x73orry";\n'
            'const UNI1: &str = "theorem bad2 : False := by \\u{73}orry";\n'
            'const UNI2: &str = "theorem bad3 : False := by \\u{00_61}dmit";\n'
            'const BAD_ESC: &str = "theorem bad4 : False := by \\xZZ";\n'
        )
        _, findings = scan_rust_template_source(rust_src, "escapes_init.rs")
        self.assertEqual(
            [(f.line, f.token) for f in findings],
            [(4, "escape"), (1, "sorry"), (2, "sorry"), (3, "admit")],
        )

    def test_python_scaffold_detects_sorry_admit_fstrings_and_implicit_concat(self):
        py_src = (
            "# Python comment: never emit sorry or admit\n"
            'CLEAN = "-- Lean comment with sorry\\ntheorem ok : True := True.intro\\n"\n'
            'BAD_SORRY = "theorem bad1 : False := by sorry"\n'
            'BAD_ADMIT = """theorem bad2 : False := by\n  admit\n"""\n'
            'IMPLICIT_CONCAT = ("theorem bad3 : False := by sor" "ry")\n'
            'FSTR_MULTILINE = f"""theorem verify : Expected.claim := by\n  sorry\n"""\n'
            'FSTR_INTERP = f"theorem {name} : False := by admit"\n'
            'FSTR_CONST_SPLIT = f"theorem bad4 : False := by sor{\'\'}ry"\n'
        )
        findings = scan_python_scaffold_source(py_src, "anneal_scaffold.py")
        self.assertEqual(
            [f.token for f in findings],
            ["sorry", "admit", "sorry", "sorry", "admit", "sorry"],
        )

        # Malformed Python syntax in scaffold must fail closed rather than pass.
        bad_py = scan_python_scaffold_source("def broken(:\n", "broken.py")
        self.assertEqual([f.token for f in bad_py], ["SyntaxError"])


if __name__ == "__main__":
    unittest.main()
