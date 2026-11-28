# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Python scaffold scanning: rebuild string constants, f-strings, and
implicit concatenations, then scan them as Lean."""

import ast

from .lean_scanner import scan_lean_source
from .support import HygieneFinding

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
