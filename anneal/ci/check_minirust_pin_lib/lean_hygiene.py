# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Lean declaration scanning and hygiene checks for the MiniRust modules."""

from __future__ import annotations

import os
from pathlib import Path
import stat

from .common import (
    COMPILED_ARTIFACT_SUFFIXES, FORBIDDEN_CODE_TOKENS,
    FORBIDDEN_IMPORT_PREFIXES, LEAN_COMMAND_STARTERS, MAX_LEAN_LINES,
    REQUIRED_EXPORTED_THEOREMS, Token, VerificationError, _require_regular_file,
    _resolve_regular_dir, _walk_error, _walk_non_symlink_dirs,
)
from .lean_lexer import lex_lean


def _read_dotted_ident(tokens: list[Token], idx: int) -> tuple[list[str], int]:
    """Read `IDENT ('.' IDENT)*` at `idx`; return `(parts, next_idx)`."""
    if idx >= len(tokens) or tokens[idx].kind != "IDENT":
        return [], idx
    parts = [tokens[idx].value]
    pos = idx + 1
    while (
        pos + 1 < len(tokens)
        and tokens[pos].kind == "PUNCT"
        and tokens[pos].value == "."
        and tokens[pos + 1].kind == "IDENT"
    ):
        parts.append(tokens[pos + 1].value)
        pos += 2
    return parts, pos


def _scan_lean_declarations(
    source: str,
    path: Path | str = "<input>",
    *,
    decl_keywords: frozenset[str],
    include_private: bool,
    include_exports: bool,
) -> list[str]:
    """Extract qualified top-level Lean declarations matching
    `decl_keywords`.
    """
    tokens = lex_lean(source, str(path))
    scopes: list[tuple[str, list[str]]] = []
    collected: list[str] = []
    seen: set[str] = set()

    def current_ns() -> list[str]:
        ns: list[str] = []
        for kind, parts in scopes:
            if kind == "namespace":
                ns.extend(parts)
        return ns

    def record(qual: str) -> None:
        if qual not in seen:
            seen.add(qual)
            collected.append(qual)

    depth = 0
    decl_is_private = False
    idx = 0
    n = len(tokens)
    decl_modifiers = frozenset(
        {
            "protected",
            "public",
            "noncomputable",
            "scoped",
            "local",
            "meta",
            "partial",
            "unsafe",
        }
    )

    while idx < n:
        tok = tokens[idx]
        if tok.kind == "PUNCT" and tok.value in ("(", "[", "{"):
            depth += 1
            idx += 1
            continue
        if tok.kind == "PUNCT" and tok.value in (")", "]", "}"):
            depth = max(0, depth - 1)
            idx += 1
            continue

        if depth > 0:
            idx += 1
            continue

        prev_is_dot = (
            idx > 0
            and tokens[idx - 1].kind == "PUNCT"
            and tokens[idx - 1].value == "."
        )

        if tok.kind == "PUNCT" and tok.value == "@":
            idx += 1
            continue

        if tok.kind == "IDENT" and not prev_is_dot:
            val = tok.value
            if val == "private":
                decl_is_private = True
                idx += 1
                continue
            if val in decl_modifiers:
                idx += 1
                continue
            if val == "namespace":
                decl_is_private = False
                parts, next_idx = _read_dotted_ident(tokens, idx + 1)
                if parts:
                    scopes.append(("namespace", parts))
                    idx = next_idx
                    continue
            if val == "section":
                decl_is_private = False
                if (
                    idx + 1 < n
                    and tokens[idx + 1].kind == "IDENT"
                    and tokens[idx + 1].line == tok.line
                    and tokens[idx + 1].value not in LEAN_COMMAND_STARTERS
                ):
                    parts, next_idx = _read_dotted_ident(tokens, idx + 1)
                    scopes.append(("section", parts))
                    idx = next_idx
                    continue
                scopes.append(("section", []))
                idx += 1
                continue
            if val == "mutual":
                decl_is_private = False
                scopes.append(("mutual", []))
                idx += 1
                continue
            if val == "end":
                decl_is_private = False
                if (
                    idx + 1 < n
                    and tokens[idx + 1].kind == "IDENT"
                    and tokens[idx + 1].line == tok.line
                    and tokens[idx + 1].value not in LEAN_COMMAND_STARTERS
                ):
                    parts, next_idx = _read_dotted_ident(tokens, idx + 1)
                    remaining = list(parts)
                    while remaining and scopes:
                        kind, top_parts = scopes.pop()
                        if not top_parts:
                            continue
                        if len(remaining) >= len(top_parts) and remaining[
                            -len(top_parts) :
                        ] == top_parts:
                            remaining = remaining[: -len(top_parts)]
                        elif (
                            len(top_parts) > len(remaining)
                            and top_parts[-len(remaining) :] == remaining
                        ):
                            scopes.append(
                                (kind, top_parts[: -len(remaining)])
                            )
                            remaining = []
                        else:
                            break
                    idx = next_idx
                    continue
                if scopes:
                    scopes.pop()
                idx += 1
                continue
            if val in decl_keywords:
                is_priv = decl_is_private
                decl_is_private = False
                parts, next_idx = _read_dotted_ident(tokens, idx + 1)
                if parts and (include_private or not is_priv):
                    record(".".join(current_ns() + parts))
                idx = next_idx
                continue
            if include_exports and val == "export":
                decl_is_private = False
                _, next_idx = _read_dotted_ident(tokens, idx + 1)
                if (
                    next_idx < n
                    and tokens[next_idx].kind == "PUNCT"
                    and tokens[next_idx].value == "("
                ):
                    pos = next_idx + 1
                    while pos < n and not (
                        tokens[pos].kind == "PUNCT" and tokens[pos].value == ")"
                    ):
                        if tokens[pos].kind == "IDENT":
                            record(".".join(current_ns() + [tokens[pos].value]))
                        pos += 1
                    idx = pos + 1
                    continue

        decl_is_private = False
        idx += 1

    return collected


def extract_exported_theorems(
    source: str, path: Path | str = "<input>"
) -> list[str]:
    """Extract qualified non-private top-level theorem names from Lean text."""
    return _scan_lean_declarations(
        source,
        path,
        decl_keywords=frozenset({"theorem", "lemma"}),
        include_private=False,
        include_exports=False,
    )


def extract_declared_symbols(
    source: str, path: Path | str = "<input>"
) -> set[str]:
    """Extract qualified non-private top-level declarations from Lean text."""
    return set(
        _scan_lean_declarations(
            source,
            path,
            decl_keywords=frozenset(
                {
                    "def",
                    "abbrev",
                    "inductive",
                    "structure",
                    "class",
                    "theorem",
                    "lemma",
                }
            ),
            include_private=False,
            include_exports=True,
        )
    )


# ---------------------------------------------------------------------------
# Lean module hygiene check (`--check-lean`)
# ---------------------------------------------------------------------------


def _is_forbidden_import(module_name: str) -> bool:
    for prefix in FORBIDDEN_IMPORT_PREFIXES:
        if module_name == prefix or module_name.startswith(prefix + "."):
            return True
    return False


def check_lean_file_hygiene(
    path: Path, *, max_lines: int = MAX_LEAN_LINES
) -> list[str]:
    """Return a list of hygiene violation messages for a single `.lean` file."""
    violations: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        return [f"{path}: cannot read UTF-8 source: {exc}"]

    line_count = len(text.splitlines())
    if line_count > max_lines:
        violations.append(
            f"{path}: exceeds line limit ({line_count} > {max_lines})"
        )

    try:
        tokens = lex_lean(text, path)
    except VerificationError as exc:
        violations.append(str(exc))
        return violations

    for idx, tok in enumerate(tokens):
        prev_is_dot = (
            idx > 0
            and tokens[idx - 1].kind == "PUNCT"
            and tokens[idx - 1].value == "."
        )
        if tok.kind == "IDENT" and tok.value == "import" and not prev_is_dot:
            next_idx = idx + 1
            if (
                next_idx < len(tokens)
                and tokens[next_idx].kind == "IDENT"
                and tokens[next_idx].value == "all"
                and next_idx + 1 < len(tokens)
                and tokens[next_idx + 1].kind == "IDENT"
                and tokens[next_idx + 1].value not in LEAN_COMMAND_STARTERS
            ):
                next_idx += 1
            parts, _ = _read_dotted_ident(tokens, next_idx)
            if parts:
                mod_name = ".".join(parts)
                if _is_forbidden_import(mod_name):
                    violations.append(
                        f"{path}:{tok.line}:{tok.col}: forbidden import "
                        f"{mod_name!r} (MiniRust must remain independent of "
                        "lean-miri, Trusted.Correspondence, and Anneal.MirWp)"
                    )

        if tok.kind == "IDENT" and tok.value in FORBIDDEN_CODE_TOKENS:
            violations.append(
                f"{path}:{tok.line}:{tok.col}: forbidden Lean token "
                f"{tok.value!r}"
            )

    return violations


def _is_compiled_artifact(filename: str) -> bool:
    return any(
        filename.endswith(suffix) for suffix in COMPILED_ARTIFACT_SUFFIXES
    )


def verify_lean_hygiene(
    repo_root: Path,
    *,
    max_lines: int = MAX_LEAN_LINES,
    require_exported_theorems: bool = True,
) -> list[Path]:
    """Verify Lean hygiene for `Anneal/MiniRust/**` and `MiniRustProof.lean`."""
    real_root = _resolve_regular_dir(repo_root, "repo root")
    anneal_dir = _walk_non_symlink_dirs(real_root, ("correspondence", "Anneal"))
    minirust_dir = _walk_non_symlink_dirs(anneal_dir, ("MiniRust",))
    proof_file = _require_regular_file(
        anneal_dir / "MiniRustProof.lean",
        "correspondence/Anneal/MiniRustProof.lean",
    )

    for entry in sorted(anneal_dir.iterdir(), key=lambda p: p.name):
        name = entry.name
        if not name.startswith("MiniRustProof."):
            continue
        mode = entry.lstat().st_mode
        if stat.S_ISLNK(mode):
            raise VerificationError(
                f"symlink forbidden in correspondence/Anneal: {name}"
            )
        if _is_compiled_artifact(name):
            raise VerificationError(
                f"compiled artifact forbidden in correspondence/Anneal: {name}"
            )

    lean_files: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(
        minirust_dir, followlinks=False, onerror=_walk_error
    ):
        base = Path(dirpath)
        for name in sorted(dirnames) + sorted(filenames):
            entry = base / name
            mode = entry.lstat().st_mode
            rel = entry.relative_to(real_root).as_posix()
            if stat.S_ISLNK(mode):
                raise VerificationError(
                    f"symlink forbidden in {minirust_dir.name}: {rel}"
                )
            if stat.S_ISDIR(mode):
                continue
            if not stat.S_ISREG(mode):
                raise VerificationError(
                    f"unexpected special file in correspondence tree: {rel}"
                )
            if _is_compiled_artifact(name):
                raise VerificationError(
                    f"compiled artifact forbidden in correspondence tree: {rel}"
                )
            if name.endswith(".lean"):
                lean_files.append(entry)

    if not lean_files:
        raise VerificationError(
            "no .lean files found under correspondence/Anneal/MiniRust"
        )

    lean_files.sort()
    lean_files.append(proof_file)

    all_violations: list[str] = []
    for lean_path in lean_files:
        all_violations.extend(
            check_lean_file_hygiene(lean_path, max_lines=max_lines)
        )

    if require_exported_theorems and not all_violations:
        exported = set(
            extract_exported_theorems(
                proof_file.read_text(encoding="utf-8"), proof_file
            )
        )
        missing = [
            thm for thm in REQUIRED_EXPORTED_THEOREMS if thm not in exported
        ]
        if missing:
            all_violations.append(
                f"{proof_file}: missing required exported theorem(s): "
                + ", ".join(missing)
            )

    if all_violations:
        raise VerificationError(
            "Lean module hygiene check failed:\n  " + "\n  ".join(all_violations)
        )

    return lean_files
