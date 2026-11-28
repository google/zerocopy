# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Parsing and verification of `SpecAnchor` records."""

from __future__ import annotations

import os
from pathlib import Path
from typing import Any

from .common import (
    LOCKED_SPEC_ANCHOR_COUNT, SpecAnchor, Token, VerificationError,
    _require_regular_file, _resolve_regular_dir, _walk_error,
    _walk_non_symlink_dirs,
)
from .lean_lexer import lex_lean
from .lean_hygiene import extract_declared_symbols


EXPECTED_ANCHOR_FIELDS = frozenset({"id", "leanSymbol", "specFile", "excerpt"})


def _eval_string_expr(
    tokens: list[Token], path: str, field_name: str, line: int
) -> str:
    """Evaluate a Lean string literal or `++`-joined string literals."""
    if not tokens:
        raise VerificationError(
            f"{path}:{line}: SpecAnchor field {field_name!r} is empty"
        )
    parts: list[str] = []
    expect_string = True
    for tok in tokens:
        if expect_string:
            if tok.kind != "STRING":
                raise VerificationError(
                    f"{path}:{tok.line}:{tok.col}: SpecAnchor field "
                    f"{field_name!r} must be a string literal, "
                    f"got {tok.value!r}"
                )
            parts.append(tok.value)
            expect_string = False
        else:
            if tok.kind == "OP" and tok.value == "++":
                expect_string = True
            else:
                raise VerificationError(
                    f"{path}:{tok.line}:{tok.col}: unexpected token "
                    f"{tok.value!r} in SpecAnchor field {field_name!r}"
                )
    if expect_string:
        raise VerificationError(
            f"{path}:{line}: trailing `++` in SpecAnchor field {field_name!r}"
        )
    return "".join(parts)


def _find_matching_delim(
    tokens: list[Token],
    open_idx: int,
    open_ch: str,
    close_ch: str,
    path: str,
) -> int:
    depth = 0
    for idx in range(open_idx, len(tokens)):
        tok = tokens[idx]
        if tok.kind == "PUNCT" and tok.value == open_ch:
            depth += 1
        elif tok.kind == "PUNCT" and tok.value == close_ch:
            depth -= 1
            if depth == 0:
                return idx
    open_tok = tokens[open_idx]
    raise VerificationError(
        f"{path}:{open_tok.line}:{open_tok.col}: "
        f"unmatched `{open_ch}` in Anchors.lean"
    )


def _parse_record_fields(
    inner: list[Token], path: str, open_line: int
) -> dict[str, tuple[int, list[Token]]]:
    """Parse strict `<ident> := <rhs>` bindings inside a `{ ... }` record."""
    fields: dict[str, tuple[int, list[Token]]] = {}
    idx = 0
    n = len(inner)
    while idx < n:
        tok = inner[idx]
        if not (
            tok.kind == "IDENT"
            and idx + 1 < n
            and inner[idx + 1].kind == "OP"
            and inner[idx + 1].value == ":="
        ):
            raise VerificationError(
                f"{path}:{tok.line}:{tok.col}: expected `<field> := <expr>` "
                f"in SpecAnchor record, got {tok.value!r}"
            )
        field_name = tok.value
        if field_name in fields:
            raise VerificationError(
                f"{path}:{tok.line}:{tok.col}: duplicate field "
                f"{field_name!r} in SpecAnchor record"
            )
        field_line = tok.line
        rhs_start = idx + 2
        rhs_depth = 0
        pos = rhs_start
        while pos < n:
            cur = inner[pos]
            if cur.kind == "PUNCT" and cur.value in ("(", "[", "{"):
                rhs_depth += 1
                pos += 1
                continue
            if cur.kind == "PUNCT" and cur.value in (")", "]", "}"):
                rhs_depth = max(0, rhs_depth - 1)
                pos += 1
                continue
            if rhs_depth == 0:
                if cur.kind == "PUNCT" and cur.value == ",":
                    break
                if (
                    cur.kind == "IDENT"
                    and pos + 1 < n
                    and inner[pos + 1].kind == "OP"
                    and inner[pos + 1].value == ":="
                ):
                    break
            pos += 1
        fields[field_name] = (field_line, inner[rhs_start:pos])
        idx = pos + 1 if (pos < n and inner[pos].value == ",") else pos

    if not fields:
        raise VerificationError(
            f"{path}:{open_line}: empty SpecAnchor record literal"
        )
    return fields


def parse_spec_anchors(
    source: str, path: Path | str = "<input>"
) -> list[SpecAnchor]:
    """Extract all `SpecAnchor` records from `Anchors.lean` source text.

    Enforces strict `{ id := ..., leanSymbol := ..., specFile := ...,
    excerpt := ... }` record literals inside `def specAnchors`, rejecting
    `⟨...⟩`, `where`, and `SpecAnchor.mk` constructor forms so unparsed
    anchors can never fail open.
    """
    path_str = str(path)
    tokens = lex_lean(source, path_str)
    n = len(tokens)

    for idx, tok in enumerate(tokens):
        if tok.value in ("⟨", "⟩"):
            raise VerificationError(
                f"{path_str}:{tok.line}:{tok.col}: anonymous constructor "
                f"`{tok.value}` is forbidden in Anchors.lean; use explicit "
                "`{ id := ..., leanSymbol := ..., specFile := ..., "
                "excerpt := ... }` records"
            )
        if tok.kind == "IDENT" and tok.value == "where":
            is_struct_decl = (
                idx >= 2
                and tokens[idx - 2].kind == "IDENT"
                and tokens[idx - 2].value == "structure"
                and tokens[idx - 1].kind == "IDENT"
                and tokens[idx - 1].value == "SpecAnchor"
            )
            if not is_struct_decl:
                raise VerificationError(
                    f"{path_str}:{tok.line}:{tok.col}: `where` constructor "
                    "form is forbidden in Anchors.lean; put all SpecAnchor "
                    "records as `{ ... }` literals in `specAnchors`"
                )
        if (
            tok.kind == "IDENT"
            and tok.value == "SpecAnchor"
            and idx + 2 < n
            and tokens[idx + 1].kind == "PUNCT"
            and tokens[idx + 1].value == "."
            and tokens[idx + 2].kind == "IDENT"
            and tokens[idx + 2].value == "mk"
        ):
            raise VerificationError(
                f"{path_str}:{tok.line}:{tok.col}: `SpecAnchor.mk` "
                "constructor form is forbidden in Anchors.lean; use explicit "
                "`{ id := ..., leanSymbol := ..., specFile := ..., "
                "excerpt := ... }` records"
            )

    # Locate `def specAnchors ... := [ ... ]`.
    list_open_idx: int | None = None
    for idx, tok in enumerate(tokens):
        if (
            tok.kind == "IDENT"
            and tok.value == "def"
            and idx + 1 < n
            and tokens[idx + 1].kind == "IDENT"
            and tokens[idx + 1].value == "specAnchors"
        ):
            pos = idx + 2
            while pos < n and not (
                tokens[pos].kind == "OP" and tokens[pos].value == ":="
            ):
                pos += 1
            if (
                pos + 1 >= n
                or tokens[pos + 1].kind != "PUNCT"
                or tokens[pos + 1].value != "["
            ):
                raise VerificationError(
                    f"{path_str}:{tok.line}: `def specAnchors` must be "
                    "defined directly as a `[ ... ]` list literal"
                )
            list_open_idx = pos + 1
            break

    if list_open_idx is None:
        raise VerificationError(
            f"{path_str}: missing `def specAnchors := [ ... ]` list"
        )

    list_close_idx = _find_matching_delim(
        tokens, list_open_idx, "[", "]", path_str
    )

    # Reject any stray `{ ... }` record literal outside `specAnchors`.
    outside = tokens[:list_open_idx] + tokens[list_close_idx + 1 :]
    for tok in outside:
        if tok.kind == "PUNCT" and tok.value == "{":
            raise VerificationError(
                f"{path_str}:{tok.line}:{tok.col}: `{{` record literal "
                "outside `specAnchors` is forbidden in Anchors.lean"
            )

    anchors: list[SpecAnchor] = []
    pos = list_open_idx + 1
    while pos < list_close_idx:
        tok = tokens[pos]
        if tok.kind == "PUNCT" and tok.value == ",":
            pos += 1
            continue
        if tok.kind != "PUNCT" or tok.value != "{":
            raise VerificationError(
                f"{path_str}:{tok.line}:{tok.col}: every `specAnchors` "
                f"element must be a `{{ ... }}` record literal, got "
                f"{tok.value!r}"
            )
        close_brace = _find_matching_delim(tokens, pos, "{", "}", path_str)
        inner = tokens[pos + 1 : close_brace]
        fields = _parse_record_fields(inner, path_str, tok.line)
        missing_fields = sorted(EXPECTED_ANCHOR_FIELDS - set(fields))
        unknown_fields = sorted(set(fields) - EXPECTED_ANCHOR_FIELDS)
        if missing_fields:
            raise VerificationError(
                f"{path_str}:{tok.line}: SpecAnchor record missing required "
                "field(s): " + ", ".join(missing_fields)
            )
        if unknown_fields:
            raise VerificationError(
                f"{path_str}:{tok.line}: SpecAnchor record has unexpected "
                "field(s): " + ", ".join(unknown_fields)
            )

        id_line, id_toks = fields["id"]
        sym_line, sym_toks = fields["leanSymbol"]
        sf_line, sf_toks = fields["specFile"]
        ex_line, ex_toks = fields["excerpt"]

        anchor_id = _eval_string_expr(id_toks, path_str, "id", id_line)
        lean_symbol = _eval_string_expr(
            sym_toks, path_str, "leanSymbol", sym_line
        )
        spec_file = _eval_string_expr(sf_toks, path_str, "specFile", sf_line)
        excerpt = _eval_string_expr(ex_toks, path_str, "excerpt", ex_line)

        anchors.append(
            SpecAnchor(
                anchor_id=anchor_id,
                lean_symbol=lean_symbol,
                spec_file=spec_file,
                excerpt=excerpt,
                line=tok.line,
            )
        )
        pos = close_brace + 1
        if pos < list_close_idx:
            if tokens[pos].kind != "PUNCT" or tokens[pos].value != ",":
                raise VerificationError(
                    f"{path_str}:{tokens[pos].line}:{tokens[pos].col}: "
                    "expected `,` between SpecAnchor records"
                )
            pos += 1

    return anchors


def collect_minirust_declared_symbols(minirust_corr: Path) -> set[str]:
    """Collect declared Lean symbols across `Anneal/MiniRust/*.lean`
    (excluding `Anchors.lean`).
    """
    declared: set[str] = set()
    for dirpath, _, filenames in os.walk(
        minirust_corr, followlinks=False, onerror=_walk_error
    ):
        base = Path(dirpath)
        for name in sorted(filenames):
            if not name.endswith(".lean") or name == "Anchors.lean":
                continue
            lean_file = _require_regular_file(base / name, name)
            declared |= extract_declared_symbols(
                lean_file.read_text(encoding="utf-8"), lean_file
            )
    return declared


def verify_spec_anchors(
    repo_root: Path,
    pin: dict[str, Any],
    *,
    expected_count: int | None = LOCKED_SPEC_ANCHOR_COUNT,
) -> list[SpecAnchor]:
    """Verify `SpecAnchor` records in `Anchors.lean` against Lean declarations
    and pinned upstream specification files.
    """
    real_root = _resolve_regular_dir(repo_root, "repo root")
    minirust_corr = _walk_non_symlink_dirs(
        real_root, ("correspondence", "Anneal", "MiniRust")
    )
    anchors_path = _require_regular_file(
        minirust_corr / "Anchors.lean",
        "correspondence/Anneal/MiniRust/Anchors.lean",
    )
    vendor_dir = _walk_non_symlink_dirs(real_root, ("vendor", "minirust"))
    pinned_files: dict[str, str] = pin["files"]

    source = anchors_path.read_text(encoding="utf-8")
    anchors = parse_spec_anchors(source, anchors_path)
    if not anchors:
        raise VerificationError(f"{anchors_path}: no SpecAnchor records found")

    if expected_count is not None and len(anchors) != expected_count:
        raise VerificationError(
            f"{anchors_path}: SpecAnchor count {len(anchors)} does not match "
            f"expected locked count {expected_count}"
        )

    declared_symbols = collect_minirust_declared_symbols(minirust_corr)

    spec_cache: dict[str, str] = {}
    seen_ids: dict[str, int] = {}
    failures: list[str] = []

    for anchor in anchors:
        label = anchor.anchor_id or f"line {anchor.line}"
        if not anchor.anchor_id.strip():
            failures.append(
                f"{anchors_path}:{anchor.line}: SpecAnchor `id` must be "
                "non-empty"
            )
        elif anchor.anchor_id in seen_ids:
            failures.append(
                f"{anchors_path}:{anchor.line}: duplicate SpecAnchor id "
                f"{anchor.anchor_id!r} (first seen at line "
                f"{seen_ids[anchor.anchor_id]})"
            )
        else:
            seen_ids[anchor.anchor_id] = anchor.line

        if not anchor.lean_symbol.strip():
            failures.append(
                f"{anchors_path}:{anchor.line} ({label}): `leanSymbol` must "
                "be non-empty"
            )
        elif anchor.lean_symbol not in declared_symbols:
            failures.append(
                f"{anchors_path}:{anchor.line} ({label}): leanSymbol "
                f"{anchor.lean_symbol!r} does not resolve to a declared "
                "symbol in correspondence/Anneal/MiniRust/*.lean"
            )

        if anchor.spec_file not in pinned_files:
            failures.append(
                f"{anchors_path}:{anchor.line} ({label}): specFile "
                f"{anchor.spec_file!r} is not in "
                "vendor/minirust/UPSTREAM_PIN.json"
            )
            continue

        if not anchor.excerpt.strip():
            failures.append(
                f"{anchors_path}:{anchor.line} ({label}): excerpt must be "
                "non-empty"
            )
            continue

        if anchor.spec_file not in spec_cache:
            spec_path = vendor_dir / anchor.spec_file
            spec_cache[anchor.spec_file] = spec_path.read_text(encoding="utf-8")

        if anchor.excerpt not in spec_cache[anchor.spec_file]:
            preview = anchor.excerpt
            if len(preview) > 80:
                preview = preview[:77] + "..."
            failures.append(
                f"{anchors_path}:{anchor.line} ({label}): excerpt {preview!r} "
                f"not found verbatim in vendor/minirust/{anchor.spec_file}"
            )

    if failures:
        raise VerificationError(
            "SpecAnchor verification failed:\n  " + "\n  ".join(failures)
        )

    return anchors
