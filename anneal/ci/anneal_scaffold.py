#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic zero-TCB `AutoScaffold.lean` generator (`TargetRole::Proof`).

Reads `capture.json` emitted by `cargo-anneal verify --artifacts <dir>` (or runs
a temporary capture pass from `request.json`) and renders a deterministic,
`<= 100`-column `AutoScaffold.lean` module containing:
- Layer S1: collision-free identity-keyed `id_<slug>`, `body_<slug>`,
  `get_<slug>`, `adm_<slug>`, typed `ValidEntryArgs` inversion, unified
  `ok_<slug>` (`BodyVerified ∧ ScafReturnsTotal`), and `all_bodies_safe`;
- Layer S2: explicit `let s_k := mkState 0 k [...]` straight-line symbolic
  MIR stepping (zero `simp` splitters, emitting `set_option maxRecDepth 4096`
  only when captured `identity` strings or body lists exceed Lean's default
  reduction depth).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any

LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
# Longest slug `render_scaffold` emits. After wrapping, every generated line
# holds at most one slug-bearing identifier, so capping slugs keeps each line
# within the 100-column limit enforced at the end of `render_scaffold`.
MAX_SLUG_LEN = 64
LEAN_RESERVED = frozenset({
    "abbrev", "axiom", "by", "calc", "cases", "change", "class", "constructor",
    "def", "deriving", "do", "dsimp", "else", "end", "exact", "example",
    "extends", "false", "forall", "from", "fun", "funext", "have", "if",
    "import", "in", "induction", "inductive", "infix", "infixl", "infixr",
    "init", "instance", "intro", "lemma", "let", "local", "macro", "match",
    "meta", "module", "mutual", "namespace", "nomatch", "noncomputable",
    "notation", "nud", "open", "opaque", "partial", "postfix", "prefix",
    "prelude", "private", "protected", "public", "refine", "renaming",
    "repeat", "return", "revert", "rw", "rfl", "scoped", "section", "set_option",
    "show", "simp", "sorry", "structure", "subst", "syntax", "then", "theorem",
    "true", "unfold", "universe", "unsafe", "variable", "where", "with",
})

FUCHSIA_LEAN_HEADER = """\
-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms."""

UNIT_TY = {"kind": "unit"}
BOOL_TY = {"kind": "bool"}
ISIZE_TY = {"kind": "int", "width": "isize", "signed": False}
U64_TY = {"kind": "int", "width": "i64", "signed": False}


class ScaffoldError(RuntimeError):
    """Raised on malformed capture JSON, unsafe paths, or `--check` drift."""


def ensure_regular_nonsymlink(
    path: Path, label: str, root: Path | None = None
) -> None:
    """Reject a symlink at `path` and, given `root`, at each lexical ancestor
    strictly below `root`.

    Ancestors at or above `root` (and, without `root`, every ancestor) are
    deliberately not inspected: host layouts such as macOS `/var` or a
    symlinked `$HOME` legitimately place symlinks there, and the caller owns
    the trust decision for `root` itself.
    """
    if root is not None:
        try:
            rel_parts = path.relative_to(root).parts
        except ValueError as exc:
            raise ScaffoldError(f"{label} escapes {root}: {path}") from exc
        cur = root
        for part in rel_parts[:-1]:
            cur = cur / part
            if cur.is_symlink():
                raise ScaffoldError(f"{label} must not traverse a symlink: {cur}")
    if path.is_symlink():
        raise ScaffoldError(f"{label} must not be a symlink: {path}")


def load_strict_json(path: Path, label: str = "JSON") -> Any:
    """Parse UTF-8 JSON while rejecting symlinks, duplicate keys, and NaN/Inf."""
    ensure_regular_nonsymlink(path, label)
    if not path.is_file():
        raise ScaffoldError(f"missing {label}: {path}")

    def reject_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for key, val in pairs:
            if key in out:
                raise ScaffoldError(f"{path}: duplicate JSON key {key!r}")
            out[key] = val
        return out

    def reject_constants(tok: str) -> Any:
        raise ScaffoldError(f"{path}: forbidden JSON constant {tok!r}")

    try:
        text = path.read_text(encoding="utf-8")
        return json.loads(
            text,
            object_pairs_hook=reject_duplicates,
            parse_constant=reject_constants,
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ScaffoldError(f"invalid {label} at {path}: {exc}") from exc


def base_identity_slug(identity: str) -> str:
    """Derive a clean deterministic Lean identifier suffix from `identity`."""
    if not isinstance(identity, str) or not identity:
        raise ScaffoldError(f"invalid body identity: {identity!r}")
    short = identity.removeprefix("rust-path-v1::")
    if short == "util::macros::__unsafe":
        slug = "unsafe_macro"
    elif m := re.match(r"^<\(\) as PointerMetadata>::([A-Za-z0-9_]+)$", short):
        slug = f"unit_{m.group(1)}"
    elif m := re.match(r"^<usize as PointerMetadata>::([A-Za-z0-9_]+)$", short):
        slug = f"usize_{m.group(1)}"
    elif m := re.match(
        r"^impls::_::<impl ([A-Za-z0-9_]+) for ([A-Za-z0-9_]+)>::"
        r"only_derive_is_allowed_to_implement_this_trait$",
        short,
    ):
        slug = f"{m.group(2)}_{m.group(1)}_marker"
    else:
        slug = re.sub(r"[^A-Za-z0-9_]+", "_", short).strip("_")
    if not slug or slug[0].isdigit() or slug in LEAN_RESERVED:
        slug = f"item_{slug}" if slug else "item"
    if not LEAN_IDENT_RE.match(slug):
        raise ScaffoldError(f"cannot sanitize identity {identity!r} -> {slug!r}")
    if len(slug) > MAX_SLUG_LEN:
        # Keep a readable prefix and disambiguate it by the full identity.
        digest = hashlib.sha256(identity.encode("utf-8")).hexdigest()[:8]
        slug = f"{slug[:MAX_SLUG_LEN - 9].rstrip('_')}_{digest}"
    return slug


def assign_unique_slugs(bodies: list[dict[str, Any]]) -> list[str]:
    """Assign deterministic collision-free slugs, rejecting duplicate identities."""
    seen_identities: set[str] = set()
    used_slugs: set[str] = set(reserved_body_slugs())
    slugs: list[str] = []
    for body in bodies:
        if not isinstance(body, dict):
            raise ScaffoldError("capture program.bodies entry must be an object")
        identity = body.get("identity")
        if not isinstance(identity, str) or not identity:
            raise ScaffoldError(f"invalid body identity: {identity!r}")
        if identity in seen_identities:
            raise ScaffoldError(f"duplicate body identity in capture: {identity!r}")
        seen_identities.add(identity)
        base = base_identity_slug(identity)
        cand = base
        suffix = 2
        while cand in used_slugs:
            tag = f"_{suffix}"
            cand = f"{base[:MAX_SLUG_LEN - len(tag)]}{tag}"
            suffix += 1
        used_slugs.add(cand)
        slugs.append(cand)
    return slugs


def _parse_nonneg_int_bits(raw: Any) -> int | None:
    if isinstance(raw, bool):
        return None
    if isinstance(raw, int):
        return raw if raw >= 0 else None
    if isinstance(raw, str) and raw.isascii() and raw.isdecimal():
        return int(raw)
    return None


def _is_nop_or_storage(stmt: dict[str, Any], num_locals: int) -> tuple[str, int] | None:
    kind = stmt.get("kind")
    if kind == "nop":
        return ("nop", 0)
    if kind in ("storage_live", "storage_dead"):
        loc = stmt.get("local")
        if isinstance(loc, int) and not isinstance(loc, bool) and 1 <= loc < num_locals:
            return (kind, loc)
    return None


def _temps_start_dead(stmts: list[Any], arg_count: int, num_locals: int) -> bool:
    """Whether every temporary local starts `.dead` in `initLocalsLoop`.

    `Trusted.MirSemantics.initLocalsLoop` starts a temporary `.dead` only when
    the body carries a `StorageLive`/`StorageDead` marker for it
    (`hasStorageAnnotation`); otherwise it starts as `liveUninitSlot ty`. The
    symbolic tracers model every temporary as initially `.dead`, so they must
    reject bodies with unannotated temporaries.
    """
    annotated = {
        st.get("local")
        for st in stmts
        if isinstance(st, dict) and st.get("kind") in ("storage_live", "storage_dead")
    }
    return all(loc in annotated for loc in range(1 + arg_count, num_locals))


def analyze_unit0_ret(body: dict[str, Any]) -> int | None:
    """Detect a 0-arg `() -> ()` 1-block body returning unit in `fuel` steps."""
    blocks = body.get("blocks")
    tys = body.get("local_tys")
    if (
        not isinstance(blocks, list)
        or len(blocks) != 1
        or body.get("arg_count") != 0
        or not isinstance(tys, list)
        or not tys
        or tys[0] != UNIT_TY
    ):
        return None
    bb = blocks[0]
    if not isinstance(bb, dict) or bb.get("terminator") != {"kind": "ret"}:
        return None
    stmts = bb.get("statements")
    if not isinstance(stmts, list):
        return None
    for st in stmts:
        if not isinstance(st, dict):
            return None
        if _is_nop_or_storage(st, len(tys)) is not None:
            continue
        if st.get("kind") == "assign" and st.get("local") == 0 and not st.get("projection"):
            val = st.get("value", {})
            op = val.get("operand", {}) if isinstance(val, dict) else {}
            if (
                val.get("kind") == "use"
                and op.get("kind") == "constant"
                and op.get("ty") == UNIT_TY
                and op.get("lit") == {"kind": "zero_sized"}
            ):
                continue
        return None
    return len(stmts) + 2


def analyze_const_ret_1arg(body: dict[str, Any]) -> tuple[str, str, int] | None:
    """Detect a 1-arg (`unit` or `usize`) 1-block body returning a constant."""
    blocks = body.get("blocks")
    tys = body.get("local_tys")
    if (
        not isinstance(blocks, list)
        or len(blocks) != 1
        or body.get("arg_count") != 1
        or not isinstance(tys, list)
        or len(tys) < 2
    ):
        return None
    if tys[1] == UNIT_TY:
        arg_kind = "unit"
    elif tys[1] == ISIZE_TY:
        arg_kind = "isize"
    else:
        return None
    bb = blocks[0]
    if not isinstance(bb, dict) or bb.get("terminator") != {"kind": "ret"}:
        return None
    stmts = bb.get("statements")
    if not isinstance(stmts, list):
        return None
    ret_expr: str | None = None
    for st in stmts:
        if not isinstance(st, dict):
            return None
        if _is_nop_or_storage(st, len(tys)) is not None:
            continue
        if st.get("kind") == "assign" and st.get("local") == 0 and not st.get("projection"):
            val = st.get("value", {})
            op = val.get("operand", {}) if isinstance(val, dict) else {}
            if val.get("kind") != "use" or op.get("kind") != "constant":
                return None
            lit = op.get("lit", {}) if isinstance(op, dict) else {}
            if op.get("ty") == UNIT_TY and lit == {"kind": "zero_sized"} and tys[0] == UNIT_TY:
                ret_expr = ".unit"
                continue
            if op.get("ty") == ISIZE_TY and isinstance(lit, dict) and lit.get("kind") == "scalar":
                bits = _parse_nonneg_int_bits(lit.get("bits"))
                if bits is not None and bits < (1 << 64) and tys[0] == ISIZE_TY:
                    ret_expr = f"(scafUsizeVal (BitVec.ofNat 64 {bits}))"
                    continue
        return None
    if ret_expr is None:
        return None
    return arg_kind, ret_expr, len(stmts) + 2


def analyze_isize_copy_chain(body: dict[str, Any]) -> list[tuple[str, int, list[str]]] | None:
    """Symbolically trace a 1-arg `usize -> usize` storage/copy/move chain (`P1`)."""
    blocks = body.get("blocks")
    tys = body.get("local_tys")
    if (
        not isinstance(blocks, list)
        or len(blocks) != 1
        or body.get("arg_count") != 1
        or not isinstance(tys, list)
        or len(tys) < 2
        or any(t != ISIZE_TY for t in tys)
    ):
        return None
    bb = blocks[0]
    if not isinstance(bb, dict) or bb.get("terminator") != {"kind": "ret"}:
        return None
    stmts = bb.get("statements")
    if not isinstance(stmts, list):
        return None
    if not _temps_start_dead(stmts, 1, len(tys)):
        return None
    slots = ["none", "arg"] + ["dead"] * (len(tys) - 2)
    trace: list[tuple[str, int, list[str]]] = []
    for idx, st in enumerate(stmts):
        if not isinstance(st, dict):
            return None
        pc = idx + 1
        ns = _is_nop_or_storage(st, len(tys))
        if ns is not None:
            sk, loc = ns
            if sk == "storage_live":
                slots[loc] = "none"
            elif sk == "storage_dead":
                slots[loc] = "dead"
            trace.append(("rfl", pc, list(slots)))
            continue
        if st.get("kind") == "assign" and not st.get("projection"):
            dst = st.get("local")
            if not isinstance(dst, int) or isinstance(dst, bool) or not (0 <= dst < len(tys)):
                return None
            if slots[dst] == "dead":
                return None
            val = st.get("value", {})
            op = val.get("operand", {}) if isinstance(val, dict) else {}
            if (
                val.get("kind") != "use"
                or op.get("kind") not in ("copy", "move")
                or op.get("projection")
            ):
                return None
            src = op.get("local")
            if (
                not isinstance(src, int)
                or isinstance(src, bool)
                or not (0 <= src < len(tys))
                or slots[src] != "arg"
            ):
                return None
            if op["kind"] == "move" and src != dst:
                slots[src] = "none"
            slots[dst] = "arg"
            trace.append(("isize_use", pc, list(slots)))
            continue
        return None
    if slots[0] != "arg":
        return None
    return trace


def _resolve_u64_operand(
    op: Any, slots: list[tuple[str, str]]
) -> str | None:
    if not isinstance(op, dict) or op.get("projection"):
        return None
    kind = op.get("kind")
    if kind in ("copy", "move"):
        loc = op.get("local")
        if not isinstance(loc, int) or isinstance(loc, bool) or not (0 <= loc < len(slots)):
            return None
        sk, expr = slots[loc]
        if sk != "u64":
            return None
        if kind == "move":
            slots[loc] = ("none", "")
        return expr
    if kind == "constant" and op.get("ty") == U64_TY:
        lit = op.get("lit")
        if isinstance(lit, dict) and lit.get("kind") == "scalar":
            bits = _parse_nonneg_int_bits(lit.get("bits"))
            if bits is not None and bits < (1 << 64):
                return f"(BitVec.ofNat 64 {bits})"
    return None


def analyze_u64_straight_line(
    body: dict[str, Any],
) -> tuple[list[str], str, str, list[tuple[Any, ...]]] | None:
    """Symbolically lower a 1-block 1/2-arg `u64 -> u64|bool` MIR body (`P3`)."""
    blocks = body.get("blocks")
    tys = body.get("local_tys")
    arg_count = body.get("arg_count")
    if (
        not isinstance(blocks, list)
        or len(blocks) != 1
        or not isinstance(arg_count, int)
        or isinstance(arg_count, bool)
        or arg_count not in (1, 2)
        or not isinstance(tys, list)
        or len(tys) < 1 + arg_count
    ):
        return None
    if tys[0] == U64_TY:
        ret_kind = "u64"
    elif tys[0] == BOOL_TY:
        ret_kind = "bool"
    else:
        return None
    if any(tys[i] != U64_TY for i in range(1, 1 + arg_count)):
        return None
    # Every temporary must be a `u64` or `bool`, the only types whose
    # `Trusted.MirSemantics.liveUninitSlot` is `.immediate none`, which is how
    # `storage_live` is modeled below. ZST temporaries (`()`, single-variant
    # enums) start live as `.immediate (some _)` and must fall back to S1.
    if any(t not in (U64_TY, BOOL_TY) for t in tys[1 + arg_count:]):
        return None
    bb = blocks[0]
    if not isinstance(bb, dict) or bb.get("terminator") != {"kind": "ret"}:
        return None
    stmts = bb.get("statements")
    if not isinstance(stmts, list):
        return None
    if not _temps_start_dead(stmts, arg_count, len(tys)):
        return None

    arg_names = [f"a{i}" for i in range(arg_count)]
    slots: list[tuple[str, str]] = (
        [("none", "")]
        + [("u64", name) for name in arg_names]
        + [("dead", "")] * (len(tys) - 1 - arg_count)
    )
    trace: list[tuple[Any, ...]] = []

    for idx, st in enumerate(stmts):
        if not isinstance(st, dict):
            return None
        pc = idx + 1
        ns = _is_nop_or_storage(st, len(tys))
        if ns is not None:
            sk, loc = ns
            if sk == "storage_live":
                slots[loc] = ("none", "")
            elif sk == "storage_dead":
                slots[loc] = ("dead", "")
            trace.append(("rfl", pc, list(slots)))
            continue
        if st.get("kind") != "assign" or st.get("projection"):
            return None
        dst = st.get("local")
        if not isinstance(dst, int) or isinstance(dst, bool) or not (0 <= dst < len(tys)):
            return None
        if slots[dst][0] == "dead":
            return None
        val = st.get("value")
        if not isinstance(val, dict):
            return None
        vk = val.get("kind")
        if vk == "use" and tys[dst] == U64_TY:
            expr = _resolve_u64_operand(val.get("operand"), slots)
            if expr is None:
                return None
            slots[dst] = ("u64", expr)
            trace.append(("u64_use", pc, expr, list(slots)))
        elif vk == "unary" and val.get("op") == "not" and tys[dst] == U64_TY:
            expr = _resolve_u64_operand(val.get("operand"), slots)
            if expr is None:
                return None
            res = f"~~~({expr})" if not expr.isidentifier() else f"~~~{expr}"
            slots[dst] = ("u64", res)
            trace.append(("u64_not", pc, expr, res, list(slots)))
        elif vk == "binary" and val.get("op") in ("bit_and", "bit_or") and tys[dst] == U64_TY:
            op_name = val["op"]
            lx = _resolve_u64_operand(val.get("left"), slots)
            rx = _resolve_u64_operand(val.get("right"), slots)
            if lx is None or rx is None:
                return None
            sym = "&&&" if op_name == "bit_and" else "|||"
            lhs_s = lx if lx.isidentifier() else f"({lx})"
            rhs_s = rx if rx.isidentifier() else f"({rx})"
            res = f"{lhs_s} {sym} {rhs_s}"
            slots[dst] = ("u64", res)
            step_tag = "u64_and" if op_name == "bit_and" else "u64_or"
            trace.append((step_tag, pc, lx, rx, list(slots)))
        elif vk == "binary" and val.get("op") == "eq" and tys[dst] == BOOL_TY:
            right = val.get("right")
            if not isinstance(right, dict) or right.get("kind") != "constant":
                return None
            lx = _resolve_u64_operand(val.get("left"), slots)
            rx = _resolve_u64_operand(right, slots)
            if lx is None or rx is None:
                return None
            bits = _parse_nonneg_int_bits(right.get("lit", {}).get("bits"))
            if bits is None or bits >= (1 << 64):
                return None
            lhs_s = lx if lx.isidentifier() else f"({lx})"
            res = f"{lhs_s} == {rx}"
            slots[dst] = ("bool", res)
            trace.append(("u64_eq_const", pc, dst, lx, bits, list(slots)))
        else:
            return None

    if slots[0][0] != ret_kind:
        return None
    return arg_names, ret_kind, slots[0][1], trace


def _format_lean_list(
    items: list[str], indent: int = 4, max_col: int = 96, prefix_len: int | None = None
) -> str:
    single = "[" + ", ".join(items) + "]"
    head_len = indent if prefix_len is None else prefix_len
    if "\n" not in single and head_len + len(single) <= max_col:
        return single
    lines = ["["]
    cur = " " * (indent + 2)
    for idx, item in enumerate(items):
        piece = item + ("," if idx + 1 < len(items) else "")
        if cur.strip() and (
            "\n" in piece or "\n" in cur or len(cur) + 1 + len(piece) > max_col
        ):
            lines.append(cur)
            cur = " " * (indent + 2) + piece
        else:
            cur = (cur + " " + piece) if cur.strip() else (" " * (indent + 2) + piece)
    if cur.strip():
        lines.append(cur)
    lines.append(" " * indent + "]")
    return "\n".join(lines)


def _wrap_lean_expr(
    expr: str, cont_indent: str, max_col: int = 94, first_prefix_len: int = 0
) -> str:
    """Break long bitwise Lean expressions at binary operators when a line wraps."""
    if len(expr) + first_prefix_len <= max_col:
        return expr
    tokens: list[str] = []
    cur: list[str] = []
    i = 0
    while i < len(expr):
        matched = None
        for op in (" &&& ", " ||| ", " == "):
            if expr.startswith(op, i):
                matched = op
                break
        if matched is not None:
            tokens.append("".join(cur))
            tokens.append(matched)
            cur = []
            i += len(matched)
        else:
            cur.append(expr[i])
            i += 1
    tokens.append("".join(cur))
    if len(tokens) == 1:
        return expr
    lines: list[str] = []
    line = tokens[0]
    for j in range(1, len(tokens), 2):
        op = tokens[j]
        rhs = tokens[j + 1]
        limit = (max_col - first_prefix_len) if not lines else max_col
        if line.strip() and len(line) + len(op) + len(rhs) > limit:
            lines.append(line + op.rstrip())
            line = cont_indent + rhs
        else:
            line += op + rhs
    if line:
        lines.append(line)
    return "\n".join(lines)


def _two_line(lhs: str, rhs: str, cont_indent: str, max_col: int = 96) -> list[str]:
    """Emit `lhs rhs` on one line when <= `max_col`, else wrap onto `cont_indent`.

    If the two-line form still exceeds 100 columns (long slugs), greedily pack
    the space-separated words of `lhs` and `rhs` at `max_col` instead.
    """
    if len(lhs) + 1 + len(rhs) <= max_col:
        return [f"{lhs} {rhs}"]
    two = [lhs, f"{cont_indent}{rhs}"]
    if all(len(line) <= 100 for line in two):
        return two
    lines: list[str] = []
    cur = lhs[: len(lhs) - len(lhs.lstrip(" "))]
    for word in lhs.split() + rhs.split():
        if not cur.strip():
            cur += word
        elif len(cur) + 1 + len(word) <= max_col:
            cur += " " + word
        else:
            lines.append(cur)
            cur = cont_indent + word
    lines.append(cur)
    return lines


_REFLOW_OPS = (" &&& ", " ||| ", " == ")


def _bracketed_at(line: str, pos: int) -> bool:
    """Whether `pos` lies inside a `(...)`/`[...]` group that `line` opens or closes."""
    unmatched_open = 0
    for ch in line[:pos]:
        if ch in "([":
            unmatched_open += 1
        elif ch in ")]" and unmatched_open:
            unmatched_open -= 1
    if unmatched_open:
        return True
    unmatched_close = 0
    for ch in reversed(line[pos:]):
        if ch in ")]":
            unmatched_close += 1
        elif ch in "([" and unmatched_close:
            unmatched_close -= 1
    return unmatched_close > 0


def _reflow_long_line(line: str, limit: int = 100) -> list[str]:
    """Split a generated line longer than `limit` after bitwise/`==` operators.

    Only splits inside a bracketed term, where Lean ignores line breaks, and
    leaves lines it cannot shorten for the caller's column check to reject.
    """
    out: list[str] = []
    cont = " " * (len(line) - len(line.lstrip(" ")) + 4)
    while len(line) > limit:
        split = None
        for i in range(len(line)):
            for op in _REFLOW_OPS:
                if (
                    line.startswith(op, i)
                    and i + len(op.rstrip()) <= limit
                    and _bracketed_at(line, i)
                ):
                    split = (i, op)
        if split is None:
            break
        i, op = split
        rest = cont + line[i + len(op):]
        if len(rest) >= len(line):
            break
        out.append(line[:i] + op.rstrip())
        line = rest
    out.append(line)
    return out


def _isize_slots_items(slots: list[str]) -> list[str]:
    mapping = {
        "none": ".immediate none",
        "arg": ".immediate v_a0",
        "dead": ".dead",
    }
    return [mapping[s] for s in slots]


def _u64_slots_items(slots: list[tuple[str, str]], arg_names: list[str]) -> list[str]:
    out: list[str] = []
    for kind, expr in slots:
        if kind == "dead":
            out.append(".dead")
        elif kind == "none":
            out.append(".immediate none")
        elif kind == "u64":
            if expr in arg_names:
                out.append(f".immediate v_{expr}")
            else:
                single = f".immediate (some (scafU64Val ({expr})))"
                if len(single) + 7 <= 96:
                    out.append(single)
                else:
                    wrapped = _wrap_lean_expr(
                        expr, "        ", max_col=92, first_prefix_len=9
                    )
                    out.append(f".immediate (some (scafU64Val\n        ({wrapped})))")
        elif kind == "bool":
            single = f".immediate (some (Val.bool ({expr})))"
            if len(single) + 7 <= 96:
                out.append(single)
            else:
                wrapped = _wrap_lean_expr(
                    expr, "        ", max_col=92, first_prefix_len=9
                )
                out.append(f".immediate (some (Val.bool\n        ({wrapped})))")
        else:
            raise ScaffoldError(f"unexpected symbolic slot kind: {kind!r}")
    return out


COMMON_HELPERS = """\
abbrev ScafReturnsTotal (program : Program) (defId : DefId)
    (args : List Val) (ret : Val) : Prop :=
  let entry := entryProgForBody program defId
  let call : Query := { args := args }
  let expected := TerminalOut.returned ⟨ret, ⟨[]⟩⟩
  SatisfiesPost entry call (fun outcome => outcome = expected) ∧
    ¬ Diverges entry call ∧
    Behavior entry call expected

theorem ok_of_executes {p : Program} {d : DefId} {b : Body}
    {args : List Val} {ret : Val}
    (hb : Trusted.MirSemantics.getElem? p.bodies d = some b)
    (hadm : BodyStaticAdmitted p b = true)
    (hargs : ValidEntryArgs b args)
    (hexec :
      Executes b (mkState 0 0 (initLocalsLoop b args 0 b.locals)) ret) :
    WellFormed (entryProgForBody p d) { args := args } ∧
    ScafReturnsTotal p d args ret :=
  Exists.elim (executes_iff_wpState.mp hexec) fun _ hruns =>
    let h := spec_and_behavior_of_wp_eq (wpProg_of_execProg (by
      unfold execProg
      rw [initState_entryProgForBody hb hadm hargs]
      exact (execOutcomeState_entryProg_iff hb
        (isSingleFrame0_mkState 0 0 _)).mpr hruns))
    ⟨h.1, h.2.2.2 _ rfl, h.2.2.1, h.2.1⟩

theorem total_of_executes {defId : DefId} {body : Body}
    {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_exec :
      Executes body
        (mkState 0 0 (initLocalsLoop body args 0 body.locals)) ret) :
    ScafReturnsTotal Captured.program defId args ret :=
  (ok_of_executes h_body h_adm h_args h_exec).2

theorem total_of_runs {defId : DefId} {body : Body}
    {fuel : Nat} {args : List Val} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_args : ValidEntryArgs body args)
    (h_runs : Runs body fuel args ret) :
    ScafReturnsTotal Captured.program defId args ret :=
  total_of_executes h_body h_adm h_args (run_executes h_runs)"""

UNIT0_HELPER = """\
theorem unit0_ok {defId : DefId} {body : Body} {fuel : Nat}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [])
    (h_runs : Runs body fuel [] .unit) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ScafReturnsTotal Captured.program defId [] .unit := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_), ?_⟩
  · have hMatch : checkArgsMatch args [] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    have hNil : args = [] := checkArgsMatch_nil_iff.mp hMatch
    subst hNil
    exact (run_initial_success h_runs).1
  · have hArgs : ValidEntryArgs body [] := by
      unfold ValidEntryArgs
      rw [h_tys]
      rfl
    exact total_of_runs h_body h_adm hArgs h_runs"""

ISIZE_BASE_HELPERS = """\
abbrev scafUsizeVal (n : BitVec 64) : Val :=
  .scalar ⟨.isize, false, BitVec.ofNat 128 n.toNat⟩

theorem valid_isize_word (n : BitVec 64) :
    checkVal (scafUsizeVal n) (.int .isize false) = true := by
  refine checkVal_scalar_of_toNat_lt ?_
  change Nat.mod n.toNat (Nat.pow 2 128) < intWidthModulus .isize
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) n.isLt

theorem validEntry_isize1 {body : Body}
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (n : BitVec 64) :
    ValidEntryArgs body [scafUsizeVal n] := by
  unfold ValidEntryArgs
  rw [h_tys]
  exact checkArgsMatch_cons_iff.mpr ⟨_, [], rfl, valid_isize_word n, rfl⟩"""

CONST_1ARG_HELPERS = """\
theorem unit_const_1arg_ok {defId : DefId} {body : Body}
    {fuel : Nat} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys : (body.locals.drop 1).take body.argumentCount = [.unit])
    (h_runs : Runs body fuel [.unit] ret) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ScafReturnsTotal Captured.program defId [.unit] ret := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_), ?_⟩
  · have hMatch : checkArgsMatch args [.unit] = true := by
      unfold ValidEntryArgs at valid
      rw [h_tys] at valid
      exact valid
    let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
    have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
    have hUnit : v = .unit := checkVal_unit_iff.mp hv
    subst hEq; subst hNil; subst hUnit
    exact (run_initial_success h_runs).1
  · have hArgs : ValidEntryArgs body [.unit] := by
      unfold ValidEntryArgs
      rw [h_tys]
      rfl
    exact total_of_runs h_body h_adm hArgs h_runs

theorem isize_const_1arg_ok {defId : DefId} {body : Body}
    {fuel : Nat} {ret : Val}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (h_runs : ∀ v : Val, Runs body fuel [v] ret) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program defId [scafUsizeVal a0] ret := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_),
    fun a0 => total_of_runs h_body h_adm
      (validEntry_isize1 h_tys a0) (h_runs (scafUsizeVal a0))⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  let ⟨v, rest, hEq, _, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact (run_initial_success (h_runs v)).1"""

ISIZE_COPY_HELPERS = """\
def EvalAssignIsizeWith (body : Body) (s : State)
    (overrideVal : Val) (next : State) : Prop :=
  match s.frames with
  | [frame] =>
    match Nat.beq frame.defId 0 with
    | false => False
    | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => False
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection.isEmpty with
          | false => False
          | true =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => False
            | some dstTy =>
              match MirTy.beq dstTy (.int .isize false) with
              | false => False
              | true =>
                match evalRvalue body.locals frame.locals s.mem
                    dstTy rvalue with
                | .error _ => False
                | .ok (_, localsAfterRval, memAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | some (.immediate _) =>
                    match setElem? localsAfterRval dst.localId
                        (.immediate (some overrideVal)) with
                    | some localsAfterWrite =>
                      (.step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                        mem := memAfterRval
                      } : StepResult State TerminalOut) = .step next
                    | none => False
                  | _ => False
        | _ => False
  | _ => False

theorem step_isizeVal {body : Body} {s next : State} {v : Val}
    (hv : checkVal v (.int .isize false) = true)
    (h_val : EvalAssignVal body s v)
    (h_next : EvalAssignIsizeWith body s v next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold EvalAssignVal at h_val
  unfold EvalAssignIsizeWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next ⊢
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        rw [Nat.eq_of_beq_eq_true h_def]
        rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
        dsimp only
        cases h_bb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [h_bb] at h_next; cases h_next
        | some bb =>
          rw [h_bb] at h_val h_next
          dsimp only at h_val h_next ⊢
          cases h_st :
              Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | none => rw [h_st] at h_next; cases h_next
          | some stmt =>
            rw [h_st] at h_val h_next
            dsimp only
            cases stmt with
            | nop | storageLive _ | storageDead _ | unsupported =>
              cases h_next
            | assign dst rvalue =>
              dsimp only at h_val h_next
              unfold evalStatement
              dsimp only
              cases h_proj : dst.projection.isEmpty with
              | false => rw [h_proj] at h_next; cases h_next
              | true =>
                rw [h_proj] at h_next
                rw [ite_bool_false (rfl : (!true) = false)]
                dsimp only at h_next
                cases h_dst :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [h_dst] at h_next; cases h_next
                | some dstTy =>
                  rw [h_dst] at h_val h_next
                  dsimp only at h_val h_next ⊢
                  cases h_ty : MirTy.beq dstTy (.int .isize false) with
                  | false => rw [h_ty] at h_next; cases h_next
                  | true =>
                    rw [h_ty] at h_next
                    dsimp only at h_next
                    have h_ty_eq := MirTy.beq_iff.mp h_ty
                    subst h_ty_eq
                    cases h_rv : evalRvalue body.locals frame.locals s.mem
                        (.int .isize false) rvalue with
                    | error _ => rw [h_rv] at h_val; cases h_val
                    | ok triple =>
                      cases triple with
                      | mk v_rv rest_rv =>
                        cases rest_rv with
                        | mk localsAfterRval memAfterRval =>
                          rw [h_rv] at h_val h_next
                          dsimp only at h_val h_next ⊢
                          rw [h_val]
                          unfold writePlace
                          rw [ite_bool_false (by rw [hv]; rfl)]
                          cases h_slot : Trusted.MirSemantics.getElem?
                              localsAfterRval dst.localId with
                          | none => rw [h_slot] at h_next; cases h_next
                          | some slot =>
                            rw [h_slot] at h_next
                            cases slot with
                            | dead | indirect _ => cases h_next
                            | immediate _ =>
                              dsimp only at h_next ⊢
                              cases h_set : setElem? localsAfterRval
                                  dst.localId (.immediate (some v)) with
                              | none => rw [h_set] at h_next; cases h_next
                              | some localsAfterWrite =>
                                rw [h_set] at h_next
                                exact h_next

theorem isize_id_1arg_ok {defId : DefId} {body : Body}
    (h_body :
      Trusted.MirSemantics.getElem? Captured.program.bodies defId = some body)
    (h_adm : BodyStaticAdmitted Captured.program body = true)
    (h_tys :
      (body.locals.drop 1).take body.argumentCount = [.int .isize false])
    (h_exec : ∀ {v : Val}, checkVal v (.int .isize false) = true →
      Executes body
        (mkState 0 0 (initLocalsLoop body [v] 0 body.locals)) v) :
    BodyVerified Captured.program defId body
      (Spec.specs.safety body.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program defId
        [scafUsizeVal a0] (scafUsizeVal a0) := by
  refine ⟨bodyVerified_of_safe h_body h_adm (fun args valid _ => ?_),
    fun a0 => total_of_executes h_body h_adm
      (validEntry_isize1 h_tys a0) (h_exec (valid_isize_word a0))⟩
  have hMatch : checkArgsMatch args [.int .isize false] = true := by
    unfold ValidEntryArgs at valid
    rw [h_tys] at valid
    exact valid
  let ⟨v, rest, hEq, hv, hRest⟩ := checkArgsMatch_cons_iff.mp hMatch
  have hNil : rest = [] := checkArgsMatch_nil_iff.mp hRest
  subst hEq; subst hNil
  exact executes_safe (h_exec hv)"""

U64_HELPERS = """\
noncomputable abbrev scafU64Val (x : BitVec 64) : Val :=
  .scalar ⟨.i64, false, bvZeroExtend 128 x⟩

private theorem u64_valid_elim {v : Val}
    (hv : checkVal v (.int .i64 false) = true) :
    ∃ x : BitVec 64, v = scafU64Val x :=
  Exists.elim (checkVal_int_iff.mp hv) fun bits h =>
    have hlt : bits.toNat < 2 ^ 64 := by
      change bits.toNat < intWidthModulus .i64
      rw [← h.2, toNat_truncateBits]
      exact Nat.mod_lt _ (intWidth_modulus_pos .i64)
    have h128 : bits.toNat < 2 ^ 128 :=
      Nat.lt_trans hlt (Nat.pow_lt_pow_right (by decide) (by decide))
    ⟨BitVec.ofNatLT bits.toNat hlt,
      h.1.trans (congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
        (bitVec_eq_of_toNat_eq (Nat.mod_eq_of_lt h128).symm))⟩

private theorem xor_odd_step (p k : Nat) (hk : k ≠ 0)
    (h : (p ^^^ k / 2) + k / 2 = p) :
    ((2 * p + 1) ^^^ k) + k = 2 * p + 1 := by
  let q := k / 2
  let x := p ^^^ q
  have ha : 2 * p + 1 ≠ 0 := by
    rw [Nat.two_mul]
    exact Nat.succ_ne_zero _
  have hda : (2 * p + 1) / 2 = p := by
    rw [Nat.mul_add_div (by decide : 0 < 2)]
    rfl
  have hma : (2 * p + 1) % 2 = 1 := by
    rw [Nat.add_comm _ 1, Nat.add_mul_mod_self_left]
  have hunf : (2 * p + 1) ^^^ k =
      if (true != decide (k % 2 = 1)) = true then x + x + 1 else x + x := by
    change Nat.bitwise bne (2 * p + 1) k = _
    rw [Anneal.NatBitwise.unfold_eq, ite_prop_false ha, ite_prop_false hk]
    change (have r := Nat.bitwise bne ((2 * p + 1) / 2) q;
      if (decide ((2 * p + 1) % 2 = 1) != decide (k % 2 = 1)) = true
      then r + r + 1 else r + r) = _
    rw [hda, hma]
    rfl
  have hdm : k = q + q + k % 2 := by
    have hdiv := (Nat.div_add_mod k 2).symm
    rw [Nat.two_mul] at hdiv
    exact hdiv
  have h1 : x + x + (q + q) = 2 * p := by
    rw [← Nat.two_mul x, ← Nat.two_mul q, ← Nat.mul_add, h]
  have hlt2 := Nat.mod_lt k (by decide : 0 < 2)
  rw [hunf]
  cases hm : k % 2 with
  | zero =>
    change (x + x + 1) + k = _
    have hk2 : k = q + q := by rw [hm, Nat.add_zero] at hdm; exact hdm
    rw [congrArg ((x + x + 1) + ·) hk2, Nat.add_right_comm (x + x) 1 (q + q),
      h1]
  | succ m =>
    cases m with
    | zero =>
      change (x + x) + k = _
      have hk2 : k = q + q + 1 := by rw [hm] at hdm; exact hdm
      rw [congrArg ((x + x) + ·) hk2, ← Nat.add_assoc (x + x), h1]
    | succ _ =>
      rw [hm] at hlt2
      exact False.elim (Nat.not_lt_of_le (Nat.le_add_left 2 _) hlt2)

private theorem nat_xor_compl (n : Nat) :
    ∀ k, k < 2 ^ n → ((2 ^ n - 1) ^^^ k) + k = 2 ^ n - 1 := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst hk0
    rfl
  | succ n ih =>
    intro k hk
    have hp : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have hpow : 0 < 2 ^ n := Nat.pow_pos (by decide)
      rw [Nat.pow_succ, Nat.mul_comm]
      cases hq : 2 ^ n with
      | zero => exact False.elim (Nat.ne_of_gt hpow hq)
      | succ p =>
        rw [Nat.mul_succ, show (2 : Nat) = 1 + 1 from rfl,
          ← Nat.add_assoc, Nat.add_sub_cancel]
        rfl
    rw [hp]
    cases k with
    | zero => rw [Nat.xor_zero]
    | succ k' =>
      exact xor_odd_step (2 ^ n - 1) (k' + 1) (Nat.succ_ne_zero _)
        (ih ((k' + 1) / 2) (Nat.div_lt_of_lt_mul
          (by rw [Nat.mul_comm, ← Nat.pow_succ]; exact hk)))

private theorem u64Not_arith (P x : Nat) (hP : 0 < P) (hx : x < P) :
    (P * P - (x + 1)) % P = P - 1 - x := by
  have hle : x ≤ P - 1 := Nat.le_pred_of_lt hx
  have hp1 : P - 1 + 1 = P := Nat.sub_add_cancel hP
  have hsplit : P * P - (x + 1) = (P - 1 - x) + (P - 1) * P := by
    symm
    apply Nat.eq_sub_of_add_eq
    rw [Nat.add_assoc (P - 1 - x), Nat.add_comm ((P - 1) * P) (x + 1),
      ← Nat.add_assoc (P - 1 - x) (x + 1), ← Nat.add_assoc (P - 1 - x) x 1,
      Nat.sub_add_cancel hle, hp1, Nat.add_comm P, ← Nat.succ_mul,
      Nat.succ_eq_add_one, hp1]
  rw [hsplit, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hP (by decide)))

private theorem subNatNat_of_le {a b : Nat} (h : b ≤ a) :
    (Int.subNatNat a b).toNat = a - b := by
  unfold Int.subNatNat
  rw [Nat.sub_eq_zero_of_le h]
  rfl

private theorem intEmod_negSucc_of_lt {m n : Nat} (h : m < n) :
    (intEmod (Int.negSucc m) (Int.ofNat n)).toNat = n - (m + 1) := by
  change (Int.subNatNat n (m % n).succ).toNat = _
  rw [Nat.mod_eq_of_lt h]
  exact subNatNat_of_le h

private theorem u64Not_bits_eq (x : BitVec 64) :
    truncateBits .i64
      (bvOfInt 128
        (Int.negSucc (truncateBits .i64 (bvZeroExtend 128 x)).toNat)) =
      bvZeroExtend 128 (~~~x) := by
  rw [truncateBits_i64_bvZeroExtend, bvZeroExtend_128_toNat]
  apply bitVec_eq_of_toNat_eq
  rw [toNat_truncateBits, bvZeroExtend_128_toNat]
  have hxlt : x.toNat < 2 ^ 64 := x.isLt
  have h64_128 : 2 ^ 64 < 2 ^ 128 :=
    Nat.pow_lt_pow_right (by decide) (by decide)
  have h128 : x.toNat < 2 ^ 128 := Nat.lt_trans hxlt h64_128
  have hbv :
      (bvOfInt 128 (Int.negSucc x.toNat)).toNat = 2 ^ 128 - (x.toNat + 1) := by
    unfold bvOfInt
    rw [intEmod_negSucc_of_lt h128]
    exact Nat.mod_eq_of_lt
      (Nat.sub_lt (Nat.pow_pos (by decide)) (Nat.succ_pos _))
  have hrhs : (~~~x).toNat = 2 ^ 64 - 1 - x.toNat :=
    Nat.eq_sub_of_add_eq (nat_xor_compl 64 x.toNat hxlt)
  rw [hbv, hrhs]
  change (2 ^ 128 - (x.toNat + 1)) % 2 ^ 64 = _
  rw [show (2 ^ 128 : Nat) = 2 ^ 64 * 2 ^ 64 from (Nat.pow_add 2 64 64).symm]
  exact u64Not_arith (2 ^ 64) x.toNat (Nat.pow_pos (by decide)) hxlt

theorem step_u64Not {body : Body} {s next : State} (x nx : BitVec 64)
    (hnx : nx = ~~~x)
    (hval : EvalAssignVal body s
      (Val.scalar ⟨.i64, false,
        truncateBits .i64
          (bvOfInt 128
            (Int.negSucc (truncateBits .i64 (bvZeroExtend 128 x)).toNat))⟩))
    (hwith : EvalAssignWith body s (scafU64Val nx) next) :
    evalStep (bodyProg body) 0 s = .step next :=
  step_eq_evalAssignWith hval
    (congrArg (fun b => Val.scalar ⟨.i64, false, b⟩)
      ((u64Not_bits_eq x).trans (congrArg (bvZeroExtend 128) hnx.symm)))
    hwith

private theorem bv64_int_eq_const_iff (x : BitVec 64) (c : Nat)
    (y : BitVec 64)
    (hy :
      (truncateBits .i64 (truncateBits .i64 (BitVec.ofNat 128 c))).toNat =
        y.toNat) :
    (Int.ofNat (truncateBits .i64 (bvZeroExtend 128 x)).toNat ==
      Int.ofNat
        (truncateBits .i64 (truncateBits .i64 (BitVec.ofNat 128 c))).toNat) =
      (x == y) := by
  rw [truncateBits_i64_bvZeroExtend, bvZeroExtend_128_toNat, hy]
  cases h : (x == y) with
  | true =>
    have heq : x = y := beq_iff_eq.mp h
    rw [heq]
    exact beq_iff_eq.mpr rfl
  | false =>
    change (Int.ofNat x.toNat == Int.ofNat y.toNat) = false
    exact decide_eq_false fun hint =>
      Bool.false_ne_true (h.symm.trans (beq_iff_eq.mpr
        (bitVec_eq_of_toNat_eq (Int.ofNat.inj hint))))

noncomputable def EvalAssignBoolWith (body : Body) (s : State)
    (overrideVal : Val) (next : State) : Prop :=
  match s.frames with
  | [frame] =>
    match Nat.beq frame.defId 0 with
    | false => False
    | true =>
      match Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
      | none => False
      | some bb =>
        match Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
        | some (.assign dst rvalue) =>
          match dst.projection.isEmpty with
          | false => False
          | true =>
            match Trusted.MirSemantics.getElem? body.locals dst.localId with
            | none => False
            | some dstTy =>
              match MirTy.beq dstTy .bool with
              | false => False
              | true =>
                match evalRvalue body.locals frame.locals s.mem
                    dstTy rvalue with
                | .error _ => False
                | .ok (_, localsAfterRval, memAfterRval) =>
                  match Trusted.MirSemantics.getElem?
                      localsAfterRval dst.localId with
                  | some (.immediate _) =>
                    match setElem? localsAfterRval dst.localId
                        (.immediate (some overrideVal)) with
                    | some localsAfterWrite =>
                      (.step {
                        frames := [{
                          frame with
                          stmtIdx := frame.stmtIdx + 1
                          locals := localsAfterWrite
                        }]
                        callerMem := s.callerMem
                        mem := memAfterRval
                      } : StepResult State TerminalOut) = .step next
                    | none => False
                  | _ => False
        | _ => False
  | _ => False

theorem step_u64EqConst {body : Body} {s next : State}
    (x : BitVec 64) (c : Nat) (y : BitVec 64)
    (hy :
      (truncateBits .i64 (truncateBits .i64 (BitVec.ofNat 128 c))).toNat =
        y.toNat)
    (h_val : EvalAssignVal body s
      (Val.bool
        (Int.ofNat (truncateBits .i64 (bvZeroExtend 128 x)).toNat ==
          Int.ofNat
            (truncateBits .i64
              (truncateBits .i64 (BitVec.ofNat 128 c))).toNat)))
    (h_next : EvalAssignBoolWith body s (Val.bool (x == y)) next) :
    evalStep (bodyProg body) 0 s = .step next := by
  unfold EvalAssignVal at h_val
  unfold EvalAssignBoolWith at h_next
  unfold bodyProg evalStep
  cases h_fr : s.frames with
  | nil => rw [h_fr] at h_next; cases h_next
  | cons frame rest =>
    cases rest with
    | cons _ _ => rw [h_fr] at h_next; cases h_next
    | nil =>
      rw [h_fr] at h_val h_next
      dsimp only at h_val h_next ⊢
      cases h_def : Nat.beq frame.defId 0 with
      | false => rw [h_def] at h_next; cases h_next
      | true =>
        rw [h_def] at h_next
        dsimp only at h_next
        rw [Nat.eq_of_beq_eq_true h_def]
        rw [show Trusted.MirSemantics.getElem? [body] 0 = some body from rfl]
        dsimp only
        cases h_bb :
            Trusted.MirSemantics.getElem? body.basicBlocks frame.blockIdx with
        | none => rw [h_bb] at h_next; cases h_next
        | some bb =>
          rw [h_bb] at h_val h_next
          dsimp only at h_val h_next ⊢
          cases h_st :
              Trusted.MirSemantics.getElem? bb.statements frame.stmtIdx with
          | none => rw [h_st] at h_next; cases h_next
          | some stmt =>
            rw [h_st] at h_val h_next
            dsimp only
            cases stmt with
            | nop | storageLive _ | storageDead _ | unsupported =>
              cases h_next
            | assign dst rvalue =>
              dsimp only at h_val h_next
              unfold evalStatement
              dsimp only
              cases h_proj : dst.projection.isEmpty with
              | false => rw [h_proj] at h_next; cases h_next
              | true =>
                rw [h_proj] at h_next
                rw [ite_bool_false (rfl : (!true) = false)]
                dsimp only at h_next
                cases h_dst :
                    Trusted.MirSemantics.getElem? body.locals dst.localId with
                | none => rw [h_dst] at h_next; cases h_next
                | some dstTy =>
                  rw [h_dst] at h_val h_next
                  dsimp only at h_val h_next ⊢
                  cases h_ty : MirTy.beq dstTy .bool with
                  | false => rw [h_ty] at h_next; cases h_next
                  | true =>
                    rw [h_ty] at h_next
                    dsimp only at h_next
                    have h_ty_eq := MirTy.beq_iff.mp h_ty
                    subst h_ty_eq
                    cases h_rv : evalRvalue body.locals frame.locals s.mem
                        .bool rvalue with
                    | error _ => rw [h_rv] at h_val; cases h_val
                    | ok triple =>
                      cases triple with
                      | mk v_rv rest_rv =>
                        cases rest_rv with
                        | mk localsAfterRval memAfterRval =>
                          rw [h_rv] at h_val h_next
                          dsimp only at h_val h_next ⊢
                          have h_veq : v_rv = Val.bool (x == y) :=
                            h_val.trans (congrArg Val.bool
                              (bv64_int_eq_const_iff x c y hy))
                          rw [h_veq]
                          unfold writePlace
                          rw [ite_bool_false
                            (rfl : (!checkVal (Val.bool (x == y)) .bool) = false)]
                          cases h_slot : Trusted.MirSemantics.getElem?
                              localsAfterRval dst.localId with
                          | none => rw [h_slot] at h_next; cases h_next
                          | some slot =>
                            rw [h_slot] at h_next
                            cases slot with
                            | dead | indirect _ => cases h_next
                            | immediate _ =>
                              dsimp only at h_next ⊢
                              cases h_set : setElem? localsAfterRval
                                  dst.localId
                                  (.immediate (some (Val.bool (x == y)))) with
                              | none => rw [h_set] at h_next; cases h_next
                              | some localsAfterWrite =>
                                rw [h_set] at h_next
                                exact h_next

theorem u64_arg1_ok {d : DefId} {b : Body} (ret : BitVec 64 → Val)
    (hb : Trusted.MirSemantics.getElem? Captured.program.bodies d = some b)
    (hadm : BodyStaticAdmitted Captured.program b = true)
    (hparam :
      (b.locals.drop 1).take b.argumentCount = [.int .i64 false])
    (hexec : ∀ a0 : BitVec 64,
      Executes b
        (mkState 0 0 (initLocalsLoop b [scafU64Val a0] 0 b.locals))
        (ret a0)) :
    BodyVerified Captured.program d b (Spec.specs.safety b.identity) ∧
    ∀ a0 : BitVec 64,
      ScafReturnsTotal Captured.program d [scafU64Val a0] (ret a0) :=
  have hok : ∀ a0 : BitVec 64,
      WellFormed (entryProgForBody Captured.program d)
        { args := [scafU64Val a0] } ∧
      ScafReturnsTotal Captured.program d [scafU64Val a0] (ret a0) :=
    fun a0 =>
      ok_of_executes hb hadm
        (by
          unfold ValidEntryArgs
          rw [hparam]
          change (checkVal (scafU64Val a0) _ && true) = true
          rw [checkVal_u64_bvZeroExtend a0]
          rfl)
        (hexec a0)
  ⟨⟨hb, hadm, fun args hargs _ =>
    Exists.elim
      (checkArgsMatch_cons_iff.mp
        (hparam ▸ (hargs : checkArgsMatch args _ = true)))
      fun v0 h1 =>
        Exists.elim h1 fun _ h2 =>
          Exists.elim (u64_valid_elim h2.2.1) fun a0 ha0 =>
            ((checkArgsMatch_nil_iff.mp h2.2.2 ▸ ha0 ▸ h2.1) :
              args = [scafU64Val a0]).symm ▸ (hok a0).1⟩,
    fun a0 => (hok a0).2⟩

theorem u64_arg2_ok {d : DefId} {b : Body}
    (ret : BitVec 64 → BitVec 64 → Val)
    (hb : Trusted.MirSemantics.getElem? Captured.program.bodies d = some b)
    (hadm : BodyStaticAdmitted Captured.program b = true)
    (hparam :
      (b.locals.drop 1).take b.argumentCount =
        [.int .i64 false, .int .i64 false])
    (hexec : ∀ a0 a1 : BitVec 64,
      Executes b
        (mkState 0 0
          (initLocalsLoop b [scafU64Val a0, scafU64Val a1] 0 b.locals))
        (ret a0 a1)) :
    BodyVerified Captured.program d b (Spec.specs.safety b.identity) ∧
    ∀ a0 a1 : BitVec 64,
      ScafReturnsTotal Captured.program d
        [scafU64Val a0, scafU64Val a1] (ret a0 a1) :=
  have hok : ∀ a0 a1 : BitVec 64,
      WellFormed (entryProgForBody Captured.program d)
        { args := [scafU64Val a0, scafU64Val a1] } ∧
      ScafReturnsTotal Captured.program d
        [scafU64Val a0, scafU64Val a1] (ret a0 a1) :=
    fun a0 a1 =>
      ok_of_executes hb hadm
        (by
          unfold ValidEntryArgs
          rw [hparam]
          change (checkVal (scafU64Val a0) _ &&
            (checkVal (scafU64Val a1) _ && true)) = true
          rw [checkVal_u64_bvZeroExtend a0, checkVal_u64_bvZeroExtend a1]
          rfl)
        (hexec a0 a1)
  ⟨⟨hb, hadm, fun args hargs _ =>
    Exists.elim
      (checkArgsMatch_cons_iff.mp
        (hparam ▸ (hargs : checkArgsMatch args _ = true)))
      fun v0 h1 =>
        Exists.elim h1 fun _ h2 =>
          Exists.elim (checkArgsMatch_cons_iff.mp h2.2.2) fun v1 h3 =>
            Exists.elim h3 fun _ h4 =>
              Exists.elim (u64_valid_elim h2.2.1) fun a0 ha0 =>
                Exists.elim (u64_valid_elim h4.2.1) fun a1 ha1 =>
                  ((checkArgsMatch_nil_iff.mp h4.2.2 ▸
                    ha1 ▸ ha0 ▸ h4.1 ▸ h2.1) :
                      args = [scafU64Val a0, scafU64Val a1]).symm ▸
                    (hok a0 a1).1⟩,
    fun a0 a1 => (hok a0 a1).2⟩"""

HELPER_BLOCKS = (
    COMMON_HELPERS,
    UNIT0_HELPER,
    ISIZE_BASE_HELPERS,
    CONST_1ARG_HELPERS,
    ISIZE_COPY_HELPERS,
    U64_HELPERS,
)

# Prefixes of the per-body declarations `render_scaffold` emits as
# `<prefix>_<slug>`.
PER_BODY_DECL_PREFIXES = ("id", "body", "get", "adm", "runs", "exec", "ok")

LEAN_DECL_NAME_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|opaque|axiom)\s+"
    r"([^\s({\[:]+)",
    re.MULTILINE,
)


def helper_declared_names() -> frozenset[str]:
    """Names declared at top level by any helper block `render_scaffold` emits."""
    return frozenset(
        name for block in HELPER_BLOCKS for name in LEAN_DECL_NAME_RE.findall(block)
    )


def reserved_body_slugs() -> frozenset[str]:
    """Slugs whose per-body declarations would redeclare a helper name."""
    return frozenset(
        name[len(prefix) + 1:]
        for name in helper_declared_names()
        for prefix in PER_BODY_DECL_PREFIXES
        if name.startswith(prefix + "_") and len(name) > len(prefix) + 1
    )


def _u64_eq_const_step(lx: str, bits: int) -> str:
    """Emit the `step_u64EqConst` proof term, whose first line sits at column 4.

    The decimal constant can be up to 20 digits, so it moves to its own line
    whenever appending it to the (possibly wrapped) left operand would leave a
    line over 100 columns even after `_reflow_long_line`.
    """
    head = "(step_u64EqConst ("
    lx_w = _wrap_lean_expr(lx, "        ", max_col=94, first_prefix_len=21)
    tail = f"      (BitVec.ofNat 64 {bits}) rfl rfl rfl)"
    joined = f"{head}{lx_w}) {bits}"
    joined_lines = ("    " + joined).split("\n")
    if all(len(p) <= 100 for ln in joined_lines for p in _reflow_long_line(ln)):
        return f"{joined}\n{tail}"
    return f"{head}{lx_w})\n      {bits}\n{tail}"


def render_scaffold(capture_data: Any) -> str:
    """Render deterministic `AutoScaffold.lean` source from parsed `capture.json`."""
    if not isinstance(capture_data, dict):
        raise ScaffoldError("capture.json root must be an object")
    program = capture_data.get("program")
    if not isinstance(program, dict):
        raise ScaffoldError("capture.json missing program object")
    bodies = program.get("bodies")
    if not isinstance(bodies, list):
        raise ScaffoldError("capture.json program.bodies must be a list")

    slugs = assign_unique_slugs(bodies)

    analyses: list[tuple[str, Any]] = []
    need_unit0 = False
    need_isize_base = False
    need_const_1arg = False
    need_isize_copy = False
    need_u64 = False

    for body in bodies:
        if (fuel := analyze_unit0_ret(body)) is not None:
            analyses.append(("unit0", fuel))
            need_unit0 = True
        elif (c1 := analyze_const_ret_1arg(body)) is not None:
            analyses.append(("const1", c1))
            need_const_1arg = True
            need_isize_base = True
        elif (ic := analyze_isize_copy_chain(body)) is not None:
            analyses.append(("isize_copy", ic))
            need_isize_base = True
            need_isize_copy = True
        elif (u64_tr := analyze_u64_straight_line(body)) is not None:
            analyses.append(("u64", u64_tr))
            need_u64 = True
        else:
            analyses.append(("s1_only", None))

    max_id_len = max((len(str(b.get("identity", ""))) for b in bodies), default=0)
    need_rec_depth = max_id_len > 80 or len(bodies) > 16

    out: list[str] = [
        FUCHSIA_LEAN_HEADER,
        "",
        "prelude",
    ]
    if need_u64:
        out.append("import Init.Data.BitVec.Basic")
    out.extend([
        "import Expected",
        "import Anneal.MirWp",
        "",
    ])
    if need_rec_depth:
        out.extend(["set_option maxRecDepth 4096", ""])
    out.extend([
        "namespace AutoScaffold",
        "",
        "open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp",
        "",
        COMMON_HELPERS,
    ])
    if need_unit0:
        out.extend(["", UNIT0_HELPER])
    if need_isize_base:
        out.extend(["", ISIZE_BASE_HELPERS])
    if need_const_1arg:
        out.extend(["", CONST_1ARG_HELPERS])
    if need_isize_copy:
        out.extend(["", ISIZE_COPY_HELPERS])
    if need_u64:
        out.extend(["", U64_HELPERS])

    verified_refs: list[str] = []

    for idx, (body, slug, (kind, payload)) in enumerate(zip(bodies, slugs, analyses)):
        out.extend([
            "",
            f"def id_{slug} : DefId :=\n  {idx}"
            if len(f"def id_{slug} : DefId := {idx}") > 96
            else f"def id_{slug} : DefId := {idx}",
            f"abbrev body_{slug} : Body :=\n  Captured.body_{idx}"
            if len(f"abbrev body_{slug} : Body := Captured.body_{idx}") > 96
            else f"abbrev body_{slug} : Body := Captured.body_{idx}",
            f"theorem get_{slug} :",
            "    Trusted.MirSemantics.getElem? Captured.program.bodies",
            *_two_line(f"      id_{slug} =", f"some body_{slug} := rfl", "        "),
            f"theorem adm_{slug} :",
            *_two_line(
                "    BodyStaticAdmitted Captured.program",
                f"body_{slug} = true :=",
                "      ",
            ),
            "  rfl",
        ])

        if kind == "unit0":
            fuel = payload
            out.extend([
                f"theorem runs_{slug} :",
                *_two_line(
                    f"    Runs body_{slug} {fuel} []",
                    ".unit := rfl",
                    "      ",
                    max_col=100,
                ),
                f"theorem ok_{slug} :",
                *_two_line(
                    "    BodyVerified Captured.program",
                    f"id_{slug} body_{slug}",
                    "      ",
                ),
                *_two_line(
                    "      (Spec.specs.safety",
                    f"body_{slug}.identity) ∧",
                    "        ",
                    max_col=100,
                ),
                *_two_line(
                    f"    ScafReturnsTotal Captured.program id_{slug}",
                    "[] .unit :=",
                    "      ",
                ),
                *_two_line(
                    "  unit0_ok",
                    f"get_{slug} adm_{slug}",
                    "    ",
                ),
                f"    rfl runs_{slug}",
            ])
            verified_refs.append(f"ok_{slug}.1")

        elif kind == "const1":
            arg_kind, ret_expr, fuel = payload
            if arg_kind == "unit":
                out.extend([
                    f"theorem runs_{slug} :",
                    f"    Runs body_{slug} {fuel} [.unit]",
                    f"      {ret_expr} := rfl",
                    f"theorem ok_{slug} :",
                    *_two_line(
                        "    BodyVerified Captured.program",
                        f"id_{slug} body_{slug}",
                        "      ",
                    ),
                    *_two_line(
                        "      (Spec.specs.safety",
                        f"body_{slug}.identity) ∧",
                        "        ",
                        max_col=100,
                    ),
                    *_two_line(
                        f"    ScafReturnsTotal Captured.program id_{slug}",
                        "[.unit]",
                        "      ",
                    ),
                    f"      {ret_expr} :=",
                    *_two_line(
                        "  unit_const_1arg_ok",
                        f"get_{slug} adm_{slug}",
                        "    ",
                    ),
                    f"    rfl runs_{slug}",
                ])
            else:
                out.extend([
                    f"theorem runs_{slug} (v : Val) :",
                    f"    Runs body_{slug} {fuel} [v]",
                    f"      {ret_expr} := rfl",
                    f"theorem ok_{slug} :",
                    *_two_line(
                        "    BodyVerified Captured.program",
                        f"id_{slug} body_{slug}",
                        "      ",
                    ),
                    *_two_line(
                        "      (Spec.specs.safety",
                        f"body_{slug}.identity) ∧",
                        "        ",
                        max_col=100,
                    ),
                    "    ∀ a0 : BitVec 64,",
                    *_two_line(
                        "      ScafReturnsTotal Captured.program",
                        f"id_{slug}",
                        "        ",
                    ),
                    f"        [scafUsizeVal a0] {ret_expr} :=",
                    *_two_line(
                        "  isize_const_1arg_ok",
                        f"get_{slug} adm_{slug}",
                        "    ",
                    ),
                    f"    rfl runs_{slug}",
                ])
            verified_refs.append(f"ok_{slug}.1")

        elif kind == "isize_copy":
            trace = payload
            out.extend([
                *_two_line(
                    f"private theorem exec_{slug}", "{v : Val}", "    ", max_col=100
                ),
                "    (hv : checkVal v (.int .isize false) = true) :",
                f"    Executes body_{slug}",
                "      (mkState 0 0",
                *_two_line(
                    f"        (initLocalsLoop body_{slug} [v] 0",
                    f"body_{slug}.locals))",
                    "          ",
                ),
                "      v :=",
                "  let v_a0 := some v",
            ])
            for _, pc, slots in trace:
                pfx = f"  let s{pc} := mkState 0 {pc} "
                list_txt = _format_lean_list(
                    _isize_slots_items(slots), indent=4, prefix_len=len(pfx)
                )
                out.append(pfx + list_txt)
            chain = "(.ret rfl)"
            for step_tag, pc, _ in reversed(trace):
                pf = "rfl" if step_tag == "rfl" else "(step_isizeVal hv rfl rfl)"
                chain = f"(.next (next := s{pc}) {pf}\n    {chain})"
            out.append("  " + chain)
            out.extend([
                f"theorem ok_{slug} :",
                *_two_line(
                    "    BodyVerified Captured.program",
                    f"id_{slug} body_{slug}",
                    "      ",
                ),
                *_two_line(
                    "      (Spec.specs.safety",
                    f"body_{slug}.identity) ∧",
                    "        ",
                    max_col=100,
                ),
                "    ∀ a0 : BitVec 64,",
                *_two_line(
                    "      ScafReturnsTotal Captured.program",
                    f"id_{slug}",
                    "        ",
                ),
                "        [scafUsizeVal a0] (scafUsizeVal a0) :=",
                *_two_line(
                    "  isize_id_1arg_ok",
                    f"get_{slug} adm_{slug}",
                    "    ",
                ),
                f"    rfl exec_{slug}",
            ])
            verified_refs.append(f"ok_{slug}.1")

        elif kind == "u64":
            arg_names, ret_kind, ret_expr, trace = payload
            params_sig = " ".join(f"({a} : BitVec 64)" for a in arg_names)
            arg_vals = ", ".join(f"scafU64Val {a}" for a in arg_names)
            ret_prefix = "scafU64Val (" if ret_kind == "u64" else "Val.bool ("
            exec_ret_expr = _wrap_lean_expr(
                ret_expr, "        ", max_col=94, first_prefix_len=7 + len(ret_prefix)
            )
            exec_ret_val = f"{ret_prefix}{exec_ret_expr})"
            ok_ret_expr = _wrap_lean_expr(
                ret_expr,
                "          ",
                max_col=94,
                first_prefix_len=12 + len(arg_vals) + len(ret_prefix),
            )
            ok_ret_val = f"{ret_prefix}{ok_ret_expr})"
            fun_args = " ".join(arg_names)
            fun_prefix = f"    (fun {fun_args} => {ret_prefix}"
            fun_ret_expr = _wrap_lean_expr(
                ret_expr, "        ", max_col=94, first_prefix_len=len(fun_prefix)
            )
            fun_ret_val = f"{ret_prefix}{fun_ret_expr})"
            init_call = f"        (initLocalsLoop body_{slug}"
            init_args = f"          [{arg_vals}]"
            init_tail = f"0 body_{slug}.locals))"
            out.extend([
                *_two_line(f"private theorem exec_{slug}", f"{params_sig} :", "    "),
                f"    Executes body_{slug}",
                "      (mkState 0 0",
                init_call,
                *_two_line(init_args, init_tail, "          "),
                f"      ({exec_ret_val}) :=",
            ])
            for a in arg_names:
                out.append(f"  let v_{a} := some (scafU64Val {a})")
            for step in trace:
                pc = step[1]
                pfx = f"  let s{pc} := mkState 0 {pc} "
                list_txt = _format_lean_list(
                    _u64_slots_items(step[-1], arg_names),
                    indent=4,
                    prefix_len=len(pfx),
                )
                out.append(pfx + list_txt)
            chain = "(.ret rfl)"
            for step in reversed(trace):
                sk = step[0]
                pc = step[1]
                if sk == "rfl":
                    pf = "rfl"
                elif sk == "u64_use":
                    s2 = _wrap_lean_expr(
                        str(step[2]), "        ", max_col=94, first_prefix_len=7
                    )
                    pf = f"(step_u64Use\n      ({s2}) rfl rfl)"
                elif sk == "u64_not":
                    s2 = _wrap_lean_expr(
                        str(step[2]), "        ", max_col=94, first_prefix_len=18
                    )
                    s3 = _wrap_lean_expr(
                        str(step[3]), "        ", max_col=94, first_prefix_len=7
                    )
                    pf = f"(step_u64Not ({s2})\n      ({s3}) rfl rfl rfl)"
                elif sk == "u64_and":
                    s2 = _wrap_lean_expr(
                        str(step[2]), "        ", max_col=94, first_prefix_len=18
                    )
                    s3 = _wrap_lean_expr(
                        str(step[3]), "        ", max_col=94, first_prefix_len=7
                    )
                    pf = f"(step_u64And ({s2})\n      ({s3}) rfl rfl)"
                elif sk == "u64_or":
                    s2 = _wrap_lean_expr(
                        str(step[2]), "        ", max_col=94, first_prefix_len=17
                    )
                    s3 = _wrap_lean_expr(
                        str(step[3]), "        ", max_col=94, first_prefix_len=7
                    )
                    pf = f"(step_u64Or ({s2})\n      ({s3}) rfl rfl)"
                elif sk == "u64_eq_const":
                    pf = _u64_eq_const_step(str(step[3]), step[4])
                else:
                    raise ScaffoldError(f"unsupported step tag: {sk!r}")
                chain = f"(.next (next := s{pc})\n    {pf}\n    {chain})"
            out.append("  " + chain)
            ok_helper = "u64_arg1_ok" if len(arg_names) == 1 else "u64_arg2_ok"
            out.extend([
                f"theorem ok_{slug} :",
                *_two_line(
                    "    BodyVerified Captured.program",
                    f"id_{slug} body_{slug}",
                    "      ",
                ),
                *_two_line(
                    "      (Spec.specs.safety",
                    f"body_{slug}.identity) ∧",
                    "        ",
                    max_col=100,
                ),
                f"    ∀ {' '.join(arg_names)} : BitVec 64,",
                *_two_line(
                    "      ScafReturnsTotal Captured.program",
                    f"id_{slug}",
                    "        ",
                ),
                *_two_line(
                    f"        [{arg_vals}]",
                    f"({ok_ret_val}) :=",
                    "          ",
                ),
                *_two_line(
                    f"  {ok_helper} (d := id_{slug})",
                    f"(b := body_{slug})",
                    "    ",
                ),
                f"    (fun {fun_args} => {fun_ret_val})",
                *_two_line(
                    f"    get_{slug} adm_{slug}",
                    f"rfl exec_{slug}",
                    "      ",
                ),
            ])
            verified_refs.append(f"ok_{slug}.1")

    if len(verified_refs) == len(bodies):
        tuple_items = verified_refs + ["True.intro"]
        tuple_lines: list[str] = []
        cur = "    ⟨"
        for idx, item in enumerate(tuple_items):
            piece = item + ("," if idx + 1 < len(tuple_items) else "⟩")
            sep = "" if cur == "    ⟨" else " "
            if cur != "    ⟨" and len(cur) + 1 + len(piece) > 96:
                tuple_lines.append(cur)
                cur = "     " + piece
            else:
                cur = cur + sep + piece
        tuple_lines.append(cur)
        out.extend([
            "",
            "theorem all_bodies_safe :",
            "    ∀ (defId : DefId) (body : Body),",
            "      Trusted.MirSemantics.getElem? Captured.program.bodies defId =",
            "        some body →",
            "      BodyVerified Captured.program defId body",
            "        (Spec.specs.safety body.identity) := by",
            "  have hAll :",
            "      BodiesVerified Captured.program Spec.specs 0",
            "        Captured.program.bodies :=",
            *tuple_lines,
            "  intro defId body found",
            "  have hSub := bodiesVerified_getElem hAll defId body found",
            "  rw [Nat.zero_add] at hSub",
            "  exact hSub",
        ])

    out.extend(["", "end AutoScaffold", ""])
    rendered = "\n".join(
        piece for line in "\n".join(out).split("\n") for piece in _reflow_long_line(line)
    )
    for lineno, line in enumerate(rendered.splitlines(), 1):
        if len(line) > 100:
            raise ScaffoldError(
                f"generated AutoScaffold.lean line {lineno} exceeds 100 cols "
                f"({len(line)}): {line!r}"
            )
    return rendered


def check_or_write_scaffold(
    capture_data: Any, output_path: Path, check_only: bool = False
) -> str:
    """Render `AutoScaffold.lean` and either check parity or write atomically."""
    ensure_regular_nonsymlink(output_path, "AutoScaffold.lean")
    rendered = render_scaffold(capture_data)
    if check_only:
        if not output_path.is_file():
            raise ScaffoldError(f"missing checked-in scaffold file: {output_path}")
        # Compare raw bytes: text-mode reads would fold CRLF and lone CR into LF.
        if output_path.read_bytes() != rendered.encode("utf-8"):
            raise ScaffoldError(
                f"AutoScaffold.lean drift detected at {output_path}; "
                "regenerate via `python3 -I -B anneal/ci/anneal_scaffold.py`"
            )
        return rendered

    output_path.parent.mkdir(parents=True, exist_ok=True)
    tmp_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            "wb",
            dir=output_path.parent,
            prefix=".autoscaffold-",
            delete=False,
        ) as tmp:
            tmp.write(rendered.encode("utf-8"))
            tmp_path = Path(tmp.name)
        tmp_path.chmod(0o644)
        tmp_path.replace(output_path)
    finally:
        if tmp_path is not None and tmp_path.exists():
            tmp_path.unlink(missing_ok=True)
    return rendered


def _resolve_confined_source(src_root: Path, rel_path: str, label: str) -> Path:
    """Resolve `rel_path` strictly inside `src_root` without symlinks."""
    rel = Path(rel_path)
    if rel.is_absolute() or ".." in rel.parts or not rel.parts:
        raise ScaffoldError(f"unsafe {label} path: {rel_path!r}")
    candidate = src_root / rel
    ensure_regular_nonsymlink(candidate, label, root=src_root)
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise ScaffoldError(f"missing {label}: {candidate}") from exc
    if not resolved.is_relative_to(src_root):
        raise ScaffoldError(f"{label} escapes source_root: {rel_path!r}")
    return resolved


def _resolve_tool(path: Path, label: str) -> Path:
    """Resolve a toolchain path once, following any symlinks."""
    try:
        return path.resolve(strict=True)
    except OSError as exc:
        raise ScaffoldError(f"missing {label}: {path}") from exc


def capture_from_request(
    request_path: Path,
    cli: Path | None = None,
    capture: Path | None = None,
    sysroot: Path | None = None,
    lean: Path | None = None,
    timeout: int = 600,
) -> dict[str, Any]:
    """Extract `capture.json` from `request.json` via `anneal-rustc-capture`."""
    del cli, lean
    if capture is None or sysroot is None:
        raise ScaffoldError("capture_from_request requires `capture` and `sysroot`")
    ensure_regular_nonsymlink(request_path, "request.json")
    # Toolchain inputs may legitimately be symlinks (elan, Nix profiles), so
    # they are resolved once instead of symlink-checked.
    capture = _resolve_tool(capture, "capture")
    sysroot = _resolve_tool(sysroot, "sysroot")
    if not capture.is_file():
        raise ScaffoldError(f"missing capture binary: {capture}")
    if not sysroot.is_dir():
        raise ScaffoldError(f"missing sysroot directory: {sysroot}")
    req_data = load_strict_json(request_path, "request.json")
    if not isinstance(req_data, dict):
        raise ScaffoldError(f"{request_path}: request must be a JSON object")
    unit_dir = request_path.resolve(strict=True).parent

    comp = req_data.get("compilation")
    if not isinstance(comp, dict):
        raise ScaffoldError(f"{request_path}: missing compilation table")
    source_root = comp.get("source_root")
    if (
        not isinstance(source_root, str)
        or not source_root
        or Path(source_root).is_absolute()
    ):
        raise ScaffoldError(
            f"{request_path}: compilation.source_root must be a non-empty "
            f"relative path: {source_root!r}"
        )
    raw_src_root = unit_dir / source_root
    ensure_regular_nonsymlink(raw_src_root, "source_root", root=unit_dir)
    try:
        real_src_root = raw_src_root.resolve(strict=True)
    except OSError as exc:
        raise ScaffoldError(
            f"{request_path}: missing source_root: {raw_src_root}"
        ) from exc
    if not real_src_root.is_dir():
        raise ScaffoldError(
            f"{request_path}: source_root is not a directory: {real_src_root}"
        )
    crate_root_rel = comp.get("crate_root")
    crate_name = comp.get("crate_name")
    source_files = comp.get("source_files")
    if (
        not isinstance(crate_root_rel, str)
        or not isinstance(crate_name, str)
        or not isinstance(source_files, list)
        or not source_files
    ):
        raise ScaffoldError(
            f"{request_path}: missing crate_root, crate_name, or source_files"
        )
    resolved_crate_root = _resolve_confined_source(
        real_src_root, crate_root_rel, "crate_root"
    )
    resolved_sources: list[Path] = []
    for rel_src in source_files:
        if not isinstance(rel_src, str):
            raise ScaffoldError(
                f"{request_path}: invalid source_files entry {rel_src!r}"
            )
        resolved_sources.append(
            _resolve_confined_source(real_src_root, rel_src, "source_file")
        )

    scope = req_data.get("scope")
    if not isinstance(scope, dict) or scope.get("kind") not in (
        "selected_unit",
        "crate",
    ):
        raise ScaffoldError(f"{request_path}: invalid scope")

    def str_field(table: dict[str, Any], key: str, default: str) -> str:
        val = table.get(key, default)
        if not isinstance(val, str):
            raise ScaffoldError(f"{request_path}: {key} must be a string: {val!r}")
        return val

    def list_field(table: dict[str, Any], key: str, item_ty: type) -> list[Any]:
        val = table.get(key, [])
        if not isinstance(val, list) or not all(isinstance(x, item_ty) for x in val):
            raise ScaffoldError(
                f"{request_path}: {key} must be a list of {item_ty.__name__}: {val!r}"
            )
        return val

    cfg_flags = list_field(comp, "cfg", str)
    env_map = comp.get("env", {})
    if not isinstance(env_map, dict) or not all(
        isinstance(k, str) and isinstance(v, str) for k, v in env_map.items()
    ):
        raise ScaffoldError(
            f"{request_path}: env must map strings to strings: {env_map!r}"
        )
    if scope["kind"] == "crate":
        scope_args = ["--scope=crate"]
    else:
        roots = list_field(scope, "roots", str)
        insts = list_field(scope, "instantiations", dict)
        scope_args = [f"--select={r}" for r in roots] + [
            f"--instantiate={json.dumps(i, separators=(',', ':'))}" for i in insts
        ]

    with tempfile.TemporaryDirectory(prefix="anneal-scaffold-cap-") as td:
        out_dir = Path(td) / "capture"
        # Join every value-bearing flag as `--flag=value` so values beginning
        # with `-` stay option data.
        cmd = [
            str(capture),
            "capture",
            f"--crate-root={resolved_crate_root}",
            f"--crate-name={crate_name}",
            f"--crate-type={str_field(comp, 'crate_type', 'lib')}",
            f"--panic={str_field(comp, 'panic', 'unwind')}",
            f"--edition={str_field(comp, 'edition', '2024')}",
            f"--target={str_field(comp, 'target', 'x86_64-unknown-linux-gnu')}",
            f"--out-dir={out_dir}",
            f"--sysroot={sysroot}",
        ]
        cmd.extend(f"--cfg={cfg_flag}" for cfg_flag in cfg_flags)
        cmd.extend(f"--env={key}={val}" for key, val in sorted(env_map.items()))
        cmd.extend(f"--source-file={src_path}" for src_path in resolved_sources)
        cmd.extend(scope_args)

        clean_env = {
            "PATH": "/usr/bin:/bin",
            "LD_LIBRARY_PATH": str(sysroot / "lib"),
        }
        proc = subprocess.run(
            cmd,
            cwd=unit_dir,
            env=clean_env,
            capture_output=True,
            text=True,
            timeout=timeout,
            check=False,
        )
        cap_json = out_dir / "capture.json"
        if proc.returncode != 0 or not cap_json.is_file():
            raise ScaffoldError(
                f"capture failed for {request_path} (exit {proc.returncode}):\n"
                f"stdout={proc.stdout[:600]}\nstderr={proc.stderr[:600]}"
            )
        return load_strict_json(cap_json, "capture.json")


def main(argv: list[str] | None = None) -> int:
    anneal_root = Path(__file__).resolve().parents[1]
    if str(anneal_root / "ci") not in sys.path:
        sys.path.insert(0, str(anneal_root / "ci"))
    import verify_zerocopy

    parser = argparse.ArgumentParser(
        prog="anneal-scaffold",
        description=__doc__,
    )
    src_group = parser.add_mutually_exclusive_group(required=True)
    src_group.add_argument(
        "--capture-json",
        type=Path,
        help="Existing `capture/capture.json` file to render from",
    )
    src_group.add_argument(
        "--request",
        type=Path,
        help="`request.json` file to capture and scaffold",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Destination `AutoScaffold.lean` path (defaults beside `--request`)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Fail closed if `--output` differs byte-for-byte from rendered output",
    )
    parser.add_argument("--timeout", type=int, default=600)
    for name in ("cli", "capture", "sysroot", "lean"):
        parser.add_argument(f"--{name}", type=Path)

    args = parser.parse_args(argv)
    if args.output is not None:
        ensure_regular_nonsymlink(args.output, "output")
    if args.capture_json is not None:
        if args.output is None:
            parser.error("--output is required when using --capture-json")
        cap_data = load_strict_json(args.capture_json, "capture.json")
        out_path = args.output
    else:
        ensure_regular_nonsymlink(args.request, "request.json")
        if not args.request.is_file():
            raise ScaffoldError(f"missing request.json: {args.request}")
        out_path = (
            args.output
            if args.output is not None
            else args.request.resolve(strict=True).parent / "AutoScaffold.lean"
        )
        env_fallbacks = {
            "capture": verify_zerocopy.env_tool(
                ["ANNEAL_CAPTURE"], "bin/anneal-rustc-capture"
            ),
            "sysroot": verify_zerocopy.env_tool(
                ["ANNEAL_SYSROOT", "ANNEAL_TEST_RUST_SYSROOT"], "rust"
            ),
        }
        for name, fb in env_fallbacks.items():
            if getattr(args, name) is None:
                setattr(args, name, fb)
        if any(getattr(args, name) is None for name in env_fallbacks):
            local = verify_zerocopy.discover_local_defaults(anneal_root)
            for name in env_fallbacks:
                if getattr(args, name) is None:
                    setattr(args, name, local[name])
        for req_tool in ("capture", "sysroot"):
            val = getattr(args, req_tool)
            if val is None:
                parser.error(f"the following arguments are required: --{req_tool}")
            setattr(args, req_tool, _resolve_tool(val, req_tool))
        cap_data = capture_from_request(
            args.request,
            capture=args.capture,
            sysroot=args.sysroot,
            timeout=args.timeout,
        )

    check_or_write_scaffold(cap_data, out_path, check_only=args.check)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ScaffoldError as err:
        print(f"anneal-scaffold: error: {err}", file=sys.stderr)
        raise SystemExit(1)
