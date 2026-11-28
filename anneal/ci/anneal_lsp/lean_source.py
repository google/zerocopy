# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Lean 4 source scanning helpers for the workspace pool: declaration and
`sorry` matching, safe file reads, diagnostics, and symbol outlines."""

from __future__ import annotations

import contextlib
import os
from pathlib import Path
import re
import stat
from typing import Any, Iterator

from .client import mask_lean_comments, utf16_to_py_col
from .discovery import validate_no_symlink_target


_WS_RE = re.compile(r"[ \t]+")
_ATTR_RE = re.compile(r"@\[[^\]\n]*\]")
_MOD_WORD_RE = re.compile(
    r"(?:private|protected|public|noncomputable|partial|unsafe|nonrec|local|scoped|meta)(?=[ \t])"
)
_OPEN_SET_RE = re.compile(r"(?:set_option|open)(?=[ \t])")
_DECL_HEAD_RE = re.compile(
    r"(inductive|structure|class|def|abbrev|theorem|lemma|instance|opaque|axiom|example)\b"
    r"(?:\s+((?:_root_\.)?(?:«[^»]+»|[^\s:({[]+?))(?:\.\{[^}]*\})?"
    r"(?=\s|:|\(|\{|\[|$))?"
)
_SCOPE_BOUND_RE = re.compile(r"^\s*(?:end|namespace|section|mutual|#)\b")
_SORRY_RE = re.compile(
    r"(?<![\w'.«`])((?:(?:_root_|«_root_»)\.)?"
    r"(?:sorry|admit|sorryAx|«sorryAx»))(?![\w'»?])"
)
_SORRY_WARN_RE = re.compile(
    r"\bdeclaration uses [`'«]?(?:sorry|sorryAx|admit)[`'»]?", re.IGNORECASE
)
_BULLET_RE = re.compile(r"^(\s*(?:[·•|]\s*)?)")
_SKIP_DIRS = frozenset({".git", ".lake", "target", "vendor", "__pycache__"})
_SEVS = {1: "error", 2: "warning", 3: "info", 4: "hint"}
_KINDS = {5: "class", 6: "method", 12: "def", 13: "var", 23: "struct", 26: "param"}


def _find_in_tok(line: str, pos: int) -> int | None:
    n, idx = len(line), pos
    while (idx := line.find("in", idx)) >= 0:
        if idx > pos and line[idx - 1] in " \t" and (idx + 2 == n or line[idx + 2] in " \t"):
            return idx + 2
        idx += 1
    return None


def _match_decl(line: str) -> re.Match[str] | None:
    pos, n = 0, len(line)
    while pos < n:
        if m := _WS_RE.match(line, pos):
            pos = m.end()
        elif m := _ATTR_RE.match(line, pos):
            pos = m.end()
        elif m := _MOD_WORD_RE.match(line, pos):
            pos = m.end()
        elif m := _OPEN_SET_RE.match(line, pos):
            if (nxt := _find_in_tok(line, m.end())) is None:
                break
            pos = nxt
        else:
            break
    return _DECL_HEAD_RE.match(line, pos)


def _logical_lines(text: str) -> list[str]:
    return text.replace("\r\n", "\n").replace("\r", "\n").split("\n")


def _read_regular_text(path: Path, *, max_bytes: int = 16 * 1024 * 1024) -> str | None:
    """Read UTF-8 text from a regular non-symlink file without blocking on FIFOs."""
    flags = os.O_RDONLY | getattr(os, "O_NONBLOCK", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(path, flags)
    except OSError:
        return None
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode) or st.st_size > max_bytes:
            return None
        with os.fdopen(fd, "r", encoding="utf-8", errors="replace") as fh:
            fd = -1
            return fh.read()
    except OSError:
        return None
    finally:
        if fd >= 0:
            with contextlib.suppress(OSError):
                os.close(fd)


def _safe_read_lines(
    raw_path: str, allowed_roots: tuple[Path, ...], excluded_roots: tuple[Path, ...] = (),
) -> list[str] | None:
    """Read regular non-symlink `.lean` source lines inside approved unhidden roots."""
    cand = Path(os.path.abspath(raw_path))
    try:
        if cand.is_symlink():
            return None
        res = cand.resolve()
        if res.suffix != ".lean" or not any(res.is_relative_to(r) for r in allowed_roots):
            return None
        if any(res == ex or res.is_relative_to(ex) for ex in excluded_roots):
            return None
    except OSError:
        return None
    raw = _read_regular_text(res)
    return _logical_lines(raw) if raw is not None else None


def _req_lean(file: str, *, home: Path | None = None) -> Path:
    p = validate_no_symlink_target(file, home=home, kind="Lean file")
    if not p.is_file():
        raise FileNotFoundError(f"Lean file not found: {p}")
    if p.suffix != ".lean":
        raise ValueError(f"Expected a `.lean` source file: {p}")
    return p


def _col(raw: str, sym: str | None = None, col: int | None = None) -> int:
    if isinstance(sym, str) and sym:
        if (i := raw.find(sym)) >= 0 or (i := raw.lower().find(sym.lower())) >= 0:
            return i
    return max(0, col - 1) if isinstance(col, int) else (len(raw) - len(raw.lstrip()))


def _cdiag(d: dict[str, Any], lines: list[str] | None = None) -> dict[str, Any]:
    s = d.get("range", {}).get("start", {})
    ln0, u16 = int(s.get("line", 0)), int(s.get("character", 0))
    col0 = utf16_to_py_col(lines[ln0], u16) if lines and 0 <= ln0 < len(lines) else u16
    return {"severity": _SEVS.get(int(d.get("severity", 1)), "error"),
            "line": ln0 + 1, "column": col0 + 1, "message": str(d.get("message", "")).strip()}


def _scan_decls(path: Path) -> list[dict[str, Any]]:
    if (raw := _read_regular_text(path)) is None:
        return []
    orig = _logical_lines(raw)
    clean = _logical_lines(mask_lean_comments(raw)) + [""] * len(orig)
    out: list[dict[str, Any]] = []
    for i, (ln, cln) in enumerate(zip(orig, clean), 1):
        if m := _match_decl(cln):
            name = ln[m.start(2) : m.end(2)] if m.group(2) is not None else "<anonymous>"
            out.append({"kind": m.group(1), "name": name, "line": i, "signature": ln.strip()})
    return out


def _walk_lean(root: Path) -> Iterator[Path]:
    for cur, dirs, files in os.walk(root):
        dirs[:] = [
            d for d in sorted(dirs)
            if d not in _SKIP_DIRS and not (Path(cur) / d).is_symlink()
        ]
        for fn in sorted(files):
            if fn.endswith(".lean"):
                fp = Path(cur) / fn
                with contextlib.suppress(OSError):
                    if stat.S_ISREG(fp.lstat().st_mode):
                        yield fp


def _fmt_cand(raw: str, sorry_m: re.Match[str] | None, cand: str) -> tuple[str, int]:
    cls = cand.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    if sorry_m:
        lead, tail = raw[: sorry_m.start(1)], raw[sorry_m.end(1) :]
    else:
        bm = _BULLET_RE.match(raw)
        ok_b = bm and not cand.lstrip().startswith(("·", "•", "|"))
        lead, tail = (bm.group(1) if ok_b else raw[: len(raw) - len(raw.lstrip())]), ""
    cont = lead if not lead.strip() else re.sub(r"[^\t ]", " ", lead)
    body = "\n".join((cont + s if s else "") if i else s for i, s in enumerate(cls))
    ec = len(lead) + len(cls[0]) if len(cls) == 1 else (len(cont) + len(cls[-1]) if cls[-1] else 0)
    return lead + body + tail, ec


def _flatten_syms(nodes: list[Any], out: list[dict[str, Any]], depth: int = 0) -> None:
    for n in nodes:
        if isinstance(n, dict):
            rng = n.get("selectionRange") or n.get("range") or {}
            out.append({
                "name": str(n.get("name", "")), "kind": _KINDS.get(int(n.get("kind") or 0), "decl"),
                "detail": str(n.get("detail") or ""),
                "line": int(rng.get("start", {}).get("line", 0)) + 1, "depth": depth,
            })
            if isinstance(n.get("children"), list):
                _flatten_syms(n["children"], out, depth + 1)
