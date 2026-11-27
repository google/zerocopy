# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Defender-side Lean 4 AST / kernel audit and lexer fallback helpers."""

from __future__ import annotations

from dataclasses import dataclass
import json
import math
from pathlib import Path
import re
import subprocess
import tempfile
import time
from typing import Any, Callable

import anneal_ci_lib


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


def strip_lean_comments_and_strings(
    source: str,
    *,
    preserve_guillemets: bool = False,
) -> str:
    """Replace Lean comments, char literals, raw strings, and plain strings with spaces.

    Preserves code inside interpolated strings (`s!"...{expr}..."`,
    `m!"...{expr}..."`, etc.) so tokens inside interpolations remain visible.
    Newlines are preserved verbatim so line numbers remain exact. When
    `preserve_guillemets` is True, French-quoted code identifiers (`«...»`)
    keep their exact characters and delimiters.
    """
    out: list[str] = []
    n = len(source)
    i = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
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

        if ch == "\u00ab":
            out.append("\u00ab" if preserve_guillemets else " ")
            i += 1
            while i < n and source[i] not in ("\u00bb", "\u00ab", "\n"):
                c = source[i]
                if preserve_guillemets:
                    out.append(c)
                else:
                    out.append(c if (c.isalnum() or c == "_") else "_")
                i += 1
            if i < n and source[i] == "\u00bb":
                out.append("\u00bb" if preserve_guillemets else " ")
                i += 1
            continue

        char_end = _match_lean_char_literal(source, i)
        if char_end != -1:
            emit_spaces(source[i:char_end])
            i = char_end
            continue

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


_ALLOWED_THEORY_IMPORT_ALL_MODULES = frozenset({"Init.Data.Nat.Bitwise.Basic"})
_LOCAL_SEMIREDUCIBLE_ALLOWLIST = frozenset({"Nat.bitwise"})
_LOCAL_SEMIREDUCIBLE_MODS = frozenset(
    {"private", "protected", "public", "noncomputable"}
)


def _ends_with_local_semireducible_name(name: str) -> bool:
    parts = [p for p in name.split(".") if p and p != "_root_"]
    for allowed in _LOCAL_SEMIREDUCIBLE_ALLOWLIST:
        aparts = allowed.split(".")
        if len(parts) >= len(aparts) and parts[-len(aparts) :] == aparts:
            return True
    return False


def _is_admitted_local_semireducible_token(
    toks: list[_Tok], idx: int, unrooted: str
) -> bool:
    if unrooted not in _LOCAL_SEMIREDUCIBLE_ALLOWLIST:
        return False
    if toks[idx].text != f"_root_.{unrooted}":
        return False
    if idx < 5:
        return False
    if [toks[idx - k].text for k in range(5, 0, -1)] != [
        "attribute",
        "[",
        "local",
        "semireducible",
        "]",
    ]:
        return False
    if idx >= 6:
        before = toks[idx - 6]
        if before.text == "in":
            return False
        if before.line == toks[idx - 5].line and before.text != ";":
            return False
    if idx + 2 >= len(toks) or toks[idx + 1].text != "in":
        return False
    j = idx + 2
    while j < len(toks) and toks[j].text in _LOCAL_SEMIREDUCIBLE_MODS:
        j += 1
    if j >= len(toks) or toks[j].text not in ("theorem", "def"):
        return False
    return True

_SPEC_ALLOWED_SET_OPTION_MODES = frozenset({"maxHeartbeats", "maxRecDepth"})
_SPEC_ALLOWED_SIMPLE_ATTRS = frozenset(
    {"reducible", "semireducible", "irreducible", "inline", "match_pattern"}
)
_SPEC_ALLOWED_ATTRS = _SPEC_ALLOWED_SIMPLE_ATTRS | frozenset(
    {"expose", "simp", "instance", "ext", "specialize"}
)
_THEORY_ALLOWED_ATTRS = frozenset(
    {"simp", "instance", "reducible", "semireducible", "irreducible", "expose"}
)

_FORBIDDEN_ATTR_NAMES = frozenset(
    {
        "implemented_by",
        "extern",
        "csimp",
        "init",
        "builtin_init",
        "macro",
        "elab_as_elim",
        "builtin_macro",
        "term_parser",
        "command_parser",
    }
)

_FORBIDDEN_PURE_IDENTS = frozenset(
    {
        "dbgTrace",
        "dbgTraceVal",
        "dbgTraceIfShared",
        "dbgStackTrace",
        "dbgStackTraceIf",
        "dbgSleep",
        "lean_dbg_trace",
        "lean_dbg_trace_if_shared",
        "lean_dbg_stack_trace",
        "lean_dbg_sleep",
        "loadDynlib",
        "loadPlugin",
        "lean_load_dynlib",
        "lean_load_plugin",
        "lean_dynlib_load",
        "lean_dynlib_get",
        "lean_dynlib_symbol_run_as_init",
        "includeStr",
    }
)

_SPEC_FORBIDDEN_IDENTS = _FORBIDDEN_PURE_IDENTS | frozenset(
    {"autoParam", "panic", "panicCore", "panicWithPos", "panicWithPosWithDecl"}
)
_THEORY_SUPPLEMENTAL_FORBIDDEN_IDENTS = frozenset({"autoParam"})
_THEORY_SUPPLEMENTAL_FORBIDDEN_PREFIXES = (
    "Lean.Syntax",
    "Lean.SourceInfo",
    "Lean.Name",
    "Lean.Parser",
    "Lean.Elab",
    "Lean.Meta",
    "Lean.Expr",
    "Lean.Environment",
    "Lean.mkAtom",
)
_SPEC_RESERVED_DECL_ROOTS = frozenset(
    {
        "Expected",
        "Captured",
        "SpecPreflight",
        "TrustedBoundary",
        "IncorrectnessCheck",
        "IncorrectnessExpected",
    }
)
_RESERVED_KERNEL_ROOTS = frozenset(
    {
        "Nat",
        "String",
        "Char",
        "Bool",
        "Int",
        "Int8",
        "Int16",
        "Int32",
        "Int64",
        "ISize",
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "BitVec",
        "Float",
        "Float32",
        "ByteArray",
        "Subarray",
        "Array",
        "List",
        "Option",
        "Sum",
        "Prod",
        "Fin",
        "Subtype",
        "Eq",
        "HEq",
        "Quot",
        "Classical",
        "Lean",
        "Init",
        "Std",
        "Lake",
        "LeanExport",
        "LeanIR",
        "System",
        "IO",
        "Task",
        "Thunk",
        "Unit",
        "PUnit",
        "Empty",
        "PEmpty",
        "True",
        "False",
        "And",
        "Or",
        "Not",
        "Iff",
        "Exists",
        "Sigma",
        "PSigma",
        "Decidable",
        "Nonempty",
        "Ordering",
        "Rat",
        "Except",
        "EStateM",
        "StateM",
    }
)
_THEORY_FORBIDDEN_DECL_ROOTS = (
    _RESERVED_KERNEL_ROOTS
    | _SPEC_RESERVED_DECL_ROOTS
    | frozenset({"Trusted", "Proof", "Spec"})
)
_KERNEL_ACCELERATED_NAMES = frozenset(
    {
        "Nat.zero",
        "Nat.succ",
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.pow",
        "Nat.gcd",
        "Nat.mod",
        "Nat.div",
        "Nat.beq",
        "Nat.ble",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
        "Nat.shiftRight",
        "String.ofList",
    }
)
_FORBIDDEN_NS_ROOTS = frozenset(
    {"Lake", "IO", "BaseIO", "EIO", "EST", "ST", "Task", "System", "Lean"}
)
_FORBIDDEN_SYS_UV_PREFIXES = (
    "Init.System",
    "Std.Internal.UV",
    "Internal.UV",
    "Lean.LoadDynlib",
    "Lean.loadDynlib",
    "Lean.loadPlugin",
    "Lean.Dynlib",
    "Dynlib",
)
_ALLOWED_SYS_PLATFORM_DECLS = frozenset(
    {
        "System.Platform.numBits",
        "System.Platform.getNumBits",
        "System.Platform.numBits_eq",
    }
)

_MOD_TOK_RE = re.compile(
    r"(?:«[^»\r\n]+»|[A-Za-z_][A-Za-z0-9_'!?]*)"
    r"(?:\.(?:«[^»\r\n]+»|[A-Za-z_][A-Za-z0-9_'!?]*))*"
)
_QUOTED_IDENT_RE = re.compile(r"«([^»\r\n]+)»")
_MODULE_HEADER_RE = re.compile(r"(?:^|[\s;])module(?:\s|;|$)")
_IMPORT_CLAUSE_RE = re.compile(
    r"(?:^|(?<=[\s;]))(?:(?:public|meta)\s+)*"
    r"import(?![\w.'!?»])(?:\s+(all)(?![\w.'!?»]))?"
)
_IMPORT_STOP_TOKENS = frozenset(
    {
        "prelude",
        "module",
        "public",
        "meta",
        "import",
        "all",
        "theorem",
        "def",
        "lemma",
        "abbrev",
        "opaque",
        "axiom",
        "inductive",
        "structure",
        "class",
        "instance",
        "example",
        "namespace",
        "section",
        "end",
        "open",
        "export",
        "variable",
        "universe",
        "set_option",
        "attribute",
        "private",
        "protected",
        "noncomputable",
        "partial",
        "unsafe",
    }
)

_CMD_STOP_TOKS = frozenset(
    {
        "axiom",
        "opaque",
        "example",
        "coinductive",
        "def",
        "theorem",
        "lemma",
        "abbrev",
        "inductive",
        "structure",
        "class",
        "instance",
        "namespace",
        "section",
        "end",
        "open",
        "export",
        "variable",
        "universe",
        "mutual",
        "set_option",
        "attribute",
        "deriving",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
        "macro",
        "macro_rules",
        "syntax",
        "declare_syntax_cat",
        "elab",
        "elab_rules",
        "run_cmd",
        "run_elab",
        "run_meta",
        "initialize",
        "builtin_initialize",
        "#eval",
        "#check",
        "#print",
        "#reduce",
        "#synth",
        "#where",
        "#exit",
    }
)
_DECL_HEADS = frozenset(
    {
        "def",
        "theorem",
        "lemma",
        "abbrev",
        "opaque",
        "axiom",
        "inductive",
        "structure",
        "class",
        "instance",
        "example",
        "coinductive",
    }
)
_FORBIDDEN_CMD_MAP = {
    "#eval": "command:#eval",
    "#check": "command:#check",
    "#print": "command:#print",
    "#reduce": "command:#reduce",
    "#synth": "command:#synth",
    "run_cmd": "run_cmd",
    "run_elab": "run_elab",
    "run_meta": "run_meta",
    "macro": "macro",
    "macro_rules": "macro",
    "syntax": "syntax",
    "declare_syntax_cat": "declare_syntax_cat",
    "elab": "elab",
    "elab_rules": "elab",
    "notation": "notation",
    "infix": "notation",
    "infixl": "notation",
    "infixr": "notation",
    "prefix": "notation",
    "postfix": "notation",
    "initialize": "initialize",
    "builtin_initialize": "initialize",
    "axiom": "axiom",
    "example": "example",
    "coinductive": "coinductive",
}
_TACTIC_START_TOKENS = frozenset({"by", ";", "<;>", "{", "·", "=>"})
_FORBIDDEN_TACTICS = {
    "sorry": "sorry",
    "admit": "sorry",
    "native_decide": "native_decide",
    "bv_decide": "bv_decide",
    "run_tac": "run_tac",
    "grind": "tactic:grind",
    "dbg_trace": "dbg_trace",
    "sleep": "sleep",
}

_NUM_LIT_RE = re.compile(
    r"^(?:0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|\d[\d_]*)$"
)


def _is_lean_ident_delim(ch: str) -> bool:
    """Return True if `ch` cannot appear inside a bare Lean identifier."""
    if ch.isspace():
        return True
    if ch in "()[]{}⟨⟩.,:;@#\"'`«»\\+-*/<>=!&|^~%$?":
        return True
    code = ord(ch)
    # Exclude Lean Unicode operators / arrows / script delimiters, while
    # preserving Unicode letters, subscripts, and symbol glyphs like `℃`.
    if 0x2190 <= code <= 0x22FF or 0x27E6 <= code <= 0x27EF:
        return True
    if 0x2980 <= code <= 0x2BFF:
        return True
    return False


def _is_lean_ident_rest(ch: str) -> bool:
    """Return True if `ch` can continue a Lean identifier component."""
    if not _is_lean_ident_delim(ch):
        return True
    return ch in "'!?"


@dataclass(frozen=True)
class _Tok:
    kind: str  # "IDENT", "NUM", "SYM", "QIDENT"
    text: str
    start: int
    end: int
    line: int


def _tokenize_lean(cleaned: str) -> list[_Tok]:
    """Tokenize comment/string-stripped Lean source into lexical tokens."""
    toks: list[_Tok] = []
    n = len(cleaned)
    i = 0
    line = 1
    while i < n:
        ch = cleaned[i]
        if ch == "\n":
            line += 1
            i += 1
            continue
        if ch.isspace():
            i += 1
            continue
        if ch == "«":
            end_q = cleaned.find("»", i + 1)
            if end_q != -1 and "\n" not in cleaned[i : end_q + 1]:
                toks.append(_Tok("QIDENT", cleaned[i : end_q + 1], i, end_q + 1, line))
                i = end_q + 1
                continue
        if ch == "#" and i + 1 < n and cleaned[i + 1].isalpha():
            j = i + 1
            while j < n and _is_lean_ident_rest(cleaned[j]):
                j += 1
            toks.append(_Tok("IDENT", cleaned[i:j], i, j, line))
            i = j
            continue
        if cleaned.startswith("<;>", i) or cleaned.startswith("=>", i):
            sym = cleaned[i : i + 3] if cleaned.startswith("<;>", i) else "=>"
            toks.append(_Tok("SYM", sym, i, i + len(sym), line))
            i += len(sym)
            continue
        if cleaned.startswith(":=", i):
            toks.append(_Tok("SYM", ":=", i, i + 2, line))
            i += 2
            continue
        if ch.isdigit():
            j = i
            while j < n and (cleaned[j].isalnum() or cleaned[j] == "_"):
                j += 1
            word = cleaned[i:j]
            toks.append(_Tok("NUM", word, i, j, line))
            i = j
            continue
        if not _is_lean_ident_delim(ch) and ch != ".":
            j = i
            while j < n:
                if (
                    cleaned[j] == "."
                    and j + 1 < n
                    and not _is_lean_ident_delim(cleaned[j + 1])
                ):
                    j += 1
                    continue
                if _is_lean_ident_rest(cleaned[j]):
                    j += 1
                    continue
                break
            toks.append(_Tok("IDENT", cleaned[i:j], i, j, line))
            i = j
            continue
        toks.append(_Tok("SYM", ch, i, i + 1, line))
        i += 1
    return toks


def detect_disallowed_imports(
    cleaned: str, *, allow_theory_import_all: bool = False
) -> set[str]:
    """Detect forbidden `import all`, `Lean.*`, `Lake.*`, or UV imports."""
    found: set[str] = set()
    normalized = cleaned.replace("\r\n", "\n").replace("\r", "\n")
    has_module_hdr = bool(_MODULE_HEADER_RE.search(normalized))
    n = len(normalized)
    pos = 0
    while pos < n:
        match = _IMPORT_CLAUSE_RE.search(normalized, pos)
        if match is None:
            break
        raw_prefix = normalized[match.start() : match.end()]
        is_all = match.group(1) == "all"
        is_meta = bool(re.search(r"(?:^|\s)meta\s+", raw_prefix))
        clause_mods: list[str] = []
        cur = match.end()
        pos = cur
        while True:
            while cur < n and normalized[cur].isspace():
                cur += 1
            if cur >= n or normalized[cur] in (";", "#", "@"):
                break
            tok = _MOD_TOK_RE.match(normalized, cur)
            if tok is None:
                break
            raw_mod = tok.group(0)
            if (
                "." not in raw_mod
                and "«" not in raw_mod
                and raw_mod in _IMPORT_STOP_TOKENS
            ):
                break
            mod_name = _QUOTED_IDENT_RE.sub(r"\1", raw_mod)
            clause_mods.append(mod_name)
            top = mod_name.split(".", 1)[0]
            if top == "Lean":
                found.add("Lean_import")
            elif top == "Lake":
                found.add("Lake_import")
            elif mod_name == "Init.Meta" or mod_name.startswith("Init.Meta."):
                found.add("Init_Meta_import")
            elif mod_name == "Init.System" or mod_name.startswith("Init.System."):
                found.add("Init_System_import")
            elif (
                mod_name == "Std.Internal.UV"
                or mod_name.startswith("Std.Internal.UV.")
                or mod_name == "Std.Async"
                or mod_name.startswith("Std.Async.")
            ):
                found.add("UV_import")
            pos = tok.end()
            cur = tok.end()
        if is_meta and clause_mods != ["Init"]:
            found.add("meta_import")
        if is_all:
            permitted = (
                allow_theory_import_all
                and has_module_hdr
                and bool(clause_mods)
                and set(clause_mods).issubset(_ALLOWED_THEORY_IMPORT_ALL_MODULES)
            )
            if not permitted:
                found.add("import_all")
    return found


def _check_attr_block_tokens(
    toks: list[_Tok],
    idx: int,
    *,
    allow_spec_options: bool,
    found: set[str],
) -> int:
    """Validate `@[...]` attribute list starting at `@`, return closing index."""
    if idx + 1 >= len(toks) or toks[idx + 1].text != "[":
        return idx
    depth = 1
    j = idx + 2
    items: list[list[_Tok]] = [[]]
    while j < len(toks) and depth > 0:
        t = toks[j].text
        if t in ("[", "(", "{"):
            depth += 1
            items[-1].append(toks[j])
        elif t in ("]", ")", "}"):
            depth -= 1
            if depth > 0:
                items[-1].append(toks[j])
        elif t == "," and depth == 1:
            items.append([])
        else:
            items[-1].append(toks[j])
        j += 1

    allowed = _SPEC_ALLOWED_ATTRS if allow_spec_options else _THEORY_ALLOWED_ATTRS
    for item in items:
        if not item:
            continue
        k = 0
        if item[k].text == "-":
            continue
        if item[k].text in ("local", "scoped"):
            if item[k].text == "scoped" or not allow_spec_options:
                found.add(f"@[{item[k].text}]")
            k += 1
        if k >= len(item):
            continue
        head = item[k].text
        if head in _FORBIDDEN_ATTR_NAMES:
            found.add(f"@[{head}]")
        elif head not in allowed:
            found.add(f"@[{head}]")
    return j - 1


def _detect_disallowed_tokens_fallback(
    sources: dict[str, str],
    *,
    allow_theory_import_all: bool = False,
    allow_spec_options: bool = False,
) -> list[str]:
    """Linear-time Lean token fallback analyzer for unit/offline tests."""
    found: set[str] = set()
    for relpath in sorted(sources):
        cleaned = strip_lean_comments_and_strings(
            sources[relpath], preserve_guillemets=True
        )
        file_allows_import_all = allow_theory_import_all and (
            relpath == "theory/Anneal.lean" or relpath.startswith("theory/Anneal/")
        )
        found.update(
            detect_disallowed_imports(
                cleaned, allow_theory_import_all=file_allows_import_all
            )
        )
        toks = _tokenize_lean(cleaned)
        n = len(toks)
        local_binders: set[str] = set()
        # Stack entries: `[open_sym, top_level_idents_before_colon, past_colon]`
        binder_stack: list[tuple[str, list[str], bool]] = []
        in_fun_binder = False
        tactic_mode = False
        for i, tok in enumerate(toks):
            t = tok.text
            prev = toks[i - 1] if i > 0 else None
            nxt = toks[i + 1] if i + 1 < n else None
            # Reset local binders and tactic mode at top-level commands.
            if prev is None or prev.line < tok.line:
                if t in _CMD_STOP_TOKS and t != "in":
                    if t not in ("def", "theorem", "lemma", "abbrev"):
                        tactic_mode = False
                    elif prev is not None:
                        local_binders = set()
                        binder_stack.clear()
                        in_fun_binder = False
                        tactic_mode = False
                elif t in ("private", "public", "protected", "noncomputable"):
                    local_binders = set()
                    binder_stack.clear()
                    in_fun_binder = False
                    tactic_mode = False

            # Track local binders in strictly O(N) linear time.
            if t in ("(", "{", "["):
                binder_stack.append((t, [], False))
            elif t in (")", "}", "]"):
                if binder_stack:
                    binder_stack.pop()
            elif t == ":" and binder_stack:
                open_sym, cands, past_colon = binder_stack[-1]
                if not past_colon and open_sym in ("(", "{"):
                    local_binders.update(cands)
                    binder_stack[-1] = (open_sym, [], True)
            elif tok.kind in ("IDENT", "QIDENT") and binder_stack:
                open_sym, cands, past_colon = binder_stack[-1]
                if not past_colon and open_sym in ("(", "{"):
                    cands.append(t)

            if t in ("fun", "λ", "∀"):
                in_fun_binder = True
            elif in_fun_binder:
                if t in ("=>", ",", "."):
                    in_fun_binder = False
                elif tok.kind in ("IDENT", "QIDENT") and not binder_stack:
                    local_binders.add(t)

            # Track `by` tactic mode cleanly until top-level decl ends it.
            if t == "by" and (prev is None or prev.text != "."):
                tactic_mode = True
                continue

            # Detect `@[...]` attribute lists while ignoring `xs@[a, b]`.
            if t == "@" and nxt is not None and nxt.text == "[":
                glued_ident = (
                    prev is not None
                    and prev.kind in ("IDENT", "QIDENT")
                    and prev.end == tok.start
                )
                if not glued_ident:
                    _check_attr_block_tokens(
                        toks, i, allow_spec_options=allow_spec_options, found=found
                    )
                continue

            if t in _FORBIDDEN_CMD_MAP:
                if prev is not None and prev.text == ".":
                    continue
                if (
                    t == "axiom"
                    and (
                        prev is None
                        or prev.text not in ("public", "private", "protected")
                    )
                    and i > 0
                    and toks[i - 1].line == tok.line
                    and toks[i - 1].text != ";"
                ):
                    continue
                found.add(_FORBIDDEN_CMD_MAP[t])
                continue

            if t == "opaque":
                if prev is None or prev.line < tok.line or prev.text in (
                    "public",
                    "private",
                    "protected",
                    "noncomputable",
                    ";",
                    "in",
                ):
                    found.add("opaque")
                continue

            if t in ("unsafe", "partial"):
                if prev is None or prev.text != ".":
                    found.add(t)
                continue

            if t == "meta":
                if (
                    prev is None
                    or prev.line < tok.line
                    or (nxt is not None and nxt.text in _DECL_HEADS)
                ):
                    found.add("meta")
                continue

            if t == "deriving" and not allow_spec_options:
                if prev is None or prev.text != ".":
                    found.add("deriving")
                continue

            if t == "set_option":
                if not allow_spec_options or i + 2 >= n:
                    found.add("set_option")
                else:
                    opt = toks[i + 1].text
                    val = toks[i + 2]
                    if opt in _SPEC_ALLOWED_SET_OPTION_MODES:
                        if not _NUM_LIT_RE.match(val.text):
                            found.add("set_option")
                    elif opt.startswith("linter.") and len(opt) > len("linter."):
                        if val.text not in ("true", "false"):
                            found.add("set_option")
                    else:
                        found.add("set_option")
                continue

            if t in ("open", "export"):
                j = i + 1
                base_ns_list: list[str] = []
                while j < n and toks[j].line == tok.line and toks[j].text not in (
                    "in",
                    ";",
                    "(",
                    "hiding",
                    "renaming",
                    "scoped",
                ):
                    ns = toks[j].text
                    ns_clean = ns.removeprefix("_root_.")
                    root = ns_clean.split(".", 1)[0]
                    base_ns_list.append(ns_clean)
                    if root in _FORBIDDEN_NS_ROOTS:
                        if not (
                            allow_spec_options
                            and ns_clean == "System.Platform"
                        ):
                            found.add(f"{t}:{ns}")
                    j += 1
                if j < n and toks[j].text == "(" and len(base_ns_list) == 1:
                    base_ns = base_ns_list[0]
                    k = j + 1
                    while k < n and toks[k].text != ")":
                        item = toks[k].text.strip("«»")
                        if item not in ("->", ","):
                            full = f"{base_ns}.{item}"
                            full_root = full.split(".", 1)[0]
                            is_uv_pfx = any(
                                full == p or full.startswith(p + ".")
                                for p in _FORBIDDEN_SYS_UV_PREFIXES
                            )
                            if (full_root in _FORBIDDEN_NS_ROOTS or is_uv_pfx) and not (
                                allow_spec_options
                                and full in _ALLOWED_SYS_PLATFORM_DECLS
                            ):
                                found.add(f"{t}:{full}")
                        k += 1
                elif (
                    t == "open"
                    and j < n
                    and toks[j].text == "renaming"
                    and len(base_ns_list) == 1
                ):
                    base_ns = base_ns_list[0]
                    k = j + 1
                    expect_rhs = False
                    while k < n and toks[k].line == tok.line and toks[k].text not in (
                        "in",
                        ";",
                    ):
                        tok_txt = toks[k].text
                        if tok_txt == "->":
                            expect_rhs = True
                        elif tok_txt == ",":
                            expect_rhs = False
                        elif not expect_rhs:
                            item = tok_txt.strip("«»")
                            full = f"{base_ns}.{item}"
                            if any(
                                full == p or full.startswith(p + ".")
                                for p in _FORBIDDEN_SYS_UV_PREFIXES
                            ):
                                found.add(f"open:{full}")
                        k += 1
                continue

            if (
                allow_spec_options
                and t == "namespace"
                and nxt is not None
                and nxt.text.removeprefix("_root_.").split(".", 1)[0]
                in _SPEC_RESERVED_DECL_ROOTS
            ):
                found.add(f"decl_ns:{nxt.text}")
                continue

            if (
                allow_spec_options
                and t in ("default_or_ofNonempty", "value_of")
                and nxt is not None
                and nxt.text == "%"
            ):
                term_kind = (
                    "Lean.Parser.Term.defaultOrOfNonempty"
                    if t == "default_or_ofNonempty"
                    else "Lean.Parser.Term.valueOf"
                )
                found.add(f"syntax:{term_kind}")
                continue

            if (
                allow_spec_options
                and prev is not None
                and prev.text in _DECL_HEADS
                and tok.kind in ("IDENT", "QIDENT")
            ):
                decl_root = t.strip("«»").removeprefix("_root_.").split(".", 1)[0]
                if decl_root in _SPEC_RESERVED_DECL_ROOTS:
                    found.add(f"decl_ns:{t}")

            if t in ("by_elab", "sorry"):
                if prev is None or prev.text != ".":
                    if t not in ("def", "theorem"):
                        found.add("by_elab" if t == "by_elab" else "sorry")
                continue

            if t in _FORBIDDEN_TACTICS:
                in_decl_id = prev is not None and prev.text in _DECL_HEADS
                in_tactic_head = tactic_mode and (
                    prev is None
                    or prev.line < tok.line
                    or prev.text in _TACTIC_START_TOKENS
                )
                if not in_decl_id and tactic_mode and in_tactic_head:
                    found.add(_FORBIDDEN_TACTICS[t])
                continue

            if t == "decide":
                if (
                    nxt is not None
                    and nxt.text == "+"
                    and i + 2 < n
                    and toks[i + 2].text == "native"
                ):
                    found.add("native_decide")
                continue

            norm = _QUOTED_IDENT_RE.sub(r"\1", t)
            unrooted = norm.removeprefix("_root_.")
            # `_root_` escapes fail isValidSourceIdent, except the exact
            # `attribute [local semireducible] _root_.<c> in <decl>` shape.
            if "_root_" in norm.split("."):
                if (
                    not allow_spec_options
                    and _is_admitted_local_semireducible_token(
                        toks, i, unrooted
                    )
                ):
                    continue
                found.add("sorry" if unrooted == "sorryAx" else f"ident:{norm}")
                continue
            if (
                not allow_spec_options
                and prev is not None
                and (prev.text in _DECL_HEADS or prev.text == "namespace")
            ):
                decl_root = unrooted.split(".", 1)[0]
                if (
                    decl_root in _THEORY_FORBIDDEN_DECL_ROOTS
                    or unrooted in _KERNEL_ACCELERATED_NAMES
                ):
                    found.add(f"decl_ns:{unrooted}")
                    continue
                if (
                    prev.text in _DECL_HEADS
                    and _ends_with_local_semireducible_name(unrooted)
                ):
                    found.add(f"decl_shadow:{unrooted}")
                    continue
            pure_set = (
                _SPEC_FORBIDDEN_IDENTS if allow_spec_options else _FORBIDDEN_PURE_IDENTS
            )
            if unrooted in pure_set or (
                not allow_spec_options
                and unrooted in _THEORY_SUPPLEMENTAL_FORBIDDEN_IDENTS
            ):
                if unrooted not in local_binders:
                    found.add(unrooted)
                continue
            if not allow_spec_options and (
                any(
                    unrooted == pfx or unrooted.startswith(pfx + ".")
                    for pfx in _THEORY_SUPPLEMENTAL_FORBIDDEN_PREFIXES
                )
                and unrooted not in local_binders
            ):
                found.add(f"ref:{t}")
                continue
            if allow_spec_options and (
                unrooted.split(".", 1)[0] in _FORBIDDEN_NS_ROOTS
                and unrooted not in _ALLOWED_SYS_PLATFORM_DECLS
                and (prev is None or prev.text not in _DECL_HEADS)
                and unrooted not in local_binders
            ):
                if t == unrooted and "." in t:
                    found.add(f"ref:{unrooted}")

    return sorted(found)


# Standalone defender-owned Lean 4 AST audit script (never imports
# SpecPreflight.lean or TrustedBoundary.lean; loads only Init + Std sysroot).
# Mirrors `SpecPreflight` (for `spec` mode) and `TrustedBoundary` (for `theory`
# mode) 1:1 with O(1) HashSet tag tracking and separate `parseErrors`.
_LEAN_AST_AUDIT_SCRIPT = r"""
import Lean.Elab.Import
import Lean.Parser.Tactic

open Lean

structure TagSet where
  seen : Std.HashSet String := {}
  items : Array String := #[]

def maxReportedTags : Nat := 128
def maxReportedParseErrs : Nat := 32

def addBounded (r : IO.Ref TagSet) (cap : Nat) (tag : String) : IO Unit :=
  r.modify fun ts =>
    if ts.seen.contains tag || ts.items.size >= cap then ts
    else { seen := ts.seen.insert tag, items := ts.items.push tag }

def addTag (tags : IO.Ref TagSet) (tag : String) : IO Unit :=
  addBounded tags maxReportedTags tag

def addParseErr (errs : IO.Ref TagSet) (msg : String) : IO Unit :=
  addBounded errs maxReportedParseErrs msg

def allowedHeaderKinds : List Name := [
  ``Parser.Module.header, ``Parser.Module.moduleTk, ``Parser.Module.prelude,
  ``Parser.Module.import, ``Parser.Module.public, ``Parser.Module.all]

def allowedTheoryCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in, ``Parser.Command.attribute,
  ``Parser.Command.moduleDoc]

def allowedTheoryDeclarationKinds : List Name := [
  ``Parser.Command.abbrev, ``Parser.Command.definition,
  ``Parser.Command.theorem, ``Parser.Command.opaque,
  ``Parser.Command.instance, ``Parser.Command.inductive,
  ``Parser.Command.classInductive, ``Parser.Command.structure]

def allowedCommandSyntaxKinds : List Name := [
  ``Parser.Command.declModifiers, ``Parser.Command.declId,
  ``Parser.Command.declSig, ``Parser.Command.optDeclSig,
  ``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
  ``Parser.Command.whereStructInst, ``Parser.Command.docComment,
  ``Parser.Command.private, ``Parser.Command.protected,
  ``Parser.Command.public, ``Parser.Command.noncomputable,
  ``Parser.Command.openSimple,
  ``Parser.Command.sectionHeader, ``Parser.Command.eraseAttr,
  ``Parser.Command.ctor, ``Parser.Command.optDeriving,
  ``Parser.Command.optDefDeriving, ``Parser.Command.classTk,
  ``Parser.Command.structureTk, ``Parser.Command.extends,
  ``Parser.Command.structCtor, ``Parser.Command.structFields,
  ``Parser.Command.structSimpleBinder, ``Parser.Command.structExplicitBinder,
  ``Parser.Command.structImplicitBinder, ``Parser.Command.structInstBinder,
  ``Parser.Command.structParent, ``Parser.Termination.suffix,
  ``Lean.binderIdent, ``Lean.explicitBinders,
  ``Lean.bracketedExplicitBinders, ``Lean.unbracketedExplicitBinders]

def allowedTermSyntaxKinds : List Name := [
  ``Parser.Term.anonymousCtor, ``Parser.Term.app, ``Parser.Term.arrow,
  ``Parser.Term.attrInstance, ``Parser.Term.attrKind,
  ``Parser.Term.attributes, ``Parser.Term.basicFun,
  ``Parser.Term.binderDefault, ``Parser.Term.cdot, ``Parser.Term.dotIdent,
  ``Parser.Term.explicit, ``Parser.Term.explicitBinder,
  ``Parser.Term.forall, ``Parser.Term.fromTerm, ``Parser.Term.fun,
  ``Parser.Term.have, `Lean.Parser.Term.haveDecl, `Lean.Parser.Term.haveId,
  `Lean.Parser.Term.haveIdDecl, `Lean.Parser.Term.haveIdLhs, ``Parser.Term.hole,
  ``Parser.Term.hygienicLParen, ``Parser.Term.implicitBinder,
  ``Parser.Term.instBinder, ``Parser.Term.let, ``Parser.Term.letConfig,
  ``Parser.Term.letDecl, ``Parser.Term.letId, ``Parser.Term.letIdDecl,
  ``Parser.Term.letPatDecl, ``Parser.Term.match, ``Parser.Term.matchAlt,
  ``Parser.Term.matchAlts, ``Parser.Term.matchAltsWhereDecls,
  ``Parser.Term.matchDiscr, ``Parser.Term.namedArgument,
  ``Parser.Term.nomatch, ``Parser.Term.optEllipsis, ``Parser.Term.paren,
  ``Parser.Term.proj, ``Parser.Term.prop, ``Parser.Term.show,
  ``Parser.Term.sort, ``Parser.Term.strictImplicitBinder,
  ``Parser.Term.structInst, ``Parser.Term.structInstField,
  ``Parser.Term.structInstFieldDef, ``Parser.Term.structInstFieldEqns,
  ``Parser.Term.structInstFields, ``Parser.Term.structInstLVal,
  ``Parser.Term.subst, ``Parser.Term.syntheticHole, ``Parser.Term.tuple,
  ``Parser.Term.type, ``Parser.Term.typeAscription, ``Parser.Term.typeSpec,
  ``Parser.Attr.simple, ``Parser.Attr.instance, `Lean.Parser.Attr.simp,
  `fieldIdx, `group, `hygieneInfo, `num, `str, `char, `scientific]

def allowedNotationSyntaxKinds : List Name := [
  `term!_, `termIfThenElse, `termDepIfThenElse, `«term[_]»,
  `«term_&&_», `«term_||_», `«term_+_», `«term_-_», `«term_*_»,
  `«term_::_», `«term_++_», `«term_<_», `«term_≤_», `«term_>_»,
  `«term_≥_», `«term_==_», `«term_!=_», `«term_=_», `«term_≠_»,
  `«term__[_]_?», `«term_×_», `«term_↔_», `«term_∈_», `«term_∧_»,
  `«term_∨_», `«term¬_», `«term∃_,_», `«term‹_›», `Lean.cdot, `Lean.cdotTk]

def allowedTheoryTacticKinds : List Name := [
  ``Parser.Term.byTactic, ``Parser.Term.binderTactic,
  `Lean.Parser.Tactic.apply, `Lean.Parser.Tactic.cases,
  `Lean.Parser.Tactic.change, `Lean.Parser.Tactic.constructor,
  `Lean.Parser.Tactic.decide, `Lean.Parser.Tactic.dsimp,
  `Lean.Parser.Tactic.elimTarget, `Lean.Parser.Tactic.exact,
  `Lean.Parser.Tactic.first, `Lean.Parser.Tactic.induction,
  `Lean.Parser.Tactic.inductionAlt, `Lean.Parser.Tactic.inductionAltLHS,
  `Lean.Parser.Tactic.inductionAlts, `Lean.Parser.Tactic.injection,
  `Lean.Parser.Tactic.intro, `Lean.Parser.Tactic.left,
  `Lean.Parser.Tactic.location, `Lean.Parser.Tactic.locationHyp,
  `Lean.Parser.Tactic.optConfig, `Lean.Parser.Tactic.paren,
  `Lean.Parser.Tactic.refine, `Lean.Parser.Tactic.revert,
  `Lean.Parser.Tactic.right, `Lean.Parser.Tactic.rwRule,
  `Lean.Parser.Tactic.rwRuleSeq, `Lean.Parser.Tactic.rwSeq,
  `Lean.Parser.Tactic.simp, `Lean.Parser.Tactic.simpLemma,
  `Lean.Parser.Tactic.subst, `Lean.Parser.Tactic.tacticHave__,
  `Lean.Parser.Tactic.tacticLet__, `Lean.Parser.Tactic.«tacticNomatch_,,»,
  `Lean.Parser.Tactic.tacticRepeat_, `Lean.Parser.Tactic.tacticRfl,
  `Lean.Parser.Tactic.tacticSeq, `Lean.Parser.Tactic.tacticSeq1Indented,
  `Lean.Parser.Tactic.«tactic_<;>_», `Lean.Parser.Tactic.unfold,
  `tacticFunext___]

def allowedTheorySyntaxKinds : NameSet :=
  .ofList <|
    allowedHeaderKinds ++
    allowedTheoryCommandKinds ++
    allowedTheoryDeclarationKinds ++
    allowedCommandSyntaxKinds ++
    allowedTermSyntaxKinds ++
    allowedNotationSyntaxKinds ++
    allowedTheoryTacticKinds

def allowedTheoryAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible, `expose]

def forbiddenPureTermKinds : NameSet := .ofList [
  ``Lean.includeStr,
  `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
  `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Term.doIdbg,
  `Lean.Parser.Tactic.dbgTrace, `termPrintln!__]

def forbiddenPureIdentifiers : List Name := [
  `dbgTrace, `dbgTraceVal, `dbgTraceIfShared,
  `dbgStackTrace, `dbgStackTraceIf, `dbgSleep,
  `lean_dbg_trace, `lean_dbg_trace_if_shared,
  `lean_dbg_stack_trace, `lean_dbg_sleep,
  `loadDynlib, `loadPlugin,
  `lean_load_dynlib, `lean_load_plugin,
  `lean_dynlib_load, `lean_dynlib_get, `lean_dynlib_symbol_run_as_init,
  `includeStr]

def forbiddenPureRootNamespaces : List Name := [
  `Lake, `IO, `BaseIO, `EIO, `EST, `ST, `Task, `System]

def forbiddenSysUvPrefixes : List Name := [
  `Init.System, `Std.Internal.UV, `Internal.UV,
  `Lean.LoadDynlib, `Lean.loadDynlib, `Lean.loadPlugin, `Lean.Dynlib,
  `Dynlib]

def allowedSystemPlatformDecls : List Name := [
  `System.Platform.numBits,
  `System.Platform.getNumBits,
  `System.Platform.numBits_eq]

def isValidSourceIdent (id : Name) : Bool :=
  id.isAnonymous ||
    (!id.hasMacroScopes && id.eraseMacroScopes == id &&
     !id.toString.isEmpty &&
     id.components.all fun
       | .str .anonymous seg => !seg.isEmpty && seg != "_root_"
       | _ => false)

def isForbiddenPureNamespace (n : Name) (banLeanRoot : Bool := false) : Bool :=
  let u := n.replacePrefix rootNamespace .anonymous
  let r := u.getRoot
  forbiddenPureRootNamespaces.contains r ||
    (banLeanRoot && r == `Lean) ||
    forbiddenSysUvPrefixes.any fun pre => u == pre || pre.isPrefixOf u

def isForbiddenPureImport (m : Name) : Bool :=
  let r := m.getRoot
  r == `Lean || r == `Lake ||
    m == `Init.System || (`Init.System).isPrefixOf m ||
    m == `Std.Internal.UV || (`Std.Internal.UV).isPrefixOf m

def isSupplementalForbiddenImport (m : Name) : Option String :=
  if m == `Init.Meta || (`Init.Meta).isPrefixOf m then some "Init_Meta_import"
  else if m == `Std.Async || (`Std.Async).isPrefixOf m then some "UV_import"
  else none

def supplementalTheoryForbiddenIdentifiers : List Name := [
  `autoParam]

def supplementalTheoryForbiddenPrefixes : List Name := [
  `Lean.Syntax, `Lean.SourceInfo, `Lean.Name, `Lean.Parser,
  `Lean.Elab, `Lean.Meta, `Lean.Expr, `Lean.Environment, `Lean.mkAtom]

def supplementalSpecDeclRootNamespaces : List Name := [
  `Expected, `Captured, `SpecPreflight, `TrustedBoundary,
  `IncorrectnessCheck, `IncorrectnessExpected]

def supplementalSpecForbiddenTermKinds : NameSet := .ofList [
  `Lean.Parser.Term.defaultOrOfNonempty,
  `Lean.Parser.Term.valueOf]

def theoryReservedKernelRoots : List Name := [
  `Nat, `String, `Char, `Bool, `Int, `Int8, `Int16, `Int32, `Int64, `ISize,
  `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Float, `Float32,
  `ByteArray, `Subarray, `Array, `List, `Option, `Sum, `Prod, `Fin, `Subtype,
  `Eq, `HEq, `Quot, `Classical, `Lean, `Init, `Std, `Lake, `LeanExport,
  `LeanIR, `System, `IO, `Task, `Thunk, `Unit, `PUnit, `Empty, `PEmpty, `True,
  `False, `And, `Or, `Not, `Iff, `Exists, `Sigma, `PSigma, `Decidable,
  `Nonempty, `Ordering, `Rat, `Except, `EStateM, `StateM]

def theoryKernelAcceleratedNames : List Name := [
  `Nat.zero, `Nat.succ, `Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd,
  `Nat.mod, `Nat.div, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor,
  `Nat.shiftLeft, `Nat.shiftRight, `String.ofList]

def supplementalTheoryDeclRootNamespaces : List Name :=
  [`Trusted, `SpecPreflight, `TrustedBoundary, `Expected, `Captured,
   `Proof, `Spec, `IncorrectnessCheck, `IncorrectnessExpected] ++
    theoryReservedKernelRoots

def candidateOpenNamespaces (currNs : Name) (openDecls : List OpenDecl)
    (id : Name) : List Name :=
  let rec scopeCandidates : Name → List Name
    | .anonymous => [id.replacePrefix rootNamespace .anonymous]
    | ns@(.str p _) => (ns ++ id) :: scopeCandidates p
    | _ => []
  let openCandidates := openDecls.filterMap fun
    | OpenDecl.simple ns _ => some (ns ++ id)
    | OpenDecl.explicit short full =>
      if id == short then some full else none
  (scopeCandidates currNs ++ openCandidates).eraseDups

structure ParseScope where
  header : String
  currNamespace : Name
  openDecls : List OpenDecl
  deriving Inhabited

def nameOfParseScopes : List ParseScope → Nat → Name
  | _, 0 => .anonymous
  | [], _ => .anonymous
  | s :: ss, n + 1 =>
    if s.header == "" then .anonymous
    else .str (nameOfParseScopes ss n) s.header

def declarationIdent? (stx : Syntax) : Option Name :=
  let decl := stx[1]
  if decl.getKind == ``Parser.Command.instance then
    if decl[3].isNone then none else some decl[3][0][0].getId
  else
    some decl[1][0].getId

def localSemireducibleAllowlist : List Name := [`Nat.bitwise]

def matchLocalSemireducibleIn? (args : Array Syntax) :
    Option (Name × Syntax) := do
  guard (args.size == 3)
  let lhs := args[0]!
  guard (lhs.isOfKind ``Parser.Command.attribute && lhs.getArgs.size == 5)
  let items := lhs[2].getArgs
  guard (items.size == 1)
  let inst := items[0]!
  guard (inst.isOfKind ``Parser.Term.attrInstance && inst.getArgs.size == 2)
  let kind := inst[0]
  guard (kind.isOfKind ``Parser.Term.attrKind && kind.getArgs.size == 1)
  let kindOpt := kind[0]
  guard (kindOpt.isOfKind nullKind && kindOpt.getArgs.size == 1 &&
    kindOpt[0].isOfKind ``Parser.Term.local)
  let attr := inst[1]
  guard (attr.isOfKind ``Parser.Attr.simple && attr.getArgs.size == 2 &&
    attr[0].isIdent && attr[0].getId == `semireducible &&
    attr[1].isOfKind nullKind && attr[1].getArgs.isEmpty)
  let ids := lhs[4].getArgs
  guard (ids.size == 1 && ids[0]!.isIdent)
  let raw := ids[0]!.getId
  guard (!raw.hasMacroScopes && raw != rootNamespace &&
    rootNamespace.isPrefixOf raw)
  let c := raw.replacePrefix rootNamespace .anonymous
  guard (localSemireducibleAllowlist.contains c)
  let decl := args[2]!
  guard (decl.isOfKind ``Parser.Command.declaration && decl.getArgs.size == 2)
  guard ([``Parser.Command.theorem, ``Parser.Command.definition].contains
    decl[1].getKind)
  guard (decl[0].isOfKind ``Parser.Command.declModifiers &&
    decl[0].getArgs.size > 1 && decl[0][1].isNone)
  return (c, decl)

def endsWithLocalSemireducibleName (n : Name) : Bool :=
  localSemireducibleAllowlist.any (·.components.isSuffixOf n.components)

partial def declaresLocalSemireducibleShadow (currNs : Name) (stx : Syntax) :
    Bool :=
  let k := stx.getKind
  if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let full := currNs ++ id.replacePrefix rootNamespace .anonymous
      let inner := collectIdents stx[1]
      endsWithLocalSemireducibleName full ||
        endsWithLocalSemireducibleName id ||
        inner.any fun i => endsWithLocalSemireducibleName (full ++ i)
    | none => false
  else if k == ``Parser.Command.in then
    declaresLocalSemireducibleShadow currNs stx[2]
  else if k == ``Parser.Command.mutual then
    stx[1].getArgs.any (declaresLocalSemireducibleShadow currNs)
  else false
where
  directIdents (s : Syntax) : Array Name :=
    s.getArgs.foldl (init := #[]) fun acc c =>
      if c.isIdent then acc.push c.getId
      else if c.isOfKind nullKind then
        acc ++ c.getArgs.filterMap fun d =>
          if d.isIdent then some d.getId else none
      else acc
  collectIdents (s : Syntax) : Array Name :=
    let here :=
      if [``Parser.Command.ctor, ``Parser.Command.structCtor,
          ``Parser.Command.structSimpleBinder,
          ``Parser.Command.structExplicitBinder,
          ``Parser.Command.structImplicitBinder,
          ``Parser.Command.structInstBinder,
          ``Parser.Command.structParent].contains s.getKind then
        directIdents s
      else #[]
    here ++ s.getArgs.foldl (fun acc c => acc ++ collectIdents c) #[]

def allowedSpecCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end,
  ``Parser.Command.universe, ``Parser.Command.variable,
  ``Parser.Command.open, ``Parser.Command.export,
  ``Parser.Command.mutual, ``Parser.Command.in,
  ``Parser.Command.attribute, ``Parser.Command.deriving,
  ``Parser.Command.set_option, ``Parser.Command.moduleDoc]

def allowedSpecInLhsKinds : List Name := [
  ``Parser.Command.open, ``Parser.Command.variable,
  ``Parser.Command.universe, ``Parser.Command.set_option,
  ``Parser.Command.attribute]

def isAllowedSpecNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedSpecCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

def allowedSpecDeclarationKinds : List Name := [
  ``Parser.Command.definition, ``Parser.Command.abbrev,
  ``Parser.Command.theorem, ``Parser.Command.structure,
  ``Parser.Command.inductive, ``Parser.Command.classInductive,
  ``Parser.Command.instance]

def allowedSpecDeclModifierKinds : List Name := [
  ``Parser.Command.docComment, ``Parser.Term.attributes,
  ``Parser.Command.private, ``Parser.Command.protected,
  ``Parser.Command.noncomputable]

def isAllowedSpecDeclModifierKind (isModule : Bool) (k : Name) : Bool :=
  allowedSpecDeclModifierKinds.contains k ||
    (isModule && k == ``Parser.Command.public)

def forbiddenSpecModifierKinds : List Name := [
  ``Parser.Command.meta, ``Parser.Command.unsafe,
  ``Parser.Command.partial,
  ``Parser.Term.unsafe, ``Parser.Term.scoped,
  `Lean.Parser.Termination.partialFixpoint,
  `Lean.Parser.Termination.coinductiveFixpoint,
  `Lean.Parser.Termination.inductiveFixpoint]

def forbiddenSpecRootNamespaces : List Name :=
  `Lean :: forbiddenPureRootNamespaces

def forbiddenSpecDeclRootNamespaces : List Name :=
  forbiddenSpecRootNamespaces ++ [
    `Trusted, `Anneal, `Proof, `Init, `Std,
    `Nat, `String, `Char, `Bool, `Int, `Int8, `Int16, `Int32, `Int64, `ISize,
    `UInt8, `UInt16, `UInt32, `UInt64, `USize, `BitVec, `Float, `Float32,
    `ByteArray, `Subarray, `Array, `List, `Option, `Sum, `Prod, `Fin, `Subtype,
    `Eq, `HEq, `Quot, `Classical, `LeanExport, `LeanIR, `Thunk, `Unit, `PUnit,
    `Empty, `PEmpty, `True, `False, `And, `Or, `Not, `Iff, `Exists, `Sigma,
    `PSigma, `Decidable, `Nonempty, `Ordering, `Rat, `Except, `EStateM, `StateM]

def forbiddenSpecIdentifierComponents : List String := [
  "autoParam", "panic", "panicCore", "panicWithPos", "panicWithPosWithDecl",
  "outOfBounds", "repeatM", "sliceOrPanic"]

def forbiddenSpecIdentifiers : List Name :=
  [`autoParam, `panic, `panicCore, `panicWithPos, `panicWithPosWithDecl] ++
    forbiddenPureIdentifiers

def allowedSpecSimpleAttrs : List Name := [
  `reducible, `semireducible, `irreducible, `inline, `match_pattern]

def allowedSpecEraseAttrs : List Name := [
  `simp, `instance, `ext, `specialize,
  `reducible, `semireducible, `irreducible, `inline, `match_pattern]

def allowedSpecDerivingClasses : List Name := [
  `BEq, `DecidableEq, `Repr, `Inhabited, `Ord, `Hashable, `Nonempty]

def nonTacticSpecCategories : List Name := [
  `attr, `binderPred, `command, `doElem, `level, `prec, `prio,
  `structInstFieldDecl, `term]

def allowedSpecTacticKinds : NameSet :=
  .ofList <| allowedTheoryTacticKinds ++ [
    `Lean.cdot, `Lean.calcTactic,
    `Lean.Parser.Tactic.tacticSeqBracketed,
    `Lean.Parser.Tactic.nestedTactic,
    `Lean.Parser.Tactic.focus, `Lean.Parser.Tactic.case,
    `Lean.Parser.Tactic.case', `Lean.Parser.Tactic.caseArg,
    `Lean.Parser.Tactic.«tacticNext_=>_»,
    `Lean.Parser.Tactic.allGoals, `Lean.Parser.Tactic.anyGoals,
    `Lean.Parser.Tactic.skip, `Lean.Parser.Tactic.done,
    `Lean.Parser.Tactic.tacticTry_, `Lean.Parser.Tactic.tacticIterate____,
    `Lean.Parser.Tactic.repeat', `Lean.Parser.Tactic.repeat1',
    `Lean.Parser.Tactic.tacIfThenElse, `Lean.Parser.Tactic.tacDepIfThenElse,
    `Lean.Parser.Tactic.rotateLeft, `Lean.Parser.Tactic.rotateRight,
    `Lean.Parser.Tactic.assumption, `Lean.Parser.Tactic.contradiction,
    `Lean.Parser.Tactic.tacticTrivial, `Lean.Parser.Tactic.tacticExfalso,
    `Lean.Parser.Tactic.tacticNofun, `Lean.Parser.Tactic.eqRefl,
    `Lean.Parser.Tactic.acRfl, `Lean.Parser.Tactic.applyRfl,
    `Lean.Parser.Tactic.symm, `Lean.Parser.Tactic.congr,
    `Lean.Parser.Tactic.split, `Lean.Parser.Tactic.clear,
    `Lean.Parser.Tactic.clearValue, `Lean.Parser.Tactic.generalize,
    `Lean.Parser.Tactic.rename, `Lean.Parser.Tactic.renameI,
    `Lean.Parser.Tactic.replace, `Lean.Parser.Tactic.specialize,
    `Lean.Parser.Tactic.intros, `Lean.Parser.Tactic.introMatch,
    `Lean.Parser.Tactic.injections, `Lean.Parser.Tactic.substEqs,
    `Lean.Parser.Tactic.substVars, `Lean.Parser.Tactic.delta,
    `Lean.Parser.Tactic.rewriteSeq, `Lean.Parser.Tactic.tacticErw___,
    `Lean.Parser.Tactic.tacticRwa__, `Lean.Parser.Tactic.show,
    `Lean.Parser.Tactic.tacticSuffices_, `Lean.Parser.Tactic.«tacticExists_,,»,
    `Lean.Parser.Tactic.tacticAnd_intros, `Lean.Parser.Tactic.tacticHave',
    `Lean.Parser.Tactic.tacticHaveI__, `Lean.Parser.Tactic.tacticLet'__,
    `Lean.Parser.Tactic.tacticLetI__, `Lean.Parser.Tactic.letToHave,
    `Lean.Parser.Tactic.tacticInfer_instance, `Lean.Parser.Tactic.refine',
    `Lean.Parser.Tactic.falseOrByContra, `Lean.Parser.Tactic.classical,
    `Lean.Parser.Tactic.match, `«tacticBy_cases_:_»,
    `Lean.Parser.Tactic.simpAll, `Lean.Parser.Tactic.simpArith,
    `Lean.Parser.Tactic.simpAllArith, `Lean.Parser.Tactic.simpa,
    `Lean.Parser.Tactic.simpaArgsRest, `Lean.Parser.Tactic.tacticSimpa!_,
    `Lean.Parser.Tactic.tacticSimpa!__1, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.locationType,
    `Lean.Parser.Tactic.locationWildcard, `Lean.Parser.Tactic.discharger,
    `Lean.Parser.Tactic.configItem, `Lean.Parser.Tactic.posConfigItem,
    `Lean.Parser.Tactic.negConfigItem,
    `Lean.Parser.Tactic.omega, `Lean.Parser.Tactic.tacticBv_omega,
    `tacticDecreasing_tactic, `tacticDecreasing_trivial,
    `tacticDecreasing_trivial_pre_omega, `tacticDecreasing_with_,
    `tacticSimp_wf, `tacticClean_wf,
    `tacticGet_elem_tactic, `tacticGet_elem_tactic_trivial,
    `Array.tacticArray_get_dec, `Array.tacticArray_mem_dec,
    `List.tacticSizeOf_list_dec,
    `Lean.Parser.Tactic.funCases, `Lean.Parser.Tactic.funInduction,
    `Lean.Parser.Tactic.rcases, `Lean.Parser.Tactic.rintro,
    `Lean.Parser.Tactic.obtain,
    `Lean.Parser.Tactic.rcasesPatLo, `Lean.Parser.Tactic.rcasesPatMed,
    `Lean.Parser.Tactic.rcasesPat.ignore, `Lean.Parser.Tactic.rcasesPat.paren,
    `Lean.Parser.Tactic.rcasesPat.clear, `Lean.Parser.Tactic.rcasesPat.explicit,
    `Lean.Parser.Tactic.rcasesPat.tuple, `Lean.Parser.Tactic.rcasesPat.one,
    `Lean.Parser.Tactic.rintroPat.one, `Lean.Parser.Tactic.rintroPat.binder]

def forbiddenSpecTermKinds : NameSet := .ofList [
  ``Lean.includeStr, ``Lean.byElab,
  ``Parser.Term.sorry, ``Parser.Term.unsafe,
  ``Parser.Term.quotedName, ``Parser.Term.doubleQuotedName,
  ``Parser.Term.binderTactic,
  `Lean.modCast,
  `Lean.Parser.Term.panic, `Lean.Parser.Term.unreachable,
  `Lean.Parser.Term.assert, `Lean.Parser.Term.debugAssert,
  `Lean.Parser.Term.doAssert, `Lean.Parser.Term.doAssertion,
  `Lean.Parser.Term.doDebugAssert,
  `«term__[_]_!»,
  `Lean.Parser.Term.doWhile, `Lean.Parser.Term.doRepeat,
  `Lean.Parser.Term.doRepeatUntil,
  `Lean.Parser.Command.contractDeclVal,
  `Lean.Parser.Command.requiresClause,
  `Lean.Parser.Command.ensuresClause,
  `«term∎»,
  `Std.DTreeMap.Internal.Impl.«term✓»,
  `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
  `Lean.Parser.Term.doDbgTrace, `Lean.Parser.Term.doIdbg,
  `Lean.Parser.Term.matchExpr, `Lean.Parser.Term.letExpr,
  `Lean.Parser.Term.doMatchExpr, `Lean.Parser.Term.doLetExpr,
  `Lean.Parser.Term.doLetMetaExpr, `Lean.Parser.Term.showTermElabImpl,
  `Lean.Parser.Tactic.showTermElab, `Lean.Parser.Term.declName,
  `Lean.Parser.Term.withDeclName, `Lean.Parser.Term.privateDecl,
  `Lean.Parser.Term.leading_parser, `Lean.Parser.Term.trailing_parser,
  `Lean.Parser.Term.elabToSyntax, `Lean.«termMacro.trace[_]_»,
  `Lean.Parser.Syntax.exact?, `Lean.termEval_prec_, `Lean.termEval_prio_,
  `termPrintln!__, `Lean.Parser.Term.dynamicQuot,
  `Lean.Parser.Term.precheckedQuot,
  `Lean.Parser.Term.logNamedErrorMacro,
  `Lean.Parser.Term.logNamedErrorAtMacro,
  `Lean.Parser.Term.logNamedWarningMacro,
  `Lean.Parser.Term.logNamedWarningAtMacro,
  `Lean.Parser.Term.throwNamedErrorMacro,
  `Lean.Parser.Term.throwNamedErrorAtMacro]

def isQuotationKind (k : SyntaxNodeKind) : Bool :=
  match k with
  | .str _ "quot" | .str _ "quotSeq" => true
  | _ => false

def hasUnsafeRecComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => seg == "_unsafe_rec"
    | _ => false

def hasBangComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => seg.contains '!'
    | _ => false

def hasForbiddenSpecIdentComponent (id : Name) : Bool :=
  id.components.any fun
    | .str .anonymous seg => forbiddenSpecIdentifierComponents.contains seg
    | _ => false

def collectSpecParserSets (env : Environment) : IO (NameSet × NameSet) := do
  let cats := (Parser.parserExtension.getState env).categories
  let some cmdCat := cats.find? `command
    | throw <| IO.userError "missing command parser category"
  let cmds := cmdCat.kinds.foldl (init := {}) fun acc k _ => acc.insert k
  let tacs := cats.foldl (init := {}) fun acc cName cat =>
    if nonTacticSpecCategories.contains cName then acc
    else cat.kinds.foldl (init := acc) fun inner k _ => inner.insert k
  return (cmds, tacs)

partial def inspectHeaderSyntax (s : Syntax) (requirePrelude := false)
    (tags : IO.Ref TagSet) : IO Unit := do
  match s with
  | .missing => addTag tags "header:missing_syntax"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do
      addTag tags s!"header:invalid_ident:{val}"
  | .node _ k args =>
    unless k == nullKind || allowedHeaderKinds.contains k do
      addTag tags s!"header:unsupported_syntax:{k}"
    if requirePrelude && k == ``Parser.Module.header then
      unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
        addTag tags "missing_prelude"
    for child in args do
      inspectHeaderSyntax child requirePrelude tags

def isSpecPrioOpt (s : Syntax) : Bool :=
  if s.isOfKind nullKind && s.getArgs.isEmpty then true
  else if s.isOfKind nullKind && s.getArgs.size == 1 then
    let k := s.getArgs[0]!.getKind
    k == numLitKind ||
      [`prioHigh, `prioLow, `prioDefault, `prioMid].contains k
  else false

def validateSpecAttrInstance (args : Array Syntax) (isModule : Bool)
    (tags : IO.Ref TagSet) : IO Unit := do
  unless args.size == 2 do
    addTag tags "@[invalid_shape]"; return ()
  let attrKind := args[0]!
  unless attrKind.isOfKind ``Parser.Term.attrKind && attrKind.getArgs.size == 1 do
    addTag tags "@[invalid_kind]"; return ()
  let kindOpt := attrKind.getArgs[0]!
  unless kindOpt.isOfKind nullKind &&
      (kindOpt.getArgs.isEmpty ||
        (kindOpt.getArgs.size == 1 && kindOpt.getArgs[0]!.isOfKind ``Parser.Term.local)) do
    addTag tags "@[scoped]"
  let attr := args[1]!
  let ak := attr.getKind
  if ak == ``Parser.Attr.simple then
    let attrName := attr[0].getId
    let ok := allowedSpecSimpleAttrs.contains attrName ||
      (isModule && attrName == `expose && kindOpt.getArgs.isEmpty)
    unless ok do addTag tags s!"@[{attrName}]"
    unless attr[1].isOfKind nullKind && attr[1].getArgs.isEmpty do
      addTag tags s!"@[{attrName}:args]"
  else if ak == `Lean.Parser.Attr.simp then
    let aArgs := attr.getArgs
    unless aArgs.size == 4 do addTag tags "@[simp:shape]"; return ()
    let okPost := aArgs[1]!.isOfKind nullKind &&
      (aArgs[1]!.getArgs.isEmpty ||
        (aArgs[1]!.getArgs.size == 1 &&
          match aArgs[1]!.getArgs[0]! with
          | .atom _ "↓" | .atom _ "↑" => true
          | _ => false))
    let okInv := aArgs[2]!.isOfKind nullKind &&
      (aArgs[2]!.getArgs.isEmpty ||
        (aArgs[2]!.getArgs.size == 1 &&
          match aArgs[2]!.getArgs[0]! with
          | .atom _ "←" | .atom _ "<-" => true
          | _ => false))
    unless okPost && okInv && isSpecPrioOpt aArgs[3]! do
      addTag tags "@[simp:args]"
  else if ak == ``Parser.Attr.instance then
    unless attr.getArgs.size == 2 && isSpecPrioOpt attr[1] do
      addTag tags "@[instance:args]"
  else if ak == ``Parser.Attr.ext then
    let aArgs := attr.getArgs
    unless aArgs.size >= 1 &&
        (aArgs.extract 1 aArgs.size).all fun c =>
          isSpecPrioOpt c ||
            (c.isOfKind nullKind && c.getArgs.size == 1 &&
              match c.getArgs[0]! with | .atom _ "flat" => true | _ => false) do
      addTag tags "@[ext:args]"
  else if ak == ``Parser.Attr.specialize then
    unless attr.getArgs.size == 2 && attr[1].isOfKind nullKind &&
        attr[1].getArgs.all fun c =>
          c.isOfKind numLitKind ||
            (c.isIdent && isValidSourceIdent c.getId &&
              !hasUnsafeRecComponent c.getId &&
              !hasBangComponent c.getId &&
              !hasForbiddenSpecIdentComponent c.getId &&
              !forbiddenSpecRootNamespaces.contains c.getId.getRoot) do
      addTag tags "@[specialize:args]"
  else
    addTag tags s!"@[{ak}]"

def validateSpecSectionHeader (args : Array Syntax) (isModule : Bool)
    (tags : IO.Ref TagSet) : IO Unit := do
  for child in args do
    let ok := child.isOfKind nullKind &&
      (child.getArgs.isEmpty ||
        (child.getArgs.size == 1 &&
          match child.getArgs[0]! with
          | .atom _ "noncomputable" => true
          | .atom _ "public" => isModule
          | _ => false) ||
        (isModule && child.getArgs.size == 3 &&
          match child.getArgs[0]!, child.getArgs[1]!, child.getArgs[2]! with
          | .atom _ "@[", .atom _ "expose", .atom _ "]" => true
          | _, _, _ => false))
    unless ok do addTag tags "section_header:unsupported"

def validateSpecSetOption (args : Array Syntax) (tags : IO.Ref TagSet) : IO Unit := do
  unless args.size == 4 || args.size == 6 do addTag tags "set_option"; return ()
  unless args[2]!.isOfKind nullKind && args[2]!.getArgs.isEmpty do
    addTag tags "set_option"; return ()
  let optName := args[1]!.getId
  let valStx := args[3]!
  if optName == `maxHeartbeats || optName == `maxRecDepth then
    unless valStx.isOfKind numLitKind do addTag tags "set_option"
  else if (`linter).isPrefixOf optName then
    let isBool := match valStx with
      | .atom _ "true" | .atom _ "false" => true
      | .ident _ _ `true _ | .ident _ _ `false _ => true
      | _ => false
    unless isBool do addTag tags "set_option"
  else
    addTag tags "set_option"

def validateSpecDecideTactic (args : Array Syntax) (tags : IO.Ref TagSet) : IO Unit := do
  unless args.size == 2 && args[1]!.isOfKind `Lean.Parser.Tactic.optConfig &&
      args[1]!.getArgs.size == 1 do
    addTag tags "decide:config"; return ()
  for item in args[1]![0].getArgs do
    unless item.isOfKind `Lean.Parser.Tactic.configItem && item.getArgs.size == 1 do
      addTag tags "decide:config"; continue
    let inner := item[0]
    let ik := inner.getKind
    unless (ik == `Lean.Parser.Tactic.posConfigItem ||
        ik == `Lean.Parser.Tactic.negConfigItem) && inner.getArgs.size == 2 do
      addTag tags "decide:config"; continue
    let opt := inner[1].getId
    unless opt == `kernel || opt == `revert do
      if opt == `native then addTag tags "native_decide"
      else addTag tags s!"decide:+{opt}"

def checkForbiddenSpecNs (how : String) (ns : Name) (tags : IO.Ref TagSet) : IO Unit := do
  if isForbiddenPureNamespace ns (banLeanRoot := true) then
    addTag tags s!"{how}:{ns}"

def checkForbiddenSpecDeclNs (how : String) (ns : Name) (tags : IO.Ref TagSet) : IO Unit := do
  checkForbiddenSpecNs how ns tags
  let u := ns.replacePrefix rootNamespace .anonymous
  if forbiddenSpecDeclRootNamespaces.contains u.getRoot ||
      supplementalSpecDeclRootNamespaces.contains u.getRoot then
    addTag tags s!"decl_ns:{ns}"

def validateSpecOpenDecl (currNs : Name) (openDecls : List OpenDecl)
    (parserEnv : Environment) (openDecl : Syntax) (tags : IO.Ref TagSet) :
    IO (Environment × List OpenDecl) := do
  let hasSimple (ods : List OpenDecl) (ns : Name) : Bool :=
    ods.any fun | OpenDecl.simple existing _ => existing == ns | _ => false
  let addSimple (ods : List OpenDecl) (ns : Name) : List OpenDecl :=
    if hasSimple ods ns then ods else OpenDecl.simple ns [] :: ods
  let k := openDecl.getKind
  if k == ``Parser.Command.openSimple then
    let mut env := parserEnv
    let mut ods := openDecls
    for idStx in openDecl[0].getArgs do
      let id := idStx.getId
      unless isValidSourceIdent id && !hasUnsafeRecComponent id do
        addTag tags s!"open:invalid:{id}"
      let candidates := candidateOpenNamespaces currNs ods id
      let mut added := false
      for ns in candidates do
        checkForbiddenSpecNs "open" ns tags
        if env.isNamespace ns then
          ods := addSimple ods ns
          env := Parser.parserExtension.activateScoped env ns
          added := true
      if !added then
        let stripped := id.replacePrefix rootNamespace .anonymous
        checkForbiddenSpecNs "open" stripped tags
        ods := addSimple ods stripped
    return (env, ods)
  else if k == ``Parser.Command.openOnly then
    let nsId := openDecl[0].getId
    unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
      addTag tags s!"open:invalid:{nsId}"
    let itemIds := openDecl[2].getArgs.map Syntax.getId
    for itemId in itemIds do
      unless isValidSourceIdent itemId && !hasUnsafeRecComponent itemId &&
          !hasBangComponent itemId && !hasForbiddenSpecIdentComponent itemId do
        addTag tags s!"open:item:{itemId}"
    let candidates := candidateOpenNamespaces currNs openDecls nsId
    let mut ods := openDecls
    for ns in candidates do
      if ns == `System.Platform then
        if itemIds.isEmpty then addTag tags "open:System.Platform"
        for itemId in itemIds do
          let full := ns ++ itemId
          unless allowedSystemPlatformDecls.contains full do
            addTag tags s!"open:{full}"
          ods := OpenDecl.explicit itemId full :: ods
      else
        checkForbiddenSpecNs "open" ns tags
        for itemId in itemIds do
          let full := ns ++ itemId
          checkForbiddenSpecNs "open" full tags
          ods := OpenDecl.explicit itemId full :: ods
    return (parserEnv, ods)
  else if k == ``Parser.Command.openHiding || k == ``Parser.Command.openRenaming then
    let nsId := openDecl[0].getId
    unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
      addTag tags s!"open:invalid:{nsId}"
    let candidates := candidateOpenNamespaces currNs openDecls nsId
    if k == ``Parser.Command.openHiding then
      for idStx in openDecl[2].getArgs do
        let hid := idStx.getId
        unless isValidSourceIdent hid && !hasUnsafeRecComponent hid do
          addTag tags s!"open:hiding:{hid}"
    else
      for itemStx in openDecl[2].getArgs do
        let fromId := itemStx[0].getId
        let toId := itemStx[2].getId
        unless isValidSourceIdent fromId && !hasUnsafeRecComponent fromId &&
            !hasBangComponent fromId && !hasForbiddenSpecIdentComponent fromId &&
            isValidSourceIdent toId && !hasUnsafeRecComponent toId &&
            !hasBangComponent toId && !hasForbiddenSpecIdentComponent toId do
          addTag tags s!"open:renaming:{fromId}"
        for cand in candidates do
          checkForbiddenSpecNs "open" (cand ++ fromId) tags
    let mut env := parserEnv
    let mut ods := openDecls
    let mut added := false
    for ns in candidates do
      checkForbiddenSpecNs "open" ns tags
      if env.isNamespace ns then
        if k == ``Parser.Command.openHiding then
          ods := addSimple ods ns
          env := Parser.parserExtension.activateScoped env ns
        else
          for itemStx in openDecl[2].getArgs do
            let fromId := itemStx[0].getId
            let toId := itemStx[2].getId
            ods := OpenDecl.explicit toId (ns ++ fromId) :: ods
        added := true
    if !added then
      let stripped := nsId.replacePrefix rootNamespace .anonymous
      checkForbiddenSpecNs "open" stripped tags
      if k == ``Parser.Command.openRenaming then
        for itemStx in openDecl[2].getArgs do
          let fromId := itemStx[0].getId
          let toId := itemStx[2].getId
          checkForbiddenSpecNs "open" (stripped ++ fromId) tags
          ods := OpenDecl.explicit toId (stripped ++ fromId) :: ods
      else
        ods := addSimple ods stripped
    return (env, ods)
  else if k == ``Parser.Command.openScoped then
    let mut env := parserEnv
    for idStx in openDecl[1].getArgs do
      let id := idStx.getId
      unless isValidSourceIdent id && !hasUnsafeRecComponent id do
        addTag tags s!"open:scoped_invalid:{id}"
      let candidates := candidateOpenNamespaces currNs openDecls id
      for ns in candidates do
        checkForbiddenSpecNs "open_scoped" ns tags
        if env.isNamespace ns then
          env := Parser.parserExtension.activateScoped env ns
    return (env, openDecls)
  else
    addTag tags s!"open:unsupported:{k}"
    return (parserEnv, openDecls)

def validateSpecExport (currNs : Name) (openDecls : List OpenDecl)
    (args : Array Syntax) (tags : IO.Ref TagSet) : IO Unit := do
  unless args.size == 5 do addTag tags "export:shape"; return ()
  let nsId := args[1]!.getId
  unless isValidSourceIdent nsId && !hasUnsafeRecComponent nsId do
    addTag tags s!"export:invalid:{nsId}"
  let itemIds := args[3]!.getArgs.map Syntax.getId
  for itemId in itemIds do
    unless isValidSourceIdent itemId && !hasUnsafeRecComponent itemId &&
        !hasBangComponent itemId && !hasForbiddenSpecIdentComponent itemId do
      addTag tags s!"export:item:{itemId}"
  for ns in candidateOpenNamespaces currNs openDecls nsId do
    if ns == `System.Platform then
      if itemIds.isEmpty then addTag tags "export:System.Platform"
      for itemId in itemIds do
        let full := ns ++ itemId
        unless allowedSystemPlatformDecls.contains full do
          addTag tags s!"export:{full}"
    else
      checkForbiddenSpecNs "export" ns tags
      for itemId in itemIds do
        checkForbiddenSpecNs "export" (ns ++ itemId) tags

def pushSpecScopes (isNewNamespace : Bool) (header : Name)
    (parserEnv : Environment) (scopes : List ParseScope) (tags : IO.Ref TagSet) :
    IO (Environment × List ParseScope) := do
  match header with
  | .anonymous => return (parserEnv, scopes)
  | .str p seg =>
    let (parserEnv, scopes) ← pushSpecScopes isNewNamespace p parserEnv scopes tags
    let top := scopes.head!
    let newNs := if isNewNamespace then Name.mkStr top.currNamespace seg
      else top.currNamespace
    if isNewNamespace then checkForbiddenSpecDeclNs "enter" newNs tags
    let mut env := parserEnv.registerNamespace newNs
    env := Parser.parserExtension.pushScope env
    if isNewNamespace && parserEnv.isNamespace newNs then
      env := Parser.parserExtension.activateScoped env newNs
    return (env, { top with header := seg, currNamespace := newNs } :: scopes)
  | _ => addTag tags s!"scope:invalid:{header}"; return (parserEnv, scopes)

def checkSpecDeclNamespace (currNs : Name) (id : Name)
    (parserEnv : Environment) (tags : IO.Ref TagSet) : IO Environment := do
  if (`_root_).isPrefixOf id then
    addTag tags s!"decl_ns:{id}"
    return parserEnv
  let rec walkPrefix (ns : Name) (env : Environment) :
      IO (Name × Environment) := do
    match ns with
    | .anonymous => return (currNs, env)
    | .str p seg =>
      let (base, env) ← walkPrefix p env
      let full := Name.mkStr base seg
      checkForbiddenSpecDeclNs "declare_in" full tags
      return (full, env.registerNamespace full)
    | _ => addTag tags s!"decl_ns:{id}"; return (currNs, env)
  match id with
  | .str .anonymous seg =>
    checkForbiddenSpecDeclNs "declare" (Name.mkStr currNs seg) tags
    return parserEnv
  | .str pre _ =>
    let (_, env) ← walkPrefix pre parserEnv
    return env
  | _ => return parserEnv

def openActivatesScoped (openDecl : Syntax) : Bool :=
  openDecl.isOfKind ``Parser.Command.openSimple ||
    openDecl.isOfKind ``Parser.Command.openHiding ||
    openDecl.isOfKind ``Parser.Command.openScoped

def specCmdTag (k : Name) : String :=
  if k == ``Parser.Command.set_option then "set_option"
  else if k == `Lean.Parser.Command.eval then "command:#eval"
  else if k == `Lean.runElab then "run_elab"
  else if k == `Lean.runMeta then "run_meta"
  else if k == `Lean.Parser.Command.notation || k == `Lean.Parser.Command.mixfix ||
          k == `Lean.Parser.Command.prefix || k == `Lean.Parser.Command.postfix then
    "notation"
  else if k == `Lean.Parser.Command.macro || k == `Lean.Parser.Command.macro_rules then
    "macro"
  else if k == `Lean.Parser.Command.syntax ||
          k == `Lean.Parser.Command.declare_syntax_cat then
    "syntax"
  else if k == `Lean.Parser.Command.elab || k == `Lean.Parser.Command.elab_rules then
    "elab"
  else if k == `Lean.Parser.Command.runCmd then "run_cmd"
  else if k == `Lean.Parser.Command.initialize then "initialize"
  else s!"command:{k}"

def specTacTag (k : Name) : String :=
  if k == `Lean.Parser.Tactic.tacticSorry || k == `Lean.Parser.Tactic.tacticAdmit then
    "sorry"
  else if k == `Lean.Parser.Tactic.nativeDecide then "native_decide"
  else if k == `Lean.Parser.Tactic.bvDecide then "bv_decide"
  else s!"tactic:{k}"

partial def inspectSpecSyntax (commandLikeKinds tacticLikeKinds : NameSet)
    (parserEnv : Environment) (currNs : Name) (openDecls : List OpenDecl)
    (s : Syntax) (isModule : Bool) (tags : IO.Ref TagSet) : IO Unit := do
  match s with
  | .missing => addTag tags "missing_syntax"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do addTag tags s!"ident:{val}"
    if hasUnsafeRecComponent val then addTag tags s!"ident:{val}"
    let checkSpecIdent (cand : Name) : IO Unit := do
      if hasForbiddenSpecIdentComponent cand || hasBangComponent cand then
        addTag tags s!"ident:{val}"
      if forbiddenSpecIdentifiers.contains cand then
        addTag tags cand.toString
      if isForbiddenPureNamespace cand (banLeanRoot := true) then
        unless allowedSystemPlatformDecls.contains cand do
          addTag tags s!"ref:{cand}"
    checkSpecIdent val
    for cand in candidateOpenNamespaces currNs openDecls val do
      checkSpecIdent cand
  | .node _ k args =>
    if k != nullKind then
      if forbiddenSpecModifierKinds.contains k ||
          (!isModule && k == ``Parser.Command.public) then
        if k == ``Parser.Command.unsafe || k == ``Parser.Term.unsafe then addTag tags "unsafe"
        else if k == ``Parser.Command.partial then addTag tags "partial"
        else if k == ``Parser.Command.meta then addTag tags "meta"
        else if k == ``Parser.Command.public then addTag tags "nonmodule_public"
        else addTag tags s!"mod:{k}"
      if forbiddenSpecTermKinds.contains k ||
          supplementalSpecForbiddenTermKinds.contains k ||
          isQuotationKind k then
        if k == ``Parser.Term.sorry then addTag tags "sorry"
        else if k == ``Lean.byElab then addTag tags "by_elab"
        else if k == ``Lean.includeStr then addTag tags "includeStr"
        else addTag tags s!"syntax:{k}"
      if commandLikeKinds.contains k then
        unless allowedSpecCommandKinds.contains k do
          addTag tags (specCmdTag k)
      if tacticLikeKinds.contains k || (`Lean.Parser.Tactic).isPrefixOf k then
        unless allowedSpecTacticKinds.contains k do
          addTag tags (specTacTag k)
    if k == ``Parser.Command.sectionHeader then
      validateSpecSectionHeader args isModule tags
    else if k == ``Parser.Command.declModifiers then
      for child in args do
        unless child.isOfKind nullKind && child.getArgs.isEmpty do
          let ck := child.getKind
          if ck == nullKind then
            for inner in child.getArgs do
              unless isAllowedSpecDeclModifierKind isModule inner.getKind do
                addTag tags s!"decl_mod:{inner.getKind}"
              inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
                currNs openDecls inner isModule tags
          else
            unless isAllowedSpecDeclModifierKind isModule ck do
              addTag tags s!"decl_mod:{ck}"
            inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
              currNs openDecls child isModule tags
    else if k == ``Parser.Command.declaration then
      unless args.size == 2 && args[0]!.isOfKind ``Parser.Command.declModifiers do
        addTag tags "decl:shape"
      if args.size >= 2 then
        let declKind := args[1]!.getKind
        unless allowedSpecDeclarationKinds.contains declKind do
          if declKind == ``Parser.Command.axiom then addTag tags "axiom"
          else if declKind == ``Parser.Command.example then addTag tags "example"
          else if declKind == ``Parser.Command.opaque then addTag tags "opaque"
          else addTag tags s!"decl:{declKind}"
        if let some id := declarationIdent? s then
          if hasUnsafeRecComponent id then addTag tags s!"decl:{id}"
          discard <| checkSpecDeclNamespace currNs id parserEnv tags
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule tags
    else if k == ``Parser.Command.mutual then
      if args.size == 3 then
        unless args[1]!.getArgs.all (isAllowedSpecNestedCommand ·.getKind) do
          addTag tags "mutual:command"
        let mut mutEnv := parserEnv
        let mut mutOpen := openDecls
        let mut mutCmds := commandLikeKinds
        let mut mutTacs := tacticLikeKinds
        for child in args[1]!.getArgs do
          inspectSpecSyntax mutCmds mutTacs mutEnv currNs mutOpen child isModule tags
          if child.isOfKind ``Parser.Command.open then
            let (nextEnv, nextOpen) ←
              validateSpecOpenDecl currNs mutOpen mutEnv child[1] tags
            mutEnv := nextEnv
            mutOpen := nextOpen
            if openActivatesScoped child[1] then
              let (nc, nt) ← collectSpecParserSets mutEnv
              mutCmds := nc
              mutTacs := nt
      else
        addTag tags "mutual:shape"
    else if k == ``Parser.Command.in then
      if args.size == 3 then
        unless allowedSpecInLhsKinds.contains args[0]!.getKind do
          addTag tags s!"in_lhs:{args[0]!.getKind}"
        unless isAllowedSpecNestedCommand args[2]!.getKind do
          addTag tags s!"in_rhs:{args[2]!.getKind}"
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls args[0]! isModule tags
        let (tmpEnv, tmpOpen) ←
          if args[0]!.isOfKind ``Parser.Command.open then
            validateSpecOpenDecl currNs openDecls parserEnv args[0]![1] tags
          else
            pure (parserEnv, openDecls)
        let (tmpCmds, tmpTacs) ←
          if args[0]!.isOfKind ``Parser.Command.open &&
              openActivatesScoped args[0]![1] then
            collectSpecParserSets tmpEnv
          else
            pure (commandLikeKinds, tacticLikeKinds)
        inspectSpecSyntax tmpCmds tmpTacs tmpEnv currNs tmpOpen args[2]! isModule tags
      else
        addTag tags "in:shape"
    else if k == ``Parser.Command.open then
      if args.size == 2 then
        discard <| validateSpecOpenDecl currNs openDecls parserEnv args[1]! tags
      else
        addTag tags "open:shape"
    else if k == ``Parser.Term.open then
      if args.size == 4 then
        let (tmpEnv, tmpOpen) ←
          validateSpecOpenDecl currNs openDecls parserEnv args[1]! tags
        let (tmpCmds, tmpTacs) ←
          if openActivatesScoped args[1]! then
            collectSpecParserSets tmpEnv
          else
            pure (commandLikeKinds, tacticLikeKinds)
        inspectSpecSyntax tmpCmds tmpTacs tmpEnv currNs tmpOpen args[3]! isModule tags
      else
        addTag tags "term_open:shape"
    else if k == ``Parser.Command.export then
      validateSpecExport currNs openDecls args tags
    else if k == ``Parser.Term.attrInstance then
      validateSpecAttrInstance args isModule tags
    else if k == ``Parser.Command.eraseAttr then
      let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
      unless allowedSpecEraseAttrs.contains attrName do
        addTag tags s!"erase_attr:{attrName}"
    else if k == ``Parser.Command.deriving then
      unless args.size == 6 && args[1]!.isOfKind nullKind &&
          args[1]!.getArgs.isEmpty do
        addTag tags "deriving:modifier"
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule tags
    else if k == ``Parser.Command.derivingClass then
      unless args.size == 2 && args[0]!.isOfKind nullKind &&
          args[0]!.getArgs.isEmpty do
        addTag tags "deriving:modifier"
      if args.size >= 2 then
        let cls := args[1]!.getId
        unless allowedSpecDerivingClasses.contains cls do
          addTag tags s!"deriving:{cls}"
    else if k == ``Parser.Command.set_option then
      validateSpecSetOption args tags
    else if k == ``Parser.Term.set_option then
      validateSpecSetOption args tags
      if args.size >= 6 then
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls args[5]! isModule tags
    else if k == `Lean.Parser.Tactic.decide then
      validateSpecDecideTactic args tags
    else
      for child in args do
        inspectSpecSyntax commandLikeKinds tacticLikeKinds parserEnv
          currNs openDecls child isModule tags

partial def applySpecScope (parserEnv : Environment)
    (scopes : List ParseScope) (stx : Syntax) (tags : IO.Ref TagSet) :
    IO (Environment × List ParseScope) := do
  let k := stx.getKind
  if k == ``Parser.Command.namespace then
    pushSpecScopes true stx[1].getId parserEnv scopes tags
  else if k == ``Parser.Command.section then
    if stx[2].isNone then
      let top := scopes.head!
      let parserEnv := Parser.parserExtension.pushScope parserEnv
      return (parserEnv, { top with header := "" } :: scopes)
    else
      pushSpecScopes false stx[2][0].getId parserEnv scopes tags
  else if k == ``Parser.Command.end then
    let header? := if stx[1].isNone then none else some stx[1][0].getId
    let endSize := match header? with | none => 1 | some n => n.getNumParts
    if scopes.length <= 1 || endSize >= scopes.length then
      return (parserEnv, scopes)
    let mut env := parserEnv
    for _ in [:endSize] do
      env := Parser.parserExtension.popScope env
    return (env, scopes.drop endSize)
  else if k == ``Parser.Command.open then
    let top := scopes.head!
    let (nextEnv, nextOpen) ←
      validateSpecOpenDecl top.currNamespace top.openDecls parserEnv stx[1] tags
    return (nextEnv, { top with openDecls := nextOpen } :: scopes.tail!)
  else if k == ``Parser.Command.in then
    let top := scopes.head!
    let tmpEnv := Parser.parserExtension.pushScope parserEnv
    let (tmpEnv, tmpScopes) ← applySpecScope tmpEnv (top :: scopes) stx[0] tags
    let (tmpEnv, _) ← applySpecScope tmpEnv tmpScopes stx[2] tags
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.mutual then
    let top := scopes.head!
    let mut tmpEnv := Parser.parserExtension.pushScope parserEnv
    let mut tmpScopes := top :: scopes
    for child in stx[1].getArgs do
      (tmpEnv, tmpScopes) ← applySpecScope tmpEnv tmpScopes child tags
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let env ← checkSpecDeclNamespace scopes.head!.currNamespace id parserEnv tags
      return (env, scopes)
    | none => return (parserEnv, scopes)
  else
    return (parserEnv, scopes)

def isAllowedTheoryNestedCommand (k : SyntaxNodeKind) : Bool :=
  allowedTheoryCommandKinds.contains k &&
    ![``Parser.Command.namespace, ``Parser.Command.section,
      ``Parser.Command.end, ``Parser.Command.mutual].contains k

def validateTheorySectionHeader (args : Array Syntax) (tags : IO.Ref TagSet) :
    IO Unit := do
  for child in args do
    let ok := child.isOfKind nullKind &&
      (child.getArgs.isEmpty ||
        (child.getArgs.size == 1 &&
          match child.getArgs[0]! with | .atom _ "public" => true | _ => false) ||
        (child.getArgs.size == 3 &&
          match child.getArgs[0]!, child.getArgs[1]!, child.getArgs[2]! with
          | .atom _ "@[", .atom _ "expose", .atom _ "]" => true
          | _, _, _ => false))
    unless ok do addTag tags "section_header:unsupported"

def inspectTheoryNodeKind (k : SyntaxNodeKind) (args : Array Syntax)
    (requirePrelude : Bool) (tags : IO.Ref TagSet) : IO Unit := do
  if k == ``Parser.Module.header then
    if requirePrelude then
      unless !(args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
        addTag tags "missing_prelude"
  else if k == ``Parser.Command.sectionHeader then
    validateTheorySectionHeader args tags
  else if k == ``Parser.Command.declaration then
    let declKind := args[1]?.map Syntax.getKind |>.getD .anonymous
    if declKind == ``Parser.Command.opaque then
      addTag tags "opaque"
    unless allowedTheoryDeclarationKinds.contains declKind do
      if declKind == ``Parser.Command.axiom then addTag tags "axiom"
      else if declKind == ``Parser.Command.example then addTag tags "example"
      else addTag tags s!"decl:{declKind}"
  else if k == ``Parser.Command.mutual then
    unless args.size == 3 &&
        args[1]!.getArgs.all (isAllowedTheoryNestedCommand ·.getKind) do
      addTag tags "mutual:unsupported"
  else if k == ``Parser.Command.in then
    unless args.size == 3 do addTag tags "in:shape"; return ()
    unless [``Parser.Command.open, ``Parser.Command.variable].contains
        args[0]!.getKind do
      addTag tags s!"in_lhs:{args[0]!.getKind}"
    unless isAllowedTheoryNestedCommand args[2]!.getKind do
      addTag tags s!"in_rhs:{args[2]!.getKind}"
  else if k == ``Parser.Attr.simple then
    let attrName := args[0]?.map Syntax.getId |>.getD .anonymous
    unless allowedTheoryAttributeNames.contains attrName do
      addTag tags s!"@[{attrName}]"
    unless (args[1]?.map Syntax.getArgs |>.getD #[]).isEmpty do
      addTag tags s!"@[{attrName}:args]"
  else if k == ``Parser.Attr.instance || k == `Lean.Parser.Attr.simp then
    unless (args.extract 1 args.size).all (·.getArgs.isEmpty) do
      addTag tags s!"@[{k}:args]"
  else if k == ``Parser.Command.eraseAttr then
    let attrName := args[1]?.map Syntax.getId |>.getD .anonymous
    unless allowedTheoryAttributeNames.contains attrName do
      addTag tags s!"erase_attr:{attrName}"

def extendTheoryOpenDeclsForOpenCmd (currNs : Name) (openDecls : List OpenDecl)
    (openStx : Syntax) : List OpenDecl :=
  if !openStx.isOfKind ``Parser.Command.open then openDecls
  else
    let openDecl := openStx[1]
    if !openDecl.isOfKind ``Parser.Command.openSimple then openDecls
    else
      openDecl[0].getArgs.foldl (init := openDecls) fun ods idStx =>
        let id := idStx.getId
        let hasOpenDecl (ns : Name) : Bool :=
          ods.any fun | OpenDecl.simple existing _ => existing == ns | _ => false
        let cands := candidateOpenNamespaces currNs ods id
        let ods' := cands.foldl (init := ods) fun acc ns =>
          if hasOpenDecl ns then acc else OpenDecl.simple ns [] :: acc
        let stripped := id.replacePrefix rootNamespace .anonymous
        if hasOpenDecl stripped then ods' else OpenDecl.simple stripped [] :: ods'

partial def inspectTheorySyntax (allowedKinds : NameSet) (s : Syntax)
    (requirePrelude : Bool) (currNs : Name) (openDecls : List OpenDecl)
    (checkPureRefs : Bool) (tags : IO.Ref TagSet)
    (allowLocalSemireducible : Bool := false) : IO Unit := do
  match s with
  | .missing => addTag tags "missing_syntax"
  | .atom _ _ => pure ()
  | .ident _ _ val _ =>
    unless isValidSourceIdent val do addTag tags s!"ident:{val}"
    if checkPureRefs then
      let checkPureIdent (cand : Name) : IO Unit := do
        let u := cand.replacePrefix rootNamespace .anonymous
        if forbiddenPureIdentifiers.contains cand ||
            supplementalTheoryForbiddenIdentifiers.contains cand ||
            isForbiddenPureNamespace cand ||
            supplementalTheoryForbiddenPrefixes.any
              (fun pre => u == pre || pre.isPrefixOf u) then
          addTag tags s!"ref:{val}"
      checkPureIdent val
      for cand in candidateOpenNamespaces currNs openDecls val do
        checkPureIdent cand
  | .node _ k args =>
    if allowLocalSemireducible && k == ``Parser.Command.in then
      if let some (_, decl) := matchLocalSemireducibleIn? args then
        inspectTheorySyntax allowedKinds decl requirePrelude currNs openDecls
          checkPureRefs tags
        return
    if forbiddenPureTermKinds.contains k then
      addTag tags s!"syntax:{k}"
    unless k == nullKind || allowedKinds.contains k do
      if k == `Lean.Parser.Command.eval then addTag tags "command:#eval"
      else if k == `Lean.runElab then addTag tags "run_elab"
      else if k == `Lean.runMeta then addTag tags "run_meta"
      else if k == `Lean.Parser.Command.set_option || k == ``Parser.Command.set_option then
        addTag tags "set_option"
      else if k == `Lean.Parser.Tactic.tacticSorry || k == `Lean.Parser.Tactic.tacticAdmit ||
              k == ``Parser.Term.sorry then
        addTag tags "sorry"
      else if k == `Lean.Parser.Tactic.nativeDecide then addTag tags "native_decide"
      else if k == `Lean.Parser.Tactic.bvDecide then addTag tags "bv_decide"
      else addTag tags s!"syntax:{k}"
    inspectTheoryNodeKind k args requirePrelude tags
    if k == ``Parser.Command.in && checkPureRefs && args.size >= 3 then
      inspectTheorySyntax allowedKinds args[0]! requirePrelude currNs openDecls
        checkPureRefs tags
      inspectTheorySyntax allowedKinds args[1]! requirePrelude currNs openDecls
        checkPureRefs tags
      let nextOpen := extendTheoryOpenDeclsForOpenCmd currNs openDecls args[0]!
      inspectTheorySyntax allowedKinds args[2]! requirePrelude currNs nextOpen
        checkPureRefs tags
    else if k == ``Parser.Command.mutual && checkPureRefs && args.size >= 3 then
      inspectTheorySyntax allowedKinds args[0]! requirePrelude currNs openDecls
        checkPureRefs tags
      let mut mutOpen := openDecls
      for child in args[1]!.getArgs do
        inspectTheorySyntax allowedKinds child requirePrelude currNs mutOpen
          checkPureRefs tags
        mutOpen := extendTheoryOpenDeclsForOpenCmd currNs mutOpen child
      inspectTheorySyntax allowedKinds args[2]! requirePrelude currNs openDecls
        checkPureRefs tags
    else
      for child in args do
        inspectTheorySyntax allowedKinds child requirePrelude currNs openDecls
          checkPureRefs tags

def collectScopedExtensionNamespaces (env : Environment) : IO NameSet := do
  let exts ← scopedEnvExtensionsRef.get
  let mut acc : NameSet := {}
  for ext in exts do
    for (ns, _) in (ext.ext.getState env).scopedEntries.map do
      acc := acc.insert ns
  return acc

def collectScopedNamespacePrefixes (scopedNamespaces : NameSet) : NameSet :=
  let rec insertPrefixes (acc : NameSet) : Name → NameSet
    | .anonymous => acc
    | ns@(.str p _) => insertPrefixes (acc.insert ns) p
    | _ => acc
  scopedNamespaces.foldl (init := {}) fun acc ns =>
    match ns with
    | .str p _ => insertPrefixes acc p
    | _ => acc

def checkScopedNs (scopedNamespaces : NameSet) (how : String) (ns : Name)
    (tags : IO.Ref TagSet) : IO Unit := do
  if scopedNamespaces.contains ns then addTag tags s!"scoped_ns:{how}:{ns}"
  if isForbiddenPureNamespace ns then addTag tags s!"{how}:{ns}"

def checkTheoryDeclNs (ns : Name) (tags : IO.Ref TagSet) : IO Unit := do
  let u := ns.replacePrefix rootNamespace .anonymous
  if supplementalTheoryDeclRootNamespaces.contains u.getRoot ||
      theoryKernelAcceleratedNames.contains u then
    addTag tags s!"decl_ns:{ns}"

def pushTheoryParseScopes (scopedNamespaces : NameSet) (isNewNamespace : Bool)
    (header : Name) (parserEnv : Environment) (scopes : List ParseScope)
    (tags : IO.Ref TagSet) : IO (Environment × List ParseScope) := do
  match header with
  | .anonymous => return (parserEnv, scopes)
  | .str p seg =>
    let (parserEnv, scopes) ←
      pushTheoryParseScopes scopedNamespaces isNewNamespace p parserEnv scopes tags
    let top := scopes.head!
    let newNs := if isNewNamespace then Name.mkStr top.currNamespace seg
      else top.currNamespace
    if isNewNamespace then
      checkScopedNs scopedNamespaces "enter" newNs tags
      checkTheoryDeclNs newNs tags
    let parserEnv := parserEnv.registerNamespace newNs
    let parserEnv := Parser.parserExtension.pushScope parserEnv
    return (parserEnv, { top with header := seg, currNamespace := newNs } :: scopes)
  | _ => addTag tags s!"scope:invalid:{header}"; return (parserEnv, scopes)

def checkTheoryDeclNamespacePrefixes (scopedNamespaces : NameSet) (currNs : Name)
    (id : Name) (parserEnv : Environment) (tags : IO.Ref TagSet) :
    IO Environment := do
  let hasRoot := (`_root_).isPrefixOf id
  let effBase := if hasRoot then .anonymous else currNs
  let effId := if hasRoot then id.replacePrefix rootNamespace .anonymous else id
  let rec walkPrefix (ns : Name) (env : Environment) : IO (Name × Environment) := do
    match ns with
    | .anonymous => return (effBase, env)
    | .str p seg =>
      let (base, env) ← walkPrefix p env
      let full := Name.mkStr base seg
      checkScopedNs scopedNamespaces "declare_in" full tags
      checkTheoryDeclNs full tags
      return (full, env.registerNamespace full)
    | _ => addTag tags s!"decl_ns:{id}"; return (effBase, env)
  match effId with
  | .str .anonymous seg =>
    checkTheoryDeclNs (Name.mkStr effBase seg) tags
    return parserEnv
  | .str pre seg =>
    let (baseNs, env) ← walkPrefix pre parserEnv
    checkTheoryDeclNs (Name.mkStr baseNs seg) tags
    return env
  | _ =>
    addTag tags s!"decl_ns:{id}"
    return parserEnv

partial def applyTheoryCommandScope (scopedNamespaces scopedPrefixes : NameSet)
    (parserEnv : Environment) (scopes : List ParseScope) (stx : Syntax)
    (tags : IO.Ref TagSet) : IO (Environment × List ParseScope) := do
  let k := stx.getKind
  if k == ``Parser.Command.namespace then
    pushTheoryParseScopes scopedNamespaces true stx[1].getId parserEnv scopes tags
  else if k == ``Parser.Command.section then
    if stx[2].isNone then
      let top := scopes.head!
      let parserEnv := Parser.parserExtension.pushScope parserEnv
      return (parserEnv, { top with header := "" } :: scopes)
    else
      pushTheoryParseScopes scopedNamespaces false stx[2][0].getId parserEnv scopes tags
  else if k == ``Parser.Command.end then
    let header? := if stx[1].isNone then none else some stx[1][0].getId
    let endSize := match header? with | none => 1 | some n => n.getNumParts
    if scopes.length <= 1 || endSize >= scopes.length then
      return (parserEnv, scopes)
    let mut env := parserEnv
    for _ in [:endSize] do
      env := Parser.parserExtension.popScope env
    return (env, scopes.drop endSize)
  else if k == ``Parser.Command.open then
    let top := scopes.head!
    let mut openDecls := top.openDecls
    let openDecl := stx[1]
    unless openDecl.isOfKind ``Parser.Command.openSimple do
      addTag tags s!"open:{openDecl.getKind}"
      return (parserEnv, scopes)
    let hasOpenDecl (ods : List OpenDecl) (ns : Name) : Bool :=
      ods.any fun | OpenDecl.simple existing _ => existing == ns | _ => false
    for idStx in openDecl[0].getArgs do
      let id := idStx.getId
      let candidates := candidateOpenNamespaces top.currNamespace openDecls id
      let mut added := false
      for ns in candidates do
        checkScopedNs scopedNamespaces "open" ns tags
        if parserEnv.isNamespace ns || scopedPrefixes.contains ns then
          if !hasOpenDecl openDecls ns then
            openDecls := OpenDecl.simple ns [] :: openDecls
          added := true
      if !added then
        let stripped := id.replacePrefix rootNamespace .anonymous
        checkScopedNs scopedNamespaces "open" stripped tags
        if !hasOpenDecl openDecls stripped then
          openDecls := OpenDecl.simple stripped [] :: openDecls
    return (parserEnv, { top with openDecls := openDecls } :: scopes.tail!)
  else if k == ``Parser.Command.in then
    if let some (_, decl) := matchLocalSemireducibleIn? stx.getArgs then
      applyTheoryCommandScope scopedNamespaces scopedPrefixes
        parserEnv scopes decl tags
    else
      let top := scopes.head!
      let tmpEnv := Parser.parserExtension.pushScope parserEnv
      let (tmpEnv, tmpScopes) ←
        applyTheoryCommandScope scopedNamespaces scopedPrefixes
          tmpEnv (top :: scopes) stx[0] tags
      let (tmpEnv, _) ←
        applyTheoryCommandScope scopedNamespaces scopedPrefixes
          tmpEnv tmpScopes stx[2] tags
      return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.mutual then
    let top := scopes.head!
    let mut tmpEnv := Parser.parserExtension.pushScope parserEnv
    let mut tmpScopes := top :: scopes
    for child in stx[1].getArgs do
      (tmpEnv, tmpScopes) ←
        applyTheoryCommandScope scopedNamespaces scopedPrefixes tmpEnv tmpScopes child tags
    return (Parser.parserExtension.popScope tmpEnv, scopes)
  else if k == ``Parser.Command.declaration then
    match declarationIdent? stx with
    | some id =>
      let env ← checkTheoryDeclNamespacePrefixes scopedNamespaces
        scopes.head!.currNamespace id parserEnv tags
      return (env, scopes)
    | none => return (parserEnv, scopes)
  else
    return (parserEnv, scopes)

structure ParsedUnit where
  modName : Name
  pathStr : String
  ctx : Parser.InputContext
  state0 : Parser.ModuleParserState
  msgs0 : MessageLog
  isModule : Bool
  imports : Array Import

def inspectOneHeader (isSpec allowImportAll : Bool)
    (allowedFnd allowedLocal : NameSet)
    (modName : Name) (pathStr : String) (tags parseErrs : IO.Ref TagSet) :
    IO (Option ParsedUnit) := do
  let text ← IO.FS.readFile pathStr
  unless isSpec do
    let directives := (text.splitOn "\n").filterMap fun rawLine =>
      (rawLine.trimAscii.toString.dropPrefix? "-- anneal-trust-tier:").map
        (·.trimAscii.toString)
    unless directives.isEmpty do
      addTag tags "trust_tier_directive"
  let ctx := Parser.mkInputContext text pathStr
  let (header, state0, msgs0) ← Parser.parseHeader ctx
  if msgs0.hasErrors || state0.recovering then
    addParseErr parseErrs "header_parse_error"
    return none
  let isModule := Elab.HeaderSyntax.isModule header
  let imports := Elab.HeaderSyntax.imports header
  if isSpec then
    inspectHeaderSyntax header.raw false tags
    let hasNonMetaInit := imports.any fun i => i.module == `Init && !i.isMeta
    for imp in imports do
      if imp.importAll then addTag tags "import_all"
      if !imp.isExported && !isModule then addTag tags "private_import"
      if imp.isMeta && !(imp.module == `Init && hasNonMetaInit) then
        addTag tags "meta_import"
      if isForbiddenPureImport imp.module then
        let r := imp.module.getRoot
        if r == `Lean then addTag tags "Lean_import"
        else if r == `Lake then addTag tags "Lake_import"
        else if imp.module == `Init.System || (`Init.System).isPrefixOf imp.module then
          addTag tags "Init_System_import"
        else addTag tags "UV_import"
      if let some extraTag := isSupplementalForbiddenImport imp.module then
        addTag tags extraTag
  else
    inspectTheorySyntax allowedTheorySyntaxKinds header.raw true .anonymous [] false tags
    for imp in imports do
      if imp.isMeta then addTag tags "meta_import"
      if !imp.isExported && !isModule then addTag tags "private_import"
      if imp.importAll then
        let okAll := allowImportAll && isModule &&
          imp.module == `Init.Data.Nat.Bitwise.Basic
        unless okAll do addTag tags "import_all"
      if isForbiddenPureImport imp.module then
        let r := imp.module.getRoot
        if r == `Lean then addTag tags "Lean_import"
        else if r == `Lake then addTag tags "Lake_import"
        else if imp.module == `Init.System || (`Init.System).isPrefixOf imp.module then
          addTag tags "Init_System_import"
        else addTag tags "UV_import"
      if let some extraTag := isSupplementalForbiddenImport imp.module then
        addTag tags extraTag
      unless allowedFnd.contains imp.module || allowedLocal.contains imp.module do
        addTag tags s!"disallowed_import:{imp.module}"
  return some {
    modName := modName
    pathStr := pathStr
    ctx := ctx
    state0 := state0
    msgs0 := msgs0
    isModule := isModule
    imports := imports
  }

def inspectOneCommands (env : Environment) (cmdKinds tacKinds : NameSet)
    (scopedNamespaces scopedPrefixes : NameSet) (isSpec : Bool)
    (ctx : Parser.InputContext) (state0 : Parser.ModuleParserState)
    (msgs0 : MessageLog) (isModule : Bool)
    (tags parseErrs : IO.Ref TagSet) : IO Unit := do
  let rootScope : ParseScope :=
    { header := "", currNamespace := .anonymous, openDecls := [] }
  let mut state := state0
  let mut msgs := msgs0
  let mut pEnv := env
  let mut scopes : List ParseScope := [rootScope]
  let mut ck := cmdKinds
  let mut tk := tacKinds
  while true do
    let top := scopes.head!
    let pmctx : Parser.ParserModuleContext := {
      env := pEnv
      options := {}
      currNamespace := top.currNamespace
      openDecls := top.openDecls
    }
    let (stx, ns, nm) := Parser.parseCommand ctx pmctx state msgs
    if nm.hasErrors || ns.recovering then
      addParseErr parseErrs "parse_error"
      break
    if stx.isOfKind ``Parser.Command.eoi then
      break
    if ns.pos <= state.pos then
      addParseErr parseErrs "parse_stall"
      break
    if isSpec then
      unless allowedSpecCommandKinds.contains stx.getKind do
        addTag tags (specCmdTag stx.getKind)
      inspectSpecSyntax ck tk pEnv top.currNamespace top.openDecls stx isModule tags
      let (nextEnv, nextScopes) ← applySpecScope pEnv scopes stx tags
      pEnv := nextEnv
      scopes := nextScopes
      if stx.isOfKind ``Parser.Command.namespace ||
          stx.isOfKind ``Parser.Command.end ||
          (stx.isOfKind ``Parser.Command.open && openActivatesScoped stx[1]) then
        let (nc, nt) ← collectSpecParserSets pEnv
        ck := nc
        tk := nt
    else
      unless allowedTheoryCommandKinds.contains stx.getKind do
        addTag tags (specCmdTag stx.getKind)
      if declaresLocalSemireducibleShadow top.currNamespace stx then
        addTag tags "decl_shadow:local_semireducible"
      inspectTheorySyntax allowedTheorySyntaxKinds stx true top.currNamespace
        top.openDecls true tags (allowLocalSemireducible := true)
      let (nextEnv, nextScopes) ←
        applyTheoryCommandScope scopedNamespaces scopedPrefixes pEnv scopes stx tags
      pEnv := nextEnv
      scopes := nextScopes
    state := ns
    msgs := nm

def parseEdgeMap (pairs : Array (String × Array String)) : NameMap (Array Name) :=
  pairs.foldl (init := {}) fun acc (mStr, deps) =>
    acc.insert mStr.toName (deps.map String.toName)

def resolveImportRoots (isSpec : Bool)
    (fndGraph locGraph entryGraph : NameMap (Array Name))
    (startImports : Array Import) : IO (Array Name) := do
  let mut queue : List Name := (startImports.map (·.module)).toList
  let mut visited : NameSet := {}
  let mut roots : NameSet := {}
  while !queue.isEmpty do
    match queue with
    | [] => pure ()
    | curr :: rest =>
      queue := rest
      if visited.contains curr then
        continue
      visited := visited.insert curr
      if let some deps := entryGraph.find? curr then
        for d in deps do
          unless visited.contains d do queue := d :: queue
      else if let some deps := locGraph.find? curr then
        for d in deps do
          unless visited.contains d do queue := d :: queue
      else if let some deps := fndGraph.find? curr then
        roots := roots.insert curr
        for d in deps do
          unless visited.contains d do queue := d :: queue
      else if isSpec && !isForbiddenPureImport curr then
        let hasOlean ← try
          discard <| findOLean curr
          pure true
        catch _ =>
          pure false
        if hasOlean then
          roots := roots.insert curr
  let arr := roots.foldl (init := #[]) (·.push ·)
  return arr.qsort (·.toString < ·.toString)

def inspectMain (args : List String) : IO Unit := do
  let reqRaw ← IO.FS.readFile args[0]!
  let req ← IO.ofExcept <| Json.parse reqRaw
  let sysrootStr ← IO.ofExcept <| req.getObjValAs? String "sysroot"
  let modeStr ← IO.ofExcept <| req.getObjValAs? String "mode"
  let isSpec := modeStr == "spec"
  let singleGroupOnly : Bool :=
    (req.getObjValAs? Bool "singleGroupOnly").toOption.getD false
  let targetGroup? : Option String :=
    (req.getObjValAs? String "targetGroup").toOption
  let _fndMods ←
    IO.ofExcept <| req.getObjValAs? (Array String) "foundationModules"
  let fndPairs ← IO.ofExcept <|
    req.getObjValAs? (Array (String × Array String)) "foundationGraph"
  let locPairs ← IO.ofExcept <|
    req.getObjValAs? (Array (String × Array String)) "localGraph"
  let entries ← IO.ofExcept <| req.getObjValAs? (Array Json) "files"
  searchPathRef.set (← getBuiltinSearchPath sysrootStr)
  let fndGraph := parseEdgeMap fndPairs
  let locGraph := parseEdgeMap locPairs
  let allowedFnd : NameSet := .ofList (_fndMods.toList.map String.toName)
  let mut allowedLocal : NameSet := {}
  for (locMod, _) in locPairs do
    allowedLocal := allowedLocal.insert locMod.toName
  for item in entries do
    let modStr ← IO.ofExcept <| item.getObjValAs? String "module"
    allowedLocal := allowedLocal.insert modStr.toName
  let tags ← IO.mkRef ({} : TagSet)
  let parseErrs ← IO.mkRef ({} : TagSet)
  let mut parsed := #[]
  let mut entryGraph : NameMap (Array Name) := {}
  for item in entries do
    let modStr ← IO.ofExcept <| item.getObjValAs? String "module"
    let pathStr ← IO.ofExcept <| item.getObjValAs? String "path"
    let allowAll ← IO.ofExcept <| item.getObjValAs? Bool "allowAll"
    if let some info ← inspectOneHeader isSpec allowAll allowedFnd allowedLocal
        modStr.toName pathStr tags parseErrs then
      entryGraph := entryGraph.insert info.modName (info.imports.map (·.module))
      parsed := parsed.push info
  let mut groupRoots : Std.HashMap String (Array Name) := {}
  let mut groups : Std.HashMap String (Array ParsedUnit) := {}
  for info in parsed do
    let roots ←
      resolveImportRoots isSpec fndGraph locGraph entryGraph info.imports
    let key := (Json.arr (roots.map toJson)).compress
    groupRoots := groupRoots.insert key roots
    groups := groups.insert key ((groups.getD key #[]).push info)
  let sortedKeys := (groups.toList.map (·.1)).toArray.qsort (· < ·)
  let mut remainingGroups : Array String := #[]
  let runKeys : Array String ← match targetGroup? with
    | some tk =>
      if groups.contains tk then
        pure #[tk]
      else
        throw <| IO.userError s!"missing targetGroup: {tk}"
    | none =>
      if singleGroupOnly && sortedKeys.size > 1 then
        remainingGroups := sortedKeys.extract 1 sortedKeys.size
        pure #[sortedKeys[0]!]
      else
        pure sortedKeys
  for key in runKeys do
    let items := groups.getD key #[]
    let roots := groupRoots.getD key #[]
    let impArgs := roots.map fun m => { module := m : Import }
    unsafe enableInitializersExecution
    let env ← importModules impArgs {} (trustLevel := 0) (plugins := #[])
      (loadExts := true) (level := .private)
    let (ck, tk) ← collectSpecParserSets env
    let (scopedNs, scopedPrefixes) ← if isSpec then
      pure ({}, {})
    else
      let ns ← collectScopedExtensionNamespaces env
      pure (ns, collectScopedNamespacePrefixes ns)
    for item in items do
      inspectOneCommands env ck tk scopedNs scopedPrefixes isSpec item.ctx
        item.state0 item.msgs0 item.isModule tags parseErrs
  let outTags := (← tags.get).items
  let outErrs := (← parseErrs.get).items
  IO.println <| Json.mkObj [
    ("tags", Json.arr (outTags.map toJson)),
    ("parseErrors", Json.arr (outErrs.map toJson)),
    ("remainingGroups", Json.arr (remainingGroups.map toJson))
  ] |>.compress

def main (args : List String) : IO Unit :=
  inspectMain args
"""


# Defender-owned Tier-E1 kernel claim-binding & namespace verification
# script. Loads compiled `.olean`s at `trustLevel := 0, loadExts := false`
# (never running attacker `[init]`/`elab` code) and checks exact module
# provenance, reserved namespaces, duplicate constants, and `Kernel.isDefEq`.
_LEAN_E1_BINDING_SCRIPT = r"""
import Lean.Elab.Import
import Lean.Meta.Match.MatcherInfo
import Lean.Meta.Match.MatchEqs
import Lean.Meta.Constructions.SparseCasesOn
import Lean.Meta.Constructions.SparseCasesOnEq
import Lean.Meta.Tactic.FunInd
import Lean.Meta.CongrTheorems

open Lean

def reservedAttackerRoots : List Name := [
  `IncorrectnessCheck, `IncorrectnessExpected, `Spec, `Captured,
  `Expected, `Trusted, `Anneal, `Init, `Std, `Lean, `Lake,
  `TrustedBoundary, `SpecPreflight]

def hasCompoundName : Name → Bool
  | .str .anonymous _ | .num .anonymous _ | .anonymous => false
  | _ => true

def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    a.name == b.name && a.type == b.type &&
    a.levelParams == b.levelParams && ta.all == tb.all
  | _, _ => false

def collectAllMatchers (env : Environment) : NameSet := Id.run do
  let mut matchers : NameSet := {}
  for modIdx in Array.range env.header.moduleData.size do
    for entry in
        Lean.Meta.Match.Extension.extension.getModuleEntries env modIdx do
      matchers := matchers.insert entry.name
  return matchers

partial def isUpstreamHelperRoot (env : Environment) (allMatchers : NameSet)
    (isOrigin : Name → Bool) (n userN : Name) : Bool :=
  if hasCompoundName userN && isOrigin userN then
    true
  else
    match n, userN with
    | .str rawParent _, .str userParent "splitter" =>
      (allMatchers.contains rawParent || allMatchers.contains userParent) &&
        isUpstreamHelperRoot env allMatchers isOrigin rawParent userParent
    | .str rawParent _, .str userParent _ =>
      let isKnownSparse :=
        (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome
      let isKnownMatcher := allMatchers.contains n || allMatchers.contains userN
      if isKnownSparse || isKnownMatcher then
        isUpstreamHelperRoot env allMatchers isOrigin rawParent userParent
      else
        false
    | _, _ => false

def isRealizedOrCompilerHelper (env : Environment) (allMatchers : NameSet)
    (isOrigin : Name → Bool) (ci : ConstantInfo) : Bool :=
  let n := ci.name
  let userN := privateToUserName n
  let hasParent := isUpstreamHelperRoot env allMatchers isOrigin
  match ci, n, userN with
  | .thmInfo _, .str rawParent _, .str userParent suffix =>
    ((Lean.isReservedName env n || Lean.isReservedName env userN) &&
      hasParent rawParent userParent) ||
    ((allMatchers.contains rawParent || allMatchers.contains userParent) &&
      (suffix == "splitter" || Lean.Meta.isEqnReservedNameSuffix suffix ||
        Lean.Meta.Match.isCongrEqnReservedNameSuffix suffix) &&
      hasParent rawParent userParent)
  | .defnInfo _, .str rawParent _, .str userParent suffix =>
    isPrivateName n &&
      if suffix == "splitter" then
        (allMatchers.contains rawParent || allMatchers.contains userParent) &&
          hasParent rawParent userParent
      else if (Lean.Meta.getSparseCasesOnInfoCore env n).isSome ||
          (Lean.Meta.getSparseCasesOnInfoCore env userN).isSome then
        hasParent rawParent userParent
      else
        false
  | _, _, _ => false

def failJson (msg : String) : IO UInt32 := do
  IO.println <| Json.mkObj [("ok", toJson false), ("message", toJson msg)] |>.compress
  return 1

def main (args : List String) : IO UInt32 := do
  let reqRaw ← IO.FS.readFile args[0]!
  let req ← IO.ofExcept <| Json.parse reqRaw
  let sysrootStr ← IO.ofExcept <| req.getObjValAs? String "sysroot"
  let artsArr ← IO.ofExcept <|
    req.getObjValAs? (Array (String × Array (Array String))) "artifacts"
  let modNames ← IO.ofExcept <| req.getObjValAs? (Array String) "modules"
  let attackerMods ← IO.ofExcept <|
    req.getObjValAs? (Array String) "attackerModules"
  let requireS2Claim :=
    (req.getObjValAs? Bool "requireS2Claim").toOption.getD false
  let mut arts : NameMap ImportArtifacts := {}
  for (n, parts) in artsArr do
    arts := arts.insert n.toName (.ofArrays (parts.map (·.map System.FilePath.mk)))
  searchPathRef.set (← getBuiltinSearchPath sysrootStr)
  let roots := modNames.map fun n => { module := n.toName : Import }
  let env ← importModules roots {} (trustLevel := 0) (plugins := #[])
    (loadExts := false) (level := .private) (arts := arts)
  let allMatchers := collectAllMatchers env
  let mut attackerIdxs : Std.HashSet Nat := {}
  for mStr in attackerMods do
    let m := mStr.toName
    let some idx := env.header.moduleNames.idxOf? m
      | return ← failJson s!"missing attacker module {m} in E1 environment"
    attackerIdxs := attackerIdxs.insert idx
  let isOrigin (userN : Name) : Bool :=
    userN.getRoot != `IncorrectnessCheck &&
      match env.getModuleIdxFor? userN with
      | some pIdx => !attackerIdxs.contains pIdx.toNat
      | none => false
  for mStr in attackerMods do
    let m := mStr.toName
    let some idx := env.header.moduleNames.idxOf? m
      | return ← failJson s!"missing attacker module {m} in E1 environment"
    let some data := env.header.moduleData[idx]?
      | return ← failJson s!"missing moduleData for {m}"
    for ci in data.constants do
      let u := privateToUserName ci.name
      let r := u.getRoot
      let isAllowedReservedHelper :=
        isRealizedOrCompilerHelper env allMatchers isOrigin ci
      if reservedAttackerRoots.contains r && !isAllowedReservedHelper then
        return ← failJson
          s!"attacker module {m} declared reserved constant {ci.name} (root {r})"
      if m != `Proof && r == `Proof && !isAllowedReservedHelper then
        return ← failJson
          s!"helper module {m} cannot declare constant {ci.name} in Proof"
      let owner := env.getModuleIdxFor? ci.name |>.map (·.toNat)
      if owner != some idx then
        let okDup :=
          isAllowedReservedHelper &&
          (ci matches .thmInfo _) &&
          ((env.find? ci.name).any (sameRealizedThmHeader · ci))
        unless okDup do
          return ← failJson
            s!"duplicate/shadowed constant {ci.name} in attacker module {m}"
  let expMod? := (env.getModuleIdxFor? `IncorrectnessExpected.claim).bind
    fun i => env.header.moduleNames[i.toNat]?
  if expMod? != some `IncorrectnessExpected then
    return ← failJson
      s!"IncorrectnessExpected.claim owned by {expMod?} instead of IncorrectnessExpected"
  if requireS2Claim then
    let some expCi := env.find? `IncorrectnessExpected.claim
      | return ← failJson "missing _root_.IncorrectnessExpected.claim"
    unless expCi matches .defnInfo _ do
      return ← failJson "IncorrectnessExpected.claim must be a definition"
    if expCi.isUnsafe || expCi.isPartial || !expCi.levelParams.isEmpty then
      return ← failJson "IncorrectnessExpected.claim must be safe, total, and non-polymorphic"
    let some expVal := expCi.value? (allowOpaque := false)
      | return ← failJson "IncorrectnessExpected.claim value must be exposed"
    let expectedProp := mkApp (mkConst `Not)
      (mkApp (mkConst `Spec.targetSpec) (mkConst `Captured.program))
    unless expVal == expectedProp do
      return ← failJson
        "IncorrectnessExpected.claim body differs from ¬ Spec.targetSpec Captured.program"
  let some proofCi := env.find? `Proof.verify
    | return ← failJson "missing _root_.Proof.verify"
  let proofMod? := (env.getModuleIdxFor? `Proof.verify).bind
    fun i => env.header.moduleNames[i.toNat]?
  if proofMod? != some `Proof then
    return ← failJson s!"Proof.verify owned by {proofMod?} instead of Proof"
  unless proofCi matches .thmInfo _ do
    return ← failJson "Proof.verify must be a theorem"
  if proofCi.isUnsafe || proofCi.isPartial || !proofCi.levelParams.isEmpty then
    return ← failJson "Proof.verify must be safe, total, and non-polymorphic"
  let expConst := mkConst `IncorrectnessExpected.claim
  match Kernel.isDefEq env {} proofCi.type expConst with
  | .ok true => pure ()
  | .ok false =>
    return ← failJson
      "Proof.verify type is not definitionally equal to IncorrectnessExpected.claim"
  | .error _ =>
    return ← failJson "kernel error checking Proof.verify type against IncorrectnessExpected.claim"
  let verMod? := (env.getModuleIdxFor? `IncorrectnessCheck.verified).bind
    fun i => env.header.moduleNames[i.toNat]?
  if verMod? != some `IncorrectnessCheck then
    return ← failJson
      s!"IncorrectnessCheck.verified owned by {verMod?} instead of IncorrectnessCheck"
  let some verCi := env.find? `IncorrectnessCheck.verified
    | return ← failJson "missing _root_.IncorrectnessCheck.verified"
  match Kernel.isDefEq env {} verCi.type expConst with
  | .ok true => pure ()
  | _ =>
    return ← failJson
      "IncorrectnessCheck.verified type mismatch against IncorrectnessExpected.claim"
  IO.println <| Json.mkObj [("ok", toJson true)] |>.compress
  return 0
"""


_LOCAL_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|meta\s+|all\s+)*"
    r"import\s+(?:all\s+)?([A-Za-z0-9_.]+)"
)


def _lean_module_for_relpath(relpath: str) -> str:
    """Map submission relpath (`Spec/Spec.lean`, `theory/Anneal/X.lean`) to module."""
    trimmed = relpath
    if trimmed.startswith("Spec/"):
        trimmed = trimmed[len("Spec/") :]
    elif trimmed.startswith("theory/"):
        trimmed = trimmed[len("theory/") :]
    if trimmed.endswith(".lean"):
        trimmed = trimmed[: -len(".lean")]
    return trimmed.replace("/", ".")


def _load_foundation_and_local_graphs(
    anneal_root: Path | None,
    *,
    infra_error_cls: type[Exception],
) -> tuple[list[str], list[list[Any]], list[list[Any]]]:
    """Load pinned `foundation-lock.json` graph and `Trusted`/`Anneal` imports."""
    root_dir = (
        anneal_root
        if anneal_root is not None
        else Path(__file__).resolve().parents[2]
    )
    lock_path = root_dir / "trusted" / "lean" / "foundation-lock.json"
    try:
        lock = anneal_ci_lib.load_strict_json_object(
            lock_path, label="foundation-lock.json"
        )
    except RuntimeError as exc:
        raise infra_error_cls(str(exc)) from exc
    raw_graph = lock.get("graph")
    if not isinstance(raw_graph, dict) or not raw_graph:
        raise infra_error_cls("foundation-lock.json missing non-empty `graph`")
    fnd_modules = sorted(k for k in raw_graph if isinstance(k, str))
    fnd_pairs: list[list[Any]] = []
    for mod in fnd_modules:
        edges = raw_graph[mod]
        if not isinstance(edges, list):
            raise infra_error_cls(
                f"invalid edge list for {mod!r} in foundation-lock.json"
            )
        deps = [
            e["module"]
            for e in edges
            if isinstance(e, dict) and isinstance(e.get("module"), str)
        ]
        fnd_pairs.append([mod, deps])

    local_map: dict[str, list[str]] = {}
    for base in (root_dir / "trusted" / "lean", root_dir / "theory"):
        if not base.is_dir():
            continue
        for p in sorted(base.rglob("*.lean")):
            rel = p.relative_to(base).as_posix()
            mod_name = rel[: -len(".lean")].replace("/", ".")
            stripped = strip_lean_comments_and_strings(p.read_text(encoding="utf-8"))
            deps = []
            for ln in stripped.splitlines():
                m = _LOCAL_IMPORT_RE.match(ln)
                if m:
                    deps.append(m.group(1))
            local_map[mod_name] = deps
    local_pairs = [[m, local_map[m]] for m in sorted(local_map)]
    return fnd_modules, fnd_pairs, local_pairs


def _parse_ast_payload(
    proc: subprocess.CompletedProcess[str],
    *,
    infra_error_cls: type[Exception],
) -> tuple[list[str], list[str], list[str]]:
    """Validate and unpack `(tags, parse_errors, remaining_groups)` JSON."""
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()[:400]
        raise infra_error_cls(
            f"defender Lean AST inspector failed (rc={proc.returncode}): {detail}"
        )
    try:
        payload = json.loads(
            proc.stdout.strip().splitlines()[-1],
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
    except (IndexError, ValueError, json.JSONDecodeError) as exc:
        raise infra_error_cls(
            f"malformed defender Lean AST output: {exc}"
        ) from exc
    if isinstance(payload, list):
        tags = payload
        parse_errs: list[str] = []
        remaining: list[str] = []
    elif isinstance(payload, dict) and isinstance(payload.get("tags"), list):
        tags = payload["tags"]
        raw_errs = payload.get("parseErrors", [])
        if not isinstance(raw_errs, list) or not all(
            isinstance(e, str) for e in raw_errs
        ):
            raise infra_error_cls(
                "defender Lean AST parseErrors must be a string list"
            )
        parse_errs = raw_errs
        raw_rem = payload.get("remainingGroups", [])
        if not isinstance(raw_rem, list) or not all(
            isinstance(g, str) for g in raw_rem
        ):
            raise infra_error_cls(
                "defender Lean AST remainingGroups must be a string list"
            )
        remaining = raw_rem
    else:
        raise infra_error_cls(
            "defender Lean AST output must be a JSON object with tags"
        )
    if not all(isinstance(t, str) for t in tags):
        raise infra_error_cls("defender Lean AST output tags must be strings")
    return tags, parse_errs, remaining


def detect_disallowed_lean_constructs(
    sources: dict[str, str],
    *,
    allow_theory_import_all: bool = False,
    allow_spec_options: bool = False,
    lean_bin: Path | None = None,
    lean_sysroot: Path | None = None,
    bwrap: Path | None = None,
    bwrap_runner: Callable[..., subprocess.CompletedProcess[str]] | None = None,
    infra_error_cls: type[Exception] = RuntimeError,
    timeout: int = 90,
    parse_errors_out: list[str] | None = None,
    anneal_root: Path | None = None,
) -> list[str]:
    """Detect forbidden Lean constructs via bwrap AST parser or lexer fallback."""
    if lean_bin is None or lean_sysroot is None or bwrap is None or bwrap_runner is None:
        return _detect_disallowed_tokens_fallback(
            sources,
            allow_theory_import_all=allow_theory_import_all,
            allow_spec_options=allow_spec_options,
        )

    fnd_modules, fnd_pairs, local_pairs = _load_foundation_and_local_graphs(
        anneal_root, infra_error_cls=infra_error_cls
    )
    with tempfile.TemporaryDirectory(prefix="anneal-rt-ast-") as td:
        root = Path(td)
        src_dir = root / "src"
        ipc_dir = root / "ipc"
        src_dir.mkdir()
        ipc_dir.mkdir()
        entries: list[dict[str, Any]] = []
        for idx, rel in enumerate(sorted(sources)):
            dest = src_dir / f"f_{idx}.lean"
            dest.write_text(sources[rel], encoding="utf-8")
            allow_all = allow_theory_import_all and (
                rel == "theory/Anneal.lean" or rel.startswith("theory/Anneal/")
            )
            entries.append(
                {
                    "rel": rel,
                    "module": _lean_module_for_relpath(rel),
                    "path": f"/work/ast_src/f_{idx}.lean",
                    "allowAll": allow_all,
                }
            )
        script = ipc_dir / "InspectAst.lean"
        script.write_text(_LEAN_AST_AUDIT_SCRIPT, encoding="utf-8")
        req_payload: dict[str, Any] = {
            "sysroot": "/toolchain",
            "mode": "spec" if allow_spec_options else "theory",
            "singleGroupOnly": True,
            "foundationModules": fnd_modules,
            "foundationGraph": fnd_pairs,
            "localGraph": local_pairs,
            "files": entries,
        }
        req_file = ipc_dir / "req.json"
        req_file.write_text(json.dumps(req_payload), encoding="utf-8")

        deadline = time.monotonic() + max(1.0, float(timeout))
        proc = bwrap_runner(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[(src_dir, "/work/ast_src"), (ipc_dir, "/work/ipc")],
            rw_mounts=[],
            lean_path_mounts=[],
            cwd_in_sandbox="/work",
            lean_args=["--run", "/work/ipc/InspectAst.lean", "/work/ipc/req.json"],
            timeout=timeout,
        )
        tags_0, errs_0, remaining_groups = _parse_ast_payload(
            proc, infra_error_cls=infra_error_cls
        )
        all_tags: set[str] = set(tags_0)
        all_parse_errs: set[str] = set(errs_0)

        if remaining_groups:
            # Run each additional import closure in a fresh Lean process so
            # initializers re-arm cleanly and mmap/FD state stays bounded.
            use_precompiled = len(remaining_groups) >= 2
            ro_base = [(src_dir, "/work/ast_src"), (ipc_dir, "/work/ipc")]
            lean_path_base: list[str] = []
            entry_lean = "/work/ipc/InspectAst.lean"
            if use_precompiled:
                lib_dir = root / "lib_ipc"
                out_dir = root / "out"
                run_ipc_dir = root / "run_ipc"
                lib_dir.mkdir()
                out_dir.mkdir()
                run_ipc_dir.mkdir()
                main_suffix = "\ndef main (args : List String) : IO Unit :=\n  inspectMain args\n"
                if not _LEAN_AST_AUDIT_SCRIPT.endswith(main_suffix):
                    raise infra_error_cls("unexpected AST script entrypoint suffix")
                (lib_dir / "InspectAstLib.lean").write_text(
                    _LEAN_AST_AUDIT_SCRIPT[: -len(main_suffix)] + "\n",
                    encoding="utf-8",
                )
                rem_pre_float = deadline - time.monotonic()
                if rem_pre_float <= 0:
                    raise subprocess.TimeoutExpired("lean", timeout)
                rem_sec = max(1, int(math.ceil(rem_pre_float)))
                comp_proc = bwrap_runner(
                    bwrap=bwrap,
                    lean_bin=lean_bin,
                    lean_sysroot=lean_sysroot,
                    ro_mounts=[(lib_dir, "/work/lib_ipc")],
                    rw_mounts=[(out_dir, "/work/ast_out")],
                    lean_path_mounts=[],
                    cwd_in_sandbox="/work",
                    lean_args=[
                        "-j1",
                        "-R",
                        "/work/lib_ipc",
                        "-o",
                        "/work/ast_out/InspectAstLib.olean",
                        "/work/lib_ipc/InspectAstLib.lean",
                    ],
                    timeout=rem_sec,
                )
                if comp_proc.returncode != 0:
                    detail = (comp_proc.stderr or comp_proc.stdout).strip()[:400]
                    raise infra_error_cls(
                        f"defender Lean AST script compile failed (rc={comp_proc.returncode}): {detail}"
                    )
                (run_ipc_dir / "RunAst.lean").write_text(
                    "import InspectAstLib\ndef main (args : List String) : IO Unit := inspectMain args\n",
                    encoding="utf-8",
                )
                ro_base.extend(
                    [(out_dir, "/work/ast_out"), (run_ipc_dir, "/work/run_ipc")]
                )
                lean_path_base.append("/work/ast_out")
                entry_lean = "/work/run_ipc/RunAst.lean"

            for grp_idx, grp_key in enumerate(remaining_groups):
                rem_sec_float = deadline - time.monotonic()
                if rem_sec_float <= 0:
                    raise subprocess.TimeoutExpired("lean", timeout)
                grp_req = ipc_dir / f"req_g{grp_idx}.json"
                grp_payload = dict(req_payload)
                grp_payload["targetGroup"] = grp_key
                grp_req.write_text(json.dumps(grp_payload), encoding="utf-8")
                grp_proc = bwrap_runner(
                    bwrap=bwrap,
                    lean_bin=lean_bin,
                    lean_sysroot=lean_sysroot,
                    ro_mounts=ro_base,
                    rw_mounts=[],
                    lean_path_mounts=lean_path_base,
                    cwd_in_sandbox="/work",
                    lean_args=[
                        "--run",
                        entry_lean,
                        f"/work/ipc/req_g{grp_idx}.json",
                    ],
                    timeout=max(1, int(math.ceil(rem_sec_float))),
                )
                g_tags, g_errs, _ = _parse_ast_payload(
                    grp_proc, infra_error_cls=infra_error_cls
                )
                all_tags.update(g_tags)
                all_parse_errs.update(g_errs)

        if parse_errors_out is not None and all_parse_errs:
            parse_errors_out.extend(sorted(all_parse_errs))
        return sorted(all_tags)


def verify_e1_kernel_binding_in_bwrap(
    *,
    bwrap: Path,
    lean_bin: Path,
    lean_sysroot: Path,
    bwrap_runner: Callable[..., subprocess.CompletedProcess[str]],
    ro_mounts: list[tuple[Path, str]],
    modules: list[str],
    attacker_modules: list[str],
    artifacts_json: list[Any],
    require_s2_claim: bool = False,
    timeout: int = 90,
) -> tuple[bool, str]:
    """Run kernel `isDefEq` & reserved-namespace validation inside `bwrap`."""
    with tempfile.TemporaryDirectory(prefix="anneal-e1-bind-") as td:
        ipc_dir = Path(td)
        script = ipc_dir / "CheckE1Binding.lean"
        script.write_text(_LEAN_E1_BINDING_SCRIPT, encoding="utf-8")
        req_file = ipc_dir / "req.json"
        req_file.write_text(
            json.dumps(
                {
                    "sysroot": "/toolchain",
                    "artifacts": artifacts_json,
                    "modules": modules,
                    "attackerModules": attacker_modules,
                    "requireS2Claim": require_s2_claim,
                }
            ),
            encoding="utf-8",
        )
        proc = bwrap_runner(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[*ro_mounts, (ipc_dir, "/work/bind_ipc")],
            rw_mounts=[],
            lean_path_mounts=[],
            cwd_in_sandbox="/work",
            lean_args=[
                "--run",
                "/work/bind_ipc/CheckE1Binding.lean",
                "/work/bind_ipc/req.json",
            ],
            timeout=timeout,
        )
        lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
        if lines:
            try:
                obj = json.loads(
                    lines[-1],
                    object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
                )
                if isinstance(obj, dict) and "ok" in obj:
                    if obj.get("ok") is True and proc.returncode == 0:
                        return True, "ok"
                    return False, str(obj.get("message") or "E1 kernel binding failed")
            except (ValueError, json.JSONDecodeError):
                pass
        detail = (proc.stderr or proc.stdout).strip()[:400]
        return False, f"E1 binding probe failed (rc={proc.returncode}): {detail}"
