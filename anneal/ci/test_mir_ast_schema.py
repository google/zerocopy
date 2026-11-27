# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Enforce zero-default invariants on `Trusted.MirAst` types."""

from __future__ import annotations

from pathlib import Path
import re
import unittest


MIR_AST_DIR = (
    Path(__file__).resolve().parents[1]
    / "trusted"
    / "lean"
    / "Trusted"
    / "MirAst"
)
MIR_AST_UMBRELLA = MIR_AST_DIR.with_suffix(".lean")

# Explicitly documented benign or fail-closed field defaults in
# `Trusted/MirAst/Body.lean` and `Trusted/MirAst/Places.lean`. Every other
# field (including `Program.scope`, `Program.mirProfileVersion`,
# `Program.pointerWidthBits`, and all `EnumTy.*` fields) must remain
# default-free.
ALLOWED_DEFAULT_FIELDS: dict[tuple[str, str], str] = {
    ("BasicBlock", "cleanup"): "false",
    ("Body", "isUnsafe"): "false",
    ("Body", "identity"): '""',
    ("Program", "entryDefId"): "0",
    ("Program", "overflowChecks"): "false",
    ("Program", "panicStrategy"): ".unwind",
    ("Program", "hasLocalPanicHandler"): "true",
    ("Place", "projection"): "[]",
}

SECURITY_CRITICAL_REQUIRED_NO_DEFAULT: dict[str, tuple[str, ...]] = {
    "Program": ("bodies", "pointerWidthBits", "mirProfileVersion", "scope"),
    "Body": ("argumentCount", "locals", "basicBlocks"),
    "EnumTy": ("id", "discrWidth", "discrSigned", "tagRepr", "discriminants"),
}

DECL_MODIFIERS = (
    r"(?:@\[[^\]]+\]\s*|(?:public|private|protected|scoped|"
    r"noncomputable|meta|partial|unsafe|local)\s+)*"
)
ANY_STRUCTURE_RE = re.compile(
    r"^(?!\s*\(?[A-Za-z0-9_']+\s*:).*\b(?:structure|class)\b"
)
STRUCTURE_RE = re.compile(
    rf"^\s*{DECL_MODIFIERS}"
    r"(?:structure|class)\s+([A-Za-z0-9_']+)(?P<header>\s+.*?|\s*)where\s*$"
)
ANY_INDUCTIVE_RE = re.compile(
    r"^(?!\s*\(?[A-Za-z0-9_']+\s*:).*\binductive\b"
)
INDUCTIVE_RE = re.compile(
    rf"^\s*{DECL_MODIFIERS}inductive\s+([A-Za-z0-9_']+)(?P<header>.*)$"
)
FIELD_TYPED_RE = re.compile(
    r"^\s*(\(?)([A-Za-z0-9_']+)\s*:(?![:=])\s*(.+)$"
)
FIELD_DEFAULT_NOTYPE_RE = re.compile(
    r"^\s*(\(?)([A-Za-z0-9_']+)\s*:=\s*(.+)$"
)
GENERIC_DEFAULT_RE = re.compile(
    r"(?::=\s*\(*\s*(?:[A-Za-z_][A-Za-z0-9_'.]*\.)?default\b"
    r"|⟨\s*(?:[A-Za-z_][A-Za-z0-9_'.]*\.)?default\b)"
)
PARAM_DEFAULT_RE = re.compile(r"\b(?:optParam|autoParam)\b")
CHAR_LITERAL_RE = re.compile(
    r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'"
)
RAW_STR_START_RE = re.compile(r'r(#*)"')
TOP_LEVEL_PREFIX_RE = re.compile(
    rf"^(?:{DECL_MODIFIERS}(?:def|theorem|abbrev|opaque|axiom|"
    r"inductive|structure|class|instance|deriving|variable)|namespace|end|"
    r"section|open|universe|import|export|set_option|attribute|mutual|#)\b"
)
VARIABLE_DECL_RE = re.compile(
    rf"(?:^\s*|\bin\s+){DECL_MODIFIERS}variable\b(.*)$"
)


def _line_has_var_default(line: str) -> bool:
    return ":=" in line or bool(PARAM_DEFAULT_RE.search(line))


def _is_token_start(text: str, i: int) -> bool:
    return i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")


def strip_lean_comments(text: str) -> str:
    """Strip Lean `--` line comments and nested `/- ... -/` block comments."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    # Stack frames: ["plain", 0] or ["interp", brace_depth].
    str_stack: list[list[object]] = []
    # True after an interpolated-string prefix (`s!`, `f!`, `m!`) while
    # scanning optional whitespace/comments before the opening `"`.
    pending_interp = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if str_stack and str_stack[-1][1] == 0:
            kind = str_stack[-1][0]
            if kind == "interp" and ch == "{":
                # Lean 4 has no `{{` escape in interpolated strings; every
                # unescaped `{` (including in `{{`) starts an expression.
                str_stack[-1][1] = 1
                out.append("{")
                i += 1
                continue
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 2
            elif ch == '"':
                str_stack.pop()
                i += 1
            else:
                i += 1
            continue

        # Comments first so comment tokens never reset `pending_interp` and
        # `{`/`}` or quotes inside comments inside `{ ... }` stay ignored.
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
            continue
        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
            continue

        if pending_interp:
            if ch.isspace():
                out.append(ch)
                i += 1
                continue
            pending_interp = False
            if ch == '"':
                str_stack.append(["interp", 0])
                out.append(ch)
                i += 1
                continue

        # French-quoted identifier `«...»`: unwrap `optParam`/`autoParam`/
        # `default` (Lean strips guillemets during lexing) and sanitize other
        # punctuation (`/-`, `"`, `:=`) while preserving newlines.
        if ch == "\u00ab":
            ident_start = i + 1
            i += 1
            while i < n and text[i] != "\u00bb":
                i += 1
            if i >= n:
                raise ValueError(
                    "unterminated Lean guillemet identifier at EOF"
                )
            raw_ident = text[ident_start:i]
            if raw_ident in ("optParam", "autoParam", "default"):
                out.append(raw_ident)
            else:
                out.append("\u00ab")
                out.extend("\n" if c == "\n" else "_" for c in raw_ident)
                out.append("\u00bb")
            i += 1
            continue

        if ch == "'" and _is_token_start(text, i):
            m_char = CHAR_LITERAL_RE.match(text, i)
            if m_char is not None:
                out.append(m_char.group(0))
                i = m_char.end()
                continue

        if ch == "r" and _is_token_start(text, i):
            m_raw = RAW_STR_START_RE.match(text, i)
            if m_raw is not None:
                end_tok = '"' + m_raw.group(1)
                end_idx = text.find(end_tok, m_raw.end())
                if end_idx == -1:
                    raise ValueError(
                        "unterminated Lean raw string literal at EOF"
                    )
                end_pos = end_idx + len(end_tok)
                out.append(text[i:end_pos])
                i = end_pos
                continue

        if ch in ("s", "m", "f") and nxt == "!" and _is_token_start(text, i):
            after = text[i + 2] if i + 2 < n else ""
            after2 = text[i + 2 : i + 4]
            if after == '"' or after.isspace() or after2 in ("/-", "--"):
                out.extend((ch, "!"))
                i += 2
                pending_interp = True
                continue

        if ch == '"':
            str_stack.append(["plain", 0])
            out.append(ch)
            i += 1
            continue

        if str_stack and int(str_stack[-1][1]) > 0:
            if ch == "{":
                str_stack[-1][1] = int(str_stack[-1][1]) + 1
            elif ch == "}":
                str_stack[-1][1] = int(str_stack[-1][1]) - 1
            out.append(ch)
            i += 1
            continue

        out.append(ch)
        i += 1

    if block_depth > 0 or str_stack:
        raise ValueError(
            "unterminated Lean string/comment state at EOF "
            f"(block_depth={block_depth}, str_stack={len(str_stack)})"
        )
    return "".join(out)


def _normalize_default_expr(expr: str, had_leading_paren: bool) -> str:
    """Normalize whitespace and outer binder paren on a field default."""
    trimmed = expr.strip()
    if had_leading_paren and trimmed.endswith(")"):
        trimmed = trimmed[:-1].strip()
    return " ".join(trimmed.split())


def _split_paren_binders(line: str) -> list[str] | None:
    """Split `(a : T) (b : U := v)` lines into binder strings, or None."""
    s = line.strip()
    if not s.startswith("("):
        return None
    binders: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        if s[i] != "(":
            return None
        start = i
        depth = 0
        in_str = False
        while i < n:
            c = s[i]
            if in_str:
                if c == "\\" and i + 1 < n:
                    i += 2
                    continue
                if c == '"':
                    in_str = False
            else:
                if c == '"':
                    in_str = True
                elif c == "(":
                    depth += 1
                elif c == ")":
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
            i += 1
        else:
            return None
        binders.append(s[start:i])
    return binders or None


def _extract_typed_default(
    current: str,
    fname: str,
    rhs: str,
    had_paren: bool,
    parse_errors: list[str],
) -> str | None:
    """Validate and extract any default expression from a typed field RHS."""
    if PARAM_DEFAULT_RE.search(rhs):
        parse_errors.append(
            f"forbidden `optParam`/`autoParam` default on `{current}.{fname}`"
        )
        return None
    if ":=" in rhs:
        return _normalize_default_expr(rhs.split(":=", 1)[1], had_paren)
    return None


def _parse_structures_entries(
    lean_source: str,
) -> tuple[list[tuple[str, dict[str, str | None]]], list[str]]:
    """Return `([(struct, {field: default_expr_or_None})], parse_errors)`."""
    try:
        cleaned = strip_lean_comments(lean_source)
    except ValueError as exc:
        return [], [str(exc)]
    entries: list[tuple[str, dict[str, str | None]]] = []
    parse_errors: list[str] = []
    seen_names: set[str] = set()
    current: str | None = None
    current_fields: dict[str, str | None] | None = None
    in_inductive: str | None = None
    in_variable = False

    for raw_line in cleaned.splitlines():
        line = raw_line.rstrip()
        if not line.strip():
            continue
        if in_variable:
            stripped = line.lstrip()
            if (
                TOP_LEVEL_PREFIX_RE.match(stripped)
                or ANY_STRUCTURE_RE.match(line)
                or ANY_INDUCTIVE_RE.match(line)
            ):
                in_variable = False
            else:
                if _line_has_var_default(line):
                    parse_errors.append(
                        f"forbidden default in `variable` declaration: "
                        f"{line.strip()!r}"
                    )
                continue
        if ANY_STRUCTURE_RE.match(line):
            in_inductive = None
            m_struct = STRUCTURE_RE.match(line)
            if not m_struct:
                parse_errors.append(
                    f"unparsed `structure` declaration: {line.strip()!r}"
                )
                current = None
                current_fields = None
            elif ":=" in (m_struct.group("header") or ""):
                parse_errors.append(
                    f"forbidden default in `structure` header: "
                    f"{line.strip()!r}"
                )
                current = None
                current_fields = None
            elif re.search(
                r"\bextends\b", m_struct.group("header") or ""
            ):
                parse_errors.append(
                    f"forbidden `extends` in `structure` header: "
                    f"{line.strip()!r}"
                )
                current = None
                current_fields = None
            else:
                current = m_struct.group(1)
                if current in seen_names:
                    parse_errors.append(
                        f"duplicate `structure` declaration `{current}`"
                    )
                seen_names.add(current)
                current_fields = {}
                entries.append((current, current_fields))
            continue
        if ANY_INDUCTIVE_RE.match(line):
            current = None
            current_fields = None
            m_ind = INDUCTIVE_RE.match(line)
            if not m_ind:
                parse_errors.append(
                    f"unparsed `inductive` declaration: {line.strip()!r}"
                )
                in_inductive = None
            else:
                in_inductive = m_ind.group(1)
                if ":=" in (m_ind.group("header") or ""):
                    parse_errors.append(
                        f"forbidden default in `inductive` `{in_inductive}`: "
                        f"{line.strip()!r}"
                    )
            continue
        if in_inductive is not None:
            if not line[0].isspace() and not line.startswith("|"):
                if TOP_LEVEL_PREFIX_RE.match(line) and not (
                    line.startswith("deriving") and ":=" in line
                ):
                    in_inductive = None
                    if not VARIABLE_DECL_RE.search(line):
                        continue
                else:
                    parse_errors.append(
                        f"unexpected column-0 line in `{in_inductive}`: "
                        f"{line.strip()!r}"
                    )
                    in_inductive = None
                    continue
            else:
                if ":=" in line:
                    parse_errors.append(
                        f"forbidden default in `inductive` `{in_inductive}`: "
                        f"{line.strip()!r}"
                    )
                continue
        if current is None or current_fields is None:
            if VARIABLE_DECL_RE.search(line):
                in_variable = True
                if _line_has_var_default(line):
                    parse_errors.append(
                        f"forbidden default in `variable` declaration: "
                        f"{line.strip()!r}"
                    )
            continue
        # Top-level keywords terminate the current `structure` block; column-0
        # fields or unrecognized lines fail closed.
        if not line[0].isspace():
            if TOP_LEVEL_PREFIX_RE.match(line) and not (
                line.startswith("deriving") and ":=" in line
            ):
                current = None
                current_fields = None
                if VARIABLE_DECL_RE.search(line):
                    in_variable = True
                    if _line_has_var_default(line):
                        parse_errors.append(
                            f"forbidden default in `variable` declaration: "
                            f"{line.strip()!r}"
                        )
                continue
            parse_errors.append(
                f"unexpected column-0 line in `{current}`: {line.strip()!r}"
            )
            current = None
            current_fields = None
            continue
        if line.lstrip().startswith("("):
            binders = _split_paren_binders(line)
            if binders is None:
                parse_errors.append(
                    f"unparsed parenthesized binders in `{current}`: "
                    f"{line.strip()!r}"
                )
                continue
            for binder in binders:
                m_typed = FIELD_TYPED_RE.match(binder)
                if m_typed:
                    had_paren = bool(m_typed.group(1))
                    fname, rhs = m_typed.group(2), m_typed.group(3)
                    current_fields[fname] = _extract_typed_default(
                        current, fname, rhs, had_paren, parse_errors
                    )
                else:
                    m_notype = FIELD_DEFAULT_NOTYPE_RE.match(binder)
                    if m_notype:
                        had_paren = bool(m_notype.group(1))
                        current_fields[m_notype.group(2)] = (
                            _normalize_default_expr(
                                m_notype.group(3), had_paren
                            )
                        )
                    else:
                        parse_errors.append(
                            f"unparsed binder in `{current}`: {binder!r}"
                        )
            continue
        m_typed = FIELD_TYPED_RE.match(line)
        if m_typed:
            had_paren = bool(m_typed.group(1))
            fname, rhs = m_typed.group(2), m_typed.group(3)
            current_fields[fname] = _extract_typed_default(
                current, fname, rhs, had_paren, parse_errors
            )
            continue
        m_notype = FIELD_DEFAULT_NOTYPE_RE.match(line)
        if m_notype:
            had_paren = bool(m_notype.group(1))
            current_fields[m_notype.group(2)] = _normalize_default_expr(
                m_notype.group(3), had_paren
            )
            continue
        if not line.lstrip().startswith("deriving"):
            parse_errors.append(
                f"unparsed line in `{current}`: {line.strip()!r}"
            )

    return entries, parse_errors


def audit_mir_ast_sources(
    sources: dict[str, str],
) -> list[str]:
    """Validate zero-default invariants across `Trusted/MirAst` sources."""
    errors: list[str] = []
    seen_struct_files: dict[str, str] = {}
    struct_entries: dict[str, list[dict[str, str | None]]] = {}
    found_defaults: dict[tuple[str, str], str] = {}

    for filename, text in sorted(sources.items()):
        try:
            stripped = strip_lean_comments(text)
        except ValueError as exc:
            errors.append(f"{filename}: {exc}")
            continue
        if GENERIC_DEFAULT_RE.search(stripped):
            errors.append(
                f"{filename}: forbidden `:= default` in Trusted.MirAst"
            )
        entries, parse_errors = _parse_structures_entries(text)
        for p_err in parse_errors:
            errors.append(f"{filename}: {p_err}")
        if PARAM_DEFAULT_RE.search(stripped) and not any(
            "optParam`/`autoParam" in p for p in parse_errors
        ):
            errors.append(
                f"{filename}: forbidden `optParam`/`autoParam` "
                f"in Trusted.MirAst"
            )
        for sname, fields in entries:
            prev_file = seen_struct_files.get(sname)
            if prev_file is not None and prev_file != filename:
                errors.append(
                    f"{filename}: duplicate `structure` declaration "
                    f"`{sname}` (also in {prev_file})"
                )
            seen_struct_files.setdefault(sname, filename)
            struct_entries.setdefault(sname, []).append(fields)
            for fname, default_expr in fields.items():
                if default_expr is not None:
                    found_defaults[(sname, fname)] = default_expr
                    expected = ALLOWED_DEFAULT_FIELDS.get((sname, fname))
                    if expected is None:
                        errors.append(
                            f"{filename}: unexpected default on "
                            f"`{sname}.{fname}` (`{default_expr}`)"
                        )
                    elif default_expr != expected:
                        errors.append(
                            f"{filename}: allowlisted `{sname}.{fname}` "
                            f"default changed from {expected!r} to "
                            f"{default_expr!r}"
                        )

    stale = sorted(set(ALLOWED_DEFAULT_FIELDS) - set(found_defaults))
    if stale:
        errors.append(
            f"stale ALLOWED_DEFAULT_FIELDS entries absent from schema: {stale}"
        )

    for sname, req_fields in SECURITY_CRITICAL_REQUIRED_NO_DEFAULT.items():
        decls = struct_entries.get(sname)
        if not decls:
            errors.append(
                f"missing required structure `{sname}` in Trusted.MirAst"
            )
            continue
        for fields in decls:
            for fname in req_fields:
                if fname not in fields:
                    errors.append(f"missing required field `{sname}.{fname}`")
                elif fields[fname] is not None:
                    errors.append(
                        f"security-critical field `{sname}.{fname}` "
                        f"must omit :="
                    )

    return errors


class MirAstSchemaTests(unittest.TestCase):
    def _load_live_sources(self) -> dict[str, str]:
        self.assertTrue(
            MIR_AST_UMBRELLA.is_file(),
            f"missing umbrella module {MIR_AST_UMBRELLA}",
        )
        files = sorted(MIR_AST_DIR.rglob("*.lean"))
        self.assertTrue(files, f"no Lean files found in {MIR_AST_DIR}")
        sources = {
            "MirAst.lean": MIR_AST_UMBRELLA.read_text(encoding="utf-8")
        }
        for p in files:
            sources[p.relative_to(MIR_AST_DIR).as_posix()] = p.read_text(
                encoding="utf-8"
            )
        return sources

    def test_live_mir_ast_has_zero_unexpected_or_generic_defaults(self) -> None:
        stripped = strip_lean_comments(
            'def quoteChar : Char := \'"\'\n/- secret -/\n'
        )
        self.assertNotIn("secret", stripped)
        self.assertIsNone(VARIABLE_DECL_RE.search("in " * 200 + "xxxxx"))
        errors = audit_mir_ast_sources(self._load_live_sources())
        self.assertEqual(errors, [])

    def test_audit_rejects_security_critical_and_generic_defaults(self) -> None:
        base = self._load_live_sources()
        for label, filename, old, new, expected_msg in (
            (
                "program_scope_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope := .unit",
                "unexpected default on `Program.scope`",
            ),
            (
                "program_profile_default",
                "Body.lean",
                "  mirProfileVersion : Nat",
                "  mirProfileVersion : Nat := 1",
                "unexpected default on `Program.mirProfileVersion`",
            ),
            (
                "type_omitted_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  sneaky := (0 : Nat)",
                "unexpected default on `Program.sneaky`",
            ),
            (
                "binder_form_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  (binderDef : Nat := 0)",
                "unexpected default on `Program.binderDef`",
            ),
            (
                "multi_binder_line_default",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  (isUnsafe : Bool) (sneakyBypass : Bool := false)",
                "unexpected default on `Body.sneakyBypass`",
            ),
            (
                "header_binder_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ParamStruct (bad : Bool := true) where\n  x : Nat",
                "forbidden default in `structure` header",
            ),
            (
                "col0_field_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure Evil where\nbad : Nat := 1",
                "unexpected column-0 line in `Evil`",
            ),
            (
                "col0_switchtargets_field",
                "Terminators.lean",
                "  otherwise : BasicBlockId",
                "otherwise : BasicBlockId\nevilDefault : Nat := 42",
                "unexpected column-0 line in `SwitchTargets`",
            ),
            (
                "block_comment_prefixed_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "  /-\n  note\n  -/sneakyField : Bool := true",
                "unexpected default on `Program.sneakyField`",
            ),
            (
                "char_literal_quote_in_lean",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                "def quoteChar : Char := '\"' -- c\n"
                "structure AfterChar where\n  bad : Bool := true",
                "unexpected default on `AfterChar.bad`",
            ),
            (
                "extends_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ExtTest extends Foo where\n  bad : Nat := 1",
                "forbidden `extends` in `structure` header",
            ),
            (
                "extends_external_parent_rejected",
                "Body.lean",
                "structure Program where",
                "structure Program extends Trusted.Other.ProgramDefaults where",
                "forbidden `extends` in `structure` header",
            ),
            (
                "extends_basicblock_inherited_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure Wrapped extends BasicBlock where\n  x : Nat",
                "forbidden `extends` in `structure` header",
            ),
            (
                "generic_default_paren",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Bool := (default)",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "generic_default_qualified",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\n"
                "def badDefault : Bool := Inhabited.default",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "generic_default_anon_ctor",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Box := ⟨default⟩",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "ctor_double_colon_rejected",
                "Places.lean",
                "  projection : List ProjectionElem := []",
                "  projection :: sneaky : List ProjectionElem := []",
                "unparsed line in `Place`",
            ),
            (
                "private_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "@[ext] private structure PrivTest where\n  bad : Nat := 1",
                "unexpected default on `PrivTest.bad`",
            ),
            (
                "public_structure_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "public structure PubTest where\n  bad : Nat := 1",
                "unexpected default on `PubTest.bad`",
            ),
            (
                "unknown_modifier_fails_closed",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "future_mod structure FutTest where\n  x : Nat",
                "unparsed `structure` declaration",
            ),
            (
                "body_is_unsafe_flipped_true",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  isUnsafe : Bool := true",
                "allowlisted `Body.isUnsafe` default changed",
            ),
            (
                "multiline_default_continuation",
                "Body.lean",
                "  entryDefId : DefId := 0",
                "  entryDefId : DefId := 0\n    + 1",
                "unparsed line in `Program`",
            ),
            (
                "class_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "class ClsTest where\n  bad : Nat := 1",
                "unexpected default on `ClsTest.bad`",
            ),
            (
                "unparsed_structure_header",
                "Body.lean",
                "structure Program where",
                "structure Program\nwhere",
                "unparsed `structure` declaration",
            ),
            (
                "enum_ty_id_default",
                "Types.lean",
                "  id : Nat",
                "  id : Nat := 0",
                "unexpected default on `EnumTy.id`",
            ),
            (
                "generic_default_keyword",
                "Body.lean",
                "  cleanup : Bool := false",
                "  cleanup : Bool := default",
                "forbidden `:= default`",
            ),
            (
                "stale_allowlist_entry",
                "Body.lean",
                "  cleanup : Bool := false",
                "  cleanup : Bool",
                "stale ALLOWED_DEFAULT_FIELDS entries",
            ),
            (
                "undocumented_new_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n  extra : Nat := 0",
                "unexpected default on `Program.extra`",
            ),
            (
                "duplicate_struct_across_namespaces_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "namespace A\nstructure Dup where\n  bad : Nat := 1\nend A\n"
                "namespace B\nstructure Dup where\n  ok : Nat\nend B",
                "unexpected default on `Dup.bad`",
            ),
            (
                "duplicate_struct_across_namespaces_rejected",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "namespace A\nstructure Dup where\n  bad : Nat := 1\nend A\n"
                "namespace B\nstructure Dup where\n  ok : Nat\nend B",
                "duplicate `structure` declaration `Dup`",
            ),
            (
                "duplicate_program_in_other_file_missing_scope",
                "Types.lean",
                "  id : Nat",
                "  id : Nat\n"
                "end Trusted.MirAst\nnamespace Shadow\n"
                "structure Program where\n  extra : Nat",
                "missing required field `Program.scope`",
            ),
            (
                "optparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : optParam VerificationScope .unit",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "autoparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : autoParam VerificationScope myTac",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "optparam_binder_default",
                "Body.lean",
                "  isUnsafe : Bool := false",
                "  (isUnsafe : Bool := false) "
                "(sneaky : optParam Bool false)",
                "forbidden `optParam`/`autoParam` default on `Body.sneaky`",
            ),
            (
                "header_optparam_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "structure ParamStruct (x : optParam Nat 0) where\n  y : Nat",
                "forbidden `optParam`/`autoParam`",
            ),
            (
                "inductive_ctor_default",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup (block : BasicBlockId := 0)",
                "forbidden default in `inductive` `UnwindAction`",
            ),
            (
                "inductive_ctor_optparam",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup (block : optParam BasicBlockId 0)",
                "forbidden `optParam`/`autoParam`",
            ),
            (
                "inductive_header_default",
                "Body.lean",
                "inductive VerificationScope where",
                "inductive VerificationScope (x : Nat := 0) where",
                "forbidden default in `inductive` `VerificationScope`",
            ),
            (
                "inductive_multiline_ctor_default",
                "Terminators.lean",
                "| cleanup (block : BasicBlockId)",
                "| cleanup\n  (block : BasicBlockId := 0)",
                "forbidden default in `inductive` `UnwindAction`",
            ),
            (
                "col0_lemma_field_default",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\nlemma : Nat := 1",
                "unexpected column-0 line in `Program`",
            ),
            (
                "raw_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def rawEsc : String := r#"\\"#\n'
                'def blockHint : String := " /- "\n'
                "structure AfterRaw where\n  bad : Nat := 1",
                "unexpected default on `AfterRaw.bad`",
            ),
            (
                "zero_hash_raw_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def rawZero : String := r"\\"\n'
                'def blockHint : String := " /- "\n'
                "structure AfterRawZero where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterRawZero.bad`",
            ),
            (
                "s_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def interp : String := s!"hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterInterp where\n  bad : Nat := 1",
                "unexpected default on `AfterInterp.bad`",
            ),
            (
                "f_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def fInterp : String := f!"hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterFInterp where\n  bad : Nat := 1",
                "unexpected default on `AfterFInterp.bad`",
            ),
            (
                "prefix_bool_not_before_brace_string",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def b : Bool := !"{".isEmpty\n'
                'def c : String := " /- "\n'
                "structure AfterNot where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterNot.bad`",
            ),
            (
                "panic_macro_with_brace_not_interp",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def p : Nat := panic!"a {"\n'
                'def c : String := " /- "\n'
                "structure AfterPanic where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterPanic.bad`",
            ),
            (
                "guillemet_identifier_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def «/-» : Nat := 0\n'
                'def «"» : Nat := 0\n'
                "structure AfterGuillemet where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterGuillemet.bad`",
            ),
            (
                "unterminated_guillemet_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badGuillemet := «/-",
                "unterminated Lean guillemet identifier at EOF",
            ),
            (
                "spaced_s_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def sSp : String := s! /- " -/ "hi { -- {\n'
                '  "x" } /- "\n'
                "structure AfterSpacedS where\n  bad : Nat := 1",
                "unexpected default on `AfterSpacedS.bad`",
            ),
            (
                "spaced_f_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def fSp : Std.Format := f! "hi { -- "\n'
                '  "x" } /- "\n'
                "structure AfterSpacedF where\n  bad : Nat := 1",
                "unexpected default on `AfterSpacedF.bad`",
            ),
            (
                "double_lbrace_interp_string_desync",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def dbl : String := s!"{{ x := "a /- b" : Box }}"\n'
                "structure AfterDblBrace where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterDblBrace.bad`",
            ),
            (
                "escaped_lbrace_interp_string_preserved",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "end Trusted.MirAst\n"
                'def esc : String := s!"\\{"\n'
                'def c : String := " /- "\n'
                "structure AfterEscBrace where\n  bad : Nat := 1\n"
                "-- -/",
                "unexpected default on `AfterEscBrace.bad`",
            ),
            (
                "guillemet_optparam_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : «optParam» VerificationScope .unit",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "guillemet_autoparam_field",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : «autoParam» VerificationScope myTac",
                "forbidden `optParam`/`autoParam` default on `Program.scope`",
            ),
            (
                "guillemet_optparam_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : «optParam» Bool true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "guillemet_optparam_inductive",
                "Body.lean",
                "inductive VerificationScope where",
                "inductive VerificationScope where\n"
                "  | bogus (bad : «optParam» Nat 0)",
                "forbidden `optParam`/`autoParam` in Trusted.MirAst",
            ),
            (
                "guillemet_generic_default",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\ndef badDefault : Bool := «default»",
                "forbidden `:= default` in Trusted.MirAst",
            ),
            (
                "unterminated_block_comment_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                "end Trusted.MirAst\n/- unterminated",
                "unterminated Lean string/comment state at EOF",
            ),
            (
                "unterminated_interp_string_fails_closed",
                "Body.lean",
                "end Trusted.MirAst",
                'end Trusted.MirAst\ndef badStr := s!"hi {',
                "unterminated Lean string/comment state at EOF",
            ),
            (
                "variable_single_line_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : Bool := true)\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_multiline_default_after_struct",
                "Body.lean",
                "  scope : VerificationScope",
                "  scope : VerificationScope\n"
                "variable\n"
                "  (bad : Bool := true)\n"
                "inductive AfterVar where | ok",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_continuation_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (good : Bool)\n"
                "(bad : Bool := true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_after_bare_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable\n"
                "(bad : Bool := true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_col0_multiline_binder_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : Bool\n"
                ":= true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "variable_optparam_default",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "variable (bad : optParam Bool true)",
                "forbidden default in `variable` declaration",
            ),
            (
                "open_in_variable_single_line",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "open Trusted.MirAst in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "open_in_variable_multiline",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "open Trusted.MirAst in variable\n"
                "  (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "set_option_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "set_option autoImplicit false in "
                "variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "omit_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "omit [Inhabited Nat] in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "include_in_variable",
                "Body.lean",
                "namespace Trusted.MirAst",
                "namespace Trusted.MirAst\n"
                "include x in variable (bad : Bool := true) in\n"
                "structure ParamStruct where\n  h : bad = true",
                "forbidden default in `variable` declaration",
            ),
            (
                "umbrella_module_structure_default",
                "MirAst.lean",
                "public import Trusted.MirAst.Body",
                "public import Trusted.MirAst.Body\n"
                "structure UmbrellaBad where\n  bad : Nat := 1",
                "unexpected default on `UmbrellaBad.bad`",
            ),
        ):
            with self.subTest(case=label):
                mutated = dict(base)
                self.assertIn(old, mutated[filename])
                mutated[filename] = mutated[filename].replace(old, new, 1)
                errors = audit_mir_ast_sources(mutated)
                self.assertTrue(
                    any(expected_msg in e for e in errors),
                    f"{label}: expected {expected_msg!r} in {errors!r}",
                )

        with_ok_var = dict(base)
        with_ok_var["Body.lean"] = with_ok_var["Body.lean"].replace(
            "namespace Trusted.MirAst",
            "namespace Trusted.MirAst\n"
            "variable (good : Bool)\n"
            "(alsoGood : Nat)\n"
            "def okHelper : Nat := 0",
            1,
        )
        self.assertEqual(audit_mir_ast_sources(with_ok_var), [])

        with_sub = dict(base)
        with_sub["Sub/Extra.lean"] = (
            "namespace Trusted.MirAst\n"
            "structure SubStruct where\n"
            "  bad : Nat := 1\n"
            "end Trusted.MirAst\n"
        )
        sub_errors = audit_mir_ast_sources(with_sub)
        self.assertTrue(
            any(
                "Sub/Extra.lean" in e and "SubStruct.bad" in e
                for e in sub_errors
            ),
            sub_errors,
        )


if __name__ == "__main__":
    unittest.main()
