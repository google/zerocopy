#!/usr/bin/env bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

set -euo pipefail

cd "$(dirname "$0")/../.."

REQUIRE_SHELLCHECK=0
for arg in "$@"; do
  case "$arg" in
    --require-shellcheck)
      REQUIRE_SHELLCHECK=1
      ;;
    *)
      echo "error: unknown argument: $arg" >&2
      exit 2
      ;;
  esac
done

shopt -s nullglob
SHELL_FILES=(
  githooks/pre-push
  ci/*.sh
  ci/scripts/*.sh
  zerocopy/cargo.sh
  zerocopy/ci/*.sh
  anneal/ci/*.sh
  .github/scripts/*.sh
  tools/*.sh
)
shopt -u nullglob

for f in "${SHELL_FILES[@]}"; do
  bash -n "$f"
done

if command -v shellcheck >/dev/null 2>&1; then
  shellcheck -S warning "${SHELL_FILES[@]}"
elif [[ "$REQUIRE_SHELLCHECK" -eq 1 ]]; then
  echo "error: shellcheck is required under --require-shellcheck" >&2
  exit 1
fi

# Fail closed on piped `grep` across `SHELL_FILES` (all scripts run with
# `pipefail`, where an early-exiting `grep -q` can SIGPIPE the upstream
# writer into a spurious non-zero failure), allowing only exact non-quiet
# lines explicitly audited below.
python3 -I -B - "${SHELL_FILES[@]}" <<'PY'
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

ALLOWLIST: set[tuple[str, str]] = {
    (
        "zerocopy/ci/check_packaging.sh",
        "grep -Fx -e '// SPDX-License-Identifier: "
        "BSD-2-Clause OR Apache-2.0 OR MIT' \\",
    ),
    (
        "zerocopy/ci/check_packaging.sh",
        "-e '/* SPDX-License-Identifier: "
        "BSD-2-Clause OR Apache-2.0 OR MIT */' \\",
    ),
    (
        "zerocopy/ci/check_packaging.sh",
        "> /dev/null; then",
    ),
}

GREP_RE = re.compile(r"^[egf]?grep$")
_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
CMD_WRAPPERS = frozenset(
    {
        "!",
        "busybox",
        "command",
        "coproc",
        "doas",
        "env",
        "eval",
        "exec",
        "nice",
        "nohup",
        "stdbuf",
        "sudo",
        "time",
        "timeout",
    }
)
OPENERS = {
    "(": ")",
    "{": "}",
    "if": "fi",
    "while": "done",
    "until": "done",
    "for": "done",
    "select": "done",
    "case": "esac",
}
CLOSERS = frozenset({")", "}", "fi", "done", "esac"})
CASE_ARMS = frozenset({";;", ";&", ";;&"})
STMT_SEPS = frozenset({"NEWLINE", ";", "&", "&&", "||"})
STAGE_KW_RESET = frozenset({"then", "do", "else", "elif"})
COMPOUND_SEPS = (
    STMT_SEPS
    | CASE_ARMS
    | frozenset({"(", "{", "then", "do", "else", "elif"})
)


@dataclass
class Tok:
    kind: str
    val: str
    quoted: bool
    lines: tuple[int, ...]
    subshells: tuple[Subshell, ...] = ()
    is_assign: bool = False


Subshell = tuple[list[Tok], bool]
PendingHd = tuple[str, bool, bool, Tok]


class Cursor:
    def __init__(self, text: str) -> None:
        self.text = text
        self.n = len(text)
        self.i = 0
        self.line = 1

    def eof(self) -> bool:
        return self.i >= self.n

    def peek(self, off: int = 0) -> str:
        idx = self.i + off
        return self.text[idx] if idx < self.n else ""

    def startswith(self, prefix: str) -> bool:
        return self.text.startswith(prefix, self.i)

    def advance(self, count: int = 1) -> str:
        seg = self.text[self.i : self.i + count]
        self.line += seg.count("\n")
        self.i += count
        return seg

    def skip_line_cont(self) -> bool:
        if self.startswith("\\\n"):
            self.advance(2)
            return True
        return False

    def cont_end(self, prefix: str) -> int | None:
        i = self.i
        n = self.n
        for want in prefix:
            while (
                i + 1 < n
                and self.text[i] == "\\"
                and self.text[i + 1] == "\n"
            ):
                i += 2
            if i >= n or self.text[i] != want:
                return None
            i += 1
        return i

    def startswith_cont(self, prefix: str) -> bool:
        return self.cont_end(prefix) is not None

    def consume_cont(self, prefix: str) -> bool:
        end = self.cont_end(prefix)
        if end is None:
            return False
        self.advance(end - self.i)
        return True

    def peek_cont(self, off: int = 0) -> str:
        i = self.i
        n = self.n
        rem = off
        while i < n:
            if (
                i + 1 < n
                and self.text[i] == "\\"
                and self.text[i + 1] == "\n"
            ):
                i += 2
                continue
            if rem == 0:
                return self.text[i]
            rem -= 1
            i += 1
        return ""


def _consume_sq(c: Cursor) -> str:
    c.advance(1)
    out: list[str] = []
    while not c.eof():
        ch = c.advance(1)
        if ch == "'":
            break
        out.append(ch)
    return "".join(out)


def _consume_ansi_sq(c: Cursor) -> str:
    c.consume_cont("$'")
    out: list[str] = []
    while not c.eof():
        ch = c.advance(1)
        if ch == "\\" and not c.eof():
            out.append(c.advance(1))
        elif ch == "'":
            break
        else:
            out.append(ch)
    return "".join(out)


def _consume_balanced(
    c: Cursor,
    open_ch: str,
    close_ch: str,
    subshells: list[Subshell],
    *,
    in_dq: bool = False,
    allow_comments: bool = True,
    pending_hd: list[PendingHd] | None = None,
) -> None:
    depth = 1
    at_word_start = True
    while not c.eof() and depth > 0:
        if c.skip_line_cont():
            continue
        if (
            allow_comments
            and open_ch == "("
            and at_word_start
            and c.peek() == "#"
        ):
            while not c.eof() and c.peek() != "\n":
                c.advance(1)
            continue
        ch = c.peek()
        if ch in (" ", "\t", "\n"):
            at_word_start = True
            c.advance(1)
            continue
        at_word_start = False
        if not in_dq and c.startswith("'") and open_ch != "'":
            _consume_sq(c)
        elif not in_dq and c.startswith_cont("$'"):
            _consume_ansi_sq(c)
        elif not in_dq and c.startswith_cont('$"'):
            _consume_dq(
                c, subshells, locale=True, pending_hd=pending_hd
            )
        elif c.startswith('"'):
            _consume_dq(c, subshells, pending_hd=pending_hd)
        elif c.startswith_cont("$("):
            _consume_dollar_lparen(
                c, subshells, in_dq=in_dq, pending_hd=pending_hd
            )
        elif not in_dq and (
            c.startswith_cont("<(") or c.startswith_cont(">(")
        ):
            is_out = c.startswith_cont(">(")
            c.consume_cont(">(" if is_out else "<(")
            sub_toks = tokenize(
                c, stop_at_rparen=True, out_pending_hd=pending_hd
            )
            subshells.append((sub_toks, is_out))
        elif c.consume_cont("${"):
            _consume_balanced(
                c, "{", "}", subshells, in_dq=in_dq, pending_hd=pending_hd
            )
        elif c.startswith("`"):
            _consume_backtick(c, subshells, in_dq=in_dq)
        elif ch == "\\":
            c.advance(1)
            if not c.eof():
                c.advance(1)
        elif ch == open_ch and open_ch != "{":
            depth += 1
            at_word_start = True
            c.advance(1)
        elif ch == close_ch:
            depth -= 1
            c.advance(1)
        else:
            c.advance(1)


def _consume_dollar_lparen(
    c: Cursor,
    subshells: list[Subshell],
    *,
    in_dq: bool = False,
    pending_hd: list[PendingHd] | None = None,
) -> None:
    saved_i, saved_line, saved_subs = c.i, c.line, len(subshells)
    if c.consume_cont("$(("):
        arith_hd: list[PendingHd] = []
        if _consume_arith(
            c, subshells, in_dq=in_dq, pending_hd=arith_hd
        ):
            if pending_hd is not None and arith_hd:
                pending_hd.extend(arith_hd)
            return
        c.i, c.line = saved_i, saved_line
        del subshells[saved_subs:]
    c.consume_cont("$(")
    sub_toks = tokenize(
        c, stop_at_rparen=True, out_pending_hd=pending_hd
    )
    subshells.append((sub_toks, False))


def _consume_arith(
    c: Cursor,
    subshells: list[Subshell],
    *,
    in_dq: bool = False,
    pending_hd: list[PendingHd] | None = None,
) -> bool:
    paren = 0
    while not c.eof():
        if c.skip_line_cont():
            continue
        if c.startswith("'"):
            _consume_sq(c)
        elif c.startswith_cont("$'"):
            _consume_ansi_sq(c)
        elif c.startswith_cont('$"'):
            _consume_dq(
                c, subshells, locale=True, pending_hd=pending_hd
            )
        elif c.startswith('"'):
            _consume_dq(c, subshells, pending_hd=pending_hd)
        elif c.startswith_cont("$("):
            _consume_dollar_lparen(
                c, subshells, in_dq=in_dq, pending_hd=pending_hd
            )
        elif c.consume_cont("${"):
            _consume_balanced(
                c, "{", "}", subshells, in_dq=in_dq, pending_hd=pending_hd
            )
        elif c.startswith("`"):
            _consume_backtick(c, subshells, in_dq=in_dq)
        elif c.peek() == "\\":
            c.advance(1)
            if not c.eof():
                c.advance(1)
        elif c.peek() == "(":
            paren += 1
            c.advance(1)
        elif c.peek() == ")":
            if paren > 0:
                paren -= 1
                c.advance(1)
            elif c.consume_cont("))"):
                return True
            else:
                return False
        else:
            c.advance(1)
    return False


def _consume_backtick(
    c: Cursor, subshells: list[Subshell], *, in_dq: bool
) -> None:
    c.advance(1)
    start_line = c.line
    chars: list[str] = []
    while not c.eof():
        if c.skip_line_cont():
            continue
        ch = c.advance(1)
        if ch == "`":
            sub_c = Cursor("".join(chars))
            sub_c.line = start_line
            sub_toks = tokenize(sub_c)
            subshells.append((sub_toks, False))
            return
        if ch == "\\" and not c.eof():
            nxt = c.peek()
            if nxt in ("$", "`", "\\") or (in_dq and nxt == '"'):
                chars.append(c.advance(1))
            else:
                chars.append(ch)
        else:
            chars.append(ch)


def _consume_dq(
    c: Cursor,
    subshells: list[Subshell],
    *,
    locale: bool = False,
    pending_hd: list[PendingHd] | None = None,
) -> str:
    if locale:
        c.consume_cont('$"')
    else:
        c.advance(1)
    out: list[str] = []
    while not c.eof():
        if c.skip_line_cont():
            continue
        ch = c.peek()
        if ch == '"':
            c.advance(1)
            break
        if ch == "\\":
            c.advance(1)
            if not c.eof():
                out.append(c.advance(1))
        elif c.startswith_cont("$("):
            _consume_dollar_lparen(
                c, subshells, in_dq=True, pending_hd=pending_hd
            )
        elif c.consume_cont("${"):
            _consume_balanced(
                c, "{", "}", subshells, in_dq=True, pending_hd=pending_hd
            )
        elif ch == "`":
            _consume_backtick(c, subshells, in_dq=True)
        else:
            out.append(c.advance(1))
    return "".join(out)


def _scan_unquoted_heredoc(
    body: str, start_line: int, subshells: list[Subshell]
) -> None:
    hc = Cursor(body)
    hc.line = start_line
    while not hc.eof():
        if hc.skip_line_cont():
            continue
        if hc.startswith("\\"):
            hc.advance(1)
            if not hc.eof():
                hc.advance(1)
        elif hc.startswith_cont("$("):
            _consume_dollar_lparen(hc, subshells, in_dq=False)
        elif hc.consume_cont("${"):
            _consume_balanced(hc, "{", "}", subshells, in_dq=True)
        elif hc.peek() == "`":
            _consume_backtick(hc, subshells, in_dq=False)
        else:
            hc.advance(1)


def _skip_heredocs(
    c: Cursor,
    pending: list[PendingHd],
) -> None:
    while pending:
        delim, strip_tabs, is_quoted, redir_tok = pending.pop(0)
        matched = False
        body_start_line = c.line
        body_lines: list[str] = []
        while not c.eof():
            line_start = c.i
            while not c.eof() and c.peek() != "\n":
                c.advance(1)
            body_line = c.text[line_start:c.i]
            raw_sep = "\n" if not c.eof() else ""
            if not c.eof():
                c.advance(1)
            cmp_line = body_line.lstrip("\t") if strip_tabs else body_line
            if cmp_line == delim:
                matched = True
                break
            body_lines.append(body_line + raw_sep)
        if not matched:
            raise ValueError(f"unterminated heredoc {delim!r}")
        if not is_quoted and body_lines:
            hd_subs: list[Subshell] = []
            _scan_unquoted_heredoc(
                "".join(body_lines), body_start_line, hd_subs
            )
            if hd_subs:
                redir_tok.subshells = redir_tok.subshells + tuple(hd_subs)


def _peek_next_is_compound_opener(c: Cursor) -> bool:
    j = c.i
    n = c.n
    while j < n:
        if c.text.startswith("\\\n", j):
            j += 2
            continue
        if c.text[j] in (" ", "\t"):
            j += 1
            continue
        break
    if j >= n:
        return False
    joined, _ = _strip_cont_prefix(c.text, j, 16)
    if joined.startswith("("):
        return not joined.startswith(("<(", ">("))
    for kw in (
        "{", "[[", "if", "while", "until", "for", "select", "case"
    ):
        if joined.startswith(kw):
            end = len(kw)
            if kw == "{":
                return end < len(joined) and joined[end] in (" ", "\t", "\n")
            if end >= len(joined) or joined[end] in (
                " ", "\t", "\n", ";", "&", "|", "(", ")", "<", ">"
            ):
                return True
    return False


_REDIR_OP_RE = re.compile(
    r"^(?:<<<|<<-|<<|>&|<&|&>>|&>|>>|>\||<>|>|<)"
)
_REDIR_SIMPLE_RE = re.compile(
    r"^(?:[0-9]+|\{[A-Za-z_][A-Za-z0-9_]*\})?"
    r"(<<<|<<-|<<|>&|<&|&>>|&>|>>|>\||<>|>|<)"
)
_REDIR_ARR_RE = re.compile(r"^\{[A-Za-z_][A-Za-z0-9_]*(?=\[)")


def _strip_cont_prefix(
    text: str, start: int, limit: int = 256
) -> tuple[str, list[int]]:
    chars: list[str] = []
    ends: list[int] = [start]
    i = start
    n = len(text)
    while i < n and len(chars) < limit:
        if text.startswith("\\\n", i):
            i += 2
            continue
        chars.append(text[i])
        i += 1
        ends.append(i)
    return ("".join(chars), ends)


def _consume_bracket_expr(
    c: Cursor,
    subshells: list[Subshell],
    lines: set[int] | None = None,
    pending_hd: list[PendingHd] | None = None,
) -> bool:
    if c.peek() != "[":
        return False
    if lines is not None:
        lines.add(c.line)
    c.advance(1)
    depth = 1
    while not c.eof() and depth > 0:
        if c.skip_line_cont():
            continue
        if lines is not None:
            lines.add(c.line)
        ch = c.peek()
        if ch == "'":
            _consume_sq(c)
        elif c.startswith_cont("$'"):
            _consume_ansi_sq(c)
        elif c.startswith_cont('$"'):
            _consume_dq(
                c, subshells, locale=True, pending_hd=pending_hd
            )
        elif ch == '"':
            _consume_dq(c, subshells, pending_hd=pending_hd)
        elif c.startswith_cont("$("):
            _consume_dollar_lparen(
                c, subshells, in_dq=False, pending_hd=pending_hd
            )
        elif c.consume_cont("${"):
            _consume_balanced(
                c, "{", "}", subshells, pending_hd=pending_hd
            )
        elif ch == "`":
            _consume_backtick(c, subshells, in_dq=False)
        elif ch == "\\":
            c.advance(1)
            if not c.eof():
                c.advance(1)
        elif ch == "[":
            depth += 1
            c.advance(1)
        elif ch == "]":
            depth -= 1
            c.advance(1)
        else:
            c.advance(1)
    if lines is not None:
        lines.add(c.line)
    return depth == 0


def _match_redir(
    c: Cursor,
    pending_hd: list[PendingHd] | None = None,
) -> tuple[str, str, tuple[int, ...], list[Subshell]] | None:
    ln = c.line
    saved_i, saved_line = c.i, c.line
    joined, ends = _strip_cont_prefix(c.text, c.i, 256)
    m = _REDIR_SIMPLE_RE.match(joined)
    if m is not None:
        r_op = m.group(0)
        r_base = m.group(1)
        c.advance(ends[len(r_op)] - c.i)
        lines_span = tuple(range(ln, c.line + 1))
        return (r_op, r_base, lines_span, [])
    arr_m = _REDIR_ARR_RE.match(joined)
    if arr_m is None:
        return None
    c.advance(ends[len(arr_m.group(0))] - c.i)
    while c.skip_line_cont():
        pass
    subshells: list[Subshell] = []
    redir_hd: list[PendingHd] = []
    if _consume_bracket_expr(c, subshells, pending_hd=redir_hd):
        while c.skip_line_cont():
            pass
        if c.peek() == "}":
            c.advance(1)
            while c.skip_line_cont():
                pass
            op_joined, op_ends = _strip_cont_prefix(c.text, c.i, 8)
            op_m = _REDIR_OP_RE.match(op_joined)
            if op_m is not None:
                r_base = op_m.group(0)
                c.advance(op_ends[len(r_base)] - c.i)
                lines_span = tuple(range(ln, c.line + 1))
                if pending_hd is not None and redir_hd:
                    pending_hd.extend(redir_hd)
                return (c.text[saved_i:c.i], r_base, lines_span, subshells)
    c.i, c.line = saved_i, saved_line
    return None


def _advance_for_hdr(
    state: str, word: str, quoted: bool
) -> tuple[str | None, str | None]:
    if state == "var":
        if not quoted and word == "(())":
            return ("sep_do", None)
        return ("after_var", None)
    if state == "after_var":
        if not quoted and word == "in":
            return ("in_list", None)
        if not quoted and word in ("do", "{"):
            return (None, "done" if word == "do" else "}")
        return ("after_var", None)
    if state == "in_list":
        return ("in_list", None)
    if not quoted and word in ("do", "{"):
        return (None, "done" if word == "do" else "}")
    return ("sep_do", None)


def tokenize(
    c: Cursor,
    *,
    stop_at_rparen: bool = False,
    out_pending_hd: list[PendingHd] | None = None,
) -> list[Tok]:
    tokens: list[Tok] = []
    inherited_hd: list[PendingHd] = []
    pending_hd: list[PendingHd] = []
    expect_hd: tuple[Tok, bool] | None = None
    paren_depth = 0
    case_stack: list[str] = []
    cmd_pos = True
    after_redir = False
    after_closer = False
    for_hdr: str | None = None
    in_bracket_test = False
    in_bracket_regex = False
    in_bracket_pat = False
    expect_func_name = False
    after_time = False
    after_coproc = False

    while not c.eof():
        while not c.eof():
            if c.skip_line_cont():
                continue
            if c.peek() in (" ", "\t"):
                c.advance(1)
                continue
            break
        if c.eof():
            break
        if c.peek() == "#":
            while not c.eof() and c.peek() != "\n":
                c.advance(1)
            continue
        if c.peek() == "\n":
            ln = c.line
            c.advance(1)
            if inherited_hd or pending_hd:
                all_hd = inherited_hd + pending_hd
                inherited_hd.clear()
                pending_hd.clear()
                _skip_heredocs(c, all_hd)
            tokens.append(Tok("NEWLINE", "\n", False, (ln,)))
            expect_hd = None
            after_redir = False
            after_closer = False
            cmd_pos = True
            if for_hdr == "in_list":
                for_hdr = "sep_do"
            if for_hdr is not None:
                cmd_pos = False
            in_bracket_regex = False
            in_bracket_pat = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            continue

        ln = c.line
        in_case_pat = bool(
            case_stack and case_stack[-1] in ("pat_start", "pat")
        )

        tok_joined, tok_ends = _strip_cont_prefix(c.text, c.i, 4)
        if (
            not in_case_pat
            and not in_bracket_test
            and not in_bracket_regex
            and tok_joined.startswith("((")
        ):
            saved_i, saved_line = c.i, c.line
            arith_subs: list[Subshell] = []
            arith_hd: list[PendingHd] = []
            c.advance(tok_ends[2] - c.i)
            if _consume_arith(c, arith_subs, pending_hd=arith_hd):
                if arith_hd:
                    inherited_hd.extend(arith_hd)
                lines_span = tuple(range(ln, c.line + 1))
                tokens.append(
                    Tok(
                        "WORD",
                        "(())",
                        False,
                        lines_span,
                        tuple(arith_subs),
                    )
                )
                expect_hd = None
                after_redir = False
                after_closer = True
                cmd_pos = False
                if for_hdr == "var":
                    for_hdr = "sep_do"
                expect_func_name = False
                continue
            c.i, c.line = saved_i, saved_line

        if tok_joined.startswith("<(") or tok_joined.startswith(">("):
            is_out = tok_joined.startswith(">(")
            c.advance(tok_ends[2] - c.i)
            sub_toks = tokenize(
                c, stop_at_rparen=True, out_pending_hd=inherited_hd
            )
            lines_span = tuple(range(ln, c.line + 1))
            tokens.append(
                Tok(
                    "WORD",
                    "<()>",
                    False,
                    lines_span,
                    ((sub_toks, is_out),),
                )
            )
            expect_hd = None
            after_redir = False
            after_closer = False
            in_bracket_regex = False
            in_bracket_pat = False
            continue

        redir = (
            None
            if (in_case_pat or in_bracket_regex)
            else _match_redir(c, inherited_hd)
        )
        if redir is not None:
            r_op, r_base, r_lines, r_subs = redir
            redir_tok = Tok("REDIR", r_op, False, r_lines, tuple(r_subs))
            tokens.append(redir_tok)
            after_redir = True
            if r_base == "<<-":
                expect_hd = (redir_tok, True)
            elif r_base == "<<":
                expect_hd = (redir_tok, False)
            else:
                expect_hd = None
            continue

        matched_op = None
        for op in (
            ";;&", ";;", ";&", "|&", "&&", "||", ";", "&", "|", "(", ")"
        ):
            if tok_joined.startswith(op):
                if in_bracket_regex and op in ("(", "|"):
                    break
                matched_op = op
                break
        if matched_op:
            op_end = tok_ends[len(matched_op)]
            expect_hd = None
            after_redir = False
            after_closer = False
            in_bracket_regex = False
            in_bracket_pat = False
            if matched_op == "(":
                if in_case_pat:
                    case_stack[-1] = "pat"
                    c.advance(op_end - c.i)
                    tokens.append(Tok("OP", "(", False, (ln,)))
                    continue
                j = op_end
                while j < len(c.text):
                    if c.text.startswith("\\\n", j):
                        j += 2
                    elif c.text[j] in (" ", "\t"):
                        j += 1
                    else:
                        break
                if j < len(c.text) and c.text[j] == ")":
                    c.advance(j - c.i + 1)
                    tokens.append(Tok("OP", "(", False, (ln,)))
                    tokens.append(Tok("OP", ")", False, (ln,)))
                    cmd_pos = True
                    expect_func_name = False
                    after_time = False
                    after_coproc = False
                    continue
                paren_depth += 1
                c.advance(op_end - c.i)
                tokens.append(Tok("OP", "(", False, (ln,)))
                cmd_pos = True
                expect_func_name = False
                after_time = False
                after_coproc = False
                continue
            if matched_op == ")":
                if in_case_pat:
                    case_stack[-1] = "body"
                    c.advance(op_end - c.i)
                    tokens.append(Tok("OP", ")", False, (ln,)))
                    cmd_pos = True
                    expect_func_name = False
                    after_time = False
                    after_coproc = False
                    continue
                if stop_at_rparen and paren_depth == 0:
                    c.advance(op_end - c.i)
                    if out_pending_hd is not None and (
                        inherited_hd or pending_hd
                    ):
                        out_pending_hd.extend(inherited_hd)
                        out_pending_hd.extend(pending_hd)
                    return tokens
                if paren_depth > 0:
                    paren_depth -= 1
                c.advance(op_end - c.i)
                tokens.append(Tok("OP", ")", False, (ln,)))
                cmd_pos = False
                after_closer = True
                expect_func_name = False
                after_time = False
                after_coproc = False
                continue
            c.advance(op_end - c.i)
            op_lines = tuple(range(ln, c.line + 1))
            expect_func_name = False
            after_time = False
            after_coproc = False
            if matched_op in ("|", "|&"):
                tokens.append(Tok("PIPE", matched_op, False, op_lines))
                if in_case_pat:
                    case_stack[-1] = "pat"
                else:
                    cmd_pos = True
            else:
                tokens.append(Tok("SEP", matched_op, False, op_lines))
                if matched_op in CASE_ARMS and case_stack:
                    case_stack[-1] = "pat_start"
                    cmd_pos = False
                elif matched_op == ";" and for_hdr in (
                    "after_var", "in_list", "sep_do"
                ):
                    for_hdr = "sep_do"
                    cmd_pos = False
                else:
                    cmd_pos = True
                    for_hdr = None
            continue

        word_parts: list[str] = []
        word_lines: set[int] = set()
        word_subs: list[Subshell] = []
        quoted = False
        has_subst = False
        is_assign = False
        regex_mode = in_bracket_regex
        regex_paren = 0
        while not c.eof():
            if c.skip_line_cont():
                continue
            ch = c.peek()
            if regex_mode:
                if regex_paren == 0 and (
                    ch in (" ", "\t", "\n", ";", ")")
                    or c.startswith_cont("&&")
                    or c.startswith_cont("||")
                ):
                    break
            elif ch in (" ", "\t", "\n", ";", "&", "|", "(", ")", "<", ">"):
                break
            word_lines.add(c.line)
            if ch == "'":
                quoted = True
                word_parts.append(_consume_sq(c))
            elif c.startswith_cont("$'"):
                quoted = True
                word_parts.append(_consume_ansi_sq(c))
            elif c.startswith_cont('$"'):
                quoted = True
                word_parts.append(
                    _consume_dq(
                        c, word_subs, locale=True, pending_hd=inherited_hd
                    )
                )
            elif ch == '"':
                quoted = True
                word_parts.append(
                    _consume_dq(c, word_subs, pending_hd=inherited_hd)
                )
            elif c.startswith_cont("$("):
                has_subst = True
                _consume_dollar_lparen(
                    c, word_subs, in_dq=False, pending_hd=inherited_hd
                )
            elif c.consume_cont("${"):
                has_subst = True
                _consume_balanced(
                    c, "{", "}", word_subs, pending_hd=inherited_hd
                )
            elif ch == "`":
                has_subst = True
                _consume_backtick(c, word_subs, in_dq=False)
            elif ch == "\\":
                quoted = True
                c.advance(1)
                if not c.eof():
                    word_parts.append(c.advance(1))
            elif regex_mode and ch == "(":
                regex_paren += 1
                word_parts.append(c.advance(1))
            elif regex_mode and ch == ")" and regex_paren > 0:
                regex_paren -= 1
                word_parts.append(c.advance(1))
            elif (
                (in_case_pat or (in_bracket_pat and not regex_mode))
                and ch in "@?*+!"
                and c.peek_cont(1) == "("
            ):
                word_parts.append(c.advance(1))
                c.consume_cont("(")
                word_parts.append("(")
                _consume_balanced(
                    c,
                    "(",
                    ")",
                    word_subs,
                    allow_comments=False,
                    pending_hd=inherited_hd,
                )
            elif (
                not is_assign
                and not quoted
                and not has_subst
                and not in_case_pat
                and not in_bracket_test
                and not regex_mode
                and ch in ("[", "=", "+")
                and _IDENT_RE.match("".join(word_parts))
            ):
                if ch == "[":
                    s_i, s_ln, s_subs = c.i, c.line, len(word_subs)
                    sub_lines: set[int] = set()
                    idx_hd: list[PendingHd] = []
                    if _consume_bracket_expr(
                        c, word_subs, sub_lines, pending_hd=idx_hd
                    ):
                        eq_j, eq_e = _strip_cont_prefix(c.text, c.i, 2)
                        eq_len = (
                            2
                            if eq_j.startswith("+=")
                            else (1 if eq_j.startswith("=") else 0)
                        )
                        if eq_len > 0:
                            c.advance(eq_e[eq_len] - c.i)
                            if idx_hd:
                                inherited_hd.extend(idx_hd)
                            word_lines.update(sub_lines)
                            word_lines.add(c.line)
                            word_parts.append(c.text[s_i:c.i])
                            is_assign = True
                            continue
                    c.i, c.line = s_i, s_ln
                    del word_subs[s_subs:]
                    word_parts.append(c.advance(1))
                elif ch == "+":
                    eq_j, eq_e = _strip_cont_prefix(c.text, c.i, 2)
                    if eq_j.startswith("+="):
                        c.advance(eq_e[2] - c.i)
                        word_lines.add(c.line)
                        word_parts.append("+=")
                        is_assign = True
                        while c.skip_line_cont():
                            pass
                        if c.peek() == "(":
                            c.advance(1)
                            _consume_balanced(
                                c,
                                "(",
                                ")",
                                word_subs,
                                pending_hd=inherited_hd,
                            )
                    else:
                        word_parts.append(c.advance(1))
                else:
                    is_assign = True
                    word_parts.append(c.advance(1))
                    while c.skip_line_cont():
                        pass
                    if c.peek() == "(":
                        c.advance(1)
                        _consume_balanced(
                            c, "(", ")", word_subs, pending_hd=inherited_hd
                        )
            else:
                word_parts.append(c.advance(1))
                if (
                    not in_bracket_test
                    and not in_case_pat
                    and word_parts[-1] == "="
                    and c.peek() == "("
                ):
                    c.advance(1)
                    _consume_balanced(
                        c, "(", ")", word_subs, pending_hd=inherited_hd
                    )
        in_bracket_regex = False
        in_bracket_pat = False
        word = "".join(word_parts)
        word_lines.add(c.line)
        kw_quoted = quoted or has_subst
        if expect_hd is not None:
            pending_hd.append((word, expect_hd[1], quoted, expect_hd[0]))
            expect_hd = None
            after_redir = False
            after_closer = False
        else:
            if after_redir:
                after_redir = False
            elif expect_func_name:
                expect_func_name = False
                cmd_pos = True
                after_closer = False
            elif in_bracket_test:
                after_closer = False
                if not kw_quoted and word == "]]":
                    in_bracket_test = False
                    after_closer = True
                elif not regex_mode and not kw_quoted and word == "=~":
                    in_bracket_regex = True
                elif (
                    not regex_mode
                    and not kw_quoted
                    and word in ("==", "!=", "=")
                ):
                    in_bracket_pat = True
            elif case_stack and case_stack[-1] == "word":
                after_closer = False
                case_stack[-1] = "in"
            elif case_stack and case_stack[-1] == "in":
                after_closer = False
                if not kw_quoted and word == "in":
                    case_stack[-1] = "pat_start"
            elif case_stack and case_stack[-1] in ("pat_start", "pat"):
                after_closer = False
                if (
                    not kw_quoted
                    and word == "esac"
                    and case_stack[-1] == "pat_start"
                ):
                    case_stack.pop()
                    after_closer = True
                else:
                    case_stack[-1] = "pat"
            elif for_hdr is not None:
                after_closer = False
                for_hdr, body_closer = _advance_for_hdr(
                    for_hdr, word, kw_quoted
                )
                if body_closer is not None:
                    cmd_pos = True
            elif (
                after_closer
                and not kw_quoted
                and word == "esac"
                and case_stack
            ):
                case_stack.pop()
                cmd_pos = False
                after_closer = True
            elif (
                after_closer
                and not kw_quoted
                and word in ("then", "do", "else", "elif")
            ):
                cmd_pos = True
                after_closer = False
            elif (
                after_closer
                and not kw_quoted
                and word in ("fi", "done", "}")
            ):
                cmd_pos = False
                after_closer = True
            elif cmd_pos and not kw_quoted:
                after_closer = False
                if after_time and word in ("-p", "--"):
                    if word == "--":
                        after_time = False
                elif after_coproc and (
                    word not in (
                        "[[", "function", "case", "for", "select", "esac",
                        "if", "while", "until", "{", "then", "do", "else",
                        "elif", "fi", "done", "}",
                    )
                    and not is_assign
                    and word.rsplit("/", 1)[-1] not in CMD_WRAPPERS
                    and _peek_next_is_compound_opener(c)
                ):
                    after_coproc = False
                else:
                    after_time = False
                    after_coproc = False
                    if word == "[[":
                        in_bracket_test = True
                        cmd_pos = False
                    elif word == "function":
                        expect_func_name = True
                        cmd_pos = False
                    elif word == "case":
                        case_stack.append("word")
                        cmd_pos = False
                    elif word in ("for", "select"):
                        for_hdr = "var"
                        cmd_pos = False
                    elif word == "esac":
                        if case_stack:
                            case_stack.pop()
                        cmd_pos = False
                        after_closer = True
                    elif word in ("if", "while", "until", "{", "then", "do",
                                  "else", "elif"):
                        cmd_pos = True
                    elif word in ("fi", "done", "}"):
                        cmd_pos = False
                        after_closer = True
                    elif word == "time":
                        after_time = True
                    elif word == "coproc":
                        after_coproc = True
                    elif (
                        not is_assign
                        and word.rsplit("/", 1)[-1] not in CMD_WRAPPERS
                    ):
                        cmd_pos = False
            else:
                after_closer = False
                cmd_pos = False
        tokens.append(
            Tok(
                "WORD",
                word,
                kw_quoted,
                tuple(sorted(word_lines)),
                tuple(word_subs),
                is_assign,
            )
        )
    if out_pending_hd is not None and (inherited_hd or pending_hd):
        out_pending_hd.extend(inherited_hd)
        out_pending_hd.extend(pending_hd)
    return tokens


def _check_tokens(
    relpath: str,
    raw_lines: list[str],
    tokens: list[Tok],
    *,
    initial_piped: bool = False,
    matched_allowlist: set[tuple[str, str]] | None = None,
) -> str | None:
    cmd_pos = True
    pipe_rhs = False
    pipe_after_bar = False
    after_redir = False
    after_closer = False
    for_hdr: str | None = None
    in_bracket_test = False
    wrapper_active = False
    expect_func_name = False
    after_time = False
    after_coproc = False
    in_grep_cmd = False
    grep_lines: set[int] = set()
    scopes: list[tuple[str, bool]] = [(">(", True)] if initial_piped else []
    case_stack: list[str] = []

    def is_piped() -> bool:
        return pipe_rhs or any(p for _, p in scopes)

    def flush_grep() -> str | None:
        nonlocal in_grep_cmd
        if not in_grep_cmd:
            return None
        for ln in sorted(grep_lines):
            trimmed = raw_lines[ln - 1].strip()
            entry = (relpath, trimmed)
            if entry not in ALLOWLIST:
                return (
                    f"error: {relpath}:{ln}: piped grep is disallowed "
                    f"(avoid -q/--quiet/--silent, read from a file, or audit)"
                )
            if matched_allowlist is not None:
                matched_allowlist.add(entry)
        in_grep_cmd = False
        grep_lines.clear()
        return None

    idx = 0
    while idx < len(tokens):
        tok = tokens[idx]
        if in_grep_cmd:
            if tok.kind in ("PIPE", "SEP", "NEWLINE") or (
                tok.kind == "OP" and tok.val == ")"
            ):
                if tok.kind == "SEP" and tok.val == ";":
                    grep_lines.update(tok.lines)
                err = flush_grep()
                if err:
                    return err
            else:
                grep_lines.update(tok.lines)

        if tok.kind not in ("NEWLINE", "PIPE"):
            pipe_after_bar = False

        # Evaluate subshells attached to this token in its enclosing pipe state
        # before NEWLINE / after_redir / test brackets reset or skip state.
        for sub_toks, force_piped in tok.subshells:
            err = _check_tokens(
                relpath,
                raw_lines,
                sub_toks,
                initial_piped=force_piped or is_piped(),
                matched_allowlist=matched_allowlist,
            )
            if err:
                return err

        if in_bracket_test:
            if tok.kind == "WORD" and not tok.quoted and tok.val == "]]":
                in_bracket_test = False
                cmd_pos = False
                after_closer = True
            idx += 1
            continue

        if tok.kind == "NEWLINE":
            if pipe_rhs and pipe_after_bar:
                cmd_pos = True
            else:
                pipe_rhs = False
                pipe_after_bar = False
                cmd_pos = True
                if for_hdr == "in_list":
                    for_hdr = "sep_do"
                if for_hdr is not None:
                    cmd_pos = False
                wrapper_active = False
            after_redir = False
            after_closer = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        if tok.kind == "PIPE":
            if case_stack and case_stack[-1] in ("pat_start", "pat"):
                case_stack[-1] = "pat"
                idx += 1
                continue
            pipe_rhs = True
            pipe_after_bar = True
            cmd_pos = True
            after_redir = False
            after_closer = False
            wrapper_active = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        if tok.kind == "SEP":
            if tok.val in CASE_ARMS and case_stack:
                case_stack[-1] = "pat_start"
                cmd_pos = False
            elif tok.val == ";" and for_hdr in (
                "after_var", "in_list", "sep_do"
            ):
                for_hdr = "sep_do"
                cmd_pos = False
            else:
                cmd_pos = True
                for_hdr = None
            pipe_rhs = False
            after_redir = False
            after_closer = False
            wrapper_active = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        if tok.kind == "REDIR":
            after_redir = True
            idx += 1
            continue

        if tok.kind == "OP" and tok.val == "(":
            if case_stack and case_stack[-1] in ("pat_start", "pat"):
                case_stack[-1] = "pat"
                idx += 1
                continue
            if (
                idx + 1 < len(tokens)
                and tokens[idx + 1].kind == "OP"
                and tokens[idx + 1].val == ")"
            ):
                cmd_pos = True
                after_redir = False
                after_closer = False
                wrapper_active = False
                expect_func_name = False
                idx += 2
                continue
            scopes.append((")", is_piped()))
            pipe_rhs = False
            cmd_pos = True
            after_redir = False
            after_closer = False
            wrapper_active = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        if tok.kind == "OP" and tok.val == ")":
            if case_stack and case_stack[-1] in ("pat_start", "pat"):
                case_stack[-1] = "body"
                cmd_pos = True
                pipe_rhs = False
                after_closer = False
                expect_func_name = False
                after_time = False
                after_coproc = False
                idx += 1
                continue
            popped_p = False
            if scopes and scopes[-1][0] == ")":
                _, popped_p = scopes.pop()
            cmd_pos = False
            after_closer = True
            pipe_rhs = popped_p
            after_redir = False
            wrapper_active = False
            expect_func_name = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        # WORD
        w = tok.val

        if after_redir:
            after_redir = False
            idx += 1
            continue

        if expect_func_name:
            expect_func_name = False
            cmd_pos = True
            idx += 1
            continue

        if case_stack and case_stack[-1] == "word":
            case_stack[-1] = "in"
            idx += 1
            continue

        if case_stack and case_stack[-1] == "in":
            if not tok.quoted and w == "in":
                case_stack[-1] = "pat_start"
            idx += 1
            continue

        if case_stack and case_stack[-1] in ("pat_start", "pat"):
            if (
                not tok.quoted
                and w == "esac"
                and case_stack[-1] == "pat_start"
            ):
                case_stack.pop()
                popped_p = False
                if scopes and scopes[-1][0] == "esac":
                    _, popped_p = scopes.pop()
                cmd_pos = False
                after_closer = True
                pipe_rhs = popped_p
            else:
                case_stack[-1] = "pat"
                after_closer = False
            idx += 1
            continue

        if for_hdr is not None:
            for_hdr, body_closer = _advance_for_hdr(for_hdr, w, tok.quoted)
            if body_closer is not None:
                if scopes and scopes[-1][0] == "done":
                    scopes[-1] = (body_closer, scopes[-1][1])
                cmd_pos = True
                pipe_rhs = False
            after_closer = False
            idx += 1
            continue

        if not tok.quoted and w == "(())":
            cmd_pos = False
            after_closer = True
            after_time = False
            after_coproc = False
            idx += 1
            continue

        if (
            not tok.quoted
            and w in CLOSERS
            and (
                cmd_pos
                or (after_closer and scopes and scopes[-1][0] == w)
            )
        ):
            if w == "esac" and case_stack:
                case_stack.pop()
            popped_p = False
            if any(end_w == w for end_w, _ in scopes):
                while scopes:
                    end_w, p = scopes.pop()
                    if end_w == w:
                        popped_p = p
                        break
            cmd_pos = False
            after_closer = True
            pipe_rhs = popped_p
            wrapper_active = False
            after_time = False
            after_coproc = False
            idx += 1
            continue

        was_after_closer = after_closer
        after_closer = False
        if (
            (cmd_pos or was_after_closer)
            and not tok.quoted
            and w in STAGE_KW_RESET
        ):
            cmd_pos = True
            pipe_rhs = False
            wrapper_active = False
            after_time = False
            after_coproc = False
            idx += 1
            continue
        if cmd_pos and not tok.quoted:
            if w == "[[":
                in_bracket_test = True
                cmd_pos = False
                after_time = False
                after_coproc = False
                idx += 1
                continue
            if w == "function":
                expect_func_name = True
                cmd_pos = False
                after_time = False
                after_coproc = False
                idx += 1
                continue
            if w in OPENERS:
                scopes.append((OPENERS[w], is_piped()))
                pipe_rhs = False
                wrapper_active = False
                after_time = False
                after_coproc = False
                if w == "case":
                    case_stack.append("word")
                    cmd_pos = False
                elif w in ("for", "select"):
                    for_hdr = "var"
                    cmd_pos = False
                else:
                    cmd_pos = True
                idx += 1
                continue

        base = w.rsplit("/", 1)[-1]
        if cmd_pos:
            if tok.is_assign:
                idx += 1
                continue
            if not tok.quoted and after_time and w in ("-p", "--"):
                if w == "--":
                    after_time = False
                idx += 1
                continue
            if not tok.quoted and after_coproc:
                after_coproc = False
                if (
                    w not in OPENERS
                    and w not in CLOSERS
                    and w not in STAGE_KW_RESET
                    and w not in ("[[", "(())", "function")
                    and not tok.is_assign
                    and base not in CMD_WRAPPERS
                ):
                    nxt_tok = (
                        tokens[idx + 1] if idx + 1 < len(tokens) else None
                    )
                    if nxt_tok is not None and not nxt_tok.quoted and (
                        (nxt_tok.kind == "OP" and nxt_tok.val == "(")
                        or (
                            nxt_tok.kind == "WORD"
                            and (
                                nxt_tok.val in OPENERS
                                or nxt_tok.val in ("[[", "(())")
                            )
                        )
                    ):
                        wrapper_active = False
                        idx += 1
                        continue
            after_time = False
            after_coproc = False
            if base in CMD_WRAPPERS:
                wrapper_active = True
                if not tok.quoted and w == "time":
                    after_time = True
                elif not tok.quoted and w == "coproc":
                    after_coproc = True
                idx += 1
                continue
        else:
            after_time = False
            after_coproc = False

        if GREP_RE.match(base) and (cmd_pos or wrapper_active):
            if is_piped():
                in_grep_cmd = True
                grep_lines.update(tok.lines)
        cmd_pos = False
        idx += 1

    err = flush_grep()
    if err:
        return err
    return None


matched_all: set[tuple[str, str]] = set()
scanned_files = set(sys.argv[1:])
for relpath in sys.argv[1:]:
    text = Path(relpath).read_text(encoding="utf-8")
    raw_lines = text.split("\n")
    try:
        toks = tokenize(Cursor(text))
        err = _check_tokens(
            relpath, raw_lines, toks, matched_allowlist=matched_all
        )
    except ValueError as exc:
        err = f"error: {relpath}: {exc}"
    if err:
        print(err, file=sys.stderr)
        sys.exit(1)
    canary = text + ("\n" if text and not text.endswith("\n") else "")
    canary += "x | grep -q y\n"
    try:
        c_toks = tokenize(Cursor(canary))
        c_err = _check_tokens(relpath, canary.split("\n"), c_toks)
    except ValueError as exc:
        c_err = f"error: {relpath}: {exc}"
    if c_err is None:
        print(
            f"error: {relpath}: self-canary failed (blind tail state)",
            file=sys.stderr,
        )
        sys.exit(1)

stale_entries = sorted(ALLOWLIST - matched_all)
if stale_entries:
    fname, line_text = stale_entries[0]
    reason = (
        "file not scanned"
        if fname not in scanned_files
        else "line not matched"
    )
    print(
        f"error: {fname}: stale ALLOWLIST entry ({reason}): {line_text!r}",
        file=sys.stderr,
    )
    sys.exit(1)
PY

# Verify that `githooks/pre-push` invokes every top-level check script in `ci/`
# and `zerocopy/ci/` (excluding release, formatting-delegate, todo, and heavy
# packaging scripts), plus waits for `./ci/test_shell_and_hooks.py`.
shopt -s extglob nullglob
GLOBIGNORE="./*/@(release_crate_version|check_todo).sh"
for f in ./ci/*.sh ./ci/*.py; do
  if ! grep -F "$f" githooks/pre-push >/dev/null; then
    echo "$f not called from githooks/pre-push" >&2
    exit 1
  fi
done
GLOBIGNORE="./zerocopy/ci/@(release_crate_version|check_fmt|check_packaging).sh"
for f in ./zerocopy/ci/*; do
  if ! grep -F "$f" githooks/pre-push >/dev/null; then
    echo "$f not called from githooks/pre-push" >&2
    exit 1
  fi
done
unset GLOBIGNORE
shopt -u extglob nullglob
if ! grep -F 'wait $SHELL_HOOKS_TEST_PID' githooks/pre-push >/dev/null; then
  echo "githooks/pre-push must wait for SHELL_HOOKS_TEST_PID" >&2
  exit 1
fi
