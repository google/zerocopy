# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""A Lean 4 lexer that separates code from comments and strings."""

from __future__ import annotations

from pathlib import Path

from .common import CHAR_LITERAL_RE, Token, VerificationError


def _is_lean_id_start(ch: str) -> bool:
    if ch == "_":
        return True
    if ch in ("«", "»", "⟨", "⟩"):
        return False
    return (
        ("a" <= ch <= "z")
        or ("A" <= ch <= "Z")
        or (ord(ch) >= 0x80 and ch.isalpha())
    )


def _is_lean_id_part(ch: str) -> bool:
    if _is_lean_id_start(ch):
        return True
    return (
        ("0" <= ch <= "9")
        or ch in ("'", "?", "!")
        or (ord(ch) >= 0x80 and ch.isalnum())
    )


class _LeanLexer:
    """Comment- and string-aware Lean 4 tokenizer.

    Handles:
      - Line comments (`-- ...`)
      - Nested block comments and docstrings (`/- ... -/`, `/-- ... -/`,
        `/-! ... -/`)
      - Standard string literals (`"..."`) with Lean escape sequences
      - Raw string literals (`r"..."`, `r#"..."#`, `r##"..."##`, ...)
      - Interpolated string literals (`s!"..."`, `m!"..."`, `f!"..."`,
        `println!"..."`, plus Lean whitespace/newlines/comments after `!` and
        raw `s! r#"..."#` forms), lexing embedded `{ ... }` expressions as real
        Lean code tokens
      - Character literals (`'a'`, `'\\n'`, ...) without colliding with primed
        identifiers (`x'`, `m'`)
      - Escaped French-quote identifiers (`«...»`)
    """

    def __init__(self, source: str, path: str) -> None:
        self.src = source
        self.n = len(source)
        self.path = path
        self.pos = 0
        self.line = 1
        self.col = 1
        self.tokens: list[Token] = []

    def _advance(self, count: int = 1) -> str:
        out = self.src[self.pos : self.pos + count]
        for ch in out:
            if ch == "\n":
                self.line += 1
                self.col = 1
            else:
                self.col += 1
        self.pos += count
        return out

    def _skip_line_comment(self) -> None:
        self._advance(2)
        while self.pos < self.n and self.src[self.pos] != "\n":
            self._advance(1)

    def _skip_block_comment(self) -> None:
        start_line, start_col = self.line, self.col
        self._advance(2)  # consume `/-`
        depth = 1
        while self.pos < self.n and depth > 0:
            two = self.src[self.pos : self.pos + 2]
            if two == "/-":
                depth += 1
                self._advance(2)
            elif two == "-/":
                depth -= 1
                self._advance(2)
            else:
                self._advance(1)
        if depth != 0:
            raise VerificationError(
                f"{self.path}:{start_line}:{start_col}: "
                "unterminated block comment"
            )

    def _decode_escape(self, start_line: int, start_col: int) -> str:
        # Caller is positioned at `\`
        self._advance(1)
        if self.pos >= self.n:
            raise VerificationError(
                f"{self.path}:{start_line}:{start_col}: "
                "unterminated escape sequence"
            )
        esc = self.src[self.pos]
        if esc == "\\":
            self._advance(1)
            return "\\"
        if esc == '"':
            self._advance(1)
            return '"'
        if esc == "'":
            self._advance(1)
            return "'"
        if esc == "n":
            self._advance(1)
            return "\n"
        if esc == "r":
            self._advance(1)
            return "\r"
        if esc == "t":
            self._advance(1)
            return "\t"
        if esc in ("\n", "\r"):
            # Lean 4 string line continuation: `\<newline>[ \t]*`
            if esc == "\r" and self.src[self.pos : self.pos + 2] == "\r\n":
                self._advance(2)
            else:
                self._advance(1)
            while self.pos < self.n and self.src[self.pos] in (" ", "\t"):
                self._advance(1)
            return ""
        if esc == "x":
            hex_digits = self.src[self.pos + 1 : self.pos + 3]
            if len(hex_digits) == 2 and all(
                c in "0123456789abcdefABCDEF" for c in hex_digits
            ):
                self._advance(3)
                return chr(int(hex_digits, 16))
            raise VerificationError(
                f"{self.path}:{self.line}:{self.col}: "
                "invalid \\x escape in string"
            )
        if esc == "u":
            hex_digits = self.src[self.pos + 1 : self.pos + 5]
            if len(hex_digits) == 4 and all(
                c in "0123456789abcdefABCDEF" for c in hex_digits
            ):
                self._advance(5)
                return chr(int(hex_digits, 16))
            raise VerificationError(
                f"{self.path}:{self.line}:{self.col}: "
                "invalid \\u escape in string"
            )
        raise VerificationError(
            f"{self.path}:{self.line}:{self.col}: unrecognized escape \\{esc}"
        )

    def _lex_string(self) -> None:
        start_line, start_col = self.line, self.col
        self._advance(1)  # opening `"`
        chars: list[str] = []
        while self.pos < self.n:
            ch = self.src[self.pos]
            if ch == '"':
                self._advance(1)
                self.tokens.append(
                    Token("STRING", "".join(chars), start_line, start_col)
                )
                return
            if ch == "\\":
                chars.append(self._decode_escape(start_line, start_col))
            else:
                chars.append(self._advance(1))
        raise VerificationError(
            f"{self.path}:{start_line}:{start_col}: unterminated string literal"
        )

    def _lex_raw_string(self, hash_count: int) -> None:
        start_line, start_col = self.line, self.col
        self._advance(1 + hash_count + 1)  # `r` + `#` * k + `"`
        closing = '"' + ("#" * hash_count)
        chars: list[str] = []
        while self.pos < self.n:
            if self.src.startswith(closing, self.pos):
                self._advance(len(closing))
                self.tokens.append(
                    Token("STRING", "".join(chars), start_line, start_col)
                )
                return
            chars.append(self._advance(1))
        raise VerificationError(
            f"{self.path}:{start_line}:{start_col}: "
            "unterminated raw string literal"
        )

    def _skip_ws_and_comments_at(self, idx: int) -> int | None:
        """Advance past Lean whitespace, `--` comments, and nested `/- ... -/`.

        Returns `None` if an unterminated block comment is encountered, leaving
        `_lex_one` to diagnose it at its exact start line and column.
        """
        while idx < self.n:
            if self.src[idx].isspace():
                idx += 1
                continue
            two = self.src[idx : idx + 2]
            if two == "--":
                idx += 2
                while idx < self.n and self.src[idx] != "\n":
                    idx += 1
                continue
            if two == "/-":
                idx += 2
                depth = 1
                while idx < self.n and depth > 0:
                    pair = self.src[idx : idx + 2]
                    if pair == "/-":
                        depth += 1
                        idx += 2
                    elif pair == "-/":
                        depth -= 1
                        idx += 2
                    else:
                        idx += 1
                if depth != 0:
                    return None
                continue
            break
        return idx

    def _match_interpolated_prefix(self) -> tuple[int, int | None] | None:
        """Match `(s|m|f|println)![<ws_or_comment>]*(" | r#*")`.

        Returns `(prefix_len_through_open_quote, raw_hash_count_or_None)`.
        """
        matched_kw: str | None = None
        for kw in ("s!", "m!", "f!", "println!"):
            if self.src.startswith(kw, self.pos):
                matched_kw = kw
                break
        if matched_kw is None:
            return None
        j = self.pos + len(matched_kw)
        # If immediately followed by an identifier continuation other than `r`
        # starting a raw string (e.g. `s!foo`), let identifier lexing handle it.
        if j < self.n and _is_lean_id_part(self.src[j]):
            if self.src[j] == "r":
                k = j + 1
                while k < self.n and self.src[k] == "#":
                    k += 1
                if k < self.n and self.src[k] == '"':
                    return (k + 1 - self.pos, k - (j + 1))
            return None
        next_j = self._skip_ws_and_comments_at(j)
        if next_j is None or next_j >= self.n:
            return None
        j = next_j
        if self.src[j] == '"':
            return (j + 1 - self.pos, None)
        if self.src[j] == "r":
            k = j + 1
            while k < self.n and self.src[k] == "#":
                k += 1
            if k < self.n and self.src[k] == '"':
                return (k + 1 - self.pos, k - (j + 1))
        return None

    def _lex_interpolated_string(
        self, prefix_len: int, raw_hashes: int | None
    ) -> None:
        start_line, start_col = self.line, self.col
        self._advance(prefix_len)
        closing = '"' if raw_hashes is None else ('"' + ("#" * raw_hashes))
        chars: list[str] = []
        while self.pos < self.n:
            if self.src.startswith(closing, self.pos):
                self._advance(len(closing))
                self.tokens.append(
                    Token("STRING", "".join(chars), start_line, start_col)
                )
                return
            ch = self.src[self.pos]
            if raw_hashes is None and ch == "\\":
                if self.pos + 1 < self.n and self.src[self.pos + 1] == "{":
                    self._advance(2)
                    chars.append("{")
                else:
                    chars.append(self._decode_escape(start_line, start_col))
            elif ch == "{":
                if raw_hashes is not None and (
                    self.pos + 1 < self.n and self.src[self.pos + 1] == "{"
                ):
                    self._advance(2)
                    chars.append("{")
                    continue
                if chars:
                    self.tokens.append(
                        Token("STRING", "".join(chars), start_line, start_col)
                    )
                    chars = []
                brace_line, brace_col = self.line, self.col
                self._advance(1)
                self.tokens.append(Token("PUNCT", "{", brace_line, brace_col))
                self._lex_until_matching_brace(brace_line, brace_col)
            else:
                chars.append(self._advance(1))
        raise VerificationError(
            f"{self.path}:{start_line}:{start_col}: "
            "unterminated interpolated string"
        )

    def _lex_until_matching_brace(self, open_line: int, open_col: int) -> None:
        depth = 1
        while self.pos < self.n and depth > 0:
            ch = self.src[self.pos]
            if ch == "}":
                line, col = self.line, self.col
                self._advance(1)
                self.tokens.append(Token("PUNCT", "}", line, col))
                depth -= 1
                continue
            if ch == "{":
                line, col = self.line, self.col
                self._advance(1)
                self.tokens.append(Token("PUNCT", "{", line, col))
                depth += 1
                continue
            self._lex_one()
        if depth != 0:
            raise VerificationError(
                f"{self.path}:{open_line}:{open_col}: "
                "unterminated interpolation `{` in string"
            )

    def _match_raw_string_prefix(self) -> int | None:
        if self.src[self.pos] != "r":
            return None
        j = self.pos + 1
        while j < self.n and self.src[j] == "#":
            j += 1
        if j < self.n and self.src[j] == '"':
            return j - (self.pos + 1)
        return None

    def _lex_one(self) -> None:
        ch = self.src[self.pos]
        if ch.isspace():
            self._advance(1)
            return

        two = self.src[self.pos : self.pos + 2]
        if two == "--":
            self._skip_line_comment()
            return
        if two == "/-":
            self._skip_block_comment()
            return

        # Interpolated strings: `s!"..."`, `s! "..."`, `s! r#"..."#`, etc.
        interp = self._match_interpolated_prefix()
        if interp is not None:
            prefix_len, raw_hashes = interp
            self._lex_interpolated_string(prefix_len, raw_hashes)
            return

        # Raw strings: `r"..."`, `r#"..."#`, ...
        raw_hashes = self._match_raw_string_prefix()
        if raw_hashes is not None:
            self._lex_raw_string(raw_hashes)
            return

        if ch == '"':
            self._lex_string()
            return

        # Escaped French-quote identifier: `«...»`
        if ch == "«":
            start_line, start_col = self.line, self.col
            self._advance(1)
            ident_chars: list[str] = []
            while self.pos < self.n and self.src[self.pos] != "»":
                ident_chars.append(self._advance(1))
            if self.pos >= self.n:
                raise VerificationError(
                    f"{self.path}:{start_line}:{start_col}: "
                    "unterminated escaped identifier `«...»`"
                )
            self._advance(1)  # consume `»`
            self.tokens.append(
                Token("IDENT", "".join(ident_chars), start_line, start_col)
            )
            return

        # Character literal `'a'` / `'\n'` (only outside identifiers)
        if ch == "'":
            start_line, start_col = self.line, self.col
            match = CHAR_LITERAL_RE.match(self.src[self.pos :])
            if match:
                lit = self._advance(len(match.group(0)))
                self.tokens.append(Token("CHAR", lit, start_line, start_col))
            else:
                self._advance(1)
                self.tokens.append(Token("PUNCT", "'", start_line, start_col))
            return

        if _is_lean_id_start(ch):
            start_line, start_col = self.line, self.col
            start = self.pos
            self._advance(1)
            while self.pos < self.n and _is_lean_id_part(self.src[self.pos]):
                self._advance(1)
            self.tokens.append(
                Token("IDENT", self.src[start : self.pos], start_line, start_col)
            )
            return

        if "0" <= ch <= "9":
            start_line, start_col = self.line, self.col
            start = self.pos
            self._advance(1)
            while self.pos < self.n and (
                self.src[self.pos].isalnum() or self.src[self.pos] == "_"
            ):
                self._advance(1)
            self.tokens.append(
                Token("NUMBER", self.src[start : self.pos], start_line, start_col)
            )
            return

        start_line, start_col = self.line, self.col
        if two in (
            ":=",
            "++",
            "=>",
            "->",
            "<-",
            "::",
            "..",
            "==",
            "!=",
            "<=",
            ">=",
            "&&",
            "||",
        ):
            self._advance(2)
            self.tokens.append(Token("OP", two, start_line, start_col))
            return

        self._advance(1)
        self.tokens.append(Token("PUNCT", ch, start_line, start_col))

    def lex(self) -> list[Token]:
        while self.pos < self.n:
            self._lex_one()
        return self.tokens


def lex_lean(source: str, path: Path | str = "<input>") -> list[Token]:
    """Tokenize Lean 4 source code, skipping comments and decoding strings."""
    return _LeanLexer(source, str(path)).lex()
