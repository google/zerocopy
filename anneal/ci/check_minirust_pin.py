# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify the vendored MiniRust specification pin, Lean hygiene, spec anchors,
and constructive axiom footprint.

Checks:
  1. Vendor pin (always on in Tier-0 CI): verifies
     `vendor/minirust/UPSTREAM_PIN.json` against `LOCKED_MINIRUST_COMMIT`,
     `LOCKED_MINIRUST_TARBALL_SHA256`, `LOCKED_MINIRUST_FILE_COUNT`, and
     `LOCKED_MINIRUST_MANIFEST_SHA256`,
     ensures every pinned file exists as a regular non-symlink file with an
     exact SHA-256 match, and rejects unpinned files, stray directories,
     symlinks, special files, or ambient build/toolchain/VCS files in
     `vendor/minirust/`.
  2. Lean module hygiene (`--check-lean`, run in Tier-0 CI): scans
     `correspondence/Anneal/MiniRust/**/*.lean` and
     `correspondence/Anneal/MiniRustProof.lean`, enforcing `<= 3,500` lines per
     file, zero symlinks, zero compiled `.olean`/`.ilean` artifacts, zero
     imports of `Miri`, `Trusted.Correspondence`, `Anneal.MirCorrespondence*`,
     or `Anneal.MirWp`, zero forbidden proof-escape tokens (`sorry`, `sorryAx`,
     `admit`, `native_decide`, `unsafe`, `partial`, `axiom`) outside
     comments/strings, and presence of `REQUIRED_EXPORTED_THEOREMS` in
     `MiniRustProof.lean`.
  3. Spec-anchor verification (`--check-anchors`, run in Tier-0 CI): parses
     `SpecAnchor` records from `correspondence/Anneal/MiniRust/Anchors.lean`,
     rejects `⟨...⟩` / `where` / `SpecAnchor.mk` constructor forms, asserts the
     locked anchor count (`58`), verifies every `leanSymbol` resolves to a
     declared symbol across `Anneal/MiniRust/*.lean` (excluding `Anchors.lean`),
     and confirms each `specFile` is pinned in `UPSTREAM_PIN.json` and each
     `excerpt` occurs verbatim inside `vendor/minirust/<specFile>`.
  4. Constructive axiom check (`--check-axioms`, local/manual verification mode
     requiring prebuilt `.olean` artifacts via `--stage-dir` or `LEAN_PATH`):
     runs Lean on an ephemeral temporary probe importing `Anneal.MiniRustProof`
     with `#print axioms` on every exported top-level theorem, rejecting any
     axiom outside `{propext, Quot.sound}`. Note: `anneal-audit`'s
     correspondence stage kernel-replays all `correspondence/` modules in a
     sandbox while permitting `Classical.choice` for `vendor/lean-miri`;
     `--check-axioms` is a stricter local/manual check for `{propext,
     Quot.sound}` purity.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from typing import Any


EXPECTED_UPSTREAM_REPO = "https://github.com/minirust/minirust"
LOCKED_MINIRUST_COMMIT = "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed"
LOCKED_MINIRUST_TARBALL_SHA256 = (
    "0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0"
)
LOCKED_MINIRUST_FILE_COUNT = 30
LOCKED_MINIRUST_MANIFEST_SHA256 = (
    "1d32e2b77d4d4fdd34f49b4f987f8e34b62eb691d6b04bb17f8d3d652cd60a18"
)
LOCKED_SPEC_ANCHOR_COUNT = 58
PIN_FILENAME = "UPSTREAM_PIN.json"
MAX_LEAN_LINES = 3500

ALLOWED_CONSTRUCTIVE_AXIOMS = frozenset({"propext", "Quot.sound"})

FORBIDDEN_VENDOR_NAMES = frozenset(
    {
        "cargo.toml",
        "cargo.lock",
        "rust-toolchain.toml",
        "rust-toolchain",
        ".cargo",
        "lean-toolchain",
        "lakefile",
        "lakefile.lean",
        "lakefile.toml",
        ".gitattributes",
        "build.rs",
        ".envrc",
    }
)
FORBIDDEN_VENDOR_FILENAMES = FORBIDDEN_VENDOR_NAMES

FORBIDDEN_IMPORT_PREFIXES = (
    "Miri",
    "Trusted.Correspondence",
    "Anneal.MirCorrespondence",
    "Anneal.MirCorrespondenceProof",
    "Anneal.MirWp",
)

FORBIDDEN_CODE_TOKENS = frozenset(
    {
        "sorry",
        "sorryAx",
        "admit",
        "native_decide",
        "unsafe",
        "partial",
        "axiom",
    }
)

REQUIRED_EXPORTED_THEOREMS = (
    "Anneal.MiniRustProof.minirust_forward_sim_holds",
    "Anneal.MiniRustProof.minirust_bi_fault_equiv_holds",
    "Anneal.MiniRustProof.minirust_admitted_prog_wellFormed",
    "Anneal.MiniRustProof.minirust_admitted_never_illFormed",
    "Anneal.MiniRustProof.minirust_forward_no_unsupported",
    "Anneal.MiniRustProof.minirust_forward_behavior",
    "Anneal.MiniRustProof.minirust_forward_ub_contrapositive",
    "Anneal.MiniRustProof.minirust_forward_wellFormed_no_ub",
    "Anneal.MiniRustProof.minirust_forward_diverges",
    "Anneal.MiniRustProof.minirust_exact_ub_iff",
    "Anneal.MiniRustProof.minirust_exact_behavior_iff",
    "Anneal.MiniRustProof.minirust_exact_diverges_iff",
    "Anneal.MiniRustProof.minirust_encode_decode_roundtrip",
    "Anneal.MiniRustProof.minirust_spec_anchors_nonempty",
    "Anneal.MiniRustProof.minirust_spec_anchors_count",
    "Anneal.MiniRustProof.witness_cast_i32_to_u64_holds",
    "Anneal.MiniRustProof.witness_cast_u8_to_char_holds",
    "Anneal.MiniRustProof.witness_char_niche_strictness_holds",
    "Anneal.MiniRustProof.witness_move_semantic_strictness_holds",
    "Anneal.MiniRustProof.witness_mr_bottom_of_stack_return_ub_holds",
)

COMPILED_ARTIFACT_SUFFIXES = (
    ".olean",
    ".olean.server",
    ".olean.private",
    ".ilean",
)

HEX40_RE = re.compile(r"^[0-9a-f]{40}$")
HEX64_RE = re.compile(r"^[0-9a-f]{64}$")

CHAR_LITERAL_RE = re.compile(
    r"^'(?:\\x[0-9a-fA-F]{2}|\\u[0-9a-fA-F]{4}|\\[\\'\"nrt]|[^'\\\r\n])'"
)

LEAN_COMMAND_STARTERS = frozenset(
    {
        "abbrev",
        "attribute",
        "axiom",
        "class",
        "def",
        "deriving",
        "end",
        "example",
        "export",
        "import",
        "inductive",
        "instance",
        "lemma",
        "local",
        "macro",
        "meta",
        "module",
        "mutual",
        "namespace",
        "noncomputable",
        "opaque",
        "open",
        "partial",
        "prelude",
        "private",
        "protected",
        "public",
        "scoped",
        "section",
        "set_option",
        "structure",
        "syntax",
        "theorem",
        "universe",
        "unsafe",
        "variable",
    }
)


class VerificationError(RuntimeError):
    """Raised when any MiniRust pin, hygiene, anchor, or axiom check fails."""


@dataclass(frozen=True)
class Token:
    """A single lexical token from a Lean 4 source file."""

    kind: str  # "IDENT", "STRING", "CHAR", "NUMBER", "OP", "PUNCT"
    value: str
    line: int
    col: int


@dataclass(frozen=True)
class SpecAnchor:
    """A structured MiniRust specification anchor parsed from `Anchors.lean`."""

    anchor_id: str
    lean_symbol: str
    spec_file: str
    excerpt: str
    line: int


def _resolve_regular_dir(path: Path, label: str) -> Path:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise VerificationError(
            f"{label} must exist as a regular directory: {path} ({exc})"
        ) from exc
    if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
        raise VerificationError(f"{label} must be a regular directory: {path}")
    return path.resolve(strict=True)


def _walk_non_symlink_dirs(base: Path, rel_parts: tuple[str, ...]) -> Path:
    cur = base
    for part in rel_parts:
        if part in ("", ".", ".."):
            raise VerificationError(f"invalid relative path segment: {part!r}")
        cur = cur / part
        try:
            mode = cur.lstat().st_mode
        except OSError as exc:
            raise VerificationError(
                f"expected regular directory: {cur} ({exc})"
            ) from exc
        if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
            raise VerificationError(f"expected regular directory: {cur}")
    return cur.resolve(strict=True)


def _require_regular_file(path: Path, label: str) -> Path:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise VerificationError(
            f"{label} must exist as a regular file: {path} ({exc})"
        ) from exc
    if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
        raise VerificationError(f"{label} must be a regular file: {path}")
    return path


def _walk_error(exc: OSError) -> None:
    raise VerificationError(f"cannot traverse directory: {exc}") from exc


def _sha256_file(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        while True:
            chunk = handle.read(65536)
            if not chunk:
                break
            hasher.update(chunk)
    return hasher.hexdigest()


def _validate_clean_rel_path(rel_path: Any, context: str) -> str:
    if not isinstance(rel_path, str) or not rel_path:
        raise VerificationError(f"{context}: path must be a non-empty string")
    if (
        rel_path.startswith("/")
        or "\\" in rel_path
        or "\x00" in rel_path
        or "\n" in rel_path
        or "\r" in rel_path
    ):
        raise VerificationError(f"{context}: invalid relative path {rel_path!r}")
    parts = rel_path.split("/")
    for part in parts:
        if part in ("", ".", ".."):
            raise VerificationError(
                f"{context}: path contains forbidden segment {part!r}: "
                f"{rel_path!r}"
            )
        if part.lower() in FORBIDDEN_VENDOR_NAMES:
            raise VerificationError(
                f"{context}: forbidden ambient/build/toolchain name "
                f"{rel_path!r}"
            )
    if rel_path == PIN_FILENAME:
        raise VerificationError(
            f"{context}: {PIN_FILENAME} must not appear in pinned files map"
        )
    return rel_path


def _compute_manifest_sha256(files_map: dict[str, str]) -> str:
    payload = "".join(
        f"{files_map[path]}  {path}\n" for path in sorted(files_map)
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _no_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for key, value in pairs:
        if key in out:
            raise ValueError(f"duplicate JSON key: {key!r}")
        out[key] = value
    return out


def verify_vendor_pin(
    repo_root: Path, *, enforce_locked_pin: bool = True
) -> dict[str, Any]:
    """Verify `vendor/minirust/UPSTREAM_PIN.json` and every file on disk."""
    real_root = _resolve_regular_dir(repo_root, "repo root")
    vendor_dir = _walk_non_symlink_dirs(real_root, ("vendor", "minirust"))
    pin_path = _require_regular_file(
        vendor_dir / PIN_FILENAME, f"vendor/minirust/{PIN_FILENAME}"
    )

    try:
        raw_pin = json.loads(
            pin_path.read_text(encoding="utf-8"),
            object_pairs_hook=_no_duplicate_json_keys,
        )
    except (
        OSError,
        UnicodeDecodeError,
        json.JSONDecodeError,
        ValueError,
    ) as exc:
        raise VerificationError(f"cannot parse {pin_path}: {exc}") from exc

    if not isinstance(raw_pin, dict):
        raise VerificationError(f"{pin_path}: top-level JSON must be an object")

    schema_ver = raw_pin.get("schema_version")
    if isinstance(schema_ver, bool) or schema_ver != 1:
        raise VerificationError(
            f"{pin_path}: schema_version must be 1, got {schema_ver!r}"
        )

    upstream_repo = raw_pin.get("upstream_repo")
    if upstream_repo != EXPECTED_UPSTREAM_REPO:
        raise VerificationError(
            f"{pin_path}: upstream_repo must be {EXPECTED_UPSTREAM_REPO!r}, "
            f"got {upstream_repo!r}"
        )

    commit = raw_pin.get("commit")
    if not isinstance(commit, str) or not HEX40_RE.match(commit):
        raise VerificationError(
            f"{pin_path}: commit must be a 40-char lowercase hex SHA, "
            f"got {commit!r}"
        )
    if enforce_locked_pin and commit != LOCKED_MINIRUST_COMMIT:
        raise VerificationError(
            f"{pin_path}: commit {commit!r} does not match "
            f"LOCKED_MINIRUST_COMMIT {LOCKED_MINIRUST_COMMIT!r}"
        )

    tarball_sha = raw_pin.get("tarball_sha256")
    if not isinstance(tarball_sha, str) or not HEX64_RE.match(tarball_sha):
        raise VerificationError(
            f"{pin_path}: tarball_sha256 must be a 64-char lowercase hex SHA, "
            f"got {tarball_sha!r}"
        )
    if enforce_locked_pin and tarball_sha != LOCKED_MINIRUST_TARBALL_SHA256:
        raise VerificationError(
            f"{pin_path}: tarball_sha256 {tarball_sha!r} does not match "
            "LOCKED_MINIRUST_TARBALL_SHA256 "
            f"{LOCKED_MINIRUST_TARBALL_SHA256!r}"
        )

    raw_files = raw_pin.get("files")
    if not isinstance(raw_files, dict) or not raw_files:
        raise VerificationError(
            f"{pin_path}: files must be a non-empty JSON object"
        )

    file_keys = list(raw_files.keys())
    if file_keys != sorted(file_keys):
        raise VerificationError(
            f"{pin_path}: files map keys must be sorted lexicographically"
        )

    pinned_files: dict[str, str] = {}
    allowed_dirs: set[str] = set()
    for rel_key, digest in raw_files.items():
        rel_path = _validate_clean_rel_path(rel_key, str(pin_path))
        if not isinstance(digest, str) or not HEX64_RE.match(digest):
            raise VerificationError(
                f"{pin_path}: invalid SHA-256 digest for {rel_path!r}: "
                f"{digest!r}"
            )
        pinned_files[rel_path] = digest
        parts = rel_path.split("/")
        for depth in range(1, len(parts)):
            allowed_dirs.add("/".join(parts[:depth]))

    if "file_count" not in raw_pin:
        raise VerificationError(f"{pin_path}: missing required key 'file_count'")
    fc = raw_pin["file_count"]
    if isinstance(fc, bool) or not isinstance(fc, int) or fc != len(pinned_files):
        raise VerificationError(
            f"{pin_path}: file_count ({fc!r}) does not match "
            f"len(files) ({len(pinned_files)})"
        )

    if "manifest_sha256" not in raw_pin:
        raise VerificationError(
            f"{pin_path}: missing required key 'manifest_sha256'"
        )
    expected_manifest = _compute_manifest_sha256(pinned_files)
    actual_manifest = raw_pin["manifest_sha256"]
    if actual_manifest != expected_manifest:
        raise VerificationError(
            f"{pin_path}: manifest_sha256 mismatch: "
            f"recorded {actual_manifest!r}, computed {expected_manifest!r}"
        )

    disk_files: set[str] = set()
    disk_dirs: set[str] = set()
    for dirpath, dirnames, filenames in os.walk(
        vendor_dir, followlinks=False, onerror=_walk_error
    ):
        base = Path(dirpath)
        for name in sorted(dirnames) + sorted(filenames):
            entry = base / name
            mode = entry.lstat().st_mode
            rel = entry.relative_to(vendor_dir).as_posix()
            if stat.S_ISLNK(mode):
                raise VerificationError(
                    f"symlink forbidden in vendor/minirust: {rel}"
                )
            if name.lower() in FORBIDDEN_VENDOR_NAMES:
                raise VerificationError(
                    "forbidden ambient/build/toolchain name in "
                    f"vendor/minirust: {rel}"
                )
            if stat.S_ISDIR(mode):
                disk_dirs.add(rel)
            elif stat.S_ISREG(mode):
                if rel != PIN_FILENAME:
                    disk_files.add(rel)
            else:
                raise VerificationError(
                    f"unexpected special file in vendor/minirust: {rel}"
                )

    extra_files = sorted(disk_files - set(pinned_files))
    if extra_files:
        raise VerificationError(
            "extra unpinned file(s) in vendor/minirust: "
            + ", ".join(extra_files)
        )

    missing_files = sorted(set(pinned_files) - disk_files)
    if missing_files:
        raise VerificationError(
            "missing pinned file(s) in vendor/minirust: "
            + ", ".join(missing_files)
        )

    stray_dirs = sorted(disk_dirs - allowed_dirs)
    if stray_dirs:
        raise VerificationError(
            "unpinned directory(ies) in vendor/minirust: "
            + ", ".join(stray_dirs)
        )

    for rel_path, expected_sha in pinned_files.items():
        parts = tuple(rel_path.split("/"))
        parent = _walk_non_symlink_dirs(vendor_dir, parts[:-1])
        leaf = _require_regular_file(parent / parts[-1], rel_path)
        actual_sha = _sha256_file(leaf)
        if actual_sha != expected_sha:
            raise VerificationError(
                f"SHA-256 mismatch for vendor/minirust/{rel_path}: "
                f"expected {expected_sha}, got {actual_sha}"
            )

    if enforce_locked_pin:
        if len(pinned_files) != LOCKED_MINIRUST_FILE_COUNT:
            raise VerificationError(
                f"{pin_path}: pinned file count {len(pinned_files)} does not "
                f"match LOCKED_MINIRUST_FILE_COUNT {LOCKED_MINIRUST_FILE_COUNT}"
            )
        if actual_manifest != LOCKED_MINIRUST_MANIFEST_SHA256:
            raise VerificationError(
                f"{pin_path}: manifest_sha256 {actual_manifest!r} does not "
                "match LOCKED_MINIRUST_MANIFEST_SHA256 "
                f"{LOCKED_MINIRUST_MANIFEST_SHA256!r}"
            )

    return raw_pin


# ---------------------------------------------------------------------------
# Comment- and string-aware Lean 4 lexer
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# Lean declaration and theorem extraction
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# Spec-anchor verification (`--check-anchors`)
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# Constructive axiom check (`--check-axioms`, local/manual mode)
# ---------------------------------------------------------------------------

_NO_AXIOMS_RE = re.compile(
    r"^'([^']+)'\s+does not depend on any axioms\s*$"
)
_DEPENDS_ON_AXIOMS_RE = re.compile(
    r"^'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]\s*$"
)
_DEPENDS_ON_AXIOMS_START_RE = re.compile(
    r"^'([^']+)'\s+depends on axioms:\s*\[(.*)$"
)


def parse_print_axioms_output(output: str) -> dict[str, list[str]]:
    """Parse Lean 4 `#print axioms` output (including multi-line lists)."""
    result: dict[str, list[str]] = {}
    lines = output.splitlines()
    idx = 0
    while idx < len(lines):
        line = lines[idx].strip()
        m_none = _NO_AXIOMS_RE.match(line)
        if m_none:
            result[m_none.group(1)] = []
            idx += 1
            continue
        m_one = _DEPENDS_ON_AXIOMS_RE.match(line)
        if m_one:
            name = m_one.group(1)
            body = m_one.group(2)
            result[name] = [a.strip() for a in body.split(",") if a.strip()]
            idx += 1
            continue
        m_start = _DEPENDS_ON_AXIOMS_START_RE.match(line)
        if m_start:
            name = m_start.group(1)
            acc = [m_start.group(2)]
            idx += 1
            closed = False
            while idx < len(lines):
                part = lines[idx].strip()
                idx += 1
                if "]" in part:
                    before, _ = part.split("]", 1)
                    acc.append(before)
                    closed = True
                    break
                acc.append(part)
            if not closed:
                raise VerificationError(
                    f"malformed `#print axioms` output for {name!r}: "
                    "missing `]`"
                )
            body = " ".join(acc)
            result[name] = [a.strip() for a in body.split(",") if a.strip()]
            continue
        idx += 1
    return result


def _has_path_separator(spec: str) -> bool:
    if "/" in spec or os.sep in spec:
        return True
    return os.altsep is not None and os.altsep in spec


def _resolve_lean_spec(
    raw: Path | str, label: str, path_env: str | None
) -> list[str]:
    spec = os.fspath(raw)
    if not spec:
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        )
    if not _has_path_separator(spec):
        which_hit = shutil.which(spec, path=path_env)
        if which_hit is None:
            raise VerificationError(
                f"{label} executable does not exist or is not executable: {raw}"
            )
        cand = Path(os.path.abspath(which_hit))
    else:
        cand = Path(os.path.abspath(spec))
    try:
        cand.lstat()
    except OSError as exc:
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        ) from exc
    if not cand.is_file() or not os.access(cand, os.X_OK):
        raise VerificationError(
            f"{label} executable does not exist or is not executable: {raw}"
        )
    return [str(cand)]


def _resolve_lean_command(
    lean_arg: Path | str | None, *, path_env: str | None = None
) -> list[str]:
    """Resolve the Lean executable from `--lean`, `ANNEAL_LEAN`, or `PATH`."""
    effective_path = (
        os.environ.get("PATH") if path_env is None else path_env
    )
    if lean_arg is not None:
        return _resolve_lean_spec(lean_arg, "--lean", effective_path)

    env_lean = os.environ.get("ANNEAL_LEAN")
    if env_lean:
        return _resolve_lean_spec(env_lean, "ANNEAL_LEAN", effective_path)

    which_lean = shutil.which("lean", path=effective_path)
    if which_lean:
        return _resolve_lean_spec(which_lean, "PATH lean", effective_path)

    raise VerificationError(
        "cannot locate a Lean executable; pass --lean <path> or set ANNEAL_LEAN"
    )


def verify_axioms(
    repo_root: Path,
    *,
    lean: Path | str | None = None,
    stage_dir: Path | None = None,
) -> dict[str, list[str]]:
    """Verify exported theorems in `Anneal.MiniRustProof` are constructive."""
    real_root = _resolve_regular_dir(repo_root, "repo root")
    anneal_dir = _walk_non_symlink_dirs(real_root, ("correspondence", "Anneal"))
    proof_file = _require_regular_file(
        anneal_dir / "MiniRustProof.lean",
        "correspondence/Anneal/MiniRustProof.lean",
    )

    theorems = extract_exported_theorems(
        proof_file.read_text(encoding="utf-8"), proof_file
    )
    if not theorems:
        raise VerificationError(
            f"{proof_file}: no exported top-level theorems found for axiom "
            "check"
        )

    env = os.environ.copy()
    for secret_var in (
        "ACTIONS_CACHE_URL",
        "ACTIONS_RESULTS_URL",
        "ACTIONS_RUNTIME_TOKEN",
        "ACTIONS_RUNTIME_URL",
        "ACTIONS_ID_TOKEN_REQUEST_URL",
        "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
        "GITHUB_TOKEN",
        "GH_TOKEN",
    ):
        env.pop(secret_var, None)
    if stage_dir is not None:
        real_stage = _resolve_regular_dir(stage_dir, "stage dir")
        existing = env.get("LEAN_PATH", "")
        env["LEAN_PATH"] = (
            f"{real_stage}{os.pathsep}{existing}"
            if existing
            else str(real_stage)
        )

    cmd_prefix = _resolve_lean_command(lean, path_env=env.get("PATH"))

    with tempfile.TemporaryDirectory(
        prefix="anneal-minirust-axioms-"
    ) as tmp_dir:
        probe_path = Path(tmp_dir) / "CheckMiniRustAxioms.lean"
        probe_lines = ["import Anneal.MiniRustProof"]
        probe_lines.extend(f"#print axioms {thm}" for thm in theorems)
        probe_path.write_text("\n".join(probe_lines) + "\n", encoding="utf-8")

        cmd = [
            *cmd_prefix,
            "-j1",
            "-DElab.async=false",
            "-Ddebug.skipKernelTC=false",
            str(probe_path),
        ]
        try:
            proc = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                env=env,
                timeout=120,
            )
        except subprocess.TimeoutExpired as exc:
            raise VerificationError(
                f"Lean axiom probe timed out after 120s: {cmd}"
            ) from exc

    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise VerificationError(
            f"Lean axiom probe failed (exit {proc.returncode}):\n{detail}"
        )

    combined = "\n".join(part for part in (proc.stdout, proc.stderr) if part)
    axioms_map = parse_print_axioms_output(combined)

    failures: list[str] = []
    for thm in theorems:
        if thm not in axioms_map:
            failures.append(
                f"theorem {thm!r} missing from `#print axioms` output"
            )
            continue
        disallowed = sorted(set(axioms_map[thm]) - ALLOWED_CONSTRUCTIVE_AXIOMS)
        if disallowed:
            failures.append(
                f"theorem {thm!r} uses disallowed axiom(s): "
                + ", ".join(disallowed)
            )

    if failures:
        raise VerificationError(
            "Constructive axiom check failed:\n  " + "\n  ".join(failures)
        )

    return {thm: axioms_map[thm] for thm in theorems}


# ---------------------------------------------------------------------------
# CLI entrypoint
# ---------------------------------------------------------------------------


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to the Anneal directory (default: parent of ci/).",
    )
    parser.add_argument(
        "--check-lean",
        action="store_true",
        help=(
            "Check Lean module hygiene in correspondence/Anneal/MiniRust/ "
            "and MiniRustProof.lean."
        ),
    )
    parser.add_argument(
        "--check-anchors",
        action="store_true",
        help=(
            "Verify SpecAnchor records in Anneal/MiniRust/Anchors.lean "
            "against Lean declarations and pinned spec files."
        ),
    )
    parser.add_argument(
        "--check-axioms",
        action="store_true",
        help=(
            "Local/manual mode: run Lean `#print axioms` on exported "
            "Anneal.MiniRustProof theorems against prebuilt .olean files."
        ),
    )
    parser.add_argument(
        "--lean",
        type=str,
        default=None,
        help="Optional explicit Lean executable path or name for --check-axioms.",
    )
    parser.add_argument(
        "--stage-dir",
        type=Path,
        default=None,
        help=(
            "Directory containing compiled .olean files (LEAN_PATH) for "
            "--check-axioms."
        ),
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)

    try:
        pin = verify_vendor_pin(args.repo_root)
        summary = [
            f"vendor-pin: OK ({len(pin['files'])} files at "
            f"{pin['commit'][:12]})"
        ]

        if args.check_lean:
            lean_files = verify_lean_hygiene(args.repo_root)
            summary.append(f"lean-hygiene: OK ({len(lean_files)} modules)")

        if args.check_anchors:
            anchors = verify_spec_anchors(args.repo_root, pin)
            summary.append(f"spec-anchors: OK ({len(anchors)} anchors)")

        if args.check_axioms:
            axioms = verify_axioms(
                args.repo_root, lean=args.lean, stage_dir=args.stage_dir
            )
            summary.append(
                f"axioms: OK ({len(axioms)} exported theorems, "
                "subset of {propext, Quot.sound})"
            )
    except VerificationError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1

    print(" | ".join(summary))
    return 0


if __name__ == "__main__":
    sys.exit(main())
