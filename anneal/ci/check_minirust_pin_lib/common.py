# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Locked pin constants, shared types, and path and hashing helpers for
`check_minirust_pin.py`."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import stat
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
