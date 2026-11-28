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
from pathlib import Path
import sys

sys.dont_write_bytecode = True
_CI_DIR = str(Path(__file__).resolve().parent)
if _CI_DIR not in sys.path:
    sys.path.insert(0, _CI_DIR)

# The implementation lives in `check_minirust_pin_lib/`. Every name it
# defines is re-exported here, so callers and tests that import this module
# keep working.
from check_minirust_pin_lib.common import (  # noqa: E402, F401
    ALLOWED_CONSTRUCTIVE_AXIOMS, CHAR_LITERAL_RE, COMPILED_ARTIFACT_SUFFIXES,
    EXPECTED_UPSTREAM_REPO, FORBIDDEN_CODE_TOKENS, FORBIDDEN_IMPORT_PREFIXES,
    FORBIDDEN_VENDOR_FILENAMES, FORBIDDEN_VENDOR_NAMES, HEX40_RE, HEX64_RE,
    LEAN_COMMAND_STARTERS, LOCKED_MINIRUST_COMMIT, LOCKED_MINIRUST_FILE_COUNT,
    LOCKED_MINIRUST_MANIFEST_SHA256, LOCKED_MINIRUST_TARBALL_SHA256,
    LOCKED_SPEC_ANCHOR_COUNT, MAX_LEAN_LINES, PIN_FILENAME,
    REQUIRED_EXPORTED_THEOREMS, SpecAnchor, Token, VerificationError,
    _compute_manifest_sha256, _no_duplicate_json_keys, _require_regular_file,
    _resolve_regular_dir, _sha256_file, _validate_clean_rel_path, _walk_error,
    _walk_non_symlink_dirs,
)
from check_minirust_pin_lib.vendor_pin import (  # noqa: E402, F401
    verify_vendor_pin,
)
from check_minirust_pin_lib.lean_lexer import (  # noqa: E402, F401
    _LeanLexer, _is_lean_id_part, _is_lean_id_start, lex_lean,
)
from check_minirust_pin_lib.lean_hygiene import (  # noqa: E402, F401
    _is_compiled_artifact, _is_forbidden_import, _read_dotted_ident,
    _scan_lean_declarations, check_lean_file_hygiene, extract_declared_symbols,
    extract_exported_theorems, verify_lean_hygiene,
)
from check_minirust_pin_lib.spec_anchors import (  # noqa: E402, F401
    EXPECTED_ANCHOR_FIELDS, _eval_string_expr, _find_matching_delim,
    _parse_record_fields, collect_minirust_declared_symbols, parse_spec_anchors,
    verify_spec_anchors,
)
from check_minirust_pin_lib.axioms import (  # noqa: E402, F401
    _DEPENDS_ON_AXIOMS_RE, _DEPENDS_ON_AXIOMS_START_RE, _NO_AXIOMS_RE,
    _has_path_separator, _resolve_lean_command, _resolve_lean_spec,
    parse_print_axioms_output, verify_axioms,
)


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
