#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verify every Anneal proof unit under `zerocopy/proofs/` against `zerocopy/src/`."""

import argparse
import collections
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time
import tomllib

_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import anneal_ci_lib  # noqa: E402


VALID_SANDBOXES = anneal_ci_lib.VALID_SANDBOXES
ALLOWED_AXIOMS = frozenset({"propext"})
UNIT_THEOREM_V1 = "Trusted.MirSemantics.UnitTheorem"
# Profile v2 units are checked against `UnitTheoremV2`, whose semantics Pass 2
# does not relate to `lean-miri`. Their receipts must mark correspondence
# provenance inapplicable and disclose the Profile v2 semantics assumptions.
UNIT_THEOREM_V2 = "Trusted.MirSemantics.UnitTheoremV2"
PROFILE_CANONICAL_ROOTS = {
    1: UNIT_THEOREM_V1,
    2: UNIT_THEOREM_V2,
}
PROFILE_V1_ASSUMPTION = "experimental pointer-free MIR semantics"
PROFILE_V2_ASSUMPTION_PREFIX = "experimental Profile v2 MIR semantics"
PROFILE_V2_REQUIRED_ASSUMPTION_PHRASES = (
    "no aliasing model",
    "raw-pointer arguments are assumed to carry provenance",
    "including those of unsafe functions",
    "decode to a valid value of the pointee type",
)
BINDING_DIGEST_FIELDS = (
    ("requestSha256", "request_sha256"),
    ("captureSha256", "capture_sha256"),
    ("specificationManifestSha256", "specification_manifest_sha256"),
    ("modelManifestSha256", "model_manifest_sha256"),
)
DEFAULT_SPEC_DECL = "Spec.specs"
DEFAULT_PROOF_THM = "Proof.verify"
EXCLUDED_SRC_FILES = frozenset({"doctests.rs"})
VALID_COMPILATION_KEYS = frozenset({
    "source_root",
    "crate_root",
    "crate_name",
    "crate_type",
    "panic",
    "overflow_checks",
    "edition",
    "target",
    "cfg",
    "env",
    "source_files",
})
VALID_RECEIPT_CONFIGURATION_KEYS = frozenset({
    "crate_root",
    "crate_name",
    "crate_type",
    "panic",
    "edition",
    "target",
    "cfg",
    "env",
    "opt_level",
    "debug_assertions",
    "overflow_checks",
    "mir_preserve_ub",
    "pointer_bits",
    "endian",
    "declared_source_files",
})
VALID_REQUEST_KEYS = frozenset({
    "schema_version",
    "compilation",
    "scope",
    "proof",
})
VALID_PROOF_KEYS = frozenset({
    "source_root",
    "specification",
    "theorem",
    "sources",
})
VALID_PROOF_SOURCE_KEYS = frozenset({"module", "path", "role"})
VALID_CRATE_TYPES = frozenset({"lib", "bin"})
VALID_PANIC_STRATEGIES = frozenset({"unwind", "abort"})
SPEC_FILE_PATTERN = re.compile(r"^Spec[A-Za-z0-9_]*\.lean$")
_SHA256_HEX_RE = re.compile(r"\A[0-9a-f]{64}\Z")
PROVENANCE_V1_KEYS = frozenset({
    "schema_version",
    "upstream_repository",
    "upstream_commit",
    "upstream_lean_toolchain",
    "build_lean_toolchain",
    "upstream_pin_sha256",
    "sysroot_foundation_manifest_sha256",
    "patched_files",
    "minirust_upstream",
    "correspondence_adapters",
    "correspondence_proofs",
    "trusted_lean",
    "note",
})
MINIRUST_UPSTREAM_KEYS = frozenset({
    "upstream_repository",
    "upstream_commit",
    "upstream_pin_sha256",
    "tarball_sha256",
    "manifest_sha256",
    "file_count",
    "files",
})
PROVENANCE_V3_EXTRA_KEYS = frozenset({
    "claim_kind",
    "permitted_axioms",
    "model_system_relation",
    "tcb_shims",
    "taint_reasons",
    "qualifiers",
})
PROVENANCE_V3_KEYS = PROVENANCE_V1_KEYS | PROVENANCE_V3_EXTRA_KEYS
PATCHED_FILE_KEYS = frozenset({"path", "upstream_sha256", "patched_sha256"})
ALLOWED_FOUNDATION_AXIOMS = frozenset({
    "Classical.choice",
    "Quot.sound",
    "propext",
})
ALLOWED_CLAIM_KINDS = frozenset({
    "exact_refines",
    "sound_refines",
    "pure_spec_agreement",
})
ALLOWED_RELATION_KINDS = frozenset({
    "none",
    "embedding",
    "homomorphism",
    "abstraction",
    "simulation",
})
ALLOWED_RELATION_QUALIFIERS = frozenset({
    "lock_step",
    "wf_stutter",
    "stutter",
})
ALLOWED_RELATION_DIRECTIONS = frozenset({
    "forward",
    "backward",
    "bidirectional",
})
ALLOWED_CLAIM_SHAPES = frozenset({
    "exists_witness",
    "forall_safety",
    "general_hyper",
    "subset_hyper",
    "termination",
})
ALLOWED_SHIM_KINDS = frozenset({
    "capture_driver",
    "unpinned_lean",
    "upstream_bugfix_patch",
    "append_only_spec_lemma",
    "approved_opaque",
    "assumed_seam",
    "extern_ffi_axiom",
    "rustc_pass_shim",
})
ALLOWED_SHIM_STATUSES = frozenset({"proved", "tested", "assumed"})
ALLOWED_PROVENANCE_TAINTS = frozenset({
    "assumed_seams_present",
    "choice_total_false",
    "vendor_upstream_patches_present",
})
ALLOWED_PROVENANCE_SCOPES = frozenset({"full_gate", "partial_gate"})
VALID_MODEL_SYSTEM_RELATION_KEYS = frozenset({
    "kind",
    "qualifier",
    "direction",
    "anchored_at",
    "licensed_claim_shapes",
    "unmodeled_downstream",
})
VALID_TCB_SHIM_KEYS = frozenset({
    "id",
    "kind",
    "commit",
    "sha256",
    "status",
    "guards",
})
VALID_PROVENANCE_QUALIFIER_KEYS = frozenset({
    "choice_total",
    "assumed_seams",
    "scope_kind",
})


def _strip_lean_comments_and_strings(text):
    """Strip Lean line/block comments and string literals before parsing."""
    out = []
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch == "-" and i + 1 < n and text[i + 1] == "-":
            nl = text.find("\n", i)
            if nl < 0:
                break
            out.append("\n")
            i = nl + 1
        elif ch == "/" and i + 1 < n and text[i + 1] == "-":
            i += 2
            depth = 1
            while i < n and depth > 0:
                if text[i : i + 2] == "/-":
                    depth += 1
                    i += 2
                elif text[i : i + 2] == "-/":
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
            out.append(" ")
        elif ch == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append('""')
        elif ch == "'" and not (
            i > 0 and (text[i - 1].isalnum() or text[i - 1] in ("_", "'"))
        ):
            # Skip Lean Char literals (`'c'`, `'\c'`, `'\xHH'`, `'\uHHHH'`)
            # without touching identifier primes such as `x'`.
            if (
                i + 3 < n
                and text[i + 1] == "\\"
                and text[i + 2] != "\n"
                and text[i + 3] == "'"
            ):
                out.append("''")
                i += 4
            elif (
                i + 5 < n
                and text[i + 1 : i + 3] == "\\x"
                and all(c in "0123456789abcdefABCDEF" for c in text[i + 3 : i + 5])
                and text[i + 5] == "'"
            ):
                out.append("''")
                i += 6
            elif (
                i + 7 < n
                and text[i + 1 : i + 3] == "\\u"
                and all(c in "0123456789abcdefABCDEF" for c in text[i + 3 : i + 7])
                and text[i + 7] == "'"
            ):
                out.append("''")
                i += 8
            elif (
                i + 2 < n
                and text[i + 1] not in ("'", "\\", "\n")
                and text[i + 2] == "'"
            ):
                out.append("''")
                i += 3
            else:
                out.append(ch)
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def _find_specification_source(unit_dir, request):
    proof = request.get("proof")
    if not isinstance(proof, dict):
        raise RuntimeError(f"{unit_dir.name}: missing proof table")
    source_root = proof.get("source_root", ".")
    if (
        not isinstance(source_root, str)
        or not source_root
        or Path(source_root).is_absolute()
    ):
        raise RuntimeError(
            f"{unit_dir.name}: proof.source_root must be a relative path: "
            f"{source_root!r}"
        )
    proof_root = unit_dir / source_root
    sources = proof.get("sources")
    if not isinstance(sources, list) or not sources:
        raise RuntimeError(f"{unit_dir.name}: proof.sources must be non-empty")

    spec_name = proof.get("specification", "Spec.specs")
    if not isinstance(spec_name, str) or not spec_name:
        raise RuntimeError(
            f"{unit_dir.name}: invalid proof.specification: {spec_name!r}"
        )
    spec_module = proof.get("specification_module")
    if spec_module is None and "." in spec_name:
        spec_module = spec_name.rsplit(".", 1)[0]
    decl_name = spec_name.rsplit(".", 1)[-1]

    candidates = []
    for source in sources:
        if not isinstance(source, dict):
            continue
        path = source.get("path")
        if not isinstance(path, str):
            continue
        if spec_module and source.get("module") == spec_module:
            candidates.append(proof_root / path)
    if not candidates:
        for source in sources:
            if isinstance(source, dict) and source.get("role") == "specification":
                path = source.get("path")
                if isinstance(path, str):
                    candidates.append(proof_root / path)
    if not candidates and spec_module:
        expected_filename = f"{spec_module.rsplit('.', 1)[-1]}.lean"
        for source in sources:
            if isinstance(source, dict) and source.get("path") == expected_filename:
                candidates.append(proof_root / expected_filename)
    if not candidates:
        raise RuntimeError(
            f"{unit_dir.name}: could not locate specification Lean source "
            f"for {spec_name!r}"
        )
    return candidates, spec_name, decl_name


def expected_unit_profile(unit_dir, request):
    """Derive the expected MIR profile (1 or 2) from the unit's `Spec.lean`.

    `cargo-anneal`'s `Request` schema uses `deny_unknown_fields` with no
    profile key; Profile v1 units annotate their specification declaration as
    `Specs` while Profile v2 units annotate it as `SpecsV2`.
    """
    candidates, spec_name, decl_name = _find_specification_source(
        unit_dir, request
    )
    pattern = re.compile(
        r"\b(?:def|abbrev)\s+"
        + re.escape(decl_name)
        + r"\s*:\s*(?:(?:_root_\.)?Trusted\.(?:MirSemantics\.)?)?"
        + r"(SpecsV2|Specs)\b"
    )
    found_profiles = set()
    for spec_path in candidates:
        try:
            raw_spec = spec_path.read_text(encoding="utf-8")
        except OSError as exc:
            raise RuntimeError(
                f"{unit_dir.name}: cannot read specification source "
                f"{spec_path}: {exc}"
            ) from exc
        cleaned = _strip_lean_comments_and_strings(raw_spec)
        for match in pattern.finditer(cleaned):
            found_profiles.add(2 if match.group(1) == "SpecsV2" else 1)
    if len(found_profiles) != 1:
        names = [p.name for p in candidates]
        raise RuntimeError(
            f"{unit_dir.name}: cannot uniquely determine MIR profile "
            f"(Specs vs SpecsV2) for {spec_name!r} in {names!r}: "
            f"found={sorted(found_profiles)!r}"
        )
    return next(iter(found_profiles))


def is_safe_relative_filename(raw):
    """Return True if `raw` is a single relative filename with no traversal."""
    if not isinstance(raw, str) or not raw:
        return False
    path = Path(raw)
    return (
        not path.is_absolute()
        and len(path.parts) == 1
        and path.parts[0] not in (".", "..")
    )


def _normalize_instantiations(raw_insts, context):
    """Validate `scope.instantiations` and return unique `(path, args)` keys.

    Empty `args` lists are permitted because `rustc-capture/src/mono.rs` allows
    omitting region-only parameters, while each provided arg must be non-empty.
    """
    if not isinstance(raw_insts, list):
        raise ValueError(f"{context}: scope.instantiations must be a list")
    seen = set()
    normalized = []
    for entry in raw_insts:
        if not isinstance(entry, dict) or set(entry) != {"path", "args"}:
            raise ValueError(
                f"{context}: scope.instantiations entries must have keys "
                f"'path' and 'args': {entry!r}"
            )
        path = entry["path"]
        args = entry["args"]
        if not isinstance(path, str) or not path:
            raise ValueError(
                f"{context}: scope.instantiations path must be a non-empty string"
            )
        if not isinstance(args, list) or not all(
            isinstance(a, str) and a for a in args
        ):
            raise ValueError(
                f"{context}: scope.instantiations args must be a list of "
                "non-empty strings"
            )
        key = (path, tuple(args))
        if key in seen:
            raise ValueError(
                f"{context}: duplicate entry in scope.instantiations: {key!r}"
            )
        seen.add(key)
        normalized.append(key)
    return normalized


def _normalize_selected_unit_scope(scope, context):
    """Validate a `selected_unit` scope dict and return `(roots, inst_keys)`."""
    if not isinstance(scope, dict) or scope.get("kind") != "selected_unit":
        raise ValueError(f"{context}: expected scope.kind == 'selected_unit'")
    extra_keys = set(scope) - {"kind", "roots", "instantiations"}
    if extra_keys:
        raise ValueError(
            f"{context}: unexpected scope keys {sorted(extra_keys)!r}"
        )
    if "roots" not in scope or not isinstance(scope["roots"], list):
        raise ValueError(
            f"{context}: scope.roots must be a list of non-empty strings"
        )
    roots = scope["roots"]
    if not all(isinstance(r, str) and r for r in roots):
        raise ValueError(
            f"{context}: scope.roots entries must be non-empty strings"
        )
    if len(roots) != len(set(roots)):
        raise ValueError(f"{context}: duplicate entry in scope.roots")

    if "instantiations" in scope:
        raw_insts = scope["instantiations"]
    else:
        raw_insts = []
    inst_keys = _normalize_instantiations(raw_insts, context)

    if not roots and not inst_keys:
        raise ValueError(
            f"{context}: scope must contain at least one root or instantiation"
        )
    return list(roots), inst_keys


_MAX_SYMLINK_HOPS = 40


def _reject_symlink_ancestors_in_repo(
    path, label, repo_root=None, *, check_outside_repo=False
):
    """Reject symlinks at `path` or along traversed in-scope prefixes."""
    if path.is_symlink():
        raise RuntimeError(f"symlink disallowed in {label} path: {path}")

    resolved_repo = (
        repo_root.resolve(strict=True) if repo_root is not None else None
    )

    if path.is_absolute():
        resolved_cur = Path(path.anchor).resolve()
        queue = collections.deque(path.parts[1:])
    else:
        resolved_cur = Path.cwd().resolve(strict=True)
        queue = collections.deque(path.parts)

    def parent_in_scope(cur_dir):
        if resolved_repo is None:
            return check_outside_repo
        return cur_dir == resolved_repo or cur_dir.is_relative_to(
            resolved_repo
        )

    # Step component-by-component over a symlink-free `resolved_cur`:
    # reject symlinks at the final target or inside `resolved_repo`, and
    # expand permitted outside-repository symlinks one `readlink` hop at a
    # time so paths entering `resolved_repo` via an external symlink still
    # check every in-repository component while relative and absolute
    # external `--artifacts-dir` paths behave identically.
    hops = 0
    while queue:
        part = queue.popleft()
        if part in ("", "."):
            continue
        if part == "..":
            resolved_cur = resolved_cur.parent
            continue
        candidate = resolved_cur / part
        is_final = not any(p not in ("", ".") for p in queue)
        if candidate.is_symlink():
            if is_final or parent_in_scope(resolved_cur):
                raise RuntimeError(
                    f"symlink disallowed in {label} path: {candidate}"
                )
            hops += 1
            if hops > _MAX_SYMLINK_HOPS:
                raise RuntimeError(
                    f"too many symlink levels in {label} path: {path}"
                )
            target = Path(os.readlink(candidate))
            if target.is_absolute():
                resolved_cur = Path(target.anchor).resolve()
                for p in reversed(target.parts[1:]):
                    queue.appendleft(p)
            else:
                for p in reversed(target.parts):
                    queue.appendleft(p)
            continue
        resolved_cur = candidate


def _validate_real_directory(path, label, repo_root=None):
    """Verify `path` is a real directory without symlink traversal."""
    _reject_symlink_ancestors_in_repo(
        path, label, repo_root=repo_root, check_outside_repo=(repo_root is None)
    )
    if not path.is_dir():
        raise RuntimeError(f"invalid {label} directory: {path}")
    return path.resolve(strict=True)


_is_nonneg_int = anneal_ci_lib.is_nonneg_int
_is_exact_int = anneal_ci_lib.is_exact_int


def _require_allowed_keys(obj, allowed, label):
    if not isinstance(obj, dict):
        raise RuntimeError(f"{label} must be a JSON object")
    unknown = sorted(set(obj) - allowed)
    if unknown:
        raise RuntimeError(f"{label}: unexpected field(s): {unknown}")


def _is_clean_rel_posix_path(raw):
    if not isinstance(raw, str) or not raw or "\\" in raw:
        return False
    p = Path(raw)
    return (
        not p.is_absolute()
        and p.as_posix() == raw
        and bool(p.parts)
        and all(seg not in ("", ".", "..") for seg in p.parts)
    )


def _validate_compilation_fields(raw, label):
    _require_allowed_keys(raw, VALID_COMPILATION_KEYS, label)
    for str_key in (
        "source_root",
        "crate_root",
        "crate_name",
        "edition",
        "target",
    ):
        if str_key in raw:
            val = raw[str_key]
            if not isinstance(val, str) or not val:
                raise RuntimeError(f"{label}.{str_key} must be a non-empty string")
    if "crate_root" in raw and not _is_clean_rel_posix_path(raw["crate_root"]):
        raise RuntimeError(f"{label}.crate_root must be a clean relative path")
    if "crate_type" in raw:
        crate_type = raw["crate_type"]
        if not isinstance(crate_type, str) or crate_type not in VALID_CRATE_TYPES:
            raise RuntimeError(
                f"{label}.crate_type must be one of {sorted(VALID_CRATE_TYPES)}"
            )
    if "panic" in raw:
        panic = raw["panic"]
        if not isinstance(panic, str) or panic not in VALID_PANIC_STRATEGIES:
            raise RuntimeError(
                f"{label}.panic must be one of {sorted(VALID_PANIC_STRATEGIES)}"
            )
    if "overflow_checks" in raw and not isinstance(
        raw["overflow_checks"], bool
    ):
        raise RuntimeError(f"{label}.overflow_checks must be a boolean")
    if "cfg" in raw:
        cfg = raw["cfg"]
        if not isinstance(cfg, list) or not all(
            isinstance(x, str) and x for x in cfg
        ):
            raise RuntimeError(f"{label}.cfg must be a list of non-empty strings")
        if len(cfg) != len(set(cfg)):
            raise RuntimeError(f"{label}.cfg must not contain duplicate entries")
    if "env" in raw:
        env = raw["env"]
        if not isinstance(env, dict) or not all(
            isinstance(k, str) and k and isinstance(v, str)
            for k, v in env.items()
        ):
            raise RuntimeError(
                f"{label}.env must map non-empty strings to strings"
            )
    if "source_files" in raw:
        srcs = raw["source_files"]
        if (
            not isinstance(srcs, list)
            or not srcs
            or not all(_is_clean_rel_posix_path(x) for x in srcs)
        ):
            raise RuntimeError(
                f"{label}.source_files must be a non-empty relative path list"
            )
        if len(srcs) != len(set(srcs)):
            raise RuntimeError(
                f"{label}.source_files must not contain duplicate entries"
            )


def _normalize_compilation(raw, *, request_defaults=False):
    merged = dict(raw)
    return {
        "source_root": merged.get("source_root"),
        "crate_root": merged.get("crate_root", "lib.rs"),
        "crate_name": merged.get("crate_name"),
        "crate_type": merged.get("crate_type", "lib"),
        "panic": merged.get("panic", "unwind"),
        "overflow_checks": merged.get("overflow_checks", False),
        "edition": merged.get(
            "edition", "2024" if request_defaults else None
        ),
        "target": merged.get(
            "target", "x86_64-unknown-linux-gnu" if request_defaults else None
        ),
        "cfg": list(merged["cfg"]) if "cfg" in merged else [],
        "env": dict(merged["env"]) if "env" in merged else {},
        "source_files": (
            list(merged["source_files"]) if "source_files" in merged else []
        ),
    }


_SENSITIVE_ENV_IDENTS = frozenset({
    "env",
    "option_env",
    "r#env",
    "r#option_env",
})
_MACRO_DELIM_CLOSE = {"(": ")", "[": "]", "{": "}"}


def _is_rust_ident_start(ch):
    return ch == "_" or ch.isalpha()


def _is_rust_ident_continue(ch):
    return ch == "_" or ch.isalnum()


def _tokenize_rust_source(text, path_label):
    """Lex Rust source into `(kind, val, line)` skipping comments."""
    tokens = []
    i = 0
    n = len(text)
    line = 1
    while i < n:
        ch = text[i]
        if ch in (" ", "\t", "\r"):
            i += 1
            continue
        if ch == "\n":
            line += 1
            i += 1
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "/":
            nl = text.find("\n", i)
            if nl < 0:
                break
            i = nl
            continue
        if ch == "/" and i + 1 < n and text[i + 1] == "*":
            start_line = line
            depth = 1
            i += 2
            while i < n and depth > 0:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "*":
                    depth += 1
                    i += 2
                elif text[i] == "*" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        line += 1
                    i += 1
            if depth != 0:
                raise RuntimeError(
                    f"{path_label}:{start_line}: unterminated block comment"
                )
            continue

        # Raw strings: `r#"..."#`, `br#"..."#`, `cr#"..."#`.
        raw_hashes = None
        raw_prefix_len = 0
        if ch == "r":
            raw_prefix_len = 1
        elif ch in ("b", "c") and i + 1 < n and text[i + 1] == "r":
            raw_prefix_len = 2
        if raw_prefix_len:
            j = i + raw_prefix_len
            while j < n and text[j] == "#":
                j += 1
            if j < n and text[j] == '"':
                raw_hashes = j - (i + raw_prefix_len)
                tok_line = line
                start = j + 1
                end_marker = '"' + ("#" * raw_hashes)
                end_idx = text.find(end_marker, start)
                if end_idx < 0:
                    raise RuntimeError(
                        f"{path_label}:{tok_line}: unterminated raw string"
                    )
                inner = text[start:end_idx]
                line += inner.count("\n")
                tokens.append(("STR", inner, tok_line))
                i = end_idx + len(end_marker)
                continue

        # Normal, byte, and C string literals.
        str_start = None
        if ch == '"':
            str_start = i + 1
        elif ch in ("b", "c") and i + 1 < n and text[i + 1] == '"':
            str_start = i + 2
        if str_start is not None:
            tok_line = line
            j = str_start
            while j < n:
                cur = text[j]
                if cur == "\\":
                    if j + 1 >= n:
                        raise RuntimeError(
                            f"{path_label}:{tok_line}: unterminated string"
                        )
                    if text[j + 1] == "\n":
                        line += 1
                    j += 2
                    continue
                if cur == '"':
                    break
                if cur == "\n":
                    line += 1
                j += 1
            if j >= n or text[j] != '"':
                raise RuntimeError(
                    f"{path_label}:{tok_line}: unterminated string literal"
                )
            tokens.append(("STR", text[str_start:j], tok_line))
            i = j + 1
            continue

        # Byte char literals (`b'x'`, `b'\x7f'`).
        if ch == "b" and i + 1 < n and text[i + 1] == "'":
            tok_line = line
            j = i + 2
            if j < n and text[j] == "\\":
                j += 2
                while j < n and text[j] not in ("'", "\n"):
                    j += 1
            elif j < n and text[j] != "\n":
                j += 1
            if j >= n or text[j] != "'":
                raise RuntimeError(
                    f"{path_label}:{tok_line}: unterminated byte literal"
                )
            tokens.append(("CHAR", text[i : j + 1], tok_line))
            i = j + 1
            continue

        # Char literals vs lifetimes (`'a`, `'static`, `'r#type`).
        if ch == "'":
            tok_line = line
            if i + 1 < n and text[i + 1] == "\\":
                j = i + 3
                while j < n and text[j] not in ("'", "\n"):
                    j += 1
                if j >= n or text[j] != "'":
                    raise RuntimeError(
                        f"{path_label}:{tok_line}: unterminated char literal"
                    )
                tokens.append(("CHAR", text[i : j + 1], tok_line))
                i = j + 1
                continue
            if (
                i + 2 < n
                and text[i + 1] not in ("'", "\n")
                and text[i + 2] == "'"
            ):
                tokens.append(("CHAR", text[i : i + 3], tok_line))
                i += 3
                continue
            if (
                text.startswith("r#", i + 1)
                and i + 3 < n
                and _is_rust_ident_start(text[i + 3])
            ):
                j = i + 4
                while j < n and _is_rust_ident_continue(text[j]):
                    j += 1
                tokens.append(("LIFETIME", text[i:j], tok_line))
                i = j
                continue
            if i + 1 < n and _is_rust_ident_start(text[i + 1]):
                j = i + 2
                while j < n and _is_rust_ident_continue(text[j]):
                    j += 1
                tokens.append(("LIFETIME", text[i:j], tok_line))
                i = j
                continue
            tokens.append(("PUNCT", "'", tok_line))
            i += 1
            continue

        # Raw identifier `r#ident`.
        if text.startswith("r#", i) and i + 2 < n and _is_rust_ident_start(
            text[i + 2]
        ):
            j = i + 3
            while j < n and _is_rust_ident_continue(text[j]):
                j += 1
            tokens.append(("IDENT", text[i:j], line))
            i = j
            continue

        if _is_rust_ident_start(ch):
            j = i + 1
            while j < n and _is_rust_ident_continue(text[j]):
                j += 1
            tokens.append(("IDENT", text[i:j], line))
            i = j
            continue

        if ch.isdigit():
            j = i + 1
            while j < n and _is_rust_ident_continue(text[j]):
                j += 1
            tokens.append(("NUM", text[i:j], line))
            i = j
            continue

        tokens.append(("PUNCT", ch, line))
        i += 1
    return tokens


def _strip_raw_ident(val):
    return val[2:] if val.startswith("r#") else val


def _is_sensitive_env_token(tok):
    kind, val, _ = tok
    if kind == "IDENT" and (
        val in _SENSITIVE_ENV_IDENTS
        or _strip_raw_ident(val) in ("env", "option_env")
        or "CARGO_PKG" in val
    ):
        return True
    if kind == "STR" and "CARGO_PKG" in val:
        return True
    return False


def _is_disallowed_non_doc_env_token(
    tokens, idx, end_idx, *, in_use=False, in_macro=False
):
    """Allow ordinary `env` identifiers outside macro/import/path contexts."""
    kind, val, _ = tokens[idx]
    if kind == "STR":
        return "CARGO_PKG" in val
    if kind != "IDENT":
        return False
    if "CARGO_PKG" in val:
        return True
    if (
        val not in _SENSITIVE_ENV_IDENTS
        and _strip_raw_ident(val) not in ("env", "option_env")
    ):
        return False
    if in_macro or in_use:
        return True
    if idx + 1 < end_idx and tokens[idx + 1][:2] == ("PUNCT", "!"):
        return True
    if (
        idx >= 2
        and tokens[idx - 1][:2] == ("PUNCT", ":")
        and tokens[idx - 2][:2] == ("PUNCT", ":")
    ):
        return True
    if (
        idx + 2 < end_idx
        and tokens[idx + 1][:2] == ("PUNCT", ":")
        and tokens[idx + 2][:2] == ("PUNCT", ":")
    ):
        return True
    return False


def _find_matching_delim(tokens, open_idx, end_idx, path_label):
    _, open_ch, open_line = tokens[open_idx]
    close_ch = _MACRO_DELIM_CLOSE[open_ch]
    stack = [open_ch]
    idx = open_idx + 1
    while idx < end_idx:
        kind, val, _ = tokens[idx]
        if kind == "PUNCT":
            if val in _MACRO_DELIM_CLOSE:
                stack.append(val)
            elif val in (")", "]", "}"):
                top = stack[-1]
                if _MACRO_DELIM_CLOSE[top] != val:
                    raise RuntimeError(
                        f"{path_label}:{open_line}: mismatched delimiters"
                    )
                stack.pop()
                if not stack:
                    return idx
        idx += 1
    raise RuntimeError(
        f"{path_label}:{open_line}: unclosed '{open_ch}' (expected "
        f"'{close_ch}')"
    )


def _split_top_level_commas(tokens, path_label, start_line):
    segments = []
    cur = []
    depth = 0
    for tok in tokens:
        kind, val, tok_line = tok
        if kind == "PUNCT":
            if val in _MACRO_DELIM_CLOSE:
                depth += 1
            elif val in (")", "]", "}"):
                if depth == 0:
                    raise RuntimeError(
                        f"{path_label}:{tok_line}: unexpected '{val}'"
                    )
                depth -= 1
            elif val == "," and depth == 0:
                segments.append(cur)
                cur = []
                continue
        cur.append(tok)
    if depth != 0:
        raise RuntimeError(f"{path_label}:{start_line}: unclosed delimiter")
    segments.append(cur)
    if segments and not segments[-1]:
        segments.pop()
    if any(not seg for seg in segments):
        raise RuntimeError(
            f"{path_label}:{start_line}: empty argument in doc attribute"
        )
    return segments


def _is_safe_doc_expr(expr_tokens, path_label, start_line):
    if not expr_tokens:
        return False
    if len(expr_tokens) == 1:
        kind, val, _ = expr_tokens[0]
        return kind == "STR" and "CARGO_PKG" not in val
    if (
        len(expr_tokens) == 5
        and expr_tokens[0][:2] == ("IDENT", "env")
        and expr_tokens[1][:2] == ("PUNCT", "!")
        and expr_tokens[2][:2] == ("PUNCT", "(")
        and expr_tokens[3][:2] == ("STR", "CARGO_PKG_VERSION")
        and expr_tokens[4][:2] == ("PUNCT", ")")
    ):
        return True
    if (
        len(expr_tokens) >= 5
        and expr_tokens[0][:2] == ("IDENT", "concat")
        and expr_tokens[1][:2] == ("PUNCT", "!")
        and expr_tokens[2][:2] == ("PUNCT", "(")
        and expr_tokens[-1][:2] == ("PUNCT", ")")
    ):
        close_idx = _find_matching_delim(
            expr_tokens, 2, len(expr_tokens), path_label
        )
        if close_idx != len(expr_tokens) - 1:
            return False
        args = _split_top_level_commas(
            expr_tokens[3:-1], path_label, start_line
        )
        return bool(args) and all(
            _is_safe_doc_expr(arg, path_label, start_line) for arg in args
        )
    return False


def _validate_doc_only_attr(attr_tokens, path_label, start_line):
    if (
        len(attr_tokens) >= 3
        and attr_tokens[0][:2] == ("IDENT", "doc")
        and attr_tokens[1][:2] == ("PUNCT", "=")
        and _is_safe_doc_expr(attr_tokens[2:], path_label, start_line)
    ):
        return
    if (
        len(attr_tokens) >= 4
        and attr_tokens[0][:2] == ("IDENT", "cfg_attr")
        and attr_tokens[1][:2] == ("PUNCT", "(")
        and attr_tokens[-1][:2] == ("PUNCT", ")")
    ):
        close_idx = _find_matching_delim(
            attr_tokens, 1, len(attr_tokens), path_label
        )
        if close_idx == len(attr_tokens) - 1:
            segs = _split_top_level_commas(
                attr_tokens[2:-1], path_label, start_line
            )
            if len(segs) >= 2 and not any(
                _is_sensitive_env_token(tok) for tok in segs[0]
            ):
                for clause in segs[1:]:
                    if any(_is_sensitive_env_token(tok) for tok in clause):
                        _validate_doc_only_attr(clause, path_label, start_line)
                return
    raise RuntimeError(
        f"{path_label}:{start_line}: env!/option_env!/CARGO_PKG_* may only "
        "appear inside doc = concat!(..., env!(\"CARGO_PKG_VERSION\"), ...) "
        "attributes outside macros"
    )


def _scan_rust_tokens_doc_only_env(
    tokens,
    start_idx,
    end_idx,
    path_label,
    *,
    in_macro=False,
    expr_depth=0,
    in_use=False,
):
    idx = start_idx
    in_use_stmt = in_use
    while idx < end_idx:
        kind, val, tok_line = tokens[idx]

        # Real item/module attributes (`#[...]` or `#![...]`) outside macros
        # and expression groups.
        if (
            not in_macro
            and expr_depth == 0
            and kind == "PUNCT"
            and val == "#"
        ):
            open_idx = None
            if (
                idx + 1 < end_idx
                and tokens[idx + 1][:2] == ("PUNCT", "[")
            ):
                open_idx = idx + 1
            elif (
                idx + 2 < end_idx
                and tokens[idx + 1][:2] == ("PUNCT", "!")
                and tokens[idx + 2][:2] == ("PUNCT", "[")
            ):
                open_idx = idx + 2
            if open_idx is not None:
                close_idx = _find_matching_delim(
                    tokens, open_idx, end_idx, path_label
                )
                attr_tokens = tokens[open_idx + 1 : close_idx]
                if any(_is_sensitive_env_token(t) for t in attr_tokens):
                    _validate_doc_only_attr(attr_tokens, path_label, tok_line)
                idx = close_idx + 1
                continue

        # Track `use ...;` items so `use core::env` / `use ... as env` fail
        # even across brace groups (`use core::{env, ...};`), without rejecting
        # ordinary parameters or locals like `fn f(env: u8)`.
        prev_is_sep = idx >= 1 and (
            tokens[idx - 1][:2] == ("PUNCT", ".")
            or (
                idx >= 2
                and tokens[idx - 1][:2] == ("PUNCT", ":")
                and tokens[idx - 2][:2] == ("PUNCT", ":")
            )
        )
        if kind == "IDENT" and val == "use" and not prev_is_sep:
            in_use_stmt = True
        elif in_use_stmt and kind == "PUNCT" and val == ";":
            in_use_stmt = False

        # Disallow macro calls, macro forwarding/defs, imports/aliases,
        # path-qualified `env`, or `CARGO_PKG*` tokens outside doc attrs.
        if _is_disallowed_non_doc_env_token(
            tokens, idx, end_idx, in_use=in_use_stmt, in_macro=in_macro
        ):
            raise RuntimeError(
                f"{path_label}:{tok_line}: disallowed `{val}` outside "
                "non-macro doc attribute"
            )

        # Enter macro invocation / `macro_rules!` bodies (`in_macro=True`) so
        # `smuggle!(#[doc = env!(...)])` cannot inject code from doc syntax.
        if (
            kind == "IDENT"
            and val not in ("for", "impl", "type", "as", "return", "break")
            and idx + 1 < end_idx
            and tokens[idx + 1][:2] == ("PUNCT", "!")
        ):
            delim_idx = idx + 2
            if (
                val == "macro_rules"
                and delim_idx < end_idx
                and tokens[delim_idx][0] == "IDENT"
            ):
                delim_idx += 1
            if (
                delim_idx < end_idx
                and tokens[delim_idx][0] == "PUNCT"
                and tokens[delim_idx][1] in _MACRO_DELIM_CLOSE
            ):
                close_idx = _find_matching_delim(
                    tokens, delim_idx, end_idx, path_label
                )
                _scan_rust_tokens_doc_only_env(
                    tokens,
                    delim_idx + 1,
                    close_idx,
                    path_label,
                    in_macro=True,
                    expr_depth=expr_depth,
                    in_use=False,
                )
                idx = close_idx + 1
                continue

        if kind == "PUNCT" and val in ("(", "[", "{"):
            close_idx = _find_matching_delim(tokens, idx, end_idx, path_label)
            next_expr_depth = expr_depth + (1 if val in ("(", "[") else 0)
            _scan_rust_tokens_doc_only_env(
                tokens,
                idx + 1,
                close_idx,
                path_label,
                in_macro=in_macro,
                expr_depth=next_expr_depth,
                in_use=in_use_stmt,
            )
            idx = close_idx + 1
            continue

        idx += 1


def _verify_env_macros_doc_only(resolved_src, rel_paths):
    """Enforce that `env!`/`option_env!`/`CARGO_PKG_*` cannot affect MIR."""
    for rel in rel_paths:
        src_path = resolved_src / rel
        if src_path.is_symlink() or not src_path.is_file():
            raise RuntimeError(
                f"invalid zerocopy compilation source: {src_path}"
            )
        text = src_path.read_text(encoding="utf-8")
        tokens = _tokenize_rust_source(text, rel)
        _scan_rust_tokens_doc_only_env(tokens, 0, len(tokens), rel)


def _read_cargo_toml_data(cargo_toml_path):
    if cargo_toml_path.is_symlink():
        raise RuntimeError(
            f"symlink disallowed for Cargo.toml: {cargo_toml_path}"
        )
    text = cargo_toml_path.read_text(encoding="utf-8")
    try:
        return tomllib.loads(text)
    except tomllib.TOMLDecodeError as exc:
        raise RuntimeError(f"invalid TOML in {cargo_toml_path}: {exc}") from exc


def _workspace_package_version(ws_data):
    ws = ws_data.get("workspace")
    if not isinstance(ws, dict):
        return None
    ws_pkg = ws.get("package")
    if isinstance(ws_pkg, dict) and isinstance(ws_pkg.get("version"), str):
        return ws_pkg["version"]
    return None


def _extract_zerocopy_crate_version(cargo_toml_path):
    """Parse `[package].version` from `Cargo.toml` using TOML semantics."""
    data = _read_cargo_toml_data(cargo_toml_path)
    pkg = data.get("package")
    if not isinstance(pkg, dict):
        return None
    version = pkg.get("version")
    if isinstance(version, str):
        return version
    if isinstance(version, dict) and version.get("workspace") is True:
        own_ver = _workspace_package_version(data)
        if own_ver is not None:
            return own_ver
        resolved_dir = cargo_toml_path.resolve(strict=True).parent
        pkg_ws = pkg.get("workspace")
        if isinstance(pkg_ws, str) and pkg_ws:
            ws_dir_raw = Path(pkg_ws)
            ws_dir = (
                ws_dir_raw
                if ws_dir_raw.is_absolute()
                else resolved_dir / ws_dir_raw
            )
            if ws_dir.is_symlink():
                raise RuntimeError(
                    f"symlink disallowed for workspace Cargo.toml: {ws_dir}"
                )
            cand = ws_dir / "Cargo.toml"
            if cand.is_symlink() or cand.is_file():
                return _workspace_package_version(_read_cargo_toml_data(cand))
            return None
        for parent in resolved_dir.parents:
            cand = parent / "Cargo.toml"
            if cand.is_symlink() or cand.is_file():
                ws_data = _read_cargo_toml_data(cand)
                if isinstance(ws_data.get("workspace"), dict):
                    return _workspace_package_version(ws_data)
    return None


def _list_actual_src_files(resolved_src):
    actual = []
    for path in sorted(resolved_src.rglob("*")):
        if path.is_symlink():
            raise RuntimeError(f"symlink disallowed in zerocopy/src: {path}")
        if path.is_file() and path.suffix == ".rs":
            actual.append(path.relative_to(resolved_src).as_posix())
    return sorted(actual)


def _is_qualified_lean_decl(raw):
    if not isinstance(raw, str) or "." not in raw:
        return False
    mod_part, decl_part = raw.rsplit(".", 1)
    return bool(mod_part) and bool(decl_part)


def _validate_request_unit(
    entry_name,
    entry,
    unit_files,
    resolved_src,
    expected_compilation_sources,
):
    """Validate one `zerocopy/proofs/<unit>/` directory and `request.json`."""
    req_path = entry / "request.json"
    if not req_path.is_file():
        raise RuntimeError(f"missing request.json in proof unit: {entry}")
    request = anneal_ci_lib.load_strict_json_object(
        req_path, f"{entry_name}/request.json"
    )
    _require_allowed_keys(
        request, VALID_REQUEST_KEYS, f"{entry_name}/request.json"
    )
    if not _is_exact_int(request.get("schema_version"), 1):
        raise RuntimeError(
            f"{entry_name}: unsupported request schema_version "
            f"{request.get('schema_version')!r}"
        )

    compilation = request.get("compilation")
    _validate_compilation_fields(compilation, f"{entry_name}: compilation")
    actual_comp = _normalize_compilation(compilation, request_defaults=True)
    for req_key in (
        "source_root",
        "crate_root",
        "crate_name",
        "edition",
        "target",
    ):
        val = compilation.get(req_key)
        if not isinstance(val, str) or not val:
            raise RuntimeError(
                f"{entry_name}: compilation.{req_key} must be non-empty"
            )
    if Path(actual_comp["source_root"]).is_absolute():
        raise RuntimeError(
            f"{entry_name}: compilation.source_root must be a relative path: "
            f"{actual_comp['source_root']!r}"
        )
    try:
        unit_src = (entry / actual_comp["source_root"]).resolve(strict=True)
    except OSError as exc:
        raise RuntimeError(
            f"{entry_name}: source_root {actual_comp['source_root']!r} "
            f"cannot resolve: {exc}"
        ) from exc
    if unit_src != resolved_src:
        raise RuntimeError(
            f"{entry_name}: source_root {actual_comp['source_root']!r} does "
            f"not resolve to {resolved_src}"
        )
    if not compilation.get("source_files"):
        raise RuntimeError(
            f"{entry_name}: compilation.source_files must be declared"
        )
    if sorted(actual_comp["source_files"]) != expected_compilation_sources:
        missing = sorted(
            set(expected_compilation_sources) - set(actual_comp["source_files"])
        )
        extra = sorted(
            set(actual_comp["source_files"]) - set(expected_compilation_sources)
        )
        raise RuntimeError(
            f"{entry_name}: compilation.source_files mismatch vs "
            f"{resolved_src} (missing={missing}, extra={extra})"
        )
    if actual_comp["crate_root"] not in expected_compilation_sources:
        raise RuntimeError(
            f"{entry_name}: compilation.crate_root must belong to "
            "compilation sources"
        )
    pkg_version = actual_comp["env"].get("CARGO_PKG_VERSION")
    if not isinstance(pkg_version, str) or not pkg_version:
        raise RuntimeError(
            f"{entry_name}: compilation.env.CARGO_PKG_VERSION must be "
            "non-empty"
        )

    try:
        _normalize_selected_unit_scope(request.get("scope"), entry_name)
    except ValueError as exc:
        raise RuntimeError(str(exc)) from exc

    proof = request.get("proof")
    if not isinstance(proof, dict):
        raise RuntimeError(f"{entry_name}: proof must be a JSON object")
    if "specification_module" in proof or "theorem_module" in proof:
        raise RuntimeError(
            f"{entry_name}: unexpected explicit "
            "specification_module/theorem_module override"
        )
    _require_allowed_keys(proof, VALID_PROOF_KEYS, f"{entry_name}: proof")
    if proof.get("source_root") != ".":
        raise RuntimeError(f"{entry_name}: proof.source_root must be '.'")
    sources = proof.get("sources")
    if not isinstance(sources, list) or not sources:
        raise RuntimeError(f"{entry_name}: proof.sources must be non-empty")

    declared_files = {"request.json"}
    spec_modules = set()
    proof_modules = set()
    declared_modules = set()
    for source in sources:
        _require_allowed_keys(
            source,
            VALID_PROOF_SOURCE_KEYS,
            f"{entry_name}: proof.sources entry",
        )
        mod_name = source.get("module")
        if not isinstance(mod_name, str) or not mod_name:
            raise RuntimeError(
                f"{entry_name}: invalid Lean module name {mod_name!r}"
            )
        if mod_name in declared_modules:
            raise RuntimeError(
                f"{entry_name}: duplicate proof module {mod_name!r}"
            )
        declared_modules.add(mod_name)
        filename = source.get("path")
        if not is_safe_relative_filename(filename) or not filename.endswith(
            ".lean"
        ):
            raise RuntimeError(
                f"{entry_name}: invalid Lean source path {filename!r}"
            )
        if filename in declared_files:
            raise RuntimeError(
                f"{entry_name}: duplicate proof source path {filename!r}"
            )
        role = source.get("role")
        if role not in ("specification", "proof"):
            raise RuntimeError(
                f"{entry_name}: invalid proof source role {role!r}"
            )
        if role == "specification":
            if (
                not SPEC_FILE_PATTERN.fullmatch(filename)
                or mod_name != filename[:-5]
            ):
                raise RuntimeError(
                    f"{entry_name}: specification source must use a "
                    "Spec*.lean file matching its module name "
                    f"(got path={filename!r}, module={mod_name!r})"
                )
            spec_modules.add(mod_name)
        else:
            proof_modules.add(mod_name)
        if not (entry / filename).is_file():
            raise RuntimeError(
                f"{entry_name}: missing declared source {filename}"
            )
        declared_files.add(filename)

    unexpected = set(unit_files) - declared_files
    if unexpected:
        raise RuntimeError(
            f"{entry_name}: undeclared files in proof unit: "
            f"{sorted(unexpected)}"
        )

    actual_spec_decl = proof.get("specification", DEFAULT_SPEC_DECL)
    actual_thm_decl = proof.get("theorem", DEFAULT_PROOF_THM)
    for k, decl in (
        ("specification", actual_spec_decl),
        ("theorem", actual_thm_decl),
    ):
        if not _is_qualified_lean_decl(decl):
            raise RuntimeError(
                f"{entry_name}: invalid proof.{k}: {decl!r}"
            )
    spec_mod = actual_spec_decl.rsplit(".", 1)[0]
    if spec_mod not in spec_modules:
        raise RuntimeError(
            f"{entry_name}: proof.specification module {spec_mod!r} must be "
            "declared with role 'specification' in proof.sources"
        )
    thm_mod = actual_thm_decl.rsplit(".", 1)[0]
    if thm_mod not in proof_modules:
        raise RuntimeError(
            f"{entry_name}: proof.theorem module {thm_mod!r} must be declared "
            "with role 'proof' in proof.sources"
        )

    actual_profile = expected_unit_profile(entry, request)
    comp_sig = (
        actual_comp["source_root"],
        actual_comp["crate_root"],
        actual_comp["crate_name"],
        actual_comp["crate_type"],
        actual_comp["panic"],
        actual_comp["overflow_checks"],
        actual_comp["edition"],
        actual_comp["target"],
        tuple(sorted(actual_comp["cfg"])),
        tuple(sorted(actual_comp["env"].items())),
        tuple(sorted(actual_comp["source_files"])),
    )
    unit_expected = {
        "profile": actual_profile,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "compilation": actual_comp,
        "scope": request["scope"],
        "proof": {
            "specification": actual_spec_decl,
            "theorem": actual_thm_decl,
        },
    }
    request_with_expected = dict(request)
    request_with_expected["_unit_expected"] = unit_expected
    return request_with_expected, comp_sig


def discover_units(
    proofs_dir,
    src_dir,
    selected_units=None,
    *,
    repo_root=None,
):
    """Validate `proofs_dir` and `request.json` files, returning units."""
    proofs_dir = _validate_real_directory(
        proofs_dir, "proofs", repo_root=repo_root
    )
    resolved_src = _validate_real_directory(
        src_dir, "src", repo_root=repo_root
    )
    lib_rs = resolved_src / "lib.rs"
    if lib_rs.is_symlink() or not lib_rs.is_file():
        raise RuntimeError(f"zerocopy crate root missing: {lib_rs}")

    actual_rs_files = _list_actual_src_files(resolved_src)
    expected_compilation_sources = sorted(
        f for f in actual_rs_files if f not in EXCLUDED_SRC_FILES
    )
    if not expected_compilation_sources:
        raise RuntimeError(f"no compilable .rs files under {resolved_src}")

    discovered = {}
    baseline_unit = None
    baseline_sig = None
    for entry in sorted(proofs_dir.iterdir(), key=lambda p: p.name):
        if entry.is_symlink():
            raise RuntimeError(f"symlink disallowed in proofs tree: {entry}")
        if entry.is_file():
            if entry.name != "README.md":
                raise RuntimeError(f"unexpected top-level proofs file: {entry}")
            continue
        if not entry.is_dir():
            raise RuntimeError(f"unexpected entry in proofs tree: {entry}")

        unit_files = []
        for child in sorted(entry.iterdir(), key=lambda p: p.name):
            if child.is_symlink():
                raise RuntimeError(f"symlink disallowed in proof unit: {child}")
            if not child.is_file():
                raise RuntimeError(
                    f"unexpected non-file entry in proof unit: {child}"
                )
            unit_files.append(child.name)

        req_with_expected, comp_sig = _validate_request_unit(
            entry.name,
            entry,
            unit_files,
            resolved_src,
            expected_compilation_sources,
        )
        if baseline_sig is None:
            baseline_unit = entry.name
            baseline_sig = comp_sig
        elif comp_sig != baseline_sig:
            raise RuntimeError(
                f"{entry.name}: compilation config inconsistent with "
                f"{baseline_unit}"
            )
        discovered[entry.name] = (entry, req_with_expected)

    if not discovered:
        raise RuntimeError(f"no proof units found under {proofs_dir}")

    _verify_env_macros_doc_only(resolved_src, expected_compilation_sources)
    source_hashes = {
        rel: anneal_ci_lib.sha256_raw_file(
            resolved_src / rel,
            reject_symlink=True,
            missing_label="zerocopy/src",
        ).hex()
        for rel in expected_compilation_sources
    }
    for _, req_with_expected in discovered.values():
        req_with_expected["_unit_expected"]["source_hashes"] = source_hashes

    if selected_units:
        unique_units = list(dict.fromkeys(selected_units))
        missing = [name for name in unique_units if name not in discovered]
        if missing:
            raise RuntimeError(f"requested proof unit(s) not found: {missing}")
        return [discovered[name] for name in unique_units]
    return [discovered[name] for name in sorted(discovered)]


_SELECTED_BODY_KEYS = frozenset(("def_id", "path", "body_index"))
_MONO_INT_ARG_RE = re.compile(
    r"^([+-]?)(?:0x([0-9a-fA-F_]+)|0o([0-7_]+)|0b([01_]+)|([0-9][0-9_]*))"
    r"(?:[ui](?:8|16|32|64|128|size))?$"
)
_MONO_INLINE_INT_RE = re.compile(
    r"(?<![A-Za-z0-9_])([+-]?)(?:0x([0-9a-fA-F_]+)|0o([0-7_]+)|0b([01_]+)|"
    r"([0-9][0-9_]*))(?:[ui](?:8|16|32|64|128|size))(?![A-Za-z0-9_])"
)
_MONO_REGION_ARGS = frozenset({"'static", "'_"})


def _replace_mono_int_match(match):
    sign, hex_d, oct_d, bin_d, dec_d = match.groups()
    if hex_d is not None:
        val = int(hex_d.replace("_", ""), 16)
    elif oct_d is not None:
        val = int(oct_d.replace("_", ""), 8)
    elif bin_d is not None:
        val = int(bin_d.replace("_", ""), 2)
    else:
        val = int(dec_d.replace("_", ""), 10)
    return f"{sign}{val}" if sign == "-" and val != 0 else str(val)


def _canonical_mono_arg(arg):
    """Normalize concrete monomorphization argument text toward rustc output."""
    cleaned = re.sub(r"\s+", " ", arg.strip())
    exact_int = _MONO_INT_ARG_RE.fullmatch(cleaned)
    if exact_int:
        return _replace_mono_int_match(exact_int)
    cleaned = _MONO_INLINE_INT_RE.sub(_replace_mono_int_match, cleaned)
    cleaned = re.sub(r"&\s*(?:'static|'_)\s+", "&", cleaned)
    return re.sub(r"(^|[\s<(&*,;\[])(?:::)", r"\1", cleaned)


def _canonical_instantiation_candidates(inst_path, inst_args):
    """Return candidate `rustc` `SelectedBody.path` spellings for an inst."""
    base_path = inst_path[2:] if inst_path.startswith("::") else inst_path
    if not inst_args:
        return frozenset({base_path})

    raw_args = [a.strip() for a in inst_args]
    norm_args = [_canonical_mono_arg(a) for a in inst_args]
    erased_args = [
        "'_" if a in _MONO_REGION_ARGS else a for a in norm_args
    ]
    nr_raw = [a for a in raw_args if a not in _MONO_REGION_ARGS]
    nr_norm = [a for a in norm_args if a not in _MONO_REGION_ARGS]

    candidates = set()
    for seq in (raw_args, norm_args, erased_args, nr_raw, nr_norm):
        if seq:
            candidates.add(f"{base_path}::<{', '.join(seq)}>")
        else:
            candidates.add(base_path)

    if "::" in base_path and not base_path.startswith("<"):
        owner_path, method = base_path.rsplit("::", 1)
        for seq in (raw_args, norm_args, erased_args, nr_raw, nr_norm):
            for split in range(1, len(seq) + 1):
                owner_args = seq[:split]
                method_args = seq[split:]
                owner_part = f"<{owner_path}<{', '.join(owner_args)}>>"
                if method_args:
                    candidates.add(
                        f"{owner_part}::{method}::<{', '.join(method_args)}>"
                    )
                else:
                    candidates.add(f"{owner_part}::{method}")
        if raw_args[0] not in _MONO_REGION_ARGS:
            self_variants = (raw_args[0], norm_args[0])
            rest_raw = raw_args[1:]
            rest_norm = norm_args[1:]
            rest_erased = erased_args[1:]
            rest_nr_raw = [a for a in rest_raw if a not in _MONO_REGION_ARGS]
            rest_nr_norm = [a for a in rest_norm if a not in _MONO_REGION_ARGS]
            for self_ty in self_variants:
                for rest_seq in (
                    rest_raw,
                    rest_norm,
                    rest_erased,
                    rest_nr_raw,
                    rest_nr_norm,
                ):
                    for split in range(len(rest_seq) + 1):
                        trait_args = rest_seq[:split]
                        method_args = rest_seq[split:]
                        trait_part = (
                            f"{owner_path}<{', '.join(trait_args)}>"
                            if trait_args
                            else owner_path
                        )
                        if method_args:
                            candidates.add(
                                f"<{self_ty} as {trait_part}>::{method}::"
                                f"<{', '.join(method_args)}>"
                            )
                        else:
                            candidates.add(
                                f"<{self_ty} as {trait_part}>::{method}"
                            )
    return frozenset(candidates)


def _validate_selected_entries(
    selected, exp_roots, exp_inst_keys, *, lowered_inst_paths=None
):
    """Return True iff `selected` matches `SelectedBody` shape and scope.

    Each instantiation must match one of its textual spellings
    (`_canonical_instantiation_candidates`). Alternatively,
    `lowered_inst_paths` gives the `SelectedBody.path`s that
    `anneal-rustc-capture` selects for all of `exp_inst_keys`
    (`resolve_instantiation_candidates_via_capture`), and `selected` must then
    be exactly those paths and the roots.
    """
    if not isinstance(selected, list) or not selected:
        return False
    paths = []
    indices = []
    for entry in selected:
        if not isinstance(entry, dict):
            return False
        if set(entry.keys()) != _SELECTED_BODY_KEYS:
            return False
        if not _is_nonneg_int(entry["def_id"]):
            return False
        if not isinstance(entry["path"], str) or not entry["path"]:
            return False
        if not _is_nonneg_int(entry["body_index"]):
            return False
        paths.append(entry["path"])
        indices.append(entry["body_index"])
    if len(indices) != len(set(indices)) or len(paths) != len(set(paths)):
        return False
    path_set = set(paths)
    root_set = set(exp_roots)
    if exp_inst_keys:
        if not root_set.issubset(path_set):
            return False
        if not (1 <= len(paths) <= len(exp_roots) + len(exp_inst_keys)):
            return False
        if lowered_inst_paths is not None:
            lowered = set(lowered_inst_paths)
            return (
                bool(lowered)
                and lowered.issubset(path_set)
                and path_set.issubset(root_set | lowered)
            )
        inst_cands = [
            _canonical_instantiation_candidates(p, a) for p, a in exp_inst_keys
        ]
        if any(not (path_set & cands) for cands in inst_cands):
            return False
        allowed_paths = set(root_set).union(*inst_cands)
        return path_set.issubset(allowed_paths)
    return path_set == root_set


def resolve_instantiation_candidates_via_capture(
    unit_dir,
    expected_compilation,
    inst_keys,
    *,
    capture,
    sysroot=None,
    timeout=120.0,
):
    """Return the `SelectedBody.path`s that `rustc` lowers `inst_keys` to.

    One `anneal-rustc-capture` run requests every instantiation in
    `inst_keys`, so the cost does not grow with their number. The result is a
    set for all of them together: a capture selects one body for requests that
    resolve to the same instance, and does not record which request selected
    which body.
    """
    if not inst_keys or capture is None or expected_compilation is None:
        return frozenset()
    resolved_src = (
        unit_dir / expected_compilation["source_root"]
    ).resolve(strict=True)
    base_cmd = [
        str(capture),
        "capture",
        "--crate-root",
        str(resolved_src / expected_compilation["crate_root"]),
        "--crate-name",
        expected_compilation["crate_name"],
        "--crate-type",
        expected_compilation["crate_type"],
        "--panic",
        expected_compilation["panic"],
        "--edition",
        expected_compilation["edition"],
        "--target",
        expected_compilation["target"],
    ]
    if expected_compilation.get("overflow_checks"):
        base_cmd.append("--overflow-checks")
    # Match `anneal/trusted/cargo-anneal/src/verify.rs`: clear ambient env
    # so target/host RUSTC wrappers or search paths cannot taint capture, and
    # inject `<sysroot>/lib` only from the explicit `--sysroot`.
    child_env = {"PATH": "/usr/bin:/bin"}
    if sysroot is not None:
        try:
            resolved_sysroot = Path(sysroot).resolve(strict=True)
        except OSError as exc:
            raise RuntimeError(
                f"{unit_dir.name}: sysroot {sysroot!r} cannot resolve: {exc}"
            ) from exc
        if not resolved_sysroot.is_dir():
            raise RuntimeError(
                f"{unit_dir.name}: sysroot is not a directory: "
                f"{resolved_sysroot}"
            )
        lib_key = (
            "DYLD_LIBRARY_PATH"
            if sys.platform == "darwin"
            else "LD_LIBRARY_PATH"
        )
        child_env[lib_key] = str(resolved_sysroot / "lib")
        base_cmd.extend(["--sysroot", str(resolved_sysroot)])
    for cfg_item in expected_compilation["cfg"]:
        base_cmd.append(f"--cfg={cfg_item}")
    for k, v in sorted(expected_compilation["env"].items()):
        base_cmd.append(f"--env={k}={v}")
    for rel in expected_compilation["source_files"]:
        base_cmd.extend(["--source-file", str(resolved_src / rel)])
    instantiate_args = []
    for inst_path, inst_args in inst_keys:
        instantiate_args.extend([
            "--instantiate",
            json.dumps({"path": inst_path, "args": list(inst_args)}),
        ])
    described = ", ".join(repr(inst_path) for inst_path, _ in inst_keys)
    with tempfile.TemporaryDirectory(prefix="anneal-zc-alias-") as tmp_str:
        out_dir = Path(tmp_str) / "out"
        cmd = [*base_cmd, "--out-dir", str(out_dir), *instantiate_args]
        try:
            proc = subprocess.run(
                cmd,
                cwd=unit_dir,
                env=child_env,
                capture_output=True,
                text=True,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                f"{unit_dir.name}: rustc-capture timed out resolving "
                f"instantiations {described}"
            ) from exc
        capture_path = out_dir / "capture.json"
        if proc.returncode != 0 or not capture_path.is_file():
            raise RuntimeError(
                f"{unit_dir.name}: rustc-capture failed resolving "
                f"instantiations {described} (exit {proc.returncode}): "
                f"stderr={proc.stderr[:400]!r} stdout={proc.stdout[:400]!r}"
            )
        cap_data = anneal_ci_lib.load_strict_json_object(
            capture_path, f"{unit_dir.name} instantiation capture"
        )
        cap_sel = cap_data.get("selected")
        if (
            not isinstance(cap_sel, list)
            or not cap_sel
            or not all(
                isinstance(e, dict)
                and isinstance(e.get("path"), str)
                and e["path"]
                for e in cap_sel
            )
        ):
            raise RuntimeError(
                f"{unit_dir.name}: invalid capture.json selected entries "
                f"resolving instantiations {described}: {cap_sel!r}"
            )
        return frozenset(e["path"] for e in cap_sel)


def _is_sha256_hex(value):
    return isinstance(value, str) and bool(_SHA256_HEX_RE.fullmatch(value))


def _is_trimmed_nonempty_str(value):
    return isinstance(value, str) and bool(value.strip()) and (
        value.strip() == value
    )


def _validate_sorted_subset(items, allowed, label, failures):
    if not isinstance(items, list) or not all(
        isinstance(item, str) for item in items
    ):
        failures.append(f"invalid {label}={items!r}")
        return False
    prev = None
    ok = True
    for item in items:
        if item not in allowed:
            failures.append(f"unexpected entry {item!r} in {label}")
            ok = False
        if prev is not None and prev >= item:
            failures.append(
                f"{label} must be strictly sorted and duplicate-free "
                f"({prev!r} before {item!r})"
            )
            ok = False
        prev = item
    return ok


def _validate_unique_trimmed_nonempty(items, label, failures):
    if not isinstance(items, list) or not all(
        isinstance(v, str) for v in items
    ):
        failures.append(f"invalid {label}={items!r}")
        return False
    seen = set()
    ok = True
    for v in items:
        if not _is_trimmed_nonempty_str(v):
            failures.append(f"{label} entries must be trimmed and non-empty")
            ok = False
        elif v in seen:
            failures.append(f"duplicate entry {v!r} in {label}")
            ok = False
        else:
            seen.add(v)
    return ok


def _validate_digest_map(mapping, label, failures):
    if not isinstance(mapping, dict) or not mapping:
        failures.append(f"missing or empty {label}={mapping!r}")
        return
    for key, val in mapping.items():
        if not _is_trimmed_nonempty_str(key) or not _is_sha256_hex(val):
            failures.append(
                f"invalid entry in {label}: {key!r}={val!r}"
            )


def _validate_patched_files(raw_patched, failures):
    if not isinstance(raw_patched, list):
        failures.append(
            f"invalid correspondence_provenance.patched_files={raw_patched!r}"
        )
        return None
    patched_by_id = {}
    for idx, entry in enumerate(raw_patched):
        ptr = f"correspondence_provenance.patched_files[{idx}]"
        if not isinstance(entry, dict):
            failures.append(f"{ptr} must be a JSON object")
            continue
        if set(entry.keys()) != PATCHED_FILE_KEYS:
            failures.append(
                f"{ptr} keys mismatch: {sorted(entry.keys())!r}"
            )
            continue
        path = entry["path"]
        up_sha = entry["upstream_sha256"]
        pa_sha = entry["patched_sha256"]
        if not _is_trimmed_nonempty_str(path):
            failures.append(f"{ptr}.path must be trimmed and non-empty")
            continue
        if not _is_sha256_hex(up_sha):
            failures.append(f"{ptr}.upstream_sha256 invalid: {up_sha!r}")
        if not _is_sha256_hex(pa_sha):
            failures.append(f"{ptr}.patched_sha256 invalid: {pa_sha!r}")
        shim_id = f"lean-miri:{path}"
        if shim_id in patched_by_id:
            failures.append(
                f"duplicate correspondence_provenance.patched_files "
                f"path {path!r}"
            )
        else:
            patched_by_id[shim_id] = pa_sha
    return patched_by_id


def _validate_model_system_relation(rel, label, failures):
    if not isinstance(rel, dict):
        failures.append(f"missing or invalid {label}={rel!r}")
        return None
    extra = sorted(set(rel.keys()) - VALID_MODEL_SYSTEM_RELATION_KEYS)
    if extra:
        failures.append(f"unexpected {label} keys={extra!r}")
    kind = rel.get("kind")
    if not isinstance(kind, str) or kind not in ALLOWED_RELATION_KINDS:
        failures.append(f"invalid {label}.kind={kind!r}")
    qualifier = rel.get("qualifier")
    if qualifier is not None and (
        not isinstance(qualifier, str)
        or qualifier not in ALLOWED_RELATION_QUALIFIERS
    ):
        failures.append(f"invalid {label}.qualifier={qualifier!r}")
    if (
        kind in ("homomorphism", "abstraction", "simulation")
        and qualifier is None
    ):
        failures.append(f"{label}.kind {kind!r} requires qualifier")
    if kind == "none" and qualifier is not None:
        failures.append(f"{label}.kind 'none' must omit qualifier")
    if kind == "embedding" and qualifier in ("wf_stutter", "stutter"):
        failures.append(
            f"{label}.kind 'embedding' does not admit {qualifier!r}"
        )
    direction = rel.get("direction")
    if (
        not isinstance(direction, str)
        or direction not in ALLOWED_RELATION_DIRECTIONS
    ):
        failures.append(f"invalid {label}.direction={direction!r}")
    anchored_at = rel.get("anchored_at")
    if anchored_at is not None and not _is_trimmed_nonempty_str(anchored_at):
        failures.append(f"{label}.anchored_at must be trimmed and non-empty")
    claims = rel.get("licensed_claim_shapes")
    claims_ok = _validate_sorted_subset(
        claims, ALLOWED_CLAIM_SHAPES, f"{label}.licensed_claim_shapes", failures
    )
    if claims_ok:
        if (kind == "none") != (len(claims) == 0):
            failures.append(
                f"{label}.licensed_claim_shapes must be empty iff "
                f"{label}.kind == 'none'"
            )
        if "general_hyper" in claims and not (
            kind in ("simulation", "homomorphism")
            and qualifier == "lock_step"
            and direction == "bidirectional"
        ):
            failures.append(
                f"{label}: 'general_hyper' requires bidirectional lock_step "
                "simulation or homomorphism"
            )
        if "termination" in claims and qualifier == "stutter":
            failures.append(
                f"{label}: 'termination' cannot be licensed under 'stutter'"
            )
    unmodeled = rel.get("unmodeled_downstream")
    if unmodeled is not None:
        _validate_unique_trimmed_nonempty(
            unmodeled, f"{label}.unmodeled_downstream", failures
        )
    return {
        "kind": kind,
        "qualifier": qualifier,
        "direction": direction,
        "licensed_claim_shapes": claims if claims_ok else None,
    }


def _validate_claim_kind_relation(claim_kind, rel, failures):
    if (
        not isinstance(claim_kind, str)
        or claim_kind not in ALLOWED_CLAIM_KINDS
        or rel is None
    ):
        return
    kind = rel["kind"]
    qualifier = rel["qualifier"]
    direction = rel["direction"]
    claims = rel["licensed_claim_shapes"]
    if claim_kind == "exact_refines":
        ok = (
            kind == "simulation"
            and direction == "bidirectional"
            and qualifier in ("wf_stutter", "lock_step")
            and claims == ["forall_safety"]
        )
    elif claim_kind == "sound_refines":
        ok = (
            kind == "simulation"
            and direction == "forward"
            and qualifier in ("wf_stutter", "lock_step")
            and claims == ["forall_safety"]
        )
    elif claim_kind == "pure_spec_agreement":
        ok = (
            kind == "embedding"
            and direction == "bidirectional"
            and qualifier not in ("wf_stutter", "stutter")
            and claims == ["forall_safety"]
        )
    else:
        ok = True
    if not ok:
        failures.append(
            f"correspondence_provenance.claim_kind {claim_kind!r} is "
            "incompatible with model_system_relation "
            f"({kind}/{qualifier!r}/{direction})"
        )


def _validate_tcb_shims(raw_shims, label, failures):
    if not isinstance(raw_shims, list):
        failures.append(f"invalid {label}={raw_shims!r}")
        return None
    shims_by_id = {}
    shims_list = []
    for idx, entry in enumerate(raw_shims):
        ptr = f"{label}[{idx}]"
        if not isinstance(entry, dict):
            failures.append(f"{ptr} must be a JSON object")
            continue
        extra = sorted(set(entry.keys()) - VALID_TCB_SHIM_KEYS)
        if extra:
            failures.append(f"unexpected {ptr} keys={extra!r}")
        shim_id = entry.get("id")
        if not _is_trimmed_nonempty_str(shim_id):
            failures.append(f"{ptr}.id must be trimmed and non-empty")
            continue
        if shim_id in shims_by_id:
            failures.append(f"duplicate tcb_shims id {shim_id!r} in {label}")
        kind = entry.get("kind")
        if not isinstance(kind, str) or kind not in ALLOWED_SHIM_KINDS:
            failures.append(f"invalid {ptr}.kind={kind!r}")
        commit = entry.get("commit")
        if commit is not None and not _is_trimmed_nonempty_str(commit):
            failures.append(f"{ptr}.commit must be trimmed and non-empty")
        sha256 = entry.get("sha256")
        if sha256 is not None and not _is_sha256_hex(sha256):
            failures.append(f"{ptr}.sha256 invalid: {sha256!r}")
        if commit is None and sha256 is None:
            failures.append(
                f"{ptr} must specify at least one of commit or sha256"
            )
        status = entry.get("status")
        if not isinstance(status, str) or status not in ALLOWED_SHIM_STATUSES:
            failures.append(f"invalid {ptr}.status={status!r}")
        guards = entry.get("guards")
        if guards is not None:
            if not isinstance(guards, list) or not all(
                isinstance(g, str) for g in guards
            ):
                failures.append(f"invalid {ptr}.guards={guards!r}")
            else:
                seen_guards = set()
                for g in guards:
                    if not g:
                        failures.append(
                            f"{ptr}.guards must not contain empty strings"
                        )
                    elif g in seen_guards:
                        failures.append(
                            f"duplicate guard {g!r} in {ptr}.guards"
                        )
                    else:
                        seen_guards.add(g)
        rec = {
            "id": shim_id,
            "kind": kind,
            "sha256": sha256,
            "status": status,
        }
        shims_by_id[shim_id] = rec
        shims_list.append(rec)
    return shims_by_id, shims_list


def _validate_provenance_qualifiers(qual, failures):
    label = "correspondence_provenance.qualifiers"
    if not isinstance(qual, dict):
        failures.append(f"missing or invalid {label}={qual!r}")
        return None
    extra = sorted(set(qual.keys()) - VALID_PROVENANCE_QUALIFIER_KEYS)
    if extra:
        failures.append(f"unexpected {label} keys={extra!r}")
    choice_total = qual.get("choice_total")
    if not isinstance(choice_total, bool):
        failures.append(f"invalid {label}.choice_total={choice_total!r}")
    assumed_seams = qual.get("assumed_seams")
    seams_ok = _validate_unique_trimmed_nonempty(
        assumed_seams, f"{label}.assumed_seams", failures
    )
    scope_kind = qual.get("scope_kind")
    if (
        not isinstance(scope_kind, str)
        or scope_kind not in ALLOWED_PROVENANCE_SCOPES
    ):
        failures.append(f"invalid {label}.scope_kind={scope_kind!r}")
    if not isinstance(choice_total, bool) or not seams_ok:
        return None
    return {"choice_total": choice_total, "assumed_seams": assumed_seams}


def _validate_provenance_v3_fields(provenance, patched_by_id, failures):
    claim_kind = provenance.get("claim_kind")
    if (
        not isinstance(claim_kind, str)
        or claim_kind not in ALLOWED_CLAIM_KINDS
    ):
        failures.append(
            f"invalid correspondence_provenance.claim_kind={claim_kind!r}"
        )

    permitted_axioms = provenance.get("permitted_axioms")
    if _validate_sorted_subset(
        permitted_axioms,
        ALLOWED_FOUNDATION_AXIOMS,
        "correspondence_provenance.permitted_axioms",
        failures,
    ):
        if not permitted_axioms:
            failures.append(
                "correspondence_provenance.permitted_axioms must not be empty"
            )

    rel = _validate_model_system_relation(
        provenance.get("model_system_relation"),
        "correspondence_provenance.model_system_relation",
        failures,
    )
    _validate_claim_kind_relation(claim_kind, rel, failures)

    shims_res = _validate_tcb_shims(
        provenance.get("tcb_shims"),
        "correspondence_provenance.tcb_shims",
        failures,
    )
    taint_reasons = provenance.get("taint_reasons")
    taints_ok = _validate_sorted_subset(
        taint_reasons,
        ALLOWED_PROVENANCE_TAINTS,
        "correspondence_provenance.taint_reasons",
        failures,
    )
    qual = _validate_provenance_qualifiers(
        provenance.get("qualifiers"), failures
    )

    if patched_by_id is None or shims_res is None or qual is None:
        return
    shims_by_id, shims_list = shims_res

    for shim_id, patched_sha in patched_by_id.items():
        shim = shims_by_id.get(shim_id)
        if shim is None:
            failures.append(
                "correspondence_provenance.patched_files entry "
                f"{shim_id!r} is missing from tcb_shims"
            )
        else:
            if (
                shim["kind"] != "upstream_bugfix_patch"
                or shim["status"] != "assumed"
            ):
                failures.append(
                    f"correspondence_provenance.tcb_shims entry {shim_id!r} "
                    "must have kind 'upstream_bugfix_patch' and status "
                    "'assumed'"
                )
            if shim["sha256"] != patched_sha:
                failures.append(
                    f"correspondence_provenance.tcb_shims {shim_id!r} sha256 "
                    "disagrees with patched_files.patched_sha256"
                )

    for shim in shims_list:
        if (
            shim["kind"] == "upstream_bugfix_patch"
            and shim["id"] not in patched_by_id
        ):
            failures.append(
                "correspondence_provenance.tcb_shims upstream_bugfix_patch "
                f"{shim['id']!r} has no matching patched_files entry"
            )
        if (
            shim["kind"] == "assumed_seam"
            and shim["id"] not in qual["assumed_seams"]
        ):
            failures.append(
                "correspondence_provenance.tcb_shims assumed_seam "
                f"{shim['id']!r} is absent from qualifiers.assumed_seams"
            )

    for seam in qual["assumed_seams"]:
        shim = shims_by_id.get(seam)
        if shim is None:
            failures.append(
                "correspondence_provenance.qualifiers.assumed_seams entry "
                f"{seam!r} is missing from tcb_shims"
            )
        elif shim["kind"] != "assumed_seam" or shim["status"] != "assumed":
            failures.append(
                f"correspondence_provenance.tcb_shims {seam!r} must have "
                "kind 'assumed_seam' and status 'assumed'"
            )

    if taints_ok:
        expected_taints = []
        if qual["assumed_seams"]:
            expected_taints.append("assumed_seams_present")
        if not qual["choice_total"]:
            expected_taints.append("choice_total_false")
        if any(s["kind"] == "upstream_bugfix_patch" for s in shims_list):
            expected_taints.append("vendor_upstream_patches_present")
        if taint_reasons != expected_taints:
            failures.append(
                "correspondence_provenance.taint_reasons "
                f"{taint_reasons!r} disagrees with expected "
                f"{expected_taints!r}"
            )


def _validate_minirust_upstream(mr_obj, failures):
    label = "correspondence_provenance.minirust_upstream"
    if not isinstance(mr_obj, dict):
        failures.append(f"invalid {label}={mr_obj!r}")
        return
    extra = sorted(set(mr_obj.keys()) - MINIRUST_UPSTREAM_KEYS)
    if extra:
        failures.append(f"unexpected {label} keys={extra!r}")
    for field in ("upstream_repository", "upstream_commit"):
        val = mr_obj.get(field)
        if not _is_trimmed_nonempty_str(val):
            failures.append(
                f"{label}.{field} must be trimmed and non-empty: {val!r}"
            )
    for sha_field in (
        "upstream_pin_sha256",
        "tarball_sha256",
        "manifest_sha256",
    ):
        val = mr_obj.get(sha_field)
        if not _is_sha256_hex(val):
            failures.append(f"{label}.{sha_field} invalid: {val!r}")
    file_count = mr_obj.get("file_count")
    count_ok = _is_nonneg_int(file_count) and file_count > 0
    if not count_ok:
        failures.append(
            f"{label}.file_count must be a positive integer: {file_count!r}"
        )
    files = mr_obj.get("files")
    _validate_digest_map(files, f"{label}.files", failures)
    if count_ok and isinstance(files, dict) and len(files) != file_count:
        failures.append(
            f"{label}.file_count ({file_count}) disagrees with "
            f"files length ({len(files)})"
        )


def _validate_profile_v1_provenance(provenance, failures):
    if not isinstance(provenance, dict) or not provenance:
        failures.append(
            "Profile v1 receipt missing correspondence_provenance "
            f"object: {provenance!r}"
        )
        return
    if "applicable" in provenance or "reason" in provenance:
        failures.append(
            "Profile v1 receipt correspondence_provenance must omit "
            f"applicable and reason: {provenance!r}"
        )
        return
    sv = provenance.get("schema_version")
    if not (_is_exact_int(sv, 1) or _is_exact_int(sv, 3)):
        failures.append(
            "Profile v1 receipt invalid "
            f"correspondence_provenance.schema_version={sv!r}"
        )
        return

    allowed_keys = PROVENANCE_V1_KEYS if sv == 1 else PROVENANCE_V3_KEYS
    extra_keys = sorted(set(provenance.keys()) - allowed_keys)
    if extra_keys:
        failures.append(
            "Profile v1 receipt unexpected correspondence_provenance "
            f"keys={extra_keys!r}"
        )

    for field in (
        "upstream_repository",
        "upstream_commit",
        "upstream_lean_toolchain",
        "build_lean_toolchain",
        "note",
    ):
        val = provenance.get(field)
        if not isinstance(val, str) or not val.strip():
            failures.append(
                "Profile v1 receipt missing or blank "
                f"correspondence_provenance.{field}={val!r}"
            )

    for field in (
        "upstream_pin_sha256",
        "sysroot_foundation_manifest_sha256",
    ):
        val = provenance.get(field)
        if not _is_sha256_hex(val):
            failures.append(
                "Profile v1 receipt invalid "
                f"correspondence_provenance.{field}={val!r}"
            )

    patched_by_id = _validate_patched_files(
        provenance.get("patched_files"), failures
    )
    if "minirust_upstream" not in provenance:
        failures.append(
            "Profile v1 receipt missing "
            "correspondence_provenance.minirust_upstream"
        )
    else:
        _validate_minirust_upstream(provenance["minirust_upstream"], failures)
    for field in (
        "correspondence_adapters",
        "correspondence_proofs",
        "trusted_lean",
    ):
        _validate_digest_map(
            provenance.get(field),
            f"correspondence_provenance.{field}",
            failures,
        )

    if sv == 3:
        _validate_provenance_v3_fields(provenance, patched_by_id, failures)


def _validate_profile_v1_disclosures(receipt, failures):
    _validate_profile_v1_provenance(
        receipt.get("correspondence_provenance"), failures
    )

    assumptions = receipt.get("assumptions")
    if (
        not isinstance(assumptions, list)
        or not assumptions
        or not all(
            isinstance(item, str) and item.strip() for item in assumptions
        )
    ):
        failures.append(
            "Profile v1 receipt missing or invalid assumptions: "
            f"{assumptions!r}"
        )
    elif any(
        item.startswith(PROFILE_V2_ASSUMPTION_PREFIX) for item in assumptions
    ):
        failures.append(
            "Profile v1 receipt carries Profile v2 semantics assumption"
        )


def _validate_profile_v2_disclosures(receipt, failures):
    provenance = receipt.get("correspondence_provenance")
    if (
        not isinstance(provenance, dict)
        or set(provenance.keys()) != {"applicable", "reason"}
        or provenance.get("applicable") is not False
        or not isinstance(provenance.get("reason"), str)
        or not provenance["reason"].strip()
    ):
        failures.append(
            "Profile v2 receipt without inapplicable "
            f"correspondence_provenance: {provenance!r}"
        )

    assumptions = receipt.get("assumptions")
    if (
        not isinstance(assumptions, list)
        or not assumptions
        or not all(
            isinstance(item, str) and item.strip() for item in assumptions
        )
    ):
        failures.append(
            f"Profile v2 receipt missing assumptions list: {assumptions!r}"
        )
        return
    if PROFILE_V1_ASSUMPTION in assumptions:
        failures.append(
            "Profile v2 receipt must not carry Profile v1 pointer-free "
            "assumption"
        )
    v2_entries = [
        item
        for item in assumptions
        if item.startswith(PROFILE_V2_ASSUMPTION_PREFIX)
    ]
    if not v2_entries:
        failures.append(
            "Profile v2 receipt missing Profile v2 semantics assumption "
            "disclosure"
        )
        return
    semantics = v2_entries[0]
    missing_phrases = [
        phrase
        for phrase in PROFILE_V2_REQUIRED_ASSUMPTION_PHRASES
        if phrase not in semantics
    ]
    if missing_phrases:
        failures.append(
            "Profile v2 semantics assumption missing disclosures: "
            f"{missing_phrases!r}"
        )


def validate_parsed_receipt(
    unit_name,
    returncode,
    receipt,
    expected_roots,
    expected_instantiations=None,
    *,
    expected_profile=None,
    expected_compilation=None,
    expected_spec_decl=None,
    expected_proof_thm=None,
    expected_axioms=None,
    expected_source_hashes=None,
    lowered_inst_paths=None,
):
    """Fail closed unless a parsed `cargo-anneal verify` receipt is clean."""
    try:
        exp_roots, exp_inst_keys = _normalize_selected_unit_scope(
            {
                "kind": "selected_unit",
                "roots": expected_roots,
                "instantiations": (
                    expected_instantiations
                    if expected_instantiations is not None
                    else []
                ),
            },
            f"{unit_name} expected",
        )
    except ValueError as exc:
        raise RuntimeError(str(exc)) from exc

    failures = anneal_ci_lib.validate_receipt_v3_envelope(
        receipt,
        returncode=returncode,
        expected_status="selected_unit_verified",
        expected_returncode=0,
        check_deferred=True,
    )

    if "deferred" not in receipt:
        failures.append("missing deferred list")
    else:
        deferred = receipt["deferred"]
        if isinstance(deferred, list) and any(
            isinstance(d, str) and not d.strip() for d in deferred
        ):
            failures.append(f"blank entry in deferred={deferred!r}")

    spec_warnings = receipt.get("spec_warnings")
    if spec_warnings != []:
        failures.append(f"spec_warnings={spec_warnings!r}")

    if expected_profile is not None and (
        isinstance(expected_profile, bool)
        or expected_profile not in PROFILE_CANONICAL_ROOTS
    ):
        failures.append(f"invalid expected_profile={expected_profile!r}")

    scope = receipt.get("scope")
    try:
        actual_roots, actual_inst_keys = _normalize_selected_unit_scope(
            scope, f"{unit_name} receipt"
        )
    except ValueError as exc:
        failures.append(f"scope mismatch ({exc}): {scope!r}")
    else:
        if set(actual_roots) != set(exp_roots) or set(actual_inst_keys) != set(
            exp_inst_keys
        ):
            failures.append(f"scope mismatch: {scope!r}")

    selected = receipt.get("selected")
    if not _validate_selected_entries(
        selected,
        exp_roots,
        exp_inst_keys,
        lowered_inst_paths=lowered_inst_paths,
    ):
        failures.append(f"selected mismatch: selected={selected!r}")

    cfg = receipt.get("configuration")
    if isinstance(cfg, dict):
        unexpected_cfg = sorted(
            set(cfg) - VALID_RECEIPT_CONFIGURATION_KEYS
        )
        if unexpected_cfg:
            failures.append(
                f"unexpected configuration keys={unexpected_cfg!r}"
            )

    if expected_compilation is not None:
        if not isinstance(cfg, dict):
            failures.append(f"missing configuration object: {cfg!r}")
        else:
            for field in (
                "crate_name",
                "crate_type",
                "panic",
                "edition",
                "target",
            ):
                if cfg.get(field) != expected_compilation[field]:
                    failures.append(
                        f"configuration.{field}={cfg.get(field)!r} "
                        f"!= {expected_compilation[field]!r}"
                    )
            expected_crate_root = expected_compilation["crate_root"]
            actual_crate_root = cfg.get("crate_root")
            stage_prefix = None
            if isinstance(actual_crate_root, str):
                if actual_crate_root == expected_crate_root:
                    stage_prefix = ""
                elif actual_crate_root.endswith(f"/{expected_crate_root}"):
                    stage_prefix = actual_crate_root[
                        : -len(expected_crate_root)
                    ]
            if stage_prefix is None:
                failures.append(
                    f"configuration.crate_root={actual_crate_root!r}"
                )
            decl_files = cfg.get("declared_source_files")
            if stage_prefix is not None:
                expected_decl = sorted(
                    f"{stage_prefix}{rel}"
                    for rel in expected_compilation["source_files"]
                )
                if (
                    not isinstance(decl_files, list)
                    or not all(isinstance(d, str) for d in decl_files)
                    or len(decl_files) != len(set(decl_files))
                    or sorted(decl_files) != expected_decl
                ):
                    failures.append(
                        f"configuration.declared_source_files={decl_files!r}"
                    )
            cfg_list = cfg.get("cfg")
            if (
                not isinstance(cfg_list, list)
                or not all(isinstance(c, str) for c in cfg_list)
                or len(cfg_list) != len(set(cfg_list))
                or sorted(cfg_list) != sorted(expected_compilation["cfg"])
            ):
                failures.append(f"configuration.cfg={cfg_list!r}")
            if cfg.get("env") != expected_compilation["env"]:
                failures.append(f"configuration.env={cfg.get('env')!r}")
            if not _is_exact_int(cfg.get("opt_level"), 0):
                failures.append(
                    f"configuration.opt_level={cfg.get('opt_level')!r}"
                )
            if cfg.get("debug_assertions") is not False:
                failures.append(
                    "configuration.debug_assertions="
                    f"{cfg.get('debug_assertions')!r}"
                )
            expected_overflow = expected_compilation.get(
                "overflow_checks", False
            )
            if cfg.get("overflow_checks") is not expected_overflow:
                failures.append(
                    "configuration.overflow_checks="
                    f"{cfg.get('overflow_checks')!r}"
                )
            if cfg.get("mir_preserve_ub") is not True:
                failures.append(
                    "configuration.mir_preserve_ub="
                    f"{cfg.get('mir_preserve_ub')!r}"
                )
            if not _is_exact_int(cfg.get("pointer_bits"), 64):
                failures.append(
                    f"configuration.pointer_bits={cfg.get('pointer_bits')!r}"
                )
            if cfg.get("endian") != "little":
                failures.append(f"configuration.endian={cfg.get('endian')!r}")

        sources = receipt.get("sources")
        if (
            not isinstance(sources, list)
            or not all(
                isinstance(s, dict)
                and isinstance(s.get("relative_path"), str)
                and s.get("relative_path")
                and isinstance(s.get("sha256"), str)
                and s.get("sha256")
                for s in sources
            )
            or sorted(s["relative_path"] for s in sources)
            != sorted(expected_compilation["source_files"])
            or len(sources) != len(expected_compilation["source_files"])
        ):
            failures.append(f"sources mismatch: {sources!r}")
        elif expected_source_hashes is not None:
            actual_hashes = {s["relative_path"]: s["sha256"] for s in sources}
            if actual_hashes != expected_source_hashes:
                failures.append(f"sources sha256 mismatch: {sources!r}")

    allowed_ax = (
        ALLOWED_AXIOMS
        if expected_axioms is None
        else frozenset(expected_axioms)
    )
    if not allowed_ax.issubset(ALLOWED_AXIOMS):
        failures.append(f"invalid expected_axioms={expected_axioms!r}")

    audit = receipt.get("audit")
    if not isinstance(audit, dict):
        failures.append("missing audit object")
    else:
        if audit.get("replay") is not True:
            failures.append(f"audit.replay={audit.get('replay')!r}")
        if audit.get("exactType") is not True:
            failures.append(f"audit.exactType={audit.get('exactType')!r}")
        if not _is_exact_int(audit.get("checkedAlternateProofs"), 0):
            failures.append(
                "audit.checkedAlternateProofs="
                f"{audit.get('checkedAlternateProofs')!r}"
            )
        replayed = audit.get("replayedDeclarations")
        if not _is_nonneg_int(replayed) or replayed == 0:
            failures.append(f"audit.replayedDeclarations={replayed!r}")
        if audit.get("sorryDeclarations") != []:
            failures.append(
                f"audit.sorryDeclarations={audit.get('sorryDeclarations')!r}"
            )
        axioms = audit.get("axioms")
        if (
            not isinstance(axioms, list)
            or not all(isinstance(a, str) for a in axioms)
            or len(axioms) != len(set(axioms))
            or not set(axioms).issubset(allowed_ax)
            or not set(axioms).issubset(ALLOWED_AXIOMS)
        ):
            failures.append(f"disallowed audit.axioms={axioms!r}")
        root = audit.get("canonicalRoot")
        if (
            expected_profile is not None
            and not isinstance(expected_profile, bool)
            and expected_profile in PROFILE_CANONICAL_ROOTS
        ):
            expected_root = PROFILE_CANONICAL_ROOTS[expected_profile]
            if root != expected_root:
                failures.append(
                    f"canonicalRoot={root!r} does not match Profile "
                    f"v{expected_profile} ({expected_root!r})"
                )
        elif root not in (UNIT_THEOREM_V1, UNIT_THEOREM_V2):
            failures.append(f"canonicalRoot={root!r}")

        if root == UNIT_THEOREM_V2:
            _validate_profile_v2_disclosures(receipt, failures)
        elif root == UNIT_THEOREM_V1:
            _validate_profile_v1_disclosures(receipt, failures)
        if audit.get("subject") != "Captured.program":
            failures.append(f"audit.subject={audit.get('subject')!r}")
        if audit.get("expected") != "Expected.claim":
            failures.append(f"audit.expected={audit.get('expected')!r}")
        if expected_spec_decl is not None and (
            audit.get("specification") != expected_spec_decl
        ):
            failures.append(
                f"audit.specification={audit.get('specification')!r} "
                f"!= {expected_spec_decl!r}"
            )
        if (
            expected_proof_thm is not None
            and audit.get("theorem") != expected_proof_thm
        ):
            failures.append(
                f"audit.theorem={audit.get('theorem')!r} "
                f"!= {expected_proof_thm!r}"
            )
        bindings = audit.get("bindings")
        if not isinstance(bindings, dict):
            failures.append("missing audit.bindings")
        else:
            for bind_key, top_key in BINDING_DIGEST_FIELDS:
                top_val = receipt.get(top_key)
                if (
                    not isinstance(top_val, str)
                    or not top_val
                    or bindings.get(bind_key) != top_val
                ):
                    failures.append(f"binding digest mismatch on {bind_key}")

    if failures:
        detail = "; ".join(failures)
        raise RuntimeError(
            f"{unit_name}: verification failed ({detail}): "
            f"{json.dumps(receipt)[:2500]}"
        )
    return receipt


def validate_receipt(
    unit_name,
    returncode,
    stdout_text,
    stderr_text,
    expected_roots,
    expected_instantiations=None,
    *,
    expected_profile=None,
    expected_compilation=None,
    expected_spec_decl=None,
    expected_proof_thm=None,
    expected_axioms=None,
    expected_source_hashes=None,
    lowered_inst_paths=None,
):
    """Fail closed unless `cargo-anneal verify` emitted a clean receipt."""
    try:
        receipt = json.loads(
            stdout_text,
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
    except (ValueError, json.JSONDecodeError) as exc:
        raise RuntimeError(
            f"{unit_name}: invalid JSON receipt (exit {returncode}): {exc}\n"
            f"stdout={stdout_text[:800]}\nstderr={stderr_text[:800]}"
        ) from exc
    if not isinstance(receipt, dict):
        raise RuntimeError(f"{unit_name}: receipt JSON must be an object")
    return validate_parsed_receipt(
        unit_name,
        returncode,
        receipt,
        expected_roots,
        expected_instantiations,
        expected_profile=expected_profile,
        expected_compilation=expected_compilation,
        expected_spec_decl=expected_spec_decl,
        expected_proof_thm=expected_proof_thm,
        expected_axioms=expected_axioms,
        expected_source_hashes=expected_source_hashes,
        lowered_inst_paths=lowered_inst_paths,
    )


def validate_unit_receipt(
    unit_dir,
    returncode,
    receipt,
    request,
    *,
    capture=None,
    sysroot=None,
    timeout=120.0,
):
    """Validate one unit's Receipt v3, resolving aliased instantiations."""
    unit_expected = request["_unit_expected"]
    expected_scope = unit_expected["scope"]
    expected_proof = unit_expected["proof"]
    raw_insts = expected_scope.get("instantiations", [])
    lowered = None
    if (
        returncode == 0
        and receipt.get("status") == "selected_unit_verified"
        and raw_insts
        and capture is not None
    ):
        exp_roots, exp_inst_keys = _normalize_selected_unit_scope(
            {
                "kind": "selected_unit",
                "roots": expected_scope["roots"],
                "instantiations": raw_insts,
            },
            f"{unit_dir.name} expected",
        )
        selected = receipt.get("selected")
        if (
            isinstance(selected, list)
            and 1 <= len(selected) <= len(exp_roots) + len(exp_inst_keys)
            and all(
                isinstance(e, dict)
                and set(e.keys()) == _SELECTED_BODY_KEYS
                and isinstance(e.get("path"), str)
                and e["path"]
                for e in selected
            )
            and not _validate_selected_entries(
                selected, exp_roots, exp_inst_keys
            )
        ):
            sel_paths = {e["path"] for e in selected}
            # Some instantiation has no predicted spelling in the receipt, so
            # learn how `rustc` lowers all of them; one capture costs the
            # same either way.
            if any(
                not (sel_paths & _canonical_instantiation_candidates(p, a))
                for p, a in exp_inst_keys
            ):
                lowered = resolve_instantiation_candidates_via_capture(
                    unit_dir,
                    unit_expected["compilation"],
                    exp_inst_keys,
                    capture=capture,
                    sysroot=sysroot,
                    timeout=timeout,
                )
    return validate_parsed_receipt(
        unit_dir.name,
        returncode,
        receipt,
        expected_scope["roots"],
        expected_instantiations=raw_insts,
        expected_profile=unit_expected["profile"],
        expected_compilation=unit_expected["compilation"],
        expected_spec_decl=expected_proof["specification"],
        expected_proof_thm=expected_proof["theorem"],
        expected_axioms=unit_expected["allowed_axioms"],
        expected_source_hashes=unit_expected.get("source_hashes"),
        lowered_inst_paths=lowered,
    )


env_tool = anneal_ci_lib.env_tool
discover_local_defaults = anneal_ci_lib.discover_local_defaults


def verify_unit(arguments, unit_dir, request, artifacts_root):
    started = time.monotonic()
    proc, receipt = anneal_ci_lib.run_cargo_anneal_verify(
        cli=arguments.cli,
        request_path=unit_dir / "request.json",
        cwd=unit_dir,
        capture=arguments.capture,
        sysroot=arguments.sysroot,
        lean=arguments.lean,
        artifacts_dir=artifacts_root / unit_dir.name,
        timeout=arguments.timeout,
        log_prefix=artifacts_root / unit_dir.name,
        label=unit_dir.name,
    )
    elapsed = round(time.monotonic() - started, 3)
    unit_expected = request["_unit_expected"]
    receipt = validate_unit_receipt(
        unit_dir,
        proc.returncode,
        receipt,
        request,
        capture=arguments.capture,
        sysroot=arguments.sysroot,
        timeout=arguments.timeout,
    )
    return unit_dir.name, {
        "status": receipt["status"],
        "profile": unit_expected["profile"],
        "canonical_root": receipt["audit"]["canonicalRoot"],
        "scope": receipt["scope"],
        "axioms": receipt["audit"]["axioms"],
        "taint_reasons": receipt["taint_reasons"],
        "assumptions": receipt["assumptions"],
        "deferred": receipt["deferred"],
        "spec_warnings": receipt["spec_warnings"],
        "correspondence_provenance": receipt["correspondence_provenance"],
        "elaboration_sandbox": receipt["elaboration_sandbox"],
        "selected": receipt["selected"],
        "request_sha256": receipt["request_sha256"],
        "capture_sha256": receipt["capture_sha256"],
        "specification_manifest_sha256": receipt[
            "specification_manifest_sha256"
        ],
        "timing_ms": receipt.get("timing_ms", {}),
        "wall_seconds": elapsed,
    }


def run_suite(arguments, work_dir, *, repo_root=None):
    units = discover_units(
        arguments.proofs_dir,
        arguments.src_dir,
        selected_units=arguments.unit or None,
        repo_root=repo_root,
    )
    cargo_toml = arguments.src_dir.resolve(strict=True).parent / "Cargo.toml"
    cargo_toml_version = (
        _extract_zerocopy_crate_version(cargo_toml)
        if cargo_toml.is_symlink() or cargo_toml.is_file()
        else None
    )
    request_crate_version = units[0][1]["_unit_expected"]["compilation"][
        "env"
    ]["CARGO_PKG_VERSION"]
    crate_version_drift = (
        cargo_toml_version is not None
        and cargo_toml_version != request_crate_version
    )
    if crate_version_drift:
        print(
            f"note: Cargo.toml version {cargo_toml_version!r} differs from "
            f"request.json CARGO_PKG_VERSION {request_crate_version!r} "
            "(verified doc-only usage)",
            file=sys.stderr,
        )
    workers = max(1, min(arguments.jobs, len(units)))
    started = time.monotonic()
    results = {}
    with ThreadPoolExecutor(max_workers=workers) as pool:
        futures = [
            pool.submit(verify_unit, arguments, unit_dir, request, work_dir)
            for unit_dir, request in units
        ]
        for future in futures:
            name, record = future.result()
            results[name] = record
    summary = {
        "units": results,
        "unit_count": len(results),
        "request_crate_version": request_crate_version,
        "cargo_toml_version": cargo_toml_version,
        "crate_version_drift": crate_version_drift,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (work_dir / "summary.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2))
    return summary


def main(argv=None):
    anneal_root = anneal_ci_lib.default_anneal_root(__file__)
    repo_root = anneal_root.parent

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--proofs-dir",
        type=Path,
        default=repo_root / "zerocopy/proofs",
        help="Path to zerocopy/proofs directory",
    )
    parser.add_argument(
        "--src-dir",
        type=Path,
        default=repo_root / "zerocopy/src",
        help="Path to zerocopy/src directory",
    )
    parser.add_argument(
        "--unit",
        action="append",
        default=[],
        help="Verify only the named proof unit subdirectory (repeatable)",
    )
    parser.add_argument(
        "--artifacts-dir",
        type=Path,
        help="New directory retaining verification artifacts and summary",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, max(1, os.cpu_count() or 1)),
        help="Maximum concurrent `cargo-anneal verify` workers",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Per-unit `cargo-anneal verify` timeout in seconds",
    )
    for name in ("cli", "capture", "sysroot", "lean"):
        parser.add_argument(f"--{name}", type=Path)

    arguments = parser.parse_args(argv)
    anneal_ci_lib.resolve_cli_tools(
        anneal_root,
        arguments,
        defaults_fn=lambda root: discover_local_defaults(root),
    )
    for required in ("cli", "capture", "sysroot", "lean"):
        value = getattr(arguments, required)
        if value is None:
            parser.error(f"the following arguments are required: --{required}")
        setattr(arguments, required, value.resolve(strict=True))

    arguments.proofs_dir = _validate_real_directory(
        arguments.proofs_dir, "proofs", repo_root=repo_root
    )
    arguments.src_dir = _validate_real_directory(
        arguments.src_dir, "src", repo_root=repo_root
    )

    if arguments.artifacts_dir is not None:
        _reject_symlink_ancestors_in_repo(
            arguments.artifacts_dir, "artifacts", repo_root=repo_root
        )
        arguments.artifacts_dir.mkdir(mode=0o700)
        run_suite(
            arguments,
            arguments.artifacts_dir.resolve(),
            repo_root=repo_root,
        )
    else:
        with tempfile.TemporaryDirectory(
            prefix="anneal-zerocopy-proofs-"
        ) as tmp:
            run_suite(arguments, Path(tmp), repo_root=repo_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
