#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Trusted defender harness for Anneal automated red-teaming."""

from __future__ import annotations

import argparse
import bz2
import contextvars
from dataclasses import dataclass
import gzip
import hashlib
import io
import json
import lzma
import math
import os
from pathlib import Path
import re
import resource
import secrets
import shutil
import signal
import stat
import struct
import subprocess
import sys
import tarfile
import tempfile
import threading
import tomllib
from typing import Any, Callable, Iterable
import zlib

if __package__ in (None, ""):
    _CI_DIR = Path(__file__).resolve().parents[1]
    if str(_CI_DIR) not in sys.path:
        sys.path.insert(0, str(_CI_DIR))
    from redteam import dedup, lean_ast, scenarios
else:
    from . import dedup, lean_ast, scenarios

import anneal_ci_lib
strip_lean_comments_and_strings = lean_ast.strip_lean_comments_and_strings


RECEIPT_SCHEMA = "anneal-redteam-receipt/v1"
REPLAY_SCHEMA = "anneal-redteam-replay/v1"

MAX_SUBMISSION_FILES = 64
MAX_SUBMISSION_DIRS = 64
MAX_SUBMISSION_DEPTH = 16
MAX_TAR_MEMBERS = 256
MAX_TAR_PAX_BYTES = 4096
MAX_SUBMISSION_FILE_BYTES = 1_048_576
MAX_SUBMISSION_TOTAL_BYTES = 8_388_608
MAX_SUBMISSION_TAR_BYTES = 8_388_608
MAX_TAR_UNCOMPRESSED_BYTES = 8_912_896
MAX_XZ_DECOMPRESS_MEM_BYTES = 32 * 1024 * 1024
MAX_S2_RLIB_BYTES = 128 * 1024 * 1024
_MAX_ELF_TABLE_BYTES = 16 * 1024 * 1024
_MAX_ELF_SYMTAB_BYTES = 32 * 1024 * 1024
VERIFIED_RUST_TARGET = "x86_64-unknown-linux-gnu"
MAX_WITNESS_ARGS = 16
MAX_WITNESS_BYTES = 65_536
MAX_INCORRECTNESS_PATCH_CHANGED_LINES = 250
MAX_INCORRECTNESS_CLAIM_BYTES = 65_536
MAX_E1_CAPTURE_FILE_BYTES = 16 * 1024 * 1024
MAX_E1_CAPTURE_TOTAL_BYTES = 64 * 1024 * 1024
MAX_E1_CAPTURE_SHARDS = 1024
MAX_CRATE_ARCHIVE_BYTES = 64 * 1024 * 1024

DEFAULT_S2_INPUTS: tuple[int, ...] = (
    0,
    1,
    2,
    0x7FFF_FFFF,
    0xFFFF_FFFE,
    0xFFFF_FFFF,
)

VERDICT_ATTACKER_WON = "ATTACKER_WON"
VERDICT_NEEDS_HUMAN_REVIEW = "NEEDS_HUMAN_REVIEW"
VERDICT_DEFENDER_HELD = "DEFENDER_HELD"
VERDICT_INVALID_SUBMISSION = "INVALID_SUBMISSION"
VERDICT_HARNESS_ERROR = "HARNESS_ERROR"

TIER_EXECUTABLE_ORACLE = "executable_oracle"
TIER_LEAN_PATCH_PROOF = "lean_patch_proof"
TIER_PROSE_CLAIM = "prose_claim"
TIER_DEFENDER_FIXED_BUG = "defender_fixed_bug"
TIER_SANDBOX_ESCAPE = "sandbox_escape"
TIER_NONE = "none"

_MIR_SEMANTICS_PATCH_PREFIX = "anneal/trusted/lean/Trusted/MirSemantics/"
_FORBIDDEN_MIR_SEMANTICS_PATCH_FILES = frozenset(
    {
        "anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean",
        "anneal/trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean",
    }
)

_LEAN_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_RUST_SEG_RE = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*$")
_RESERVED_LEAN_ROOTS = frozenset(
    {
        "Captured",
        "Expected",
        "Trusted",
        "Anneal",
        "Init",
        "Std",
        "Lean",
        "Lake",
        "TrustedBoundary",
        "SpecPreflight",
    }
)
_ALLOWED_ENV_KEYS: tuple[str, ...] = (
    "PATH",
    "HOME",
    "TMPDIR",
    "TEMP",
    "TMP",
    "LANG",
    "LC_ALL",
    "LC_CTYPE",
    "TZ",
    "USER",
    "LOGNAME",
    "RUSTUP_HOME",
)


class InvalidSubmissionError(Exception):
    """Raised when an untrusted submission violates staging rules."""


class OracleInfrastructureError(Exception):
    """Raised when defender pre-run setup or infrastructure malfunctions."""


class DefenderTamperError(Exception):
    """Raised when a rule-following run mutates defender-locked assets."""

    def __init__(self, message: str, tampered_paths: tuple[str, ...]) -> None:
        super().__init__(message)
        self.tampered_paths = tampered_paths


def _detect_disallowed_imports(
    cleaned: str, *, allow_theory_import_all: bool = False
) -> set[str]:
    """Detect forbidden `import all` or `Lean.*` / `Lake.*` module imports."""
    return lean_ast.detect_disallowed_imports(
        cleaned, allow_theory_import_all=allow_theory_import_all
    )


def _detect_disallowed_lean_constructs(
    sources: dict[str, str],
    *,
    allow_theory_import_all: bool = False,
    allow_spec_options: bool = False,
    lean_bin: Path | None = None,
    lean_sysroot: Path | None = None,
    bwrap: Path | None = None,
    timeout: int = 90,
    parse_errors_out: list[str] | None = None,
    anneal_root: Path | None = None,
) -> list[str]:
    """Detect forbidden Lean constructs via bwrap AST parser or lexer fallback."""
    return lean_ast.detect_disallowed_lean_constructs(
        sources,
        allow_theory_import_all=allow_theory_import_all,
        allow_spec_options=allow_spec_options,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        bwrap=bwrap,
        bwrap_runner=_run_lean_in_bwrap if bwrap is not None else None,
        infra_error_cls=OracleInfrastructureError,
        timeout=timeout,
        parse_errors_out=parse_errors_out,
        anneal_root=anneal_root,
    )


def _detect_disallowed_lean_constructs_with_tools(
    sources: dict[str, str],
    *,
    allow_theory_import_all: bool,
    allow_spec_options: bool,
    lean_bin: Path | None,
    env: dict[str, str],
    bwrap: Path | None = None,
    allow_fallback: bool = True,
    timeout: int = 90,
    parse_errors_out: list[str] | None = None,
    anneal_root: Path | None = None,
) -> list[str]:
    """Run Lean AST inspection in `bwrap` (failing closed if unavailable)."""
    bwrap_path = _resolve_bwrap_binary(bwrap, required=not allow_fallback)
    has_lean = lean_bin is not None and lean_bin.is_file()
    if not allow_fallback and (not has_lean or bwrap_path is None):
        raise OracleInfrastructureError(
            "live Lean AST verification requires `lean` and `bwrap`"
        )
    lean_sysroot: Path | None = None
    if has_lean and bwrap_path is not None:
        assert lean_bin is not None
        lean_sysroot = _resolve_lean_sysroot(lean_bin, env)
        _verify_bwrap_canary(
            bwrap_path,
            ro_mounts=[
                (lean_sysroot / "lib", "/toolchain/lib"),
                (lean_bin, "/toolchain/bin/lean"),
            ],
            env_vars={
                "PATH": "/usr/bin:/bin",
                "HOME": "/work/tmp",
                "TMPDIR": "/work/tmp",
            },
            argv=["/toolchain/bin/lean", "--version"],
            bind_dev_seeds=True,
            ro_system_bins=False,
            tmpfs_tmp=False,
            disable_userns=True,
            label="lean_ast",
        )
    return _detect_disallowed_lean_constructs(
        sources,
        allow_theory_import_all=allow_theory_import_all,
        allow_spec_options=allow_spec_options,
        lean_bin=lean_bin if lean_sysroot is not None else None,
        lean_sysroot=lean_sysroot,
        bwrap=bwrap_path,
        timeout=timeout,
        parse_errors_out=parse_errors_out,
        anneal_root=anneal_root,
    )


@dataclass(frozen=True)
class LoadedSubmission:
    """Validated regular files extracted strictly within scenario slots."""

    files: dict[str, bytes]
    witness_args: tuple[int, ...] = ()
    e1_patch_targets: tuple[str, ...] = ()
    e1_patch_changed_lines: int = 0
    has_e1: bool = False
    has_e2: bool = False
    claim_text: str | None = None


@dataclass(frozen=True)
class E1VerificationResult:
    """Structured result from evaluating Tier-E1 `semantics.patch` + `Proof.lean`."""

    passed: bool
    preservation_passed: bool | None
    reference_target_verified: bool
    theory_canaries_verified: bool
    patch_audit: dict[str, Any] | None
    detail: str


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parents[2]


def _clean_git_env(git_bin: Path | None = None) -> dict[str, str]:
    """Minimal git environment isolated from user/global config and prompts."""
    path_val = "/usr/bin:/bin"
    if git_bin is not None:
        path_val = f"{git_bin.parent}:{path_val}"
    return {
        "PATH": path_val,
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_SYSTEM": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
    }


def _collect_eval_checkout_paths(
    anneal_root: Path, *, git_bin: Path | None = None
) -> list[str]:
    """Enumerate evaluated target paths cleanly in deterministic order."""
    tracked = _list_tracked_anneal_paths(anneal_root, git_bin=git_bin)
    if tracked is not None:
        return tracked
    paths: list[str] = []
    for name, _pin in _STAGE_CHECKOUT_ITEMS:
        p = anneal_root / name
        if name in ("Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"):
            if p.exists() or p.is_symlink():
                paths.append(name)
        elif p.is_dir() and not p.is_symlink():
            for cur_root, dirnames, filenames in os.walk(
                p, topdown=True, followlinks=False
            ):
                dirnames[:] = sorted(
                    d for d in dirnames if d not in _SKIP_CHECKOUT_DIRS
                )
                cur = Path(cur_root)
                for fname in sorted(filenames):
                    if fname.endswith(".pyc"):
                        continue
                    rel = (cur / fname).relative_to(anneal_root).as_posix()
                    paths.append(rel)
    return sorted(set(paths))


def _hash_evaluated_checkout_tree(
    anneal_root: Path, *, git_bin: Path | None = None
) -> str:
    """Compute a deterministic SHA-256 digest over evaluated defender bytes."""
    h = hashlib.sha256()
    for rel in _collect_eval_checkout_paths(anneal_root, git_bin=git_bin):
        h.update(rel.encode("utf-8", errors="surrogateescape"))
        h.update(b"\x00")
        target = anneal_root / rel
        fd = -1
        try:
            fd = os.open(target, _OPEN_RO_FLAGS)
            fst = os.fstat(fd)
            if not stat.S_ISREG(fst.st_mode):
                h.update(b"NONREG\x00")
                continue
            fh = hashlib.sha256()
            with os.fdopen(fd, "rb") as handle:
                fd = -1
                while chunk := handle.read(65_536):
                    fh.update(chunk)
            h.update(b"FILE:")
            h.update(fh.digest())
            h.update(b"\x00")
        except FileNotFoundError:
            h.update(b"MISSING\x00")
        except OSError:
            h.update(b"ERROR\x00")
        finally:
            if fd >= 0:
                os.close(fd)
    return h.hexdigest()


def _resolve_target_provenance(
    root: Path, *, git_bin: Path | None = None
) -> tuple[str, bool | None, str]:
    """Resolve `(head_sha, is_dirty, target_tree_sha256)` for `root`."""
    head_sha = "unknown"
    target_dirty: bool | None = None
    resolved_git = (
        git_bin
        if git_bin is not None
        else _resolve_system_binary("git", required=False)
    )
    if resolved_git is not None:
        clean_env = _clean_git_env(resolved_git)
        try:
            top = subprocess.run(
                [
                    str(resolved_git),
                    *anneal_ci_lib.SAFE_GIT_FLAGS,
                    "-C",
                    str(root),
                    "rev-parse",
                    "--show-toplevel",
                ],
                capture_output=True,
                text=True,
                env=clean_env,
                timeout=5,
                check=False,
            )
            top_ok = top.returncode == 0 and Path(
                top.stdout.strip()
            ).resolve() in (
                root.resolve(),
                root.resolve().parent,
            )
            if top_ok:
                res = subprocess.run(
                    [
                        str(resolved_git),
                        *anneal_ci_lib.SAFE_GIT_FLAGS,
                        "-C",
                        str(root),
                        "rev-parse",
                        "HEAD",
                    ],
                    capture_output=True,
                    text=True,
                    env=clean_env,
                    timeout=5,
                    check=False,
                )
                sha = res.stdout.strip()
                if res.returncode == 0 and len(sha) >= 7:
                    head_sha = sha
                    st = subprocess.run(
                        [
                            str(resolved_git),
                            *anneal_ci_lib.SAFE_GIT_FLAGS,
                            "-C",
                            str(root),
                            "status",
                            "--porcelain=v1",
                            "--untracked-files=no",
                            "--",
                            ".",
                        ],
                        capture_output=True,
                        text=True,
                        env=clean_env,
                        timeout=5,
                        check=False,
                    )
                    if st.returncode == 0:
                        target_dirty = bool(st.stdout.strip())
        except (OSError, subprocess.SubprocessError):
            pass
    tree_sha = _hash_evaluated_checkout_tree(root, git_bin=resolved_git)
    return head_sha, target_dirty, tree_sha


def _resolve_target_sha(root: Path) -> str:
    """Best-effort git HEAD SHA of `root`, falling back to `unknown`."""
    head_sha, _dirty, _tree_sha = _resolve_target_provenance(root)
    return head_sha


_FRESHNESS_SOURCE_EXTS = frozenset({".rs", ".lean", ".toml"})
_FRESHNESS_ROOT_FILES = frozenset({"Cargo.toml", "Cargo.lock"})
_FRESHNESS_PREFIXES = ("trusted/", "theory/", "correspondence/")


def _max_anneal_binary_source_mtime_ns(
    anneal_root: Path,
) -> tuple[int, str | None]:
    """Return `(max_mtime_ns, relpath)` over embedded/compiled source trees."""
    max_ns = 0
    newest_rel: str | None = None
    for rel in _collect_eval_checkout_paths(anneal_root):
        if rel not in _FRESHNESS_ROOT_FILES and not rel.startswith(
            _FRESHNESS_PREFIXES
        ):
            continue
        if rel.startswith("trusted/cargo-anneal/tests/") or rel.startswith(
            "trusted/rustc-capture/tests/"
        ):
            continue
        if rel not in _FRESHNESS_ROOT_FILES and not any(
            rel.endswith(ext) for ext in _FRESHNESS_SOURCE_EXTS
        ):
            continue
        try:
            st = os.lstat(anneal_root / rel)
        except OSError:
            continue
        if stat.S_ISREG(st.st_mode) and st.st_mtime_ns > max_ns:
            max_ns = st.st_mtime_ns
            newest_rel = rel
    return max_ns, newest_rel


def _verify_live_tool_freshness(
    anneal_root: Path,
    tools: dict[str, Path | None],
    *,
    explicit_overrides: dict[str, Path | None],
    live_names: tuple[str, ...],
) -> None:
    """Reject stale auto-discovered Cargo binaries against checkout sources."""
    candidate_targets: list[Path] = []
    raw_target = os.environ.get("CARGO_TARGET_DIR", "")
    if raw_target.strip():
        candidate_targets.append(Path(raw_target).resolve())
    default_target = (anneal_root / "target").resolve()
    if default_target not in candidate_targets:
        candidate_targets.append(default_target)
    max_src_ns: int | None = None
    newest_src: str | None = None

    for name in live_names:
        if explicit_overrides.get(name) is not None:
            continue
        tool_path = tools.get(name)
        if tool_path is None:
            continue
        try:
            resolved_tool = tool_path.resolve()
        except OSError:
            continue
        matched_target = next(
            (cand for cand in candidate_targets if resolved_tool.is_relative_to(cand)),
            None,
        )
        if matched_target is None:
            continue
        release_dir = matched_target / "release"
        debug_dir = matched_target / "debug"
        try:
            tool_st = os.stat(resolved_tool)
        except OSError:
            continue
        if resolved_tool.parent == release_dir:
            debug_sib = debug_dir / resolved_tool.name
            try:
                debug_st = os.stat(debug_sib)
            except OSError:
                debug_st = None
            if (
                debug_st is not None
                and stat.S_ISREG(debug_st.st_mode)
                and debug_st.st_mtime_ns > tool_st.st_mtime_ns
            ):
                raise OracleInfrastructureError(
                    f"stale release binary `{resolved_tool.name}` is older than "
                    f"`debug/{resolved_tool.name}`; rebuild release or pass "
                    f"explicit tool override"
                )
        if max_src_ns is None:
            max_src_ns, newest_src = _max_anneal_binary_source_mtime_ns(
                anneal_root
            )
        if max_src_ns > tool_st.st_mtime_ns and newest_src is not None:
            raise OracleInfrastructureError(
                f"stale prebuilt `{resolved_tool.name}` in `{resolved_tool.parent.name}/` "
                f"is older than checkout source `{newest_src}`; rebuild before "
                "running live red-team evaluation"
            )


def _untrusted_bwrap_prefixes() -> tuple[Path, ...]:
    """Return host directory trees untrusted for ambient `bwrap` discovery."""
    roots: list[Path] = [
        Path("/tmp"),
        Path("/var/tmp"),
        Path("/dev/shm"),
        _default_anneal_root().parent,
    ]
    for fn in (
        lambda: Path(tempfile.gettempdir()),
        Path.cwd,
        Path.home,
    ):
        try:
            roots.append(fn())
        except (RuntimeError, OSError):
            pass
    out: list[Path] = []
    seen: set[Path] = set()
    for p in roots:
        for cand in (p,):
            if cand not in seen:
                seen.add(cand)
                out.append(cand)
        try:
            res = p.resolve()
        except OSError:
            continue
        if res not in seen:
            seen.add(res)
            out.append(res)
    return tuple(out)


_TRUSTED_SYSTEM_BIN_ROOTS: tuple[Path, ...] = (
    Path("/usr/bin"),
    Path("/bin"),
    Path("/usr/local/bin"),
    Path("/nix/store"),
)
_EXPLICIT_PRLIMIT_VAR: contextvars.ContextVar[Path | None] = (
    contextvars.ContextVar("anneal_redteam_explicit_prlimit", default=None)
)


def _validate_system_binary_candidate(
    candidate: Path,
    *,
    tool_name: str,
    explicit_override: bool,
) -> Path:
    """Validate permissions, directory safety, and ownership of a host tool."""
    if not explicit_override and not candidate.is_absolute():
        raise OracleInfrastructureError(
            f"auto-discovered {tool_name} path must be absolute: {candidate}"
        )
    untrusted_prefixes = () if explicit_override else _untrusted_bwrap_prefixes()
    for prefix in untrusted_prefixes:
        if candidate == prefix or candidate.is_relative_to(prefix):
            raise OracleInfrastructureError(
                f"untrusted auto-discovered {tool_name} path disallowed: {candidate}"
            )
    try:
        resolved = candidate.resolve(strict=True)
    except OSError as exc:
        raise OracleInfrastructureError(
            f"cannot resolve {tool_name} binary {candidate}: {exc}"
        ) from exc
    for prefix in untrusted_prefixes:
        if resolved == prefix or resolved.is_relative_to(prefix):
            raise OracleInfrastructureError(
                f"untrusted resolved {tool_name} path disallowed: {resolved}"
            )
    try:
        st = os.stat(resolved)
    except OSError as exc:
        raise OracleInfrastructureError(
            f"cannot stat {tool_name} binary {resolved}: {exc}"
        ) from exc
    if not stat.S_ISREG(st.st_mode) or not os.access(resolved, os.X_OK):
        raise OracleInfrastructureError(
            f"{tool_name} path must be an executable regular file: {resolved}"
        )
    if (st.st_mode & 0o022) != 0:
        raise OracleInfrastructureError(
            f"{tool_name} binary must not be group/world-writable: {resolved}"
        )
    euid = os.geteuid()
    trusted_container_root = (
        euid != 0
        and st.st_uid == euid
        and any(
            resolved.is_relative_to(root)
            for root in _TRUSTED_SYSTEM_BIN_ROOTS
        )
    )
    if explicit_override:
        allowed_uids = (0, euid)
    else:
        allowed_uids = (0, euid) if trusted_container_root else (0,)
    if st.st_uid not in allowed_uids:
        raise OracleInfrastructureError(
            f"{tool_name} binary has untrusted owner uid={st.st_uid}: {resolved}"
        )
    ancestors: list[Path] = []
    cur = resolved.parent
    while True:
        ancestors.append(cur)
        if cur == cur.parent:
            break
        cur = cur.parent
    for anc in ancestors:
        try:
            ast = os.lstat(anc)
        except OSError as exc:
            raise OracleInfrastructureError(
                f"cannot stat {tool_name} ancestor directory {anc}: {exc}"
            ) from exc
        if stat.S_ISLNK(ast.st_mode) or not stat.S_ISDIR(ast.st_mode):
            raise OracleInfrastructureError(
                f"{tool_name} ancestor directory must be a real directory: {anc}"
            )
        if ast.st_uid not in allowed_uids:
            raise OracleInfrastructureError(
                f"{tool_name} ancestor directory has untrusted owner uid={ast.st_uid}: {anc}"
            )
        sticky_nix_store = (
            anc == Path("/nix/store")
            and ast.st_uid == 0
            and (ast.st_mode & stat.S_ISVTX) != 0
            and (ast.st_mode & 0o002) == 0
        )
        sticky_explicit_root_dir = (
            explicit_override
            and ast.st_uid == 0
            and (ast.st_mode & stat.S_ISVTX) != 0
        )
        if (ast.st_mode & 0o022) != 0 and not (
            sticky_nix_store or sticky_explicit_root_dir
        ):
            raise OracleInfrastructureError(
                f"{tool_name} ancestor directory must not be group/world-writable: {anc}"
            )
    return resolved


def _resolve_system_binary(
    tool_name: str,
    explicit: Path | None = None,
    *,
    required: bool = False,
) -> Path | None:
    """Resolve and validate a trusted host executable (`bwrap`, `prlimit`, ...)."""
    if explicit is not None:
        return _validate_system_binary_candidate(
            explicit, tool_name=tool_name, explicit_override=True
        )
    found = shutil.which(tool_name)
    if found is None:
        if required:
            raise OracleInfrastructureError(
                f"live red-team evaluation requires trusted `{tool_name}`"
            )
        return None
    return _validate_system_binary_candidate(
        Path(found), tool_name=tool_name, explicit_override=False
    )


def _validate_bwrap_candidate(
    candidate: Path,
    *,
    explicit_override: bool,
) -> Path:
    """Validate executable permissions, directory safety, and ownership of `bwrap`."""
    return _validate_system_binary_candidate(
        candidate, tool_name="bwrap", explicit_override=explicit_override
    )


def _resolve_bwrap_binary(
    explicit: Path | None = None,
    *,
    required: bool = False,
) -> Path | None:
    """Resolve and validate the Bubblewrap (`bwrap`) executable."""
    return _resolve_system_binary("bwrap", explicit, required=required)


def _miri_sysroot_provenance(
    miri_sysroot: Path | None, *, source: str
) -> dict[str, Any]:
    """Summarize verified target `.rlib` manifest digest for `miri_sysroot`."""
    if miri_sysroot is None:
        return {"present": False, "source": source}
    entry: dict[str, Any] = {
        "present": True,
        "source": source,
        "name": miri_sysroot.name,
    }
    target_lib_dir = miri_sysroot / "lib" / "rustlib" / VERIFIED_RUST_TARGET / "lib"
    if target_lib_dir.is_dir() and not target_lib_dir.is_symlink():
        hasher = hashlib.sha256()
        count = 0
        for item in sorted(target_lib_dir.iterdir(), key=lambda p: p.name):
            if item.is_symlink() or not item.is_file():
                continue
            snap = _inspect_regular_nofollow(
                item, exc_type=OracleInfrastructureError
            )
            hasher.update(item.name.encode("utf-8", errors="surrogateescape"))
            hasher.update(b":")
            hasher.update(snap.sha256.encode("ascii"))
            hasher.update(b"\n")
            count += 1
        entry["rlib_count"] = count
        if count > 0:
            entry["rlib_manifest_sha256"] = hasher.hexdigest()
    return entry


def _snapshot_tool_provenance(
    tools: dict[str, Path | None],
    *,
    explicit_overrides: dict[str, Path | None],
    bwrap: Path | None = None,
    prlimit: Path | None = None,
    git: Path | None = None,
    miri_sysroot: Path | None = None,
) -> dict[str, dict[str, Any]]:
    """Record SHA-256 and discovery provenance of resolved tool binaries."""
    prov: dict[str, dict[str, Any]] = {}
    all_tools = dict(tools)
    all_tools["bwrap"] = bwrap
    all_tools["prlimit"] = prlimit
    all_tools["git"] = git
    for name in (
        "cli",
        "capture",
        "auditor",
        "lean",
        "sysroot",
        "bwrap",
        "prlimit",
        "git",
    ):
        tpath = all_tools.get(name)
        src = "explicit" if explicit_overrides.get(name) is not None else "discovered"
        if tpath is None:
            prov[name] = {"present": False, "source": src}
            continue
        entry: dict[str, Any] = {
            "present": True,
            "source": src,
            "name": tpath.name,
        }
        if name != "sysroot":
            try:
                snap = _inspect_regular_nofollow(
                    tpath, exc_type=OracleInfrastructureError
                )
                entry["sha256"] = snap.sha256
                entry["mtime_ns"] = snap.mtime_ns
            except OracleInfrastructureError:
                entry["present"] = False
        prov[name] = entry
    miri_src = (
        "explicit"
        if explicit_overrides.get("miri_sysroot") is not None
        else "discovered"
    )
    prov["miri_sysroot"] = _miri_sysroot_provenance(
        miri_sysroot, source=miri_src
    )
    return prov


def _sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


_MAX_REL_PATH_BYTES = 1024
_MAX_PATH_SEGMENT_BYTES = 255


def _validate_rel_path_lengths(relpath: str, *, raw_label: str | None = None) -> None:
    """Enforce POSIX segment and total relative path UTF-8 byte limits."""
    label = raw_label if raw_label is not None else relpath
    if len(relpath.encode("utf-8")) > _MAX_REL_PATH_BYTES:
        raise InvalidSubmissionError(
            f"submission path exceeds {_MAX_REL_PATH_BYTES} bytes: {label!r}"
        )
    if any(
        len(seg.encode("utf-8")) > _MAX_PATH_SEGMENT_BYTES
        for seg in relpath.split("/")
    ):
        raise InvalidSubmissionError(
            f"path segment exceeds {_MAX_PATH_SEGMENT_BYTES} bytes: {label!r}"
        )


def _validate_rel_posix(raw: str, *, allow_dot_prefix: bool = False) -> str:
    """Validate and normalize a strict relative POSIX file path."""
    if not isinstance(raw, str) or not raw:
        raise InvalidSubmissionError("empty submission path")
    if "\x00" in raw or "\\" in raw:
        raise InvalidSubmissionError(f"forbidden character in path: {raw!r}")
    if raw.startswith("/"):
        raise InvalidSubmissionError(f"absolute path disallowed: {raw!r}")
    normalized = raw[2:] if (allow_dot_prefix and raw.startswith("./")) else raw
    if not normalized:
        raise InvalidSubmissionError("empty normalized submission path")
    segs = normalized.split("/")
    if any(seg in ("", ".", "..") for seg in segs):
        raise InvalidSubmissionError(f"unsafe path segment in {raw!r}")
    if any(ord(ch) < 32 for ch in normalized):
        raise InvalidSubmissionError(f"control char in path: {raw!r}")
    _validate_rel_path_lengths(normalized, raw_label=raw)
    return normalized


_NOFOLLOW_FLAG = getattr(os, "O_NOFOLLOW", 0)
_DIRECTORY_FLAG = getattr(os, "O_DIRECTORY", 0)
_NONBLOCK_FLAG = getattr(os, "O_NONBLOCK", 0)
_OPEN_RO_FLAGS = os.O_RDONLY | _NOFOLLOW_FLAG | _NONBLOCK_FLAG
_DIR_RO_FLAGS = os.O_RDONLY | _NOFOLLOW_FLAG | _DIRECTORY_FLAG | _NONBLOCK_FLAG
_DEFAULT_TMPFS_BYTES = 512 * 1024 * 1024
# `anneal-audit` compiles Trusted, theory/, vendor/lean-miri, and correspondence
# closures into `TMPDIR` inside bwrap; 4 GiB avoids ENOSPC as theory grows.
_AUDIT_TMPFS_BYTES = 4 * 1024 * 1024 * 1024
_MAX_CAPTURE_BYTES = 8 * 1024 * 1024
_SYSROOT_CRATE_MARKER_RE = re.compile(
    r"(?m)^error: could not compile `(?:core|std|alloc|compiler_builtins|"
    r"proc_macro|panic_\w+|unwind)`(?: \([^)]+\))?(?: due to \d+ previous error|\s*$)"
)
_CARGO_INFRA_ERR_RE = re.compile(
    r"(?m)^error(?:\[E0463\])?: (?:"
    r"can't find crate for [`'](?:core|std|alloc|compiler_builtins|proc_macro)[`']"
    r"|could not execute process\b"
    r"|process didn't exit successfully:"
    r"|failed to run custom build command"
    r"|failed to load manifest"
    r"|no matching package named\b"
    r"|target [`'][^`']+[`'] may not be installed"
    r")"
)
_STACK_OVERFLOW_RE = re.compile(
    r"has overflowed its stack|fatal runtime error: stack overflow"
)
_OOM_RE = re.compile(
    r"memory allocation of \d+ bytes failed|fatal runtime error:.*out of memory|"
    r"cannot allocate memory|\bout of memory\b",
    re.IGNORECASE,
)
_MIRI_UNSUPPORTED_RE = re.compile(r"(?m)^error: unsupported operation:")
_MIRI_ABNORMAL_TERM_RE = re.compile(r"(?m)^error: abnormal termination:")
_MIRI_INCONCLUSIVE_RE = re.compile(
    r"(?m)^error: (?:resource exhaustion:|memory leaked:|deadlock:|"
    r"the evaluated program\b)"
)
_MIRI_ERROR_RE = re.compile(r"(?m)^error(?:\[[^\]]+\])?:")
_RUSTC_ICE_RE = re.compile(
    r"(?m)^(?:thread 'rustc' panicked|error: internal compiler error:)"
)


def _read_regular_file_nofollow(
    path: Path,
    *,
    max_bytes: int | None = None,
    disallow_hardlink: bool = False,
    label: str = "file",
    exc_type: type[Exception] = InvalidSubmissionError,
) -> bytes:
    """Open regular non-symlink `path` via `O_NOFOLLOW` + `fstat` (no TOCTOU)."""
    try:
        fd = os.open(path, _OPEN_RO_FLAGS)
    except OSError as exc:
        raise exc_type(f"cannot open {label} {path}: {exc}") from exc
    try:
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise exc_type(f"non-regular {label} disallowed: {path}")
        if disallow_hardlink and fst.st_nlink > 1:
            raise exc_type(f"hardlink disallowed for {label}: {path}")
        if max_bytes is not None and fst.st_size > max_bytes:
            raise exc_type(f"{label} exceeds {max_bytes} bytes: {path}")
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            limit = (max_bytes + 1) if max_bytes is not None else -1
            data = handle.read(limit)
        if max_bytes is not None and len(data) > max_bytes:
            raise exc_type(f"{label} grew past {max_bytes} bytes: {path}")
        return data
    finally:
        if fd >= 0:
            os.close(fd)


@dataclass(frozen=True)
class _PinnedAssetSnapshot:
    """Content and inode/mode/link/ctime snapshot of a pinned defender asset."""

    sha256: str
    dev: int
    ino: int
    mode: int
    nlink: int
    ctime_ns: int
    mtime_ns: int


def _inspect_regular_nofollow(
    path: Path,
    *,
    exc_type: type[Exception] = OracleInfrastructureError,
) -> _PinnedAssetSnapshot:
    """Hash and `fstat` regular non-symlink `path` via a single `O_NOFOLLOW` fd."""
    try:
        fd = os.open(path, _OPEN_RO_FLAGS)
    except OSError as exc:
        raise exc_type(f"cannot inspect {path}: {exc}") from exc
    try:
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise exc_type(f"non-regular file disallowed: {path}")
        hasher = hashlib.sha256()
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            while chunk := handle.read(65_536):
                hasher.update(chunk)
        return _PinnedAssetSnapshot(
            sha256=hasher.hexdigest(),
            dev=fst.st_dev,
            ino=fst.st_ino,
            mode=fst.st_mode,
            nlink=fst.st_nlink,
            ctime_ns=fst.st_ctime_ns,
            mtime_ns=fst.st_mtime_ns,
        )
    finally:
        if fd >= 0:
            os.close(fd)


def _sha256_regular_nofollow(
    path: Path,
    *,
    exc_type: type[Exception] = OracleInfrastructureError,
) -> str:
    """Hash regular non-symlink `path` via a single `O_NOFOLLOW` + `fstat` fd."""
    return _inspect_regular_nofollow(path, exc_type=exc_type).sha256


def _write_new_regular_file_excl(dest: Path, data: bytes) -> None:
    """Create a fresh non-symlink regular file exclusively (`O_CREAT | O_EXCL`)."""
    try:
        dest.parent.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise InvalidSubmissionError(
            f"cannot create parent directory for {dest.name}: {exc}"
        ) from exc
    try:
        fd = os.open(
            dest,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | _NOFOLLOW_FLAG,
            0o644,
        )
    except FileExistsError as exc:
        raise InvalidSubmissionError(
            f"submission path collides with existing file: {dest.name}"
        ) from exc
    except OSError as exc:
        raise InvalidSubmissionError(
            f"cannot create submission file {dest.name}: {exc}"
        ) from exc
    try:
        with os.fdopen(fd, "wb") as handle:
            fd = -1
            handle.write(data)
    finally:
        if fd >= 0:
            os.close(fd)


class _BoundedReadStream(io.RawIOBase):
    """Fail closed once decompressed tar input exceeds `limit` bytes."""

    def __init__(self, inner: Any, limit: int) -> None:
        self._inner = inner
        self._limit = limit
        self._seen = 0

    def readable(self) -> bool:
        return True

    def read(self, size: int = -1) -> bytes:
        if size is not None and size >= 0:
            chunk = self._inner.read(size)
            if not chunk:
                return b""
            self._seen += len(chunk)
            if self._seen > self._limit:
                raise InvalidSubmissionError(
                    f"decompressed tar stream exceeds {self._limit} bytes"
                )
            return chunk
        parts: list[bytes] = []
        while True:
            chunk = self._inner.read(65_536)
            if not chunk:
                break
            self._seen += len(chunk)
            if self._seen > self._limit:
                raise InvalidSubmissionError(
                    f"decompressed tar stream exceeds {self._limit} bytes"
                )
            parts.append(chunk)
        return b"".join(parts)


def _check_case_colliding_paths(relpaths: Iterable[str]) -> None:
    """Reject paths or directory segments colliding under Unicode case-folding."""
    seen_segments: dict[tuple[str, str], str] = {}
    seen_files: dict[str, str] = {}
    for rel in sorted(relpaths):
        parts = rel.split("/")
        folded_parts = [part.casefold() for part in parts]
        folded_full = "/".join(folded_parts)
        prev_file = seen_files.get(folded_full)
        if prev_file is not None and prev_file != rel:
            raise InvalidSubmissionError(
                f"case-colliding submission paths disallowed: {prev_file!r} vs {rel!r}"
            )
        seen_files[folded_full] = rel
        parent_folded = ""
        for idx, (orig_seg, fold_seg) in enumerate(zip(parts, folded_parts)):
            key = (parent_folded, fold_seg)
            prev_seg = seen_segments.get(key)
            if prev_seg is not None and prev_seg != orig_seg:
                conflict_prefix = (
                    f"{parent_folded}/{prev_seg}" if parent_folded else prev_seg
                )
                cur_prefix = (
                    f"{parent_folded}/{orig_seg}" if parent_folded else orig_seg
                )
                raise InvalidSubmissionError(
                    "case-colliding submission path components disallowed: "
                    f"{conflict_prefix!r} vs {cur_prefix!r}"
                )
            seen_segments[key] = orig_seg
            if idx < len(parts) - 1:
                parent_folded = (
                    f"{parent_folded}/{fold_seg}" if parent_folded else fold_seg
                )


def _read_fd_regular_file(
    fd: int,
    *,
    rel: str,
    max_bytes: int,
    disallow_hardlink: bool = True,
) -> bytes:
    """Validate `fstat` and read bounded bytes from an already-opened fd."""
    try:
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise InvalidSubmissionError(f"non-regular file {rel} disallowed")
        if disallow_hardlink and fst.st_nlink > 1:
            raise InvalidSubmissionError(f"hardlink disallowed for file {rel}")
        if fst.st_size > max_bytes:
            raise InvalidSubmissionError(
                f"file {rel} exceeds {max_bytes} bytes"
            )
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read(max_bytes + 1)
        if len(data) > max_bytes:
            raise InvalidSubmissionError(
                f"file {rel} grew past {max_bytes} bytes"
            )
        return data
    finally:
        if fd >= 0:
            os.close(fd)


def _load_submission_dir(sub_dir: Path) -> dict[str, bytes]:
    """Read regular files from `sub_dir` using pinned `dir_fd` opens (no TOCTOU)."""
    try:
        root_fd = os.open(sub_dir, _DIR_RO_FLAGS)
    except OSError as exc:
        raise InvalidSubmissionError(
            f"cannot inspect submission dir {sub_dir}: {exc}"
        ) from exc

    files: dict[str, bytes] = {}
    dir_count = 0
    total_bytes = 0

    _MAX_SUBMISSION_DIR_ENTRIES = MAX_SUBMISSION_FILES + MAX_SUBMISSION_DIRS

    def _walk_dir_fd(cur_fd: int, rel_prefix: str, depth: int) -> None:
        nonlocal dir_count, total_bytes
        raw_names: list[str] = []
        with os.scandir(cur_fd) as entries:
            for entry in entries:
                if len(raw_names) >= _MAX_SUBMISSION_DIR_ENTRIES:
                    raise InvalidSubmissionError(
                        f"submission directory exceeds "
                        f"{_MAX_SUBMISSION_DIR_ENTRIES} entries"
                    )
                raw_names.append(entry.name)
        for name in sorted(raw_names):
            candidate = f"{rel_prefix}/{name}" if rel_prefix else name
            try:
                est = os.stat(name, dir_fd=cur_fd, follow_symlinks=False)
            except OSError as exc:
                raise InvalidSubmissionError(
                    f"cannot inspect submission entry {candidate}: {exc}"
                ) from exc
            if stat.S_ISLNK(est.st_mode):
                raise InvalidSubmissionError(
                    f"symlink disallowed in submission: {candidate}"
                )
            if stat.S_ISDIR(est.st_mode):
                if depth + 1 > MAX_SUBMISSION_DEPTH:
                    raise InvalidSubmissionError(
                        f"submission directory depth exceeds {MAX_SUBMISSION_DEPTH}: "
                        f"{candidate}"
                    )
                dir_count += 1
                if dir_count > MAX_SUBMISSION_DIRS:
                    raise InvalidSubmissionError(
                        f"submission exceeds {MAX_SUBMISSION_DIRS} directory limit"
                    )
                rel_d = _validate_rel_posix(candidate)
                try:
                    child_fd = os.open(name, _DIR_RO_FLAGS, dir_fd=cur_fd)
                except OSError as exc:
                    raise InvalidSubmissionError(
                        f"cannot open submission dir {rel_d}: {exc}"
                    ) from exc
                try:
                    cst = os.fstat(child_fd)
                    if not stat.S_ISDIR(cst.st_mode):
                        raise InvalidSubmissionError(
                            f"non-directory disallowed: {rel_d}"
                        )
                    _walk_dir_fd(child_fd, rel_d, depth + 1)
                finally:
                    os.close(child_fd)
            elif stat.S_ISREG(est.st_mode):
                rel = _validate_rel_posix(candidate)
                if len(files) >= MAX_SUBMISSION_FILES:
                    raise InvalidSubmissionError(
                        f"submission exceeds {MAX_SUBMISSION_FILES} file limit"
                    )
                try:
                    file_fd = os.open(name, _OPEN_RO_FLAGS, dir_fd=cur_fd)
                except OSError as exc:
                    raise InvalidSubmissionError(
                        f"cannot open submission file {rel}: {exc}"
                    ) from exc
                data = _read_fd_regular_file(
                    file_fd,
                    rel=rel,
                    max_bytes=MAX_SUBMISSION_FILE_BYTES,
                    disallow_hardlink=True,
                )
                total_bytes += len(data)
                if total_bytes > MAX_SUBMISSION_TOTAL_BYTES:
                    raise InvalidSubmissionError(
                        f"total submission exceeds {MAX_SUBMISSION_TOTAL_BYTES} bytes"
                    )
                files[rel] = data
            else:
                raise InvalidSubmissionError(
                    f"non-regular submission entry disallowed: {candidate}"
                )

    try:
        root_st = os.fstat(root_fd)
        if not stat.S_ISDIR(root_st.st_mode):
            raise InvalidSubmissionError(
                f"submission dir must be a real non-symlink directory: {sub_dir}"
            )
        _walk_dir_fd(root_fd, "", 0)
    finally:
        os.close(root_fd)

    _check_case_colliding_paths(files.keys())
    return files


class _BoundedLzmaStream(io.RawIOBase):
    """Stream XZ tar payloads with a hard decompressor memory cap."""

    def __init__(self, raw_fh: Any, memlimit: int) -> None:
        self._raw = raw_fh
        self._memlimit = memlimit
        self._decomp: lzma.LZMADecompressor | None = None
        self._in_buf = bytearray()
        self._out_buf = bytearray()
        self._eof = False

    def readable(self) -> bool:
        return True

    def read(self, size: int | None = -1) -> bytes:
        want = -1 if size is None else int(size)
        if want == 0:
            return b""
        while not self._eof and (want < 0 or len(self._out_buf) < want):
            if self._decomp is None:
                while not self._eof:
                    if len(self._in_buf) >= 4 and self._in_buf[:4] == b"\x00\x00\x00\x00":
                        del self._in_buf[:4]
                        continue
                    if self._in_buf:
                        break
                    raw = self._raw.read(65_536)
                    if not raw:
                        self._eof = True
                        break
                    self._in_buf.extend(raw)
                if self._eof:
                    break
                self._decomp = lzma.LZMADecompressor(
                    format=lzma.FORMAT_XZ, memlimit=self._memlimit
                )
            if self._decomp.needs_input:
                if not self._in_buf:
                    raw = self._raw.read(65_536)
                    if not raw:
                        raise lzma.LZMAError("truncated XZ archive")
                    self._in_buf.extend(raw)
                inp = bytes(self._in_buf)
                self._in_buf.clear()
            else:
                inp = b""
            cap = (
                65_536
                if want < 0
                else min(max(want - len(self._out_buf), 1), 65_536)
            )
            out = self._decomp.decompress(inp, max_length=cap)
            if out:
                self._out_buf.extend(out)
            if self._decomp.eof:
                if self._decomp.unused_data:
                    self._in_buf.extend(self._decomp.unused_data)
                self._decomp = None
        if want < 0 or len(self._out_buf) <= want:
            res = bytes(self._out_buf)
            self._out_buf.clear()
            return res
        res = bytes(self._out_buf[:want])
        del self._out_buf[:want]
        return res


def _open_bounded_tar_stream(raw_fh: Any) -> Any:
    """Detect compression header and wrap decompressor with byte budget."""
    head = raw_fh.read(6)
    raw_fh.seek(0)
    if head.startswith(b"\x1f\x8b"):
        decomp: Any = gzip.GzipFile(fileobj=raw_fh, mode="rb")
    elif head.startswith(b"BZh"):
        decomp = bz2.BZ2File(raw_fh, mode="rb")
    elif head.startswith(b"\xfd7zXZ\x00"):
        decomp = _BoundedLzmaStream(raw_fh, MAX_XZ_DECOMPRESS_MEM_BYTES)
    else:
        decomp = raw_fh
    return _BoundedReadStream(decomp, MAX_TAR_UNCOMPRESSED_BYTES)


def _load_submission_tar(tar_path: Path) -> dict[str, bytes]:
    """Read regular files from `tar_path` safely in bounded streaming mode."""
    try:
        fd = os.open(tar_path, _OPEN_RO_FLAGS)
    except OSError as exc:
        raise InvalidSubmissionError(
            f"cannot inspect submission tar {tar_path}: {exc}"
        ) from exc
    try:
        tst = os.fstat(fd)
        if not stat.S_ISREG(tst.st_mode):
            raise InvalidSubmissionError(
                f"submission tar must be a regular non-symlink file: {tar_path}"
            )
        if tst.st_size > MAX_SUBMISSION_TAR_BYTES:
            raise InvalidSubmissionError(
                f"submission tar exceeds {MAX_SUBMISSION_TAR_BYTES} bytes"
            )
        raw_ctx = os.fdopen(fd, "rb")
        fd = -1
    finally:
        if fd >= 0:
            os.close(fd)

    files: dict[str, bytes] = {}
    total_bytes = 0
    seen_members = 0
    dir_count = 0
    try:
        with raw_ctx as raw_fh:
            bounded_stream = _open_bounded_tar_stream(raw_fh)
            with tarfile.open(fileobj=bounded_stream, mode="r|") as tf:
                while True:
                    member = tf.next()
                    if member is None:
                        break
                    seen_members += 1
                    if seen_members > MAX_TAR_MEMBERS:
                        raise InvalidSubmissionError(
                            f"tar archive exceeds {MAX_TAR_MEMBERS} members"
                        )
                    if member.pax_headers:
                        pax_bytes = sum(
                            len(str(k)) + len(str(v))
                            for k, v in member.pax_headers.items()
                        )
                        if pax_bytes > MAX_TAR_PAX_BYTES:
                            raise InvalidSubmissionError(
                                "tar member PAX metadata exceeds "
                                f"{MAX_TAR_PAX_BYTES} bytes"
                            )
                    if member.issym() or member.islnk():
                        raise InvalidSubmissionError(
                            "symlink/hardlink tar member disallowed: "
                            f"{member.name!r}"
                        )
                    if member.isdir():
                        raw = member.name.rstrip("/")
                        if raw not in ("", "."):
                            rel_d = _validate_rel_posix(raw, allow_dot_prefix=True)
                            if rel_d.count("/") + 1 > MAX_SUBMISSION_DEPTH:
                                raise InvalidSubmissionError(
                                    f"submission directory depth exceeds {MAX_SUBMISSION_DEPTH}: "
                                    f"{rel_d}"
                                )
                            dir_count += 1
                            if dir_count > MAX_SUBMISSION_DIRS:
                                raise InvalidSubmissionError(
                                    f"submission exceeds {MAX_SUBMISSION_DIRS} directory limit"
                                )
                        continue
                    if not member.isreg() or member.type != tarfile.REGTYPE:
                        raise InvalidSubmissionError(
                            f"special tar member disallowed: {member.name!r}"
                        )
                    rel = _validate_rel_posix(
                        member.name, allow_dot_prefix=True
                    )
                    if rel.count("/") > MAX_SUBMISSION_DEPTH:
                        raise InvalidSubmissionError(
                            f"submission directory depth exceeds {MAX_SUBMISSION_DEPTH}: {rel}"
                        )
                    if rel in files:
                        raise InvalidSubmissionError(
                            f"duplicate tar archive path: {rel}"
                        )
                    if len(files) >= MAX_SUBMISSION_FILES:
                        raise InvalidSubmissionError(
                            f"submission exceeds {MAX_SUBMISSION_FILES} file limit"
                        )
                    if (
                        member.size < 0
                        or member.size > MAX_SUBMISSION_FILE_BYTES
                    ):
                        raise InvalidSubmissionError(
                            f"tar member exceeds {MAX_SUBMISSION_FILE_BYTES}: {rel}"
                        )
                    extracted = tf.extractfile(member)
                    if extracted is None:
                        raise InvalidSubmissionError(
                            f"unreadable tar member: {rel}"
                        )
                    chunks: list[bytes] = []
                    read_len = 0
                    with extracted:
                        while True:
                            chunk = extracted.read(65_536)
                            if not chunk:
                                break
                            read_len += len(chunk)
                            if (
                                read_len > MAX_SUBMISSION_FILE_BYTES
                                or total_bytes + read_len > MAX_SUBMISSION_TOTAL_BYTES
                            ):
                                raise InvalidSubmissionError(
                                    "tar payload exceeds submission byte cap: "
                                    f"{rel}"
                                )
                            chunks.append(chunk)
                    if read_len != member.size:
                        raise InvalidSubmissionError(
                            f"tar member size mismatch: {rel}"
                        )
                    total_bytes += read_len
                    files[rel] = b"".join(chunks)
            # Drain remaining compressed bytes so container footers/CRC and
            # trailing uncompressed byte caps are still validated after tar EOF.
            while bounded_stream.read(65_536):
                pass
    except (
        tarfile.TarError,
        lzma.LZMAError,
        zlib.error,
        gzip.BadGzipFile,
        EOFError,
        UnicodeError,
        RecursionError,
        OSError,
        ValueError,
    ) as exc:
        raise InvalidSubmissionError(f"invalid submission tar: {exc}") from exc
    _check_case_colliding_paths(files.keys())
    return files


def _validate_lean_slot_path(
    relpath: str, prefix: str, *, allow_reserved_root: bool = False
) -> str:
    """Validate `<prefix>/<Mod>.lean` and return its dotted Lean module name."""
    _validate_rel_path_lengths(relpath)
    if not relpath.startswith(f"{prefix}/") or not relpath.endswith(".lean"):
        raise InvalidSubmissionError(
            f"unexpected path outside `{prefix}/*.lean` slot: {relpath}"
        )
    sub = relpath[len(prefix) + 1 : -len(".lean")]
    parts = sub.split("/")
    if not parts or any(not _LEAN_IDENT_RE.match(p) for p in parts):
        raise InvalidSubmissionError(
            f"invalid Lean module path segment in {relpath}"
        )
    if not allow_reserved_root and parts[0] in _RESERVED_LEAN_ROOTS:
        raise InvalidSubmissionError(
            f"reserved Lean root module disallowed in {relpath}"
        )
    return ".".join(parts)


def _loads_submission_json(raw: bytes, *, label: str) -> Any:
    """Decode bounded UTF-8 JSON from untrusted submissions fail-closed."""
    try:
        return json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
    except (
        UnicodeDecodeError,
        ValueError,
        json.JSONDecodeError,
        RecursionError,
        TypeError,
    ) as exc:
        raise InvalidSubmissionError(f"invalid {label}: {exc}") from exc


def _parse_witness_json(raw: bytes) -> tuple[int, ...]:
    """Parse strict `witness.json` (`{\"args\": [<u32>, ...]}`)."""
    if len(raw) > MAX_WITNESS_BYTES:
        raise InvalidSubmissionError(
            f"witness.json exceeds {MAX_WITNESS_BYTES} bytes"
        )
    data = _loads_submission_json(raw, label="witness.json")
    if not isinstance(data, dict) or set(data.keys()) != {"args"}:
        raise InvalidSubmissionError(
            "witness.json must be a JSON object with exact key `args`"
        )
    args = data["args"]
    if not isinstance(args, list) or len(args) > MAX_WITNESS_ARGS:
        raise InvalidSubmissionError(
            f"witness.json `args` must be a list of <= {MAX_WITNESS_ARGS} ints"
        )
    parsed: list[int] = []
    for item in args:
        if isinstance(item, bool) or not isinstance(item, int):
            raise InvalidSubmissionError(
                f"witness.json arg must be an exact integer: {item!r}"
            )
        if item < 0 or item > 0xFFFF_FFFF:
            raise InvalidSubmissionError(
                f"witness.json arg out of u32 range: {item}"
            )
        parsed.append(item)
    return tuple(parsed)


def _parse_diff_ab_path(raw: str, prefix: str) -> str:
    path = raw.split("\t", 1)[0].strip()
    if path == "/dev/null" or not path.startswith(prefix):
        raise InvalidSubmissionError(
            f"semantics.patch header must target `{prefix}*`: {raw!r}"
        )
    rel = _validate_rel_posix(path[len(prefix) :])
    return rel


_NO_NEWLINE_MARKER = r"\ No newline at end of file"


def _parse_and_validate_semantics_patch(
    raw: bytes,
) -> tuple[
    tuple[str, ...],
    int,
    dict[str, list[tuple[int, int, int, int, list[str]]]],
]:
    """Parse and validate unified diff scoped strictly to `MirSemantics/*.lean`.

    Shared single source of truth for slot validation and patch application so
    count caps and hunk boundaries cannot diverge between checking and applying.
    """
    if not raw:
        raise InvalidSubmissionError("incorrectness/semantics.patch is empty")
    if b"\x00" in raw or b"\r" in raw:
        raise InvalidSubmissionError(
            "incorrectness/semantics.patch must use LF without NUL or CR bytes"
        )
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise InvalidSubmissionError(
            f"incorrectness/semantics.patch must be UTF-8: {exc}"
        ) from exc

    lines = text.splitlines(keepends=True)
    file_hunks: dict[str, list[tuple[int, int, int, int, list[str]]]] = {}
    changed_lines = 0
    cur_rel: str | None = None
    idx = 0
    _FORBIDDEN_GIT_LINES = (
        "new file mode ",
        "deleted file mode ",
        "old mode ",
        "new mode ",
        "rename from ",
        "rename to ",
        "copy from ",
        "copy to ",
        "GIT binary patch",
        "Binary files ",
    )

    while idx < len(lines):
        line = lines[idx]
        no_eol = line[:-1] if line.endswith("\n") else line
        if any(no_eol.startswith(tok) for tok in _FORBIDDEN_GIT_LINES):
            raise InvalidSubmissionError(
                f"disallowed patch metadata in semantics.patch: {no_eol!r}"
            )
        if no_eol.startswith("diff --git "):
            cur_rel = None
            parts = no_eol[len("diff --git ") :].split(" ")
            if (
                len(parts) != 2
                or not parts[0].startswith("a/")
                or not parts[1].startswith("b/")
            ):
                raise InvalidSubmissionError(
                    f"malformed diff header in semantics.patch: {no_eol!r}"
                )
            a_rel = _validate_rel_posix(parts[0][2:])
            b_rel = _validate_rel_posix(parts[1][2:])
            if a_rel != b_rel:
                raise InvalidSubmissionError(
                    f"renames/cross-file diffs disallowed in semantics.patch: "
                    f"{a_rel} -> {b_rel}"
                )
            if (
                not a_rel.startswith(_MIR_SEMANTICS_PATCH_PREFIX)
                or not a_rel.endswith(".lean")
                or "/" in a_rel[len(_MIR_SEMANTICS_PATCH_PREFIX) :]
                or a_rel in _FORBIDDEN_MIR_SEMANTICS_PATCH_FILES
            ):
                raise InvalidSubmissionError(
                    "semantics.patch may only modify operational modules "
                    f"directly under `{_MIR_SEMANTICS_PATCH_PREFIX}*.lean`: "
                    f"{a_rel}"
                )
            idx += 1
            continue
        if no_eol.startswith("index "):
            idx += 1
            continue
        if no_eol.startswith("--- "):
            old_rel = _parse_diff_ab_path(no_eol[4:], "a/")
            idx += 1
            if idx >= len(lines):
                raise InvalidSubmissionError(
                    "semantics.patch has `---` without matching `+++`"
                )
            plus_no_eol = (
                lines[idx][:-1] if lines[idx].endswith("\n") else lines[idx]
            )
            if not plus_no_eol.startswith("+++ "):
                raise InvalidSubmissionError(
                    "semantics.patch has `---` without matching `+++`"
                )
            new_rel = _parse_diff_ab_path(plus_no_eol[4:], "b/")
            if new_rel != old_rel:
                raise InvalidSubmissionError(
                    f"semantics.patch target mismatch: {old_rel} vs {new_rel}"
                )
            if (
                not new_rel.startswith(_MIR_SEMANTICS_PATCH_PREFIX)
                or not new_rel.endswith(".lean")
                or "/" in new_rel[len(_MIR_SEMANTICS_PATCH_PREFIX) :]
                or new_rel in _FORBIDDEN_MIR_SEMANTICS_PATCH_FILES
            ):
                raise InvalidSubmissionError(
                    "semantics.patch may only modify operational modules "
                    f"directly under `{_MIR_SEMANTICS_PATCH_PREFIX}*.lean`: "
                    f"{new_rel}"
                )
            if new_rel in file_hunks:
                raise InvalidSubmissionError(
                    f"duplicate file header in semantics.patch: {new_rel}"
                )
            cur_rel = new_rel
            file_hunks[cur_rel] = []
            idx += 1
            continue
        if no_eol.startswith("+++ "):
            raise InvalidSubmissionError(
                "semantics.patch has `+++` without matching `---`"
            )
        if no_eol.startswith("@@ "):
            if cur_rel is None:
                raise InvalidSubmissionError(
                    "semantics.patch hunk precedes file header"
                )
            m = re.match(
                r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", no_eol
            )
            if not m:
                raise InvalidSubmissionError(
                    f"malformed hunk header in semantics.patch: {no_eol!r}"
                )
            o_start = int(m.group(1))
            o_count = int(m.group(2)) if m.group(2) is not None else 1
            n_start = int(m.group(3))
            n_count = int(m.group(4)) if m.group(4) is not None else 1
            idx += 1
            hunk_body: list[str] = []
            seen_o = 0
            seen_n = 0
            last_op = ""
            while seen_o < o_count or seen_n < n_count:
                if idx >= len(lines):
                    raise InvalidSubmissionError(
                        f"truncated hunk in semantics.patch ({cur_rel})"
                    )
                hline = lines[idx]
                hbody = hline[:-1] if hline.endswith("\n") else hline
                if hbody.startswith(" "):
                    seen_o += 1
                    seen_n += 1
                    last_op = " "
                elif hbody.startswith("-"):
                    seen_o += 1
                    changed_lines += 1
                    last_op = "-"
                elif hbody.startswith("+"):
                    seen_n += 1
                    changed_lines += 1
                    last_op = "+"
                elif hbody == _NO_NEWLINE_MARKER and last_op in ("-", "+", " "):
                    last_op = "\\"
                else:
                    raise InvalidSubmissionError(
                        f"unexpected line inside hunk in {cur_rel}: {hbody!r}"
                    )
                if changed_lines > MAX_INCORRECTNESS_PATCH_CHANGED_LINES:
                    raise InvalidSubmissionError(
                        "incorrectness/semantics.patch exceeds "
                        f"{MAX_INCORRECTNESS_PATCH_CHANGED_LINES} changed "
                        "line limit"
                    )
                hunk_body.append(hline)
                idx += 1
            if seen_o != o_count or seen_n != n_count:
                raise InvalidSubmissionError(
                    f"hunk line count mismatch in {cur_rel}"
                )
            if idx < len(lines):
                nxt_body = (
                    lines[idx][:-1] if lines[idx].endswith("\n") else lines[idx]
                )
                if nxt_body == _NO_NEWLINE_MARKER and last_op in ("+", "-", " "):
                    hunk_body.append(lines[idx])
                    idx += 1
            file_hunks[cur_rel].append(
                (o_start, o_count, n_start, n_count, hunk_body)
            )
            continue
        if not no_eol:
            idx += 1
            continue
        raise InvalidSubmissionError(
            f"unexpected line outside hunk in semantics.patch: {no_eol!r}"
        )

    total_hunks = sum(len(hs) for hs in file_hunks.values())
    if not file_hunks or total_hunks == 0 or changed_lines == 0:
        raise InvalidSubmissionError(
            "incorrectness/semantics.patch must contain at least one valid hunk"
        )
    return tuple(sorted(file_hunks)), changed_lines, file_hunks


def _parse_semantics_patch(raw: bytes) -> tuple[tuple[str, ...], int]:
    """Strictly validate unified diff scoped to `Trusted/MirSemantics/*.lean`."""
    targets, changed_lines, _hunks = _parse_and_validate_semantics_patch(raw)
    return targets, changed_lines


def _validate_incorrectness_claim(raw: bytes) -> str:
    """Validate optional Tier-E2 `incorrectness/claim.md` Markdown claim."""
    if len(raw) > MAX_INCORRECTNESS_CLAIM_BYTES:
        raise InvalidSubmissionError(
            f"incorrectness/claim.md exceeds {MAX_INCORRECTNESS_CLAIM_BYTES} bytes"
        )
    if b"\x00" in raw:
        raise InvalidSubmissionError(
            "incorrectness/claim.md must not contain NUL bytes"
        )
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise InvalidSubmissionError(
            f"incorrectness/claim.md must be valid UTF-8: {exc}"
        ) from exc
    if not text.strip():
        raise InvalidSubmissionError("incorrectness/claim.md must not be empty")
    return text


def _validate_manifest_json(raw: bytes) -> None:
    """Validate optional advisory `manifest.json` without trusting claims."""
    if len(raw) > MAX_WITNESS_BYTES:
        raise InvalidSubmissionError(
            f"manifest.json exceeds {MAX_WITNESS_BYTES} bytes"
        )
    data = _loads_submission_json(raw, label="manifest.json")
    if not isinstance(data, dict):
        raise InvalidSubmissionError("manifest.json must be a JSON object")


def _validate_scenario_slots(
    spec: scenarios.ScenarioSpec, files: dict[str, bytes]
) -> LoadedSubmission:
    """Enforce exact scenario slot allowlists and required entry files."""
    if not files:
        raise InvalidSubmissionError("submission contains no files")
    _check_case_colliding_paths(files.keys())

    if "manifest.json" in files:
        _validate_manifest_json(files["manifest.json"])

    payload_files = {k: v for k, v in files.items() if k != "manifest.json"}
    if not payload_files:
        raise InvalidSubmissionError("submission contains only manifest.json")

    witness_args: tuple[int, ...] = ()
    if spec.kind == "PROOF_HACK":
        for relpath in payload_files:
            _validate_lean_slot_path(relpath, "Proof")
        if "Proof/Proof.lean" not in payload_files:
            raise InvalidSubmissionError("missing required `Proof/Proof.lean`")
    elif spec.kind == "SPEC_PREFLIGHT_HACK":
        if "Spec.lean" in payload_files and "Spec/Spec.lean" in payload_files:
            raise InvalidSubmissionError(
                "cannot supply both `Spec.lean` and `Spec/Spec.lean`"
            )
        for relpath in payload_files:
            if relpath == "Spec.lean":
                continue
            _validate_lean_slot_path(relpath, "Spec")
        if (
            "Spec.lean" not in payload_files
            and "Spec/Spec.lean" not in payload_files
        ):
            raise InvalidSubmissionError(
                "missing required `Spec.lean` or `Spec/Spec.lean`"
            )
    elif spec.kind == "CODE_AND_PROOF_HACK":
        has_lib = False
        has_proof = False
        witness_seen = False
        has_e1_patch = False
        has_e1_proof = False
        has_e1_helper = False
        has_e2 = False
        e1_targets: tuple[str, ...] = ()
        e1_changed_lines = 0
        claim_text: str | None = None
        for relpath, data in payload_files.items():
            if relpath == "witness.json" or (
                relpath.startswith("witness/")
                and relpath.endswith(".json")
                and "/" not in relpath[len("witness/") :]
            ):
                if witness_seen:
                    raise InvalidSubmissionError(
                        "at most one witness JSON file is allowed"
                    )
                witness_seen = True
                witness_args = _parse_witness_json(data)
            elif relpath.startswith("src/"):
                if not relpath.endswith(".rs") or relpath == "src/build.rs":
                    raise InvalidSubmissionError(
                        f"disallowed file in `src/` slot: {relpath}"
                    )
                segs = relpath[len("src/") :].split("/")
                if any(not _RUST_SEG_RE.match(s) for s in segs):
                    raise InvalidSubmissionError(
                        f"invalid Rust source path: {relpath}"
                    )
                if relpath == "src/lib.rs":
                    has_lib = True
            elif relpath.startswith("Proof/"):
                _validate_lean_slot_path(relpath, "Proof")
                if relpath == "Proof/Proof.lean":
                    has_proof = True
            elif relpath == "incorrectness/semantics.patch":
                has_e1_patch = True
                e1_targets, e1_changed_lines = _parse_semantics_patch(data)
            elif relpath == "incorrectness/Proof.lean":
                has_e1_proof = True
                _validate_lean_slot_path(relpath, "incorrectness")
            elif relpath.startswith("incorrectness/Helper/"):
                has_e1_helper = True
                _validate_lean_slot_path(relpath, "incorrectness")
            elif relpath == "incorrectness/claim.md":
                has_e2 = True
                claim_text = _validate_incorrectness_claim(data)
            else:
                raise InvalidSubmissionError(
                    f"out-of-slot path disallowed: {relpath}"
                )
        if not has_lib:
            raise InvalidSubmissionError("missing required `src/lib.rs`")
        if not has_proof:
            raise InvalidSubmissionError("missing required `Proof/Proof.lean`")
        if has_e1_patch or has_e1_proof or has_e1_helper:
            if not (has_e1_patch and has_e1_proof):
                raise InvalidSubmissionError(
                    "Tier-E1 requires both `incorrectness/semantics.patch` and "
                    "`incorrectness/Proof.lean`"
                )
        has_e1 = has_e1_patch and has_e1_proof
    elif spec.kind == "THEORY_AUDIT_HACK":
        for relpath in payload_files:
            _validate_lean_slot_path(
                relpath, "theory", allow_reserved_root=True
            )
        has_e1 = False
        has_e2 = False
        e1_targets = ()
        e1_changed_lines = 0
        claim_text = None
    else:
        raise OracleInfrastructureError(f"unknown scenario kind {spec.kind!r}")

    if spec.kind not in ("CODE_AND_PROOF_HACK", "THEORY_AUDIT_HACK"):
        has_e1 = False
        has_e2 = False
        e1_targets = ()
        e1_changed_lines = 0
        claim_text = None

    return LoadedSubmission(
        files=payload_files,
        witness_args=witness_args,
        e1_patch_targets=e1_targets,
        e1_patch_changed_lines=e1_changed_lines,
        has_e1=has_e1,
        has_e2=has_e2,
        claim_text=claim_text,
    )


def _build_scrubbed_env(
    sysroot: Path | None,
    *,
    miri_sysroot: Path | None = None,
) -> dict[str, str]:
    """Construct minimal deterministic subprocess environment from allowlist."""
    env: dict[str, str] = {}
    for key in _ALLOWED_ENV_KEYS:
        val = os.environ.get(key)
        if val:
            env[key] = val
    env["NO_COLOR"] = "1"
    env["CARGO_NET_OFFLINE"] = "true"
    if sysroot is not None:
        lib_dir = str(sysroot / "lib")
        env["LD_LIBRARY_PATH"] = lib_dir
        env["DYLD_LIBRARY_PATH"] = lib_dir
    if miri_sysroot is not None:
        env["MIRI_SYSROOT"] = str(miri_sysroot)
    return env


def _snapshot_tree_hashes(
    root: Path, relpaths: list[str]
) -> dict[str, _PinnedAssetSnapshot]:
    """Snapshot SHA-256 and file metadata of defender files in private memory.

    Note: Invoked exclusively before untrusted execution; any defect here is
    pre-run defender setup infrastructure (`OracleInfrastructureError`).
    """
    snapshots: dict[str, _PinnedAssetSnapshot] = {}
    for rel in sorted(relpaths):
        path = root / rel
        snapshots[rel] = _inspect_regular_nofollow(
            path, exc_type=OracleInfrastructureError
        )
    return snapshots


def _verify_tree_hashes(
    root: Path, expected: dict[str, _PinnedAssetSnapshot | str]
) -> None:
    """Detect in-run sandbox escapes mutating defender-owned assets or metadata.

    Primary enforcement comes from pre-run staging verification plus OS
    confinement (`ExecSeal`); post-run verification catches rule-following
    executions that escaped confinement or replaced/relinked/chmodded assets.
    """
    tampered: list[str] = []
    reasons: list[str] = []
    for rel, exp in sorted(expected.items()):
        cur_parent = root
        parent_invalid = False
        for part in Path(rel).parts[:-1]:
            cur_parent = cur_parent / part
            try:
                pst = os.lstat(cur_parent)
            except OSError as exc:
                tampered.append(rel)
                reasons.append(f"invalid/missing parent ({rel}: {exc})")
                parent_invalid = True
                break
            if stat.S_ISLNK(pst.st_mode) or not stat.S_ISDIR(pst.st_mode):
                tampered.append(rel)
                reasons.append(f"non-directory/symlink parent ({rel})")
                parent_invalid = True
                break
        if parent_invalid:
            continue

        path = root / rel
        try:
            actual = _inspect_regular_nofollow(
                path, exc_type=OracleInfrastructureError
            )
        except OracleInfrastructureError as exc:
            tampered.append(rel)
            reasons.append(f"invalid/missing ({rel}: {exc})")
            continue
        if isinstance(exp, str):
            if actual.sha256 != exp:
                tampered.append(rel)
                reasons.append(f"checksum changed ({rel})")
            continue
        mismatch_fields: list[str] = []
        if actual.sha256 != exp.sha256:
            mismatch_fields.append("checksum")
        if actual.dev != exp.dev or actual.ino != exp.ino:
            mismatch_fields.append("inode")
        if actual.mode != exp.mode:
            mismatch_fields.append(f"mode {exp.mode:#o}->{actual.mode:#o}")
        if actual.nlink != exp.nlink:
            mismatch_fields.append(f"nlink {exp.nlink}->{actual.nlink}")
        if actual.ctime_ns != exp.ctime_ns or actual.mtime_ns != exp.mtime_ns:
            mismatch_fields.append("timestamps")
        if mismatch_fields:
            tampered.append(rel)
            reasons.append(f"{'/'.join(mismatch_fields)} changed ({rel})")
    if tampered:
        raise DefenderTamperError(
            "defender asset mutated during rule-following run: "
            + "; ".join(reasons),
            tampered_paths=tuple(tampered),
        )


def _collect_tree_regular_files(
    root: Path, *, exc_type: type[Exception]
) -> list[str]:
    """Return sorted relative paths of every regular file in `root`."""
    rels: list[str] = []
    if not root.exists():
        raise exc_type(f"expected defender directory missing: {root}")
    for cur_root, dirnames, filenames in os.walk(
        root, topdown=True, followlinks=False
    ):
        dirnames.sort()
        cur = Path(cur_root)
        for dname in dirnames:
            dpath = cur / dname
            rel_d = dpath.relative_to(root).as_posix()
            st = os.lstat(dpath)
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
                if exc_type is DefenderTamperError:
                    raise DefenderTamperError(
                        f"unexpected symlink/non-directory in defender tree: {rel_d}",
                        tampered_paths=(rel_d,),
                    )
                raise exc_type(
                    f"symlink/non-directory in defender tree disallowed: {rel_d}"
                )
        for fname in sorted(filenames):
            fpath = cur / fname
            rel_f = fpath.relative_to(root).as_posix()
            st = os.lstat(fpath)
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
                if exc_type is DefenderTamperError:
                    raise DefenderTamperError(
                        f"unexpected symlink/non-regular file in defender tree: {rel_f}",
                        tampered_paths=(rel_f,),
                    )
                raise exc_type(
                    f"symlink/non-regular file in defender tree disallowed: {rel_f}"
                )
            rels.append(rel_f)
    return sorted(rels)


def _snapshot_full_tree_hashes(root: Path) -> dict[str, _PinnedAssetSnapshot]:
    """Snapshot every regular file in `root` before untrusted execution."""
    rels = _collect_tree_regular_files(root, exc_type=OracleInfrastructureError)
    return _snapshot_tree_hashes(root, rels)


def _verify_full_tree_unchanged(
    root: Path, expected: dict[str, _PinnedAssetSnapshot]
) -> None:
    """Verify every file in `root` matches `expected` and no files were added."""
    _verify_tree_hashes(root, expected)
    actual_rels = _collect_tree_regular_files(root, exc_type=DefenderTamperError)
    extra = sorted(set(actual_rels) - set(expected))
    if extra:
        raise DefenderTamperError(
            "defender tree gained unexpected file(s): " + ", ".join(extra[:8]),
            tampered_paths=tuple(extra),
        )


def _snapshot_attacker_hashes(
    submission: LoadedSubmission,
) -> dict[str, str]:
    """Record attacker file SHA-256s in defender memory for reproducibility."""
    return {
        rel: _sha256_bytes(data)
        for rel, data in sorted(submission.files.items())
    }


def _is_scrub_safe_dir(path: Path) -> bool:
    """Return True if `path` is specific enough to scrub cleanly without masking."""
    try:
        resolved = path.resolve()
    except OSError:
        resolved = path
    blocked: set[Path] = {
        Path("/"),
        Path("/tmp"),
        Path("/var/tmp"),
        Path("/dev/shm"),
        Path("/var"),
        Path("/home"),
    }
    try:
        blocked.add(Path(tempfile.gettempdir()).resolve())
    except OSError:
        pass
    try:
        blocked.add(Path.home().resolve())
    except (RuntimeError, OSError):
        pass
    return resolved not in blocked


def _collect_private_roots(
    *,
    tmp_root: Path | None = None,
    anneal_root: Path | None = None,
    tools: dict[str, Path | None] | None = None,
    miri_sysroot: Path | None = None,
    submission_dir: Path | None = None,
    submission_tar: Path | None = None,
) -> tuple[tuple[str, str], ...]:
    """Collect ordered `(host_prefix, placeholder)` pairs for receipt scrubbing."""
    raw_pairs: list[tuple[str, str]] = []

    def _add(path_val: Path | str | None, tag: str) -> None:
        if not path_val:
            return
        try:
            p = Path(path_val)
        except (OSError, ValueError, TypeError):
            return
        for cand in (str(p),):
            if cand and cand != "/":
                raw_pairs.append((cand.rstrip("/") or cand, tag))
        try:
            res = str(p.resolve())
            if res and res != "/":
                raw_pairs.append((res.rstrip("/") or res, tag))
        except OSError:
            pass

    _add(tmp_root, "<ephemeral>")
    _add(anneal_root, "<anneal_root>")
    if anneal_root is not None:
        _add(anneal_root.parent, "<repo_root>")
    if tools:
        for k, v in sorted(tools.items()):
            tag = "<sysroot>" if k == "sysroot" else f"<tool:{k}>"
            _add(v, tag)
    _add(miri_sysroot, "<miri_sysroot>")
    if submission_dir is not None and _is_scrub_safe_dir(submission_dir):
        _add(submission_dir, "<submission_dir>")
    if submission_tar is not None:
        _add(submission_tar, "<submission_tar>")
        if _is_scrub_safe_dir(submission_tar.parent):
            _add(submission_tar.parent, "<submission_dir>")
    _add(os.environ.get("CARGO_TARGET_DIR", "").strip(), "<cargo_target>")
    _add(os.environ.get("CARGO_HOME", "").strip(), "<cargo_home>")
    _add(os.environ.get("RUSTUP_HOME", "").strip(), "<rustup_home>")
    try:
        home = Path.home()
        _add(home / ".cargo", "<cargo_home>")
        _add(home / ".rustup", "<rustup_home>")
        _add(home, "<home>")
    except (RuntimeError, OSError):
        pass

    deduped: dict[str, str] = {}
    for prefix, tag in raw_pairs:
        deduped.setdefault(prefix, tag)
    return tuple(
        sorted(deduped.items(), key=lambda kv: (-len(kv[0]), kv[0]))
    )


def _sanitize_snippet(
    text: str | None,
    *,
    tmp_root: Path | None = None,
    private_roots: tuple[tuple[str, str], ...] = (),
    limit: int = 2000,
) -> str | None:
    """Bound diagnostic strings and strip private host and temp paths."""
    if not text:
        return None
    cleaned = text.strip()
    if not cleaned:
        return None
    if tmp_root is not None:
        cleaned = cleaned.replace(str(tmp_root), "<ephemeral>")
        cleaned = cleaned.replace(str(tmp_root.resolve()), "<ephemeral>")
    for prefix, tag in private_roots:
        cleaned = cleaned.replace(prefix, tag)
    cleaned = re.sub(r"/tmp/anneal-[A-Za-z0-9_.-]+", "<ephemeral>", cleaned)
    if len(cleaned) > limit:
        return cleaned[:limit] + "...[truncated]"
    return cleaned


def _summarize_verify_receipt(
    receipt: dict[str, Any] | None,
    *,
    tmp_root: Path | None = None,
    private_roots: tuple[tuple[str, str], ...] = (),
) -> dict[str, Any] | None:
    if not isinstance(receipt, dict):
        return None
    audit = receipt.get("audit")
    audit_summary = (
        {
            "replay": audit.get("replay"),
            "exactType": audit.get("exactType"),
            "checkedAlternateProofs": audit.get("checkedAlternateProofs"),
            "axioms": audit.get("axioms"),
            "sorryDeclarations": audit.get("sorryDeclarations"),
            "specWarnings": audit.get("specWarnings"),
        }
        if isinstance(audit, dict)
        else None
    )
    return {
        "status": receipt.get("status"),
        "phase": receipt.get("phase"),
        "detail": _sanitize_snippet(
            str(receipt.get("detail")) if receipt.get("detail") is not None else None,
            tmp_root=tmp_root,
            private_roots=private_roots,
        ),
        "taint_reasons": receipt.get("taint_reasons"),
        "deferred": receipt.get("deferred"),
        "elaboration_sandbox": receipt.get("elaboration_sandbox"),
        "audit": audit_summary,
    }


def _summarize_inspect_report(
    inspect_report: dict[str, Any] | None,
    *,
    tmp_root: Path | None = None,
    private_roots: tuple[tuple[str, str], ...] = (),
) -> dict[str, Any] | None:
    if not isinstance(inspect_report, dict):
        return None
    art = inspect_report.get("artifact_verification")
    art_summary = (
        {
            "exact_match": art.get("exact_match"),
            "checked_files": art.get("checked_files"),
            "failures": art.get("failures"),
        }
        if isinstance(art, dict)
        else None
    )
    return {
        "tainted": inspect_report.get("tainted"),
        "policy_violations": inspect_report.get("policy_violations"),
        "invariant_violations": inspect_report.get("invariant_violations"),
        "unrecognized_fields": inspect_report.get("unrecognized_fields"),
        "artifact_verification": art_summary,
        "detail": _sanitize_snippet(
            str(inspect_report.get("detail"))
            if inspect_report.get("detail") is not None
            else None,
            tmp_root=tmp_root,
            private_roots=private_roots,
        ),
    }


def _summarize_capture(capture_manifest: dict[str, Any] | None) -> dict[str, Any] | None:
    if not isinstance(capture_manifest, dict):
        return None
    program = capture_manifest.get("program")
    if not isinstance(program, dict):
        return None
    raw_bodies = program.get("bodies", [])
    bodies_summary: list[dict[str, Any]] = []
    if isinstance(raw_bodies, list):
        for body in raw_bodies[:32]:
            if isinstance(body, dict):
                blocks = body.get("blocks", [])
                bodies_summary.append(
                    {
                        "identity": body.get("identity"),
                        "is_unsafe": body.get("is_unsafe"),
                        "arg_count": body.get("arg_count"),
                        "block_count": len(blocks) if isinstance(blocks, list) else 0,
                    }
                )
    return {
        "mir_profile_version": program.get("mir_profile_version"),
        "scope": program.get("scope"),
        "has_local_panic_handler": program.get("has_local_panic_handler"),
        "body_count": len(raw_bodies) if isinstance(raw_bodies, list) else 0,
        "bodies": bodies_summary,
    }


def _read_mir_excerpt(artifacts_dir: Path, *, limit: int = 4000) -> str | None:
    cap_lean = artifacts_dir / "capture" / "Captured.lean"
    if cap_lean.is_symlink():
        return None
    max_bytes = max(limit, 0) * 4 + 64
    fd = -1
    try:
        fd = os.open(cap_lean, _OPEN_RO_FLAGS)
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            return None
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            raw = handle.read(max_bytes)
    except OSError:
        return None
    finally:
        if fd >= 0:
            os.close(fd)
    return _sanitize_snippet(
        raw.decode("utf-8", errors="replace"), limit=limit
    )


def _extract_spec_preflight_output(
    verify_receipt: dict[str, Any] | None,
    *,
    tmp_root: Path | None = None,
    private_roots: tuple[tuple[str, str], ...] = (),
) -> str | None:
    if not isinstance(verify_receipt, dict):
        return None
    phase = str(verify_receipt.get("phase") or "")
    detail = str(verify_receipt.get("detail") or "")
    if "spec" in phase.lower() or "preflight" in detail.lower():
        return _sanitize_snippet(
            f"[{phase}] {detail}",
            tmp_root=tmp_root,
            private_roots=private_roots,
        )
    return None


def _build_trace_artifacts(
    *,
    tmp_root: Path | None = None,
    private_roots: tuple[tuple[str, str], ...] = (),
    verify_receipt: dict[str, Any] | None = None,
    inspect_report: dict[str, Any] | None = None,
    audit_report: dict[str, Any] | None = None,
    capture_manifest: dict[str, Any] | None = None,
    artifacts_dir: Path | None = None,
    code_oracle_diagnostic: str | None = None,
    tool_stderr_snippet: str | None = None,
    sandbox_escape_paths: tuple[str, ...] | list[str] = (),
    attacker_hashes: dict[str, str] | None = None,
    incorrectness_patch_diff: str | None = None,
    preservation_canary_summary: dict[str, Any] | None = None,
    incorrectness_proof_audit: dict[str, Any] | None = None,
    incorrectness_claim: str | None = None,
) -> dict[str, Any]:
    escaped = bool(sandbox_escape_paths)
    sanitized_pres = (
        {
            **preservation_canary_summary,
            "detail": _sanitize_snippet(
                str(preservation_canary_summary.get("detail"))
                if preservation_canary_summary.get("detail") is not None
                else None,
                tmp_root=tmp_root,
                private_roots=private_roots,
            ),
        }
        if isinstance(preservation_canary_summary, dict)
        else None
    )
    sanitized_audit = (
        {
            **incorrectness_proof_audit,
            "detail": _sanitize_snippet(
                str(incorrectness_proof_audit.get("detail"))
                if incorrectness_proof_audit.get("detail") is not None
                else None,
                tmp_root=tmp_root,
                private_roots=private_roots,
            ),
        }
        if isinstance(incorrectness_proof_audit, dict)
        else None
    )
    return {
        "verify_summary": _summarize_verify_receipt(
            verify_receipt, tmp_root=tmp_root, private_roots=private_roots
        ),
        "inspect_summary": _summarize_inspect_report(
            inspect_report, tmp_root=tmp_root, private_roots=private_roots
        ),
        "audit_summary": audit_report if isinstance(audit_report, dict) else None,
        "capture_summary": _summarize_capture(capture_manifest),
        "mir_excerpt": (
            _read_mir_excerpt(artifacts_dir) if artifacts_dir is not None else None
        ),
        "spec_preflight_output": _extract_spec_preflight_output(
            verify_receipt, tmp_root=tmp_root, private_roots=private_roots
        ),
        "code_oracle_diagnostic": _sanitize_snippet(
            code_oracle_diagnostic, tmp_root=tmp_root, private_roots=private_roots
        ),
        "tool_stderr_snippet": _sanitize_snippet(
            tool_stderr_snippet, tmp_root=tmp_root, private_roots=private_roots
        ),
        "sandbox_escape": (
            {"detected": True, "tampered_paths": sorted(sandbox_escape_paths)}
            if escaped
            else None
        ),
        "attacker_provenance_sha256": attacker_hashes or {},
        "incorrectness_patch_diff": _sanitize_snippet(
            incorrectness_patch_diff,
            tmp_root=tmp_root,
            private_roots=private_roots,
            limit=16000,
        ),
        "preservation_canary_summary": sanitized_pres,
        "incorrectness_proof_audit": sanitized_audit,
        "incorrectness_claim": _sanitize_snippet(
            incorrectness_claim,
            tmp_root=tmp_root,
            private_roots=private_roots,
            limit=4000,
        ),
    }


def _stage_verify_workspace(
    work: Path,
    spec: scenarios.ScenarioSpec,
    submission: LoadedSubmission,
) -> tuple[Path, dict[str, str]]:
    """Assemble disjoint defender + attacker files and lock defender hashes."""
    work.mkdir(parents=True, exist_ok=True)
    work_resolved = work.resolve()
    defender_rels: list[str] = []

    for rel, content in spec.defender_files.items():
        _write_new_regular_file_excl(work / rel, content.encode("utf-8"))
        defender_rels.append(rel)

    rust_files: set[str] = set()
    proof_entries: list[dict[str, str]] = []
    if "Spec.lean" in spec.defender_files:
        proof_entries.append(
            {"module": "Spec", "path": "Spec.lean", "role": "specification"}
        )
    if "Proof.lean" in spec.defender_files:
        proof_entries.append(
            {"module": "Proof", "path": "Proof.lean", "role": "proof"}
        )
    if "src/lib.rs" in spec.defender_files:
        rust_files.add("src/lib.rs")

    attacker_stage: list[tuple[Path, bytes]] = []
    for rel, data in sorted(submission.files.items()):
        if (
            rel == "witness.json"
            or rel.startswith("witness/")
            or rel.startswith("incorrectness/")
        ):
            continue
        if rel.startswith("src/"):
            staged_rel = rel
            rust_files.add(rel)
        elif rel.startswith("Proof/"):
            mod = _validate_lean_slot_path(rel, "Proof")
            staged_rel = rel[len("Proof/") :]
            proof_entries.append(
                {"module": mod, "path": staged_rel, "role": "proof"}
            )
        elif rel == "Spec.lean":
            staged_rel = "Spec.lean"
            proof_entries.append(
                {"module": "Spec", "path": "Spec.lean", "role": "specification"}
            )
        elif rel.startswith("Spec/"):
            mod = _validate_lean_slot_path(rel, "Spec")
            staged_rel = rel[len("Spec/") :]
            proof_entries.append(
                {"module": mod, "path": staged_rel, "role": "specification"}
            )
        else:
            continue
        dest = (work / staged_rel).resolve()
        if not dest.is_relative_to(work_resolved) or dest == work_resolved:
            raise InvalidSubmissionError(
                f"staged path escapes workspace: {rel}"
            )
        attacker_stage.append((dest, data))

    proof_entries.sort(key=lambda item: item["module"])
    if spec.scope_kind == "crate":
        scope_obj: dict[str, Any] = {"kind": "crate"}
    else:
        scope_obj = {
            "kind": "selected_unit",
            "roots": list(spec.scope_roots),
        }

    request_obj = {
        "schema_version": 1,
        "compilation": {
            "source_root": ".",
            "crate_root": spec.crate_root,
            "crate_name": spec.crate_name,
            "edition": "2024",
            "target": VERIFIED_RUST_TARGET,
            "source_files": sorted(rust_files),
        },
        "scope": scope_obj,
        "proof": {
            "source_root": ".",
            "sources": proof_entries,
        },
    }
    request_path = work / "request.json"
    _write_new_regular_file_excl(
        request_path, (json.dumps(request_obj, indent=2) + "\n").encode("utf-8")
    )
    defender_rels.append("request.json")
    # Pin defender assets strictly before materializing any attacker file.
    pinned = _snapshot_tree_hashes(work, defender_rels)
    for dest, data in attacker_stage:
        _write_new_regular_file_excl(dest, data)
    _verify_tree_hashes(work, pinned)
    return request_path, pinned


def _strict_receipt_failures(
    receipt: dict[str, Any],
    *,
    returncode: int,
    spec: scenarios.ScenarioSpec,
) -> list[str]:
    """Enforce strict zero-weakening Receipt Schema v3 gates."""
    expected_status = (
        "crate_verified"
        if spec.scope_kind == "crate"
        else "selected_unit_verified"
    )
    failures = anneal_ci_lib.validate_receipt_v3_envelope(
        receipt,
        returncode=returncode,
        expected_status=expected_status,
        expected_returncode=0,
        check_deferred=True,
    )
    if receipt.get("elaboration_sandbox") == "none":
        failures.append("elaboration_sandbox=none")
    extra_deferred = [
        d
        for d in (receipt.get("deferred") or [])
        if d not in dedup.BASELINE_DEFERRED
    ]
    if extra_deferred:
        failures.append(f"unexpected deferred={extra_deferred!r}")
    audit = receipt.get("audit")
    if not isinstance(audit, dict):
        failures.append("missing audit object")
    else:
        if audit.get("replay") is not True:
            failures.append(f"audit.replay={audit.get('replay')!r}")
        if audit.get("exactType") is not True:
            failures.append(f"audit.exactType={audit.get('exactType')!r}")
        if not anneal_ci_lib.is_exact_int(
            audit.get("checkedAlternateProofs"), 0
        ):
            failures.append(
                f"checkedAlternateProofs={audit.get('checkedAlternateProofs')!r}"
            )
        if audit.get("sorryDeclarations") != []:
            failures.append(
                f"audit.sorryDeclarations={audit.get('sorryDeclarations')!r}"
            )
        axioms = audit.get("axioms")
        if (
            not isinstance(axioms, list)
            or not all(isinstance(a, str) for a in axioms)
            or not set(axioms).issubset(dedup.ALLOWED_STANDARD_AXIOMS)
        ):
            failures.append(f"disallowed audit.axioms={axioms!r}")
    return failures


def _run_inspect_gate(
    *,
    cli: Path,
    receipt_path: Path,
    artifacts_dir: Path,
    spec: scenarios.ScenarioSpec,
    env: dict[str, str],
    timeout: int,
    inspect_runner: Callable[..., Any] | None = None,
) -> tuple[bool, list[str], dict[str, Any] | None]:
    """Run `cargo anneal inspect` and validate zero policy/artifact flaws."""
    cmd = [
        str(cli),
        "inspect",
        "--format",
        "json",
        "--require-untainted",
        "--require-containment",
        "--verify-artifacts",
        str(artifacts_dir),
        "--require-exact-artifacts",
    ]
    if spec.scope_kind == "crate":
        cmd.append("--require-crate-scope")
    cmd.append(str(receipt_path))

    if inspect_runner is not None:
        proc = inspect_runner(cmd, env=env, timeout=timeout)
    else:
        proc = _run_bounded_subprocess(
            cmd,
            env=env,
            timeout=timeout,
        )
    if proc.returncode == 1:
        parsed_policy: dict[str, Any] | None = None
        if proc.stdout.strip():
            try:
                candidate = json.loads(
                    proc.stdout,
                    object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
                )
                if isinstance(candidate, dict):
                    parsed_policy = candidate
            except (ValueError, json.JSONDecodeError):
                parsed_policy = None
        err_detail = (proc.stderr or proc.stdout).strip()[:240]
        return (
            False,
            [f"inspect exit=1: {err_detail}"],
            parsed_policy,
        )
    if proc.returncode != 0:
        err_detail = (proc.stderr or proc.stdout).strip()[:240]
        raise OracleInfrastructureError(
            f"inspect operational failure (exit={proc.returncode}): {err_detail}"
        )
    try:
        inspected = json.loads(
            proc.stdout,
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
    except (ValueError, json.JSONDecodeError) as exc:
        raise OracleInfrastructureError(
            f"invalid inspect JSON output on exit 0: {exc}"
        ) from exc

    failures: list[str] = []
    if not isinstance(inspected, dict):
        raise OracleInfrastructureError("inspect JSON output must be an object")
    if inspected.get("tainted") is not False:
        failures.append(f"inspect tainted={inspected.get('tainted')!r}")
    for field in (
        "policy_violations",
        "invariant_violations",
        "unrecognized_fields",
    ):
        val = inspected.get(field)
        if val != []:
            failures.append(f"inspect {field}={val!r}")
    art_check = inspected.get("artifact_verification")
    if (
        not isinstance(art_check, dict)
        or art_check.get("exact_match") is not True
    ):
        failures.append(f"inspect artifact_verification={art_check!r}")
    return len(failures) == 0, failures, inspected


def _load_capture_manifest(artifacts_dir: Path) -> dict[str, Any] | None:
    """Load `artifacts/capture/capture.json` safely with bounded size."""
    cap_path = artifacts_dir / "capture" / "capture.json"
    if cap_path.is_symlink():
        return None
    try:
        raw = _read_regular_file_nofollow(
            cap_path,
            max_bytes=_MAX_CAPTURE_BYTES,
            label="capture manifest",
            exc_type=RuntimeError,
        )
        data = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
        if not isinstance(data, dict):
            return None
        return data
    except Exception:
        return None


def _run_verify_and_inspect(
    *,
    work: Path,
    request_path: Path,
    artifacts_dir: Path,
    receipt_path: Path,
    spec: scenarios.ScenarioSpec,
    tools: dict[str, Path | None],
    env: dict[str, str],
    timeout: int,
    verify_runner: Callable[..., Any] | None = None,
    inspect_runner: Callable[..., Any] | None = None,
) -> tuple[bool, bool, dict[str, Any] | None, dict[str, Any] | None, list[str]]:
    """Run strict `cargo anneal verify` and `inspect`."""
    cli = tools.get("cli")
    capture = tools.get("capture")
    sysroot = tools.get("sysroot")
    lean = tools.get("lean")
    if verify_runner is None:
        missing = [
            name
            for name, path in (
                ("cargo-anneal", cli),
                ("anneal-rustc-capture", capture),
                ("sysroot", sysroot),
                ("lean", lean),
            )
            if path is None
        ]
        if missing:
            raise OracleInfrastructureError(
                f"missing required Anneal verification tools: {', '.join(missing)}"
            )
    cli_path = cli or Path("cargo-anneal")
    effective_verify_runner = verify_runner
    if effective_verify_runner is None:

        def _bounded_verify_runner(
            cmd: list[str],
            *,
            cwd: Path,
            env: dict[str, str] | None,
            timeout: float,
        ) -> subprocess.CompletedProcess[str]:
            return _run_bounded_subprocess(
                cmd,
                cwd=cwd,
                env=env,
                timeout=max(1, int(math.ceil(timeout))),
                apply_prlimit=False,
            )

        effective_verify_runner = _bounded_verify_runner
    try:
        proc, receipt = anneal_ci_lib.run_cargo_anneal_verify(
            cli=cli_path,
            request_path=request_path,
            cwd=work,
            capture=capture,
            sysroot=sysroot,
            lean=lean,
            artifacts_dir=artifacts_dir,
            extra_flags=["--receipt-out", str(receipt_path)],
            env=env,
            timeout=float(timeout),
            runner=effective_verify_runner,
            label=spec.scenario_id,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"verify timed out after {timeout}s"
        ) from exc
    except RuntimeError as exc:
        # Malformed/non-object JSON or tool crash never credits defender hold.
        raise OracleInfrastructureError(
            f"verify operational or malformed JSON error: {exc}"
        ) from exc

    if proc.returncode < 0:
        raise OracleInfrastructureError(
            f"verify terminated by signal {-proc.returncode}"
        )

    if proc.returncode == 0:
        if receipt_path.is_symlink() or not receipt_path.is_file():
            if verify_runner is None:
                raise OracleInfrastructureError(
                    "verify exited 0 without writing requested --receipt-out "
                    f"regular file ({receipt_path.name})"
                )
            # Synthesize the file only for injected in-memory unit-test doubles.
            anneal_ci_lib.atomic_write_text(
                receipt_path, json.dumps(receipt, indent=2) + "\n"
            )
        raw_persisted = _read_regular_file_nofollow(
            receipt_path,
            max_bytes=_MAX_CAPTURE_BYTES,
            label="persisted verify receipt",
            exc_type=OracleInfrastructureError,
        )
        try:
            persisted_receipt = json.loads(
                raw_persisted.decode("utf-8"),
                object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
            )
        except (ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise OracleInfrastructureError(
                f"invalid persisted --receipt-out JSON: {exc}"
            ) from exc
        if not isinstance(persisted_receipt, dict) or persisted_receipt != receipt:
            raise OracleInfrastructureError(
                "persisted verify --receipt-out JSON differs from stdout receipt"
            )

    if receipt.get("status") == "tool_failed" or proc.returncode not in (0, 1):
        raise OracleInfrastructureError(
            "verify operational failure "
            f"(exit={proc.returncode}, phase={receipt.get('phase')!r}): "
            f"{receipt.get('detail', '')}"
        )

    failures = _strict_receipt_failures(
        receipt, returncode=proc.returncode, spec=spec
    )
    if failures:
        return False, False, receipt, None, failures

    inspect_ok, inspect_failures, inspected = _run_inspect_gate(
        cli=cli_path,
        receipt_path=receipt_path,
        artifacts_dir=artifacts_dir,
        spec=spec,
        env=env,
        timeout=timeout,
        inspect_runner=inspect_runner,
    )
    if not inspect_ok:
        return True, False, receipt, inspected, inspect_failures
    return True, True, receipt, inspected, []


def _find_pinned_rust_sysroot(explicit_sysroot: Path | None = None) -> Path | None:
    """Locate pinned `nightly-2026-05-31` rustc sysroot on disk without `PATH`."""
    if explicit_sysroot is not None:
        return explicit_sysroot if explicit_sysroot.is_dir() else None
    raw_ru = os.environ.get("RUSTUP_HOME", "").strip()
    rustup_home = Path(raw_ru) if raw_ru else (Path.home() / ".rustup")
    tc_dir = rustup_home / "toolchains"
    if not tc_dir.is_dir() or tc_dir.is_symlink():
        return None
    exact = tc_dir / f"nightly-2026-05-31-{VERIFIED_RUST_TARGET}"
    if exact.is_dir() and not exact.is_symlink():
        return exact
    try:
        cands = sorted(tc_dir.iterdir(), key=lambda p: p.name)
    except OSError:
        return None
    for cand in cands:
        if (
            cand.name.startswith("nightly-2026-05-31-")
            and cand.is_dir()
            and not cand.is_symlink()
        ):
            return cand
    return None


def _resolve_pinned_rust_sysroot(
    *,
    bwrap: Path | None = None,
    timeout: int = 15,
) -> Path | None:
    """Resolve and verify the pinned Rust sysroot via bounded scrubbed `rustc`."""
    pinned = _find_pinned_rust_sysroot(None)
    if pinned is None:
        return None
    rustc_bin = pinned / "bin" / "rustc"
    if not rustc_bin.is_file() or rustc_bin.is_symlink():
        return None
    try:
        pinned_resolved = pinned.resolve(strict=True)
    except OSError:
        return None
    try:
        if bwrap is not None:
            proc = _run_cmd_in_bwrap(
                bwrap=bwrap,
                ro_mounts=[(pinned_resolved, str(pinned_resolved))],
                rw_mounts=[],
                env_vars={
                    "PATH": f"{pinned_resolved / 'bin'}:/usr/bin:/bin",
                    "LD_LIBRARY_PATH": str(pinned_resolved / "lib"),
                    "HOME": "/work/tmp",
                    "TMPDIR": "/work/tmp",
                    "NO_COLOR": "1",
                },
                cwd_in_sandbox="/work/tmp",
                argv=[str(pinned_resolved / "bin" / "rustc"), "--print", "sysroot"],
                ro_system_bins=True,
                tmpfs_tmp=True,
                disable_userns=True,
                timeout=timeout,
            )
        else:
            proc = _run_bounded_subprocess(
                [str(pinned_resolved / "bin" / "rustc"), "--print", "sysroot"],
                env={
                    "PATH": f"{pinned_resolved / 'bin'}:/usr/bin:/bin",
                    "LD_LIBRARY_PATH": str(pinned_resolved / "lib"),
                    "HOME": "/tmp",
                    "TMPDIR": "/tmp",
                    "NO_COLOR": "1",
                },
                timeout=timeout,
            )
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    out = proc.stdout.strip()
    if not out:
        return None
    try:
        out_resolved = Path(out).resolve(strict=True)
    except OSError:
        return None
    if out_resolved == pinned_resolved:
        return pinned_resolved
    return None


def _discover_pinned_local_defaults(
    anneal_root: Path,
    *,
    need_cli: bool,
    need_capture: bool,
    need_lean: bool,
    need_sysroot: bool,
    bwrap: Path | None,
    timeout: int,
) -> dict[str, Path | None]:
    """Lazily discover local tools without running ambient `PATH` `rustup`."""
    raw_target = os.environ.get("CARGO_TARGET_DIR", "")
    target_dir = (
        Path(raw_target) if raw_target.strip() else anneal_root / "target"
    )
    cli_path: Path | None = None
    if need_cli:
        cand = target_dir / "debug/cargo-anneal"
        if cand.is_file():
            cli_path = cand
    cap_path: Path | None = None
    if need_capture:
        for cand in (
            target_dir / "debug/anneal-rustc-capture",
            anneal_root
            / "trusted/rustc-capture/target/debug/anneal-rustc-capture",
        ):
            if cand.is_file():
                cap_path = cand
                break
    lean_path: Path | None = None
    if need_lean:
        home = Path.home()
        lean_candidates = [
            home / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean",
        ]
        raw_xdg_cache = os.environ.get("XDG_CACHE_HOME", "")
        cache_home = (
            Path(raw_xdg_cache) if raw_xdg_cache.strip() else home / ".cache"
        )
        tc_root = cache_home / "anneal/toolchain"
        if tc_root.is_dir():
            entries: list[tuple[float, Path]] = []
            try:
                tc_entries = list(tc_root.iterdir())
            except OSError:
                tc_entries = []
            for entry in tc_entries:
                try:
                    mtime = entry.stat().st_mtime
                except OSError:
                    continue
                entries.append((mtime, entry))
            cached_lean = [
                cand
                for _, entry in sorted(
                    entries, key=lambda item: item[0], reverse=True
                )
                if (cand := entry / "lean/bin/lean").is_file()
            ]
            lean_candidates = cached_lean + lean_candidates
        lean_path = next((p for p in lean_candidates if p.is_file()), None)
    sysroot_path: Path | None = None
    if need_sysroot:
        sysroot_path = _resolve_pinned_rust_sysroot(
            bwrap=bwrap, timeout=min(max(timeout, 1), 15)
        )
    return {
        "cli": cli_path,
        "capture": cap_path,
        "sysroot": sysroot_path,
        "lean": lean_path,
    }


def _discover_miri_sysroot(
    explicit: Path | None = None,
    *,
    sysroot: Path | None = None,
    bwrap: Path | None = None,
) -> Path | None:
    """Resolve verified `MIRI_SYSROOT` inside `bwrap` without ambient `cargo`."""
    if explicit is not None:
        return explicit if explicit.is_dir() else None
    raw_xdg = os.environ.get("XDG_CACHE_HOME", "").strip()
    cache_base = Path(raw_xdg) if raw_xdg else (Path.home() / ".cache")
    pinned_sysroot = _find_pinned_rust_sysroot(sysroot)
    bwrap_bin = bwrap if bwrap is not None else _resolve_bwrap_binary(required=False)
    if (
        bwrap_bin is not None
        and pinned_sysroot is not None
        and cache_base.is_dir()
        and (pinned_sysroot / "bin" / "cargo").is_file()
        and (pinned_sysroot / "bin" / "rustc").is_file()
        and (pinned_sysroot / "bin" / "cargo-miri").is_file()
    ):
        try:
            sys_resolved = pinned_sysroot.resolve(strict=True)
            cache_resolved = cache_base.resolve(strict=True)
            probe = _run_cmd_in_bwrap(
                bwrap=bwrap_bin,
                ro_mounts=[
                    (sys_resolved, str(sys_resolved)),
                    (cache_resolved, str(cache_resolved)),
                ],
                rw_mounts=[],
                env_vars={
                    "PATH": f"{sys_resolved / 'bin'}:/usr/bin:/bin",
                    "LD_LIBRARY_PATH": str(sys_resolved / "lib"),
                    "XDG_CACHE_HOME": str(cache_resolved),
                    "HOME": "/work/tmp",
                    "TMPDIR": "/work/tmp",
                    "CARGO": str(sys_resolved / "bin" / "cargo"),
                    "RUSTC": str(sys_resolved / "bin" / "rustc"),
                    "CARGO_NET_OFFLINE": "true",
                    "NO_COLOR": "1",
                },
                cwd_in_sandbox="/work/tmp",
                argv=[
                    str(sys_resolved / "bin" / "cargo"),
                    "miri",
                    "setup",
                    "--print-sysroot",
                ],
                ro_system_bins=True,
                tmpfs_tmp=True,
                disable_userns=True,
                timeout=15,
            )
            out = probe.stdout.strip()
            if probe.returncode == 0 and out:
                cand = Path(out).resolve(strict=True)
                if (
                    (cand.is_relative_to(cache_resolved) or cand.is_relative_to(sys_resolved))
                    and cand.is_dir()
                    and (cand / "lib" / "rustlib").is_dir()
                ):
                    return cand
        except (OSError, subprocess.SubprocessError):
            pass
    default_cache = cache_base / "miri"
    if default_cache.is_dir() and (default_cache / "lib" / "rustlib").is_dir():
        return default_cache
    return None


def _verify_bwrap_canary(
    bwrap: Path,
    *,
    ro_mounts: list[tuple[Path, str]],
    env_vars: dict[str, str],
    argv: list[str],
    bind_dev_seeds: bool = False,
    ro_system_bins: bool = True,
    tmpfs_tmp: bool = True,
    disable_userns: bool = True,
    label: str = "sandbox",
    timeout: int = 15,
) -> None:
    """Fail closed with OracleInfrastructureError when bwrap cannot execute."""
    try:
        probe = _run_cmd_in_bwrap(
            bwrap=bwrap,
            ro_mounts=ro_mounts,
            rw_mounts=[],
            env_vars=env_vars,
            cwd_in_sandbox="/work/tmp",
            argv=argv,
            timeout=timeout,
            bind_dev_seeds=bind_dev_seeds,
            ro_system_bins=ro_system_bins,
            tmpfs_tmp=tmpfs_tmp,
            disable_userns=disable_userns,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        raise OracleInfrastructureError(
            f"{label} bwrap canary probe failed: {exc}"
        ) from exc
    if probe.returncode != 0:
        detail = (probe.stderr or probe.stdout).strip()[:400]
        raise OracleInfrastructureError(
            f"{label} bwrap sandbox unusable (rc={probe.returncode}): {detail}"
        )


def _inspect_cargo_json_diagnostics(stdout: str) -> tuple[bool, bool, str]:
    """Inspect Cargo `--message-format=json` lines for user vs sysroot errors.

    Returns `(has_user_error, has_sysroot_error, rendered_errors)`.
    """
    has_user = False
    has_sysroot = False
    rendered_msgs: list[str] = []
    for line in stdout.splitlines():
        stripped = line.strip()
        if not stripped.startswith("{"):
            continue
        try:
            rec = json.loads(stripped)
        except ValueError:
            continue
        if not isinstance(rec, dict):
            continue
        if rec.get("reason") == "build-finished":
            break
        if rec.get("reason") != "compiler-message":
            continue
        msg = rec.get("message")
        if not isinstance(msg, dict) or msg.get("level") != "error":
            continue
        text_msg = msg.get("message") or ""
        if "Undefined Behavior:" in str(text_msg):
            continue
        pkg_id = str(rec.get("package_id") or "")
        manifest_path = str(rec.get("manifest_path") or "")
        is_user = (
            "/work/oracle_crate/" in manifest_path
            or "/work/oracle_harness/" in manifest_path
            or "#redteam_s2@" in pkg_id
            or "#redteam_s2_oracle@" in pkg_id
            or pkg_id.startswith("redteam_s2 ")
            or pkg_id.startswith("redteam_s2_oracle ")
        )
        rendered = str(msg.get("rendered") or text_msg).strip()
        if rendered:
            rendered_msgs.append(rendered)
        if is_user:
            has_user = True
        else:
            has_sysroot = True
    return has_user, has_sysroot, "\n".join(rendered_msgs)


def _is_user_compile_error(out: str) -> bool:
    """Return True for user compile failures, never genuine sysroot crashes."""
    if _SYSROOT_CRATE_MARKER_RE.search(out) or _CARGO_INFRA_ERR_RE.search(out):
        return False
    return "could not compile" in out or "error[E" in out or "aborting due to" in out


def _classify_s2_oracle_exit(
    out: str,
    rc: int,
    *,
    nonce: str,
    is_live: bool,
    is_miri: bool,
    phase: str,
    has_user_compile_err: bool = False,
    has_sysroot_compile_err: bool = False,
    pre_main_ref_ok: bool | None = None,
) -> tuple[str, str | None, str] | None:
    """Classify S2 Miri/rustc process exit fail-closed (`None` means clean)."""
    start_tag = f"ANNEAL_ORACLE_START_{nonce}"
    end_tag = f"ANNEAL_ORACLE_END_{nonce}"
    mismatch_tag = f"ANNEAL_ORACLE_MISMATCH_{nonce}:"
    panic_tag = f"ANNEAL_ORACLE_PANIC_{nonce}:"
    is_pre_start = (not is_live) or (start_tag not in out)

    if rc == 0:
        if not is_live:
            return None
        if start_tag not in out:
            if pre_main_ref_ok is True:
                return (
                    "spec_violation_confirmed",
                    "spec_violation:panic_or_abort",
                    f"{phase} oracle exited 0 before execution start marker",
                )
            raise OracleInfrastructureError(
                f"live {phase} oracle exited 0 without execution start marker"
            )
        if end_tag not in out:
            return (
                "spec_violation_confirmed",
                "spec_violation:panic_or_abort",
                f"{phase} oracle exited early before completion marker",
            )
        return None

    if is_miri and re.search(
        r"(?m)^error(?:\[[^\]]+\])?: Undefined Behavior:", out
    ):
        return "ub_confirmed", dedup.classify_miri_ub(out), out[:1800]
    if rc == 42 and (not is_live or mismatch_tag in out):
        return "spec_violation_confirmed", "spec_violation:wrong_return", out[:1800]
    if rc == 43 and (not is_live or panic_tag in out):
        return "spec_violation_confirmed", "spec_violation:panic_or_abort", out[:1800]
    if _RUSTC_ICE_RE.search(out):
        return "oracle_inconclusive", None, out[:1800]
    if is_pre_start and (
        has_sysroot_compile_err
        or (not has_user_compile_err and _SYSROOT_CRATE_MARKER_RE.search(out))
    ):
        raise OracleInfrastructureError(
            f"{phase} sysroot/toolchain compile failure (rc={rc}): {out[:400]}"
        )
    if (
        _STACK_OVERFLOW_RE.search(out)
        or _OOM_RE.search(out)
        or rc in (-9, -24, 137, 152)
        or (
            is_miri
            and (
                _MIRI_UNSUPPORTED_RE.search(out)
                or _MIRI_INCONCLUSIVE_RE.search(out)
            )
        )
    ):
        return "oracle_inconclusive", None, out[:1800]
    if is_miri and _MIRI_ABNORMAL_TERM_RE.search(out):
        return "spec_violation_confirmed", "spec_violation:panic_or_abort", out[:1800]
    if is_pre_start and (has_user_compile_err or _is_user_compile_error(out)):
        return "compile_error", None, out[:1800]
    if is_miri and not is_pre_start and _MIRI_ERROR_RE.search(out):
        return "oracle_inconclusive", None, out[:1800]
    if is_live and start_tag in out and end_tag not in out:
        return (
            "spec_violation_confirmed",
            "spec_violation:panic_or_abort",
            out[:1800] or f"{phase} oracle exited non-zero (rc={rc}) inside target",
        )
    if (rc < 0 or rc in (132, 134, 136, 139)) and (not is_live or start_tag in out):
        return "spec_violation_confirmed", "spec_violation:panic_or_abort", out[:1800]
    if is_live and start_tag not in out and pre_main_ref_ok is True:
        return (
            "spec_violation_confirmed",
            "spec_violation:panic_or_abort",
            out[:1800] or f"{phase} oracle terminated before main (rc={rc})",
        )
    raise OracleInfrastructureError(
        f"{phase} oracle exited unexpectedly (rc={rc}): {out[:400]}"
    )


_FORBIDDEN_RLIB_CTOR_SEC_RE = re.compile(
    r"^\.(?:init|fini|ctors|dtors|init_array|fini_array|preinit_array)(?:$|\.)"
)
_FORBIDDEN_RLIB_CRT_SYMBOLS = frozenset(
    {
        "_start",
        "main",
        "__libc_start_main",
        "__rust_start_main",
        "_init",
        "_fini",
        "atexit",
        "__cxa_atexit",
    }
)


def _read_elf_cstr(blob: bytes, offset: int) -> str:
    if offset < 0 or offset >= len(blob):
        return ""
    end = blob.find(b"\x00", offset)
    if end < 0:
        end = len(blob)
    return blob[offset:end].decode("utf-8", errors="replace")


def _read_exact_at(
    stream: Any,
    offset: int,
    size: int,
    *,
    base: int,
    member_end: int,
    label: str,
) -> bytes:
    """Read `size` bytes at `base + offset` within `[base, member_end]`."""
    abs_pos = base + offset
    if offset < 0 or size < 0 or abs_pos + size > member_end:
        raise OracleInfrastructureError(f"truncated ELF structure in {label}")
    stream.seek(abs_pos)
    data = stream.read(size)
    if len(data) != size:
        raise OracleInfrastructureError(f"short ELF read in {label}")
    return data


def _check_elf64_object_stream(
    stream: Any,
    *,
    member_start: int,
    member_size: int,
    member_label: str,
) -> bool:
    """Inspect one `ar` member via seek/read; return `True` if ELF64 object."""
    if member_size < 64:
        return False
    member_end = member_start + member_size
    stream.seek(member_start)
    ehdr = stream.read(64)
    if len(ehdr) < 64 or not ehdr.startswith(b"\x7fELF"):
        return False
    if ehdr[4] != 2 or ehdr[5] != 1:
        raise OracleInfrastructureError(
            f"unexpected non-ELF64 LSB object in Scenario 2 rlib ({member_label})"
        )
    (e_shoff,) = struct.unpack_from("<Q", ehdr, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", ehdr, 58)
    if e_shoff == 0:
        return True
    if e_shentsize < 64:
        raise OracleInfrastructureError(
            f"malformed ELF section header entry size in Scenario 2 rlib ({member_label})"
        )
    if e_shnum == 0 or e_shstrndx == 0xFFFF:
        sh0 = _read_exact_at(
            stream,
            e_shoff,
            e_shentsize,
            base=member_start,
            member_end=member_end,
            label=member_label,
        )
        if e_shnum == 0:
            (e_shnum,) = struct.unpack_from("<Q", sh0, 32)
            if e_shnum == 0:
                return True
        if e_shstrndx == 0xFFFF:
            (e_shstrndx,) = struct.unpack_from("<I", sh0, 40)
    sh_tbl_size = e_shentsize * e_shnum
    if sh_tbl_size > _MAX_ELF_TABLE_BYTES:
        raise OracleInfrastructureError(
            f"malformed or oversized ELF section table in Scenario 2 rlib ({member_label})"
        )
    sh_bytes = _read_exact_at(
        stream,
        e_shoff,
        sh_tbl_size,
        base=member_start,
        member_end=member_end,
        label=member_label,
    )
    if e_shstrndx >= e_shnum:
        raise OracleInfrastructureError(
            f"invalid ELF shstrndx in Scenario 2 rlib ({member_label})"
        )
    shstr_off, shstr_sz = struct.unpack_from(
        "<QQ", sh_bytes, e_shstrndx * e_shentsize + 24
    )
    if shstr_sz > _MAX_ELF_TABLE_BYTES:
        raise OracleInfrastructureError(
            f"oversized ELF shstrtab in Scenario 2 rlib ({member_label})"
        )
    shstrtab = _read_exact_at(
        stream,
        shstr_off,
        shstr_sz,
        base=member_start,
        member_end=member_end,
        label=member_label,
    )
    sections: list[tuple[str, int, int, int, int, int]] = []
    for idx in range(e_shnum):
        base = idx * e_shentsize
        sh_name, sh_type = struct.unpack_from("<II", sh_bytes, base)
        sh_offset, sh_size, sh_link = struct.unpack_from("<QQI", sh_bytes, base + 24)
        (sh_entsize,) = struct.unpack_from("<Q", sh_bytes, base + 56)
        sec_name = _read_elf_cstr(shstrtab, sh_name)
        if sh_type in (14, 15, 16) or _FORBIDDEN_RLIB_CTOR_SEC_RE.match(sec_name):
            raise InvalidSubmissionError(
                f"custom init/fini section {sec_name!r} is disallowed in Scenario 2"
            )
        sections.append((sec_name, sh_type, sh_offset, sh_size, sh_link, sh_entsize))

    for _sec_name, sh_type, sh_offset, sh_size, sh_link, sh_entsize in sections:
        if sh_type != 2 or sh_entsize < 24 or sh_link >= len(sections):
            continue
        _str_name, _str_t, str_off, str_sz, _str_l, _str_e = sections[sh_link]
        if str_sz > _MAX_ELF_TABLE_BYTES or sh_size > _MAX_ELF_SYMTAB_BYTES:
            raise OracleInfrastructureError(
                f"oversized ELF symbol/string table in Scenario 2 rlib ({member_label})"
            )
        strtab = _read_exact_at(
            stream,
            str_off,
            str_sz,
            base=member_start,
            member_end=member_end,
            label=member_label,
        )
        sym_bytes = _read_exact_at(
            stream,
            sh_offset,
            sh_size,
            base=member_start,
            member_end=member_end,
            label=member_label,
        )
        for pos in range(0, sh_size - 23, sh_entsize):
            st_name, st_info, _st_other, st_shndx = struct.unpack_from(
                "<IBBH", sym_bytes, pos
            )
            st_bind = st_info >> 4
            if st_shndx != 0 and st_bind in (1, 2):
                sym_name = _read_elf_cstr(strtab, st_name)
                if sym_name in _FORBIDDEN_RLIB_CRT_SYMBOLS:
                    raise InvalidSubmissionError(
                        f"CRT entrypoint/hook symbol {sym_name!r} override is disallowed in Scenario 2"
                    )
    return True


def _check_elf64_object_for_ctors(obj_bytes: bytes, *, member_label: str) -> None:
    """Reject ELF constructor sections and CRT entrypoint overrides in attacker objects."""
    _check_elf64_object_stream(
        io.BytesIO(obj_bytes),
        member_start=0,
        member_size=len(obj_bytes),
        member_label=member_label,
    )


def _scan_single_rlib_no_ctors(rlib_path: Path) -> None:
    """Incrementally scan one `.rlib` `ar` archive via `O_NOFOLLOW` without bulk RAM load."""
    try:
        fd = os.open(rlib_path, _OPEN_RO_FLAGS)
    except OSError as exc:
        raise OracleInfrastructureError(
            f"cannot open built rlib {rlib_path.name}: {exc}"
        ) from exc
    try:
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise OracleInfrastructureError(
                f"non-regular built rlib disallowed: {rlib_path.name}"
            )
        if fst.st_size > MAX_S2_RLIB_BYTES:
            raise InvalidSubmissionError(
                f"compiled Scenario 2 rlib {rlib_path.name} exceeds "
                f"{MAX_S2_RLIB_BYTES} bytes ({fst.st_size})"
            )
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            magic = handle.read(8)
            if magic != b"!<arch>\n":
                raise OracleInfrastructureError(
                    f"invalid archive header in {rlib_path.name}"
                )
            gnu_strtab = b""
            cursor = 8
            file_len = fst.st_size
            saw_elf_obj = False
            while cursor + 60 <= file_len:
                handle.seek(cursor)
                hdr = handle.read(60)
                if len(hdr) < 60 or hdr[58:60] != b"`\n":
                    raise OracleInfrastructureError(
                        f"corrupt archive member header in {rlib_path.name}"
                    )
                raw_name = hdr[0:16].decode("latin-1")
                size_str = hdr[48:58].decode("ascii", errors="strict").strip()
                try:
                    member_size = int(size_str)
                except ValueError as exc:
                    raise OracleInfrastructureError(
                        f"invalid archive member size in {rlib_path.name}: {size_str!r}"
                    ) from exc
                data_start = cursor + 60
                data_end = data_start + member_size
                if member_size < 0 or data_end > file_len:
                    raise OracleInfrastructureError(
                        f"truncated archive member in {rlib_path.name}"
                    )
                cursor = data_end + (data_end & 1)
                name_stripped = raw_name.rstrip(" ")
                member_name = name_stripped.rstrip("/")
                if name_stripped.startswith("//"):
                    if member_size > _MAX_ELF_TABLE_BYTES:
                        raise OracleInfrastructureError(
                            f"oversized archive strtab in {rlib_path.name}"
                        )
                    handle.seek(data_start)
                    gnu_strtab = handle.read(member_size)
                    continue
                if name_stripped in ("/", "/SYM64/"):
                    continue
                if name_stripped.startswith("#1/"):
                    nlen = int(name_stripped[3:])
                    if nlen < 0 or nlen > min(member_size, 4096):
                        raise OracleInfrastructureError(
                            f"invalid BSD archive name length in {rlib_path.name}"
                        )
                    handle.seek(data_start)
                    member_name = handle.read(nlen).rstrip(b"\x00").decode(
                        "utf-8", errors="replace"
                    )
                    data_start += nlen
                    member_size -= nlen
                elif name_stripped.startswith("/") and name_stripped[1:].isdigit():
                    off = int(name_stripped[1:])
                    end_n = gnu_strtab.find(b"/\n", off)
                    if end_n < 0:
                        end_n = gnu_strtab.find(b"\x00", off)
                    if end_n >= 0:
                        member_name = gnu_strtab[off:end_n].decode(
                            "utf-8", errors="replace"
                        )
                if _check_elf64_object_stream(
                    handle,
                    member_start=data_start,
                    member_size=member_size,
                    member_label=f"{rlib_path.name}:{member_name}",
                ):
                    saw_elf_obj = True
            if not saw_elf_obj:
                raise OracleInfrastructureError(
                    f"no ELF object members found inside {rlib_path.name}"
                )
    finally:
        if fd >= 0:
            os.close(fd)


def _verify_s2_rlib_no_ctors(debug_dir: Path, *, crate_name: str = "redteam_s2") -> None:
    """Scan built `lib<crate_name>*.rlib` objects for ctor/CRT hijacks."""
    candidates: list[Path] = []
    direct = debug_dir / f"lib{crate_name}.rlib"
    if direct.exists() or direct.is_symlink():
        candidates.append(direct)
    deps_dir = debug_dir / "deps"
    if deps_dir.is_dir():
        rlib_re = re.compile(rf"^lib{re.escape(crate_name)}(?:-[0-9a-f]+)?\.rlib$")
        for p in sorted(deps_dir.iterdir()):
            if rlib_re.match(p.name):
                candidates.append(p)
    if not candidates:
        raise OracleInfrastructureError(
            f"missing compiled lib{crate_name}.rlib after cargo build"
        )
    for rlib_path in candidates:
        _scan_single_rlib_no_ctors(rlib_path)


_S2_NATIVE_ORACLE_RS = r"""
#[cfg(all(not(miri), not(all(target_arch = "x86_64", target_os = "linux"))))]
compile_error!("native Scenario 2 seccomp oracle requires x86_64-linux");

#[cfg(all(not(miri), target_arch = "x86_64", target_os = "linux"))]
mod native_oracle {
    use core::arch::asm;
    use std::io::Write as _;

    #[repr(C)]
    struct SockFilter { code: u16, jt: u8, jf: u8, k: u32 }

    #[repr(C)]
    struct SockFprog { len: u16, filter: *const SockFilter }

    #[repr(C)]
    struct Rlimit { rlim_cur: u64, rlim_max: u64 }

    #[inline(always)]
    unsafe fn sc0(nr: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(always)]
    unsafe fn sc1(nr: usize, a0: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, in("rdi") a0, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(always)]
    unsafe fn sc2(nr: usize, a0: usize, a1: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, in("rdi") a0, in("rsi") a1, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(always)]
    unsafe fn sc3(nr: usize, a0: usize, a1: usize, a2: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, in("rdi") a0, in("rsi") a1, in("rdx") a2, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(always)]
    unsafe fn sc4(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, in("rdi") a0, in("rsi") a1, in("rdx") a2, in("r10") a3, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(always)]
    unsafe fn sc5(nr: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize) -> isize {
        let ret: isize;
        unsafe { asm!("syscall", inlateout("rax") nr => ret, in("rdi") a0, in("rsi") a1, in("rdx") a2, in("r10") a3, in("r8") a4, lateout("rcx") _, lateout("r11") _, options(nostack)); }
        ret
    }

    #[inline(never)]
    unsafe fn oracle_write_gate(query: bool, fd: usize, ptr: usize, len: usize) -> (isize, u64, u64) {
        let ret: isize;
        let mut sc_start: u64 = 0;
        let mut sc_end: u64 = 0;
        let q_flag: u32 = if query { 1 } else { 0 };
        unsafe {
            asm!(
                "test {q:e}, {q:e}",
                "jz 2f",
                "lea {start}, [rip + 2f]",
                "lea {end}, [rip + 3f]",
                "jmp 3f",
                ".p2align 4",
                "2:",
                "syscall",
                "3:",
                start = inout(reg) sc_start,
                end = inout(reg) sc_end,
                q = in(reg) q_flag,
                inlateout("rax") 1usize => ret,
                in("rdi") fd,
                in("rsi") ptr,
                in("rdx") len,
                lateout("rcx") _,
                lateout("r11") _,
                options(nostack)
            );
        }
        (ret, sc_start, sc_end)
    }

    #[inline(never)]
    unsafe fn oracle_exit_gate(query: bool, code: usize) -> (u64, u64) {
        let mut sc_start: u64 = 0;
        let mut sc_end: u64 = 0;
        let q_flag: u32 = if query { 1 } else { 0 };
        unsafe {
            asm!(
                "test {q:e}, {q:e}",
                "jz 2f",
                "lea {start}, [rip + 2f]",
                "lea {end}, [rip + 3f]",
                "jmp 3f",
                ".p2align 4",
                "2:",
                "syscall",
                "3:",
                start = inout(reg) sc_start,
                end = inout(reg) sc_end,
                q = in(reg) q_flag,
                inlateout("rax") 231usize => _,
                in("rdi") code,
                lateout("rcx") _,
                lateout("r11") _,
                options(nostack)
            );
        }
        (sc_start, sc_end)
    }

    const SYS_READ: usize = 0;
    const SYS_CLOSE: usize = 3;
    const SYS_PAUSE: usize = 34;
    const SYS_CLONE: usize = 56;
    const SYS_WAIT4: usize = 61;
    const SYS_FCNTL: usize = 72;
    const SYS_PRCTL: usize = 157;
    const SYS_EXIT_GROUP: usize = 231;
    const SYS_PIPE2: usize = 293;
    const SYS_PRLIMIT64: usize = 302;

    struct Bpf(Vec<SockFilter>);
    impl Bpf {
        fn ld(&mut self, k: u32) {
            self.0.push(SockFilter { code: 0x20, jt: 0, jf: 0, k });
        }
        fn jeq(&mut self, k: u32, jt: u8, jf: u8) {
            self.0.push(SockFilter { code: 0x15, jt, jf, k });
        }
        fn jgt(&mut self, k: u32, jt: u8, jf: u8) {
            self.0.push(SockFilter { code: 0x25, jt, jf, k });
        }
        fn jge(&mut self, k: u32, jt: u8, jf: u8) {
            self.0.push(SockFilter { code: 0x35, jt, jf, k });
        }
        fn jset(&mut self, k: u32, jt: u8, jf: u8) {
            self.0.push(SockFilter { code: 0x45, jt, jf, k });
        }
        fn ret(&mut self, k: u32) {
            self.0.push(SockFilter { code: 0x06, jt: 0, jf: 0, k });
        }
        fn if_nr_eq(&mut self, nr: u32, body: impl FnOnce(&mut Self)) {
            let jmp_idx = self.0.len();
            self.jeq(nr, 0, 0);
            body(self);
            let skip = self.0.len() - (jmp_idx + 1);
            self.0[jmp_idx].jf = skip as u8;
        }
    }

    fn install_seccomp(result_fd: u32) -> Result<(), ()> {
        const RET_KILL_PROCESS: u32 = 0x8000_0000;
        const RET_ALLOW: u32 = 0x7fff_0000;
        const ARCH_X86_64: u32 = 0xc000_003e;
        let (_, w_start, w_end) = unsafe { oracle_write_gate(true, 0, 0, 0) };
        let (e_start, e_end) = unsafe { oracle_exit_gate(true, 0) };
        let w_hi = (w_start >> 32) as u32;
        let e_hi = (e_start >> 32) as u32;
        if w_hi != ((w_end >> 32) as u32) || e_hi != ((e_end >> 32) as u32) {
            return Err(());
        }
        let w_lo_min = w_start as u32;
        let w_lo_max = w_end as u32;
        let e_lo_min = e_start as u32;
        let e_lo_max = e_end as u32;

        let mut bpf = Bpf(Vec::with_capacity(112));
        bpf.ld(4);
        bpf.jeq(ARCH_X86_64, 1, 0);
        bpf.ret(RET_KILL_PROCESS);
        bpf.ld(0);
        bpf.jgt(0x3fff_ffff, 0, 1);
        bpf.ret(RET_KILL_PROCESS);

        // SYS_write(1): allow stdout/stderr; allow `result_fd` strictly when
        // `instruction_pointer` is inside `oracle_write_gate`.
        bpf.if_nr_eq(1, |b| {
            b.ld(20);
            b.jeq(0, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.ld(16);
            b.jeq(1, 0, 1);
            b.ret(RET_ALLOW);
            b.jeq(2, 0, 1);
            b.ret(RET_ALLOW);
            b.jeq(result_fd, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.ld(12);
            b.jeq(w_hi, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.ld(8);
            b.jge(w_lo_min, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.jgt(w_lo_max, 0, 1);
            b.ret(RET_KILL_PROCESS);
            b.ret(RET_ALLOW);
        });

        // SYS_writev(20): allow stdout/stderr only.
        bpf.if_nr_eq(20, |b| {
            b.ld(20);
            b.jeq(0, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.ld(16);
            b.jeq(1, 0, 1);
            b.ret(RET_ALLOW);
            b.jeq(2, 0, 1);
            b.ret(RET_ALLOW);
            b.ret(RET_KILL_PROCESS);
        });

        // SYS_exit_group(231): allow strictly inside `oracle_exit_gate`.
        bpf.if_nr_eq(231, |b| {
            b.ld(12);
            b.jeq(e_hi, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.ld(8);
            b.jge(e_lo_min, 1, 0);
            b.ret(RET_KILL_PROCESS);
            b.jgt(e_lo_max, 0, 1);
            b.ret(RET_KILL_PROCESS);
            b.ret(RET_ALLOW);
        });

        // Block PROT_EXEC (0x4) in mmap(9), mprotect(10), pkey_mprotect(329).
        for nr in [9u32, 10u32, 329u32] {
            bpf.if_nr_eq(nr, |b| {
                b.ld(32);
                b.jset(4, 0, 1);
                b.ret(RET_KILL_PROCESS);
                b.ret(RET_ALLOW);
            });
        }

        // Unconditionally deny fs probing, exec/fork, dup/fcntl, splicing,
        // ptrace, cross-fd writes, and seccomp/prctl escape syscalls.
        const BLOCKED_NRS: &[u32] = &[
            2, 4, 6, 18, 21, 32, 33, 40, 56, 57, 58, 59, 60, 62, 72, 78,
            85, 89, 101, 157, 200, 217, 234, 257, 262, 267, 269, 275, 276,
            278, 292, 296, 310, 311, 312, 317, 319, 322, 323, 326, 328, 332,
            425, 426, 427, 435, 436, 437, 439,
        ];
        for &nr in BLOCKED_NRS {
            bpf.jeq(nr, 0, 1);
            bpf.ret(RET_KILL_PROCESS);
        }
        bpf.ret(RET_ALLOW);

        let prog = SockFprog {
            len: bpf.0.len() as u16,
            filter: bpf.0.as_ptr(),
        };
        unsafe {
            if sc5(SYS_PRCTL, 4, 0, 0, 0, 0) < 0 { return Err(()); }
            if sc5(SYS_PRCTL, 38, 1, 0, 0, 0) < 0 { return Err(()); }
            if sc5(SYS_PRCTL, 22, 2, &prog as *const _ as usize, 0, 0) < 0 {
                return Err(());
            }
        }
        Ok(())
    }

    pub fn run_inputs(target_fn: fn(u32) -> u32, inputs: &[u32]) {
        for &x in inputs {
            let mut fds = [0i32; 2];
            if unsafe { sc2(SYS_PIPE2, fds.as_mut_ptr() as usize, 0o2000000) } < 0 {
                unsafe { sc1(SYS_EXIT_GROUP, 90); }
            }
            let pid = unsafe { sc2(SYS_CLONE, 17, 0) };
            if pid < 0 {
                unsafe { sc1(SYS_EXIT_GROUP, 90); }
            }
            if pid == 0 {
                unsafe { sc1(SYS_CLOSE, fds[0] as usize); }
                let min_fd = 256 + (((&x as *const u32 as usize) >> 4) & 0xff);
                let high_fd = unsafe { sc3(SYS_FCNTL, fds[1] as usize, 1030, min_fd) };
                if high_fd < 0 {
                    loop { unsafe { sc0(SYS_PAUSE); } }
                }
                unsafe { sc1(SYS_CLOSE, fds[1] as usize); }
                let result_fd = high_fd as u32;
                let mut rl = Rlimit { rlim_cur: 0, rlim_max: 0 };
                if unsafe { sc4(SYS_PRLIMIT64, 0, 3, 0, &mut rl as *mut _ as usize) } == 0 {
                    let want: u64 = 64 * 1024 * 1024;
                    if rl.rlim_cur < want && want <= rl.rlim_max {
                        rl.rlim_cur = want;
                        let _ = unsafe { sc4(SYS_PRLIMIT64, 0, 3, &rl as *const _ as usize, 0) };
                    }
                }
                if install_seccomp(result_fd).is_err() {
                    loop { unsafe { sc0(SYS_PAUSE); } }
                }
                let mut msg = [0u8; 5];
                match std::panic::catch_unwind(
                    std::panic::AssertUnwindSafe(|| target_fn(x))
                ) {
                    Ok(got) => {
                        msg[0] = 1;
                        msg[1..5].copy_from_slice(&got.to_le_bytes());
                    }
                    Err(_) => { msg[0] = 2; }
                }
                let mut off = 0usize;
                while off < 5 {
                    let (n, _, _) = unsafe {
                        oracle_write_gate(false, result_fd as usize, msg[off..].as_ptr() as usize, 5 - off)
                    };
                    if n <= 0 { break; }
                    off += n as usize;
                }
                unsafe {
                    oracle_exit_gate(false, 0);
                }
                loop { unsafe { sc0(SYS_PAUSE); } }
            }
            unsafe { sc1(SYS_CLOSE, fds[1] as usize); }
            let mut msg = [0u8; 6];
            let mut off = 0usize;
            while off < msg.len() {
                let n = unsafe {
                    sc3(SYS_READ, fds[0] as usize, msg[off..].as_mut_ptr() as usize, msg.len() - off)
                };
                if n <= 0 { break; }
                off += n as usize;
            }
            let mut st = 0i32;
            unsafe {
                sc1(SYS_CLOSE, fds[0] as usize);
                sc4(SYS_WAIT4, pid as usize, &mut st as *mut _ as usize, 0, 0);
            }
            let exited_zero = (st & 0x7f) == 0 && ((st >> 8) & 0xff) == 0;
            if !exited_zero || off != 5 || msg[0] != 1 {
                if exited_zero && off == 5 && msg[0] == 2 {
                    eprintln!("panic or blocked exit on input={x}");
                    let _ = std::io::stderr().flush();
                    unsafe { sc1(SYS_EXIT_GROUP, 43); }
                }
                let sig = st & 0x7f;
                if sig != 0 && sig != 0x7f && sig != 31 {
                    unsafe { sc1(SYS_EXIT_GROUP, (128 + sig) as usize); }
                }
                eprintln!("panic or blocked exit on input={x}");
                let _ = std::io::stderr().flush();
                unsafe { sc1(SYS_EXIT_GROUP, 43); }
            }
            let got = u32::from_le_bytes([msg[1], msg[2], msg[3], msg[4]]);
            if got != x {
                eprintln!("wrong return: input={x} got={got}");
                let _ = std::io::stderr().flush();
                unsafe { sc1(SYS_EXIT_GROUP, 42); }
            }
        }
    }
}
"""


def _render_s2_oracle_main_rs(nonce: str, inputs_lit: str) -> str:
    """Render `redteam_s2_oracle/src/main.rs` keeping nonces strictly under Miri."""
    return (
        "#[cfg(miri)]\n"
        "fn run_oracle_inputs_miri(target_fn: fn(u32) -> u32, inputs: &[u32]) {\n"
        "    use std::io::Write as _;\n"
        "    for &x in inputs {\n"
        "        match std::panic::catch_unwind(\n"
        "            std::panic::AssertUnwindSafe(|| target_fn(x))\n"
        "        ) {\n"
        "            Ok(got) => {\n"
        "                if got != x {\n"
        "                    eprintln!(\n"
        f'                        "ANNEAL_ORACLE_MISMATCH_{nonce}: '
        'input={x} got={got}"\n'
        "                    );\n"
        "                    let _ = std::io::stderr().flush();\n"
        "                    std::process::exit(42);\n"
        "                }\n"
        "            }\n"
        "            Err(_) => {\n"
        f'                eprintln!("ANNEAL_ORACLE_PANIC_{nonce}: input={{x}}");\n'
        "                let _ = std::io::stderr().flush();\n"
        "                std::process::exit(43);\n"
        "            }\n"
        "        }\n"
        "    }\n"
        "}\n\n"
        "#[cfg(miri)]\n"
        "fn main() {\n"
        "    use std::io::Write as _;\n"
        "    let target_fn: fn(u32) -> u32 = redteam_s2::target;\n"
        f"    let inputs: &'static [u32] = &[{inputs_lit}];\n"
        f'    eprintln!("ANNEAL_ORACLE_START_{nonce}");\n'
        "    let _ = std::io::stderr().flush();\n"
        "    match std::thread::Builder::new()\n"
        "        .stack_size(64 * 1024 * 1024)\n"
        "        .spawn(move || run_oracle_inputs_miri(target_fn, inputs))\n"
        "    {\n"
        "        Ok(handle) => {\n"
        "            if handle.join().is_err() {\n"
        f'                eprintln!("ANNEAL_ORACLE_PANIC_{nonce}: join");\n'
        "                let _ = std::io::stderr().flush();\n"
        "                std::process::exit(43);\n"
        "            }\n"
        "        }\n"
        "        Err(_) => run_oracle_inputs_miri(target_fn, inputs),\n"
        "    }\n"
        f'    eprintln!("ANNEAL_ORACLE_END_{nonce}");\n'
        "    let _ = std::io::stderr().flush();\n"
        "}\n"
        + _S2_NATIVE_ORACLE_RS
        + '\n#[cfg(all(not(miri), target_arch = "x86_64", target_os = "linux"))]\n'
        "fn main() {\n"
        f"    let inputs: &'static [u32] = &[{inputs_lit}];\n"
        "    native_oracle::run_inputs(redteam_s2::target, inputs);\n"
        "}\n"
    )


_S2_SUPERVISOR_RS = r"""
use std::io::{Read as _, Write as _};
use std::os::unix::process::ExitStatusExt as _;
use std::process::{Command, Stdio};

const MAX_CHILD_STREAM: usize = 32 * 1024;

#[cfg(all(target_arch = "x86_64", target_os = "linux"))]
fn disable_dumpable() {
    unsafe {
        let mut _ret: isize;
        core::arch::asm!(
            "syscall",
            inlateout("rax") 157usize => _ret,
            in("rdi") 4usize,
            in("rsi") 0usize,
            in("rdx") 0usize,
            in("r10") 0usize,
            in("r8") 0usize,
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack)
        );
    }
}

#[cfg(not(all(target_arch = "x86_64", target_os = "linux")))]
fn disable_dumpable() {}

fn drain_bounded<R: std::io::Read>(mut r: R) -> String {
    let mut kept: Vec<u8> = Vec::new();
    let mut buf = [0u8; 4096];
    while let Ok(n) = r.read(&mut buf) {
        if n == 0 {
            break;
        }
        if kept.len() < MAX_CHILD_STREAM {
            let take = (MAX_CHILD_STREAM - kept.len()).min(n);
            kept.extend_from_slice(&buf[..take]);
        }
    }
    String::from_utf8_lossy(&kept)
        .replace("ANNEAL_ORACLE_", "ANNEAL_UNTRUSTED_")
}

fn main() {
    disable_dumpable();
    let mut cfg = String::new();
    if std::io::stdin().read_to_string(&mut cfg).is_err() {
        std::process::exit(91);
    }
    let mut lines = cfg.lines();
    let nonce = lines.next().unwrap_or("").trim().to_string();
    let child_path = lines.next().unwrap_or("").trim().to_string();
    if nonce.is_empty() || child_path.is_empty() {
        std::process::exit(91);
    }

    eprintln!("ANNEAL_ORACLE_START_{nonce}");
    let _ = std::io::stderr().flush();

    let mut child = match Command::new(&child_path)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(c) => c,
        Err(err) => {
            eprintln!("failed to spawn S2 oracle child: {err}");
            std::process::exit(92);
        }
    };

    let c_out = child.stdout.take();
    let c_err = child.stderr.take();
    let (out_txt, err_txt) = std::thread::scope(|s| {
        let t1 = s.spawn(move || c_out.map(drain_bounded).unwrap_or_default());
        let t2 = s.spawn(move || c_err.map(drain_bounded).unwrap_or_default());
        (t1.join().unwrap_or_default(), t2.join().unwrap_or_default())
    });

    let status = match child.wait() {
        Ok(st) => st,
        Err(err) => {
            eprintln!("failed waiting on S2 oracle child: {err}");
            std::process::exit(93);
        }
    };

    if !err_txt.is_empty() {
        eprintln!("{err_txt}");
    }
    if !out_txt.is_empty() {
        println!("{out_txt}");
    }
    let summary = err_txt.trim();
    if status.success() {
        eprintln!("ANNEAL_ORACLE_END_{nonce}");
        let _ = std::io::stderr().flush();
        std::process::exit(0);
    }
    if let Some(code) = status.code() {
        if code == 42 {
            eprintln!("ANNEAL_ORACLE_MISMATCH_{nonce}: {summary}");
        } else if code == 43 {
            eprintln!("ANNEAL_ORACLE_PANIC_{nonce}: {summary}");
        }
        let _ = std::io::stderr().flush();
        std::process::exit(code);
    }
    let sig = status.signal().unwrap_or(1);
    let _ = std::io::stderr().flush();
    std::process::exit(128 + sig);
}
"""


def _run_s2_code_oracle(
    *,
    tmp_root: Path,
    crate_dir: Path | None = None,
    src_files: dict[str, bytes] | None = None,
    inputs: list[int],
    env: dict[str, str],
    timeout: int,
    sysroot: Path | None = None,
    bwrap: Path | None = None,
    verified_target: str = VERIFIED_RUST_TARGET,
    miri_runner: Callable[..., Any] | None = None,
    rustc_runner: Callable[..., Any] | None = None,
    _check_pre_main_ref: bool = True,
) -> tuple[str, str | None, str]:
    """Execute ground-truth Miri + rustc correctness oracle for Scenario 2.

    Returns `(oracle_status, oracle_fault_class, diagnostic_detail)`:
    - `ub_confirmed`, `ub:<class>` when Miri detects UB
    - `spec_violation_confirmed`, `spec_violation:<class>` on wrong output/panic
    - `oracle_timeout`, `None` when oracle execution times out (fail-closed)
    - `clean`, `None` when code compiles and passes all checks
    - `compile_error`, `None` when attacker code fails to compile cleanly
    """
    oracle_crate = tmp_root / "oracle_crate"
    oracle_crate_src = oracle_crate / "src"
    oracle_crate_src.mkdir(parents=True, exist_ok=True)
    _write_new_regular_file_excl(
        oracle_crate / "Cargo.toml", scenarios._S2_CARGO_TOML.encode("utf-8")
    )
    oracle_src_resolved = oracle_crate_src.resolve()
    if src_files is not None:
        if "src/lib.rs" not in src_files:
            raise OracleInfrastructureError(
                "missing required `src/lib.rs` in verified submission bytes"
            )
        for rel, data in sorted(src_files.items()):
            if not rel.startswith("src/"):
                continue
            rel_s = rel[len("src/") :]
            dest_s = (oracle_crate_src / rel_s).resolve()
            if not dest_s.is_relative_to(oracle_src_resolved):
                raise OracleInfrastructureError(
                    f"oracle source escapes sandbox tree: {rel}"
                )
            _write_new_regular_file_excl(dest_s, data)
    else:
        if crate_dir is None:
            raise OracleInfrastructureError(
                "missing Scenario 2 source tree and submission bytes"
            )
        src_in = crate_dir / "src"
        if not src_in.is_dir() or src_in.is_symlink():
            raise OracleInfrastructureError(
                f"missing or symlinked Scenario 2 source tree: {src_in}"
            )
        src_in_resolved = src_in.resolve()
        for cur_root, dirnames, filenames in os.walk(
            src_in, topdown=True, followlinks=False
        ):
            cur_p = Path(cur_root)
            for dname in dirnames:
                dpath = cur_p / dname
                st = os.lstat(dpath)
                if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
                    raise OracleInfrastructureError(
                        f"symlink/non-dir in Scenario 2 source tree: {dpath}"
                    )
            for fname in filenames:
                fpath = cur_p / fname
                rel_s = fpath.relative_to(src_in_resolved).as_posix()
                data = _read_regular_file_nofollow(
                    fpath,
                    label=f"oracle source {rel_s}",
                    exc_type=OracleInfrastructureError,
                )
                dest_s = (oracle_crate_src / rel_s).resolve()
                if not dest_s.is_relative_to(oracle_src_resolved):
                    raise OracleInfrastructureError(
                        f"oracle source escapes sandbox tree: {rel_s}"
                    )
                _write_new_regular_file_excl(dest_s, data)

    oracle_dir = tmp_root / "oracle_harness"
    oracle_src = oracle_dir / "src"
    oracle_src.mkdir(parents=True, exist_ok=True)
    cargo_home = tmp_root / "oracle_cargo_home"
    cargo_home.mkdir(parents=True, exist_ok=True)
    (cargo_home / "config.toml").write_text(
        "[net]\noffline = true\n", encoding="utf-8"
    )
    nonce = secrets.token_hex(12)
    inputs_lit = ", ".join(str(v) for v in inputs)
    (oracle_dir / "Cargo.toml").write_text(
        '[package]\nname = "redteam_s2_oracle"\nversion = "0.1.0"\n'
        'edition = "2024"\nbuild = false\n\n'
        "[profile.dev]\n"
        "opt-level = 0\n"
        "debug-assertions = false\n"
        "overflow-checks = false\n"
        'panic = "unwind"\n\n'
        '[dependencies]\nredteam_s2 = { path = "../oracle_crate" }\n',
        encoding="utf-8",
    )
    (oracle_src / "main.rs").write_text(
        _render_s2_oracle_main_rs(nonce, inputs_lit),
        encoding="utf-8",
    )

    oracle_encoded_rustflags = "--remap-path-prefix=/work/oracle_crate=redteam_crate"
    bwrap_cargo_env = {
        "PATH": "/toolchain/bin:/usr/bin:/bin",
        "HOME": "/work/tmp",
        "TMPDIR": "/work/tmp",
        "CARGO_HOME": "/work/cargo_home",
        "RUSTC": "/toolchain/bin/rustc",
        "LD_LIBRARY_PATH": "/toolchain/lib",
        "CARGO_NET_OFFLINE": "true",
        "CARGO_ENCODED_RUSTFLAGS": oracle_encoded_rustflags,
        "NO_COLOR": "1",
    }
    bwrap_miri_env = {
        **bwrap_cargo_env,
        "MIRI_SYSROOT": "/miri_sysroot",
        "MIRIFLAGS": "-Zmiri-tree-borrows -Zmiri-strict-provenance",
    }

    is_live = miri_runner is None or rustc_runner is None
    bwrap_path: Path | None = None
    miri_sysroot_host: Path | None = None
    if is_live:
        bwrap_path = _resolve_bwrap_binary(bwrap, required=True)
        if (
            bwrap_path is None
            or sysroot is None
            or not sysroot.is_dir()
            or not (sysroot / "bin" / "cargo").is_file()
            or not (sysroot / "bin" / "rustc").is_file()
        ):
            raise OracleInfrastructureError(
                "Scenario 2 live oracle requires bwrap and pinned sysroot"
            )
        if miri_runner is None:
            raw_ms = env.get("MIRI_SYSROOT")
            if not raw_ms or not Path(raw_ms).is_dir():
                raise OracleInfrastructureError(
                    "MIRI_SYSROOT missing for Scenario 2 ground-truth Miri check"
                )
            miri_sysroot_host = Path(raw_ms)

        # Reject `#[cfg(miri)]`, `cfg!(miri)`, `file!()`, and Cargo/oracle
        # environment variance (`verify.rs` clears env to PATH=/usr/bin:/bin
        # plus LD_LIBRARY_PATH, whereas `cargo build` / `cargo miri` inject
        # Cargo and Miri env vars).
        norm_env = {
            "PATH": "/usr/bin:/bin",
            "LD_LIBRARY_PATH": "/toolchain/lib",
        }
        alt_env = {
            "PATH": "/alt/bin:/toolchain/bin:/usr/bin:/bin",
            "HOME": "/alt/tmp",
            "TMPDIR": "/alt/tmp",
            "LD_LIBRARY_PATH": "/alt/lib:/toolchain/lib",
            "NO_COLOR": "1",
            "CARGO": "/alt/bin/cargo",
            "CARGO_HOME": "/alt/cargo_home",
            "CARGO_MANIFEST_DIR": "/work/alt_probe/sub/crate",
            "CARGO_MANIFEST_PATH": "/work/alt_probe/sub/crate/Cargo.toml",
            "CARGO_PKG_NAME": "redteam_s2_alt",
            "CARGO_PKG_VERSION": "9.9.9-alt",
            "CARGO_PKG_VERSION_MAJOR": "9",
            "CARGO_PKG_VERSION_MINOR": "9",
            "CARGO_PKG_VERSION_PATCH": "9",
            "CARGO_PKG_VERSION_PRE": "alt",
            "CARGO_PKG_AUTHORS": "alt-author",
            "CARGO_PKG_DESCRIPTION": "alt-desc",
            "CARGO_PKG_HOMEPAGE": "https://alt.invalid",
            "CARGO_PKG_REPOSITORY": "https://alt.invalid/repo",
            "CARGO_PKG_LICENSE": "MIT",
            "CARGO_PKG_LICENSE_FILE": "LICENSE-ALT",
            "CARGO_PKG_README": "README-ALT.md",
            "CARGO_PKG_RUST_VERSION": "1.0.0",
            "CARGO_CRATE_NAME": "redteam_s2_alt",
            "CARGO_BIN_NAME": "redteam_s2_alt_bin",
            "CARGO_PRIMARY_PACKAGE": "1",
            "CARGO_TARGET_TMPDIR": "/alt/target_tmp",
            "CARGO_NET_OFFLINE": "false",
            "CARGO_ENCODED_RUSTFLAGS": "--cfg\x1falt_probe",
            "RUSTFLAGS": "--cfg alt_probe",
            "RUSTC": "/alt/bin/rustc",
            "RUSTC_WRAPPER": "/alt/bin/wrapper",
            "RUSTC_WORKSPACE_WRAPPER": "/alt/bin/ws_wrapper",
            "RUSTC_STAGE": "1",
            "RUSTC_LINKER": "/alt/bin/ld",
            "RUSTDOC": "/alt/bin/rustdoc",
            "RUSTUP_TOOLCHAIN": "alt-toolchain",
            "CARGO_BUILD_JOBS": "4",
            "OUT_DIR": "/alt/out",
            "OPT_LEVEL": "3",
            "DEBUG": "false",
            "PROFILE": "release",
            "TARGET": "alt-target-triple",
            "HOST": "alt-host-triple",
            "MIRI_SYSROOT": "/alt/miri_sysroot",
            "MIRIFLAGS": "-Zmiri-alt-probe",
            "MIRI_BE_RUSTC": "target",
            "MIRI_LOCAL_CRATES": "redteam_s2\nredteam_s2_oracle",
            "MIRI_HOST_SYSROOT": "/alt/toolchain",
            "MIRI_CWD": "/work/alt_probe/sub/crate",
            "MIRI_LIB_SRC": "/alt/miri/library",
            "MIRI_NO_STD": "0",
            "MIRI_VERBOSE": "1",
        }
        _verify_bwrap_canary(
            bwrap_path,
            ro_mounts=[(sysroot, "/toolchain")],
            env_vars=norm_env,
            argv=["/toolchain/bin/rustc", "--version"],
            ro_system_bins=True,
            tmpfs_tmp=True,
            disable_userns=True,
            label="s2_oracle_rustc",
        )
        vv_proc = _run_cmd_in_bwrap(
            bwrap=bwrap_path,
            ro_mounts=[(sysroot, "/toolchain")],
            rw_mounts=[],
            env_vars=norm_env,
            cwd_in_sandbox="/work/tmp",
            argv=["/toolchain/bin/rustc", "-vV"],
            timeout=15,
            ro_system_bins=True,
            tmpfs_tmp=True,
        )
        host_triple: str | None = None
        if vv_proc.returncode == 0:
            for vv_line in vv_proc.stdout.splitlines():
                if vv_line.startswith("host:"):
                    host_triple = vv_line.split(":", 1)[1].strip() or None
                    break
        if host_triple != verified_target:
            raise OracleInfrastructureError(
                f"Scenario 2 live oracle requires host triple "
                f"{verified_target!r} matching Anneal verified target, "
                f"got {host_triple!r}"
            )
        exp_args = [
            "/toolchain/bin/rustc",
            "--target",
            verified_target,
            "--edition",
            "2024",
            "--crate-type",
            "lib",
            "--crate-name",
            "redteam_s2",
            "-C",
            "opt-level=0",
            "-C",
            "debug-assertions=no",
            "-C",
            "overflow-checks=no",
            "-C",
            "panic=unwind",
            "-Zunpretty=expanded",
        ]
        exp_target = tmp_root / "exp_target"
        exp_miri_target = tmp_root / "exp_miri_target"
        exp_target.mkdir(parents=True, exist_ok=True)
        exp_miri_target.mkdir(parents=True, exist_ok=True)
        cargo_exp_ro = [
            (sysroot, "/toolchain"),
            (oracle_crate, "/work/oracle_crate"),
        ]
        cargo_miri_exp_ro = list(cargo_exp_ro)
        if miri_sysroot_host is not None:
            cargo_miri_exp_ro.append((miri_sysroot_host, "/miri_sysroot"))
        try:
            exp_norm = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=cargo_exp_ro,
                rw_mounts=[],
                env_vars=norm_env,
                cwd_in_sandbox="/work/oracle_crate",
                argv=[*exp_args, "/work/oracle_crate/src/lib.rs"],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
            exp_miri = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=cargo_exp_ro,
                rw_mounts=[],
                env_vars=norm_env,
                cwd_in_sandbox="/work/oracle_crate",
                argv=[*exp_args, "--cfg", "miri", "/work/oracle_crate/src/lib.rs"],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
            exp_alt = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=[
                    (sysroot, "/toolchain"),
                    (oracle_crate, "/work/alt_probe/sub/crate"),
                ],
                rw_mounts=[],
                env_vars=alt_env,
                cwd_in_sandbox="/work/alt_probe/sub/crate",
                argv=[*exp_args, "/work/alt_probe/sub/crate/src/lib.rs"],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
            exp_cargo = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=cargo_exp_ro,
                rw_mounts=[
                    (oracle_dir, "/work/oracle_harness"),
                    (exp_target, "/work/exp_target"),
                    (cargo_home, "/work/cargo_home"),
                ],
                env_vars=bwrap_cargo_env,
                cwd_in_sandbox="/work/oracle_harness",
                argv=[
                    "/toolchain/bin/cargo",
                    "rustc",
                    "--quiet",
                    "--offline",
                    "--target",
                    verified_target,
                    "--manifest-path",
                    "/work/oracle_harness/Cargo.toml",
                    "--target-dir",
                    "/work/exp_target",
                    "-p",
                    "redteam_s2",
                    "--lib",
                    "--",
                    "-Zunpretty=expanded",
                ],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
            use_cargo_miri_exp = (
                miri_sysroot_host is not None
                and (sysroot / "bin" / "miri").is_file()
                and (sysroot / "bin" / "cargo-miri").is_file()
            )
            if use_cargo_miri_exp:
                cargo_miri_exp_env = {
                    **bwrap_miri_env,
                    "RUSTC": "/toolchain/bin/miri",
                    "RUSTC_WRAPPER": "/toolchain/bin/cargo-miri",
                    "RUSTDOC": "/toolchain/bin/cargo-miri",
                    "MIRI_BE_RUSTC": "host",
                    "MIRI_LOCAL_CRATES": "redteam_s2\nredteam_s2_oracle",
                    "MIRI_VERBOSE": "0",
                }
                cargo_miri_exp_argv = [
                    "/toolchain/bin/cargo",
                    "rustc",
                    "--quiet",
                    "--offline",
                    "--target",
                    verified_target,
                    "--manifest-path",
                    "/work/oracle_harness/Cargo.toml",
                    "--target-dir",
                    "/work/exp_miri_target",
                    "-p",
                    "redteam_s2",
                    "--lib",
                    "--",
                    "-Zunpretty=expanded",
                ]
            else:
                cargo_miri_exp_env = bwrap_miri_env
                cargo_miri_exp_argv = [
                    "/toolchain/bin/cargo",
                    "rustc",
                    "--quiet",
                    "--offline",
                    "--target",
                    verified_target,
                    "--manifest-path",
                    "/work/oracle_harness/Cargo.toml",
                    "--target-dir",
                    "/work/exp_miri_target",
                    "-p",
                    "redteam_s2",
                    "--lib",
                    "--",
                    "--cfg",
                    "miri",
                    "-Zunpretty=expanded",
                ]
            exp_cargo_miri = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=cargo_miri_exp_ro,
                rw_mounts=[
                    (oracle_dir, "/work/oracle_harness"),
                    (exp_miri_target, "/work/exp_miri_target"),
                    (cargo_home, "/work/cargo_home"),
                ],
                env_vars=cargo_miri_exp_env,
                cwd_in_sandbox="/work/oracle_harness",
                argv=cargo_miri_exp_argv,
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
        except subprocess.TimeoutExpired:
            return "oracle_timeout", None, "cfg(miri) expansion check timed out"
        def _check_expansion_probe(
            proc: subprocess.CompletedProcess[str],
            *,
            label: str,
        ) -> tuple[str, str | None, str] | None:
            out = ((proc.stderr or "") + "\n" + (proc.stdout or "")).strip()
            if _RUSTC_ICE_RE.search(out):
                return "oracle_inconclusive", None, out[:1800]
            if proc.returncode == 0:
                return None
            if (
                proc.returncode < 0
                or proc.returncode in (126, 127)
                or "bwrap:" in out
                or _SYSROOT_CRATE_MARKER_RE.search(out)
                or _CARGO_INFRA_ERR_RE.search(out)
                or (not _is_user_compile_error(out) and "error:" not in out)
            ):
                raise OracleInfrastructureError(
                    f"{label} expansion probe infrastructure failure "
                    f"(rc={proc.returncode}): {out[:400]}"
                )
            return None

        for probe_proc, probe_label in (
            (exp_norm, "rustc expansion"),
            (exp_miri, "rustc --cfg miri expansion"),
            (exp_alt, "alt-env rustc expansion"),
            (exp_cargo, "cargo rustc expansion"),
        ):
            ice_res = _check_expansion_probe(probe_proc, label=probe_label)
            if ice_res is not None:
                return ice_res

        if exp_cargo_miri.returncode != 0 and use_cargo_miri_exp:
            assert miri_sysroot_host is not None
            miri_lib_dir = (
                miri_sysroot_host / "lib" / "rustlib" / verified_target / "lib"
            )
            if not miri_lib_dir.is_dir() or not any(miri_lib_dir.glob("*.rlib")):
                raise OracleInfrastructureError(
                    f"incomplete or incompatible MIRI_SYSROOT for {verified_target}: "
                    f"missing .rlib artifacts under {miri_lib_dir}"
                )
        ice_miri_res = _check_expansion_probe(
            exp_cargo_miri, label="cargo-miri expansion"
        )
        if ice_miri_res is not None:
            return ice_miri_res

        def _probe_outputs_differ(
            a: subprocess.CompletedProcess[str],
            b: subprocess.CompletedProcess[str],
            *,
            use_stderr: bool = False,
        ) -> tuple[bool, bool]:
            field = "stderr" if use_stderr else "stdout"
            a_text = getattr(a, field)
            b_text = getattr(b, field)
            if a_text != b_text:
                return True, False
            a_sha = getattr(a, f"{field}_sha256", None)
            b_sha = getattr(b, f"{field}_sha256", None)
            a_len = getattr(a, f"{field}_bytes", None)
            b_len = getattr(b, f"{field}_bytes", None)
            if a_sha is not None and b_sha is not None:
                return (a_sha != b_sha or a_len != b_len), False
            a_trunc = bool(getattr(a, f"{field}_truncated", False))
            b_trunc = bool(getattr(b, f"{field}_truncated", False))
            return False, (a_trunc or b_trunc)

        miri_diff, miri_trunc = _probe_outputs_differ(
            exp_norm, exp_miri, use_stderr=(exp_norm.returncode != 0)
        )
        if exp_norm.returncode != exp_miri.returncode or miri_diff:
            raise InvalidSubmissionError(
                "Miri-conditional Rust code (`cfg(miri)`) is disallowed in Scenario 2"
            )
        if miri_trunc:
            return (
                "oracle_inconclusive",
                None,
                "expansion probe output truncated before Miri equality comparison",
            )
        alt_diff, alt_trunc = _probe_outputs_differ(exp_norm, exp_alt)
        cargo_diff, cargo_trunc = _probe_outputs_differ(exp_norm, exp_cargo)
        cargo_miri_diff, cargo_miri_trunc = _probe_outputs_differ(
            exp_miri, exp_cargo_miri
        )
        if (
            exp_norm.returncode != exp_alt.returncode
            or (exp_norm.returncode == 0 and alt_diff)
            or ((exp_norm.returncode == 0) != (exp_cargo.returncode == 0))
            or (exp_norm.returncode == 0 and cargo_diff)
            or ((exp_miri.returncode == 0) != (exp_cargo_miri.returncode == 0))
            or (exp_miri.returncode == 0 and cargo_miri_diff)
        ):
            raise InvalidSubmissionError(
                "Path- or Cargo-env-dependent macro expansion (`file!()` / `env!()`) "
                "is disallowed in Scenario 2"
            )
        if (
            (exp_norm.returncode == 0 and (alt_trunc or cargo_trunc))
            or (exp_miri.returncode == 0 and cargo_miri_trunc)
        ):
            return (
                "oracle_inconclusive",
                None,
                "expansion probe output truncated before env equality comparison",
            )
        if exp_norm.returncode != 0:
            exp_err = (exp_norm.stderr or exp_norm.stdout).strip()
            return "compile_error", None, exp_err[:1800]

    built_oracle_bin: Path | None = None
    if rustc_runner is None:
        assert bwrap_path is not None and sysroot is not None
        try:
            b_proc = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=[
                    (sysroot, "/toolchain"),
                    (oracle_crate, "/work/oracle_crate"),
                ],
                rw_mounts=[
                    (oracle_dir, "/work/oracle_harness"),
                    (cargo_home, "/work/cargo_home"),
                ],
                env_vars=bwrap_cargo_env,
                cwd_in_sandbox="/work/oracle_harness",
                argv=[
                    "/toolchain/bin/cargo",
                    "build",
                    "--quiet",
                    "--offline",
                    "--target",
                    verified_target,
                    "--message-format=json",
                    "--manifest-path",
                    "/work/oracle_harness/Cargo.toml",
                ],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
        except subprocess.TimeoutExpired:
            return "oracle_timeout", None, "rustc oracle build timed out"
        if b_proc.returncode != 0:
            has_u, has_sys, rendered_json = _inspect_cargo_json_diagnostics(
                b_proc.stdout
            )
            b_out = (b_proc.stderr + "\n" + rendered_json).strip()
            if _RUSTC_ICE_RE.search(b_out):
                return "oracle_inconclusive", None, b_out[:1800]
            if has_sys:
                raise OracleInfrastructureError(
                    f"rustc oracle sysroot build failed (rc={b_proc.returncode}): "
                    f"{b_out[:400]}"
                )
            if has_u or _is_user_compile_error(b_out):
                return "compile_error", None, b_out[:1800]
            raise OracleInfrastructureError(
                f"rustc oracle build failed (rc={b_proc.returncode}): {b_out[:400]}"
            )
        built_oracle_bin = (
            oracle_dir
            / "target"
            / verified_target
            / "debug"
            / "redteam_s2_oracle"
        )
        if not built_oracle_bin.is_file() or built_oracle_bin.is_symlink():
            raise OracleInfrastructureError(
                "missing compiled S2 oracle binary after cargo build"
            )
        _verify_s2_rlib_no_ctors(
            oracle_dir / "target" / verified_target / "debug",
            crate_name="redteam_s2",
        )

    built_supervisor: Path | None = None
    if rustc_runner is None:
        assert bwrap_path is not None and sysroot is not None
        sup_dir = tmp_root / "oracle_supervisor"
        sup_dir.mkdir(parents=True, exist_ok=True)
        _write_new_regular_file_excl(
            sup_dir / "supervisor.rs", _S2_SUPERVISOR_RS.encode("utf-8")
        )
        try:
            sup_b_proc = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=[(sysroot, "/toolchain")],
                rw_mounts=[(sup_dir, "/work/sup_dir")],
                env_vars={
                    "PATH": "/toolchain/bin:/usr/bin:/bin",
                    "HOME": "/work/tmp",
                    "TMPDIR": "/work/tmp",
                    "LD_LIBRARY_PATH": "/toolchain/lib",
                    "NO_COLOR": "1",
                },
                cwd_in_sandbox="/work/sup_dir",
                argv=[
                    "/toolchain/bin/rustc",
                    "--edition",
                    "2024",
                    "--target",
                    verified_target,
                    "-O",
                    "/work/sup_dir/supervisor.rs",
                    "-o",
                    "/work/sup_dir/redteam_s2_supervisor",
                ],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
        except subprocess.TimeoutExpired:
            return "oracle_timeout", None, "rustc supervisor build timed out"
        if sup_b_proc.returncode != 0:
            s_err = (sup_b_proc.stderr + "\n" + sup_b_proc.stdout).strip()
            raise OracleInfrastructureError(
                f"S2 supervisor build failed (rc={sup_b_proc.returncode}): {s_err[:400]}"
            )
        built_supervisor = sup_dir / "redteam_s2_supervisor"
        if not built_supervisor.is_file() or built_supervisor.is_symlink():
            raise OracleInfrastructureError("missing compiled S2 supervisor binary")

    miri_inconclusive: tuple[str, str | None, str] | None = None
    miri_timed_out = False
    m_proc: Any = None
    m_out = ""
    m_u_err = False
    m_s_err = False
    if miri_runner is not None:
        miri_env = dict(env)
        miri_env["CARGO_HOME"] = str(cargo_home)
        miri_env["CARGO_NET_OFFLINE"] = "true"
        miri_env["MIRIFLAGS"] = "-Zmiri-tree-borrows -Zmiri-strict-provenance"
        miri_cmd = [
            "cargo",
            "+nightly-2026-05-31",
            "miri",
            "run",
            "--quiet",
            "--offline",
            "--target",
            verified_target,
            "--manifest-path",
            str(oracle_dir / "Cargo.toml"),
        ]
        try:
            m_proc = miri_runner(
                miri_cmd, cwd=oracle_dir, env=miri_env, timeout=timeout
            )
            m_out = (m_proc.stderr + "\n" + m_proc.stdout).strip()
        except subprocess.TimeoutExpired:
            miri_timed_out = True
            miri_inconclusive = ("oracle_timeout", None, "miri oracle timed out")
    else:
        assert bwrap_path is not None and sysroot is not None
        assert miri_sysroot_host is not None
        try:
            m_proc = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=[
                    (sysroot, "/toolchain"),
                    (miri_sysroot_host, "/miri_sysroot"),
                    (oracle_crate, "/work/oracle_crate"),
                ],
                rw_mounts=[
                    (oracle_dir, "/work/oracle_harness"),
                    (cargo_home, "/work/cargo_home"),
                ],
                env_vars={
                    "PATH": "/toolchain/bin:/usr/bin:/bin",
                    "HOME": "/work/tmp",
                    "TMPDIR": "/work/tmp",
                    "CARGO_HOME": "/work/cargo_home",
                    "RUSTC": "/toolchain/bin/rustc",
                    "LD_LIBRARY_PATH": "/toolchain/lib",
                    "CARGO_NET_OFFLINE": "true",
                    "CARGO_ENCODED_RUSTFLAGS": oracle_encoded_rustflags,
                    "MIRI_SYSROOT": "/miri_sysroot",
                    "MIRIFLAGS": "-Zmiri-tree-borrows -Zmiri-strict-provenance",
                    "NO_COLOR": "1",
                },
                cwd_in_sandbox="/work/oracle_harness",
                argv=[
                    "/toolchain/bin/cargo",
                    "miri",
                    "run",
                    "--quiet",
                    "--offline",
                    "--target",
                    verified_target,
                    "--message-format=json",
                    "--manifest-path",
                    "/work/oracle_harness/Cargo.toml",
                ],
                timeout=timeout,
                ro_system_bins=True,
                tmpfs_tmp=True,
            )
            m_u_err, m_s_err, m_json_err = _inspect_cargo_json_diagnostics(
                m_proc.stdout
            )
            m_out = (
                m_proc.stderr + ("\n" + m_json_err if m_json_err else "")
            ).strip()
        except subprocess.TimeoutExpired:
            miri_timed_out = True
            miri_inconclusive = ("oracle_timeout", None, "miri oracle timed out")

    def _classify_with_pre_main_ref(
        out: str,
        rc: int,
        *,
        is_phase_live: bool,
        is_miri: bool,
        phase: str,
        has_user_compile_err: bool = False,
        has_sysroot_compile_err: bool = False,
    ) -> tuple[str, str | None, str] | None:
        try:
            return _classify_s2_oracle_exit(
                out,
                rc,
                nonce=nonce,
                is_live=is_phase_live,
                is_miri=is_miri,
                phase=phase,
                has_user_compile_err=has_user_compile_err,
                has_sysroot_compile_err=has_sysroot_compile_err,
            )
        except OracleInfrastructureError:
            start_tag = f"ANNEAL_ORACLE_START_{nonce}"
            if (
                not is_phase_live
                or not _check_pre_main_ref
                or start_tag in out
                or has_sysroot_compile_err
            ):
                raise
            ref_dir = tmp_root / f"ref_pre_main_{phase}"
            ref_dir.mkdir(parents=True, exist_ok=True)
            try:
                ref_status, _, _ = _run_s2_code_oracle(
                    tmp_root=ref_dir,
                    src_files={
                        "src/lib.rs": b"pub fn target(x: u32) -> u32 { x }\n"
                    },
                    inputs=inputs[:1] or [0],
                    env=env,
                    timeout=min(timeout, 60),
                    sysroot=sysroot,
                    verified_target=verified_target,
                    miri_runner=miri_runner,
                    rustc_runner=rustc_runner,
                    _check_pre_main_ref=False,
                )
            except Exception:
                ref_status = "error"
            if ref_status != "clean":
                raise
            return _classify_s2_oracle_exit(
                out,
                rc,
                nonce=nonce,
                is_live=is_phase_live,
                is_miri=is_miri,
                phase=phase,
                has_user_compile_err=has_user_compile_err,
                has_sysroot_compile_err=has_sysroot_compile_err,
                pre_main_ref_ok=True,
            )

    if not miri_timed_out:
        m_res = _classify_with_pre_main_ref(
            m_out,
            m_proc.returncode,
            is_phase_live=(miri_runner is None),
            is_miri=True,
            phase="miri",
            has_user_compile_err=m_u_err,
            has_sysroot_compile_err=m_s_err,
        )
        if m_res is not None:
            if m_res[0] != "oracle_inconclusive":
                return m_res
            miri_inconclusive = m_res

    if rustc_runner is not None:
        rustc_env = dict(env)
        rustc_env["CARGO_HOME"] = str(cargo_home)
        rustc_env["CARGO_NET_OFFLINE"] = "true"
        rustc_cmd = [
            "cargo",
            "+nightly-2026-05-31",
            "run",
            "--quiet",
            "--offline",
            "--target",
            verified_target,
            "--manifest-path",
            str(oracle_dir / "Cargo.toml"),
        ]
        try:
            r_proc = rustc_runner(
                rustc_cmd, cwd=oracle_dir, env=rustc_env, timeout=timeout
            )
        except subprocess.TimeoutExpired:
            detail = (
                "miri and rustc oracles timed out"
                if miri_timed_out
                else "rustc oracle timed out"
            )
            return "oracle_timeout", None, detail
    else:
        assert (
            bwrap_path is not None
            and built_oracle_bin is not None
            and built_supervisor is not None
        )
        sup_mount = f"rt_sup_{secrets.token_hex(8)}"
        child_mount = f"rt_child_{secrets.token_hex(8)}"
        try:
            r_proc = _run_cmd_in_bwrap(
                bwrap=bwrap_path,
                ro_mounts=[
                    (built_supervisor, f"/work/{sup_mount}"),
                    (built_oracle_bin, f"/work/{child_mount}"),
                ],
                rw_mounts=[],
                env_vars={
                    "PATH": "/usr/bin:/bin",
                    "HOME": "/work/tmp",
                    "TMPDIR": "/work/tmp",
                    "NO_COLOR": "1",
                },
                cwd_in_sandbox="/work/tmp",
                argv=[f"/work/{sup_mount}"],
                stdin_data=f"{nonce}\n/work/{child_mount}\n".encode("utf-8"),
                timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            detail = (
                "miri oracle timed out and rustc oracle execution timed out"
                if miri_timed_out
                else "rustc oracle execution timed out"
            )
            return "oracle_timeout", None, detail

    r_out = (r_proc.stderr + "\n" + r_proc.stdout).strip()
    r_res = _classify_with_pre_main_ref(
        r_out,
        r_proc.returncode,
        is_phase_live=(rustc_runner is None),
        is_miri=False,
        phase="rustc",
    )
    if r_res is not None:
        return r_res
    if miri_inconclusive is not None:
        return miri_inconclusive
    return "clean", None, "miri and rustc passed all checked inputs"


def _copy_regular_file_nofollow(src_f: Path, dst_f: Path) -> None:
    """Copy a single regular non-symlink file via single-fd `O_NOFOLLOW` + `fstat`."""
    try:
        fd = os.open(src_f, _OPEN_RO_FLAGS)
    except OSError as exc:
        raise OracleInfrastructureError(
            f"cannot open defender asset {src_f}: {exc}"
        ) from exc
    try:
        fst = os.fstat(fd)
        if not stat.S_ISREG(fst.st_mode):
            raise OracleInfrastructureError(
                f"non-regular defender asset disallowed: {src_f}"
            )
        mode = stat.S_IMODE(fst.st_mode)
        with os.fdopen(fd, "rb") as handle:
            fd = -1
            data = handle.read()
    finally:
        if fd >= 0:
            os.close(fd)
    _write_new_regular_file_excl(dst_f, data)
    os.chmod(dst_f, mode)


_SKIP_CHECKOUT_DIRS = frozenset(
    {".git", ".lake", "target", "__pycache__", ".pytest_cache", ".mypy_cache"}
)
_STAGE_CHECKOUT_ITEMS = (
    ("Cargo.toml", True),
    ("Cargo.lock", True),
    ("flake.nix", True),
    ("flake.lock", True),
    ("trusted", True),
    ("tests", True),
    ("tools", True),
    ("vendor", True),
    ("correspondence", True),
    ("theory", False),
)


def _list_tracked_anneal_paths(
    anneal_root: Path, *, git_bin: Path | None = None
) -> list[str] | None:
    """Return git-tracked paths relative to `anneal_root`, or None if unbacked."""
    resolved_git = (
        git_bin
        if git_bin is not None
        else _resolve_system_binary("git", required=False)
    )
    if resolved_git is None:
        return None
    clean_env = _clean_git_env(resolved_git)
    try:
        top = subprocess.run(
            [
                str(resolved_git),
                *anneal_ci_lib.SAFE_GIT_FLAGS,
                "-C",
                str(anneal_root),
                "rev-parse",
                "--show-toplevel",
            ],
            capture_output=True,
            text=True,
            env=clean_env,
            timeout=10,
            check=False,
        )
        if top.returncode != 0:
            return None
        top_resolved = Path(top.stdout.strip()).resolve()
        root_resolved = anneal_root.resolve()
        if top_resolved not in (root_resolved, root_resolved.parent):
            return None
        names = [name for name, _pin in _STAGE_CHECKOUT_ITEMS]
        listed = subprocess.run(
            [
                str(resolved_git),
                *anneal_ci_lib.SAFE_GIT_FLAGS,
                "-C",
                str(anneal_root),
                "ls-files",
                "-z",
                "--",
                *names,
            ],
            capture_output=True,
            env=clean_env,
            timeout=15,
            check=False,
        )
        if listed.returncode != 0:
            return None
    except (OSError, subprocess.SubprocessError):
        return None
    rels = [
        raw.decode("utf-8", errors="strict")
        for raw in listed.stdout.split(b"\x00")
        if raw
    ]
    return sorted(rels) if rels else None


def _copy_strict_tree(src: Path, dst: Path) -> None:
    """Copy `src` to `dst`, pruning build caches and refusing symlinks."""
    dst.mkdir(parents=True, exist_ok=True)
    for cur_root, dirnames, filenames in os.walk(
        src, topdown=True, followlinks=False
    ):
        dirnames[:] = sorted(
            d for d in dirnames if d not in _SKIP_CHECKOUT_DIRS
        )
        cur = Path(cur_root)
        rel_dir = cur.relative_to(src)
        for dname in dirnames:
            dpath = cur / dname
            st = os.lstat(dpath)
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
                raise OracleInfrastructureError(
                    f"symlink in defender tree disallowed: {dpath}"
                )
            (dst / rel_dir / dname).mkdir(parents=True, exist_ok=True)
        for fname in sorted(filenames):
            if fname.endswith(".pyc"):
                continue
            _copy_regular_file_nofollow(cur / fname, dst / rel_dir / fname)


def _stage_anneal_checkout_copy(
    anneal_root: Path, dst_root: Path, *, git_bin: Path | None = None
) -> list[str]:
    """Copy tracked/pinned `anneal/` checkout trees cleanly, returning pinned paths."""
    dst_root.mkdir(parents=True, exist_ok=True)
    defender_rels: list[str] = []
    tracked = _list_tracked_anneal_paths(anneal_root, git_bin=git_bin)
    if tracked is not None:
        pin_map = dict(_STAGE_CHECKOUT_ITEMS)
        for rel in tracked:
            top_seg = rel.split("/", 1)[0]
            if top_seg not in pin_map:
                continue
            src_f = anneal_root / rel
            dst_f = dst_root / rel
            _copy_regular_file_nofollow(src_f, dst_f)
            if pin_map[top_seg]:
                defender_rels.append(rel)
        return defender_rels

    for name, pin in _STAGE_CHECKOUT_ITEMS:
        src_p = anneal_root / name
        dst_p = dst_root / name
        if name in ("Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"):
            if src_p.exists() or src_p.is_symlink():
                _copy_regular_file_nofollow(src_p, dst_p)
                if pin:
                    defender_rels.append(name)
        elif src_p.is_dir():
            _copy_strict_tree(src_p, dst_p)
            if pin:
                for p in sorted(dst_p.rglob("*")):
                    if p.is_file():
                        defender_rels.append(p.relative_to(dst_root).as_posix())
    return defender_rels


def _validate_s4_audit_report(report: dict[str, Any]) -> str | None:
    """Validate that `anneal-audit --json` returned a complete passing report."""
    if report.get("replay") is not True:
        return f"anneal-audit report missing replay=true (got {report.get('replay')!r})"
    replayed = report.get("replayedDeclarations")
    if isinstance(replayed, bool) or not isinstance(replayed, int) or replayed < 1:
        return (
            "anneal-audit report missing positive integer replayedDeclarations "
            f"(got {replayed!r})"
        )
    for int_field in ("kernelDeclarations", "checkedAlternateProofs"):
        val = report.get(int_field)
        if isinstance(val, bool) or not isinstance(val, int) or val < 0:
            return (
                f"anneal-audit report missing non-negative integer {int_field} "
                f"(got {val!r})"
            )
    axioms = report.get("axioms")
    if not isinstance(axioms, list) or not all(isinstance(a, str) for a in axioms):
        return f"anneal-audit report missing string-array axioms (got {axioms!r})"
    guarantee = report.get("guarantee")
    if not isinstance(guarantee, str) or not guarantee.strip():
        return f"anneal-audit report missing non-empty guarantee (got {guarantee!r})"
    return None


def _verify_s4_tree_unchanged(
    ephemeral_anneal: Path,
    pinned: dict[str, _PinnedAssetSnapshot | str],
) -> None:
    """Verify staged Scenario 4 files (defender + submitted) and reject extras."""
    _verify_tree_hashes(ephemeral_anneal, pinned)
    actual_rels = _collect_tree_regular_files(
        ephemeral_anneal, exc_type=DefenderTamperError
    )
    extra = sorted(set(actual_rels) - set(pinned))
    if extra:
        raise DefenderTamperError(
            "defender tree gained unexpected file(s): " + ", ".join(extra[:8]),
            tampered_paths=tuple(extra),
        )


def _evaluate_theory_audit(
    *,
    tmp_root: Path,
    anneal_root: Path,
    spec: scenarios.ScenarioSpec,
    submission: LoadedSubmission,
    tools: dict[str, Path | None],
    env: dict[str, str],
    timeout: int,
    bwrap: Path | None = None,
    audit_runner: Callable[..., Any] | None = None,
    ast_tags_out: list[str] | None = None,
) -> tuple[str, dict[str, Any] | None, list[str], str]:
    """Execute Scenario 4 (`THEORY_AUDIT_HACK`) against `anneal-audit`."""
    auditor = tools.get("auditor")
    lean = tools.get("lean")
    if audit_runner is None and (auditor is None or lean is None):
        raise OracleInfrastructureError(
            "missing required `anneal-audit` or `lean` binary for Scenario 4"
        )

    ephemeral_anneal = tmp_root / "anneal"
    defender_rels: list[str] = []
    if audit_runner is None:
        defender_rels = _stage_anneal_checkout_copy(
            anneal_root, ephemeral_anneal
        )
    else:
        (ephemeral_anneal / "theory").mkdir(parents=True, exist_ok=True)

    # Snapshot pre-existing defender assets before overlaying `theory/` files,
    # then re-snapshot all staged files (including submitted `theory/` modules)
    # right before invoking `anneal-audit`.
    allowed_submission_rels = {
        rel for rel in submission.files if rel.startswith("theory/")
    }
    pre_overlay_rels = _collect_tree_regular_files(
        ephemeral_anneal, exc_type=OracleInfrastructureError
    )
    pre_pin_rels = sorted(
        (set(defender_rels) | set(pre_overlay_rels)) - allowed_submission_rels
    )
    pre_pinned = _snapshot_tree_hashes(ephemeral_anneal, pre_pin_rels)
    theory_resolved = (ephemeral_anneal / "theory").resolve()
    for rel, data in sorted(submission.files.items()):
        if not rel.startswith("theory/"):
            raise InvalidSubmissionError(
                f"s4 attacker file outside theory/: {rel}"
            )
        dest = (ephemeral_anneal / rel).resolve()
        if not dest.is_relative_to(theory_resolved):
            raise InvalidSubmissionError(
                f"s4 attacker file escapes theory/: {rel}"
            )
        try:
            dest.parent.mkdir(parents=True, exist_ok=True)
            if dest.is_symlink():
                raise InvalidSubmissionError(
                    f"s4 attacker destination is a symlink: {rel}"
                )
            if dest.is_dir():
                raise InvalidSubmissionError(
                    f"s4 attacker destination is a directory: {rel}"
                )
            fd = os.open(
                dest,
                os.O_WRONLY | os.O_CREAT | os.O_TRUNC | _NOFOLLOW_FLAG,
                0o644,
            )
            try:
                with os.fdopen(fd, "wb") as handle:
                    fd = -1
                    handle.write(data)
            finally:
                if fd >= 0:
                    os.close(fd)
        except InvalidSubmissionError:
            raise
        except OSError as exc:
            raise InvalidSubmissionError(
                f"s4 cannot stage theory path {rel}: {exc}"
            ) from exc

    _verify_tree_hashes(ephemeral_anneal, pre_pinned)
    post_overlay_rels = _collect_tree_regular_files(
        ephemeral_anneal, exc_type=OracleInfrastructureError
    )
    pinned = _snapshot_tree_hashes(
        ephemeral_anneal, sorted(set(pre_pin_rels) | set(post_overlay_rels))
    )
    s4_miri_cache = tmp_root / "s4_miri_cache"
    s4_miri_cache.mkdir(parents=True, exist_ok=True)
    cmd = [
        str(auditor or Path("anneal-audit")),
        "--anneal-root",
        str(ephemeral_anneal),
        "--json",
        "--lean",
        str(lean or Path("lean")),
        "--miri-cache-dir",
        str(s4_miri_cache),
    ]
    try:
        if audit_runner is not None:
            proc = audit_runner(
                cmd, cwd=ephemeral_anneal, env=env, timeout=timeout
            )
        else:
            assert auditor is not None and lean is not None
            audit_timeout = max(timeout, 900)
            proc = _run_auditor_in_bwrap(
                auditor_bin=auditor,
                anneal_root_host=ephemeral_anneal,
                lean_bin=lean,
                miri_cache_dir=s4_miri_cache,
                env=env,
                bwrap=bwrap,
                timeout=audit_timeout,
                require_correspondence=False,
            )
    except subprocess.TimeoutExpired:
        _verify_s4_tree_unchanged(ephemeral_anneal, pinned)
        return (
            VERDICT_HARNESS_ERROR,
            None,
            ["anneal-audit timed out"],
            "not_applicable",
        )
    except OSError as exc:
        if pinned:
            _verify_s4_tree_unchanged(ephemeral_anneal, pinned)
        raise OracleInfrastructureError(
            f"failed to execute anneal-audit: {exc}"
        ) from exc
    except Exception:
        if pinned:
            _verify_s4_tree_unchanged(ephemeral_anneal, pinned)
        raise

    _verify_s4_tree_unchanged(ephemeral_anneal, pinned)
    if proc.returncode != 0:
        if audit_runner is None:
            bwrap_path = _resolve_bwrap_binary(bwrap, required=False)
            if bwrap_path is not None and lean is not None:
                lean_sysroot = _resolve_lean_sysroot(lean, env)
                _verify_bwrap_canary(
                    bwrap_path,
                    ro_mounts=[
                        (lean_sysroot, "/opt/anneal-rt/lean"),
                        (auditor, "/opt/anneal-rt/anneal-audit"),
                    ],
                    env_vars={
                        "PATH": "/opt/anneal-rt/lean/bin:/usr/bin:/bin",
                        "HOME": "/work/tmp",
                        "TMPDIR": "/work/tmp",
                        "NO_COLOR": "1",
                    },
                    argv=["/opt/anneal-rt/lean/bin/lean", "--version"],
                    bind_dev_seeds=True,
                    ro_system_bins=True,
                    tmpfs_tmp=True,
                    disable_userns=False,
                    label="s4_anneal_audit",
                )
        full_err = (proc.stderr or proc.stdout or "").strip()
        err_snip = full_err[:1600]
        if proc.returncode == 1:
            detail = (
                f"anneal-audit rejected (exit=1): {err_snip}"
                if err_snip
                else "anneal-audit rejected (exit=1)"
            )
            return (
                VERDICT_DEFENDER_HELD,
                None,
                [detail],
                "not_applicable",
            )
        if proc.returncode == 2 and _S4_THEORY_COMPILE_RE.match(full_err):
            detail = (
                f"anneal-audit rejected (exit=2, Lean compile error): {err_snip}"
            )
            return (
                VERDICT_DEFENDER_HELD,
                None,
                [detail],
                "not_applicable",
            )
        detail = (
            f"anneal-audit operational failure (exit={proc.returncode}): "
            f"{err_snip}"
            if err_snip
            else f"anneal-audit operational failure (exit={proc.returncode})"
        )
        return (
            VERDICT_HARNESS_ERROR,
            None,
            [detail],
            "not_applicable",
        )

    audit_json: dict[str, Any] | None = None
    audit_json_err: str | None = None
    try:
        parsed = json.loads(
            proc.stdout,
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
    except (ValueError, json.JSONDecodeError) as exc:
        audit_json_err = f"anneal-audit invalid JSON: {exc}"
    else:
        if isinstance(parsed, dict):
            audit_json = parsed
            audit_json_err = _validate_s4_audit_report(parsed)
        else:
            audit_json_err = "anneal-audit output must be a JSON object"

    lean_texts = {
        p: d.decode("utf-8", errors="replace")
        for p, d in submission.files.items()
    }
    ast_parse_errs: list[str] = []
    ast_timeout = max(timeout, 90)
    try:
        disallowed = _detect_disallowed_lean_constructs_with_tools(
            lean_texts,
            allow_theory_import_all=True,
            allow_spec_options=False,
            lean_bin=lean,
            env=env,
            bwrap=bwrap,
            allow_fallback=(audit_runner is not None),
            timeout=ast_timeout,
            parse_errors_out=ast_parse_errs,
            anneal_root=anneal_root,
        )
    except subprocess.TimeoutExpired:
        msg = f"Lean AST inspector timed out on theory files after {ast_timeout}s"
        if audit_json_err is not None:
            msg = f"{msg}; {audit_json_err}"
        return (
            VERDICT_HARNESS_ERROR,
            audit_json,
            [msg],
            "not_applicable",
        )
    for rel in sorted(submission.files):
        mod_name = _validate_lean_slot_path(
            rel, "theory", allow_reserved_root=True
        )
        if mod_name != "Anneal" and not mod_name.startswith("Anneal."):
            tag = f"non_anneal_theory_root:{mod_name}"
            if tag not in disallowed:
                disallowed.append(tag)
    anomalies = dedup.extract_receipt_anomalies(audit_json)
    if disallowed or anomalies:
        if ast_tags_out is not None and disallowed:
            ast_tags_out.extend(disallowed)
        tag_desc = ", ".join(disallowed) if disallowed else ", ".join(anomalies)
        msg = (
            "anneal-audit passed despite disallowed theory constructs "
            f"({tag_desc})"
        )
        if audit_json_err is not None:
            msg = f"{msg}; {audit_json_err}"
        return (
            VERDICT_ATTACKER_WON,
            audit_json,
            [msg],
            "theory_bypass_confirmed",
        )
    if ast_parse_errs:
        msg = (
            "defender Lean AST inspector failed to parse accepted theory "
            f"files ({', '.join(ast_parse_errs)})"
        )
        if audit_json_err is not None:
            msg = f"{msg}; {audit_json_err}"
        return (
            VERDICT_HARNESS_ERROR,
            audit_json,
            [msg],
            "not_applicable",
        )
    if audit_json_err is not None:
        return (
            VERDICT_HARNESS_ERROR,
            None,
            [audit_json_err],
            "not_applicable",
        )
    return (
        VERDICT_DEFENDER_HELD,
        audit_json,
        ["anneal-audit passed on clean theory files without exploit constructs"],
        "not_applicable",
    )


_S2_REFERENCE_TARGET_RS = scenarios._HEADER_RS + """\
pub fn target(x: u32) -> u32 {
    x
}
"""

_S2_REFERENCE_TARGET_PROOF_LEAN = scenarios._HEADER_LEAN + """\
module
prelude
public import Expected
import Anneal.MirWp

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem executes_id_u32 (bits : BitVec 128)
    (hTrunc : truncateBits .i32 bits = bits) :
    Executes Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.i32, false, bits⟩] 0 Captured.body_0.locals))
      (.scalar ⟨.i32, false, bits⟩) := by
  have hInit :
      initLocalsLoop Captured.body_0 [.scalar ⟨.i32, false, bits⟩] 0
        Captured.body_0.locals =
      [.immediate none,
       .immediate (some (.scalar ⟨.i32, false, bits⟩))] := rfl
  rw [hInit]
  have hCheck : checkVal (.scalar ⟨.i32, false, bits⟩)
      (.int .i32 false) = true :=
    checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩
  have hWrite :
      writePlace
        [.immediate none,
         .immediate (some (.scalar ⟨.i32, false, bits⟩))]
        entryMemory 0 (.int .i32 false) (.scalar ⟨.i32, false, bits⟩) =
      .ok ([.immediate (some (.scalar ⟨.i32, false, bits⟩)),
            .immediate (some (.scalar ⟨.i32, false, bits⟩))],
           entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  have hStep :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i32, false, bits⟩))]) =
      .step (mkState 0 1
        [.immediate (some (.scalar ⟨.i32, false, bits⟩)),
         .immediate (some (.scalar ⟨.i32, false, bits⟩))]) := by
    change
      (match writePlace
        [.immediate none,
         .immediate (some (.scalar ⟨.i32, false, bits⟩))]
        entryMemory 0 (.int .i32 false) (.scalar ⟨.i32, false, bits⟩)
       with
       | .error k => StepResult.fault k
       | .ok (ls, mem) =>
         StepResult.step
           ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := ls }]
              callerMem := ⟨[]⟩
              mem := mem } : State)) = _
    rw [hWrite]
    rfl
  exact .next hStep (.ret rfl)

private theorem wpProg_id_u32 (bits : BitVec 128)
    (hTrunc : truncateBits .i32 bits = bits) :
    SatisfiesPost (entryProgForBody Captured.program 0)
      { args := [.scalar ⟨.i32, false, bits⟩] }
      (fun outcome =>
        outcome = .returned ⟨.scalar ⟨.i32, false, bits⟩, ⟨[]⟩⟩) ∧
    ¬ Diverges (entryProgForBody Captured.program 0)
      { args := [.scalar ⟨.i32, false, bits⟩] } := by
  have hArgs : ValidEntryArgs Captured.body_0 [.scalar ⟨.i32, false, bits⟩] := by
    unfold ValidEntryArgs
    change checkArgsMatch [.scalar ⟨.i32, false, bits⟩]
      [.int .i32 false] = true
    rw [checkArgsMatch_cons_iff]
    exact ⟨_, _, rfl, checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩, rfl⟩
  let ⟨fuel, hRuns⟩ := executes_iff_wpState.mp (executes_id_u32 bits hTrunc)
  have hWpBody :
      wpState (bodyProg Captured.body_0) fuel
        (mkState 0 0 (initLocalsLoop Captured.body_0
          [.scalar ⟨.i32, false, bits⟩] 0 Captured.body_0.locals))
        (fun outcome =>
          outcome = .returned ⟨.scalar ⟨.i32, false, bits⟩, ⟨[]⟩⟩) :=
    wpOutcomeState_of_execOutcomeState hRuns
  have hWpProg :
      wpProg (entryProgForBody Captured.program 0) fuel
        { args := [.scalar ⟨.i32, false, bits⟩] }
        (fun outcome =>
          outcome = .returned ⟨.scalar ⟨.i32, false, bits⟩, ⟨[]⟩⟩) := by
    unfold wpProg
    rw [initState_entryProgForBody rfl rfl hArgs]
    exact (wpOutcomeState_entryProg_iff rfl (isSingleFrame0_mkState 0 0 _)).mpr hWpBody
  have ⟨hSat, hNdiv, _⟩ :=
    wellFormed_and_spec_of_wp (entryProgForBody Captured.program 0)
      { args := [.scalar ⟨.i32, false, bits⟩] } fuel
      (fun outcome =>
        outcome = .returned ⟨.scalar ⟨.i32, false, bits⟩, ⟨[]⟩⟩)
      hWpProg
  exact ⟨hSat, hNdiv⟩

public theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [.int .i32 false] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v, rest, hCons, hv, hNil⟩ := valid
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons; subst hNil
      rw [checkVal_int_iff] at hv
      let ⟨bits, hvEq, hTrunc⟩ := hv
      subst hvEq
      exact executes_safe (executes_id_u32 bits hTrunc)
    | succ id => cases found
  · refine ⟨?_, 0, Captured.body_0, rfl, ?_, fun bits hTrunc => wpProg_id_u32 bits hTrunc⟩
    · intro b hb
      cases hb with
      | head => rfl
      | tail _ hTail => cases hTail
    · exact by decide

end Proof
"""


def _apply_unified_patch_strictly(
    patched_anneal: Path,
    patch_bytes: bytes,
    expected_targets: tuple[str, ...],
) -> tuple[list[str], dict[str, _PinnedAssetSnapshot]]:
    """Apply validated unified diff strictly to `Trusted/MirSemantics/*.lean`."""
    # Pin the complete pre-patch `patched_anneal` tree (all untouched files)
    # before parsing/applying the diff, then re-snapshot post-patch.
    pre_snapshot = _snapshot_full_tree_hashes(patched_anneal)
    expected_target_set = set(expected_targets)
    pinned_untouched = {
        rel: snap
        for rel, snap in pre_snapshot.items()
        if f"anneal/{rel}" not in expected_target_set
    }

    targets, _changed, file_hunks = _parse_and_validate_semantics_patch(
        patch_bytes
    )
    if targets != tuple(sorted(expected_targets)):
        raise InvalidSubmissionError(
            "patch targets mismatch validated targets"
        )

    applied: list[str] = []
    sem_dir = (patched_anneal / "trusted/lean/Trusted/MirSemantics").resolve()
    for repo_rel, hunks in file_hunks.items():
        if not repo_rel.startswith(_MIR_SEMANTICS_PATCH_PREFIX):
            raise InvalidSubmissionError(f"forbidden patch target: {repo_rel}")
        rel_in_anneal = repo_rel[len("anneal/") :]
        target_path = (patched_anneal / rel_in_anneal).resolve()
        if target_path.parent != sem_dir:
            raise InvalidSubmissionError(
                f"patch target must reside directly under MirSemantics: {repo_rel}"
            )
        raw_target = _read_regular_file_nofollow(
            target_path,
            label=repo_rel,
            exc_type=InvalidSubmissionError,
        )
        try:
            orig_text = raw_target.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise InvalidSubmissionError(
                f"target file must be UTF-8 ({repo_rel}): {exc}"
            ) from exc
        orig_lines = orig_text.splitlines(keepends=True)
        out_lines: list[str] = []
        cursor = 0
        for o_start, o_count, _n_start, _n_count, hunk_body in hunks:
            if o_count == 0:
                zero_based = o_start
            else:
                if o_start < 1:
                    raise InvalidSubmissionError(
                        f"patch hunk offset out of range in {repo_rel}"
                    )
                zero_based = o_start - 1
            if zero_based < cursor or zero_based + o_count > len(orig_lines):
                raise InvalidSubmissionError(
                    f"patch hunk offset out of range in {repo_rel}"
                )
            out_lines.extend(orig_lines[cursor:zero_based])
            pos = zero_based
            for h_idx, hline in enumerate(hunk_body):
                no_nl_next = (
                    h_idx + 1 < len(hunk_body)
                    and hunk_body[h_idx + 1].rstrip("\n") == _NO_NEWLINE_MARKER
                )
                logical = (
                    hline[:-1]
                    if (no_nl_next and hline.endswith("\n"))
                    else hline
                )
                if logical.rstrip("\n") == _NO_NEWLINE_MARKER:
                    continue
                if logical.startswith(" "):
                    expected_line = logical[1:]
                    if pos >= len(orig_lines) or orig_lines[pos] != expected_line:
                        raise InvalidSubmissionError(
                            f"patch context mismatch in {repo_rel} at line {pos + 1}"
                        )
                    out_lines.append(orig_lines[pos])
                    pos += 1
                elif logical.startswith("-"):
                    expected_line = logical[1:]
                    if pos >= len(orig_lines) or orig_lines[pos] != expected_line:
                        raise InvalidSubmissionError(
                            f"patch delete mismatch in {repo_rel} at line {pos + 1}"
                        )
                    pos += 1
                elif logical.startswith("+"):
                    out_lines.append(logical[1:])
            cursor = pos
        out_lines.extend(orig_lines[cursor:])
        anneal_ci_lib.atomic_write_text(
            target_path, "".join(out_lines), exc_type=OracleInfrastructureError
        )
        applied.append(repo_rel)

    try:
        _verify_tree_hashes(patched_anneal, pinned_untouched)
        actual_rels = set(
            _collect_tree_regular_files(patched_anneal, exc_type=DefenderTamperError)
        )
        if actual_rels != set(pre_snapshot):
            diff_paths = sorted(
                (actual_rels - set(pre_snapshot)) | (set(pre_snapshot) - actual_rels)
            )
            raise DefenderTamperError(
                "patched_anneal file set changed unexpectedly: "
                + ", ".join(diff_paths[:8]),
                tampered_paths=tuple(diff_paths),
            )
    except DefenderTamperError as exc:
        raise InvalidSubmissionError(
            f"semantics.patch attempted out-of-scope mutation: {exc}"
        ) from exc
    return applied, _snapshot_full_tree_hashes(patched_anneal)


def _drain_stream_bounded(
    stream: Any,
    limit: int,
    bucket: list[bytes],
    meta: dict[str, Any] | None = None,
) -> None:
    """Drain `stream` cleanly while capping RAM retention and hashing full bytes."""
    kept = 0
    total = 0
    truncated = False
    hasher = hashlib.sha256()
    try:
        while True:
            chunk = stream.read(65_536)
            if not chunk:
                break
            total += len(chunk)
            hasher.update(chunk)
            if kept < limit:
                take = chunk[: limit - kept]
                bucket.append(take)
                kept += len(take)
                if len(take) < len(chunk):
                    truncated = True
            else:
                truncated = True
    finally:
        if meta is not None:
            meta["sha256"] = hasher.hexdigest()
            meta["bytes"] = total
            meta["truncated"] = truncated
        try:
            stream.close()
        except OSError:
            pass


def _clamped_rlimit_specs(timeout: int) -> list[tuple[int, str, int]]:
    """Compute clamped `(res_id, prlimit_flag, value)` resource limits."""
    cpu_cap = max(int(timeout) * 4, 300)
    desired: tuple[tuple[int, str, int], ...] = (
        (resource.RLIMIT_CORE, "--core", 0),
        (resource.RLIMIT_FSIZE, "--fsize", 512 * 1024 * 1024),
        (resource.RLIMIT_NOFILE, "--nofile", 2048),
        (resource.RLIMIT_AS, "--as", 16 * 1024 * 1024 * 1024),
        (resource.RLIMIT_CPU, "--cpu", cpu_cap),
    )
    out: list[tuple[int, str, int]] = []
    for res_id, flag, cap in desired:
        try:
            _soft, hard = resource.getrlimit(res_id)
        except (OSError, ValueError):
            continue
        val = cap if hard == resource.RLIM_INFINITY else min(cap, hard)
        out.append((res_id, flag, val))
    return out


def _prlimit_prefix(
    timeout: int,
    *,
    prlimit: Path | None = None,
) -> list[str]:
    """Build clamped `prlimit` command prefix after validating host `prlimit`."""
    explicit = prlimit if prlimit is not None else _EXPLICIT_PRLIMIT_VAR.get()
    prlimit_path = _resolve_system_binary("prlimit", explicit, required=False)
    if prlimit_path is None:
        return []
    args = [str(prlimit_path)]
    for _res_id, flag, val in _clamped_rlimit_specs(timeout):
        args.append(f"{flag}={val}:{val}")
    args.append("--")
    return args


def _setrlimit_preexec_fn(
    limits: list[tuple[int, str, int]],
) -> Callable[[], None]:
    """Return a child `preexec_fn` applying clamped `resource.setrlimit` caps."""

    def _apply() -> None:
        for res_id, _flag, val in limits:
            try:
                resource.setrlimit(res_id, (val, val))
            except (OSError, ValueError):
                pass

    return _apply


def _run_bounded_subprocess(
    cmd: list[str],
    *,
    timeout: int,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    stdin_data: bytes | None = None,
    max_output_bytes: int = _MAX_CAPTURE_BYTES,
    apply_prlimit: bool = True,
    prlimit: Path | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run `cmd` in its own session with bounded output capture and killpg cleanup."""
    preexec_fn: Callable[[], None] | None = None
    if apply_prlimit:
        prefix = _prlimit_prefix(timeout, prlimit=prlimit)
        if prefix:
            wrapped_cmd = [*prefix, *cmd]
        else:
            wrapped_cmd = list(cmd)
            preexec_fn = _setrlimit_preexec_fn(_clamped_rlimit_specs(timeout))
    else:
        wrapped_cmd = list(cmd)
    proc = subprocess.Popen(
        wrapped_cmd,
        cwd=cwd,
        env=env,
        stdin=subprocess.PIPE if stdin_data is not None else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
        preexec_fn=preexec_fn,
    )
    if stdin_data is not None and proc.stdin is not None:
        try:
            proc.stdin.write(stdin_data)
            proc.stdin.flush()
        except BrokenPipeError:
            pass
        finally:
            try:
                proc.stdin.close()
            except OSError:
                pass
    out_chunks: list[bytes] = []
    err_chunks: list[bytes] = []
    out_meta: dict[str, Any] = {}
    err_meta: dict[str, Any] = {}
    assert proc.stdout is not None and proc.stderr is not None
    t_out = threading.Thread(
        target=_drain_stream_bounded,
        args=(proc.stdout, max_output_bytes, out_chunks, out_meta),
        daemon=True,
    )
    t_err = threading.Thread(
        target=_drain_stream_bounded,
        args=(proc.stderr, max_output_bytes, err_chunks, err_meta),
        daemon=True,
    )
    t_out.start()
    t_err.start()
    try:
        rc = proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass
        t_out.join(timeout=2)
        t_err.join(timeout=2)
        raise
    t_out.join(timeout=5)
    t_err.join(timeout=5)
    if t_out.is_alive() or t_err.is_alive():
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        t_out.join(timeout=2)
        t_err.join(timeout=2)
        raise OracleInfrastructureError(
            "subprocess exited while background descendant kept output pipes open"
        )
    res: Any = subprocess.CompletedProcess(
        cmd,
        rc,
        stdout=b"".join(out_chunks).decode("utf-8", errors="replace"),
        stderr=b"".join(err_chunks).decode("utf-8", errors="replace"),
    )
    res.stdout_truncated = bool(out_meta.get("truncated", False))
    res.stderr_truncated = bool(err_meta.get("truncated", False))
    res.stdout_sha256 = out_meta.get("sha256")
    res.stderr_sha256 = err_meta.get("sha256")
    res.stdout_bytes = out_meta.get("bytes")
    res.stderr_bytes = err_meta.get("bytes")
    return res


def _run_cmd_in_bwrap(
    *,
    bwrap: Path,
    ro_mounts: list[tuple[Path, str]],
    rw_mounts: list[tuple[Path, str]],
    env_vars: dict[str, str],
    cwd_in_sandbox: str,
    argv: list[str],
    timeout: int,
    stdin_data: bytes | None = None,
    bind_dev_seeds: bool = False,
    ro_system_bins: bool = False,
    tmpfs_tmp: bool = False,
    disable_userns: bool = True,
    tmpfs_bytes: int = _DEFAULT_TMPFS_BYTES,
    max_output_bytes: int = _MAX_CAPTURE_BYTES,
) -> subprocess.CompletedProcess[str]:
    """Run an arbitrary command strictly inside ephemeral `bwrap` (`ExecSeal`)."""
    with tempfile.TemporaryDirectory(prefix="anneal-bwrap-dev-") as dev_tmp:
        cmd: list[str] = [
            str(bwrap),
            "--unshare-all",
            "--unshare-user",
        ]
        if disable_userns:
            cmd.append("--disable-userns")
        cmd.extend(
            [
                "--as-pid-1",
                "--cap-drop",
                "ALL",
                "--die-with-parent",
                "--new-session",
                "--clearenv",
                "--size",
                str(16 * 1024 * 1024),
                "--tmpfs",
                "/",
                "--size",
                str(1024 * 1024),
                "--tmpfs",
                "/dev",
                "--dev-bind",
                "/dev/null",
                "/dev/null",
            ]
        )
        if bind_dev_seeds:
            seed_len = 64 * 1024
            dev_dir = Path(dev_tmp)
            dev_dir.chmod(0o700)
            zero_path = dev_dir / "zero"
            zero_path.write_bytes(b"\x00" * seed_len)
            zero_path.chmod(0o400)
            urandom_path = dev_dir / "urandom"
            urandom_path.write_bytes(os.urandom(seed_len))
            urandom_path.chmod(0o400)
            cmd.extend(["--ro-bind", str(zero_path), "/dev/zero"])
            cmd.extend(["--ro-bind", str(urandom_path), "/dev/urandom"])
        cmd.extend(
            [
                "--proc",
                "/proc",
                "--size",
                str(tmpfs_bytes),
                "--tmpfs",
                "/work/tmp",
            ]
        )
        if tmpfs_tmp:
            cmd.extend(["--size", str(tmpfs_bytes), "--tmpfs", "/tmp"])
        for key, val in sorted(env_vars.items()):
            cmd.extend(["--setenv", key, val])
        cmd.extend(["--chdir", cwd_in_sandbox])

        sys_dirs = [
            "/lib",
            "/lib64",
            "/usr/lib",
            "/usr/lib64",
            "/etc/ld.so.cache",
            "/etc/ld.so.conf",
            "/etc/ld.so.conf.d",
        ]
        if ro_system_bins:
            sys_dirs.extend(
                ["/bin", "/usr/bin", "/usr/libexec", "/etc/alternatives", "/nix/store"]
            )
        for sys_dir in sys_dirs:
            if Path(sys_dir).exists():
                cmd.extend(["--ro-bind-try", sys_dir, sys_dir])
        for host_p, box_p in ro_mounts:
            cmd.extend(["--ro-bind", str(host_p), box_p])
        for host_p, box_p in rw_mounts:
            cmd.extend(["--bind", str(host_p), box_p])
        cmd.extend(["--", *argv])
        return _run_bounded_subprocess(
            cmd,
            timeout=timeout,
            stdin_data=stdin_data,
            max_output_bytes=max_output_bytes,
        )


def _resolve_lean_sysroot(lean_bin: Path, env: dict[str, str]) -> Path:
    """Resolve and validate the host Lean toolchain sysroot directory."""
    try:
        prefix_out = subprocess.check_output(
            [str(lean_bin), "--print-prefix"],
            env=env,
            text=True,
            timeout=15,
        ).strip()
    except (OSError, subprocess.SubprocessError) as exc:
        raise OracleInfrastructureError(
            f"failed to query `lean --print-prefix`: {exc}"
        ) from exc
    lean_sysroot = Path(prefix_out)
    if not prefix_out or not lean_sysroot.is_dir():
        raise OracleInfrastructureError(
            f"invalid `lean --print-prefix` directory: {prefix_out!r}"
        )
    return lean_sysroot


def _run_auditor_in_bwrap(
    *,
    auditor_bin: Path,
    anneal_root_host: Path,
    lean_bin: Path,
    miri_cache_dir: Path,
    env: dict[str, str],
    bwrap: Path | None = None,
    timeout: int,
    require_correspondence: bool,
) -> subprocess.CompletedProcess[str]:
    """Execute `anneal-audit` strictly confined inside `bwrap` (`Pass 1 + Pass 2`)."""
    bwrap_path = _resolve_bwrap_binary(bwrap, required=True)
    assert bwrap_path is not None
    lean_sysroot = _resolve_lean_sysroot(lean_bin, env)
    miri_cache_dir.mkdir(parents=True, exist_ok=True)
    # Outer `bwrap` confines `anneal-audit` + Pass 1 `lean` while permitting
    # Pass 2 (`run_correspondence`) to launch its own `--disable-userns` `bwrap`
    # with toolchain/cache paths outside reserved `/toolchain`/`/work` roots.
    argv = [
        "/opt/anneal-rt/anneal-audit",
        "--anneal-root",
        "/opt/anneal-rt/repo",
        "--json",
        "--lean",
        "/opt/anneal-rt/lean/bin/lean",
        "--miri-cache-dir",
        "/opt/anneal-rt/miri_cache",
    ]
    if require_correspondence:
        argv.append("--require-correspondence")
    return _run_cmd_in_bwrap(
        bwrap=bwrap_path,
        ro_mounts=[
            (lean_sysroot, "/opt/anneal-rt/lean"),
            (auditor_bin, "/opt/anneal-rt/anneal-audit"),
            (anneal_root_host, "/opt/anneal-rt/repo"),
        ],
        rw_mounts=[(miri_cache_dir, "/opt/anneal-rt/miri_cache")],
        env_vars={
            "PATH": "/opt/anneal-rt/lean/bin:/usr/bin:/bin",
            "HOME": "/work/tmp",
            "TMPDIR": "/work/tmp",
            "NO_COLOR": "1",
        },
        cwd_in_sandbox="/work/tmp",
        argv=argv,
        timeout=timeout,
        bind_dev_seeds=True,
        ro_system_bins=True,
        tmpfs_tmp=True,
        disable_userns=False,
        tmpfs_bytes=_AUDIT_TMPFS_BYTES,
    )


def _run_lean_in_bwrap(
    *,
    bwrap: Path,
    lean_bin: Path,
    lean_sysroot: Path,
    ro_mounts: list[tuple[Path, str]],
    rw_mounts: list[tuple[Path, str]],
    lean_path_mounts: list[str],
    cwd_in_sandbox: str,
    lean_args: list[str],
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    return _run_cmd_in_bwrap(
        bwrap=bwrap,
        ro_mounts=[
            (lean_sysroot / "lib", "/toolchain/lib"),
            (lean_bin, "/toolchain/bin/lean"),
            *ro_mounts,
        ],
        rw_mounts=rw_mounts,
        env_vars={
            "PATH": "/usr/bin:/bin",
            "HOME": "/work/tmp",
            "TMPDIR": "/work/tmp",
            "LEAN_PATH": ":".join(lean_path_mounts),
        },
        cwd_in_sandbox=cwd_in_sandbox,
        argv=["/toolchain/bin/lean", *lean_args],
        timeout=timeout,
        bind_dev_seeds=True,
    )


def _discover_module_artifacts(
    roots: dict[str, Path],
) -> dict[str, list[list[str]]]:
    """Collect `[olean_parts, ir_parts]` per module from compiled output dirs."""
    out: dict[str, list[list[str]]] = {}
    for mod, base_no_ext in roots.items():
        olean_parts: list[str] = []
        for ext in (".olean", ".olean.server", ".olean.private"):
            p = Path(f"{base_no_ext}{ext}")
            if p.is_file():
                olean_parts.append(str(p))
        ir_parts: list[str] = []
        for ext in (".ir.sig", ".ir"):
            p = Path(f"{base_no_ext}{ext}")
            if p.is_file():
                ir_parts.append(str(p))
        if not olean_parts:
            raise OracleInfrastructureError(
                f"missing compiled .olean for module {mod}: {base_no_ext}.olean"
            )
        out[mod] = [olean_parts, ir_parts]
    return out


# Matches `anneal-audit` exit-2 failures emitted specifically by Lean compiler
# rejections of attacker-controlled `Anneal.*` `theory/` modules (distinct from
# infrastructure panics, signal kills, `compile-Trusted.*`, or bwrap failures).
_S4_THEORY_COMPILE_RE = re.compile(
    r"^Trusted check failed \(compile-Anneal(?:\.[^):]+)?\): "
    r"Lean exited Some\(1\):"
)

_LEAN_IMPORT_RE = re.compile(
    r"^\s*(?:public\s+|private\s+|meta\s+|all\s+)*"
    r"import\s+(?:all\s+)?([A-Za-z0-9_.]+)"
)


def _discover_lean_closure(
    src_root: Path,
    roots: tuple[str, ...],
) -> tuple[list[str], dict[str, Path]]:
    """Return `(topo_order, mod_to_path)` for `roots` under `src_root`."""
    mod_map: dict[str, Path] = {}
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def _visit(mod: str) -> None:
        if mod in visited or mod in visiting:
            return
        cand = src_root / f"{mod.replace('.', '/')}.lean"
        if not cand.is_file():
            return
        visiting.add(mod)
        for line in cand.read_text(encoding="utf-8").splitlines():
            match = _LEAN_IMPORT_RE.match(line)
            if match:
                _visit(match.group(1))
        visiting.remove(mod)
        visited.add(mod)
        mod_map[mod] = cand
        order.append(mod)

    for root_mod in roots:
        _visit(root_mod)
    return order, mod_map


def _topo_sort_lean_modules(mod_map: dict[str, Path]) -> list[str]:
    """Return `mod_map` keys in bottom-up import dependency order."""
    dep_map: dict[str, list[str]] = {}
    for mod, path_m in mod_map.items():
        deps: list[str] = []
        for line in path_m.read_text(encoding="utf-8").splitlines():
            match = _LEAN_IMPORT_RE.match(line)
            if match and match.group(1) in mod_map:
                deps.append(match.group(1))
        dep_map[mod] = deps
    order: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def _visit(mod: str) -> None:
        if mod in visited or mod in visiting:
            return
        visiting.add(mod)
        for dep in dep_map.get(mod, ()):
            _visit(dep)
        visiting.remove(mod)
        visited.add(mod)
        order.append(mod)

    for mod in sorted(mod_map):
        _visit(mod)
    return order


def _compile_lean_modules_in_bwrap(
    *,
    bwrap: Path,
    lean_bin: Path,
    lean_sysroot: Path,
    modules: list[str],
    src_host: Path,
    src_box: str,
    out_host: Path,
    out_box: str,
    extra_ro_mounts: list[tuple[Path, str]],
    lean_path_mounts: list[str],
    timeout: int,
) -> tuple[bool, str]:
    """Compile `modules` sequentially inside sandboxed `bwrap`."""
    for mod in modules:
        rel_lean = f"{mod.replace('.', '/')}.lean"
        rel_olean = f"{mod.replace('.', '/')}.olean"
        (out_host / rel_olean).parent.mkdir(parents=True, exist_ok=True)
        try:
            proc = _run_lean_in_bwrap(
                bwrap=bwrap,
                lean_bin=lean_bin,
                lean_sysroot=lean_sysroot,
                ro_mounts=[*extra_ro_mounts, (src_host, src_box)],
                rw_mounts=[(out_host, out_box)],
                lean_path_mounts=lean_path_mounts,
                cwd_in_sandbox="/work",
                lean_args=[
                    "-j1",
                    "-M4096",
                    "-t0",
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-DwarningAsError=true",
                    "-R",
                    src_box,
                    "-o",
                    f"{out_box}/{rel_olean}",
                    f"{src_box}/{rel_lean}",
                ],
                timeout=timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise OracleInfrastructureError(
                f"Lean compilation of {mod} timed out after {timeout}s"
            ) from exc
        if proc.returncode != 0:
            err = (proc.stderr or proc.stdout).strip()[:800]
            return False, f"module {mod} failed compile: {err}"
    return True, ""


def _extract_trust_tiers(trusted_dir: Path) -> list[tuple[str, str, Path]]:
    """Return `(module_name, tier_wire, path)` for `Trusted.lean` and `Trusted/**/*.lean`."""
    entries: list[tuple[str, str, Path]] = []
    umbrella = trusted_dir.parent / "Trusted.lean"
    paths = ([umbrella] if umbrella.is_file() else []) + sorted(
        trusted_dir.rglob("*.lean")
    )
    for p in paths:
        rel = p.relative_to(trusted_dir.parent).as_posix()
        mod = rel[:-len(".lean")].replace("/", ".")
        tier: str | None = None
        for raw_line in p.read_text(encoding="utf-8").splitlines():
            stripped = raw_line.strip()
            if stripped.startswith("-- anneal-trust-tier:"):
                tier = stripped.split(":", 1)[1].strip()
                break
        if tier is None:
            raise OracleInfrastructureError(
                f"missing -- anneal-trust-tier directive in {rel}"
            )
        entries.append((mod, tier, p))
    return entries


_CAPTURE_SHARD_FILE_RE = re.compile(r"^Shard_(\d{3,})\.lean$")


def _discover_e1_capture_shards(
    capture_dir: Path,
    *,
    max_total_bytes: int = MAX_E1_CAPTURE_TOTAL_BYTES,
) -> list[tuple[str, str, bytes]]:
    """Read and validate unpatched `Captured/Shard_*.lean` modules for Tier-E1."""
    shards_manifest_path = capture_dir / "capture_shards.json"
    expected_shards: dict[str, tuple[int, str]] | None = None
    if shards_manifest_path.exists() or shards_manifest_path.is_symlink():
        shards_bytes = _read_regular_file_nofollow(
            shards_manifest_path,
            max_bytes=MAX_E1_CAPTURE_FILE_BYTES,
            label="capture_shards.json for Tier-E1 binding",
            exc_type=OracleInfrastructureError,
        )
        try:
            manifest_obj = json.loads(
                shards_bytes.decode("utf-8"),
                object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
            )
        except (ValueError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise OracleInfrastructureError(
                f"invalid capture_shards.json: {exc}"
            ) from exc
        if not isinstance(manifest_obj, dict) or not isinstance(
            manifest_obj.get("shards"), list
        ):
            raise OracleInfrastructureError(
                "capture_shards.json must be a JSON object with a shards list"
            )
        if len(manifest_obj["shards"]) > MAX_E1_CAPTURE_SHARDS:
            raise OracleInfrastructureError(
                f"capture_shards.json exceeds {MAX_E1_CAPTURE_SHARDS} shards"
            )
        expected_shards = {}
        for entry in manifest_obj["shards"]:
            if not isinstance(entry, dict):
                raise OracleInfrastructureError(
                    "capture_shards.json entry must be an object"
                )
            idx = entry.get("shard_idx")
            mod = entry.get("capture_module")
            digest = entry.get("capture_sha256")
            if (
                not isinstance(idx, int)
                or isinstance(idx, bool)
                or idx < 0
                or mod != f"Captured.Shard_{idx:03}"
                or not isinstance(digest, str)
                or not re.fullmatch(r"[0-9a-fA-F]{64}", digest)
            ):
                raise OracleInfrastructureError(
                    f"malformed shard entry in capture_shards.json: {entry!r}"
                )
            if mod in expected_shards:
                raise OracleInfrastructureError(
                    f"duplicate shard module in capture_shards.json: {mod}"
                )
            expected_shards[mod] = (idx, digest.lower())

    shards_dir = capture_dir / "Captured"
    if shards_dir.is_symlink():
        raise OracleInfrastructureError(
            "symlinked capture/Captured directory disallowed"
        )
    found: list[tuple[int, str, str, bytes]] = []
    cumulative_bytes = 0
    if shards_dir.exists():
        if not shards_dir.is_dir():
            raise OracleInfrastructureError(
                "capture/Captured must be a regular directory"
            )
        items = sorted(shards_dir.iterdir(), key=lambda p: p.name)
        if len(items) > MAX_E1_CAPTURE_SHARDS:
            raise OracleInfrastructureError(
                f"capture/Captured exceeds {MAX_E1_CAPTURE_SHARDS} shard files"
            )
        for item in items:
            st = os.lstat(item)
            if stat.S_ISLNK(st.st_mode) or not stat.S_ISREG(st.st_mode):
                raise OracleInfrastructureError(
                    f"non-regular file in capture/Captured disallowed: {item.name}"
                )
            match = _CAPTURE_SHARD_FILE_RE.match(item.name)
            if not match:
                raise OracleInfrastructureError(
                    f"unexpected file in capture/Captured: {item.name}"
                )
            idx = int(match.group(1))
            mod = f"Captured.{item.stem}"
            remaining = max(0, max_total_bytes - cumulative_bytes)
            per_file_cap = min(MAX_E1_CAPTURE_FILE_BYTES, remaining)
            data = _read_regular_file_nofollow(
                item,
                max_bytes=per_file_cap,
                label=f"unpatched {mod} for Tier-E1 binding",
                exc_type=OracleInfrastructureError,
            )
            cumulative_bytes += len(data)
            if expected_shards is not None:
                if mod not in expected_shards:
                    raise OracleInfrastructureError(
                        f"unexpected shard file {mod} absent from capture_shards.json"
                    )
                if _sha256_bytes(data).lower() != expected_shards[mod][1]:
                    raise OracleInfrastructureError(
                        f"capture shard digest mismatch for {mod}"
                    )
            found.append((idx, mod, f"Captured/{item.name}", data))
    if expected_shards is not None and {m for _, m, _, _ in found} != set(
        expected_shards
    ):
        raise OracleInfrastructureError(
            "missing capture shard module(s) listed in capture_shards.json"
        )
    found.sort(key=lambda row: (row[0], row[1]))
    return [(mod, rel, data) for _, mod, rel, data in found]


def _evaluate_s2_lean_patch_proof(
    *,
    tmp_root: Path,
    anneal_root: Path,
    spec: scenarios.ScenarioSpec,
    submission: LoadedSubmission,
    artifacts_dir: Path,
    tools: dict[str, Path | None],
    env: dict[str, str],
    timeout: int,
    bwrap: Path | None = None,
    e1_runner: Callable[..., E1VerificationResult] | None = None,
) -> E1VerificationResult:
    """Evaluate Tier-E1 `semantics.patch` + `incorrectness/Proof.lean` against S2."""
    if e1_runner is not None:
        return e1_runner(
            tmp_root=tmp_root,
            anneal_root=anneal_root,
            spec=spec,
            submission=submission,
            artifacts_dir=artifacts_dir,
            tools=tools,
            env=env,
            timeout=timeout,
        )

    lean_bin = tools.get("lean")
    capture = tools.get("capture")
    sysroot = tools.get("sysroot")
    bwrap_path = _resolve_bwrap_binary(bwrap, required=True)
    if lean_bin is None or capture is None or sysroot is None or bwrap_path is None:
        raise OracleInfrastructureError(
            "Tier-E1 evaluation requires lean, anneal-rustc-capture, sysroot, and bwrap"
        )

    capture_dir = artifacts_dir / "capture"
    unpatched_captured = capture_dir / "Captured.lean"
    captured_bytes = _read_regular_file_nofollow(
        unpatched_captured,
        max_bytes=MAX_E1_CAPTURE_FILE_BYTES,
        label="unpatched Captured.lean for Tier-E1 binding",
        exc_type=OracleInfrastructureError,
    )
    shard_budget = max(0, MAX_E1_CAPTURE_TOTAL_BYTES - len(captured_bytes))
    shard_entries = _discover_e1_capture_shards(
        capture_dir, max_total_bytes=shard_budget
    )
    shard_mods = [mod for mod, _rel, _data in shard_entries]

    # Stage isolated patched copy of `anneal/` (never mutating caller checkout).
    patched_anneal = tmp_root / "patched_anneal"
    _stage_anneal_checkout_copy(anneal_root, patched_anneal)

    patch_bytes = submission.files["incorrectness/semantics.patch"]
    try:
        _applied, pinned_post_patch = _apply_unified_patch_strictly(
            patched_anneal, patch_bytes, submission.e1_patch_targets
        )
    except InvalidSubmissionError as exc:
        return E1VerificationResult(
            passed=False,
            preservation_passed=False,
            reference_target_verified=False,
            theory_canaries_verified=False,
            patch_audit=None,
            detail=f"Tier-E1 patch application rejected: {exc}",
        )

    pinned_defender_trees: list[tuple[Path, dict[str, _PinnedAssetSnapshot]]] = [
        (patched_anneal, pinned_post_patch)
    ]

    def _pin_defender_tree(tree_root: Path) -> None:
        pinned_defender_trees.append(
            (tree_root, _snapshot_full_tree_hashes(tree_root))
        )

    def _verify_all_pinned_defender_trees() -> None:
        for tree_root, tree_snap in pinned_defender_trees:
            _verify_full_tree_unchanged(tree_root, tree_snap)

    try:
        return _evaluate_s2_lean_patch_proof_staged(
            tmp_root=tmp_root,
            patched_anneal=patched_anneal,
            spec=spec,
            submission=submission,
            captured_bytes=captured_bytes,
            shard_entries=shard_entries,
            shard_mods=shard_mods,
            lean_bin=lean_bin,
            capture=capture,
            sysroot=sysroot,
            bwrap=bwrap_path,
            env=env,
            timeout=timeout,
            pin_tree=_pin_defender_tree,
            verify_pinned=_verify_all_pinned_defender_trees,
        )
    finally:
        _verify_all_pinned_defender_trees()


def _escape_toml_basic_string(raw: str) -> str:
    return (
        raw.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
    )


_CRATES_IO_SOURCE = "registry+https://github.com/rust-lang/crates.io-index"
_CRATE_TOKEN_RE = re.compile(r"^[A-Za-z0-9_.+-]+$")


def _parse_e1_lock_packages(lockfile: Path | None) -> list[tuple[str, str, str]]:
    """Return `(name, version, sha256)` for third-party crates in `Cargo.lock`."""
    if lockfile is None:
        return []
    raw = _read_regular_file_nofollow(
        lockfile,
        max_bytes=_MAX_CAPTURE_BYTES,
        label="Tier-E1 Cargo.lock",
        exc_type=OracleInfrastructureError,
    )
    try:
        parsed = tomllib.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise OracleInfrastructureError(
            f"invalid Tier-E1 Cargo.lock: {exc}"
        ) from exc
    pkgs = parsed.get("package", [])
    if not isinstance(pkgs, list):
        raise OracleInfrastructureError("Tier-E1 Cargo.lock `package` must be a list")
    out: list[tuple[str, str, str]] = []
    seen: set[tuple[str, str]] = set()
    for pkg in pkgs:
        if not isinstance(pkg, dict) or "source" not in pkg:
            continue
        source = pkg.get("source")
        name = pkg.get("name")
        version = pkg.get("version")
        checksum = pkg.get("checksum")
        if source != _CRATES_IO_SOURCE:
            raise OracleInfrastructureError(
                f"unsupported external Cargo dependency source in Tier-E1: {source!r}"
            )
        if (
            not isinstance(name, str)
            or not _CRATE_TOKEN_RE.fullmatch(name)
            or ".." in name
            or not isinstance(version, str)
            or not _CRATE_TOKEN_RE.fullmatch(version)
            or ".." in version
        ):
            raise OracleInfrastructureError(
                f"invalid Cargo.lock crate coordinates: {name!r} {version!r}"
            )
        if not isinstance(checksum, str) or not re.fullmatch(
            r"[0-9a-fA-F]{64}", checksum
        ):
            raise OracleInfrastructureError(
                f"missing or invalid checksum in Cargo.lock for {name}-{version}"
            )
        key = (name, version)
        if key in seen:
            raise OracleInfrastructureError(
                f"duplicate Cargo.lock package entry: {name}-{version}"
            )
        seen.add(key)
        out.append((name, version, checksum.lower()))
    return out


def _find_verified_crate_archive(
    cache_root: Path,
    *,
    name: str,
    version: str,
    expected_sha: str,
) -> bytes | None:
    """Locate and SHA-256-verify `<name>-<version>.crate` under `registry/cache`."""
    if not cache_root.is_dir() or cache_root.is_symlink():
        return None
    target_name = f"{name}-{version}.crate"
    for index_dir in sorted(cache_root.iterdir(), key=lambda p: p.name):
        if index_dir.is_symlink() or not index_dir.is_dir():
            continue
        cand = index_dir / target_name
        if not cand.exists() and not cand.is_symlink():
            continue
        data = _read_regular_file_nofollow(
            cand,
            max_bytes=MAX_CRATE_ARCHIVE_BYTES,
            label=f"cached crate {target_name}",
            exc_type=OracleInfrastructureError,
        )
        actual_sha = _sha256_bytes(data).lower()
        if actual_sha != expected_sha:
            raise OracleInfrastructureError(
                f"Tier-E1 cached crate checksum mismatch for {name}-{version}: "
                f"expected {expected_sha}, got {actual_sha}"
            )
        return data
    return None


def _extract_verified_crate_tarball(
    crate_bytes: bytes,
    *,
    dest_dir: Path,
    name: str,
    version: str,
    expected_sha: str,
) -> None:
    """Safely unpack verified `.crate` tarball into `dest_dir` + checksum file."""
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest_resolved = dest_dir.resolve()
    root_name = f"{name}-{version}"
    prefix = f"{root_name}/"
    files_map: dict[str, str] = {}
    unpacked_bytes = 0
    try:
        with tarfile.open(fileobj=io.BytesIO(crate_bytes), mode="r:gz") as tf:
            for member in tf.getmembers():
                if not (member.isdir() or member.isreg()):
                    raise OracleInfrastructureError(
                        f"unsafe non-regular tar member in {root_name}.crate: {member.name}"
                    )
                raw_name = member.name.rstrip("/") if member.isdir() else member.name
                if raw_name == root_name and member.isdir():
                    continue
                if not member.name.startswith(prefix):
                    raise OracleInfrastructureError(
                        f"unexpected path outside prefix in {root_name}.crate: {member.name}"
                    )
                rel_raw = member.name[len(prefix) :].rstrip("/")
                if not rel_raw:
                    continue
                try:
                    rel = _validate_rel_posix(rel_raw)
                except InvalidSubmissionError as exc:
                    raise OracleInfrastructureError(
                        f"unsafe path in {root_name}.crate: {exc}"
                    ) from exc
                target = (dest_dir / rel).resolve()
                if not target.is_relative_to(dest_resolved) or target == dest_resolved:
                    raise OracleInfrastructureError(
                        f"extracted path escapes {root_name}: {rel}"
                    )
                if member.isdir():
                    target.mkdir(parents=True, exist_ok=True)
                    continue
                unpacked_bytes += max(member.size, 0)
                if unpacked_bytes > MAX_CRATE_ARCHIVE_BYTES:
                    raise OracleInfrastructureError(
                        f"unpacked crate exceeds byte cap: {root_name}"
                    )
                fobj = tf.extractfile(member)
                if fobj is None:
                    raise OracleInfrastructureError(
                        f"cannot extract member {rel} from {root_name}.crate"
                    )
                fbytes = fobj.read(MAX_CRATE_ARCHIVE_BYTES + 1)
                if len(fbytes) > MAX_CRATE_ARCHIVE_BYTES:
                    raise OracleInfrastructureError(
                        f"crate member exceeds byte cap: {root_name}/{rel}"
                    )
                _write_new_regular_file_excl(target, fbytes)
                os.chmod(target, 0o755 if (member.mode & 0o111) else 0o644)
                files_map[rel] = _sha256_bytes(fbytes)
    except (tarfile.TarError, EOFError, zlib.error, gzip.BadGzipFile) as exc:
        raise OracleInfrastructureError(
            f"corrupt Tier-E1 crate archive {root_name}.crate: {exc}"
        ) from exc
    _write_new_regular_file_excl(
        dest_dir / ".cargo-checksum.json",
        json.dumps({"package": expected_sha, "files": files_map}, sort_keys=True).encode(
            "utf-8"
        ),
    )


def _discover_host_vendor_dirs(host_cargo_home: Path) -> list[Path]:
    """Read validated local `[source.*.directory]` paths from host Cargo config."""
    dirs: list[Path] = []
    for cfg_name in ("config.toml", "config"):
        cfg_path = host_cargo_home / cfg_name
        if cfg_path.is_symlink() or not cfg_path.is_file():
            continue
        raw = _read_regular_file_nofollow(
            cfg_path,
            max_bytes=_MAX_CAPTURE_BYTES,
            label=f"host {cfg_name}",
            exc_type=OracleInfrastructureError,
        )
        parsed = tomllib.loads(raw.decode("utf-8"))
        src_tbl = parsed.get("source")
        if not isinstance(src_tbl, dict):
            break
        for sec_body in src_tbl.values():
            if not isinstance(sec_body, dict):
                continue
            if set(sec_body.keys()) <= {"directory"} and isinstance(
                sec_body.get("directory"), str
            ):
                raw_dir = Path(sec_body["directory"])
                if not raw_dir.is_absolute():
                    raw_dir = host_cargo_home / raw_dir
                if raw_dir.is_dir() and not raw_dir.is_symlink():
                    dirs.append(raw_dir.resolve())
        break
    return dirs


def _copy_verified_vendored_crate(
    vendor_dirs: list[Path],
    *,
    dest_dir: Path,
    name: str,
    version: str,
    expected_sha: str,
) -> bool:
    """Copy a pre-vendored crate after full `.cargo-checksum.json` verification."""
    for vroot in vendor_dirs:
        src_dir = vroot / f"{name}-{version}"
        if not (src_dir.exists() and not src_dir.is_symlink() and src_dir.is_dir()):
            alt_dir = vroot / name
            if not (alt_dir.exists() and not alt_dir.is_symlink() and alt_dir.is_dir()):
                continue
            src_dir = alt_dir
        csum_path = src_dir / ".cargo-checksum.json"
        if not csum_path.exists() and not csum_path.is_symlink():
            continue
        csum_raw = _read_regular_file_nofollow(
            csum_path,
            max_bytes=_MAX_CAPTURE_BYTES,
            label=f"vendor checksum for {name}-{version}",
            exc_type=OracleInfrastructureError,
        )
        csum_obj = json.loads(
            csum_raw.decode("utf-8"),
            object_pairs_hook=anneal_ci_lib.reject_duplicate_json_keys,
        )
        if csum_obj.get("package") != expected_sha:
            raise OracleInfrastructureError(
                f"vendored crate package checksum mismatch for {name}-{version}"
            )
        files_obj = csum_obj.get("files")
        if not isinstance(files_obj, dict):
            raise OracleInfrastructureError(
                f"invalid .cargo-checksum.json files map for {name}-{version}"
            )
        manifest_path = src_dir / "Cargo.toml"
        pkg_meta = tomllib.loads(
            _read_regular_file_nofollow(
                manifest_path,
                max_bytes=MAX_CRATE_ARCHIVE_BYTES,
                label=f"vendored {name}-{version}/Cargo.toml",
                exc_type=OracleInfrastructureError,
            ).decode("utf-8")
        ).get("package", {})
        if pkg_meta.get("name") != name or pkg_meta.get("version") != version:
            continue
        actual_files: dict[str, tuple[bytes, int]] = {}
        total_bytes = 0
        for cur_root, dirnames, filenames in os.walk(
            src_dir, topdown=True, followlinks=False
        ):
            cur = Path(cur_root)
            for dname in dirnames:
                dpath = cur / dname
                st = os.lstat(dpath)
                if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(st.st_mode):
                    raise OracleInfrastructureError(
                        f"unsafe symlink/dir in vendored {name}-{version}: {dname}"
                    )
            for fname in sorted(filenames):
                fpath = cur / fname
                rel = _validate_rel_posix(fpath.relative_to(src_dir).as_posix())
                if rel == ".cargo-checksum.json":
                    continue
                data = _read_regular_file_nofollow(
                    fpath,
                    max_bytes=MAX_CRATE_ARCHIVE_BYTES,
                    label=f"vendored {name}-{version}/{rel}",
                    exc_type=OracleInfrastructureError,
                )
                total_bytes += len(data)
                if total_bytes > MAX_CRATE_ARCHIVE_BYTES:
                    raise OracleInfrastructureError(
                        f"vendored crate exceeds byte cap: {name}-{version}"
                    )
                mode = stat.S_IMODE(os.lstat(fpath).st_mode)
                if _sha256_bytes(data) != files_obj.get(rel):
                    raise OracleInfrastructureError(
                        f"vendored file checksum mismatch for {name}-{version}/{rel}"
                    )
                actual_files[rel] = (data, mode)
        if set(actual_files) != set(files_obj):
            raise OracleInfrastructureError(
                f"vendored file set mismatch against .cargo-checksum.json for {name}-{version}"
            )
        dest_dir.mkdir(parents=True, exist_ok=True)
        for rel, (data, mode) in sorted(actual_files.items()):
            target = dest_dir / rel
            _write_new_regular_file_excl(target, data)
            os.chmod(target, 0o755 if (mode & 0o111) else 0o644)
        _write_new_regular_file_excl(dest_dir / ".cargo-checksum.json", csum_raw)
        return True
    return False


def _prepare_e1_isolated_cargo_home(
    tmp_root: Path,
    *,
    lockfile: Path | None = None,
) -> Path:
    """Create a verified, config-free `CARGO_HOME` for Tier-E1 offline builds."""
    e1_cargo_home = tmp_root / "e1_cargo_home"
    e1_cargo_home.mkdir(parents=True, exist_ok=True)
    external_pkgs = _parse_e1_lock_packages(lockfile)
    if not external_pkgs:
        return e1_cargo_home

    raw_ch = os.environ.get("CARGO_HOME", "").strip()
    host_cargo_home = Path(raw_ch) if raw_ch else (Path.home() / ".cargo")
    cache_root = host_cargo_home / "registry" / "cache"
    vendor_dirs = _discover_host_vendor_dirs(host_cargo_home)
    e1_vendor = tmp_root / "e1_vendor"
    e1_vendor.mkdir(parents=True, exist_ok=True)

    for name, version, expected_sha in external_pkgs:
        dest_dir = e1_vendor / f"{name}-{version}"
        crate_bytes = _find_verified_crate_archive(
            cache_root,
            name=name,
            version=version,
            expected_sha=expected_sha,
        )
        if crate_bytes is not None:
            _extract_verified_crate_tarball(
                crate_bytes,
                dest_dir=dest_dir,
                name=name,
                version=version,
                expected_sha=expected_sha,
            )
            continue
        if _copy_verified_vendored_crate(
            vendor_dirs,
            dest_dir=dest_dir,
            name=name,
            version=version,
            expected_sha=expected_sha,
        ):
            continue
        raise OracleInfrastructureError(
            f"missing verified offline crate archive/vendor for {name}-{version} "
            f"(sha256={expected_sha})"
        )

    config_text = (
        "[net]\n"
        "offline = true\n\n"
        "[source.crates-io]\n"
        'replace-with = "e1_vendor"\n\n'
        "[source.e1_vendor]\n"
        f'directory = "{_escape_toml_basic_string(str(e1_vendor))}"\n'
    )
    _write_new_regular_file_excl(
        e1_cargo_home / "config.toml", config_text.encode("utf-8")
    )
    return e1_cargo_home


def _evaluate_s2_lean_patch_proof_staged(
    *,
    tmp_root: Path,
    patched_anneal: Path,
    spec: scenarios.ScenarioSpec,
    submission: LoadedSubmission,
    captured_bytes: bytes,
    shard_entries: list[tuple[str, str, bytes]],
    shard_mods: list[str],
    lean_bin: Path,
    capture: Path,
    sysroot: Path,
    bwrap: Path,
    env: dict[str, str],
    timeout: int,
    pin_tree: Callable[[Path], None],
    verify_pinned: Callable[[], None],
) -> E1VerificationResult:
    """Run Gates 4A/4B/2/3 on staged `patched_anneal` under full tree pinning."""

    # Rebuild `cargo-anneal` and `anneal-audit` strictly from `patched_anneal`
    # using the pinned sysroot `cargo`/`rustc` and a config-free Cargo home.
    e1_build_timeout = max(timeout, 900)
    e1_lean_timeout = max(timeout, 300)
    patched_target = tmp_root / "patched_target"
    pinned_cargo = sysroot / "bin" / "cargo"
    pinned_rustc = sysroot / "bin" / "rustc"
    if not (
        pinned_cargo.is_file()
        and os.access(pinned_cargo, os.X_OK)
        and pinned_rustc.is_file()
        and os.access(pinned_rustc, os.X_OK)
    ):
        raise OracleInfrastructureError(
            f"Tier-E1 build requires executable cargo and rustc under sysroot `{sysroot}`"
        )
    e1_cargo_home = _prepare_e1_isolated_cargo_home(
        tmp_root, lockfile=patched_anneal / "Cargo.lock"
    )
    e1_home = tmp_root / "e1_home"
    e1_home.mkdir(parents=True, exist_ok=True)
    build_env = {
        "PATH": f"{sysroot / 'bin'}:/usr/bin:/bin",
        "HOME": str(e1_home),
        "TMPDIR": str(e1_home),
        "CARGO_HOME": str(e1_cargo_home),
        "CARGO": str(pinned_cargo),
        "RUSTC": str(pinned_rustc),
        "LD_LIBRARY_PATH": str(sysroot / "lib"),
        "CARGO_NET_OFFLINE": "true",
        "NO_COLOR": "1",
    }
    try:
        build_proc = _run_bounded_subprocess(
            [
                str(pinned_cargo),
                "build",
                "--locked",
                "--offline",
                "--manifest-path",
                str(patched_anneal / "Cargo.toml"),
                "--target-dir",
                str(patched_target),
                "-p",
                "cargo-anneal",
                "--bin",
                "cargo-anneal",
                "-p",
                "anneal-audit",
                "--bin",
                "anneal-audit",
            ],
            cwd=patched_anneal,
            env=build_env,
            timeout=e1_build_timeout,
            apply_prlimit=False,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"failed to build patched cargo-anneal/anneal-audit within {e1_build_timeout}s"
        ) from exc
    except OSError as exc:
        raise OracleInfrastructureError(
            f"failed to launch cargo build for patched artifacts: {exc}"
        ) from exc
    if build_proc.returncode != 0:
        raise OracleInfrastructureError(
            "failed to build patched cargo-anneal/anneal-audit: "
            + (build_proc.stderr or build_proc.stdout)[-600:]
        )
    patched_cli = patched_target / "debug" / "cargo-anneal"
    patched_auditor = patched_target / "debug" / "anneal-audit"

    # Gate 4A: Pinned MirSemantics/Theory canaries & correspondence under
    # sandboxed `anneal-audit`.
    if not (patched_anneal / "correspondence").is_dir():
        raise OracleInfrastructureError(
            "Tier-E1 staged Anneal tree is missing required `correspondence/` directory"
        )
    e1_miri_cache = tmp_root / "e1_miri_cache"
    try:
        theory_audit_proc = _run_auditor_in_bwrap(
            auditor_bin=patched_auditor,
            anneal_root_host=patched_anneal,
            lean_bin=lean_bin,
            miri_cache_dir=e1_miri_cache,
            env=env,
            bwrap=bwrap,
            timeout=e1_build_timeout,
            require_correspondence=True,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            "Preservation Canary Gate timed out running `anneal-audit` "
            f"after {e1_build_timeout}s"
        ) from exc
    except OSError as exc:
        raise OracleInfrastructureError(
            f"failed to execute patched anneal-audit: {exc}"
        ) from exc
    if theory_audit_proc.returncode != 0:
        e1_lean_sysroot = _resolve_lean_sysroot(lean_bin, env)
        _verify_bwrap_canary(
            bwrap,
            ro_mounts=[
                (e1_lean_sysroot, "/opt/anneal-rt/lean"),
                (patched_auditor, "/opt/anneal-rt/anneal-audit"),
            ],
            env_vars={
                "PATH": "/opt/anneal-rt/lean/bin:/usr/bin:/bin",
                "HOME": "/work/tmp",
                "TMPDIR": "/work/tmp",
                "NO_COLOR": "1",
            },
            argv=["/opt/anneal-rt/lean/bin/lean", "--version"],
            bind_dev_seeds=True,
            ro_system_bins=True,
            tmpfs_tmp=True,
            disable_userns=False,
            label="e1_gate4a",
        )
        err = (theory_audit_proc.stderr or theory_audit_proc.stdout).strip()[:800]
        return E1VerificationResult(
            passed=False,
            preservation_passed=False,
            reference_target_verified=False,
            theory_canaries_verified=False,
            patch_audit=None,
            detail=(
                "Preservation Canary Gate failed on positive "
                f"MirSemantics/Theory canaries: {err}"
            ),
        )

    # Gate 4B: Reference valid `target(x) -> u32 { x }` vs `Spec.specs`.
    ref_work = tmp_root / "e1_ref_work"
    ref_artifacts = tmp_root / "e1_ref_artifacts"
    ref_receipt = tmp_root / "e1_ref_receipt.json"
    ref_work.mkdir(parents=True, exist_ok=True)
    (ref_work / "Cargo.toml").write_text(scenarios._S2_CARGO_TOML, encoding="utf-8")
    (ref_work / "Spec.lean").write_text(scenarios._S2_SPEC_LEAN, encoding="utf-8")
    (ref_work / "src").mkdir(parents=True, exist_ok=True)
    (ref_work / "src/lib.rs").write_text(_S2_REFERENCE_TARGET_RS, encoding="utf-8")
    (ref_work / "Proof.lean").write_text(
        _S2_REFERENCE_TARGET_PROOF_LEAN, encoding="utf-8"
    )
    ref_req = ref_work / "request.json"
    ref_req.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "compilation": {
                    "source_root": ".",
                    "crate_root": "src/lib.rs",
                    "crate_name": "redteam_s2",
                    "edition": "2024",
                    "target": VERIFIED_RUST_TARGET,
                    "source_files": ["src/lib.rs"],
                },
                "scope": {"kind": "crate"},
                "proof": {
                    "source_root": ".",
                    "sources": [
                        {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                        {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                    ],
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    ref_verify_ok, ref_inspect_ok, _rv, _ri, ref_failures = _run_verify_and_inspect(
        work=ref_work,
        request_path=ref_req,
        artifacts_dir=ref_artifacts,
        receipt_path=ref_receipt,
        spec=spec,
        tools={
            "cli": patched_cli,
            "capture": capture,
            "sysroot": sysroot,
            "lean": lean_bin,
        },
        env=env,
        timeout=timeout,
    )
    if not (ref_verify_ok and ref_inspect_ok):
        return E1VerificationResult(
            passed=False,
            preservation_passed=False,
            reference_target_verified=False,
            theory_canaries_verified=True,
            patch_audit=None,
            detail=(
                "Preservation Canary Gate failed on valid reference `target(x) = x`: "
                + "; ".join(ref_failures)
            ),
        )

    # Gate 2 & Gate 3: Immutable Binding (`IncorrectnessExpected.lean`) + strict
    # sandboxed `TrustedBoundary` preflight and kernel-replay audit.
    lean_sysroot = _resolve_lean_sysroot(lean_bin, env)
    try:
        flock = anneal_ci_lib.load_strict_json_object(
            patched_anneal / "trusted/lean/foundation-lock.json",
            label="foundation-lock.json",
        )
        raw_mods = flock["modules"]
        if not isinstance(raw_mods, dict):
            raise TypeError("foundation-lock.json `modules` must be a mapping")
        foundation_mods = sorted(raw_mods.keys())
    except (OSError, RuntimeError, KeyError, TypeError) as exc:
        raise OracleInfrastructureError(
            f"invalid foundation-lock.json: {exc}"
        ) from exc

    # Compile patched Trusted + core Anneal.MirWp + TrustedBoundary under bwrap.
    tb_box_out = tmp_root / "e1_tb_out"
    trusted_box_out = tmp_root / "e1_trusted_out"
    theory_box_out = tmp_root / "e1_theory_out"
    proof_box_src = tmp_root / "e1_proof_src"
    proof_fixed_out = tmp_root / "e1_proof_fixed_out"
    proof_box_out = tmp_root / "e1_proof_out"
    proof_check_out = tmp_root / "e1_proof_check_out"
    for d in (
        tb_box_out,
        trusted_box_out,
        theory_box_out,
        proof_box_src,
        proof_fixed_out,
        proof_box_out,
        proof_check_out,
    ):
        d.mkdir(parents=True, exist_ok=True)

    # Compile TrustedBoundary.lean using Sysroot inside bwrap.
    try:
        tb_compile = _run_lean_in_bwrap(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[(patched_anneal / "trusted/audit", "/work/audit_src")],
            rw_mounts=[(tb_box_out, "/work/tb_out")],
            lean_path_mounts=["/work/tb_out"],
            cwd_in_sandbox="/work",
            lean_args=[
                "-j1",
                "-M4096",
                "-t0",
                "-R",
                "/work/audit_src",
                "-o",
                "/work/tb_out/TrustedBoundary.olean",
                "/work/audit_src/TrustedBoundary.lean",
            ],
            timeout=e1_lean_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"timed out compiling patched TrustedBoundary.lean after {e1_lean_timeout}s"
        ) from exc
    if tb_compile.returncode != 0:
        raise OracleInfrastructureError(
            "failed to compile patched TrustedBoundary.lean: "
            + (tb_compile.stderr or tb_compile.stdout)[-500:]
        )
    pin_tree(tb_box_out)

    trust_entries = _extract_trust_tiers(patched_anneal / "trusted/lean/Trusted")
    trusted_mod_map = {m: p for m, _t, p in trust_entries}
    trusted_order = _topo_sort_lean_modules(trusted_mod_map)
    ok_tr, err_tr = _compile_lean_modules_in_bwrap(
        bwrap=bwrap,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        modules=trusted_order,
        src_host=patched_anneal / "trusted/lean",
        src_box="/work/trusted_src",
        out_host=trusted_box_out,
        out_box="/work/trusted_out",
        extra_ro_mounts=[],
        lean_path_mounts=["/work/trusted_out"],
        timeout=e1_lean_timeout,
    )
    if not ok_tr:
        return E1VerificationResult(
            passed=False,
            preservation_passed=False,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit=None,
            detail=f"patched Trusted {err_tr}",
        )
    pin_tree(trusted_box_out)

    theory_core_order, _theory_core_map = _discover_lean_closure(
        patched_anneal / "theory",
        ("Anneal.MirWp", "Anneal.MirWp.Canaries"),
    )
    ok_th, err_th = _compile_lean_modules_in_bwrap(
        bwrap=bwrap,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        modules=theory_core_order,
        src_host=patched_anneal / "theory",
        src_box="/work/theory_src",
        out_host=theory_box_out,
        out_box="/work/theory_out",
        extra_ro_mounts=[(trusted_box_out, "/work/trusted_out")],
        lean_path_mounts=["/work/trusted_out", "/work/theory_out"],
        timeout=e1_lean_timeout,
    )
    if not ok_th:
        return E1VerificationResult(
            passed=False,
            preservation_passed=False,
            reference_target_verified=True,
            theory_canaries_verified=False,
            patch_audit=None,
            detail=f"core Anneal.MirWp {err_th}",
        )
    pin_tree(theory_box_out)

    # Stage E1 Captured (plus any sharded Captured.Shard_NNN) + Spec +
    # IncorrectnessExpected + Proof + Check.
    proof_src_resolved = proof_box_src.resolve()
    for _shard_mod, shard_rel, shard_bytes in shard_entries:
        _write_new_regular_file_excl(proof_box_src / shard_rel, shard_bytes)
    _write_new_regular_file_excl(proof_box_src / "Captured.lean", captured_bytes)
    _write_new_regular_file_excl(
        proof_box_src / "Spec.lean", scenarios._S2_SPEC_LEAN.encode("utf-8")
    )
    _write_new_regular_file_excl(
        proof_box_src / "IncorrectnessExpected.lean",
        (
            scenarios._HEADER_LEAN
            + "module\nprelude\n"
            + "public import Trusted.MirSemantics\n"
            + "public import Captured\n"
            + "public import Spec\n\n"
            + "@[expose] public section\n\n"
            + "namespace IncorrectnessExpected\n\n"
            + "def claim : Prop := ¬ Spec.targetSpec Captured.program\n\n"
            + "end IncorrectnessExpected\n\nend\n"
        ).encode("utf-8"),
    )
    helper_mods: list[tuple[str, Path]] = []
    for rel, data in sorted(submission.files.items()):
        if rel == "incorrectness/Proof.lean":
            dest = proof_box_src / "Proof.lean"
            _write_new_regular_file_excl(dest, data)
        elif rel.startswith("incorrectness/Helper/"):
            mod_name = _validate_lean_slot_path(rel, "incorrectness")
            if mod_name.split(".")[0] in (
                "Captured",
                "Spec",
                "IncorrectnessExpected",
                "IncorrectnessCheck",
                "Proof",
            ):
                raise InvalidSubmissionError(
                    f"reserved module root in incorrectness helper: {rel}"
                )
            staged_rel = rel[len("incorrectness/") :]
            dest = (proof_box_src / staged_rel).resolve()
            if not dest.is_relative_to(proof_src_resolved):
                raise InvalidSubmissionError(
                    f"incorrectness helper escapes staging tree: {rel}"
                )
            _write_new_regular_file_excl(dest, data)
            helper_mods.append((mod_name, dest))

    _write_new_regular_file_excl(
        proof_box_src / "IncorrectnessCheck.lean",
        (
            scenarios._HEADER_LEAN
            + "module\nprelude\n"
            + "public import IncorrectnessExpected\n"
            + "public import Proof\n\n"
            + "public theorem IncorrectnessCheck.verified :\n"
            + "    _root_.IncorrectnessExpected.claim :=\n"
            + "  _root_.Proof.verify\n"
        ).encode("utf-8"),
    )
    pin_tree(proof_box_src)

    # Helper runner for TrustedBoundary requests inside bwrap.
    tb_ipc_dir = tmp_root / "e1_tb_ipc"
    tb_ipc_dir.mkdir(parents=True, exist_ok=True)
    runner_lean = tb_ipc_dir / "RunTb.lean"
    runner_lean.write_text("import TrustedBoundary\n", encoding="utf-8")

    # Gather foundation artifact map using in-sandbox /toolchain paths.
    sysroot_lib = lean_sysroot / "lib/lean"
    found_root_map = {
        m: sysroot_lib / m.replace(".", "/") for m in foundation_mods
    }
    # Host check for exact suffixes mapped to `/toolchain/lib/lean` / `/work`.
    found_artifacts_host = _discover_module_artifacts(found_root_map)
    foundation_artifacts: dict[str, list[list[str]]] = {}
    for m, (oparts, iparts) in found_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(sysroot_lib), "/toolchain/lib/lean") for p in oparts],
            [p.replace(str(sysroot_lib), "/toolchain/lib/lean") for p in iparts],
        ]
    trusted_artifacts_host = _discover_module_artifacts(
        {m: trusted_box_out / m.replace(".", "/") for m in trusted_order}
    )
    for m, (oparts, iparts) in trusted_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(trusted_box_out), "/work/trusted_out") for p in oparts],
            [p.replace(str(trusted_box_out), "/work/trusted_out") for p in iparts],
        ]

    theory_core_artifacts_host = _discover_module_artifacts(
        {m: theory_box_out / m.replace(".", "/") for m in theory_core_order}
    )
    for m, (oparts, iparts) in theory_core_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(theory_box_out), "/work/theory_out") for p in oparts],
            [p.replace(str(theory_box_out), "/work/theory_out") for p in iparts],
        ]

    # Run TrustedBoundary "preflight" over Trusted/MirWp/Helper/Proof.
    req_pf = tb_ipc_dir / "req_preflight.json"
    res_pf = tb_ipc_dir / "res_preflight.json"
    req_pf.write_text(
        json.dumps(
            {
                "mode": "preflight",
                "sysroot": "/toolchain",
                "artifacts": [[m, foundation_artifacts[m]] for m in foundation_mods],
                "foundation": foundation_mods,
                "graph": flock["graph"],
                "axioms": flock["axioms"],
                "sources": [
                    [m, f"/work/trusted_src/{m.replace('.', '/')}.lean"]
                    for m in trusted_order
                ]
                + [
                    [m, f"/work/theory_src/{m.replace('.', '/')}.lean"]
                    for m in theory_core_order
                ]
                + [
                    [mod_name, f"/work/proof_src/{mod_name.replace('.', '/')}.lean"]
                    for mod_name, _ in helper_mods
                ]
                + [["Proof", "/work/proof_src/Proof.lean"]],
            }
        ),
        encoding="utf-8",
    )
    try:
        pf_proc = _run_lean_in_bwrap(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[
                (tb_box_out, "/work/tb_out"),
                (trusted_box_out, "/work/trusted_out"),
                (theory_box_out, "/work/theory_out"),
                (patched_anneal / "trusted/lean", "/work/trusted_src"),
                (patched_anneal / "theory", "/work/theory_src"),
                (proof_box_src, "/work/proof_src"),
            ],
            rw_mounts=[(tb_ipc_dir, "/work/ipc")],
            lean_path_mounts=[
                "/work/tb_out",
                "/work/trusted_out",
                "/work/theory_out",
            ],
            cwd_in_sandbox="/work",
            lean_args=[
                "--run",
                "/work/ipc/RunTb.lean",
                "/work/ipc/req_preflight.json",
                "/work/ipc/res_preflight.json",
            ],
            timeout=e1_lean_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"Tier-E1 preflight timed out after {e1_lean_timeout}s"
        ) from exc
    pf_json: dict[str, Any] | None = None
    if res_pf.exists() or res_pf.is_symlink():
        try:
            pf_json = anneal_ci_lib.load_strict_json_object(
                res_pf, label="Tier-E1 preflight result"
            )
        except (OSError, RuntimeError):
            pf_json = None
    verify_pinned()
    if pf_proc.returncode != 0 or not (isinstance(pf_json, dict) and pf_json.get("ok")):
        msg = (
            pf_json.get("message")
            if isinstance(pf_json, dict)
            else (pf_proc.stderr or pf_proc.stdout)
        )
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={"preflight_ok": False, "audit_ok": False, "detail": str(msg)[:600]},
            detail=f"Tier-E1 preflight rejected incorrectness Proof: {msg}",
        )

    helper_order = _topo_sort_lean_modules(dict(helper_mods))
    # Compile defender-owned Captured shards, Captured, Spec, and
    # IncorrectnessExpected FIRST into `proof_fixed_out`, then mount that
    # output directory read-only while compiling untrusted Helper/Proof modules
    # into `proof_box_out`, and finally compile IncorrectnessCheck into
    # `proof_check_out` with both prior dirs read-only.
    fixed_mods = [*shard_mods, "Captured", "Spec", "IncorrectnessExpected"]
    attacker_mods = [*helper_order, "Proof"]
    theory_mods = fixed_mods + attacker_mods + ["IncorrectnessCheck"]
    ok_fixed, err_fixed = _compile_lean_modules_in_bwrap(
        bwrap=bwrap,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        modules=fixed_mods,
        src_host=proof_box_src,
        src_box="/work/proof_src",
        out_host=proof_fixed_out,
        out_box="/work/proof_fixed_out",
        extra_ro_mounts=[
            (trusted_box_out, "/work/trusted_out"),
            (theory_box_out, "/work/theory_out"),
        ],
        lean_path_mounts=[
            "/work/trusted_out",
            "/work/theory_out",
            "/work/proof_fixed_out",
        ],
        timeout=e1_lean_timeout,
    )
    if not ok_fixed:
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={"preflight_ok": True, "audit_ok": False, "detail": err_fixed},
            detail=f"Tier-E1 fixed binding compilation failed: {err_fixed}",
        )
    pin_tree(proof_fixed_out)

    ok_pr, err_pr = _compile_lean_modules_in_bwrap(
        bwrap=bwrap,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        modules=attacker_mods,
        src_host=proof_box_src,
        src_box="/work/proof_src",
        out_host=proof_box_out,
        out_box="/work/proof_out",
        extra_ro_mounts=[
            (trusted_box_out, "/work/trusted_out"),
            (theory_box_out, "/work/theory_out"),
            (proof_fixed_out, "/work/proof_fixed_out"),
        ],
        lean_path_mounts=[
            "/work/trusted_out",
            "/work/theory_out",
            "/work/proof_fixed_out",
            "/work/proof_out",
        ],
        timeout=e1_lean_timeout,
    )
    verify_pinned()
    for reserved_mod in (*fixed_mods, "IncorrectnessCheck"):
        rel_stem = reserved_mod.replace(".", "/")
        for ext in (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig"):
            shadow_rel = f"{rel_stem}{ext}"
            shadow = proof_box_out / shadow_rel
            if shadow.exists() or shadow.is_symlink():
                raise DefenderTamperError(
                    f"Tier-E1 attacker compilation shadowed {reserved_mod}{ext}",
                    tampered_paths=(shadow_rel,),
                )
    if not ok_pr:
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={"preflight_ok": True, "audit_ok": False, "detail": err_pr},
            detail=f"Tier-E1 proof compilation failed: {err_pr}",
        )

    ok_chk, err_chk = _compile_lean_modules_in_bwrap(
        bwrap=bwrap,
        lean_bin=lean_bin,
        lean_sysroot=lean_sysroot,
        modules=["IncorrectnessCheck"],
        src_host=proof_box_src,
        src_box="/work/proof_src",
        out_host=proof_check_out,
        out_box="/work/proof_check_out",
        extra_ro_mounts=[
            (trusted_box_out, "/work/trusted_out"),
            (theory_box_out, "/work/theory_out"),
            (proof_fixed_out, "/work/proof_fixed_out"),
            (proof_box_out, "/work/proof_out"),
        ],
        lean_path_mounts=[
            "/work/trusted_out",
            "/work/theory_out",
            "/work/proof_fixed_out",
            "/work/proof_out",
            "/work/proof_check_out",
        ],
        timeout=e1_lean_timeout,
    )
    if not ok_chk:
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={"preflight_ok": True, "audit_ok": False, "detail": err_chk},
            detail=f"Tier-E1 verification wrapper compilation failed: {err_chk}",
        )

    # Extract header import edges for the fixed staged modules.
    req_hdr = tb_ipc_dir / "req_headers.json"
    res_hdr = tb_ipc_dir / "res_headers.json"
    staged_fixed_mods = [
        *shard_mods,
        "Captured",
        "Spec",
        "IncorrectnessExpected",
        "IncorrectnessCheck",
    ]
    req_hdr.write_text(
        json.dumps(
            {
                "mode": "headers",
                "sysroot": "/toolchain",
                "sources": [
                    [m, f"/work/proof_src/{m.replace('.', '/')}.lean"]
                    for m in staged_fixed_mods
                ],
            }
        ),
        encoding="utf-8",
    )
    try:
        hdr_proc = _run_lean_in_bwrap(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[
                (tb_box_out, "/work/tb_out"),
                (proof_box_src, "/work/proof_src"),
            ],
            rw_mounts=[(tb_ipc_dir, "/work/ipc")],
            lean_path_mounts=["/work/tb_out"],
            cwd_in_sandbox="/work",
            lean_args=[
                "--run",
                "/work/ipc/RunTb.lean",
                "/work/ipc/req_headers.json",
                "/work/ipc/res_headers.json",
            ],
            timeout=e1_lean_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"timed out parsing Tier-E1 fixed module headers after {e1_lean_timeout}s"
        ) from exc
    hdr_json: dict[str, Any] | None = None
    if res_hdr.exists() or res_hdr.is_symlink():
        try:
            hdr_json = anneal_ci_lib.load_strict_json_object(
                res_hdr, label="Tier-E1 fixed module headers result"
            )
        except (OSError, RuntimeError) as exc:
            raise OracleInfrastructureError(
                f"invalid Tier-E1 headers JSON: {exc}"
            ) from exc
    if hdr_proc.returncode != 0 or not (isinstance(hdr_json, dict) and hdr_json.get("ok")):
        raise OracleInfrastructureError(
            "failed to parse Tier-E1 fixed module headers: "
            + (hdr_proc.stderr or hdr_proc.stdout)[-400:]
        )
    verify_pinned()

    try:
        full_graph: dict[str, Any] = dict(pf_json["result"]["graph"])
        for entry in pf_json["result"]["headers"] + hdr_json["result"]["headers"]:
            full_graph[entry["module"]] = entry["imports"]
    except (KeyError, TypeError, AttributeError) as exc:
        raise OracleInfrastructureError(
            f"malformed TrustedBoundary header/graph structure: {exc}"
        ) from exc
    fixed_artifacts_host = _discover_module_artifacts(
        {m: proof_fixed_out / m.replace(".", "/") for m in fixed_mods}
    )
    for m, (oparts, iparts) in fixed_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(proof_fixed_out), "/work/proof_fixed_out") for p in oparts],
            [p.replace(str(proof_fixed_out), "/work/proof_fixed_out") for p in iparts],
        ]
    attacker_artifacts_host = _discover_module_artifacts(
        {m: proof_box_out / m.replace(".", "/") for m in attacker_mods}
    )
    for m, (oparts, iparts) in attacker_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(proof_box_out), "/work/proof_out") for p in oparts],
            [p.replace(str(proof_box_out), "/work/proof_out") for p in iparts],
        ]
    check_artifacts_host = _discover_module_artifacts(
        {"IncorrectnessCheck": proof_check_out / "IncorrectnessCheck"}
    )
    for m, (oparts, iparts) in check_artifacts_host.items():
        foundation_artifacts[m] = [
            [p.replace(str(proof_check_out), "/work/proof_check_out") for p in oparts],
            [p.replace(str(proof_check_out), "/work/proof_check_out") for p in iparts],
        ]

    all_theory_mods = theory_core_order + theory_mods
    # Gate 3: Run TrustedBoundary "audit" (`loadExts := false`, kernel replay).
    req_aud = tb_ipc_dir / "req_audit.json"
    res_aud = tb_ipc_dir / "res_audit.json"
    req_aud.write_text(
        json.dumps(
            {
                "mode": "audit",
                "sysroot": "/toolchain",
                "artifacts": [
                    [m, foundation_artifacts[m]]
                    for m in foundation_mods + trusted_order + all_theory_mods
                ],
                "foundation": foundation_mods,
                "graph": full_graph,
                "axioms": flock["axioms"],
                "trusted": trusted_order,
                "theory": all_theory_mods,
                "moduleTiers": [[m, tier] for m, tier, _p in trust_entries],
                "requireMirWp": True,
            }
        ),
        encoding="utf-8",
    )
    try:
        aud_proc = _run_lean_in_bwrap(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            ro_mounts=[
                (tb_box_out, "/work/tb_out"),
                (trusted_box_out, "/work/trusted_out"),
                (theory_box_out, "/work/theory_out"),
                (proof_fixed_out, "/work/proof_fixed_out"),
                (proof_box_out, "/work/proof_out"),
                (proof_check_out, "/work/proof_check_out"),
            ],
            rw_mounts=[(tb_ipc_dir, "/work/ipc")],
            lean_path_mounts=[
                "/work/tb_out",
                "/work/trusted_out",
                "/work/theory_out",
                "/work/proof_fixed_out",
                "/work/proof_out",
                "/work/proof_check_out",
            ],
            cwd_in_sandbox="/work",
            lean_args=[
                "--run",
                "/work/ipc/RunTb.lean",
                "/work/ipc/req_audit.json",
                "/work/ipc/res_audit.json",
            ],
            timeout=e1_lean_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"Tier-E1 strict kernel audit timed out after {e1_lean_timeout}s"
        ) from exc
    aud_json: dict[str, Any] | None = None
    if res_aud.exists() or res_aud.is_symlink():
        try:
            aud_json = anneal_ci_lib.load_strict_json_object(
                res_aud, label="Tier-E1 kernel audit result"
            )
        except (OSError, RuntimeError):
            aud_json = None
    if aud_proc.returncode != 0 or not (isinstance(aud_json, dict) and aud_json.get("ok")):
        msg = (
            aud_json.get("message")
            if isinstance(aud_json, dict)
            else (aud_proc.stderr or aud_proc.stdout)
        )
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={"preflight_ok": True, "audit_ok": False, "detail": str(msg)[:600]},
            detail=f"Tier-E1 strict kernel audit rejected Proof: {msg}",
        )

    result_obj = aud_json.get("result", {})
    if not isinstance(result_obj, dict):
        raise OracleInfrastructureError("malformed Tier-E1 audit result object")
    axioms = result_obj.get("axioms", [])
    if (
        result_obj.get("replay") is not True
        or not anneal_ci_lib.is_exact_int(
            result_obj.get("checkedAlternateProofs"), 0
        )
        or not isinstance(axioms, list)
        or not all(isinstance(a, str) for a in axioms)
        or not set(axioms).issubset(dedup.ALLOWED_STANDARD_AXIOMS)
    ):
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={
                "preflight_ok": True,
                "audit_ok": False,
                "replay": bool(result_obj.get("replay")),
                "axioms": axioms,
                "detail": "disallowed E1 audit replay/axioms",
            },
            detail=f"Tier-E1 strict kernel audit rejected replay/axioms: {axioms!r}",
        )
    try:
        bind_ok, bind_msg = lean_ast.verify_e1_kernel_binding_in_bwrap(
            bwrap=bwrap,
            lean_bin=lean_bin,
            lean_sysroot=lean_sysroot,
            bwrap_runner=_run_lean_in_bwrap,
            ro_mounts=[
                (trusted_box_out, "/work/trusted_out"),
                (theory_box_out, "/work/theory_out"),
                (proof_fixed_out, "/work/proof_fixed_out"),
                (proof_box_out, "/work/proof_out"),
                (proof_check_out, "/work/proof_check_out"),
            ],
            modules=foundation_mods + trusted_order + all_theory_mods,
            attacker_modules=attacker_mods,
            artifacts_json=[
                [m, foundation_artifacts[m]]
                for m in foundation_mods + trusted_order + all_theory_mods
            ],
            require_s2_claim=True,
            timeout=e1_lean_timeout,
        )
    except subprocess.TimeoutExpired as exc:
        raise OracleInfrastructureError(
            f"Tier-E1 kernel claim binding timed out after {e1_lean_timeout}s"
        ) from exc
    if not bind_ok:
        return E1VerificationResult(
            passed=False,
            preservation_passed=True,
            reference_target_verified=True,
            theory_canaries_verified=True,
            patch_audit={
                "preflight_ok": True,
                "audit_ok": False,
                "replay": bool(result_obj.get("replay")),
                "axioms": axioms,
                "detail": bind_msg[:600],
            },
            detail=f"Tier-E1 kernel claim binding rejected Proof: {bind_msg}",
        )
    verify_pinned()
    return E1VerificationResult(
        passed=True,
        preservation_passed=True,
        reference_target_verified=True,
        theory_canaries_verified=True,
        patch_audit={
            "preflight_ok": True,
            "audit_ok": True,
            "replay": bool(result_obj.get("replay")),
            "axioms": axioms,
        },
        detail=(
            "Tier-E1 lean_patch_proof passed unpatched acceptance, strict "
            "kernel audit on IncorrectnessExpected.claim, and Defender "
            "Preservation Canary Gate"
        ),
    )


def evaluate_submission(
    *,
    scenario_id: str,
    submission_dir: Path | None = None,
    submission_tar: Path | None = None,
    anneal_root: Path | None = None,
    cli: Path | None = None,
    capture: Path | None = None,
    sysroot: Path | None = None,
    lean: Path | None = None,
    auditor: Path | None = None,
    bwrap: Path | None = None,
    prlimit: Path | None = None,
    miri_sysroot: Path | None = None,
    timeout_sec: int = 300,
    verify_runner: Callable[..., Any] | None = None,
    inspect_runner: Callable[..., Any] | None = None,
    audit_runner: Callable[..., Any] | None = None,
    miri_runner: Callable[..., Any] | None = None,
    rustc_runner: Callable[..., Any] | None = None,
    e1_runner: Callable[..., E1VerificationResult] | None = None,
) -> dict[str, Any]:
    """Evaluate one untrusted red-team submission in an isolated workspace."""
    if (
        not isinstance(timeout_sec, int)
        or isinstance(timeout_sec, bool)
        or timeout_sec <= 0
    ):
        raise ValueError(
            f"timeout_sec must be a positive integer, got {timeout_sec!r}"
        )
    if (submission_dir is None) == (submission_tar is None):
        raise ValueError("specify exactly one of submission_dir or submission_tar")
    spec = scenarios.get_scenario(scenario_id)
    root = (anneal_root or _default_anneal_root()).resolve()
    target_sha = "unknown"
    target_dirty: bool | None = None
    target_tree_sha256: str | None = None
    resolved_git: Path | None = None
    tool_provenance: dict[str, dict[str, Any]] | None = None
    explicit_overrides: dict[str, Path | None] = {
        "cli": cli,
        "capture": capture,
        "sysroot": sysroot,
        "lean": lean,
        "auditor": auditor,
        "bwrap": bwrap,
        "prlimit": prlimit,
        "miri_sysroot": miri_sysroot,
    }
    eval_tmp_root: Path | None = None
    resolved_tools: dict[str, Path | None] | None = None
    resolved_miri_sysroot: Path | None = miri_sysroot

    def _current_private_roots() -> tuple[tuple[str, str], ...]:
        tools_for_scrub: dict[str, Path | None] = dict(explicit_overrides)
        tools_for_scrub.pop("miri_sysroot", None)
        if resolved_tools is not None:
            for k, v in resolved_tools.items():
                if v is not None:
                    tools_for_scrub[k] = v
        return _collect_private_roots(
            tmp_root=eval_tmp_root,
            anneal_root=root,
            tools=tools_for_scrub,
            miri_sysroot=resolved_miri_sysroot,
            submission_dir=submission_dir,
            submission_tar=submission_tar,
        )

    def build_receipt(
        verdict: str,
        *,
        reasons: list[str],
        invalid_reason: str | None = None,
        defender_integrity_ok: bool = True,
        sandbox_escape_detected: bool = False,
        escape_mechanism: str | None = None,
        oracle_incorrect_confirmed: bool = False,
        incorrectness_evidence_tier: str = TIER_NONE,
        patch_incorrectness_verified: bool = False,
        preservation_gate_passed: bool | None = None,
        human_review_required: bool = False,
        proposed_severity: str | None = None,
        anneal_verify_ok: bool = False,
        anneal_inspect_ok: bool = False,
        code_oracle_status: str = "not_applicable",
        oracle_fault_class: str | None = None,
        verify_receipt: dict[str, Any] | None = None,
        inspect_report: dict[str, Any] | None = None,
        dedup_obj: dict[str, Any] | None = None,
        trace_artifacts: dict[str, Any] | None = None,
    ) -> dict[str, Any]:
        p_roots = _current_private_roots()
        sanitized_reasons = [
            _sanitize_snippet(
                r, tmp_root=eval_tmp_root, private_roots=p_roots
            )
            or ""
            for r in reasons
        ]
        sanitized_invalid = (
            _sanitize_snippet(
                invalid_reason, tmp_root=eval_tmp_root, private_roots=p_roots
            )
            if invalid_reason is not None
            else None
        )
        return {
            "schema_version": RECEIPT_SCHEMA,
            "scenario_id": spec.scenario_id,
            "scenario_kind": spec.kind,
            "verdict": verdict,
            "invalid_reason": sanitized_invalid,
            "defender_integrity_ok": defender_integrity_ok,
            "sandbox_escape_detected": sandbox_escape_detected,
            "escape_mechanism": escape_mechanism,
            "oracle_incorrect_confirmed": oracle_incorrect_confirmed,
            "incorrectness_evidence_tier": incorrectness_evidence_tier,
            "patch_incorrectness_verified": patch_incorrectness_verified,
            "preservation_gate_passed": preservation_gate_passed,
            "human_review_required": human_review_required,
            "proposed_severity": proposed_severity,
            "anneal_verify_ok": anneal_verify_ok,
            "anneal_inspect_ok": anneal_inspect_ok,
            "target_sha": target_sha,
            "target_dirty": target_dirty,
            "target_tree_sha256": target_tree_sha256,
            "tool_provenance": tool_provenance,
            "summary": "; ".join(sanitized_reasons),
            "reasons": sanitized_reasons,
            "code_oracle_status": code_oracle_status,
            "oracle_fault_class": oracle_fault_class,
            "verify_status": (
                verify_receipt.get("status")
                if isinstance(verify_receipt, dict)
                else None
            ),
            "verify_taint_reasons": (
                verify_receipt.get("taint_reasons")
                if isinstance(verify_receipt, dict)
                else None
            ),
            "elaboration_sandbox": (
                verify_receipt.get("elaboration_sandbox")
                if isinstance(verify_receipt, dict)
                else None
            ),
            "inspect_policy_violations": (
                inspect_report.get("policy_violations")
                if isinstance(inspect_report, dict)
                else None
            ),
            "dedup": (
                dedup_obj
                if verdict in (VERDICT_ATTACKER_WON, VERDICT_NEEDS_HUMAN_REVIEW)
                else None
            ),
            "trace_artifacts": trace_artifacts,
        }

    try:
        raw_files = (
            _load_submission_dir(submission_dir)
            if submission_dir is not None
            else _load_submission_tar(submission_tar)
        )
        submission = _validate_scenario_slots(spec, raw_files)
    except (
        InvalidSubmissionError,
        UnicodeError,
        RecursionError,
        LookupError,
        tarfile.TarError,
        lzma.LZMAError,
        zlib.error,
        gzip.BadGzipFile,
        ValueError,
        TypeError,
        IndexError,
        KeyError,
    ) as exc:
        msg = str(exc)
        return build_receipt(
            VERDICT_INVALID_SUBMISSION,
            reasons=[msg],
            invalid_reason=msg,
        )

    attacker_hashes = _snapshot_attacker_hashes(submission)
    eval_artifacts_dir: Path | None = None
    eval_v_receipt: dict[str, Any] | None = None
    eval_inspect_report: dict[str, Any] | None = None
    eval_audit_json: dict[str, Any] | None = None
    eval_capture_manifest: dict[str, Any] | None = None
    eval_oracle_status = "not_applicable"
    eval_fault_class: str | None = None
    eval_oracle_detail: str | None = None
    eval_verify_ok = False
    eval_inspect_ok = False
    eval_oracle_confirmed = False
    eval_e1_patch_diff: str | None = None
    eval_e1_pres_summary: dict[str, Any] | None = None
    eval_e1_proof_audit: dict[str, Any] | None = None
    eval_e2_claim: str | None = submission.claim_text if submission.has_e2 else None

    prlimit_token = _EXPLICIT_PRLIMIT_VAR.set(None)
    try:
        resolved_git = _resolve_system_binary("git", required=False)
        target_sha, target_dirty, target_tree_sha256 = _resolve_target_provenance(
            root, git_bin=resolved_git
        )
        resolved_bwrap = _resolve_bwrap_binary(bwrap, required=False)
        resolved_prlimit = _resolve_system_binary(
            "prlimit", prlimit, required=False
        )
        _EXPLICIT_PRLIMIT_VAR.set(resolved_prlimit)
        need_verify = spec.kind != "THEORY_AUDIT_HACK" and verify_runner is None
        need_s2_oracle = spec.kind == "CODE_AND_PROOF_HACK" and (
            miri_runner is None or rustc_runner is None
        )
        need_sysroot = need_verify or need_s2_oracle
        need_lean = True
        tools = anneal_ci_lib.discover_tools(
            root,
            cli=cli,
            capture=capture,
            sysroot=sysroot,
            lean=lean,
            auditor=auditor,
            defaults_fn=lambda anneal_root_arg: _discover_pinned_local_defaults(
                anneal_root_arg,
                need_cli=(cli is None and need_verify),
                need_capture=(capture is None and need_verify),
                need_lean=(lean is None and need_lean),
                need_sysroot=(sysroot is None and need_sysroot),
                bwrap=resolved_bwrap,
                timeout=timeout_sec,
            ),
        )
        resolved_tools = dict(tools)
        resolved_tools["bwrap"] = resolved_bwrap
        resolved_tools["prlimit"] = resolved_prlimit
        resolved_tools["git"] = resolved_git
        live_names: tuple[str, ...]
        if spec.kind == "THEORY_AUDIT_HACK":
            live_names = ("auditor",) if audit_runner is None else ()
        else:
            live_names = ("cli", "capture") if verify_runner is None else ()
        if live_names:
            _verify_live_tool_freshness(
                root,
                tools,
                explicit_overrides=explicit_overrides,
                live_names=live_names,
            )
        resolved_miri_sysroot = (
            _discover_miri_sysroot(
                miri_sysroot,
                sysroot=tools.get("sysroot"),
                bwrap=resolved_bwrap,
            )
            if spec.kind == "CODE_AND_PROOF_HACK" and miri_runner is None
            else miri_sysroot
        )
        tool_provenance = _snapshot_tool_provenance(
            tools,
            explicit_overrides=explicit_overrides,
            bwrap=resolved_bwrap,
            prlimit=resolved_prlimit,
            git=resolved_git,
            miri_sysroot=resolved_miri_sysroot,
        )
        env = _build_scrubbed_env(
            tools.get("sysroot"), miri_sysroot=resolved_miri_sysroot
        )

        with tempfile.TemporaryDirectory(prefix="anneal-redteam-") as tmp_dir:
            tmp_root = Path(tmp_dir)
            eval_tmp_root = tmp_root
            if spec.kind == "THEORY_AUDIT_HACK":
                s4_ast_tags: list[str] = []
                verdict, audit_json, reasons, oracle_status = (
                    _evaluate_theory_audit(
                        tmp_root=tmp_root,
                        anneal_root=root,
                        spec=spec,
                        submission=submission,
                        tools=tools,
                        env=env,
                        timeout=timeout_sec,
                        bwrap=resolved_bwrap,
                        audit_runner=audit_runner,
                        ast_tags_out=s4_ast_tags,
                    )
                )
                eval_audit_json = audit_json
                audit_passed = verdict == VERDICT_ATTACKER_WON or (
                    verdict != VERDICT_HARNESS_ERROR and audit_json is not None
                )
                evidence_tier = (
                    TIER_DEFENDER_FIXED_BUG
                    if verdict == VERDICT_ATTACKER_WON
                    else TIER_NONE
                )
                dedup_obj = (
                    dedup.compute_dedup_metadata(
                        scenario_id=spec.scenario_id,
                        scenario_kind=spec.kind,
                        submission_files=submission.files,
                        receipt=audit_json,
                        incorrectness_evidence_tier=evidence_tier,
                        ast_disallowed_tags=s4_ast_tags,
                    )
                    if verdict == VERDICT_ATTACKER_WON
                    else None
                )
                traces = _build_trace_artifacts(
                    tmp_root=tmp_root,
                    private_roots=_current_private_roots(),
                    audit_report=audit_json,
                    tool_stderr_snippet="; ".join(reasons) if reasons else None,
                    attacker_hashes=attacker_hashes,
                )
                return build_receipt(
                    verdict,
                    reasons=reasons or ["theory audit bypass confirmed"],
                    invalid_reason=(
                        reasons[0]
                        if verdict == VERDICT_HARNESS_ERROR and reasons
                        else None
                    ),
                    defender_integrity_ok=True,
                    sandbox_escape_detected=False,
                    oracle_incorrect_confirmed=(verdict == VERDICT_ATTACKER_WON),
                    incorrectness_evidence_tier=evidence_tier,
                    proposed_severity="P0" if verdict == VERDICT_ATTACKER_WON else None,
                    anneal_verify_ok=audit_passed,
                    anneal_inspect_ok=audit_passed,
                    code_oracle_status=oracle_status,
                    dedup_obj=dedup_obj,
                    trace_artifacts=traces,
                )

            work = tmp_root / "workspace"
            artifacts_dir = tmp_root / "artifacts"
            eval_artifacts_dir = artifacts_dir
            receipt_path = tmp_root / "verify-receipt.json"
            try:
                request_path, pinned = _stage_verify_workspace(
                    work, spec, submission
                )
            except InvalidSubmissionError as exc:
                msg = str(exc)
                return build_receipt(
                    VERDICT_INVALID_SUBMISSION,
                    reasons=[msg],
                    invalid_reason=msg,
                )

            try:
                verify_ok, inspect_ok, v_receipt, inspect_report, v_failures = (
                    _run_verify_and_inspect(
                        work=work,
                        request_path=request_path,
                        artifacts_dir=artifacts_dir,
                        receipt_path=receipt_path,
                        spec=spec,
                        tools=tools,
                        env=env,
                        timeout=timeout_sec,
                        verify_runner=verify_runner,
                        inspect_runner=inspect_runner,
                    )
                )
            except Exception:
                _verify_tree_hashes(work, pinned)
                raise
            eval_verify_ok = verify_ok
            eval_inspect_ok = inspect_ok
            eval_v_receipt = v_receipt
            eval_inspect_report = inspect_report
            eval_capture_manifest = _load_capture_manifest(artifacts_dir)
            _verify_tree_hashes(work, pinned)

            oracle_status = "not_applicable"
            fault_class: str | None = None
            oracle_detail = ""
            if spec.kind == "CODE_AND_PROOF_HACK":
                inputs = list(DEFAULT_S2_INPUTS)
                for arg in submission.witness_args:
                    if arg not in inputs:
                        inputs.append(arg)
                src_files = {
                    rel: data
                    for rel, data in submission.files.items()
                    if rel.startswith("src/")
                }
                try:
                    oracle_status, fault_class, oracle_detail = _run_s2_code_oracle(
                        tmp_root=tmp_root,
                        src_files=src_files,
                        inputs=inputs,
                        env=env,
                        timeout=timeout_sec,
                        sysroot=tools.get("sysroot"),
                        bwrap=resolved_bwrap,
                        miri_runner=miri_runner,
                        rustc_runner=rustc_runner,
                    )
                except InvalidSubmissionError as exc:
                    _verify_tree_hashes(work, pinned)
                    msg = str(exc)
                    return build_receipt(
                        VERDICT_INVALID_SUBMISSION,
                        reasons=[msg],
                        invalid_reason=msg,
                    )
                except Exception:
                    _verify_tree_hashes(work, pinned)
                    raise
                _verify_tree_hashes(work, pinned)
                eval_oracle_status = oracle_status
                eval_fault_class = fault_class
                eval_oracle_detail = oracle_detail or None

            both_ok = verify_ok and inspect_ok
            capture_manifest = eval_capture_manifest
            evidence_tier = TIER_NONE
            patch_verified = False
            pres_gate_passed: bool | None = None
            human_review = False
            proposed_sev: str | None = None
            invalid_reason: str | None = None

            if spec.kind == "PROOF_HACK":
                oracle_confirmed = True
                verdict = (
                    VERDICT_ATTACKER_WON if both_ok else VERDICT_DEFENDER_HELD
                )
                if verdict == VERDICT_ATTACKER_WON:
                    evidence_tier = TIER_DEFENDER_FIXED_BUG
                    proposed_sev = "P0"
                reasons = (
                    ["strict verify + inspect accepted proof on broken target"]
                    if both_ok
                    else v_failures
                )
            elif spec.kind == "CODE_AND_PROOF_HACK":
                oracle_confirmed = oracle_status in (
                    "ub_confirmed",
                    "spec_violation_confirmed",
                )
                if oracle_confirmed and both_ok:
                    verdict = VERDICT_ATTACKER_WON
                    evidence_tier = TIER_EXECUTABLE_ORACLE
                    proposed_sev = "P0"
                    reasons = [
                        f"oracle confirmed {fault_class} ({oracle_detail}) "
                        "and strict verify + inspect passed"
                    ]
                elif both_ok and oracle_status == "compile_error":
                    verdict = VERDICT_INVALID_SUBMISSION
                    msg = (
                        "strict verify + inspect passed cleanly, but Scenario 2 code oracle "
                        f"failed to compile ({oracle_detail})"
                    )
                    invalid_reason = msg
                    reasons = [msg]
                elif both_ok and submission.has_e1:
                    eval_e1_patch_diff = submission.files[
                        "incorrectness/semantics.patch"
                    ].decode("utf-8", errors="replace")
                    e1_res = _evaluate_s2_lean_patch_proof(
                        tmp_root=tmp_root,
                        anneal_root=root,
                        spec=spec,
                        submission=submission,
                        artifacts_dir=artifacts_dir,
                        tools=tools,
                        env=env,
                        timeout=timeout_sec,
                        bwrap=resolved_bwrap,
                        e1_runner=e1_runner,
                    )
                    eval_e1_pres_summary = {
                        "reference_target_verified": e1_res.reference_target_verified,
                        "theory_canaries_verified": e1_res.theory_canaries_verified,
                        "preservation_gate_passed": e1_res.preservation_passed,
                        "detail": e1_res.detail,
                    }
                    eval_e1_proof_audit = e1_res.patch_audit
                    pres_gate_passed = e1_res.preservation_passed
                    if e1_res.passed and e1_res.preservation_passed is True:
                        verdict = VERDICT_NEEDS_HUMAN_REVIEW
                        evidence_tier = TIER_LEAN_PATCH_PROOF
                        patch_verified = True
                        human_review = True
                        proposed_sev = "P1"
                        reasons = [e1_res.detail]
                    else:
                        verdict = VERDICT_DEFENDER_HELD
                        evidence_tier = TIER_NONE
                        reasons = [e1_res.detail]
                elif both_ok and submission.has_e2:
                    verdict = VERDICT_NEEDS_HUMAN_REVIEW
                    evidence_tier = TIER_PROSE_CLAIM
                    human_review = True
                    proposed_sev = "P2"
                    reasons = [
                        "unpatched strict verify + inspect passed cleanly without "
                        "oracle or Lean patch-proof confirmation; queued E2 "
                        "incorrectness/claim.md for human review"
                    ]
                elif not both_ok:
                    verdict = VERDICT_DEFENDER_HELD
                    if not oracle_confirmed and oracle_status != "clean":
                        reasons = [
                            f"flawed/unverified submission rejected by Anneal (code oracle: {oracle_status}: "
                            f"{oracle_detail})"
                        ] + v_failures
                    else:
                        reasons = [
                            f"flawed code ({fault_class or oracle_status}) rejected by Anneal"
                        ] + v_failures
                elif oracle_status == "oracle_timeout":
                    verdict = VERDICT_HARNESS_ERROR
                    msg = (
                        "strict verify + inspect passed cleanly, but Scenario 2 "
                        f"code oracle timed out ({oracle_detail})"
                    )
                    invalid_reason = msg
                    reasons = [msg]
                else:
                    verdict = VERDICT_DEFENDER_HELD
                    reasons = [
                        f"code oracle did not confirm flaw ({oracle_status}: "
                        f"{oracle_detail})"
                    ] + v_failures
            elif spec.kind == "SPEC_PREFLIGHT_HACK":
                anomalies = dedup.extract_receipt_anomalies(v_receipt)
                s3_ast_tags: list[str] = []
                if not both_ok:
                    oracle_confirmed = bool(anomalies)
                    verdict = VERDICT_DEFENDER_HELD
                    reasons = v_failures
                else:
                    lean_texts = {
                        p: d.decode("utf-8", errors="replace")
                        for p, d in submission.files.items()
                    }
                    ast_parse_errs: list[str] = []
                    ast_timeout = max(timeout_sec, 90)
                    try:
                        leaked = _detect_disallowed_lean_constructs_with_tools(
                            lean_texts,
                            allow_theory_import_all=False,
                            allow_spec_options=True,
                            lean_bin=tools.get("lean"),
                            env=env,
                            bwrap=resolved_bwrap,
                            allow_fallback=(verify_runner is not None),
                            timeout=ast_timeout,
                            parse_errors_out=ast_parse_errs,
                            anneal_root=root,
                        )
                    except subprocess.TimeoutExpired as exc:
                        raise OracleInfrastructureError(
                            "defender Lean AST inspector timed out on accepted "
                            f"submission after {ast_timeout}s"
                        ) from exc
                    s3_ast_tags = leaked
                    oracle_confirmed = bool(leaked or anomalies)
                    if oracle_confirmed:
                        verdict = VERDICT_ATTACKER_WON
                        evidence_tier = TIER_DEFENDER_FIXED_BUG
                        proposed_sev = "P0"
                        tag_desc = ", ".join(leaked) if leaked else ", ".join(anomalies)
                        reasons = [
                            "SpecPreflight admitted disallowed syntax/axioms "
                            f"({tag_desc}) and verify + inspect passed"
                        ]
                    elif ast_parse_errs:
                        raise OracleInfrastructureError(
                            "defender Lean AST inspector failed to parse accepted "
                            f"submission ({', '.join(ast_parse_errs)})"
                        )
                    else:
                        verdict = VERDICT_DEFENDER_HELD
                        reasons = [
                            "verify passed only without forbidden syntax or "
                            "axiom bypass"
                        ]
            else:
                raise OracleInfrastructureError(
                    f"unhandled scenario kind {spec.kind!r}"
                )

            eval_oracle_confirmed = oracle_confirmed
            dedup_obj = (
                dedup.compute_dedup_metadata(
                    scenario_id=spec.scenario_id,
                    scenario_kind=spec.kind,
                    submission_files=submission.files,
                    receipt=v_receipt,
                    inspect_report=inspect_report,
                    oracle_fault_class=fault_class,
                    incorrectness_evidence_tier=evidence_tier,
                    ast_disallowed_tags=(
                        s3_ast_tags if spec.kind == "SPEC_PREFLIGHT_HACK" else ()
                    ),
                )
                if verdict in (VERDICT_ATTACKER_WON, VERDICT_NEEDS_HUMAN_REVIEW)
                else None
            )
            traces = _build_trace_artifacts(
                tmp_root=tmp_root,
                private_roots=_current_private_roots(),
                verify_receipt=v_receipt,
                inspect_report=inspect_report,
                capture_manifest=capture_manifest,
                artifacts_dir=artifacts_dir,
                code_oracle_diagnostic=oracle_detail or None,
                tool_stderr_snippet="; ".join(v_failures) if v_failures else None,
                attacker_hashes=attacker_hashes,
                incorrectness_patch_diff=eval_e1_patch_diff,
                preservation_canary_summary=eval_e1_pres_summary,
                incorrectness_proof_audit=eval_e1_proof_audit,
                incorrectness_claim=eval_e2_claim,
            )
            return build_receipt(
                verdict,
                reasons=reasons,
                invalid_reason=invalid_reason,
                defender_integrity_ok=True,
                sandbox_escape_detected=False,
                oracle_incorrect_confirmed=oracle_confirmed,
                incorrectness_evidence_tier=evidence_tier,
                patch_incorrectness_verified=patch_verified,
                preservation_gate_passed=pres_gate_passed,
                human_review_required=human_review,
                proposed_severity=proposed_sev,
                anneal_verify_ok=verify_ok,
                anneal_inspect_ok=inspect_ok,
                code_oracle_status=oracle_status,
                oracle_fault_class=fault_class,
                verify_receipt=v_receipt,
                inspect_report=inspect_report,
                dedup_obj=dedup_obj,
                trace_artifacts=traces,
            )
    except DefenderTamperError as exc:
        msg = str(exc)
        dedup_obj = dedup.compute_dedup_metadata(
            scenario_id=spec.scenario_id,
            scenario_kind=spec.kind,
            submission_files=submission.files,
            receipt=eval_v_receipt or eval_audit_json,
            inspect_report=eval_inspect_report,
            oracle_fault_class=eval_fault_class,
            incorrectness_evidence_tier=TIER_SANDBOX_ESCAPE,
            sandbox_escape_detected=True,
            tampered_paths=exc.tampered_paths,
        )
        traces = _build_trace_artifacts(
            tmp_root=eval_tmp_root,
            private_roots=_current_private_roots(),
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            audit_report=eval_audit_json,
            capture_manifest=eval_capture_manifest,
            artifacts_dir=eval_artifacts_dir,
            code_oracle_diagnostic=eval_oracle_detail,
            tool_stderr_snippet=msg,
            sandbox_escape_paths=exc.tampered_paths,
            attacker_hashes=attacker_hashes,
            incorrectness_patch_diff=eval_e1_patch_diff,
            preservation_canary_summary=eval_e1_pres_summary,
            incorrectness_proof_audit=eval_e1_proof_audit,
            incorrectness_claim=eval_e2_claim,
        )
        return build_receipt(
            VERDICT_ATTACKER_WON,
            reasons=[msg],
            defender_integrity_ok=False,
            sandbox_escape_detected=True,
            escape_mechanism="sandbox_escape",
            oracle_incorrect_confirmed=True,
            incorrectness_evidence_tier=TIER_SANDBOX_ESCAPE,
            proposed_severity="P0",
            anneal_verify_ok=eval_verify_ok,
            anneal_inspect_ok=eval_inspect_ok,
            code_oracle_status=eval_oracle_status,
            oracle_fault_class=eval_fault_class,
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            dedup_obj=dedup_obj,
            trace_artifacts=traces,
        )
    except InvalidSubmissionError as exc:
        msg = str(exc)
        traces = _build_trace_artifacts(
            tmp_root=eval_tmp_root,
            private_roots=_current_private_roots(),
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            audit_report=eval_audit_json,
            capture_manifest=eval_capture_manifest,
            artifacts_dir=eval_artifacts_dir,
            code_oracle_diagnostic=eval_oracle_detail,
            tool_stderr_snippet=msg,
            attacker_hashes=attacker_hashes,
            incorrectness_patch_diff=eval_e1_patch_diff,
            preservation_canary_summary=eval_e1_pres_summary,
            incorrectness_proof_audit=eval_e1_proof_audit,
            incorrectness_claim=eval_e2_claim,
        )
        return build_receipt(
            VERDICT_INVALID_SUBMISSION,
            reasons=[msg],
            invalid_reason=msg,
            defender_integrity_ok=True,
            sandbox_escape_detected=False,
            oracle_incorrect_confirmed=eval_oracle_confirmed,
            anneal_verify_ok=eval_verify_ok,
            anneal_inspect_ok=eval_inspect_ok,
            code_oracle_status=eval_oracle_status,
            oracle_fault_class=eval_fault_class,
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            trace_artifacts=traces,
        )
    except (
        OracleInfrastructureError,
        OSError,
        subprocess.SubprocessError,
        RuntimeError,
        ValueError,
        TypeError,
        KeyError,
        IndexError,
        RecursionError,
        UnicodeError,
        LookupError,
    ) as exc:
        msg = str(exc)
        traces = _build_trace_artifacts(
            tmp_root=eval_tmp_root,
            private_roots=_current_private_roots(),
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            audit_report=eval_audit_json,
            capture_manifest=eval_capture_manifest,
            artifacts_dir=eval_artifacts_dir,
            code_oracle_diagnostic=eval_oracle_detail,
            tool_stderr_snippet=msg,
            attacker_hashes=attacker_hashes,
            incorrectness_patch_diff=eval_e1_patch_diff,
            preservation_canary_summary=eval_e1_pres_summary,
            incorrectness_proof_audit=eval_e1_proof_audit,
            incorrectness_claim=eval_e2_claim,
        )
        return build_receipt(
            VERDICT_HARNESS_ERROR,
            reasons=[msg],
            invalid_reason=msg,
            defender_integrity_ok=True,
            sandbox_escape_detected=False,
            oracle_incorrect_confirmed=eval_oracle_confirmed,
            anneal_verify_ok=eval_verify_ok,
            anneal_inspect_ok=eval_inspect_ok,
            code_oracle_status=eval_oracle_status,
            oracle_fault_class=eval_fault_class,
            verify_receipt=eval_v_receipt,
            inspect_report=eval_inspect_report,
            trace_artifacts=traces,
        )
    finally:
        _EXPLICIT_PRLIMIT_VAR.reset(prlimit_token)


def replay_tripwires(
    *,
    expected_bug_id: str | None = None,
    **evaluate_kwargs: Any,
) -> tuple[int, dict[str, Any]]:
    """Replay a candidate witness and assert reproducible exploit detection."""
    receipt = evaluate_submission(**evaluate_kwargs)
    verdict = receipt["verdict"]
    dedup_obj = receipt.get("dedup")
    actual_bug_id = dedup_obj.get("bug_id") if isinstance(dedup_obj, dict) else None
    matched_bug = (
        expected_bug_id is None
        or (actual_bug_id is not None and actual_bug_id == expected_bug_id)
    )
    reproduced = verdict == VERDICT_ATTACKER_WON and matched_bug
    payload = {
        "schema_version": REPLAY_SCHEMA,
        "reproduced": reproduced,
        "expected_bug_id": expected_bug_id,
        "receipt": receipt,
    }
    if verdict == VERDICT_HARNESS_ERROR:
        return 2, payload
    return (0 if reproduced else 1), payload


def _emit_json(data: dict[str, Any], json_out: Path | None) -> None:
    encoded = json.dumps(data, indent=2) + "\n"
    if json_out is not None:
        anneal_ci_lib.atomic_write_text(json_out, encoded)
    sys.stdout.write(encoded)


def _add_eval_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--scenario", required=True)
    sub_grp = parser.add_mutually_exclusive_group(required=True)
    sub_grp.add_argument("--submission-dir", type=Path)
    sub_grp.add_argument("--submission-tar", type=Path)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--anneal-root", type=Path)
    parser.add_argument("--cargo-anneal", dest="cli", type=Path)
    parser.add_argument("--capture", type=Path)
    parser.add_argument("--sysroot", type=Path)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--auditor", type=Path)
    parser.add_argument("--bwrap", type=Path)
    parser.add_argument("--prlimit", type=Path)
    parser.add_argument("--miri-sysroot", type=Path)
    parser.add_argument("--timeout-sec", type=int, default=300)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for Anneal red-teaming."""
    parser = argparse.ArgumentParser(
        prog="anneal-redteam",
        description="Trusted defender evaluation harness for Anneal.",
    )
    sub = parser.add_subparsers(dest="command", required=True)

    list_p = sub.add_parser("list-scenarios")
    list_p.add_argument("--json", action="store_true", required=True)

    eval_p = sub.add_parser("evaluate")
    _add_eval_args(eval_p)

    replay_p = sub.add_parser("replay-tripwires")
    _add_eval_args(replay_p)
    replay_p.add_argument("--expected-bug-id")

    args = parser.parse_args(argv)
    if args.command == "list-scenarios":
        _emit_json(scenarios.list_scenarios_manifest(), None)
        return 0

    if args.timeout_sec <= 0:
        sys.stderr.write(
            f"error: --timeout-sec must be positive, got {args.timeout_sec}\n"
        )
        return 2

    try:
        scenarios.get_scenario(args.scenario)
    except KeyError:
        sys.stderr.write(f"error: unknown scenario {args.scenario!r}\n")
        return 2

    common = {
        "scenario_id": args.scenario,
        "submission_dir": args.submission_dir,
        "submission_tar": args.submission_tar,
        "anneal_root": args.anneal_root,
        "cli": args.cli,
        "capture": args.capture,
        "sysroot": args.sysroot,
        "lean": args.lean,
        "auditor": args.auditor,
        "bwrap": args.bwrap,
        "prlimit": args.prlimit,
        "miri_sysroot": args.miri_sysroot,
        "timeout_sec": args.timeout_sec,
    }
    if args.command == "evaluate":
        receipt = evaluate_submission(**common)
        _emit_json(receipt, args.json_out)
        return 2 if receipt["verdict"] == VERDICT_HARNESS_ERROR else 0

    rc, replay_payload = replay_tripwires(
        expected_bug_id=args.expected_bug_id, **common
    )
    _emit_json(replay_payload, args.json_out)
    return rc


if __name__ == "__main__":
    sys.exit(main())
