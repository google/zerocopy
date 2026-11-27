#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""CI driver for Stage-1 and Stage-2 MIR differential oracle checks.

Runs `anneal-diff run --json` against the Profile v1 litmus corpus and
`anneal-diff fuzz --json` for deterministic admitted-subset property fuzzing,
executes an optional explicit `--mir-eval-manifest` Leg-3 evaluator when
provided, and emits `anneal-semantic-detail/v1` plus `anneal-perf-record/v1`
telemetry.

Stage 0 Alpha — Not Yet Audited: empirical differential testing raises
confidence and uncovers divergences rather than proving universal soundness.

Threat model: runs assume a trusted single-tenant host and UID domain (CI jobs
/ `bwrap` sandboxes own OS/UID isolation; defending against concurrent
adversarial same-UID processes mutating `TMPDIR` or build/cache dirs mid-run
is explicitly out of scope).
"""

from __future__ import annotations

import argparse
from collections import deque
import contextlib
from dataclasses import dataclass
from datetime import datetime, timezone
import errno
import glob
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import signal
import stat
import struct
import subprocess
import sys
import tempfile
import tomllib
from typing import Any


DETAIL_SCHEMA = "anneal-semantic-detail/v1"
ALPHA_NOTICE = "Stage 0 Alpha — Not Yet Audited (this is alpha software!)"
REQUIRED_METRICS_KEYS = frozenset(
    {
        "compared_count",
        "pass_agreed_count",
        "ub_agreed_count",
        "conservative_unsupported_count",
        "kernel_checked_pass_count",
        "kernel_checked_ub_count",
        "unsound_missed_fault_count",
        "value_mismatch_count",
        "unexpected_conservative_count",
        "leg_divergence_count",
    }
)


_DIFF_CHILD_PATH_ENV_VARS = (
    "ANNEAL_CAPTURE",
    "ANNEAL_MVP_CAPTURE",
    "ANNEAL_CLI",
    "ANNEAL_MVP_CLI",
    "ANNEAL_AUDITOR",
    "ANNEAL_LEAN",
    "ANNEAL_MVP_LEAN",
    "ANNEAL_SYSROOT",
    "ANNEAL_TEST_RUST_SYSROOT",
    "ANNEAL_MVP_SYSROOT",
    "ANNEAL_TEST_INSTALL_ROOT",
    "ANNEAL_MIRI_SYSROOT",
    "ANNEAL_DIFF_CACHE_DIR",
    "CARGO_TARGET_DIR",
    "XDG_CACHE_HOME",
)

_DIFF_CHILD_EXECUTABLE_ENV_VARS = frozenset(
    {
        "ANNEAL_CAPTURE",
        "ANNEAL_MVP_CAPTURE",
        "ANNEAL_CLI",
        "ANNEAL_MVP_CLI",
        "ANNEAL_AUDITOR",
        "ANNEAL_LEAN",
        "ANNEAL_MVP_LEAN",
    }
)
_DIFF_CHILD_DIR_ENV_VARS = frozenset({"ANNEAL_MIRI_SYSROOT"})


def _anchor_search_path_list(raw: str, base_dir: Path) -> str:
    """Anchor relative entries inside `os.pathsep`-delimited search lists."""
    return os.pathsep.join(
        _anchor_env_path(entry or ".", base_dir)
        for entry in raw.split(os.pathsep)
    )

_STRIPPED_CHILD_ENV_VARS = (
    "ACTIONS_CACHE_URL",
    "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
    "ACTIONS_ID_TOKEN_REQUEST_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "ACTIONS_RUNTIME_URL",
    "GH_TOKEN",
    "GITHUB_TOKEN",
)

_STRIPPED_LOADER_ENV_VARS = (
    "BASH_ENV",
    "ENV",
    "GCONV_PATH",
    "GLIBC_TUNABLES",
    "HOSTALIASES",
    "LOCPATH",
)

_STRIPPED_LOADER_ENV_PREFIXES = (
    "LD_",
    "DYLD_",
)

_STRIPPED_CARGO_OVERRIDE_ENV_VARS = (
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "RUSTC_LINKER",
    "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS",
    "RUSTDOCFLAGS",
    "CARGO_ENCODED_RUSTDOCFLAGS",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTDOC",
    "CARGO_BUILD_RUSTDOC_WRAPPER",
    "CARGO_BUILD_TARGET_DIR",
)

_STRIPPED_CARGO_OVERRIDE_PREFIXES = (
    "CARGO_TARGET_",
    "CARGO_BUILD_",
    "CARGO_PROFILE_",
    "CARGO_UNSTABLE_",
    "CARGO_ENV_",
    "CARGO_REGISTRIES_",
    "CARGO_SOURCE_",
    "CARGO_ALIAS_",
    "CARGO_HTTP_",
)

_ALLOWED_CARGO_PREFIXED_ENV_VARS = frozenset(
    {
        "CARGO_TARGET_DIR",
        "CARGO_BUILD_JOBS",
    }
)


def _strip_cargo_override_env_vars(env: dict[str, str]) -> dict[str, str]:
    """Remove ambient Cargo/rustc runner, wrapper, and flag overrides."""
    for env_key in _STRIPPED_CARGO_OVERRIDE_ENV_VARS:
        env.pop(env_key, None)
    for env_key in list(env.keys()):
        if env_key in _ALLOWED_CARGO_PREFIXED_ENV_VARS:
            continue
        if any(env_key.startswith(pfx) for pfx in _STRIPPED_CARGO_OVERRIDE_PREFIXES):
            env.pop(env_key, None)
    return env

MIR_EVAL_MANIFEST_TIMEOUT_SECS = 300.0
ANNEAL_DIFF_SUBCOMMAND_TIMEOUT_SECS = 600.0


def _strip_child_credentials(env: dict[str, str]) -> dict[str, str]:
    """Remove GitHub Actions and API credential variables from child env."""
    for env_key in _STRIPPED_CHILD_ENV_VARS:
        env.pop(env_key, None)
    return env


def _strip_loader_env_vars(env: dict[str, str]) -> dict[str, str]:
    """Remove ambient dynamic-linker and shell-preload injection variables."""
    for env_key in _STRIPPED_LOADER_ENV_VARS:
        env.pop(env_key, None)
    for env_key in list(env.keys()):
        if any(
            env_key.startswith(pfx) for pfx in _STRIPPED_LOADER_ENV_PREFIXES
        ):
            env.pop(env_key, None)
    return env


def ensure_not_symlink(path: Path, label: str = "path") -> None:
    """Reject symlink inputs/outputs fail-closed."""
    if path.is_symlink():
        raise ValueError(f"{label} must not be a symlink: {path}")


_STORE_PREFIX = Path("/nix/store")


def _resolve_store_contained_entry(
    path: Path,
    label: str,
    *,
    store_prefix: Path | None = None,
    base_dir: Path | None = None,
    expect_dir: bool = False,
) -> Path | None:
    """Return canonical `/nix/store` path when `path` stays strictly inside."""
    if ".." in path.parts:
        return None
    eff_store = _STORE_PREFIX if store_prefix is None else store_prefix
    anchor = Path.cwd() if base_dir is None else base_dir
    abs_path = path if path.is_absolute() else (anchor.absolute() / path)
    try:
        store_st = os.lstat(eff_store)
    except OSError:
        return None
    if stat.S_ISLNK(store_st.st_mode) or not stat.S_ISDIR(store_st.st_mode):
        return None
    try:
        canon_store = _resolve_cli_path(
            eff_store,
            "store root",
            base_dir=anchor,
            require_dir_components=True,
        ).resolve(strict=True)
    except (OSError, ValueError):
        return None

    in_store = (
        abs_path == eff_store
        or abs_path.is_relative_to(eff_store)
        or abs_path.is_relative_to(canon_store)
    )
    # Reject hardlinked non-dir/symlink hops before checking store containment.
    if abs_path.is_absolute():
        walk = Path(abs_path.anchor)
        for part in abs_path.parts[1:]:
            if part in ("", "."):
                continue
            walk = walk / part
            try:
                wst = os.lstat(walk)
            except OSError:
                break
            if not stat.S_ISDIR(wst.st_mode) and wst.st_nlink > 1:
                if in_store:
                    raise _HardlinkedCommandError(
                        f"{label} must not be a hardlink "
                        f"(nlink={wst.st_nlink}): {walk}"
                    )
                return None

    try:
        canon = abs_path.resolve(strict=True)
    except FileNotFoundError:
        return None
    except OSError as exc:
        if in_store:
            raise ValueError(
                f"cannot canonicalize {label} {abs_path}: {exc}"
            ) from exc
        return None
    if canon == canon_store or not canon.is_relative_to(canon_store):
        if in_store:
            raise ValueError(
                f"{label} symlink escaped store {canon_store}: "
                f"{abs_path} -> {canon}"
            )
        return None

    cur = canon_store
    rel_parts = canon.relative_to(canon_store).parts
    for idx, part in enumerate(rel_parts):
        cur = cur / part
        is_last = idx + 1 == len(rel_parts)
        try:
            st = os.lstat(cur)
        except OSError as exc:
            raise ValueError(f"cannot inspect {label} {cur}: {exc}") from exc
        if (
            (is_last and not expect_dir) or not stat.S_ISDIR(st.st_mode)
        ) and st.st_nlink > 1:
            raise _HardlinkedCommandError(
                f"{label} must not be a hardlink "
                f"(nlink={st.st_nlink}): {cur}"
            )
        if stat.S_ISLNK(st.st_mode):
            try:
                step_canon = cur.resolve(strict=True)
            except OSError as exc:
                raise ValueError(
                    f"cannot canonicalize {label} {cur}: {exc}"
                ) from exc
            if step_canon == canon_store or not step_canon.is_relative_to(
                canon_store
            ):
                raise ValueError(
                    f"{label} symlink escaped store {canon_store}: "
                    f"{cur} -> {step_canon}"
                )

    try:
        canon_st = os.lstat(canon)
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {canon}: {exc}") from exc
    if stat.S_ISLNK(canon_st.st_mode):
        raise ValueError(f"{label} canonical target is a symlink: {canon}")
    if expect_dir:
        if not stat.S_ISDIR(canon_st.st_mode):
            raise ValueError(f"{label} is not a directory: {canon}")
    else:
        if not stat.S_ISREG(canon_st.st_mode):
            raise ValueError(
                f"{label} target is not a regular file: {canon}"
            )
        if canon_st.st_nlink > 1:
            raise _HardlinkedCommandError(
                f"{label} target must not be a hardlink "
                f"(nlink={canon_st.st_nlink}): {canon}"
            )
    return canon


def _resolve_cli_path(
    path: Path,
    label: str = "path",
    *,
    base_dir: Path | None = None,
    require_dir_components: bool = False,
) -> Path:
    """Anchor `path` to `base_dir` (or `Path.cwd()`) and reject symlinks."""
    anchor = Path.cwd() if base_dir is None else base_dir
    if path.is_absolute():
        cur = Path(path.anchor)
        rel_parts = path.parts[1:]
    else:
        ensure_not_symlink(anchor, label)
        cur = anchor.resolve(strict=False)
        rel_parts = path.parts
    for idx, part in enumerate(rel_parts):
        if part in ("", "."):
            ensure_not_symlink(cur, label)
            if require_dir_components and cur.exists() and not cur.is_dir():
                raise ValueError(f"{label} component is not a directory: {cur}")
        elif part == "..":
            raise ValueError(
                f"{label} must not contain parent traversal ('..'): {path}"
            )
        else:
            cur = cur / part
            if (
                sys.platform == "darwin"
                and idx + 1 < len(rel_parts)
                and cur in (Path("/var"), Path("/tmp"), Path("/etc"))
            ):
                cur = cur.resolve(strict=False)
                continue
            ensure_not_symlink(cur, label)
            if require_dir_components and cur.exists() and not cur.is_dir():
                raise ValueError(f"{label} component is not a directory: {cur}")
    if cur.name in ("", "."):
        resolved = cur.resolve(strict=False)
    else:
        resolved = cur.parent.resolve(strict=False) / cur.name
    ensure_not_symlink(resolved, label)
    if require_dir_components and resolved.exists() and not resolved.is_dir():
        raise ValueError(f"{label} must be a directory: {resolved}")
    return resolved


def _workspace_target_roots(work_dir: Path) -> tuple[Path, ...]:
    roots = [work_dir]
    for anc in work_dir.parents:
        manifest = anc / "Cargo.toml"
        try:
            st = os.lstat(manifest)
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(st.st_mode):
            raise ValueError(f"ancestor Cargo.toml must not be a symlink: {manifest}")
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"ancestor Cargo.toml is not a regular file: {manifest}")
        if hasattr(st, "st_nlink") and st.st_nlink > 1:
            raise ValueError(
                f"ancestor Cargo.toml must not be a hardlink (nlink={st.st_nlink}): "
                f"{manifest}"
            )
        roots.append(anc)
    return tuple(roots)


def _validate_cargo_target_dirs(
    env: dict[str, str],
    *,
    base_dir: Path,
    default_target_roots: tuple[Path, ...] = (),
) -> Path | None:
    """Validate `CARGO_TARGET_DIR` (or default `target/`) components fail-closed."""
    raw_td = env.get("CARGO_TARGET_DIR")
    if raw_td:
        return _resolve_cli_path(
            Path(raw_td),
            "CARGO_TARGET_DIR",
            base_dir=base_dir,
            require_dir_components=True,
        )
    for root in default_target_roots:
        _resolve_cli_path(
            root / "target",
            "cargo target dir",
            base_dir=root,
            require_dir_components=True,
        )
    return None


def _resolve_optional_cli_path(
    path: Path | None,
    label: str,
    *,
    base_dir: Path | None = None,
    reject_hardlinks: bool = False,
    allow_cargo_deps_hardlink: bool = False,
) -> Path | None:
    if path is None:
        return None
    if reject_hardlinks:
        anchor = Path.cwd() if base_dir is None else base_dir
        return _resolve_executable_cli_path(
            path,
            label,
            base_dir=anchor,
            allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
        )
    return _resolve_cli_path(path, label, base_dir=base_dir)


def _anchor_env_path(raw: str, base_dir: Path) -> str:
    """Anchor a relative environment path without following leaf symlinks."""
    p = Path(raw)
    if p.is_absolute():
        return raw
    anchored = base_dir / p
    if anchored.name in ("", ".", ".."):
        return os.path.abspath(anchored)
    return str(anchored.parent.resolve(strict=False) / anchored.name)


class _HardlinkedCommandError(ValueError):
    """Raised when a resolved command executable has multiple hardlinks."""


def _is_verified_elan_bin_proxy(
    clean_dir: Path, clean_cand: Path, clean_st: os.stat_result, base_dir: Path
) -> bool:
    """Allow an unmodified `elan` multiplexer hardlink under `$ELAN_HOME/bin`."""
    raw_eh = os.environ.get("ELAN_HOME")
    elan_base = Path(raw_eh) if raw_eh else Path.home() / ".elan"
    try:
        expected_bin = _resolve_cli_path(
            elan_base / "bin",
            "ELAN_HOME bin",
            base_dir=base_dir,
            require_dir_components=True,
        ).resolve(strict=False)
    except ValueError:
        return False
    if clean_dir.resolve(strict=False) != expected_bin:
        return False
    elan_sib = clean_dir / "elan"
    try:
        elan_st = os.lstat(elan_sib)
    except OSError:
        return False
    return (
        not stat.S_ISLNK(elan_st.st_mode)
        and stat.S_ISREG(elan_st.st_mode)
        and (elan_st.st_dev, elan_st.st_ino) == (clean_st.st_dev, clean_st.st_ino)
    )


@dataclass
class _OpenedExecutable:
    path: Path
    fd: int | None
    st: os.stat_result | None
    parent_fd: int | None
    is_rustup_proxy: bool = False


def _close_fd_quiet(fd: int) -> None:
    try:
        os.close(fd)
    except OSError:
        pass


def _open_verified_executable_via_dirfd(
    file_path: Path,
    base_dir: Path,
    *,
    reject_hardlinks: bool,
    allow_cargo_deps_hardlink: bool = False,
    label: str,
    exit_stack: contextlib.ExitStack,
) -> _OpenedExecutable:
    if ".." in file_path.parts:
        raise ValueError(
            f"{label} must not contain parent traversal ('..'): {file_path}"
        )
    joined = file_path if file_path.is_absolute() else (base_dir.absolute() / file_path)
    if ".." in joined.parts:
        raise ValueError(
            f"{label} must not contain parent traversal ('..'): {file_path}"
        )
    if os.name != "posix":
        resolved = _resolve_executable_cli_path(
            file_path,
            label,
            base_dir=base_dir,
            allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
        )
        return _OpenedExecutable(
            path=resolved,
            fd=None,
            st=os.lstat(resolved),
            parent_fd=None,
        )
    leaf = joined.name
    if not leaf or leaf in (".", ".."):
        raise ValueError(f"{label} is not a regular file: {joined}")
    parent_fd = _open_dir_handle_no_symlinks(joined.parent, label)
    exit_stack.callback(_close_fd_quiet, parent_fd)
    fd, st = _open_regular_file_from_fd(
        parent_fd,
        leaf,
        None,
        allow_hardlink=True,
        label=label,
    )
    exit_stack.callback(_close_fd_quiet, fd)
    if reject_hardlinks and st.st_nlink > 1:
        if (
            allow_cargo_deps_hardlink
            and st.st_nlink == 2
            and _has_verified_cargo_hardlink_partner_fd(
                parent_fd, leaf, (st.st_dev, st.st_ino)
            )
        ):
            pass
        else:
            raise _HardlinkedCommandError(
                f"{label} must not be a hardlink (nlink={st.st_nlink}): {joined}"
            )
    try:
        canon = joined.resolve(strict=True)
        canon_st = os.lstat(canon)
    except OSError as exc:
        raise ValueError(
            f"{label} ancestor changed concurrently during validation: {joined}: {exc}"
        ) from exc
    if (canon_st.st_dev, canon_st.st_ino) != (st.st_dev, st.st_ino):
        raise ValueError(
            f"{label} ancestor changed concurrently during validation: {joined}"
        )
    return _OpenedExecutable(path=canon, fd=fd, st=st, parent_fd=parent_fd)


def _open_store_aware_executable(
    raw_path: Path,
    label: str,
    *,
    base_dir: Path,
    allow_cargo_deps_hardlink: bool = False,
    store_prefix: Path | None = None,
    exit_stack: contextlib.ExitStack,
) -> _OpenedExecutable:
    eff_store = _STORE_PREFIX if store_prefix is None else store_prefix
    if ".." not in raw_path.parts:
        store_cand = _resolve_store_contained_entry(
            raw_path, label, store_prefix=eff_store, base_dir=base_dir
        )
        if store_cand is not None:
            return _OpenedExecutable(
                path=store_cand, fd=None, st=None, parent_fd=None
            )
    return _open_verified_executable_via_dirfd(
        raw_path,
        base_dir,
        reject_hardlinks=True,
        allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
        label=label,
        exit_stack=exit_stack,
    )


def _resolve_command_from_path_opened(
    raw_cmd: str,
    base_dir: Path,
    *,
    allow_rustup_proxy: bool,
    allow_elan_proxy: bool = False,
    store_prefix: Path = _STORE_PREFIX,
    path_var: str | None = None,
    exit_stack: contextlib.ExitStack | None = None,
) -> _OpenedExecutable | None:
    """Resolve bare `raw_cmd` via `PATH`, opening non-store executables via dirfd."""
    resolved_path_var = os.environ.get("PATH") if path_var is None else path_var
    if not resolved_path_var:
        return None
    for raw_entry in resolved_path_var.split(os.pathsep):
        if not raw_entry:
            continue
        dir_path = Path(raw_entry)
        lex_dir = (
            dir_path
            if dir_path.is_absolute()
            else (base_dir.absolute() / dir_path)
        )
        cand_lex = lex_dir / raw_cmd
        try:
            st = os.lstat(cand_lex)
        except (FileNotFoundError, NotADirectoryError):
            continue
        except OSError as exc:
            raise ValueError(
                f"cannot inspect command PATH candidate {cand_lex}: {exc}"
            ) from exc
        if not stat.S_ISLNK(st.st_mode) and stat.S_ISDIR(st.st_mode):
            continue

        try:
            clean_dir = _resolve_cli_path(
                dir_path,
                "command PATH entry",
                base_dir=base_dir,
                require_dir_components=True,
            )
        except ValueError:
            if ".." not in dir_path.parts:
                store_cand = _resolve_store_contained_entry(
                    cand_lex,
                    f"{raw_cmd} PATH candidate",
                    store_prefix=store_prefix,
                    base_dir=base_dir,
                )
                if store_cand is not None:
                    return _OpenedExecutable(
                        path=store_cand, fd=None, st=None, parent_fd=None
                    )
            raise
        clean_cand = clean_dir / raw_cmd
        try:
            clean_st = os.lstat(clean_cand)
        except (FileNotFoundError, NotADirectoryError):
            continue
        except OSError as exc:
            raise ValueError(
                f"cannot inspect command PATH candidate {clean_cand}: {exc}"
            ) from exc
        if stat.S_ISLNK(clean_st.st_mode):
            if (
                allow_rustup_proxy
                and raw_cmd in ("cargo", "rustc")
                and os.readlink(clean_cand) == "rustup"
            ):
                rustup_path = clean_dir / "rustup"
                if exit_stack is not None:
                    try:
                        opened_rustup = _open_verified_executable_via_dirfd(
                            rustup_path,
                            base_dir,
                            reject_hardlinks=True,
                            label=f"{raw_cmd} rustup proxy",
                            exit_stack=exit_stack,
                        )
                    except _HardlinkedCommandError:
                        raise
                    return _OpenedExecutable(
                        path=clean_cand,
                        fd=opened_rustup.fd,
                        st=opened_rustup.st,
                        parent_fd=opened_rustup.parent_fd,
                        is_rustup_proxy=True,
                    )
                checked_rustup = _resolve_cli_path(
                    rustup_path,
                    f"{raw_cmd} rustup proxy",
                    base_dir=base_dir,
                )
                try:
                    rustup_st = os.lstat(checked_rustup)
                except OSError as exc:
                    raise ValueError(
                        f"cannot inspect {raw_cmd} rustup proxy {checked_rustup}: {exc}"
                    ) from exc
                if not stat.S_ISREG(rustup_st.st_mode):
                    raise ValueError(
                        f"{raw_cmd} rustup proxy target is not a regular file: "
                        f"{checked_rustup}"
                    )
                if rustup_st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{raw_cmd} rustup proxy must not be a hardlink "
                        f"(nlink={rustup_st.st_nlink}): {checked_rustup}"
                    )
                return _OpenedExecutable(
                    path=clean_cand,
                    fd=None,
                    st=None,
                    parent_fd=None,
                    is_rustup_proxy=True,
                )
            store_cand = _resolve_store_contained_entry(
                clean_cand,
                f"{raw_cmd} PATH candidate",
                store_prefix=store_prefix,
                base_dir=base_dir,
            )
            if store_cand is not None:
                return _OpenedExecutable(
                    path=store_cand, fd=None, st=None, parent_fd=None
                )
            raise ValueError(f"command path must not be a symlink: {clean_cand}")
        if not stat.S_ISREG(clean_st.st_mode):
            raise ValueError(
                f"command path is not a regular file: {clean_cand}"
            )
        if clean_st.st_nlink > 1:
            if (
                allow_elan_proxy
                and raw_cmd == "lean"
                and _is_verified_elan_bin_proxy(
                    clean_dir, clean_cand, clean_st, base_dir
                )
            ):
                return _OpenedExecutable(
                    path=clean_cand, fd=None, st=clean_st, parent_fd=None
                )
            raise _HardlinkedCommandError(
                f"command path must not be a hardlink (nlink={clean_st.st_nlink}): "
                f"{clean_cand}"
            )
        if exit_stack is not None:
            return _open_verified_executable_via_dirfd(
                clean_cand,
                base_dir,
                reject_hardlinks=True,
                label="command path",
                exit_stack=exit_stack,
            )
        return _OpenedExecutable(
            path=clean_cand, fd=None, st=clean_st, parent_fd=None
        )
    return None


def _resolve_command_from_path(
    raw_cmd: str,
    base_dir: Path,
    *,
    allow_rustup_proxy: bool,
    allow_elan_proxy: bool = False,
    store_prefix: Path = _STORE_PREFIX,
    path_var: str | None = None,
) -> str | None:
    """Resolve bare `raw_cmd` via `PATH`, rejecting symlinks fail-closed."""
    resolved = _resolve_command_from_path_opened(
        raw_cmd,
        base_dir,
        allow_rustup_proxy=allow_rustup_proxy,
        allow_elan_proxy=allow_elan_proxy,
        store_prefix=store_prefix,
        path_var=path_var,
        exit_stack=None,
    )
    return None if resolved is None else str(resolved.path)


def _resolve_executable_cli_path(
    path: Path,
    label: str,
    *,
    base_dir: Path,
    allow_cargo_deps_hardlink: bool = False,
    store_prefix: Path | None = None,
) -> Path:
    eff_store = _STORE_PREFIX if store_prefix is None else store_prefix
    try:
        resolved = _resolve_cli_path(path, label, base_dir=base_dir)
    except ValueError:
        if ".." not in path.parts:
            store_cand = _resolve_store_contained_entry(
                path, label, store_prefix=eff_store, base_dir=base_dir
            )
            if store_cand is not None:
                return store_cand
        raise
    try:
        st = os.lstat(resolved)
    except FileNotFoundError:
        return resolved
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {resolved}: {exc}") from exc
    if stat.S_ISLNK(st.st_mode):
        store_cand = _resolve_store_contained_entry(
            resolved, label, store_prefix=eff_store, base_dir=base_dir
        )
        if store_cand is not None:
            return store_cand
        raise ValueError(f"{label} must not be a symlink: {resolved}")
    if not stat.S_ISREG(st.st_mode):
        raise ValueError(f"{label} is not a regular file: {resolved}")
    if st.st_nlink > 1:
        if allow_cargo_deps_hardlink and st.st_nlink == 2:
            canon = resolved.resolve(strict=True)
            if _has_verified_cargo_hardlink_partner(
                canon.parent, canon.name, (st.st_dev, st.st_ino)
            ):
                return canon
        raise _HardlinkedCommandError(
            f"{label} must not be a hardlink (nlink={st.st_nlink}): {resolved}"
        )
    return resolved


def _maybe_stage_cargo_hardlink_executable(
    bin_path: Path,
    bin_name: str,
    *,
    exit_stack: contextlib.ExitStack | None,
    base_dir: Path,
    tmp_parent: str | None = None,
    store_prefix: Path | None = None,
    preopened: _OpenedExecutable | None = None,
) -> Path:
    """Stage non-store Cargo/capture binaries into a pinned `0o555` TMPDIR."""
    eff_store = _STORE_PREFIX if store_prefix is None else store_prefix
    if preopened is not None and preopened.fd is None and preopened.st is None:
        return preopened.path
    store_cand = _resolve_store_contained_entry(
        bin_path, bin_name, store_prefix=eff_store, base_dir=base_dir
    )
    if store_cand is not None:
        return store_cand
    if exit_stack is None:
        raise ValueError(
            f"cannot stage non-store {bin_name} without ExitStack: {bin_path}"
        )
    return _stage_verified_executable(
        bin_path,
        bin_name,
        allow_cargo_deps_hardlink=True,
        exit_stack=exit_stack,
        base_dir=base_dir,
        tmp_parent=tmp_parent,
        store_prefix=eff_store,
        pin_proc_fd=True,
        preopened=preopened,
    )


def _resolve_cargo_executable_cli_path(
    path: Path, label: str, *, base_dir: Path
) -> Path:
    """Validate Cargo binary (rejecting symlinks and isolating Cargo deps)."""
    return _resolve_executable_cli_path(
        path, label, base_dir=base_dir, allow_cargo_deps_hardlink=True
    )


def _resolve_command_token_opened(
    raw_cmd: str,
    base_dir: Path,
    *,
    allow_rustup_proxy: bool = False,
    store_prefix: Path = _STORE_PREFIX,
    exit_stack: contextlib.ExitStack,
) -> _OpenedExecutable:
    """Resolve and open command tokens via dirfd where non-store."""
    if not raw_cmd or raw_cmd in (".", ".."):
        raise ValueError(
            f"command path must not be empty or dot-segment: {raw_cmd!r}"
        )
    if (
        os.sep in raw_cmd
        or (os.altsep and os.altsep in raw_cmd)
        or Path(raw_cmd).is_absolute()
    ):
        p = Path(raw_cmd)
        store_cand = _resolve_store_contained_entry(
            p, "command path", store_prefix=store_prefix, base_dir=base_dir
        )
        if store_cand is not None:
            return _OpenedExecutable(path=store_cand, fd=None, st=None, parent_fd=None)
        return _open_verified_executable_via_dirfd(
            p,
            base_dir,
            reject_hardlinks=True,
            label="command path",
            exit_stack=exit_stack,
        )
    resolved = _resolve_command_from_path_opened(
        raw_cmd,
        base_dir,
        allow_rustup_proxy=allow_rustup_proxy,
        store_prefix=store_prefix,
        exit_stack=exit_stack,
    )
    if resolved is None:
        raise ValueError(f"cannot resolve command {raw_cmd!r} in PATH")
    return resolved


def _resolve_command_token(
    raw_cmd: str,
    base_dir: Path,
    *,
    allow_rustup_proxy: bool = False,
) -> str:
    """Resolve command tokens and reject symlinks and hardlinks fail-closed."""
    if not raw_cmd or raw_cmd in (".", ".."):
        raise ValueError(
            f"command path must not be empty or dot-segment: {raw_cmd!r}"
        )
    if (
        os.sep in raw_cmd
        or (os.altsep and os.altsep in raw_cmd)
        or Path(raw_cmd).is_absolute()
    ):
        return str(
            _resolve_executable_cli_path(
                Path(raw_cmd), "command path", base_dir=base_dir
            )
        )
    resolved = _resolve_command_from_path(
        raw_cmd,
        base_dir,
        allow_rustup_proxy=allow_rustup_proxy,
    )
    if resolved is None:
        raise ValueError(f"cannot resolve command {raw_cmd!r} in PATH")
    return resolved


def _resolve_cargo_command_opened(
    base_dir: Path, exit_stack: contextlib.ExitStack
) -> _OpenedExecutable:
    raw_cargo = os.environ.get("CARGO")
    return _resolve_command_token_opened(
        raw_cargo or "cargo",
        base_dir,
        allow_rustup_proxy=not raw_cargo,
        exit_stack=exit_stack,
    )


def _resolve_cargo_command(base_dir: Path) -> str:
    """Resolve `CARGO` (default `"cargo"`) against `base_dir` or `PATH`."""
    raw_cargo = os.environ.get("CARGO")
    return _resolve_command_token(
        raw_cargo or "cargo",
        base_dir,
        allow_rustup_proxy=not raw_cargo,
    )


def _git_metadata(
    repo_root: Path,
    *,
    allow_unknown_git: bool = False,
    commit_sha_override: str | None = None,
    commit_unix_ts_override: int | None = None,
    branch_override: str | None = None,
) -> tuple[str, str, int]:
    """Return `(branch, commit_sha, commit_unix_ts)`, failing closed."""
    if (commit_sha_override is None) != (commit_unix_ts_override is None):
        raise ValueError(
            "commit_sha_override and commit_unix_ts_override must be provided together"
        )
    if (
        commit_sha_override is not None
        and commit_unix_ts_override is not None
        and branch_override
    ):
        return branch_override, commit_sha_override.lower(), commit_unix_ts_override

    child_env = _strip_loader_env_vars(
        _strip_cargo_override_env_vars(
            _strip_child_credentials(os.environ.copy())
        )
    )
    sha_ok = False
    br_ok = False
    ts_ok = False
    sha = ""
    branch = ""
    ts_val = 0
    try:
        sha_out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        br_out = subprocess.run(
            ["git", "-C", str(repo_root), "rev-parse", "--abbrev-ref", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        ts_out = subprocess.run(
            ["git", "-C", str(repo_root), "show", "-s", "--format=%ct", "HEAD"],
            env=child_env,
            capture_output=True,
            text=True,
            check=False,
        )
        raw_sha = sha_out.stdout.strip()
        sha_ok = (
            sha_out.returncode == 0
            and len(raw_sha) == 40
            and all(c in "0123456789abcdefABCDEF" for c in raw_sha)
        )
        if sha_ok:
            sha = raw_sha.lower()
        raw_br = br_out.stdout.strip()
        br_ok = br_out.returncode == 0 and bool(raw_br)
        if br_ok:
            branch = raw_br
        raw_ts = ts_out.stdout.strip()
        ts_ok = ts_out.returncode == 0 and raw_ts.isdigit()
        if ts_ok:
            ts_val = int(raw_ts)
    except OSError as exc:
        if (
            not allow_unknown_git
            and (
                commit_sha_override is None
                or commit_unix_ts_override is None
                or not branch_override
            )
        ):
            raise RuntimeError(
                f"git metadata query failed in {repo_root}: {exc}"
            ) from exc

    final_sha = (
        commit_sha_override.lower()
        if commit_sha_override is not None
        else (sha if sha_ok else ("0" * 40 if allow_unknown_git else ""))
    )
    final_branch = (
        branch_override
        if branch_override
        else (branch if br_ok else ("unknown" if allow_unknown_git else ""))
    )
    if commit_unix_ts_override is not None:
        final_ts: int | None = commit_unix_ts_override
    elif ts_ok:
        final_ts = ts_val
    elif allow_unknown_git:
        final_ts = 0
    else:
        final_ts = None

    if final_sha and final_branch and final_ts is not None:
        return final_branch, final_sha, final_ts
    raise RuntimeError(
        f"missing valid git HEAD metadata in {repo_root} (pass --allow-unknown-git or explicit revision flags)"
    )


def _extract_proc_fd_numbers(
    cmd: list[str],
    env: dict[str, str] | None = None,
    *,
    cwd: Path | None = None,
) -> tuple[int, ...]:
    """Return verified open staging directory fds referenced by `/proc/self/fd`."""
    if not sys.platform.startswith("linux"):
        return ()
    tokens = list(cmd)
    if cwd is not None:
        tokens.append(str(cwd))
    if env is not None:
        for val in env.values():
            tokens.extend(val.split(os.pathsep))
    fds: set[int] = set()
    prefix = "/proc/self/fd/"
    for tok in tokens:
        if not tok.startswith(prefix):
            continue
        rest = tok[len(prefix) :]
        fd_str = rest.split("/", 1)[0]
        if not fd_str.isdigit():
            continue
        fd_num = int(fd_str)
        if fd_num <= 2:
            continue
        try:
            st = os.fstat(fd_num)
        except OSError:
            continue
        if stat.S_ISDIR(st.st_mode):
            fds.add(fd_num)
    return tuple(sorted(fds))


def _tool_version(
    cmd: list[str], *, extra_lib_dir: Path | None = None
) -> str:
    probe_env = _strip_loader_env_vars(
        _strip_cargo_override_env_vars(
            _strip_child_credentials(os.environ.copy())
        )
    )
    if extra_lib_dir is not None:
        probe_env["LD_LIBRARY_PATH"] = str(extra_lib_dir)
    run_kwargs: dict[str, Any] = {
        "env": probe_env,
        "capture_output": True,
        "text": True,
        "timeout": 10.0,
        "check": False,
    }
    pass_fds = _extract_proc_fd_numbers(cmd, probe_env)
    if pass_fds:
        run_kwargs["pass_fds"] = pass_fds
    try:
        res = subprocess.run(cmd, **run_kwargs)
        if res.returncode == 0 and res.stdout.strip():
            return res.stdout.strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError):
        pass
    return "unknown"


def _resolve_explicit_lean_override(
    raw_lean: str, env_key: str, base_dir: Path
) -> str:
    """Resolve `ANNEAL*_LEAN` via path or `PATH`, rejecting symlinks/hardlinks."""
    if (
        os.sep in raw_lean
        or (os.altsep and os.altsep in raw_lean)
        or Path(raw_lean).is_absolute()
        or (base_dir / raw_lean).exists()
        or (base_dir / raw_lean).is_symlink()
    ):
        return str(
            _resolve_executable_cli_path(
                Path(raw_lean), env_key, base_dir=base_dir
            )
        )
    return _resolve_command_token(raw_lean, base_dir)


def _find_cached_lean(
    toolchain_parent: Path, *, base_dir: Path
) -> Path | None:
    try:
        entries = sorted(toolchain_parent.iterdir())
    except OSError:
        return None
    for entry in entries:
        cand = entry / "lean" / "bin" / "lean"
        try:
            os.lstat(cand)
        except OSError:
            continue
        resolved = _resolve_executable_cli_path(
            cand, "cached lean", base_dir=base_dir
        )
        if resolved.is_file():
            return resolved
    return None


def _resolve_store_aware_dir_cli_path(
    dir_path: Path,
    label: str,
    *,
    base_dir: Path,
    store_prefix: Path | None = None,
) -> Path:
    try:
        return _resolve_cli_path(
            dir_path, label, base_dir=base_dir, require_dir_components=True
        )
    except ValueError:
        if ".." not in dir_path.parts:
            store_dir = _resolve_store_contained_entry(
                dir_path,
                label,
                store_prefix=store_prefix,
                base_dir=base_dir,
                expect_dir=True,
            )
            if store_dir is not None:
                return store_dir
        raise


def _resolve_suite_dir_executable(
    dir_path: Path,
    rel_exe: tuple[str, ...],
    label: str,
    *,
    base_dir: Path,
) -> Path | None:
    clean_dir = _resolve_store_aware_dir_cli_path(
        dir_path, label, base_dir=base_dir
    )
    cand = clean_dir
    for part in rel_exe:
        cand = cand / part
    try:
        os.lstat(cand)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {cand}: {exc}") from exc
    resolved = _resolve_executable_cli_path(
        cand, f"{label} {'/'.join(rel_exe)}", base_dir=base_dir
    )
    if resolved.is_file():
        return resolved
    return None


def _resolve_suite_rustc_cmd(
    anchor: Path,
    *,
    exit_stack: contextlib.ExitStack,
) -> tuple[str | None, Path | None]:
    sysroot_candidates: list[tuple[str, Path]] = []
    for key in (
        "ANNEAL_SYSROOT",
        "ANNEAL_TEST_RUST_SYSROOT",
        "ANNEAL_MVP_SYSROOT",
    ):
        raw = os.environ.get(key)
        if raw:
            sysroot_candidates.append((key, Path(raw)))
    raw_inst = os.environ.get("ANNEAL_TEST_INSTALL_ROOT")
    if raw_inst:
        sysroot_candidates.append(
            ("ANNEAL_TEST_INSTALL_ROOT", Path(raw_inst) / "rust")
        )
    for label, sys_dir in sysroot_candidates:
        rustc_bin = _resolve_suite_dir_executable(
            sys_dir, ("bin", "rustc"), label, base_dir=anchor
        )
        if rustc_bin is not None:
            extra_lib = _validate_sysroot_lib_dir_path(
                sys_dir / "lib",
                f"{label} lib",
                base_dir=anchor,
                exit_stack=exit_stack,
            )
            return str(rustc_bin), extra_lib

    raw_rustc = os.environ.get("RUSTC")
    if raw_rustc:
        return _resolve_command_token(raw_rustc, anchor), None
    return (
        _resolve_command_from_path(
            "rustc", anchor, allow_rustup_proxy=True
        ),
        None,
    )


def _resolve_suite_lean_cmd(anneal_root: Path, anchor: Path) -> str | None:
    raw_lean = os.environ.get("ANNEAL_LEAN") or os.environ.get(
        "ANNEAL_MVP_LEAN"
    )
    if raw_lean:
        lean_key = (
            "ANNEAL_LEAN"
            if os.environ.get("ANNEAL_LEAN")
            else "ANNEAL_MVP_LEAN"
        )
        return _resolve_explicit_lean_override(raw_lean, lean_key, anchor)
    raw_inst = os.environ.get("ANNEAL_TEST_INSTALL_ROOT")
    if raw_inst:
        inst_lean = _resolve_suite_dir_executable(
            Path(raw_inst),
            ("lean", "bin", "lean"),
            "ANNEAL_TEST_INSTALL_ROOT",
            base_dir=anchor,
        )
        if inst_lean is not None:
            return str(inst_lean)
    raw_xdg = os.environ.get("XDG_CACHE_HOME")
    if raw_xdg:
        found = _find_cached_lean(
            Path(_anchor_env_path(raw_xdg, anchor)) / "anneal" / "toolchain",
            base_dir=anchor,
        )
        if found is not None:
            return str(found)
    raw_home = os.environ.get("HOME")
    if raw_home:
        home_path = Path(_anchor_env_path(raw_home, anchor))
        for rel in (
            ".cache/anneal/toolchain",
            "Library/Caches/anneal/toolchain",
            "anneal/toolchain",
        ):
            found = _find_cached_lean(home_path / rel, base_dir=anchor)
            if found is not None:
                return str(found)
    try:
        lean = _resolve_command_from_path(
            "lean", anchor, allow_rustup_proxy=False, allow_elan_proxy=True
        )
    except _HardlinkedCommandError:
        lean = None
    if lean is not None:
        return lean
    tc_file = anneal_root / "trusted" / "lean" / "lean-toolchain"
    if tc_file.is_file() and not tc_file.is_symlink():
        tc_spec = tc_file.read_text(encoding="utf-8").strip()
        if tc_spec:
            tc_dir = tc_spec.replace("/", "--").replace(":", "---")
            elan_base = (
                Path(_anchor_env_path(os.environ["ELAN_HOME"], anchor))
                if os.environ.get("ELAN_HOME")
                else Path.home() / ".elan"
            )
            cand_lean = elan_base / "toolchains" / tc_dir / "bin" / "lean"
            if cand_lean.exists():
                try:
                    return str(
                        _resolve_executable_cli_path(
                            cand_lean,
                            "elan toolchain lean",
                            base_dir=anchor,
                        )
                    )
                except _HardlinkedCommandError:
                    return None
    return None


def _collect_environment(
    anneal_root: Path, *, caller_cwd: Path | None = None
) -> dict[str, Any]:
    anchor = Path.cwd() if caller_cwd is None else caller_cwd
    lean = _resolve_suite_lean_cmd(anneal_root, anchor)
    rustc_version = "unknown"
    with contextlib.ExitStack() as cleanup:
        rustc_cmd, extra_lib_dir = _resolve_suite_rustc_cmd(
            anchor, exit_stack=cleanup
        )
        rustc = rustc_cmd
        probe_env = os.environ.copy()
        raw_rh = probe_env.get("RUSTUP_HOME")
        if raw_rh:
            probe_env["RUSTUP_HOME"] = str(
                _validate_rustup_home_and_settings(
                    Path(raw_rh), "RUSTUP_HOME", base_dir=anchor
                )
            )
        raw_rt = probe_env.get("RUSTUP_TOOLCHAIN")
        if raw_rt:
            probe_env["RUSTUP_TOOLCHAIN"] = _validate_rustup_toolchain(raw_rt)
        _validate_default_rustup_home_if_proxy((rustc,), anchor, env=probe_env)
        try:
            if rustc is not None and _is_rustup_proxy_symlink(Path(rustc)):
                proxy_opened = _open_tool_or_rustup_proxy(
                    rustc,
                    "rustc",
                    anchor,
                    store_prefix=_STORE_PREFIX,
                    exit_stack=cleanup,
                )
                _pin_rustup_settings(probe_env, anchor, anneal_root, cleanup)
                opened_rustc = _resolve_rustup_proxy_binary_opened(
                    proxy_opened.path,
                    "rustc",
                    work_dir=anneal_root,
                    env=probe_env,
                    base_dir=anchor,
                    exit_stack=cleanup,
                    preopened_rustup=proxy_opened,
                    orig_work_dir=anneal_root,
                    rustup_settings_pinned=True,
                )
                staged_rustc = _stage_verified_executable(
                    opened_rustc.path,
                    "rustc",
                    allow_cargo_deps_hardlink=False,
                    exit_stack=cleanup,
                    base_dir=anchor,
                    tmp_parent=probe_env.get("TMPDIR"),
                    preserve_bin_name=True,
                    preopened=opened_rustc,
                )
                rustc = str(staged_rustc)
                if extra_lib_dir is None:
                    extra_lib_dir = _validate_rustc_sysroot_lib_dir(
                        opened_rustc.path,
                        base_dir=anchor,
                        exit_stack=cleanup,
                        co_locate_rustc=opened_rustc.path,
                        co_locate_rustc_preopened=opened_rustc,
                    )
            rustc_version = (
                _tool_version(
                    [rustc, "--version"], extra_lib_dir=extra_lib_dir
                )
                if rustc is not None
                else "unknown"
            )
        except _RustupProxyResolutionError:
            rustc_version = "unknown"
    return {
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "rustc_version": rustc_version,
        "lean_version": (
            _tool_version([lean, "--version"])
            if lean is not None
            else "unknown"
        ),
        "anneal_root": anneal_root.name,
    }


def _default_anneal_root() -> Path:
    return Path(__file__).resolve().parent.parent


def _open_pinned_proc_fd_dup(pinned_root_prefix: str, label: str) -> int:
    try:
        rel_proc = Path(pinned_root_prefix).relative_to(Path("/proc/self/fd"))
    except ValueError as exc:
        raise ValueError(
            f"invalid pinned staging root for {label}: {pinned_root_prefix}"
        ) from exc
    parts = [p for p in rel_proc.parts if p != "."]
    if len(parts) != 1 or not parts[0].isdigit():
        raise ValueError(
            f"invalid pinned staging root for {label}: {pinned_root_prefix}"
        )
    fd = int(parts[0])
    if fd <= 2:
        raise ValueError(f"invalid stdio pinned descriptor for {label}: {fd}")
    dup_fd = os.dup(fd)
    try:
        st = os.fstat(dup_fd)
        if not stat.S_ISDIR(st.st_mode) or st.st_uid != os.geteuid():
            raise ValueError(
                f"pinned staging root type/owner mismatch for {label}: "
                f"{pinned_root_prefix}"
            )
        return dup_fd
    except Exception:
        os.close(dup_fd)
        raise


def _strip_pinned_rel_path(raw_path: str | Path, prefix: str) -> Path | None:
    raw = str(raw_path)
    if raw != prefix and not raw.startswith(prefix + "/"):
        return None
    rel_str = raw[len(prefix) :].lstrip("/")
    if not rel_str or "\0" in rel_str:
        return None
    raw_p = Path(rel_str)
    if ".." in raw_p.parts:
        return None
    norm = _normalize_lexical_path_py(raw_p)
    if norm is None or norm == Path(".") or not norm.parts:
        return None
    return norm


def _allowed_artifact_manifests_from_pinned_fd(
    root_fd: int, rel_manifest: Path
) -> set[Path]:
    rel_ws_dir = rel_manifest.parent
    walk_fds: list[int] = []
    cur_fd = os.dup(root_fd)
    walk_fds.append(cur_fd)
    try:
        for seg in rel_ws_dir.parts:
            if seg in ("", "."):
                continue
            cur_fd = _open_child_dir_nofollow(
                cur_fd, seg, None, "staged workspace dir"
            )
            walk_fds.append(cur_fd)
        ws_fd = cur_fd
        try:
            os.lstat(rel_manifest.name, dir_fd=ws_fd)
            m_fd, _ = _open_regular_file_from_fd(
                ws_fd, rel_manifest.name, None, False, "staged Cargo.toml"
            )
        except (OSError, ValueError):
            return set()
        try:
            raw_bytes = os.fdopen(m_fd, "rb", closefd=False).read()
        finally:
            os.close(m_fd)
        try:
            parsed = tomllib.loads(raw_bytes.decode("utf-8"))
        except (UnicodeDecodeError, tomllib.TOMLDecodeError):
            return {rel_manifest}
        if not isinstance(parsed, dict):
            return {rel_manifest}
        workspace = parsed.get("workspace")
        if not isinstance(workspace, dict):
            return {rel_manifest}
        if "default-members" in workspace:
            raw_select = workspace.get("default-members")
            if not isinstance(raw_select, list):
                return set()
        elif "package" in parsed:
            return {rel_manifest}
        else:
            raw_select = workspace.get("members", [])
            if not isinstance(raw_select, list):
                return set()

        select_pats = [
            pat.strip()
            for pat in raw_select
            if isinstance(pat, str) and pat.strip()
        ]
        if not select_pats:
            return set()
        raw_exclude = workspace.get("exclude", [])
        excludes = (
            [
                pat.strip()
                for pat in raw_exclude
                if isinstance(pat, str) and pat.strip()
            ]
            if isinstance(raw_exclude, list)
            else []
        )
        allowed: set[Path] = set()
        stack: list[tuple[int, tuple[str, ...]]] = [(os.dup(ws_fd), ())]
        try:
            while stack:
                cand_fd, rel_parts = stack.pop()
                try:
                    rel_dir = Path(*rel_parts) if rel_parts else Path(".")
                    if _is_dir_excluded_by_ws_patterns(
                        Path("."), excludes, rel_dir
                    ):
                        continue
                    if any(
                        _workspace_pattern_matches_dir_py(
                            Path("."), pat, rel_dir
                        )
                        for pat in select_pats
                    ):
                        try:
                            os.lstat("Cargo.toml", dir_fd=cand_fd)
                        except OSError:
                            pass
                        else:
                            try:
                                mem_fd, _ = _open_regular_file_from_fd(
                                    cand_fd,
                                    "Cargo.toml",
                                    None,
                                    False,
                                    "workspace member Cargo.toml",
                                )
                                os.close(mem_fd)
                                allowed.add(
                                    Path(
                                        *rel_ws_dir.parts,
                                        *rel_parts,
                                        "Cargo.toml",
                                    )
                                )
                            except ValueError:
                                pass
                    for name, st in _read_dir_entries_from_fd(
                        cand_fd, "staged workspace"
                    ):
                        if name in ("target", ".git", ".lake"):
                            continue
                        if stat.S_ISLNK(st.st_mode) or not stat.S_ISDIR(
                            st.st_mode
                        ):
                            continue
                        child_fd = _open_child_dir_nofollow(
                            cand_fd,
                            name,
                            (st.st_dev, st.st_ino),
                            "staged workspace member dir",
                        )
                        stack.append((child_fd, (*rel_parts, name)))
                finally:
                    os.close(cand_fd)
        finally:
            while stack:
                leftover_fd, _ = stack.pop()
                os.close(leftover_fd)
        return allowed
    finally:
        for fd in reversed(walk_fds):
            os.close(fd)


def _allowed_artifact_manifests(manifest_canon: Path) -> set[Path]:
    """Resolve canonical manifests permitted to emit a built binary target.

    Plain `[package]` manifests (and non-virtual workspace manifests without
    `workspace.default-members`) only match `manifest_canon` itself; virtual
    workspaces and package workspaces with explicit `workspace.default-members`
    match resolved selected member `Cargo.toml` files excluding
    `workspace.exclude`.
    """
    try:
        parsed = tomllib.loads(manifest_canon.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return {manifest_canon}
    if not isinstance(parsed, dict):
        return {manifest_canon}
    workspace = parsed.get("workspace")
    if not isinstance(workspace, dict):
        return {manifest_canon}
    if "default-members" in workspace:
        raw_select = workspace.get("default-members")
        if not isinstance(raw_select, list):
            return set()
    elif "package" in parsed:
        return {manifest_canon}
    else:
        raw_select = workspace.get("members", [])
        if not isinstance(raw_select, list):
            return set()

    allowed: set[Path] = set()
    ws_dir = manifest_canon.parent
    escaped_ws = glob.escape(str(ws_dir))
    excluded_dirs: set[Path] = set()
    raw_exclude = workspace.get("exclude", [])
    if isinstance(raw_exclude, list):
        for pat in raw_exclude:
            if not isinstance(pat, str) or not pat.strip():
                continue
            for match in glob.glob(
                os.path.join(escaped_ws, pat.strip()), recursive=True
            ):
                try:
                    excluded_dirs.add(Path(match).resolve(strict=True))
                except OSError:
                    continue

    for pat in raw_select:
        if not isinstance(pat, str) or not pat.strip():
            continue
        for match in glob.glob(
            os.path.join(escaped_ws, pat.strip()), recursive=True
        ):
            cand_dir = Path(match)
            try:
                resolved_dir = _resolve_cli_path(
                    cand_dir, "workspace member", base_dir=ws_dir
                )
                if not resolved_dir.is_dir():
                    continue
                resolved_dir = resolved_dir.resolve(strict=True)
                if resolved_dir != ws_dir and ws_dir not in resolved_dir.parents:
                    continue
                if any(
                    resolved_dir == ex or ex in resolved_dir.parents
                    for ex in excluded_dirs
                ):
                    continue
                cand_manifest = resolved_dir / "Cargo.toml"
                if cand_manifest.is_symlink() or not cand_manifest.is_file():
                    continue
                allowed.add(cand_manifest.resolve(strict=True))
            except (OSError, ValueError):
                continue
    return allowed


def _resolve_artifact_manifest_path(
    raw_msg_manifest: str,
    ws_dir: Path,
    *,
    staging_root: Path | None = None,
) -> Path | None:
    if staging_root is None:
        try:
            return _resolve_executable_cli_path(
                Path(raw_msg_manifest),
                "compiler-artifact manifest_path",
                base_dir=ws_dir,
            ).resolve(strict=True)
        except (OSError, ValueError):
            return None
    try:
        canon = _resolve_executable_cli_path(
            Path(raw_msg_manifest),
            "compiler-artifact manifest_path",
            base_dir=staging_root,
        ).resolve(strict=True)
    except (OSError, ValueError):
        return None
    return canon if canon.is_relative_to(staging_root) else None


def _extract_built_executable(
    stdout: str,
    bin_name: str,
    manifest_canon: Path,
    *,
    staged_manifest: Path | None = None,
    pinned_root_prefix: str | None = None,
    staging_root: Path | None = None,
) -> Path | None:
    """Extract the binary path from `cargo build --message-format=json`."""
    check_manifest = (
        staged_manifest if staged_manifest is not None else manifest_canon
    )
    pinned_fd: int | None = None
    allowed_rel: set[Path] | None = None
    allowed_manifests: set[Path] | None = None
    try:
        if pinned_root_prefix is not None:
            rel_target = _strip_pinned_rel_path(
                check_manifest, pinned_root_prefix
            )
            if rel_target is None:
                return None
            pinned_fd = _open_pinned_proc_fd_dup(
                pinned_root_prefix, "compiler-artifact staging root"
            )
            allowed_rel = _allowed_artifact_manifests_from_pinned_fd(
                pinned_fd, rel_target
            )
        else:
            allowed_manifests = _allowed_artifact_manifests(check_manifest)

        found: Path | None = None
        for raw_line in stdout.splitlines():
            line = raw_line.strip()
            if not line.startswith("{"):
                continue
            try:
                msg = json.loads(line)
            except json.JSONDecodeError:
                continue
            if (
                not isinstance(msg, dict)
                or msg.get("reason") != "compiler-artifact"
            ):
                continue
            msg_manifest = msg.get("manifest_path")
            if not isinstance(msg_manifest, str) or not msg_manifest:
                continue
            if pinned_root_prefix is not None:
                assert allowed_rel is not None
                rel_msg = _strip_pinned_rel_path(
                    msg_manifest, pinned_root_prefix
                )
                if rel_msg is None or rel_msg not in allowed_rel:
                    continue
            else:
                assert allowed_manifests is not None
                resolved_msg_manifest = _resolve_artifact_manifest_path(
                    msg_manifest,
                    check_manifest.parent,
                    staging_root=staging_root,
                )
                if (
                    resolved_msg_manifest is None
                    or resolved_msg_manifest not in allowed_manifests
                ):
                    continue
            target = msg.get("target")
            if not isinstance(target, dict) or target.get("name") != bin_name:
                continue
            kinds = target.get("kind")
            if not isinstance(kinds, list) or "bin" not in kinds:
                continue
            profile = msg.get("profile")
            if isinstance(profile, dict) and profile.get("test") is True:
                continue
            exe = msg.get("executable")
            if isinstance(exe, str) and exe:
                cand = Path(exe)
                if found is not None and cand != found:
                    return None
                found = cand
        return found
    finally:
        if pinned_fd is not None:
            os.close(pinned_fd)


def _manifest_is_workspace_root(manifest_path: Path) -> bool:
    try:
        parsed = tomllib.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError):
        return False
    return isinstance(parsed, dict) and isinstance(parsed.get("workspace"), dict)


def _default_pinned_target_dir(
    manifest_canon: Path, default_roots: tuple[Path, ...]
) -> Path:
    """Determine Cargo's default workspace target directory to pin via CLI."""
    work_dir = manifest_canon.parent
    if _manifest_is_workspace_root(manifest_canon):
        return work_dir / "target"
    for anc in default_roots[1:]:
        if _manifest_is_workspace_root(anc / "Cargo.toml"):
            return anc / "target"
    return work_dir / "target"


def _validate_safe_toml_str(val: str, label: str) -> None:
    if not val or "\0" in val or "\n" in val or "\r" in val:
        raise ValueError(
            f"{label} contains empty or unsafe control characters: {val!r}"
        )


def _format_toml_key(key: str) -> str:
    if key and all(c.isascii() and (c.isalnum() or c in "_-") for c in key):
        return key
    return _toml_basic_string(key)


def _render_validated_cargo_source_toml(parsed: dict[str, Any]) -> str:
    source_tbl = parsed.get("source")
    if not isinstance(source_tbl, dict) or not source_tbl:
        return ""
    lines: list[str] = []
    for src_name, src_val in source_tbl.items():
        if lines:
            lines.append("")
        lines.append(f"[source.{_format_toml_key(src_name)}]")
        for k, v in src_val.items():
            lines.append(f"{_format_toml_key(k)} = {_toml_basic_string(v)}")
    return "\n".join(lines) + "\n"


def _extract_locked_registry_crates_from_bytes(
    raw_bytes: bytes, label: str
) -> tuple[tuple[str, str, str | None], ...]:
    try:
        parsed = tomllib.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(f"invalid {label}: {exc}") from exc
    if not isinstance(parsed, dict):
        raise ValueError(f"{label} must parse to a TOML table")
    pkgs = parsed.get("package")
    if not isinstance(pkgs, list):
        return ()
    out: list[tuple[str, str, str | None]] = []
    for item in pkgs:
        if not isinstance(item, dict):
            continue
        src = item.get("source")
        name = item.get("name")
        version = item.get("version")
        checksum = item.get("checksum")
        if (
            isinstance(src, str)
            and src.startswith("registry+")
            and isinstance(name, str)
            and isinstance(version, str)
        ):
            out.append(
                (name, version, checksum if isinstance(checksum, str) else None)
            )
    return tuple(out)


def _read_locked_registry_crates_from_dir(
    dir_path: Path, label: str
) -> tuple[tuple[str, str, str | None], ...] | None:
    if os.name == "posix":
        dir_fd = _open_dir_handle_no_symlinks(dir_path, label)
        try:
            return _read_locked_registry_crates_from_fd(dir_fd, label)
        finally:
            os.close(dir_fd)
    else:
        lock_p = dir_path / "Cargo.lock"
        if not lock_p.exists() and not lock_p.is_symlink():
            return None
        _validate_regular_non_linked_file(
            lock_p, f"{label} Cargo.lock", base_dir=dir_path
        )
        raw_bytes = lock_p.read_bytes()
        return _extract_locked_registry_crates_from_bytes(
            raw_bytes, f"{label} Cargo.lock"
        )


def _read_locked_registry_crates_from_fd(
    dir_fd: int, label: str
) -> tuple[tuple[str, str, str | None], ...] | None:
    try:
        os.lstat("Cargo.lock", dir_fd=dir_fd)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ValueError(f"stat {label} Cargo.lock: {exc}") from exc
    fd, _ = _open_regular_file_from_fd(
        dir_fd, "Cargo.lock", None, False, f"{label} Cargo.lock"
    )
    try:
        raw_bytes = os.fdopen(fd, "rb", closefd=False).read()
    finally:
        os.close(fd)
    return _extract_locked_registry_crates_from_bytes(
        raw_bytes, f"{label} Cargo.lock"
    )


def _read_locked_registry_crates_from_staged_dir(
    staged_root: Path, rel_dir: Path, label: str
) -> tuple[tuple[str, str, str | None], ...] | None:
    if os.name != "posix" or not str(staged_root).startswith("/proc/self/fd/"):
        target = staged_root if rel_dir == Path(".") else (staged_root / rel_dir)
        return _read_locked_registry_crates_from_dir(target, label)
    cur_fd = _open_pinned_proc_fd_dup(str(staged_root), label)
    try:
        for seg in rel_dir.parts:
            if seg in ("", "."):
                continue
            if seg == "..":
                raise ValueError(
                    f"{label} staging relative path must not traverse `..`: {rel_dir}"
                )
            next_fd = _open_child_dir_nofollow(cur_fd, seg, None, label)
            os.close(cur_fd)
            cur_fd = next_fd
        return _read_locked_registry_crates_from_fd(cur_fd, label)
    finally:
        os.close(cur_fd)


def _resolve_cargo_source_directory_py(
    raw_dir: str,
    cargo_home: Path,
    *,
    store_prefix: Path,
    base_dir: Path,
    cfg_display: Path,
    src_name: str,
) -> tuple[bool, Path]:
    _validate_safe_toml_str(
        raw_dir,
        f"CARGO_HOME config {cfg_display} [source.{src_name}].directory",
    )
    dir_path = Path(raw_dir)
    label = "CARGO_HOME [source] directory"
    if dir_path.is_absolute():
        joined = dir_path
    else:
        if ".." in dir_path.parts:
            raise ValueError(
                f"CARGO_HOME config {cfg_display} [source.{src_name}].directory "
                f"invalid: must not contain `..`: {raw_dir}"
            )
        rel_base = (
            cargo_home.parent
            if cargo_home.parent != cargo_home
            else cargo_home
        )
        joined = rel_base / dir_path
    store_dir = _resolve_store_contained_entry(
        joined,
        label,
        store_prefix=store_prefix,
        base_dir=base_dir,
        expect_dir=True,
    )
    if store_dir is not None:
        _validate_store_contained_dir_tree(
            store_dir,
            store_prefix=store_prefix,
            base_dir=base_dir,
            label=label,
        )
        return True, store_dir
    try:
        resolved = _resolve_cli_path(
            joined, label, base_dir=base_dir, require_dir_components=True
        )
    except ValueError as exc:
        raise ValueError(
            f"CARGO_HOME config {cfg_display} [source.{src_name}].directory "
            f"invalid: {exc}"
        ) from exc
    return False, resolved


def _read_cargo_home_config_bytes_py(
    cargo_home: Path, cfg_name: str
) -> bytes | None:
    cfg_path = cargo_home / cfg_name
    if os.name == "posix":
        ch_fd = _open_dir_handle_no_symlinks(cargo_home, "CARGO_HOME")
        try:
            try:
                st = os.lstat(cfg_name, dir_fd=ch_fd)
            except FileNotFoundError:
                return None
            except OSError as exc:
                raise ValueError(
                    f"cannot inspect CARGO_HOME config {cfg_path}: {exc}"
                ) from exc
            if stat.S_ISLNK(st.st_mode):
                raise ValueError(
                    "ambient Cargo config symlink rejected before Cargo build: "
                    f"{cfg_path}"
                )
            if not stat.S_ISREG(st.st_mode):
                raise ValueError(
                    f"ambient Cargo config is not a regular file: {cfg_path}"
                )
            fd, _ = _open_regular_file_from_fd(
                ch_fd,
                cfg_name,
                (st.st_dev, st.st_ino),
                False,
                "ambient Cargo config",
            )
            try:
                return os.fdopen(fd, "rb", closefd=False).read()
            finally:
                os.close(fd)
        finally:
            os.close(ch_fd)

    try:
        cfg_st = os.lstat(cfg_path)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ValueError(
            f"cannot inspect CARGO_HOME config {cfg_path}: {exc}"
        ) from exc
    if stat.S_ISLNK(cfg_st.st_mode):
        raise ValueError(
            "ambient Cargo config symlink rejected before Cargo build: "
            f"{cfg_path}"
        )
    if not stat.S_ISREG(cfg_st.st_mode):
        raise ValueError(
            f"ambient Cargo config is not a regular file: {cfg_path}"
        )
    if cfg_st.st_nlink > 1:
        raise ValueError(
            "ambient Cargo config must not be a hardlink "
            f"(nlink={cfg_st.st_nlink}): {cfg_path}"
        )
    return cfg_path.read_bytes()


def _cargo_home_has_registry_dir_py(cargo_home: Path) -> bool:
    if os.name == "posix":
        ch_fd = _open_dir_handle_no_symlinks(cargo_home, "CARGO_HOME")
        try:
            try:
                st = os.lstat("registry", dir_fd=ch_fd)
            except FileNotFoundError:
                return False
            except OSError as exc:
                raise ValueError(
                    f"cannot inspect CARGO_HOME registry {cargo_home}: {exc}"
                ) from exc
            return not stat.S_ISLNK(st.st_mode) and stat.S_ISDIR(st.st_mode)
        finally:
            os.close(ch_fd)
    reg = cargo_home / "registry"
    try:
        st = os.lstat(reg)
    except OSError:
        return False
    return not stat.S_ISLNK(st.st_mode) and stat.S_ISDIR(st.st_mode)


def _copy_locked_cargo_registry_to_staging_py(
    cargo_home: Path,
    stage_root: Path,
    locked_crates: tuple[tuple[str, str, str | None], ...],
) -> None:
    reg_dir = cargo_home / "registry"
    if os.name != "posix":
        idx_dir = reg_dir / "index"
        if idx_dir.is_dir():
            _copy_cargo_source_dir_to_staging(
                idx_dir,
                stage_root / "registry" / "index",
                copy_full=True,
                reject_ambient=False,
                skip_repo_dirs=False,
                skip_git_anywhere=True,
                label="CARGO_HOME registry index",
            )
        (stage_root / "registry" / "src").mkdir(parents=True, exist_ok=True)
        return

    reg_fd = _open_dir_handle_no_symlinks(reg_dir, "CARGO_HOME registry")
    try:
        try:
            idx_st = os.lstat("index", dir_fd=reg_fd)
            if stat.S_ISLNK(idx_st.st_mode):
                raise ValueError(
                    f"CARGO_HOME registry index must not be a symlink: {reg_dir / 'index'}"
                )
            if stat.S_ISDIR(idx_st.st_mode):
                _copy_cargo_source_dir_to_staging(
                    reg_dir / "index",
                    stage_root / "registry" / "index",
                    copy_full=True,
                    reject_ambient=False,
                    skip_repo_dirs=False,
                    skip_git_anywhere=True,
                    label="CARGO_HOME registry index",
                )
        except FileNotFoundError:
            pass
        try:
            os.lstat("cache", dir_fd=reg_fd)
            cache_fd = _open_child_dir_nofollow(
                reg_fd, "cache", None, "CARGO_HOME registry cache"
            )
        except FileNotFoundError:
            cache_fd = None
        if cache_fd is not None:
            try:
                for idx_name, idx_st in _read_dir_entries_from_fd(
                    cache_fd, "CARGO_HOME registry cache"
                ):
                    if stat.S_ISLNK(idx_st.st_mode):
                        raise ValueError(
                            "CARGO_HOME registry cache must not contain symlink: "
                            f"{idx_name}"
                        )
                    if not stat.S_ISDIR(idx_st.st_mode):
                        continue
                    sub_fd = _open_child_dir_nofollow(
                        cache_fd,
                        idx_name,
                        (idx_st.st_dev, idx_st.st_ino),
                        "CARGO_HOME registry cache subdir",
                    )
                    try:
                        dst_sub = stage_root / "registry" / "cache" / idx_name
                        for name, version, checksum in locked_crates:
                            if (
                                any(ch in name for ch in "/\\\0")
                                or any(ch in version for ch in "/\\\0")
                            ):
                                raise ValueError(
                                    f"unsafe crate name/version in Cargo.lock: {name} {version}"
                                )
                            fname = f"{name}-{version}.crate"
                            try:
                                os.lstat(fname, dir_fd=sub_fd)
                            except FileNotFoundError:
                                continue
                            f_fd, f_st = _open_regular_file_from_fd(
                                sub_fd,
                                fname,
                                None,
                                False,
                                "CARGO_HOME registry .crate",
                            )
                            try:
                                if checksum is not None:
                                    h = hashlib.sha256()
                                    with os.fdopen(
                                        f_fd, "rb", closefd=False
                                    ) as fh:
                                        while chunk := fh.read(1048576):
                                            h.update(chunk)
                                    got_sha = h.hexdigest()
                                    if got_sha != checksum:
                                        raise ValueError(
                                            f"CARGO_HOME registry cache checksum mismatch for {fname}: "
                                            f"expected {checksum}, got {got_sha}"
                                        )
                                    os.lseek(f_fd, 0, os.SEEK_SET)
                                dst_sub.mkdir(
                                    mode=0o700, parents=True, exist_ok=True
                                )
                                dst_file = dst_sub / fname
                                if not dst_file.exists():
                                    _copy_opened_file_to_new_dst(
                                        f_fd,
                                        f_st.st_mode,
                                        dst_file,
                                        "CARGO_HOME registry .crate",
                                    )
                            finally:
                                os.close(f_fd)
                    finally:
                        os.close(sub_fd)
            finally:
                os.close(cache_fd)
    finally:
        os.close(reg_fd)
    reg_src = stage_root / "registry" / "src"
    reg_src.mkdir(mode=0o700, parents=True, exist_ok=True)
    if os.name == "posix":
        os.chmod(reg_src, 0o700)


def _inspect_and_stage_cargo_home_py(
    ch_path: Path,
    *,
    base_dir: Path,
    explicit_override: bool,
    store_prefix: Path,
    stage_ctx: tuple[Path, Path] | None = None,
    locked_crates: tuple[tuple[str, str, str | None], ...] = (),
    lockfile_dir: Path | None = None,
) -> tuple[Path, Path | None]:
    """Validate `$CARGO_HOME` `config{,.toml}` and optionally stage immutably."""
    ch_label = "CARGO_HOME" if explicit_override else "HOME/.cargo"
    validated_ch = _resolve_cli_path(
        ch_path,
        ch_label,
        base_dir=base_dir,
        require_dir_components=True,
    )
    try:
        ch_st = os.lstat(validated_ch)
    except FileNotFoundError:
        return validated_ch, None
    except OSError as exc:
        raise ValueError(
            f"cannot inspect CARGO_HOME {validated_ch}: {exc}"
        ) from exc
    if stat.S_ISLNK(ch_st.st_mode):
        raise ValueError(
            "CARGO_HOME directory must not be a symlink before Cargo build: "
            f"{validated_ch}"
        )
    if not stat.S_ISDIR(ch_st.st_mode):
        raise ValueError(
            f"CARGO_HOME path is not a directory before Cargo build: {validated_ch}"
        )

    staged_cfg_count = 0
    staged_sources: dict[Path, Path] = {}
    next_src_idx = 0

    for cfg_name in ("config", "config.toml"):
        cfg_path = validated_ch / cfg_name
        raw_bytes = _read_cargo_home_config_bytes_py(validated_ch, cfg_name)
        if raw_bytes is None:
            continue
        try:
            parsed = tomllib.loads(raw_bytes.decode("utf-8"))
        except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
            raise ValueError(
                f"invalid CARGO_HOME Cargo config {cfg_path}: {exc}"
            ) from exc
        if not isinstance(parsed, dict):
            raise ValueError(
                f"CARGO_HOME config {cfg_path} must parse to a TOML table"
            )
        disallowed = sorted(k for k in parsed if k != "source")
        if disallowed:
            raise ValueError(
                f"ambient Cargo config in CARGO_HOME ({cfg_path}) defines "
                f"disallowed section(s) {disallowed!r} (only `[source]` is "
                "permitted before Cargo build)"
            )
        source_tbl = parsed.get("source")
        if source_tbl is not None:
            if not isinstance(source_tbl, dict):
                raise ValueError(
                    f"CARGO_HOME config {cfg_path} `[source]` must be a TOML table"
                )
            for src_name, src_val in source_tbl.items():
                if not isinstance(src_val, dict):
                    raise ValueError(
                        f"CARGO_HOME config {cfg_path} [source.{src_name}] "
                        "must be a TOML table"
                    )
                for k, v in src_val.items():
                    if k not in ("replace-with", "directory"):
                        raise ValueError(
                            f"CARGO_HOME config {cfg_path} [source.{src_name}] "
                            f"defines disallowed key {k!r} (only `replace-with` "
                            "and `directory` are permitted)"
                        )
                    if not isinstance(v, str):
                        raise ValueError(
                            f"CARGO_HOME config {cfg_path} [source.{src_name}].{k} "
                            "must be a string"
                        )
                    _validate_safe_toml_str(
                        v,
                        f"CARGO_HOME config {cfg_path} [source.{src_name}].{k}",
                    )
                raw_dir = src_val.get("directory")
                if isinstance(raw_dir, str):
                    is_store, resolved_dir = _resolve_cargo_source_directory_py(
                        raw_dir,
                        validated_ch,
                        store_prefix=store_prefix,
                        base_dir=base_dir,
                        cfg_display=cfg_path,
                        src_name=src_name,
                    )
                    if is_store:
                        src_val["directory"] = str(resolved_dir)
                    elif stage_ctx is not None:
                        _, pinned_root = stage_ctx
                        canon_host = resolved_dir.resolve(strict=True)
                        if canon_host in staged_sources:
                            pinned_src = staged_sources[canon_host]
                        else:
                            slot = f"src-{next_src_idx}"
                            next_src_idx += 1
                            dst_dir = pinned_root / "sources" / slot
                            try:
                                _copy_cargo_source_dir_to_staging(
                                    resolved_dir,
                                    dst_dir,
                                    copy_full=True,
                                    reject_ambient=False,
                                    skip_repo_dirs=False,
                                    skip_git_anywhere=False,
                                    label="CARGO_HOME [source] directory",
                                )
                            except ValueError as exc:
                                raise ValueError(
                                    f"CARGO_HOME config {cfg_path} [source.{src_name}].directory "
                                    f"invalid: {exc}"
                                ) from exc
                            staged_sources[canon_host] = dst_dir
                            pinned_src = dst_dir
                        src_val["directory"] = str(pinned_src)
                    else:
                        try:
                            _validate_dir_tree_no_links(
                                resolved_dir, "CARGO_HOME [source] directory"
                            )
                        except ValueError as exc:
                            raise ValueError(
                                f"CARGO_HOME config {cfg_path} [source.{src_name}].directory "
                                f"invalid: {exc}"
                            ) from exc
        if stage_ctx is not None:
            _, pinned_root = stage_ctx
            rendered = _render_validated_cargo_source_toml(parsed)
            dst_cfg = pinned_root / cfg_name
            flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(
                os, "O_NOFOLLOW", 0
            )
            fd = os.open(dst_cfg, flags, 0o444)
            try:
                with os.fdopen(fd, "w", encoding="utf-8") as fh:
                    fh.write(rendered)
                    fh.flush()
                    if os.name == "posix":
                        os.fchmod(fh.fileno(), 0o444)
            except Exception:
                try:
                    dst_cfg.unlink()
                except OSError:
                    pass
                raise
            staged_cfg_count += 1

    if stage_ctx is not None and staged_cfg_count == 0:
        if _cargo_home_has_registry_dir_py(validated_ch):
            effective_locked = locked_crates
            if not effective_locked and lockfile_dir is not None:
                effective_locked = (
                    _read_locked_registry_crates_from_dir(
                        lockfile_dir, "workspace"
                    )
                    or ()
                )
            if effective_locked:
                _, pinned_root = stage_ctx
                _copy_locked_cargo_registry_to_staging_py(
                    validated_ch, pinned_root, effective_locked
                )
                return validated_ch, Path("registry") / "src"
    return validated_ch, None


def _validate_cargo_home_configs(
    ch_path: Path,
    *,
    base_dir: Path,
    explicit_override: bool,
    store_prefix: Path = _STORE_PREFIX,
) -> Path:
    """Validate `$CARGO_HOME` and its `config{,.toml}` pre-Cargo."""
    validated_ch, _ = _inspect_and_stage_cargo_home_py(
        ch_path,
        base_dir=base_dir,
        explicit_override=explicit_override,
        store_prefix=store_prefix,
        stage_ctx=None,
    )
    return validated_ch


def _validate_ambient_cargo_paths(
    work_dir: Path,
    default_roots: tuple[Path, ...],
    *,
    base_dir: Path,
    env: dict[str, str] | None = None,
) -> tuple[Path | None, bool]:
    src_env = os.environ if env is None else env
    raw_home = src_env.get("HOME")
    if raw_home:
        _resolve_cli_path(
            Path(raw_home),
            "HOME",
            base_dir=base_dir,
            require_dir_components=True,
        )
    raw_ch = src_env.get("CARGO_HOME")
    effective_ch: Path | None
    explicit_override = False
    if raw_ch:
        effective_ch = _resolve_cli_path(
            Path(raw_ch),
            "CARGO_HOME",
            base_dir=base_dir,
            require_dir_components=True,
        )
        explicit_override = True
    elif raw_home:
        effective_ch = _resolve_cli_path(
            Path(raw_home) / ".cargo",
            "HOME/.cargo",
            base_dir=base_dir,
            require_dir_components=True,
        )
    else:
        effective_ch = None

    allowed_cargo_home = (
        effective_ch.resolve(strict=False)
        if effective_ch is not None
        else None
    )
    repo_roots = set(default_roots)
    for anc in (work_dir, *work_dir.parents):
        for tc_name in ("rust-toolchain", "rust-toolchain.toml"):
            tc_path = anc / tc_name
            if tc_path.is_symlink() or tc_path.exists():
                raise ValueError(
                    f"ambient `{tc_name}` override rejected before Cargo build: "
                    f"{tc_path}"
                )
        dot_cargo = anc / ".cargo"
        if dot_cargo.is_symlink():
            raise ValueError(
                f"ambient `.cargo` symlink rejected before Cargo build: {dot_cargo}"
            )
        if dot_cargo.exists():
            in_repo_root = anc in repo_roots
            is_cargo_home = (
                not in_repo_root
                and allowed_cargo_home is not None
                and dot_cargo.resolve(strict=False) == allowed_cargo_home
            )
            if not is_cargo_home:
                raise ValueError(
                    f"ambient `.cargo` directory rejected before Cargo build: "
                    f"{dot_cargo}"
                )
    return effective_ch, explicit_override


def _pin_cargo_home_from_path(
    effective_ch: Path | None,
    *,
    explicit_override: bool,
    base_dir: Path,
    exit_stack: contextlib.ExitStack,
    tmp_parent: str | None = None,
    store_prefix: Path = _STORE_PREFIX,
    locked_crates: tuple[tuple[str, str, str | None], ...] = (),
    lockfile_dir: Path | None = None,
) -> Path:
    def _populate(priv_root: Path, pinned_root: Path) -> Path | None:
        if effective_ch is None:
            return None
        _, writable_rel = _inspect_and_stage_cargo_home_py(
            effective_ch,
            base_dir=base_dir,
            explicit_override=explicit_override,
            store_prefix=store_prefix,
            stage_ctx=(priv_root, pinned_root),
            locked_crates=locked_crates,
            lockfile_dir=lockfile_dir,
        )
        return writable_rel

    return _build_pinned_staging_dir(
        exit_stack,
        prefix="anneal-cargo-home-",
        base_dir=base_dir,
        tmp_parent=tmp_parent,
        label="CARGO_HOME",
        populate=_populate,
    )


def _reject_ambient_cargo_configs(
    work_dir: Path,
    default_roots: tuple[Path, ...],
    *,
    base_dir: Path | None = None,
    store_prefix: Path = _STORE_PREFIX,
    exit_stack: contextlib.ExitStack | None = None,
    tmp_parent: str | None = None,
    locked_crates: tuple[tuple[str, str, str | None], ...] = (),
    lockfile_dir: Path | None = None,
) -> Path | None:
    """Reject ambient `.cargo`/`rust-toolchain*` and pin `CARGO_HOME`."""
    anchor = Path.cwd() if base_dir is None else base_dir
    effective_ch, explicit_override = _validate_ambient_cargo_paths(
        work_dir, default_roots, base_dir=anchor
    )
    if exit_stack is None:
        if effective_ch is not None:
            _validate_cargo_home_configs(
                effective_ch,
                base_dir=anchor,
                explicit_override=explicit_override,
                store_prefix=store_prefix,
            )
        return None
    use_tmp = tmp_parent
    if use_tmp is None and os.environ.get("TMPDIR"):
        valid_tmp = _validate_child_tmpdir(
            {"TMPDIR": os.environ.get("TMPDIR", "")}, anchor
        )
        use_tmp = str(valid_tmp) if valid_tmp is not None else None
    return _pin_cargo_home_from_path(
        effective_ch,
        explicit_override=explicit_override,
        base_dir=anchor,
        exit_stack=exit_stack,
        tmp_parent=use_tmp,
        store_prefix=store_prefix,
        locked_crates=locked_crates,
        lockfile_dir=lockfile_dir,
    )


def _pin_cargo_home_configs_env(
    env: dict[str, str],
    base_dir: Path,
    *,
    exit_stack: contextlib.ExitStack,
    store_prefix: Path = _STORE_PREFIX,
    locked_crates: tuple[tuple[str, str, str | None], ...] = (),
    lockfile_dir: Path | None = None,
) -> Path:
    effective_ch, explicit_override = _validate_ambient_cargo_paths(
        base_dir, (), base_dir=base_dir, env=env
    )
    pinned = _pin_cargo_home_from_path(
        effective_ch,
        explicit_override=explicit_override,
        base_dir=base_dir,
        exit_stack=exit_stack,
        tmp_parent=env.get("TMPDIR"),
        store_prefix=store_prefix,
        locked_crates=locked_crates,
        lockfile_dir=lockfile_dir,
    )
    env["CARGO_HOME"] = str(pinned)
    return pinned


def _is_non_symlink_dir(path: Path) -> bool:
    try:
        st = os.lstat(path)
    except OSError:
        return False
    return not stat.S_ISLNK(st.st_mode) and stat.S_ISDIR(st.st_mode)


def _matches_cargo_hardlink_partner(
    cand: Path, bin_dev_ino: tuple[int, int]
) -> bool:
    try:
        st = os.lstat(cand)
    except OSError:
        return False
    return (
        not stat.S_ISLNK(st.st_mode)
        and stat.S_ISREG(st.st_mode)
        and st.st_nlink == 2
        and (st.st_dev, st.st_ino) == bin_dev_ino
    )


def _has_verified_cargo_hardlink_partner_fd(
    profile_fd: int, bin_name: str, bin_dev_ino: tuple[int, int]
) -> bool:
    stem = bin_name.replace("-", "_")
    try:
        deps_fd = _open_child_dir_nofollow(profile_fd, "deps", None, "Cargo deps dir")
    except ValueError:
        deps_fd = None
    if deps_fd is not None:
        try:
            stem_prefix = f"{stem}-"
            for name, st in _read_dir_entries_from_fd(deps_fd, "Cargo deps dir"):
                if stat.S_ISREG(st.st_mode) and name.startswith(stem_prefix):
                    try:
                        p_fd, p_st = _open_regular_file_from_fd(
                            deps_fd, name, None, True, "Cargo deps binary"
                        )
                    except ValueError:
                        continue
                    try:
                        if (
                            p_st.st_nlink == 2
                            and (p_st.st_dev, p_st.st_ino) == bin_dev_ino
                        ):
                            return True
                    finally:
                        os.close(p_fd)
        finally:
            os.close(deps_fd)

    try:
        build_fd = _open_child_dir_nofollow(profile_fd, "build", None, "Cargo build dir")
    except ValueError:
        return False
    exe_suffix = ".exe" if sys.platform == "win32" else ""
    out_leaf = f"{stem}{exe_suffix}"
    try:
        for pkg_name, pkg_st in _read_dir_entries_from_fd(build_fd, "Cargo build dir"):
            if not stat.S_ISDIR(pkg_st.st_mode):
                continue
            try:
                pkg_fd = _open_child_dir_nofollow(
                    build_fd,
                    pkg_name,
                    (pkg_st.st_dev, pkg_st.st_ino),
                    "Cargo build package dir",
                )
            except ValueError:
                continue
            try:
                for hash_name, hash_st in _read_dir_entries_from_fd(
                    pkg_fd, "Cargo hash dir"
                ):
                    if (
                        not stat.S_ISDIR(hash_st.st_mode)
                        or not hash_name
                        or not hash_name.isascii()
                        or not hash_name.isalnum()
                    ):
                        continue
                    try:
                        hash_fd = _open_child_dir_nofollow(
                            pkg_fd,
                            hash_name,
                            (hash_st.st_dev, hash_st.st_ino),
                            "Cargo build hash dir",
                        )
                    except ValueError:
                        continue
                    try:
                        try:
                            out_fd = _open_child_dir_nofollow(
                                hash_fd, "out", None, "Cargo build out dir"
                            )
                        except ValueError:
                            continue
                        try:
                            try:
                                out_f, out_st = _open_regular_file_from_fd(
                                    out_fd, out_leaf, None, True, "Cargo out binary"
                                )
                            except ValueError:
                                continue
                            try:
                                if (
                                    out_st.st_nlink == 2
                                    and (out_st.st_dev, out_st.st_ino) == bin_dev_ino
                                ):
                                    return True
                            finally:
                                os.close(out_f)
                        finally:
                            os.close(out_fd)
                    finally:
                        os.close(hash_fd)
            finally:
                os.close(pkg_fd)
    finally:
        os.close(build_fd)
    return False


def _has_verified_cargo_hardlink_partner(
    profile_dir: Path, bin_name: str, bin_dev_ino: tuple[int, int]
) -> bool:
    if os.name == "posix":
        try:
            profile_fd = _open_dir_handle_no_symlinks(
                profile_dir, "Cargo profile dir"
            )
        except ValueError:
            return False
        try:
            return _has_verified_cargo_hardlink_partner_fd(
                profile_fd, bin_name, bin_dev_ino
            )
        finally:
            os.close(profile_fd)
    stem = bin_name.replace("-", "_")
    deps_dir = profile_dir / "deps"
    if _is_non_symlink_dir(deps_dir):
        stem_prefix = f"{stem}-"
        for entry in deps_dir.iterdir():
            if entry.name.startswith(stem_prefix) and _matches_cargo_hardlink_partner(
                entry, bin_dev_ino
            ):
                return True
    build_dir = profile_dir / "build"
    if _is_non_symlink_dir(build_dir):
        exe_suffix = ".exe" if sys.platform == "win32" else ""
        out_leaf = f"{stem}{exe_suffix}"
        for pkg_dir in build_dir.iterdir():
            if not _is_non_symlink_dir(pkg_dir):
                continue
            for hash_dir in pkg_dir.iterdir():
                if (
                    not hash_dir.name
                    or not hash_dir.name.isascii()
                    or not hash_dir.name.isalnum()
                    or not _is_non_symlink_dir(hash_dir)
                ):
                    continue
                out_dir = hash_dir / "out"
                if _is_non_symlink_dir(out_dir) and _matches_cargo_hardlink_partner(
                    out_dir / out_leaf, bin_dev_ino
                ):
                    return True
    return False


def _materialize_cargo_built_executable(
    bin_canon: Path,
    pinned_td_canon: Path,
    bin_name: str,
    *,
    dest_dir: Path | None = None,
    force_copy: bool = False,
    chmod_mode: int = 0o755,
    allow_cargo_deps_hardlink: bool = True,
    preserve_bin_name: bool = False,
    preopened: _OpenedExecutable | None = None,
    dest_is_pinned: bool = False,
) -> Path:
    """Isolate Cargo's output to a verified single-link executable."""
    with contextlib.ExitStack() as local_stack:
        opened = preopened
        if opened is None or opened.fd is None or opened.st is None:
            opened = _open_verified_executable_via_dirfd(
                bin_canon,
                bin_canon.parent,
                reject_hardlinks=False,
                allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
                label=f"built {bin_name}",
                exit_stack=local_stack,
            )
        st = opened.st
        assert st is not None
        if st.st_nlink == 1:
            if not force_copy and dest_dir is None:
                return opened.path
        elif st.st_nlink == 2:
            partner_ok = False
            if allow_cargo_deps_hardlink:
                if opened.parent_fd is not None:
                    partner_ok = _has_verified_cargo_hardlink_partner_fd(
                        opened.parent_fd, opened.path.name, (st.st_dev, st.st_ino)
                    )
                else:
                    partner_ok = _has_verified_cargo_hardlink_partner(
                        opened.path.parent, opened.path.name, (st.st_dev, st.st_ino)
                    )
                if not partner_ok and opened.path.name != bin_name:
                    if opened.parent_fd is not None:
                        partner_ok = _has_verified_cargo_hardlink_partner_fd(
                            opened.parent_fd, bin_name, (st.st_dev, st.st_ino)
                        )
                    else:
                        partner_ok = _has_verified_cargo_hardlink_partner(
                            opened.path.parent, bin_name, (st.st_dev, st.st_ino)
                        )
            if not partner_ok:
                raise ValueError(
                    f"built {bin_name} must not be hardlinked outside Cargo deps "
                    f"(nlink=2): {opened.path}"
                )
        else:
            raise ValueError(
                f"built {bin_name} must not have extra hardlinks "
                f"(nlink={st.st_nlink}): {opened.path}"
            )

        iso_dir = (
            dest_dir
            if dest_dir is not None
            else (pinned_td_canon / ".anneal-isolated-bins")
        )
        if not dest_is_pinned:
            iso_dir = _resolve_cli_path(
                iso_dir,
                "isolated bin dir",
                base_dir=iso_dir.parent,
                require_dir_components=True,
            )
            try:
                iso_st = os.lstat(iso_dir)
                if stat.S_ISLNK(iso_st.st_mode) or not stat.S_ISDIR(
                    iso_st.st_mode
                ):
                    raise ValueError(
                        f"isolated bin dir must be a real dir: {iso_dir}"
                    )
            except FileNotFoundError:
                iso_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
            iso_canon = iso_dir.resolve(strict=True)
        else:
            iso_canon = iso_dir

        sha256_h = hashlib.sha256()
        if opened.fd is not None:
            opened_st = os.fstat(opened.fd)
            if (
                not stat.S_ISREG(opened_st.st_mode)
                or opened_st.st_nlink != st.st_nlink
                or (opened_st.st_dev, opened_st.st_ino) != (st.st_dev, st.st_ino)
            ):
                raise ValueError(
                    f"built {bin_name} changed concurrently during isolation: {opened.path}"
                )
            os.lseek(opened.fd, 0, os.SEEK_SET)
            src_ctx = os.fdopen(opened.fd, "rb", closefd=False)
        else:
            open_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
            src_fd = os.open(opened.path, open_flags)
            local_stack.callback(_close_fd_quiet, src_fd)
            opened_st = os.fstat(src_fd)
            if (
                not stat.S_ISREG(opened_st.st_mode)
                or opened_st.st_nlink != st.st_nlink
                or (opened_st.st_dev, opened_st.st_ino) != (st.st_dev, st.st_ino)
            ):
                raise ValueError(
                    f"built {bin_name} changed concurrently during isolation: {opened.path}"
                )
            src_ctx = os.fdopen(src_fd, "rb", closefd=False)

        with src_ctx as src_f:
            tmp_path: Path | None = None
            try:
                with tempfile.NamedTemporaryFile(
                    dir=iso_canon, prefix=f".{bin_name}-", delete=False
                ) as tmp_f:
                    tmp_path = Path(tmp_f.name)
                    while chunk := src_f.read(65536):
                        sha256_h.update(chunk)
                        tmp_f.write(chunk)
                    tmp_f.flush()
                    os.fchmod(tmp_f.fileno(), chmod_mode)
                    tmp_st = os.fstat(tmp_f.fileno())
                if (
                    stat.S_ISLNK(tmp_st.st_mode)
                    or not stat.S_ISREG(tmp_st.st_mode)
                    or tmp_st.st_nlink != 1
                ):
                    raise ValueError(
                        f"isolated {bin_name} temp file failed single-link check "
                        f"(nlink={tmp_st.st_nlink}): {tmp_path}"
                    )
                bin_sha16 = sha256_h.hexdigest()[:16]
                dest_name = (
                    bin_name if preserve_bin_name else f"{bin_name}-{bin_sha16}"
                )
                dest_path = iso_canon / dest_name
                os.replace(tmp_path, dest_path)
                tmp_path = None
            finally:
                if tmp_path is not None:
                    try:
                        tmp_path.unlink()
                    except OSError:
                        pass

    dest_st = os.lstat(dest_path)
    if (
        stat.S_ISLNK(dest_st.st_mode)
        or not stat.S_ISREG(dest_st.st_mode)
        or dest_st.st_nlink != 1
        or (dest_st.st_dev, dest_st.st_ino) != (tmp_st.st_dev, tmp_st.st_ino)
    ):
        raise ValueError(
            f"isolated {bin_name} failed single-link verification "
            f"(nlink={dest_st.st_nlink}): {dest_path}"
        )
    if dest_is_pinned:
        return dest_path
    return dest_path.resolve(strict=True)


def _format_timeout_tail(exc: subprocess.TimeoutExpired) -> str:
    raw = exc.stderr or exc.stdout or b""
    if isinstance(raw, bytes):
        return raw.decode("utf-8", errors="replace")[-1000:]
    return str(raw)[-1000:]


def _terminate_process_group(proc: subprocess.Popen[str]) -> None:
    if os.name == "posix":
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return
        except ProcessLookupError:
            return
        except OSError:
            pass
    try:
        proc.kill()
    except OSError:
        pass


def _run_subcommand_process_group(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout_secs: float,
) -> subprocess.CompletedProcess[str]:
    """Run a child in its own session/process group and kill the tree on timeout."""
    popen_kwargs: dict[str, Any] = {
        "cwd": cwd,
        "env": env,
        "stdin": subprocess.DEVNULL,
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
    }
    if os.name == "posix":
        popen_kwargs["start_new_session"] = True
    pass_fds = _extract_proc_fd_numbers(cmd, env, cwd=cwd)
    if pass_fds:
        popen_kwargs["pass_fds"] = pass_fds
    proc = subprocess.Popen(cmd, **popen_kwargs)
    try:
        stdout, stderr = proc.communicate(timeout=timeout_secs)
    except subprocess.TimeoutExpired as exc:
        _terminate_process_group(proc)
        try:
            out_tail, err_tail = proc.communicate(timeout=5.0)
        except subprocess.TimeoutExpired:
            try:
                proc.kill()
            except OSError:
                pass
            proc.wait()
            out_tail, err_tail = exc.output, exc.stderr
        raise subprocess.TimeoutExpired(
            cmd=cmd,
            timeout=timeout_secs,
            output=out_tail if out_tail is not None else exc.output,
            stderr=err_tail if err_tail is not None else exc.stderr,
        ) from exc
    except BaseException:
        _terminate_process_group(proc)
        try:
            proc.wait(timeout=5.0)
        except Exception:
            pass
        raise
    return subprocess.CompletedProcess(
        args=cmd,
        returncode=proc.returncode if proc.returncode is not None else 1,
        stdout=stdout,
        stderr=stderr,
    )


@dataclass
class _PreparedMirEvalSources:
    canon_orig_manifest: Path
    canon_orig_work_dir: Path
    default_roots: tuple[Path, ...]
    staged_manifest: Path
    staged_work_dir: Path
    staging_root: Path | None
    pinned_root_prefix: str | None
    locked_registry_crates: tuple[tuple[str, str, str | None], ...] = ()


def _normalize_manifest_rel_path(
    base_dir: Path,
    raw_rel: str,
    *,
    store_prefix: Path,
    allow_store_abs: bool,
    label: str,
) -> tuple[Path, bool]:
    if not raw_rel or "\0" in raw_rel:
        raise ValueError(f"empty or NUL {label} path in Cargo.toml: {raw_rel!r}")
    p = Path(raw_rel)
    if p.is_absolute():
        if allow_store_abs:
            store_dir = _resolve_store_contained_entry(
                p, label, store_prefix=store_prefix, base_dir=base_dir, expect_dir=True
            )
            if store_dir is not None:
                return store_dir, True
        raise ValueError(
            f"{label} must not use an absolute non-store path outside staged source tree: {raw_rel}"
        )
    cur = base_dir
    for comp in p.parts:
        if comp in ("", "."):
            continue
        if comp == "..":
            if cur == cur.parent:
                raise ValueError(f"{label} escaped filesystem root: {raw_rel}")
            cur = cur.parent
        else:
            cur = cur / comp
    return cur, False


def _check_manifest_dir_no_links(cand: Path, label: str) -> Path | None:
    try:
        st = os.lstat(cand)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ValueError(f"stat {label} {cand}: {exc}") from exc
    if stat.S_ISLNK(st.st_mode):
        raise ValueError(f"{label} must not be a symlink: {cand}")
    return _resolve_cli_path(
        cand, label, base_dir=Path("/"), require_dir_components=True
    ).resolve(strict=True)


def _read_cargo_toml_via_dirfd(
    dir_path: Path, label: str
) -> tuple[dict[str, Any], bytes] | None:
    if os.name == "posix":
        dir_fd = _open_dir_handle_no_symlinks(dir_path, label)
        try:
            try:
                os.lstat("Cargo.toml", dir_fd=dir_fd)
            except FileNotFoundError:
                return None
            except OSError as exc:
                raise ValueError(f"stat {label} Cargo.toml: {exc}") from exc
            fd, _ = _open_regular_file_from_fd(
                dir_fd, "Cargo.toml", None, False, label
            )
            try:
                raw_bytes = os.fdopen(fd, "rb", closefd=False).read()
            finally:
                os.close(fd)
        finally:
            os.close(dir_fd)
    else:
        p = dir_path / "Cargo.toml"
        if not p.exists() and not p.is_symlink():
            return None
        _validate_regular_non_linked_file(p, label, base_dir=dir_path)
        raw_bytes = p.read_bytes()
    try:
        parsed = tomllib.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(f"invalid {label} Cargo.toml in {dir_path}: {exc}") from exc
    if not isinstance(parsed, dict):
        raise ValueError(f"invalid {label} Cargo.toml table in {dir_path}")
    return parsed, raw_bytes


def _segment_glob_matches_py(pat: str, text: str) -> bool:
    memo: dict[tuple[int, int], bool] = {}

    def _match(pi: int, ti: int) -> bool:
        key = (pi, ti)
        cached = memo.get(key)
        if cached is not None:
            return cached
        if pi == len(pat):
            res = ti == len(text)
        elif pat[pi] == "*":
            res = _match(pi + 1, ti) or (ti < len(text) and _match(pi, ti + 1))
        elif pat[pi] == "?":
            res = ti < len(text) and _match(pi + 1, ti + 1)
        elif pat[pi] == "[":
            if ti >= len(text):
                res = False
            else:
                idx = pi + 1
                negate = idx < len(pat) and pat[idx] in ("!", "^")
                if negate:
                    idx += 1
                matched = False
                ch = text[ti]
                while idx < len(pat) and pat[idx] != "]":
                    if (
                        idx + 2 < len(pat)
                        and pat[idx + 1] == "-"
                        and pat[idx + 2] != "]"
                    ):
                        if pat[idx] <= ch <= pat[idx + 2]:
                            matched = True
                        idx += 3
                    else:
                        if ch == pat[idx]:
                            matched = True
                        idx += 1
                if idx >= len(pat) or pat[idx] != "]":
                    res = pat[pi] == ch and _match(pi + 1, ti + 1)
                else:
                    ok = (not matched) if negate else matched
                    res = ok and _match(idx + 1, ti + 1)
        else:
            res = (
                ti < len(text)
                and pat[pi] == text[ti]
                and _match(pi + 1, ti + 1)
            )
        memo[key] = res
        return res

    return _match(0, 0)


def _split_glob_segments_py(pattern: str) -> tuple[str, ...]:
    return tuple(
        seg for seg in pattern.strip().split("/") if seg and seg != "."
    )


def _path_components_glob_match_py(
    pat_segs: tuple[str, ...], rel_segs: tuple[str, ...]
) -> bool:
    memo: dict[tuple[int, int], bool] = {}

    def _match(pi: int, ri: int) -> bool:
        key = (pi, ri)
        cached = memo.get(key)
        if cached is not None:
            return cached
        if pi == len(pat_segs):
            res = ri == len(rel_segs)
        elif pat_segs[pi] == "**":
            res = _match(pi + 1, ri) or (
                ri < len(rel_segs) and _match(pi, ri + 1)
            )
        elif ri == len(rel_segs):
            res = False
        else:
            res = _segment_glob_matches_py(pat_segs[pi], rel_segs[ri]) and _match(
                pi + 1, ri + 1
            )
        memo[key] = res
        return res

    return _match(0, 0)


def _normalize_lexical_path_py(path: Path) -> Path | None:
    parts: list[str] = []
    anchor = path.anchor
    for part in path.parts:
        if part == anchor or part in ("", "."):
            continue
        if part == "..":
            if not parts:
                return None
            parts.pop()
        else:
            parts.append(part)
    return Path(anchor, *parts) if anchor else Path(*parts)


def _workspace_pattern_matches_dir_py(
    ws_dir: Path, pat: str, cand_dir: Path
) -> bool:
    trimmed = pat.strip()
    if not trimmed:
        return False
    has_glob = any(ch in trimmed for ch in "*?[")
    if not has_glob:
        if "\0" in trimmed or Path(trimmed).is_absolute():
            return False
        norm_pat = _normalize_lexical_path_py(ws_dir / trimmed)
        norm_cand = _normalize_lexical_path_py(cand_dir)
        return norm_pat is not None and norm_pat == norm_cand
    try:
        rel = cand_dir.relative_to(ws_dir)
    except ValueError:
        return False
    pat_segs = _split_glob_segments_py(trimmed)
    return bool(pat_segs) and _path_components_glob_match_py(
        pat_segs, rel.parts
    )


def _is_dir_excluded_by_ws_patterns(
    ws_dir: Path, excludes: list[str], cand_dir: Path
) -> bool:
    for ex in excludes:
        for anc in (cand_dir, *cand_dir.parents):
            if _workspace_pattern_matches_dir_py(ws_dir, ex, anc):
                return True
            if anc == ws_dir:
                break
            if any(ch in ex for ch in "*?[") and not anc.is_relative_to(ws_dir):
                break
    return False


def _expand_glob_ws_members_from_fd(
    ws_dir: Path, pat: str, excludes: list[str]
) -> list[Path]:
    matched: list[Path] = []
    pat_segs = _split_glob_segments_py(pat)
    root_fd = (
        _open_dir_handle_no_symlinks(ws_dir, "workspace root")
        if os.name == "posix"
        else -1
    )
    stack: list[tuple[int | None, Path, tuple[str, ...]]] = [(None, ws_dir, ())]
    try:
        while stack:
            dir_fd, cur_disp, rel_parts = stack.pop()
            if _is_dir_excluded_by_ws_patterns(ws_dir, excludes, cur_disp):
                if dir_fd is not None:
                    os.close(dir_fd)
                continue
            active_fd = root_fd if dir_fd is None else dir_fd
            try:
                if (
                    rel_parts
                    and pat_segs
                    and _path_components_glob_match_py(pat_segs, rel_parts)
                ):
                    if os.name == "posix":
                        try:
                            os.lstat("Cargo.toml", dir_fd=active_fd)
                            matched.append(cur_disp)
                        except OSError:
                            pass
                    elif (cur_disp / "Cargo.toml").exists():
                        matched.append(cur_disp)
                if os.name == "posix":
                    entries = _read_dir_entries_from_fd(
                        active_fd, "workspace members"
                    )
                else:
                    entries = [
                        (e.name, os.lstat(e.path))
                        for e in sorted(os.scandir(cur_disp), key=lambda x: x.name)
                    ]
                for name, st in entries:
                    if name in ("target", ".git", ".lake"):
                        continue
                    nxt = cur_disp / name
                    if stat.S_ISLNK(st.st_mode):
                        if not _is_dir_excluded_by_ws_patterns(
                            ws_dir, excludes, nxt
                        ):
                            raise ValueError(
                                f"workspace member path must not traverse a symlink: {nxt}"
                            )
                        continue
                    if stat.S_ISDIR(st.st_mode):
                        child_fd = (
                            _open_child_dir_nofollow(
                                active_fd,
                                name,
                                (st.st_dev, st.st_ino),
                                "workspace member dir",
                            )
                            if os.name == "posix"
                            else None
                        )
                        stack.append((child_fd, nxt, (*rel_parts, name)))
            finally:
                if dir_fd is not None:
                    os.close(dir_fd)
    finally:
        while stack:
            leftover_fd, _, _ = stack.pop()
            if leftover_fd is not None:
                os.close(leftover_fd)
        if os.name == "posix" and root_fd >= 0:
            os.close(root_fd)
    return sorted(matched)


def _collect_manifest_referenced_dirs(
    parsed: dict[str, Any],
    cur_dir: Path,
    *,
    include_workspace_members: bool,
    store_prefix: Path,
) -> tuple[list[Path], list[Path]]:
    dirs: list[Path] = []
    store_dirs: list[Path] = []

    def _scan_deps(tbl: Any) -> None:
        if not isinstance(tbl, dict):
            return
        for val in tbl.values():
            if not isinstance(val, dict):
                continue
            raw_p = val.get("path")
            if isinstance(raw_p, str):
                cand, is_store = _normalize_manifest_rel_path(
                    cur_dir,
                    raw_p,
                    store_prefix=store_prefix,
                    allow_store_abs=True,
                    label="Cargo dependency path",
                )
                if is_store:
                    store_dirs.append(cand)
                else:
                    norm = _check_manifest_dir_no_links(
                        cand, "Cargo path dependency"
                    )
                    if norm is not None:
                        dirs.append(norm)

    def _scan_target_file(raw_p: Any, lbl: str) -> None:
        if not isinstance(raw_p, str):
            return
        joined_f, _ = _normalize_manifest_rel_path(
            cur_dir,
            raw_p,
            store_prefix=store_prefix,
            allow_store_abs=False,
            label=lbl,
        )
        norm = _check_manifest_dir_no_links(joined_f.parent, lbl)
        if norm is not None:
            dirs.append(norm)

    for k in ("dependencies", "dev-dependencies", "build-dependencies"):
        _scan_deps(parsed.get(k))
    target_tbl = parsed.get("target")
    if isinstance(target_tbl, dict):
        for cfg_val in target_tbl.values():
            if isinstance(cfg_val, dict):
                for k in (
                    "dependencies",
                    "dev-dependencies",
                    "build-dependencies",
                ):
                    _scan_deps(cfg_val.get(k))
    patch_tbl = parsed.get("patch")
    if isinstance(patch_tbl, dict):
        for src_val in patch_tbl.values():
            _scan_deps(src_val)
    _scan_deps(parsed.get("replace"))
    pkg_tbl = parsed.get("package")
    if isinstance(pkg_tbl, dict):
        for k in ("build", "readme", "license-file"):
            _scan_target_file(pkg_tbl.get(k), f"package.{k}")
    lib_tbl = parsed.get("lib")
    if isinstance(lib_tbl, dict):
        _scan_target_file(lib_tbl.get("path"), "lib.path")
    for arr_k in ("bin", "example", "test", "bench"):
        arr = parsed.get(arr_k)
        if isinstance(arr, list):
            for item in arr:
                if isinstance(item, dict):
                    _scan_target_file(item.get("path"), f"{arr_k}.path")

    ws_tbl = parsed.get("workspace")
    if isinstance(ws_tbl, dict):
        _scan_deps(ws_tbl.get("dependencies"))
        ws_pkg = ws_tbl.get("package")
        if isinstance(ws_pkg, dict):
            for k in ("readme", "license-file"):
                _scan_target_file(ws_pkg.get(k), f"workspace.package.{k}")
        if include_workspace_members:
            raw_ex = ws_tbl.get("exclude", [])
            excludes = (
                [x for x in raw_ex if isinstance(x, str)]
                if isinstance(raw_ex, list)
                else []
            )
            for m_key in ("members", "default-members"):
                raw_m = ws_tbl.get(m_key, [])
                if not isinstance(raw_m, list):
                    continue
                for pat in raw_m:
                    if not isinstance(pat, str) or not pat.strip():
                        continue
                    trimmed = pat.strip()
                    if any(ch in trimmed for ch in "*?["):
                        dirs.extend(
                            _expand_glob_ws_members_from_fd(
                                cur_dir, trimmed, excludes
                            )
                        )
                    else:
                        cand, _ = _normalize_manifest_rel_path(
                            cur_dir,
                            trimmed,
                            store_prefix=store_prefix,
                            allow_store_abs=False,
                            label="workspace member",
                        )
                        norm = _check_manifest_dir_no_links(
                            cand, "workspace member"
                        )
                        if (
                            norm is not None
                            and not _is_dir_excluded_by_ws_patterns(
                                cur_dir, excludes, norm
                            )
                        ):
                            dirs.append(norm)
    return dirs, store_dirs


def _copy_cargo_source_dir_to_staging(
    src_dir: Path,
    dst_dir: Path,
    *,
    copy_full: bool,
    reject_ambient: bool = True,
    skip_repo_dirs: bool = True,
    skip_git_anywhere: bool = False,
    label: str = "manifest sources",
) -> None:
    forbidden = frozenset({".cargo", "rust-toolchain", "rust-toolchain.toml"})
    if os.name != "posix":
        if not copy_full:
            dst_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
            for e in sorted(os.scandir(src_dir), key=lambda x: x.name):
                if reject_ambient and e.name in forbidden:
                    raise ValueError(
                        f"ambient `{e.name}` entry rejected in source tree: {e.path}"
                    )
                p = Path(e.path)
                st = os.lstat(p)
                if stat.S_ISLNK(st.st_mode):
                    if e.name in ("Cargo.toml", "Cargo.lock"):
                        raise ValueError(
                            f"workspace root file must not be a symlink: {p}"
                        )
                    continue
                if stat.S_ISREG(st.st_mode):
                    _copy_verified_regular_file(p, dst_dir / e.name, label)
            return
        for cur_root_str, dirnames, filenames in os.walk(
            src_dir, followlinks=False
        ):
            cur_root = Path(cur_root_str)
            rel_cur = cur_root.relative_to(src_dir)
            dirnames[:] = sorted(
                d
                for d in dirnames
                if not (skip_git_anywhere and d == ".git")
                and not (
                    skip_repo_dirs
                    and (
                        d == ".git"
                        or (rel_cur == Path(".") and d in ("target", ".lake"))
                    )
                )
            )
            if reject_ambient:
                for name in (*dirnames, *filenames):
                    if name in forbidden:
                        raise ValueError(
                            f"ambient `{name}` entry rejected in source tree: {cur_root / name}"
                        )
            cur_dst = dst_dir / rel_cur if rel_cur != Path(".") else dst_dir
            cur_dst.mkdir(mode=0o700, parents=True, exist_ok=True)
            for fname in sorted(filenames):
                _copy_verified_regular_file(
                    cur_root / fname, cur_dst / fname, label
                )
        return

    src_root_fd = _open_dir_handle_no_symlinks(src_dir, label)
    if not copy_full:
        try:
            dst_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
            for name, st in _read_dir_entries_from_fd(
                src_root_fd, "workspace root"
            ):
                if reject_ambient and name in forbidden:
                    raise ValueError(
                        f"ambient `{name}` entry rejected in workspace root: {src_dir / name}"
                    )
                if stat.S_ISLNK(st.st_mode):
                    if name in ("Cargo.toml", "Cargo.lock"):
                        raise ValueError(
                            f"workspace root file must not be a symlink: {src_dir / name}"
                        )
                    continue
                if stat.S_ISREG(st.st_mode):
                    fd, opened_st = _open_regular_file_from_fd(
                        src_root_fd,
                        name,
                        (st.st_dev, st.st_ino),
                        False,
                        "workspace file",
                    )
                    try:
                        _copy_opened_file_to_new_dst(
                            fd,
                            opened_st.st_mode,
                            dst_dir / name,
                            "workspace file",
                        )
                    finally:
                        os.close(fd)
        finally:
            os.close(src_root_fd)
        return

    stack: list[tuple[int | None, tuple[str, ...], Path, Path]] = [
        (None, (), src_dir, dst_dir)
    ]
    try:
        dst_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        while stack:
            cur_fd, rel_parts, cur_disp, cur_dst = stack.pop()
            active_fd = src_root_fd if cur_fd is None else cur_fd
            try:
                for name, st in _read_dir_entries_from_fd(active_fd, label):
                    p = cur_disp / name
                    if reject_ambient and name in forbidden:
                        raise ValueError(
                            f"ambient `{name}` entry rejected inside {label}: {p}"
                        )
                    if stat.S_ISLNK(st.st_mode):
                        raise ValueError(
                            f"{label} must not contain a symlink: {p}"
                        )
                    if stat.S_ISDIR(st.st_mode):
                        child_fd = _open_child_dir_nofollow(
                            active_fd,
                            name,
                            (st.st_dev, st.st_ino),
                            label,
                        )
                        if (skip_git_anywhere and name == ".git") or (
                            skip_repo_dirs
                            and (
                                name == ".git"
                                or (
                                    not rel_parts
                                    and name in ("target", ".lake")
                                )
                            )
                        ):
                            os.close(child_fd)
                            continue
                        next_dst = cur_dst / name
                        next_dst.mkdir(mode=0o700, parents=True, exist_ok=True)
                        stack.append(
                            (child_fd, (*rel_parts, name), p, next_dst)
                        )
                    elif stat.S_ISREG(st.st_mode):
                        fd, opened_st = _open_regular_file_from_fd(
                            active_fd,
                            name,
                            (st.st_dev, st.st_ino),
                            False,
                            label,
                        )
                        try:
                            _copy_opened_file_to_new_dst(
                                fd,
                                opened_st.st_mode,
                                cur_dst / name,
                                label,
                            )
                        finally:
                            os.close(fd)
                    else:
                        raise ValueError(
                            f"{label} contains non-regular entry: {p}"
                        )
            finally:
                if cur_fd is not None:
                    os.close(cur_fd)
    finally:
        while stack:
            leftover_fd, _, _, _ = stack.pop()
            if leftover_fd is not None:
                os.close(leftover_fd)
        os.close(src_root_fd)


def _compute_common_root_py(dirs: list[Path]) -> Path:
    if not dirs:
        raise ValueError("source staging graph is empty")
    prefix = list(dirs[0].parts)
    for d in dirs[1:]:
        parts = d.parts
        limit = 0
        for a, b in zip(prefix, parts):
            if a != b:
                break
            limit += 1
        prefix = prefix[:limit]
    if not prefix:
        raise ValueError("--mir-eval-manifest dependencies lack a common root")
    common = Path(*prefix)
    if common == common.parent:
        raise ValueError(
            f"--mir-eval-manifest dependencies must share a non-root staging ancestor (got {common})"
        )
    return common


def _stage_mir_eval_source_graph(
    manifest: Path,
    caller_cwd: Path,
    *,
    tmp_parent: str | None,
    exit_stack: contextlib.ExitStack,
    store_prefix: Path = _STORE_PREFIX,
) -> _PreparedMirEvalSources:
    store_manifest = _resolve_store_contained_entry(
        manifest,
        "mir_eval_manifest",
        store_prefix=store_prefix,
        base_dir=caller_cwd,
    )
    if store_manifest is not None:
        work_dir = store_manifest.parent
        default_roots = _workspace_target_roots(work_dir)
        _validate_store_contained_dir_tree(
            work_dir,
            store_prefix=store_prefix,
            base_dir=caller_cwd,
            label="mir_eval_manifest store sources",
        )
        locked_crates = (
            _read_locked_registry_crates_from_dir(
                work_dir, "mir_eval_manifest store"
            )
            or ()
        )
        return _PreparedMirEvalSources(
            canon_orig_manifest=store_manifest,
            canon_orig_work_dir=work_dir,
            default_roots=default_roots,
            staged_manifest=store_manifest,
            staged_work_dir=work_dir,
            staging_root=None,
            pinned_root_prefix=None,
            locked_registry_crates=locked_crates,
        )

    with contextlib.ExitStack() as open_stack:
        opened_manifest = _open_verified_executable_via_dirfd(
            manifest,
            caller_cwd,
            reject_hardlinks=True,
            label="mir_eval_manifest",
            exit_stack=open_stack,
        )
        canon_orig_manifest = opened_manifest.path
        canon_orig_work_dir = canon_orig_manifest.parent
        if opened_manifest.fd is not None:
            os.lseek(opened_manifest.fd, 0, os.SEEK_SET)
            raw_bytes = os.fdopen(
                opened_manifest.fd, "rb", closefd=False
            ).read()
        else:
            raw_bytes = canon_orig_manifest.read_bytes()
    try:
        root_toml = tomllib.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(
            f"invalid mir_eval_manifest {canon_orig_manifest}: {exc}"
        ) from exc
    if not isinstance(root_toml, dict):
        raise ValueError(
            f"invalid mir_eval_manifest table: {canon_orig_manifest}"
        )

    default_roots = _workspace_target_roots(canon_orig_work_dir)
    ws_root: Path | None = None
    pkg_tbl = root_toml.get("package")
    pkg_ws = pkg_tbl.get("workspace") if isinstance(pkg_tbl, dict) else None
    if isinstance(pkg_ws, str):
        cand_ws, _ = _normalize_manifest_rel_path(
            canon_orig_work_dir,
            pkg_ws,
            store_prefix=store_prefix,
            allow_store_abs=False,
            label="package.workspace",
        )
        ws_root = _check_manifest_dir_no_links(cand_ws, "package.workspace")
    elif "workspace" not in root_toml:
        for anc in default_roots[1:]:
            res = _read_cargo_toml_via_dirfd(anc, "ancestor Cargo.toml")
            if res is None:
                continue
            anc_toml, _ = res
            ws_tbl = anc_toml.get("workspace")
            if isinstance(ws_tbl, dict):
                raw_ex = ws_tbl.get("exclude", [])
                excludes = (
                    [x for x in raw_ex if isinstance(x, str)]
                    if isinstance(raw_ex, list)
                    else []
                )
                if not _is_dir_excluded_by_ws_patterns(
                    anc, excludes, canon_orig_work_dir
                ):
                    ws_root = anc
                break

    collected: dict[Path, bool] = {canon_orig_work_dir: True}
    queue: deque[tuple[Path, bool, dict[str, Any] | None]] = deque(
        [(canon_orig_work_dir, "workspace" in root_toml, root_toml)]
    )
    if ws_root is not None and ws_root != canon_orig_work_dir:
        ws_res = _read_cargo_toml_via_dirfd(ws_root, "workspace Cargo.toml")
        if ws_res is not None:
            ws_toml, _ = ws_res
            collected[ws_root] = "package" in ws_toml
            queue.append((ws_root, True, ws_toml))

    while queue:
        cur_dir, include_members, pre_toml = queue.popleft()
        if pre_toml is None:
            res = _read_cargo_toml_via_dirfd(cur_dir, "Cargo manifest")
            if res is None:
                continue
            parsed = res[0]
        else:
            parsed = pre_toml
        next_dirs, store_dirs = _collect_manifest_referenced_dirs(
            parsed,
            cur_dir,
            include_workspace_members=include_members,
            store_prefix=store_prefix,
        )
        for s_dir in store_dirs:
            _validate_store_contained_dir_tree(
                s_dir,
                store_prefix=store_prefix,
                base_dir=caller_cwd,
                label="store dependency sources",
            )
        for nd in next_dirs:
            if nd not in collected:
                collected[nd] = True
                queue.append((nd, False, None))
            elif not collected[nd]:
                collected[nd] = True
                queue.append((nd, False, None))

    common_root = _compute_common_root_py(sorted(collected.keys()))
    full_roots = {d for d, full in collected.items() if full}
    rel_manifest = canon_orig_manifest.relative_to(common_root)
    rel_work = canon_orig_work_dir.relative_to(common_root)
    lock_rels: list[Path] = [rel_work]
    if ws_root is not None and ws_root.is_relative_to(common_root):
        rel_ws = ws_root.relative_to(common_root)
        if rel_ws != rel_work:
            lock_rels.insert(0, rel_ws)
    locked_crates: tuple[tuple[str, str, str | None], ...] = ()
    staged_priv_root: Path | None = None

    def _populate_sources(priv_root: Path, pinned_root: Path) -> None:
        nonlocal locked_crates, staged_priv_root
        staged_priv_root = priv_root
        for d, copy_full in sorted(collected.items()):
            if any(anc in full_roots for anc in d.parents):
                continue
            rel = d.relative_to(common_root)
            dst_dir = pinned_root if rel == Path(".") else (pinned_root / rel)
            _copy_cargo_source_dir_to_staging(d, dst_dir, copy_full=copy_full)

        for lock_rel in lock_rels:
            found_crates = _read_locked_registry_crates_from_staged_dir(
                pinned_root, lock_rel, "staged workspace"
            )
            if found_crates is not None:
                locked_crates = found_crates
                break

    pinned_root = _build_pinned_staging_dir(
        exit_stack,
        prefix="anneal-mir-eval-src-",
        base_dir=caller_cwd,
        tmp_parent=tmp_parent,
        label="Leg 3 manifest sources",
        populate=_populate_sources,
    )
    assert staged_priv_root is not None
    staged_manifest = pinned_root / rel_manifest
    staged_work_dir = (
        pinned_root if rel_work == Path(".") else (pinned_root / rel_work)
    )
    pin_prefix = (
        str(pinned_root)
        if str(pinned_root).startswith("/proc/self/fd/")
        else None
    )
    return _PreparedMirEvalSources(
        canon_orig_manifest=canon_orig_manifest,
        canon_orig_work_dir=canon_orig_work_dir,
        default_roots=default_roots,
        staged_manifest=staged_manifest,
        staged_work_dir=staged_work_dir,
        staging_root=staged_priv_root,
        pinned_root_prefix=pin_prefix,
        locked_registry_crates=locked_crates,
    )


def _resolve_mir_eval_staging_dir(
    staging_dir: Path | None,
    manifest_canon: Path,
    default_roots: tuple[Path, ...],
    *,
    caller_cwd: Path,
    work_dir: Path,
) -> Path:
    if staging_dir is not None:
        resolved = _resolve_cli_path(
            staging_dir,
            "mir-eval staging dir",
            base_dir=caller_cwd,
            require_dir_components=True,
        )
        if not resolved.is_dir():
            raise ValueError(
                f"mir-eval staging dir must be an existing directory: {resolved}"
            )
        return resolved.resolve(strict=True)
    fallback_td = _default_pinned_target_dir(manifest_canon, default_roots)
    return _resolve_cli_path(
        fallback_td / ".anneal-isolated-bins",
        "isolated bin dir",
        base_dir=work_dir,
        require_dir_components=True,
    )


def maybe_run_mir_eval_manifest(
    manifest: Path | None,
    *,
    skip_tests: bool = False,
    timeout_secs: float = MIR_EVAL_MANIFEST_TIMEOUT_SECS,
    staging_dir: Path | None = None,
    staging_exit_stack: contextlib.ExitStack | None = None,
) -> tuple[dict[str, Any], Path | None]:
    """Run and build an explicit `anneal-mir-eval` Cargo manifest when given."""
    if manifest is None:
        return (
            {
                "executed": False,
                "passed": None,
                "reason": "no --mir-eval-manifest supplied",
            },
            None,
        )
    if staging_dir is not None and staging_exit_stack is None:
        raise ValueError(
            "staging_dir requires staging_exit_stack so staged evaluator root "
            "can be frozen and descriptor-pinned"
        )

    caller_cwd = Path.cwd()
    manifest_abs = _resolve_executable_cli_path(
        manifest, "mir_eval_manifest", base_dir=caller_cwd
    )
    if not manifest_abs.is_file():
        return (
            {
                "executed": False,
                "passed": False,
                "manifest_path": str(manifest_abs),
                "error": f"missing mir-eval manifest: {manifest_abs}",
            },
            None,
        )

    with contextlib.ExitStack() as cleanup:
        tmp_parent = os.environ.get("TMPDIR") or None
        if tmp_parent:
            tmp_p = _resolve_cli_path(
                Path(tmp_parent),
                "TMPDIR",
                base_dir=caller_cwd,
                require_dir_components=True,
            )
            if not tmp_p.is_dir():
                raise ValueError(f"TMPDIR must be an existing directory: {tmp_p}")
            tmp_parent = str(tmp_p.resolve(strict=True))
        prepared_src = _stage_mir_eval_source_graph(
            manifest,
            caller_cwd,
            tmp_parent=tmp_parent,
            exit_stack=cleanup,
        )
        manifest_canon = prepared_src.canon_orig_manifest
        orig_work_dir = prepared_src.canon_orig_work_dir
        default_roots = prepared_src.default_roots
        pinned_ch = _reject_ambient_cargo_configs(
            orig_work_dir,
            default_roots,
            base_dir=caller_cwd,
            exit_stack=cleanup,
            tmp_parent=tmp_parent,
            locked_crates=prepared_src.locked_registry_crates,
        )
        cargo_opened = _resolve_cargo_command_opened(caller_cwd, cleanup)
        env = _build_child_env(
            caller_cwd,
            target_base_dir=orig_work_dir,
            default_target_roots=default_roots,
            exit_stack=cleanup,
        )
        if pinned_ch is not None:
            env["CARGO_HOME"] = str(pinned_ch)
        cargo, linker_cfg_args = _pin_cargo_rustc_env(
            env,
            caller_cwd,
            str(cargo_opened.path),
            work_dir=prepared_src.staged_work_dir,
            orig_work_dir=orig_work_dir,
            cargo_opened=cargo_opened,
            exit_stack=cleanup,
            cargo_home_pinned=pinned_ch is not None,
        )
        stage_root: Path | None = None
        pinned_stage_root: Path | None = None
        pinned_stage_fd: int | None = None
        if staging_dir is not None:
            assert staging_exit_stack is not None
            stage_root = _resolve_mir_eval_staging_dir(
                staging_dir,
                manifest_canon,
                default_roots,
                caller_cwd=caller_cwd,
                work_dir=orig_work_dir,
            )
            if os.name == "posix":
                os.chmod(stage_root, 0o700)
            pinned_stage_root, pinned_stage_fd = _begin_pinned_staging_dir_fd(
                staging_exit_stack, stage_root, "mir-eval staging"
            )
            if pinned_stage_fd is not None:
                staging_exit_stack.callback(
                    _restore_dir_write_perms_from_fd, pinned_stage_fd
                )
            else:
                staging_exit_stack.callback(
                    _restore_dir_write_perms_top_down, stage_root
                )
        elif staging_exit_stack is None:
            stage_root = _resolve_mir_eval_staging_dir(
                None,
                manifest_canon,
                default_roots,
                caller_cwd=caller_cwd,
                work_dir=orig_work_dir,
            )
        # Build inside a fresh private 0o700 target directory rather than
        # reusing workspace `target/` or ambient `CARGO_TARGET_DIR`.
        env.pop("CARGO_TARGET_DIR", None)
        tmp_parent = env.get("TMPDIR")
        wrapper_clear_args = [
            "--config",
            'build.rustc-wrapper=""',
            "--config",
            'build.rustc-workspace-wrapper=""',
            *linker_cfg_args,
        ]
        priv_td_obj = cleanup.enter_context(
            tempfile.TemporaryDirectory(
                prefix="anneal-mir-eval-target-", dir=tmp_parent
            )
        )
        raw_priv_td = priv_td_obj
        if os.name == "posix":
            os.chmod(raw_priv_td, 0o700)
        priv_td = _resolve_cli_path(
            Path(raw_priv_td),
            "private Cargo target dir",
            base_dir=caller_cwd,
            require_dir_components=True,
        ).resolve(strict=True)
        if not skip_tests:
            try:
                test_res = _run_subcommand_process_group(
                    [
                        cargo,
                        "test",
                        "--manifest-path",
                        str(prepared_src.staged_manifest),
                        "--target-dir",
                        str(priv_td),
                        "--locked",
                        *wrapper_clear_args,
                    ],
                    cwd=prepared_src.staged_work_dir,
                    env=env,
                    timeout_secs=timeout_secs,
                )
            except subprocess.TimeoutExpired as exc:
                tail = _format_timeout_tail(exc)
                detail = f"cargo test timed out after {timeout_secs:g}s"
                if tail:
                    detail = f"{detail}: {tail}"
                return (
                    {
                        "executed": True,
                        "passed": False,
                        "manifest_path": str(manifest_abs),
                        "error": detail,
                    },
                    None,
                )
            if test_res.returncode != 0:
                return (
                    {
                        "executed": True,
                        "passed": False,
                        "manifest_path": str(manifest_abs),
                        "error": (test_res.stderr or test_res.stdout)[-1200:],
                    },
                    None,
                )

        try:
            build_res = _run_subcommand_process_group(
                [
                    cargo,
                    "build",
                    "--manifest-path",
                    str(prepared_src.staged_manifest),
                    "--target-dir",
                    str(priv_td),
                    "--locked",
                    "--bin",
                    "anneal-mir-eval",
                    "--message-format=json",
                    *wrapper_clear_args,
                ],
                cwd=prepared_src.staged_work_dir,
                env=env,
                timeout_secs=timeout_secs,
            )
        except subprocess.TimeoutExpired as exc:
            tail = _format_timeout_tail(exc)
            detail = f"cargo build timed out after {timeout_secs:g}s"
            if tail:
                detail = f"{detail}: {tail}"
            return (
                {
                    "executed": True,
                    "passed": False,
                    "manifest_path": str(manifest_abs),
                    "error": detail,
                },
                None,
            )
        if build_res.returncode != 0:
            return (
                {
                    "executed": True,
                    "passed": False,
                    "manifest_path": str(manifest_abs),
                    "error": (build_res.stderr or build_res.stdout)[-1200:],
                },
                None,
            )

        extracted_bin = _extract_built_executable(
            build_res.stdout,
            "anneal-mir-eval",
            manifest_canon,
            staged_manifest=prepared_src.staged_manifest,
            pinned_root_prefix=prepared_src.pinned_root_prefix,
            staging_root=prepared_src.staging_root,
        )
        if extracted_bin is None:
            return (
                {
                    "executed": True,
                    "passed": False,
                    "manifest_path": str(manifest_abs),
                    "error": (
                        "cargo build JSON output lacked compiler-artifact "
                        "executable for anneal-mir-eval"
                    ),
                },
                None,
            )
        bin_path = _resolve_cli_path(
            extracted_bin, "anneal-mir-eval binary", base_dir=priv_td
        )
        if not bin_path.is_file():
            return (
                {
                    "executed": True,
                    "passed": False,
                    "manifest_path": str(manifest_abs),
                    "error": f"expected built binary at {bin_path}",
                },
                None,
            )
        opened_built = _open_verified_executable_via_dirfd(
            extracted_bin,
            priv_td,
            reject_hardlinks=False,
            allow_cargo_deps_hardlink=True,
            label="built anneal-mir-eval",
            exit_stack=cleanup,
        )
        if not opened_built.path.is_relative_to(priv_td):
            raise ValueError(
                "built anneal-mir-eval escaped expected Cargo target "
                f"directory: {opened_built.path}"
            )
        if staging_dir is None and staging_exit_stack is not None:
            isolated_bin = _stage_verified_executable(
                opened_built.path,
                "anneal-mir-eval",
                allow_cargo_deps_hardlink=True,
                exit_stack=staging_exit_stack,
                base_dir=priv_td,
                tmp_parent=tmp_parent,
                pin_proc_fd=True,
                preopened=opened_built,
            )
        elif stage_root is not None and pinned_stage_root is not None:
            iso_dir = pinned_stage_root / ".anneal-isolated-bins"
            iso_dir.mkdir(mode=0o700)
            staged_bin = _materialize_cargo_built_executable(
                opened_built.path,
                priv_td,
                "anneal-mir-eval",
                dest_dir=iso_dir,
                force_copy=True,
                chmod_mode=0o555,
                preopened=opened_built,
                dest_is_pinned=True,
            )
            if pinned_stage_fd is not None:
                _freeze_staging_dir_from_fd(
                    pinned_stage_fd, pinned_stage_root, "mir-eval staging"
                )
                post_st = os.fstat(pinned_stage_fd)
                if (
                    not stat.S_ISDIR(post_st.st_mode)
                    or stat.S_IMODE(post_st.st_mode) != 0o555
                ):
                    raise ValueError(
                        "mir-eval staging root permissions altered after "
                        f"freeze: {stage_root}"
                    )
            else:
                _freeze_staging_dir(pinned_stage_root, "mir-eval staging")
            isolated_bin = staged_bin
            if sys.platform.startswith("linux"):
                _verify_pinned_proc_fd_executable(
                    isolated_bin, "staged anneal-mir-eval"
                )
        else:
            assert stage_root is not None
            isolated_bin = _materialize_cargo_built_executable(
                opened_built.path,
                priv_td,
                "anneal-mir-eval",
                dest_dir=stage_root,
                force_copy=True,
                chmod_mode=0o555,
                preopened=opened_built,
            )
        return (
            {
                "executed": not skip_tests,
                "passed": True if not skip_tests else None,
                "manifest_path": str(manifest_abs),
            },
            isolated_bin,
        )


REQUIRED_FUZZ_METRICS_KEYS = frozenset(
    {
        "total_cases",
        "targeted_ub_probes",
        "admission_eligible_cases",
        "admitted_cases",
        "admission_rate",
        "bi_fault_equiv_count",
        "ub_probes_agreed_count",
        "conservative_over_approx_count",
        "spurious_lean_ub_count",
        "admitted_authority_ub_count",
        "unsound_accept_count",
        "authority_disagreement_count",
        "move_reinit_exercised_count",
    }
)

FUZZ_SCHEMA = "anneal-differential-fuzz/v1"
_VALID_OUTCOME_KINDS = frozenset(
    {
        "returned",
        "panic",
        "unwound",
        "abnormal_abort",
        "undefined_behavior",
        "unsupported",
        "init_unsupported",
        "out_of_fuel",
        "tool_error",
    }
)


_INT_KIND_BITS: dict[str, int] = {
    "u8": 8,
    "i8": 8,
    "u16": 16,
    "i16": 16,
    "u32": 32,
    "i32": 32,
    "u64": 64,
    "i64": 64,
    "u128": 128,
    "i128": 128,
    "usize": 64,
    "isize": 64,
}


def _is_valid_sha256_hex(raw: Any) -> bool:
    return (
        isinstance(raw, str)
        and len(raw) == 64
        and all(ch in "0123456789abcdef" for ch in raw)
    )


def _reject_json_constant(token: str) -> Any:
    raise ValueError(f"non-finite JSON constant {token!r} is forbidden")


def _is_bounded_rate(raw: Any, *, upper: float = 1.0) -> bool:
    if isinstance(raw, bool) or not isinstance(raw, (int, float)):
        return False
    val = float(raw)
    return math.isfinite(val) and (0.0 <= val <= upper)


def _validate_bounded_rate(
    raw: Any, label: str, *, upper: float = 1.0
) -> float:
    if not _is_bounded_rate(raw, upper=upper):
        raise ValueError(
            f"{label} must be a finite float in 0.0..={upper}, got {raw!r}"
        )
    return float(raw)


def _validate_canonical_int_bits(
    int_kind: Any, raw_bits: Any, label: str
) -> None:
    if not isinstance(int_kind, str) or int_kind not in _INT_KIND_BITS:
        raise ValueError(f"{label} invalid `int_kind` {int_kind!r}")
    if (
        not isinstance(raw_bits, str)
        or not raw_bits
        or not raw_bits.isascii()
        or not raw_bits.isdigit()
        or (len(raw_bits) > 1 and raw_bits.startswith("0"))
    ):
        raise ValueError(f"{label} non-canonical decimal `bits` {raw_bits!r}")
    bits_val = int(raw_bits)
    width = _INT_KIND_BITS[int_kind]
    if bits_val < 0 or bits_val >= (1 << width):
        raise ValueError(
            f"{label} unmasked `bits` {raw_bits!r} out of {int_kind} range"
        )


def _validate_mir_value(
    val: Any, label: str, *, allow_enum: bool = False
) -> None:
    if not isinstance(val, dict):
        raise ValueError(f"{label} must be a JSON object")
    vkind = val.get("kind")
    keys = set(val.keys())
    if vkind == "int":
        if keys != {"kind", "int_kind", "bits"}:
            raise ValueError(f"{label} `int` value has unexpected keys")
        _validate_canonical_int_bits(val["int_kind"], val["bits"], label)
    elif vkind == "bool":
        if keys != {"kind", "value"} or not isinstance(val["value"], bool):
            raise ValueError(f"{label} invalid `bool` value")
    elif vkind == "char":
        scalar = val.get("scalar")
        if (
            keys != {"kind", "scalar"}
            or isinstance(scalar, bool)
            or not isinstance(scalar, int)
            or scalar < 0
            or scalar > 0x10FFFF
            or (0xD800 <= scalar <= 0xDFFF)
        ):
            raise ValueError(f"{label} invalid Unicode scalar `char` value")
    elif vkind == "ordering":
        if keys != {"kind", "value"} or val["value"] not in (
            "less",
            "equal",
            "greater",
        ):
            raise ValueError(f"{label} invalid `ordering` value")
    elif vkind == "unit":
        if keys != {"kind"}:
            raise ValueError(f"{label} `unit` value has extra keys")
    elif vkind == "overflow_pair":
        if keys != {"kind", "int_kind", "bits", "overflow"} or not isinstance(
            val["overflow"], bool
        ):
            raise ValueError(f"{label} invalid `overflow_pair` value")
        _validate_canonical_int_bits(val["int_kind"], val["bits"], label)
    elif vkind == "enum":
        if not allow_enum:
            raise ValueError(f"{label} enum return values are unsupported")
        vidx = val.get("variant_index")
        etype = val.get("enum_type")
        variant = val.get("variant")
        variants = _GEN_ENUM_VARIANTS.get(etype) if isinstance(etype, str) else None
        if (
            keys != {"kind", "enum_type", "variant", "variant_index"}
            or variants is None
            or not isinstance(variant, str)
            or isinstance(vidx, bool)
            or not isinstance(vidx, int)
            or not (0 <= vidx < len(variants))
            or variants[vidx] != variant
        ):
            raise ValueError(f"{label} invalid `enum` value")
    else:
        raise ValueError(f"{label} unknown `MirValue` kind {vkind!r}")


def _validate_observed_outcome(obj: Any, label: str) -> dict[str, Any]:
    if not isinstance(obj, dict):
        raise ValueError(f"{label} must be a JSON object")
    kind = obj.get("kind")
    if not isinstance(kind, str) or kind not in _VALID_OUTCOME_KINDS:
        raise ValueError(f"{label} has invalid outcome kind {kind!r}")
    if kind == "returned":
        if set(obj.keys()) != {"kind", "value"}:
            raise ValueError(f"{label} `returned` outcome has unexpected keys")
        _validate_mir_value(obj.get("value"), f"{label}.value")
    else:
        if set(obj.keys()) != {"kind", "detail"} or not isinstance(
            obj.get("detail"), str
        ):
            raise ValueError(f"{label} `{kind}` outcome missing string `detail`")
    return obj


def _to_terminal_outcome(obj: dict[str, Any]) -> tuple[str, Any] | None:
    kind = obj["kind"]
    if kind == "tool_error":
        return None
    if kind == "returned":
        return ("returned", obj["value"])
    if kind in ("panic", "unwound"):
        return ("unwound", None)
    if kind == "abnormal_abort":
        return ("aborted", None)
    if kind == "undefined_behavior":
        return ("undefined_behavior", None)
    if kind in ("unsupported", "init_unsupported"):
        return ("unsupported", None)
    return ("out_of_fuel", None)


def _outcomes_agree_mir_json(
    lean: dict[str, Any], mir_eval: dict[str, Any]
) -> bool:
    lk = lean["kind"]
    mk = mir_eval["kind"]
    if lk == "returned" and mk == "returned":
        return lean["value"] == mir_eval["value"]
    if lk == "undefined_behavior" and mk == "undefined_behavior":
        return True
    if lk in ("init_unsupported", "unsupported") and mk == "unsupported":
        return True
    if lk == "out_of_fuel" and mk == "out_of_fuel":
        return True
    if lk in ("unwound", "panic") and mk in ("unwound", "panic"):
        return True
    if lk == "abnormal_abort" and mk == "abnormal_abort":
        return True
    return False


def _derive_fuzz_case_evaluation(
    case: dict[str, Any],
    *,
    idx: int,
    has_rustc_leg: bool,
    has_mir_eval_leg: bool,
) -> tuple[str, bool, str, str | None]:
    """Recompute `(agreement, is_spurious_lean_ub, rustc_status, disclosed_gap)`."""
    miri = _validate_observed_outcome(case.get("miri"), f"case[{idx}].miri")
    lean = _validate_observed_outcome(case.get("lean"), f"case[{idx}].lean")
    raw_cap_rej = case.get("capture_rejected")
    if raw_cap_rej is not None and (
        not isinstance(raw_cap_rej, str) or not raw_cap_rej
    ):
        raise ValueError(f"case[{idx}] invalid `capture_rejected`")

    raw_rustc = case.get("rustc")
    miri_ub_free = miri["kind"] in (
        "returned",
        "panic",
        "unwound",
        "abnormal_abort",
    )
    if has_rustc_leg and miri_ub_free and raw_rustc is None:
        raise ValueError(f"case[{idx}] missing `rustc` outcome for active leg")
    if has_rustc_leg and not miri_ub_free and raw_rustc is not None:
        raise ValueError(
            f"case[{idx}] must not execute compiled `rustc` without UB-free Miri outcome"
        )
    rustc = (
        None
        if raw_rustc is None
        else _validate_observed_outcome(raw_rustc, f"case[{idx}].rustc")
    )

    raw_mir_eval = case.get("mir_eval")
    if has_mir_eval_leg and raw_cap_rej is None and raw_mir_eval is None:
        raise ValueError(
            f"case[{idx}] missing `mir_eval` outcome for active leg"
        )
    mir_eval = (
        None
        if raw_mir_eval is None
        else _validate_observed_outcome(raw_mir_eval, f"case[{idx}].mir_eval")
    )

    miri_term = _to_terminal_outcome(miri)
    if miri["kind"] == "undefined_behavior" and (
        has_rustc_leg or rustc is not None
    ):
        rustc_status = "ignored_due_to_miri_ub"
    elif rustc is None:
        rustc_status = "not_run"
    else:
        rustc_term = _to_terminal_outcome(rustc)
        if miri_term is None or rustc_term is None:
            rustc_status = "disagreement"
        elif miri_term[0] == "returned" and rustc_term[0] == "returned":
            rustc_status = (
                "agreed" if miri_term[1] == rustc_term[1] else "disagreement"
            )
        elif miri_term[0] == rustc_term[0] and miri_term[0] in (
            "unwound",
            "aborted",
        ):
            rustc_status = "agreed"
        else:
            rustc_status = "disagreement"

    if miri_term is None:
        return ("authority_disagreement", False, rustc_status, None)
    if rustc_status == "disagreement":
        return ("authority_disagreement", False, rustc_status, None)
    if miri_term[0] in ("unsupported", "out_of_fuel"):
        return ("authority_disagreement", False, rustc_status, None)
    if raw_cap_rej is not None:
        if lean["kind"] != "unsupported":
            raise ValueError(
                f"case[{idx}] has `capture_rejected` with non-unsupported "
                f"Lean outcome {lean['kind']!r}"
            )
        return (
            "conservative_over_approx_forward_sim_only",
            False,
            rustc_status,
            "unbridged_semantics",
        )
    if lean["kind"] == "init_unsupported":
        return ("authority_disagreement", False, rustc_status, None)
    lean_term = _to_terminal_outcome(lean)
    if lean_term is None:
        return ("authority_disagreement", False, rustc_status, None)

    mk, mv = miri_term
    lk, lv = lean_term
    if mk == "returned" and lk == "returned":
        primary: tuple[str, bool, str | None] = (
            ("bi_fault_equiv_agreement", False, None)
            if mv == lv
            else ("unsound_accept_critical", False, None)
        )
    elif mk == lk and mk in ("undefined_behavior", "unwound", "aborted"):
        primary = ("bi_fault_equiv_agreement", False, None)
    elif mk == "undefined_behavior" and lk in ("returned", "unwound", "aborted"):
        primary = ("unsound_accept_critical", False, None)
    elif mk in ("unwound", "aborted") and lk == "returned":
        primary = ("unsound_accept_critical", False, None)
    elif (mk, lk) in (("unwound", "aborted"), ("aborted", "unwound")):
        primary = ("unsound_accept_critical", False, None)
    elif mk == "returned" and lk in ("unwound", "aborted"):
        primary = ("unsound_accept_critical", False, None)
    elif lk == "out_of_fuel":
        primary = ("conservative_over_approx_forward_sim_only", False, "fuel_exhausted")
    elif lk == "unsupported":
        primary = (
            "conservative_over_approx_forward_sim_only",
            False,
            "unbridged_semantics",
        )
    else:
        primary = ("conservative_over_approx_forward_sim_only", True, None)

    is_primary_failure = (
        primary[0] in ("unsound_accept_critical", "authority_disagreement")
        or primary[1]
    )
    if not is_primary_failure and mir_eval is not None:
        if mir_eval["kind"] == "tool_error" or not _outcomes_agree_mir_json(
            lean, mir_eval
        ):
            return ("authority_disagreement", False, rustc_status, None)

    return (primary[0], primary[1], rustc_status, primary[2])


_MASK64 = (1 << 64) - 1


def _host_usize_max() -> int:
    """Return host pointer-width `usize::MAX` matching Rust CLI parsing."""
    return (1 << (struct.calcsize("P") * 8)) - 1
_ALL_INT_KINDS = (
    "u8",
    "u16",
    "u32",
    "u64",
    "u128",
    "usize",
    "i8",
    "i16",
    "i32",
    "i64",
    "i128",
    "isize",
)
_SIGNED_INT_KINDS = ("i8", "i16", "i32", "i64", "i128", "isize")
_GEN_ENUM_KINDS = (
    "GenSignedTag",
    "GenUnsignedTag",
    "GenSoloRepr",
    "GenZstUnit",
)
_GEN_ENUM_VARIANTS: dict[str, tuple[str, ...]] = {
    "GenSignedTag": ("NegFive", "Zero", "Four", "ThreeHundred"),
    "GenUnsignedTag": ("Alpha", "Beta", "Gamma"),
    "GenSoloRepr": ("Only",),
    "GenZstUnit": ("Only",),
}
_BOUNDARY_CHARS = (
    0x0000,
    0x0041,
    0x007F,
    0x00FF,
    0x03BB,
    0xD7FF,
    0xE000,
    0x10_FFFF,
)


def _splitmix64_next(state: int) -> tuple[int, int]:
    """Advance a 64-bit SplitMix64 state identically to `gen.rs`."""
    state = (state + 0x9E37_79B9_7F4A_7C15) & _MASK64
    z = state
    z = ((z ^ (z >> 30)) * 0xBF58_476D_1CE4_E5B9) & _MASK64
    z = ((z ^ (z >> 27)) * 0x94D0_49BB_1331_11EB) & _MASK64
    return state, (z ^ (z >> 31)) & _MASK64


class _SplitMix64:
    """SplitMix64 stream matching `gen.rs` for case input validation."""

    def __init__(self, state: int) -> None:
        self.state = state & _MASK64

    @classmethod
    def for_case(cls, master_seed: int, case_index: int) -> "_SplitMix64":
        mixed = (
            master_seed
            ^ ((case_index * 0x9E37_79B9_7F4A_7C15) & _MASK64)
            ^ 0xD1B5_4A32_D192_ED03
        ) & _MASK64
        rng = cls(mixed)
        rng.next_u64()
        rng.next_u64()
        return rng

    def next_u64(self) -> int:
        self.state, out = _splitmix64_next(self.state)
        return out

    def next_u128(self) -> int:
        hi = self.next_u64()
        lo = self.next_u64()
        return (hi << 64) | lo

    def gen_range(self, upper: int) -> int:
        return 0 if upper <= 1 else self.next_u64() % upper

    def coin(self, num: int, den: int) -> bool:
        return False if den == 0 else (self.next_u64() % den) < num

    def pick(self, items: tuple[Any, ...] | list[Any]) -> Any:
        return items[self.gen_range(len(items))]


def _choose_fuzz_category(
    rng: _SplitMix64, case_index: int, ub_ratio: float
) -> str:
    scale = 1_000_000_000
    if ub_ratio <= 0.0:
        ub_ppb = 0
    else:
        scaled = ub_ratio * float(scale)
        fl = math.floor(scaled)
        # Match Rust `f64::round()` (round half away from zero on `scaled > 0`).
        rounded = int(fl + 1) if (scaled - fl) >= 0.5 else int(fl)
        ub_ppb = max(1, min(850_000_000, rounded))

    if case_index == 0:
        return "safe_admitted"
    if case_index == 1:
        return "boundary_edge_case"
    if case_index == 2 and ub_ppb > 0:
        return "targeted_ub_probe"
    if case_index == 3:
        return "scope_control"

    roll = rng.next_u64() % scale
    if roll < ub_ppb:
        return "targeted_ub_probe"
    if roll < min(950_000_000, ub_ppb + 50_000_000):
        return "scope_control"
    if roll < min(980_000_000, ub_ppb + 350_000_000):
        return "boundary_edge_case"
    return "safe_admitted"


def _expected_fuzz_case_category(
    master_seed: int, case_index: int, ub_ratio: float
) -> str:
    """Derive the deterministic `GenCategory` from `(seed, index, ub_ratio)`."""
    rng = _SplitMix64.for_case(master_seed, case_index)
    return _choose_fuzz_category(rng, case_index, ub_ratio)


def _gen_boundary_bits_for_int(kind: str) -> list[int]:
    w = _INT_KIND_BITS[kind]
    mask = (1 << w) - 1
    vals = [0, 1 & mask, 2 & mask, mask, max(0, mask - 1)]
    if kind.startswith("i"):
        min_bits = 1 << (w - 1)
        max_bits = min_bits - 1
        vals.extend(
            [
                min_bits,
                (min_bits + 1) & mask,
                max_bits,
                max(0, max_bits - 1),
                mask,
                (-2) & mask,
                (-w) & mask,
            ]
        )
    vals.extend([(w - 1) & mask, w & mask, (w + 3) & mask])
    return list(dict.fromkeys(vals))


def _gen_int_value(
    rng: _SplitMix64, kind: str, boundary_bias: bool
) -> dict[str, Any]:
    mask = (1 << _INT_KIND_BITS[kind]) - 1
    if boundary_bias or rng.coin(3, 5):
        bits = rng.pick(_gen_boundary_bits_for_int(kind))
    else:
        bits = rng.next_u128() & mask
    return {"kind": "int", "int_kind": kind, "bits": str(bits)}


def _gen_value_for_type(
    rng: _SplitMix64, ty: tuple[str, ...], boundary_bias: bool
) -> dict[str, Any]:
    kind = ty[0]
    if kind == "int":
        return _gen_int_value(rng, ty[1], boundary_bias)
    if kind == "bool":
        return {"kind": "bool", "value": rng.coin(1, 2)}
    if kind == "char":
        if boundary_bias or rng.coin(3, 4):
            scalar = rng.pick(_BOUNDARY_CHARS)
        else:
            raw = (rng.next_u64() & 0xFFFF_FFFF) % 0x10_FFFF
            scalar = 0x03BB if 0xD800 <= raw <= 0xDFFF else raw
        return {"kind": "char", "scalar": scalar}
    if kind == "ordering":
        return {
            "kind": "ordering",
            "value": rng.pick(("less", "equal", "greater")),
        }
    ekind = ty[1]
    variants = _GEN_ENUM_VARIANTS[ekind]
    vidx = rng.gen_range(len(variants))
    return {
        "kind": "enum",
        "enum_type": ekind,
        "variant": variants[vidx],
        "variant_index": vidx,
    }


_GEN_CRATE_HEADER = (
    "#![allow(dead_code, unused_variables, "
    "unused_mut, unused_assignments, unused_parens, unreachable_code, "
    "unreachable_patterns, arithmetic_overflow, unconditional_panic, unused_unsafe)]\n"
)
_GEN_ENUM_PREAMBLE = (
    "pub const GEN_UNIT: () = ();\n\n"
    "#[repr(i16)]\n"
    "pub enum GenSignedTag {\n"
    "    NegFive = -5,\n"
    "    Zero = 0,\n"
    "    Four = 4,\n"
    "    ThreeHundred = 300,\n"
    "}\n\n"
    "pub const GEN_SIGNED_NEG_FIVE: GenSignedTag = GenSignedTag::NegFive;\n"
    "pub const GEN_SIGNED_ZERO: GenSignedTag = GenSignedTag::Zero;\n"
    "pub const GEN_SIGNED_FOUR: GenSignedTag = GenSignedTag::Four;\n"
    "pub const GEN_SIGNED_THREE_HUNDRED: GenSignedTag = GenSignedTag::ThreeHundred;\n\n"
    "#[repr(u8)]\n"
    "pub enum GenUnsignedTag {\n"
    "    Alpha = 0,\n"
    "    Beta = 7,\n"
    "    Gamma = 250,\n"
    "}\n\n"
    "pub const GEN_UNSIGNED_ALPHA: GenUnsignedTag = GenUnsignedTag::Alpha;\n"
    "pub const GEN_UNSIGNED_BETA: GenUnsignedTag = GenUnsignedTag::Beta;\n"
    "pub const GEN_UNSIGNED_GAMMA: GenUnsignedTag = GenUnsignedTag::Gamma;\n\n"
    "#[repr(u8)]\n"
    "pub enum GenSoloRepr {\n"
    "    Only = 42,\n"
    "}\n\n"
    "pub const GEN_SOLO_ONLY: GenSoloRepr = GenSoloRepr::Only;\n\n"
    "pub enum GenZstUnit {\n"
    "    Only,\n"
    "}\n\n"
    "pub const GEN_ZST_ONLY: GenZstUnit = GenZstUnit::Only;\n\n"
    "pub const GEN_ORD_LESS: core::cmp::Ordering = core::cmp::Ordering::Less;\n"
    "pub const GEN_ORD_EQUAL: core::cmp::Ordering = core::cmp::Ordering::Equal;\n"
    "pub const GEN_ORD_GREATER: core::cmp::Ordering = core::cmp::Ordering::Greater;\n"
)
_GEN_ARITH_OPS = (
    ("add", "+"),
    ("sub", "-"),
    ("mul", "*"),
    ("bit_and", "&"),
    ("bit_or", "|"),
    ("bit_xor", "^"),
)
_GEN_CMP_OPS = (
    ("eq", "=="),
    ("ne", "!="),
    ("lt", "<"),
    ("le", "<="),
    ("gt", ">"),
    ("ge", ">="),
)
_GEN_BOOL_BIN_OPS = (
    ("and", "&&"),
    ("or", "||"),
    ("bit_and", "&"),
    ("bit_or", "|"),
    ("bit_xor", "^"),
)
_UNSIGNED_NON_USIZE_INT_KINDS = ("u8", "u16", "u32", "u64", "u128")
_GEN_SYSROOT_NUM_OPS: tuple[tuple[str, bool], ...] = (
    ("unchecked_add", True),
    ("unchecked_sub", True),
    ("unchecked_mul", True),
    ("wrapping_add", False),
    ("wrapping_sub", False),
    ("wrapping_mul", False),
)
_GEN_SYSROOT_NUM_OPS_USIZE_SAFE: tuple[tuple[str, bool], ...] = (
    ("unchecked_add", True),
    ("unchecked_mul", True),
    ("wrapping_add", False),
    ("wrapping_sub", False),
    ("wrapping_mul", False),
)


def _pick_sysroot_op_for_kind(
    rng: _SplitMix64, kind: str
) -> tuple[str, bool]:
    if kind == "usize":
        return rng.pick(_GEN_SYSROOT_NUM_OPS_USIZE_SAFE)
    return rng.pick(_GEN_SYSROOT_NUM_OPS)
_GEN_ENUM_CONSTS: dict[tuple[str, str], str] = {
    ("GenSignedTag", "NegFive"): "GEN_SIGNED_NEG_FIVE",
    ("GenSignedTag", "Zero"): "GEN_SIGNED_ZERO",
    ("GenSignedTag", "Four"): "GEN_SIGNED_FOUR",
    ("GenSignedTag", "ThreeHundred"): "GEN_SIGNED_THREE_HUNDRED",
    ("GenUnsignedTag", "Alpha"): "GEN_UNSIGNED_ALPHA",
    ("GenUnsignedTag", "Beta"): "GEN_UNSIGNED_BETA",
    ("GenUnsignedTag", "Gamma"): "GEN_UNSIGNED_GAMMA",
    ("GenSoloRepr", "Only"): "GEN_SOLO_ONLY",
    ("GenZstUnit", "Only"): "GEN_ZST_ONLY",
}


def _to_signed_i128(kind: str, bits: int) -> int:
    w = _INT_KIND_BITS[kind]
    masked = bits & ((1 << w) - 1)
    if kind.startswith("i") and (masked & (1 << (w - 1))):
        return masked - (1 << w)
    return masked


def _format_rust_literal(kind: str, bits: int) -> str:
    w = _INT_KIND_BITS[kind]
    mask = (1 << w) - 1
    if kind.startswith("i"):
        signed = _to_signed_i128(kind, bits)
        if signed == -(1 << (w - 1)):
            return f"{kind}::MIN"
        return f"({signed}{kind})"
    return f"{bits & mask}{kind}"


def _format_rust_int_pattern(kind: str, bits: int) -> str:
    w = _INT_KIND_BITS[kind]
    mask = (1 << w) - 1
    if kind.startswith("i"):
        signed = _to_signed_i128(kind, bits)
        if signed == -(1 << (w - 1)):
            return f"{kind}::MIN"
        return f"{signed}{kind}"
    return f"{bits & mask}{kind}"


def _format_rust_value_expr(v: dict[str, Any]) -> str:
    kind = v["kind"]
    if kind == "int":
        return _format_rust_literal(v["int_kind"], int(v["bits"]))
    if kind == "bool":
        return "true" if v["value"] else "false"
    if kind == "char":
        return f"'\\u{{{int(v['scalar']):x}}}'"
    if kind == "ordering":
        ord_val = v["value"]
        if ord_val == "less":
            return "GEN_ORD_LESS"
        if ord_val == "equal":
            return "GEN_ORD_EQUAL"
        return "GEN_ORD_GREATER"
    if kind == "unit":
        return "GEN_UNIT"
    if kind == "overflow_pair":
        ovf = "true" if v["overflow"] else "false"
        return f"({_format_rust_literal(v['int_kind'], int(v['bits']))}, {ovf})"
    if kind == "enum":
        return _GEN_ENUM_CONSTS.get(
            (v["enum_type"], v["variant"]), f"{v['enum_type']}::{v['variant']}"
        )
    raise ValueError(f"unsupported MirValue kind {kind!r}")


def _gen_type_rust_name(ty: tuple[str, ...]) -> str:
    kind = ty[0]
    if kind == "int":
        return ty[1]
    if kind == "bool":
        return "bool"
    if kind == "char":
        return "char"
    if kind == "ordering":
        return "core::cmp::Ordering"
    if kind == "unit":
        return "()"
    if kind == "enum":
        return ty[1]
    raise ValueError(f"unsupported GenType {ty!r}")


def _gen_expr_uses_unsafe(expr: tuple[Any, ...]) -> bool:
    tag = expr[0]
    if tag in ("lit", "param", "local"):
        return False
    if tag == "sysroot_num":
        _, _method, is_unch, _ty, lhs, rhs, _guarded = expr
        return (
            is_unch
            or _gen_expr_uses_unsafe(lhs)
            or _gen_expr_uses_unsafe(rhs)
        )
    if tag in ("bin_arith", "shift", "cmp", "bool_logic", "three_way_cmp"):
        return _gen_expr_uses_unsafe(expr[-2]) or _gen_expr_uses_unsafe(expr[-1])
    if tag == "unary":
        return _gen_expr_uses_unsafe(expr[3])
    if tag == "cast":
        return _gen_expr_uses_unsafe(expr[1])
    if tag == "match_ordering":
        return (
            _gen_expr_uses_unsafe(expr[1])
            or _gen_expr_uses_unsafe(expr[3])
            or _gen_expr_uses_unsafe(expr[4])
            or _gen_expr_uses_unsafe(expr[5])
        )
    if tag == "match_enum":
        return any(_gen_expr_uses_unsafe(arm) for arm in expr[4])
    if tag == "match_int":
        return (
            _gen_expr_uses_unsafe(expr[1])
            or any(_gen_expr_uses_unsafe(arm) for _, arm in expr[4])
            or _gen_expr_uses_unsafe(expr[5])
        )
    if tag == "match_char":
        return (
            _gen_expr_uses_unsafe(expr[1])
            or any(_gen_expr_uses_unsafe(arm) for _, arm in expr[3])
            or _gen_expr_uses_unsafe(expr[4])
        )
    raise ValueError(f"unknown GenExpr tag {tag!r}")


def _gen_stmt_uses_unsafe(stmt: tuple[Any, ...]) -> bool:
    tag = stmt[0]
    if tag in ("assign", "move_reinit"):
        return _gen_expr_uses_unsafe(stmt[2])
    if tag == "if_else":
        return (
            _gen_expr_uses_unsafe(stmt[1])
            or any(_gen_stmt_uses_unsafe(s) for s in stmt[2])
            or any(_gen_stmt_uses_unsafe(s) for s in stmt[3])
        )
    if tag == "while_loop":
        return (
            any(_gen_stmt_uses_unsafe(s) for s in stmt[2])
            or (stmt[3] is not None and _gen_expr_uses_unsafe(stmt[3]))
            or (stmt[4] is not None and _gen_expr_uses_unsafe(stmt[4]))
        )
    if tag in ("hint_unreachable",):
        return True
    if tag == "abort":
        return False
    raise ValueError(f"unknown GenStmt tag {tag!r}")


def _render_gen_expr(expr: tuple[Any, ...]) -> str:
    tag = expr[0]
    if tag == "lit":
        return _format_rust_value_expr(expr[1])
    if tag == "param":
        return f"p{expr[1]}"
    if tag == "local":
        return f"v{expr[1]}"
    if tag in ("bin_arith", "shift"):
        return f"(({_render_gen_expr(expr[3])}) {expr[1]} ({_render_gen_expr(expr[4])}))"
    if tag == "sysroot_num":
        _, method, is_unch, ty, lhs, rhs, guarded = expr
        if not is_unch:
            return (
                f"{{ let __a: {ty} = {_render_gen_expr(lhs)}; "
                f"let __b: {ty} = {_render_gen_expr(rhs)}; "
                f"__a.{method}(__b) }}"
            )
        if not guarded:
            return (
                f"{{ let __a: {ty} = {_render_gen_expr(lhs)}; "
                f"let __b: {ty} = {_render_gen_expr(rhs)}; "
                f"unsafe {{ __a.{method}(__b) }} }}"
            )
        seven = _format_rust_literal(ty, 7)
        if method == "unchecked_sub" and not ty.startswith("i"):
            return (
                f"{{ let __sa: {ty} = ({_render_gen_expr(lhs)}) & {seven}; "
                f"let __sb: {ty} = ({_render_gen_expr(rhs)}) & {seven}; "
                f"if __sa >= __sb {{ unsafe {{ __sa.unchecked_sub(__sb) }} }} "
                f"else {{ unsafe {{ __sb.unchecked_sub(__sa) }} }} }}"
            )
        return (
            f"{{ let __sa: {ty} = ({_render_gen_expr(lhs)}) & {seven}; "
            f"let __sb: {ty} = ({_render_gen_expr(rhs)}) & {seven}; "
            f"unsafe {{ __sa.{method}(__sb) }} }}"
        )
    if tag == "unary":
        op = expr[1]
        prefix = "!" if op == "not" else "-"
        return f"({prefix}({_render_gen_expr(expr[3])}))"
    if tag in ("cmp", "bool_logic"):
        return f"(({_render_gen_expr(expr[2])}) {expr[1]} ({_render_gen_expr(expr[3])}))"
    if tag == "three_way_cmp":
        return (
            f"{{ let __cmp_l = {_render_gen_expr(expr[1])}; "
            f"let __cmp_r = {_render_gen_expr(expr[2])}; "
            f"if __cmp_l < __cmp_r {{ GEN_ORD_LESS }} "
            f"else if __cmp_l > __cmp_r {{ GEN_ORD_GREATER }} "
            f"else {{ GEN_ORD_EQUAL }} }}"
        )
    if tag == "cast":
        return f"(({_render_gen_expr(expr[1])}) as {_gen_type_rust_name(expr[3])})"
    if tag == "match_ordering":
        _, scrut, _, less, eq, gt = expr
        return (
            f"match {_render_gen_expr(scrut)} {{ "
            f"core::cmp::Ordering::Less => {_render_gen_expr(less)}, "
            f"core::cmp::Ordering::Equal => {_render_gen_expr(eq)}, "
            f"core::cmp::Ordering::Greater => {_render_gen_expr(gt)} }}"
        )
    if tag == "match_enum":
        _, pidx, ekind, _, arms = expr
        parts = [f"match p{pidx} {{ "]
        for variant, arm in zip(_GEN_ENUM_VARIANTS[ekind], arms):
            parts.append(f"{ekind}::{variant} => {_render_gen_expr(arm)}, ")
        parts.append("}")
        return "".join(parts)
    if tag == "match_int":
        _, scrut, sty, _, arms, otherwise = expr
        parts = [f"match {_render_gen_expr(scrut)} {{ "]
        for bits, arm in arms:
            parts.append(f"{_format_rust_int_pattern(sty, bits)} => {_render_gen_expr(arm)}, ")
        parts.append(f"_ => {_render_gen_expr(otherwise)} }}")
        return "".join(parts)
    if tag == "match_char":
        _, scrut, _, arms, otherwise = expr
        parts = [f"match {_render_gen_expr(scrut)} {{ "]
        for scalar, arm in arms:
            parts.append(f"'\\u{{{scalar:x}}}' => {_render_gen_expr(arm)}, ")
        parts.append(f"_ => {_render_gen_expr(otherwise)} }}")
        return "".join(parts)
    raise ValueError(f"unknown GenExpr tag {tag!r}")


def _render_gen_stmt_into(
    stmt: tuple[Any, ...], out: list[str], indent: int, loop_counter: list[int]
) -> None:
    pad = " " * indent
    tag = stmt[0]
    if tag == "assign":
        out.append(f"{pad}v{stmt[1]} = {_render_gen_expr(stmt[2])};\n")
        return
    if tag == "move_reinit":
        out.append(f"{pad}{{\n")
        out.append(f"{pad}    let __moved = v{stmt[1]};\n")
        out.append(f"{pad}    let _ = __moved as isize;\n")
        out.append(f"{pad}    v{stmt[1]} = {_render_gen_expr(stmt[2])};\n")
        out.append(f"{pad}}}\n")
        return
    if tag == "if_else":
        _, cond, then_body, else_body = stmt
        out.append(f"{pad}if {_render_gen_expr(cond)} {{\n")
        for s in then_body:
            _render_gen_stmt_into(s, out, indent + 4, loop_counter)
        if not else_body:
            out.append(f"{pad}}}\n")
        else:
            out.append(f"{pad}}} else {{\n")
            for s in else_body:
                _render_gen_stmt_into(s, out, indent + 4, loop_counter)
            out.append(f"{pad}}}\n")
        return
    if tag == "while_loop":
        _, bound, body, break_cond, continue_cond = stmt
        lid = loop_counter[0]
        loop_counter[0] += 1
        out.append(f"{pad}let mut __loop_i_{lid}: u32 = 0u32;\n")
        out.append(f"{pad}while __loop_i_{lid} < {bound}u32 {{\n")
        out.append(f"{pad}    __loop_i_{lid} = __loop_i_{lid} + 1u32;\n")
        if continue_cond is not None:
            out.append(f"{pad}    if {_render_gen_expr(continue_cond)} {{ continue; }}\n")
        for s in body:
            _render_gen_stmt_into(s, out, indent + 4, loop_counter)
        if break_cond is not None:
            out.append(f"{pad}    if {_render_gen_expr(break_cond)} {{ break; }}\n")
        out.append(f"{pad}}}\n")
        return
    if tag == "abort":
        out.append(f"{pad}std::process::abort();\n")
        return
    if tag == "hint_unreachable":
        out.append(f"{pad}unsafe {{ core::hint::unreachable_unchecked() }};\n")
        return
    raise ValueError(f"unknown GenStmt tag {tag!r}")


def _render_gen_program_standalone(
    *,
    fn_name: str,
    is_unsafe: bool,
    params: list[tuple[tuple[str, ...], dict[str, Any]]],
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    body: list[tuple[Any, ...]],
    ret_ty: tuple[str, ...],
    ret_expr: tuple[Any, ...],
) -> str:
    needs_unsafe = (
        is_unsafe
        or any(_gen_expr_uses_unsafe(init) for _, init in locals_list)
        or any(_gen_stmt_uses_unsafe(s) for s in body)
        or _gen_expr_uses_unsafe(ret_expr)
    )
    unsafe_kw = "unsafe " if needs_unsafe else ""
    params_rendered = ", ".join(
        f"p{idx}: {_gen_type_rust_name(pty)}" for idx, (pty, _) in enumerate(params)
    )
    out = [
        _GEN_CRATE_HEADER,
        "\n",
        _GEN_ENUM_PREAMBLE,
        "\n",
        f"pub {unsafe_kw}fn {fn_name}({params_rendered}) -> {_gen_type_rust_name(ret_ty)} {{\n",
    ]
    for idx, (lty, init) in enumerate(locals_list):
        out.append(f"    let mut v{idx}: {_gen_type_rust_name(lty)} = {_render_gen_expr(init)};\n")
    loop_counter = [0]
    for stmt in body:
        _render_gen_stmt_into(stmt, out, 4, loop_counter)
    out.append(f"    {_render_gen_expr(ret_expr)}\n")
    out.append("}\n")
    return "".join(out)


def _gen_atom_of_type(
    rng: _SplitMix64,
    ty: tuple[str, ...],
    params: list[tuple[tuple[str, ...], dict[str, Any]]],
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    boundary_bias: bool,
) -> tuple[Any, ...]:
    if ty[0] == "enum":
        return ("lit", _gen_value_for_type(rng, ty, boundary_bias))
    candidates: list[tuple[Any, ...]] = []
    for idx, (pty, _) in enumerate(params):
        if pty == ty:
            candidates.append(("param", idx))
    for idx, (lty, _) in enumerate(locals_list):
        if lty == ty:
            candidates.append(("local", idx))
    if candidates and rng.coin(3, 4):
        return rng.pick(candidates)
    return ("lit", _gen_value_for_type(rng, ty, boundary_bias))


def _gen_expr_of_type(
    rng: _SplitMix64,
    ty: tuple[str, ...],
    params: list[tuple[tuple[str, ...], dict[str, Any]]],
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    boundary_bias: bool,
    depth: int,
) -> tuple[Any, ...]:
    if depth == 0:
        return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)
    kind = ty[0]
    if kind == "int":
        ik = ty[1]
        roll = rng.gen_range(11)
        if roll == 0:
            return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)
        if 1 <= roll <= 3:
            _, op_sym = rng.pick(_GEN_ARITH_OPS)
            lhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            rhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("bin_arith", op_sym, ik, lhs, rhs)
        if roll == 4:
            op_sym = "<<" if rng.coin(1, 2) else ">>"
            rhs_ty = rng.pick(_ALL_INT_KINDS)
            lhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            rhs = _gen_expr_of_type(
                rng, ("int", rhs_ty), params, locals_list, boundary_bias, depth - 1
            )
            return ("shift", op_sym, ik, lhs, rhs)
        if roll == 5:
            method, is_unch = _pick_sysroot_op_for_kind(rng, ik)
            lhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            rhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("sysroot_num", method, is_unch, ik, lhs, rhs, is_unch)
        if roll == 6:
            op_name = "neg" if (ik.startswith("i") and rng.coin(1, 2)) else "not"
            operand = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("unary", op_name, ty, operand)
        if roll == 7:
            c_roll = rng.gen_range(4)
            if c_roll == 0:
                src_ty: tuple[str, ...] = ("bool",)
            elif c_roll == 1:
                src_ty = ("char",)
            else:
                src_ty = ("int", rng.pick(_ALL_INT_KINDS))
            inner = _gen_expr_of_type(rng, src_ty, params, locals_list, boundary_bias, depth - 1)
            return ("cast", inner, src_ty, ty)
        if roll == 8:
            enum_param = next(
                ((i, pty[1]) for i, (pty, _) in enumerate(params) if pty[0] == "enum"),
                None,
            )
            if enum_param is not None:
                pidx, ekind = enum_param
                arms = [
                    _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
                    for _ in range(len(_GEN_ENUM_VARIANTS[ekind]))
                ]
                return ("match_enum", pidx, ekind, ty, arms)
            scrut = _gen_expr_of_type(
                rng, ("ordering",), params, locals_list, boundary_bias, depth - 1
            )
            less = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            eq = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            gt = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("match_ordering", scrut, ty, less, eq, gt)
        if roll == 9:
            scrut = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            pool = _gen_boundary_bits_for_int(ik)
            seen_pats: set[int] = set()
            arms_int: list[tuple[int, tuple[Any, ...]]] = []
            for _ in range(2):
                pat = rng.pick(pool)
                if pat not in seen_pats:
                    seen_pats.add(pat)
                    arms_int.append(
                        (pat, _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1))
                    )
            otherwise = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("match_int", scrut, ik, ty, arms_int, otherwise)
        return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)

    if kind == "bool":
        roll = rng.gen_range(5)
        if roll == 0:
            return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)
        if roll == 1:
            operand = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("unary", "not", ty, operand)
        if roll == 2:
            _, op_sym = rng.pick(_GEN_BOOL_BIN_OPS)
            lhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            rhs = _gen_expr_of_type(rng, ty, params, locals_list, boundary_bias, depth - 1)
            return ("bool_logic", op_sym, lhs, rhs)
        c_roll = rng.gen_range(4)
        if c_roll == 0:
            cmp_ty: tuple[str, ...] = ("bool",)
        elif c_roll == 1:
            cmp_ty = ("char",)
        else:
            first_int = (
                locals_list[0][0][1]
                if locals_list and locals_list[0][0][0] == "int"
                else "u32"
            )
            cmp_ty = ("int", first_int)
        _, op_sym = rng.pick(_GEN_CMP_OPS)
        lhs = _gen_expr_of_type(rng, cmp_ty, params, locals_list, boundary_bias, depth - 1)
        rhs = _gen_expr_of_type(rng, cmp_ty, params, locals_list, boundary_bias, depth - 1)
        return ("cmp", op_sym, lhs, rhs)

    if kind == "char":
        roll = rng.gen_range(3)
        if roll == 1:
            byte = _gen_expr_of_type(
                rng, ("int", "u8"), params, locals_list, boundary_bias, depth - 1
            )
            return ("cast", byte, ("int", "u8"), ("char",))
        return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)

    if kind == "ordering":
        if rng.coin(1, 2):
            cmp_ty = ("char",) if rng.coin(1, 4) else ("int", rng.pick(_ALL_INT_KINDS))
            lhs = _gen_expr_of_type(rng, cmp_ty, params, locals_list, boundary_bias, depth - 1)
            rhs = _gen_expr_of_type(rng, cmp_ty, params, locals_list, boundary_bias, depth - 1)
            return ("three_way_cmp", lhs, rhs)
        return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)

    if kind == "unit":
        return ("lit", {"kind": "unit"})
    if kind == "enum":
        return _gen_atom_of_type(rng, ty, params, locals_list, boundary_bias)
    raise ValueError(f"unsupported GenType {ty!r}")


def _gen_safe_stmt(
    rng: _SplitMix64,
    params: list[tuple[tuple[str, ...], dict[str, Any]]],
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    boundary_bias: bool,
    depth: int,
    rem: list[int],
) -> tuple[Any, ...]:
    can_move_reinit = rem[0] >= 3
    can_branch = depth > 0 and rem[0] >= 2
    can_loop = depth > 0 and rem[0] >= 4
    choices = [0]
    if can_move_reinit:
        choices.append(1)
    if can_branch:
        choices.append(2)
    if can_loop:
        choices.append(3)
    if len(choices) > 1:
        choices.append(4)
    roll = choices[rng.gen_range(len(choices))]
    if roll == 1:
        rem[0] -= 3
        local_idx = next((i for i, (lty, _) in enumerate(locals_list) if lty[0] == "enum"), 0)
        expr = _gen_expr_of_type(
            rng, locals_list[local_idx][0], params, locals_list, boundary_bias, 1
        )
        return ("move_reinit", local_idx, expr)
    if roll == 2:
        rem[0] -= 1
        cond = _gen_expr_of_type(rng, ("bool",), params, locals_list, boundary_bias, 2)
        then_len = 1 + rng.gen_range(min(rem[0], 2))
        then_body = []
        for _ in range(then_len):
            if rem[0] == 0:
                break
            then_body.append(
                _gen_safe_stmt(rng, params, locals_list, boundary_bias, depth - 1, rem)
            )
        else_len = rng.gen_range(min(rem[0], 1) + 1) if rem[0] > 0 else 0
        else_body = []
        for _ in range(else_len):
            if rem[0] == 0:
                break
            else_body.append(
                _gen_safe_stmt(rng, params, locals_list, boundary_bias, depth - 1, rem)
            )
        return ("if_else", cond, then_body, else_body)
    if roll == 3:
        rem[0] -= 3
        bound = (rng.gen_range(2) + 1) if depth < 2 else (rng.gen_range(6) + 1)
        body_len = 1 + rng.gen_range(min(rem[0], 2))
        loop_body = []
        for _ in range(body_len):
            if rem[0] == 0:
                break
            loop_body.append(
                _gen_safe_stmt(rng, params, locals_list, boundary_bias, depth - 1, rem)
            )
        if rem[0] >= 2 and rng.coin(1, 3):
            rem[0] -= 2
            break_cond: tuple[Any, ...] | None = _gen_expr_of_type(
                rng, ("bool",), params, locals_list, boundary_bias, 1
            )
        else:
            break_cond = None
        if rem[0] >= 2 and rng.coin(1, 4):
            rem[0] -= 2
            continue_cond: tuple[Any, ...] | None = _gen_expr_of_type(
                rng, ("bool",), params, locals_list, boundary_bias, 1
            )
        else:
            continue_cond = None
        return ("while_loop", bound, loop_body, break_cond, continue_cond)
    rem[0] -= 1
    copy_indices = [i for i, (lty, _) in enumerate(locals_list) if lty[0] != "enum"]
    local_idx = rng.pick(copy_indices) if copy_indices else 0
    expr = _gen_expr_of_type(
        rng, locals_list[local_idx][0], params, locals_list, boundary_bias, 2
    )
    return ("assign", local_idx, expr)


def _materialize_u128_mix_expr(
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    body: list[tuple[Any, ...]],
    emit_mixer_stmt: bool,
) -> tuple[Any, ...]:
    u128_ty: tuple[str, ...] = ("int", "u128")
    acc: tuple[Any, ...] | None = None
    for idx, (lty, _) in enumerate(locals_list):
        term: tuple[Any, ...] = (
            ("local", idx) if lty == u128_ty else ("cast", ("local", idx), lty, u128_ty)
        )
        if acc is None:
            acc = term
        else:
            op_sym = "+" if idx % 2 == 0 else "^"
            acc = ("bin_arith", op_sym, "u128", acc, term)
    initial_fold = acc if acc is not None else ("lit", {"kind": "int", "int_kind": "u128", "bits": "0"})
    if not emit_mixer_stmt:
        return initial_fold
    mix_idx = len(locals_list)
    locals_list.append((u128_ty, ("lit", {"kind": "int", "int_kind": "u128", "bits": "0"})))
    body.append(("assign", mix_idx, initial_fold))
    fold: tuple[Any, ...] = ("local", mix_idx)
    for shift_amt in (64, 32, 16, 8, 24, 40, 48, 56, 72, 80, 88, 96, 104, 112, 120):
        shifted = (
            "shift",
            ">>",
            "u128",
            ("local", mix_idx),
            ("lit", {"kind": "int", "int_kind": "u32", "bits": str(shift_amt)}),
        )
        fold = ("bin_arith", "^", "u128", fold, shifted)
    return fold


def _project_expr_to_int(expr: tuple[Any, ...], dst: str) -> tuple[Any, ...]:
    if dst == "u128":
        return expr
    return ("cast", expr, ("int", "u128"), ("int", dst))


def _gen_safe_return(
    rng: _SplitMix64,
    params: list[tuple[tuple[str, ...], dict[str, Any]]],
    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]],
    body: list[tuple[Any, ...]],
    primary_int: str,
    boundary_bias: bool,
    emit_mixer_stmt: bool,
) -> tuple[tuple[str, ...], tuple[Any, ...]]:
    if boundary_bias and rng.gen_range(32) == 0:
        return (("unit",), ("lit", {"kind": "unit"}))
    roll = rng.gen_range(10)
    if 0 <= roll <= 5:
        ret_ty: tuple[str, ...] = ("int", primary_int)
        expr = _gen_expr_of_type(rng, ret_ty, params, locals_list, boundary_bias, 2)
        mix_expr = _materialize_u128_mix_expr(locals_list, body, emit_mixer_stmt)
        live_mix = _project_expr_to_int(mix_expr, primary_int)
        return (ret_ty, ("bin_arith", "^", primary_int, expr, live_mix))
    if roll == 6:
        ret_ty = ("bool",)
        expr = _gen_expr_of_type(rng, ret_ty, params, locals_list, boundary_bias, 2)
        mix_expr = _materialize_u128_mix_expr(locals_list, body, emit_mixer_stmt)
        if emit_mixer_stmt:
            parity = _project_expr_to_int(mix_expr, "u8")
            for s in (4, 2, 1):
                sh = (
                    "shift",
                    ">>",
                    "u8",
                    parity,
                    ("lit", {"kind": "int", "int_kind": "u32", "bits": str(s)}),
                )
                parity = ("bin_arith", "^", "u8", parity, sh)
            low_bit = (
                "bin_arith",
                "&",
                "u8",
                parity,
                ("lit", {"kind": "int", "int_kind": "u8", "bits": "1"}),
            )
            mix_bool: tuple[Any, ...] = (
                "cmp",
                "!=",
                low_bit,
                ("lit", {"kind": "int", "int_kind": "u8", "bits": "0"}),
            )
        else:
            mix_bool = (
                "cmp",
                "!=",
                mix_expr,
                ("lit", {"kind": "int", "int_kind": "u128", "bits": "0"}),
            )
        return (ret_ty, ("bool_logic", "^", expr, mix_bool))
    if roll == 7:
        ret_ty = ("int", primary_int)
        method, is_unch = _pick_sysroot_op_for_kind(rng, primary_int)
        rhs = _gen_expr_of_type(
            rng, ("int", primary_int), params, locals_list, boundary_bias, 1
        )
        mix_expr = _materialize_u128_mix_expr(locals_list, body, emit_mixer_stmt)
        live_mix = _project_expr_to_int(mix_expr, primary_int)
        return (ret_ty, ("sysroot_num", method, is_unch, primary_int, live_mix, rhs, is_unch))
    if roll == 8:
        ret_ty = ("ordering",)
        rhs = _gen_expr_of_type(
            rng, ("int", "u128"), params, locals_list, boundary_bias, 1
        )
        mix_expr = _materialize_u128_mix_expr(locals_list, body, emit_mixer_stmt)
        return (ret_ty, ("three_way_cmp", mix_expr, rhs))
    ret_ty = ("char",)
    base = _gen_expr_of_type(rng, ret_ty, params, locals_list, boundary_bias, 1)
    mix_expr = _materialize_u128_mix_expr(locals_list, body, emit_mixer_stmt)
    base_u8 = ("cast", base, ("char",), ("int", "u8"))
    mixed_u8 = ("bin_arith", "^", "u8", base_u8, _project_expr_to_int(mix_expr, "u8"))
    return (ret_ty, ("cast", mixed_u8, ("int", "u8"), ("char",)))


def _gen_safe_program(
    rng: _SplitMix64, fn_name: str, max_stmts: int, boundary_bias: bool
) -> tuple[list[dict[str, Any]], str, list[tuple[str, ...]], tuple[str, ...]]:
    primary_int = rng.pick(_ALL_INT_KINDS)
    secondary_int = rng.pick(_ALL_INT_KINDS)
    params: list[tuple[tuple[str, ...], dict[str, Any]]] = [
        (("int", primary_int), _gen_value_for_type(rng, ("int", primary_int), boundary_bias)),
        (("int", primary_int), _gen_value_for_type(rng, ("int", primary_int), boundary_bias)),
    ]
    extra_count = 1 + rng.gen_range(3)
    for _ in range(extra_count):
        choice = rng.gen_range(6)
        if choice == 0:
            extra_ty: tuple[str, ...] = ("int", secondary_int)
        elif choice == 1:
            extra_ty = ("bool",)
        elif choice == 2:
            extra_ty = ("char",)
        elif choice == 3:
            extra_ty = ("ordering",)
        elif choice == 4:
            extra_ty = ("enum", rng.pick(_GEN_ENUM_KINDS))
        else:
            extra_ty = ("int", rng.pick(_ALL_INT_KINDS))
        params.append((extra_ty, _gen_value_for_type(rng, extra_ty, boundary_bias)))

    locals_list: list[tuple[tuple[str, ...], tuple[Any, ...]]] = [
        (("int", primary_int), ("param", 0)),
        (("int", primary_int), ("param", 1)),
        (("bool",), ("lit", _gen_value_for_type(rng, ("bool",), boundary_bias))),
    ]
    sec_idx = next((i for i, (pty, _) in enumerate(params) if pty == ("int", secondary_int)), None)
    if sec_idx is not None:
        locals_list.append((("int", secondary_int), ("param", sec_idx)))
    else:
        locals_list.append(
            (("int", secondary_int), ("lit", _gen_value_for_type(rng, ("int", secondary_int), boundary_bias)))
        )
    move_enum = rng.pick(("GenSignedTag", "GenUnsignedTag"))
    locals_list.append(
        (("enum", move_enum), ("lit", _gen_value_for_type(rng, ("enum", move_enum), boundary_bias)))
    )

    reserve_mixer_stmt = 1 if max_stmts >= 2 else 0
    body_budget = max_stmts - reserve_mixer_stmt
    target_body_stmts = 1 + rng.gen_range(body_budget)
    rem = [target_body_stmts]
    body: list[tuple[Any, ...]] = []
    while rem[0] > 0:
        body.append(_gen_safe_stmt(rng, params, locals_list, boundary_bias, 2, rem))
    ret_ty, ret_expr = _gen_safe_return(
        rng, params, locals_list, body, primary_int, boundary_bias, reserve_mixer_stmt > 0
    )
    src = _render_gen_program_standalone(
        fn_name=fn_name,
        is_unsafe=False,
        params=params,
        locals_list=locals_list,
        body=body,
        ret_ty=ret_ty,
        ret_expr=ret_expr,
    )
    return (
        [val for _, val in params],
        hashlib.sha256(src.encode("utf-8")).hexdigest(),
        [pty for pty, _ in params],
        ret_ty,
    )


def _gen_enum_mir_value(ekind: str, vidx: int) -> dict[str, Any]:
    variants = _GEN_ENUM_VARIANTS[ekind]
    idx = vidx % len(variants)
    return {
        "kind": "enum",
        "enum_type": ekind,
        "variant": variants[idx],
        "variant_index": idx,
    }


def _gen_boundary_program(
    rng: _SplitMix64, fn_name: str, case_index: int, max_stmts: int
) -> tuple[list[dict[str, Any]], str, list[tuple[str, ...]], tuple[str, ...]]:
    if max_stmts == 1:
        candidates = (3, 4, 6)
    elif max_stmts == 2:
        candidates = (0, 3, 4, 6)
    elif max_stmts == 3:
        candidates = (0, 2, 3, 4, 6)
    elif max_stmts in (4, 5):
        candidates = (0, 1, 2, 3, 4, 6)
    else:
        candidates = (0, 1, 2, 3, 4, 5, 6)
    arm = candidates[case_index % len(candidates)]
    if arm == 0:
        lhs_ty = rng.pick(_ALL_INT_KINDS)
        rhs_ty = rng.pick(_ALL_INT_KINDS)
        lhs_val = _gen_int_value(rng, lhs_ty, True)
        w = _INT_KIND_BITS[lhs_ty]
        rw = _INT_KIND_BITS[rhs_ty]
        rmask = (1 << rw) - 1
        rhs_cands = [0, 1, w - 1, w, w + 5]
        if rhs_ty.startswith("i"):
            rhs_cands.extend([(-1) & rmask, (-w) & rmask, 1 << (rw - 1)])
        else:
            rhs_cands.append(rmask)
        rhs_bits = rng.pick(rhs_cands) & rmask
        rhs_val = {"kind": "int", "int_kind": rhs_ty, "bits": str(rhs_bits)}
        params = [(("int", lhs_ty), lhs_val), (("int", rhs_ty), rhs_val)]
        locals_list = [
            (("int", lhs_ty), ("param", 0)),
            (("int", lhs_ty), ("lit", {"kind": "int", "int_kind": lhs_ty, "bits": "0"})),
        ]
        body = [
            ("assign", 1, ("shift", "<<", lhs_ty, ("local", 0), ("param", 1))),
            ("assign", 0, ("shift", ">>", lhs_ty, ("local", 0), ("param", 1))),
        ]
        ret_expr = ("bin_arith", "^", lhs_ty, ("local", 0), ("local", 1))
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=False,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", lhs_ty),
            ret_expr=ret_expr,
        )
        return (
            [lhs_val, rhs_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", lhs_ty),
        )
    if arm == 1:
        kind = rng.pick(_ALL_INT_KINDS)
        method, is_unch = _pick_sysroot_op_for_kind(rng, kind)
        a = _gen_int_value(rng, kind, True)
        b = _gen_int_value(rng, kind, True)
        params = [(("int", kind), a), (("int", kind), b)]
        locals_list = [
            (("int", kind), ("param", 0)),
            (("enum", "GenSignedTag"), ("lit", _gen_enum_mir_value("GenSignedTag", 0))),
        ]
        body = [
            ("move_reinit", 1, ("lit", _gen_enum_mir_value("GenSignedTag", 2))),
            (
                "assign",
                0,
                (
                    "bin_arith",
                    "^",
                    kind,
                    ("local", 0),
                    ("cast", ("local", 1), ("enum", "GenSignedTag"), ("int", kind)),
                ),
            ),
        ]
        ret_expr = ("sysroot_num", method, is_unch, kind, ("local", 0), ("param", 1), is_unch)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=is_unch,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [a, b],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    if arm == 2:
        src_int = rng.pick(_ALL_INT_KINDS)
        mid_int = rng.pick(_ALL_INT_KINDS)
        dst_int = rng.pick(_ALL_INT_KINDS)
        params = [
            (("int", src_int), _gen_int_value(rng, src_int, True)),
            (("bool",), _gen_value_for_type(rng, ("bool",), True)),
            (("char",), _gen_value_for_type(rng, ("char",), True)),
            (("int", "u8"), _gen_int_value(rng, "u8", True)),
        ]
        locals_list = [
            (("int", mid_int), ("cast", ("param", 0), ("int", src_int), ("int", mid_int))),
            (("char",), ("cast", ("param", 3), ("int", "u8"), ("char",))),
            (("int", dst_int), ("cast", ("param", 1), ("bool",), ("int", dst_int))),
        ]
        body = [
            (
                "if_else",
                ("cmp", "<", ("param", 2), ("local", 1)),
                [
                    (
                        "assign",
                        2,
                        (
                            "bin_arith",
                            "^",
                            dst_int,
                            ("local", 2),
                            ("cast", ("local", 0), ("int", mid_int), ("int", dst_int)),
                        ),
                    )
                ],
                [
                    (
                        "assign",
                        2,
                        (
                            "bin_arith",
                            "+",
                            dst_int,
                            ("cast", ("param", 2), ("char",), ("int", dst_int)),
                            ("cast", ("local", 0), ("int", mid_int), ("int", dst_int)),
                        ),
                    )
                ],
            )
        ]
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=False,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", dst_int),
            ret_expr=("local", 2),
        )
        return (
            [v for _, v in params],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", dst_int),
        )
    if arm == 3:
        params = [
            (("char",), _gen_value_for_type(rng, ("char",), True)),
            (("char",), _gen_value_for_type(rng, ("char",), True)),
        ]
        locals_list = [(("ordering",), ("three_way_cmp", ("param", 0), ("param", 1)))]
        if rng.coin(1, 3):
            src = _render_gen_program_standalone(
                fn_name=fn_name,
                is_unsafe=False,
                params=params,
                locals_list=locals_list,
                body=[],
                ret_ty=("ordering",),
                ret_expr=("local", 0),
            )
            return (
                [v for _, v in params],
                hashlib.sha256(src.encode("utf-8")).hexdigest(),
                [pty for pty, _ in params],
                ("ordering",),
            )
        ret_expr = (
            "match_ordering",
            ("local", 0),
            ("int", "i32"),
            (
                "match_char",
                ("param", 0),
                ("int", "i32"),
                [
                    (0x0000, ("lit", {"kind": "int", "int_kind": "i32", "bits": str((-10) & 0xFFFF_FFFF)})),
                    (0xD7FF, ("lit", {"kind": "int", "int_kind": "i32", "bits": "77"})),
                ],
                ("cast", ("param", 0), ("char",), ("int", "i32")),
            ),
            ("lit", {"kind": "int", "int_kind": "i32", "bits": "0"}),
            ("cast", ("param", 1), ("char",), ("int", "i32")),
        )
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=False,
            params=params,
            locals_list=locals_list,
            body=[],
            ret_ty=("int", "i32"),
            ret_expr=ret_expr,
        )
        return (
            [v for _, v in params],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", "i32"),
        )
    if arm == 4:
        ekind = rng.pick(_GEN_ENUM_KINDS)
        ikind = rng.pick(_SIGNED_INT_KINDS)
        params = [
            (("enum", ekind), _gen_value_for_type(rng, ("enum", ekind), True)),
            (("int", ikind), _gen_int_value(rng, ikind, True)),
        ]
        locals_list = [(("int", ikind), ("param", 1))]
        mask = (1 << _INT_KIND_BITS[ikind]) - 1
        arms = [
            (
                "bin_arith",
                "+" if i % 2 == 0 else "^",
                ikind,
                ("local", 0),
                ("lit", {"kind": "int", "int_kind": ikind, "bits": str((i - 2) & mask)}),
            )
            for i in range(len(_GEN_ENUM_VARIANTS[ekind]))
        ]
        body = [("assign", 0, ("match_enum", 0, ekind, ("int", ikind), arms))]
        ret_expr = ("unary", "neg", ("int", ikind), ("local", 0))
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=False,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", ikind),
            ret_expr=ret_expr,
        )
        return (
            [v for _, v in params],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", ikind),
        )
    if arm == 5:
        kind = rng.pick(_SIGNED_INT_KINDS)
        bound = rng.pick((0, 1, 2, 4, 7))
        params = [
            (("int", kind), _gen_int_value(rng, kind, True)),
            (("int", kind), _gen_int_value(rng, kind, True)),
        ]
        locals_list = [(("int", kind), ("param", 0))]
        loop_op = rng.pick(("+", "-", "*"))
        body = [
            (
                "while_loop",
                bound,
                [("assign", 0, ("bin_arith", loop_op, kind, ("local", 0), ("param", 1)))],
                (
                    "cmp",
                    "==",
                    ("local", 0),
                    ("lit", {"kind": "int", "int_kind": kind, "bits": "0"}),
                ),
                None,
            )
        ]
        method, is_unch = rng.pick(_GEN_SYSROOT_NUM_OPS)
        ret_expr = ("sysroot_num", method, is_unch, kind, ("local", 0), ("param", 1), is_unch)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=is_unch,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [v for _, v in params],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    return _gen_safe_program(rng, fn_name, max_stmts, True)


def _gen_ub_probe_program(
    rng: _SplitMix64, fn_name: str, case_index: int, max_stmts: int
) -> tuple[list[dict[str, Any]], str, list[tuple[str, ...]], tuple[str, ...]]:
    variant = (case_index + rng.gen_range(5)) % 5
    if variant == 0:
        kind = rng.pick(_ALL_INT_KINDS)
        w = _INT_KIND_BITS[kind]
        mask = (1 << w) - 1
        max_bits = (mask >> 1) if kind.startswith("i") else mask
        a_val = {"kind": "int", "int_kind": kind, "bits": str(max_bits)}
        b_val = {"kind": "int", "int_kind": kind, "bits": "1"}
        params = [(("int", kind), a_val), (("int", kind), b_val)]
        locals_list = [(("int", kind), ("param", 0)), (("int", kind), ("param", 1))]
        want_loop = max_stmts >= 4 and rng.coin(1, 2)
        loop_cost = 4 if want_loop else 0
        decoy_stmts = rng.gen_range(min(max_stmts - loop_cost, 2) + 1)
        body: list[tuple[Any, ...]] = [
            (
                "assign",
                1,
                (
                    "bin_arith",
                    "+",
                    kind,
                    ("local", 1),
                    ("lit", {"kind": "int", "int_kind": kind, "bits": "2"}),
                ),
            )
            for _ in range(decoy_stmts)
        ]
        if want_loop:
            body.append(
                (
                    "while_loop",
                    2,
                    [
                        (
                            "assign",
                            1,
                            (
                                "bin_arith",
                                "+",
                                kind,
                                ("local", 1),
                                ("lit", {"kind": "int", "int_kind": kind, "bits": "2"}),
                            ),
                        )
                    ],
                    None,
                    None,
                )
            )
        ret_expr = ("sysroot_num", "unchecked_add", True, kind, ("local", 0), ("local", 1), False)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=True,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [a_val, b_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    if variant == 1:
        kind = rng.pick(_SIGNED_INT_KINDS)
        w = _INT_KIND_BITS[kind]
        a_val = {"kind": "int", "int_kind": kind, "bits": str(1 << (w - 1))}
        b_val = {"kind": "int", "int_kind": kind, "bits": "1"}
        params = [(("int", kind), a_val), (("int", kind), b_val)]
        locals_list = [
            (("int", kind), ("param", 0)),
            (("int", kind), ("param", 1)),
            (("enum", "GenSignedTag"), ("lit", _gen_enum_mir_value("GenSignedTag", 0))),
        ]
        decoy_stmts = rng.gen_range(min(max_stmts // 3, 2) + 1)
        body = [
            ("move_reinit", 2, ("lit", _gen_enum_mir_value("GenSignedTag", 1)))
            for _ in range(decoy_stmts)
        ]
        ret_expr = ("sysroot_num", "unchecked_sub", True, kind, ("local", 0), ("local", 1), False)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=True,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [a_val, b_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    if variant == 2:
        kind = rng.pick(_UNSIGNED_NON_USIZE_INT_KINDS)
        a_val = {"kind": "int", "int_kind": kind, "bits": "0"}
        b_val = {"kind": "int", "int_kind": kind, "bits": "1"}
        params = [(("int", kind), a_val), (("int", kind), b_val)]
        locals_list = [(("int", kind), ("param", 0))]
        ret_expr = ("sysroot_num", "unchecked_sub", True, kind, ("local", 0), ("param", 1), False)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=True,
            params=params,
            locals_list=locals_list,
            body=[],
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [a_val, b_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    if variant == 3:
        kind = rng.pick(_ALL_INT_KINDS)
        w = _INT_KIND_BITS[kind]
        a_val = {"kind": "int", "int_kind": kind, "bits": str(1 << (w - 2))}
        b_val = {"kind": "int", "int_kind": kind, "bits": "4"}
        params = [(("int", kind), a_val), (("int", kind), b_val)]
        locals_list = [(("int", kind), ("param", 0))]
        ret_expr = ("sysroot_num", "unchecked_mul", True, kind, ("local", 0), ("param", 1), False)
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=True,
            params=params,
            locals_list=locals_list,
            body=[],
            ret_ty=("int", kind),
            ret_expr=ret_expr,
        )
        return (
            [a_val, b_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", kind),
        )
    kind = rng.pick(_ALL_INT_KINDS)
    w = _INT_KIND_BITS[kind]
    mask = (1 << w) - 1
    max_bits = (mask >> 1) if kind.startswith("i") else mask
    trigger_val = {"kind": "int", "int_kind": kind, "bits": str(max_bits)}
    bool_val = {"kind": "bool", "value": True}
    params = [(("int", kind), trigger_val), (("bool",), bool_val)]
    locals_list = [
        (("int", kind), ("param", 0)),
        (("int", kind), ("lit", {"kind": "int", "int_kind": kind, "bits": "1"})),
    ]
    ovf_stmt = (
        "assign",
        0,
        (
            "sysroot_num",
            "unchecked_add",
            True,
            kind,
            ("local", 0),
            ("lit", {"kind": "int", "int_kind": kind, "bits": "1"}),
            False,
        ),
    )
    if max_stmts < 2:
        body = [ovf_stmt]
    else:
        decoy_stmts = rng.gen_range(min(max_stmts - 2, 2) + 1)
        body = [
            (
                "assign",
                1,
                (
                    "bin_arith",
                    "^",
                    kind,
                    ("local", 1),
                    ("lit", {"kind": "int", "int_kind": kind, "bits": "1"}),
                ),
            )
            for _ in range(decoy_stmts)
        ]
        body.append(("if_else", ("param", 1), [ovf_stmt], []))
    src = _render_gen_program_standalone(
        fn_name=fn_name,
        is_unsafe=True,
        params=params,
        locals_list=locals_list,
        body=body,
        ret_ty=("int", kind),
        ret_expr=("local", 0),
    )
    return (
        [trigger_val, bool_val],
        hashlib.sha256(src.encode("utf-8")).hexdigest(),
        [pty for pty, _ in params],
        ("int", kind),
    )


def _gen_scope_control_program(
    rng: _SplitMix64,
    fn_name: str,
    case_index: int,
    max_stmts: int,
    default_fuel: int = 1500,
) -> tuple[list[dict[str, Any]], str, list[tuple[str, ...]], tuple[str, ...], int]:
    n_vars = 2 if max_stmts < 4 else 3
    variant = (case_index + rng.gen_range(n_vars)) % n_vars
    if variant == 0:
        arg_val = {"kind": "int", "int_kind": "u32", "bits": "0"}
        params = [(("int", "u32"), arg_val)]
        locals_list = [(("int", "u32"), ("param", 0))]
        body = (
            [("abort",)]
            if max_stmts < 2
            else [
                (
                    "if_else",
                    ("cmp", "==", ("local", 0), ("lit", {"kind": "int", "int_kind": "u32", "bits": "0"})),
                    [("abort",)],
                    [],
                )
            ]
        )
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=False,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", "u32"),
            ret_expr=("local", 0),
        )
        return (
            [arg_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", "u32"),
            default_fuel,
        )
    if variant == 1:
        arg_val = {"kind": "bool", "value": True}
        params = [(("bool",), arg_val)]
        locals_list = [
            (("int", "u32"), ("lit", {"kind": "int", "int_kind": "u32", "bits": "7"}))
        ]
        body = (
            [("hint_unreachable",)]
            if max_stmts < 2
            else [("if_else", ("param", 0), [("hint_unreachable",)], [])]
        )
        src = _render_gen_program_standalone(
            fn_name=fn_name,
            is_unsafe=True,
            params=params,
            locals_list=locals_list,
            body=body,
            ret_ty=("int", "u32"),
            ret_expr=("local", 0),
        )
        return (
            [arg_val],
            hashlib.sha256(src.encode("utf-8")).hexdigest(),
            [pty for pty, _ in params],
            ("int", "u32"),
            default_fuel,
        )
    arg_val = {"kind": "int", "int_kind": "u32", "bits": "1"}
    params = [(("int", "u32"), arg_val)]
    locals_list = [(("int", "u32"), ("param", 0))]
    body = [
        (
            "while_loop",
            120,
            [
                (
                    "assign",
                    0,
                    (
                        "bin_arith",
                        "+",
                        "u32",
                        ("local", 0),
                        ("lit", {"kind": "int", "int_kind": "u32", "bits": "1"}),
                    ),
                )
            ],
            None,
            None,
        )
    ]
    src = _render_gen_program_standalone(
        fn_name=fn_name,
        is_unsafe=False,
        params=params,
        locals_list=locals_list,
        body=body,
        ret_ty=("int", "u32"),
        ret_expr=("local", 0),
    )
    return (
        [arg_val],
        hashlib.sha256(src.encode("utf-8")).hexdigest(),
        [pty for pty, _ in params],
        ("int", "u32"),
        min(default_fuel, 40),
    )


def _expected_fuzz_case_details(
    master_seed: int,
    case_index: int,
    max_stmts: int,
    ub_ratio: float,
    default_fuel: int = 1500,
) -> tuple[str, list[dict[str, Any]], str, list[tuple[str, ...]], tuple[str, ...], int]:
    """Regenerate `(category, args, program_sha256, param_tys, ret_ty, fuel)`."""
    rng = _SplitMix64.for_case(master_seed, case_index)
    cat = _choose_fuzz_category(rng, case_index, ub_ratio)
    fn_name = f"fuzz_case_{case_index:04d}"
    case_fuel = default_fuel
    if cat == "safe_admitted":
        args, prog_sha, param_tys, ret_ty = _gen_safe_program(
            rng, fn_name, max_stmts, False
        )
    elif cat == "boundary_edge_case":
        args, prog_sha, param_tys, ret_ty = _gen_boundary_program(
            rng, fn_name, case_index, max_stmts
        )
    elif cat == "targeted_ub_probe":
        args, prog_sha, param_tys, ret_ty = _gen_ub_probe_program(
            rng, fn_name, case_index, max_stmts
        )
    else:
        args, prog_sha, param_tys, ret_ty, case_fuel = _gen_scope_control_program(
            rng, fn_name, case_index, max_stmts, default_fuel=default_fuel
        )
    return cat, args, prog_sha, param_tys, ret_ty, case_fuel


def _expected_fuzz_case_spec(
    master_seed: int, case_index: int, max_stmts: int, ub_ratio: float
) -> tuple[str, list[dict[str, Any]], str]:
    """Regenerate `(category, args, program_sha256)` deterministically."""
    cat, args, prog_sha, _, _, _ = _expected_fuzz_case_details(
        master_seed, case_index, max_stmts, ub_ratio
    )
    return cat, args, prog_sha


def _expected_fuzz_case_args(
    master_seed: int, case_index: int, max_stmts: int, ub_ratio: float
) -> list[dict[str, Any]]:
    """Derive deterministic `args` from `(seed, index, max_stmts, ub_ratio)`."""
    _, args, _ = _expected_fuzz_case_spec(master_seed, case_index, max_stmts, ub_ratio)
    return args


_EVIDENCE_KEYS = frozenset(
    {
        "body_id",
        "fn_identity",
        "local_slot",
        "arg_count",
        "local_tys",
        "blocks",
        "total_steps",
        "init_step",
        "move_step",
        "reinit_step",
        "read_step",
        "lean_probe_line",
        "capture_body_sha256",
    }
)
_COORD_KEYS = frozenset({"step", "block", "stmt"})


def _is_nonneg_int(val: Any) -> bool:
    return not isinstance(val, bool) and isinstance(val, int) and val >= 0


def _validate_step_coord(raw: Any, label: str) -> dict[str, int]:
    if not isinstance(raw, dict) or set(raw.keys()) != _COORD_KEYS:
        raise ValueError(f"{label} must have exact keys {sorted(_COORD_KEYS)}")
    for k in _COORD_KEYS:
        if not _is_nonneg_int(raw[k]):
            raise ValueError(f"{label}.{k} must be non-negative int")
    return {"step": int(raw["step"]), "block": int(raw["block"]), "stmt": int(raw["stmt"])}


def _canonical_capture_body_sha256(
    fn_identity: str,
    arg_count: int,
    local_tys: list[Any],
    blocks: list[Any],
) -> str:
    payload = {
        "identity": fn_identity,
        "arg_count": arg_count,
        "local_tys": local_tys,
        "blocks": blocks,
    }
    raw = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _is_non_zst_captured_ty(ty: Any) -> bool:
    if not isinstance(ty, dict):
        return False
    kind = ty.get("kind")
    if kind in ("bool", "char", "ordering", "int", "overflow_pair"):
        return True
    if kind == "enum":
        tag = ty.get("tag_repr")
        return isinstance(tag, dict) and tag.get("kind") == "scalar"
    return False


def _block_action_at(
    blocks: list[dict[str, Any]], coord: dict[str, int], label: str
) -> tuple[bool, dict[str, Any]]:
    b_idx = coord["block"]
    s_idx = coord["stmt"]
    if b_idx >= len(blocks):
        raise ValueError(
            f"{label} block {b_idx} out of bounds ({len(blocks)})"
        )
    blk = blocks[b_idx]
    if not isinstance(blk, dict):
        raise ValueError(f"{label} block {b_idx} must be a dict")
    stmts = blk.get("statements")
    if not isinstance(stmts, list):
        raise ValueError(f"{label} block {b_idx} missing `statements` list")
    if s_idx < len(stmts):
        st = stmts[s_idx]
        if not isinstance(st, dict):
            raise ValueError(f"{label} stmt {b_idx}:{s_idx} must be a dict")
        return (False, st)
    if s_idx == len(stmts):
        term = blk.get("terminator")
        if not isinstance(term, dict):
            raise ValueError(
                f"{label} block {b_idx} missing dict `terminator`"
            )
        return (True, term)
    raise ValueError(
        f"{label} stmt {s_idx} out of bounds for block {b_idx} ({len(stmts)})"
    )


def _stmt_writes_local(stmt: dict[str, Any], target_local: int) -> bool:
    kind = stmt.get("kind")
    if kind == "assign":
        return (
            not isinstance(stmt.get("local"), bool)
            and stmt.get("local") == target_local
        )
    if kind == "assign_place":
        pl = stmt.get("place")
        return (
            isinstance(pl, dict)
            and pl.get("projection") == []
            and not isinstance(pl.get("local"), bool)
            and pl.get("local") == target_local
        )
    return False


def _operand_moves_local(op: Any, target_local: int) -> bool:
    if not isinstance(op, dict):
        return False
    kind = op.get("kind")
    if kind == "move":
        return (
            not isinstance(op.get("local"), bool)
            and op.get("local") == target_local
        )
    if kind == "move_place":
        pl = op.get("place")
        return (
            isinstance(pl, dict)
            and pl.get("projection") == []
            and not isinstance(pl.get("local"), bool)
            and pl.get("local") == target_local
        )
    return False


def _operand_reads_local(op: Any, target_local: int) -> bool:
    if not isinstance(op, dict):
        return False
    kind = op.get("kind")
    if kind in ("copy", "move"):
        return (
            not isinstance(op.get("local"), bool)
            and op.get("local") == target_local
        )
    if kind in ("copy_place", "move_place"):
        pl = op.get("place")
        return (
            isinstance(pl, dict)
            and not isinstance(pl.get("local"), bool)
            and pl.get("local") == target_local
        )
    return False


def _rvalue_reads_local(rv: Any, target_local: int) -> bool:
    if not isinstance(rv, dict):
        return False
    kind = rv.get("kind")
    if kind in ("use", "use_retag", "unary", "cast"):
        return _operand_reads_local(rv.get("operand"), target_local)
    if kind == "binary":
        return _operand_reads_local(
            rv.get("left"), target_local
        ) or _operand_reads_local(rv.get("right"), target_local)
    if kind == "discriminant":
        pl = rv.get("place")
        if isinstance(pl, dict):
            return (
                not isinstance(pl.get("local"), bool)
                and pl.get("local") == target_local
            )
        return (
            not isinstance(rv.get("local"), bool)
            and rv.get("local") == target_local
        )
    if kind == "aggregate_tuple":
        fields = rv.get("fields")
        return isinstance(fields, list) and any(
            _operand_reads_local(f, target_local) for f in fields
        )
    if kind == "aggregate_range_to":
        return _operand_reads_local(rv.get("end"), target_local)
    if kind == "aggregate_range_from":
        return _operand_reads_local(rv.get("start"), target_local)
    return False


def _term_reads_local(term: dict[str, Any], target_local: int) -> bool:
    kind = term.get("kind")
    if kind == "switch_int":
        return _operand_reads_local(term.get("operand"), target_local)
    if kind == "assert":
        return _operand_reads_local(term.get("cond"), target_local)
    if kind in ("core_call", "call", "sysroot_call"):
        args = term.get("args")
        return isinstance(args, list) and any(
            _operand_reads_local(a, target_local) for a in args
        )
    return False


def _term_moves_local(term: dict[str, Any], target_local: int) -> bool:
    kind = term.get("kind")
    if kind == "switch_int":
        return _operand_moves_local(term.get("operand"), target_local)
    if kind == "assert":
        return _operand_moves_local(term.get("cond"), target_local)
    if kind in ("core_call", "call", "sysroot_call"):
        args = term.get("args")
        return isinstance(args, list) and any(
            _operand_moves_local(a, target_local) for a in args
        )
    return False


def _block_successors(term: Any, n_blocks: int) -> list[int]:
    if not isinstance(term, dict):
        return []
    kind = term.get("kind")
    out: list[int] = []
    if kind == "goto":
        b = term.get("block")
        if _is_nonneg_int(b) and b < n_blocks:
            out.append(int(b))
    elif kind == "switch_int":
        targets = term.get("targets")
        if isinstance(targets, list):
            for pair in targets:
                if (
                    isinstance(pair, list)
                    and len(pair) == 2
                    and _is_nonneg_int(pair[1])
                    and pair[1] < n_blocks
                ):
                    out.append(int(pair[1]))
        oth = term.get("otherwise")
        if _is_nonneg_int(oth) and oth < n_blocks:
            out.append(int(oth))
    elif kind in ("assert", "core_call", "call", "sysroot_call"):
        tgt = term.get("target")
        if _is_nonneg_int(tgt) and tgt < n_blocks:
            out.append(int(tgt))
    return out


def _cfg_can_reach(
    blocks: list[dict[str, Any]],
    from_block: int,
    to_block: int,
    *,
    allow_zero_edges: bool,
) -> bool:
    if allow_zero_edges and from_block == to_block:
        return True
    seen: set[int] = set()
    q: deque[int] = deque()
    for succ in _block_successors(blocks[from_block].get("terminator"), len(blocks)):
        if succ not in seen:
            seen.add(succ)
            q.append(succ)
    while q:
        cur = q.popleft()
        if cur == to_block:
            return True
        for succ in _block_successors(blocks[cur].get("terminator"), len(blocks)):
            if succ not in seen:
                seen.add(succ)
                q.append(succ)
    return False


def _cfg_step_follows(
    blocks: list[dict[str, Any]], a: dict[str, int], b: dict[str, int]
) -> bool:
    if a["block"] == b["block"] and a["stmt"] < b["stmt"]:
        return True
    return _cfg_can_reach(
        blocks, a["block"], b["block"], allow_zero_edges=(a["block"] != b["block"])
    )


def _lean_int_kind_from_probe(width: str, sign: str) -> str | None:
    if sign not in ("s", "u"):
        return None
    if width == "isize":
        return "isize" if sign == "s" else "usize"
    if width in ("i8", "i16", "i32", "i64", "i128"):
        return width if sign == "s" else ("u" + width[1:])
    return None


def _verify_lean_probe_payload(payload: str, lean_outcome: dict[str, Any]) -> bool:
    lkind = lean_outcome.get("kind")
    if payload == "UNWOUND":
        return lkind == "unwound"
    if payload == "ABORTED":
        return lean_outcome == {
            "kind": "abnormal_abort",
            "detail": "Trusted.MirModel.TerminalOut.aborted",
        }
    if not payload.startswith("RETURNED:") or lkind != "returned":
        return False
    val = lean_outcome.get("value")
    if not isinstance(val, dict):
        return False
    spec = payload[len("RETURNED:") :]
    if spec == "UNIT":
        return val == {"kind": "unit"}
    if spec == "BOOL:true":
        return val == {"kind": "bool", "value": True}
    if spec == "BOOL:false":
        return val == {"kind": "bool", "value": False}
    if spec.startswith("CHAR:"):
        raw = spec[len("CHAR:") :]
        return raw.isdigit() and val == {"kind": "char", "scalar": int(raw)}
    if spec.startswith("ORDERING:"):
        ord_val = spec[len("ORDERING:") :]
        return ord_val in ("less", "equal", "greater") and val == {
            "kind": "ordering",
            "value": ord_val,
        }
    if spec.startswith("INT:"):
        parts = spec[len("INT:") :].split(":")
        if len(parts) != 3:
            return False
        ik = _lean_int_kind_from_probe(parts[0], parts[1])
        return ik is not None and val == {
            "kind": "int",
            "int_kind": ik,
            "bits": parts[2],
        }
    if spec.startswith("OVF:"):
        parts = spec[len("OVF:") :].split(":")
        if len(parts) != 4 or parts[3] not in ("true", "false"):
            return False
        ik = _lean_int_kind_from_probe(parts[0], parts[1])
        return ik is not None and val == {
            "kind": "overflow_pair",
            "int_kind": ik,
            "bits": parts[2],
            "overflow": parts[3] == "true",
        }
    return False


def _matches_fn_identity(fn_identity: Any, fn_name: str) -> bool:
    return isinstance(fn_identity, str) and (
        fn_identity == fn_name
        or fn_identity == f"rust-path-v1::{fn_name}"
        or fn_identity.endswith(f"::{fn_name}")
    )


def _verify_move_reinit_evidence(
    case: dict[str, Any], idx: int
) -> dict[str, Any]:
    case_id = case["case_id"]
    fn_name = case["fn_name"]
    args = case.get("args")
    if not isinstance(args, list):
        raise ValueError(f"fuzz case [{idx}] ({case_id}) missing `args` list")
    ev = case.get("move_reinit_evidence")
    if not isinstance(ev, dict) or set(ev.keys()) != _EVIDENCE_KEYS:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `exercised_move_reinit` requires "
            "valid `move_reinit_evidence`"
        )
    body_id = ev["body_id"]
    fn_identity = ev["fn_identity"]
    local_slot = ev["local_slot"]
    arg_count = ev["arg_count"]
    total_steps = ev["total_steps"]
    local_tys = ev["local_tys"]
    blocks = ev["blocks"]
    sha = ev["capture_body_sha256"]
    probe_line = ev["lean_probe_line"]

    if not _is_nonneg_int(body_id):
        raise ValueError(f"fuzz case [{idx}] invalid evidence `body_id`")
    if not _matches_fn_identity(fn_identity, fn_name):
        raise ValueError(
            f"fuzz case [{idx}] evidence `fn_identity` {fn_identity!r} != {fn_name!r}"
        )
    if not _is_nonneg_int(arg_count) or int(arg_count) != len(args):
        raise ValueError(
            f"fuzz case [{idx}] evidence `arg_count` {arg_count!r} != {len(args)}"
        )
    if not isinstance(local_tys, list) or not isinstance(blocks, list) or not blocks:
        raise ValueError(
            f"fuzz case [{idx}] evidence invalid `local_tys` or `blocks`"
        )
    if not _is_nonneg_int(local_slot) or not (
        int(arg_count) < int(local_slot) < len(local_tys)
    ):
        raise ValueError(
            f"fuzz case [{idx}] evidence `local_slot` {local_slot!r} out of range"
        )
    if not _is_non_zst_captured_ty(local_tys[int(local_slot)]):
        raise ValueError(
            f"fuzz case [{idx}] evidence `local_slot` {local_slot} is not non-ZST"
        )
    if not _is_nonneg_int(total_steps) or int(total_steps) <= 0:
        raise ValueError(f"fuzz case [{idx}] invalid evidence `total_steps`")

    init_step = _validate_step_coord(ev["init_step"], f"case[{idx}].init_step")
    move_step = _validate_step_coord(ev["move_step"], f"case[{idx}].move_step")
    reinit_step = _validate_step_coord(
        ev["reinit_step"], f"case[{idx}].reinit_step"
    )
    read_step = _validate_step_coord(ev["read_step"], f"case[{idx}].read_step")
    if not (
        init_step["step"]
        < move_step["step"]
        < reinit_step["step"]
        < read_step["step"]
        < int(total_steps)
    ):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) non-monotonic move/reinit trace steps"
        )

    if not _is_valid_sha256_hex(sha):
        raise ValueError(f"fuzz case [{idx}] invalid `capture_body_sha256`")
    expected_sha = _canonical_capture_body_sha256(
        fn_identity, int(arg_count), local_tys, blocks
    )
    if sha != expected_sha:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `capture_body_sha256` mismatch"
        )

    expected_prefix = (
        f"ANNEAL_LEAN_CASE:{case_id}:BODY|{int(body_id)}|{fn_identity}|"
        f"MR1|{int(local_slot)}|{int(total_steps)}|"
        f"{init_step['step']},{init_step['block']},{init_step['stmt']}|"
        f"{move_step['step']},{move_step['block']},{move_step['stmt']}|"
        f"{reinit_step['step']},{reinit_step['block']},{reinit_step['stmt']}|"
        f"{read_step['step']},{read_step['block']},{read_step['stmt']}:"
    )
    if not isinstance(probe_line, str) or not probe_line.startswith(
        expected_prefix
    ):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `lean_probe_line` does not bind "
            "witness trace"
        )
    payload = probe_line[len(expected_prefix) :]
    if not _verify_lean_probe_payload(payload, case["lean"]):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `lean_probe_line` payload "
            f"{payload!r} disagrees with serialized `lean` outcome"
        )

    slot = int(local_slot)
    init_is_term, init_act = _block_action_at(
        blocks, init_step, f"case[{idx}].init"
    )
    if init_is_term or not _stmt_writes_local(init_act, slot):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) init step does not assign slot {slot}"
        )

    move_is_term, move_act = _block_action_at(
        blocks, move_step, f"case[{idx}].move"
    )
    if move_is_term:
        move_ok = _term_moves_local(move_act, slot)
    else:
        rv = move_act.get("value")
        move_ok = (
            move_act.get("kind") in ("assign", "assign_place")
            and not _stmt_writes_local(move_act, slot)
            and isinstance(rv, dict)
            and rv.get("kind") in ("use", "use_retag")
            and _operand_moves_local(rv.get("operand"), slot)
        )
    if not move_ok:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) move step does not execute "
            f"`Operand::Move` on slot {slot}"
        )

    reinit_is_term, reinit_act = _block_action_at(
        blocks, reinit_step, f"case[{idx}].reinit"
    )
    if reinit_is_term or not _stmt_writes_local(reinit_act, slot):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) reinit step does not assign slot {slot}"
        )

    read_is_term, read_act = _block_action_at(
        blocks, read_step, f"case[{idx}].read"
    )
    if read_is_term:
        read_ok = _term_reads_local(read_act, slot)
    else:
        read_ok = read_act.get("kind") in (
            "assign",
            "assign_place",
        ) and _rvalue_reads_local(read_act.get("value"), slot)
    if not read_ok:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) read step does not read "
            f"reinitialized slot {slot}"
        )

    if (
        not _cfg_can_reach(blocks, 0, init_step["block"], allow_zero_edges=True)
        or not _cfg_step_follows(blocks, init_step, move_step)
        or not _cfg_step_follows(blocks, move_step, reinit_step)
        or not _cfg_step_follows(blocks, reinit_step, read_step)
    ):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) CFG blocks do not connect "
            "init -> move -> reinit -> read"
        )

    return {
        "case_id": case_id,
        "body_id": int(body_id),
        "fn_identity": fn_identity,
        "local_slot": slot,
        "total_steps": int(total_steps),
        "capture_body_sha256": sha,
        "init_step": init_step,
        "move_step": move_step,
        "reinit_step": reinit_step,
        "read_step": read_step,
    }


_CAPTURE_BODY_KEYS = frozenset(
    {
        "body_id",
        "fn_identity",
        "arg_count",
        "local_tys",
        "blocks",
        "capture_body_sha256",
    }
)
_LEG_EVIDENCE_KEYS = frozenset(
    {
        "lean_probe_line",
        "capture_refusal_json",
        "miri_evidence",
        "rustc_evidence",
        "mir_eval_body_id",
        "mir_eval_raw_json",
    }
)
_SHRINK_TRACE_KEYS = frozenset(
    {
        "original_nodes",
        "shrunk_nodes",
        "steps_evaluated",
        "oracle_runs",
        "cache_hits",
        "converged_1_minimal",
        "minimized_source",
        "minimized_args",
    }
)
_SHRINK_VERIFICATION_KEYS = frozenset(
    {
        "fn_name",
        "args",
        "program_sha256",
        "fuel",
        "capture_body",
        "rustc",
        "miri",
        "lean",
        "mir_eval",
        "capture_rejected",
        "leg_evidence",
        "evaluation",
    }
)
_GEN_INT_TO_IR: dict[str, tuple[str, bool]] = {
    k: (
        ("isize" if k in ("isize", "usize") else ("i" + k[1:])),
        k.startswith("i"),
    )
    for k in _ALL_INT_KINDS
}
_GEN_ENUM_IR_SPEC: dict[str, tuple[str, bool, list[str]]] = {
    "GenSignedTag": ("i16", True, ["65531", "0", "4", "300"]),
    "GenUnsignedTag": ("i8", False, ["0", "7", "250"]),
    "GenSoloRepr": ("i8", False, ["42"]),
    "GenZstUnit": ("isize", True, ["0"]),
}


def _mir_value_gen_ty(val: dict[str, Any]) -> tuple[str, ...]:
    vkind = val["kind"]
    if vkind == "int":
        return ("int", str(val["int_kind"]))
    if vkind == "overflow_pair":
        return ("overflow_pair", str(val["int_kind"]))
    if vkind == "enum":
        return ("enum", str(val["enum_type"]))
    return (str(vkind),)


def _captured_ty_matches_gen_ty(
    cap_ty: Any, gen_ty: tuple[str, ...]
) -> bool:
    if not isinstance(cap_ty, dict):
        return False
    tag = gen_ty[0]
    if tag in ("bool", "char", "ordering", "unit"):
        return cap_ty == {"kind": tag}
    if tag in ("int", "overflow_pair"):
        width, signed = _GEN_INT_TO_IR[gen_ty[1]]
        return cap_ty == {"kind": tag, "width": width, "signed": signed}
    if tag == "enum":
        ekind = gen_ty[1]
        if ekind not in _GEN_ENUM_IR_SPEC:
            return False
        exp_w, exp_s, exp_discrs = _GEN_ENUM_IR_SPEC[ekind]
        return (
            cap_ty.get("kind") == "enum"
            and _is_nonneg_int(cap_ty.get("id"))
            and cap_ty.get("discr_width") == exp_w
            and cap_ty.get("discr_signed") is exp_s
            and cap_ty.get("discriminants") == exp_discrs
        )
    return False


def _validate_fuzz_capture_body(
    cb: Any,
    *,
    label: str,
    fn_name: str,
    expected_param_tys: list[tuple[str, ...]],
    expected_ret_ty: tuple[str, ...] | dict[str, Any],
) -> dict[str, Any]:
    if not isinstance(cb, dict) or set(cb.keys()) != _CAPTURE_BODY_KEYS:
        raise ValueError(
            f"{label} `capture_body` must have exact keys "
            f"{sorted(_CAPTURE_BODY_KEYS)}"
        )
    body_id = cb["body_id"]
    fn_identity = cb["fn_identity"]
    arg_count = cb["arg_count"]
    local_tys = cb["local_tys"]
    blocks = cb["blocks"]
    sha = cb["capture_body_sha256"]
    if not _is_nonneg_int(body_id):
        raise ValueError(f"{label} invalid `capture_body.body_id`")
    if not _matches_fn_identity(fn_identity, fn_name):
        raise ValueError(
            f"{label} invalid `capture_body.fn_identity` {fn_identity!r} "
            f"for {fn_name!r}"
        )
    if not _is_nonneg_int(arg_count) or int(arg_count) != len(expected_param_tys):
        raise ValueError(
            f"{label} `capture_body.arg_count` {arg_count!r} != "
            f"{len(expected_param_tys)}"
        )
    if (
        not isinstance(local_tys, list)
        or len(local_tys) < 1 + len(expected_param_tys)
        or not isinstance(blocks, list)
        or not blocks
    ):
        raise ValueError(
            f"{label} `capture_body` has invalid `local_tys` or empty `blocks`"
        )
    for b_idx, blk in enumerate(blocks):
        if (
            not isinstance(blk, dict)
            or not isinstance(blk.get("statements"), list)
            or not isinstance(blk.get("terminator"), dict)
        ):
            raise ValueError(
                f"{label} `capture_body.blocks[{b_idx}]` has invalid MIR block shape"
            )
    if isinstance(expected_ret_ty, dict):
        ret_ok = local_tys[0] == expected_ret_ty
    else:
        ret_ok = _captured_ty_matches_gen_ty(local_tys[0], expected_ret_ty)
    if not ret_ok:
        raise ValueError(
            f"{label} `capture_body.local_tys[0]` {local_tys[0]!r} != "
            f"expected return type {expected_ret_ty!r}"
        )
    for p_idx, pty in enumerate(expected_param_tys):
        if not _captured_ty_matches_gen_ty(local_tys[1 + p_idx], pty):
            raise ValueError(
                f"{label} `capture_body.local_tys[{1 + p_idx}]` "
                f"{local_tys[1 + p_idx]!r} != expected param type {pty!r}"
            )
    if not isinstance(sha, str) or not _is_valid_sha256_hex(sha):
        raise ValueError(
            f"{label} invalid `capture_body.capture_body_sha256`"
        )
    expected_sha = _canonical_capture_body_sha256(
        fn_identity, int(arg_count), local_tys, blocks
    )
    if sha != expected_sha:
        raise ValueError(
            f"{label} `capture_body.capture_body_sha256` mismatch against "
            "serialized capture data"
        )
    return cb


def _parse_rust_ret_payload(payload: str) -> dict[str, Any] | None:
    if payload == "UNIT":
        return {"kind": "unit"}
    if payload == "BOOL:true":
        return {"kind": "bool", "value": True}
    if payload == "BOOL:false":
        return {"kind": "bool", "value": False}
    if payload.startswith("CHAR:"):
        raw = payload[len("CHAR:") :].strip()
        if not raw.isdigit():
            return None
        scalar = int(raw, 10)
        if scalar > 0x10_FFFF or (0xD800 <= scalar <= 0xDFFF):
            return None
        return {"kind": "char", "scalar": scalar}
    if payload.startswith("ORDERING:"):
        raw_ord = payload[len("ORDERING:") :].strip()
        if raw_ord not in ("less", "equal", "greater"):
            return None
        return {"kind": "ordering", "value": raw_ord}
    if payload.startswith("INT:"):
        parts = payload[len("INT:") :].split(":", 1)
        if len(parts) != 2:
            return None
        ikind, dec_raw = parts[0], parts[1].strip()
        if ikind not in _INT_KIND_BITS:
            return None
        bits = _parse_rust_decimal_bits(ikind, dec_raw)
        if bits is None:
            return None
        return {"kind": "int", "int_kind": ikind, "bits": bits}
    if payload.startswith("OVF:"):
        parts = payload[len("OVF:") :].split(":")
        if len(parts) != 3:
            return None
        ikind, dec_raw, ovf_raw = parts[0], parts[1].strip(), parts[2].strip()
        if ikind not in _INT_KIND_BITS or ovf_raw not in ("true", "false"):
            return None
        bits = _parse_rust_decimal_bits(ikind, dec_raw)
        if bits is None:
            return None
        return {
            "kind": "overflow_pair",
            "int_kind": ikind,
            "bits": bits,
            "overflow": ovf_raw == "true",
        }
    return None


def _parse_rust_decimal_bits(ikind: str, dec_raw: str) -> str | None:
    if not dec_raw or (
        not dec_raw.isdigit()
        and not (dec_raw[0] in ("-", "+") and dec_raw[1:].isdigit())
    ):
        return None
    val = int(dec_raw, 10)
    w = _INT_KIND_BITS[ikind]
    if ikind.startswith("i"):
        lo = -(1 << (w - 1))
        hi = (1 << (w - 1)) - 1
        if not (lo <= val <= hi):
            return None
        return str(val & ((1 << w) - 1))
    if not (0 <= val < (1 << w)):
        return None
    return str(val)


def _valid_mr_tag_shape(mr_tag: str) -> bool:
    if mr_tag == "MR0":
        return True
    if not mr_tag.startswith("MR1|"):
        return False
    parts = mr_tag[len("MR1|") :].split("|")
    if len(parts) != 6 or not parts[0].isdigit() or not parts[1].isdigit():
        return False
    total_steps = int(parts[1])
    coords: list[int] = []
    for raw_c in parts[2:]:
        cparts = raw_c.split(",")
        if len(cparts) != 3 or any(not p.isdigit() for p in cparts):
            return False
        coords.append(int(cparts[0]))
    return coords[0] < coords[1] < coords[2] < coords[3] < total_steps


def _lean_probe_line_matches_outcome(
    probe_line: str,
    case_id: str,
    lean: dict[str, Any],
    *,
    capture_body: dict[str, Any] | None = None,
) -> bool:
    if not isinstance(capture_body, dict):
        return False
    expected_body_id = capture_body.get("body_id")
    expected_identity = capture_body.get("fn_identity")
    if (
        not _is_nonneg_int(expected_body_id)
        or not isinstance(expected_identity, str)
        or not expected_identity
    ):
        return False
    prefix = f"ANNEAL_LEAN_CASE:{case_id}:"
    if not probe_line.startswith(prefix):
        return False
    rest = probe_line[len(prefix) :]
    if not rest.startswith("BODY|"):
        return False
    body_parts = rest[len("BODY|") :].split("|", 2)
    if len(body_parts) != 3:
        return False
    body_id_str, fn_ident, mr_and_payload = body_parts
    if not body_id_str.isdigit() or int(body_id_str) != int(expected_body_id):
        return False
    if fn_ident != expected_identity:
        return False
    if ":" not in mr_and_payload:
        return False
    mr_tag, payload = mr_and_payload.split(":", 1)
    if not _valid_mr_tag_shape(mr_tag):
        return False
    if payload == "INIT_UNSUPPORTED":
        return lean == {
            "kind": "init_unsupported",
            "detail": (
                "Anneal.MirTotal.StepCore.initStateBy returned .error .unsupported"
            ),
        }
    if payload == "INIT_UNDEFINED":
        return lean == {
            "kind": "init_unsupported",
            "detail": (
                "Anneal.MirTotal.StepCore.initStateBy returned .error .undefined"
            ),
        }
    if payload == "FAULT:unsupported":
        return lean == {
            "kind": "unsupported",
            "detail": "Trusted.MirSemantics.FaultKind.unsupported",
        }
    if payload == "UNWOUND":
        return lean == {
            "kind": "unwound",
            "detail": "Trusted.MirModel.TerminalOut.unwound",
        }
    if payload == "ABORTED":
        return lean == {
            "kind": "abnormal_abort",
            "detail": "Trusted.MirModel.TerminalOut.aborted",
        }
    if payload == "OUT_OF_FUEL":
        return lean == {
            "kind": "out_of_fuel",
            "detail": "Anneal.MirTotal.evalMirFuelBy reached fuel limit",
        }
    if payload == "FAULT:undefined":
        return lean == {
            "kind": "undefined_behavior",
            "detail": "Trusted.MirSemantics.FaultKind.undefined",
        }
    if payload.startswith("FAULT:undefined:"):
        cause = payload[len("FAULT:undefined:") :]
        exp_detail = (
            "Trusted.MirSemantics.FaultKind.undefined"
            if not cause
            else f"Trusted.MirSemantics.FaultKind.undefined ({cause})"
        )
        return lean == {"kind": "undefined_behavior", "detail": exp_detail}
    return _verify_lean_probe_payload(payload, lean)


def _convert_mir_eval_raw_val(raw_val: Any) -> dict[str, Any] | None:
    if not isinstance(raw_val, dict):
        return None
    kind = raw_val.get("kind")
    val = raw_val.get("value")
    if kind == "unit":
        return {"kind": "unit"}
    if kind == "bool" and isinstance(val, bool):
        return {"kind": "bool", "value": val}
    if kind == "char" and isinstance(val, str) and len(val) == 1:
        return {"kind": "char", "scalar": ord(val)}
    if kind == "ordering" and isinstance(val, str):
        norm = val.lower()
        if norm in ("less", "equal", "greater"):
            return {"kind": "ordering", "value": norm}
        return None
    if kind == "scalar" and isinstance(val, dict):
        ik = _lean_int_kind_from_probe(
            str(val.get("width")), "s" if val.get("signed") is True else (
                "u" if val.get("signed") is False else "x"
            )
        )
        bits_raw = val.get("bits")
        if ik is None or not isinstance(bits_raw, str) or not bits_raw.isdigit():
            return None
        try:
            _validate_canonical_int_bits(ik, bits_raw, "mir_eval_raw")
        except ValueError:
            return None
        return {"kind": "int", "int_kind": ik, "bits": bits_raw}
    if kind == "tuple" and isinstance(val, list) and len(val) == 2:
        lhs = _convert_mir_eval_raw_val(val[0])
        rhs = _convert_mir_eval_raw_val(val[1])
        if (
            lhs is not None
            and lhs.get("kind") == "int"
            and rhs is not None
            and rhs.get("kind") == "bool"
        ):
            return {
                "kind": "overflow_pair",
                "int_kind": lhs["int_kind"],
                "bits": lhs["bits"],
                "overflow": rhs["value"],
            }
    return None


def _mir_eval_raw_json_matches(
    raw_json_str: str,
    mir_eval: dict[str, Any],
    *,
    expected_body_id: int,
    expected_identity: str,
) -> bool:
    try:
        trace = json.loads(raw_json_str, parse_constant=_reject_json_constant)
    except (json.JSONDecodeError, ValueError):
        return False
    if not isinstance(trace, dict):
        return False
    emitted_body_id = trace.get("body_id")
    if (
        not isinstance(emitted_body_id, int)
        or isinstance(emitted_body_id, bool)
        or emitted_body_id != expected_body_id
    ):
        return False
    if trace.get("identity") != expected_identity:
        return False
    raw_out = trace.get("outcome")
    if not isinstance(raw_out, dict):
        return False
    okind = raw_out.get("kind")
    oval = raw_out.get("value")
    if okind == "returned" and isinstance(oval, dict):
        ik = oval.get("kind")
        if ik == "returned":
            conv = _convert_mir_eval_raw_val(oval.get("ret"))
            return conv is not None and mir_eval == {
                "kind": "returned",
                "value": conv,
            }
        if ik == "unwound":
            return mir_eval == {
                "kind": "unwound",
                "detail": "anneal-mir-eval unwound",
            }
        return False
    if okind == "aborted":
        return mir_eval == {
            "kind": "abnormal_abort",
            "detail": "anneal-mir-eval aborted (UnwindAction::Terminate)",
        }
    if okind == "out_of_fuel":
        return mir_eval == {
            "kind": "out_of_fuel",
            "detail": "anneal-mir-eval hit fuel limit",
        }
    if okind == "fault" and isinstance(oval, dict):
        fkind = oval.get("kind")
        reason = oval.get("reason")
        if not isinstance(reason, str):
            return False
        if fkind == "undefined":
            return mir_eval == {"kind": "undefined_behavior", "detail": reason}
        if fkind == "unsupported":
            return mir_eval == {"kind": "unsupported", "detail": reason}
    return False


def _capture_refusal_binds_fn(path: str, fn_name: str) -> bool:
    return (
        path == fn_name
        or path == f"rust-path-v1::{fn_name}"
        or path.endswith(f"::{fn_name}")
    )


def _validate_fuzz_leg_evidence(
    obj: dict[str, Any],
    *,
    label: str,
    case_id: str,
    fn_name: str,
    capture_body: dict[str, Any] | None,
    has_rustc_leg: bool,
    has_mir_eval_leg: bool,
) -> None:
    miri = obj["miri"]
    lean = obj["lean"]
    rustc = obj.get("rustc")
    mir_eval = obj.get("mir_eval")
    cap_rej = obj.get("capture_rejected")
    need_miri = miri["kind"] != "tool_error"
    need_lean = cap_rej is None and lean["kind"] != "tool_error"
    need_capture_refusal = cap_rej is not None
    need_rustc = (
        has_rustc_leg and isinstance(rustc, dict) and rustc["kind"] != "tool_error"
    )
    need_mir_eval = (
        has_mir_eval_leg
        and cap_rej is None
        and isinstance(mir_eval, dict)
        and mir_eval["kind"] != "tool_error"
    )
    le = obj.get("leg_evidence")
    if not (
        need_miri
        or need_lean
        or need_capture_refusal
        or need_rustc
        or need_mir_eval
    ):
        if le is not None and not isinstance(le, dict):
            raise ValueError(f"{label} invalid `leg_evidence`")
        return
    if not isinstance(le, dict) or not set(le.keys()).issubset(_LEG_EVIDENCE_KEYS):
        raise ValueError(
            f"{label} missing or malformed `leg_evidence` for active legs"
        )
    if need_capture_refusal:
        crj = le.get("capture_refusal_json")
        if not isinstance(crj, str) or not crj.strip():
            raise ValueError(
                f"{label} missing `leg_evidence.capture_refusal_json` for `capture_rejected`"
            )
        try:
            refusal = json.loads(crj, parse_constant=_reject_json_constant)
        except (json.JSONDecodeError, ValueError) as exc:
            raise ValueError(
                f"{label} invalid `leg_evidence.capture_refusal_json`: {exc}"
            ) from exc
        if not isinstance(refusal, dict) or refusal.get("status") != "unsupported":
            raise ValueError(
                f"{label} `capture_refusal_json` must have status='unsupported'"
            )
        diags = refusal.get("diagnostics")
        if (
            not isinstance(diags, list)
            or not diags
            or not all(isinstance(d, str) and d.strip() for d in diags)
        ):
            raise ValueError(
                f"{label} `capture_refusal_json` missing non-empty `diagnostics`"
            )
        unsup = refusal.get("unsupported")
        if not isinstance(unsup, list) or not unsup:
            raise ValueError(
                f"{label} `capture_refusal_json` must include case-bound `unsupported` items"
            )
        bound = False
        for u in unsup:
            if not isinstance(u, dict):
                raise ValueError(f"{label} invalid item in `capture_refusal_json.unsupported`")
            did = u.get("def_id")
            upath = u.get("path")
            ureason = u.get("reason")
            if (
                isinstance(did, bool)
                or not isinstance(did, int)
                or did < 0
                or not isinstance(upath, str)
                or not upath.strip()
                or not isinstance(ureason, str)
                or not ureason.strip()
            ):
                raise ValueError(
                    f"{label} malformed item in `capture_refusal_json.unsupported`"
                )
            if _capture_refusal_binds_fn(upath, fn_name):
                bound = True
        if not bound:
            raise ValueError(
                f"{label} `capture_refusal_json.unsupported` is not bound to `{fn_name}`"
            )
        expected_reason = f"capture unsupported: {'; '.join(diags)} ({crj.strip()})"
        if cap_rej != expected_reason or lean.get("detail") != expected_reason:
            raise ValueError(
                f"{label} `capture_rejected` / `lean.detail` disagrees with `capture_refusal_json`"
            )
        if (
            le.get("lean_probe_line") is not None
            or le.get("mir_eval_body_id") is not None
            or le.get("mir_eval_raw_json") is not None
        ):
            raise ValueError(
                f"{label} capture-rejected case must not carry Lean/mir_eval probe evidence"
            )
    elif le.get("capture_refusal_json") is not None:
        raise ValueError(
            f"{label} unexpected `leg_evidence.capture_refusal_json` without `capture_rejected`"
        )
    if need_miri:
        mev = le.get("miri_evidence")
        run_prefix = f"ANNEAL_MIRI_RUN:{case_id}:{fn_name}|"
        if not isinstance(mev, str) or not mev.startswith(run_prefix):
            raise ValueError(
                f"{label} missing or unbound `leg_evidence.miri_evidence`"
            )
        rest = mev[len(run_prefix) :]
        if miri["kind"] == "returned":
            case_prefix = f"ANNEAL_MIRI_CASE:{case_id}:"
            if not rest.startswith(case_prefix):
                raise ValueError(
                    f"{label} `miri_evidence` missing `{case_prefix}` payload"
                )
            decoded = _parse_rust_ret_payload(rest[len(case_prefix) :])
            if decoded != miri["value"]:
                raise ValueError(
                    f"{label} `miri_evidence` payload disagrees with `miri` value"
                )
        else:
            tag_map = {
                "undefined_behavior": "UB",
                "abnormal_abort": "ABORT",
                "panic": "PANIC",
                "unsupported": "UNSUPPORTED",
            }
            tag = tag_map.get(miri["kind"])
            if tag is None or rest != f"{tag}|{miri['detail']}":
                raise ValueError(
                    f"{label} `miri_evidence` fault tag/detail disagrees with `miri`"
                )
    if need_lean:
        lpl = le.get("lean_probe_line")
        if not isinstance(lpl, str) or not _lean_probe_line_matches_outcome(
            lpl, case_id, lean, capture_body=capture_body
        ):
            raise ValueError(
                f"{label} missing or mismatched `leg_evidence.lean_probe_line`"
            )
    if need_rustc:
        assert isinstance(rustc, dict)
        rev = le.get("rustc_evidence")
        run_prefix = f"ANNEAL_RUSTC_RUN:{case_id}:{fn_name}|"
        if not isinstance(rev, str) or not rev.startswith(run_prefix):
            raise ValueError(
                f"{label} missing or unbound `leg_evidence.rustc_evidence`"
            )
        rest = rev[len(run_prefix) :]
        if rustc["kind"] == "returned":
            case_prefix = f"ANNEAL_RUSTC_CASE:{case_id}:"
            if not rest.startswith(case_prefix):
                raise ValueError(
                    f"{label} `rustc_evidence` missing `{case_prefix}` payload"
                )
            decoded = _parse_rust_ret_payload(rest[len(case_prefix) :])
            if decoded != rustc["value"]:
                raise ValueError(
                    f"{label} `rustc_evidence` payload disagrees with `rustc` value"
                )
        else:
            rtag_map = {"abnormal_abort": "ABORT", "panic": "PANIC"}
            rtag = rtag_map.get(rustc["kind"])
            if rtag is None or rest != f"{rtag}|{rustc['detail']}":
                raise ValueError(
                    f"{label} `rustc_evidence` fault tag/detail disagrees with `rustc`"
                )
    if need_mir_eval:
        assert isinstance(mir_eval, dict)
        if capture_body is None or le.get("mir_eval_body_id") != capture_body["body_id"]:
            raise ValueError(
                f"{label} `leg_evidence.mir_eval_body_id` does not match `capture_body.body_id`"
            )
        raw_js = le.get("mir_eval_raw_json")
        if not isinstance(raw_js, str) or not _mir_eval_raw_json_matches(
            raw_js,
            mir_eval,
            expected_body_id=capture_body["body_id"],
            expected_identity=capture_body["fn_identity"],
        ):
            raise ValueError(
                f"{label} `leg_evidence.mir_eval_raw_json` disagrees with `mir_eval` or body identity"
            )


def _classify_ub_bucket(detail: str) -> str:
    lower = detail.lower()
    if "dividing by zero" in lower or "divisor of zero" in lower:
        return "division_by_zero"
    if (
        "overflow in signed" in lower
        or "calculating the remainder with overflow" in lower
        or "dividing min by -1" in lower
    ):
        return "signed_div_overflow"
    if (
        "arithmetic overflow" in lower
        or "overflowing add" in lower
        or "overflowing sub" in lower
        or "overflowing mul" in lower
    ):
        return "arithmetic_overflow"
    if "overflowing shift" in lower:
        return "oversized_shift"
    if "unreachable" in lower:
        return "unreachable"
    if "invalid value" in lower or "discriminant" in lower:
        return "invalid_value"
    if "uninitialized" in lower or "uninit" in lower:
        return "uninitialized"
    return "other"


def _fuzz_obj_has_tool_error(obj: dict[str, Any]) -> bool:
    ev = obj["evaluation"]
    rustc = obj.get("rustc")
    rustc_st = (ev.get("rustc_status") or {}).get("status")
    rustc_err = (
        rustc_st != "ignored_due_to_miri_ub"
        and isinstance(rustc, dict)
        and rustc["kind"] == "tool_error"
    )
    miri_err = obj["miri"]["kind"] == "tool_error"
    mir_eval = obj.get("mir_eval")
    me_err = isinstance(mir_eval, dict) and mir_eval["kind"] == "tool_error"
    lean_err = obj.get("capture_rejected") is None and obj["lean"]["kind"] == "tool_error"
    return miri_err or rustc_err or me_err or lean_err


def _secondary_mismatch_sig(
    primary: tuple[str, Any], secondary: dict[str, Any]
) -> tuple[Any, ...] | None:
    sterm = _to_terminal_outcome(secondary)
    if sterm is None:
        return None
    if primary[0] == "returned" and sterm[0] == "returned" and primary[1] != sterm[1]:
        return ("returned_value",)
    ub_bucket = (
        _classify_ub_bucket(secondary.get("detail", ""))
        if sterm[0] == "undefined_behavior"
        else None
    )
    return ("outcome_kind", sterm[0], secondary["kind"] == "init_unsupported", ub_bucket)


def _is_admitted_authority_ub(
    obj: dict[str, Any], *, category: str | None = None
) -> bool:
    eff_cat = obj.get("category") if category is None else category
    miri = obj.get("miri")
    return (
        eff_cat in ("safe_admitted", "boundary_edge_case")
        and isinstance(miri, dict)
        and miri.get("kind") == "undefined_behavior"
    )


def _is_missed_targeted_ub_probe(
    obj: dict[str, Any], *, category: str | None = None
) -> bool:
    eff_cat = obj.get("category") if category is None else category
    miri = obj.get("miri")
    ev = obj.get("evaluation")
    return eff_cat == "targeted_ub_probe" and (
        not isinstance(miri, dict)
        or miri.get("kind") != "undefined_behavior"
        or not isinstance(ev, dict)
        or ev.get("agreement") != "bi_fault_equiv_agreement"
    )


def _fuzz_failure_signature(
    obj: dict[str, Any], *, category: str | None = None
) -> tuple[Any, ...] | None:
    ev = obj.get("evaluation")
    if not isinstance(ev, dict):
        return None
    agreement = ev.get("agreement")
    is_spurious = bool(ev.get("is_spurious_lean_ub", False))
    is_admitted_ub = _is_admitted_authority_ub(obj, category=category)
    is_missed_ub = _is_missed_targeted_ub_probe(obj, category=category)
    if (
        agreement not in ("unsound_accept_critical", "authority_disagreement")
        and not is_spurious
        and not is_admitted_ub
        and not is_missed_ub
    ):
        return None
    if _fuzz_obj_has_tool_error(obj):
        return None
    miri_term = _to_terminal_outcome(obj["miri"])
    if miri_term is None:
        return None
    miri_ub = (
        _classify_ub_bucket(obj["miri"].get("detail", ""))
        if miri_term[0] == "undefined_behavior"
        else None
    )
    cap_rej = obj.get("capture_rejected")
    lean_init_unsup = cap_rej is None and obj["lean"]["kind"] == "init_unsupported"
    if cap_rej is not None:
        lean_term = None
        lean_kind = None
        lean_ub = None
    else:
        lean_term = _to_terminal_outcome(obj["lean"])
        if lean_term is None:
            return None
        lean_kind = lean_term[0]
        lean_ub = (
            _classify_ub_bucket(obj["lean"].get("detail", ""))
            if lean_kind == "undefined_behavior"
            else None
        )
    rustc_st = (ev.get("rustc_status") or {}).get("status")
    rustc_mis = None
    if rustc_st == "disagreement" and isinstance(obj.get("rustc"), dict):
        rustc_mis = _secondary_mismatch_sig(miri_term, obj["rustc"])
    mir_eval_mis = None
    if (
        lean_term is not None
        and isinstance(obj.get("mir_eval"), dict)
        and agreement == "authority_disagreement"
        and not _outcomes_agree_mir_json(obj["lean"], obj["mir_eval"])
    ):
        mir_eval_mis = _secondary_mismatch_sig(lean_term, obj["mir_eval"])
    return (
        agreement,
        miri_term[0],
        miri_ub,
        lean_kind,
        lean_ub,
        lean_init_unsup,
        rustc_mis,
        mir_eval_mis,
        is_spurious,
        is_admitted_ub,
        is_missed_ub,
    )


def _validate_optional_fuzz_capture_body(
    obj: dict[str, Any],
    *,
    label: str,
    fn_name: str,
    expected_param_tys: list[tuple[str, ...]],
    expected_ret_ty: tuple[str, ...],
) -> dict[str, Any] | None:
    raw_cb = obj.get("capture_body")
    if obj.get("capture_rejected") is not None:
        if raw_cb is not None:
            raise ValueError(
                f"{label} capture-rejected case must not carry `capture_body`"
            )
        return None
    if obj["lean"]["kind"] == "tool_error" and raw_cb is None:
        return None
    return _validate_fuzz_capture_body(
        raw_cb,
        label=label,
        fn_name=fn_name,
        expected_param_tys=expected_param_tys,
        expected_ret_ty=expected_ret_ty,
    )


def _validate_fuzz_shrink_trace(
    case: dict[str, Any],
    *,
    idx: int,
    expected_ret_ty: tuple[str, ...],
    has_rustc_leg: bool,
    has_mir_eval_leg: bool,
) -> None:
    case_id = case["case_id"]
    fn_name = case["fn_name"]
    st = case.get("shrink_trace")
    sv = case.get("shrink_verification")
    ev = case["evaluation"]
    is_shrinkable = (
        ev.get("agreement") in ("unsound_accept_critical", "authority_disagreement")
        or bool(ev.get("is_spurious_lean_ub", False))
        or _is_admitted_authority_ub(case)
        or _is_missed_targeted_ub_probe(case)
    )
    if not is_shrinkable:
        if st is not None or sv is not None:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) cannot carry `shrink_trace` or "
                "`shrink_verification` on a non-shrinkable case"
            )
        return
    if st is None:
        if sv is not None:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) includes `shrink_verification` "
                "without `shrink_trace`"
            )
        return
    if not isinstance(st, dict) or set(st.keys()) != _SHRINK_TRACE_KEYS:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_trace` must have exact keys "
            f"{sorted(_SHRINK_TRACE_KEYS)}"
        )
    orig_nodes = st["original_nodes"]
    shrunk_nodes = st["shrunk_nodes"]
    steps_ev = st["steps_evaluated"]
    oracle_runs = st["oracle_runs"]
    cache_hits = st["cache_hits"]
    converged = st["converged_1_minimal"]
    min_src = st["minimized_source"]
    min_args = st["minimized_args"]
    for name, val in (
        ("original_nodes", orig_nodes),
        ("shrunk_nodes", shrunk_nodes),
        ("steps_evaluated", steps_ev),
        ("oracle_runs", oracle_runs),
        ("cache_hits", cache_hits),
    ):
        if not _is_nonneg_int(val):
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) `shrink_trace.{name}` must be non-negative int"
            )
    if int(orig_nodes) < 1 or not (1 <= int(shrunk_nodes) <= int(orig_nodes)):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) invalid `shrink_trace` node bounds "
            f"({shrunk_nodes} vs {orig_nodes})"
        )
    if int(steps_ev) != int(oracle_runs) + int(cache_hits):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_trace.steps_evaluated` "
            f"{steps_ev} != oracle_runs + cache_hits ({oracle_runs} + {cache_hits})"
        )
    if not isinstance(converged, bool):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) non-boolean `shrink_trace.converged_1_minimal`"
        )
    if not isinstance(min_src, str) or f"fn {fn_name}(" not in min_src:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_trace.minimized_source` "
            f"missing function `{fn_name}`"
        )
    if not isinstance(min_args, list):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_trace.minimized_args` must be list"
        )
    for a_idx, arg in enumerate(min_args):
        _validate_mir_value(
            arg, f"fuzz case [{idx}].shrink_trace.minimized_args[{a_idx}]", allow_enum=True
        )
    min_src_sha = hashlib.sha256(min_src.encode("utf-8")).hexdigest()
    if sv is None:
        if (
            converged
            or int(shrunk_nodes) != int(orig_nodes)
            or min_src_sha != case["program_sha256"]
            or min_args != case["args"]
        ):
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) missing `shrink_verification` for "
                "converged or modified `shrink_trace`"
            )
        return
    if converged and int(oracle_runs) < 1:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_trace` claims convergence "
            "with zero `oracle_runs`"
        )
    if not isinstance(sv, dict) or not _SHRINK_VERIFICATION_KEYS.issuperset(sv.keys()):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) invalid `shrink_verification` keys"
        )
    for req_k in ("fn_name", "args", "program_sha256", "fuel", "miri", "lean", "evaluation"):
        if req_k not in sv:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) `shrink_verification` missing `{req_k}`"
            )
    if sv["fn_name"] != fn_name:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.fn_name` mismatch"
        )
    sv_fuel = sv["fuel"]
    if (
        isinstance(sv_fuel, bool)
        or not isinstance(sv_fuel, int)
        or sv_fuel < 1
        or sv_fuel != case["fuel"]
    ):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.fuel` {sv_fuel!r} != {case['fuel']!r}"
        )
    sv_args = sv["args"]
    if not isinstance(sv_args, list) or len(sv_args) > len(case["args"]):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.args` mismatch"
        )
    for a_idx, arg in enumerate(sv_args):
        _validate_mir_value(
            arg, f"fuzz case [{idx}].shrink_verification.args[{a_idx}]", allow_enum=True
        )
    if sv_args != min_args:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.args` != `minimized_args`"
        )
    if sv["program_sha256"] != min_src_sha:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.program_sha256` != "
            "`sha256(minimized_source)`"
        )
    sv_ev = sv["evaluation"]
    if not isinstance(sv_ev, dict):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification` missing `evaluation`"
        )
    exp_ag, exp_sp, exp_rs, exp_gap = _derive_fuzz_case_evaluation(
        sv,
        idx=idx,
        has_rustc_leg=has_rustc_leg,
        has_mir_eval_leg=has_mir_eval_leg,
    )
    sv_gap = sv_ev.get("disclosed_gap")
    if (sv_gap is not None and not isinstance(sv_gap, str)) or sv_gap != exp_gap:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.evaluation.disclosed_gap` "
            f"{sv_gap!r} != derived {exp_gap!r}"
        )
    if (
        sv_ev.get("agreement") != exp_ag
        or bool(sv_ev.get("is_spurious_lean_ub", False)) != exp_sp
        or (sv_ev.get("rustc_status") or {}).get("status") != exp_rs
    ):
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification.evaluation` "
            "disagrees with minimized leg outcomes"
        )
    sv_param_tys = [_mir_value_gen_ty(a) for a in sv_args]
    sv_cb = _validate_optional_fuzz_capture_body(
        sv,
        label=f"fuzz case [{idx}] ({case_id}) shrink_verification",
        fn_name=fn_name,
        expected_param_tys=sv_param_tys,
        expected_ret_ty=expected_ret_ty,
    )
    _validate_fuzz_leg_evidence(
        sv,
        label=f"fuzz case [{idx}] ({case_id}) shrink_verification",
        case_id=case_id,
        fn_name=fn_name,
        capture_body=sv_cb,
        has_rustc_leg=has_rustc_leg,
        has_mir_eval_leg=has_mir_eval_leg,
    )
    orig_sig = _fuzz_failure_signature(case)
    min_sig = _fuzz_failure_signature(sv, category=case["category"])
    if orig_sig is None or min_sig is None or min_sig != orig_sig:
        raise ValueError(
            f"fuzz case [{idx}] ({case_id}) `shrink_verification` does not preserve "
            f"original failure signature ({min_sig!r} != {orig_sig!r})"
        )


_FUZZ_TIMEOUT_REPORT_KEYS = frozenset(
    {
        "schema",
        "mir_dialect",
        "timed_out",
        "timeout_secs",
        "error",
        "gate_error",
    }
)


def _reject_diff_timeout(diff_report: dict[str, Any]) -> None:
    """Reject any `timed_out` key on Stage-1 `diff_report` payloads."""
    if "timed_out" in diff_report:
        raise ValueError(
            "diff_report must not contain untrusted 'timed_out' field"
        )


def _is_synthesized_fuzz_timeout(fuzz_report: dict[str, Any] | None) -> bool:
    """Return True only for strict synthesized Stage-2 timeout payloads."""
    if fuzz_report is None or "timed_out" not in fuzz_report:
        return False
    raw_timed_out = fuzz_report["timed_out"]
    if type(raw_timed_out) is not bool or not raw_timed_out:
        raise ValueError(
            f"fuzz_report invalid 'timed_out' value {raw_timed_out!r}; "
            "must be strictly True only on synthesized timeouts"
        )
    if fuzz_report.get("schema") != FUZZ_SCHEMA:
        raise ValueError(
            f"timed-out fuzz_report has unexpected schema {fuzz_report.get('schema')!r}"
        )
    extra_keys = set(fuzz_report.keys()) - _FUZZ_TIMEOUT_REPORT_KEYS
    if extra_keys:
        raise ValueError(
            f"timed-out fuzz_report contains unexpected keys: {sorted(extra_keys)}"
        )
    return True


def validate_fuzz_report(
    fuzz_report: dict[str, Any],
    *,
    expected_seed: int | None = None,
    expected_cases: int | None = None,
    expected_max_stmts: int | None = None,
    expected_ub_ratio: float | None = None,
    expected_fuel: int | None = None,
    expected_min_admission_rate: float | None = None,
    expect_mir_eval: bool = False,
) -> dict[str, Any]:
    """Cross-check fuzz `metrics` and per-case classifications against legs."""
    if "timed_out" in fuzz_report:
        raise ValueError(
            "fuzz_report must not contain 'timed_out' when validating fuzz metrics"
        )
    if fuzz_report.get("schema") != FUZZ_SCHEMA:
        raise ValueError(
            f"unexpected fuzz report schema {fuzz_report.get('schema')!r}; "
            f"expected {FUZZ_SCHEMA!r}"
        )
    if fuzz_report.get("mir_dialect") != "profile_v1":
        raise ValueError(
            f"unexpected fuzz report mir_dialect "
            f"{fuzz_report.get('mir_dialect')!r}; expected 'profile_v1'"
        )
    report_min_rate = _validate_bounded_rate(
        fuzz_report.get("min_admission_rate"),
        "fuzz_report.min_admission_rate",
    )
    if expected_min_admission_rate is not None:
        req_min_rate = _validate_bounded_rate(
            expected_min_admission_rate, "fuzz_min_admission_rate"
        )
        if abs(report_min_rate - req_min_rate) > 1e-12:
            raise ValueError(
                f"fuzz_report `min_admission_rate` {report_min_rate} != "
                f"requested {req_min_rate}"
            )
    if expected_ub_ratio is not None:
        _validate_bounded_rate(
            expected_ub_ratio, "fuzz_ub_ratio", upper=0.85
        )
    raw_ub_ratio = fuzz_report.get(
        "ub_ratio", 0.20 if expected_ub_ratio is None else expected_ub_ratio
    )
    report_ub_ratio = _validate_bounded_rate(
        raw_ub_ratio, "fuzz_report.ub_ratio", upper=0.85
    )
    if (
        expected_ub_ratio is not None
        and abs(report_ub_ratio - expected_ub_ratio) > 1e-12
    ):
        raise ValueError(
            f"fuzz_report `ub_ratio` {report_ub_ratio} != requested "
            f"{expected_ub_ratio}"
        )
    fmetrics = fuzz_report.get("metrics")
    if not isinstance(fmetrics, dict):
        raise ValueError("fuzz_report missing `metrics` object")
    fmissing = REQUIRED_FUZZ_METRICS_KEYS - set(fmetrics.keys())
    if fmissing:
        raise ValueError(
            f"missing metrics keys in fuzz report: {sorted(fmissing)}"
        )
    raw_legs = fuzz_report.get("legs", [])
    if not isinstance(raw_legs, list) or any(
        not isinstance(lg, str) for lg in raw_legs
    ):
        raise ValueError("fuzz_report `legs` must be a list of strings")
    has_rustc_leg = "rustc_compiled" in raw_legs
    has_mir_eval_leg = "anneal_mir_eval_captured" in raw_legs
    if expect_mir_eval and not has_mir_eval_leg:
        raise ValueError(
            "fuzz_report missing requested `anneal_mir_eval_captured` leg"
        )

    report_seed = fuzz_report.get("seed")
    if (
        isinstance(report_seed, bool)
        or not isinstance(report_seed, int)
        or not (0 <= report_seed <= _MASK64)
    ):
        raise ValueError(f"fuzz_report invalid `seed` {report_seed!r}")
    if expected_seed is not None and report_seed != expected_seed:
        raise ValueError(
            f"fuzz_report `seed` {report_seed} != requested {expected_seed}"
        )
    raw_max_stmts = fuzz_report.get("max_stmts", 6)
    if (
        isinstance(raw_max_stmts, bool)
        or not isinstance(raw_max_stmts, int)
        or not (1 <= raw_max_stmts <= 20)
    ):
        raise ValueError(f"fuzz_report invalid `max_stmts` {raw_max_stmts!r}")
    if expected_max_stmts is not None and raw_max_stmts != expected_max_stmts:
        raise ValueError(
            f"fuzz_report `max_stmts` {raw_max_stmts} != requested "
            f"{expected_max_stmts}"
        )
    raw_fuel = fuzz_report.get("fuel")
    if isinstance(raw_fuel, bool) or not isinstance(raw_fuel, int) or raw_fuel < 1:
        raise ValueError(f"fuzz_report invalid or missing `fuel` {raw_fuel!r}")
    if expected_fuel is not None and raw_fuel != expected_fuel:
        raise ValueError(
            f"fuzz_report `fuel` {raw_fuel} != requested {expected_fuel}"
        )

    cases = fuzz_report.get("cases")
    if not isinstance(cases, list) or not cases or any(
        not isinstance(c, dict) for c in cases
    ):
        raise ValueError("fuzz_report must contain a non-empty `cases` object list")
    if expected_cases is not None and len(cases) != expected_cases:
        raise ValueError(
            f"fuzz_report case count {len(cases)} != requested {expected_cases}"
        )

    recomputed_int: dict[str, int] = {
        "total_cases": len(cases),
        "safe_admitted_cases": 0,
        "boundary_edge_cases": 0,
        "targeted_ub_probes": 0,
        "scope_control_cases": 0,
        "admission_eligible_cases": 0,
        "admitted_cases": 0,
        "bi_fault_equiv_count": 0,
        "ub_probes_agreed_count": 0,
        "conservative_over_approx_count": 0,
        "spurious_lean_ub_count": 0,
        "admitted_authority_ub_count": 0,
        "unsound_accept_count": 0,
        "authority_disagreement_count": 0,
        "move_reinit_exercised_count": 0,
        "rustc_agreed_count": 0,
        "rustc_ignored_ub_count": 0,
        "rustc_disagreement_count": 0,
    }
    valid_categories = {
        "safe_admitted",
        "boundary_edge_case",
        "targeted_ub_probe",
        "scope_control",
    }
    valid_agreements = {
        "bi_fault_equiv_agreement",
        "conservative_over_approx_forward_sim_only",
        "unsound_accept_critical",
        "authority_disagreement",
    }

    seen_case_ids: set[str] = set()
    seen_fn_names: set[str] = set()
    seen_case_indices: set[int] = set()
    seen_program_sha256s: set[str] = set()
    seen_capture_body_sha256s: set[str] = set()
    verified_witnesses: list[dict[str, Any]] = []
    recomputed_gaps: dict[str, int] = {}
    capture_rejected_count = 0
    mir_eval_verified_count = 0
    for idx, c in enumerate(cases):
        case_id = c.get("case_id")
        if not isinstance(case_id, str) or not case_id:
            raise ValueError(f"fuzz case [{idx}] missing string `case_id`")
        if case_id in seen_case_ids:
            raise ValueError(f"duplicate fuzz `case_id` {case_id!r} at [{idx}]")
        seen_case_ids.add(case_id)

        fn_name = c.get("fn_name")
        if not isinstance(fn_name, str) or not fn_name:
            raise ValueError(f"fuzz case [{idx}] missing string `fn_name`")
        if fn_name in seen_fn_names:
            raise ValueError(f"duplicate fuzz `fn_name` {fn_name!r} at [{idx}]")
        seen_fn_names.add(fn_name)

        case_index = c.get("case_index")
        if (
            isinstance(case_index, bool)
            or not isinstance(case_index, int)
            or case_index in seen_case_indices
            or case_index != idx
        ):
            raise ValueError(
                f"fuzz case [{idx}] invalid or duplicate `case_index` {case_index!r}"
            )
        seen_case_indices.add(case_index)

        master_seed = c.get("master_seed")
        if (
            isinstance(master_seed, bool)
            or not isinstance(master_seed, int)
            or master_seed != report_seed
        ):
            raise ValueError(
                f"fuzz case [{idx}] `master_seed` {master_seed!r} != {report_seed!r}"
            )
        expected_case_id = f"fuzz_s{report_seed}_c{idx:04d}"
        expected_fn_name = f"fuzz_case_{idx:04d}"
        if case_id != expected_case_id or fn_name != expected_fn_name:
            raise ValueError(
                f"fuzz case [{idx}] identity ({case_id!r}, {fn_name!r}) != "
                f"({expected_case_id!r}, {expected_fn_name!r})"
            )
        cat = c.get("category")
        if cat not in valid_categories:
            raise ValueError(f"fuzz case [{idx}] has invalid category {cat!r}")
        (
            expected_cat,
            expected_args,
            expected_program_sha256,
            expected_param_tys,
            expected_ret_ty,
            expected_case_fuel,
        ) = _expected_fuzz_case_details(
            report_seed,
            idx,
            raw_max_stmts,
            report_ub_ratio,
            default_fuel=raw_fuel,
        )
        if cat != expected_cat:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) category {cat!r} != "
                f"deterministic campaign category {expected_cat!r}"
            )
        raw_case_fuel = c.get("fuel")
        if (
            isinstance(raw_case_fuel, bool)
            or not isinstance(raw_case_fuel, int)
            or raw_case_fuel < 1
        ):
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) invalid or missing `fuel` {raw_case_fuel!r}"
            )
        if raw_case_fuel != expected_case_fuel:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) `fuel` {raw_case_fuel} != "
                f"expected effective fuel {expected_case_fuel}"
            )
        raw_args = c.get("args")
        if not isinstance(raw_args, list):
            raise ValueError(f"fuzz case [{idx}] ({case_id}) missing `args` list")
        for a_idx, arg in enumerate(raw_args):
            _validate_mir_value(
                arg, f"fuzz case [{idx}].args[{a_idx}]", allow_enum=True
            )
        if raw_args != expected_args:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) `args` do not match "
                "deterministic campaign inputs"
            )
        prog_sha = c.get("program_sha256")
        if not isinstance(prog_sha, str) or not _is_valid_sha256_hex(prog_sha):
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) missing or invalid `program_sha256`"
            )
        if prog_sha in seen_program_sha256s:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) duplicate `program_sha256` {prog_sha!r}"
            )
        if prog_sha != expected_program_sha256:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) `program_sha256` {prog_sha!r} != "
                f"deterministic campaign digest {expected_program_sha256!r}"
            )
        seen_program_sha256s.add(prog_sha)
        raw_source = c.get("source")
        if raw_source is not None:
            if not isinstance(raw_source, str):
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) non-string `source`"
                )
            src_sha = hashlib.sha256(raw_source.encode("utf-8")).hexdigest()
            if src_sha != expected_program_sha256:
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) `source` digest mismatch"
                )
        ev = c.get("evaluation")
        if not isinstance(ev, dict):
            raise ValueError(f"fuzz case [{idx}] missing `evaluation` object")
        agreement = ev.get("agreement")
        if agreement not in valid_agreements:
            raise ValueError(
                f"fuzz case [{idx}] has invalid agreement {agreement!r}"
            )
        miri = c["miri"] if isinstance(c.get("miri"), dict) else None
        if miri is None:
            raise ValueError(f"fuzz case [{idx}] missing `miri` outcome")
        lean = c.get("lean")
        if not isinstance(lean, dict):
            raise ValueError(f"fuzz case [{idx}] missing `lean` outcome")
        verified_capture_body = _validate_optional_fuzz_capture_body(
            c,
            label=f"fuzz case [{idx}] ({case_id})",
            fn_name=fn_name,
            expected_param_tys=expected_param_tys,
            expected_ret_ty=expected_ret_ty,
        )
        if verified_capture_body is not None:
            cap_body_sha = verified_capture_body["capture_body_sha256"]
            if cap_body_sha in seen_capture_body_sha256s:
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) duplicate "
                    f"`capture_body_sha256` {cap_body_sha!r}"
                )
            seen_capture_body_sha256s.add(cap_body_sha)

        exp_agreement, exp_spurious, exp_rustc, exp_gap = _derive_fuzz_case_evaluation(
            c,
            idx=idx,
            has_rustc_leg=has_rustc_leg,
            has_mir_eval_leg=has_mir_eval_leg,
        )
        if agreement != exp_agreement:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) reported agreement "
                f"{agreement!r}, but leg outcomes derive {exp_agreement!r}"
            )
        raw_gap = ev.get("disclosed_gap")
        if (raw_gap is not None and not isinstance(raw_gap, str)) or raw_gap != exp_gap:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) reported disclosed_gap "
                f"{raw_gap!r}, derived {exp_gap!r}"
            )
        if exp_gap is not None:
            recomputed_gaps[exp_gap] = recomputed_gaps.get(exp_gap, 0) + 1

        is_spurious = ev.get("is_spurious_lean_ub", False)
        if not isinstance(is_spurious, bool):
            raise ValueError(
                f"fuzz case [{idx}] non-boolean `is_spurious_lean_ub`"
            )
        if is_spurious != exp_spurious:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) reported "
                f"is_spurious_lean_ub={is_spurious!r}, derived {exp_spurious!r}"
            )

        raw_rustc_st = ev.get("rustc_status")
        if raw_rustc_st is not None:
            if (
                not isinstance(raw_rustc_st, dict)
                or raw_rustc_st.get("status") != exp_rustc
            ):
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) reported rustc_status "
                    f"{raw_rustc_st!r}, derived {exp_rustc!r}"
                )
        elif has_rustc_leg:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) missing `rustc_status`"
            )

        _validate_fuzz_leg_evidence(
            c,
            label=f"fuzz case [{idx}] ({case_id})",
            case_id=case_id,
            fn_name=fn_name,
            capture_body=verified_capture_body,
            has_rustc_leg=has_rustc_leg,
            has_mir_eval_leg=has_mir_eval_leg,
        )
        _validate_fuzz_shrink_trace(
            c,
            idx=idx,
            expected_ret_ty=expected_ret_ty,
            has_rustc_leg=has_rustc_leg,
            has_mir_eval_leg=has_mir_eval_leg,
        )

        if exp_rustc == "agreed":
            recomputed_int["rustc_agreed_count"] += 1
        elif exp_rustc == "ignored_due_to_miri_ub":
            recomputed_int["rustc_ignored_ub_count"] += 1
        elif exp_rustc == "disagreement":
            recomputed_int["rustc_disagreement_count"] += 1

        if cat == "safe_admitted":
            recomputed_int["safe_admitted_cases"] += 1
        elif cat == "boundary_edge_case":
            recomputed_int["boundary_edge_cases"] += 1
        elif cat == "targeted_ub_probe":
            recomputed_int["targeted_ub_probes"] += 1
        else:
            recomputed_int["scope_control_cases"] += 1

        if c.get("capture_rejected") is not None:
            capture_rejected_count += 1
        elif has_mir_eval_leg and c.get("mir_eval") is not None:
            mir_eval_verified_count += 1

        raw_move_reinit = c.get("exercised_move_reinit", False)
        if not isinstance(raw_move_reinit, bool):
            raise ValueError(
                f"fuzz case [{idx}] non-boolean `exercised_move_reinit`"
            )
        if raw_move_reinit:
            if (
                exp_agreement != "bi_fault_equiv_agreement"
                or miri.get("kind") == "undefined_behavior"
                or c.get("capture_rejected") is not None
            ):
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) cannot claim "
                    "exercised_move_reinit without UB-free bi-fault agreement"
                )
            witness = _verify_move_reinit_evidence(c, idx)
            raw_mr = c["move_reinit_evidence"]
            if (
                verified_capture_body is None
                or verified_capture_body["body_id"] != witness["body_id"]
                or verified_capture_body["capture_body_sha256"]
                != witness["capture_body_sha256"]
                or verified_capture_body["fn_identity"] != witness["fn_identity"]
                or verified_capture_body["blocks"] != raw_mr["blocks"]
                or verified_capture_body["local_tys"] != raw_mr["local_tys"]
                or (
                    c.get("leg_evidence", {}).get("lean_probe_line")
                    != raw_mr["lean_probe_line"]
                )
            ):
                raise ValueError(
                    f"fuzz case [{idx}] ({case_id}) move/reinit witness does not "
                    "match case capture binding"
                )
            verified_witnesses.append(witness)
            recomputed_int["move_reinit_exercised_count"] += 1
        elif c.get("move_reinit_evidence") is not None:
            raise ValueError(
                f"fuzz case [{idx}] ({case_id}) includes `move_reinit_evidence` "
                "with `exercised_move_reinit=False`"
            )
        if is_spurious:
            recomputed_int["spurious_lean_ub_count"] += 1

        if cat in ("safe_admitted", "boundary_edge_case"):
            recomputed_int["admission_eligible_cases"] += 1
            if miri.get("kind") == "undefined_behavior":
                recomputed_int["admitted_authority_ub_count"] += 1
            elif (
                c.get("capture_rejected") is None
                and miri.get("kind") == "returned"
                and agreement == "bi_fault_equiv_agreement"
            ):
                recomputed_int["admitted_cases"] += 1

        if agreement == "bi_fault_equiv_agreement":
            recomputed_int["bi_fault_equiv_count"] += 1
            if (
                cat == "targeted_ub_probe"
                and miri.get("kind") == "undefined_behavior"
            ):
                recomputed_int["ub_probes_agreed_count"] += 1
        elif agreement == "conservative_over_approx_forward_sim_only":
            if not is_spurious:
                recomputed_int["conservative_over_approx_count"] += 1
        elif agreement == "unsound_accept_critical":
            recomputed_int["unsound_accept_count"] += 1
        elif agreement == "authority_disagreement":
            recomputed_int["authority_disagreement_count"] += 1

    for key, expected_val in recomputed_int.items():
        if key not in fmetrics and key in (
            "safe_admitted_cases",
            "boundary_edge_cases",
            "scope_control_cases",
            "rustc_agreed_count",
            "rustc_ignored_ub_count",
            "rustc_disagreement_count",
        ):
            continue
        raw_val = fmetrics[key]
        if isinstance(raw_val, bool) or not isinstance(raw_val, int):
            raise ValueError(
                f"inconsistent fuzz metric `{key}`: expected int, got {raw_val!r}"
            )
        if raw_val != expected_val:
            raise ValueError(
                f"inconsistent fuzz metric `{key}`: reported {raw_val}, "
                f"recomputed {expected_val} from {len(cases)} serialized cases"
            )

    elig = recomputed_int["admission_eligible_cases"]
    expected_rate = (
        (recomputed_int["admitted_cases"] / elig) if elig > 0 else 0.0
    )
    actual_rate = _validate_bounded_rate(
        fmetrics["admission_rate"], "fuzz_report.metrics.admission_rate"
    )
    if abs(actual_rate - expected_rate) > 1e-6:
        raise ValueError(
            f"inconsistent fuzz metric `admission_rate`: reported "
            f"{actual_rate}, recomputed {expected_rate}"
        )

    raw_gaps = fmetrics.get("disclosed_gaps")
    if not isinstance(raw_gaps, dict):
        raise ValueError(
            f"inconsistent fuzz metric `disclosed_gaps`: expected dict, got {raw_gaps!r}"
        )
    for gkey, gval in raw_gaps.items():
        if (
            not isinstance(gkey, str)
            or not gkey
            or isinstance(gval, bool)
            or not isinstance(gval, int)
            or gval <= 0
        ):
            raise ValueError(
                f"invalid `disclosed_gaps` entry ({gkey!r}: {gval!r})"
            )
    if raw_gaps != recomputed_gaps:
        raise ValueError(
            f"inconsistent fuzz metric `disclosed_gaps`: reported {raw_gaps}, "
            f"recomputed {recomputed_gaps} from {len(cases)} serialized cases"
        )

    return {
        **fmetrics,
        **recomputed_int,
        "disclosed_gaps": recomputed_gaps,
        "ub_ratio": report_ub_ratio,
        "fuel": raw_fuel,
        "admission_rate": expected_rate,
        "case_records_verified_count": len(cases),
        "capture_rejected_count": capture_rejected_count,
        "mir_eval_verified_count": mir_eval_verified_count,
        "move_reinit_evidence_verified_count": recomputed_int[
            "move_reinit_exercised_count"
        ],
        "move_reinit_witnesses": verified_witnesses,
    }


def _validate_combined_mir_dialect(
    diff_report: dict[str, Any],
    fuzz_report: dict[str, Any] | None = None,
) -> str:
    diff_dialect = diff_report.get("mir_dialect")
    if diff_dialect != "profile_v1":
        raise ValueError(
            f"unexpected differential report mir_dialect {diff_dialect!r}; "
            "expected 'profile_v1'"
        )
    if fuzz_report is not None:
        if not isinstance(fuzz_report, dict):
            raise ValueError("fuzz_report must be a JSON object")
        fuzz_dialect = fuzz_report.get("mir_dialect")
        if fuzz_dialect != diff_dialect:
            raise ValueError(
                f"mir_dialect mismatch across Stage-1 ({diff_dialect!r}) and "
                f"Stage-2 ({fuzz_dialect!r}); expected 'profile_v1'"
            )
    return diff_dialect


def build_perf_metrics_snippet(
    diff_report: dict[str, Any],
    fuzz_report: dict[str, Any] | None = None,
) -> dict[str, float | int]:
    """Project differential and fuzz reports into perf-record metrics."""
    _validate_combined_mir_dialect(diff_report, fuzz_report)
    metrics = diff_report["metrics"]
    missing = REQUIRED_METRICS_KEYS - set(metrics.keys())
    if missing:
        raise ValueError(f"missing metrics keys in differential report: {sorted(missing)}")

    out: dict[str, float | int] = {
        "differential_oracle.litmus.compared_count": int(metrics["compared_count"]),
        "differential_oracle.litmus.pass_agreed_count": int(
            metrics["pass_agreed_count"]
        ),
        "differential_oracle.litmus.ub_agreed_count": int(metrics["ub_agreed_count"]),
        "differential_oracle.litmus.conservative_unsupported_count": int(
            metrics["conservative_unsupported_count"]
        ),
        "differential_oracle.litmus.kernel_checked_pass_count": int(
            metrics["kernel_checked_pass_count"]
        ),
        "differential_oracle.litmus.kernel_checked_ub_count": int(
            metrics["kernel_checked_ub_count"]
        ),
        "differential_oracle.litmus.unsound_missed_fault_count": int(
            metrics["unsound_missed_fault_count"]
        ),
        "differential_oracle.litmus.value_mismatch_count": int(
            metrics["value_mismatch_count"]
        ),
        "differential_oracle.litmus.unexpected_conservative_count": int(
            metrics["unexpected_conservative_count"]
        ),
        "differential_oracle.litmus.leg_divergence_count": int(
            metrics["leg_divergence_count"]
        ),
        "differential_oracle.red_flags.passed_count": int(
            diff_report.get("red_flags_passed", 0)
        ),
    }
    _reject_diff_timeout(diff_report)
    mutants = diff_report.get("mutant_check")
    if isinstance(mutants, dict) and "killed_pct" in mutants:
        out["differential_oracle.mutants.killed_pct"] = float(mutants["killed_pct"])

    fuzz_timed_out = _is_synthesized_fuzz_timeout(fuzz_report)
    if isinstance(fuzz_report, dict) and not fuzz_timed_out:
        fmetrics = validate_fuzz_report(fuzz_report)
        out["differential_oracle.fuzz.total_cases_count"] = int(fmetrics["total_cases"])
        out["differential_oracle.fuzz.bi_fault_equiv_count"] = int(
            fmetrics["bi_fault_equiv_count"]
        )
        out["differential_oracle.fuzz.ub_probes_agreed_count"] = int(
            fmetrics["ub_probes_agreed_count"]
        )
        out["differential_oracle.fuzz.conservative_over_approx_count"] = int(
            fmetrics["conservative_over_approx_count"]
        )
        out["differential_oracle.fuzz.spurious_lean_ub_count"] = int(
            fmetrics["spurious_lean_ub_count"]
        )
        out["differential_oracle.fuzz.admitted_authority_ub_count"] = int(
            fmetrics["admitted_authority_ub_count"]
        )
        out["differential_oracle.fuzz.unsound_accept_count"] = int(
            fmetrics["unsound_accept_count"]
        )
        out["differential_oracle.fuzz.authority_disagreement_count"] = int(
            fmetrics["authority_disagreement_count"]
        )
        out["differential_oracle.fuzz.admitted_cases_count"] = int(
            fmetrics["admitted_cases"]
        )
        out["differential_oracle.fuzz.move_reinit_exercised_count"] = int(
            fmetrics["move_reinit_exercised_count"]
        )
    return out


def _load_perf_tracking():
    raw_script = Path(__file__)
    ensure_not_symlink(raw_script, "script")
    raw_ci_dir = raw_script.parent
    ensure_not_symlink(raw_ci_dir, "ci directory")
    ci_dir = raw_ci_dir.resolve(strict=True)
    perf_path = ci_dir / "perf_tracking.py"
    ensure_not_symlink(perf_path, "perf_tracking.py")
    if str(ci_dir) not in sys.path:
        sys.path.insert(0, str(ci_dir))
    import perf_tracking

    return perf_tracking


def build_perf_record_from_snippet(
    perf_snippet: dict[str, float | int],
    *,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
) -> dict[str, Any]:
    """Assemble and validate a full `anneal-perf-record/v1` record."""
    if not isinstance(perf_snippet, dict) or not perf_snippet:
        raise ValueError("perf_snippet must be a non-empty dict")
    pt = _load_perf_tracking()
    for metric_id, value in perf_snippet.items():
        if not pt.METRIC_ID_RE.match(metric_id):
            raise ValueError(f"invalid metric ID in snippet: {metric_id!r}")
        desc = pt.describe_metric(metric_id)
        if desc["category"] != "differential_oracle":
            raise ValueError(
                f"unexpected category {desc['category']!r} for {metric_id!r}"
            )
        if (
            isinstance(value, bool)
            or not isinstance(value, (int, float))
            or not math.isfinite(value)
            or value < 0
        ):
            raise ValueError(f"invalid numeric metric value {metric_id}={value!r}")

    if not pt.SHA40_RE.match(commit_sha) or not branch:
        raise ValueError(
            f"cannot build anneal-perf-record/v1 without valid 40-hex commit_sha and non-empty branch: sha={commit_sha!r}, branch={branch!r}"
        )
    ts_iso = datetime.fromtimestamp(max(0, commit_unix_ts), tz=timezone.utc).strftime(
        "%Y-%m-%dT%H:%M:%SZ"
    )
    os_name = str(environment_profile.get("os") or platform.system().lower() or "linux")
    arch = str(environment_profile.get("arch") or platform.machine() or "x86_64")
    has_fuzz_metrics = any(
        metric_id.startswith("differential_oracle.fuzz.")
        for metric_id in perf_snippet
    )
    record = {
        "schema": pt.RECORD_SCHEMA,
        "commit": {
            "sha": commit_sha,
            "short_sha": commit_sha[:12],
            "timestamp": ts_iso,
            "unix_ts": max(0, int(commit_unix_ts)),
            "subject": (
                "Stage-1 and Stage-2 differential oracle telemetry"
                if has_fuzz_metrics
                else "Stage-1 differential oracle telemetry"
            ),
            "branch": branch,
        },
        "environment": {
            "profile": f"{os_name}-{arch}",
            "os": os_name,
            "arch": arch,
            "cpu_model": "ci-runner",
            "vcpu_count": max(1, os.cpu_count() or 1),
            "ram_total_kib": 0,
            "lean_version": str(
                environment_profile.get("lean_version") or "unknown"
            ),
            "rustc_version": str(
                environment_profile.get("rustc_version") or "unknown"
            ),
        },
        "sampling": {
            "verify_repeats": 1,
            "aggregation": "single",
        },
        "metrics": perf_snippet,
    }
    return pt.validate_record(record)


def validate_perf_metrics_snippet(
    perf_snippet: dict[str, float | int],
    *,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
) -> None:
    """Validate snippet metric IDs, categories, and `perf-record` schema."""
    build_perf_record_from_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=environment_profile,
    )


def build_semantic_detail_report(
    *,
    diff_report: dict[str, Any],
    mir_eval_status: dict[str, Any],
    repo: str,
    branch: str,
    commit_sha: str,
    commit_unix_ts: int,
    environment_profile: dict[str, Any],
    fuzz_report: dict[str, Any] | None = None,
    fuzz_ub_ratio: float | None = None,
    fuzz_expected_seed: int | None = None,
    fuzz_expected_cases: int | None = None,
    fuzz_expected_max_stmts: int | None = None,
    fuzz_expected_fuel: int | None = None,
    fuzz_min_admission_rate: float | None = None,
    expect_mir_eval: bool = False,
) -> dict[str, Any]:
    """Assemble the canonical `anneal-semantic-detail/v1` JSON document."""
    _reject_diff_timeout(diff_report)
    fuzz_timed_out = _is_synthesized_fuzz_timeout(fuzz_report)
    combined_dialect = _validate_combined_mir_dialect(diff_report, fuzz_report)
    if expect_mir_eval:
        diff_legs = diff_report.get("legs", [])
        if (
            not isinstance(diff_legs, list)
            or "anneal_mir_eval_captured" not in diff_legs
        ):
            raise ValueError(
                "diff_report missing requested `anneal_mir_eval_captured` leg"
            )
        for idx, c in enumerate(diff_report.get("cases", [])):
            if not isinstance(c, dict) or c.get("mir_eval") is None:
                raise ValueError(
                    f"diff_report case [{idx}] missing requested `mir_eval` outcome"
                )
            _validate_observed_outcome(
                c.get("mir_eval"), f"diff_case[{idx}].mir_eval"
            )

    failing_cases = [
        {
            "id": c["id"],
            "category": c["category"],
            "expected": c["expected"],
            "verdict": c["verdict"],
        }
        for c in diff_report.get("cases", [])
        if not _verdict_is_ok(c.get("verdict"))
    ]
    perf_snippet = build_perf_metrics_snippet(diff_report, fuzz_report=fuzz_report)
    validate_perf_metrics_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=environment_profile,
    )
    capture_source = str(diff_report.get("capture_bin_source") or "unknown")
    capture_sha256 = str(diff_report.get("capture_bin_sha256") or "")
    prebuilt_overlay = str(diff_report.get("prebuilt_overlay") or "unknown")
    evidence_blocks: dict[str, Any] = {
        "differential_oracle": {
            **diff_report["metrics"],
            "red_flags_passed": diff_report.get("red_flags_passed", 0),
            "red_flag_error": diff_report.get("red_flag_error"),
            "legs": diff_report.get("legs", []),
            "capture_bin_source": capture_source,
            "capture_bin_sha256": capture_sha256,
            "prebuilt_overlay": prebuilt_overlay,
        },
        "mir_eval_cargo_test": mir_eval_status,
        "perf_metrics": perf_snippet,
    }
    if diff_report.get("mutant_check") is not None:
        evidence_blocks["oracle_mutants"] = diff_report["mutant_check"]

    if isinstance(fuzz_report, dict):
        if fuzz_timed_out:
            err_msg = str(
                fuzz_report.get("gate_error")
                or fuzz_report.get("error")
                or "anneal-diff fuzz timed out"
            )
            evidence_blocks["differential_fuzz"] = {
                "executed": True,
                "passed": False,
                "timed_out": True,
                "timeout_secs": fuzz_report.get("timeout_secs"),
                "error": err_msg,
                "gate_error": err_msg,
                "seed": fuzz_expected_seed,
                "max_stmts": fuzz_expected_max_stmts,
                "fuel": fuzz_expected_fuel,
                "min_admission_rate": fuzz_min_admission_rate,
                "total_cases": 0,
            }
        else:
            verified_fuzz_metrics = validate_fuzz_report(
                fuzz_report,
                expected_seed=fuzz_expected_seed,
                expected_cases=fuzz_expected_cases,
                expected_max_stmts=fuzz_expected_max_stmts,
                expected_ub_ratio=fuzz_ub_ratio,
                expected_fuel=fuzz_expected_fuel,
                expected_min_admission_rate=fuzz_min_admission_rate,
                expect_mir_eval=expect_mir_eval,
            )
            verified_min_rate = _validate_bounded_rate(
                fuzz_report.get("min_admission_rate"),
                "fuzz_report.min_admission_rate",
            )
            fuzz_failing = [
                {
                    "id": c["case_id"],
                    "fn_name": c["fn_name"],
                    "category": c["category"],
                    "args": c["args"],
                    "program_sha256": c["program_sha256"],
                    "fuel": c["fuel"],
                    "source": c.get("source"),
                    "agreement": c.get("evaluation", {}).get("agreement"),
                    "is_spurious_lean_ub": bool(
                        c.get("evaluation", {}).get("is_spurious_lean_ub", False)
                    ),
                    "detail": c.get("evaluation", {}).get("detail"),
                    "shrink_trace": c.get("shrink_trace"),
                    **(
                        {"shrink_verification": c.get("shrink_verification")}
                        if c.get("shrink_verification") is not None
                        else {}
                    ),
                }
                for c in fuzz_report.get("cases", [])
                if c.get("evaluation", {}).get("agreement")
                in ("unsound_accept_critical", "authority_disagreement")
                or c.get("evaluation", {}).get("is_spurious_lean_ub")
                or _is_admitted_authority_ub(c)
                or _is_missed_targeted_ub_probe(c)
            ]
            failing_cases.extend(fuzz_failing)
            fuzz_block: dict[str, Any] = {
                **verified_fuzz_metrics,
                "seed": fuzz_report.get("seed"),
                "max_stmts": int(fuzz_report.get("max_stmts", 6)),
                "fuel": verified_fuzz_metrics["fuel"],
                "min_admission_rate": verified_min_rate,
                "gate_error": fuzz_report.get("gate_error"),
                "legs": fuzz_report.get("legs", []),
                "capture_bin_source": str(fuzz_report.get("capture_bin_source") or "unknown"),
                "capture_bin_sha256": str(fuzz_report.get("capture_bin_sha256") or ""),
                "prebuilt_overlay": str(fuzz_report.get("prebuilt_overlay") or "unknown"),
                "failing_cases": fuzz_failing,
            }
            if fuzz_ub_ratio is not None:
                fuzz_block["ub_ratio"] = _validate_bounded_rate(
                    fuzz_ub_ratio, "fuzz_ub_ratio", upper=0.85
                )
            evidence_blocks["differential_fuzz"] = fuzz_block

    return {
        "schema": DETAIL_SCHEMA,
        "alpha_notice": ALPHA_NOTICE,
        "repo": repo,
        "branch": branch,
        "commit_sha": commit_sha,
        "commit_unix_ts": commit_unix_ts,
        "mir_dialect": combined_dialect,
        "environment_profile": environment_profile,
        "trust_tier": "candidate:mir_semantics",
        "evidence_blocks": evidence_blocks,
        "differential_runs": [
            {
                "manifest_path": diff_report.get("manifest_path", ""),
                "legs": diff_report.get("legs", []),
                "capture_bin_source": capture_source,
                "capture_bin_sha256": capture_sha256,
                "prebuilt_overlay": prebuilt_overlay,
                "metrics": diff_report["metrics"],
                "cases": diff_report.get("cases", []),
            }
        ],
        "known_bugs": failing_cases,
        "corpus_blockers": [],
    }


def _verdict_is_ok(verdict: Any) -> bool:
    if not isinstance(verdict, dict):
        return False
    return verdict.get("kind") in (
        "agree_value",
        "agree_undefined_behavior",
        "sound_conservative_abstraction",
    )


def _witness_summaries_valid(
    witnesses: Any, expected_count: int
) -> bool:
    if not isinstance(witnesses, list) or len(witnesses) != expected_count:
        return False
    seen_ids: set[str] = set()
    for w in witnesses:
        if not isinstance(w, dict):
            return False
        cid = w.get("case_id")
        if not isinstance(cid, str) or not cid or cid in seen_ids:
            return False
        seen_ids.add(cid)
        if not _is_nonneg_int(w.get("body_id")) or not isinstance(
            w.get("fn_identity"), str
        ):
            return False
        if not _is_nonneg_int(w.get("local_slot")):
            return False
        tot = w.get("total_steps")
        if not _is_nonneg_int(tot) or int(tot) <= 0:
            return False
        if not _is_valid_sha256_hex(w.get("capture_body_sha256")):
            return False
        try:
            i_st = _validate_step_coord(w.get("init_step"), "init_step")
            m_st = _validate_step_coord(w.get("move_step"), "move_step")
            r_st = _validate_step_coord(w.get("reinit_step"), "reinit_step")
            rd_st = _validate_step_coord(w.get("read_step"), "read_step")
        except ValueError:
            return False
        if not (
            i_st["step"]
            < m_st["step"]
            < r_st["step"]
            < rd_st["step"]
            < int(tot)
        ):
            return False
    return True


def report_passes(
    detail: dict[str, Any],
    *,
    require_mutants: bool = True,
    require_fuzz: bool = False,
    require_mir_eval: bool = False,
    fuzz_min_admission_rate: float | None = None,
    fuzz_ub_ratio: float | None = None,
    fuzz_require_rustc_leg: bool = True,
    fuzz_expected_cases: int | None = None,
    fuzz_expected_max_stmts: int | None = None,
    fuzz_expected_fuel: int | None = None,
) -> bool:
    """Validate cases, red flags, mutants, fuzz gates, and mir-eval."""
    runs = detail.get("differential_runs", [])
    if not isinstance(runs, list) or not runs:
        return False
    cases = runs[0].get("cases", [])
    if not isinstance(cases, list) or not cases:
        return False
    if any(not _verdict_is_ok(c.get("verdict")) for c in cases):
        return False

    blocks = detail.get("evidence_blocks", {})
    diff_ev = blocks.get("differential_oracle", {})
    if diff_ev.get("red_flag_error") is not None:
        return False
    if int(diff_ev.get("red_flags_passed", 0)) <= 0:
        return False
    if int(diff_ev.get("compared_count", 0)) != len(cases):
        return False
    if int(diff_ev.get("kernel_checked_pass_count", 0)) <= 0:
        return False
    if int(diff_ev.get("kernel_checked_ub_count", 0)) <= 0:
        return False
    if int(diff_ev.get("unsound_missed_fault_count", 1)) > 0:
        return False
    if int(diff_ev.get("value_mismatch_count", 1)) > 0:
        return False
    if int(diff_ev.get("unexpected_conservative_count", 1)) > 0:
        return False
    if int(diff_ev.get("leg_divergence_count", 1)) > 0:
        return False
    if diff_ev.get("timed_out"):
        return False
    if not diff_ev.get("capture_bin_source") or not _is_valid_sha256_hex(
        diff_ev.get("capture_bin_sha256")
    ):
        return False
    if detail.get("known_bugs"):
        return False
    if require_mir_eval:
        if "anneal_mir_eval_captured" not in (diff_ev.get("legs") or []):
            return False
        if "anneal_mir_eval_captured" not in (runs[0].get("legs") or []):
            return False
        if any(not isinstance(c.get("mir_eval"), dict) for c in cases):
            return False

    mutants = blocks.get("oracle_mutants")
    if require_mutants and not isinstance(mutants, dict):
        return False
    if isinstance(mutants, dict):
        total = int(mutants.get("total_mutants", 0))
        killed = int(mutants.get("killed_mutants", 0))
        if total == 0 or killed != total:
            return False
        probes = mutants.get("synthetic_lean_probes", [])
        if not isinstance(probes, list) or not probes or any(
            not p.get("passed") for p in probes
        ):
            return False

    fuzz_ev = blocks.get("differential_fuzz")
    if require_fuzz and not isinstance(fuzz_ev, dict):
        return False
    if isinstance(fuzz_ev, dict):
        if fuzz_ev.get("timed_out") or fuzz_ev.get("passed") is False:
            return False
        for fcase in fuzz_ev.get("failing_cases", []):
            if isinstance(fcase, dict) and fcase.get("shrink_trace") is not None:
                st = fcase["shrink_trace"]
                if not isinstance(st, dict):
                    return False
                sv = fcase.get("shrink_verification")
                if sv is None:
                    min_src = st.get("minimized_source")
                    min_src_sha = (
                        hashlib.sha256(min_src.encode("utf-8")).hexdigest()
                        if isinstance(min_src, str)
                        else None
                    )
                    if (
                        st.get("converged_1_minimal")
                        or st.get("shrunk_nodes") != st.get("original_nodes")
                        or st.get("minimized_args") != fcase.get("args")
                        or min_src_sha != fcase.get("program_sha256")
                    ):
                        return False
                elif not isinstance(sv, dict):
                    return False
        run_cap_src = diff_ev.get("capture_bin_source")
        run_cap_sha = diff_ev.get("capture_bin_sha256")
        fuzz_cap_src = fuzz_ev.get("capture_bin_source")
        fuzz_cap_sha = fuzz_ev.get("capture_bin_sha256")
        if (
            not _is_valid_sha256_hex(run_cap_sha)
            or not _is_valid_sha256_hex(fuzz_cap_sha)
            or fuzz_cap_sha != run_cap_sha
            or fuzz_cap_src != run_cap_src
        ):
            return False
        if fuzz_ev.get("gate_error") is not None:
            return False
        if int(fuzz_ev.get("total_cases", 0)) <= 0:
            return False
        if int(fuzz_ev.get("case_records_verified_count", 0)) != int(
            fuzz_ev.get("total_cases", 0)
        ):
            return False
        if int(fuzz_ev.get("unsound_accept_count", 1)) > 0:
            return False
        if int(fuzz_ev.get("authority_disagreement_count", 1)) > 0:
            return False
        if int(fuzz_ev.get("spurious_lean_ub_count", 1)) > 0:
            return False
        if int(fuzz_ev.get("admitted_authority_ub_count", 1)) > 0:
            return False
        if fuzz_require_rustc_leg and "rustc_compiled" not in (
            fuzz_ev.get("legs") or []
        ):
            return False
        if require_mir_eval:
            if "anneal_mir_eval_captured" not in (fuzz_ev.get("legs") or []):
                return False
            cap_rej_cnt = fuzz_ev.get("capture_rejected_count", 0)
            me_ver_cnt = fuzz_ev.get("mir_eval_verified_count", 0)
            if (
                not _is_nonneg_int(cap_rej_cnt)
                or not _is_nonneg_int(me_ver_cnt)
                or int(me_ver_cnt) <= 0
                or int(me_ver_cnt)
                != int(fuzz_ev.get("total_cases", 0)) - int(cap_rej_cnt)
            ):
                return False
        if int(fuzz_ev.get("bi_fault_equiv_count", 0)) <= 0:
            return False
        raw_ub_ratio = (
            fuzz_ub_ratio
            if fuzz_ub_ratio is not None
            else fuzz_ev.get("ub_ratio", 0.20)
        )
        if not _is_bounded_rate(raw_ub_ratio, upper=0.85):
            return False
        eff_ub_ratio = float(raw_ub_ratio)
        total_fuzz_cases = int(fuzz_ev.get("total_cases", 0))
        if (
            fuzz_expected_cases is not None
            and total_fuzz_cases != fuzz_expected_cases
        ):
            return False
        targeted_ub = int(fuzz_ev.get("targeted_ub_probes", 0))
        ub_agreed = int(fuzz_ev.get("ub_probes_agreed_count", 0))
        if eff_ub_ratio > 0.0 and total_fuzz_cases >= 3 and targeted_ub <= 0:
            return False
        if targeted_ub > 0 and ub_agreed != targeted_ub:
            return False
        raw_max_stmts = fuzz_ev.get("max_stmts", 6)
        if (
            isinstance(raw_max_stmts, bool)
            or not isinstance(raw_max_stmts, int)
            or not (1 <= raw_max_stmts <= 20)
        ):
            return False
        if (
            fuzz_expected_max_stmts is not None
            and raw_max_stmts != fuzz_expected_max_stmts
        ):
            return False
        raw_fuel = fuzz_ev.get("fuel")
        if (
            isinstance(raw_fuel, bool)
            or not isinstance(raw_fuel, int)
            or raw_fuel < 1
        ):
            return False
        if fuzz_expected_fuel is not None and raw_fuel != fuzz_expected_fuel:
            return False
        mr_count = int(fuzz_ev.get("move_reinit_exercised_count", 0))
        if (
            raw_max_stmts >= 4
            and int(fuzz_ev.get("total_cases", 0)) >= 16
            and mr_count <= 0
        ):
            return False
        if mr_count > 0:
            ev_count = fuzz_ev.get("move_reinit_evidence_verified_count", 0)
            if not _is_nonneg_int(ev_count) or int(ev_count) != mr_count:
                return False
            if not _witness_summaries_valid(
                fuzz_ev.get("move_reinit_witnesses"), mr_count
            ):
                return False
        raw_reported_floor = fuzz_ev.get("min_admission_rate")
        if not _is_bounded_rate(raw_reported_floor):
            return False
        reported_floor = float(raw_reported_floor)
        if fuzz_min_admission_rate is not None:
            if not _is_bounded_rate(fuzz_min_admission_rate):
                return False
            req_floor = float(fuzz_min_admission_rate)
            if abs(reported_floor - req_floor) > 1e-12:
                return False
            min_rate = req_floor
        else:
            min_rate = reported_floor
        if int(fuzz_ev.get("admission_eligible_cases", 0)) <= 0:
            return False
        raw_adm_rate = fuzz_ev.get("admission_rate")
        if not _is_bounded_rate(raw_adm_rate):
            return False
        if float(raw_adm_rate) < min_rate:
            return False

    mir_eval = blocks.get("mir_eval_cargo_test", {})
    if mir_eval.get("passed") is False or (
        mir_eval.get("executed") and not mir_eval.get("passed")
    ):
        return False
    return True


def _validate_child_tmpdir(env: dict[str, str], base_dir: Path) -> Path | None:
    """Validate and canonicalize optional `TMPDIR` against `base_dir`."""
    raw_tmp = env.get("TMPDIR")
    if not raw_tmp:
        env.pop("TMPDIR", None)
        return None
    validated = _resolve_cli_path(
        Path(raw_tmp),
        "TMPDIR",
        base_dir=base_dir,
        require_dir_components=True,
    )
    if not validated.is_dir():
        raise ValueError(f"TMPDIR must be an existing directory: {validated}")
    canon_tmp = validated.resolve(strict=True)
    env["TMPDIR"] = str(canon_tmp)
    return canon_tmp


def _build_child_env(
    caller_cwd: Path,
    *,
    target_base_dir: Path | None = None,
    default_target_roots: tuple[Path, ...] = (),
    exit_stack: contextlib.ExitStack | None = None,
    _pre_staged_capture_env: dict[str, Path] | None = None,
) -> dict[str, str]:
    """Copy `os.environ`, strip unsafe/loader vars, and anchor paths."""
    child_env = _strip_loader_env_vars(
        _strip_cargo_override_env_vars(
            _strip_child_credentials(os.environ.copy())
        )
    )
    validated_tmp = _validate_child_tmpdir(child_env, caller_cwd)
    tmp_parent = str(validated_tmp) if validated_tmp is not None else None
    td_base = caller_cwd if target_base_dir is None else target_base_dir
    validated_td = _validate_cargo_target_dirs(
        child_env,
        base_dir=td_base,
        default_target_roots=default_target_roots,
    )
    for env_key in _DIFF_CHILD_PATH_ENV_VARS:
        raw_val = child_env.get(env_key)
        if _pre_staged_capture_env is not None and env_key in _pre_staged_capture_env:
            child_env[env_key] = str(
                _validate_pre_staged_executable(
                    _pre_staged_capture_env[env_key],
                    "anneal-rustc-capture",
                    env_key,
                    base_dir=caller_cwd,
                )
            )
            continue
        if raw_val:
            if env_key == "CARGO_TARGET_DIR" and validated_td is not None:
                child_env[env_key] = str(validated_td)
            elif env_key in ("ANNEAL_LEAN", "ANNEAL_MVP_LEAN"):
                child_env[env_key] = _resolve_explicit_lean_override(
                    raw_val, env_key, caller_cwd
                )
            elif env_key in ("ANNEAL_CAPTURE", "ANNEAL_MVP_CAPTURE"):
                if exit_stack is not None:
                    opened_cap = _open_store_aware_executable(
                        Path(raw_val),
                        env_key,
                        base_dir=caller_cwd,
                        allow_cargo_deps_hardlink=True,
                        exit_stack=exit_stack,
                    )
                    child_env[env_key] = str(
                        _maybe_stage_cargo_hardlink_executable(
                            opened_cap.path,
                            "anneal-rustc-capture",
                            exit_stack=exit_stack,
                            base_dir=caller_cwd,
                            tmp_parent=tmp_parent,
                            preopened=opened_cap,
                        )
                    )
                else:
                    verified_cap = _resolve_cargo_executable_cli_path(
                        Path(raw_val), env_key, base_dir=caller_cwd
                    )
                    child_env[env_key] = str(verified_cap)
            elif env_key in _DIFF_CHILD_EXECUTABLE_ENV_VARS:
                child_env[env_key] = str(
                    _resolve_executable_cli_path(
                        Path(raw_val), env_key, base_dir=caller_cwd
                    )
                )
            elif env_key in _DIFF_CHILD_DIR_ENV_VARS:
                child_env[env_key] = str(
                    _resolve_store_aware_dir_cli_path(
                        Path(raw_val),
                        env_key,
                        base_dir=caller_cwd,
                    )
                )
            else:
                child_env[env_key] = _anchor_env_path(raw_val, caller_cwd)
        elif env_key == "CARGO_TARGET_DIR":
            child_env.pop(env_key, None)
    for cmd_key in ("CARGO", "RUSTC", "RUSTDOC"):
        raw_cmd = child_env.get(cmd_key)
        if raw_cmd:
            child_env[cmd_key] = _resolve_command_token(raw_cmd, caller_cwd)
        elif cmd_key in child_env:
            child_env.pop(cmd_key, None)
    raw_path = child_env.get("PATH")
    if raw_path:
        child_env["PATH"] = _anchor_search_path_list(raw_path, caller_cwd)
    raw_ch = child_env.get("CARGO_HOME")
    if raw_ch:
        child_env["CARGO_HOME"] = str(
            _resolve_cli_path(
                Path(raw_ch),
                "CARGO_HOME",
                base_dir=caller_cwd,
                require_dir_components=True,
            )
        )
    elif "CARGO_HOME" in child_env:
        child_env.pop("CARGO_HOME", None)
    raw_rh = child_env.get("RUSTUP_HOME")
    if raw_rh:
        child_env["RUSTUP_HOME"] = str(
            _validate_rustup_home_and_settings(
                Path(raw_rh), "RUSTUP_HOME", base_dir=caller_cwd
            )
        )
    elif "RUSTUP_HOME" in child_env:
        child_env.pop("RUSTUP_HOME", None)
    raw_rt = child_env.get("RUSTUP_TOOLCHAIN")
    if raw_rt:
        child_env["RUSTUP_TOOLCHAIN"] = _validate_rustup_toolchain(raw_rt)
    elif "RUSTUP_TOOLCHAIN" in child_env:
        child_env.pop("RUSTUP_TOOLCHAIN", None)
    raw_home = child_env.get("HOME")
    if raw_home:
        child_env["HOME"] = str(
            _resolve_cli_path(
                Path(raw_home),
                "HOME",
                base_dir=caller_cwd,
                require_dir_components=True,
            )
        )
    elif "HOME" in child_env:
        child_env.pop("HOME", None)
    return child_env


_TRUSTED_LINKER_DIRS: tuple[Path, ...] = (
    (Path("/usr/bin"), Path("/usr/local/bin")) if os.name != "nt" else ()
)
_TRUSTED_LINKER_SYMLINK_DIRS: tuple[Path, ...] = (
    (Path("/etc/alternatives"),) if os.name != "nt" else ()
)
_TRUSTED_CHILD_PATH_DIRS: tuple[Path, ...] = (
    (Path("/usr/bin"), Path("/bin")) if os.name != "nt" else ()
)
_LINKER_BIN_NAME = "cc.exe" if os.name == "nt" else "cc"
_MAX_LINKER_SYMLINK_HOPS = 16


def _is_rustup_proxy_symlink(path: Path) -> bool:
    try:
        st = os.lstat(path)
    except OSError:
        return False
    if not stat.S_ISLNK(st.st_mode):
        return False
    try:
        return os.readlink(path) == "rustup"
    except OSError:
        return False


def _validate_regular_non_linked_file(
    path: Path, label: str, *, base_dir: Path | None = None
) -> Path:
    resolved = _resolve_cli_path(path, label, base_dir=base_dir)
    try:
        st = os.lstat(resolved)
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {resolved}: {exc}") from exc
    if stat.S_ISLNK(st.st_mode):
        raise ValueError(f"{label} must not be a symlink: {resolved}")
    if not stat.S_ISREG(st.st_mode):
        raise ValueError(f"{label} is not a regular file: {resolved}")
    if st.st_nlink > 1:
        raise ValueError(
            f"{label} must not be a hardlink (nlink={st.st_nlink}): {resolved}"
        )
    return resolved


class _RustupProxyResolutionError(ValueError):
    """Raised when `rustup which` execution itself fails."""


def _validate_rustup_toolchain(raw_val: str) -> str:
    if (
        "\0" in raw_val
        or "/" in raw_val
        or "\\" in raw_val
        or ".." in raw_val
    ):
        raise ValueError(f"unsafe RUSTUP_TOOLCHAIN value: {raw_val!r}")
    return raw_val


def _read_rustup_settings_bytes_via_dirfd(
    rustup_dir: Path, label: str, *, base_dir: Path
) -> tuple[Path, bytes | None]:
    resolved = _resolve_cli_path(
        rustup_dir,
        label,
        base_dir=base_dir,
        require_dir_components=True,
    )
    try:
        os.lstat(resolved)
    except FileNotFoundError:
        return resolved, None
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {resolved}: {exc}") from exc
    if os.name == "posix":
        dir_fd = _open_dir_handle_no_symlinks(resolved, label)
        try:
            try:
                os.lstat("settings.toml", dir_fd=dir_fd)
            except FileNotFoundError:
                return resolved, None
            except OSError as exc:
                raise ValueError(
                    f"cannot inspect {label}/settings.toml {resolved / 'settings.toml'}: {exc}"
                ) from exc
            fd, _ = _open_regular_file_from_fd(
                dir_fd, "settings.toml", None, False, f"{label}/settings.toml"
            )
            try:
                return resolved, os.fdopen(fd, "rb", closefd=False).read()
            finally:
                os.close(fd)
        finally:
            os.close(dir_fd)
    settings_toml = resolved / "settings.toml"
    try:
        os.lstat(settings_toml)
    except FileNotFoundError:
        return resolved, None
    except OSError as exc:
        raise ValueError(
            f"cannot inspect {label}/settings.toml {settings_toml}: {exc}"
        ) from exc
    checked = _validate_regular_non_linked_file(
        settings_toml,
        f"{label}/settings.toml",
        base_dir=base_dir,
    )
    return resolved, checked.read_bytes()


def _validate_rustup_home_and_settings(
    rustup_dir: Path, label: str, *, base_dir: Path
) -> Path:
    resolved, _ = _read_rustup_settings_bytes_via_dirfd(
        rustup_dir, label, base_dir=base_dir
    )
    return resolved


def _derive_toolchain_from_rustup_settings(
    raw_bytes: bytes, orig_work_dir: Path, label: str
) -> str | None:
    try:
        parsed = tomllib.loads(raw_bytes.decode("utf-8"))
    except (UnicodeDecodeError, tomllib.TOMLDecodeError) as exc:
        raise ValueError(f"invalid {label}/settings.toml: {exc}") from exc
    if not isinstance(parsed, dict):
        raise ValueError(f"{label}/settings.toml must parse to a TOML table")
    derived: str | None = None
    overrides = parsed.get("overrides")
    if isinstance(overrides, dict):
        for anc in (orig_work_dir, *orig_work_dir.parents):
            for k, v in overrides.items():
                kp = Path(k)
                matched = kp == anc
                if not matched:
                    try:
                        matched = (
                            _resolve_cli_path(
                                kp,
                                f"{label}/settings.toml override",
                                base_dir=orig_work_dir,
                                require_dir_components=True,
                            ).resolve(strict=False)
                            == anc
                        )
                    except ValueError:
                        matched = False
                if matched:
                    if not isinstance(v, str):
                        raise ValueError(
                            f"{label}/settings.toml [overrides] value must be a string"
                        )
                    derived = v
                    break
            if derived is not None:
                break
    if derived is None and "default_toolchain" in parsed:
        def_val = parsed["default_toolchain"]
        if not isinstance(def_val, str):
            raise ValueError(
                f"{label}/settings.toml default_toolchain must be a string"
            )
        derived = def_val
    if derived is not None:
        return _validate_rustup_toolchain(derived)
    return None


def _pin_rustup_settings(
    probe_env: dict[str, str],
    base_dir: Path,
    orig_work_dir: Path,
    exit_stack: contextlib.ExitStack,
) -> None:
    """Pin `RUSTUP_TOOLCHAIN` or an immutable `RUSTUP_HOME` from `settings.toml`."""
    raw_rt = probe_env.get("RUSTUP_TOOLCHAIN")
    if raw_rt:
        probe_env["RUSTUP_TOOLCHAIN"] = _validate_rustup_toolchain(raw_rt)
    raw_rh = probe_env.get("RUSTUP_HOME")
    settings_bytes: bytes | None = None
    label = ""
    if raw_rh:
        resolved_rh, settings_bytes = _read_rustup_settings_bytes_via_dirfd(
            Path(raw_rh), "RUSTUP_HOME", base_dir=base_dir
        )
        probe_env["RUSTUP_HOME"] = str(resolved_rh)
        label = "RUSTUP_HOME"
    else:
        raw_home = probe_env.get("HOME")
        home_path: Path | None = None
        if raw_home:
            home_path = Path(_anchor_env_path(raw_home, base_dir))
        else:
            try:
                home_path = Path.home()
            except RuntimeError:
                home_path = None
        if home_path is not None:
            dot_rustup = home_path / ".rustup"
            try:
                os.lstat(dot_rustup)
                _, settings_bytes = _read_rustup_settings_bytes_via_dirfd(
                    dot_rustup, "HOME/.rustup", base_dir=base_dir
                )
                label = "HOME/.rustup"
            except FileNotFoundError:
                pass
            except OSError as exc:
                raise ValueError(
                    f"cannot inspect HOME/.rustup {dot_rustup}: {exc}"
                ) from exc
    if raw_rt:
        return
    if settings_bytes is not None:
        derived = _derive_toolchain_from_rustup_settings(
            settings_bytes, orig_work_dir, label
        )
        if derived is not None:
            probe_env["RUSTUP_TOOLCHAIN"] = derived
            return

    def _populate_rustup(_priv_root: Path, pinned_root: Path) -> None:
        if settings_bytes is None:
            return
        dst = pinned_root / "settings.toml"
        if os.name == "posix":
            dst_fd = os.open(
                dst, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600
            )
            with os.fdopen(dst_fd, "wb") as dst_f:
                dst_f.write(settings_bytes)
                dst_f.flush()
                os.fchmod(dst_f.fileno(), 0o444)
        else:
            dst.write_bytes(settings_bytes)

    pinned_rh = _build_pinned_staging_dir(
        exit_stack,
        prefix="anneal-rustup-home-",
        base_dir=base_dir,
        tmp_parent=probe_env.get("TMPDIR") or None,
        label="rustup settings",
        populate=_populate_rustup,
    )
    probe_env["RUSTUP_HOME"] = str(pinned_rh)


def _validate_default_rustup_home_if_proxy(
    cmd_paths: tuple[str | None, ...],
    base_dir: Path,
    *,
    env: dict[str, str] | None = None,
) -> None:
    """Validate `RUSTUP_HOME` or `HOME/.rustup` before running a proxy."""
    if not any(
        p is not None and _is_rustup_proxy_symlink(Path(p)) for p in cmd_paths
    ):
        return
    src_env = os.environ if env is None else env
    raw_rustup_home = src_env.get("RUSTUP_HOME")
    if raw_rustup_home:
        _validate_rustup_home_and_settings(
            Path(raw_rustup_home), "RUSTUP_HOME", base_dir=base_dir
        )
        return
    raw_home = src_env.get("HOME")
    if raw_home:
        home_path = Path(_anchor_env_path(raw_home, base_dir))
    else:
        try:
            home_path = Path.home()
        except RuntimeError:
            return
    rustup_dir = home_path / ".rustup"
    try:
        os.lstat(rustup_dir)
    except FileNotFoundError:
        return
    except OSError as exc:
        raise ValueError(
            f"cannot inspect HOME/.rustup {rustup_dir}: {exc}"
        ) from exc
    _validate_rustup_home_and_settings(
        rustup_dir, "HOME/.rustup", base_dir=base_dir
    )


def _resolve_rustup_proxy_binary_opened(
    proxy_cmd: Path,
    tool_name: str,
    *,
    work_dir: Path,
    env: dict[str, str],
    base_dir: Path,
    exit_stack: contextlib.ExitStack,
    store_prefix: Path = _STORE_PREFIX,
    preopened_rustup: _OpenedExecutable | None = None,
    orig_work_dir: Path | None = None,
    rustup_settings_pinned: bool = False,
) -> _OpenedExecutable:
    """Resolve a `rustup` proxy and open the resolved target via dirfd."""
    rustup_path = proxy_cmd.parent / "rustup"
    probe_env = _strip_loader_env_vars(
        _strip_cargo_override_env_vars(_strip_child_credentials(dict(env)))
    )
    anchor_work = work_dir if orig_work_dir is None else orig_work_dir
    if not rustup_settings_pinned:
        _pin_rustup_settings(probe_env, base_dir, anchor_work, exit_stack)
    staged_rustup = _stage_verified_executable(
        rustup_path,
        "rustup",
        allow_cargo_deps_hardlink=False,
        exit_stack=exit_stack,
        base_dir=base_dir,
        tmp_parent=probe_env.get("TMPDIR"),
        store_prefix=store_prefix,
        preserve_bin_name=True,
        preopened=(
            preopened_rustup
            if preopened_rustup is not None and preopened_rustup.fd is not None
            else None
        ),
    )
    probe_env["PATH"] = str(staged_rustup.parent)
    proc = _run_subcommand_process_group(
        [str(staged_rustup), "which", tool_name],
        cwd=work_dir,
        env=probe_env,
        timeout_secs=30.0,
    )
    if proc.returncode != 0:
        detail = (proc.stderr or proc.stdout).strip()
        raise _RustupProxyResolutionError(
            f"rustup proxy resolution failed for `{tool_name}` "
            f"(rc={proc.returncode}): {detail}"
        )
    raw_resolved = proc.stdout.strip()
    if not raw_resolved:
        raise _RustupProxyResolutionError(
            f"rustup proxy `{rustup_path} which {tool_name}` returned empty output"
        )
    cand_path = Path(raw_resolved.splitlines()[0].strip())
    if ".." in cand_path.parts or not cand_path.is_absolute():
        raise ValueError(
            f"rustup proxy returned unsafe `{tool_name}` path: {cand_path}"
        )
    if _is_rustup_proxy_symlink(cand_path):
        raise ValueError(
            f"resolved rustup `{tool_name}` must not chain back to proxy: "
            f"{cand_path}"
        )
    opened = _open_store_aware_executable(
        cand_path,
        f"resolved rustup {tool_name}",
        base_dir=work_dir,
        store_prefix=store_prefix,
        exit_stack=exit_stack,
    )
    if _is_rustup_proxy_symlink(opened.path):
        raise ValueError(
            f"resolved rustup `{tool_name}` must not chain back to proxy: "
            f"{opened.path}"
        )
    return opened


def _resolve_rustup_proxy_binary(
    proxy_cmd: Path,
    tool_name: str,
    *,
    work_dir: Path,
    env: dict[str, str],
    base_dir: Path,
    exit_stack: contextlib.ExitStack | None = None,
    store_prefix: Path = _STORE_PREFIX,
    orig_work_dir: Path | None = None,
    preopened_rustup: _OpenedExecutable | None = None,
    rustup_settings_pinned: bool = False,
) -> Path:
    """Resolve a `rustup` symlink proxy cleanly to a validated real binary."""
    with contextlib.ExitStack() as local_stack:
        stack = local_stack if exit_stack is None else exit_stack
        return _resolve_rustup_proxy_binary_opened(
            proxy_cmd,
            tool_name,
            work_dir=work_dir,
            env=env,
            base_dir=base_dir,
            exit_stack=stack,
            store_prefix=store_prefix,
            orig_work_dir=orig_work_dir,
            preopened_rustup=preopened_rustup,
            rustup_settings_pinned=rustup_settings_pinned,
        ).path


def _open_dir_handle_no_symlinks(abs_dir: Path, label: str) -> int:
    """Open `abs_dir` step-by-step using `O_RDONLY | O_DIRECTORY | O_NOFOLLOW`."""
    if not abs_dir.is_absolute():
        raise ValueError(f"{label} must be an absolute path: {abs_dir}")
    dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    try:
        cur_fd = os.open("/", dir_flags)
    except OSError as exc:
        raise ValueError(f"open `/` for {label}: {exc}") from exc
    try:
        for seg in abs_dir.parts:
            if seg in ("", "/", "."):
                continue
            if seg == "..":
                raise ValueError(
                    f"{label} must not contain `..` traversal: {abs_dir}"
                )
            next_fd = _open_child_dir_nofollow(cur_fd, seg, None, label)
            os.close(cur_fd)
            cur_fd = next_fd
        st = os.fstat(cur_fd)
        if not stat.S_ISDIR(st.st_mode):
            raise ValueError(f"{label} is not a directory: {abs_dir}")
        return cur_fd
    except Exception:
        os.close(cur_fd)
        raise


def _open_child_dir_nofollow(
    parent_fd: int,
    name: str,
    expected_dev_ino: tuple[int, int] | None,
    label: str,
) -> int:
    if not name or name in (".", "..") or "/" in name or "\0" in name:
        raise ValueError(f"{label} directory segment must not traverse: {name!r}")
    dir_flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0)
    try:
        fd = os.open(name, dir_flags, dir_fd=parent_fd)
    except OSError as exc:
        is_sym = (
            exc.errno == getattr(errno, "ELOOP", None)
            or "ELOOP" in str(exc)
            or exc.errno == 40
        )
        if not is_sym and exc.errno == getattr(errno, "ENOTDIR", None):
            try:
                is_sym = stat.S_ISLNK(os.lstat(name, dir_fd=parent_fd).st_mode)
            except OSError:
                is_sym = False
        if is_sym:
            raise ValueError(
                f"{label} must not be or traverse a symlink: {name}"
            ) from exc
        raise ValueError(f"open {label} {name}: {exc}") from exc
    try:
        st = os.fstat(fd)
        if not stat.S_ISDIR(st.st_mode):
            raise ValueError(f"{label} is not a directory: {name}")
        if expected_dev_ino is not None and (st.st_dev, st.st_ino) != expected_dev_ino:
            raise ValueError(
                f"{label} directory changed identity during traversal: {name}"
            )
        return fd
    except Exception:
        os.close(fd)
        raise


def _read_dir_entries_from_fd(
    dir_fd: int, label: str
) -> list[tuple[str, os.stat_result]]:
    try:
        names = sorted(os.listdir(dir_fd))
    except OSError as exc:
        raise ValueError(f"read {label} dir: {exc}") from exc
    entries: list[tuple[str, os.stat_result]] = []
    for name in names:
        try:
            st = os.lstat(name, dir_fd=dir_fd)
        except OSError as exc:
            raise ValueError(f"stat {label} {name}: {exc}") from exc
        entries.append((name, st))
    return entries


def _open_regular_file_from_fd(
    dir_fd: int,
    name: str,
    expected_dev_ino: tuple[int, int] | None,
    allow_hardlink: bool,
    label: str,
) -> tuple[int, os.stat_result]:
    open_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_CLOEXEC", 0)
    try:
        fd = os.open(name, open_flags, dir_fd=dir_fd)
    except OSError as exc:
        if exc.errno == getattr(errno, "ELOOP", None) or exc.errno == 40:
            raise ValueError(f"{label} must not be a symlink: {name}") from exc
        raise ValueError(f"open {label} {name}: {exc}") from exc
    try:
        st = os.fstat(fd)
        if not stat.S_ISREG(st.st_mode):
            raise ValueError(f"{label} is not a regular file: {name}")
        if not allow_hardlink and st.st_nlink > 1:
            raise _HardlinkedCommandError(
                f"{label} file must not be a hardlink (nlink={st.st_nlink}): {name}"
            )
        if expected_dev_ino is not None and (st.st_dev, st.st_ino) != expected_dev_ino:
            raise ValueError(
                f"{label} inode changed between validation and open: {name}"
            )
        return fd, st
    except Exception:
        os.close(fd)
        raise


def _resolve_and_open_confined_lib_symlink_from_fd(
    root_fd: int,
    cur_fd: int,
    cur_rel_parts: tuple[str, ...],
    link_name: str,
    link_display: Path,
    label: str,
) -> tuple[int, os.stat_result]:
    hop_dir_fd: int | None = None
    hop_rel_parts = list(cur_rel_parts)
    hop_name = link_name
    try:
        for _ in range(_MAX_LINKER_SYMLINK_HOPS):
            active_fd = cur_fd if hop_dir_fd is None else hop_dir_fd
            try:
                raw_str = os.readlink(hop_name, dir_fd=active_fd)
            except OSError as exc:
                raise ValueError(f"readlink {label} {link_display}: {exc}") from exc
            if not raw_str:
                raise ValueError(f"{label} contains empty symlink: {link_display}")
            raw_target = Path(raw_str)
            if (
                raw_target.is_absolute()
                or bool(raw_target.anchor)
                or (raw_target.parts and raw_target.parts[0] in ("/", "\\"))
            ):
                raise ValueError(
                    f"{label} must not contain an absolute symlink: "
                    f"{link_display} -> {raw_target}"
                )
            target_segs = list(hop_rel_parts)
            for comp in raw_target.parts:
                if comp == ".":
                    continue
                if comp == "..":
                    if not target_segs:
                        raise ValueError(
                            f"{label} symlink escaped {label}: "
                            f"{link_display} -> {raw_target}"
                        )
                    target_segs.pop()
                else:
                    target_segs.append(comp)
            if not target_segs:
                raise ValueError(
                    f"{label} symlink targets {label} root: "
                    f"{link_display} -> {raw_target}"
                )
            *dir_segs, leaf_name = target_segs
            walk_fds: list[int] = []
            try:
                parent_fd = root_fd
                for seg in dir_segs:
                    try:
                        child_fd = _open_child_dir_nofollow(
                            parent_fd, seg, None, label
                        )
                    except ValueError as exc:
                        raise ValueError(
                            f"{label} symlink must resolve to a regular file "
                            f"inside {label}: {link_display}"
                        ) from exc
                    walk_fds.append(child_fd)
                    parent_fd = child_fd
                try:
                    st = os.lstat(leaf_name, dir_fd=parent_fd)
                except OSError as exc:
                    raise ValueError(
                        f"stat {label} {link_display}: {exc}"
                    ) from exc
                if stat.S_ISLNK(st.st_mode):
                    if st.st_nlink > 1:
                        raise _HardlinkedCommandError(
                            f"{label} symlink target must not be a hardlink "
                            f"(nlink={st.st_nlink}): {link_display}"
                        )
                    if hop_dir_fd is not None:
                        os.close(hop_dir_fd)
                    hop_dir_fd = walk_fds.pop() if walk_fds else os.dup(root_fd)
                    hop_rel_parts = dir_segs
                    hop_name = leaf_name
                    continue
                if not stat.S_ISREG(st.st_mode):
                    raise ValueError(
                        f"{label} symlink must resolve to a regular file "
                        f"inside {label}: {link_display}"
                    )
                if st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{label} symlink target must not be a hardlink "
                        f"(nlink={st.st_nlink}): {link_display}"
                    )
                return _open_regular_file_from_fd(
                    parent_fd,
                    leaf_name,
                    (st.st_dev, st.st_ino),
                    False,
                    label,
                )
            finally:
                for fd in walk_fds:
                    os.close(fd)
        raise ValueError(
            f"{label} exceeded {_MAX_LINKER_SYMLINK_HOPS} symlink hops: "
            f"{link_display}"
        )
    finally:
        if hop_dir_fd is not None:
            os.close(hop_dir_fd)


def _resolve_confined_lib_symlink(
    canon_lib: Path, cur_dir: Path, path: Path, label: str
) -> Path:
    """Resolve intra-`lib/` relative symlink targeting a unique file."""
    try:
        raw_str = os.readlink(path)
    except OSError as exc:
        raise ValueError(f"readlink {label} {path}: {exc}") from exc
    if not raw_str:
        raise ValueError(f"{label} contains empty symlink: {path}")
    raw_target = Path(raw_str)
    if (
        raw_target.is_absolute()
        or bool(raw_target.anchor)
        or (raw_target.parts and raw_target.parts[0] in ("/", "\\"))
    ):
        raise ValueError(
            f"{label} must not contain an absolute symlink: "
            f"{path} -> {raw_target}"
        )
    cur_lex = cur_dir
    for comp in raw_target.parts:
        if comp == ".":
            continue
        if comp == "..":
            if cur_lex == canon_lib or not cur_lex.is_relative_to(canon_lib):
                raise ValueError(
                    f"{label} symlink escaped {label}: {path} -> {raw_target}"
                )
            cur_lex = cur_lex.parent
            if not cur_lex.is_relative_to(canon_lib):
                raise ValueError(
                    f"{label} symlink escaped {label}: {path} -> {raw_target}"
                )
        else:
            cur_lex = cur_lex / comp
    if cur_lex == canon_lib:
        raise ValueError(
            f"{label} symlink targets {label} root: {path} -> {raw_target}"
        )
    try:
        target_canon = path.resolve(strict=True)
    except OSError as exc:
        raise ValueError(f"canonicalize {label} {path}: {exc}") from exc
    if target_canon == canon_lib or not target_canon.is_relative_to(canon_lib):
        raise ValueError(
            f"{label} symlink escaped {label}: {path} -> {target_canon}"
        )
    try:
        target_lstat = os.lstat(target_canon)
    except OSError as exc:
        raise ValueError(f"stat {label} {target_canon}: {exc}") from exc
    if stat.S_ISLNK(target_lstat.st_mode) or not stat.S_ISREG(
        target_lstat.st_mode
    ):
        raise ValueError(
            f"{label} symlink must resolve to a regular file inside "
            f"{label}: {path}"
        )
    if target_lstat.st_nlink > 1:
        raise _HardlinkedCommandError(
            f"{label} symlink target must not be a hardlink "
            f"(nlink={target_lstat.st_nlink}): {target_canon}"
        )
    return target_canon


def _inspect_sysroot_lib_dir_tree(
    canon_lib: Path,
    label: str,
    *,
    allow_confined_symlinks: bool = False,
) -> bool:
    """Validate `lib/` tree; optionally allow confined intra-`lib/` links."""
    if os.name == "posix":
        root_fd = _open_dir_handle_no_symlinks(canon_lib, label)
        has_symlinks = False
        stack: list[tuple[int | None, tuple[str, ...], Path]] = [
            (None, (), canon_lib)
        ]
        try:
            while stack:
                dir_fd, rel_parts, cur_disp = stack.pop()
                active_fd = root_fd if dir_fd is None else dir_fd
                try:
                    entries = _read_dir_entries_from_fd(active_fd, label)
                    for name, st in entries:
                        path = cur_disp / name
                        if stat.S_ISLNK(st.st_mode):
                            if not allow_confined_symlinks:
                                raise ValueError(
                                    f"{label} must not contain a symlink: {path}"
                                )
                            if st.st_nlink > 1:
                                raise _HardlinkedCommandError(
                                    f"{label} symlink must not be a hardlink "
                                    f"(nlink={st.st_nlink}): {path}"
                                )
                            opened_fd, _ = (
                                _resolve_and_open_confined_lib_symlink_from_fd(
                                    root_fd,
                                    active_fd,
                                    rel_parts,
                                    name,
                                    path,
                                    label,
                                )
                            )
                            os.close(opened_fd)
                            has_symlinks = True
                        elif stat.S_ISDIR(st.st_mode):
                            child_fd = _open_child_dir_nofollow(
                                active_fd,
                                name,
                                (st.st_dev, st.st_ino),
                                label,
                            )
                            stack.append(
                                (child_fd, (*rel_parts, name), path)
                            )
                        elif stat.S_ISREG(st.st_mode):
                            if st.st_nlink > 1:
                                raise _HardlinkedCommandError(
                                    f"{label} file must not be a hardlink "
                                    f"(nlink={st.st_nlink}): {path}"
                                )
                        else:
                            raise ValueError(
                                f"{label} contains non-regular entry: {path}"
                            )
                finally:
                    if dir_fd is not None:
                        os.close(dir_fd)
            return has_symlinks
        finally:
            while stack:
                leftover_fd, _, _ = stack.pop()
                if leftover_fd is not None:
                    os.close(leftover_fd)
            os.close(root_fd)

    stack = [canon_lib]
    has_symlinks = False
    while stack:
        cur_dir = stack.pop()
        try:
            with os.scandir(cur_dir) as it:
                entries = sorted(it, key=lambda e: e.name)
        except OSError as exc:
            raise ValueError(f"read {label} dir {cur_dir}: {exc}") from exc
        for entry in entries:
            path = Path(entry.path)
            try:
                st = os.lstat(path)
            except OSError as exc:
                raise ValueError(f"stat {label} {path}: {exc}") from exc
            if stat.S_ISLNK(st.st_mode):
                if not allow_confined_symlinks:
                    raise ValueError(
                        f"{label} must not contain a symlink: {path}"
                    )
                if st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{label} symlink must not be a hardlink "
                        f"(nlink={st.st_nlink}): {path}"
                    )
                _resolve_confined_lib_symlink(canon_lib, cur_dir, path, label)
                has_symlinks = True
            elif stat.S_ISDIR(st.st_mode):
                stack.append(path)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{label} file must not be a hardlink "
                        f"(nlink={st.st_nlink}): {path}"
                    )
            else:
                raise ValueError(
                    f"{label} contains non-regular entry: {path}"
                )
    return has_symlinks


def _validate_dir_tree_no_links(root_dir: Path, label: str) -> None:
    """Recursively reject symlinks, hardlinks, and non-regular entries."""
    _inspect_sysroot_lib_dir_tree(
        root_dir, label, allow_confined_symlinks=False
    )


def _validate_store_contained_dir_tree(
    root_dir: Path,
    *,
    store_prefix: Path,
    base_dir: Path,
    label: str,
) -> None:
    """Validate `/nix/store` `lib/` descendants stay inside `store_prefix`."""
    try:
        canon_store = _resolve_cli_path(
            store_prefix,
            "store root",
            base_dir=base_dir,
            require_dir_components=True,
        ).resolve(strict=True)
    except (OSError, ValueError) as exc:
        raise ValueError(
            f"cannot resolve store root for {label}: {exc}"
        ) from exc
    stack = [root_dir]
    visited = {root_dir}
    while stack:
        cur_dir = stack.pop()
        try:
            with os.scandir(cur_dir) as it:
                entries = sorted(it, key=lambda e: e.name)
        except OSError as exc:
            raise ValueError(f"read {label} dir {cur_dir}: {exc}") from exc
        for entry in entries:
            path = Path(entry.path)
            try:
                st = os.lstat(path)
            except OSError as exc:
                raise ValueError(f"stat {label} {path}: {exc}") from exc
            if stat.S_ISLNK(st.st_mode):
                if st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{label} symlink must not be a hardlink "
                        f"(nlink={st.st_nlink}): {path}"
                    )
                try:
                    target_canon = path.resolve(strict=True)
                except OSError as exc:
                    raise ValueError(
                        f"cannot canonicalize {label} {path}: {exc}"
                    ) from exc
                if (
                    target_canon == canon_store
                    or not target_canon.is_relative_to(canon_store)
                ):
                    raise ValueError(
                        f"{label} symlink escaped store {canon_store}: "
                        f"{path} -> {target_canon}"
                    )
                target_is_dir = os.path.isdir(target_canon)
                checked = _resolve_store_contained_entry(
                    path,
                    label,
                    store_prefix=store_prefix,
                    base_dir=base_dir,
                    expect_dir=target_is_dir,
                )
                if checked is None:
                    raise ValueError(
                        f"{label} symlink escaped store {canon_store}: "
                        f"{path}"
                    )
                if target_is_dir and checked not in visited:
                    visited.add(checked)
                    stack.append(checked)
            elif stat.S_ISDIR(st.st_mode):
                if path not in visited:
                    visited.add(path)
                    stack.append(path)
            elif stat.S_ISREG(st.st_mode):
                if st.st_nlink > 1:
                    raise _HardlinkedCommandError(
                        f"{label} file must not be a hardlink "
                        f"(nlink={st.st_nlink}): {path}"
                    )
            else:
                raise ValueError(
                    f"{label} contains non-regular entry: {path}"
                )


def _restore_dir_write_perms_from_fd(root_fd: int) -> None:
    """Restore owner write bits top-down through a pinned open dir fd."""
    if os.name != "posix":
        return
    try:
        stack = [os.dup(root_fd)]
    except OSError:
        return
    while stack:
        cur_fd = stack.pop()
        try:
            try:
                os.fchmod(cur_fd, 0o700)
            except OSError:
                pass
            try:
                entries = _read_dir_entries_from_fd(
                    cur_fd, "mir-eval staging cleanup"
                )
            except ValueError:
                continue
            for name, st in entries:
                if stat.S_ISDIR(st.st_mode) and not stat.S_ISLNK(st.st_mode):
                    try:
                        child_fd = _open_child_dir_nofollow(
                            cur_fd,
                            name,
                            (st.st_dev, st.st_ino),
                            "mir-eval staging cleanup",
                        )
                        stack.append(child_fd)
                    except (OSError, ValueError):
                        pass
        finally:
            _close_fd_quiet(cur_fd)


def _restore_dir_write_perms_top_down(root: Path) -> None:
    """Restore owner write bits top-down before `TemporaryDirectory` removal."""
    if os.name != "posix":
        return
    stack = [root]
    while stack:
        cur = stack.pop()
        try:
            os.chmod(cur, 0o700)
        except OSError:
            pass
        try:
            with os.scandir(cur) as it:
                for entry in it:
                    path = Path(entry.path)
                    try:
                        st = os.lstat(path)
                    except OSError:
                        continue
                    if stat.S_ISDIR(st.st_mode) and not stat.S_ISLNK(st.st_mode):
                        stack.append(path)
        except OSError:
            continue


def _cleanup_staging_tempdir(
    tmp_dir: tempfile.TemporaryDirectory[Any], priv_root: Path
) -> None:
    _restore_dir_write_perms_top_down(priv_root)
    tmp_dir.cleanup()


def _copy_opened_file_to_new_dst(
    src_fd: int, src_mode: int, dst_path: Path, label: str
) -> None:
    dst_fd = os.open(dst_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(src_fd, "rb", closefd=False) as src_f:
            with os.fdopen(dst_fd, "wb") as dst_f:
                while chunk := src_f.read(1048576):
                    dst_f.write(chunk)
                dst_f.flush()
                if os.name == "posix":
                    is_exec = (src_mode & 0o111) != 0
                    os.fchmod(dst_f.fileno(), 0o555 if is_exec else 0o444)
    except Exception:
        try:
            dst_path.unlink()
        except OSError:
            pass
        raise


def _copy_verified_regular_file(
    src_path: Path, dst_path: Path, label: str
) -> None:
    """Copy a validated non-hardlinked file without following leaf symlinks."""
    try:
        lstat = os.lstat(src_path)
    except OSError as exc:
        raise ValueError(f"stat {label} {src_path}: {exc}") from exc
    if stat.S_ISLNK(lstat.st_mode) or not stat.S_ISREG(lstat.st_mode):
        raise ValueError(
            f"{label} target must be a regular non-symlink file: {src_path}"
        )
    if lstat.st_nlink > 1:
        raise _HardlinkedCommandError(
            f"{label} must not be a hardlink (nlink={lstat.st_nlink}): "
            f"{src_path}"
        )

    open_flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    try:
        src_fd = os.open(src_path, open_flags)
    except OSError as exc:
        raise ValueError(f"open {label} {src_path}: {exc}") from exc
    try:
        fstat = os.fstat(src_fd)
        if not stat.S_ISREG(fstat.st_mode):
            raise ValueError(f"{label} target is not a regular file: {src_path}")
        if (fstat.st_dev, fstat.st_ino) != (lstat.st_dev, lstat.st_ino):
            raise ValueError(
                f"{label} inode changed between validation and open: "
                f"{src_path}"
            )
        if fstat.st_nlink > 1:
            raise _HardlinkedCommandError(
                f"{label} must not be a hardlink (nlink={fstat.st_nlink}): "
                f"{src_path}"
            )
        _copy_opened_file_to_new_dst(src_fd, lstat.st_mode, dst_path, label)
    finally:
        os.close(src_fd)


def _close_staging_fd(fd: int) -> None:
    try:
        os.close(fd)
    except OSError:
        pass


def _begin_pinned_staging_dir_fd(
    exit_stack: contextlib.ExitStack, priv_root: Path, label: str
) -> tuple[Path, int | None]:
    if not sys.platform.startswith("linux"):
        return priv_root, None
    fd = _open_dir_handle_no_symlinks(priv_root, label)
    try:
        st = os.fstat(fd)
        if (
            not stat.S_ISDIR(st.st_mode)
            or stat.S_IMODE(st.st_mode) != 0o700
            or st.st_uid != os.geteuid()
        ):
            raise ValueError(
                f"{label} staging root permissions/owner altered before pinning: "
                f"{priv_root}"
            )
        if os.listdir(fd):
            raise ValueError(
                f"{label} staging root was not empty before pinning: {priv_root}"
            )
    except Exception:
        os.close(fd)
        raise
    exit_stack.callback(_close_staging_fd, fd)
    return Path(f"/proc/self/fd/{fd}"), fd


def _build_pinned_staging_dir(
    exit_stack: contextlib.ExitStack,
    *,
    prefix: str,
    base_dir: Path,
    tmp_parent: str | None,
    label: str,
    populate: Any,
) -> Path:
    tmp_dir = tempfile.TemporaryDirectory(prefix=prefix, dir=tmp_parent)
    raw_priv = Path(tmp_dir.name)
    cleaned = False
    try:
        if os.name == "posix":
            os.chmod(raw_priv, 0o700)
        priv_root = _resolve_cli_path(
            raw_priv,
            f"private {label} staging dir",
            base_dir=base_dir,
            require_dir_components=True,
        ).resolve(strict=True)
        exit_stack.callback(_cleanup_staging_tempdir, tmp_dir, priv_root)
        cleaned = True
        pinned_root, pinned_fd = _begin_pinned_staging_dir_fd(
            exit_stack, priv_root, label
        )
        writable_rel = populate(priv_root, pinned_root)
        if pinned_fd is not None:
            _freeze_staging_dir_from_fd(
                pinned_fd,
                pinned_root,
                label,
                writable_rel=writable_rel,
            )
            st = os.fstat(pinned_fd)
            if not stat.S_ISDIR(st.st_mode) or stat.S_IMODE(st.st_mode) != 0o555:
                raise ValueError(
                    f"{label} staging root permissions altered after freeze: "
                    f"{priv_root}"
                )
        else:
            writable_abs = (
                (priv_root / writable_rel) if writable_rel is not None else None
            )
            _freeze_staging_dir(priv_root, label, writable_dir=writable_abs)
        return pinned_root
    finally:
        if not cleaned:
            _restore_dir_write_perms_top_down(raw_priv)
            tmp_dir.cleanup()


def _freeze_staging_dir_from_fd(
    root_fd: int,
    root_disp: Path,
    label: str,
    *,
    writable_rel: Path | None = None,
) -> None:
    if os.name != "posix":
        _validate_dir_tree_no_links(root_disp, label)
        return
    root_dup = os.dup(root_fd)
    dir_entries: list[tuple[int, Path, Path]] = [(root_dup, Path("."), root_disp)]
    try:
        idx = 0
        while idx < len(dir_entries):
            cur_fd, rel_cur, cur_disp = dir_entries[idx]
            idx += 1
            for name, st in _read_dir_entries_from_fd(cur_fd, label):
                path = cur_disp / name
                if stat.S_ISLNK(st.st_mode):
                    raise ValueError(
                        f"{label} must not contain a symlink: {path}"
                    )
                if stat.S_ISDIR(st.st_mode):
                    child_fd = _open_child_dir_nofollow(
                        cur_fd, name, (st.st_dev, st.st_ino), label
                    )
                    next_rel = (
                        Path(name) if rel_cur == Path(".") else (rel_cur / name)
                    )
                    dir_entries.append((child_fd, next_rel, path))
                elif stat.S_ISREG(st.st_mode):
                    if st.st_nlink > 1:
                        raise _HardlinkedCommandError(
                            f"{label} file must not be a hardlink "
                            f"(nlink={st.st_nlink}): {path}"
                        )
                else:
                    raise ValueError(
                        f"{label} contains non-regular entry: {path}"
                    )
        for dir_fd, rel_cur, _ in reversed(dir_entries):
            mode = (
                0o700
                if writable_rel is not None and rel_cur == writable_rel
                else 0o555
            )
            os.fchmod(dir_fd, mode)
    finally:
        for dir_fd, _, _ in reversed(dir_entries):
            os.close(dir_fd)


def _freeze_staging_dir(
    root: Path, label: str, *, writable_dir: Path | None = None
) -> None:
    if os.name == "posix":
        root_fd = _open_dir_handle_no_symlinks(root, label)
        try:
            writable_rel: Path | None = None
            if writable_dir is not None:
                writable_rel = writable_dir.relative_to(root)
            _freeze_staging_dir_from_fd(
                root_fd, root, label, writable_rel=writable_rel
            )
        finally:
            os.close(root_fd)
    else:
        _validate_dir_tree_no_links(root, label)


def _materialize_immutable_top_level_lib(
    canon_lib: Path,
    label: str,
    *,
    base_dir: Path,
    exit_stack: contextlib.ExitStack,
    tmp_parent: Path | str | None = None,
    include_subdirs: bool = False,
    co_locate_rustc: Path | None = None,
    co_locate_rustc_preopened: _OpenedExecutable | None = None,
) -> Path:
    """Stage `lib/` files (and optional subdirs/`rustc`) into `0o555` root."""
    rustc_target: Path | None = None
    if co_locate_rustc_preopened is not None:
        rustc_target = co_locate_rustc_preopened.path
    elif co_locate_rustc is not None:
        rustc_target = _resolve_cli_path(
            co_locate_rustc, "rustc", base_dir=base_dir
        )

    def _populate_lib(_priv_root: Path, pinned_root: Path) -> None:
        priv_lib = pinned_root / "lib"
        priv_lib.mkdir(mode=0o700)
        if os.name == "posix":
            src_root_fd = _open_dir_handle_no_symlinks(canon_lib, label)
            stack_fd: list[tuple[int | None, tuple[str, ...], Path, Path]] = [
                (None, (), canon_lib, priv_lib)
            ]
            try:
                while stack_fd:
                    cur_fd, rel_parts, cur_disp, cur_dst = stack_fd.pop()
                    active_fd = src_root_fd if cur_fd is None else cur_fd
                    try:
                        entries = _read_dir_entries_from_fd(active_fd, label)
                        for name, st in entries:
                            path = cur_disp / name
                            dst_path = cur_dst / name
                            if stat.S_ISLNK(st.st_mode):
                                if st.st_nlink > 1:
                                    raise _HardlinkedCommandError(
                                        f"{label} symlink must not be a "
                                        f"hardlink (nlink={st.st_nlink}): {path}"
                                    )
                                opened_fd, opened_st = (
                                    _resolve_and_open_confined_lib_symlink_from_fd(
                                        src_root_fd,
                                        active_fd,
                                        rel_parts,
                                        name,
                                        path,
                                        label,
                                    )
                                )
                                try:
                                    _copy_opened_file_to_new_dst(
                                        opened_fd,
                                        opened_st.st_mode,
                                        dst_path,
                                        label,
                                    )
                                finally:
                                    os.close(opened_fd)
                            elif stat.S_ISREG(st.st_mode):
                                opened_fd, opened_st = _open_regular_file_from_fd(
                                    active_fd,
                                    name,
                                    (st.st_dev, st.st_ino),
                                    False,
                                    label,
                                )
                                try:
                                    _copy_opened_file_to_new_dst(
                                        opened_fd,
                                        opened_st.st_mode,
                                        dst_path,
                                        label,
                                    )
                                finally:
                                    os.close(opened_fd)
                            elif stat.S_ISDIR(st.st_mode):
                                if include_subdirs:
                                    dst_path.mkdir(mode=0o700)
                                    child_fd = _open_child_dir_nofollow(
                                        active_fd,
                                        name,
                                        (st.st_dev, st.st_ino),
                                        label,
                                    )
                                    stack_fd.append(
                                        (
                                            child_fd,
                                            (*rel_parts, name),
                                            path,
                                            dst_path,
                                        )
                                    )
                            else:
                                raise ValueError(
                                    f"{label} contains non-regular entry: {path}"
                                )
                    finally:
                        if cur_fd is not None:
                            os.close(cur_fd)
            finally:
                while stack_fd:
                    leftover_fd, _, _, _ = stack_fd.pop()
                    if leftover_fd is not None:
                        os.close(leftover_fd)
                os.close(src_root_fd)
        else:
            stack: list[tuple[Path, Path]] = [(canon_lib, priv_lib)]
            while stack:
                cur_src, cur_dst = stack.pop()
                with os.scandir(cur_src) as it:
                    entries = sorted(it, key=lambda e: e.name)
                for entry in entries:
                    path = Path(entry.path)
                    st = os.lstat(path)
                    dst_path = cur_dst / entry.name
                    if stat.S_ISLNK(st.st_mode):
                        if st.st_nlink > 1:
                            raise _HardlinkedCommandError(
                                f"{label} symlink must not be a hardlink "
                                f"(nlink={st.st_nlink}): {path}"
                            )
                        target = _resolve_confined_lib_symlink(
                            canon_lib, cur_src, path, label
                        )
                        _copy_verified_regular_file(target, dst_path, label)
                    elif stat.S_ISREG(st.st_mode):
                        _copy_verified_regular_file(path, dst_path, label)
                    elif stat.S_ISDIR(st.st_mode):
                        if include_subdirs:
                            dst_path.mkdir(mode=0o700)
                            stack.append((path, dst_path))
                    else:
                        raise ValueError(
                            f"{label} contains non-regular entry: {path}"
                        )
        if rustc_target is not None:
            iso_dir = pinned_root / ".anneal-isolated-bins"
            iso_dir.mkdir(mode=0o700)
            _materialize_cargo_built_executable(
                rustc_target,
                pinned_root,
                "rustc",
                dest_dir=iso_dir,
                force_copy=True,
                chmod_mode=0o555,
                allow_cargo_deps_hardlink=False,
                preserve_bin_name=True,
                preopened=co_locate_rustc_preopened,
                dest_is_pinned=True,
            )

    dir_arg = str(tmp_parent) if tmp_parent is not None else None
    pinned_root = _build_pinned_staging_dir(
        exit_stack,
        prefix="anneal-tc-lib-",
        base_dir=base_dir,
        tmp_parent=dir_arg,
        label=label,
        populate=_populate_lib,
    )
    return pinned_root / "lib"


def _verify_pinned_proc_fd_executable(
    bin_path: Path,
    label: str,
    *,
    allow_cargo_deps_hardlink: bool = False,
) -> None:
    """Verify `/proc/self/fd/<fd>/<rel>` traverses frozen dirs to a file."""
    if not sys.platform.startswith("linux"):
        return
    try:
        rel_proc = bin_path.relative_to(Path("/proc/self/fd"))
    except ValueError as exc:
        raise ValueError(
            f"{label} must be rooted under /proc/self/fd/: {bin_path}"
        ) from exc
    parts = [p for p in rel_proc.parts if p != "."]
    if ".." in parts or len(parts) < 2:
        raise ValueError(
            f"{label} pinned fd path must identify a dir fd and file: {bin_path}"
        )
    fd_str = parts[0]
    if not fd_str.isdigit():
        raise ValueError(
            f"{label} pinned fd segment must be numeric: {bin_path}"
        )
    fd = int(fd_str)
    if fd <= 2:
        raise ValueError(
            f"{label} pinned fd must not target stdio descriptor {fd}: {bin_path}"
        )
    euid = os.geteuid()

    def _assert_frozen_entry(
        st: os.stat_result, desc: str | Path, *, expect_dir: bool
    ) -> None:
        if expect_dir and not stat.S_ISDIR(st.st_mode):
            raise ValueError(
                f"{label} pinned fd target is not a directory: {desc}"
            )
        if st.st_uid != euid:
            raise ValueError(
                f"{label} pinned entry owner {st.st_uid} != euid {euid}: {desc}"
            )
        if stat.S_IMODE(st.st_mode) & 0o222:
            raise ValueError(
                f"{label} pinned entry must be frozen non-writable "
                f"(mode {stat.S_IMODE(st.st_mode):04o}): {desc}"
            )

    try:
        root_st = os.fstat(fd)
    except OSError as exc:
        raise ValueError(
            f"{label} pinned descriptor fd {fd} is unavailable ({bin_path}): {exc}"
        ) from exc
    _assert_frozen_entry(root_st, f"/proc/self/fd/{fd}", expect_dir=True)

    cur_fd = fd
    opened_dirs: list[int] = []
    try:
        for seg in parts[1:-1]:
            next_fd = _open_child_dir_nofollow(cur_fd, seg, None, label)
            opened_dirs.append(next_fd)
            cur_fd = next_fd
            _assert_frozen_entry(os.fstat(cur_fd), bin_path, expect_dir=True)
        leaf_fd, leaf_st = _open_regular_file_from_fd(
            cur_fd,
            parts[-1],
            None,
            allow_cargo_deps_hardlink,
            label,
        )
        try:
            _assert_frozen_entry(leaf_st, bin_path, expect_dir=False)
            if (stat.S_IMODE(leaf_st.st_mode) & 0o111) == 0:
                raise ValueError(
                    f"{label} pinned executable is not executable "
                    f"(mode {stat.S_IMODE(leaf_st.st_mode):04o}): {bin_path}"
                )
        finally:
            os.close(leaf_fd)
    finally:
        for d_fd in reversed(opened_dirs):
            _close_fd_quiet(d_fd)


def _validate_pre_staged_executable(
    bin_path: Path,
    bin_name: str,
    label: str,
    *,
    base_dir: Path,
    allow_cargo_deps_hardlink: bool = False,
) -> Path:
    """Validate a pre-staged executable (store-contained or `/proc/self/fd`)."""
    store_cand = _resolve_store_contained_entry(
        bin_path, bin_name, base_dir=base_dir
    )
    if store_cand is not None:
        return store_cand
    if sys.platform.startswith("linux"):
        if not _extract_proc_fd_numbers([str(bin_path)]):
            raise ValueError(
                f"pre-staged {bin_name} missing live fd handle: {bin_path}"
            )
        _verify_pinned_proc_fd_executable(
            bin_path,
            label,
            allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
        )
        return bin_path
    return _resolve_executable_cli_path(
        bin_path,
        label,
        base_dir=base_dir,
        allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
    )


def _stage_verified_executable(
    bin_path: Path,
    bin_name: str,
    *,
    allow_cargo_deps_hardlink: bool,
    exit_stack: contextlib.ExitStack,
    base_dir: Path,
    tmp_parent: str | None = None,
    store_prefix: Path | None = None,
    preserve_bin_name: bool = False,
    pin_proc_fd: bool = True,
    preopened: _OpenedExecutable | None = None,
) -> Path:
    """Stage a verified non-store executable inside a private `0o555` dir."""
    eff_store = _STORE_PREFIX if store_prefix is None else store_prefix
    if preopened is not None:
        if preopened.fd is None and preopened.st is None:
            return preopened.path
        opened_bin = preopened
    else:
        store_cand = _resolve_store_contained_entry(
            bin_path,
            bin_name,
            store_prefix=eff_store,
            base_dir=base_dir,
        )
        if store_cand is not None:
            return store_cand
        opened_bin = _open_verified_executable_via_dirfd(
            bin_path,
            base_dir,
            reject_hardlinks=True,
            allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
            label=bin_name,
            exit_stack=exit_stack,
        )
    staged_name: str | None = None

    def _populate_bin(_priv_root: Path, pinned_root: Path) -> None:
        nonlocal staged_name
        iso_dir = pinned_root / ".anneal-isolated-bins"
        iso_dir.mkdir(mode=0o700)
        staged_bin = _materialize_cargo_built_executable(
            opened_bin.path,
            pinned_root,
            bin_name,
            dest_dir=iso_dir,
            force_copy=True,
            chmod_mode=0o555,
            allow_cargo_deps_hardlink=allow_cargo_deps_hardlink,
            preserve_bin_name=preserve_bin_name,
            preopened=opened_bin,
            dest_is_pinned=True,
        )
        staged_name = staged_bin.name

    pinned_root = _build_pinned_staging_dir(
        exit_stack,
        prefix=f"anneal-stage-{bin_name}-",
        base_dir=base_dir,
        tmp_parent=tmp_parent,
        label=f"staged {bin_name}",
        populate=_populate_bin,
    )
    assert staged_name is not None
    pinned_bin = pinned_root / ".anneal-isolated-bins" / staged_name
    if sys.platform.startswith("linux"):
        _verify_pinned_proc_fd_executable(
            pinned_bin,
            f"staged {bin_name}",
            allow_cargo_deps_hardlink=False,
        )
    if pin_proc_fd:
        return pinned_bin
    return pinned_bin.resolve(strict=True)


def _validate_sysroot_lib_dir_path(
    lib_dir: Path,
    label: str,
    *,
    base_dir: Path,
    exit_stack: contextlib.ExitStack,
    store_prefix: Path = _STORE_PREFIX,
    tmp_parent: Path | str | None = None,
    include_subdirs: bool = False,
    co_locate_rustc: Path | None = None,
    co_locate_rustc_preopened: _OpenedExecutable | None = None,
) -> Path | None:
    """Validate `lib/`, returning store path or private immutable stage."""
    try:
        os.lstat(lib_dir)
    except FileNotFoundError:
        return None
    except OSError as exc:
        raise ValueError(f"cannot inspect {label} {lib_dir}: {exc}") from exc

    store_lib = _resolve_store_contained_entry(
        lib_dir,
        label,
        base_dir=base_dir,
        expect_dir=True,
        store_prefix=store_prefix,
    )
    if store_lib is not None:
        _validate_store_contained_dir_tree(
            store_lib,
            store_prefix=store_prefix,
            base_dir=base_dir,
            label=label,
        )
        return store_lib

    canon_lib = _resolve_cli_path(
        lib_dir,
        label,
        base_dir=base_dir,
        require_dir_components=True,
    ).resolve(strict=True)
    _inspect_sysroot_lib_dir_tree(
        canon_lib, label, allow_confined_symlinks=True
    )
    non_store_rustc: Path | None = None
    non_store_rustc_preopened: _OpenedExecutable | None = None
    if co_locate_rustc_preopened is not None:
        if (
            not (
                co_locate_rustc_preopened.fd is None
                and co_locate_rustc_preopened.st is None
            )
            and _resolve_store_contained_entry(
                co_locate_rustc_preopened.path,
                "rustc",
                store_prefix=store_prefix,
                base_dir=base_dir,
            )
            is None
        ):
            non_store_rustc = co_locate_rustc_preopened.path
            non_store_rustc_preopened = co_locate_rustc_preopened
    elif co_locate_rustc is not None:
        if (
            _resolve_store_contained_entry(
                co_locate_rustc,
                "rustc",
                store_prefix=store_prefix,
                base_dir=base_dir,
            )
            is None
        ):
            non_store_rustc = co_locate_rustc
    return _materialize_immutable_top_level_lib(
        canon_lib,
        label,
        base_dir=base_dir,
        exit_stack=exit_stack,
        tmp_parent=tmp_parent,
        include_subdirs=include_subdirs,
        co_locate_rustc=non_store_rustc,
        co_locate_rustc_preopened=non_store_rustc_preopened,
    )


def _validate_rustc_sysroot_lib_dir(
    rustc_bin: Path,
    *,
    base_dir: Path,
    exit_stack: contextlib.ExitStack,
    store_prefix: Path = _STORE_PREFIX,
    tmp_parent: Path | str | None = None,
    include_subdirs: bool = False,
    co_locate_rustc: Path | None = None,
    co_locate_rustc_preopened: _OpenedExecutable | None = None,
) -> Path | None:
    prefix = rustc_bin.parent.parent
    return _validate_sysroot_lib_dir_path(
        prefix / "lib",
        "Cargo RUSTC sysroot lib",
        base_dir=base_dir,
        exit_stack=exit_stack,
        store_prefix=store_prefix,
        tmp_parent=tmp_parent,
        include_subdirs=include_subdirs,
        co_locate_rustc=co_locate_rustc,
        co_locate_rustc_preopened=co_locate_rustc_preopened,
    )


def _canonical_dirs_set(
    dirs: tuple[Path, ...], base_dir: Path
) -> set[Path]:
    out: set[Path] = set()
    for d in dirs:
        try:
            canon = _resolve_cli_path(
                d,
                "trusted linker directory",
                base_dir=base_dir,
                require_dir_components=True,
            ).resolve(strict=True)
            out.add(canon)
        except (OSError, ValueError):
            continue
    return out


def _validate_bounded_system_file(
    cand: Path,
    *,
    trusted_dirs: tuple[Path, ...],
    symlink_dirs: tuple[Path, ...],
    base_dir: Path,
    label: str,
) -> Path:
    trusted_set = _canonical_dirs_set(trusted_dirs, base_dir)
    sym_set = _canonical_dirs_set(symlink_dirs, base_dir)
    cur = cand
    for _ in range(_MAX_LINKER_SYMLINK_HOPS):
        parent = cur.parent
        canon_parent = _resolve_cli_path(
            parent, label, base_dir=base_dir, require_dir_components=True
        ).resolve(strict=True)
        try:
            st = os.lstat(cur)
        except OSError as exc:
            raise ValueError(f"cannot inspect {label} {cur}: {exc}") from exc
        if st.st_nlink > 1:
            raise _HardlinkedCommandError(
                f"{label} must not be a hardlink (nlink={st.st_nlink}): {cur}"
            )
        if not stat.S_ISLNK(st.st_mode):
            if canon_parent not in trusted_set:
                raise ValueError(
                    f"{label} target escaped trusted system directories: {cur}"
                )
            return _resolve_executable_cli_path(cur, label, base_dir=base_dir)
        if canon_parent not in trusted_set and canon_parent not in sym_set:
            raise ValueError(
                f"{label} symlink escaped trusted system directories: {cur}"
            )
        target = Path(os.readlink(cur))
        if ".." in target.parts:
            raise ValueError(
                f"{label} symlink target must not contain '..': {cur} -> {target}"
            )
        next_path = target if target.is_absolute() else (parent / target)
        next_parent = next_path.parent
        canon_next_parent = _resolve_cli_path(
            next_parent, label, base_dir=base_dir, require_dir_components=True
        ).resolve(strict=True)
        if canon_next_parent not in trusted_set and canon_next_parent not in sym_set:
            raise ValueError(
                f"{label} symlink target escaped trusted directories: "
                f"{cur} -> {next_path}"
            )
        cur = next_path
    raise ValueError(
        f"{label} exceeded {_MAX_LINKER_SYMLINK_HOPS} symlink hops: {cand}"
    )


def _validate_trusted_system_linker(
    *,
    trusted_dirs: tuple[Path, ...],
    symlink_dirs: tuple[Path, ...],
    base_dir: Path,
) -> Path | None:
    for directory in trusted_dirs:
        cand = directory / _LINKER_BIN_NAME
        try:
            os.lstat(cand)
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise ValueError(
                f"cannot inspect trusted Cargo linker {cand}: {exc}"
            ) from exc
        return _validate_bounded_system_file(
            cand,
            trusted_dirs=trusted_dirs,
            symlink_dirs=symlink_dirs,
            base_dir=base_dir,
            label="Cargo linker binary",
        )
    return None


def _validate_store_linker_from_path(
    ambient_path: str | None,
    *,
    base_dir: Path,
    store_prefix: Path = _STORE_PREFIX,
) -> Path | None:
    if not ambient_path:
        return None
    for raw_dir in ambient_path.split(os.pathsep):
        if not raw_dir:
            continue
        d = Path(raw_dir)
        if not d.is_absolute() or ".." in d.parts:
            continue
        cand = d / _LINKER_BIN_NAME
        try:
            os.lstat(cand)
        except FileNotFoundError:
            continue
        except OSError as exc:
            raise ValueError(
                f"cannot inspect store Cargo linker {cand}: {exc}"
            ) from exc
        store_cand = _resolve_store_contained_entry(
            cand,
            "Cargo linker binary",
            store_prefix=store_prefix,
            base_dir=base_dir,
        )
        if store_cand is not None:
            return store_cand
    return None


def _resolve_validated_linker(
    rustc_bin: Path,
    base_dir: Path,
    ambient_path: str | None,
    *,
    store_prefix: Path = _STORE_PREFIX,
    trusted_dirs: tuple[Path, ...] = _TRUSTED_LINKER_DIRS,
    symlink_dirs: tuple[Path, ...] = _TRUSTED_LINKER_SYMLINK_DIRS,
) -> Path:
    """Resolve and validate the host C linker without trusting ambient PATH."""
    is_store_rustc = rustc_bin == store_prefix or rustc_bin.is_relative_to(
        store_prefix
    )
    if is_store_rustc:
        linker = _validate_store_linker_from_path(
            ambient_path, base_dir=base_dir, store_prefix=store_prefix
        )
        if linker is not None:
            return linker
        linker = _validate_trusted_system_linker(
            trusted_dirs=trusted_dirs,
            symlink_dirs=symlink_dirs,
            base_dir=base_dir,
        )
        if linker is not None:
            return linker
    else:
        linker = _validate_trusted_system_linker(
            trusted_dirs=trusted_dirs,
            symlink_dirs=symlink_dirs,
            base_dir=base_dir,
        )
        if linker is not None:
            return linker
        linker = _validate_store_linker_from_path(
            ambient_path, base_dir=base_dir, store_prefix=store_prefix
        )
        if linker is not None:
            return linker
    raise ValueError(
        f"cannot resolve validated Cargo linker (`{_LINKER_BIN_NAME}`) in "
        "trusted system directories or Nix store"
    )


def _build_minimal_toolchain_path(
    primary_bins: tuple[Path, ...],
    linker: Path,
    ambient_path: str | None,
    base_dir: Path,
    *,
    extra_dirs: tuple[Path, ...] = (),
    store_prefix: Path = _STORE_PREFIX,
    trusted_child_dirs: tuple[Path, ...] = _TRUSTED_CHILD_PATH_DIRS,
) -> str:
    """Construct a minimal `PATH` containing only validated toolchain dirs."""
    seen: set[Path] = set()
    entries: list[str] = []

    def _push(d: Path) -> None:
        if d not in seen:
            seen.add(d)
            entries.append(str(d))

    for bin_path in primary_bins:
        _push(bin_path.parent)
    _push(linker.parent)

    uses_store = any(
        p.is_relative_to(store_prefix) for p in (*primary_bins, linker)
    )
    if uses_store and ambient_path:
        try:
            canon_store = _resolve_cli_path(
                store_prefix,
                "store root",
                base_dir=base_dir,
                require_dir_components=True,
            ).resolve(strict=True)
        except (OSError, ValueError):
            canon_store = None
        if canon_store is not None:
            for raw_dir in ambient_path.split(os.pathsep):
                if not raw_dir:
                    continue
                d = Path(raw_dir)
                if not d.is_absolute() or ".." in d.parts:
                    continue
                if d != store_prefix and d.is_relative_to(store_prefix):
                    try:
                        os.lstat(d)
                    except FileNotFoundError:
                        continue
                    except OSError as exc:
                        raise ValueError(
                            f"cannot inspect store PATH entry {d}: {exc}"
                        ) from exc
                    store_dir = _resolve_store_contained_entry(
                        d,
                        "store PATH entry",
                        store_prefix=store_prefix,
                        base_dir=base_dir,
                        expect_dir=True,
                    )
                    if store_dir is not None:
                        _push(store_dir)

    for extra_dir in extra_dirs:
        _push(extra_dir)

    for trusted_dir in trusted_child_dirs:
        try:
            st = os.lstat(trusted_dir)
        except FileNotFoundError:
            continue
        except OSError:
            continue
        if not stat.S_ISLNK(st.st_mode) and stat.S_ISDIR(st.st_mode):
            canon_td = _resolve_cli_path(
                trusted_dir,
                "trusted child PATH dir",
                base_dir=base_dir,
                require_dir_components=True,
            )
            _push(canon_td)

    return os.pathsep.join(entries)


def _toml_basic_string(val: str) -> str:
    if "\n" in val or "\r" in val or "\0" in val:
        raise ValueError(f"unsafe control character in TOML config value: {val!r}")
    return json.dumps(val)


def _open_tool_or_rustup_proxy(
    raw_cmd: str,
    tool_name: str,
    base_dir: Path,
    *,
    store_prefix: Path,
    exit_stack: contextlib.ExitStack,
) -> _OpenedExecutable:
    raw_path = Path(raw_cmd)
    if ".." not in raw_path.parts:
        store_cand = _resolve_store_contained_entry(
            raw_path, tool_name, store_prefix=store_prefix, base_dir=base_dir
        )
        if store_cand is not None:
            return _OpenedExecutable(path=store_cand, fd=None, st=None, parent_fd=None)
    anchored = raw_path if raw_path.is_absolute() else (base_dir.absolute() / raw_path)
    if _is_rustup_proxy_symlink(anchored):
        proxy_dir = _resolve_cli_path(
            raw_path.parent,
            f"{tool_name} proxy dir",
            base_dir=base_dir,
            require_dir_components=True,
        ).resolve(strict=True)
        proxy_cand = proxy_dir / raw_path.name
        if not _is_rustup_proxy_symlink(proxy_cand):
            raise ValueError(
                f"{tool_name} rustup proxy changed during validation: {proxy_cand}"
            )
        opened_rustup = _open_verified_executable_via_dirfd(
            proxy_dir / "rustup",
            base_dir,
            reject_hardlinks=True,
            label=f"{tool_name} rustup proxy",
            exit_stack=exit_stack,
        )
        return _OpenedExecutable(
            path=proxy_cand,
            fd=opened_rustup.fd,
            st=opened_rustup.st,
            parent_fd=opened_rustup.parent_fd,
            is_rustup_proxy=True,
        )
    return _open_store_aware_executable(
        raw_path,
        tool_name,
        base_dir=base_dir,
        store_prefix=store_prefix,
        exit_stack=exit_stack,
    )


def _pin_cargo_rustc_env(
    env: dict[str, str],
    caller_cwd: Path,
    cargo: str,
    *,
    exit_stack: contextlib.ExitStack,
    work_dir: Path | None = None,
    orig_work_dir: Path | None = None,
    cargo_opened: _OpenedExecutable | None = None,
    preserve_rustup_dir: bool = False,
    cargo_home_pinned: bool = False,
    locked_crates: tuple[tuple[str, str, str | None], ...] = (),
    lockfile_dir: Path | None = None,
    store_prefix: Path = _STORE_PREFIX,
    trusted_linker_dirs: tuple[Path, ...] = _TRUSTED_LINKER_DIRS,
    trusted_linker_symlink_dirs: tuple[Path, ...] = _TRUSTED_LINKER_SYMLINK_DIRS,
    trusted_child_dirs: tuple[Path, ...] = _TRUSTED_CHILD_PATH_DIRS,
) -> tuple[str, list[str]]:
    """Resolve real toolchain bins + linker and sanitize child `PATH`."""
    probe_cwd = caller_cwd if work_dir is None else work_dir
    anchor_work = probe_cwd if orig_work_dir is None else orig_work_dir
    ambient_path = env.get("PATH")
    resolved_cargo = cargo_opened
    if resolved_cargo is None:
        resolved_cargo = _open_tool_or_rustup_proxy(
            cargo,
            "cargo",
            caller_cwd,
            store_prefix=store_prefix,
            exit_stack=exit_stack,
        )
    elif (
        store_prefix != _STORE_PREFIX
        and resolved_cargo.fd is not None
        and ".." not in resolved_cargo.path.parts
    ):
        store_cand = _resolve_store_contained_entry(
            resolved_cargo.path, "cargo", store_prefix=store_prefix, base_dir=caller_cwd
        )
        if store_cand is not None:
            resolved_cargo = _OpenedExecutable(
                path=store_cand, fd=None, st=None, parent_fd=None
            )
    env["CARGO"] = str(resolved_cargo.path)

    rustc_opened: _OpenedExecutable | None = None
    raw_rustc = env.get("RUSTC")
    if not raw_rustc:
        rustc_opened = _resolve_command_from_path_opened(
            "rustc",
            caller_cwd,
            allow_rustup_proxy=True,
            store_prefix=store_prefix,
            path_var=ambient_path,
            exit_stack=exit_stack,
        )
        if rustc_opened is not None:
            env["RUSTC"] = str(rustc_opened.path)
    else:
        rustc_opened = _open_tool_or_rustup_proxy(
            raw_rustc,
            "rustc",
            caller_cwd,
            store_prefix=store_prefix,
            exit_stack=exit_stack,
        )

    uses_proxy = resolved_cargo.is_rustup_proxy or (
        rustc_opened is not None and rustc_opened.is_rustup_proxy
    )
    if uses_proxy:
        _pin_rustup_settings(env, caller_cwd, anchor_work, exit_stack)
    if not cargo_home_pinned:
        _pin_cargo_home_configs_env(
            env,
            caller_cwd,
            exit_stack=exit_stack,
            store_prefix=store_prefix,
            locked_crates=locked_crates,
            lockfile_dir=lockfile_dir,
        )

    rustup_dirs: list[Path] = []
    if resolved_cargo.is_rustup_proxy:
        pinned_cargo_opened = _resolve_rustup_proxy_binary_opened(
            resolved_cargo.path,
            "cargo",
            work_dir=probe_cwd,
            env=env,
            base_dir=caller_cwd,
            exit_stack=exit_stack,
            store_prefix=store_prefix,
            preopened_rustup=resolved_cargo,
            orig_work_dir=anchor_work,
            rustup_settings_pinned=True,
        )
        rustup_dirs.append(resolved_cargo.path.parent.resolve(strict=True))
    else:
        pinned_cargo_opened = resolved_cargo

    if rustc_opened is not None:
        if rustc_opened.is_rustup_proxy:
            pinned_rustc_opened = _resolve_rustup_proxy_binary_opened(
                rustc_opened.path,
                "rustc",
                work_dir=probe_cwd,
                env=env,
                base_dir=caller_cwd,
                exit_stack=exit_stack,
                store_prefix=store_prefix,
                preopened_rustup=rustc_opened,
                orig_work_dir=anchor_work,
                rustup_settings_pinned=True,
            )
            rustup_dirs.append(rustc_opened.path.parent.resolve(strict=True))
        else:
            pinned_rustc_opened = rustc_opened
    elif resolved_cargo.is_rustup_proxy:
        pinned_rustc_opened = _resolve_rustup_proxy_binary_opened(
            resolved_cargo.path,
            "rustc",
            work_dir=probe_cwd,
            env=env,
            base_dir=caller_cwd,
            exit_stack=exit_stack,
            store_prefix=store_prefix,
            preopened_rustup=resolved_cargo,
            orig_work_dir=anchor_work,
            rustup_settings_pinned=True,
        )
        rustup_dirs.append(resolved_cargo.path.parent.resolve(strict=True))
    else:
        raise ValueError("cannot resolve validated RUSTC binary for Cargo build")

    if preserve_rustup_dir and not rustup_dirs and ambient_path:
        rustup_cmd = _resolve_command_from_path(
            "rustup",
            caller_cwd,
            allow_rustup_proxy=False,
            store_prefix=store_prefix,
            path_var=ambient_path,
        )
        if rustup_cmd is not None:
            rustup_dirs.append(Path(rustup_cmd).parent.resolve(strict=True))

    sysroot_lib = _validate_rustc_sysroot_lib_dir(
        pinned_rustc_opened.path,
        base_dir=caller_cwd,
        exit_stack=exit_stack,
        store_prefix=store_prefix,
        tmp_parent=env.get("TMPDIR"),
        include_subdirs=True,
        co_locate_rustc=pinned_rustc_opened.path,
        co_locate_rustc_preopened=pinned_rustc_opened,
    )
    if sysroot_lib is not None:
        env["LD_LIBRARY_PATH"] = str(sysroot_lib)

    linker = _resolve_validated_linker(
        pinned_rustc_opened.path,
        caller_cwd,
        ambient_path,
        store_prefix=store_prefix,
        trusted_dirs=trusted_linker_dirs,
        symlink_dirs=trusted_linker_symlink_dirs,
    )
    staged_cargo = _stage_verified_executable(
        pinned_cargo_opened.path,
        "cargo",
        allow_cargo_deps_hardlink=False,
        exit_stack=exit_stack,
        base_dir=caller_cwd,
        tmp_parent=env.get("TMPDIR"),
        store_prefix=store_prefix,
        preserve_bin_name=True,
        preopened=pinned_cargo_opened,
    )
    co_located_rustc = (
        sysroot_lib.parent / ".anneal-isolated-bins" / "rustc"
        if sysroot_lib is not None
        and sysroot_lib != store_prefix
        and not sysroot_lib.is_relative_to(store_prefix)
        else None
    )
    if co_located_rustc is not None and co_located_rustc.is_file():
        staged_rustc = co_located_rustc
    else:
        staged_rustc = _stage_verified_executable(
            pinned_rustc_opened.path,
            "rustc",
            allow_cargo_deps_hardlink=False,
            exit_stack=exit_stack,
            base_dir=caller_cwd,
            tmp_parent=env.get("TMPDIR"),
            store_prefix=store_prefix,
            preserve_bin_name=True,
            preopened=pinned_rustc_opened,
        )
    env["CARGO"] = str(staged_cargo)
    env["RUSTC"] = str(staged_rustc)
    # Place validated rustup dir after pinned toolchain bins so `cargo`/
    # `rustc` hit pinned binaries while `anneal-diff` can invoke `rustup`.
    env["PATH"] = _build_minimal_toolchain_path(
        (staged_rustc, staged_cargo),
        linker,
        ambient_path,
        caller_cwd,
        extra_dirs=tuple(rustup_dirs) if preserve_rustup_dir else (),
        store_prefix=store_prefix,
        trusted_child_dirs=trusted_child_dirs,
    )
    linker_cfg = f'target."cfg(all())".linker={_toml_basic_string(str(linker))}'
    return str(staged_cargo), ["--config", linker_cfg]


def _run_anneal_diff_proc(
    cmd: list[str],
    *,
    subcmd: str,
    cwd: Path,
    env: dict[str, str],
    timeout_secs: float,
) -> tuple[int, dict[str, Any]]:
    label = "anneal-diff fuzz" if subcmd == "fuzz" else "anneal-diff"
    try:
        proc = _run_subcommand_process_group(
            cmd,
            cwd=cwd,
            env=env,
            timeout_secs=timeout_secs,
        )
    except subprocess.TimeoutExpired as exc:
        tail = _format_timeout_tail(exc)
        detail = f"{label} timed out after {timeout_secs:g}s"
        if tail:
            detail = f"{detail}: {tail}"
        if subcmd == "fuzz":
            return (
                1,
                {
                    "schema": FUZZ_SCHEMA,
                    "mir_dialect": "profile_v1",
                    "timed_out": True,
                    "timeout_secs": float(timeout_secs),
                    "error": detail,
                    "gate_error": detail,
                },
            )
        raise RuntimeError(detail) from exc
    stdout = proc.stdout.strip()
    if not stdout:
        raise RuntimeError(
            f"{label} produced no JSON stdout (rc={proc.returncode}): "
            f"{proc.stderr}"
        )
    parsed = json.loads(stdout, parse_constant=_reject_json_constant)
    if not isinstance(parsed, dict):
        raise ValueError(f"{label} JSON stdout must be a JSON object")
    if "timed_out" in parsed:
        raise ValueError(
            f"{label} JSON stdout must not contain untrusted 'timed_out' field"
        )
    return proc.returncode, parsed


def _run_anneal_diff_subcommand(
    *,
    subcmd: str,
    anneal_root: Path,
    capture_bin: Path | None,
    mir_eval_bin: Path | None,
    cache_root: Path | None,
    anneal_diff_bin: Path | None,
    extra_args: list[str],
    timeout_secs: float = ANNEAL_DIFF_SUBCOMMAND_TIMEOUT_SECS,
    _anneal_diff_pre_staged: bool = False,
    _capture_opened: _OpenedExecutable | None = None,
    _capture_pre_staged: bool = False,
    _mir_eval_pre_staged: bool = False,
    _pre_staged_capture_env: dict[str, Path] | None = None,
) -> tuple[int, dict[str, Any]]:
    if (
        isinstance(timeout_secs, bool)
        or not isinstance(timeout_secs, (int, float))
        or not math.isfinite(timeout_secs)
        or timeout_secs <= 0
    ):
        raise ValueError(f"invalid subcommand timeout: {timeout_secs!r}")
    caller_cwd = Path.cwd()
    anneal_root_canon = _resolve_cli_path(
        anneal_root, "anneal_root", base_dir=caller_cwd
    ).resolve(strict=True)
    default_roots = (
        _workspace_target_roots(anneal_root_canon)
        if anneal_diff_bin is None
        else ()
    )
    with contextlib.ExitStack() as cleanup:
        pinned_ch: Path | None = None
        if anneal_diff_bin is None:
            pinned_ch = _reject_ambient_cargo_configs(
                anneal_root_canon,
                default_roots,
                base_dir=caller_cwd,
                exit_stack=cleanup,
                lockfile_dir=anneal_root_canon,
            )
        child_env = _build_child_env(
            caller_cwd,
            default_target_roots=default_roots,
            exit_stack=cleanup,
            _pre_staged_capture_env=_pre_staged_capture_env,
        )
        if pinned_ch is not None:
            child_env["CARGO_HOME"] = str(pinned_ch)
        validated_tmp = _validate_child_tmpdir(child_env, caller_cwd)
        tmp_parent = str(validated_tmp) if validated_tmp is not None else None
        tail_args = list(extra_args)
        if capture_bin is not None:
            if _capture_pre_staged:
                capture_abs = _validate_pre_staged_executable(
                    capture_bin,
                    "anneal-rustc-capture",
                    "capture binary",
                    base_dir=caller_cwd,
                )
            else:
                cap_opened = (
                    _capture_opened
                    if _capture_opened is not None
                    else _open_store_aware_executable(
                        capture_bin,
                        "capture binary",
                        base_dir=caller_cwd,
                        allow_cargo_deps_hardlink=True,
                        exit_stack=cleanup,
                    )
                )
                capture_abs = _maybe_stage_cargo_hardlink_executable(
                    cap_opened.path,
                    "anneal-rustc-capture",
                    exit_stack=cleanup,
                    base_dir=caller_cwd,
                    tmp_parent=tmp_parent,
                    preopened=cap_opened,
                )
            tail_args.extend(["--capture-bin", str(capture_abs)])
        if mir_eval_bin is not None:
            if _mir_eval_pre_staged:
                mir_eval_abs = _validate_pre_staged_executable(
                    mir_eval_bin,
                    "anneal-mir-eval",
                    "mir-eval binary",
                    base_dir=caller_cwd,
                )
            else:
                opened_mir_eval = _open_store_aware_executable(
                    mir_eval_bin,
                    "mir-eval binary",
                    base_dir=caller_cwd,
                    allow_cargo_deps_hardlink=False,
                    exit_stack=cleanup,
                )
                mir_eval_abs = _stage_verified_executable(
                    opened_mir_eval.path,
                    "anneal-mir-eval",
                    allow_cargo_deps_hardlink=False,
                    exit_stack=cleanup,
                    base_dir=caller_cwd,
                    tmp_parent=tmp_parent,
                    preopened=opened_mir_eval,
                )
            tail_args.extend(["--mir-eval-bin", str(mir_eval_abs)])
        if cache_root is not None:
            cache_abs = _resolve_cli_path(
                cache_root, "cache root", base_dir=caller_cwd
            )
            tail_args.extend(["--cache-root", str(cache_abs)])
        if anneal_diff_bin is not None:
            if _anneal_diff_pre_staged:
                staged_diff_bin = _validate_pre_staged_executable(
                    anneal_diff_bin,
                    "anneal-diff",
                    "anneal-diff binary",
                    base_dir=caller_cwd,
                )
            else:
                opened_diff = _open_store_aware_executable(
                    anneal_diff_bin,
                    "anneal-diff binary",
                    base_dir=caller_cwd,
                    allow_cargo_deps_hardlink=True,
                    exit_stack=cleanup,
                )
                staged_diff_bin = _stage_verified_executable(
                    opened_diff.path,
                    "anneal-diff",
                    allow_cargo_deps_hardlink=True,
                    exit_stack=cleanup,
                    base_dir=caller_cwd,
                    tmp_parent=tmp_parent,
                    preopened=opened_diff,
                )
            return _run_anneal_diff_proc(
                [str(staged_diff_bin), subcmd, "--json", *tail_args],
                subcmd=subcmd,
                cwd=anneal_root_canon,
                env=child_env,
                timeout_secs=timeout_secs,
            )

        cargo_opened = _resolve_cargo_command_opened(caller_cwd, cleanup)
        cargo, linker_cfg_args = _pin_cargo_rustc_env(
            child_env,
            caller_cwd,
            str(cargo_opened.path),
            exit_stack=cleanup,
            work_dir=anneal_root_canon,
            orig_work_dir=anneal_root_canon,
            cargo_opened=cargo_opened,
            preserve_rustup_dir=True,
            cargo_home_pinned=pinned_ch is not None,
        )
        # Build in a fresh private 0o700 target directory rather than reusing
        # workspace `target/` or ambient `CARGO_TARGET_DIR`.
        child_env.pop("CARGO_TARGET_DIR", None)
        raw_priv_td = cleanup.enter_context(
            tempfile.TemporaryDirectory(
                prefix="anneal-diff-target-", dir=tmp_parent
            )
        )
        if os.name == "posix":
            os.chmod(raw_priv_td, 0o700)
        priv_td = _resolve_cli_path(
            Path(raw_priv_td),
            "private Cargo target dir",
            base_dir=caller_cwd,
            require_dir_components=True,
        ).resolve(strict=True)
        cmd = [
            cargo,
            "run",
            "--locked",
            "-q",
            "-p",
            "anneal-differential-tests",
            "--bin",
            "anneal-diff",
            "--target-dir",
            str(priv_td),
            "--config",
            'build.rustc-wrapper=""',
            "--config",
            'build.rustc-workspace-wrapper=""',
            *linker_cfg_args,
            "--",
            subcmd,
            "--json",
            *tail_args,
        ]
        return _run_anneal_diff_proc(
            cmd,
            subcmd=subcmd,
            cwd=anneal_root_canon,
            env=child_env,
            timeout_secs=timeout_secs,
        )


def run_anneal_diff(
    *,
    anneal_root: Path,
    manifest: Path | None,
    capture_bin: Path | None,
    mir_eval_bin: Path | None,
    cache_root: Path | None,
    self_check_oracle: bool,
    anneal_diff_bin: Path | None = None,
    timeout_secs: float = ANNEAL_DIFF_SUBCOMMAND_TIMEOUT_SECS,
    _anneal_diff_pre_staged: bool = False,
    _capture_opened: _OpenedExecutable | None = None,
    _capture_pre_staged: bool = False,
    _mir_eval_pre_staged: bool = False,
    _pre_staged_capture_env: dict[str, Path] | None = None,
) -> tuple[int, dict[str, Any]]:
    """Run `anneal-diff run --json` and parse its JSON payload."""
    caller_cwd = Path.cwd()
    extra_args: list[str] = []
    if manifest is not None:
        manifest_abs = _resolve_cli_path(
            manifest, "manifest", base_dir=caller_cwd
        )
        extra_args.extend(["--manifest", str(manifest_abs)])
    if self_check_oracle:
        extra_args.append("--self-check-oracle")
    return _run_anneal_diff_subcommand(
        subcmd="run",
        anneal_root=anneal_root,
        capture_bin=capture_bin,
        mir_eval_bin=mir_eval_bin,
        cache_root=cache_root,
        anneal_diff_bin=anneal_diff_bin,
        extra_args=extra_args,
        timeout_secs=timeout_secs,
        _anneal_diff_pre_staged=_anneal_diff_pre_staged,
        _capture_opened=_capture_opened,
        _capture_pre_staged=_capture_pre_staged,
        _mir_eval_pre_staged=_mir_eval_pre_staged,
        _pre_staged_capture_env=_pre_staged_capture_env,
    )


def run_anneal_fuzz(
    *,
    anneal_root: Path,
    capture_bin: Path | None,
    mir_eval_bin: Path | None,
    cache_root: Path | None,
    seed: int,
    cases: int,
    max_stmts: int,
    ub_ratio: float,
    min_admission_rate: float,
    fuel: int = 1500,
    anneal_diff_bin: Path | None = None,
    timeout_secs: float = ANNEAL_DIFF_SUBCOMMAND_TIMEOUT_SECS,
    _anneal_diff_pre_staged: bool = False,
    _capture_opened: _OpenedExecutable | None = None,
    _capture_pre_staged: bool = False,
    _mir_eval_pre_staged: bool = False,
    _pre_staged_capture_env: dict[str, Path] | None = None,
) -> tuple[int, dict[str, Any]]:
    """Run `anneal-diff fuzz --json` and parse its JSON payload."""
    return _run_anneal_diff_subcommand(
        subcmd="fuzz",
        anneal_root=anneal_root,
        capture_bin=capture_bin,
        mir_eval_bin=mir_eval_bin,
        cache_root=cache_root,
        anneal_diff_bin=anneal_diff_bin,
        timeout_secs=timeout_secs,
        _anneal_diff_pre_staged=_anneal_diff_pre_staged,
        _capture_opened=_capture_opened,
        _capture_pre_staged=_capture_pre_staged,
        _mir_eval_pre_staged=_mir_eval_pre_staged,
        _pre_staged_capture_env=_pre_staged_capture_env,
        extra_args=[
            "--seed",
            str(seed),
            "--cases",
            str(cases),
            "--max-stmts",
            str(max_stmts),
            "--ub-ratio",
            str(ub_ratio),
            "--min-admission-rate",
            str(min_admission_rate),
            "--fuel",
            str(fuel),
        ],
    )


def main(argv: list[str] | None = None) -> int:
    caller_cwd = Path.cwd()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--anneal-root",
        type=Path,
        default=_default_anneal_root(),
        help="Path to the anneal/ workspace root.",
    )
    parser.add_argument("--manifest", type=Path, help="Override differential manifest.")
    parser.add_argument(
        "--capture-bin",
        type=Path,
        help="Explicit anneal-rustc-capture binary path.",
    )
    mir_eval_group = parser.add_mutually_exclusive_group()
    mir_eval_group.add_argument(
        "--mir-eval-manifest",
        type=Path,
        help="Optional explicit anneal-mir-eval Cargo.toml manifest to test and build.",
    )
    mir_eval_group.add_argument(
        "--mir-eval-bin",
        type=Path,
        help="Optional prebuilt anneal-mir-eval binary path.",
    )
    parser.add_argument(
        "--anneal-diff-bin",
        type=Path,
        help="Optional prebuilt anneal-diff binary path.",
    )
    parser.add_argument(
        "--cache-root",
        type=Path,
        help="Optional cache root for Miri sysroot and Lean DAG artifacts.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        help="Optional output path for anneal-semantic-detail/v1 JSON.",
    )
    parser.add_argument(
        "--perf-metrics-out",
        type=Path,
        help="Optional output path for differential metric snippet JSON.",
    )
    parser.add_argument(
        "--perf-record-out",
        type=Path,
        help="Optional output path for full validated `anneal-perf-record/v1` JSON.",
    )
    parser.add_argument(
        "--expect-capture-source",
        help="Optional expected `capture_bin_source` provenance to enforce fail-closed.",
    )
    parser.add_argument(
        "--no-self-check-oracle",
        action="store_true",
        help="Disable injected oracle mutant checks.",
    )
    parser.add_argument(
        "--no-fuzz",
        action="store_true",
        help="Disable Stage-2 deterministic property fuzz campaign.",
    )
    parser.add_argument(
        "--fuzz-seed",
        type=int,
        default=20261124,
        help="Deterministic master seed for Stage-2 fuzz campaign.",
    )
    parser.add_argument(
        "--fuzz-cases",
        type=int,
        default=32,
        help="Number of generated cases for Stage-2 fuzz campaign.",
    )
    parser.add_argument(
        "--fuzz-max-stmts",
        type=int,
        default=6,
        help="Maximum rendered body statements per generated fuzz function (1..=20).",
    )
    parser.add_argument(
        "--fuzz-ub-ratio",
        type=float,
        default=0.20,
        help="Fraction of generated fuzz cases targeting UB probes (0.0..=0.85).",
    )
    parser.add_argument(
        "--fuzz-min-admission-rate",
        type=float,
        default=0.90,
        help="Non-vacuity minimum admission rate for SafeAdmitted/BoundaryEdgeCase cases.",
    )
    parser.add_argument(
        "--fuzz-fuel",
        type=int,
        default=1500,
        help="Lean / anneal-mir-eval step fuel budget per generated fuzz case (>= 1).",
    )
    parser.add_argument(
        "--fuzz-timeout-secs",
        type=float,
        default=ANNEAL_DIFF_SUBCOMMAND_TIMEOUT_SECS,
        help="Subprocess timeout in seconds for Stage-2 `anneal-diff fuzz`.",
    )
    parser.add_argument(
        "--skip-mir-eval-tests",
        action="store_true",
        help="Skip running --mir-eval-manifest unit/CLI tests even if supplied.",
    )
    parser.add_argument(
        "--allow-unknown-git",
        action="store_true",
        help="Allow fallback git metadata when running outside a git checkout.",
    )
    parser.add_argument("--repo", default="google/zerocopy")
    parser.add_argument("--branch")
    parser.add_argument(
        "--commit-sha",
        help="Explicit 40-hex commit SHA override for telemetry metadata.",
    )
    parser.add_argument(
        "--commit-unix-ts",
        type=int,
        help="Explicit commit UNIX timestamp override (>= 0) for telemetry metadata.",
    )
    args = parser.parse_args(argv)

    if (args.commit_sha is None) != (args.commit_unix_ts is None):
        parser.error(
            "--commit-sha and --commit-unix-ts must be provided together"
        )
    if args.commit_sha is not None and (
        len(args.commit_sha) != 40
        or any(c not in "0123456789abcdefABCDEF" for c in args.commit_sha)
    ):
        parser.error("--commit-sha must be a 40-character hexadecimal digest")
    if args.commit_unix_ts is not None and args.commit_unix_ts < 0:
        parser.error("--commit-unix-ts must be a non-negative integer")

    anneal_root = _resolve_cli_path(
        args.anneal_root, "anneal_root", base_dir=caller_cwd
    ).resolve(strict=True)
    if not args.no_fuzz:
        usize_max = _host_usize_max()
        if args.fuzz_seed < 0 or args.fuzz_seed > _MASK64:
            raise ValueError(
                f"--fuzz-seed must be in 0..={_MASK64}, got {args.fuzz_seed}"
            )
        if not (1 <= args.fuzz_cases <= usize_max):
            raise ValueError(
                f"--fuzz-cases must be in 1..={usize_max}, got {args.fuzz_cases}"
            )
        if not (1 <= args.fuzz_max_stmts <= 20):
            raise ValueError(
                f"--fuzz-max-stmts must be in 1..=20, got {args.fuzz_max_stmts}"
            )
        if not _is_bounded_rate(args.fuzz_ub_ratio, upper=0.85):
            raise ValueError(
                f"--fuzz-ub-ratio must be in 0.0..=0.85, got {args.fuzz_ub_ratio}"
            )
        if not _is_bounded_rate(args.fuzz_min_admission_rate):
            raise ValueError(
                "--fuzz-min-admission-rate must be a finite float in 0.0..=1.0, "
                f"got {args.fuzz_min_admission_rate}"
            )
        if not (1 <= args.fuzz_fuel <= usize_max):
            raise ValueError(
                f"--fuzz-fuel must be in 1..={usize_max}, got {args.fuzz_fuel}"
            )
        if (
            not math.isfinite(args.fuzz_timeout_secs)
            or args.fuzz_timeout_secs <= 0
        ):
            raise ValueError(
                "--fuzz-timeout-secs must be a positive finite float, "
                f"got {args.fuzz_timeout_secs}"
            )

    manifest_path = _resolve_optional_cli_path(
        args.manifest, "manifest", base_dir=caller_cwd
    )
    mir_eval_manifest_path = _resolve_optional_cli_path(
        args.mir_eval_manifest,
        "mir_eval_manifest",
        base_dir=caller_cwd,
        reject_hardlinks=True,
    )
    cache_root_path = _resolve_optional_cli_path(
        args.cache_root, "cache_root", base_dir=caller_cwd
    )
    output_path = _resolve_optional_cli_path(
        args.output, "output", base_dir=caller_cwd
    )
    perf_metrics_out_path = _resolve_optional_cli_path(
        args.perf_metrics_out, "perf_metrics_out", base_dir=caller_cwd
    )
    perf_record_out_path = _resolve_optional_cli_path(
        args.perf_record_out, "perf_record_out", base_dir=caller_cwd
    )

    with contextlib.ExitStack() as cleanup_stack:
        capture_opened = (
            _open_store_aware_executable(
                args.capture_bin,
                "capture_bin",
                base_dir=caller_cwd,
                allow_cargo_deps_hardlink=True,
                exit_stack=cleanup_stack,
            )
            if args.capture_bin is not None
            else None
        )
        env_capture_opened = {
            cap_key: _open_store_aware_executable(
                Path(raw_cap),
                cap_key,
                base_dir=caller_cwd,
                allow_cargo_deps_hardlink=True,
                exit_stack=cleanup_stack,
            )
            for cap_key in ("ANNEAL_CAPTURE", "ANNEAL_MVP_CAPTURE")
            if (raw_cap := os.environ.get(cap_key))
        }
        mir_eval_opened = (
            _open_store_aware_executable(
                args.mir_eval_bin,
                "mir_eval_bin",
                base_dir=caller_cwd,
                allow_cargo_deps_hardlink=False,
                exit_stack=cleanup_stack,
            )
            if args.mir_eval_bin is not None
            else None
        )
        anneal_diff_opened = (
            _open_store_aware_executable(
                args.anneal_diff_bin,
                "anneal_diff_bin",
                base_dir=caller_cwd,
                allow_cargo_deps_hardlink=True,
                exit_stack=cleanup_stack,
            )
            if args.anneal_diff_bin is not None
            else None
        )
        tmp_parent_path = (
            _validate_child_tmpdir(
                {"TMPDIR": os.environ.get("TMPDIR", "")}, caller_cwd
            )
            if (
                mir_eval_manifest_path is not None
                or mir_eval_opened is not None
                or anneal_diff_opened is not None
                or capture_opened is not None
                or env_capture_opened
            )
            else None
        )
        tmp_parent_str = str(tmp_parent_path) if tmp_parent_path is not None else None
        effective_mir_eval_bin = (
            _stage_verified_executable(
                mir_eval_opened.path,
                "anneal-mir-eval",
                allow_cargo_deps_hardlink=False,
                exit_stack=cleanup_stack,
                base_dir=caller_cwd,
                tmp_parent=tmp_parent_str,
                preopened=mir_eval_opened,
            )
            if mir_eval_opened is not None
            else None
        )
        effective_capture_bin = (
            _maybe_stage_cargo_hardlink_executable(
                capture_opened.path,
                "anneal-rustc-capture",
                exit_stack=cleanup_stack,
                base_dir=caller_cwd,
                tmp_parent=tmp_parent_str,
                preopened=capture_opened,
            )
            if capture_opened is not None
            else None
        )
        pre_staged_capture_env = {
            cap_key: _maybe_stage_cargo_hardlink_executable(
                opened_cap.path,
                "anneal-rustc-capture",
                exit_stack=cleanup_stack,
                base_dir=caller_cwd,
                tmp_parent=tmp_parent_str,
                preopened=opened_cap,
            )
            for cap_key, opened_cap in env_capture_opened.items()
        }
        effective_anneal_diff_bin = (
            _stage_verified_executable(
                anneal_diff_opened.path,
                "anneal-diff",
                allow_cargo_deps_hardlink=True,
                exit_stack=cleanup_stack,
                base_dir=caller_cwd,
                tmp_parent=tmp_parent_str,
                preopened=anneal_diff_opened,
            )
            if anneal_diff_opened is not None
            else None
        )
        mir_eval_status, built_mir_eval_bin = (
            maybe_run_mir_eval_manifest(
                mir_eval_manifest_path,
                skip_tests=args.skip_mir_eval_tests,
                staging_exit_stack=cleanup_stack,
            )
            if mir_eval_manifest_path is not None
            else maybe_run_mir_eval_manifest(
                None, skip_tests=args.skip_mir_eval_tests
            )
        )
        if (
            mir_eval_manifest_path is not None
            and mir_eval_status.get("passed") is False
        ):
            print(
                f"mir-eval manifest check failed: {mir_eval_status.get('error', '')}",
                file=sys.stderr,
            )
            return 1
        if mir_eval_manifest_path is not None:
            effective_mir_eval_bin = built_mir_eval_bin

        self_check_oracle = not args.no_self_check_oracle
        pre_cap_env_kw: dict[str, Any] = (
            {"_pre_staged_capture_env": pre_staged_capture_env}
            if pre_staged_capture_env
            else {}
        )
        diff_rc, diff_report = run_anneal_diff(
            anneal_root=anneal_root,
            manifest=manifest_path,
            capture_bin=effective_capture_bin,
            mir_eval_bin=effective_mir_eval_bin,
            cache_root=cache_root_path,
            self_check_oracle=self_check_oracle,
            anneal_diff_bin=effective_anneal_diff_bin,
            _anneal_diff_pre_staged=effective_anneal_diff_bin is not None,
            _capture_pre_staged=effective_capture_bin is not None,
            _mir_eval_pre_staged=effective_mir_eval_bin is not None,
            **pre_cap_env_kw,
        )

        run_fuzz = not args.no_fuzz
        fuzz_rc = 0
        fuzz_report: dict[str, Any] | None = None
        if run_fuzz:
            fuzz_rc, fuzz_report = run_anneal_fuzz(
                anneal_root=anneal_root,
                capture_bin=effective_capture_bin,
                mir_eval_bin=effective_mir_eval_bin,
                cache_root=cache_root_path,
                seed=args.fuzz_seed,
                cases=args.fuzz_cases,
                max_stmts=args.fuzz_max_stmts,
                ub_ratio=args.fuzz_ub_ratio,
                min_admission_rate=args.fuzz_min_admission_rate,
                fuel=args.fuzz_fuel,
                anneal_diff_bin=effective_anneal_diff_bin,
                timeout_secs=args.fuzz_timeout_secs,
                _anneal_diff_pre_staged=effective_anneal_diff_bin is not None,
                _capture_pre_staged=effective_capture_bin is not None,
                _mir_eval_pre_staged=effective_mir_eval_bin is not None,
                **pre_cap_env_kw,
            )

    branch, commit_sha, commit_unix_ts = _git_metadata(
        anneal_root,
        allow_unknown_git=args.allow_unknown_git,
        commit_sha_override=args.commit_sha,
        commit_unix_ts_override=args.commit_unix_ts,
        branch_override=args.branch,
    )
    env_profile = _collect_environment(anneal_root, caller_cwd=caller_cwd)
    expect_mir_eval = effective_mir_eval_bin is not None
    detail = build_semantic_detail_report(
        diff_report=diff_report,
        mir_eval_status=mir_eval_status,
        repo=args.repo,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=env_profile,
        fuzz_report=fuzz_report,
        fuzz_ub_ratio=args.fuzz_ub_ratio if run_fuzz else None,
        fuzz_expected_seed=args.fuzz_seed if run_fuzz else None,
        fuzz_expected_cases=args.fuzz_cases if run_fuzz else None,
        fuzz_expected_max_stmts=args.fuzz_max_stmts if run_fuzz else None,
        fuzz_expected_fuel=args.fuzz_fuel if run_fuzz else None,
        fuzz_min_admission_rate=args.fuzz_min_admission_rate if run_fuzz else None,
        expect_mir_eval=expect_mir_eval,
    )
    perf_snippet = build_perf_metrics_snippet(diff_report, fuzz_report=fuzz_report)
    perf_record = build_perf_record_from_snippet(
        perf_snippet,
        branch=branch,
        commit_sha=commit_sha,
        commit_unix_ts=commit_unix_ts,
        environment_profile=env_profile,
    )

    _reject_diff_timeout(diff_report)
    fuzz_timed_out = _is_synthesized_fuzz_timeout(fuzz_report)
    run_src = diff_report.get("capture_bin_source")
    run_sha = str(diff_report.get("capture_bin_sha256") or "")
    if fuzz_report is not None and not fuzz_timed_out:
        fuzz_src = fuzz_report.get("capture_bin_source")
        fuzz_sha = str(fuzz_report.get("capture_bin_sha256") or "")
        if (
            not _is_valid_sha256_hex(run_sha)
            or not _is_valid_sha256_hex(fuzz_sha)
            or fuzz_sha != run_sha
            or fuzz_src != run_src
        ):
            print(
                f"capture provenance mismatch across run vs fuzz: "
                f"run=({run_src!r}, {run_sha!r}), "
                f"fuzz=({fuzz_src!r}, {fuzz_sha!r})",
                file=sys.stderr,
            )
            return 1

    if args.expect_capture_source:
        provenance_checks: list[tuple[str, dict[str, Any]]] = [("run", diff_report)]
        if fuzz_report is not None and not fuzz_timed_out:
            provenance_checks.append(("fuzz", fuzz_report))
        for label, rep in provenance_checks:
            actual_src = rep.get("capture_bin_source")
            actual_sha = str(rep.get("capture_bin_sha256") or "")
            if actual_src != args.expect_capture_source or not _is_valid_sha256_hex(
                actual_sha
            ):
                print(
                    f"capture provenance mismatch ({label}): "
                    f"expected source={args.expect_capture_source!r}, "
                    f"got source={actual_src!r}, sha256={actual_sha!r}",
                    file=sys.stderr,
                )
                return 1

    if output_path is not None:
        ensure_not_symlink(output_path, "output")
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_text(
            json.dumps(detail, indent=2) + "\n", encoding="utf-8"
        )
    if perf_metrics_out_path is not None:
        ensure_not_symlink(perf_metrics_out_path, "perf_metrics_out")
        perf_metrics_out_path.parent.mkdir(parents=True, exist_ok=True)
        perf_metrics_out_path.write_text(
            json.dumps(perf_snippet, indent=2) + "\n", encoding="utf-8"
        )
    if perf_record_out_path is not None:
        ensure_not_symlink(perf_record_out_path, "perf_record_out")
        perf_record_out_path.parent.mkdir(parents=True, exist_ok=True)
        perf_record_out_path.write_text(
            json.dumps(perf_record, indent=2) + "\n", encoding="utf-8"
        )

    print(json.dumps(detail, indent=2))
    if (
        diff_rc != 0
        or fuzz_rc != 0
        or not report_passes(
            detail,
            require_mutants=self_check_oracle,
            require_fuzz=run_fuzz,
            require_mir_eval=expect_mir_eval,
            fuzz_min_admission_rate=args.fuzz_min_admission_rate,
            fuzz_ub_ratio=args.fuzz_ub_ratio if run_fuzz else None,
            fuzz_expected_cases=args.fuzz_cases if run_fuzz else None,
            fuzz_expected_max_stmts=args.fuzz_max_stmts if run_fuzz else None,
            fuzz_expected_fuel=args.fuzz_fuel if run_fuzz else None,
        )
    ):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
