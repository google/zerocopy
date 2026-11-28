# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Landlock rulesets and the confinement support preflight."""

from __future__ import annotations

import ctypes
import os
from pathlib import Path
import platform
import stat
import struct
import sys

from .common import OracleError
from .linux_abi import (
    _LANDLOCK_ACCESS_FS_ABI1_ALL, _LANDLOCK_ACCESS_FS_IOCTL_DEV, _LANDLOCK_ACCESS_FS_REFER,
    _LANDLOCK_ACCESS_FS_TRUNCATE, _LANDLOCK_CREATE_RULESET_VERSION, _LANDLOCK_DIR_RO,
    _LANDLOCK_DIR_RO_EXEC, _LANDLOCK_DIR_RW_BASE, _LANDLOCK_FILE_RO, _LANDLOCK_FILE_RO_EXEC,
    _LANDLOCK_FILE_RW_BASE, _LANDLOCK_RULE_PATH_BENEATH, _LANDLOCK_SYSTEM_RO_EXEC_DIRS,
    _LANDLOCK_SYSTEM_RO_PATHS, _PR_SET_NO_NEW_PRIVS, _SYS_LANDLOCK_ADD_RULE,
    _SYS_LANDLOCK_CREATE_RULESET, _SYS_LANDLOCK_RESTRICT_SELF,
)
from .seccomp import _build_confinement_seccomp_bpf
from .capture import _assert_capture_non_root_uid, _harden_parent_process


def _probe_landlock_abi() -> int:
    """Return the active Linux Landlock ABI version (>= 1) or fail closed."""
    libc = ctypes.CDLL(None, use_errno=True)
    abi = int(
        libc.syscall(
            _SYS_LANDLOCK_CREATE_RULESET,
            0,
            0,
            _LANDLOCK_CREATE_RULESET_VERSION,
        )
    )
    if abi < 1:
        err = ctypes.get_errno()
        raise OracleError(
            f"Linux Landlock LSM is unavailable (abi={abi}, errno={err}); "
            "refusing to run evaluator without filesystem/proc isolation"
        )
    return abi


def _elf_pt_interp(exe_path: Path) -> Path | None:
    """Return the ELF64 `PT_INTERP` dynamic linker path for `exe_path`, if any."""
    try:
        with exe_path.open("rb") as fh:
            ehdr = fh.read(64)
            if len(ehdr) < 64 or ehdr[:4] != b"\x7fELF" or ehdr[4] != 2 or ehdr[5] != 1:
                return None
            e_phoff = struct.unpack_from("<Q", ehdr, 32)[0]
            e_phentsize, e_phnum = struct.unpack_from("<HH", ehdr, 54)
            if e_phentsize < 56 or e_phnum == 0 or e_phnum > 128:
                return None
            fh.seek(e_phoff)
            phdrs = fh.read(e_phentsize * e_phnum)
            for i in range(e_phnum):
                off = i * e_phentsize
                if off + 56 > len(phdrs):
                    break
                p_type = struct.unpack_from("<I", phdrs, off)[0]
                if p_type == 3:  # PT_INTERP
                    p_offset = struct.unpack_from("<Q", phdrs, off + 8)[0]
                    p_filesz = struct.unpack_from("<Q", phdrs, off + 32)[0]
                    if 0 < p_filesz <= 4096:
                        fh.seek(p_offset)
                        raw = fh.read(p_filesz).split(b"\x00", 1)[0]
                        if raw:
                            return Path(os.fsdecode(raw))
                    return None
    except OSError:
        return None
    return None


def _shebang_interpreter(exe_path: Path) -> Path | None:
    """Return the `#!` interpreter binary path for `exe_path`, if any."""
    try:
        with exe_path.open("rb") as fh:
            line = fh.readline(256)
        if not line.startswith(b"#!"):
            return None
        parts = line[2:].strip().split()
        if not parts:
            return None
        return Path(os.fsdecode(parts[0]))
    except OSError:
        return None


def _is_script_or_python(target_exe: Path) -> bool:
    """Return True if `target_exe` is the Python interpreter or a `#!` script."""
    try:
        if target_exe.resolve() == Path(sys.executable).resolve():
            return True
    except OSError:
        pass
    return _shebang_interpreter(target_exe) is not None


def _collect_landlock_read_paths(
    target_exe: Path,
    read_only_paths: list[Path],
    read_only_exec_paths: list[Path] = (),  # type: ignore[assignment]
) -> tuple[list[tuple[Path, bool]], list[tuple[Path, bool]]]:
    """Return `(ro_exec_entries, ro_entries)` of `(path, required)` pairs.

    Shared single source of truth between Landlock read-only rules and
    `capture`-mode read-only bind-mounts so every external readable path
    accessible under Landlock is also read-only at the VFS mount layer.
    """
    ro_exec_entries: list[tuple[Path, bool]] = [
        (Path(sys_dir), False) for sys_dir in _LANDLOCK_SYSTEM_RO_EXEC_DIRS
    ]
    ro_entries: list[tuple[Path, bool]] = [
        (Path(sys_ro), False) for sys_ro in _LANDLOCK_SYSTEM_RO_PATHS
    ]
    if _is_script_or_python(target_exe):
        for py_root in sorted(
            {
                Path(sys.executable),
                Path(sys.executable).resolve(),
                Path(sys.prefix),
                Path(sys.prefix).resolve(),
                Path(sys.base_prefix),
                Path(sys.base_prefix).resolve(),
            }
        ):
            ro_exec_entries.append((py_root, False))
        shebang = _shebang_interpreter(target_exe)
        if shebang is not None:
            ro_exec_entries.append((shebang, False))
            sb_interp = _elf_pt_interp(shebang)
            if sb_interp is not None:
                ro_exec_entries.append((sb_interp, False))
    interp = _elf_pt_interp(target_exe)
    if interp is not None:
        ro_exec_entries.append((interp, False))
    ro_exec_entries.append((target_exe, True))
    for ro_exec in read_only_exec_paths:
        ro_exec_entries.append((ro_exec, True))
    for ro_path in read_only_paths:
        ro_entries.append((ro_path, True))
    return ro_exec_entries, ro_entries


def _install_landlock(
    target_exe: Path,
    read_only_paths: list[Path],
    *,
    read_only_exec_paths: list[Path] = (),  # type: ignore[assignment]
    read_write_paths: list[Path] = (),  # type: ignore[assignment]
    allow_proc_self: bool = False,
    require_truncate_mediation: bool = False,
) -> None:
    """Confine children to a Landlock filesystem allowlist.

    Grants read-only/exec access strictly to standard dynamic-linker runtime
    paths, `target_exe`, and explicit `read_only_exec_paths`, read-only access
    to `read_only_paths`, and narrow read-write access (no `EXECUTE`, no device
    nodes, no symlinks/FIFOs/sockets) strictly to `read_write_paths`. Denies
    `/proc` enumeration and all other paths so children cannot inspect parent
    environments or mutate the checkout, home directory, or sibling workers.
    When `require_truncate_mediation=True` (used in `capture` mode where
    `truncate`/`ftruncate` are permitted inside the work tmpfs), fails closed
    unless Landlock ABI >= 3 is active so read-only paths cannot be truncated.
    """
    abi = _probe_landlock_abi()
    if require_truncate_mediation:
        _assert_capture_non_root_uid()
        if abi < 3:
            raise OracleError(
                "capture confinement requires Linux Landlock ABI >= 3 for "
                f"truncate mediation (got ABI {abi})"
            )
    handled = _LANDLOCK_ACCESS_FS_ABI1_ALL
    if abi >= 2:
        handled |= _LANDLOCK_ACCESS_FS_REFER
    if abi >= 3:
        handled |= _LANDLOCK_ACCESS_FS_TRUNCATE
    if abi >= 5:
        handled |= _LANDLOCK_ACCESS_FS_IOCTL_DEV

    dir_rw = _LANDLOCK_DIR_RW_BASE
    file_rw = _LANDLOCK_FILE_RW_BASE
    if abi >= 2:
        dir_rw |= _LANDLOCK_ACCESS_FS_REFER
    if abi >= 3:
        dir_rw |= _LANDLOCK_ACCESS_FS_TRUNCATE
        file_rw |= _LANDLOCK_ACCESS_FS_TRUNCATE

    libc = ctypes.CDLL(None, use_errno=True)
    attr = ctypes.create_string_buffer(struct.pack("<Q", handled))
    ruleset_fd = int(libc.syscall(_SYS_LANDLOCK_CREATE_RULESET, attr, 8, 0))
    if ruleset_fd < 0:
        err = ctypes.get_errno()
        raise OracleError(f"landlock_create_ruleset failed: errno={err}")

    def _add_rule(
        path: Path, *, allow_exec: bool, allow_write: bool, required: bool
    ) -> None:
        if not path.exists():
            if required:
                raise OracleError(f"Landlock allowed path does not exist: {path}")
            return
        o_path = getattr(os, "O_PATH", 0x200000)
        o_cloexec = getattr(os, "O_CLOEXEC", 0x80000)
        try:
            fd = os.open(path, o_path | o_cloexec)
        except OSError as exc:
            if not required:
                return
            raise OracleError(
                f"failed opening Landlock path '{path}': {exc}"
            ) from exc
        try:
            st = os.fstat(fd)
            if stat.S_ISDIR(st.st_mode):
                if allow_write:
                    access = dir_rw
                else:
                    access = (
                        _LANDLOCK_DIR_RO_EXEC if allow_exec else _LANDLOCK_DIR_RO
                    )
            else:
                if allow_write:
                    access = file_rw
                else:
                    access = (
                        _LANDLOCK_FILE_RO_EXEC if allow_exec else _LANDLOCK_FILE_RO
                    )
            pattr = ctypes.create_string_buffer(struct.pack("<Qi", access, fd))
            rc = int(
                libc.syscall(
                    _SYS_LANDLOCK_ADD_RULE,
                    ruleset_fd,
                    _LANDLOCK_RULE_PATH_BENEATH,
                    pattr,
                    0,
                )
            )
            if rc != 0:
                err = ctypes.get_errno()
                raise OracleError(
                    f"landlock_add_rule('{path}') failed: errno={err}"
                )
        finally:
            os.close(fd)

    ro_exec_entries, ro_entries = _collect_landlock_read_paths(
        target_exe, read_only_paths, read_only_exec_paths
    )
    try:
        for path, required in ro_exec_entries:
            _add_rule(path, allow_exec=True, allow_write=False, required=required)
        for path, required in ro_entries:
            _add_rule(path, allow_exec=False, allow_write=False, required=required)
        if allow_proc_self:
            _add_rule(Path("/proc/self"), allow_exec=False, allow_write=False, required=False)
        for rw_path in read_write_paths:
            _add_rule(rw_path, allow_exec=False, allow_write=True, required=True)
        if libc.prctl(_PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            err = ctypes.get_errno()
            raise OracleError(f"prctl(PR_SET_NO_NEW_PRIVS) failed: errno={err}")
        if int(libc.syscall(_SYS_LANDLOCK_RESTRICT_SELF, ruleset_fd, 0)) != 0:
            err = ctypes.get_errno()
            raise OracleError(f"landlock_restrict_self failed: errno={err}")
    finally:
        os.close(ruleset_fd)


def _install_eval_landlock(
    target_exe: Path, read_only_paths: list[Path]
) -> None:
    """Confine `eval` children to a Landlock read-only allowlist (no `/proc`, no writes)."""
    _install_landlock(target_exe, read_only_paths)


def _require_confinement_support(
    max_memory_mb: int, *, require_truncate_mediation: bool = False
) -> None:
    """Fail closed unless Linux Landlock + seccomp + rlimit + non-dumpable works."""
    if (
        isinstance(max_memory_mb, bool)
        or not isinstance(max_memory_mb, int)
        or max_memory_mb <= 0
    ):
        raise OracleError(
            f"--max-memory-mb must be a positive integer MiB value, got {max_memory_mb!r}"
        )
    if sys.platform != "linux":
        raise OracleError(
            "Linux Landlock + seccomp + RLIMIT_AS confinement is required to bound child process trees"
        )
    _build_confinement_seccomp_bpf(platform.machine(), confinement="eval")
    _build_confinement_seccomp_bpf(platform.machine(), confinement="capture")
    try:
        status_text = Path("/proc/self/status").read_text(encoding="utf-8")
    except OSError as exc:
        raise OracleError(f"failed to probe /proc/self/status for seccomp: {exc}") from exc
    if "Seccomp:" not in status_text:
        raise OracleError(
            "Linux kernel seccomp support is unavailable; refusing to spawn unconfined children"
        )
    _assert_capture_non_root_uid()
    abi = _probe_landlock_abi()
    if require_truncate_mediation and abi < 3:
        raise OracleError(
            "capture confinement requires Linux Landlock ABI >= 3 for "
            f"truncate mediation (got ABI {abi})"
        )
    _harden_parent_process()
