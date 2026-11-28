# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared fixtures, helpers, and the module-level `setUpModule` and
`tearDownModule` for the `anneal-lean-run` tests."""

from __future__ import annotations

import contextlib
import fcntl
import importlib.machinery
import importlib.util
import io
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
from typing import Any, MutableMapping
import unittest
from unittest import mock

sys.dont_write_bytecode = True

SCRIPT_PATH = Path(__file__).resolve().parent.parent / "anneal-lean-run"


def _load_anneal_lean_run():
    loader = importlib.machinery.SourceFileLoader(
        "anneal_lean_run", str(SCRIPT_PATH)
    )
    spec = importlib.util.spec_from_loader("anneal_lean_run", loader)
    assert spec is not None
    module = importlib.util.module_from_spec(spec)
    loader.exec_module(module)
    return module


alr = _load_anneal_lean_run()
MIB = 1024 * 1024

_AMBIENT_ANNEAL_ENV_PREFIXES: tuple[str, ...] = (
    "ANNEAL_LEAN_",
    "ANNEAL_WORKTREE_",
)
_ENV_PATCHER: Any = None
# Every Python-level way to replace the current process image ends in `os.execv`
# or `os.execve` (`os.execl*` / `os.execvp*` are wrappers around them).
_GUARDED_EXEC_FUNCTIONS: tuple[str, ...] = ("execv", "execve", "execvp", "execvpe")
_EXEC_GUARDS: list[Any] = []
_XDG_TMPDIR: tempfile.TemporaryDirectory[str] | None = None
_MGR_UNIT_TMPDIR: tempfile.TemporaryDirectory[str] | None = None
_REAL_SYSTEMCTL: str | None = shutil.which("systemctl") or (
    "/usr/bin/systemctl" if Path("/usr/bin/systemctl").is_file() else None
)
# Text of the `anneal-workloads.slice` unit `ensure_workloads_slice` reconciles
# on this host, or `None` when it refuses to write one (no delegated
# `systemd --user`).
_SLICE_UNIT_SEED: str | None = None


def _install_test_systemctl_shim(
    bin_dir: Path, unit_dir: Path
) -> Path | None:
    """Installs a `systemctl` shim redirecting `UnitPath` to `unit_dir` and
    turning `daemon-reload` into a no-op while forwarding all other queries to
    the host's real `systemctl`.
    """
    if _REAL_SYSTEMCTL is None:
        return None
    bin_dir.mkdir(parents=True, exist_ok=True)
    shim = bin_dir / "systemctl"
    q_unit = shlex.quote(str(unit_dir))
    q_real = shlex.quote(_REAL_SYSTEMCTL)
    shim.write_text(
        "#!/bin/sh\n"
        'if [ "$*" = "--user show -p UnitPath --value" ]; then\n'
        f"  printf '%s.control /run/systemd/user %s\\n' {q_unit} {q_unit}\n"
        "  exit 0\n"
        "fi\n"
        'if [ "$*" = "--user daemon-reload" ]; then\n'
        "  exit 0\n"
        "fi\n"
        f'exec {q_real} "$@"\n',
        encoding="utf-8",
    )
    shim.chmod(0o755)
    return bin_dir


def _scrub_ambient_anneal_env(env: MutableMapping[str, str]) -> None:
    for key in list(env):
        if key.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES):
            env.pop(key, None)


def _isolated_cli_env(
    xdg_config_home: Path, env_extra: dict[str, str] | None = None
) -> dict[str, str]:
    env = dict(os.environ)
    _scrub_ambient_anneal_env(env)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["XDG_CONFIG_HOME"] = str(xdg_config_home)
    if env_extra:
        env.update(env_extra)
    eff_xdg = Path(env["XDG_CONFIG_HOME"]) if env.get("XDG_CONFIG_HOME") else xdg_config_home
    seeded_bin = eff_xdg / ".test-bin"
    if (seeded_bin / "systemctl").is_file():
        env["PATH"] = f"{seeded_bin}:{env.get('PATH', '')}"
    return env


def _forbid_in_process_exec(file: str, args: Any, *rest: Any) -> None:
    raise AssertionError(
        f"in-process exec of {args!r} would replace the unittest runner and report the "
        "command's exit status as the suite's (did ANNEAL_LEAN_RUN_IN_SCOPE leak into "
        "the test process?)"
    )


def _render_live_workloads_slice_unit() -> str | None:
    """Unit text `ensure_workloads_slice` renders on this host (`None` if it
    refuses).
    """
    try:
        info = alr.probe_host_envelope(is_probe=True)
    # seeding is best-effort; the probe has its own tests
    except Exception:  # noqa: BLE001
        return None
    if not (info.get("user_systemd_active") and info.get("t_cg_is_user_service")):
        return None
    return alr.render_workloads_slice_unit(
        int(info["w_slice_high_mb"]), int(info["w_slice_max_mb"])
    )


def _seed_workloads_slice_unit(config_root: Path) -> Path | None:
    """Pre-renders `anneal-workloads.slice` under an isolated manager `UnitPath`
    directory (`config_root/systemd/user`) and installs a matching `systemctl`
    shim under `config_root/.test-bin` so subprocesses neither touch the host's
    real `~/.config/systemd/user` nor reload live `systemd --user`.

    Returns the seeded path, or `None` when this host never reconciles the unit.
    """
    if _SLICE_UNIT_SEED is None:
        return None
    unit_dir = config_root / "systemd" / "user"
    unit = unit_dir / "anneal-workloads.slice"
    unit.parent.mkdir(parents=True, exist_ok=True)
    unit.write_text(_SLICE_UNIT_SEED, encoding="utf-8")
    _install_test_systemctl_shim(config_root / ".test-bin", unit_dir)
    return unit


def _can_launch_live_systemd_scope() -> bool:
    """True only when user systemd is active and `systemd-run --user --scope`
    can actually launch a trivial transient scope on this host.
    """
    if not sys.platform.startswith("linux") or not alr.check_user_systemd_active():
        return False
    srun_bin = alr._find_systemd_run()
    if not srun_bin:
        return False
    rb, sock_alive = alr.resolve_runtime_base()
    try:
        res = subprocess.run(
            [srun_bin, "--user", "--scope", "--collect", "--quiet", "--", "true"],
            env=alr._systemd_env(rb, sock_alive),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=5.0,
            check=False,
        )
        return res.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _file_identity(path: Path) -> tuple[int, int, str]:
    """`(inode, mtime_ns, text)`: changes whenever the file is rewritten or
    replaced.
    """
    st = path.stat()
    return st.st_ino, st.st_mtime_ns, path.read_text(encoding="utf-8")


def setUpModule() -> None:
    global _ENV_PATCHER, _XDG_TMPDIR, _MGR_UNIT_TMPDIR, _SLICE_UNIT_SEED
    try:
        _XDG_TMPDIR = tempfile.TemporaryDirectory(prefix="anneal-test-xdg-")
        _MGR_UNIT_TMPDIR = tempfile.TemporaryDirectory(
            prefix="anneal-test-mgr-unit-"
        )
        mgr_root = Path(_MGR_UNIT_TMPDIR.name)
        mgr_bin = _install_test_systemctl_shim(
            mgr_root / ".test-bin", mgr_root / "systemd" / "user"
        )
        patch_vals = {"XDG_CONFIG_HOME": _XDG_TMPDIR.name}
        if mgr_bin is not None:
            patch_vals["PATH"] = f"{mgr_bin}:{os.environ.get('PATH', '')}"
        _ENV_PATCHER = mock.patch.dict(os.environ, patch_vals)
        _ENV_PATCHER.start()
        _scrub_ambient_anneal_env(os.environ)
        # The re-entrancy pass-through of `alr.main` `os.execvp`s its command.
        # In-process that would replace the unittest runner and end the run
        # early with the command's own exit status (`true` -> 0: a truncated run
        # reported as success), so fail loudly instead. Subprocesses are
        # unaffected (`subprocess` does not go through `os.exec*`).
        for name in _GUARDED_EXEC_FUNCTIONS:
            guard = mock.patch.object(os, name, side_effect=_forbid_in_process_exec)
            guard.start()
            _EXEC_GUARDS.append(guard)
        # Keep `_MGR_UNIT_TMPDIR` distinct from client `_XDG_TMPDIR` so every
        # in-process command run exercises manager `UnitPath` resolution while
        # remaining a content-diff no-op isolated from the host's live units.
        _SLICE_UNIT_SEED = _render_live_workloads_slice_unit()
        _seed_workloads_slice_unit(mgr_root)
    except BaseException:
        tearDownModule()
        raise


def tearDownModule() -> None:
    global _ENV_PATCHER, _XDG_TMPDIR, _MGR_UNIT_TMPDIR, _SLICE_UNIT_SEED
    while _EXEC_GUARDS:
        _EXEC_GUARDS.pop().stop()
    if _ENV_PATCHER is not None:
        _ENV_PATCHER.stop()
        _ENV_PATCHER = None
    if _MGR_UNIT_TMPDIR is not None:
        _MGR_UNIT_TMPDIR.cleanup()
        _MGR_UNIT_TMPDIR = None
    if _XDG_TMPDIR is not None:
        _XDG_TMPDIR.cleanup()
        _XDG_TMPDIR = None
    _SLICE_UNIT_SEED = None


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _write_cgroup_file(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


# Synthetic hosts: 16 logical cores, 64 GiB RAM, one process in
# `/user.slice/job.scope` whose only (optional) memory ceiling is
# `user.slice/memory.max`.
SYNTHETIC_HOST_CORES = 16


def _write_synthetic_host_base(root: Path) -> None:
    """Writes the `/proc/meminfo` and `/proc/self/cgroup` stand-ins shared by
    every host.
    """
    _write_cgroup_file(
        root / "meminfo",
        "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
    )
    _write_cgroup_file(root / "proc_cgroup", "0::/user.slice/job.scope\n")


def _write_synthetic_cgroup_root(
    root: Path, name: str, user_slice_max_mib: int | None
) -> Path:
    """Writes cgroup v2 root `root/name`; `user_slice_max_mib=None` leaves it
    uncapped.
    """
    cg = root / name
    ceiling = "max" if user_slice_max_mib is None else str(user_slice_max_mib * MIB)
    _write_cgroup_file(cg / "user.slice" / "memory.max", f"{ceiling}\n")
    _write_cgroup_file(cg / "user.slice" / "job.scope" / "memory.max", "max\n")
    _write_cgroup_file(
        cg / "user.slice" / "job.scope" / "memory.stat",
        f"anon {512 * MIB}\nshmem 0\nfile {1024 * MIB}\n",
    )
    return cg


# Fields: (cgroup root name, `user.slice` `memory.max` in MiB,
# `is_cg_capped`, `s_heavy_safe`).
SYNTHETIC_HOSTS: tuple[tuple[str, int | None, bool, int], ...] = (
    ("cg_uncapped", None, False, 2),
    ("cg_capped_1", 12288, True, 1),
    ("cg_capped_2", 32768, True, 2),
)

# Runs the real `main()` of `anneal/ci/anneal-lean-run` in a fresh interpreter
# with only the host probe's inputs redirected to a synthetic host, so argument
# parsing, environment and `$XDG_CONFIG_HOME` handling and the JSON contract are
# exercised end to end for a cgroup regime the machine running the tests may not
# have. argv: <script> <host root> <cgroup root name> [anneal-lean-run args...]
_SYNTHETIC_HOST_CLI_SHIM = f"""\
import functools, importlib.machinery, importlib.util, pathlib, sys
script, root, cg_name = sys.argv[1], pathlib.Path(sys.argv[2]), sys.argv[3]
loader = importlib.machinery.SourceFileLoader("anneal_lean_run_synthetic", script)
spec = importlib.util.spec_from_loader("anneal_lean_run_synthetic", loader)
mod = importlib.util.module_from_spec(spec)
loader.exec_module(mod)
mod.probe_host_envelope = functools.partial(
    mod.probe_host_envelope,
    meminfo_path=root / "meminfo",
    cgroup_root=root / cg_name,
    proc_cgroup_path=root / "proc_cgroup",
    cpu_cores={SYNTHETIC_HOST_CORES},
    user_systemd_active=False,
    runtime_base=root,
)
sys.exit(mod.main(sys.argv[4:]))
"""


FAKE_CGROUP_INFO: dict[str, Any] = {
    "cgroup_v2": True,
    "cgroup_path": "/fake.slice/test.scope",
    "cgroup_anon_mib": 1000,
    "cgroup_shmem_mib": 234,
    "cgroup_anon_shmem_mib": 1234,
    "cgroup_file_cache_mib": 5678,
    "cgroup_current_mib": 6912,
    "cgroup_memory_max_mib": None,
    "cgroup_avail_mib": None,
}

FIXED_HW: dict[str, Any] = {
    "cpu_cores": 8,
    "mem_total_mb": 32768,
    "mem_avail_mb": 24576,
    "cgroup_v2": True,
    "cgroup_path": "/user.slice/anneal.scope",
    "cgroup_anon_mib": 900,
    "cgroup_shmem_mib": 100,
    "cgroup_anon_shmem_mib": 1000,
    "cgroup_file_cache_mib": 3000,
    "cgroup_current_mib": 4200,
    "cgroup_memory_max_mib": 20480,
    "cgroup_avail_mib": 19480,
}


# ---------------------------------------------------------------------------
# CLI, limits, and bounded execution
# ---------------------------------------------------------------------------


class _FakePopen:
    """Records the argv/kwargs of `subprocess.Popen` without running anything.
    """

    calls: list[tuple[list[str], dict[str, Any]]] = []

    def __init__(self, argv: list[str], **kwargs: Any) -> None:
        _FakePopen.calls.append((list(argv), kwargs))
        self.pid = 2**22 + 12345
        self.returncode = 0

    def wait(self, timeout: float | None = None) -> int:
        return 0

    def poll(self) -> int:
        return 0
