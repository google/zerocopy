#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and integration tests for `anneal/ci/anneal-lean-run`."""

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

SCRIPT_PATH = Path(__file__).resolve().parent / "anneal-lean-run"


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
# on this host, or `None` when it refuses to write one (no delegated `systemd
# --user`).
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


# `(cgroup root name, user.slice memory.max in MiB, is_cg_capped,
# s_heavy_safe)`.
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
# Cgroup v2 probing
# ---------------------------------------------------------------------------


class TestCgroupV2Probing(unittest.TestCase):
    """Tests cgroup v2 discovery, `memory.stat` parsing, and `anon + shmem`
    budgeting.
    """

    def test_parse_proc_cgroup_v2_variants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "cgroup"

            # Standard systemd unified cgroup v2 path
            p.write_text(
                "0::/user.slice/user-1000.slice/session-1.scope\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p),
                "/user.slice/user-1000.slice/session-1.scope",
            )

            # Hybrid v1 + v2 hierarchy with (deleted) suffix
            p.write_text(
                "12:pids:/user.slice\n0::/app.slice/worker.scope (deleted)\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p), "/app.slice/worker.scope"
            )

            # Colons inside the path survive (`0::` is split only once)
            p.write_text("0::/app.slice/a:b.scope\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/app.slice/a:b.scope")

            # Root unified hierarchy inside container namespace
            p.write_text("0::/\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/")

            # Cgroup v1 only (no 0:: line), including a named v1 hierarchy
            p.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n1:name=systemd:/x\n",
                encoding="utf-8",
            )
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))

            # Empty file and non-existent file
            p.write_text("", encoding="utf-8")
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))
            self.assertIsNone(alr.parse_proc_cgroup_v2(Path(tmp) / "missing"))

    def test_parse_memory_stat(self) -> None:
        raw = (
            "anon 2147483648\n"
            "file 30064771072\n"
            "shmem 536870912\n"
            "inactive_file 25769803776\n"
            "active_file 4294967296\n"
            "malformed_line_without_val\n"
            "bad_int not_a_number\n"
            "neg_val -100\n"
        )
        stats = alr.parse_memory_stat(raw)
        self.assertEqual(stats["anon"], 2147483648)
        self.assertEqual(stats["file"], 30064771072)
        self.assertEqual(stats["shmem"], 536870912)
        self.assertEqual(stats["inactive_file"], 25769803776)
        self.assertEqual(stats["active_file"], 4294967296)
        self.assertNotIn("bad_int", stats)
        self.assertNotIn("neg_val", stats)
        self.assertNotIn("malformed_line_without_val", stats)

        with tempfile.TemporaryDirectory() as tmp:
            stat_file = Path(tmp) / "memory.stat"
            stat_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(stat_file), stats)
            self.assertEqual(alr.parse_memory_stat(str(stat_file)), stats)
            self.assertEqual(alr.parse_memory_stat(Path(tmp) / "missing"), {})

        with tempfile.TemporaryDirectory(prefix="anneal space $dir-") as tmp_sp:
            sp_file = Path(tmp_sp) / "memory.stat"
            sp_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(str(sp_file)), stats)

    def test_reclaimable_file_cache_does_not_throttle_available_memory(
        self,
    ) -> None:
        """32 GiB cgroup with 28 GiB `.olean` file cache and 2 GiB `anon +
        shmem` must report 30 GiB available (`32 - 2`), NOT 2 GiB (`32 - 30`).
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            # Notice: root cgroup does NOT have memory.stat (standard systemd
            # host)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {1536 * MIB}\n"
                f"shmem {512 * MIB}\n"
                f"file {28672 * MIB}\n"
                f"inactive_file {24576 * MIB}\n"
                f"active_file {4096 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            cores, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(cg["cgroup_path"], "/user.slice/anneal.scope")
            self.assertEqual(cg["cgroup_anon_mib"], 1536)
            self.assertEqual(cg["cgroup_shmem_mib"], 512)
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 2048)
            self.assertEqual(cg["cgroup_file_cache_mib"], 28672)
            self.assertEqual(cg["cgroup_current_mib"], 30720)
            self.assertEqual(cg["cgroup_memory_max_mib"], 32768)
            # Headroom MUST be 32768 - 2048 = 30720 MiB (not 32768 - 30720 =
            # 2048 MiB), while raw `/proc/meminfo` fields stay un-clamped
            # (`65536` / `48000`) for `c_high_mb`.
            self.assertEqual(cg["cgroup_avail_mib"], 30720)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 48000)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertTrue(limits["is_cg_capped"])
            self.assertGreater(limits["w_slice_max_mb"], 24576)
            self.assertEqual(limits["cgroup_avail_mib"], 30720)
            self.assertEqual(limits["cgroup_memory_max_mib"], 32768)
            # Reclaimable `.olean` file cache (28 GiB) must NOT throttle a build
            # down to 2048 MiB.
            self.assertGreater(limits["memory_max_mb"], 14000)
            self.assertGreater(cores, 0)

    def test_high_anon_shmem_throttles_available_memory(self) -> None:
        """32 GiB cgroup with 28 GiB `anon + shmem` and 2 GiB `file` cache
        must drop `cgroup_avail_mib` to 4 GiB (`4096 MiB`) and throttle
        `memory_max_mb`.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {28000 * MIB}\n"
                f"shmem {672 * MIB}\n"
                f"file {2048 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 28672)
            self.assertEqual(cg["cgroup_avail_mib"], 4096)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 48000)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertTrue(limits["is_cg_capped"])
            self.assertLessEqual(limits["memory_max_mb"], 4096)
            # File cache must stay un-penalized while 28 GiB anon+shmem
            # throttles build budget
            (leaf / "memory.stat").write_text(
                f"anon {2048 * MIB}\nshmem 0\nfile {2048 * MIB}\n",
                encoding="utf-8",
            )
            limits_reclaimable = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertLess(limits["memory_max_mb"], limits_reclaimable["memory_max_mb"])

    def test_cgroup_avail_exhausted_floors_mem_avail_at_512(self) -> None:
        """`anon + shmem` above `memory.max` clamps headroom to 0 and
        `mem_avail_mb` to 512.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{4096 * MIB}\n")
            _write_cgroup_file(leaf / "memory.current", f"{4200 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {4000 * MIB}\nshmem {200 * MIB}\nfile 0\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
                encoding="utf-8",
            )
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertEqual(cg["cgroup_avail_mib"], 0)
            self.assertEqual(cg["cgroup_memory_max_mib"], 4096)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 49152)
            build = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            # Fail-closed admission: exhausted 4 GiB cgroup must NOT unsafely
            # clamp up to >= 2048 MiB.
            self.assertLess(build["memory_max_mb"], 2048)
            file_limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="file",
                runtime_base=Path(tmp),
            )
            self.assertLessEqual(file_limits["memory_max_mb"], 1024)

    def test_ancestor_hierarchy_walk_and_root_container_cgroup(self) -> None:
        """Leaf has `memory.max = max`, parent and grandparent have finite
        limits.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            user_slice = cg_root / "user.slice"
            svc = user_slice / "agent-host.service"
            leaf = svc / "server"
            leaf.mkdir(parents=True)

            # Root: 30 GiB max, 5 GiB anon+shmem -> 25 GiB avail
            (cg_root / "memory.max").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"anon {5120 * MIB}\nshmem 0\nfile {10240 * MIB}\n",
                encoding="utf-8",
            )

            # user.slice: 24 GiB max, 10 GiB anon+shmem -> 14 GiB avail
            # (tightest avail)
            (user_slice / "memory.max").write_text(
                f"{24576 * MIB}\n", encoding="utf-8"
            )
            (user_slice / "memory.stat").write_text(
                f"anon {9216 * MIB}\nshmem {1024 * MIB}\nfile {8192 * MIB}\n",
                encoding="utf-8",
            )

            # svc: 20 GiB max (tightest max), 3 GiB anon+shmem -> 17 GiB avail
            (svc / "memory.max").write_text(
                f"{20480 * MIB}\n", encoding="utf-8"
            )
            (svc / "memory.stat").write_text(
                f"anon {3072 * MIB}\nshmem 0\nfile {6144 * MIB}\n",
                encoding="utf-8",
            )

            # leaf: unbounded max, 1 GiB anon+shmem
            (leaf / "memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.current").write_text(
                f"{4096 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {900 * MIB}\nshmem {124 * MIB}\nfile {3072 * MIB}\n",
                encoding="utf-8",
            )

            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/agent-host.service/server\n", encoding="utf-8"
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(
                cg["cgroup_path"], "/user.slice/agent-host.service/server"
            )
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_file_cache_mib"], 3072)
            self.assertEqual(cg["cgroup_current_mib"], 4096)
            self.assertEqual(cg["cgroup_memory_max_mib"], 20480)
            self.assertEqual(cg["cgroup_avail_mib"], 14336)

            # Also test 0::/ container root mapping
            proc_cg_root = Path(tmp) / "proc_cgroup_root"
            proc_cg_root.write_text("0::/\n", encoding="utf-8")
            cg_at_root = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg_root
            )
            self.assertTrue(cg_at_root["cgroup_v2"])
            self.assertEqual(cg_at_root["cgroup_path"], "/")
            self.assertEqual(cg_at_root["cgroup_memory_max_mib"], 30720)
            self.assertEqual(cg_at_root["cgroup_avail_mib"], 25600)

    def test_unbounded_hierarchy_keeps_host_ram_and_reports_unbounded(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "a.scope"
            _write_cgroup_file(cg_root / "user.slice" / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{3000 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {700 * MIB}\nshmem {100 * MIB}\nfile {2000 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/user.slice/a.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertIsNone(cg["cgroup_memory_max_mib"])
            self.assertIsNone(cg["cgroup_avail_mib"])
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 800)
            self.assertEqual(total_mb, 16384)
            self.assertEqual(avail_mb, 12288)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            line = alr.format_cgroup_probe_line(limits)
            self.assertIn("Cgroup v2 Envelope", line)
            self.assertIn("regime=uncapped", line)
            self.assertIn("W_slice_max=", line)

            bounded = dict(
                limits,
                is_cg_capped=True,
                c_high_mb=4096,
                a_lim_path="/sys/fs/cgroup/user.slice",
                w_slice_max_mb=3072,
                w_slice_high_mb=2764,
                w_live_mb=2500,
            )
            bounded_line = alr.format_cgroup_probe_line(bounded)
            self.assertIn("regime=capped", bounded_line)
            self.assertIn("C_high=4096 MiB (/sys/fs/cgroup/user.slice)", bounded_line)
            unavailable = alr.format_cgroup_probe_line(alr._empty_cgroup_info())
            self.assertIn("unavailable", unavailable)

    def test_ancestor_without_memory_stat_falls_back_to_current(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            parent = cg_root / "svc.slice"
            leaf = parent / "job.scope"
            # Parent: finite max, `memory.current` but no `memory.stat`.
            _write_cgroup_file(parent / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(parent / "memory.current", f"{6144 * MIB}\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{5120 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {1024 * MIB}\nshmem 0\nfile {4096 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/svc.slice/job.scope\n", encoding="utf-8")
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_memory_max_mib"], 8192)
            # 8192 - memory.current (6144) = 2048
            self.assertEqual(cg["cgroup_avail_mib"], 2048)

    def test_missing_memory_stat_fallback_and_non_v2_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # Ancestor with memory.max and memory.current + inactive_file only
            cg_root = Path(tmp) / "cgroup"
            cg_root.mkdir()
            (cg_root / "memory.max").write_text(
                f"{16384 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.current").write_text(
                f"{10240 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"inactive_file {6144 * MIB}\n", encoding="utf-8"
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/\n", encoding="utf-8")

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            # used = current (10240) - inactive_file (6144) = 4096 -> avail =
            # 16384 - 4096 = 12288
            self.assertEqual(cg["cgroup_avail_mib"], 12288)

            # Missing cgroup_root entirely -> graceful fallback
            cg_none = alr.probe_cgroup_v2_memory(
                cgroup_root=Path(tmp) / "nonexistent",
                proc_cgroup_path=proc_cg,
            )
            self.assertEqual(cg_none, alr._empty_cgroup_info())

    def test_cgroup_v1_only_and_escaping_paths_fall_back(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            _write_cgroup_file(cg_root / "memory.stat", f"anon {MIB}\n")
            _write_cgroup_file(cg_root / "memory.max", f"{1024 * MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"

            # cgroup v1-only host: no `0::` line even though files exist.
            proc_cg.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n", encoding="utf-8"
            )
            self.assertEqual(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                ),
                alr._empty_cgroup_info(),
            )

            # A path escaping the namespace root must never be followed.
            proc_cg.write_text("0::/../../escape.scope\n", encoding="utf-8")
            self.assertFalse(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )["cgroup_v2"]
            )

    def test_probe_never_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(leaf / "memory.stat", f"anon {MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )

            with mock.patch.object(
                alr, "parse_memory_stat", side_effect=RuntimeError("boom")
            ):
                cg = alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )
            self.assertEqual(cg, alr._empty_cgroup_info())

            with mock.patch.object(
                alr,
                "_probe_cgroup_v2_memory_impl",
                side_effect=PermissionError("EACCES"),
            ):
                env_err = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=cg_root,
                    proc_cgroup_path=proc_cg,
                    user_systemd_active=False,
                    cli_concurrency=1,
                    mode="build",
                    runtime_base=Path(tmp),
                )
                self.assertFalse(env_err["cgroup_v2"])
                self.assertEqual(env_err["mem_total_mb"], 16384)
                self.assertEqual(env_err["mem_avail_mb"], 12288)
                self.assertEqual(alr.format_cgroup_diagnostic_snapshot(), "")


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


class TestCliAndLimits(unittest.TestCase):
    """Tests mode detection, `-M` flag injection, `--probe` / `--print-limits`,
    and execution.
    """

    INT_KEYS = (
        "concurrency",
        "cpu_cores",
        "mem_total_mb",
        "mem_avail_mb",
        "threads",
        "memory_max_mb",
        "lean_m_mb",
        "timeout_sec",
        "build_slots",
    )
    OPTIONAL_INT_KEYS = (
        "cgroup_anon_mib",
        "cgroup_shmem_mib",
        "cgroup_anon_shmem_mib",
        "cgroup_file_cache_mib",
        "cgroup_current_mib",
        "cgroup_memory_max_mib",
        "cgroup_avail_mib",
    )

    def _assert_probe_json_schema(self, data: dict[str, Any]) -> None:
        for key in self.INT_KEYS:
            self.assertIn(key, data)
            self.assertIsInstance(data[key], int, key)
            self.assertNotIsInstance(data[key], bool, key)
        self.assertIsInstance(data["mode"], str)
        self.assertIsInstance(data["systemd_user_scope"], bool)
        self.assertIsInstance(data["cgroup_v2"], bool)
        self.assertTrue(
            data["cgroup_path"] is None or isinstance(data["cgroup_path"], str)
        )
        for key in self.OPTIONAL_INT_KEYS:
            self.assertIn(key, data)
            value = data[key]
            self.assertTrue(
                value is None
                or (isinstance(value, int) and not isinstance(value, bool)),
                f"{key}={value!r}",
            )

    def test_detect_mode_and_inject_lean_m_flag(self) -> None:
        self.assertEqual(alr.detect_mode(["lean", "Foo.lean"], "auto"), "file")
        self.assertEqual(
            alr.detect_mode(["lake", "env", "lean", "Foo.lean"], "auto"),
            "file",
        )
        self.assertEqual(
            alr.detect_mode(["lean", "--run", "Foo.lean"], "auto"), "build"
        )
        self.assertEqual(alr.detect_mode(["lake", "build"], "auto"), "build")
        self.assertEqual(
            alr.detect_mode(["lake", "build"], "file"), "file"
        )

        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "Foo.lean"], 4096),
            ["lean", "-M", "4096", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lake", "env", "lean", "Foo.lean"], 4096),
            ["lake", "env", "lean", "-M", "4096", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "-M", "2048", "Foo.lean"], 4096),
            ["lean", "-M", "2048", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lean", "-M2048", "Foo.lean"], 4096),
            ["lean", "-M2048", "Foo.lean"],
        )
        self.assertEqual(
            alr.inject_lean_m_flag(["lake", "build"], 4096),
            ["lake", "build"],
        )

    def test_probe_and_print_limits_cli_and_json(self) -> None:
        """Live host probe: both flags succeed and keep the full JSON schema."""
        for flag in ("--probe", "--print-limits"):
            buf = io.StringIO()
            with mock.patch("sys.stdout", buf):
                rc = alr.main([flag, "--json"])
            self.assertEqual(rc, 0)
            self._assert_probe_json_schema(json.loads(buf.getvalue()))

            text_buf = io.StringIO()
            with mock.patch("sys.stdout", text_buf):
                rc_txt = alr.main([flag])
            self.assertEqual(rc_txt, 0)
            self.assertIn("Cgroup v2", text_buf.getvalue())

    def test_probe_and_print_limits_are_identical_aliases(self) -> None:
        outputs: dict[tuple[str, bool], str] = {}
        fixed_env = alr.compute_workload_memory_envelope(
            cpu_cores=int(FIXED_HW["cpu_cores"]),
            mem_total_mb=int(FIXED_HW["mem_total_mb"]),
            mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
            ancestors=[
                {
                    "path": FIXED_HW["cgroup_path"],
                    "name": "anneal.scope",
                    "c_high_mb": FIXED_HW["cgroup_memory_max_mib"],
                    "w_mb": FIXED_HW["cgroup_anon_shmem_mib"],
                    "is_shared_user_slice": False,
                }
            ],
            cli_concurrency=2,
            mode="build",
        )
        for k in alr._empty_cgroup_info():
            fixed_env[k] = FIXED_HW[k]
        with mock.patch.object(alr, "probe_host_envelope", return_value=fixed_env):
            for flag in ("--probe", "--print-limits"):
                for as_json in (False, True):
                    buf = io.StringIO()
                    argv = [flag, "--concurrency", "2"] + (
                        ["--json"] if as_json else []
                    )
                    with mock.patch("sys.stdout", buf):
                        self.assertEqual(alr.main(argv), 0)
                    outputs[(flag, as_json)] = buf.getvalue()

        self.assertEqual(outputs[("--probe", False)], outputs[("--print-limits", False)])
        self.assertEqual(outputs[("--probe", True)], outputs[("--print-limits", True)])

        data = json.loads(outputs[("--probe", True)])
        self._assert_probe_json_schema(data)
        for key, value in fixed_env.items():
            self.assertEqual(data[key], value, key)
        self.assertEqual(data["mem_total_mb"], 32768)
        self.assertEqual(data["c_high_mb"], 20480)
        self.assertTrue(data["is_cg_capped"])
        self.assertFalse(data["systemd_user_scope"])

        text = outputs[("--probe", False)]
        self.assertIn("Cgroup v2 Envelope : regime=capped", text)
        self.assertIn("W_slice_max=", text)
        self.assertIn(f"(mode=build, W={data['w_eff']})", text)

    def test_systemd_scope_keeps_memory_max_and_zero_swap(self) -> None:
        _FakePopen.calls = []
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=int(FIXED_HW["cpu_cores"]),
            mem_total_mb=int(FIXED_HW["mem_total_mb"]),
            mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
            user_systemd_active=True,
            systemd_version=255,
            systemd_run_version=255,
            t_cg_is_user_service=True,
            cli_concurrency=2,
            mode="file",
        )
        with mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr, "resolve_runtime_base", return_value=(Path("/tmp"), True)), \
             mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
             mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
             mock.patch.object(alr.subprocess, "Popen", _FakePopen):
            rc = alr.main(
                [
                    "--mode",
                    "file",
                    "--concurrency",
                    "2",
                    "--no-slot-lock",
                    "--",
                    "lean",
                    "Foo.lean",
                ]
            )
        self.assertEqual(rc, 0)
        self.assertEqual(len(_FakePopen.calls), 1)
        argv, kwargs = _FakePopen.calls[0]
        self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
        self.assertIn("--quiet", argv)
        self.assertIn("--slice=anneal-workloads.slice", argv)
        self.assertIn(f"MemoryMax={limits['memory_max_mb']}M", argv)
        self.assertIn("MemorySwapMax=0", argv)
        self.assertIn("OOMPolicy=kill", argv)
        self.assertIn(f"CPUQuota={limits['threads'] * 100}%", argv)
        self.assertIn(f"RuntimeMaxSec={limits['timeout_sec'] + 5}s", argv)
        sep_idx = argv.index("--")
        inner = argv[sep_idx + 1 :]
        self.assertIn("oom_score_adj", inner[2])
        self.assertEqual(inner[4:], ["lean", "-M", str(limits["lean_m_mb"]), "Foo.lean"])
        self.assertTrue(kwargs.get("start_new_session"))
        self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_IN_SCOPE"], "1")
        expected_lean_threads = str(
            alr._resolve_thread_env(limits["threads"], limits["is_cg_capped"])["LEAN_NUM_THREADS"]
        )
        self.assertEqual(kwargs["env"]["LEAN_NUM_THREADS"], expected_lean_threads)

    def test_run_bounded_command_success_and_timeout(self) -> None:
        rc_file = alr.main(
            [
                "--mode",
                "file",
                "--no-slot-lock",
                "--concurrency",
                "1",
                "--memory-max-mb",
                "512",
                "--",
                "true",
            ]
        )
        self.assertEqual(rc_file, 0)

        rc_build = alr.main(
            [
                "--mode",
                "build",
                "--no-slot-lock",
                "--concurrency",
                "1",
                "--memory-max-mb",
                "512",
                "--",
                "true",
            ]
        )
        self.assertEqual(rc_build, 0)

        rc_exit = alr.main(
            [
                "--no-slot-lock",
                "--concurrency",
                "1",
                "--memory-max-mb",
                "512",
                "--",
                "sh",
                "-c",
                "exit 3",
            ]
        )
        self.assertEqual(rc_exit, 3)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)
        ):
            rc_timeout = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "1",
                    "--memory-max-mb",
                    "512",
                    "--no-slot-lock",
                    "--",
                    "python3",
                    "-c",
                    "import time; time.sleep(10)",
                ]
            )
        self.assertEqual(rc_timeout, 124)
        err = err_buf.getvalue()
        self.assertIn("Command timed out after 1s", err)
        self.assertIn(
            "Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M, current=6912M, "
            "memory.max=unbounded",
            err,
        )

    def test_in_process_passthrough_cannot_replace_the_test_runner(self) -> None:
        """A leaked `ANNEAL_LEAN_RUN_IN_SCOPE=1` fails loudly instead of
        `exec`ing the command over the unittest runner (which would end the run
        early with exit 0).
        """
        self.assertNotIn("ANNEAL_LEAN_RUN_IN_SCOPE", os.environ)
        # Check the guards before provoking the pass-through: without them the
        # call below would really replace this process.  The direct calls name a
        # missing binary, so even an unguarded primitive could only raise.
        self.assertEqual(len(_EXEC_GUARDS), len(_GUARDED_EXEC_FUNCTIONS))
        missing_bin = "/nonexistent/anneal-test-exec"
        for name, call_args in (
            ("execv", (missing_bin, ["anneal-test-exec"])),
            ("execve", (missing_bin, ["anneal-test-exec"], {})),
            ("execvp", (missing_bin, ["anneal-test-exec"])),
            ("execvpe", (missing_bin, ["anneal-test-exec"], {})),
        ):
            self.assertIsInstance(getattr(os, name), mock.Mock, name)
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                getattr(os, name)(*call_args)
        for name, call_args in (
            ("execl", (missing_bin, "anneal-test-exec")),
            ("execle", (missing_bin, "anneal-test-exec", {})),
            ("execlp", (missing_bin, "anneal-test-exec")),
            ("execlpe", (missing_bin, "anneal-test-exec", {})),
        ):
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                getattr(os, name)(*call_args)
        with mock.patch.dict(os.environ, {"ANNEAL_LEAN_RUN_IN_SCOPE": "1"}):
            with self.assertRaisesRegex(AssertionError, "replace the unittest runner"):
                alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
        self.assertNotIn("ANNEAL_LEAN_RUN_IN_SCOPE", os.environ)

    def test_command_execution_leaves_live_user_systemd_alone(self) -> None:
        """Under the isolated manager `UnitPath`, running a command neither
        rewrites `anneal-workloads.slice` nor reloads the host's `systemd
        --user`, even when the client shell overrides `XDG_CONFIG_HOME`.
        """
        if _SLICE_UNIT_SEED is None:
            self.skipTest("no delegated systemd --user: the slice unit is never reconciled")
        unit = alr._workloads_slice_unit_path()
        assert unit is not None
        assert _MGR_UNIT_TMPDIR is not None
        assert _XDG_TMPDIR is not None
        self.assertEqual(unit.parents[2], Path(_MGR_UNIT_TMPDIR.name))
        self.assertNotEqual(unit.parents[2], Path(_XDG_TMPDIR.name))
        before = _file_identity(unit)
        self.assertEqual(before[2], _SLICE_UNIT_SEED)

        real_run = subprocess.run
        seen: list[list[str]] = []

        def spy(argv: list[str], *args: Any, **kwargs: Any) -> Any:
            seen.append([str(a) for a in argv])
            return real_run(argv, *args, **kwargs)

        with tempfile.TemporaryDirectory(prefix="anneal-client-xdg-") as client_xdg:
            with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": client_xdg}), mock.patch.object(
                alr.subprocess, "run", side_effect=spy
            ):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual([argv for argv in seen if "daemon-reload" in argv], [])
            self.assertEqual(_file_identity(unit), before)
            self.assertFalse(
                (Path(client_xdg) / "systemd" / "user" / "anneal-workloads.slice").exists()
            )

        # Positive control: when the manager's `UnitPath` points to an unseeded
        # directory while `XDG_CONFIG_HOME` points elsewhere, reconciliation
        # writes into the manager's `UnitPath` (never the client's XDG path).
        seen.clear()
        with tempfile.TemporaryDirectory(prefix="anneal-unseeded-mgr-") as unseeded_mgr, \
             tempfile.TemporaryDirectory(prefix="anneal-mismatch-xdg-") as mismatch_xdg:
            mgr_unit_dir = Path(unseeded_mgr) / "systemd" / "user"

            def stub(argv: list[str], *args: Any, **kwargs: Any) -> Any:
                cmd_strs = [str(a) for a in argv]
                seen.append(cmd_strs)
                if cmd_strs[1:] == ["--user", "show", "-p", "UnitPath", "--value"]:
                    return subprocess.CompletedProcess(
                        argv,
                        0,
                        f"{mgr_unit_dir}.control /run/systemd/user {mgr_unit_dir}\n",
                        "",
                    )
                if "daemon-reload" in cmd_strs:
                    return subprocess.CompletedProcess(argv, 0, "", "")
                return real_run(argv, *args, **kwargs)

            with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": mismatch_xdg}), mock.patch.object(
                alr.subprocess, "run", side_effect=stub
            ):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len([argv for argv in seen if "daemon-reload" in argv]), 1)
            written = mgr_unit_dir / "anneal-workloads.slice"
            self.assertEqual(written.read_text(encoding="utf-8"), _SLICE_UNIT_SEED)
            self.assertFalse(
                (Path(mismatch_xdg) / "systemd" / "user" / "anneal-workloads.slice").exists()
            )

    def test_timeout_captures_cgroup_snapshot_before_terminating_process(self) -> None:
        """On timeout, the live child scope (`pid=proc.pid`) must be sampled
        before `_kill_systemd_scope`.
        """
        events: list[tuple[str, int | None]] = []
        orig_snap = alr.format_cgroup_diagnostic_snapshot
        orig_kill = alr._kill_systemd_scope

        def spy_snap(
            cg: dict[str, Any] | None = None, pid: int | None = None
        ) -> str:
            events.append(("snap", pid))
            return orig_snap(cg=dict(FAKE_CGROUP_INFO), pid=pid)

        def spy_kill(unit_name, proc, rt_base, sock_alive, grace_sec=2.0) -> None:
            events.append(("term", proc.pid))
            orig_kill(unit_name, proc, rt_base, sock_alive, grace_sec=grace_sec)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), mock.patch.object(
            alr, "format_cgroup_diagnostic_snapshot", side_effect=spy_snap
        ), mock.patch.object(
            alr, "_kill_systemd_scope", side_effect=spy_kill
        ):
            rc = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "1",
                    "--memory-max-mb",
                    "512",
                    "--no-slot-lock",
                    "--",
                    "python3",
                    "-c",
                    "import time; time.sleep(10)",
                ]
            )
        self.assertEqual(rc, 124)
        self.assertEqual([e[0] for e in events], ["snap", "term"])
        self.assertIsNotNone(events[0][1])
        self.assertEqual(events[0][1], events[1][1])

    def test_snapshot_probes_child_pid_cgroup_first(self) -> None:
        if not Path("/proc/self/cgroup").is_file():
            self.skipTest("requires Linux /proc/<pid>/cgroup")
        child = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(30)"],
            stdin=subprocess.DEVNULL,
        )
        try:
            probed: list[Path] = []

            def spy(
                cgroup_root: Path = Path("/sys/fs/cgroup"),
                proc_cgroup_path: Path = Path("/proc/self/cgroup"),
            ) -> dict[str, Any]:
                probed.append(proc_cgroup_path)
                return dict(FAKE_CGROUP_INFO)

            with mock.patch.object(alr, "probe_cgroup_v2_memory", side_effect=spy):
                snap = alr.format_cgroup_diagnostic_snapshot(pid=child.pid)
            self.assertEqual(probed, [Path(f"/proc/{child.pid}/cgroup")])
            self.assertIn("anon+shmem=1234M", snap)
        finally:
            child.kill()
            child.wait()

    def test_timeout_snapshot_samples_live_child_scope(self) -> None:
        """End to end: the 124 snapshot reports the child's own systemd scope
        (its `MemoryMax` and resident `anon` heap), sampled before the kill."""
        if not _can_launch_live_systemd_scope():
            self.skipTest("systemd-run --user --scope unavailable")
        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf):
            rc = alr.main(
                [
                    "--mode",
                    "file",
                    "--timeout",
                    "3",
                    "--memory-max-mb",
                    "1536",
                    "--no-slot-lock",
                    "--",
                    sys.executable,
                    "-c",
                    "import time; b = bytearray(128 * 1024 * 1024); time.sleep(30)",
                ]
            )
        self.assertEqual(rc, 124)
        err = err_buf.getvalue()
        self.assertIn("memory.max=1536M (avail=", err)
        match = re.search(r"Cgroup v2 Snapshot : anon\+shmem=(\d+)M", err)
        self.assertIsNotNone(match, err)
        assert match is not None
        self.assertGreaterEqual(int(match.group(1)), 120)

    def test_oom_exit_137_diagnostic_includes_cgroup_snapshot(self) -> None:
        # Non-systemd path: honest non-cgroup 137 diagnostic + cgroup snapshot.
        err_buf = io.StringIO()
        non_systemd_limits = alr.compute_workload_memory_envelope(
            cpu_cores=8,
            mem_total_mb=32768,
            mem_avail_mb=24576,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="file",
        )
        with mock.patch("sys.stderr", err_buf), \
             mock.patch.object(alr, "probe_host_envelope", return_value=non_systemd_limits), \
             mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)):
            rc = alr.main(
                ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
            )
        self.assertEqual(rc, 137)
        err = err_buf.getvalue()
        self.assertIn("no cgroup MemoryMax was active", err)
        self.assertNotIn("MemorySwapMax=0", err)
        self.assertIn("Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M", err)

        # Scoped systemd path: reports Memory guard ONLY when `oom_kill > 0`.
        with tempfile.TemporaryDirectory(prefix="anneal-oom-diag-") as td:
            scoped_limits = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=True,
                systemd_version=255,
                systemd_run_version=255,
                t_cg_is_user_service=True,
                w_cg_path=td,
                cli_concurrency=1,
                mode="file",
            )

            class _Scoped137Proc:
                pid = 2**22 + 12346

                def __init__(self, _argv: Any, **kwargs: Any) -> None:
                    marker = (kwargs.get("env") or {}).get("ANNEAL_LEAN_RUN_SCOPE_MARKER")
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")

                def wait(self, timeout: float | None = None) -> int:
                    return 137

                def poll(self) -> int:
                    return 137

            # Case 1: oom_kill == 0 -> honest non-certain message (NOT
            # "terminated by OS memory guard").
            non_oom_err = io.StringIO()
            with mock.patch("sys.stderr", non_oom_err), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scoped_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "_read_memory_events_oom_kill", return_value=0), \
                 mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)), \
                 mock.patch.object(alr.subprocess, "Popen", _Scoped137Proc):
                rc_non_oom = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
                )
            self.assertEqual(rc_non_oom, 137)
            s_non = non_oom_err.getvalue()
            self.assertIn("oom_kill was not observed", s_non)
            self.assertIn("MemorySwapMax=0", s_non)
            self.assertNotIn("terminated by the OS memory guard", s_non)

            # Case 2: oom_kill > 0 -> confirms OS memory guard OOM kill.
            oom_err = io.StringIO()
            with mock.patch("sys.stderr", oom_err), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scoped_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "_read_memory_events_oom_kill", return_value=1), \
                 mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO)), \
                 mock.patch.object(alr.subprocess, "Popen", _Scoped137Proc):
                rc_oom = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
                )
            self.assertEqual(rc_oom, 137)
            s_oom = oom_err.getvalue()
            self.assertIn("terminated by the OS memory guard", s_oom)
            self.assertIn("cgroup OOM kill", s_oom)
            self.assertIn("MemorySwapMax=0", s_oom)
            self.assertIn("Cgroup v2 Snapshot : anon+shmem=1234M, file=5678M", s_oom)

    def test_oom_snapshot_prefers_target_scope_over_wrapper_cgroup(self) -> None:
        """OOM diagnostics must read the child scope cgroup, not
        `/proc/self/cgroup`.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-scope-oom-") as td:
            slice_cg = Path(td) / "anneal-workloads.slice"
            slice_cg.mkdir()
            _write_cgroup_file(slice_cg / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(slice_cg / "memory.current", f"{256 * MIB}\n")
            _write_cgroup_file(
                slice_cg / "memory.stat",
                f"anon {200 * MIB}\nshmem 0\nfile {56 * MIB}\n",
            )
            scoped_limits = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=True,
                systemd_version=260,
                systemd_run_version=260,
                t_cg_is_user_service=True,
                w_cg_path=str(slice_cg),
                cli_concurrency=1,
                mode="file",
                override_mem_mb=512,
            )

            class _FakeScopeOomProc:
                pid = 2**22 + 12347

                def __init__(self, argv: list[str], **kwargs: Any) -> None:
                    marker = (kwargs.get("env") or {}).get("ANNEAL_LEAN_RUN_SCOPE_MARKER")
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")
                    unit_flag = [a for a in argv if a.startswith("--unit=")][0]
                    unit = unit_flag.split("=", 1)[1]
                    scope_dir = slice_cg / unit
                    _write_cgroup_file(scope_dir / "memory.max", f"{512 * MIB}\n")
                    _write_cgroup_file(scope_dir / "memory.current", f"{400 * MIB}\n")
                    _write_cgroup_file(scope_dir / "memory.peak", f"{512 * MIB}\n")
                    _write_cgroup_file(
                        scope_dir / "memory.stat",
                        f"anon {390 * MIB}\nshmem {10 * MIB}\nfile {16 * MIB}\n",
                    )
                    _write_cgroup_file(scope_dir / "memory.events", "oom 1\noom_kill 1\n")

                def wait(self, timeout: float | None = None) -> int:
                    return -9

                def poll(self) -> int:
                    return -9

            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scoped_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(
                     alr,
                     "probe_cgroup_v2_memory",
                     side_effect=AssertionError("must not fall back to wrapper cgroup"),
                 ), \
                 mock.patch.object(alr.subprocess, "Popen", _FakeScopeOomProc):
                rc = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--memory-max-mb", "512", "--", "true"]
                )
            self.assertEqual(rc, 137)
            err = err_buf.getvalue()
            self.assertIn("anon+shmem=400M", err)
            self.assertIn("memory.max=512M", err)
            self.assertIn("peak=512M", err)
            self.assertIn("[target scope]", err)

    def test_collected_scope_oom_uses_parent_slice_delta_and_live_oom(self) -> None:
        """Definitive OOM fires even if `--collect` removes scope_cg."""
        with tempfile.TemporaryDirectory(prefix="anneal-slice-oom-") as td:
            slice_cg = Path(td) / "anneal-workloads.slice"
            slice_cg.mkdir()
            _write_cgroup_file(slice_cg / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(slice_cg / "memory.current", f"{256 * MIB}\n")
            _write_cgroup_file(
                slice_cg / "memory.stat",
                f"anon {200 * MIB}\nshmem 0\nfile {56 * MIB}\n",
            )
            _write_cgroup_file(slice_cg / "memory.events", "oom 0\noom_kill 5\n")
            scoped_limits = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=True,
                systemd_version=260,
                systemd_run_version=260,
                t_cg_is_user_service=True,
                w_cg_path=str(slice_cg),
                cli_concurrency=1,
                mode="file",
                override_mem_mb=512,
            )

            class _CollectedOomProc:
                pid = 2**22 + 12348

                def __init__(self, _argv: list[str], **kwargs: Any) -> None:
                    marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")
                    # Simulate scope collected while parent slice increments.
                    _write_cgroup_file(
                        slice_cg / "memory.events", "oom 1\noom_kill 6\n"
                    )

                def wait(self, timeout: float | None = None) -> int:
                    return -9

                def poll(self) -> int:
                    return -9

            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scoped_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _CollectedOomProc):
                rc = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--memory-max-mb", "512", "--", "true"]
                )
            self.assertEqual(rc, 137)
            err = err_buf.getvalue()
            self.assertIn("terminated by the OS memory guard", err)
            self.assertIn("[target slice (scope collected)]", err)

            # Cold-slice case: `anneal-workloads.slice` does not exist in
            # cgroupfs before `Popen` and is lazily created by `systemd-run`
            # with `oom_kill = 1` while `--collect` removes `scope_cg`.
            cold_slice_cg = Path(td) / "cold-anneal-workloads.slice"
            self.assertFalse(cold_slice_cg.exists())
            cold_limits = dict(scoped_limits, w_cg_path=str(cold_slice_cg))

            class _ColdSliceCollectedOomProc:
                pid = 2**22 + 12350

                def __init__(self, _argv: list[str], **kwargs: Any) -> None:
                    marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")
                    cold_slice_cg.mkdir()
                    _write_cgroup_file(cold_slice_cg / "memory.max", "max\n")
                    _write_cgroup_file(cold_slice_cg / "memory.current", "0\n")
                    _write_cgroup_file(
                        cold_slice_cg / "memory.peak", f"{32 * MIB}\n"
                    )
                    _write_cgroup_file(
                        cold_slice_cg / "memory.stat",
                        "anon 0\nshmem 0\nfile 0\n",
                    )
                    _write_cgroup_file(
                        cold_slice_cg / "memory.events", "oom 1\noom_kill 1\n"
                    )

                def wait(self, timeout: float | None = None) -> int:
                    return 137

                def poll(self) -> int:
                    return 137

            cold_err_buf = io.StringIO()
            with mock.patch("sys.stderr", cold_err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=cold_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _ColdSliceCollectedOomProc):
                rc_cold = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--memory-max-mb", "32", "--", "true"]
                )
            self.assertEqual(rc_cold, 137)
            cold_err = cold_err_buf.getvalue()
            self.assertIn(
                "terminated by the OS memory guard (cgroup OOM kill", cold_err
            )
            self.assertIn("peak=32M", cold_err)
            self.assertIn("[target slice (scope collected)]", cold_err)

            # Collected-slice fallback: both `scope_cg` and the workload slice
            # are already collected before `proc.wait` returns, while `t_cg`
            # (`user@<uid>.service`) records the hierarchical `oom_kill` delta.
            user_cg = Path(td) / "user@1000.service"
            user_cg.mkdir()
            _write_cgroup_file(user_cg / "memory.max", "max\n")
            _write_cgroup_file(user_cg / "memory.current", f"{64 * MIB}\n")
            _write_cgroup_file(
                user_cg / "memory.stat",
                f"anon {64 * MIB}\nshmem 0\nfile 0\n",
            )
            _write_cgroup_file(
                user_cg / "memory.events", "oom 10\noom_kill 10\n"
            )
            transient_slice_cg = user_cg / "anneal.slice" / "anneal-workloads.slice"
            gc_limits = dict(
                scoped_limits,
                w_cg_path=str(transient_slice_cg),
                t_cg_path=str(user_cg),
            )

            class _BothCollectedOomProc:
                pid = 2**22 + 12351

                def __init__(self, _argv: list[str], **kwargs: Any) -> None:
                    marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")
                    _write_cgroup_file(
                        user_cg / "memory.events", "oom 11\noom_kill 11\n"
                    )

                def wait(self, timeout: float | None = None) -> int:
                    return 137

                def poll(self) -> int:
                    return 137

            gc_err_buf = io.StringIO()
            with mock.patch("sys.stderr", gc_err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=gc_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _BothCollectedOomProc):
                rc_gc = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--memory-max-mb", "32", "--", "true"]
                )
            self.assertEqual(rc_gc, 137)
            gc_err = gc_err_buf.getvalue()
            self.assertIn(
                "terminated by the OS memory guard (cgroup OOM kill", gc_err
            )
            self.assertIn("[user service cgroup (scope collected)]", gc_err)

        if _can_launch_live_systemd_scope():
            err_live = io.StringIO()
            with mock.patch("sys.stderr", err_live):
                rc_live = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--memory-max-mb",
                        "32",
                        "--",
                        sys.executable,
                        "-c",
                        "b = bytearray(128 * 1024 * 1024); print(len(b))",
                    ]
                )
            self.assertEqual(rc_live, 137)
            self.assertIn(
                "terminated by the OS memory guard (cgroup OOM kill",
                err_live.getvalue(),
            )

    def test_probe_reports_insufficient_headroom_instead_of_zero_ram_cap(self) -> None:
        """Low `MemAvailable` prints `insufficient headroom`, not `0 MiB`."""
        zero_limits = alr.compute_workload_memory_envelope(
            cpu_cores=8,
            mem_total_mb=32768,
            mem_avail_mb=0,
            user_systemd_active=True,
            systemd_version=260,
            systemd_run_version=260,
            t_cg_is_user_service=True,
            cli_concurrency=1,
            mode="build",
        )
        self.assertEqual(zero_limits["memory_max_mb"], 0)
        out_txt = io.StringIO()
        with mock.patch("sys.stdout", out_txt), \
             mock.patch.object(alr, "probe_host_envelope", return_value=zero_limits), \
             mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"):
            rc_txt = alr.main(["--probe"])
        self.assertEqual(rc_txt, 0)
        txt = out_txt.getvalue()
        self.assertIn("insufficient headroom", txt)
        self.assertNotIn("Hard RAM Cap       : 0 MiB", txt)

        out_json = io.StringIO()
        with mock.patch("sys.stdout", out_json), \
             mock.patch.object(alr, "probe_host_envelope", return_value=zero_limits), \
             mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"):
            rc_json = alr.main(["--probe", "--json"])
        self.assertEqual(rc_json, 0)
        self.assertEqual(json.loads(out_json.getvalue())["memory_max_mb"], 0)


class TestCallerLoweredThreadCount(unittest.TestCase):
    """A caller's lower positive `LEAN_NUM_THREADS` is what the command runs
    with and what the timeout / OOM diagnostics report, never the envelope's
    larger thread budget.
    """

    THREAD_VARS = ("LEAN_NUM_THREADS", "CARGO_BUILD_JOBS", "RAYON_NUM_THREADS")

    def _limits(self, cpu_cores: int, mode: str = "file", **overrides: Any) -> dict[str, Any]:
        """Synthetic uncapped host envelope whose thread budget is `cpu_cores`.
        """
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=cpu_cores,
            mem_total_mb=262144,
            mem_avail_mb=200000,
            user_systemd_active=False,
            cli_concurrency=1,
            mode=mode,
        )
        self.assertEqual(limits["threads"], cpu_cores)
        self.assertFalse(limits["is_cg_capped"])
        self.assertFalse(limits["user_systemd_active"])
        limits.update(overrides)
        return limits

    def _run(
        self,
        limits: dict[str, Any] | list[dict[str, Any]],
        argv: list[str],
        thread_env: dict[str, str],
        *,
        direct: bool = False,
    ) -> tuple[int, str, list[dict[str, str]]]:
        """Runs `alr.main(argv)` (or `run_bounded_command` when `direct`)
        against synthetic `limits` with exactly `thread_env` of the three thread
        variables exported.

        Returns `(exit code, stderr, environments of the launched commands)`.
        """
        real_popen = subprocess.Popen
        child_envs: list[dict[str, str]] = []

        def spy_popen(popen_argv: Any, *args: Any, **kwargs: Any) -> Any:
            env = kwargs.get("env")
            if env is not None and env.get("ANNEAL_LEAN_RUN_IN_SCOPE") == "1":
                child_envs.append(dict(env))
            return real_popen(popen_argv, *args, **kwargs)

        probe_replies = [dict(lim) for lim in (limits if isinstance(limits, list) else [limits])]
        probe_calls = 0

        def fake_probe(**kwargs: Any) -> dict[str, Any]:
            nonlocal probe_calls
            reply = dict(probe_replies[min(probe_calls, len(probe_replies) - 1)])
            probe_calls += 1
            override_timeout = kwargs.get("override_timeout_sec")
            if override_timeout is not None and override_timeout > 0:
                reply["timeout_sec"] = int(override_timeout)
            return reply

        err_buf = io.StringIO()
        with contextlib.ExitStack() as stack:
            stack.enter_context(mock.patch.dict(os.environ, thread_env))
            for var in self.THREAD_VARS:
                if var not in thread_env:
                    os.environ.pop(var, None)
            stack.enter_context(mock.patch.object(alr, "probe_host_envelope", side_effect=fake_probe))
            stack.enter_context(
                mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=dict(FAKE_CGROUP_INFO))
            )
            stack.enter_context(mock.patch.object(alr.subprocess, "Popen", side_effect=spy_popen))
            stack.enter_context(mock.patch("sys.stderr", err_buf))
            if direct:
                rc = alr.run_bounded_command(
                    argv,
                    probe_replies[0],
                    use_slot_lock=False,
                    probe_fn=fake_probe,
                )
            else:
                rc = alr.main(argv)
        return rc, err_buf.getvalue(), child_envs

    def test_oversized_thread_counts_fall_back_to_the_budget_without_raising(self) -> None:
        parse = alr._parse_positive_thread_count
        limit = alr._MAX_THREAD_COUNT_DIGITS
        self.assertEqual(limit, 9)
        # Up to `limit` significant digits parse; leading zeros are not
        # significant.
        self.assertEqual(parse("9" * limit), 10**limit - 1)
        self.assertEqual(parse("0" * 5000 + "8"), 8)
        self.assertEqual(parse(" 007 "), 7)
        # All-zero strings of any length are not positive.
        for zeros in ("0", "000", "0" * 5000):
            self.assertIsNone(parse(zeros), len(zeros))
        # One digit more overflows the tools' 32-bit job counts, and past
        # `sys.get_int_max_str_digits()` (4300) digits `int()` raises
        # `ValueError`.
        oversized = ("1" + "0" * limit, "9" * 4300, "9" * 4301, "9" * 20000, "0" * 3 + "9" * 5000)
        for raw in oversized:
            self.assertIsNone(parse(raw), len(raw))
        for capped in (False, True):
            for raw in oversized:
                env = dict.fromkeys(self.THREAD_VARS, raw)
                self.assertEqual(
                    alr._resolve_thread_env(3, capped, env),
                    dict.fromkeys(self.THREAD_VARS, 3),
                    (capped, len(raw)),
                )
                self.assertEqual(alr.format_threads_diagnostic(3, env), "threads=3", (capped, len(raw)))
        # The child environment never carries the oversized value through.
        with mock.patch.dict(os.environ, dict.fromkeys(self.THREAD_VARS, "9" * 5000)):
            child = alr._build_child_env(
                threads=4,
                lean_m_mb=1024,
                is_cg_capped=False,
                runtime_base=Path("/tmp"),
                user_systemd_sock_alive=False,
            )
        self.assertEqual({var: child[var] for var in self.THREAD_VARS}, dict.fromkeys(self.THREAD_VARS, "4"))

    def test_resolve_thread_env_keeps_lower_positive_caller_values(self) -> None:
        resolve = alr._resolve_thread_env
        self.assertEqual(alr._THREAD_ENV_VARS, self.THREAD_VARS)
        for capped in (False, True):
            for budget in (1, 3, 64):
                at_budget = dict.fromkeys(self.THREAD_VARS, budget)
                # Unset, blank, non-numeric, zero, negative, signed, underscore,
                # non-ASCII digit, or non-ASCII whitespace values: fall back to
                # the envelope's budget.
                self.assertEqual(resolve(budget, capped, {}), at_budget)
                for raw in (
                    "",
                    "   ",
                    "abc",
                    "1.5",
                    "0",
                    "-2",
                    "+1",
                    "1_2",
                    "\u0661",
                    "\u00a01\u00a0",
                    "\u20032",
                    "\u30004",
                    "\x851",
                ):
                    env = dict.fromkeys(self.THREAD_VARS, raw)
                    self.assertEqual(resolve(budget, capped, env), at_budget, (capped, budget, raw))
                # A positive value at or below the budget always wins, in both
                # regimes.
                for raw, want in (("1", 1), (" 1 ", 1), (str(budget), budget)):
                    env = dict.fromkeys(self.THREAD_VARS, raw)
                    self.assertEqual(
                        resolve(budget, capped, env),
                        dict.fromkeys(self.THREAD_VARS, want),
                        (capped, budget, raw),
                    )
        # Defensive clamp: a non-positive budget still yields at least 1 thread.
        for bad_budget in (0, -3):
            self.assertEqual(resolve(bad_budget, True, {}), dict.fromkeys(self.THREAD_VARS, 1))
            self.assertEqual(
                resolve(bad_budget, True, {"LEAN_NUM_THREADS": "4"}),
                dict.fromkeys(self.THREAD_VARS, 1),
            )
            self.assertEqual(alr.format_threads_diagnostic(bad_budget, None), "threads=1")
            self.assertEqual(
                alr.format_threads_diagnostic(bad_budget, {"LEAN_NUM_THREADS": "4"}),
                "threads=4, thread_budget=1",
            )
        # A value above the budget is clamped on a memory-capped slice only.
        self.assertEqual(resolve(3, True, {"LEAN_NUM_THREADS": "64"})["LEAN_NUM_THREADS"], 3)
        self.assertEqual(resolve(3, False, {"LEAN_NUM_THREADS": "64"})["LEAN_NUM_THREADS"], 64)
        # Each variable is resolved on its own.
        self.assertEqual(
            resolve(8, True, {"LEAN_NUM_THREADS": "1", "CARGO_BUILD_JOBS": "4"}),
            {"LEAN_NUM_THREADS": 1, "CARGO_BUILD_JOBS": 4, "RAYON_NUM_THREADS": 8},
        )
        # Default source is the ambient environment, which is only read.
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}):
            for var in self.THREAD_VARS[1:]:
                os.environ.pop(var, None)
            before = dict(os.environ)
            self.assertEqual(
                resolve(64, False),
                {"LEAN_NUM_THREADS": 1, "CARGO_BUILD_JOBS": 64, "RAYON_NUM_THREADS": 64},
            )
            self.assertEqual(dict(os.environ), before)

    def test_build_child_env_and_diagnostic_field_report_the_lowered_count(self) -> None:
        for budget in (3, 64):
            for capped in (False, True):
                base_env = {"PATH": "/usr/bin", "LEAN_NUM_THREADS": "1"}
                env = alr._build_child_env(
                    threads=budget,
                    lean_m_mb=1024,
                    is_cg_capped=capped,
                    runtime_base=Path("/tmp"),
                    user_systemd_sock_alive=False,
                    base_env=base_env,
                )
                self.assertEqual(base_env, {"PATH": "/usr/bin", "LEAN_NUM_THREADS": "1"})
                self.assertEqual(env["LEAN_NUM_THREADS"], "1")
                self.assertEqual(env["CARGO_BUILD_JOBS"], str(budget))
                self.assertEqual(env["RAYON_NUM_THREADS"], str(budget))
                self.assertEqual(
                    alr.format_threads_diagnostic(budget, env), f"threads=1, thread_budget={budget}"
                )
        # No caller value: the budget itself, with no separate budget field.
        env = alr._build_child_env(
            threads=3,
            lean_m_mb=1024,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env={"PATH": "/usr/bin"},
        )
        self.assertEqual([env[var] for var in self.THREAD_VARS], ["3", "3", "3"])
        self.assertEqual(alr.format_threads_diagnostic(3, env), "threads=3")
        # A larger caller value: clamped (and reported as the budget) on a
        # capped slice, kept (and reported with the budget next to it) on an
        # uncapped host.
        for capped, lean_threads, diag in (
            (True, "3", "threads=3"),
            (False, "64", "threads=64, thread_budget=3"),
        ):
            env = alr._build_child_env(
                threads=3,
                lean_m_mb=1024,
                is_cg_capped=capped,
                runtime_base=Path("/tmp"),
                user_systemd_sock_alive=False,
                base_env={"PATH": "/usr/bin", "LEAN_NUM_THREADS": "64"},
            )
            self.assertEqual(env["LEAN_NUM_THREADS"], lean_threads)
            self.assertEqual(alr.format_threads_diagnostic(3, env), diag)
        # Without a usable child value the field falls back to the budget.
        for child_env in (
            None,
            {},
            {"LEAN_NUM_THREADS": ""},
            {"LEAN_NUM_THREADS": "x"},
            {"LEAN_NUM_THREADS": "0"},
            {"LEAN_NUM_THREADS": "-1"},
            {"LEAN_NUM_THREADS": "+1"},
            {"LEAN_NUM_THREADS": "1_2"},
            {"LEAN_NUM_THREADS": "\u0661"},
            {"LEAN_NUM_THREADS": "\u00a01\u00a0"},
            {"LEAN_NUM_THREADS": "\u20031"},
        ):
            self.assertEqual(alr.format_threads_diagnostic(3, child_env), "threads=3", child_env)

    def test_cpu_quota_stays_at_the_thread_budget(self) -> None:
        with mock.patch.dict(os.environ, {"LEAN_NUM_THREADS": "1"}), mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ):
            argv, in_scope = alr._build_scope_launch_cmd(
                ["lake", "build"],
                b_max_mb=4096,
                threads=64,
                timeout_sec=60,
                user_systemd_active=True,
                unit_name="anneal-run-test.scope",
                systemd_version=255,
                systemd_run_version=255,
            )
        self.assertTrue(in_scope)
        self.assertIn("CPUQuota=6400%", argv)
        self.assertEqual([a for a in argv if a.startswith("CPUQuota=")], ["CPUQuota=6400%"])

    def test_timeout_diagnostic_logs_caller_lowered_lean_num_threads(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        for budget in (3, 64):
            rc, err, child_envs = self._run(self._limits(budget), sleeper, {"LEAN_NUM_THREADS": "1"})
            self.assertEqual(rc, 124)
            self.assertEqual(len(child_envs), 1)
            self.assertEqual(child_envs[0]["LEAN_NUM_THREADS"], "1")
            self.assertEqual(child_envs[0]["CARGO_BUILD_JOBS"], str(budget))
            self.assertIn("Command timed out after 1s (mode=file,", err)
            self.assertIn(f"no cgroup MemoryMax, threads=1, thread_budget={budget}).\n", err)
            self.assertNotIn(f"threads={budget}", err)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), ["1"])

    def test_timeout_diagnostic_without_caller_value_logs_the_budget(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        rc, err, child_envs = self._run(self._limits(3), sleeper, {})
        self.assertEqual(rc, 124)
        self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], ["3"])
        self.assertIn("no cgroup MemoryMax, threads=3).\n", err)
        self.assertNotIn("thread_budget", err)

    def test_timeout_diagnostic_on_capped_slice_clamps_high_and_rejects_invalid(self) -> None:
        sleeper = ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "30"]
        capped = self._limits(3, is_cg_capped=True)
        for thread_env, want_threads, want_field in (
            ({"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=3"),
            ({"LEAN_NUM_THREADS": "64"}, "3", "threads=3"),
            ({"LEAN_NUM_THREADS": "1_2"}, "3", "threads=3"),
        ):
            rc, err, child_envs = self._run(capped, sleeper, thread_env)
            self.assertEqual(rc, 124, thread_env)
            self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], [want_threads], thread_env)
            self.assertIn(f"no cgroup MemoryMax, {want_field}).\n", err, thread_env)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), [want_threads], thread_env)

    def test_pressure_abort_diagnostic_logs_effective_lean_num_threads(self) -> None:
        # Watchdog ancestor-pressure aborts report the same effective thread
        # count as timeout / OOM diagnostics.
        capped = self._limits(
            3,
            mode="build",
            is_cg_capped=True,
            user_systemd_active=True,
            systemd_version=255,
            systemd_run_version=255,
            t_cg_is_user_service=False,
        )

        class _InstantAbortWatchdog:
            def __init__(self, **_kwargs: Any) -> None:
                pass

            def tick(self, _now: float) -> dict[str, Any]:
                return {"action": "abort_pressure", "breach_ticks": 3}

        fake_clock = {"t": 100.0}

        class _TimeoutOnceProc:
            pid = 2**22 + 12349

            def __init__(self, *_args: Any, **kwargs: Any) -> None:
                self._done = False
                marker = (kwargs.get("env") or {}).get(
                    "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                )
                if marker:
                    Path(marker).write_text("1", encoding="utf-8")

            def wait(self, timeout: float | None = None) -> int:
                if not self._done:
                    fake_clock["t"] += float(timeout or 0.0)
                    if fake_clock["t"] < 102.0:
                        raise subprocess.TimeoutExpired(
                            cmd=["sleep"], timeout=timeout or 0
                        )
                    self._done = True
                    raise subprocess.TimeoutExpired(cmd=["sleep"], timeout=timeout or 0)
                return -9

            def poll(self) -> int | None:
                return -9 if self._done else None

        for thread_env, want_field in (
            ({"LEAN_NUM_THREADS": "1"}, "threads=1, thread_budget=3"),
            ({}, "threads=3"),
        ):
            fake_clock["t"] = 100.0
            err_buf = io.StringIO()
            with contextlib.ExitStack() as stack:
                stack.enter_context(mock.patch.dict(os.environ, thread_env))
                for var in self.THREAD_VARS:
                    if var not in thread_env:
                        os.environ.pop(var, None)
                stack.enter_context(
                    mock.patch.object(
                        alr.time, "monotonic", side_effect=lambda: fake_clock["t"]
                    )
                )
                stack.enter_context(mock.patch.object(alr, "_build_scope_launch_cmd", return_value=(["true"], True)))
                stack.enter_context(mock.patch.object(alr, "BuildWatchdog", _InstantAbortWatchdog))
                stack.enter_context(mock.patch.object(alr.subprocess, "Popen", _TimeoutOnceProc))
                stack.enter_context(mock.patch.object(alr, "_kill_systemd_scope"))
                stack.enter_context(mock.patch("sys.stderr", err_buf))
                rc = alr.run_bounded_command(
                    ["lake", "build"],
                    capped,
                    use_slot_lock=False,
                    probe_fn=lambda **_kw: dict(capped),
                )
            self.assertEqual(rc, 137, thread_env)
            err = err_buf.getvalue()
            self.assertIn("USER_SLICE_PRESSURE_ABORT:", err)
            self.assertIn(f"(mode=build, {want_field}, budget_gb=", err, thread_env)

    def test_oom_diagnostic_logs_caller_lowered_lean_num_threads(self) -> None:
        oom = ["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"]
        for budget, thread_env, lean_threads, field in (
            (3, {"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=3"),
            (64, {"LEAN_NUM_THREADS": "1"}, "1", "threads=1, thread_budget=64"),
            (64, {"LEAN_NUM_THREADS": " 2 "}, "2", "threads=2, thread_budget=64"),
            (3, {}, "3", "threads=3"),
            (3, {"LEAN_NUM_THREADS": "0"}, "3", "threads=3"),
            (3, {"LEAN_NUM_THREADS": "64"}, "64", "threads=64, thread_budget=3"),
        ):
            rc, err, child_envs = self._run(self._limits(budget), oom, thread_env)
            self.assertEqual(rc, 137, thread_env)
            self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], [lean_threads], thread_env)
            self.assertIn("no cgroup MemoryMax was active; mode=file, lean -M", err)
            self.assertIn(f"{field}).\n", err, thread_env)
            self.assertEqual(re.findall(r"\bthreads=(\d+)", err), [lean_threads], thread_env)
        # On a memory-capped slice a larger caller value is clamped to the
        # budget.
        capped = self._limits(3, is_cg_capped=True)
        rc, err, child_envs = self._run(capped, oom, {"LEAN_NUM_THREADS": "64"})
        self.assertEqual(rc, 137)
        self.assertEqual([env["LEAN_NUM_THREADS"] for env in child_envs], ["3"])
        self.assertIn("mode=file, lean -M", err)
        self.assertIn("threads=3).", err)
        self.assertNotIn("thread_budget", err)

    def test_probe_text_reports_effective_lean_num_threads(self) -> None:
        for limits, cases in (
            (
                self._limits(64, mode="build"),
                (
                    ({"LEAN_NUM_THREADS": "1"}, 1),
                    ({"LEAN_NUM_THREADS": "64"}, 64),
                    ({"LEAN_NUM_THREADS": "128"}, 128),
                    ({}, 64),
                    ({"LEAN_NUM_THREADS": "-1"}, 64),
                    ({"LEAN_NUM_THREADS": "1_2"}, 64),
                ),
            ),
            (
                self._limits(3, mode="build", is_cg_capped=True),
                (
                    ({"LEAN_NUM_THREADS": "1"}, 1),
                    ({"LEAN_NUM_THREADS": "64"}, 3),
                    ({}, 3),
                    ({"LEAN_NUM_THREADS": "0"}, 3),
                    ({"LEAN_NUM_THREADS": "abc"}, 3),
                    ({"LEAN_NUM_THREADS": "\u0661"}, 3),
                ),
            ),
        ):
            budget = limits["threads"]
            for thread_env, lean_threads in cases:
                out = io.StringIO()
                with mock.patch("sys.stdout", out):
                    rc, _err, child_envs = self._run(limits, ["--probe"], thread_env)
                self.assertEqual(rc, 0)
                self.assertEqual(child_envs, [])
                self.assertIn(
                    f"Thread Budget (-j) : {budget} threads (LEAN_NUM_THREADS={lean_threads})\n",
                    out.getvalue(),
                    (limits["is_cg_capped"], thread_env),
                )
                # The JSON contract keeps reporting the envelope's budget.
                out = io.StringIO()
                with mock.patch("sys.stdout", out):
                    rc, _err, _envs = self._run(limits, ["--probe", "--json"], thread_env)
                self.assertEqual(rc, 0)
                self.assertEqual(json.loads(out.getvalue()), limits)


class TestCliSubprocess(unittest.TestCase):
    """Runs `anneal/ci/anneal-lean-run` as a real subprocess
    (`stdin=/dev/null`).

    Every subprocess is isolated from the invoking host: ambient `ANNEAL_LEAN_*`
    / `ANNEAL_WORKTREE_*` variables are scrubbed, and `XDG_CONFIG_HOME` is a
    fresh empty directory unless `env_extra` provides one.
    """

    def _run_isolated(
        self, argv: list[str], env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="anneal-cli-xdg-") as xdg_dir:
            return subprocess.run(
                argv,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                env=_isolated_cli_env(Path(xdg_dir), env_extra),
                timeout=120,
            )

    def _cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        return self._run_isolated([sys.executable, str(SCRIPT_PATH), *args], env_extra)

    def _synthetic_cli(
        self,
        host_root: Path,
        cgroup_name: str,
        *args: str,
        env_extra: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """`_cli` against synthetic host `host_root` / `cgroup_name` (same
        isolation).
        """
        return self._run_isolated(
            [
                sys.executable,
                "-B",
                "-c",
                _SYNTHETIC_HOST_CLI_SHIM,
                str(SCRIPT_PATH),
                str(host_root),
                cgroup_name,
                *args,
            ],
            env_extra,
        )

    def _probe_json(self, res: subprocess.CompletedProcess[str]) -> dict[str, Any]:
        self.assertEqual(res.returncode, 0, res.stderr)
        data = json.loads(res.stdout)
        self.assertIsInstance(data, dict)
        return data

    def _assert_concurrency(self, data: dict[str, Any], expected: int) -> None:
        for key in ("concurrency", "w_eff", "build_slots"):
            self.assertEqual(data[key], expected, key)

    @staticmethod
    def _host_bounded(requested: int, data: dict[str, Any]) -> int:
        """Concurrency the probed host grants for `requested`: cgroup-capped
        hosts clamp it to `s_heavy_safe`, uncapped hosts honor it.
        """
        if data["is_cg_capped"]:
            return min(requested, data["s_heavy_safe"])
        return requested

    def test_cli_probe_and_execution(self) -> None:
        if os.access(SCRIPT_PATH, os.X_OK):
            direct = self._run_isolated([str(SCRIPT_PATH), "--print-limits", "--json"])
            self.assertIn("cgroup_avail_mib", self._probe_json(direct))

        probe = self._cli("--probe")
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertIn("Cgroup v2", probe.stdout)

        # An isolated probe sees no host override at all: neither ambient
        # `ANNEAL_*` variables nor
        # `{$XDG_CONFIG_HOME,~/.config}/anneal/concurrency`.
        default = self._probe_json(self._cli("--probe", "--json"))
        if default["user_systemd_active"] and alr._find_systemd_run() is not None:
            self.assertIn("Hard RAM Cap", probe.stdout)
        else:
            self.assertNotIn("Hard RAM Cap", probe.stdout)
            self.assertIn("none (no systemd scope", probe.stdout)
        self._assert_concurrency(default, 1)
        self.assertEqual(default["mode"], "build")
        self.assertEqual(default["timeout_sec"], 900)

        data = self._probe_json(
            self._cli(
                "--probe",
                "--json",
                env_extra={
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                    "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                    "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                },
            )
        )
        self._assert_concurrency(data, self._host_bounded(2, data))
        expected_mem = (
            min(3000, data["w_slice_max_mb"]) if data["is_cg_capped"] else 3000
        )
        self.assertEqual(data["memory_max_mb"], expected_mem)
        if data["w_slice_max_mb"] >= 3000:
            self.assertEqual(data["memory_max_mb"], 3000)
        self.assertEqual(data["timeout_sec"], 77)

        # `--unsafe-ignore-cgroup` only lifts the `w_slice_max_mb` clamp on an
        # explicit `--memory-max-mb`.  It neither flips `is_cg_capped` nor
        # un-clamps concurrency, so the sibling probe reports `is_cg_capped is
        # False` / `concurrency == 2` exactly on uncapped hosts and stays
        # clamped to `s_heavy_safe` on capped ones.
        unsafe = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertIs(unsafe["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe, self._host_bounded(2, unsafe))

        over_cap_mb = data["w_slice_max_mb"] + 1024
        capped_data = self._probe_json(
            self._cli(
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(
            capped_data["memory_max_mb"],
            min(over_cap_mb, capped_data["w_slice_max_mb"])
            if capped_data["is_cg_capped"]
            else over_cap_mb,
        )
        self._assert_concurrency(capped_data, self._host_bounded(2, capped_data))

        unsafe_data = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(unsafe_data["memory_max_mb"], over_cap_mb)
        self.assertIs(unsafe_data["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe_data, self._host_bounded(2, unsafe_data))

        # A populated `$XDG_CONFIG_HOME/anneal/concurrency` is read, and is
        # subject to the same host bound with or without
        # `--unsafe-ignore-cgroup`.
        with tempfile.TemporaryDirectory(prefix="anneal-xdg-cfg-") as cfg_dir:
            _write_cgroup_file(Path(cfg_dir) / "anneal" / "concurrency", "3\n")
            for flags in ((), ("--unsafe-ignore-cgroup",)):
                cfg_data = self._probe_json(
                    self._cli(
                        *flags,
                        "--probe",
                        "--json",
                        env_extra={"XDG_CONFIG_HOME": cfg_dir},
                    )
                )
                self._assert_concurrency(cfg_data, self._host_bounded(3, cfg_data))

        bad_env = self._probe_json(
            self._cli(
                "--probe", "--json", env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "abc"}
            )
        )
        self._assert_concurrency(bad_env, 1)

        flag_data = self._probe_json(
            self._cli(
                "--concurrency", "1", "--memory-max-mb", "2500", "--timeout", "60",
                "--probe", "--json",
            )
        )
        self._assert_concurrency(flag_data, 1)
        self.assertEqual(
            flag_data["memory_max_mb"],
            min(2500, flag_data["w_slice_max_mb"])
            if flag_data["is_cg_capped"]
            else 2500,
        )
        self.assertEqual(flag_data["timeout_sec"], 60)

        # Command-executing runs reconcile `anneal-workloads.slice` under
        # `XDG_CONFIG_HOME`. Give them a seeded one and check they leave it
        # untouched: no rewrite, hence no `systemctl --user daemon-reload` of
        # the host's live user manager.
        with tempfile.TemporaryDirectory(prefix="anneal-cli-run-xdg-") as run_xdg:
            unit = _seed_workloads_slice_unit(Path(run_xdg))
            before = None if unit is None else _file_identity(unit)
            run_cases = [
                (
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ],
                    0,
                ),
                (
                    [
                        "--no-slot-lock",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "sh",
                        "-c",
                        "exit 5",
                    ],
                    5,
                ),
                (
                    [
                        "--mode",
                        "build",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ],
                    0,
                ),
            ]
            for argv, expected_rc in run_cases:
                res = self._cli(*argv, env_extra={"XDG_CONFIG_HOME": run_xdg})
                self.assertEqual(res.returncode, expected_rc, (argv, res.stderr))
            if unit is not None:
                self.assertEqual(_file_identity(unit), before)

        usage = self._cli()
        self.assertEqual(usage.returncode, 2)

    def test_cli_synthetic_hosts_cover_uncapped_and_capped_regimes(self) -> None:
        """Both cgroup regimes through the real CLI, whichever host runs the
        tests.
        """
        # host -> concurrency granted for a requested 2 (environment /
        # `--concurrency`) and for a requested 3
        # (`$XDG_CONFIG_HOME/anneal/concurrency`).
        granted = {"cg_uncapped": (2, 3), "cg_capped_1": (1, 1), "cg_capped_2": (2, 2)}
        with tempfile.TemporaryDirectory(prefix="anneal-synth-host-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            xdg_three = root / "xdg_three"
            _write_cgroup_file(xdg_three / "anneal" / "concurrency", "3\n")
            for cg_name, ceiling_mib, capped, s_heavy_safe in SYNTHETIC_HOSTS:
                _write_synthetic_cgroup_root(root, cg_name, ceiling_mib)
                conc_for_2, conc_for_3 = granted[cg_name]

                def probe(
                    *args: str,
                    env_extra: dict[str, str] | None = None,
                    cg_name: str = cg_name,
                ) -> dict[str, Any]:
                    return self._probe_json(
                        self._synthetic_cli(
                            root, cg_name, *args, "--probe", "--json", env_extra=env_extra
                        )
                    )

                with self.subTest(host=cg_name):
                    default = probe()
                    self.assertIs(default["is_cg_capped"], capped)
                    self.assertEqual(default["s_heavy_safe"], s_heavy_safe)
                    self.assertEqual(default["cpu_cores"], SYNTHETIC_HOST_CORES)
                    self.assertEqual(default["mem_total_mb"], 65536)
                    self._assert_concurrency(default, 1)
                    self.assertEqual(default["timeout_sec"], 900)
                    w_slice_max_mb = default["w_slice_max_mb"]
                    self.assertGreater(w_slice_max_mb, 3000)

                    overridden = probe(
                        env_extra={
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                            "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                            "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                        }
                    )
                    self._assert_concurrency(overridden, conc_for_2)
                    self.assertEqual(overridden["memory_max_mb"], 3000)
                    self.assertEqual(overridden["timeout_sec"], 77)

                    unsafe = probe(
                        "--unsafe-ignore-cgroup",
                        env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
                    )
                    self.assertIs(unsafe["is_cg_capped"], capped)
                    self._assert_concurrency(unsafe, conc_for_2)

                    self._assert_concurrency(probe("--concurrency", "2"), conc_for_2)

                    for flags in ((), ("--unsafe-ignore-cgroup",)):
                        from_file = probe(
                            *flags, env_extra={"XDG_CONFIG_HOME": str(xdg_three)}
                        )
                        self.assertIs(from_file["is_cg_capped"], capped)
                        self._assert_concurrency(from_file, conc_for_3)

                    # Host concurrency file acts as the floor for env
                    # concurrency, while explicit `--concurrency` during
                    # `--probe` overrides `w_eff` yet leaves `build_slots`
                    # pinned to the host file value.
                    file_plus_env = probe(
                        env_extra={
                            "XDG_CONFIG_HOME": str(xdg_three),
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        }
                    )
                    self._assert_concurrency(file_plus_env, conc_for_3)
                    file_plus_cli = probe(
                        "--concurrency",
                        "1",
                        env_extra={"XDG_CONFIG_HOME": str(xdg_three)},
                    )
                    self.assertEqual(file_plus_cli["concurrency"], 1)
                    self.assertEqual(file_plus_cli["w_eff"], 1)
                    self.assertEqual(file_plus_cli["build_slots"], conc_for_3)

                    over_cap_mb = w_slice_max_mb + 1024
                    for clamp_args, clamp_env in (
                        (("--memory-max-mb", str(over_cap_mb)), None),
                        ((), {"ANNEAL_LEAN_MEMORY_MAX_MB": str(over_cap_mb)}),
                    ):
                        clamped = probe(*clamp_args, env_extra=clamp_env)
                        expected_clamped = w_slice_max_mb if capped else over_cap_mb
                        self.assertEqual(clamped["memory_max_mb"], expected_clamped)
                        self.assertEqual(
                            clamped["lean_m_mb"], (75 * expected_clamped) // 100
                        )
                        lifted = probe(
                            "--unsafe-ignore-cgroup", *clamp_args, env_extra=clamp_env
                        )
                        self.assertEqual(lifted["memory_max_mb"], over_cap_mb)
                        self.assertEqual(lifted["lean_m_mb"], (75 * over_cap_mb) // 100)
                        self.assertIs(lifted["is_cg_capped"], capped)
                        self._assert_concurrency(lifted, 1)

    def test_scrubbed_prefixes_cover_every_anneal_variable_of_the_script(self) -> None:
        """An `ANNEAL_*` variable added to `anneal/ci/anneal-lean-run` must be
        scrubbed too.
        """
        names = set(
            re.findall(r"ANNEAL_[A-Z0-9_]+", SCRIPT_PATH.read_text(encoding="utf-8"))
        )
        for known in (
            "ANNEAL_WORKTREE_CONCURRENCY",
            "ANNEAL_LEAN_MEMORY_MAX_MB",
            "ANNEAL_LEAN_TIMEOUT_SEC",
            "ANNEAL_LEAN_RUN_IN_SCOPE",
            "ANNEAL_LEAN_RUN_SCOPE_MARKER",
        ):
            self.assertIn(known, names)
        self.assertEqual(
            sorted(n for n in names if not n.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)),
            [],
        )

    def test_cli_isolation_scrubs_poisoned_ambient_environment(self) -> None:
        """Neither ambient `ANNEAL_*` overrides nor host concurrency files reach
        `_cli`.

        Runs on an uncapped synthetic host, where a leaked concurrency override
        would be honored verbatim instead of being hidden by a capped host's
        `s_heavy_safe == 1` clamp.
        """
        ambient_overrides = {
            "ANNEAL_WORKTREE_CONCURRENCY": "6",
            "ANNEAL_LEAN_MEMORY_MAX_MB": "17",
            "ANNEAL_LEAN_TIMEOUT_SEC": "55",
        }
        with tempfile.TemporaryDirectory(prefix="anneal-ambient-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            poisoned_xdg = root / "poisoned_xdg"
            _write_cgroup_file(poisoned_xdg / "anneal" / "concurrency", "7\n")
            poisoned_home = root / "poisoned_home"
            _write_cgroup_file(
                poisoned_home / ".config" / "anneal" / "concurrency", "5\n"
            )
            poison = {
                **ambient_overrides,
                "HOME": str(poisoned_home),
                "XDG_CONFIG_HOME": str(poisoned_xdg),
                "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
            }

            def synthetic(env_extra: dict[str, str] | None = None) -> dict[str, Any]:
                return self._probe_json(
                    self._synthetic_cli(
                        root, "cg_uncapped", "--probe", "--json", env_extra=env_extra
                    )
                )

            clean = synthetic()
            self.assertIs(clean["is_cg_capped"], False)
            self._assert_concurrency(clean, 1)
            self.assertEqual(clean["timeout_sec"], 900)
            clean_file = self._probe_json(
                self._synthetic_cli(
                    root, "cg_uncapped", "--mode", "file", "--probe", "--json"
                )
            )
            self.assertGreater(clean_file["lean_m_mb"], 99)
            live_clean = self._probe_json(self._cli("--probe", "--json"))
            child_env_cmd = [
                sys.executable,
                "-c",
                "import json, os; print(json.dumps({"
                "k: os.environ.get(k) for k in ("
                "'ANNEAL_LEAN_RUN_LEAN_M_MB', 'ANNEAL_WORKTREE_CONCURRENCY'"
                ")}))",
            ]

            with mock.patch.dict(os.environ, poison):
                fresh_xdg = root / "fresh_xdg"
                env = _isolated_cli_env(fresh_xdg)
                self.assertEqual(
                    [k for k in env if k.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)], []
                )
                self.assertEqual(env["XDG_CONFIG_HOME"], str(fresh_xdg))
                # `env_extra` is applied after the scrub, so explicit overrides
                # survive it.
                explicit = _isolated_cli_env(
                    fresh_xdg,
                    {
                        "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        "XDG_CONFIG_HOME": str(poisoned_xdg),
                    },
                )
                self.assertEqual(explicit["ANNEAL_WORKTREE_CONCURRENCY"], "2")
                self.assertEqual(explicit["XDG_CONFIG_HOME"], str(poisoned_xdg))
                self.assertNotIn("ANNEAL_LEAN_MEMORY_MAX_MB", explicit)
                self.assertNotIn("ANNEAL_LEAN_TIMEOUT_SEC", explicit)

                isolated = synthetic()
                isolated_exec = self._synthetic_cli(
                    root,
                    "cg_uncapped",
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--",
                    *child_env_cmd,
                )
                live = self._probe_json(self._cli("--probe", "--json"))
                direct = (
                    self._probe_json(
                        self._run_isolated(
                            [str(SCRIPT_PATH), "--print-limits", "--json"]
                        )
                    )
                    if os.access(SCRIPT_PATH, os.X_OK)
                    else None
                )

            # The synthetic host is deterministic: a poisoned parent changes
            # nothing.
            self.assertEqual(isolated, clean)
            self.assertEqual(isolated_exec.returncode, 0, isolated_exec.stderr)
            self.assertEqual(
                json.loads(isolated_exec.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": str(clean_file["lean_m_mb"]),
                    "ANNEAL_WORKTREE_CONCURRENCY": None,
                },
            )
            for live_data in (live, direct):
                if live_data is not None:
                    self._assert_concurrency(live_data, 1)
                    self.assertEqual(live_data["timeout_sec"], 900)
                    if live_clean["memory_max_mb"] != 17:
                        self.assertNotEqual(live_data["memory_max_mb"], 17)

            # Positive controls: each poison is honored once passed explicitly,
            # so the equality above is not vacuous.
            leaked_env = synthetic(env_extra=ambient_overrides)
            self._assert_concurrency(leaked_env, 6)
            self.assertEqual(leaked_env["memory_max_mb"], 17)
            self.assertEqual(leaked_env["timeout_sec"], 55)
            leaked_xdg = synthetic(env_extra={"XDG_CONFIG_HOME": str(poisoned_xdg)})
            self._assert_concurrency(leaked_xdg, 7)
            # `XDG_CONFIG_HOME=""` falls back to `$HOME/.config`, which the
            # isolated non-empty `XDG_CONFIG_HOME` of `_cli` therefore masks.
            leaked_home = synthetic(
                env_extra={"HOME": str(poisoned_home), "XDG_CONFIG_HOME": ""}
            )
            self._assert_concurrency(leaked_home, 5)
            leaked_passthrough = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--no-slot-lock",
                "--",
                *child_env_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_WORKTREE_CONCURRENCY": "4",
                },
            )
            self.assertEqual(leaked_passthrough.returncode, 0, leaked_passthrough.stderr)
            self.assertEqual(
                json.loads(leaked_passthrough.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_WORKTREE_CONCURRENCY": "4",
                },
            )

    def test_cli_synthetic_hosts_honor_caller_lowered_lean_num_threads_end_to_end(self) -> None:
        """Real subprocess CLI on both uncapped and cgroup-capped synthetic
        hosts: `LEAN_NUM_THREADS=1` flows to `--probe` text and the executed
        child while leaving `CARGO_BUILD_JOBS`/`RAYON_NUM_THREADS` at the host
        budget, and oversized values clamp strictly on the capped host.
        """
        dump_threads = [
            sys.executable,
            "-c",
            "import json, os; print(json.dumps({k: os.environ.get(k) for k in "
            "('LEAN_NUM_THREADS', 'CARGO_BUILD_JOBS', 'RAYON_NUM_THREADS')}))",
        ]
        with tempfile.TemporaryDirectory(prefix="anneal-synth-threads-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            for cg_name, ceiling_mib, capped in (
                ("cg_uncapped", None, False),
                ("cg_capped_1", 12288, True),
            ):
                _write_synthetic_cgroup_root(root, cg_name, ceiling_mib)
                probe_json = self._probe_json(
                    self._synthetic_cli(root, cg_name, "--mode", "build", "--probe", "--json")
                )
                self.assertIs(probe_json["is_cg_capped"], capped)
                budget = probe_json["threads"]
                self.assertGreater(budget, 1)

                # Lower positive `LEAN_NUM_THREADS=1` wins in both regimes.
                probe_txt = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--probe",
                    env_extra={"LEAN_NUM_THREADS": "1"},
                )
                self.assertEqual(probe_txt.returncode, 0, probe_txt.stderr)
                self.assertIn(
                    f"Thread Budget (-j) : {budget} threads (LEAN_NUM_THREADS=1)\n",
                    probe_txt.stdout,
                )
                run_low = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--no-slot-lock",
                    "--",
                    *dump_threads,
                    env_extra={"LEAN_NUM_THREADS": "1", "CARGO_BUILD_JOBS": "", "RAYON_NUM_THREADS": ""},
                )
                self.assertEqual(run_low.returncode, 0, run_low.stderr)
                self.assertEqual(
                    json.loads(run_low.stdout),
                    {
                        "LEAN_NUM_THREADS": "1",
                        "CARGO_BUILD_JOBS": str(budget),
                        "RAYON_NUM_THREADS": str(budget),
                    },
                )

                # Oversized `LEAN_NUM_THREADS=99` clamps on capped hosts and is
                # kept on uncapped hosts.
                want_high = budget if capped else 99
                run_high = self._synthetic_cli(
                    root,
                    cg_name,
                    "--mode",
                    "build",
                    "--no-slot-lock",
                    "--",
                    *dump_threads,
                    env_extra={"LEAN_NUM_THREADS": "99", "CARGO_BUILD_JOBS": "", "RAYON_NUM_THREADS": ""},
                )
                self.assertEqual(run_high.returncode, 0, run_high.stderr)
                self.assertEqual(
                    json.loads(run_high.stdout)["LEAN_NUM_THREADS"],
                    str(want_high),
                )

    def test_build_child_env_exports_slots_and_mem_mb_overwriting_stale(self) -> None:
        """`_build_child_env` exports integer-formatted `ANNEAL_LEAN_RUN_SLOTS`
        and `ANNEAL_LEAN_RUN_MEM_MB` and overwrites any stale inherited values.
        """
        base_env = {
            "PATH": "/usr/bin",
            "ANNEAL_LEAN_RUN_SLOTS": "99",
            "ANNEAL_LEAN_RUN_MEM_MB": "999999",
        }
        child = alr._build_child_env(
            threads=4,
            lean_m_mb=3072,
            is_cg_capped=False,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=3,
            memory_max_mb=4096,
        )
        self.assertEqual(base_env["ANNEAL_LEAN_RUN_SLOTS"], "99")
        self.assertEqual(base_env["ANNEAL_LEAN_RUN_MEM_MB"], "999999")
        self.assertEqual(child["ANNEAL_LEAN_RUN_SLOTS"], "3")
        self.assertEqual(child["ANNEAL_LEAN_RUN_MEM_MB"], "4096")
        self.assertEqual(child["ANNEAL_LEAN_RUN_LEAN_M_MB"], "3072")

        zero_child = alr._build_child_env(
            threads=1,
            lean_m_mb=0,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=0,
            memory_max_mb=0,
        )
        self.assertEqual(zero_child["ANNEAL_LEAN_RUN_SLOTS"], "0")
        self.assertEqual(zero_child["ANNEAL_LEAN_RUN_MEM_MB"], "0")

        neg_child = alr._build_child_env(
            threads=1,
            lean_m_mb=-5,
            is_cg_capped=True,
            runtime_base=Path("/tmp"),
            user_systemd_sock_alive=False,
            base_env=base_env,
            granted_slots=-2,
            memory_max_mb=-10,
        )
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_SLOTS"], "0")
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_MEM_MB"], "0")
        self.assertEqual(neg_child["ANNEAL_LEAN_RUN_LEAN_M_MB"], "0")

    def test_systemd_scope_and_direct_exec_export_budget_env_vars(self) -> None:
        """Both `systemd-run --user --scope` and direct non-systemd execution
        export `ANNEAL_LEAN_RUN_SLOTS` (0 for unslotted/`--no-slot-lock`, 1 for
        shared-slot, `build_slots` for `--exclusive`) and
        `ANNEAL_LEAN_RUN_MEM_MB` (`memory_max_mb`), overwriting stale values.
        """
        stale_env = {
            "ANNEAL_LEAN_RUN_SLOTS": "99",
            "ANNEAL_LEAN_RUN_MEM_MB": "999999",
        }

        with tempfile.TemporaryDirectory(prefix="anneal-slots-rt-") as rt_tmp:
            rt_path = Path(rt_tmp)

            # 1. `systemd-run --user --scope` shared-slot build -> SLOTS=1.
            _FakePopen.calls = []
            scope_limits = alr.compute_workload_memory_envelope(
                cpu_cores=int(FIXED_HW["cpu_cores"]),
                mem_total_mb=int(FIXED_HW["mem_total_mb"]),
                mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
                user_systemd_active=True,
                systemd_version=255,
                systemd_run_version=255,
                t_cg_is_user_service=True,
                cli_concurrency=3,
                mode="build",
                runtime_base=str(rt_path),
            )
            self.assertEqual(scope_limits["build_slots"], 3)
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scope_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
            self.assertIn(f"MemoryMax={scope_limits['memory_max_mb']}M", argv)
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "1")
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(scope_limits["memory_max_mb"])
            )

            # 2. `systemd-run --user --scope` with `--exclusive` sets
            # SLOTS=build_slots.
            _FakePopen.calls = []
            excl_limits = alr.compute_workload_memory_envelope(
                cpu_cores=int(FIXED_HW["cpu_cores"]),
                mem_total_mb=int(FIXED_HW["mem_total_mb"]),
                mem_avail_mb=int(FIXED_HW["mem_avail_mb"]),
                user_systemd_active=True,
                systemd_version=255,
                systemd_run_version=255,
                t_cg_is_user_service=True,
                cli_concurrency=3,
                exclusive=True,
                mode="build",
                runtime_base=str(rt_path),
            )
            self.assertEqual(excl_limits["build_slots"], 3)
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=excl_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--exclusive", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:4], ["/usr/bin/systemd-run", "--user", "--scope", "--collect"])
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], str(excl_limits["build_slots"])
            )
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(excl_limits["memory_max_mb"])
            )

            # 3. `--no-slot-lock` on build mode -> SLOTS=0.
            _FakePopen.calls = []
            with mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scope_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--no-slot-lock", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            _, kwargs = _FakePopen.calls[0]
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "0")
            self.assertEqual(
                kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(scope_limits["memory_max_mb"])
            )

            # 4. Direct non-systemd execution (unslotted file mode -> SLOTS=0,
            #    shared-slot build mode -> SLOTS=1, `--exclusive` -> SLOTS=2).
            direct_file = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=False,
                t_cg_is_user_service=False,
                cli_concurrency=2,
                mode="file",
                override_mem_mb=6144,
                runtime_base=str(rt_path),
            )
            self.assertEqual(direct_file["build_slots"], 2)
            self.assertEqual(direct_file["memory_max_mb"], 6144)
            _FakePopen.calls = []
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=direct_file), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, False)), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--concurrency",
                        "2",
                        "--memory-max-mb",
                        "6144",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 1)
            argv, kwargs = _FakePopen.calls[0]
            self.assertEqual(argv[:2], ["/bin/sh", "-c"])
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "0")
            self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], "6144")

            direct_build = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=False,
                t_cg_is_user_service=False,
                cli_concurrency=2,
                mode="build",
                override_mem_mb=6144,
                runtime_base=str(rt_path),
            )
            for extra_args, want_slots in (([], "1"), (["--exclusive"], "2"), (["--no-slot-lock"], "0")):
                _FakePopen.calls = []
                with mock.patch("sys.stderr", io.StringIO()), \
                     mock.patch.dict(os.environ, stale_env, clear=False), \
                     mock.patch.object(alr, "probe_host_envelope", return_value=direct_build), \
                     mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, False)), \
                     mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                    rc = alr.main(
                        [
                            "--mode",
                            "build",
                            "--concurrency",
                            "2",
                            "--memory-max-mb",
                            "6144",
                            *extra_args,
                            "--",
                            "true",
                        ]
                    )
                self.assertEqual(rc, 0)
                self.assertEqual(len(_FakePopen.calls), 1)
                argv, kwargs = _FakePopen.calls[0]
                self.assertEqual(argv[:2], ["/bin/sh", "-c"])
                self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], want_slots, extra_args)
                self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], "6144", extra_args)

            # 5. `systemd-run` launch failure falling back to direct execution
            #    keeps the exact exported `ANNEAL_LEAN_RUN_SLOTS` & `MEM_MB`.
            _FakePopen.calls = []

            class _FailScopeThenPass(_FakePopen):
                def __init__(self, argv: list[str], **kwargs: Any) -> None:
                    super().__init__(argv, **kwargs)
                    if argv and argv[0] == "/usr/bin/systemd-run":
                        raise OSError("synthetic systemd-run launch failure")

            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.dict(os.environ, stale_env, clear=False), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=scope_limits), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(rt_path, True)), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FailScopeThenPass):
                rc = alr.main(
                    ["--mode", "build", "--concurrency", "3", "--", "true"]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(len(_FakePopen.calls), 2)
            fb_argv, fb_kwargs = _FakePopen.calls[1]
            self.assertEqual(fb_argv[:2], ["/bin/sh", "-c"])
            self.assertEqual(fb_kwargs["env"]["ANNEAL_LEAN_RUN_SLOTS"], "1")
            self.assertEqual(
                fb_kwargs["env"]["ANNEAL_LEAN_RUN_MEM_MB"], str(scope_limits["memory_max_mb"])
            )

    def test_cli_subprocess_exports_budget_env_vars_end_to_end(self) -> None:
        """End-to-end subprocess checks across synthetic direct execution,
        re-entrancy pass-through vs `--nested-ok`, and live `systemd-run` scope.
        """
        inspect_cmd = [
            sys.executable,
            "-c",
            "import json, os; print(json.dumps({"
            "k: os.environ.get(k) for k in ("
            "'ANNEAL_LEAN_RUN_SLOTS', 'ANNEAL_LEAN_RUN_MEM_MB'"
            ")}))",
        ]
        with tempfile.TemporaryDirectory(prefix="anneal-budget-env-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            probe = self._probe_json(
                self._synthetic_cli(
                    root,
                    "cg_uncapped",
                    "--mode",
                    "file",
                    "--concurrency",
                    "2",
                    "--memory-max-mb",
                    "2048",
                    "--probe",
                    "--json",
                )
            )
            self.assertEqual(probe["build_slots"], 2)
            self.assertEqual(probe["memory_max_mb"], 2048)

            # Unslotted `--no-slot-lock` overwrites stale parent values to 0.
            res_direct = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_SLOTS": "88",
                    "ANNEAL_LEAN_RUN_MEM_MB": "888888",
                },
            )
            self.assertEqual(res_direct.returncode, 0, res_direct.stderr)
            self.assertEqual(
                json.loads(res_direct.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "0", "ANNEAL_LEAN_RUN_MEM_MB": "2048"},
            )

            # Pass-through inside an outer scope preserves the outer budget.
            res_passthrough = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_SLOTS": "5",
                    "ANNEAL_LEAN_RUN_MEM_MB": "12345",
                },
            )
            self.assertEqual(res_passthrough.returncode, 0, res_passthrough.stderr)
            self.assertEqual(
                json.loads(res_passthrough.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "5", "ANNEAL_LEAN_RUN_MEM_MB": "12345"},
            )

            # `--nested-ok` bypasses pass-through and overwrites stale values.
            res_nested = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--nested-ok",
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_SLOTS": "5",
                    "ANNEAL_LEAN_RUN_MEM_MB": "12345",
                },
            )
            self.assertEqual(res_nested.returncode, 0, res_nested.stderr)
            self.assertEqual(
                json.loads(res_nested.stdout),
                {"ANNEAL_LEAN_RUN_SLOTS": "0", "ANNEAL_LEAN_RUN_MEM_MB": "2048"},
            )

        if _can_launch_live_systemd_scope():
            live_probe = self._probe_json(
                self._cli(
                    "--mode",
                    "file",
                    "--concurrency",
                    "2",
                    "--memory-max-mb",
                    "2048",
                    "--probe",
                    "--json",
                )
            )
            live_res = self._cli(
                "--mode",
                "file",
                "--concurrency",
                "2",
                "--memory-max-mb",
                "2048",
                "--no-slot-lock",
                "--",
                *inspect_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_SLOTS": "77",
                    "ANNEAL_LEAN_RUN_MEM_MB": "777777",
                },
            )
            self.assertEqual(live_res.returncode, 0, live_res.stderr)
            self.assertEqual(
                json.loads(live_res.stdout),
                {
                    "ANNEAL_LEAN_RUN_SLOTS": "0",
                    "ANNEAL_LEAN_RUN_MEM_MB": str(live_probe["memory_max_mb"]),
                },
            )


class TestWorkloadMemoryEnvelope(unittest.TestCase):
    """Tests `anneal-workloads.slice`, `--exclusive`, and re-entrancy
    pass-through.
    """

    def test_ensure_slice_gate_and_content_diff(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slice-") as td:
            unit_p = Path(td) / "anneal-workloads.slice"
            bad_env = {
                "user_systemd_active": False,
                "t_cg_is_user_service": False,
                "w_slice_high_mb": 7768,
                "w_slice_max_mb": 8264,
            }
            ok, ch, _ = alr.ensure_workloads_slice(bad_env, unit_path=unit_p, reload_systemd=False)
            self.assertFalse(ok)
            self.assertFalse(ch)
            self.assertFalse(unit_p.exists())

            good_env = {
                "user_systemd_active": True,
                "t_cg_is_user_service": True,
                "w_slice_high_mb": 7768,
                "w_slice_max_mb": 8264,
                "runtime_base": td,
            }
            with mock.patch.object(alr.subprocess, "run") as mock_run:
                mock_run.return_value = subprocess.CompletedProcess([], 0, "", "")
                ok1, ch1, _ = alr.ensure_workloads_slice(good_env, unit_path=unit_p, reload_systemd=True)
                self.assertTrue(ok1)
                self.assertTrue(ch1)
                self.assertEqual(mock_run.call_count, 1)
                txt = unit_p.read_text(encoding="utf-8")
                self.assertIn("MemoryHigh=7768M", txt)
                self.assertIn("MemoryMax=8264M", txt)
                self.assertIn("MemorySwapMax=0", txt)
                self.assertIn("ManagedOOMMemoryPressure=kill", txt)
                self.assertIn("ManagedOOMMemoryPressureLimit=40%", txt)

                ok2, ch2, _ = alr.ensure_workloads_slice(good_env, unit_path=unit_p, reload_systemd=True)
                self.assertTrue(ok2)
                self.assertFalse(ch2)
                self.assertEqual(mock_run.call_count, 1)

    def test_exclusive_multi_lock_and_in_scope_passthrough(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-excl-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700, parents=True)
            fd2 = os.open(str(slot_dir / "slot-2.lock"), os.O_CREAT | os.O_RDWR, 0o600)
            fcntl.flock(fd2, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                wait_err = io.StringIO()
                with mock.patch("sys.stderr", wait_err):
                    with self.assertRaises(TimeoutError):
                        with alr.acquire_build_slot(
                            3, 0.12, enabled=True, exclusive=True, runtime_base=rt, poll_interval=0.03
                        ):
                            self.fail("Expected timeout while slot-2 locked")
                self.assertIn("Waiting for exclusive access", wait_err.getvalue())
                fd1 = os.open(str(slot_dir / "slot-1.lock"), os.O_CREAT | os.O_RDWR, 0o600)
                try:
                    fcntl.flock(fd1, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    fcntl.flock(fd1, fcntl.LOCK_UN)
                finally:
                    os.close(fd1)
            finally:
                fcntl.flock(fd2, fcntl.LOCK_UN)
                os.close(fd2)

            with alr.acquire_build_slot(3, 1.0, enabled=True, exclusive=True, runtime_base=rt) as slots:
                self.assertEqual(slots, [1, 2, 3])
                self.assertEqual(alr.count_active_build_slots(rt), 3)

            with tempfile.TemporaryDirectory(prefix="anneal-excl-xdg-") as xdg_dir:
                env_in = _isolated_cli_env(
                    Path(xdg_dir),
                    {
                        "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                        "XDG_RUNTIME_DIR": str(rt),
                    },
                )
                res = subprocess.run(
                    [sys.executable, str(SCRIPT_PATH), "--mode", "build", "--", sys.executable, "-c", "print('ok')"],
                    env=env_in,
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10.0,
                )
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertEqual(res.stdout.strip(), "ok")

    def test_concurrency_isolation_uncapped_and_capped(self) -> None:
        """Hermetically verifies `XDG_CONFIG_HOME` / `HOME` isolation and
        `ANNEAL_WORKTREE_CONCURRENCY` behavior under both uncapped and
        cgroup-capped regimes (even when tests run on a 1-slot cgroup-capped
        host).
        """
        with tempfile.TemporaryDirectory(prefix="anneal-conc-iso-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            meminfo = root / "meminfo"
            proc_cg = root / "proc_cgroup"
            uncapped_cg, capped_1slot_cg, capped_2slot_cg = (
                _write_synthetic_cgroup_root(root, name, ceiling_mib)
                for name, ceiling_mib, _capped, _s_heavy_safe in SYNTHETIC_HOSTS
            )

            fake_home = root / "home"
            _write_cgroup_file(fake_home / ".config" / "anneal" / "concurrency", "5\n")
            empty_xdg = root / "xdg_empty"
            empty_xdg.mkdir()
            populated_xdg = root / "xdg_three"
            _write_cgroup_file(populated_xdg / "anneal" / "concurrency", "3\n")

            # Empty XDG_CONFIG_HOME masks $HOME/.config/anneal/concurrency;
            # unset XDG falls back to HOME.
            with mock.patch.dict(
                os.environ,
                {"HOME": str(fake_home), "XDG_CONFIG_HOME": str(empty_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                self.assertIsNone(alr.read_concurrency_config_file())
                env_default = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(env_default["is_cg_capped"])
                self.assertEqual(env_default["concurrency"], 1)
                self.assertEqual(env_default["build_slots"], 1)

            with mock.patch.dict(
                os.environ,
                {"HOME": str(fake_home), "XDG_CONFIG_HOME": ""},
                clear=False,
            ):
                self.assertEqual(alr.read_concurrency_config_file(), 5)

            # Uncapped regime: ANNEAL_WORKTREE_CONCURRENCY=2 -> 2; XDG file "3"
            # -> 3.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                uncapped_env = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(uncapped_env["is_cg_capped"])
                self.assertEqual(uncapped_env["concurrency"], 2)
                self.assertEqual(uncapped_env["build_slots"], 2)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                uncapped_cfg = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=uncapped_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertFalse(uncapped_cfg["is_cg_capped"])
                self.assertEqual(uncapped_cfg["concurrency"], 3)
                self.assertEqual(uncapped_cfg["build_slots"], 3)

            # Capped 1-slot regime: env=2 and xdg=3 both clamp to s_heavy_safe
            # == 1, and unsafe_ignore_cgroup lifts only override_mem_mb above
            # w_slice_max_mb.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                cap1 = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap1["is_cg_capped"])
                self.assertEqual(cap1["s_heavy_safe"], 1)
                self.assertEqual(cap1["concurrency"], 1)
                self.assertEqual(cap1["build_slots"], 1)
                over_mb = cap1["w_slice_max_mb"] + 1024
                cap1_mem_clamped = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                    override_mem_mb=over_mb,
                    unsafe_ignore_cgroup=False,
                )
                self.assertEqual(cap1_mem_clamped["memory_max_mb"], cap1["w_slice_max_mb"])
                cap1_mem_unsafe = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                    override_mem_mb=over_mb,
                    unsafe_ignore_cgroup=True,
                )
                self.assertEqual(cap1_mem_unsafe["memory_max_mb"], over_mb)
                self.assertEqual(cap1_mem_unsafe["concurrency"], 1)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                cap1_xdg = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_1slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap1_xdg["is_cg_capped"])
                self.assertEqual(cap1_xdg["s_heavy_safe"], 1)
                self.assertEqual(cap1_xdg["concurrency"], 1)
                self.assertEqual(cap1_xdg["build_slots"], 1)

            # Capped 2-slot regime: s_heavy_safe == 2 keeps env=2 and clamps
            # xdg=3 to 2.
            with mock.patch.dict(
                os.environ,
                {
                    "XDG_CONFIG_HOME": str(empty_xdg),
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                },
                clear=False,
            ):
                cap2_env = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_2slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap2_env["is_cg_capped"])
                self.assertEqual(cap2_env["s_heavy_safe"], 2)
                self.assertEqual(cap2_env["concurrency"], 2)
                self.assertEqual(cap2_env["build_slots"], 2)

            with mock.patch.dict(
                os.environ,
                {"XDG_CONFIG_HOME": str(populated_xdg)},
                clear=False,
            ):
                os.environ.pop("ANNEAL_WORKTREE_CONCURRENCY", None)
                cap2 = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=capped_2slot_cg,
                    proc_cgroup_path=proc_cg,
                    cpu_cores=SYNTHETIC_HOST_CORES,
                    user_systemd_active=False,
                    runtime_base=root,
                    is_probe=True,
                )
                self.assertTrue(cap2["is_cg_capped"])
                self.assertEqual(cap2["s_heavy_safe"], 2)
                self.assertEqual(cap2["concurrency"], 2)
                self.assertEqual(cap2["build_slots"], 2)

    def test_exclusive_probe_matches_execution_w_eff_with_cli_concurrency(self) -> None:
        """`--exclusive` forces `w_eff = 1` in `--probe` just as in execution,
        even when `--concurrency` (`cli_concurrency`) is also supplied, while
        preserving `build_slots`.
        """
        for is_cg_capped, s_heavy_safe, w_file, cli_c, want_slots in (
            (False, 4, None, 4, 4),
            (False, 4, 3, 2, 3),
            (True, 2, None, 4, 2),
            (True, 2, 4, 3, 2),
        ):
            probe_res = alr.resolve_effective_concurrency(
                is_cg_capped=is_cg_capped,
                s_heavy_safe=s_heavy_safe,
                w_file=w_file,
                cli_concurrency=cli_c,
                env_concurrency=None,
                exclusive=True,
                is_probe=True,
            )
            exec_res = alr.resolve_effective_concurrency(
                is_cg_capped=is_cg_capped,
                s_heavy_safe=s_heavy_safe,
                w_file=w_file,
                cli_concurrency=cli_c,
                env_concurrency=None,
                exclusive=True,
                is_probe=False,
            )
            self.assertEqual(probe_res, (1, want_slots))
            self.assertEqual(probe_res, exec_res)

        probe_env = alr.compute_workload_memory_envelope(
            cpu_cores=16,
            mem_total_mb=32768,
            mem_avail_mb=28672,
            w_file=4,
            cli_concurrency=4,
            exclusive=True,
            is_probe=True,
            mode="build",
        )
        exec_env = alr.compute_workload_memory_envelope(
            cpu_cores=16,
            mem_total_mb=32768,
            mem_avail_mb=28672,
            w_file=4,
            cli_concurrency=4,
            exclusive=True,
            is_probe=False,
            mode="build",
        )
        self.assertEqual(probe_env["w_eff"], 1)
        self.assertEqual(probe_env["build_slots"], 4)
        self.assertEqual(probe_env["memory_max_mb"], exec_env["memory_max_mb"])

    def test_probe_cap_brackets_execution_cap_on_multi_slot_hosts(self) -> None:
        """Contract multi-slot callers rely on when reconciling probe vs
        execution caps.

        A non-exclusive `--probe --concurrency w` plans for `w` slots, while
        execution runs at `build_slots` when the host's concurrency file asks
        for more. Then `--probe --concurrency <build_slots>` reproduces the
        execution plan, and the execution `memory_max_mb` lies in `[probe * w //
        build_slots, probe]`.
        """
        reprobed = 0
        for mem_total, mem_avail, cores in (
            (16384, 14000, 8),
            (32768, 28672, 16),
            (65536, 60000, 32),
            (262144, 200000, 96),
        ):
            for c_high in (None, mem_total // 2, (3 * mem_total) // 4):
                ancestors = (
                    []
                    if c_high is None
                    else [
                        {
                            "path": "/sys/fs/cgroup/user.slice",
                            "name": "user.slice",
                            "c_high_mb": c_high,
                            "w_mb": 512,
                            "is_shared_user_slice": False,
                        }
                    ]
                )
                for w_file in (2, 3, 4):
                    for cli_c in (1, 2, 3):
                        for mode in ("build", "file"):
                            for w_cg in (0, 2500):

                                def plan(concurrency: int, is_probe: bool) -> dict:
                                    return alr.compute_workload_memory_envelope(
                                        cpu_cores=cores,
                                        mem_total_mb=mem_total,
                                        mem_avail_mb=mem_avail,
                                        ancestors=ancestors,
                                        w_cg_mb=w_cg,
                                        w_cg_nonrecl_mb=w_cg,
                                        w_file=w_file,
                                        cli_concurrency=concurrency,
                                        is_probe=is_probe,
                                        mode=mode,
                                    )

                                case = (mem_total, c_high, w_file, cli_c, mode, w_cg)
                                probe, execd = plan(cli_c, True), plan(cli_c, False)
                                slots = probe["build_slots"]
                                self.assertEqual(slots, execd["build_slots"], case)
                                if probe["w_eff"] >= slots:
                                    # Nothing to reconcile: the probe already is
                                    # the plan.
                                    self.assertEqual(probe["w_eff"], execd["w_eff"], case)
                                    self.assertEqual(
                                        probe["memory_max_mb"], execd["memory_max_mb"], case
                                    )
                                    continue
                                reprobed += 1
                                self.assertEqual(execd["w_eff"], slots, case)
                                again = plan(slots, True)
                                self.assertEqual(again["w_eff"], slots, case)
                                self.assertEqual(
                                    again["memory_max_mb"], execd["memory_max_mb"], case
                                )
                                self.assertLessEqual(
                                    execd["memory_max_mb"], probe["memory_max_mb"], case
                                )
                                self.assertGreaterEqual(
                                    execd["memory_max_mb"],
                                    probe["memory_max_mb"] * probe["w_eff"] // slots,
                                    case,
                                )
        self.assertGreater(reprobed, 0)


class TestCrossPlatformAndNonSystemdFallback(unittest.TestCase):
    """Tests macOS (`darwin`) and non-systemd Linux graceful fallback paths."""

    def test_darwin_sysctl_memsize_fallback_and_probe(self) -> None:
        missing_root = Path("/nonexistent-anneal-test-root")
        meminfo_p = Path("/proc/meminfo")

        def fake_sysctl(cmd: list[str], **_kwargs: Any) -> subprocess.CompletedProcess[str]:
            self.assertEqual(cmd, ["sysctl", "-n", "hw.memsize"])
            return subprocess.CompletedProcess(cmd, 0, f"{32768 * MIB}\n", "")

        with mock.patch.object(alr.sys, "platform", "darwin"), \
             mock.patch.object(alr.os, "cpu_count", return_value=12), \
             mock.patch.object(alr.os, "sched_getaffinity", return_value=set(range(12)), create=True), \
             mock.patch.object(Path, "is_file", return_value=False), \
             mock.patch.object(alr.subprocess, "run", side_effect=fake_sysctl):
            cores, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(meminfo_p)

        self.assertEqual((cores, total_mb, avail_mb), (12, 32768, 24576))
        with mock.patch.object(alr, "_read_raw_meminfo_and_cpus", return_value=(12, 32768, 24576)), \
             mock.patch.object(alr, "resolve_runtime_base", return_value=(Path("/tmp"), False)), \
             mock.patch.object(alr, "check_user_systemd_active", return_value=False):
            env_info = alr.probe_host_envelope(
                cgroup_root=missing_root / "cgroup",
                proc_cgroup_path=missing_root / "proc_cgroup",
                cli_concurrency=1,
                is_probe=True,
                mode="build",
            )
        self.assertFalse(env_info["is_cg_capped"])
        self.assertFalse(env_info["user_systemd_active"])
        self.assertFalse(env_info["cgroup_v2"])
        self.assertEqual(env_info["threads"], 12)
        self.assertEqual(env_info["w_slice_max_mb"], 24576)
        self.assertIn("unavailable", alr.format_cgroup_probe_line(env_info))

    def test_non_systemd_execution_runs_in_process_group_with_lean_m_and_threads(self) -> None:
        _FakePopen.calls = []
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=8,
            mem_total_mb=32768,
            mem_avail_mb=24576,
            user_systemd_active=False,
            t_cg_is_user_service=False,
            cli_concurrency=2,
            mode="file",
        )
        with mock.patch.dict(os.environ, {}, clear=False) as patched_env, \
             mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr, "resolve_runtime_base", return_value=(Path("/tmp"), False)), \
             mock.patch.object(alr.subprocess, "Popen", _FakePopen):
            for var in ("LEAN_NUM_THREADS", "CARGO_BUILD_JOBS", "RAYON_NUM_THREADS"):
                patched_env.pop(var, None)
            rc = alr.main(
                ["--mode", "file", "--concurrency", "2", "--no-slot-lock", "--", "lean", "Foo.lean"]
            )
        self.assertEqual(rc, 0)
        self.assertEqual(len(_FakePopen.calls), 1)
        argv, kwargs = _FakePopen.calls[0]
        self.assertEqual(argv[:2], ["/bin/sh", "-c"])
        self.assertEqual(argv[4:], ["lean", "-M", str(limits["lean_m_mb"]), "Foo.lean"])
        self.assertTrue(kwargs.get("start_new_session"))
        self.assertEqual(kwargs["env"]["ANNEAL_LEAN_RUN_IN_SCOPE"], "1")
        self.assertEqual(kwargs["env"]["LEAN_NUM_THREADS"], str(limits["threads"]))
        self.assertEqual(kwargs["env"]["CARGO_BUILD_JOBS"], str(limits["threads"]))
        self.assertEqual(kwargs["env"]["RAYON_NUM_THREADS"], str(limits["threads"]))

    def test_remediation_messages_reference_public_proof_scaling_skill(self) -> None:
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=8,
            mem_total_mb=32768,
            mem_avail_mb=24576,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="file",
        )
        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), \
             mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr, "probe_cgroup_v2_memory", return_value=alr._empty_cgroup_info()):
            rc_oom = alr.main(["--mode", "file", "--no-slot-lock", "--", "sh", "-c", "exit 137"])
        self.assertEqual(rc_oom, 137)
        oom_err = err_buf.getvalue()
        self.assertIn("anneal/skills/proof-scaling/SKILL.md", oom_err)
        self.assertIn("no cgroup MemoryMax was active", oom_err)

    def test_non_systemd_probe_omits_hard_ram_cap_and_warns_on_memory_max(self) -> None:
        """Non-systemd `--probe` must not print `Hard RAM Cap` and execution
        warns.
        """
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=8,
            mem_total_mb=32768,
            mem_avail_mb=24576,
            user_systemd_active=False,
            t_cg_is_user_service=False,
            cli_concurrency=1,
            mode="build",
            override_mem_mb=64,
        )
        out_buf = io.StringIO()
        with mock.patch("sys.stdout", out_buf), \
             mock.patch.object(alr, "probe_host_envelope", return_value=limits):
            rc_probe = alr.main(["--probe", "--memory-max-mb", "64"])
        self.assertEqual(rc_probe, 0)
        probe_out = out_buf.getvalue()
        self.assertNotIn("Hard RAM Cap", probe_out)
        self.assertIn("none (no systemd scope", probe_out)
        self.assertIn("lean -M 48 only", probe_out)

        err_buf = io.StringIO()
        with mock.patch("sys.stderr", err_buf), \
             mock.patch.object(alr, "probe_host_envelope", return_value=limits):
            rc_run = alr.main(
                ["--mode", "build", "--no-slot-lock", "--memory-max-mb", "64", "--", "true"]
            )
        self.assertEqual(rc_run, 0)
        self.assertIn("no hard OS memory cap is enforced", err_buf.getvalue())

    def test_low_mem_available_with_memory_max_override_avoids_spurious_137(self) -> None:
        """Low `MemAvailable` triggers 137 without override, passes with
        override.
        """
        _FakePopen.calls = []
        with tempfile.TemporaryDirectory(prefix="anneal-lowmem-") as td:
            cg = Path(td) / "cg"
            uid = os.getuid()
            user_cg = cg / "user.slice" / f"user-{uid}.slice" / f"user@{uid}.service"
            _write_cgroup_file(user_cg / "memory.max", "max\n")
            _write_cgroup_file(user_cg / "memory.stat", "anon 0\nshmem 0\nfile 0\n")
            low_limits_no_override = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=256,
                user_systemd_active=True,
                systemd_version=260,
                systemd_run_version=260,
                t_cg_is_user_service=True,
                cli_concurrency=1,
                mode="file",
            )
            low_limits_override = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=256,
                user_systemd_active=True,
                systemd_version=260,
                systemd_run_version=260,
                t_cg_is_user_service=True,
                cli_concurrency=1,
                mode="file",
                override_mem_mb=512,
            )
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=low_limits_no_override), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc_fail = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
            self.assertEqual(rc_fail, 137)

            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=low_limits_override), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc_ok = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--memory-max-mb", "512", "--", "true"]
                )
            self.assertEqual(rc_ok, 0)


class TestSecurityHardeningAndSystemdVersions(unittest.TestCase):
    """Tests slot-lock symlink/permission hardening, systemd version gating, and
    fallbacks.
    """

    def test_slot_lock_rejects_symlinks_without_truncating_target(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-sym-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            victim = rt / "victim.txt"
            victim.write_text("DO NOT TRUNCATE OR OVERWRITE THIS FILE\n", encoding="utf-8")
            os.symlink(victim, slot_dir / "slot-1.lock")

            for excl in (False, True):
                with self.assertRaises(PermissionError):
                    with alr.acquire_build_slot(
                        2, 1.0, enabled=True, exclusive=excl, runtime_base=rt
                    ):
                        pass
            self.assertEqual(
                victim.read_text(encoding="utf-8"),
                "DO NOT TRUNCATE OR OVERWRITE THIS FILE\n",
            )

            # Symlinked slot directory itself must be rejected too.
            rt2 = Path(td) / "rt2"
            rt2.mkdir()
            target_dir = rt / "real_slots"
            target_dir.mkdir()
            os.symlink(target_dir, rt2 / f"anneal-build-slots-{os.getuid()}")
            with self.assertRaises(PermissionError):
                with alr.acquire_build_slot(1, 1.0, enabled=True, runtime_base=rt2):
                    pass

    def test_slot_lock_fails_immediately_on_permission_or_wrong_owner_and_exits_126(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-perm-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            # Wrong-owner directory must fail immediately without waiting for
            # slot timeout.
            wrong_uid = os.getuid() + 1000
            fake_stat = os.stat_result((0o40700, 1, 1, 2, wrong_uid, 0, 0, 0, 0, 0))
            with mock.patch.object(alr.os, "lstat", return_value=fake_stat):
                with self.assertRaises(PermissionError):
                    with alr.acquire_build_slot(
                        2, 1200.0, enabled=True, exclusive=False, runtime_base=rt
                    ):
                        pass

            # Unwritable/inaccessible directory fails fast with PermissionError
            # -> exit 126.
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=16384,
                mem_avail_mb=12288,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=str(rt),
            )
            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr.os, "access", return_value=False):
                rc = alr.main(["--mode", "build", "--", "true"])
            self.assertEqual(rc, 126)
            self.assertNotIn("BUILD_SLOT_TIMEOUT", err_buf.getvalue())

            # FIFO and symlinks inside slot_dir never block
            # count_active_build_slots.
            os.mkfifo(slot_dir / "slot-1.lock")
            os.symlink(rt / "nonexistent", slot_dir / "slot-2.lock")
            self.assertEqual(alr.count_active_build_slots(rt), 0)

    def test_slot_lock_rejects_hardlinks_loose_modes_bad_types_and_missing_home(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-hard-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)

            # 1. Hardlinked lock file (`st_nlink > 1`) is rejected without
            # truncating victim.
            victim = rt / "hard_victim.txt"
            victim.write_text("KEEP HARDLINK VICTIM INTACT\n", encoding="utf-8")
            os.link(victim, slot_dir / "slot-1.lock")
            with self.assertRaisesRegex(PermissionError, "hardlinked"):
                with alr.acquire_build_slot(1, 0.2, enabled=True, runtime_base=rt):
                    pass
            self.assertEqual(victim.read_text(encoding="utf-8"), "KEEP HARDLINK VICTIM INTACT\n")
            (slot_dir / "slot-1.lock").unlink()

            # 2. Pre-existing loose-mode lock file (`0644`) is rejected, never
            # fchmod-repaired.
            loose_lock = slot_dir / "slot-1.lock"
            loose_lock.write_text("PRESERVE", encoding="utf-8")
            loose_lock.chmod(0o644)
            with self.assertRaisesRegex(PermissionError, "Unsafe permissions"):
                with alr.acquire_build_slot(1, 0.2, enabled=True, runtime_base=rt):
                    pass
            self.assertEqual(loose_lock.stat().st_mode & 0o777, 0o644)
            self.assertEqual(loose_lock.read_text(encoding="utf-8"), "PRESERVE")
            loose_lock.unlink()

            # 3. Directory at lock path exits 126 cleanly (never exit 1).
            (slot_dir / "slot-1.lock").mkdir(mode=0o700)
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=16384,
                mem_avail_mb=12288,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=str(rt),
            )
            err_dir = io.StringIO()
            with mock.patch("sys.stderr", err_dir), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)
            (slot_dir / "slot-1.lock").rmdir()

            # 4. Loose-mode pre-existing slot_dir (`0770`) is rejected
            # fail-closed (not repaired).
            rt_loose = Path(td) / "rt_loose"
            rt_loose.mkdir()
            bad_slot_dir = rt_loose / f"anneal-build-slots-{os.getuid()}"
            bad_slot_dir.mkdir(mode=0o770)
            bad_slot_dir.chmod(0o770)
            loose_limits = dict(limits, runtime_base=str(rt_loose))
            err_loose = io.StringIO()
            with mock.patch("sys.stderr", err_loose), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=loose_limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)
            self.assertEqual(bad_slot_dir.stat().st_mode & 0o777, 0o770)

            # 5. Missing base dir exits 126 consistently (never 127
            # command-not-found).
            missing_limits = dict(limits, runtime_base=str(Path(td) / "no_such_base"))
            err_miss = io.StringIO()
            with mock.patch("sys.stderr", err_miss), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=missing_limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)

        # 6. `Path.home()` raising RuntimeError never produces an uncaught
        # traceback.
        with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": ""}, clear=False), \
             mock.patch.object(alr.Path, "home", side_effect=RuntimeError("no passwd")):
            self.assertIsNone(alr.read_concurrency_config_file())
            ok, changed, msg = alr.ensure_workloads_slice(
                {"user_systemd_active": True, "t_cg_is_user_service": True, "w_slice_high_mb": 1024, "w_slice_max_mb": 2048}
            )
            self.assertFalse(ok)
            self.assertFalse(changed)
            self.assertIn("cannot resolve", msg)

    def test_non_exclusive_slot_contention_and_timeout(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-cont-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            fd1 = alr._open_private_lock_file(slot_dir / "slot-1.lock", os.getuid())
            fcntl.flock(fd1, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                with alr.acquire_build_slot(
                    2, 0.2, enabled=True, exclusive=False, runtime_base=rt
                ) as slot_idx:
                    self.assertEqual(slot_idx, 2)
                fd2 = alr._open_private_lock_file(slot_dir / "slot-2.lock", os.getuid())
                fcntl.flock(fd2, fcntl.LOCK_EX | fcntl.LOCK_NB)
                try:
                    cont_err = io.StringIO()
                    with mock.patch("sys.stderr", cont_err):
                        with self.assertRaisesRegex(TimeoutError, "BUILD_SLOT_TIMEOUT"):
                            with alr.acquire_build_slot(
                                2, 0.08, enabled=True, exclusive=False, runtime_base=rt, poll_interval=0.02
                            ):
                                pass
                    self.assertIn("All 2 host build slot(s) busy", cont_err.getvalue())
                finally:
                    fcntl.flock(fd2, fcntl.LOCK_UN)
                    os.close(fd2)
            finally:
                fcntl.flock(fd1, fcntl.LOCK_UN)
                os.close(fd1)

    def test_systemd_version_parsing_oom_policy_and_expand_environment(self) -> None:
        cases = (
            ("249.11-0ubuntu3.12", 249, 249, False, False),
            ("252.26-1~deb12u2", 252, 252, False, False),
            ("253", 253, 253, True, False),
            ("v254.0", 254, 254, True, True),
            # Skew: manager 257 with client 260 passes --expand-environment=no.
            ("257.9", 257, 260, True, True),
            # Reverse skew: client 252 omits both OOMPolicy=kill and no-expand.
            ("260.1\n", 260, 252, False, False),
            # Old manager 252 with client 260 omits OOMPolicy=kill, keeps
            # no-expand.
            ("252.9", 252, 260, False, True),
            ("systemd 260 (260.1-1)\n+PAM", 260, 260, True, True),
        )
        with mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"):
            for raw, mgr_ver, client_ver, want_oom_pol, want_no_expand in cases:
                self.assertEqual(alr._parse_systemd_major_version(raw), mgr_ver, raw)
                argv, in_scope = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-ver.scope",
                    systemd_version=mgr_ver,
                    systemd_run_version=client_ver,
                )
                self.assertTrue(in_scope)
                self.assertEqual("OOMPolicy=kill" in argv, want_oom_pol, raw)
                self.assertEqual("--expand-environment=no" in argv, want_no_expand, raw)

        # Unknown client version inspects `systemd-run --help` for
        # `--expand-environment` instead of silently dropping it.
        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=True
        ), mock.patch("sys.stderr", io.StringIO()) as unk_err:
            argv_unk_help, _ = alr._build_scope_launch_cmd(
                ["echo", "$HOME"],
                b_max_mb=4096,
                threads=2,
                timeout_sec=30,
                user_systemd_active=True,
                unit_name="anneal-unk.scope",
                systemd_version=260,
                systemd_run_version=None,
            )
            self.assertIn("--expand-environment=no", argv_unk_help)
            self.assertNotIn("OOMPolicy=kill", argv_unk_help)
            self.assertIn("WARNING:", unk_err.getvalue())

        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=False
        ), mock.patch("sys.stderr", io.StringIO()) as no_help_err:
            argv_no_help, _ = alr._build_scope_launch_cmd(
                ["echo", "$HOME"],
                b_max_mb=4096,
                threads=2,
                timeout_sec=30,
                user_systemd_active=True,
                unit_name="anneal-nohelp.scope",
                systemd_version=260,
                systemd_run_version=None,
            )
            self.assertNotIn("--expand-environment=no", argv_no_help)
            self.assertIn("WARNING:", no_help_err.getvalue())

        # Both --version and --help failing passes --expand-environment=no when
        # user manager >= 254 and omits it when < 254, always warning clearly.
        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=None
        ):
            with mock.patch("sys.stderr", io.StringIO()) as err_260:
                argv_both_260, _ = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-both260.scope",
                    systemd_version=260,
                    systemd_run_version=None,
                )
            self.assertIn("--expand-environment=no", argv_both_260)
            self.assertIn("WARNING:", err_260.getvalue())

            with mock.patch("sys.stderr", io.StringIO()) as err_252:
                argv_both_252, _ = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-both252.scope",
                    systemd_version=252,
                    systemd_run_version=None,
                )
            self.assertNotIn("--expand-environment=no", argv_both_252)
            self.assertIn("WARNING:", err_252.getvalue())

        # Within a single invocation, `systemd-run --version` and `--help` are
        # each probed at most once across probe, reprobe, and launch.
        with tempfile.TemporaryDirectory(prefix="anneal-cache-srun-") as td:
            cg = Path(td) / "cg"
            uid = os.getuid()
            user_cg = cg / "user.slice" / f"user-{uid}.slice" / f"user@{uid}.service"
            _write_cgroup_file(user_cg / "cgroup.controllers", "memory cpu\n")
            _write_cgroup_file(user_cg / "cgroup.subtree_control", "memory cpu\n")
            _write_cgroup_file(user_cg / "memory.max", "max\n")
            _write_cgroup_file(user_cg / "memory.stat", "anon 0\nshmem 0\nfile 0\n")
            seen_srun: list[list[str]] = []

            def fake_subproc_run(argv: list[str], **_kw: Any) -> subprocess.CompletedProcess[str]:
                seen_srun.append(list(argv))
                if "show" in argv:
                    return subprocess.CompletedProcess(argv, 0, "260\n", "")
                if "--version" in argv or "--help" in argv:
                    return subprocess.CompletedProcess(argv, 1, "", "probe failed")
                return subprocess.CompletedProcess(argv, 0, "", "")

            _FakePopen.calls = []
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "_find_systemctl", return_value="/usr/bin/systemctl"), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(Path(td), True)), \
                 mock.patch.object(
                     alr,
                     "probe_host_envelope",
                     wraps=lambda **kw: alr.compute_workload_memory_envelope(
                         cpu_cores=8,
                         mem_total_mb=32768,
                         mem_avail_mb=24576,
                         user_systemd_active=True,
                         systemd_version=alr.detect_user_systemd_version(Path(td)),
                         systemd_run_version=alr.detect_systemd_run_client_version("/usr/bin/systemd-run"),
                         t_cg_is_user_service=True,
                         cli_concurrency=1,
                         mode=kw.get("mode", "file"),
                         override_mem_mb=kw.get("override_mem_mb"),
                     ),
                 ), \
                 mock.patch.object(alr.subprocess, "run", side_effect=fake_subproc_run), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc_cache = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
            self.assertEqual(rc_cache, 0)
            ver_calls = [a for a in seen_srun if "--version" in a]
            help_calls = [a for a in seen_srun if "--help" in a]
            show_calls = [a for a in seen_srun if "show" in a]
            self.assertEqual(len(ver_calls), 1, ver_calls)
            self.assertEqual(len(help_calls), 1, help_calls)
            self.assertEqual(len(show_calls), 1, show_calls)

        # Client detection helper queries `systemd-run --version` directly.
        with mock.patch.object(
            alr.subprocess,
            "run",
            return_value=subprocess.CompletedProcess(
                ["systemd-run", "--version"], 0, "systemd 260 (260.1-1)\n+PAM\n", ""
            ),
        ):
            self.assertEqual(alr.detect_systemd_run_client_version("/usr/bin/systemd-run"), 260)

        for bad in ("", "   ", "custom-version"):
            self.assertIsNone(alr._parse_systemd_major_version(bad), bad)

        # If systemd-run client >= 254 is active live, verify special $-args
        # arrive verbatim.
        if (
            _can_launch_live_systemd_scope()
            and (alr.detect_systemd_run_client_version() or 0) >= 254
        ):
            with tempfile.TemporaryDirectory(prefix="anneal-argv-lit-") as td:
                out_f = Path(td) / "argv.json"
                probe_args = [
                    "lit$$pid",
                    "${HOME}",
                    "$HOME",
                    "x=${ANNEAL_TEST_UNSET_VAR}y",
                    "$f.lean",
                ]
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--memory-max-mb",
                        "512",
                        "--",
                        sys.executable,
                        "-c",
                        "import json, pathlib, sys; "
                        "pathlib.Path(sys.argv[1]).write_text(json.dumps(sys.argv[2:]))",
                        str(out_f),
                        *probe_args,
                    ]
                )
                self.assertEqual(rc, 0)
                self.assertEqual(json.loads(out_f.read_text(encoding="utf-8")), probe_args)

    def test_probe_user_systemd_retries_and_warns_on_show_timeout_or_failure(
        self,
    ) -> None:
        """Timeout or nonzero `systemctl --user show` warns instead of silent
        fail-open.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-sd-probe-") as td:
            cg = Path(td) / "cg"
            uid = os.getuid()
            user_cg = cg / "user.slice" / f"user-{uid}.slice" / f"user@{uid}.service"
            _write_cgroup_file(user_cg / "cgroup.controllers", "memory cpu\n")
            _write_cgroup_file(user_cg / "cgroup.subtree_control", "memory cpu\n")
            calls = 0

            def timeout_run(*_a: Any, **_kw: Any) -> Any:
                nonlocal calls
                calls += 1
                raise subprocess.TimeoutExpired(cmd=["systemctl"], timeout=2.0)

            err_to = io.StringIO()
            with mock.patch("sys.stderr", err_to), mock.patch.object(
                alr, "_find_systemctl", return_value="/usr/bin/systemctl"
            ), mock.patch.object(alr.subprocess, "run", side_effect=timeout_run):
                active, ver = alr._probe_user_systemd(
                    runtime_base=Path(td),
                    user_systemd_sock_alive=True,
                    cgroup_root=cg,
                    uid=uid,
                )
            self.assertFalse(active)
            self.assertIsNone(ver)
            self.assertEqual(calls, 2)
            self.assertIn("WARNING:", err_to.getvalue())

            # Non-zero exit also emits explicit warning.
            err_fail = io.StringIO()
            with mock.patch("sys.stderr", err_fail), mock.patch.object(
                alr, "_find_systemctl", return_value="/usr/bin/systemctl"
            ), mock.patch.object(
                alr.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    ["systemctl"], 1, "", "Failed to connect"
                ),
            ):
                active2, ver2 = alr._probe_user_systemd(
                    runtime_base=Path(td),
                    user_systemd_sock_alive=True,
                    cgroup_root=cg,
                    uid=uid,
                )
            self.assertFalse(active2)
            self.assertIsNone(ver2)
            self.assertIn("WARNING:", err_fail.getvalue())

    def test_acquire_build_slot_propagates_caller_blocking_io_error(self) -> None:
        """`except BlockingIOError:` only wraps flock, never the caller's yield.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-slot-bio-") as td:
            rt = Path(td)
            with self.assertRaisesRegex(BlockingIOError, "caller-blocking"):
                with alr.acquire_build_slot(
                    2, 1.0, enabled=True, exclusive=False, runtime_base=rt
                ) as slot_idx:
                    self.assertEqual(slot_idx, 1)
                    raise BlockingIOError("caller-blocking")
            # Slot 1 must be cleanly unlocked and re-acquirable.
            with alr.acquire_build_slot(
                1, 0.5, enabled=True, exclusive=False, runtime_base=rt
            ) as slot_idx:
                self.assertEqual(slot_idx, 1)

    def test_systemd_run_launch_failure_falls_back_while_child_error_does_not(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-srun-fb-") as td:
            stub = Path(td) / "systemd-run"
            stub.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
            stub.chmod(0o755)
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=True,
                systemd_version=252,
                systemd_run_version=252,
                t_cg_is_user_service=False,
                cli_concurrency=1,
                mode="file",
            )
            marker_out = Path(td) / "ran.txt"
            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "_find_systemd_run", return_value=str(stub)):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--",
                        sys.executable,
                        "-c",
                        "import pathlib, sys; pathlib.Path(sys.argv[1]).write_text('ok')",
                        str(marker_out),
                    ]
                )
            self.assertEqual(rc, 0)
            self.assertEqual(marker_out.read_text(encoding="utf-8"), "ok")
            self.assertIn("before launching command; falling back", err_buf.getvalue())

            # When `systemd-run` dies by signal before writing marker, NEVER
            # fall back uncapped.
            sig_runs: list[list[str]] = []

            class _PreMarkerSignalProc:
                pid = 2**22 + 12350

                def __init__(self, argv: list[str], **_kwargs: Any) -> None:
                    sig_runs.append(list(argv))

                def wait(self, timeout: float | None = None) -> int:
                    return -signal.SIGTERM.value

                def poll(self) -> int:
                    return -signal.SIGTERM.value

            err_sig = io.StringIO()
            with mock.patch("sys.stderr", err_sig), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "_find_systemd_run", return_value=str(stub)), \
                 mock.patch.object(alr.subprocess, "Popen", _PreMarkerSignalProc):
                rc_sig = alr.main(["--mode", "file", "--no-slot-lock", "--", "false"])
            self.assertEqual(rc_sig, 128 + signal.SIGTERM.value)
            self.assertEqual(len(sig_runs), 1)

            # Wrapped `/bin/sh -c` tolerates unwritable
            # ANNEAL_LEAN_RUN_SCOPE_MARKER under dash.
            wrapped, _ = alr._build_scope_launch_cmd(
                ["true"],
                b_max_mb=2048,
                threads=1,
                timeout_sec=10,
                user_systemd_active=False,
                unit_name="dash.scope",
            )
            dash_res = subprocess.run(
                wrapped,
                env={**os.environ, "ANNEAL_LEAN_RUN_SCOPE_MARKER": "/nonexistent_dir/sub/marker"},
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(dash_res.returncode, 0, dash_res.stderr)

            # When the child itself exits nonzero after scope entry (marker
            # created), there is NO fallback and the child runs exactly once.
            runs: list[list[str]] = []

            class _ScopedChildFails:
                pid = 2**22 + 12351

                def __init__(self, argv: list[str], **kwargs: Any) -> None:
                    runs.append(list(argv))
                    m = (kwargs.get("env") or {}).get("ANNEAL_LEAN_RUN_SCOPE_MARKER")
                    if m:
                        Path(m).write_text("1", encoding="utf-8")

                def wait(self, timeout: float | None = None) -> int:
                    return 7

                def poll(self) -> int:
                    return 7

            err_buf2 = io.StringIO()
            with mock.patch("sys.stderr", err_buf2), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "_find_systemd_run", return_value=str(stub)), \
                 mock.patch.object(alr.subprocess, "Popen", _ScopedChildFails):
                rc2 = alr.main(["--mode", "file", "--no-slot-lock", "--", "false"])
            self.assertEqual(rc2, 7)
            self.assertEqual(len(runs), 1)
            self.assertEqual(err_buf2.getvalue(), "")

    def test_mid_run_marker_deletion_does_not_rerun_uncapped(self) -> None:
        """Deleting marker_dir mid-run must NOT trigger an uncapped fallback."""
        with tempfile.TemporaryDirectory(prefix="anneal-mkr-del-") as td:
            td_path = Path(td)
            count_file = td_path / "count.txt"
            stub = td_path / "systemd-run"
            stub.write_text(
                "#!/bin/sh\n"
                "while [ \"$1\" != \"--\" ]; do shift; done\n"
                "shift\n"
                "\"$@\"\n"
                "exit 3\n",
                encoding="utf-8",
            )
            stub.chmod(0o755)
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                user_systemd_active=True,
                systemd_version=252,
                systemd_run_version=252,
                t_cg_is_user_service=False,
                cli_concurrency=1,
                mode="file",
            )
            # Track marker path via spy Popen so child can remove marker_dir.
            real_popen = subprocess.Popen

            def track_marker_popen(argv: list[str], **kwargs: Any) -> Any:
                env = dict(kwargs.get("env") or {})
                if "ANNEAL_LEAN_RUN_SCOPE_MARKER" in env:
                    env["TEST_MARKER_PATH"] = env["ANNEAL_LEAN_RUN_SCOPE_MARKER"]
                    kwargs["env"] = env
                return real_popen(argv, **kwargs)

            child_del = (
                "import os, pathlib, shutil, sys, time; "
                "p = pathlib.Path(sys.argv[1]); "
                "prev = int(p.read_text()) if p.is_file() else 0; "
                "p.write_text(str(prev + 1), encoding='utf-8'); "
                "time.sleep(0.2); "
                "mp = os.environ.get('TEST_MARKER_PATH'); "
                "mp and shutil.rmtree(pathlib.Path(mp).parent, ignore_errors=True); "
                "time.sleep(0.1); "
                "sys.exit(3)"
            )
            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "_find_systemd_run", return_value=str(stub)), \
                 mock.patch.object(alr.subprocess, "Popen", side_effect=track_marker_popen):
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--",
                        sys.executable,
                        "-c",
                        child_del,
                        str(count_file),
                    ]
                )
            self.assertEqual(rc, 3, err_buf.getvalue())
            self.assertEqual(count_file.read_text(encoding="utf-8"), "1")
            self.assertNotIn("falling back", err_buf.getvalue())

            # Deleting marker_dir before entered_marker is written also never
            # triggers a second uncapped run.
            count_pre = td_path / "count_pre.txt"
            child_pre_del = (
                "import os, pathlib, shutil, sys; "
                "p = pathlib.Path(sys.argv[1]); "
                "prev = int(p.read_text()) if p.is_file() else 0; "
                "p.write_text(str(prev + 1), encoding='utf-8'); "
                "mp = os.environ.get('TEST_MARKER_PATH'); "
                "mp and shutil.rmtree(pathlib.Path(mp).parent, ignore_errors=True); "
                "sys.exit(3)"
            )
            err_pre = io.StringIO()
            with mock.patch("sys.stderr", err_pre), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr, "_find_systemd_run", return_value=str(stub)), \
                 mock.patch.object(alr.subprocess, "Popen", side_effect=track_marker_popen):
                rc_pre = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--",
                        sys.executable,
                        "-c",
                        child_pre_del,
                        str(count_pre),
                    ]
                )
            self.assertEqual(rc_pre, 3, err_pre.getvalue())
            self.assertEqual(count_pre.read_text(encoding="utf-8"), "1")
            self.assertNotIn("falling back", err_pre.getvalue())

    def test_killpg_eperm_wait_oserror_pre_handler_sigint_and_exit_race(self) -> None:
        """Covers signal exit race, killpg/wait error bounds, and SIGINT."""
        # os.killpg raising PermissionError must not escape cleanup.
        class _DummyProc:
            pid = 2**22 + 12352

            def poll(self) -> int:
                return 0

            def wait(self, timeout: float | None = None) -> int:
                return 0

        with mock.patch.object(alr.os, "killpg", side_effect=PermissionError("EPERM")):
            alr._kill_systemd_scope(None, _DummyProc(), Path("/tmp"), False, grace_sec=0.0)

        # OSError inside proc.wait() does not trigger fallback.
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=32768,
            mem_avail_mb=24576,
            user_systemd_active=True,
            systemd_version=260,
            systemd_run_version=260,
            t_cg_is_user_service=False,
            cli_concurrency=1,
            mode="file",
        )
        popen_calls = 0

        class _WaitOErrorProc:
            pid = 2**22 + 12353

            def __init__(self, _argv: list[str], **_kw: Any) -> None:
                nonlocal popen_calls
                popen_calls += 1

            def wait(self, timeout: float | None = None) -> int:
                raise OSError("waitpid boom")

            def poll(self) -> int:
                return 0

        with mock.patch("sys.stderr", io.StringIO()), \
             mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
             mock.patch.object(alr.subprocess, "Popen", _WaitOErrorProc):
            rc_wait_err = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
        self.assertEqual(rc_wait_err, 1)
        self.assertEqual(popen_calls, 1)

        # KeyboardInterrupt during pre-handler probe exits 130 cleanly.
        with mock.patch.object(alr, "probe_host_envelope", side_effect=KeyboardInterrupt):
            self.assertEqual(alr.main(["--", "true"]), 130)

        # Pending signal at end of run_bounded_command is handled while
        # masked and never raises _ForwardSignal during handler restoration.
        non_sd = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=16384,
            mem_avail_mb=12288,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="file",
        )
        with mock.patch.object(alr, "probe_host_envelope", return_value=non_sd), \
             mock.patch.object(alr.subprocess, "Popen", _FakePopen), \
             mock.patch.object(alr.signal, "sigpending", return_value={signal.SIGTERM}):
            rc_pend = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
        self.assertEqual(rc_pend, 128 + signal.SIGTERM.value)
        # Low-memory non-systemd host must warn on tiny `lean -M` without
        # failing with INSUFFICIENT_CGROUP_HEADROOM.
        low_non_systemd = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=4096,
            mem_avail_mb=2048,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="build",
        )
        self.assertLess(low_non_systemd["memory_max_mb"], 2048)
        err_non = io.StringIO()
        with mock.patch("sys.stderr", err_non), \
             mock.patch.object(alr, "probe_host_envelope", return_value=low_non_systemd):
            rc_non = alr.main(["--mode", "build", "--no-slot-lock", "--", "true"])
        self.assertEqual(rc_non, 0)
        self.assertNotIn("INSUFFICIENT_CGROUP_HEADROOM", err_non.getvalue())
        self.assertIn("LOW_MEMORY_HEADROOM", err_non.getvalue())

        low_probe_out = io.StringIO()
        with mock.patch("sys.stdout", low_probe_out), \
             mock.patch.object(alr, "probe_host_envelope", return_value=low_non_systemd):
            self.assertEqual(alr.main(["--probe", "--mode", "build"]), 0)
        self.assertIn("low headroom", low_probe_out.getvalue())

        # Enforced low-headroom systemd host refuses with exit 137 and hints
        # --memory-max-mb.
        low_systemd = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=4096,
            mem_avail_mb=2048,
            user_systemd_active=True,
            t_cg_is_user_service=True,
            cli_concurrency=1,
            mode="build",
        )
        err_sys = io.StringIO()
        with mock.patch("sys.stderr", err_sys), \
             mock.patch.object(alr, "probe_host_envelope", return_value=low_systemd), \
             mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
             mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"):
            rc_sys = alr.main(["--mode", "build", "--no-slot-lock", "--", "true"])
        self.assertEqual(rc_sys, 137)
        self.assertIn("INSUFFICIENT_CGROUP_HEADROOM", err_sys.getvalue())
        self.assertIn("--memory-max-mb", err_sys.getvalue())

        # Non-positive and out-of-range numeric CLI overrides are rejected (rc
        # 2).
        for bad_args in (
            ["--memory-max-mb", "0", "--", "true"],
            ["--memory-max-mb", "-1", "--", "true"],
            ["--timeout", "0", "--", "true"],
            ["--concurrency", "0", "--", "true"],
            ["--timeout", "99999999999999999999", "--", "true"],
            [
                "--unsafe-ignore-cgroup",
                "--memory-max-mb",
                "99999999999999999999",
                "--",
                "true",
            ],
            ["--concurrency", "99999999999999999999", "--", "true"],
        ):
            with mock.patch("sys.stderr", io.StringIO()):
                with self.assertRaises(SystemExit) as cm:
                    alr.main(bad_args)
            self.assertEqual(cm.exception.code, 2, bad_args)

        # Out-of-range env overrides warn on stderr and fall back safely, and
        # oversized concurrency files clamp to MAX_CONCURRENCY with a warning.
        env_err = io.StringIO()
        with mock.patch("sys.stderr", env_err), \
             mock.patch.dict(
                 os.environ,
                 {
                     "ANNEAL_LEAN_MEMORY_MAX_MB": "99999999999999999999",
                     "ANNEAL_LEAN_TIMEOUT_SEC": "0",
                     "ANNEAL_WORKTREE_CONCURRENCY": "999999",
                 },
             ):
            parsed = alr.build_parser().parse_args(["--", "true"])
            self.assertIsNone(parsed.memory_max_mb)
            self.assertIsNone(parsed.timeout)
            self.assertIsNone(
                alr._env_optional_pos_int(
                    "ANNEAL_WORKTREE_CONCURRENCY", max_value=alr.MAX_CONCURRENCY
                )
            )
        self.assertIn("ignoring out-of-range ANNEAL_LEAN_MEMORY_MAX_MB", env_err.getvalue())
        self.assertIn("ignoring out-of-range ANNEAL_LEAN_TIMEOUT_SEC", env_err.getvalue())
        self.assertIn("ignoring out-of-range ANNEAL_WORKTREE_CONCURRENCY", env_err.getvalue())

        with tempfile.TemporaryDirectory(prefix="anneal-conc-clamp-") as td:
            cpath = Path(td) / "concurrency"
            cpath.write_text(f"{alr.MAX_CONCURRENCY + 500}\n", encoding="utf-8")
            cerr = io.StringIO()
            with mock.patch("sys.stderr", cerr):
                self.assertEqual(alr.read_concurrency_config_file(cpath), alr.MAX_CONCURRENCY)
            self.assertIn("clamping", cerr.getvalue())

        # _ForwardSignal during an except OSError handler returns 128 + signum
        # cleanly without escaping.
        def _raise_fwd_on_write(_msg: str) -> int:
            raise alr._ForwardSignal(signal.SIGTERM.value)

        spy_err = mock.Mock()
        spy_err.write.side_effect = _raise_fwd_on_write
        with mock.patch("sys.stderr", spy_err), \
             mock.patch.object(alr, "probe_host_envelope", return_value=non_sd), \
             mock.patch.object(
                 alr, "acquire_build_slot", side_effect=PermissionError("slot EACCES")
             ):
            rc_err_sig = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
        self.assertEqual(rc_err_sig, 128 + signal.SIGTERM.value)

        # Pending signal arriving during timeout teardown returns 128 + sig.
        import time

        class _HangingTimeoutProc:
            pid = 2**22 + 12355

            def __init__(self, *_a: Any, **_kw: Any) -> None:
                pass

            def wait(self, timeout: float | None = None) -> int:
                time.sleep(min(0.05, max(0.01, timeout or 0.05)))
                raise subprocess.TimeoutExpired(cmd=["sleep"], timeout=timeout or 0)

            def poll(self) -> int | None:
                return 0

        sig_state = {"tripped": False}

        def _pending_during_kill(*_a: Any, **_kw: Any) -> None:
            sig_state["tripped"] = True

        with mock.patch("sys.stderr", io.StringIO()), \
             mock.patch.object(
                 alr, "probe_host_envelope", return_value={**non_sd, "timeout_sec": 1}
             ), \
             mock.patch.object(alr.subprocess, "Popen", _HangingTimeoutProc), \
             mock.patch.object(alr, "_kill_systemd_scope", side_effect=_pending_during_kill), \
             mock.patch.object(
                 alr.signal,
                 "sigpending",
                 side_effect=lambda: {signal.SIGTERM} if sig_state["tripped"] else set(),
             ):
            rc_to_sig = alr.main(
                ["--mode", "file", "--timeout", "1", "--no-slot-lock", "--", "sleep", "5"]
            )
        self.assertEqual(rc_to_sig, 128 + signal.SIGTERM.value)

        # CLI help must remain pure ASCII (for LC_ALL=C / latin-1) and state the
        # non-systemd caveat.
        raw_help = alr.build_parser().format_help()
        self.assertTrue(raw_help.isascii(), "CLI --help must be pure ASCII")
        help_txt = " ".join(raw_help.split())
        self.assertIn("cgroup hard cap requires active user systemd scope", help_txt)
        help_res = subprocess.run(
            [sys.executable, "-B", str(SCRIPT_PATH), "--help"],
            env={**os.environ, "LC_ALL": "C", "LANG": "C", "PYTHONIOENCODING": "ascii"},
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(help_res.returncode, 0, help_res.stderr)
        self.assertTrue(help_res.stdout.isascii())

        # Exclusive lock acquisition across MAX_CONCURRENCY under low
        # RLIMIT_NOFILE completes cleanly without EMFILE.
        with tempfile.TemporaryDirectory(prefix="anneal-excl-nofile-") as td:
            rt = Path(td)
            child_res = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    "-c",
                    (
                        "import importlib.machinery, importlib.util, pathlib, resource, sys\n"
                        "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
                        "spec = importlib.util.spec_from_loader('alr', loader)\n"
                        "mod = importlib.util.module_from_spec(spec)\n"
                        "loader.exec_module(mod)\n"
                        "soft, hard = resource.getrlimit(resource.RLIMIT_NOFILE)\n"
                        "rlim_inf = getattr(resource, 'RLIM_INFINITY', -1)\n"
                        "target = 256 if (hard == rlim_inf or hard <= 0) else min(hard, 256)\n"
                        "resource.setrlimit(resource.RLIMIT_NOFILE, (target, target))\n"
                        "with mod.acquire_build_slot(\n"
                        "    mod.MAX_CONCURRENCY, 2.0, enabled=True, exclusive=True,\n"
                        "    runtime_base=pathlib.Path(sys.argv[2])\n"
                        ") as slots:\n"
                        "    assert len(slots) == mod.MAX_CONCURRENCY, len(slots)\n"
                    ),
                    str(SCRIPT_PATH),
                    str(rt),
                ],
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(child_res.returncode, 0, child_res.stderr)


class TestWatchdogSignalsAndCpuLimits(unittest.TestCase):
    """Tests `BuildWatchdog.tick`, signal normalization/forwarding, and
    CPU/macOS fixes.
    """

    def test_build_watchdog_tick_transitions(self) -> None:
        a_path = Path("/fake/user.slice")
        state = {"w": 1000, "high": 0, "psi": 0.0}
        wd = alr.BuildWatchdog(
            is_cg_capped=True,
            capped_ancestors=[(a_path, 10000)],
            read_w_fn=lambda _p: int(state["w"]),
            read_local_high_fn=lambda _p: int(state["high"]),
            read_psi_fn=lambda _p: float(state["psi"]),
        )
        # Healthy.
        self.assertEqual(wd.tick(1.0), {"action": "ok", "breach_ticks": 0})
        # Breach 1 via working-set threshold (c_high=10000 ->
        # thresh=10000-1000=9000).
        state["w"] = 9050
        self.assertEqual(wd.tick(3.0), {"action": "ok", "breach_ticks": 1})
        # Reset on recovery.
        state["w"] = 5000
        self.assertEqual(wd.tick(5.0), {"action": "ok", "breach_ticks": 0})
        # Consecutive 3 ticks via delta_local_high > 0 + PSI full >= 20 ->
        # abort_pressure.
        for t, expect_action, expect_ticks in (
            (7.0, "ok", 1),
            (9.0, "ok", 2),
            (11.0, "abort_pressure", 3),
        ):
            state["high"] = int(state["high"]) + 1
            state["psi"] = 25.0
            self.assertEqual(
                wd.tick(t), {"action": expect_action, "breach_ticks": expect_ticks}
            )

        # Uncapped host never aborts.
        uncapped = alr.BuildWatchdog(
            is_cg_capped=False,
            capped_ancestors=[(a_path, 10000)],
        )
        self.assertEqual(uncapped.tick(1.0), {"action": "ok", "breach_ticks": 0})

    def test_child_signal_exit_codes_and_wrapper_signal_forwarding(self) -> None:
        limits = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=16384,
            mem_avail_mb=12288,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="file",
        )
        with mock.patch.object(alr, "probe_host_envelope", return_value=limits):
            # SIGTERM from child -> 128 + 15 = 143; SIGKILL -> 137.
            rc_term = alr.main(
                ["--mode", "file", "--no-slot-lock", "--", sys.executable, "-c",
                 f"import os, signal; os.kill(os.getpid(), {signal.SIGTERM.value})"]
            )
            self.assertEqual(rc_term, 128 + signal.SIGTERM.value)
            with mock.patch("sys.stderr", io.StringIO()):
                rc_kill = alr.main(
                    ["--mode", "file", "--no-slot-lock", "--", sys.executable, "-c",
                     f"import os, signal; os.kill(os.getpid(), {signal.SIGKILL.value})"]
                )
            self.assertEqual(rc_kill, 128 + signal.SIGKILL.value)

        # Wrapper signal forwarding cleans up child via _kill_systemd_scope and
        # returns 128 + sig.
        class _HangingProc:
            pid = 2**22 + 12354

            def __init__(self, *_a: Any, **_kw: Any) -> None:
                self._killed = False

            def wait(self, timeout: float | None = None) -> int:
                raise alr._ForwardSignal(signal.SIGTERM.value)

            def poll(self) -> int | None:
                return 0 if self._killed else None

        killed: list[int] = []

        def fake_kill(_unit: Any, proc: Any, _rb: Any, _alive: Any, grace_sec: float = 2.0) -> None:
            proc._killed = True
            killed.append(proc.pid)

        with mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
             mock.patch.object(alr.subprocess, "Popen", _HangingProc), \
             mock.patch.object(alr, "_kill_systemd_scope", side_effect=fake_kill):
            rc_fwd = alr.main(["--mode", "file", "--no-slot-lock", "--", "sleep", "10"])
        self.assertEqual(rc_fwd, 128 + signal.SIGTERM.value)
        self.assertEqual(killed, [2**22 + 12354])

    def test_repeated_signals_during_cleanup_kill_term_ignoring_child_without_traceback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-sig-multi-") as td:
            td_path = Path(td)
            xdg_dir = td_path / "xdg"
            _seed_workloads_slice_unit(xdg_dir)
            ready_file = td_path / "child_pid"
            child_script = (
                "import os, pathlib, signal, sys, time; "
                "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
                "pathlib.Path(sys.argv[1]).write_text(str(os.getpid()), encoding='utf-8'); "
                "time.sleep(60)"
            )
            env = _isolated_cli_env(xdg_dir, {"TMPDIR": td})
            wrapper = subprocess.Popen(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT_PATH),
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--memory-max-mb",
                    "512",
                    "--",
                    sys.executable,
                    "-c",
                    child_script,
                    str(ready_file),
                ],
                env=env,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                import time

                deadline = time.monotonic() + 10.0
                while not ready_file.is_file() or not ready_file.read_text(encoding="utf-8").strip():
                    if wrapper.poll() is not None or time.monotonic() >= deadline:
                        self.fail("child did not write pid before timeout")
                    time.sleep(0.05)
                child_pid = int(ready_file.read_text(encoding="utf-8").strip())

                # Deliver three signals ~50ms apart during grace_sec=2s
                # teardown.
                wrapper.send_signal(signal.SIGTERM)
                time.sleep(0.05)
                wrapper.send_signal(signal.SIGTERM)
                time.sleep(0.05)
                wrapper.send_signal(signal.SIGINT)

                stdout, stderr = wrapper.communicate(timeout=15)
            finally:
                if wrapper.poll() is None:
                    wrapper.kill()
                    wrapper.wait()

            self.assertEqual(wrapper.returncode, 128 + signal.SIGTERM.value, stderr)
            self.assertNotIn("Traceback", stderr)
            self.assertNotIn("ignored due to race condition", stderr)
            # Confirm the TERM-ignoring child was reaped/killed via SIGKILL.
            with self.assertRaises(ProcessLookupError):
                os.kill(child_pid, 0)
            self.assertEqual(list(td_path.glob("anneal-scope-marker-*")), [])

    def test_launch_window_signals_and_double_signals_do_not_orphan_or_leak(
        self,
    ) -> None:
        """Signals during marker/Popen setup never orphan, crash, or leak
        markers.
        """
        import time

        modes: list[tuple[str, dict[str, str]]] = [("non-systemd", {"XDG_RUNTIME_DIR": "/nonexistent"})]
        if _can_launch_live_systemd_scope():
            modes.insert(0, ("systemd", {}))

        child_script = (
            "import os, pathlib, sys, time; "
            "pathlib.Path(sys.argv[1]).write_text(str(os.getpid()), encoding='utf-8'); "
            "time.sleep(60)"
        )
        for mode_label, extra_env in modes:
            for trial in range(10):
                with tempfile.TemporaryDirectory(prefix="anneal-lw-") as td:
                    td_path = Path(td)
                    xdg_dir = td_path / "xdg"
                    _seed_workloads_slice_unit(xdg_dir)
                    pid_file = td_path / "child.pid"
                    env = _isolated_cli_env(xdg_dir, {"TMPDIR": td, **extra_env})
                    if mode_label == "non-systemd":
                        # Force non-systemd via bogus systemctl/systemd-run on
                        # PATH.
                        shim_bin = td_path / "shim"
                        shim_bin.mkdir()
                        for tool in ("systemctl", "systemd-run"):
                            p = shim_bin / tool
                            p.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                            p.chmod(0o755)
                        env["PATH"] = f"{shim_bin}:{env.get('PATH', '')}"
                    wrapper = subprocess.Popen(
                        [
                            sys.executable,
                            "-B",
                            str(SCRIPT_PATH),
                            "--mode",
                            "file",
                            "--no-slot-lock",
                            "--memory-max-mb",
                            "512",
                            "--",
                            sys.executable,
                            "-c",
                            child_script,
                            str(pid_file),
                        ],
                        env=env,
                        stdin=subprocess.DEVNULL,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                    )
                    try:
                        # Poll tightly for anneal-scope-marker-* and send
                        # SIGTERM.
                        deadline = time.monotonic() + 5.0
                        while not list(td_path.glob("anneal-scope-marker-*")):
                            if wrapper.poll() is not None or time.monotonic() >= deadline:
                                break
                            time.sleep(0.0005)
                        if wrapper.poll() is None:
                            wrapper.send_signal(signal.SIGTERM)
                        _, stderr = wrapper.communicate(timeout=15)
                    finally:
                        if wrapper.poll() is None:
                            wrapper.kill()
                            wrapper.wait()
                    self.assertEqual(
                        wrapper.returncode,
                        128 + signal.SIGTERM.value,
                        (mode_label, trial, stderr),
                    )
                    self.assertNotIn("Traceback", stderr, (mode_label, trial))
                    self.assertEqual(
                        list(td_path.glob("anneal-scope-marker-*")),
                        [],
                        (mode_label, trial),
                    )
                    if pid_file.is_file() and pid_file.read_text(encoding="utf-8").strip():
                        cpid = int(pid_file.read_text(encoding="utf-8").strip())
                        time.sleep(0.05)
                        with self.assertRaises(ProcessLookupError):
                            os.kill(cpid, 0)

        # Same-instant double signal (SIGTERM + SIGINT back-to-back) must never
        # emit `ignored due to race condition` or crash.
        with tempfile.TemporaryDirectory(prefix="anneal-dbl-sig-") as td:
            td_path = Path(td)
            xdg_dir = td_path / "xdg"
            _seed_workloads_slice_unit(xdg_dir)
            pid_file = td_path / "child.pid"
            env = _isolated_cli_env(xdg_dir, {"TMPDIR": td})
            wrapper = subprocess.Popen(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT_PATH),
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--memory-max-mb",
                    "512",
                    "--",
                    sys.executable,
                    "-c",
                    child_script,
                    str(pid_file),
                ],
                env=env,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )
            try:
                deadline = time.monotonic() + 10.0
                while not pid_file.is_file() or not pid_file.read_text(encoding="utf-8").strip():
                    if wrapper.poll() is not None or time.monotonic() >= deadline:
                        self.fail("child did not start before timeout")
                    time.sleep(0.02)
                cpid = int(pid_file.read_text(encoding="utf-8").strip())
                wrapper.send_signal(signal.SIGTERM)
                wrapper.send_signal(signal.SIGINT)
                _, stderr = wrapper.communicate(timeout=15)
            finally:
                if wrapper.poll() is None:
                    wrapper.kill()
                    wrapper.wait()
            self.assertIn(
                wrapper.returncode,
                (128 + signal.SIGTERM.value, 128 + signal.SIGINT.value),
                stderr,
            )
            self.assertNotIn("Traceback", stderr)
            self.assertNotIn("ignored due to race condition", stderr)
            with self.assertRaises(ProcessLookupError):
                os.kill(cpid, 0)
            self.assertEqual(list(td_path.glob("anneal-scope-marker-*")), [])

    def test_launch_window_killpg_group_signals_return_128_plus_sig(self) -> None:
        """Process-group launch-window signals return 128+sig with no leaks."""
        import time

        modes: list[tuple[str, dict[str, str]]] = [
            ("non-systemd", {"XDG_RUNTIME_DIR": "/nonexistent"})
        ]
        if _can_launch_live_systemd_scope():
            modes.insert(0, ("systemd", {}))

        sigs = [signal.SIGTERM, signal.SIGHUP, signal.SIGINT]
        sigquit = getattr(signal, "SIGQUIT", None)
        if sigquit is not None:
            sigs.append(sigquit)

        child_script = (
            "import os, pathlib, sys, time; "
            "pathlib.Path(sys.argv[1]).write_text(str(os.getpid()), encoding='utf-8'); "
            "time.sleep(60)"
        )

        def _reset_dfl() -> None:
            for s in sigs:
                signal.signal(s, signal.SIG_DFL)

        for mode_label, extra_env in modes:
            for sig in sigs:
                for delay_ms in (0, 1, 2, 4):
                    with tempfile.TemporaryDirectory(prefix="anneal-killpg-") as td:
                        td_path = Path(td)
                        xdg_dir = td_path / "xdg"
                        _seed_workloads_slice_unit(xdg_dir)
                        pid_file = td_path / "child.pid"
                        env = _isolated_cli_env(xdg_dir, {"TMPDIR": td, **extra_env})
                        if mode_label == "non-systemd":
                            shim_bin = td_path / "shim"
                            shim_bin.mkdir()
                            for tool in ("systemctl", "systemd-run"):
                                p = shim_bin / tool
                                p.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                                p.chmod(0o755)
                            env["PATH"] = f"{shim_bin}:{env.get('PATH', '')}"

                        wrapper = subprocess.Popen(
                            [
                                sys.executable,
                                "-B",
                                str(SCRIPT_PATH),
                                "--mode",
                                "file",
                                "--no-slot-lock",
                                "--memory-max-mb",
                                "512",
                                "--",
                                sys.executable,
                                "-c",
                                child_script,
                                str(pid_file),
                            ],
                            env=env,
                            stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                            start_new_session=True,
                            preexec_fn=_reset_dfl,
                        )
                        try:
                            deadline = time.monotonic() + 5.0
                            while not list(td_path.glob("anneal-scope-marker-*")):
                                if wrapper.poll() is not None or time.monotonic() >= deadline:
                                    break
                                time.sleep(0.0005)
                            if delay_ms > 0:
                                time.sleep(delay_ms / 1000.0)
                            if wrapper.poll() is None:
                                os.killpg(wrapper.pid, sig)
                            _, stderr = wrapper.communicate(timeout=15)
                        finally:
                            if wrapper.poll() is None:
                                os.killpg(wrapper.pid, signal.SIGKILL)
                                wrapper.communicate()
                            if wrapper.stdout is not None:
                                wrapper.stdout.close()
                            if wrapper.stderr is not None:
                                wrapper.stderr.close()

                        self.assertEqual(
                            wrapper.returncode,
                            128 + sig.value,
                            (mode_label, sig, delay_ms, stderr),
                        )
                        self.assertNotIn("Traceback", stderr)
                        self.assertNotIn("SubprocessError", stderr)
                        if pid_file.is_file() and pid_file.read_text().strip():
                            cpid = int(pid_file.read_text().strip())
                            time.sleep(0.05)
                            with self.assertRaises(ProcessLookupError):
                                os.kill(cpid, 0)
                        self.assertEqual(
                            list(td_path.glob("anneal-scope-marker-*")), []
                        )

    def test_inherited_sig_ign_and_sigquit_across_systemd_and_non_systemd(
        self,
    ) -> None:
        """Verifies inherited SIG_IGN preservation and SIGQUIT forwarding."""
        import time

        modes: list[tuple[str, dict[str, str]]] = [
            ("non-systemd", {"XDG_RUNTIME_DIR": "/nonexistent"})
        ]
        if _can_launch_live_systemd_scope():
            modes.insert(0, ("systemd", {}))

        child_script = (
            "import os, pathlib, sys, time; "
            "pathlib.Path(sys.argv[1]).write_text(str(os.getpid()), encoding='utf-8'); "
            "time.sleep(60)"
        )

        sigquit = getattr(signal, "SIGQUIT", None)
        ign_sigs = [signal.SIGHUP, signal.SIGINT]
        if sigquit is not None:
            ign_sigs.append(sigquit)
        ign_child_script = (
            "import os, pathlib, signal, sys, time; "
            "sig = int(sys.argv[2]); "
            "is_ign = signal.getsignal(sig) is signal.SIG_IGN; "
            "pathlib.Path(sys.argv[1]).write_text("
            "f'{os.getpid()}:{is_ign}', encoding='utf-8'); "
            "time.sleep(60)"
        )

        all_reset_sigs = list(ign_sigs) + [signal.SIGTERM]

        for mode_label, extra_env in modes:
            # 1. Inherited SIG_IGN on SIGHUP/SIGINT/SIGQUIT is preserved for
            # both wrapper and child, while SIGTERM still terminates cleanly.
            for ign_sig in ign_sigs:
                with tempfile.TemporaryDirectory(prefix="anneal-sigign-") as td:
                    td_path = Path(td)
                    xdg_dir = td_path / "xdg"
                    _seed_workloads_slice_unit(xdg_dir)
                    pid_file = td_path / "child.pid"
                    env = _isolated_cli_env(xdg_dir, {"TMPDIR": td, **extra_env})
                    if mode_label == "non-systemd":
                        shim_bin = td_path / "shim"
                        shim_bin.mkdir()
                        for tool in ("systemctl", "systemd-run"):
                            p = shim_bin / tool
                            p.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                            p.chmod(0o755)
                        env["PATH"] = f"{shim_bin}:{env.get('PATH', '')}"

                    def _ignore_in_wrapper(s: int = ign_sig.value) -> None:
                        for rs in all_reset_sigs:
                            signal.signal(rs, signal.SIG_DFL)
                        signal.signal(s, signal.SIG_IGN)

                    wrapper = subprocess.Popen(
                        [
                            sys.executable,
                            "-B",
                            str(SCRIPT_PATH),
                            "--mode",
                            "file",
                            "--no-slot-lock",
                            "--memory-max-mb",
                            "512",
                            "--",
                            sys.executable,
                            "-c",
                            ign_child_script,
                            str(pid_file),
                            str(ign_sig.value),
                        ],
                        env=env,
                        stdin=subprocess.DEVNULL,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        preexec_fn=_ignore_in_wrapper,
                    )
                    try:
                        deadline = time.monotonic() + 10.0
                        while (
                            not pid_file.is_file()
                            or ":" not in pid_file.read_text(encoding="utf-8")
                        ):
                            if wrapper.poll() is not None or time.monotonic() >= deadline:
                                self.fail(f"{mode_label} child never started")
                            time.sleep(0.02)
                        pid_raw, ign_raw = pid_file.read_text(encoding="utf-8").strip().split(":", 1)
                        cpid = int(pid_raw)
                        self.assertEqual(
                            ign_raw,
                            "True",
                            (mode_label, ign_sig, "child lost SIG_IGN"),
                        )
                        wrapper.send_signal(ign_sig)
                        time.sleep(0.2)
                        self.assertIsNone(
                            wrapper.poll(),
                            (mode_label, ign_sig, "wrapper died on ignored signal"),
                        )
                        os.kill(cpid, 0)
                        wrapper.send_signal(signal.SIGTERM)
                        _, stderr = wrapper.communicate(timeout=15)
                    finally:
                        if wrapper.poll() is None:
                            wrapper.kill()
                            wrapper.communicate()
                        if wrapper.stdout is not None:
                            wrapper.stdout.close()
                        if wrapper.stderr is not None:
                            wrapper.stderr.close()
                    self.assertEqual(
                        wrapper.returncode,
                        128 + signal.SIGTERM.value,
                        (mode_label, ign_sig, stderr),
                    )
                    with self.assertRaises(ProcessLookupError):
                        os.kill(cpid, 0)
                    self.assertEqual(list(td_path.glob("anneal-scope-marker-*")), [])

            # 2. SIGQUIT kills detached child, removes marker, and exits 131
            # cleanly regardless of caller backgrounding dispositions.
            if sigquit is not None:
                with tempfile.TemporaryDirectory(prefix="anneal-sigquit-") as td:
                    td_path = Path(td)
                    xdg_dir = td_path / "xdg"
                    _seed_workloads_slice_unit(xdg_dir)
                    pid_file = td_path / "child.pid"
                    env = _isolated_cli_env(xdg_dir, {"TMPDIR": td, **extra_env})
                    if mode_label == "non-systemd":
                        shim_bin = td_path / "shim"
                        shim_bin.mkdir()
                        for tool in ("systemctl", "systemd-run"):
                            p = shim_bin / tool
                            p.write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
                            p.chmod(0o755)
                        env["PATH"] = f"{shim_bin}:{env.get('PATH', '')}"

                    def _reset_quit_dfl() -> None:
                        for rs in all_reset_sigs:
                            signal.signal(rs, signal.SIG_DFL)

                    wrapper = subprocess.Popen(
                        [
                            sys.executable,
                            "-B",
                            str(SCRIPT_PATH),
                            "--mode",
                            "file",
                            "--no-slot-lock",
                            "--memory-max-mb",
                            "512",
                            "--",
                            sys.executable,
                            "-c",
                            child_script,
                            str(pid_file),
                        ],
                        env=env,
                        stdin=subprocess.DEVNULL,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE,
                        text=True,
                        preexec_fn=_reset_quit_dfl,
                    )
                    try:
                        deadline = time.monotonic() + 10.0
                        while (
                            not pid_file.is_file()
                            or not pid_file.read_text(encoding="utf-8").strip()
                        ):
                            if wrapper.poll() is not None or time.monotonic() >= deadline:
                                self.fail(f"{mode_label} child never started")
                            time.sleep(0.02)
                        cpid = int(pid_file.read_text(encoding="utf-8").strip())
                        wrapper.send_signal(sigquit)
                        _, stderr = wrapper.communicate(timeout=15)
                    finally:
                        if wrapper.poll() is None:
                            wrapper.kill()
                            wrapper.communicate()
                        if wrapper.stdout is not None:
                            wrapper.stdout.close()
                        if wrapper.stderr is not None:
                            wrapper.stderr.close()
                    self.assertEqual(
                        wrapper.returncode,
                        128 + sigquit.value,
                        (mode_label, stderr),
                    )
                    self.assertNotIn("Traceback", stderr)
                    time.sleep(0.05)
                    with self.assertRaises(ProcessLookupError):
                        os.kill(cpid, 0)
                    self.assertEqual(list(td_path.glob("anneal-scope-marker-*")), [])

    def test_oom_score_adj_check_has_zero_stderr_noise_when_unwritable(self) -> None:
        # Exercise the exact wrapped shell command when pointing at a
        # nonexistent oom_score_adj path.
        argv, in_scope = alr._build_scope_launch_cmd(
            ["true"],
            b_max_mb=2048,
            threads=1,
            timeout_sec=10,
            user_systemd_active=False,
            unit_name="test.scope",
        )
        self.assertFalse(in_scope)
        patched_sh = argv[2].replace("/proc/self/oom_score_adj", "/nonexistent/oom_score_adj")
        res = subprocess.run(
            ["/bin/sh", "-c", patched_sh, "_", "true"],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0)
        self.assertEqual(res.stderr, "")

    def test_cpu_count_honors_sched_getaffinity_and_cgroup_cpu_max(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-cpumax-") as td:
            root = Path(td)
            cg = root / "cg"
            _write_cgroup_file(root / "proc_cg", "0::/job.scope\n")
            _write_cgroup_file(cg / "job.scope" / "cpu.max", "200000 100000\n")
            _write_cgroup_file(cg / "job.scope" / "memory.max", "max\n")

            with mock.patch.object(alr.os, "cpu_count", return_value=16), \
                 mock.patch.object(alr.os, "sched_getaffinity", return_value={0, 1, 2, 3}, create=True):
                self.assertEqual(
                    alr._detect_effective_cpu_cores(cg, root / "proc_cg"),
                    2,
                )

            _write_cgroup_file(cg / "job.scope" / "cpu.max", "max 100000\n")
            with mock.patch.object(alr.os, "cpu_count", return_value=16), \
                 mock.patch.object(alr.os, "sched_getaffinity", return_value={0, 1, 2, 3}, create=True):
                self.assertEqual(
                    alr._detect_effective_cpu_cores(cg, root / "proc_cg"),
                    4,
                )

    def test_exclusive_starvation_emfile_warnings_and_exit_shield(self) -> None:
        """Tests exclusive writer-priority gating, EMFILE fd recovery,
        deduped strict env/config warnings, budget=0 message, and exit shield.
        """
        import time

        # 1. Exclusive writer-priority acquires promptly against alternating
        # shared clients in both 1-slot/2-client and 2-slot/3-client regimes.
        shared_worker_code = (
            "import importlib.machinery, importlib.util, pathlib, sys, time\n"
            "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
            "spec = importlib.util.spec_from_loader('alr', loader)\n"
            "mod = importlib.util.module_from_spec(spec)\n"
            "loader.exec_module(mod)\n"
            "rt = pathlib.Path(sys.argv[2])\n"
            "max_slots = int(sys.argv[3])\n"
            "wid = sys.argv[4]\n"
            "log_p = pathlib.Path(sys.argv[5])\n"
            "stop_p = pathlib.Path(sys.argv[6])\n"
            "ready_p = pathlib.Path(sys.argv[7])\n"
            "it = 0\n"
            "while not stop_p.is_file():\n"
            "    try:\n"
            "        with mod.acquire_build_slot(\n"
            "            max_slots, 3.0, enabled=True, exclusive=False,\n"
            "            runtime_base=rt, poll_interval=0.01\n"
            "        ) as slot:\n"
            "            ready_p.write_text('1', encoding='utf-8')\n"
            "            with log_p.open('a', encoding='utf-8') as f:\n"
            "                f.write(f'S:{wid}:{it}:{slot}:in\\n')\n"
            "            time.sleep(0.06)\n"
            "            with log_p.open('a', encoding='utf-8') as f:\n"
            "                f.write(f'S:{wid}:{it}:{slot}:out\\n')\n"
            "            it += 1\n"
            "        time.sleep(0.02)\n"
            "    except TimeoutError:\n"
            "        continue\n"
        )
        excl_worker_code = (
            "import importlib.machinery, importlib.util, pathlib, sys, time\n"
            "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
            "spec = importlib.util.spec_from_loader('alr', loader)\n"
            "mod = importlib.util.module_from_spec(spec)\n"
            "loader.exec_module(mod)\n"
            "rt = pathlib.Path(sys.argv[2])\n"
            "max_slots = int(sys.argv[3])\n"
            "log_p = pathlib.Path(sys.argv[4])\n"
            "with mod.acquire_build_slot(\n"
            "    max_slots, 2.5, enabled=True, exclusive=True,\n"
            "    runtime_base=rt, poll_interval=0.01\n"
            ") as slots:\n"
            "    assert len(slots) == max_slots, slots\n"
            "    with log_p.open('a', encoding='utf-8') as f:\n"
            "        f.write('E:in\\n')\n"
            "    time.sleep(0.08)\n"
            "    with log_p.open('a', encoding='utf-8') as f:\n"
            "        f.write('E:out\\n')\n"
        )
        for max_slots, n_shared in ((1, 2), (2, 3)):
            with tempfile.TemporaryDirectory(prefix="anneal-excl-fair-") as td:
                td_p = Path(td)
                rt = td_p / "rt"
                rt.mkdir()
                log_p = td_p / "events.log"
                stop_p = td_p / "stop"
                workers: list[subprocess.Popen[str]] = []
                try:
                    for i in range(n_shared):
                        ready_p = td_p / f"ready-{i}"
                        wp = subprocess.Popen(
                            [
                                sys.executable,
                                "-B",
                                "-c",
                                shared_worker_code,
                                str(SCRIPT_PATH),
                                str(rt),
                                str(max_slots),
                                str(i),
                                str(log_p),
                                str(stop_p),
                                str(ready_p),
                            ],
                            stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE,
                            text=True,
                        )
                        workers.append(wp)
                        deadline = time.monotonic() + 10.0
                        while not ready_p.is_file():
                            if wp.poll() is not None or time.monotonic() >= deadline:
                                err_txt = wp.stderr.read() if wp.stderr else ""
                                self.fail(
                                    f"shared worker {i} failed to start "
                                    f"(rc={wp.returncode}): {err_txt}"
                                )
                            time.sleep(0.01)

                    ex_res = subprocess.run(
                        [
                            sys.executable,
                            "-B",
                            "-c",
                            excl_worker_code,
                            str(SCRIPT_PATH),
                            str(rt),
                            str(max_slots),
                            str(log_p),
                        ],
                        stdin=subprocess.DEVNULL,
                        capture_output=True,
                        text=True,
                        timeout=10,
                        check=False,
                    )
                    self.assertEqual(
                        ex_res.returncode,
                        0,
                        (max_slots, n_shared, ex_res.stderr),
                    )
                finally:
                    stop_p.write_text("1", encoding="utf-8")
                    for wp in workers:
                        try:
                            wp.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            wp.kill()
                            wp.wait()
                        self.assertEqual(wp.returncode, 0, wp.stderr.read() if wp.stderr else "")
                        if wp.stdout is not None:
                            wp.stdout.close()
                        if wp.stderr is not None:
                            wp.stderr.close()

                events = log_p.read_text(encoding="utf-8").splitlines()
                self.assertIn("E:in", events)
                self.assertIn("E:out", events)
                e_in_idx = events.index("E:in")
                e_out_idx = events.index("E:out")
                self.assertEqual(e_out_idx, e_in_idx + 1, events)

        # CLI --help for --exclusive documents intent-gate writer priority.
        raw_help = alr.build_parser().format_help()
        help_txt = " ".join(raw_help.split())
        self.assertIn("exclusive_intent.lock", help_txt)
        self.assertIn("intent gating", help_txt)
        self.assertIn("slotted-build", help_txt)
        self.assertIn("--no-slot-lock", help_txt)

        # 2. EMFILE recovery under RLIMIT_NOFILE=256 with 80 extra open FDs
        # succeeds cleanly and still allows subprocess execution inside slot.
        with tempfile.TemporaryDirectory(prefix="anneal-emfile-") as td:
            rt = Path(td)
            emfile_res = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    "-c",
                    (
                        "import importlib.machinery, importlib.util, os, "
                        "pathlib, resource, subprocess, sys\n"
                        "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
                        "spec = importlib.util.spec_from_loader('alr', loader)\n"
                        "mod = importlib.util.module_from_spec(spec)\n"
                        "loader.exec_module(mod)\n"
                        "_, hard = resource.getrlimit(resource.RLIMIT_NOFILE)\n"
                        "rlim_inf = getattr(resource, 'RLIM_INFINITY', -1)\n"
                        "target = 256 if (hard == rlim_inf or hard <= 0) else min(hard, 256)\n"
                        "resource.setrlimit(resource.RLIMIT_NOFILE, (target, target))\n"
                        "extra = [os.open(os.devnull, os.O_RDONLY) for _ in range(80)]\n"
                        "try:\n"
                        "    with mod.acquire_build_slot(\n"
                        "        mod.MAX_CONCURRENCY, 2.0, enabled=True, exclusive=True,\n"
                        "        runtime_base=pathlib.Path(sys.argv[2])\n"
                        "    ) as slots:\n"
                        "        assert len(slots) == mod.MAX_CONCURRENCY, len(slots)\n"
                        "        p = subprocess.run([sys.executable, '-c', 'print(1)'], "
                        "capture_output=True, text=True, check=True)\n"
                        "        assert p.stdout.strip() == '1'\n"
                        "finally:\n"
                        "    for fd in extra:\n"
                        "        os.close(fd)\n"
                    ),
                    str(SCRIPT_PATH),
                    str(rt),
                ],
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(emfile_res.returncode, 0, emfile_res.stderr)

        # 3. Strict ASCII validation rejects underscores/non-numeric env & file
        # values, and invocation-scoped warnings are deduplicated.
        bad_env_err = io.StringIO()
        with mock.patch("sys.stderr", bad_env_err):
            for bad_tok in ("1_0", "abc", "1e3", "-5"):
                with mock.patch.dict(
                    os.environ, {"ANNEAL_WORKTREE_CONCURRENCY": bad_tok}
                ):
                    self.assertIsNone(
                        alr._env_optional_pos_int(
                            "ANNEAL_WORKTREE_CONCURRENCY",
                            max_value=alr.MAX_CONCURRENCY,
                        )
                    )
        bad_err_txt = bad_env_err.getvalue()
        for bad_tok in ("1_0", "abc", "1e3", "-5"):
            self.assertIn(repr(bad_tok), bad_err_txt)
        with mock.patch("sys.stderr", io.StringIO()):
            with self.assertRaises(SystemExit) as cm_under:
                alr.main(["--concurrency", "1_0", "--", "true"])
            self.assertEqual(cm_under.exception.code, 2)

        with tempfile.TemporaryDirectory(prefix="anneal-dedup-warn-") as td:
            td_p = Path(td)
            xdg = td_p / "xdg"
            _write_cgroup_file(
                xdg / "anneal" / "concurrency",
                f"{alr.MAX_CONCURRENCY + 77}\n",
            )
            fake_root = td_p / "fake"
            _write_synthetic_host_base(fake_root)
            _write_cgroup_file(fake_root / "cgroup" / "memory.max", "max\n")
            dedup_err = io.StringIO()
            with mock.patch("sys.stderr", dedup_err), \
                 mock.patch.dict(
                     os.environ,
                     {
                         "XDG_CONFIG_HOME": str(xdg),
                         "ANNEAL_WORKTREE_CONCURRENCY": str(alr.MAX_CONCURRENCY + 5),
                     },
                 ):
                # Re-probe twice inside a single main() invocation by wrapping
                # probe_host_envelope to read real env + config each call.
                real_probe = alr.probe_host_envelope

                def _local_probe(**kw: Any) -> dict[str, Any]:
                    kw["meminfo_path"] = fake_root / "meminfo"
                    kw["cgroup_root"] = fake_root / "cgroup"
                    kw["proc_cgroup_path"] = fake_root / "proc_cgroup"
                    kw["cpu_cores"] = 4
                    kw["user_systemd_active"] = False
                    kw["runtime_base"] = td_p
                    return real_probe(**kw)

                with mock.patch.object(alr, "probe_host_envelope", side_effect=_local_probe):
                    rc_dedup = alr.main(["--mode", "build", "--no-slot-lock", "--", "true"])
                self.assertEqual(rc_dedup, 0, dedup_err.getvalue())
            d_txt = dedup_err.getvalue()
            self.assertEqual(d_txt.count("ignoring out-of-range ANNEAL_WORKTREE_CONCURRENCY"), 1, d_txt)
            self.assertEqual(d_txt.count("exceeds max 4096; clamping to 4096"), 1, d_txt)

            # Reject underscores in concurrency file too.
            _write_cgroup_file(xdg / "anneal" / "concurrency", "1_0\n")
            with mock.patch("sys.stderr", io.StringIO()) as cerr, \
                 mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": str(xdg)}):
                self.assertIsNone(alr.read_concurrency_config_file())
                self.assertIn("ignoring invalid", cerr.getvalue())

        # 4. Budget=0 reports skipped lean -M injection instead of `lean -M 0`.
        zero_env = alr.compute_workload_memory_envelope(
            cpu_cores=4,
            mem_total_mb=1024,
            mem_avail_mb=128,
            user_systemd_active=False,
            cli_concurrency=1,
            mode="build",
        )
        self.assertEqual(zero_env["memory_max_mb"], 0)
        self.assertEqual(zero_env["lean_m_mb"], 0)
        zero_probe_out = io.StringIO()
        with mock.patch("sys.stdout", zero_probe_out), \
             mock.patch.object(alr, "probe_host_envelope", return_value=zero_env):
            self.assertEqual(alr.main(["--probe", "--mode", "build"]), 0)
        self.assertIn("skipping lean -M injection (budget=0)", zero_probe_out.getvalue())
        self.assertNotIn("lean -M 0", zero_probe_out.getvalue())

        zero_run_err = io.StringIO()
        with mock.patch("sys.stderr", zero_run_err), \
             mock.patch.object(alr, "probe_host_envelope", return_value=zero_env):
            self.assertEqual(alr.main(["--mode", "file", "--no-slot-lock", "--", "true"]), 0)
        self.assertIn("LOW_MEMORY_HEADROOM", zero_run_err.getvalue())
        self.assertIn("skipping lean -M injection (budget=0)", zero_run_err.getvalue())
        self.assertNotIn("lean -M 0", zero_run_err.getvalue())

        # 5. CLI shield (_keep_signal_shield=True) leaves signals blocked across
        # normal return so late signals never reach SIG_DFL before sys.exit().
        shield_res = subprocess.run(
            [
                sys.executable,
                "-B",
                "-c",
                (
                    "import importlib.machinery, importlib.util, signal, sys\n"
                    "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
                    "spec = importlib.util.spec_from_loader('alr', loader)\n"
                    "mod = importlib.util.module_from_spec(spec)\n"
                    "loader.exec_module(mod)\n"
                    "signal.signal(signal.SIGTERM, signal.SIG_DFL)\n"
                    "signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGTERM})\n"
                    "rc = mod.main(['--mode', 'file', '--no-slot-lock', '--memory-max-mb', '256', '--', 'true'], _keep_signal_shield=True)\n"
                    "assert rc == 0, rc\n"
                    "cur_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())\n"
                    "assert signal.SIGTERM in cur_mask, cur_mask\n"
                ),
                str(SCRIPT_PATH),
            ],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(shield_res.returncode, 0, shield_res.stderr)

    def test_oversized_digit_guards_headroom_shield_zero_file_and_temp_cleanup(
        self,
    ) -> None:
        """Guards >4300-digit integer inputs, headroom-refusal signal shield,
        zero concurrency file warnings, and slice temp-file cleanup on signal.
        """
        huge_values = ("9" * 5000, "0" * 4400 + "5")

        # 1. Over-4300-digit env/file values never raise ValueError in --probe,
        # --help, concurrency config, or IN_SCOPE pass-through.
        for huge in huge_values:
            with tempfile.TemporaryDirectory(prefix="anneal-huge-int-") as td:
                td_p = Path(td)
                xdg = td_p / "xdg"
                _write_cgroup_file(xdg / "anneal" / "concurrency", f"{huge}\n")
                _seed_workloads_slice_unit(xdg)

                cfg_err = io.StringIO()
                with mock.patch("sys.stderr", cfg_err):
                    self.assertIsNone(
                        alr.read_concurrency_config_file(
                            xdg / "anneal" / "concurrency"
                        )
                    )
                self.assertIn("ignoring invalid", cfg_err.getvalue())

                with mock.patch.dict(
                    os.environ, {"ANNEAL_LEAN_RUN_LEAN_M_MB": huge}
                ):
                    self.assertEqual(
                        alr._env_int("ANNEAL_LEAN_RUN_LEAN_M_MB", 0), 0
                    )

                env_base = _isolated_cli_env(
                    xdg,
                    {
                        "TMPDIR": td,
                        "ANNEAL_WORKTREE_CONCURRENCY": huge,
                        "ANNEAL_LEAN_MEMORY_MAX_MB": huge,
                        "ANNEAL_LEAN_TIMEOUT_SEC": huge,
                        "ANNEAL_LEAN_RUN_LEAN_M_MB": huge,
                    },
                )
                probe_res = subprocess.run(
                    [sys.executable, "-B", str(SCRIPT_PATH), "--probe", "--json"],
                    env=env_base,
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(probe_res.returncode, 0, probe_res.stderr)
                self.assertNotIn("ValueError", probe_res.stderr)
                self.assertIn("WARNING: ignoring invalid", probe_res.stderr)
                self.assertEqual(
                    json.loads(probe_res.stdout)["concurrency"], 1
                )

                help_res = subprocess.run(
                    [sys.executable, "-B", str(SCRIPT_PATH), "--help"],
                    env=env_base,
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(help_res.returncode, 0, help_res.stderr)
                self.assertNotIn("ValueError", help_res.stderr)
                self.assertIn("WARNING: ignoring invalid", help_res.stderr)

                pt_res = subprocess.run(
                    [
                        sys.executable,
                        "-B",
                        str(SCRIPT_PATH),
                        "--",
                        "true",
                    ],
                    env={**env_base, "ANNEAL_LEAN_RUN_IN_SCOPE": "1"},
                    stdin=subprocess.DEVNULL,
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(pt_res.returncode, 0, pt_res.stderr)
                self.assertNotIn("ValueError", pt_res.stderr)

                for flag in ("--concurrency", "--memory-max-mb", "--timeout"):
                    cli_res = subprocess.run(
                        [
                            sys.executable,
                            "-B",
                            str(SCRIPT_PATH),
                            flag,
                            huge,
                            "--",
                            "true",
                        ],
                        env=_isolated_cli_env(xdg, {"TMPDIR": td}),
                        stdin=subprocess.DEVNULL,
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(cli_res.returncode, 2, (flag, cli_res.stderr))
                    self.assertNotIn("ValueError", cli_res.stderr)
                    self.assertNotIn("Traceback", cli_res.stderr)

        # 2. Concurrency file containing '0' emits a deduped out-of-range
        # warning matching ANNEAL_WORKTREE_CONCURRENCY=0.
        with tempfile.TemporaryDirectory(prefix="anneal-conc-zero-") as td:
            xdg = Path(td) / "xdg"
            cpath = xdg / "anneal" / "concurrency"
            _write_cgroup_file(cpath, "0\n")
            zerr = io.StringIO()
            with mock.patch("sys.stderr", zerr):
                self.assertIsNone(alr.read_concurrency_config_file(cpath))
            self.assertIn("ignoring out-of-range", zerr.getvalue())

        # 3. INSUFFICIENT_CGROUP_HEADROOM return keeps signals blocked so a
        # signal delivered during cleanup/finally never leaks _ForwardSignal.
        headroom_sig_res = subprocess.run(
            [
                sys.executable,
                "-B",
                "-c",
                (
                    "import contextlib, importlib.machinery, importlib.util, "
                    "io, os, signal, sys\n"
                    "from unittest import mock\n"
                    "loader = importlib.machinery.SourceFileLoader('alr', sys.argv[1])\n"
                    "spec = importlib.util.spec_from_loader('alr', loader)\n"
                    "mod = importlib.util.module_from_spec(spec)\n"
                    "loader.exec_module(mod)\n"
                    "signal.signal(signal.SIGTERM, signal.SIG_DFL)\n"
                    "signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGTERM})\n"
                    "low = mod.compute_workload_memory_envelope(\n"
                    "    cpu_cores=4, mem_total_mb=4096, mem_avail_mb=2048,\n"
                    "    user_systemd_active=True, t_cg_is_user_service=True,\n"
                    "    cli_concurrency=1, mode='build',\n"
                    ")\n"
                    "@contextlib.contextmanager\n"
                    "def _sig_on_exit(*_a, **_kw):\n"
                    "    try:\n"
                    "        yield None\n"
                    "    finally:\n"
                    "        os.kill(os.getpid(), signal.SIGTERM)\n"
                    "with mock.patch('sys.stderr', io.StringIO()), \\\n"
                    "     mock.patch.object(mod, 'probe_host_envelope', return_value=low), \\\n"
                    "     mock.patch.object(mod, 'ensure_workloads_slice', return_value=(True, False, 'ok')), \\\n"
                    "     mock.patch.object(mod, '_find_systemd_run', return_value='/usr/bin/systemd-run'), \\\n"
                    "     mock.patch.object(mod, 'acquire_build_slot', _sig_on_exit):\n"
                    "    rc = mod.main(['--mode', 'build', '--', 'true'], _keep_signal_shield=True)\n"
                    "assert rc == 137, rc\n"
                ),
                str(SCRIPT_PATH),
            ],
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(headroom_sig_res.returncode, 0, headroom_sig_res.stderr)

        # 4. ensure_workloads_slice unlinks its mkstemp file even when
        # BaseException (_ForwardSignal / KeyboardInterrupt) interrupts staging.
        with tempfile.TemporaryDirectory(prefix="anneal-slice-clean-") as td:
            unit_p = Path(td) / "systemd" / "user" / "anneal-workloads.slice"
            fake_env = {
                "user_systemd_active": True,
                "t_cg_is_user_service": True,
                "w_slice_high_mb": 4096,
                "w_slice_max_mb": 8192,
            }
            with mock.patch.object(
                alr.os,
                "chmod",
                side_effect=alr._ForwardSignal(signal.SIGTERM.value),
            ):
                with self.assertRaises(alr._ForwardSignal):
                    alr.ensure_workloads_slice(
                        fake_env, unit_path=unit_p, reload_systemd=False
                    )
            self.assertEqual(
                list(unit_p.parent.glob(".anneal-workloads.slice.*")), []
            )


class TestCodexP2Regressions(unittest.TestCase):
    """Regression coverage for the three Codex P2 review findings on #4265."""

    def test_watchdog_cadence_gates_50ms_startup_marker_polls(self) -> None:
        """P2 #1: 50 ms scope-entry marker polls must not tick `BuildWatchdog`
        faster than `WATCHDOG_INTERVAL_SEC` (2.0s), nor shorten the 6.0s window
        when the marker appears at 50 ms.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-wd-cadence-") as td:
            anc = Path(td) / "user.slice"
            anc.mkdir()
            # Breach condition active from t=0 (`w=9800 >= 10000 - 1000`).
            _write_cgroup_file(anc / "memory.max", f"{10000 * MIB}\n")
            _write_cgroup_file(
                anc / "memory.stat", f"anon {9800 * MIB}\nshmem 0\nfile 0\n"
            )
            capped_limits = alr.compute_workload_memory_envelope(
                cpu_cores=8,
                mem_total_mb=32768,
                mem_avail_mb=24576,
                ancestors=[
                    {
                        "path": str(anc),
                        "name": "user.slice",
                        "c_high_mb": 10000,
                        "w_mb": 9800,
                        "is_shared_user_slice": False,
                    }
                ],
                user_systemd_active=True,
                systemd_version=260,
                systemd_run_version=260,
                t_cg_is_user_service=False,
                w_cg_path=str(Path(td) / "anneal-workloads.slice"),
                cli_concurrency=1,
                mode="build",
                override_mem_mb=2048,
            )

            # Case 1: 12 consecutive 50 ms marker-poll timeouts (0.60s total)
            # during scope startup under continuous ancestor breach must fire 0
            # watchdog ticks and let the command finish cleanly (rc == 0).
            clock_1 = {"t": 500.0}
            tick_times_1: list[float] = []
            orig_tick = alr.BuildWatchdog.tick

            def spy_tick_1(wd_self: Any, now: float) -> dict[str, Any]:
                tick_times_1.append(round(now - 500.0, 3))
                return orig_tick(wd_self, now)

            class _SlowMarkerProc:
                pid = 2**22 + 12360

                def __init__(self, *_a: Any, **kwargs: Any) -> None:
                    self._polls = 0
                    self._marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )

                def wait(self, timeout: float | None = None) -> int:
                    dt = float(timeout or 0.0)
                    clock_1["t"] += dt
                    self._polls += 1
                    if self._polls <= 12:
                        raise subprocess.TimeoutExpired(
                            cmd=["systemd-run"], timeout=dt
                        )
                    if self._marker:
                        Path(self._marker).write_text("1", encoding="utf-8")
                    return 0

                def poll(self) -> int | None:
                    return 0 if self._polls > 12 else None

            err_1 = io.StringIO()
            with mock.patch("sys.stderr", err_1), \
                 mock.patch.object(alr.time, "monotonic", side_effect=lambda: clock_1["t"]), \
                 mock.patch.object(alr.BuildWatchdog, "tick", spy_tick_1), \
                 mock.patch.object(alr, "_build_scope_launch_cmd", return_value=(["true"], True)), \
                 mock.patch.object(alr.subprocess, "Popen", _SlowMarkerProc), \
                 mock.patch.object(alr, "_kill_systemd_scope"):
                rc_1 = alr.run_bounded_command(
                    ["lake", "build"],
                    capped_limits,
                    use_slot_lock=False,
                    override_mem_mb=2048,
                    probe_fn=lambda **_kw: dict(capped_limits),
                )
            self.assertEqual(rc_1, 0, err_1.getvalue())
            self.assertEqual(tick_times_1, [])

            # Case 2: Marker appears on the initial 50 ms poll, then ancestor
            # breach persists. Ticks must occur at ~2.0s, ~4.0s, and ~6.0s
            # (never at 0.05s or 4.05s).
            clock_2 = {"t": 1000.0}
            tick_times_2: list[float] = []

            def spy_tick_2(wd_self: Any, now: float) -> dict[str, Any]:
                tick_times_2.append(round(now - 1000.0, 3))
                return orig_tick(wd_self, now)

            class _SustainedBreachProc:
                pid = 2**22 + 12361

                def __init__(self, *_a: Any, **kwargs: Any) -> None:
                    self._aborted = False
                    marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")

                def wait(self, timeout: float | None = None) -> int:
                    if self._aborted:
                        return -9
                    dt = float(timeout or 0.0)
                    clock_2["t"] += dt
                    raise subprocess.TimeoutExpired(cmd=["lean"], timeout=dt)

                def poll(self) -> int | None:
                    return -9 if self._aborted else None

            err_2 = io.StringIO()
            with mock.patch("sys.stderr", err_2), \
                 mock.patch.object(alr.time, "monotonic", side_effect=lambda: clock_2["t"]), \
                 mock.patch.object(alr.BuildWatchdog, "tick", spy_tick_2), \
                 mock.patch.object(alr, "_build_scope_launch_cmd", return_value=(["true"], True)), \
                 mock.patch.object(alr.subprocess, "Popen", _SustainedBreachProc), \
                 mock.patch.object(alr, "_kill_systemd_scope"):
                rc_2 = alr.run_bounded_command(
                    ["lake", "build"],
                    capped_limits,
                    use_slot_lock=False,
                    override_mem_mb=2048,
                    probe_fn=lambda **_kw: dict(capped_limits),
                )
            self.assertEqual(rc_2, 137)
            self.assertIn("USER_SLICE_PRESSURE_ABORT:", err_2.getvalue())
            self.assertEqual(tick_times_2, [2.0, 4.0, 6.0])

    def test_unsafe_ignore_cgroup_bypasses_workloads_slice_clamp(self) -> None:
        """P2 #2: `--unsafe-ignore-cgroup --memory-max-mb N` launches the scope
        under `--slice=-.slice` (bypassing `anneal-workloads.slice` clamping),
        skips slice reconciliation and ancestor watchdog abort, and warns when
        `N` exceeds a root-owned ancestor ceiling `C_high`.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-unsafe-slice-") as td:
            user_cg = Path(td) / "user.slice" / "user-1000.slice" / "user@1000.service"
            user_cg.mkdir(parents=True)
            _write_cgroup_file(user_cg / "memory.events", "oom 0\noom_kill 0\n")
            ancestors = [
                {
                    "path": str(Path(td) / "user.slice"),
                    "name": "user.slice",
                    "c_high_mb": 12288,
                    "w_mb": 1024,
                    "is_shared_user_slice": True,
                }
            ]

            def _make_limits(mem_override: int, unsafe: bool) -> dict[str, Any]:
                return alr.compute_workload_memory_envelope(
                    cpu_cores=16,
                    mem_total_mb=65536,
                    mem_avail_mb=49152,
                    ancestors=ancestors,
                    user_systemd_active=True,
                    systemd_version=260,
                    systemd_run_version=260,
                    t_cg_path=str(user_cg),
                    t_cg_is_user_service=True,
                    w_cg_path=str(user_cg / "anneal.slice" / "anneal-workloads.slice"),
                    cli_concurrency=1,
                    mode="build",
                    override_mem_mb=mem_override,
                    unsafe_ignore_cgroup=unsafe,
                )

            safe_limits = _make_limits(10240, unsafe=False)
            unsafe_below_slice = _make_limits(4096, unsafe=True)
            unsafe_within_anc = _make_limits(10240, unsafe=True)
            unsafe_above_anc = _make_limits(16384, unsafe=True)
            self.assertLess(safe_limits["w_slice_max_mb"], 10240)
            self.assertGreater(safe_limits["w_slice_max_mb"], 4096)
            self.assertEqual(
                safe_limits["memory_max_mb"], safe_limits["w_slice_max_mb"]
            )
            self.assertEqual(unsafe_below_slice["memory_max_mb"], 4096)
            self.assertEqual(unsafe_within_anc["memory_max_mb"], 10240)
            self.assertEqual(unsafe_above_anc["memory_max_mb"], 16384)

            captured_cmds: list[list[str]] = []

            class _CaptureProc:
                pid = 2**22 + 12362

                def __init__(self, argv: list[str], **kwargs: Any) -> None:
                    captured_cmds.append([str(a) for a in argv])
                    marker = (kwargs.get("env") or {}).get(
                        "ANNEAL_LEAN_RUN_SCOPE_MARKER"
                    )
                    if marker:
                        Path(marker).write_text("1", encoding="utf-8")

                def wait(self, timeout: float | None = None) -> int:
                    return 0

                def poll(self) -> int:
                    return 0

            # 1. Without `--unsafe-ignore-cgroup`, uses the workload slice and
            # reconciles `anneal-workloads.slice`.
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=safe_limits), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")) as mock_ensure_safe, \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _CaptureProc):
                rc_safe = alr.main(
                    ["--mode", "build", "--no-slot-lock", "--memory-max-mb", "10240", "--", "true"]
                )
            self.assertEqual(rc_safe, 0)
            self.assertEqual(mock_ensure_safe.call_count, 1)
            self.assertIn("--slice=anneal-workloads.slice", captured_cmds[-1])
            self.assertIn(
                f"MemoryMax={safe_limits['w_slice_max_mb']}M", captured_cmds[-1]
            )

            # 2. `--unsafe-ignore-cgroup` with `N <= w_slice_max_mb` stays in
            # `anneal-workloads.slice` rather than needlessly escaping it.
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=unsafe_below_slice), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")) as mock_ensure_below, \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _CaptureProc):
                rc_below = alr.main(
                    [
                        "--mode",
                        "build",
                        "--no-slot-lock",
                        "--unsafe-ignore-cgroup",
                        "--memory-max-mb",
                        "4096",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc_below, 0)
            self.assertEqual(mock_ensure_below.call_count, 1)
            self.assertIn("--slice=anneal-workloads.slice", captured_cmds[-1])
            self.assertIn("MemoryMax=4096M", captured_cmds[-1])

            # 3. `--unsafe-ignore-cgroup --memory-max-mb 10240` (`> slice`,
            # `<= C_high=12288`) uses `--slice=-.slice`, skips slice updates,
            # and emits no ancestor-ceiling warning.
            err_within = io.StringIO()
            with mock.patch("sys.stderr", err_within), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=unsafe_within_anc), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")) as mock_ensure_unsafe, \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _CaptureProc):
                rc_within = alr.main(
                    [
                        "--mode",
                        "build",
                        "--no-slot-lock",
                        "--unsafe-ignore-cgroup",
                        "--memory-max-mb",
                        "10240",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc_within, 0)
            self.assertEqual(mock_ensure_unsafe.call_count, 0)
            self.assertIn("--slice=-.slice", captured_cmds[-1])
            self.assertNotIn("--slice=anneal-workloads.slice", captured_cmds[-1])
            self.assertIn("MemoryMax=10240M", captured_cmds[-1])
            self.assertEqual(err_within.getvalue(), "")

            # 4. With `--unsafe-ignore-cgroup --memory-max-mb 16384`
            # (`> C_high=12288`), bypasses the slice and warns about `C_high`.
            err_above = io.StringIO()
            with mock.patch("sys.stderr", err_above), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=unsafe_above_anc), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr.subprocess, "Popen", _CaptureProc):
                rc_above = alr.main(
                    [
                        "--mode",
                        "build",
                        "--no-slot-lock",
                        "--unsafe-ignore-cgroup",
                        "--memory-max-mb",
                        "16384",
                        "--",
                        "true",
                    ]
                )
            self.assertEqual(rc_above, 0)
            self.assertIn("--slice=-.slice", captured_cmds[-1])
            self.assertIn("MemoryMax=16384M", captured_cmds[-1])
            self.assertIn("C_high=12288M", err_above.getvalue())

        if _can_launch_live_systemd_scope():
            live_info = alr.probe_host_envelope(is_probe=True, mode="file")
            above_slice_mb = int(live_info["w_slice_max_mb"]) + 64
            res = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPT_PATH),
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--unsafe-ignore-cgroup",
                    "--memory-max-mb",
                    str(above_slice_mb),
                    "--",
                    "cat",
                    "/proc/self/cgroup",
                ],
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                timeout=15.0,
            )
            self.assertEqual(res.returncode, 0, res.stderr)
            self.assertNotIn("anneal-workloads.slice", res.stdout)
            self.assertIn(f"user@{os.getuid()}.service/anneal-run-", res.stdout)

    def test_slice_unit_uses_manager_unit_path_despite_client_xdg_override(
        self,
    ) -> None:
        """P2 #3: `ensure_workloads_slice` resolves the running `systemd --user`
        manager's `UnitPath` directory rather than assuming the invoking shell's
        `XDG_CONFIG_HOME`, including paths with spaces.
        """
        rt = Path("/run/user/1000")
        self.assertEqual(
            alr._parse_systemd_user_unit_dir(
                "/home/alice/.config/systemd/user.control "
                "/run/user/1000/systemd/user.control "
                "/run/user/1000/systemd/transient "
                "/run/user/1000/systemd/generator.early "
                "/home/alice/.config/systemd/user "
                "/etc/systemd/user /run/user/1000/systemd/user",
                runtime_base=rt,
            ),
            Path("/home/alice/.config/systemd/user"),
        )
        self.assertEqual(
            alr._parse_systemd_user_unit_dir(
                "/home/jane doe/.config/systemd/user.control "
                "/run/user/1000/systemd/user.control "
                "/home/jane doe/.config/systemd/user "
                "/etc/systemd/user",
                runtime_base=rt,
            ),
            Path("/home/jane doe/.config/systemd/user"),
        )
        self.assertEqual(
            alr._parse_systemd_user_unit_dir(
                "/opt/mgr-xdg/systemd/user /etc/systemd/user /usr/lib/systemd/user",
                runtime_base=rt,
            ),
            Path("/opt/mgr-xdg/systemd/user"),
        )
        self.assertEqual(
            alr._parse_systemd_user_unit_dir(
                "/etc/systemd/user /run/user/1000/systemd/user /usr/lib/systemd/user",
                runtime_base=rt,
            ),
            Path("/run/user/1000/systemd/user"),
        )
        self.assertIsNone(
            alr._parse_systemd_user_unit_dir(
                "/home/alice/../evil/systemd/user /etc/systemd/user",
                runtime_base=rt,
            )
        )

        # End-to-end mocked socket with mismatched client XDG_CONFIG_HOME.
        with tempfile.TemporaryDirectory(prefix="anneal-mgr-unitpath-") as td:
            td_p = Path(td)
            mgr_cfg_dir = td_p / "mgr config" / "systemd" / "user"
            client_xdg_dir = td_p / "client_xdg"
            _write_cgroup_file(client_xdg_dir / "anneal" / "concurrency", "2\n")
            fake_rt = td_p / "run_user"
            fake_rt.mkdir()

            def fake_run(argv: list[str], *_a: Any, **_kw: Any) -> Any:
                cmd_s = [str(x) for x in argv]
                if cmd_s[1:] == ["--user", "show", "-p", "UnitPath", "--value"]:
                    return subprocess.CompletedProcess(
                        argv,
                        0,
                        f"{mgr_cfg_dir}.control {fake_rt}/systemd/user.control "
                        f"{mgr_cfg_dir} /etc/systemd/user\n",
                        "",
                    )
                if "daemon-reload" in cmd_s:
                    return subprocess.CompletedProcess(argv, 0, "", "")
                raise AssertionError(f"unexpected subprocess.run: {cmd_s}")

            env_info = {
                "user_systemd_active": True,
                "t_cg_is_user_service": True,
                "w_slice_high_mb": 7500,
                "w_slice_max_mb": 8000,
                "runtime_base": str(fake_rt),
            }
            with mock.patch.dict(
                os.environ, {"XDG_CONFIG_HOME": str(client_xdg_dir)}
            ), mock.patch.object(
                alr, "_has_user_systemd_sock", return_value=True
            ), mock.patch.object(
                alr, "_find_systemctl", return_value="/usr/bin/systemctl"
            ), mock.patch.object(
                alr.subprocess, "run", side_effect=fake_run
            ):
                self.assertEqual(alr.read_concurrency_config_file(), 2)
                ok, changed, _ = alr.ensure_workloads_slice(env_info)
            self.assertTrue(ok)
            self.assertTrue(changed)
            expected_unit = mgr_cfg_dir / "anneal-workloads.slice"
            self.assertTrue(expected_unit.is_file())
            self.assertIn(
                "MemoryMax=8000M", expected_unit.read_text(encoding="utf-8")
            )
            self.assertFalse(
                (
                    client_xdg_dir / "systemd" / "user" / "anneal-workloads.slice"
                ).exists()
            )


if __name__ == "__main__":
    unittest.main()
