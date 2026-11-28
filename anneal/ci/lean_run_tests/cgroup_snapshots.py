# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for the cgroup snapshots taken on timeouts and
OOM kills, and for probe headroom reporting.
"""

from __future__ import annotations

from .support import (
    _can_launch_live_systemd_scope,
    _write_cgroup_file,
    alr,
    Any,
    FAKE_CGROUP_INFO,
    io,
    json,
    MIB,
    mock,
    Path,
    re,
    subprocess,
    sys,
    tempfile,
)


class CgroupSnapshotCases:
    """`TestCliAndLimits` methods for timeout and OOM cgroup snapshots and
    probe headroom.
    """

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
