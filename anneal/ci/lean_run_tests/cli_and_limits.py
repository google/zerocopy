# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for mode detection, limit flags, `--probe`, and
execution.
"""

from __future__ import annotations

from . import support
from .support import (
    _can_launch_live_systemd_scope,
    _EXEC_GUARDS,
    _FakePopen,
    _file_identity,
    _GUARDED_EXEC_FUNCTIONS,
    _write_cgroup_file,
    alr,
    Any,
    FAKE_CGROUP_INFO,
    FIXED_HW,
    io,
    json,
    MIB,
    mock,
    os,
    Path,
    re,
    setUpModule,
    subprocess,
    sys,
    tearDownModule,
    tempfile,
    unittest,
)


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
        if support._SLICE_UNIT_SEED is None:
            self.skipTest("no delegated systemd --user: the slice unit is never reconciled")
        unit = alr._workloads_slice_unit_path()
        assert unit is not None
        assert support._MGR_UNIT_TMPDIR is not None
        assert support._XDG_TMPDIR is not None
        self.assertEqual(unit.parents[2], Path(support._MGR_UNIT_TMPDIR.name))
        self.assertNotEqual(unit.parents[2], Path(support._XDG_TMPDIR.name))
        before = _file_identity(unit)
        self.assertEqual(before[2], support._SLICE_UNIT_SEED)

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
            self.assertEqual(written.read_text(encoding="utf-8"), support._SLICE_UNIT_SEED)
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
