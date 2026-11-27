# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for regressions found in review."""

from __future__ import annotations

from .support import (
    _can_launch_live_systemd_scope,
    _write_cgroup_file,
    alr,
    Any,
    io,
    MIB,
    mock,
    os,
    Path,
    SCRIPT_PATH,
    setUpModule,
    subprocess,
    sys,
    tearDownModule,
    tempfile,
    unittest,
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
