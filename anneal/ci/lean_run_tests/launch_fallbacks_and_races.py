# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` launch-fallback and race tests, mixed into
`TestSecurityHardeningAndSystemdVersions`.
"""

from __future__ import annotations

from .support import (
    _FakePopen,
    alr,
    Any,
    io,
    mock,
    os,
    Path,
    SCRIPT_PATH,
    signal,
    subprocess,
    sys,
    tempfile,
)


class LaunchFallbacksAndRacesTests:
    """Tests of `systemd-run` launch fallback, a deleted mid-run marker,
    and `killpg`, `wait`, and early-signal races, run as part of
    `TestSecurityHardeningAndSystemdVersions`.
    """

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
