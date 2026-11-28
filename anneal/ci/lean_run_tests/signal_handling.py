# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` signal-handling tests, mixed into
`TestWatchdogSignalsAndCpuLimits`.
"""

from __future__ import annotations

from .support import (
    _can_launch_live_systemd_scope,
    _isolated_cli_env,
    _seed_workloads_slice_unit,
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


class SignalHandlingTests:
    """Tests of child exit signals, wrapper signal forwarding, inherited
    ignored signals, and signals during launch and cleanup, run as part of
    `TestWatchdogSignalsAndCpuLimits`.
    """

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
