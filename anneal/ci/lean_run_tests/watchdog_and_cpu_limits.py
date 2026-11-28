# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for the watchdog, signal handling, and CPU limits."""

from __future__ import annotations

from .signal_handling import SignalHandlingTests
from .support import (
    _isolated_cli_env,
    _seed_workloads_slice_unit,
    _write_cgroup_file,
    _write_synthetic_host_base,
    alr,
    Any,
    io,
    json,
    mock,
    os,
    Path,
    SCRIPT_PATH,
    setUpModule,
    signal,
    subprocess,
    sys,
    tearDownModule,
    tempfile,
    unittest,
)


class TestWatchdogSignalsAndCpuLimits(SignalHandlingTests, unittest.TestCase):
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
