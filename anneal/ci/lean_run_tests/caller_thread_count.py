# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for caller-lowered thread counts."""

from __future__ import annotations

from .support import (
    alr,
    Any,
    contextlib,
    FAKE_CGROUP_INFO,
    io,
    json,
    mock,
    os,
    Path,
    re,
    setUpModule,
    subprocess,
    tearDownModule,
    unittest,
)


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
