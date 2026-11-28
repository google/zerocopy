# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for the thread and memory budgets that the
command-line interface exports to its child.
"""

from __future__ import annotations

from .support import (
    _can_launch_live_systemd_scope,
    _FakePopen,
    _write_synthetic_cgroup_root,
    _write_synthetic_host_base,
    alr,
    FIXED_HW,
    io,
    json,
    mock,
    os,
    Path,
    sys,
    tempfile,
)


class CliBudgetEnvCases:
    """`TestCliSubprocess` methods for the exported thread and memory
    budgets."""

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
