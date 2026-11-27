# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for cross-platform and non-systemd fallbacks."""

from __future__ import annotations

from .support import (
    _FakePopen,
    _write_cgroup_file,
    alr,
    Any,
    io,
    MIB,
    mock,
    os,
    Path,
    setUpModule,
    subprocess,
    tearDownModule,
    tempfile,
    unittest,
)


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
