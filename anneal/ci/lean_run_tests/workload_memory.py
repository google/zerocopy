# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for the workload memory envelope."""

from __future__ import annotations

from .support import (
    _isolated_cli_env,
    _write_cgroup_file,
    _write_synthetic_cgroup_root,
    _write_synthetic_host_base,
    alr,
    fcntl,
    io,
    mock,
    os,
    Path,
    SCRIPT_PATH,
    setUpModule,
    subprocess,
    SYNTHETIC_HOST_CORES,
    SYNTHETIC_HOSTS,
    sys,
    tearDownModule,
    tempfile,
    unittest,
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
            # Stub the `systemctl` lookup too, so the test does not depend
            # on the host (e.g. a sandboxed CI image without systemd).
            with mock.patch.object(alr.subprocess, "run") as mock_run, \
                 mock.patch.object(alr, "_find_systemctl", return_value="/usr/bin/systemctl"):
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
