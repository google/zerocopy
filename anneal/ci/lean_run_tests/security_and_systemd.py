# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for security hardening and systemd version
handling.
"""

from __future__ import annotations

from .launch_fallbacks_and_races import LaunchFallbacksAndRacesTests
from .support import (
    _can_launch_live_systemd_scope,
    _FakePopen,
    _write_cgroup_file,
    alr,
    Any,
    fcntl,
    io,
    json,
    mock,
    os,
    Path,
    setUpModule,
    subprocess,
    sys,
    tearDownModule,
    tempfile,
    unittest,
)


class TestSecurityHardeningAndSystemdVersions(LaunchFallbacksAndRacesTests, unittest.TestCase):
    """Tests slot-lock symlink/permission hardening, systemd version gating, and
    fallbacks.
    """

    def test_slot_lock_rejects_symlinks_without_truncating_target(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-sym-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            victim = rt / "victim.txt"
            victim.write_text("DO NOT TRUNCATE OR OVERWRITE THIS FILE\n", encoding="utf-8")
            os.symlink(victim, slot_dir / "slot-1.lock")

            for excl in (False, True):
                with self.assertRaises(PermissionError):
                    with alr.acquire_build_slot(
                        2, 1.0, enabled=True, exclusive=excl, runtime_base=rt
                    ):
                        pass
            self.assertEqual(
                victim.read_text(encoding="utf-8"),
                "DO NOT TRUNCATE OR OVERWRITE THIS FILE\n",
            )

            # Symlinked slot directory itself must be rejected too.
            rt2 = Path(td) / "rt2"
            rt2.mkdir()
            target_dir = rt / "real_slots"
            target_dir.mkdir()
            os.symlink(target_dir, rt2 / f"anneal-build-slots-{os.getuid()}")
            with self.assertRaises(PermissionError):
                with alr.acquire_build_slot(1, 1.0, enabled=True, runtime_base=rt2):
                    pass

    def test_slot_lock_fails_immediately_on_permission_or_wrong_owner_and_exits_126(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-perm-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            # Wrong-owner directory must fail immediately without waiting for
            # slot timeout.
            wrong_uid = os.getuid() + 1000
            fake_stat = os.stat_result((0o40700, 1, 1, 2, wrong_uid, 0, 0, 0, 0, 0))
            with mock.patch.object(alr.os, "lstat", return_value=fake_stat):
                with self.assertRaises(PermissionError):
                    with alr.acquire_build_slot(
                        2, 1200.0, enabled=True, exclusive=False, runtime_base=rt
                    ):
                        pass

            # Unwritable/inaccessible directory fails fast with PermissionError
            # -> exit 126.
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=16384,
                mem_avail_mb=12288,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=str(rt),
            )
            err_buf = io.StringIO()
            with mock.patch("sys.stderr", err_buf), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits), \
                 mock.patch.object(alr.os, "access", return_value=False):
                rc = alr.main(["--mode", "build", "--", "true"])
            self.assertEqual(rc, 126)
            self.assertNotIn("BUILD_SLOT_TIMEOUT", err_buf.getvalue())

            # FIFO and symlinks inside slot_dir never block
            # count_active_build_slots.
            os.mkfifo(slot_dir / "slot-1.lock")
            os.symlink(rt / "nonexistent", slot_dir / "slot-2.lock")
            self.assertEqual(alr.count_active_build_slots(rt), 0)

    def test_slot_lock_rejects_hardlinks_loose_modes_bad_types_and_missing_home(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-hard-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)

            # 1. Hardlinked lock file (`st_nlink > 1`) is rejected without
            # truncating victim.
            victim = rt / "hard_victim.txt"
            victim.write_text("KEEP HARDLINK VICTIM INTACT\n", encoding="utf-8")
            os.link(victim, slot_dir / "slot-1.lock")
            with self.assertRaisesRegex(PermissionError, "hardlinked"):
                with alr.acquire_build_slot(1, 0.2, enabled=True, runtime_base=rt):
                    pass
            self.assertEqual(victim.read_text(encoding="utf-8"), "KEEP HARDLINK VICTIM INTACT\n")
            (slot_dir / "slot-1.lock").unlink()

            # 2. Pre-existing loose-mode lock file (`0644`) is rejected, never
            # fchmod-repaired.
            loose_lock = slot_dir / "slot-1.lock"
            loose_lock.write_text("PRESERVE", encoding="utf-8")
            loose_lock.chmod(0o644)
            with self.assertRaisesRegex(PermissionError, "Unsafe permissions"):
                with alr.acquire_build_slot(1, 0.2, enabled=True, runtime_base=rt):
                    pass
            self.assertEqual(loose_lock.stat().st_mode & 0o777, 0o644)
            self.assertEqual(loose_lock.read_text(encoding="utf-8"), "PRESERVE")
            loose_lock.unlink()

            # 3. Directory at lock path exits 126 cleanly (never exit 1).
            (slot_dir / "slot-1.lock").mkdir(mode=0o700)
            limits = alr.compute_workload_memory_envelope(
                cpu_cores=4,
                mem_total_mb=16384,
                mem_avail_mb=12288,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=str(rt),
            )
            err_dir = io.StringIO()
            with mock.patch("sys.stderr", err_dir), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)
            (slot_dir / "slot-1.lock").rmdir()

            # 4. Loose-mode pre-existing slot_dir (`0770`) is rejected
            # fail-closed (not repaired).
            rt_loose = Path(td) / "rt_loose"
            rt_loose.mkdir()
            bad_slot_dir = rt_loose / f"anneal-build-slots-{os.getuid()}"
            bad_slot_dir.mkdir(mode=0o770)
            bad_slot_dir.chmod(0o770)
            loose_limits = dict(limits, runtime_base=str(rt_loose))
            err_loose = io.StringIO()
            with mock.patch("sys.stderr", err_loose), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=loose_limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)
            self.assertEqual(bad_slot_dir.stat().st_mode & 0o777, 0o770)

            # 5. Missing base dir exits 126 consistently (never 127
            # command-not-found).
            missing_limits = dict(limits, runtime_base=str(Path(td) / "no_such_base"))
            err_miss = io.StringIO()
            with mock.patch("sys.stderr", err_miss), \
                 mock.patch.object(alr, "probe_host_envelope", return_value=missing_limits):
                self.assertEqual(alr.main(["--mode", "build", "--", "true"]), 126)

        # 6. `Path.home()` raising RuntimeError never produces an uncaught
        # traceback.
        with mock.patch.dict(os.environ, {"XDG_CONFIG_HOME": ""}, clear=False), \
             mock.patch.object(alr.Path, "home", side_effect=RuntimeError("no passwd")):
            self.assertIsNone(alr.read_concurrency_config_file())
            ok, changed, msg = alr.ensure_workloads_slice(
                {"user_systemd_active": True, "t_cg_is_user_service": True, "w_slice_high_mb": 1024, "w_slice_max_mb": 2048}
            )
            self.assertFalse(ok)
            self.assertFalse(changed)
            self.assertIn("cannot resolve", msg)

    def test_non_exclusive_slot_contention_and_timeout(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-slot-cont-") as td:
            rt = Path(td)
            slot_dir = rt / f"anneal-build-slots-{os.getuid()}"
            slot_dir.mkdir(mode=0o700)
            fd1 = alr._open_private_lock_file(slot_dir / "slot-1.lock", os.getuid())
            fcntl.flock(fd1, fcntl.LOCK_EX | fcntl.LOCK_NB)
            try:
                with alr.acquire_build_slot(
                    2, 0.2, enabled=True, exclusive=False, runtime_base=rt
                ) as slot_idx:
                    self.assertEqual(slot_idx, 2)
                fd2 = alr._open_private_lock_file(slot_dir / "slot-2.lock", os.getuid())
                fcntl.flock(fd2, fcntl.LOCK_EX | fcntl.LOCK_NB)
                try:
                    cont_err = io.StringIO()
                    with mock.patch("sys.stderr", cont_err):
                        with self.assertRaisesRegex(TimeoutError, "BUILD_SLOT_TIMEOUT"):
                            with alr.acquire_build_slot(
                                2, 0.08, enabled=True, exclusive=False, runtime_base=rt, poll_interval=0.02
                            ):
                                pass
                    self.assertIn("All 2 host build slot(s) busy", cont_err.getvalue())
                finally:
                    fcntl.flock(fd2, fcntl.LOCK_UN)
                    os.close(fd2)
            finally:
                fcntl.flock(fd1, fcntl.LOCK_UN)
                os.close(fd1)

    def test_systemd_version_parsing_oom_policy_and_expand_environment(self) -> None:
        cases = (
            ("249.11-0ubuntu3.12", 249, 249, False, False),
            ("252.26-1~deb12u2", 252, 252, False, False),
            ("253", 253, 253, True, False),
            ("v254.0", 254, 254, True, True),
            # Skew: manager 257 with client 260 passes --expand-environment=no.
            ("257.9", 257, 260, True, True),
            # Reverse skew: client 252 omits both OOMPolicy=kill and no-expand.
            ("260.1\n", 260, 252, False, False),
            # Old manager 252 with client 260 omits OOMPolicy=kill, keeps
            # no-expand.
            ("252.9", 252, 260, False, True),
            ("systemd 260 (260.1-1)\n+PAM", 260, 260, True, True),
        )
        with mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"):
            for raw, mgr_ver, client_ver, want_oom_pol, want_no_expand in cases:
                self.assertEqual(alr._parse_systemd_major_version(raw), mgr_ver, raw)
                argv, in_scope = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-ver.scope",
                    systemd_version=mgr_ver,
                    systemd_run_version=client_ver,
                )
                self.assertTrue(in_scope)
                self.assertEqual("OOMPolicy=kill" in argv, want_oom_pol, raw)
                self.assertEqual("--expand-environment=no" in argv, want_no_expand, raw)

        # Unknown client version inspects `systemd-run --help` for
        # `--expand-environment` instead of silently dropping it.
        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=True
        ), mock.patch("sys.stderr", io.StringIO()) as unk_err:
            argv_unk_help, _ = alr._build_scope_launch_cmd(
                ["echo", "$HOME"],
                b_max_mb=4096,
                threads=2,
                timeout_sec=30,
                user_systemd_active=True,
                unit_name="anneal-unk.scope",
                systemd_version=260,
                systemd_run_version=None,
            )
            self.assertIn("--expand-environment=no", argv_unk_help)
            self.assertNotIn("OOMPolicy=kill", argv_unk_help)
            self.assertIn("WARNING:", unk_err.getvalue())

        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=False
        ), mock.patch("sys.stderr", io.StringIO()) as no_help_err:
            argv_no_help, _ = alr._build_scope_launch_cmd(
                ["echo", "$HOME"],
                b_max_mb=4096,
                threads=2,
                timeout_sec=30,
                user_systemd_active=True,
                unit_name="anneal-nohelp.scope",
                systemd_version=260,
                systemd_run_version=None,
            )
            self.assertNotIn("--expand-environment=no", argv_no_help)
            self.assertIn("WARNING:", no_help_err.getvalue())

        # Both --version and --help failing passes --expand-environment=no when
        # user manager >= 254 and omits it when < 254, always warning clearly.
        with mock.patch.object(
            alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"
        ), mock.patch.object(
            alr, "detect_systemd_run_client_version", return_value=None
        ), mock.patch.object(
            alr, "_systemd_run_supports_expand_environment", return_value=None
        ):
            with mock.patch("sys.stderr", io.StringIO()) as err_260:
                argv_both_260, _ = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-both260.scope",
                    systemd_version=260,
                    systemd_run_version=None,
                )
            self.assertIn("--expand-environment=no", argv_both_260)
            self.assertIn("WARNING:", err_260.getvalue())

            with mock.patch("sys.stderr", io.StringIO()) as err_252:
                argv_both_252, _ = alr._build_scope_launch_cmd(
                    ["echo", "$HOME"],
                    b_max_mb=4096,
                    threads=2,
                    timeout_sec=30,
                    user_systemd_active=True,
                    unit_name="anneal-both252.scope",
                    systemd_version=252,
                    systemd_run_version=None,
                )
            self.assertNotIn("--expand-environment=no", argv_both_252)
            self.assertIn("WARNING:", err_252.getvalue())

        # Within a single invocation, `systemd-run --version` and `--help` are
        # each probed at most once across probe, reprobe, and launch.
        with tempfile.TemporaryDirectory(prefix="anneal-cache-srun-") as td:
            cg = Path(td) / "cg"
            uid = os.getuid()
            user_cg = cg / "user.slice" / f"user-{uid}.slice" / f"user@{uid}.service"
            _write_cgroup_file(user_cg / "cgroup.controllers", "memory cpu\n")
            _write_cgroup_file(user_cg / "cgroup.subtree_control", "memory cpu\n")
            _write_cgroup_file(user_cg / "memory.max", "max\n")
            _write_cgroup_file(user_cg / "memory.stat", "anon 0\nshmem 0\nfile 0\n")
            seen_srun: list[list[str]] = []

            def fake_subproc_run(argv: list[str], **_kw: Any) -> subprocess.CompletedProcess[str]:
                seen_srun.append(list(argv))
                if "show" in argv:
                    return subprocess.CompletedProcess(argv, 0, "260\n", "")
                if "--version" in argv or "--help" in argv:
                    return subprocess.CompletedProcess(argv, 1, "", "probe failed")
                return subprocess.CompletedProcess(argv, 0, "", "")

            _FakePopen.calls = []
            with mock.patch("sys.stderr", io.StringIO()), \
                 mock.patch.object(alr, "_find_systemctl", return_value="/usr/bin/systemctl"), \
                 mock.patch.object(alr, "_find_systemd_run", return_value="/usr/bin/systemd-run"), \
                 mock.patch.object(alr, "ensure_workloads_slice", return_value=(True, False, "ok")), \
                 mock.patch.object(alr, "resolve_runtime_base", return_value=(Path(td), True)), \
                 mock.patch.object(
                     alr,
                     "probe_host_envelope",
                     wraps=lambda **kw: alr.compute_workload_memory_envelope(
                         cpu_cores=8,
                         mem_total_mb=32768,
                         mem_avail_mb=24576,
                         user_systemd_active=True,
                         systemd_version=alr.detect_user_systemd_version(Path(td)),
                         systemd_run_version=alr.detect_systemd_run_client_version("/usr/bin/systemd-run"),
                         t_cg_is_user_service=True,
                         cli_concurrency=1,
                         mode=kw.get("mode", "file"),
                         override_mem_mb=kw.get("override_mem_mb"),
                     ),
                 ), \
                 mock.patch.object(alr.subprocess, "run", side_effect=fake_subproc_run), \
                 mock.patch.object(alr.subprocess, "Popen", _FakePopen):
                rc_cache = alr.main(["--mode", "file", "--no-slot-lock", "--", "true"])
            self.assertEqual(rc_cache, 0)
            ver_calls = [a for a in seen_srun if "--version" in a]
            help_calls = [a for a in seen_srun if "--help" in a]
            show_calls = [a for a in seen_srun if "show" in a]
            self.assertEqual(len(ver_calls), 1, ver_calls)
            self.assertEqual(len(help_calls), 1, help_calls)
            self.assertEqual(len(show_calls), 1, show_calls)

        # Client detection helper queries `systemd-run --version` directly.
        with mock.patch.object(
            alr.subprocess,
            "run",
            return_value=subprocess.CompletedProcess(
                ["systemd-run", "--version"], 0, "systemd 260 (260.1-1)\n+PAM\n", ""
            ),
        ):
            self.assertEqual(alr.detect_systemd_run_client_version("/usr/bin/systemd-run"), 260)

        for bad in ("", "   ", "custom-version"):
            self.assertIsNone(alr._parse_systemd_major_version(bad), bad)

        # If systemd-run client >= 254 is active live, verify special $-args
        # arrive verbatim.
        if (
            _can_launch_live_systemd_scope()
            and (alr.detect_systemd_run_client_version() or 0) >= 254
        ):
            with tempfile.TemporaryDirectory(prefix="anneal-argv-lit-") as td:
                out_f = Path(td) / "argv.json"
                probe_args = [
                    "lit$$pid",
                    "${HOME}",
                    "$HOME",
                    "x=${ANNEAL_TEST_UNSET_VAR}y",
                    "$f.lean",
                ]
                rc = alr.main(
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--memory-max-mb",
                        "512",
                        "--",
                        sys.executable,
                        "-c",
                        "import json, pathlib, sys; "
                        "pathlib.Path(sys.argv[1]).write_text(json.dumps(sys.argv[2:]))",
                        str(out_f),
                        *probe_args,
                    ]
                )
                self.assertEqual(rc, 0)
                self.assertEqual(json.loads(out_f.read_text(encoding="utf-8")), probe_args)

    def test_probe_user_systemd_retries_and_warns_on_show_timeout_or_failure(
        self,
    ) -> None:
        """Timeout or nonzero `systemctl --user show` warns instead of silent
        fail-open.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-sd-probe-") as td:
            cg = Path(td) / "cg"
            uid = os.getuid()
            user_cg = cg / "user.slice" / f"user-{uid}.slice" / f"user@{uid}.service"
            _write_cgroup_file(user_cg / "cgroup.controllers", "memory cpu\n")
            _write_cgroup_file(user_cg / "cgroup.subtree_control", "memory cpu\n")
            calls = 0

            def timeout_run(*_a: Any, **_kw: Any) -> Any:
                nonlocal calls
                calls += 1
                raise subprocess.TimeoutExpired(cmd=["systemctl"], timeout=2.0)

            err_to = io.StringIO()
            with mock.patch("sys.stderr", err_to), mock.patch.object(
                alr, "_find_systemctl", return_value="/usr/bin/systemctl"
            ), mock.patch.object(alr.subprocess, "run", side_effect=timeout_run):
                active, ver = alr._probe_user_systemd(
                    runtime_base=Path(td),
                    user_systemd_sock_alive=True,
                    cgroup_root=cg,
                    uid=uid,
                )
            self.assertFalse(active)
            self.assertIsNone(ver)
            self.assertEqual(calls, 2)
            self.assertIn("WARNING:", err_to.getvalue())

            # Non-zero exit also emits explicit warning.
            err_fail = io.StringIO()
            with mock.patch("sys.stderr", err_fail), mock.patch.object(
                alr, "_find_systemctl", return_value="/usr/bin/systemctl"
            ), mock.patch.object(
                alr.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    ["systemctl"], 1, "", "Failed to connect"
                ),
            ):
                active2, ver2 = alr._probe_user_systemd(
                    runtime_base=Path(td),
                    user_systemd_sock_alive=True,
                    cgroup_root=cg,
                    uid=uid,
                )
            self.assertFalse(active2)
            self.assertIsNone(ver2)
            self.assertIn("WARNING:", err_fail.getvalue())

    def test_acquire_build_slot_propagates_caller_blocking_io_error(self) -> None:
        """`except BlockingIOError:` only wraps flock, never the caller's yield.
        """
        with tempfile.TemporaryDirectory(prefix="anneal-slot-bio-") as td:
            rt = Path(td)
            with self.assertRaisesRegex(BlockingIOError, "caller-blocking"):
                with alr.acquire_build_slot(
                    2, 1.0, enabled=True, exclusive=False, runtime_base=rt
                ) as slot_idx:
                    self.assertEqual(slot_idx, 1)
                    raise BlockingIOError("caller-blocking")
            # Slot 1 must be cleanly unlocked and re-acquirable.
            with alr.acquire_build_slot(
                1, 0.5, enabled=True, exclusive=False, runtime_base=rt
            ) as slot_idx:
                self.assertEqual(slot_idx, 1)
