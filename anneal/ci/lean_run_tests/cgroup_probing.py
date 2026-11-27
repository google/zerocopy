# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for cgroup v2 discovery and `memory.stat` parsing."""

from __future__ import annotations

from .support import (
    _write_cgroup_file,
    alr,
    MIB,
    mock,
    Path,
    setUpModule,
    tearDownModule,
    tempfile,
    unittest,
)


# ---------------------------------------------------------------------------
# Cgroup v2 probing
# ---------------------------------------------------------------------------


class TestCgroupV2Probing(unittest.TestCase):
    """Tests cgroup v2 discovery, `memory.stat` parsing, and `anon + shmem`
    budgeting.
    """

    def test_parse_proc_cgroup_v2_variants(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "cgroup"

            # Standard systemd unified cgroup v2 path
            p.write_text(
                "0::/user.slice/user-1000.slice/session-1.scope\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p),
                "/user.slice/user-1000.slice/session-1.scope",
            )

            # Hybrid v1 + v2 hierarchy with (deleted) suffix
            p.write_text(
                "12:pids:/user.slice\n0::/app.slice/worker.scope (deleted)\n",
                encoding="utf-8",
            )
            self.assertEqual(
                alr.parse_proc_cgroup_v2(p), "/app.slice/worker.scope"
            )

            # Colons inside the path survive (`0::` is split only once)
            p.write_text("0::/app.slice/a:b.scope\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/app.slice/a:b.scope")

            # Root unified hierarchy inside container namespace
            p.write_text("0::/\n", encoding="utf-8")
            self.assertEqual(alr.parse_proc_cgroup_v2(p), "/")

            # Cgroup v1 only (no 0:: line), including a named v1 hierarchy
            p.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n1:name=systemd:/x\n",
                encoding="utf-8",
            )
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))

            # Empty file and non-existent file
            p.write_text("", encoding="utf-8")
            self.assertIsNone(alr.parse_proc_cgroup_v2(p))
            self.assertIsNone(alr.parse_proc_cgroup_v2(Path(tmp) / "missing"))

    def test_parse_memory_stat(self) -> None:
        raw = (
            "anon 2147483648\n"
            "file 30064771072\n"
            "shmem 536870912\n"
            "inactive_file 25769803776\n"
            "active_file 4294967296\n"
            "malformed_line_without_val\n"
            "bad_int not_a_number\n"
            "neg_val -100\n"
        )
        stats = alr.parse_memory_stat(raw)
        self.assertEqual(stats["anon"], 2147483648)
        self.assertEqual(stats["file"], 30064771072)
        self.assertEqual(stats["shmem"], 536870912)
        self.assertEqual(stats["inactive_file"], 25769803776)
        self.assertEqual(stats["active_file"], 4294967296)
        self.assertNotIn("bad_int", stats)
        self.assertNotIn("neg_val", stats)
        self.assertNotIn("malformed_line_without_val", stats)

        with tempfile.TemporaryDirectory() as tmp:
            stat_file = Path(tmp) / "memory.stat"
            stat_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(stat_file), stats)
            self.assertEqual(alr.parse_memory_stat(str(stat_file)), stats)
            self.assertEqual(alr.parse_memory_stat(Path(tmp) / "missing"), {})

        with tempfile.TemporaryDirectory(prefix="anneal space $dir-") as tmp_sp:
            sp_file = Path(tmp_sp) / "memory.stat"
            sp_file.write_text(raw, encoding="utf-8")
            self.assertEqual(alr.parse_memory_stat(str(sp_file)), stats)

    def test_reclaimable_file_cache_does_not_throttle_available_memory(
        self,
    ) -> None:
        """32 GiB cgroup with 28 GiB `.olean` file cache and 2 GiB `anon +
        shmem` must report 30 GiB available (`32 - 2`), NOT 2 GiB (`32 - 30`).
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            # Notice: root cgroup does NOT have memory.stat (standard systemd
            # host)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {1536 * MIB}\n"
                f"shmem {512 * MIB}\n"
                f"file {28672 * MIB}\n"
                f"inactive_file {24576 * MIB}\n"
                f"active_file {4096 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            cores, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(cg["cgroup_path"], "/user.slice/anneal.scope")
            self.assertEqual(cg["cgroup_anon_mib"], 1536)
            self.assertEqual(cg["cgroup_shmem_mib"], 512)
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 2048)
            self.assertEqual(cg["cgroup_file_cache_mib"], 28672)
            self.assertEqual(cg["cgroup_current_mib"], 30720)
            self.assertEqual(cg["cgroup_memory_max_mib"], 32768)
            # Headroom MUST be 32768 - 2048 = 30720 MiB (not 32768 - 30720 =
            # 2048 MiB), while raw `/proc/meminfo` fields stay un-clamped
            # (`65536` / `48000`) for `c_high_mb`.
            self.assertEqual(cg["cgroup_avail_mib"], 30720)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 48000)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertTrue(limits["is_cg_capped"])
            self.assertGreater(limits["w_slice_max_mb"], 24576)
            self.assertEqual(limits["cgroup_avail_mib"], 30720)
            self.assertEqual(limits["cgroup_memory_max_mib"], 32768)
            # Reclaimable `.olean` file cache (28 GiB) must NOT throttle a build
            # down to 2048 MiB.
            self.assertGreater(limits["memory_max_mb"], 14000)
            self.assertGreater(cores, 0)

    def test_high_anon_shmem_throttles_available_memory(self) -> None:
        """32 GiB cgroup with 28 GiB `anon + shmem` and 2 GiB `file` cache
        must drop `cgroup_avail_mib` to 4 GiB (`4096 MiB`) and throttle
        `memory_max_mb`.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "anneal.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.max").write_text(
                f"{32768 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.current").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {28000 * MIB}\n"
                f"shmem {672 * MIB}\n"
                f"file {2048 * MIB}\n",
                encoding="utf-8",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/anneal.scope\n", encoding="utf-8"
            )
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   49152000 kB\n",
                encoding="utf-8",
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 28672)
            self.assertEqual(cg["cgroup_avail_mib"], 4096)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 48000)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertTrue(limits["is_cg_capped"])
            self.assertLessEqual(limits["memory_max_mb"], 4096)
            # File cache must stay un-penalized while 28 GiB anon+shmem
            # throttles build budget
            (leaf / "memory.stat").write_text(
                f"anon {2048 * MIB}\nshmem 0\nfile {2048 * MIB}\n",
                encoding="utf-8",
            )
            limits_reclaimable = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            self.assertLess(limits["memory_max_mb"], limits_reclaimable["memory_max_mb"])

    def test_cgroup_avail_exhausted_floors_mem_avail_at_512(self) -> None:
        """`anon + shmem` above `memory.max` clamps headroom to 0 and
        `mem_avail_mb` to 512.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{4096 * MIB}\n")
            _write_cgroup_file(leaf / "memory.current", f"{4200 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {4000 * MIB}\nshmem {200 * MIB}\nfile 0\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       67108864 kB\nMemAvailable:   50331648 kB\n",
                encoding="utf-8",
            )
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertEqual(cg["cgroup_avail_mib"], 0)
            self.assertEqual(cg["cgroup_memory_max_mib"], 4096)
            self.assertEqual(total_mb, 65536)
            self.assertEqual(avail_mb, 49152)
            build = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            # Fail-closed admission: exhausted 4 GiB cgroup must NOT unsafely
            # clamp up to >= 2048 MiB.
            self.assertLess(build["memory_max_mb"], 2048)
            file_limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="file",
                runtime_base=Path(tmp),
            )
            self.assertLessEqual(file_limits["memory_max_mb"], 1024)

    def test_ancestor_hierarchy_walk_and_root_container_cgroup(self) -> None:
        """Leaf has `memory.max = max`, parent and grandparent have finite
        limits.
        """
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            user_slice = cg_root / "user.slice"
            svc = user_slice / "agent-host.service"
            leaf = svc / "server"
            leaf.mkdir(parents=True)

            # Root: 30 GiB max, 5 GiB anon+shmem -> 25 GiB avail
            (cg_root / "memory.max").write_text(
                f"{30720 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"anon {5120 * MIB}\nshmem 0\nfile {10240 * MIB}\n",
                encoding="utf-8",
            )

            # user.slice: 24 GiB max, 10 GiB anon+shmem -> 14 GiB avail
            # (tightest avail)
            (user_slice / "memory.max").write_text(
                f"{24576 * MIB}\n", encoding="utf-8"
            )
            (user_slice / "memory.stat").write_text(
                f"anon {9216 * MIB}\nshmem {1024 * MIB}\nfile {8192 * MIB}\n",
                encoding="utf-8",
            )

            # svc: 20 GiB max (tightest max), 3 GiB anon+shmem -> 17 GiB avail
            (svc / "memory.max").write_text(
                f"{20480 * MIB}\n", encoding="utf-8"
            )
            (svc / "memory.stat").write_text(
                f"anon {3072 * MIB}\nshmem 0\nfile {6144 * MIB}\n",
                encoding="utf-8",
            )

            # leaf: unbounded max, 1 GiB anon+shmem
            (leaf / "memory.max").write_text("max\n", encoding="utf-8")
            (leaf / "memory.current").write_text(
                f"{4096 * MIB}\n", encoding="utf-8"
            )
            (leaf / "memory.stat").write_text(
                f"anon {900 * MIB}\nshmem {124 * MIB}\nfile {3072 * MIB}\n",
                encoding="utf-8",
            )

            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text(
                "0::/user.slice/agent-host.service/server\n", encoding="utf-8"
            )

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(
                cg["cgroup_path"], "/user.slice/agent-host.service/server"
            )
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_file_cache_mib"], 3072)
            self.assertEqual(cg["cgroup_current_mib"], 4096)
            self.assertEqual(cg["cgroup_memory_max_mib"], 20480)
            self.assertEqual(cg["cgroup_avail_mib"], 14336)

            # Also test 0::/ container root mapping
            proc_cg_root = Path(tmp) / "proc_cgroup_root"
            proc_cg_root.write_text("0::/\n", encoding="utf-8")
            cg_at_root = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg_root
            )
            self.assertTrue(cg_at_root["cgroup_v2"])
            self.assertEqual(cg_at_root["cgroup_path"], "/")
            self.assertEqual(cg_at_root["cgroup_memory_max_mib"], 30720)
            self.assertEqual(cg_at_root["cgroup_avail_mib"], 25600)

    def test_unbounded_hierarchy_keeps_host_ram_and_reports_unbounded(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "user.slice" / "a.scope"
            _write_cgroup_file(cg_root / "user.slice" / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{3000 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {700 * MIB}\nshmem {100 * MIB}\nfile {2000 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/user.slice/a.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            _, total_mb, avail_mb = alr._read_raw_meminfo_and_cpus(
                meminfo, cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertIsNone(cg["cgroup_memory_max_mib"])
            self.assertIsNone(cg["cgroup_avail_mib"])
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 800)
            self.assertEqual(total_mb, 16384)
            self.assertEqual(avail_mb, 12288)

            limits = alr.probe_host_envelope(
                meminfo_path=meminfo,
                cgroup_root=cg_root,
                proc_cgroup_path=proc_cg,
                user_systemd_active=False,
                cli_concurrency=1,
                mode="build",
                runtime_base=Path(tmp),
            )
            line = alr.format_cgroup_probe_line(limits)
            self.assertIn("Cgroup v2 Envelope", line)
            self.assertIn("regime=uncapped", line)
            self.assertIn("W_slice_max=", line)

            bounded = dict(
                limits,
                is_cg_capped=True,
                c_high_mb=4096,
                a_lim_path="/sys/fs/cgroup/user.slice",
                w_slice_max_mb=3072,
                w_slice_high_mb=2764,
                w_live_mb=2500,
            )
            bounded_line = alr.format_cgroup_probe_line(bounded)
            self.assertIn("regime=capped", bounded_line)
            self.assertIn("C_high=4096 MiB (/sys/fs/cgroup/user.slice)", bounded_line)
            unavailable = alr.format_cgroup_probe_line(alr._empty_cgroup_info())
            self.assertIn("unavailable", unavailable)

    def test_ancestor_without_memory_stat_falls_back_to_current(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            parent = cg_root / "svc.slice"
            leaf = parent / "job.scope"
            # Parent: finite max, `memory.current` but no `memory.stat`.
            _write_cgroup_file(parent / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(parent / "memory.current", f"{6144 * MIB}\n")
            _write_cgroup_file(leaf / "memory.max", "max\n")
            _write_cgroup_file(leaf / "memory.current", f"{5120 * MIB}\n")
            _write_cgroup_file(
                leaf / "memory.stat",
                f"anon {1024 * MIB}\nshmem 0\nfile {4096 * MIB}\n",
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/svc.slice/job.scope\n", encoding="utf-8")
            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            self.assertEqual(cg["cgroup_anon_shmem_mib"], 1024)
            self.assertEqual(cg["cgroup_memory_max_mib"], 8192)
            # 8192 - memory.current (6144) = 2048
            self.assertEqual(cg["cgroup_avail_mib"], 2048)

    def test_missing_memory_stat_fallback_and_non_v2_fallback(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            # Ancestor with memory.max and memory.current + inactive_file only
            cg_root = Path(tmp) / "cgroup"
            cg_root.mkdir()
            (cg_root / "memory.max").write_text(
                f"{16384 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.current").write_text(
                f"{10240 * MIB}\n", encoding="utf-8"
            )
            (cg_root / "memory.stat").write_text(
                f"inactive_file {6144 * MIB}\n", encoding="utf-8"
            )
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/\n", encoding="utf-8")

            cg = alr.probe_cgroup_v2_memory(
                cgroup_root=cg_root, proc_cgroup_path=proc_cg
            )
            self.assertTrue(cg["cgroup_v2"])
            # used = current (10240) - inactive_file (6144) = 4096 -> avail =
            # 16384 - 4096 = 12288
            self.assertEqual(cg["cgroup_avail_mib"], 12288)

            # Missing cgroup_root entirely -> graceful fallback
            cg_none = alr.probe_cgroup_v2_memory(
                cgroup_root=Path(tmp) / "nonexistent",
                proc_cgroup_path=proc_cg,
            )
            self.assertEqual(cg_none, alr._empty_cgroup_info())

    def test_cgroup_v1_only_and_escaping_paths_fall_back(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            _write_cgroup_file(cg_root / "memory.stat", f"anon {MIB}\n")
            _write_cgroup_file(cg_root / "memory.max", f"{1024 * MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"

            # cgroup v1-only host: no `0::` line even though files exist.
            proc_cg.write_text(
                "11:memory:/user.slice\n10:cpu:/user.slice\n", encoding="utf-8"
            )
            self.assertEqual(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                ),
                alr._empty_cgroup_info(),
            )

            # A path escaping the namespace root must never be followed.
            proc_cg.write_text("0::/../../escape.scope\n", encoding="utf-8")
            self.assertFalse(
                alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )["cgroup_v2"]
            )

    def test_probe_never_raises(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            cg_root = Path(tmp) / "cgroup"
            leaf = cg_root / "job.scope"
            _write_cgroup_file(leaf / "memory.max", f"{8192 * MIB}\n")
            _write_cgroup_file(leaf / "memory.stat", f"anon {MIB}\n")
            proc_cg = Path(tmp) / "proc_cgroup"
            proc_cg.write_text("0::/job.scope\n", encoding="utf-8")
            meminfo = Path(tmp) / "meminfo"
            meminfo.write_text(
                "MemTotal:       16777216 kB\nMemAvailable:   12582912 kB\n",
                encoding="utf-8",
            )

            with mock.patch.object(
                alr, "parse_memory_stat", side_effect=RuntimeError("boom")
            ):
                cg = alr.probe_cgroup_v2_memory(
                    cgroup_root=cg_root, proc_cgroup_path=proc_cg
                )
            self.assertEqual(cg, alr._empty_cgroup_info())

            with mock.patch.object(
                alr,
                "_probe_cgroup_v2_memory_impl",
                side_effect=PermissionError("EACCES"),
            ):
                env_err = alr.probe_host_envelope(
                    meminfo_path=meminfo,
                    cgroup_root=cg_root,
                    proc_cgroup_path=proc_cg,
                    user_systemd_active=False,
                    cli_concurrency=1,
                    mode="build",
                    runtime_base=Path(tmp),
                )
                self.assertFalse(env_err["cgroup_v2"])
                self.assertEqual(env_err["mem_total_mb"], 16384)
                self.assertEqual(env_err["mem_avail_mb"], 12288)
                self.assertEqual(alr.format_cgroup_diagnostic_snapshot(), "")
