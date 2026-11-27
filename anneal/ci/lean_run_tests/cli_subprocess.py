# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lean-run` tests for the command-line interface run as a
subprocess.
"""

from __future__ import annotations

from .support import (
    _AMBIENT_ANNEAL_ENV_PREFIXES,
    _can_launch_live_systemd_scope,
    _FakePopen,
    _file_identity,
    _isolated_cli_env,
    _seed_workloads_slice_unit,
    _SYNTHETIC_HOST_CLI_SHIM,
    _write_cgroup_file,
    _write_synthetic_cgroup_root,
    _write_synthetic_host_base,
    alr,
    Any,
    FIXED_HW,
    io,
    json,
    mock,
    os,
    Path,
    re,
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


class TestCliSubprocess(unittest.TestCase):
    """Runs `anneal/ci/anneal-lean-run` as a real subprocess
    (`stdin=/dev/null`).

    Every subprocess is isolated from the invoking host: ambient `ANNEAL_LEAN_*`
    / `ANNEAL_WORKTREE_*` variables are scrubbed, and `XDG_CONFIG_HOME` is a
    fresh empty directory unless `env_extra` provides one.
    """

    def _run_isolated(
        self, argv: list[str], env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="anneal-cli-xdg-") as xdg_dir:
            return subprocess.run(
                argv,
                stdin=subprocess.DEVNULL,
                capture_output=True,
                text=True,
                check=False,
                env=_isolated_cli_env(Path(xdg_dir), env_extra),
                timeout=120,
            )

    def _cli(
        self, *args: str, env_extra: dict[str, str] | None = None
    ) -> subprocess.CompletedProcess[str]:
        return self._run_isolated([sys.executable, str(SCRIPT_PATH), *args], env_extra)

    def _synthetic_cli(
        self,
        host_root: Path,
        cgroup_name: str,
        *args: str,
        env_extra: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        """`_cli` against synthetic host `host_root` / `cgroup_name` (same
        isolation).
        """
        return self._run_isolated(
            [
                sys.executable,
                "-B",
                "-c",
                _SYNTHETIC_HOST_CLI_SHIM,
                str(SCRIPT_PATH),
                str(host_root),
                cgroup_name,
                *args,
            ],
            env_extra,
        )

    def _probe_json(self, res: subprocess.CompletedProcess[str]) -> dict[str, Any]:
        self.assertEqual(res.returncode, 0, res.stderr)
        data = json.loads(res.stdout)
        self.assertIsInstance(data, dict)
        return data

    def _assert_concurrency(self, data: dict[str, Any], expected: int) -> None:
        for key in ("concurrency", "w_eff", "build_slots"):
            self.assertEqual(data[key], expected, key)

    @staticmethod
    def _host_bounded(requested: int, data: dict[str, Any]) -> int:
        """Concurrency the probed host grants for `requested`: cgroup-capped
        hosts clamp it to `s_heavy_safe`, uncapped hosts honor it.
        """
        if data["is_cg_capped"]:
            return min(requested, data["s_heavy_safe"])
        return requested

    def test_cli_probe_and_execution(self) -> None:
        if os.access(SCRIPT_PATH, os.X_OK):
            direct = self._run_isolated([str(SCRIPT_PATH), "--print-limits", "--json"])
            self.assertIn("cgroup_avail_mib", self._probe_json(direct))

        probe = self._cli("--probe")
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertIn("Cgroup v2", probe.stdout)

        # An isolated probe sees no host override at all: neither ambient
        # `ANNEAL_*` variables nor
        # `{$XDG_CONFIG_HOME,~/.config}/anneal/concurrency`.
        default = self._probe_json(self._cli("--probe", "--json"))
        if default["user_systemd_active"] and alr._find_systemd_run() is not None:
            self.assertIn("Hard RAM Cap", probe.stdout)
        else:
            self.assertNotIn("Hard RAM Cap", probe.stdout)
            self.assertIn("none (no systemd scope", probe.stdout)
        self._assert_concurrency(default, 1)
        self.assertEqual(default["mode"], "build")
        self.assertEqual(default["timeout_sec"], 900)

        data = self._probe_json(
            self._cli(
                "--probe",
                "--json",
                env_extra={
                    "ANNEAL_WORKTREE_CONCURRENCY": "2",
                    "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                    "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                },
            )
        )
        self._assert_concurrency(data, self._host_bounded(2, data))
        expected_mem = (
            min(3000, data["w_slice_max_mb"]) if data["is_cg_capped"] else 3000
        )
        self.assertEqual(data["memory_max_mb"], expected_mem)
        if data["w_slice_max_mb"] >= 3000:
            self.assertEqual(data["memory_max_mb"], 3000)
        self.assertEqual(data["timeout_sec"], 77)

        # `--unsafe-ignore-cgroup` only lifts the `w_slice_max_mb` clamp on an
        # explicit `--memory-max-mb`.  It neither flips `is_cg_capped` nor
        # un-clamps concurrency, so the sibling probe reports
        # `is_cg_capped is False` / `concurrency == 2` exactly on uncapped
        # hosts and stays clamped to `s_heavy_safe` on capped ones.
        unsafe = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertIs(unsafe["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe, self._host_bounded(2, unsafe))

        over_cap_mb = data["w_slice_max_mb"] + 1024
        capped_data = self._probe_json(
            self._cli(
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(
            capped_data["memory_max_mb"],
            min(over_cap_mb, capped_data["w_slice_max_mb"])
            if capped_data["is_cg_capped"]
            else over_cap_mb,
        )
        self._assert_concurrency(capped_data, self._host_bounded(2, capped_data))

        unsafe_data = self._probe_json(
            self._cli(
                "--unsafe-ignore-cgroup",
                "--memory-max-mb",
                str(over_cap_mb),
                "--probe",
                "--json",
                env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
            )
        )
        self.assertEqual(unsafe_data["memory_max_mb"], over_cap_mb)
        self.assertIs(unsafe_data["is_cg_capped"], data["is_cg_capped"])
        self._assert_concurrency(unsafe_data, self._host_bounded(2, unsafe_data))

        # A populated `$XDG_CONFIG_HOME/anneal/concurrency` is read, and is
        # subject to the same host bound with or without
        # `--unsafe-ignore-cgroup`.
        with tempfile.TemporaryDirectory(prefix="anneal-xdg-cfg-") as cfg_dir:
            _write_cgroup_file(Path(cfg_dir) / "anneal" / "concurrency", "3\n")
            for flags in ((), ("--unsafe-ignore-cgroup",)):
                cfg_data = self._probe_json(
                    self._cli(
                        *flags,
                        "--probe",
                        "--json",
                        env_extra={"XDG_CONFIG_HOME": cfg_dir},
                    )
                )
                self._assert_concurrency(cfg_data, self._host_bounded(3, cfg_data))

        bad_env = self._probe_json(
            self._cli(
                "--probe", "--json", env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "abc"}
            )
        )
        self._assert_concurrency(bad_env, 1)

        flag_data = self._probe_json(
            self._cli(
                "--concurrency", "1", "--memory-max-mb", "2500", "--timeout", "60",
                "--probe", "--json",
            )
        )
        self._assert_concurrency(flag_data, 1)
        self.assertEqual(
            flag_data["memory_max_mb"],
            min(2500, flag_data["w_slice_max_mb"])
            if flag_data["is_cg_capped"]
            else 2500,
        )
        self.assertEqual(flag_data["timeout_sec"], 60)

        # Command-executing runs reconcile `anneal-workloads.slice` under
        # `XDG_CONFIG_HOME`. Give them a seeded one and check they leave it
        # untouched: no rewrite, hence no `systemctl --user daemon-reload` of
        # the host's live user manager.
        with tempfile.TemporaryDirectory(prefix="anneal-cli-run-xdg-") as run_xdg:
            unit = _seed_workloads_slice_unit(Path(run_xdg))
            before = None if unit is None else _file_identity(unit)
            run_cases = [
                (
                    [
                        "--mode",
                        "file",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ],
                    0,
                ),
                (
                    [
                        "--no-slot-lock",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "sh",
                        "-c",
                        "exit 5",
                    ],
                    5,
                ),
                (
                    [
                        "--mode",
                        "build",
                        "--no-slot-lock",
                        "--concurrency",
                        "1",
                        "--memory-max-mb",
                        "512",
                        "--",
                        "true",
                    ],
                    0,
                ),
            ]
            for argv, expected_rc in run_cases:
                res = self._cli(*argv, env_extra={"XDG_CONFIG_HOME": run_xdg})
                self.assertEqual(res.returncode, expected_rc, (argv, res.stderr))
            if unit is not None:
                self.assertEqual(_file_identity(unit), before)

        usage = self._cli()
        self.assertEqual(usage.returncode, 2)

    def test_cli_synthetic_hosts_cover_uncapped_and_capped_regimes(self) -> None:
        """Both cgroup regimes through the real CLI, whichever host runs the
        tests.
        """
        # host -> concurrency granted for a requested 2 (environment /
        # `--concurrency`) and for a requested 3
        # (`$XDG_CONFIG_HOME/anneal/concurrency`).
        granted = {"cg_uncapped": (2, 3), "cg_capped_1": (1, 1), "cg_capped_2": (2, 2)}
        with tempfile.TemporaryDirectory(prefix="anneal-synth-host-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            xdg_three = root / "xdg_three"
            _write_cgroup_file(xdg_three / "anneal" / "concurrency", "3\n")
            for cg_name, ceiling_mib, capped, s_heavy_safe in SYNTHETIC_HOSTS:
                _write_synthetic_cgroup_root(root, cg_name, ceiling_mib)
                conc_for_2, conc_for_3 = granted[cg_name]

                def probe(
                    *args: str,
                    env_extra: dict[str, str] | None = None,
                    cg_name: str = cg_name,
                ) -> dict[str, Any]:
                    return self._probe_json(
                        self._synthetic_cli(
                            root, cg_name, *args, "--probe", "--json", env_extra=env_extra
                        )
                    )

                with self.subTest(host=cg_name):
                    default = probe()
                    self.assertIs(default["is_cg_capped"], capped)
                    self.assertEqual(default["s_heavy_safe"], s_heavy_safe)
                    self.assertEqual(default["cpu_cores"], SYNTHETIC_HOST_CORES)
                    self.assertEqual(default["mem_total_mb"], 65536)
                    self._assert_concurrency(default, 1)
                    self.assertEqual(default["timeout_sec"], 900)
                    w_slice_max_mb = default["w_slice_max_mb"]
                    self.assertGreater(w_slice_max_mb, 3000)

                    overridden = probe(
                        env_extra={
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                            "ANNEAL_LEAN_MEMORY_MAX_MB": "3000",
                            "ANNEAL_LEAN_TIMEOUT_SEC": "77",
                        }
                    )
                    self._assert_concurrency(overridden, conc_for_2)
                    self.assertEqual(overridden["memory_max_mb"], 3000)
                    self.assertEqual(overridden["timeout_sec"], 77)

                    unsafe = probe(
                        "--unsafe-ignore-cgroup",
                        env_extra={"ANNEAL_WORKTREE_CONCURRENCY": "2"},
                    )
                    self.assertIs(unsafe["is_cg_capped"], capped)
                    self._assert_concurrency(unsafe, conc_for_2)

                    self._assert_concurrency(probe("--concurrency", "2"), conc_for_2)

                    for flags in ((), ("--unsafe-ignore-cgroup",)):
                        from_file = probe(
                            *flags, env_extra={"XDG_CONFIG_HOME": str(xdg_three)}
                        )
                        self.assertIs(from_file["is_cg_capped"], capped)
                        self._assert_concurrency(from_file, conc_for_3)

                    # Host concurrency file acts as the floor for env
                    # concurrency, while explicit `--concurrency` during
                    # `--probe` overrides `w_eff` yet leaves `build_slots`
                    # pinned to the host file value.
                    file_plus_env = probe(
                        env_extra={
                            "XDG_CONFIG_HOME": str(xdg_three),
                            "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        }
                    )
                    self._assert_concurrency(file_plus_env, conc_for_3)
                    file_plus_cli = probe(
                        "--concurrency",
                        "1",
                        env_extra={"XDG_CONFIG_HOME": str(xdg_three)},
                    )
                    self.assertEqual(file_plus_cli["concurrency"], 1)
                    self.assertEqual(file_plus_cli["w_eff"], 1)
                    self.assertEqual(file_plus_cli["build_slots"], conc_for_3)

                    over_cap_mb = w_slice_max_mb + 1024
                    for clamp_args, clamp_env in (
                        (("--memory-max-mb", str(over_cap_mb)), None),
                        ((), {"ANNEAL_LEAN_MEMORY_MAX_MB": str(over_cap_mb)}),
                    ):
                        clamped = probe(*clamp_args, env_extra=clamp_env)
                        expected_clamped = w_slice_max_mb if capped else over_cap_mb
                        self.assertEqual(clamped["memory_max_mb"], expected_clamped)
                        self.assertEqual(
                            clamped["lean_m_mb"], (75 * expected_clamped) // 100
                        )
                        lifted = probe(
                            "--unsafe-ignore-cgroup", *clamp_args, env_extra=clamp_env
                        )
                        self.assertEqual(lifted["memory_max_mb"], over_cap_mb)
                        self.assertEqual(lifted["lean_m_mb"], (75 * over_cap_mb) // 100)
                        self.assertIs(lifted["is_cg_capped"], capped)
                        self._assert_concurrency(lifted, 1)

    def test_scrubbed_prefixes_cover_every_anneal_variable_of_the_script(self) -> None:
        """An `ANNEAL_*` variable added to `anneal/ci/anneal-lean-run` must be
        scrubbed too.
        """
        names = set(
            re.findall(r"ANNEAL_[A-Z0-9_]+", SCRIPT_PATH.read_text(encoding="utf-8"))
        )
        for known in (
            "ANNEAL_WORKTREE_CONCURRENCY",
            "ANNEAL_LEAN_MEMORY_MAX_MB",
            "ANNEAL_LEAN_TIMEOUT_SEC",
            "ANNEAL_LEAN_RUN_IN_SCOPE",
            "ANNEAL_LEAN_RUN_SCOPE_MARKER",
        ):
            self.assertIn(known, names)
        self.assertEqual(
            sorted(n for n in names if not n.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)),
            [],
        )

    def test_cli_isolation_scrubs_poisoned_ambient_environment(self) -> None:
        """Neither ambient `ANNEAL_*` overrides nor host concurrency files reach
        `_cli`.

        Runs on an uncapped synthetic host, where a leaked concurrency override
        would be honored verbatim instead of being hidden by a capped host's
        `s_heavy_safe == 1` clamp.
        """
        ambient_overrides = {
            "ANNEAL_WORKTREE_CONCURRENCY": "6",
            "ANNEAL_LEAN_MEMORY_MAX_MB": "17",
            "ANNEAL_LEAN_TIMEOUT_SEC": "55",
        }
        with tempfile.TemporaryDirectory(prefix="anneal-ambient-") as tmp:
            root = Path(tmp)
            _write_synthetic_host_base(root)
            _write_synthetic_cgroup_root(root, "cg_uncapped", None)
            poisoned_xdg = root / "poisoned_xdg"
            _write_cgroup_file(poisoned_xdg / "anneal" / "concurrency", "7\n")
            poisoned_home = root / "poisoned_home"
            _write_cgroup_file(
                poisoned_home / ".config" / "anneal" / "concurrency", "5\n"
            )
            poison = {
                **ambient_overrides,
                "HOME": str(poisoned_home),
                "XDG_CONFIG_HOME": str(poisoned_xdg),
                "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
            }

            def synthetic(env_extra: dict[str, str] | None = None) -> dict[str, Any]:
                return self._probe_json(
                    self._synthetic_cli(
                        root, "cg_uncapped", "--probe", "--json", env_extra=env_extra
                    )
                )

            clean = synthetic()
            self.assertIs(clean["is_cg_capped"], False)
            self._assert_concurrency(clean, 1)
            self.assertEqual(clean["timeout_sec"], 900)
            clean_file = self._probe_json(
                self._synthetic_cli(
                    root, "cg_uncapped", "--mode", "file", "--probe", "--json"
                )
            )
            self.assertGreater(clean_file["lean_m_mb"], 99)
            live_clean = self._probe_json(self._cli("--probe", "--json"))
            child_env_cmd = [
                sys.executable,
                "-c",
                "import json, os; print(json.dumps({"
                "k: os.environ.get(k) for k in ("
                "'ANNEAL_LEAN_RUN_LEAN_M_MB', 'ANNEAL_WORKTREE_CONCURRENCY'"
                ")}))",
            ]

            with mock.patch.dict(os.environ, poison):
                fresh_xdg = root / "fresh_xdg"
                env = _isolated_cli_env(fresh_xdg)
                self.assertEqual(
                    [k for k in env if k.startswith(_AMBIENT_ANNEAL_ENV_PREFIXES)], []
                )
                self.assertEqual(env["XDG_CONFIG_HOME"], str(fresh_xdg))
                # `env_extra` is applied after the scrub, so explicit overrides
                # survive it.
                explicit = _isolated_cli_env(
                    fresh_xdg,
                    {
                        "ANNEAL_WORKTREE_CONCURRENCY": "2",
                        "XDG_CONFIG_HOME": str(poisoned_xdg),
                    },
                )
                self.assertEqual(explicit["ANNEAL_WORKTREE_CONCURRENCY"], "2")
                self.assertEqual(explicit["XDG_CONFIG_HOME"], str(poisoned_xdg))
                self.assertNotIn("ANNEAL_LEAN_MEMORY_MAX_MB", explicit)
                self.assertNotIn("ANNEAL_LEAN_TIMEOUT_SEC", explicit)

                isolated = synthetic()
                isolated_exec = self._synthetic_cli(
                    root,
                    "cg_uncapped",
                    "--mode",
                    "file",
                    "--no-slot-lock",
                    "--",
                    *child_env_cmd,
                )
                live = self._probe_json(self._cli("--probe", "--json"))
                direct = (
                    self._probe_json(
                        self._run_isolated(
                            [str(SCRIPT_PATH), "--print-limits", "--json"]
                        )
                    )
                    if os.access(SCRIPT_PATH, os.X_OK)
                    else None
                )

            # The synthetic host is deterministic: a poisoned parent changes
            # nothing.
            self.assertEqual(isolated, clean)
            self.assertEqual(isolated_exec.returncode, 0, isolated_exec.stderr)
            self.assertEqual(
                json.loads(isolated_exec.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": str(clean_file["lean_m_mb"]),
                    "ANNEAL_WORKTREE_CONCURRENCY": None,
                },
            )
            for live_data in (live, direct):
                if live_data is not None:
                    self._assert_concurrency(live_data, 1)
                    self.assertEqual(live_data["timeout_sec"], 900)
                    if live_clean["memory_max_mb"] != 17:
                        self.assertNotEqual(live_data["memory_max_mb"], 17)

            # Positive controls: each poison is honored once passed explicitly,
            # so the equality above is not vacuous.
            leaked_env = synthetic(env_extra=ambient_overrides)
            self._assert_concurrency(leaked_env, 6)
            self.assertEqual(leaked_env["memory_max_mb"], 17)
            self.assertEqual(leaked_env["timeout_sec"], 55)
            leaked_xdg = synthetic(env_extra={"XDG_CONFIG_HOME": str(poisoned_xdg)})
            self._assert_concurrency(leaked_xdg, 7)
            # `XDG_CONFIG_HOME=""` falls back to `$HOME/.config`, which the
            # isolated non-empty `XDG_CONFIG_HOME` of `_cli` therefore masks.
            leaked_home = synthetic(
                env_extra={"HOME": str(poisoned_home), "XDG_CONFIG_HOME": ""}
            )
            self._assert_concurrency(leaked_home, 5)
            leaked_passthrough = self._synthetic_cli(
                root,
                "cg_uncapped",
                "--mode",
                "file",
                "--no-slot-lock",
                "--",
                *child_env_cmd,
                env_extra={
                    "ANNEAL_LEAN_RUN_IN_SCOPE": "1",
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_WORKTREE_CONCURRENCY": "4",
                },
            )
            self.assertEqual(leaked_passthrough.returncode, 0, leaked_passthrough.stderr)
            self.assertEqual(
                json.loads(leaked_passthrough.stdout),
                {
                    "ANNEAL_LEAN_RUN_LEAN_M_MB": "99",
                    "ANNEAL_WORKTREE_CONCURRENCY": "4",
                },
            )

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
