# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`ci-core` workflow, TCB dominance, sandbox, cache, and runner invariants."""

from .support import (
    os,
    Path,
    re,
    REPO_ROOT,
    subprocess,
    tempfile,
)


class CiCoreWorkflowCases:
    """`ci-core` workflow tests of `CiWorkflowManifestGuardTests`."""

    def test_active_ci_core_workflows_and_tcb_dominance(self):
        for retired in ("anneal.yml", "anneal-current.yml", "ci.yml"):
            self.assertFalse(
                (REPO_ROOT / ".github/workflows" / retired).exists(),
                f"legacy workflow {retired} must be retired after cutover",
            )

        repo_cfg = self.checks_cfg["repo"]
        trusted_shas = set(repo_cfg["trusted_engine_shas"])
        self.assertTrue(trusted_shas)
        for sha in trusted_shas:
            self.assertRegex(sha, r"^[0-9a-f]{40}$")

        trusted_engine_wf = repo_cfg["trusted_engine_workflow"]
        self.assertTrue(trusted_engine_wf.endswith("/.github/workflows/ci.yml"))
        pr_engine_wf = trusted_engine_wf[: -len("ci.yml")] + "ci-pr.yml"

        for wf, expected_workflow in (
            (self.pr_wf, pr_engine_wf),
            (self.trusted_wf, trusted_engine_wf),
        ):
            self.assertEqual(wf.get("permissions"), {})
            job = wf["jobs"]["ci-core"]
            self.assertEqual(job["with"]["config_path"], "ci/checks.toml")
            uses_wf, sep, uses_sha = job["uses"].partition("@")
            self.assertEqual(sep, "@")
            self.assertEqual(uses_wf, expected_workflow)
            self.assertIn(uses_sha, trusted_shas)

        self.assertEqual(
            self.pr_wf["jobs"]["ci-core"]["with"].get("shadow_mode", "false"),
            "false",
        )
        self.assertNotIn("shadow_mode", self.trusted_wf["jobs"]["ci-core"]["with"])

        self.assertEqual(
            self.pr_wf["jobs"]["ci-core"]["permissions"],
            {
                "actions": "read",
                "contents": "read",
                "packages": "read",
                "pull-requests": "read",
            },
        )
        self.assertEqual(
            self.trusted_wf["jobs"]["ci-core"]["permissions"],
            {
                "actions": "read",
                "contents": "read",
                "id-token": "write",
                "packages": "write",
                "pull-requests": "read",
            },
        )

        tcb_cfg = self.checks_cfg["tcb"]
        self.assertIs(tcb_cfg["allow_owner_self_approval"], True)
        # Every root workflow stays in the TCB: the engine's non-TCB
        # permission scan cannot see `secrets.*` use or job names that spoof
        # required checks.
        self.assertEqual(tcb_cfg.get("non_tcb_workflows", []), [])
        for exec_glob in (
            "anneal/ci/**",
            "ci/scripts/**",
            "zerocopy/cargo.sh",
            "zerocopy/ci/**",
        ):
            self.assertIn(exec_glob, tcb_cfg["extra_executable_paths"])
        self.assertEqual(
            tcb_cfg["caller"]["caller_workflows"],
            [
                ".github/workflows/ci-core-pr.yml",
                ".github/workflows/ci-core-trusted.yml",
            ],
        )
        self.assertEqual(tcb_cfg["caller"]["gate_check_name"], "ci-core / gate")

        for owner_rule in (
            "/.github/**",
            "/ci/**",
            "/zerocopy/cargo.sh",
            "/tools/**",
            "/anneal/ci/**",
            "/anneal/flake.nix",
            "/anneal/flake.lock",
            "/anneal/Cargo.toml",
            "/anneal/Cargo.lock",
            "/anneal/trusted/**",
            "/anneal/vendor/lean-miri/UPSTREAM_PIN.json",
        ):
            self.assertIn(owner_rule, self.codeowners)

    def test_anneal_checks_nested_bwrap_and_miri_cache_isolation(self):
        checks_by_id = {c["id"]: c for c in self.checks_cfg["checks"]}
        self.assertEqual(
            checks_by_id["meta-githooks"]["command"],
            ["./ci/scripts/check_shell_and_hooks.sh", "--require-shellcheck"],
        )

        expected_anneal = (
            "anneal-flake-eval",
            "anneal-ci-tests",
            "anneal-clippy",
            "anneal-sandbox-aarch64",
            "anneal-audit",
            "anneal-guard-mutation",
            "anneal-ws-meta",
            "anneal-ws-test",
            "anneal-installed-smoke",
        )
        for cid in expected_anneal:
            self.assertIn(cid, checks_by_id)
            self.assertNotIn(
                "events",
                checks_by_id[cid],
                f"{cid} must run across PR, merge_group, and push",
            )

        for bwrap_cid in (
            "anneal-flake-eval",
            "anneal-ci-tests",
            "anneal-audit",
            "anneal-guard-mutation",
            "anneal-ws-meta",
            "anneal-ws-test",
            "anneal-installed-smoke",
        ):
            chk = checks_by_id[bwrap_cid]
            self.assertEqual(chk.get("sandbox"), "nested_bwrap", bwrap_cid)
            self.assertEqual(chk.get("image"), "anneal-tc", bwrap_cid)

        arm_chk = checks_by_id["anneal-sandbox-aarch64"]
        self.assertEqual(arm_chk.get("sandbox"), "nested_bwrap")
        self.assertEqual(arm_chk.get("runner"), "ubuntu-24.04-arm")
        self.assertEqual(arm_chk.get("image"), "anneal-arm64")
        self.assertEqual(arm_chk.get("command"), ["./ci/run_anneal_check.sh", "sandbox"])
        self.assertEqual(
            self.checks_cfg["images"]["anneal-arm64"].get("platform"),
            "linux/arm64",
        )

        miri_cache = self.checks_cfg["caches"]["miri-v1"]
        self.assertEqual(miri_cache["tier"], "public_cas")
        self.assertEqual(miri_cache["mount"], "/ci-cache/miri")
        self.assertFalse(miri_cache["mount"].startswith("/work"))
        miri_inputs = set()
        for entry in miri_cache["inputs"]:
            miri_inputs.update(entry.get("include", ()))
        for key_file in (
            "anneal/flake.nix",
            "anneal/flake.lock",
            "anneal/trusted/lean/lean-toolchain",
            "anneal/trusted/lean/foundation-lock.json",
            "anneal/vendor/lean-miri/UPSTREAM_PIN.json",
        ):
            self.assertIn(key_file, miri_inputs)

        audit_match = re.search(
            r"(?ms)^\s*audit\)\n(.*?)\n\s*;;$", self.runner_script
        )
        self.assertIsNotNone(audit_match)
        audit_body = audit_match.group(1)

        with tempfile.TemporaryDirectory(prefix="anneal-miri-cache-") as tmp:
            tmp_path = Path(tmp)
            bin_dir = tmp_path / "bin"
            bin_dir.mkdir()
            recorded = tmp_path / "cargo_args.txt"
            seen_env = tmp_path / "ambient_env.txt"
            stub_cargo = bin_dir / "cargo"
            stub_cargo.write_text(
                "#!/usr/bin/env bash\n"
                f"printf '%s\\n' \"$@\" > '{recorded}'\n"
                f"printf '%s' \"${{ANNEAL_MIRI_CACHE_DIR-UNSET}}\" > '{seen_env}'\n"
            )
            stub_cargo.chmod(0o755)
            scratch_root = tmp_path / "scratch"
            scratch_miri = scratch_root / "miri-cache"

            # Execute the real `audit)` cache-selection logic with
            # `SCRATCH_ROOT` bound directly and stubbed
            # `verify_bwrap_sandbox`/`apply_bundle_env`.
            adapted_body = audit_body.replace(
                "cp -rL /opt/anneal-nix/lean-toolchain",
                "mkdir -p",
            )
            harness = (
                "set -euo pipefail\n"
                "unset ANNEAL_MIRI_CACHE_DIR ANNEAL_TEST_ARCHIVE ANNEAL_TEST_CASE\n"
                f"export SCRATCH_ROOT='{scratch_root}'\n"
                "HASH_OPT_ARGS=(--config 'profile.dev.package.sha2.opt-level=3')\n"
                "verify_bwrap_sandbox() { :; }\n"
                "apply_bundle_env() { export ANNEAL_TEST_INSTALL_ROOT=/fake/install; }\n"
                f"{adapted_body}\n"
            )

            def run_audit_probe(cache_path: Path):
                recorded.unlink(missing_ok=True)
                seen_env.unlink(missing_ok=True)
                env = os.environ.copy()
                env["PATH"] = f"{bin_dir}:{env.get('PATH', '')}"
                env["ANNEAL_MIRI_CACHE_DIR"] = "/ambient/poison"
                env["ANNEAL_CI_MIRI_CACHE_DIR"] = str(cache_path)
                res = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", harness],
                    cwd=tmp_path,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertEqual(seen_env.read_text(), "UNSET")
                return recorded.read_text().splitlines()

            # 1. Absent cache -> cold build without --miri-cache-dir.
            cold_args = run_audit_probe(tmp_path / "missing-cache")
            self.assertNotIn("--miri-cache-dir", cold_args)

            # 2. Writable cache -> passes --miri-cache-dir directly.
            rw_cache = tmp_path / "rw-cache"
            rw_cache.mkdir()
            rw_args = run_audit_probe(rw_cache)
            self.assertIn("--miri-cache-dir", rw_args)
            self.assertIn(str(rw_cache), rw_args)

            # 3. Read-only cache -> copies to scratch and passes scratch dir.
            ro_cache = tmp_path / "ro-cache"
            ro_cache.mkdir()
            (ro_cache / "marker.olean").write_text("olean")
            ro_cache.chmod(0o555)
            try:
                ro_args = run_audit_probe(ro_cache)
            finally:
                ro_cache.chmod(0o755)
            if os.geteuid() != 0:
                self.assertIn("--miri-cache-dir", ro_args)
                self.assertIn(str(scratch_miri), ro_args)
                self.assertTrue((scratch_miri / "marker.olean").is_file())

    def test_runner_optimization_sandbox_and_python_isolation_invariants(self):
        self.assertIn('CARGO_BUILD_JOBS="${CARGO_BUILD_JOBS:-4}"', self.runner_script)
        self.assertIn('RUST_TEST_THREADS="${RUST_TEST_THREADS:-4}"', self.runner_script)
        self.assertIn("CARGO_NET_OFFLINE=true", self.runner_script)
        self.assertIn('ANNEAL_TEST_JOBS="4"', self.runner_script)

        for pkg in ("cpufeatures", "digest", "sha2", "zstd-sys"):
            self.assertIn(
                f"--config 'profile.dev.package.{pkg}.opt-level=3'",
                self.runner_script,
            )

        for mode_header in ("sandbox)", "audit)", "ws-meta)", "ws-test)", "installed-smoke)"):
            idx = self.runner_script.index(f"  {mode_header}\n")
            end = self.runner_script.index("\n    ;;", idx)
            window = self.runner_script[idx:end]
            self.assertIn("verify_bwrap_sandbox", window, mode_header)

        for sandbox_test in (
            "sandbox_escape_vectors_blocked_in_tier1_and_tier2",
            "wall_clock_timeout_kills_process_group_in_tier1_and_tier2",
            "tier1_as_pid1_prevents_post_exit_out_writes",
        ):
            self.assertIn(sandbox_test, self.runner_script)

        self.assertIn(
            "cargo package --allow-dirty --no-verify --offline --registry crates-io",
            self.runner_script,
        )
        self.assertIn(
            'cargo build --locked --offline --manifest-path "$PREPARED_MANIFEST"',
            self.runner_script,
        )
        self.assertIn(
            'cargo test --locked --offline --manifest-path "$PREPARED_MANIFEST" --no-run',
            self.runner_script,
        )
        self.assertIn("ci/probe_alpha.py --cli /cargo-anneal", self.runner_script)
        self.assertIn("ci/verify_starnix_e2e.py", self.runner_script)
        self.assertIn("ci/verify_zerocopy.py", self.runner_script)

        # Every inline python3 heredoc in run_anneal_check.sh must run with
        # `-I -B` so repository files cannot shadow stdlib modules.
        heredocs = list(re.finditer(r"python3\b[^;\n]*<<", self.runner_script))
        self.assertGreaterEqual(len(heredocs), 1)
        for match in heredocs:
            self.assertIn("python3 -I -B -", match.group(0))
