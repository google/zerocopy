# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise current Anneal CI manifest guards and cache invariants."""

from datetime import datetime, timedelta, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from workflow_yaml import load_workflow_yaml


SOURCE = Path(__file__).resolve().parent


class CiWorkflowManifestGuardTests(unittest.TestCase):
    def setUp(self):
        self.workflow = load_workflow_yaml(
            (SOURCE.parent.parent / ".github/workflows/anneal-current.yml").read_text()
        )
        workflow = self.workflow
        self.manifest_steps = {}
        for job_name in (
            "static-checks",
            "build-exocrate",
            "test-and-verify",
            "installed-smoke",
            "workspace-tests",
            "sandbox-aarch64",
        ):
            steps = workflow["jobs"][job_name]["steps"]
            matches = [
                step["run"]
                for step in steps
                if step.get("name") == "Verify root TCB manifest"
            ]
            self.assertEqual(len(matches), 1, job_name)
            self.manifest_steps[job_name] = matches[0]

    def run_manifest_step(self, job_name, mutate=None, *, parent_override=False):
        with tempfile.TemporaryDirectory(prefix="anneal-ci-guard-") as tmp:
            root = Path(tmp) / "repo"
            project = root / "anneal"
            project.mkdir(parents=True)
            diag = Path(tmp) / "diag"
            diag.mkdir()
            github_env = Path(tmp) / "github_env"
            github_env.write_text("")

            (project / "trusted").mkdir()
            cargo_toml = project / "Cargo.toml"
            cargo_toml.write_bytes(b"[workspace]\n")
            digest = hashlib.sha256(cargo_toml.read_bytes()).hexdigest()
            (project / "trusted/root-manifest.sha256").write_text(
                f"{digest}  Cargo.toml\n"
            )

            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "init", "-q"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.email", "test@example.com"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Test"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false",
                 "add", "anneal/Cargo.toml", "anneal/trusted/root-manifest.sha256"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "commit", "-qm", "init"],
                cwd=root,
                check=True,
            )

            if mutate is not None:
                mutate(root if parent_override else project)

            env = os.environ.copy()
            env["ANNEAL_BUILD_DIAGNOSTICS"] = str(diag)
            env["ANNEAL_TEST_DIAGNOSTICS"] = str(diag)
            env["GITHUB_WORKSPACE"] = str(root)
            env["GITHUB_ENV"] = str(github_env)
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-eo", "pipefail", "-c",
                 self.manifest_steps[job_name]],
                cwd=project,
                env=env,
                capture_output=True,
                text=True,
            )

    def test_clean_tree_passes_manifest_guard(self):
        for job_name in self.manifest_steps:
            with self.subTest(job=job_name):
                res = self.run_manifest_step(job_name)
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_root_override_paths_and_symlinks_fail_closed(self):
        cases = [
            ("cargo_dir", lambda r: (r / ".cargo").mkdir()),
            ("cargo_file", lambda r: (r / ".cargo").write_text("")),
            ("rust_toolchain", lambda r: (r / "rust-toolchain").write_text("nightly\n")),
            ("rust_toolchain_toml", lambda r: (r / "rust-toolchain.toml").write_text("")),
            ("valid_symlink_cargo", lambda r: (r / ".cargo").symlink_to("Cargo.toml")),
            ("valid_symlink_toolchain", lambda r: (r / "rust-toolchain.toml").symlink_to("Cargo.toml")),
            ("dangling_symlink_cargo", lambda r: (r / ".cargo").symlink_to("missing")),
            ("dangling_symlink_toolchain", lambda r: (r / "rust-toolchain").symlink_to("missing")),
        ]
        for job_name in self.manifest_steps:
            for parent_override in (False, True):
                for label, mutate in cases:
                    with self.subTest(job=job_name, case=label, parent=parent_override):
                        res = self.run_manifest_step(
                            job_name, mutate=mutate, parent_override=parent_override
                        )
                        self.assertNotEqual(res.returncode, 0)
                        self.assertIn(
                            "forbidden root config override:", res.stdout + res.stderr
                        )

    def test_nix_cache_restricts_trusted_substituter_to_main_push(self):
        build_steps = {
            step["id"]: step
            for step in self.workflow["jobs"]["build-exocrate"]["steps"]
            if "id" in step
        }
        restore = build_steps["restore_nix_cache"]
        expected_restore_if = (
            "github.event_name == 'push' "
            "&& github.repository == 'google/zerocopy' "
            "&& github.ref == 'refs/heads/main'"
        )
        self.assertEqual(restore["if"], expected_restore_if)
        self.assertTrue(
            restore["uses"].startswith("actions/cache/restore@")
        )
        self.assertNotIn("pull_request", restore["if"])
        self.assertNotIn("merge_group", restore["if"])
        self.assertNotIn("restore-keys", restore["with"])
        self.assertTrue(restore["with"]["path"].startswith("${{ runner.temp }}/"))
        self.assertNotIn("anneal/trusted/audit/**", restore["with"]["key"])

        expected_writer_if = (
            "github.event_name == 'push' "
            "&& github.repository == 'google/zerocopy' "
            "&& github.ref == 'refs/heads/main' "
            "&& steps.restore_nix_cache.outputs.cache-hit != 'true'"
        )
        for writer_id in ("populate_nix_cache", "save_nix_cache"):
            self.assertEqual(build_steps[writer_id]["if"], expected_writer_if)
        populate_run = build_steps["populate_nix_cache"]["run"]
        wipe_idx = populate_run.index('rm -rf "$RUNNER_TEMP/anneal-nix-cache"')
        mkdir_idx = populate_run.index('mkdir -p "$RUNNER_TEMP/anneal-nix-cache"')
        self.assertLess(wipe_idx, mkdir_idx)
        save_nix = build_steps["save_nix_cache"]
        self.assertTrue(save_nix["uses"].startswith("actions/cache/save@"))
        self.assertEqual(save_nix["with"]["path"], restore["with"]["path"])
        self.assertEqual(
            save_nix["with"]["key"],
            "${{ steps.restore_nix_cache.outputs.cache-primary-key }}",
        )

    def test_miri_olean_cache_compiles_cold_on_main_and_merge_group(self):
        ordered_steps = self.workflow["jobs"]["test-and-verify"]["steps"]
        step_indices = {
            step["id"]: idx
            for idx, step in enumerate(ordered_steps)
            if "id" in step
        }
        test_steps = {
            step["id"]: step for step in ordered_steps if "id" in step
        }
        self.assertLess(
            step_indices["miri_olean_cache"], step_indices["audit"]
        )
        self.assertLess(
            step_indices["audit"], step_indices["save_miri_olean_cache"]
        )

        restore = test_steps["miri_olean_cache"]
        self.assertTrue(
            restore["uses"].startswith("actions/cache/restore@")
        )
        self.assertEqual(
            restore["if"],
            "${{ github.event_name == 'pull_request' || "
            "(github.event_name == 'push' "
            "&& github.repository == 'google/zerocopy' "
            "&& github.ref == 'refs/heads/main') }}",
        )
        self.assertNotIn("restore-keys", restore["with"])
        self.assertTrue(restore["with"]["path"].startswith("${{ runner.temp }}/"))
        self.assertEqual(
            restore["with"]["lookup-only"],
            "${{ github.event_name == 'push' }}",
        )

        save = test_steps["save_miri_olean_cache"]
        self.assertTrue(save["uses"].startswith("actions/cache/save@"))
        self.assertEqual(
            save["if"],
            "${{ steps.miri_olean_cache.outputs.cache-hit != 'true' && "
            "(github.event_name == 'pull_request' || "
            "(github.event_name == 'push' "
            "&& github.repository == 'google/zerocopy' "
            "&& github.ref == 'refs/heads/main')) }}",
        )
        self.assertEqual(save["with"]["path"], restore["with"]["path"])
        self.assertEqual(
            save["with"]["key"],
            "${{ steps.miri_olean_cache.outputs.cache-primary-key }}",
        )

        # Execute the `audit` step's argument-selection shell logic against a
        # stub `cargo` command to verify cold compilation on `push`,
        # `merge_group`, `workflow_dispatch`, and unknown events, and seeding
        # only on a missing `main` cache entry.
        audit_script = test_steps["audit"]["run"]
        with tempfile.TemporaryDirectory(prefix="anneal-ci-miri-cache-") as tmp:
            tmp_path = Path(tmp)
            bin_dir = tmp_path / "bin"
            bin_dir.mkdir()
            recorded = tmp_path / "cargo_args.txt"
            seen_cache = tmp_path / "cache_seen_by_cargo.txt"
            seen_env = tmp_path / "ambient_env_seen.txt"
            stub_cargo = bin_dir / "cargo"
            stub_cargo.write_text(
                "#!/usr/bin/env bash\n"
                f"printf '%s\\n' \"$@\" > '{recorded}'\n"
                "if [ -e \"$MIRI_OLEAN_CACHE_DIR\" ]; then\n"
                f"  echo exists > '{seen_cache}'\n"
                "else\n"
                f"  echo absent > '{seen_cache}'\n"
                "fi\n"
                f"printf '%s' \"${{ANNEAL_MIRI_CACHE_DIR-UNSET}}\" > '{seen_env}'\n"
            )
            stub_cargo.chmod(0o755)
            diag = tmp_path / "diag"
            diag.mkdir()

            def run_audit_case(event_name, repo, ref, cache_hit, preseed=False):
                cache_dir = tmp_path / "miri-cache"
                if cache_dir.exists():
                    for p in sorted(cache_dir.rglob("*"), reverse=True):
                        p.unlink() if p.is_file() else p.rmdir()
                    cache_dir.rmdir()
                if preseed:
                    cache_dir.mkdir(parents=True, exist_ok=True)
                    (cache_dir / "stale.olean").write_text("stale")
                recorded.unlink(missing_ok=True)
                seen_cache.unlink(missing_ok=True)
                seen_env.unlink(missing_ok=True)
                env = os.environ.copy()
                env.update({
                    "PATH": f"{bin_dir}:{env.get('PATH', '')}",
                    "ANNEAL_MIRI_CACHE_DIR": "/ambient/poison",
                    "ANNEAL_TEST_DIAGNOSTICS": str(diag),
                    "ANNEAL_TEST_INSTALL_ROOT": "/fake/install",
                    "CI_EVENT_NAME": event_name,
                    "CI_REPOSITORY": repo,
                    "CI_REF": ref,
                    "MIRI_CACHE_HIT": cache_hit,
                    "MIRI_OLEAN_CACHE_DIR": str(cache_dir),
                })
                res = subprocess.run(
                    [
                        "bash",
                        "--noprofile",
                        "--norc",
                        "-eo",
                        "pipefail",
                        "-c",
                        audit_script,
                    ],
                    cwd=tmp_path,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertEqual(seen_env.read_text(), "UNSET")
                return (
                    recorded.read_text().splitlines(),
                    seen_cache.read_text().strip(),
                )

            # 1. merge_group, workflow_dispatch, and other non-PR events never
            # pass --miri-cache-dir.
            for ev in ("merge_group", "workflow_dispatch", "schedule"):
                args, _ = run_audit_case(
                    ev, "google/zerocopy", "refs/heads/main", ""
                )
                self.assertNotIn("--miri-cache-dir", args)

            # 2. push on main with cache hit wipes any pre-existing cache dir
            # before cargo runs and omits --miri-cache-dir.
            args, seen = run_audit_case(
                "push", "google/zerocopy", "refs/heads/main", "true",
                preseed=True,
            )
            self.assertEqual(seen, "absent")
            self.assertNotIn("--miri-cache-dir", args)

            # 3. push on main with cache miss (false or empty) wipes any
            # pre-existing cache dir before cargo runs (cold compile) and
            # passes --miri-cache-dir to seed main.
            for miss_val in ("false", ""):
                args, seen = run_audit_case(
                    "push", "google/zerocopy", "refs/heads/main", miss_val,
                    preseed=True,
                )
                self.assertEqual(seen, "absent")
                self.assertIn("--miri-cache-dir", args)

            # 4. push on a fork or non-main branch wipes any pre-existing cache
            # dir before cargo runs and omits --miri-cache-dir.
            for repo, ref in (
                ("someone/zerocopy", "refs/heads/main"),
                ("google/zerocopy", "refs/heads/dev"),
            ):
                args, seen = run_audit_case(
                    "push", repo, ref, "false", preseed=True
                )
                self.assertEqual(seen, "absent")
                self.assertNotIn("--miri-cache-dir", args)

            # 5. pull_request preserves the restored cache dir and passes
            # --miri-cache-dir to consume main's cache.
            args, seen = run_audit_case(
                "pull_request", "google/zerocopy", "refs/pull/1/merge", "true",
                preseed=True,
            )
            self.assertEqual(seen, "exists")
            self.assertIn("--miri-cache-dir", args)

    def test_ci_performance_and_sandbox_probe_invariants(self):
        top_env = self.workflow["env"]
        self.assertEqual(top_env.get("CARGO_BUILD_JOBS"), "4")
        self.assertEqual(top_env.get("RUST_TEST_THREADS"), "4")

        jobs = self.workflow["jobs"]
        self.assertEqual(
            jobs["installed-smoke"]["env"].get("ANNEAL_TEST_JOBS"), "4"
        )
        hash_opt_flags = tuple(
            f"--config 'profile.dev.package.{pkg}.opt-level=3'"
            for pkg in ("cpufeatures", "digest", "sha2")
        )
        full_opt_flags = hash_opt_flags + (
            "--config 'profile.dev.package.zstd-sys.opt-level=3'",
        )
        for job_name, step_ids, required_flags in (
            ("test-and-verify", ("audit",), hash_opt_flags),
            (
                "installed-smoke",
                ("installed_cli", "installed_auditor", "package", "smoke"),
                full_opt_flags,
            ),
            ("workspace-tests", ("workspace",), full_opt_flags),
        ):
            by_id = {
                s["id"]: s for s in jobs[job_name]["steps"] if "id" in s
            }
            for step_id in step_ids:
                for flag in required_flags:
                    self.assertIn(
                        flag,
                        by_id[step_id]["run"],
                        f"{job_name}.{step_id} missing {flag}",
                    )
        # Verify BOTH `cargo publish --dry-run` and `cargo test --no-run` in
        # `installed-smoke.package` receive all four optimization `--config`
        # flags so Cargo does not recompile deps at opt-level=0.
        pkg_run = next(
            s["run"]
            for s in jobs["installed-smoke"]["steps"]
            if s.get("id") == "package"
        )
        publish_block, test_block = pkg_run.split("prepared_manifest=", 1)
        for flag in full_opt_flags:
            self.assertIn(flag, publish_block, f"cargo publish missing {flag}")
            self.assertIn(flag, test_block, f"packaged cargo test missing {flag}")

        rg_step = next(
            s for s in jobs["static-checks"]["steps"]
            if s.get("name") == "Install ripgrep"
        )
        self.assertIn("set -euo pipefail", rg_step["run"])
        self.assertIn("rg --version", rg_step["run"])

        for job_name in ("test-and-verify", "installed-smoke", "workspace-tests"):
            sandbox_step = next(
                s for s in jobs[job_name]["steps"] if s.get("id") == "sandbox"
            )
            self.assertIn("set -euo pipefail", sandbox_step["run"])
            self.assertIn("bwrap --unshare-all", sandbox_step["run"])
            self.assertIn("-- /true", sandbox_step["run"])

        build_step = next(
            s for s in jobs["build-exocrate"]["steps"] if s.get("id") == "build"
        )
        self.assertIn("nix build --max-jobs 4 --cores 4", build_step["run"])

        extract_step = next(
            s for s in jobs["test-and-verify"]["steps"]
            if s.get("id") == "extract_lean"
        )
        self.assertIn("bwrap --unshare-all", extract_step["run"])
        self.assertIn("tar --no-same-owner --zstd -xf /archive.tar.zst -C /out lean", extract_step["run"])
        self.assertIn("/usr/bin/python3 -I -B ci/check_bundle_tree.py", extract_step["run"])
        self.assertIn("--lean-only", extract_step["run"])

        setup_step = next(
            s for s in jobs["installed-smoke"]["steps"]
            if s.get("id") == "setup"
        )
        self.assertIn("/usr/bin/python3 -I -B ci/check_bundle_tree.py", setup_step["run"])
        self.assertIn("--discover-single", setup_step["run"])

        ws_extract = next(
            s for s in jobs["workspace-tests"]["steps"]
            if s.get("id") == "extract_toolchain"
        )
        self.assertIn("bwrap --unshare-all", ws_extract["run"])
        self.assertIn("tar --no-same-owner --zstd -xf /archive.tar.zst -C /out", ws_extract["run"])
        self.assertIn("/usr/bin/python3 -I -B ci/check_bundle_tree.py", ws_extract["run"])
        for ws_step in jobs["workspace-tests"]["steps"]:
            self.assertNotIn("cargo install", ws_step.get("run", ""))

        alpha_step = next(
            s for s in jobs["installed-smoke"]["steps"]
            if s.get("name") == "Check the scalar alpha with the installed toolchain"
        )
        self.assertIn('"$ANNEAL_TEST_CARGO_ANNEAL" /cargo-anneal', alpha_step["run"])
        self.assertNotIn("cargo build", alpha_step["run"])

        starnix_step = next(
            s for s in jobs["installed-smoke"]["steps"]
            if s.get("id") == "starnix"
        )
        self.assertIn("ci/verify_starnix_e2e.py", starnix_step["run"])
        self.assertIn("--fetch-only", starnix_step["run"])
        self.assertIn("bwrap --unshare-all", starnix_step["run"])
        self.assertIn('--cli "$ANNEAL_TEST_CARGO_ANNEAL"', starnix_step["run"])

        zc_step = next(
            s for s in jobs["installed-smoke"]["steps"]
            if s.get("id") == "verify_zerocopy"
        )
        self.assertIn("ci/verify_zerocopy.py", zc_step["run"])
        self.assertIn("bwrap --unshare-all", zc_step["run"])
        self.assertIn('--cli "$ANNEAL_TEST_CARGO_ANNEAL"', zc_step["run"])
        self.assertIn('--jobs "$ANNEAL_TEST_JOBS"', zc_step["run"])
        for token in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
            "ACTIONS_RUNTIME_URL",
        ):
            self.assertEqual(zc_step.get("env", {}).get(token), "")

    def test_parallel_workspace_tests_job_wired_into_gate_and_isolated(self):
        jobs = self.workflow["jobs"]
        for parallel_job in ("installed-smoke", "workspace-tests"):
            self.assertIn(parallel_job, jobs["all-jobs-succeed"]["needs"])
            self.assertEqual(jobs[parallel_job]["needs"], ["build-exocrate"])
        self.assertIn("sandbox-aarch64", jobs["all-jobs-succeed"]["needs"])
        arm_job = jobs["sandbox-aarch64"]
        arm_checkout = next(
            step for step in arm_job["steps"]
            if step.get("uses", "").startswith("actions/checkout@")
        )
        self.assertEqual(
            arm_checkout["with"]["persist-credentials"], "false"
        )
        for token in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        ):
            self.assertEqual(arm_job.get("env", {}).get(token), "")
        ws_steps_list = jobs["workspace-tests"]["steps"]
        ws_steps = {
            step["id"]: step
            for step in ws_steps_list
            if "id" in step
        }
        self.assertEqual(
            ws_steps["checkout"]["with"]["persist-credentials"], "false"
        )
        self.assertIn("cargo test --workspace --locked", ws_steps["workspace"]["run"])
        tokens = (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        )
        # Every run step after checkout in test-and-verify, installed-smoke,
        # and workspace-tests must strip Actions tokens.
        for job_name, min_run_steps in (
            ("test-and-verify", 6),
            ("installed-smoke", 12),
            ("workspace-tests", 6),
        ):
            steps_list = jobs[job_name]["steps"]
            checkout_idx = next(
                i for i, step in enumerate(steps_list)
                if step.get("id") == "checkout"
            )
            self.assertEqual(
                steps_list[checkout_idx]["with"]["persist-credentials"], "false"
            )
            post_checkout_run_steps = [
                step for step in steps_list[checkout_idx + 1:] if "run" in step
            ]
            self.assertGreaterEqual(len(post_checkout_run_steps), min_run_steps)
            for step in post_checkout_run_steps:
                step_env = step.get("env", {})
                for token in tokens:
                    self.assertEqual(
                        step_env.get(token),
                        "",
                        f"{job_name} step {step.get('name')!r} must strip {token}",
                    )
        # Every inline python3 heredoc in anneal-current.yml must run isolated
        # (-I -B) so untrusted repo root files cannot shadow stdlib modules.
        inline_py_count = 0
        for job_name, job in jobs.items():
            for step in job.get("steps", []):
                run_src = step.get("run", "")
                for match in re.finditer(r"python3\b[^;\n]*<<", run_src):
                    inline_py_count += 1
                    self.assertTrue(
                        match.group(0).startswith("python3 -I -B -"),
                        f"{job_name}/{step.get('name')!r} must use python3 -I -B -: "
                        f"{match.group(0)!r}",
                    )
        self.assertGreaterEqual(inline_py_count, 5)
        # Verify clean_tree in test-and-verify, installed-smoke, and
        # workspace-tests fails closed when git status errors (e.g., outside a
        # git repository).
        with tempfile.TemporaryDirectory() as non_git_dir:
            for job_name in ("test-and-verify", "installed-smoke", "workspace-tests"):
                clean_step = next(
                    s for s in jobs[job_name]["steps"]
                    if s.get("id") == "clean_tree"
                )
                self.assertIn("set -euo pipefail", clean_step["run"])
                res = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", clean_step["run"]],
                    cwd=non_git_dir,
                    capture_output=True,
                    text=True,
                )
                self.assertNotEqual(
                    res.returncode,
                    0,
                    f"{job_name}.clean_tree masked git status failure",
                )
        # Diagnostic artifact names must stay distinct across all parallel jobs
        # so concurrent failures never collide during upload.
        upload_names = []
        for job_name, step_name in (
            ("test-and-verify", "Upload failed test diagnostics"),
            ("installed-smoke", "Upload failed installed smoke diagnostics"),
            ("workspace-tests", "Upload failed workspace test diagnostics"),
        ):
            upload = next(
                s for s in jobs[job_name]["steps"]
                if s.get("name") == step_name
            )
            upload_names.append(upload["with"]["name"])
        self.assertEqual(len(upload_names), len(set(upload_names)), upload_names)

    def test_release_lock_wired_into_gate_with_least_privilege(self):
        jobs = self.workflow["jobs"]
        self.assertIn("release-lock", jobs)
        lock_job = jobs["release-lock"]
        self.assertEqual(
            lock_job["if"],
            "github.event_name == 'merge_group' && vars.ANNEAL_RELEASE_LOCK != ''",
        )
        self.assertEqual(lock_job["permissions"], {"contents": "read"})
        self.assertEqual(lock_job["timeout-minutes"], "10")
        for token in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
        ):
            self.assertEqual(lock_job.get("env", {}).get(token), "")

        steps = lock_job["steps"]
        checkout = next(
            s for s in steps if s.get("uses", "").startswith("actions/checkout@")
        )
        self.assertRegex(
            checkout["uses"], r"^actions/checkout@[0-9a-f]{40}$"
        )
        self.assertEqual(checkout["with"]["persist-credentials"], "false")

        lock_step = next(s for s in steps if s.get("id") == "lock")
        self.assertEqual(lock_step.get("working-directory"), ".")
        self.assertEqual(
            lock_step["env"]["ANNEAL_RELEASE_LOCK"],
            "${{ vars.ANNEAL_RELEASE_LOCK }}",
        )
        self.assertEqual(
            lock_step["env"]["BASE_SHA"],
            "${{ github.event.merge_group.base_sha }}",
        )
        self.assertNotIn("${{", lock_step["run"])
        for allowed in (
            "anneal/trusted/cargo-anneal/Cargo.toml",
            "anneal/Cargo.lock",
            "anneal/trusted/root-manifest.sha256",
        ):
            self.assertIn(allowed, lock_step["run"])

        gate = jobs["all-jobs-succeed"]
        self.assertIn("release-lock", gate["needs"])
        gate_step = next(
            s for s in gate["steps"]
            if s.get("name") == "Require every dependency to succeed"
        )
        self.assertEqual(
            gate_step["env"]["EVENT_NAME"], "${{ github.event_name }}"
        )
        self.assertEqual(
            gate_step["env"]["ANNEAL_RELEASE_LOCK"],
            "${{ vars.ANNEAL_RELEASE_LOCK }}",
        )
        self.assertEqual(gate_step["env"]["NEEDS_JSON"], "${{ toJSON(needs) }}")
        self.assertNotIn("${{", gate_step["run"])

    def test_release_lock_script_enforces_three_file_allowlist_and_shallow_fetch(self):
        lock_step = next(
            s for s in self.workflow["jobs"]["release-lock"]["steps"]
            if s.get("id") == "lock"
        )
        script = lock_step["run"]
        allowlist = (
            "anneal/trusted/cargo-anneal/Cargo.toml",
            "anneal/Cargo.lock",
            "anneal/trusted/root-manifest.sha256",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-release-lock-") as tmp:
            tmp_path = Path(tmp)
            bare = tmp_path / "remote.git"
            seed = tmp_path / "seed"
            subprocess.run(
                ["git", "init", "--bare", "-q", str(bare)], check=True
            )
            subprocess.run(
                ["git", "--git-dir", str(bare), "config",
                 "uploadpack.allowAnySHA1InWant", "true"],
                check=True,
            )
            subprocess.run(
                ["git", "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "init", "-q", str(seed)],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(seed), "config", "user.name", "Test"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(seed), "config", "user.email", "t@example.com"],
                check=True,
            )
            for rel in allowlist + ("anneal/README.md", "zerocopy/src/lib.rs", "other.txt"):
                target = seed / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text("base\n" * 20)
            subprocess.run(
                ["git", "-C", str(seed), "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "add", "."],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(seed), "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "commit", "-qm", "base"],
                check=True,
            )
            base_sha = subprocess.check_output(
                ["git", "-C", str(seed), "rev-parse", "HEAD"], text=True
            ).strip()
            # Advance main once more on origin so base_sha is a non-tip SHA.
            (seed / "anneal/README.md").write_text("base\n" * 20 + "next\n")
            subprocess.run(
                ["git", "-C", str(seed), "-c", "core.hooksPath=/dev/null",
                 "-c", "core.fsmonitor=false", "commit", "-qam", "main-tip"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(seed), "remote", "add", "origin", bare.as_uri()],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(seed), "push", "-q", "origin", "HEAD:refs/heads/main"],
                check=True,
            )

            def run_case(label, mutate, *, base=base_sha, lock_val="0.2.0-alpha.8"):
                subprocess.run(
                    ["git", "-C", str(seed), "checkout", "-qB", label, base_sha],
                    check=True,
                )
                mutate(seed)
                subprocess.run(
                    ["git", "-C", str(seed), "-c", "core.hooksPath=/dev/null",
                     "-c", "core.fsmonitor=false", "push", "-qf", "origin",
                     f"HEAD:refs/heads/{label}"],
                    check=True,
                )
                shallow = tmp_path / f"shallow-{label}"
                subprocess.run(
                    ["git", "clone", "--quiet", "--depth=1", "--branch", label,
                     bare.as_uri(), str(shallow)],
                    check=True,
                )
                env = os.environ.copy()
                env["ANNEAL_RELEASE_LOCK"] = lock_val
                env["BASE_SHA"] = base
                return subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", script],
                    cwd=shallow,
                    env=env,
                    capture_output=True,
                    text=True,
                )

            def commit_updates(repo, paths):
                for rel in paths:
                    (repo / rel).write_text("updated\n")
                subprocess.run(
                    ["git", "-C", str(repo), "-c", "core.hooksPath=/dev/null",
                     "-c", "core.fsmonitor=false", "add", "--", *paths],
                    check=True,
                )
                subprocess.run(
                    ["git", "-C", str(repo), "-c", "core.hooksPath=/dev/null",
                     "-c", "core.fsmonitor=false", "commit", "-qm", "update"],
                    check=True,
                )

            # 1. Pure 3-file release PR passes.
            res = run_case("release-three", lambda r: commit_updates(r, allowlist))
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn(
                "Release lock (0.2.0-alpha.8): allowing pure Anneal release PR.",
                res.stdout,
            )

            # 2. Single-file release pin PR passes.
            res = run_case("release-one", lambda r: commit_updates(r, (allowlist[0],)))
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            # 3. Non-release PR fails with expected diagnostic.
            res = run_case("non-release", lambda r: commit_updates(r, ("anneal/README.md",)))
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(
                "Merge queue is locked for Anneal release (0.2.0-alpha.8); "
                "only the 3-file release PR may merge while ANNEAL_RELEASE_LOCK is set.",
                res.stderr,
            )

            # 4. Batched merge group (3 release files + 1 unrelated file) fails.
            res = run_case(
                "batched",
                lambda r: commit_updates(r, allowlist + ("zerocopy/src/lib.rs",)),
            )
            self.assertNotEqual(res.returncode, 0)

            # 5. Rename into allowlist path fails closed (--no-renames).
            def rename_into_allowlist(repo):
                subprocess.run(
                    ["git", "-C", str(repo), "mv", "-f", "other.txt", "anneal/Cargo.lock"],
                    check=True,
                )
                subprocess.run(
                    ["git", "-C", str(repo), "-c", "core.hooksPath=/dev/null",
                     "-c", "core.fsmonitor=false", "commit", "-qm", "rename"],
                    check=True,
                )

            res = run_case("rename-bypass", rename_into_allowlist)
            self.assertNotEqual(res.returncode, 0)

            # 6. Empty diff fails closed.
            res = run_case("empty-diff", lambda _r: None)
            self.assertNotEqual(res.returncode, 0)

            # 7. Invalid BASE_SHA or empty ANNEAL_RELEASE_LOCK fails closed.
            res = run_case("bad-sha", lambda _r: None, base="not-a-sha")
            self.assertNotEqual(res.returncode, 0)
            res = run_case("empty-lock", lambda _r: None, lock_val="")
            self.assertNotEqual(res.returncode, 0)

            # 8. TTL active enforces allowlist; TTL expired auto-unlocks;
            #    malformed TTL values fail closed.
            future_ts = (
                datetime.now(timezone.utc) + timedelta(hours=2)
            ).strftime("%Y-%m-%dT%H:%M:%SZ")
            past_ts = (
                datetime.now(timezone.utc) - timedelta(seconds=60)
            ).strftime("%Y-%m-%dT%H:%M:%SZ")
            active_lock = f"0.2.0-alpha.8;expires={future_ts}"
            expired_lock = f"0.2.0-alpha.8;expires={past_ts}"

            res = run_case(
                "ttl-active-release",
                lambda r: commit_updates(r, allowlist),
                lock_val=active_lock,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn(
                f"Release lock ({active_lock}): allowing pure Anneal release PR.",
                res.stdout,
            )

            res = run_case(
                "ttl-active-non-release",
                lambda r: commit_updates(r, ("anneal/README.md",)),
                lock_val=active_lock,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(
                f"Merge queue is locked for Anneal release ({active_lock});",
                res.stderr,
            )

            res = run_case(
                "ttl-expired-non-release",
                lambda r: commit_updates(r, ("anneal/README.md",)),
                lock_val=expired_lock,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn(
                f"Release lock ({expired_lock}) expired at {past_ts}; allowing merge_group.",
                res.stdout,
            )

            for idx, bad_lock in enumerate((
                "0.2.0-alpha.8;expires=not-a-timestamp",
                "0.2.0-alpha.8;expires=2026-11-23T06:00:00",
                "0.2.0-alpha.8;expires=2026-02-30T00:00:00Z",
                "0.2.0-alpha.8;expire=2026-11-23T06:00:00Z",
                f";expires={future_ts}",
                f"0.2.0-alpha.8;extra;expires={future_ts}",
            )):
                with self.subTest(bad_lock=bad_lock):
                    res = run_case(
                        f"ttl-malformed-{idx}",
                        lambda r: commit_updates(r, allowlist),
                        lock_val=bad_lock,
                    )
                    self.assertNotEqual(res.returncode, 0)

    def test_all_jobs_succeed_skip_handling_for_release_lock(self):
        gate = self.workflow["jobs"]["all-jobs-succeed"]
        gate_step = next(
            s for s in gate["steps"]
            if s.get("name") == "Require every dependency to succeed"
        )
        script = gate_step["run"]
        other_jobs = [j for j in gate["needs"] if j != "release-lock"]

        def run_gate(event_name, lock_val, release_result, other_overrides=None):
            needs = {j: {"result": "success"} for j in other_jobs}
            if other_overrides:
                for k, v in other_overrides.items():
                    needs[k] = {"result": v}
            needs["release-lock"] = {"result": release_result}
            env = os.environ.copy()
            env["EVENT_NAME"] = event_name
            env["ANNEAL_RELEASE_LOCK"] = lock_val
            env["NEEDS_JSON"] = json.dumps(needs)
            return subprocess.run(
                ["bash", "--noprofile", "--norc", "-c", script],
                env=env,
                capture_output=True,
                text=True,
            )

        for event, lock_val, release_result, expected_ok in (
            ("pull_request", "", "skipped", True),
            ("pull_request", "0.2.0-alpha.8", "skipped", True),
            ("pull_request", "", "success", False),
            ("pull_request", "", "failure", False),
            ("push", "", "skipped", True),
            ("push", "0.2.0-alpha.8", "skipped", True),
            ("push", "", "failure", False),
            ("merge_group", "", "skipped", True),
            ("merge_group", "", "success", True),
            ("merge_group", "", "failure", False),
            ("merge_group", "", "cancelled", False),
            ("merge_group", "0.2.0-alpha.8", "success", True),
            ("merge_group", "0.2.0-alpha.8", "skipped", False),
            ("merge_group", "0.2.0-alpha.8", "failure", False),
            ("merge_group", "0.2.0-alpha.8", "cancelled", False),
        ):
            with self.subTest(
                event=event, lock=lock_val, release_result=release_result
            ):
                res = run_gate(event, lock_val, release_result)
                self.assertEqual(
                    res.returncode == 0,
                    expected_ok,
                    res.stdout + res.stderr,
                )

        for bad_result in ("skipped", "failure", "cancelled"):
            res = run_gate(
                "pull_request", "", "skipped", {"static-checks": bad_result}
            )
            self.assertNotEqual(res.returncode, 0)


if __name__ == "__main__":
    unittest.main()
