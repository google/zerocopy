# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise current Anneal CI manifest guards and cache invariants."""

import hashlib
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
            "workspace-tests",
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
            jobs["test-and-verify"]["env"].get("ANNEAL_TEST_JOBS"), "4"
        )
        opt_flags = tuple(
            f"--config 'profile.dev.package.{pkg}.opt-level=3'"
            for pkg in ("cpufeatures", "digest", "sha2")
        )
        for job_name, step_ids in (
            (
                "test-and-verify",
                ("installed_cli", "installed_auditor", "audit", "package", "smoke"),
            ),
            ("workspace-tests", ("installed_cli", "workspace")),
        ):
            by_id = {
                s["id"]: s for s in jobs[job_name]["steps"] if "id" in s
            }
            for step_id in step_ids:
                for flag in opt_flags:
                    self.assertIn(
                        flag,
                        by_id[step_id]["run"],
                        f"{job_name}.{step_id} missing {flag}",
                    )

        rg_step = next(
            s for s in jobs["static-checks"]["steps"]
            if s.get("name") == "Install ripgrep"
        )
        self.assertIn("set -euo pipefail", rg_step["run"])
        self.assertIn("rg --version", rg_step["run"])

        for job_name in ("test-and-verify", "workspace-tests"):
            sandbox_step = next(
                s for s in jobs[job_name]["steps"] if s.get("id") == "sandbox"
            )
            self.assertIn("set -euo pipefail", sandbox_step["run"])
            self.assertIn("bwrap --unshare-all", sandbox_step["run"])
            self.assertIn("-- /true", sandbox_step["run"])

        alpha_step = next(
            s for s in jobs["test-and-verify"]["steps"]
            if s.get("name") == "Check the scalar alpha with the installed toolchain"
        )
        self.assertIn('"$ANNEAL_TEST_CARGO_ANNEAL" /cargo-anneal', alpha_step["run"])
        self.assertNotIn("cargo build", alpha_step["run"])

    def test_parallel_workspace_tests_job_wired_into_gate_and_isolated(self):
        jobs = self.workflow["jobs"]
        self.assertIn("workspace-tests", jobs["all-jobs-succeed"]["needs"])
        self.assertEqual(jobs["workspace-tests"]["needs"], ["build-exocrate"])
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
        # Every run step after checkout in workspace-tests (including manifest
        # and Record workspace test step results) must strip Actions tokens.
        checkout_idx = next(
            i for i, step in enumerate(ws_steps_list)
            if step.get("id") == "checkout"
        )
        post_checkout_run_steps = [
            step for step in ws_steps_list[checkout_idx + 1:] if "run" in step
        ]
        self.assertGreaterEqual(len(post_checkout_run_steps), 7)
        for step in post_checkout_run_steps:
            step_env = step.get("env", {})
            for token in tokens:
                self.assertEqual(
                    step_env.get(token),
                    "",
                    f"workspace-tests step {step.get('name')!r} must strip {token}",
                )
        # Record test step results in test-and-verify strips Actions tokens too.
        record_test_step = next(
            s for s in jobs["test-and-verify"]["steps"]
            if s.get("name") == "Record test step results"
        )
        for token in tokens:
            self.assertEqual(record_test_step.get("env", {}).get(token), "")
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
        self.assertGreaterEqual(inline_py_count, 6)
        # Verify clean_tree in both test-and-verify and workspace-tests fails
        # closed when git status errors (e.g., outside a git repository).
        with tempfile.TemporaryDirectory() as non_git_dir:
            for job_name in ("test-and-verify", "workspace-tests"):
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
        # Diagnostic artifact names must stay distinct so parallel failures
        # never collide during upload.
        test_upload = next(
            s for s in jobs["test-and-verify"]["steps"]
            if s.get("name") == "Upload failed test diagnostics"
        )
        ws_upload = next(
            s for s in jobs["workspace-tests"]["steps"]
            if s.get("name") == "Upload failed workspace test diagnostics"
        )
        self.assertNotEqual(test_upload["with"]["name"], ws_upload["with"]["name"])


if __name__ == "__main__":
    unittest.main()
