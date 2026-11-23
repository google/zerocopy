# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise Anneal and repository CI manifest, cache, and path-filter guards."""

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
        self.assertNotIn("anneal/theory/**", restore["with"]["key"])
        self.assertNotIn(
            "anneal/trusted/cargo-anneal/src/bundled_resources.rs",
            restore["with"]["key"],
        )
        self.assertNotIn(
            "anneal/trusted/cargo-anneal/src/trusted_bundle.rs",
            restore["with"]["key"],
        )
        self.assertNotIn(
            "anneal/trusted/rustc-capture/**", restore["with"]["key"]
        )
        self.assertNotIn("anneal/Cargo.lock", restore["with"]["key"])
        for expected_input in (
            "anneal/flake.nix",
            "anneal/flake.lock",
            "anneal/trusted/lean/lean-toolchain",
            "anneal/trusted/lean/foundation-lock.json",
        ):
            self.assertIn(expected_input, restore["with"]["key"])

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
        self.assertIn("nix copy .#rust-toolchain .#lean-toolchain", populate_run)
        self.assertNotIn("omnibus-archive", populate_run)
        save_nix = build_steps["save_nix_cache"]
        self.assertTrue(save_nix["uses"].startswith("actions/cache/save@"))
        self.assertEqual(save_nix["with"]["path"], restore["with"]["path"])
        self.assertEqual(
            save_nix["with"]["key"],
            "${{ steps.restore_nix_cache.outputs.cache-primary-key }}",
        )

    def test_miri_olean_cache_restores_verified_on_merge_group_and_compiles_cold_on_main(self):
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
            "${{ github.event_name == 'pull_request' "
            "|| github.event_name == 'merge_group' || "
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
        self.assertNotIn("merge_group", save["if"])
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
        # `merge_group` misses, `workflow_dispatch`, and unknown events,
        # read-only cache hits on `merge_group`, and seeding only on a missing
        # `main` cache entry.
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

            # 1. workflow_dispatch and unknown non-PR/non-MG events never
            # pass --miri-cache-dir.
            for ev in ("workflow_dispatch", "schedule"):
                args, _ = run_audit_case(
                    ev, "google/zerocopy", "refs/heads/main", ""
                )
                self.assertNotIn("--miri-cache-dir", args)

            # 1b. merge_group uses read-only restored cache on cache-hit ==
            # "true" (SHA-256 verified inside anneal-audit) and compiles cold
            # on miss (wiping stale directory and omitting --miri-cache-dir).
            args, seen = run_audit_case(
                "merge_group",
                "google/zerocopy",
                "refs/heads/gh-readonly-queue/main/pr-1",
                "true",
                preseed=True,
            )
            self.assertEqual(seen, "exists")
            self.assertIn("--miri-cache-dir", args)
            for miss_val in ("false", ""):
                args, seen = run_audit_case(
                    "merge_group",
                    "google/zerocopy",
                    "refs/heads/gh-readonly-queue/main/pr-1",
                    miss_val,
                    preseed=True,
                )
                self.assertEqual(seen, "absent")
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
        # Verify `regenerate_bundle --stage-package`, `cargo publish --dry-run`,
        # and `cargo test --no-run` in `installed-smoke.package` each receive
        # all four optimization `--config` flags so Cargo does not recompile
        # deps at opt-level=0, and pin the clean-tree/single-file/cleanup guards
        # required for `--allow-dirty`.
        pkg_run = next(
            s["run"]
            for s in jobs["installed-smoke"]["steps"]
            if s.get("id") == "package"
        )
        pre_test_block, test_block = pkg_run.split("prepared_manifest=", 1)
        stage_block, publish_block = pre_test_block.split("cargo publish --dry-run", 1)
        self.assertIn(
            'clean_status="$(git status --porcelain --untracked-files=all)"',
            stage_block,
        )
        self.assertIn('test -z "$clean_status"', stage_block)
        self.assertIn("trap 'rm -rf trusted/cargo-anneal/packaged' EXIT", stage_block)
        self.assertIn("--stage-package", stage_block)
        self.assertIn(
            'test "$staged_status" = '
            '"?? anneal/trusted/cargo-anneal/packaged/bundled_resources.rs"',
            stage_block,
        )
        for flag in full_opt_flags:
            self.assertIn(flag, stage_block, f"regenerate_bundle missing {flag}")
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
            gate_step["env"]["RUN_HEAVY"],
            "${{ github.event_name != 'pull_request' || inputs.run_heavy }}",
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
        run_heavy_input = self.workflow["on"]["workflow_call"]["inputs"]["run_heavy"]
        self.assertEqual(run_heavy_input["type"], "boolean")
        self.assertEqual(run_heavy_input["default"], "true")
        for heavy_job in (
            "build-exocrate",
            "test-and-verify",
            "installed-smoke",
            "workspace-tests",
            "sandbox-aarch64",
        ):
            self.assertEqual(
                self.workflow["jobs"][heavy_job]["if"],
                "${{ github.event_name != 'pull_request' || inputs.run_heavy }}",
                heavy_job,
            )

        gate = self.workflow["jobs"]["all-jobs-succeed"]
        gate_step = next(
            s for s in gate["steps"]
            if s.get("name") == "Require every dependency to succeed"
        )
        script = gate_step["run"]
        other_jobs = [j for j in gate["needs"] if j != "release-lock"]

        def run_gate(
            event_name,
            lock_val,
            release_result,
            other_overrides=None,
            *,
            run_heavy="true",
        ):
            needs = {j: {"result": "success"} for j in other_jobs}
            if other_overrides:
                for k, v in other_overrides.items():
                    needs[k] = {"result": v}
            needs["release-lock"] = {"result": release_result}
            env = os.environ.copy()
            env["EVENT_NAME"] = event_name
            env["RUN_HEAVY"] = run_heavy
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

        # pull_request with run_heavy == "false" passes only when
        # static-checks succeeded and all heavy/lock jobs were skipped.
        pr_light_overrides = {
            j: "skipped" for j in other_jobs if j != "static-checks"
        }
        self.assertEqual(
            run_gate(
                "pull_request",
                "",
                "skipped",
                pr_light_overrides,
                run_heavy="false",
            ).returncode,
            0,
        )
        # Non-PR events ignore run_heavy == "false" and require heavy jobs.
        for non_pr in ("merge_group", "push", "workflow_dispatch"):
            self.assertNotEqual(
                run_gate(
                    non_pr,
                    "",
                    "skipped",
                    pr_light_overrides,
                    run_heavy="false",
                ).returncode,
                0,
                non_pr,
            )
        # Skipping static-checks or failing a heavy job on light PR fails
        # closed.
        self.assertNotEqual(
            run_gate(
                "pull_request",
                "",
                "skipped",
                {**pr_light_overrides, "static-checks": "skipped"},
                run_heavy="false",
            ).returncode,
            0,
        )
        self.assertNotEqual(
            run_gate(
                "pull_request",
                "",
                "skipped",
                {**pr_light_overrides, "workspace-tests": "failure"},
                run_heavy="false",
            ).returncode,
            0,
        )
        for bad_heavy in ("", "unexpected"):
            self.assertNotEqual(
                run_gate(
                    "pull_request",
                    "",
                    "skipped",
                    pr_light_overrides,
                    run_heavy=bad_heavy,
                ).returncode,
                0,
            )

        for bad_result in ("skipped", "failure", "cancelled"):
            res = run_gate(
                "pull_request", "", "skipped", {"static-checks": bad_result}
            )
            self.assertNotEqual(res.returncode, 0)


class PathFilterWorkflowTests(unittest.TestCase):
    def setUp(self):
        root = SOURCE.parent.parent
        self.ci_wf = load_workflow_yaml(
            (root / ".github/workflows/ci.yml").read_text()
        )
        self.anneal_wf = load_workflow_yaml(
            (root / ".github/workflows/anneal.yml").read_text()
        )

    def _run_detect_changes(
        self,
        workflow,
        event_name,
        commit_batches,
        *,
        setup_extra=None,
        synthetic_merge=False,
        pr_base_sha_override=None,
        pr_head_sha_override=None,
        drop_origin_main=False,
        pr_draft=None,
        pr_has_run_ci=None,
    ):
        script = next(
            step["run"]
            for step in workflow["jobs"]["detect_changes"]["steps"]
            if step.get("id") == "filter"
        )
        with tempfile.TemporaryDirectory(prefix="anneal-ci-filter-") as tmp:
            repo = Path(tmp) / "repo"
            repo.mkdir()
            gh_out = Path(tmp) / "gh_out.txt"
            gh_out.write_text("")

            def git(*args):
                return subprocess.run(
                    [
                        "git",
                        "-c",
                        "core.hooksPath=/dev/null",
                        "-c",
                        "core.fsmonitor=false",
                        *args,
                    ],
                    cwd=repo,
                    check=True,
                    capture_output=True,
                    text=True,
                )

            git("init", "-q", "-b", "main")
            git("config", "user.email", "test@example.com")
            git("config", "user.name", "Test")
            (repo / "README.md").write_text("base\n")
            git("add", "README.md")
            git("commit", "-qm", "base")
            if setup_extra is not None:
                setup_extra(repo, git)
            main_sha = git("rev-parse", "HEAD").stdout.strip()
            if not drop_origin_main:
                git("update-ref", "refs/remotes/origin/main", main_sha)

            base_sha = main_sha
            pr_tip = main_sha
            if synthetic_merge:
                # Create a diverged base commit on `main`, branch the PR from
                # `main_sha`, commit `commit_batches`, and merge PR into base
                # (mirroring GitHub's synthetic `refs/pull/N/merge` HEAD).
                git("checkout", "-qb", "pr-branch", main_sha)
                for idx, ops in enumerate(commit_batches):
                    self._apply_ops(repo, git, ops)
                    git("commit", "-qm", f"pr-{idx}")
                pr_tip = git("rev-parse", "HEAD").stdout.strip()
                git("checkout", "-q", "main")
                (repo / "zerocopy").mkdir(exist_ok=True)
                (repo / "zerocopy/unrelated_main.txt").write_text("main\n")
                git("add", "zerocopy/unrelated_main.txt")
                git("commit", "-qm", "advance-main")
                base_sha = git("rev-parse", "HEAD").stdout.strip()
                if not drop_origin_main:
                    git("update-ref", "refs/remotes/origin/main", base_sha)
                git("merge", "--no-ff", "-qm", "synthetic-pr-merge", pr_tip)
            else:
                for idx, ops in enumerate(commit_batches):
                    self._apply_ops(repo, git, ops)
                    git("commit", "-qm", f"batch-{idx}")
                    if idx + 1 < len(commit_batches):
                        base_sha = git("rev-parse", "HEAD").stdout.strip()
                pr_tip = git("rev-parse", "HEAD").stdout.strip()

            env = os.environ.copy()
            env.update({
                "GITHUB_OUTPUT": str(gh_out),
                "EVENT_NAME": event_name,
                "PR_DRAFT": (
                    pr_draft
                    if pr_draft is not None
                    else ("false" if event_name == "pull_request" else "")
                ),
                "PR_HAS_RUN_CI": (
                    pr_has_run_ci
                    if pr_has_run_ci is not None
                    else ("false" if event_name == "pull_request" else "")
                ),
                "PR_BASE_SHA": (
                    pr_base_sha_override
                    if pr_base_sha_override is not None
                    else (base_sha if event_name == "pull_request" else "")
                ),
                "PR_HEAD_SHA": (
                    pr_head_sha_override
                    if pr_head_sha_override is not None
                    else (pr_tip if event_name == "pull_request" else "")
                ),
            })
            res = subprocess.run(
                [
                    "bash",
                    "--noprofile",
                    "--norc",
                    "-eo",
                    "pipefail",
                    "-c",
                    script,
                ],
                cwd=repo,
                env=env,
                capture_output=True,
                text=True,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            out = {}
            for line in gh_out.read_text().splitlines():
                k, v = line.split("=", 1)
                out[k] = v
            return out

    @staticmethod
    def _apply_ops(repo, git, ops):
        if callable(ops):
            ops(repo, git)
            return
        for rel, content in ops.items():
            p = repo / rel
            if content is None:
                git("rm", "-q", rel)
            else:
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(content)
                git("add", rel)

    def test_detect_changes_classification_and_fail_closed_invariants(self):
        # Verify least-privilege, token-stripping, and PR event triggers.
        for wf_name, wf in (("ci.yml", self.ci_wf), ("anneal.yml", self.anneal_wf)):
            self.assertEqual(
                wf["on"]["pull_request"]["types"],
                [
                    "opened",
                    "synchronize",
                    "reopened",
                    "ready_for_review",
                    "converted_to_draft",
                    "labeled",
                    "unlabeled",
                ],
                wf_name,
            )
            job = wf["jobs"]["detect_changes"]
            self.assertEqual(job["permissions"], {"contents": "read"}, wf_name)
            for token in (
                "ACTIONS_CACHE_URL",
                "ACTIONS_RESULTS_URL",
                "ACTIONS_RUNTIME_TOKEN",
            ):
                self.assertEqual(job["env"][token], "", f"{wf_name}:{token}")
            checkout = next(
                s for s in job["steps"] if s.get("uses", "").startswith("actions/checkout@")
            )
            self.assertEqual(
                checkout["with"]["persist-credentials"], "false", wf_name
            )
            self.assertEqual(
                checkout["if"],
                "github.event_name == 'pull_request' && "
                "!contains(github.event.pull_request.labels.*.name, 'run-ci') "
                "&& !github.event.pull_request.draft",
                wf_name,
            )
            filter_step = next(
                s for s in job["steps"] if s.get("id") == "filter"
            )
            self.assertEqual(
                filter_step["env"]["EVENT_NAME"],
                "${{ github.event_name }}",
                wf_name,
            )
            self.assertEqual(
                filter_step["env"]["PR_DRAFT"],
                "${{ github.event.pull_request.draft }}",
                wf_name,
            )
            self.assertEqual(
                filter_step["env"]["PR_HAS_RUN_CI"],
                "${{ contains(github.event.pull_request.labels.*.name, 'run-ci') }}",
                wf_name,
            )
        self.assertEqual(
            self.ci_wf["jobs"]["detect_changes"]["outputs"]["run_zerocopy"],
            "${{ steps.filter.outputs.run_zerocopy }}",
        )
        self.assertEqual(
            self.anneal_wf["jobs"]["detect_changes"]["outputs"]["run_anneal"],
            "${{ steps.filter.outputs.run_anneal }}",
        )
        self.assertEqual(
            self.anneal_wf["jobs"]["detect_changes"]["outputs"]["run_heavy"],
            "${{ steps.filter.outputs.run_heavy }}",
        )
        self.assertEqual(
            self.anneal_wf["jobs"]["current_anneal"]["with"]["run_heavy"],
            "${{ needs.detect_changes.outputs.run_heavy != 'false' }}",
        )
        anneal_gate_step = next(
            s
            for s in self.anneal_wf["jobs"]["all-jobs-succeed"]["steps"]
            if s.get("name") == "Require every dependency to succeed"
        )
        self.assertEqual(
            anneal_gate_step["env"]["EVENT_NAME"],
            "${{ github.event_name }}",
        )
        self.assertEqual(
            anneal_gate_step["env"]["RUN_ANNEAL"],
            "${{ needs.detect_changes.outputs.run_anneal }}",
        )
        self.assertEqual(
            anneal_gate_step["env"]["RUN_HEAVY"],
            "${{ needs.detect_changes.outputs.run_heavy }}",
        )
        self.assertEqual(
            anneal_gate_step["env"]["NEEDS_JSON"],
            "${{ toJSON(needs) }}",
        )

        cases = [
            # (label, event, commit_batches, exp_run_zerocopy,
            #  exp_run_anneal, exp_run_heavy)
            ("anneal_only_pr", "pull_request", [{"anneal/README.md": "a"}], "false", "true", "false"),
            ("anneal_only_2_commits", "pull_request", [{"anneal/a.md": "a"}, {"anneal/b.md": "b"}], "false", "true", "false"),
            (
                "zerocopy_proofs_only_pr",
                "pull_request",
                [{"zerocopy/proofs/01_usize_pointer_metadata/Proof.lean": "p"}],
                "false",
                "true",
                "false",
            ),
            (
                "anneal_plus_zerocopy_proofs_pr",
                "pull_request",
                [{"anneal/README.md": "a", "zerocopy/proofs/05/Spec.lean": "s"}],
                "false",
                "true",
                "false",
            ),
            ("zerocopy_only_pr", "pull_request", [{"zerocopy/src/lib.rs": "z"}], "true", "false", "false"),
            ("zerocopy_only_2_commits", "pull_request", [{"zerocopy/a.rs": "a"}, {"zerocopy/b.rs": "b"}], "true", "false", "false"),
            (
                "zerocopy_proofs_plus_src_pr",
                "pull_request",
                [{"zerocopy/proofs/01/Proof.lean": "p", "zerocopy/src/lib.rs": "z"}],
                "true",
                "true",
                "false",
            ),
            (
                "non_anneal_prefixes",
                "pull_request",
                [{"evals/a.txt": "e", "tools/b.txt": "t", "maintainers/c.txt": "m"}],
                "true",
                "false",
                "false",
            ),
            (
                "allowed_root_non_anneal",
                "pull_request",
                [{
                    "CONTRIBUTING.md": "c",
                    "LICENSE-APACHE": "la",
                    "LICENSE-BSD": "lb",
                    "LICENSE-MIT": "lm",
                    "rustfmt.toml": "r",
                    ".dockerignore": "d",
                }],
                "true",
                "false",
                "false",
            ),
            ("exocrate_touches_both", "pull_request", [{"exocrate/src/lib.rs": "e"}], "true", "true", "false"),
            ("workflow_touches_both", "pull_request", [{".github/workflows/ci.yml": "w"}], "true", "true", "false"),
            ("ci_dir_touches_both", "pull_request", [{"ci/check_fmt.sh": "s"}], "true", "true", "false"),
            ("githooks_touches_both", "pull_request", [{"githooks/pre-push": "h"}], "true", "true", "false"),
            ("skills_dir_touches_both", "pull_request", [{"skills/commit-message/SKILL.md": "s"}], "true", "true", "false"),
            ("root_cargo_override", "pull_request", [{".cargo/config.toml": "x"}], "true", "true", "false"),
            ("root_rust_toolchain_override", "pull_request", [{"rust-toolchain.toml": "n"}], "true", "true", "false"),
            ("root_gitignore_touches_both", "pull_request", [{".gitignore": "g"}], "true", "true", "false"),
            ("root_rgignore_touches_both", "pull_request", [{".rgignore": "r"}], "true", "true", "false"),
            ("root_gemini_touches_both", "pull_request", [{".gemini/styleguide.md": "s"}], "true", "true", "false"),
            ("root_vscode_touches_both", "pull_request", [{".vscode/settings.json": "{}"}], "true", "true", "false"),
            ("mixed_pr", "pull_request", [{"anneal/a.txt": "a", "zerocopy/z.txt": "z"}], "true", "true", "false"),
            (
                "stacked_pr_lower_zerocopy_upper_anneal",
                "pull_request",
                [{"zerocopy/src/lib.rs": "z"}, {"anneal/README.md": "a"}],
                "true",
                "true",
                "false",
            ),
            (
                "stacked_pr_lower_anneal_upper_zerocopy",
                "pull_request",
                [{"anneal/README.md": "a"}, {"zerocopy/src/lib.rs": "z"}],
                "true",
                "true",
                "false",
            ),
            ("push_always_runs_both", "push", [{"anneal/README.md": "a"}], "true", "true", "true"),
            ("merge_group_always_runs_both", "merge_group", [{"zerocopy/src/lib.rs": "z"}], "true", "true", "true"),
            ("workflow_dispatch_always_runs_both", "workflow_dispatch", [{"anneal/README.md": "a"}], "true", "true", "true"),
        ]
        for label, event, batches, exp_zc, exp_an, exp_heavy in cases:
            with self.subTest(case=label):
                zc_out = self._run_detect_changes(self.ci_wf, event, batches)
                an_out = self._run_detect_changes(self.anneal_wf, event, batches)
                self.assertEqual(zc_out["run_zerocopy"], exp_zc)
                self.assertEqual(an_out["run_anneal"], exp_an)
                self.assertEqual(an_out["run_heavy"], exp_heavy)

        # Draft PRs without `run-ci` skip heavy jobs; explicit `run-ci` opts
        # even Draft PRs into full CI.
        for label, batch, run_ci, exp_zc, exp_an, exp_heavy in (
            ("draft_zerocopy", [{"zerocopy/src/lib.rs": "z"}], "false", "false", "false", "false"),
            ("draft_anneal", [{"anneal/README.md": "a"}], "false", "false", "false", "false"),
            ("draft_with_run_ci", [{"zerocopy/src/lib.rs": "z"}], "true", "true", "true", "true"),
        ):
            with self.subTest(case=label):
                zc_out = self._run_detect_changes(
                    self.ci_wf, "pull_request", batch, pr_draft="true", pr_has_run_ci=run_ci
                )
                an_out = self._run_detect_changes(
                    self.anneal_wf, "pull_request", batch, pr_draft="true", pr_has_run_ci=run_ci
                )
                self.assertEqual(zc_out["run_zerocopy"], exp_zc)
                self.assertEqual(an_out["run_anneal"], exp_an)
                self.assertEqual(an_out["run_heavy"], exp_heavy)

        # Ready PRs with `run-ci` label run full PR CI in both workflows.
        for label, batch in (
            ("run_ci_anneal_only", [{"anneal/README.md": "a"}]),
            ("run_ci_proofs_only", [{"zerocopy/proofs/01/Proof.lean": "p"}]),
            ("run_ci_zerocopy_only", [{"zerocopy/src/lib.rs": "z"}]),
        ):
            with self.subTest(case=label):
                zc_out = self._run_detect_changes(
                    self.ci_wf, "pull_request", batch, pr_draft="false", pr_has_run_ci="true"
                )
                an_out = self._run_detect_changes(
                    self.anneal_wf, "pull_request", batch, pr_draft="false", pr_has_run_ci="true"
                )
                self.assertEqual(zc_out["run_zerocopy"], "true")
                self.assertEqual(an_out["run_anneal"], "true")
                self.assertEqual(an_out["run_heavy"], "true")

        # Non-PR events ignore ambient PR_DRAFT and always run everything.
        for ev in ("merge_group", "push", "workflow_dispatch"):
            with self.subTest(case=f"{ev}_ignores_draft"):
                zc_out = self._run_detect_changes(
                    self.ci_wf, ev, [{"anneal/README.md": "a"}], pr_draft="true"
                )
                an_out = self._run_detect_changes(
                    self.anneal_wf, ev, [{"zerocopy/src/lib.rs": "z"}], pr_draft="true"
                )
                self.assertEqual(zc_out["run_zerocopy"], "true")
                self.assertEqual(an_out["run_anneal"], "true")
                self.assertEqual(an_out["run_heavy"], "true")

        # Decoy root `subprocess.py` in an untrusted PR must NOT be imported by
        # `python3 -I -B -` to spoof `run_*=false`.
        with self.subTest(case="decoy_root_subprocess_py_ignored"):
            decoy = (
                "import sys\n"
                "print('run_anneal=false')\n"
                "print('run_zerocopy=false')\n"
                "sys.exit(0)\n"
            )
            batch = [{
                "subprocess.py": decoy,
                "anneal/trusted/foo.rs": "// tcb\n",
                "zerocopy/src/lib.rs": "// zc\n",
            }]
            zc_out = self._run_detect_changes(self.ci_wf, "pull_request", batch)
            an_out = self._run_detect_changes(self.anneal_wf, "pull_request", batch)
            self.assertEqual(zc_out["run_zerocopy"], "true")
            self.assertEqual(an_out["run_anneal"], "true")

        # Cross-boundary renames must emit both source and destination paths
        # (`--no-renames`) and trigger both suites in both directions.
        def seed_renames(repo, git):
            for rel, txt in (
                ("anneal/src.txt", "unique-anneal-payload\n" * 20),
                ("zerocopy/src.txt", "unique-zerocopy-payload\n" * 20),
                ("exocrate/src.txt", "unique-exocrate-payload\n" * 20),
            ):
                p = repo / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt)
                git("add", rel)
            git("commit", "-qm", "seed-renames")

        for label, src, dst in (
            ("mv_anneal_to_zerocopy", "anneal/src.txt", "zerocopy/moved.txt"),
            ("mv_zerocopy_to_anneal", "zerocopy/src.txt", "anneal/moved.txt"),
            ("mv_exocrate_to_zerocopy", "exocrate/src.txt", "zerocopy/moved_exo.txt"),
        ):
            def do_mv(repo, git, s=src, d=dst):
                (repo / d).parent.mkdir(parents=True, exist_ok=True)
                git("mv", s, d)

            with self.subTest(case=label):
                zc_out = self._run_detect_changes(
                    self.ci_wf, "pull_request", [do_mv], setup_extra=seed_renames
                )
                an_out = self._run_detect_changes(
                    self.anneal_wf, "pull_request", [do_mv], setup_extra=seed_renames
                )
                self.assertEqual(zc_out["run_zerocopy"], "true")
                self.assertEqual(an_out["run_anneal"], "true")

        # Synthetic PR merge commits (`HEAD^1` = main with unrelated zerocopy
        # change, `HEAD^2` = Anneal-only PR) must classify using PR changes.
        with self.subTest(case="synthetic_merge_anneal_only"):
            zc_out = self._run_detect_changes(
                self.ci_wf, "pull_request", [{"anneal/doc.md": "a"}],
                synthetic_merge=True,
            )
            an_out = self._run_detect_changes(
                self.anneal_wf, "pull_request", [{"anneal/doc.md": "a"}],
                synthetic_merge=True,
            )
            self.assertEqual(zc_out["run_zerocopy"], "false")
            self.assertEqual(an_out["run_anneal"], "true")

        # Intermediate commit touching and reverting a file in the other suite
        # must still trigger that suite via commit-log inspection (both linear
        # and authored side-branch merges).
        with self.subTest(case="intermediate_commit_touch_and_revert_anneal"):
            def make_revert_anneal(repo, git):
                (repo / "anneal").mkdir(exist_ok=True)
                (repo / "anneal/temp.txt").write_text("temp\n")
                git("add", "anneal/temp.txt")
                git("commit", "-qm", "touch-anneal")
                git("rm", "-q", "anneal/temp.txt")
                (repo / "zerocopy").mkdir(exist_ok=True)
                (repo / "zerocopy/change.rs").write_text("// zc\n")
                git("add", "zerocopy/change.rs")

            an_out = self._run_detect_changes(
                self.anneal_wf, "pull_request", [make_revert_anneal],
                synthetic_merge=True,
            )
            self.assertEqual(an_out["run_anneal"], "true")

        with self.subTest(case="intermediate_commit_touch_and_revert_zerocopy"):
            def make_revert_zc(repo, git):
                (repo / "zerocopy").mkdir(exist_ok=True)
                (repo / "zerocopy/temp.rs").write_text("// temp\n")
                git("add", "zerocopy/temp.rs")
                git("commit", "-qm", "touch-zc")
                git("rm", "-q", "zerocopy/temp.rs")
                (repo / "anneal").mkdir(exist_ok=True)
                (repo / "anneal/doc.md").write_text("a\n")
                git("add", "anneal/doc.md")

            zc_out = self._run_detect_changes(
                self.ci_wf, "pull_request", [make_revert_zc],
                synthetic_merge=True,
            )
            self.assertEqual(zc_out["run_zerocopy"], "true")

        with self.subTest(case="authored_merge_side_branch_touch_and_revert"):
            def make_side_branch_merge(repo, git):
                start = git("rev-parse", "HEAD").stdout.strip()
                git("checkout", "-qb", "side-branch", start)
                (repo / "anneal").mkdir(exist_ok=True)
                (repo / "anneal/side.txt").write_text("side\n")
                git("add", "anneal/side.txt")
                git("commit", "-qm", "side-touch-anneal")
                git("rm", "-q", "anneal/side.txt")
                git("commit", "-qm", "side-revert-anneal")
                side_tip = git("rev-parse", "HEAD").stdout.strip()
                git("checkout", "-q", "pr-branch")
                (repo / "zerocopy").mkdir(exist_ok=True)
                (repo / "zerocopy/mainline.rs").write_text("// zc\n")
                git("add", "zerocopy/mainline.rs")
                git("commit", "-qm", "pr-zc-change")
                git("merge", "--no-ff", "-qm", "merge-side", side_tip)
                (repo / "zerocopy/final.rs").write_text("// final\n")
                git("add", "zerocopy/final.rs")

            an_out = self._run_detect_changes(
                self.anneal_wf, "pull_request", [make_side_branch_merge],
                synthetic_merge=True,
            )
            self.assertEqual(an_out["run_anneal"], "true")

        # Fail-closed error and empty-diff conditions must run both suites.
        # Use an Anneal-only commit for `ci.yml` and a Zerocopy-only commit for
        # `anneal.yml` so every error guard is exercised non-vacuously.
        fail_closed_cases = [
            ("empty_diff", [], [], {}),
            ("empty_pr_draft", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_draft": ""}),
            ("invalid_pr_draft", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_draft": "yes"}),
            ("empty_pr_has_run_ci", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_has_run_ci": ""}),
            ("invalid_pr_has_run_ci", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_has_run_ci": "1"}),
            ("missing_pr_base_sha", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_base_sha_override": ""}),
            ("invalid_pr_base_sha", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_base_sha_override": "0" * 40}),
            ("missing_pr_head_sha", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_head_sha_override": ""}),
            ("mismatched_pr_head_sha", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"pr_head_sha_override": "f" * 40}),
            ("missing_origin_main", [{"anneal/a.md": "a"}], [{"zerocopy/z.rs": "z"}], {"drop_origin_main": True}),
        ]
        for label, zc_batches, an_batches, kwargs in fail_closed_cases:
            with self.subTest(case=label):
                zc_out = self._run_detect_changes(self.ci_wf, "pull_request", zc_batches, **kwargs)
                an_out = self._run_detect_changes(self.anneal_wf, "pull_request", an_batches, **kwargs)
                self.assertEqual(zc_out["run_zerocopy"], "true")
                self.assertEqual(an_out["run_anneal"], "true")
                self.assertEqual(an_out["run_heavy"], "true")

    def test_all_jobs_succeed_gates_fail_closed(self):
        for wf_name, wf, env_flag, always_on, gated_sample in [
            (
                "ci.yml",
                self.ci_wf,
                "RUN_ZEROCOPY",
                {
                    "detect_changes",
                    "check_fmt",
                    "check_actions",
                    "check-job-dependencies",
                    "check-todo",
                    "test-tools",
                    "check-skills",
                    "run-git-hooks",
                    "zizmor",
                },
                "kani",
            ),
            (
                "anneal.yml",
                self.anneal_wf,
                "RUN_ANNEAL",
                {"detect_changes"},
                "current_anneal",
            ),
        ]:
            gate_steps = wf["jobs"]["all-jobs-succeed"]["steps"]
            self.assertTrue(
                any(
                    s.get("name") == "Reject workflow cancellation"
                    and s.get("if") == "${{ cancelled() }}"
                    for s in gate_steps
                ),
                wf_name,
            )
            gate_script = next(
                step["run"]
                for step in gate_steps
                if step.get("name") == "Require every dependency to succeed"
            )
            deps = wf["jobs"]["all-jobs-succeed"]["needs"]

            def eval_gate(event, run_flag, overrides=None, run_heavy=None):
                needs = {}
                for d in deps:
                    if run_flag == "true":
                        res = (
                            "skipped"
                            if (wf_name == "ci.yml" and d == "miri" and event == "pull_request")
                            else "success"
                        )
                    else:
                        res = "success" if d in always_on else "skipped"
                    needs[d] = {"result": res}
                if overrides:
                    for k, v in overrides.items():
                        needs[k] = {"result": v}
                env = os.environ.copy()
                env.update({
                    "EVENT_NAME": event,
                    env_flag: run_flag,
                    "NEEDS_JSON": json.dumps(needs),
                })
                if wf_name == "anneal.yml":
                    env["RUN_HEAVY"] = (
                        run_flag if run_heavy is None else run_heavy
                    )
                return subprocess.run(
                    [
                        "bash",
                        "--noprofile",
                        "--norc",
                        "-eo",
                        "pipefail",
                        "-c",
                        gate_script,
                    ],
                    env=env,
                    capture_output=True,
                    text=True,
                ).returncode

            self.assertEqual(eval_gate("pull_request", "true"), 0, wf_name)
            self.assertEqual(eval_gate("pull_request", "false"), 0, wf_name)
            self.assertEqual(eval_gate("merge_group", "true"), 0, wf_name)
            # Non-PR skip must fail closed.
            self.assertNotEqual(eval_gate("merge_group", "false"), 0, wf_name)
            self.assertNotEqual(eval_gate("push", "false"), 0, wf_name)
            self.assertNotEqual(eval_gate("workflow_dispatch", "false"), 0, wf_name)
            # Empty or malformed run_flag must fail closed even when
            # detect_changes reports success.
            self.assertNotEqual(eval_gate("pull_request", ""), 0, wf_name)
            self.assertNotEqual(eval_gate("pull_request", "unexpected"), 0, wf_name)
            # Failed detect_changes must fail closed even if run_flag is empty.
            self.assertNotEqual(
                eval_gate("pull_request", "", {"detect_changes": "failure"}),
                0,
                wf_name,
            )
            # Failed or cancelled gated job must fail closed for both flags.
            for run_flag in ("true", "false"):
                for bad in ("failure", "cancelled"):
                    self.assertNotEqual(
                        eval_gate("pull_request", run_flag, {gated_sample: bad}),
                        0,
                        f"{wf_name}:{run_flag}:{bad}",
                    )
            if wf_name == "ci.yml":
                # Miri skipped on push or merge_group must fail closed.
                for ev in ("push", "merge_group"):
                    self.assertNotEqual(
                        eval_gate(ev, "true", {"miri": "skipped"}),
                        0,
                        f"ci.yml:miri:{ev}",
                    )
            if wf_name == "anneal.yml":
                self.assertEqual(
                    eval_gate("pull_request", "true", run_heavy="false"),
                    0,
                )
                for bad_event, bad_anneal, bad_heavy in [
                    ("pull_request", "true", ""),
                    ("pull_request", "true", "unexpected"),
                    ("pull_request", "true", "True"),
                    ("pull_request", "false", ""),
                    ("pull_request", "false", "true"),
                    ("merge_group", "true", "false"),
                    ("push", "true", "false"),
                    ("workflow_dispatch", "true", "false"),
                    ("merge_group", "true", ""),
                    ("merge_group", "false", "false"),
                    ("push", "false", "false"),
                    ("workflow_dispatch", "false", "false"),
                ]:
                    self.assertNotEqual(
                        eval_gate(bad_event, bad_anneal, run_heavy=bad_heavy),
                        0,
                        f"anneal.yml:{bad_event}:{bad_anneal}:{bad_heavy}",
                    )
            # Skipped always-on job must fail closed.
            for job in always_on:
                self.assertNotEqual(
                    eval_gate("pull_request", "false", {job: "skipped"}),
                    0,
                    f"{wf_name}:{job}",
                )


if __name__ == "__main__":
    unittest.main()
