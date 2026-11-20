# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Exercise Anneal and repository CI manifest, cache, and path-filter guards."""

import hashlib
import json
import os
from pathlib import Path
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
        for job_name in ("static-checks", "build-exocrate", "test-and-verify"):
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
        # Verify least-privilege & token-stripping posture on both jobs.
        for wf_name, wf in (("ci.yml", self.ci_wf), ("anneal.yml", self.anneal_wf)):
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

        cases = [
            # (label, event, commit_batches, exp_run_zerocopy, exp_run_anneal)
            ("anneal_only_pr", "pull_request", [{"anneal/README.md": "a"}], "false", "true"),
            ("anneal_only_2_commits", "pull_request", [{"anneal/a.md": "a"}, {"anneal/b.md": "b"}], "false", "true"),
            ("zerocopy_only_pr", "pull_request", [{"zerocopy/src/lib.rs": "z"}], "true", "false"),
            ("zerocopy_only_2_commits", "pull_request", [{"zerocopy/a.rs": "a"}, {"zerocopy/b.rs": "b"}], "true", "false"),
            ("allowed_root_non_anneal", "pull_request", [{"CONTRIBUTING.md": "c", "rustfmt.toml": "r"}], "true", "false"),
            ("exocrate_touches_both", "pull_request", [{"exocrate/src/lib.rs": "e"}], "true", "true"),
            ("workflow_touches_both", "pull_request", [{".github/workflows/ci.yml": "w"}], "true", "true"),
            ("ci_dir_touches_both", "pull_request", [{"ci/check_fmt.sh": "s"}], "true", "true"),
            ("githooks_touches_both", "pull_request", [{"githooks/pre-push": "h"}], "true", "true"),
            ("root_cargo_override", "pull_request", [{".cargo/config.toml": "x"}], "true", "true"),
            ("root_rust_toolchain_override", "pull_request", [{"rust-toolchain.toml": "n"}], "true", "true"),
            ("root_gitignore_touches_both", "pull_request", [{".gitignore": "g"}], "true", "true"),
            ("root_rgignore_touches_both", "pull_request", [{".rgignore": "r"}], "true", "true"),
            ("root_gemini_touches_both", "pull_request", [{".gemini/styleguide.md": "s"}], "true", "true"),
            ("root_vscode_touches_both", "pull_request", [{".vscode/settings.json": "{}"}], "true", "true"),
            ("mixed_pr", "pull_request", [{"anneal/a.txt": "a", "zerocopy/z.txt": "z"}], "true", "true"),
            (
                "stacked_pr_lower_zerocopy_upper_anneal",
                "pull_request",
                [{"zerocopy/src/lib.rs": "z"}, {"anneal/README.md": "a"}],
                "true",
                "true",
            ),
            (
                "stacked_pr_lower_anneal_upper_zerocopy",
                "pull_request",
                [{"anneal/README.md": "a"}, {"zerocopy/src/lib.rs": "z"}],
                "true",
                "true",
            ),
            ("push_always_runs_both", "push", [{"anneal/README.md": "a"}], "true", "true"),
            ("merge_group_always_runs_both", "merge_group", [{"zerocopy/src/lib.rs": "z"}], "true", "true"),
            ("workflow_dispatch_always_runs_both", "workflow_dispatch", [{"anneal/README.md": "a"}], "true", "true"),
        ]
        for label, event, batches, exp_zc, exp_an in cases:
            with self.subTest(case=label):
                zc_out = self._run_detect_changes(self.ci_wf, event, batches)
                an_out = self._run_detect_changes(self.anneal_wf, event, batches)
                self.assertEqual(zc_out["run_zerocopy"], exp_zc)
                self.assertEqual(an_out["run_anneal"], exp_an)

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

            def eval_gate(event, run_flag, overrides=None):
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
            # Skipped always-on job must fail closed.
            for job in always_on:
                self.assertNotEqual(
                    eval_gate("pull_request", "false", {job: "skipped"}),
                    0,
                    f"{wf_name}:{job}",
                )


if __name__ == "__main__":
    unittest.main()
