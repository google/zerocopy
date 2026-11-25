# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Audit Anneal release workflow triggers, privilege boundaries, and scripts."""

from __future__ import annotations

import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

from anneal_ci_lib import WorkflowRepoFixture, load_workflow, sha256_bytes


WORKFLOWS = Path(__file__).resolve().parents[2] / ".github/workflows"
PUBLISH_ACTION = "./.github/actions/publish-github-release"
UPLOAD_ACTION = "./.github/actions/upload-file-artifact"
DOWNLOAD_ACTION = "./.github/actions/download-artifact-with-retry"
SHA_PINNED_ACTION_RE = re.compile(
    r"\A[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+@[0-9a-f]{40}\Z"
)

ANNEAL_JOBS = (
    "anneal-build-archive",
    "anneal-host-archive",
    "anneal-qualify-package",
    "anneal-publish-crate",
    "anneal-publish-github",
)
STRIPPED_RUNTIME_VARS = (
    "ACTIONS_CACHE_URL",
    "ACTIONS_RESULTS_URL",
    "ACTIONS_RUNTIME_TOKEN",
    "ACTIONS_RUNTIME_URL",
)
STRIPPED_OIDC_VARS = (
    "ACTIONS_ID_TOKEN_REQUEST_URL",
    "ACTIONS_ID_TOKEN_REQUEST_TOKEN",
)


class ReleaseWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.workflow = load_workflow(WORKFLOWS / "release.yml")
        cls.preparation = load_workflow(WORKFLOWS / "release-crate-version.yml")
        cls.jobs = cls.workflow["jobs"]

    def test_zerocopy_coexistence_and_shared_manual_entry_point(self) -> None:
        events = self.workflow["on"]
        self.assertEqual(set(events), {"push", "workflow_dispatch"})
        self.assertEqual(self.workflow["permissions"], {})
        self.assertEqual(events["push"]["branches"], ["main"])
        self.assertEqual(
            events["push"]["paths"],
            ["zerocopy/Cargo.toml", "zerocopy/zerocopy-derive/Cargo.toml"],
        )
        self.assertNotIn("check-anneal-release", self.jobs)

        inputs = events["workflow_dispatch"]["inputs"]
        self.assertEqual(inputs["project"]["options"], ["zerocopy", "anneal"])
        self.assertEqual(inputs["project"]["default"], "zerocopy")
        self.assertEqual(inputs["branch"]["default"], "main")
        self.assertEqual(inputs["commit"]["required"], "false")
        self.assertEqual(inputs["commit"]["default"], "")

        self.assertEqual(
            set(self.preparation["on"]), {"workflow_dispatch", "workflow_call"}
        )
        zerocopy = self.jobs["prepare-zerocopy"]
        self.assertEqual(
            zerocopy["uses"], "./.github/workflows/release-crate-version.yml"
        )
        self.assertEqual(zerocopy["with"]["version"], "${{ inputs.version }}")
        self.assertEqual(
            set(zerocopy["secrets"]), {"GOOGLE_PR_CREATION_BOT_TOKEN"}
        )

        caller = self.jobs["anneal-build-archive"]
        self.assertNotIn("secrets", caller)
        self.assertEqual(caller["permissions"], {"contents": "read"})
        self.assertEqual(
            " ".join(caller["if"].split()),
            "github.event_name == 'workflow_dispatch' && inputs.project == 'anneal'"
            " && github.repository == 'google/zerocopy'",
        )

    def test_five_job_dag_permissions_and_environment_isolation(self) -> None:
        expected_permissions = {
            "anneal-build-archive": {"contents": "read"},
            "anneal-host-archive": {"contents": "write"},
            "anneal-qualify-package": {"contents": "read"},
            "anneal-publish-crate": {"contents": "read", "id-token": "write"},
            "anneal-publish-github": {
                "contents": "write",
                "issues": "read",
                "pull-requests": "read",
            },
        }
        expected_needs = {
            "anneal-host-archive": "anneal-build-archive",
            "anneal-qualify-package": [
                "anneal-build-archive",
                "anneal-host-archive",
            ],
            "anneal-publish-crate": "anneal-qualify-package",
            "anneal-publish-github": [
                "anneal-qualify-package",
                "anneal-publish-crate",
            ],
        }
        for name in ANNEAL_JOBS:
            with self.subTest(job=name):
                job = self.jobs[name]
                self.assertEqual(job["runs-on"], "ubuntu-24.04")
                self.assertEqual(job["permissions"], expected_permissions[name])
                self.assertNotIn("secrets", job)
                self.assertNotIn("continue-on-error", job)
                if name != "anneal-build-archive":
                    self.assertNotIn("if", job)
                    self.assertEqual(job["needs"], expected_needs[name])
                if name == "anneal-publish-crate":
                    self.assertEqual(job["environment"], "anneal-release")
                    self.assertNotEqual(
                        job["environment"], self.jobs["release"]["environment"]
                    )
                    self.assertEqual(
                        job["concurrency"],
                        {
                            "group": "anneal-publish",
                            "cancel-in-progress": "false",
                        },
                    )
                else:
                    self.assertNotIn("environment", job)
                for step in job["steps"]:
                    self.assertNotIn("continue-on-error", step)
                    self.assertNotIn("always(", step.get("if", ""))
                    uses = step.get("uses", "")
                    self.assertFalse(
                        uses.startswith("peter-evans/create-pull-request"),
                        f"unexpected PR bot action in {name}: {uses}",
                    )

    def test_zero_expression_interpolation_in_run_and_sha_pinned_actions(self) -> None:
        for job_name, job in self.jobs.items():
            for step in job.get("steps", []):
                with self.subTest(job=job_name, step=step.get("name", step.get("uses"))):
                    if "run" in step:
                        self.assertNotIn(
                            "${{",
                            step["run"],
                            f"{job_name} interpolates GitHub expression inside run:",
                        )
                        if job_name in ANNEAL_JOBS:
                            self.assertNotRegex(
                                step["run"],
                                r"\|\s*grep\b",
                                f"{job_name} pipes into grep under pipefail (SIGPIPE hazard)",
                            )
                    if "uses" in step:
                        uses = step["uses"]
                        if uses.startswith("./"):
                            self.assertTrue(uses.startswith("./.github/"))
                        else:
                            self.assertRegex(uses, SHA_PINNED_ACTION_RE)

    def test_checkouts_fetch_depth_artifact_id_wiring_and_token_stripping(self) -> None:
        for name in ANNEAL_JOBS:
            with self.subTest(job=name):
                job = self.jobs[name]
                [checkout] = [
                    step
                    for step in job["steps"]
                    if step.get("uses", "").startswith("actions/checkout@")
                ]
                self.assertNotIn("repository", checkout["with"])
                # Every Anneal job checks out the dispatched workflow revision
                # (`github.sha`) into `$GITHUB_WORKSPACE` so composite actions
                # and workflow-coupled scripts execute at `github.sha` rather
                # than a historical target commit `C`.
                self.assertEqual(
                    checkout["with"].get("ref"), "${{ github.sha }}"
                )
                self.assertEqual(
                    checkout["with"]["persist-credentials"], "false"
                )
                self.assertEqual(checkout["with"].get("fetch-depth"), "0")
                for step in job["steps"]:
                    if "run" in step:
                        self.assertNotRegex(
                            step["run"],
                            r"(?m)^\s*git checkout\b",
                            f"{name} mutates $GITHUB_WORKSPACE HEAD via git checkout",
                        )

        # Verify immutable numeric `artifact_id` wiring between Jobs 1 and 2,
        # and zero `download-artifact` steps in Jobs 3, 4, and 5.
        build_job = self.jobs["anneal-build-archive"]
        self.assertEqual(
            build_job["outputs"]["artifact_id"],
            "${{ steps.upload.outputs.artifact-id }}",
        )
        [upload_step] = [
            s for s in build_job["steps"] if s.get("uses") == UPLOAD_ACTION
        ]
        self.assertEqual(upload_step["id"], "upload")
        self.assertEqual(
            upload_step["with"]["name"], "anneal-toolchain-linux-x86_64.tar.zst"
        )

        host_job = self.jobs["anneal-host-archive"]
        [download_step] = [
            s for s in host_job["steps"] if s.get("uses") == DOWNLOAD_ACTION
        ]
        self.assertEqual(
            download_step["with"]["artifact-id"],
            "${{ needs.anneal-build-archive.outputs.artifact_id }}",
        )
        self.assertEqual(
            download_step["with"]["expected-file"],
            "anneal-toolchain-linux-x86_64.tar.zst",
        )

        for downstream in (
            "anneal-qualify-package",
            "anneal-publish-crate",
            "anneal-publish-github",
        ):
            for step in self.jobs[downstream]["steps"]:
                uses = step.get("uses", "")
                self.assertNotIn("download-artifact", uses)

        # Verify runtime/cache token stripping after checkout on every Anneal
        # job, plus OIDC request token stripping on every `run:` step in Job 4.
        for name in ANNEAL_JOBS:
            job = self.jobs[name]
            job_env = job.get("env", {})
            steps = job["steps"]
            checkout_idx = next(
                i
                for i, s in enumerate(steps)
                if s.get("uses", "").startswith("actions/checkout@")
            )
            for step in steps[checkout_idx + 1 :]:
                if "run" not in step:
                    continue
                if step.get("id") == "emit":
                    continue
                merged_env = {**job_env, **step.get("env", {})}
                for var in STRIPPED_RUNTIME_VARS:
                    self.assertEqual(
                        merged_env.get(var),
                        "",
                        f"{name}/{step.get('name')!r} must strip {var}",
                    )
                if name == "anneal-publish-crate":
                    for oidc_var in STRIPPED_OIDC_VARS:
                        self.assertEqual(
                            merged_env.get(oidc_var),
                            "",
                            f"{name}/{step.get('name')!r} must strip {oidc_var}",
                        )
                # `alpha_release.py` steps must never receive `GH_TOKEN`.
                if "alpha_release.py" in step["run"]:
                    self.assertNotIn("GH_TOKEN", merged_env)

    def test_qualification_publish_and_github_release_contracts(self) -> None:
        qualify = self.jobs["anneal-qualify-package"]
        env_steps = [
            s
            for s in qualify["steps"]
            if s.get("name") == "Check Anneal publishing environment protections"
        ]
        self.assertEqual(len(env_steps), 1)
        env_step = env_steps[0]
        self.assertNotIn("if", env_step)
        self.assertNotIn("GH_TOKEN", env_step.get("env", {}))
        self.assertNotIn("GH_TOKEN", env_step["run"])
        self.assertIn("curl -fsS --retry 3", env_step["run"])
        self.assertIn("/environments/anneal-release", env_step["run"])
        self.assertIn("required_reviewers", env_step["run"])
        self.assertIn("deployment-branch-policies", env_step["run"])

        by_id = {s["id"]: s for s in qualify["steps"] if "id" in s}
        qual_run = by_id["qualify"]["run"]
        self.assertIn(
            '"$GITHUB_WORKSPACE/anneal/ci/alpha_release.py" stamp \\\n'
            '  --repo "$target_src"',
            qual_run,
        )
        self.assertIn(
            "cargo run --locked -p cargo-anneal --example regenerate_bundle -- --root . --stage-package",
            qual_run,
        )
        self.assertIn(
            "trap 'rm -rf \"$target_src/anneal/trusted/cargo-anneal/packaged\"' EXIT",
            qual_run,
        )
        self.assertIn(
            "?? anneal/trusted/cargo-anneal/packaged/bundled_theory.json",
            qual_run,
        )
        self.assertIn("cargo package --locked --allow-dirty -p cargo-anneal", qual_run)
        self.assertIn(
            '"$GITHUB_WORKSPACE/anneal/ci/alpha_release.py" verify-crate',
            qual_run,
        )
        self.assertIn("anneal-rustc-capture", qual_run)
        self.assertGreaterEqual(qual_run.count('"$cli" setup'), 2)
        self.assertIn('"$target_src/anneal/ci/probe_alpha.py" --cli "$cli"', qual_run)

        pub_crate = self.jobs["anneal-publish-crate"]
        pub_steps = {s.get("id", s.get("name")): s for s in pub_crate["steps"]}
        precheck_run = pub_steps["precheck"]["run"]
        self.assertIn(
            '[[ ! "$QUALIFIED_SOURCE_SHA256" =~ ^[0-9a-f]{64}$ ]]',
            precheck_run,
        )
        self.assertIn(
            "invalid or unpinned QUALIFIED_SOURCE_SHA256",
            precheck_run,
        )
        self.assertIn(
            "--expected-source-sha256 \"$QUALIFIED_SOURCE_SHA256\"",
            precheck_run,
        )
        self.assertIn(
            "--wait-for-prior-tags-seconds 300",
            precheck_run,
        )
        self.assertIn(
            "--repo \"$target_src\"",
            precheck_run,
        )
        self.assertIn("--stage-package", precheck_run)
        self.assertIn(
            "?? anneal/trusted/cargo-anneal/packaged/bundled_theory.json",
            precheck_run,
        )
        self.assertIn('publish_src="$RUNNER_TEMP/publish-src"', precheck_run)
        self.assertIn('publish_target="$RUNNER_TEMP/publish-target"', precheck_run)
        self.assertEqual(precheck_run.count("verify-crate"), 2)
        self.assertIn(
            'rm -rf "$CARGO_TARGET_DIR/package/cargo-anneal-$VERSION.crate" "$target_src"',
            precheck_run,
        )
        pub_step = pub_steps["Publish the qualified package to crates.io"]
        pub_run = pub_step["run"]
        self.assertIn('cd "$RUNNER_TEMP/publish-src/anneal"', pub_run)
        self.assertIn("trap 'rm -rf \"$RUNNER_TEMP/publish-src/anneal/trusted/cargo-anneal/packaged\"' EXIT", pub_run)
        self.assertIn('test "$staged_status" = "$expected_status"', pub_run)
        self.assertIn(
            "?? anneal/trusted/cargo-anneal/packaged/bundled_theory.json",
            pub_run,
        )
        self.assertIn(
            "cargo publish --locked --no-verify --allow-dirty -p cargo-anneal --registry crates-io",
            pub_run,
        )
        verify_pub_step = pub_steps[
            "Verify published crate parity and crates.io checksum"
        ]
        self.assertEqual(
            verify_pub_step.get("if"),
            "steps.precheck.outputs.already_published == 'false'",
        )
        self.assertNotIn("CARGO_REGISTRY_TOKEN", verify_pub_step.get("env", {}))
        self.assertNotIn("GH_TOKEN", verify_pub_step.get("env", {}))
        self.assertNotIn("CARGO_TARGET_DIR", verify_pub_step.get("env", {}))
        self.assertIn("verify-published-crate", verify_pub_step["run"])
        self.assertNotIn("--crate", verify_pub_step["run"])
        self.assertIn('--version "$VERSION"', verify_pub_step["run"])
        self.assertIn('--commit "$COMMIT"', verify_pub_step["run"])
        self.assertIn('--sha256 "$ARCHIVE_SHA256"', verify_pub_step["run"])
        self.assertIn(
            '--expected-source-sha256 "$QUALIFIED_SOURCE_SHA256"',
            verify_pub_step["run"],
        )
        # Missing, non-hex, or all-zero `QUALIFIED_SOURCE_SHA256` must abort
        # `precheck` immediately before reaching `alpha_release.py`.
        with tempfile.TemporaryDirectory(prefix="anneal-precheck-guard-") as tmp:
            tmp_path = Path(tmp)
            runner_temp = tmp_path / "runner_temp"
            workspace = tmp_path / "workspace"
            sentinel = tmp_path / "alpha_release_reached"
            runner_temp.mkdir()
            (workspace / "anneal/ci").mkdir(parents=True)
            (workspace / "anneal/ci/alpha_release.py").write_text(
                "from pathlib import Path\n"
                f"Path({str(sentinel)!r}).write_text('reached\\n')\n"
                "print('already_published=false')\n",
                encoding="utf-8",
            )
            for bad_sha in ("", "0" * 64, "not-a-sha256"):
                with self.subTest(bad_sha=bad_sha):
                    sentinel.unlink(missing_ok=True)
                    empty_precheck = subprocess.run(
                        ["bash", "--noprofile", "--norc", "-c", precheck_run],
                        env={
                            "PATH": os.environ["PATH"],
                            "RUNNER_TEMP": str(runner_temp),
                            "GITHUB_WORKSPACE": str(workspace),
                            "QUALIFIED_SOURCE_SHA256": bad_sha,
                            "COMMIT": "a" * 40,
                            "VERSION": "0.2.0-alpha.7",
                            "ARCHIVE_SHA256": "b" * 64,
                        },
                        capture_output=True,
                        text=True,
                    )
                    self.assertNotEqual(empty_precheck.returncode, 0)
                    self.assertIn(
                        "invalid or unpinned QUALIFIED_SOURCE_SHA256",
                        empty_precheck.stderr,
                    )
                    self.assertFalse(sentinel.exists())

    def test_harness_target_separation_runs_scripts_from_github_sha(self) -> None:
        """Historical target commit `C` must stamp cleanly using `github.sha`'s
        `alpha_release.py` and `check_non_stable_version.sh` even if `C`'s own
        `ci/` scripts are older or incompatible."""
        repo_root = WORKFLOWS.parents[1]
        with tempfile.TemporaryDirectory(prefix="anneal-harness-sep-") as tmp:
            tmp_path = Path(tmp)
            workspace = tmp_path / "workspace"
            runner_temp = tmp_path / "runner_temp"
            runner_temp.mkdir()
            subprocess.run(
                ["git", "init", "-q", "--initial-branch=main", str(workspace)],
                check=True,
            )
            (workspace / "anneal/trusted/cargo-anneal").mkdir(parents=True)
            (workspace / "anneal/ci").mkdir(parents=True)
            (workspace / ".github").mkdir(parents=True)
            for rel in (
                "anneal/trusted/cargo-anneal/Cargo.toml",
                "anneal/Cargo.lock",
            ):
                (workspace / rel).write_bytes((repo_root / rel).read_bytes())
            # Commit `c_old` has a broken/older `alpha_release.py` and
            # `check_non_stable_version.sh` that always fail if executed.
            for script_rel in (
                "anneal/ci/alpha_release.py",
                "anneal/ci/check_non_stable_version.sh",
            ):
                bad_script = workspace / script_rel
                bad_script.write_text("#!/usr/bin/env bash\nexit 77\n", encoding="utf-8")
                bad_script.chmod(0o755)
            subprocess.run(["git", "add", "."], cwd=workspace, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "commit",
                    "-qm",
                    "c_old",
                ],
                cwd=workspace,
                check=True,
            )
            c_old = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=workspace, text=True
            ).strip()

            # Commit `github_sha` (`HEAD` of `workspace`) installs the current
            # release harness scripts on `main`.
            for rel in (
                "anneal/ci/alpha_release.py",
                "anneal/ci/check_non_stable_version.sh",
                ".github/release_notes.py",
            ):
                dst = workspace / rel
                dst.write_bytes((repo_root / rel).read_bytes())
                dst.chmod((repo_root / rel).stat().st_mode)
            subprocess.run(["git", "add", "."], cwd=workspace, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "commit",
                    "-qm",
                    "github_sha",
                ],
                cwd=workspace,
                check=True,
            )

            target_src = runner_temp / "target-src"
            subprocess.run(
                [
                    "git",
                    "-c",
                    "core.hooksPath=/dev/null",
                    "-c",
                    "core.fsmonitor=false",
                    "-c",
                    "init.defaultRefFormat=files",
                    "clone",
                    "--quiet",
                    "--local",
                    "--no-checkout",
                    str(workspace),
                    str(target_src),
                ],
                check=True,
            )
            subprocess.run(
                [
                    "git",
                    "-c",
                    "core.hooksPath=/dev/null",
                    "-c",
                    "core.fsmonitor=false",
                    "-C",
                    str(target_src),
                    "checkout",
                    "--quiet",
                    "--detach",
                    c_old,
                ],
                check=True,
            )
            subprocess.run(
                [
                    "python3",
                    "-I",
                    "-B",
                    str(workspace / "anneal/ci/alpha_release.py"),
                    "stamp",
                    "--repo",
                    str(target_src),
                    "--version",
                    "0.2.0-alpha.8",
                    "--commit",
                    c_old,
                    "--sha256",
                    "d" * 64,
                ],
                cwd=workspace,
                check=True,
            )
            # `$GITHUB_WORKSPACE` (`workspace`) remains completely clean at
            # `github_sha`.
            ws_status = subprocess.check_output(
                ["git", "status", "--porcelain", "--untracked-files=all"],
                cwd=workspace,
                text=True,
            ).strip()
            self.assertEqual(ws_status, "")

        announcement = self.jobs["anneal-publish-github"]
        self.assertEqual(
            announcement["env"]["RELEASE_COMMIT"],
            "${{ needs.anneal-qualify-package.outputs.commit }}",
        )
        self.assertEqual(
            announcement["env"]["RELEASE_TAG"],
            "anneal-v${{ needs.anneal-qualify-package.outputs.version }}",
        )
        self.assertEqual(
            announcement["env"]["TOOLCHAIN_TAG"],
            "${{ needs.anneal-qualify-package.outputs.toolchain_tag }}",
        )
        [notes_step] = [
            s
            for s in announcement["steps"]
            if s.get("name") == "Generate Anneal release notes"
        ]
        self.assertIn(
            'python3 -I -B .github/release_notes.py --tag "$RELEASE_TAG"',
            notes_step["run"],
        )
        self.assertIn('--target "$RELEASE_COMMIT" --path anneal', notes_step["run"])
        [gh_rel_step] = [
            s for s in announcement["steps"] if s.get("uses") == PUBLISH_ACTION
        ]
        self.assertEqual(
            gh_rel_step["with"],
            {
                "tag": "${{ env.RELEASE_TAG }}",
                "commit": "${{ env.RELEASE_COMMIT }}",
                "notes-file": "${{ runner.temp }}/release-notes.md",
            },
        )
        self.assertEqual(gh_rel_step["env"], {"GH_TOKEN": "${{ github.token }}"})

        zerocopy = self.jobs["release"]
        [zerocopy_publish] = [
            step for step in zerocopy["steps"] if step.get("uses") == PUBLISH_ACTION
        ]
        self.assertEqual(zerocopy["needs"], "check-version")
        self.assertEqual(zerocopy["environment"], "release")
        self.assertEqual(
            zerocopy["env"]["RELEASE_TAG"],
            "v${{ needs.check-version.outputs.version }}",
        )
        self.assertEqual(
            zerocopy_publish["with"],
            {
                "tag": "${{ env.RELEASE_TAG }}",
                "commit": "${{ github.sha }}",
                "notes-file": "${{ runner.temp }}/release-notes.md",
            },
        )
        self.assertEqual(zerocopy_publish["env"], {"GH_TOKEN": "${{ github.token }}"})

    def test_first_parent_guard_handles_large_history_without_sigpipe(self) -> None:
        host_job = self.jobs["anneal-host-archive"]
        [guard_step] = [
            s
            for s in host_job["steps"]
            if s.get("name") == "Verify first-parent commit ancestry and TCB manifest"
        ]
        # Replace only the network `git fetch` line while running the exact
        # `git rev-list --first-parent` + `grep -Fxq` + TCB guard logic on a
        # repository whose first-parent history exceeds the 64 KiB Linux pipe
        # buffer (`2000 * 41 > 65536` bytes), matching at line 1 (`HEAD`).
        script = guard_step["run"].replace(
            "git fetch --force origin \\\n"
            "  +refs/heads/main:refs/remotes/origin/main \\\n"
            "  '+refs/tags/anneal-*:refs/tags/anneal-*'",
            "true",
        )
        with tempfile.TemporaryDirectory(prefix="anneal-sigpipe-guard-") as tmp:
            tmp_path = Path(tmp)
            repo = tmp_path / "repo"
            runner_temp = tmp_path / "runner_temp"
            runner_temp.mkdir()
            (repo / "anneal/trusted").mkdir(parents=True)
            for name in ("Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"):
                (repo / "anneal" / name).write_text(f"# {name}\n", encoding="utf-8")
            manifest_lines = []
            for name in ("Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"):
                digest = sha256_bytes(
                    (repo / "anneal" / name).read_bytes()
                )
                manifest_lines.append(f"{digest}  {name}\n")
            (repo / "anneal/trusted/root-manifest.sha256").write_text(
                "".join(manifest_lines), encoding="utf-8"
            )
            subprocess.run(
                ["git", "init", "-q", "--initial-branch=main", str(repo)],
                check=True,
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "commit",
                    "-qm",
                    "c0",
                ],
                cwd=repo,
                check=True,
            )
            base_tree = subprocess.check_output(
                ["git", "rev-parse", "HEAD^{tree}"], cwd=repo, text=True
            ).strip()
            head_sha = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=repo, text=True
            ).strip()
            # Build 2,000 first-parent commits (>80 KiB of SHA lines) rapidly
            # via `git fast-import` so line-1 matches exercise >64 KiB output.
            fi_lines = []
            for idx in range(1, 2001):
                msg = f"c{idx}\n"
                fi_lines.append("commit refs/heads/main\n")
                fi_lines.append(f"mark :{idx}\n")
                fi_lines.append("committer T <t@e> 1700000000 +0000\n")
                fi_lines.append(f"data {len(msg)}\n{msg}")
                if idx == 1:
                    fi_lines.append(f"from {head_sha}\n")
                else:
                    fi_lines.append(f"from :{idx - 1}\n")
            subprocess.run(
                ["git", "fast-import", "--quiet"],
                cwd=repo,
                input="".join(fi_lines),
                text=True,
                check=True,
            )
            tip_sha = subprocess.check_output(
                ["git", "rev-parse", "refs/heads/main"], cwd=repo, text=True
            ).strip()
            subprocess.run(
                ["git", "update-ref", "refs/remotes/origin/main", tip_sha],
                cwd=repo,
                check=True,
            )
            unrelated_sha = subprocess.check_output(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "commit-tree",
                    base_tree,
                    "-m",
                    "orphan",
                ],
                cwd=repo,
                text=True,
            ).strip()

            ok = subprocess.run(
                ["bash", "--noprofile", "--norc", "-c", script],
                cwd=repo,
                env={
                    **os.environ,
                    "HARNESS_SHA": tip_sha,
                    "COMMIT": head_sha,
                    "RUNNER_TEMP": str(runner_temp),
                },
                capture_output=True,
                text=True,
            )
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            bad = subprocess.run(
                ["bash", "--noprofile", "--norc", "-c", script],
                cwd=repo,
                env={
                    **os.environ,
                    "HARNESS_SHA": tip_sha,
                    "COMMIT": unrelated_sha,
                    "RUNNER_TEMP": str(runner_temp),
                },
                capture_output=True,
                text=True,
            )
            self.assertNotEqual(bad.returncode, 0)

    def test_host_archive_draft_staging_and_digest_verification_simulation(self) -> None:
        host_job = self.jobs["anneal-host-archive"]
        [stage_step] = [
            s
            for s in host_job["steps"]
            if s.get("name")
            == "Stage draft prerelease, verify server SHA-256, and publish atomically"
        ]
        payload = b"simulated omnibus archive bytes"
        digest = sha256_bytes(payload)
        commit = "a" * 40
        toolchain_tag = f"anneal-toolchain-{commit[:12]}-{digest[:16]}"

        for server_digest, pre_existing_tag, expected_rc in (
            (f"sha256:{digest}", False, 0),
            (f"sha256:{digest}", True, 0),
            (f"sha256:{'f' * 64}", False, 1),
        ):
            with self.subTest(
                server_digest=server_digest, pre_existing_tag=pre_existing_tag
            ), tempfile.TemporaryDirectory(prefix="anneal-host-sim-") as tmp:
                tmp_path = Path(tmp)
                origin = tmp_path / "origin.git"
                work = tmp_path / "work"
                runner_temp = tmp_path / "runner_temp"
                (runner_temp / "anneal-alpha").mkdir(parents=True)
                (
                    runner_temp
                    / "anneal-alpha"
                    / "anneal-toolchain-linux-x86_64.tar.zst"
                ).write_bytes(payload)

                subprocess.run(
                    ["git", "init", "-q", "--bare", "--initial-branch=main", str(origin)],
                    check=True,
                )
                subprocess.run(
                    ["git", "init", "-q", "--initial-branch=main", str(work)],
                    check=True,
                )
                subprocess.run(
                    ["git", "remote", "add", "origin", str(origin)],
                    cwd=work,
                    check=True,
                )
                (work / "file.txt").write_text("x\n", encoding="utf-8")
                subprocess.run(["git", "add", "."], cwd=work, check=True)
                subprocess.run(
                    [
                        "git",
                        "-c",
                        "user.name=T",
                        "-c",
                        "user.email=t@e",
                        "commit",
                        "-qm",
                        "init",
                    ],
                    cwd=work,
                    check=True,
                )
                real_commit = subprocess.check_output(
                    ["git", "rev-parse", "HEAD"], cwd=work, text=True
                ).strip()
                real_tag = f"anneal-toolchain-{real_commit[:12]}-{digest[:16]}"
                if pre_existing_tag:
                    subprocess.run(
                        [
                            "git",
                            "-c",
                            "user.name=T",
                            "-c",
                            "user.email=t@e",
                            "tag",
                            "-a",
                            "-m",
                            "t",
                            real_tag,
                            real_commit,
                        ],
                        cwd=work,
                        check=True,
                    )

                calls_log = tmp_path / "calls.log"
                bin_dir = tmp_path / "bin"
                bin_dir.mkdir()
                (bin_dir / "gh").write_text(
                    "#!/usr/bin/env bash\n"
                    "set -euo pipefail\n"
                    "if [[ \"$1\" == auth ]]; then exit 0; fi\n"
                    f"printf 'gh %s\\n' \"$*\" >> '{calls_log}'\n"
                    "if [[ \"$*\" == *'releases?per_page=100'* ]]; then\n"
                    "  printf '777\\n'\n"
                    "elif [[ \"$*\" == *'-X DELETE'* ]]; then\n"
                    "  exit 0\n"
                    "elif [[ \"$*\" == *'-X POST repos/google/zerocopy/releases'* ]]; then\n"
                    "  printf '888\\n'\n"
                    "elif [[ \"$*\" == *'-X PATCH repos/google/zerocopy/releases/888'* ]]; then\n"
                    "  printf '{}\\n'\n"
                    "elif [[ \"$2\" == 'repos/google/zerocopy/releases/888' ]]; then\n"
                    f"  printf '{{\"draft\":true,\"prerelease\":true,\"assets\":[{{\"name\":\"anneal-toolchain-linux-x86_64.tar.zst\",\"state\":\"uploaded\",\"digest\":\"{server_digest}\"}}]}}\\n'\n"
                    "else\n"
                    f"  printf '{{\"draft\":false,\"prerelease\":true,\"assets\":[{{\"name\":\"anneal-toolchain-linux-x86_64.tar.zst\",\"state\":\"uploaded\",\"digest\":\"{server_digest}\"}}]}}\\n'\n"
                    "fi\n",
                    encoding="utf-8",
                )
                (bin_dir / "gh").chmod(0o755)
                (bin_dir / "curl").write_text(
                    "#!/usr/bin/env bash\n"
                    f"printf 'curl %s\\n' \"$*\" >> '{calls_log}'\n"
                    "printf '{}\\n'\n",
                    encoding="utf-8",
                )
                (bin_dir / "curl").chmod(0o755)

                env = {
                    **os.environ,
                    "PATH": f"{bin_dir}:{os.environ.get('PATH', '')}",
                    "GH_TOKEN": "secret-token",
                    "GITHUB_REPOSITORY": "google/zerocopy",
                    "RUNNER_TEMP": str(runner_temp),
                    "COMMIT": real_commit,
                    "TOOLCHAIN_TAG": real_tag,
                    "ARCHIVE_SHA256": digest,
                }
                result = subprocess.run(
                    ["bash", "--noprofile", "--norc", "-c", stage_step["run"]],
                    cwd=work,
                    env=env,
                    capture_output=True,
                    text=True,
                )
                self.assertEqual(
                    result.returncode,
                    expected_rc,
                    result.stdout + result.stderr,
                )
                logged = calls_log.read_text(encoding="utf-8")
                self.assertNotIn("secret-token", logged)
                self.assertIn("-X DELETE repos/google/zerocopy/releases/777", logged)
                self.assertIn("-f make_latest=false", logged)
                if expected_rc != 0:
                    self.assertNotIn("-X PATCH", logged)
                else:
                    self.assertIn(
                        "-X PATCH repos/google/zerocopy/releases/888 "
                        "-F draft=false -F prerelease=true -f make_latest=false",
                        logged,
                    )

    def test_shared_github_release_action_selects_status_and_retries(self) -> None:
        action_path = WORKFLOWS.parents[1] / PUBLISH_ACTION / "action.yml"
        action = load_workflow(action_path)
        [step] = action["runs"]["steps"]
        simulate_commands = """
git() {
  if [[ "$1" == ls-remote ]]; then
    if [[ -n "$REMOTE_COMMIT" ]]; then
      printf '%s\\t%s\\n' "$OBJECT_ID" "$3" "$REMOTE_COMMIT" "$4"
    fi
  else
    printf 'git %s\\n' "$*"
  fi
}
gh() {
  if [[ "$2" == view ]]; then
    [[ -n "$EXISTING" ]] || return 1
    printf '%s\\n' "$EXISTING"
  else
    printf '%s\\n' "$@"
  fi
}
"""
        commit = "1" * 40
        alpha = "anneal-v0.2.0-alpha.2"
        published = '{"isDraft":false,"isPrerelease":true}'
        for tag, remote, existing, expected_exit, expected_flags in (
            ("v0.8.64+build-with-hyphen", commit, "", 0, {"--latest"}),
            (alpha, "", "", 0, {"--prerelease", "--latest=false"}),
            (alpha, commit, published, 0, set()),
            (alpha, "3" * 40, published, 1, set()),
            (alpha, commit, '{"isDraft":true,"isPrerelease":true}', 1, set()),
        ):
            with self.subTest(
                tag=tag, remote=remote, existing=existing
            ), WorkflowRepoFixture() as fx:
                notes = fx.write_file("release-notes.md", "Release notes\n")
                result = fx.run_bash(
                    simulate_commands + step["run"],
                    env={
                        **os.environ,
                        "RELEASE_TAG": tag,
                        "RELEASE_COMMIT": commit,
                        "GITHUB_ACTION_PATH": str(action_path.parent),
                        "NOTES_FILE": str(notes),
                        "EXISTING": existing,
                        "REMOTE_COMMIT": remote,
                        "OBJECT_ID": "2" * 40,
                    },
                    shell=step["shell"],
                    strict=False,
                )
                self.assertEqual(result.returncode, expected_exit, result.stderr)
                git_writes = [
                    line
                    for line in result.stdout.splitlines()
                    if line.startswith("git ")
                ]
                if remote:
                    self.assertEqual(git_writes, [])
                else:
                    self.assertEqual(len(git_writes), 2)
                    self.assertIn(f"-- {tag} {commit}", git_writes[0])
                    self.assertTrue(
                        git_writes[1].endswith(f"push origin refs/tags/{tag}")
                    )
                args = [
                    line
                    for line in result.stdout.splitlines()
                    if not line.startswith("git ")
                ]
                if not existing:
                    self.assertEqual(args[:2], ["release", "create"])
                    self.assertIn("--verify-tag", args)
                    self.assertEqual(args[-2:], ["--", tag])
                else:
                    self.assertNotIn("create", args)
                self.assertEqual(
                    set(args) & {"--latest", "--latest=false", "--prerelease"},
                    expected_flags,
                )

    def test_version_history_guard_handles_tags_and_monorepo_moves(
        self,
    ) -> None:
        prep_job = self.preparation["jobs"]["release"]
        [guard_step] = [
            s
            for s in prep_job["steps"]
            if s.get("name") == "Reject versions already in Git history"
        ]
        script = guard_step["run"]

        with tempfile.TemporaryDirectory(prefix="anneal-ver-history-") as tmp:
            repo = Path(tmp) / "repo"
            subprocess.run(
                ["git", "init", "-q", "--initial-branch=main", str(repo)],
                check=True,
            )

            def git_commit(msg: str) -> None:
                subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
                subprocess.run(
                    [
                        "git",
                        "-c",
                        "user.name=T",
                        "-c",
                        "user.email=t@e",
                        "commit",
                        "-qm",
                        msg,
                    ],
                    cwd=repo,
                    check=True,
                )

            # Commit 1: pre-monorepo layout at repository root (`0.7.35`).
            (repo / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.7.35"\n',
                encoding="utf-8",
            )
            (repo / "zerocopy-derive").mkdir()
            (repo / "zerocopy-derive" / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy-derive"\nversion = "0.7.35"\n',
                encoding="utf-8",
            )
            git_commit("Pre-monorepo 0.7.35")

            # Commit 2: move crate under `zerocopy/`, deleting root Cargo.tomls.
            (repo / "Cargo.toml").unlink()
            (repo / "zerocopy-derive" / "Cargo.toml").unlink()
            (repo / "zerocopy-derive").rmdir()
            (repo / "zerocopy" / "zerocopy-derive").mkdir(parents=True)
            (repo / "zerocopy" / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.8.64"\n',
                encoding="utf-8",
            )
            (repo / "zerocopy" / "zerocopy-derive" / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy-derive"\nversion = "0.8.64"\n',
                encoding="utf-8",
            )
            git_commit("Monorepo 0.8.64")

            # Commit 3: current version `0.8.65` with release tag `v0.8.65`.
            (repo / "zerocopy" / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy"\nversion = "0.8.65"\n',
                encoding="utf-8",
            )
            (repo / "zerocopy" / "zerocopy-derive" / "Cargo.toml").write_text(
                '[package]\nname = "zerocopy-derive"\nversion = "0.8.65"\n',
                encoding="utf-8",
            )
            git_commit("Release 0.8.65")
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "tag",
                    "-a",
                    "v0.8.65",
                    "-m",
                    "v0.8.65",
                ],
                cwd=repo,
                check=True,
            )
            # Tag-only release without a matching Cargo.toml history entry.
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=T",
                    "-c",
                    "user.email=t@e",
                    "tag",
                    "-a",
                    "v0.8.66",
                    "-m",
                    "v0.8.66",
                ],
                cwd=repo,
                check=True,
            )

            for version, expect_rc, expected_err in (
                ("0.8.66", 1, "already has release tag v0.8.66"),
                ("0.8.65", 1, "already has release tag v0.8.65"),
                ("0.8.64", 1, "already appears in Git history"),
                ("0.7.35", 1, "already appears in Git history"),
                ("0.9.0", 0, ""),
            ):
                with self.subTest(version=version):
                    res = subprocess.run(
                        [
                            "bash",
                            "--noprofile",
                            "--norc",
                            "-euo",
                            "pipefail",
                            "-c",
                            script,
                        ],
                        cwd=repo,
                        env={**os.environ, "VERSION": version},
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(
                        res.returncode, expect_rc, res.stdout + res.stderr
                    )
                    if expected_err:
                        self.assertIn(expected_err, res.stderr)


if __name__ == "__main__":
    unittest.main()
