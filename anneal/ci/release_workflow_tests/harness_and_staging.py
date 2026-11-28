# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Harness and target separation, and simulated draft release staging."""

from __future__ import annotations

from .support import (
    os,
    Path,
    PUBLISH_ACTION,
    sha256_bytes,
    subprocess,
    tempfile,
    WORKFLOWS,
)


class HarnessAndStagingCases:
    """Harness and staging tests of `ReleaseWorkflowTests`."""

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
