# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""First-parent and version history guards over simulated repositories."""

from __future__ import annotations

from .support import (
    os,
    Path,
    sha256_bytes,
    subprocess,
    tempfile,
)


class HistoryGuardCases:
    """History guard tests of `ReleaseWorkflowTests`."""

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
