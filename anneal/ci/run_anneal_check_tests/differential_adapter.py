# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests of the MIR differential adapter in `run_anneal_check.sh`."""

import os
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib

from run_anneal_check_tests.support import ANNEAL_ROOT, SCRIPT, shell_function


class DifferentialAdapterParityCases:
    def test_ws_test_overlays_miri_and_runs_check_mir_differential(
        self,
    ) -> None:
        script_text = SCRIPT.read_text(encoding="utf-8")
        ws_match = re.search(r"^\s*ws-test\)\n(.*?)^\s*;;", script_text, re.M | re.S)
        self.assertIsNotNone(ws_match)
        assert ws_match is not None
        ws_body = ws_match.group(1)
        self.assertIn("bin/miri bin/cargo-miri lib/rustlib/src", ws_body)
        self.assertIn("tar --no-same-owner -xzf /miri-overlay.tar.gz -C /out", ws_body)
        self.assertIn("--require-miri", ws_body)
        self.assertIn(
            "cargo build --locked --offline -p anneal-differential-tests",
            ws_body,
        )
        self.assertIn("ci/check_mir_differential.py", ws_body)
        self.assertIn("--expect-capture-source env_anneal_capture", ws_body)

        dockerfile = (
            ANNEAL_ROOT.parent / "ci" / "docker" / "anneal-tc.Dockerfile"
        ).read_text(encoding="utf-8")
        self.assertIn("anneal/tests/differential/Cargo.toml", dockerfile)
        self.assertIn("anneal/tests/differential/src/lib.rs", dockerfile)
        self.assertIn(
            "anneal/tests/differential/src/bin/anneal-diff.rs", dockerfile
        )

        checks = tomllib.loads(
            (ANNEAL_ROOT.parent / "ci" / "checks.toml").read_text(
                encoding="utf-8"
            )
        )
        tc_ctx = checks["images"]["anneal-tc"]["context"][0]["include"]
        self.assertIn("anneal/tests/differential/Cargo.toml", tc_ctx)
        ci_tests_check = next(
            c for c in checks["checks"] if c["id"] == "anneal-ci-tests"
        )
        ci_tests_globs = [
            pat
            for inp in ci_tests_check["inputs"]
            for pat in inp.get("include", [])
        ]
        self.assertIn("ci/docker/anneal-tc.Dockerfile", ci_tests_globs)

        codeowners = (ANNEAL_ROOT.parent / ".github" / "CODEOWNERS").read_text(
            encoding="utf-8"
        )
        self.assertIn(
            "/anneal/tests/differential/Cargo.toml @joshlf @jswrenn @mdittmer",
            codeowners,
        )

    def test_build_differential_check_args_prefers_ci_revision_or_git(self) -> None:
        fn_src = shell_function(
            SCRIPT.read_text(encoding="utf-8"), "build_differential_check_args"
        )

        def eval_args(cwd: Path, env_extra: dict[str, str]) -> list[str]:
            env = {k: v for k, v in os.environ.items() if not k.startswith("ANNEAL_DIFF_")}
            env.update(env_extra)
            proc = subprocess.run(
                [
                    "bash",
                    "-euo",
                    "pipefail",
                    "-c",
                    f"{fn_src}\nbuild_differential_check_args /bin/diff /tmp/diag\n"
                    'printf \'%s\\0\' "${DIFF_CHECK_ARGS[@]}"',
                ],
                cwd=cwd,
                env=env,
                capture_output=True,
                check=True,
            )
            return [s for s in proc.stdout.decode("utf-8").split("\0") if s]

        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd)
            # 1. Explicit CI revision vars emit `--commit-sha` /
            # `--commit-unix-ts` and `--perf-record-out` without
            # `--allow-unknown-git`.
            explicit = eval_args(
                root,
                {
                    "ANNEAL_DIFF_COMMIT_SHA": "ab" * 20,
                    "ANNEAL_DIFF_COMMIT_UNIX_TS": "1785000123",
                    "ANNEAL_DIFF_BRANCH": "pr-head",
                },
            )
            self.assertIn("--commit-sha", explicit)
            self.assertIn("ab" * 20, explicit)
            self.assertIn("--commit-unix-ts", explicit)
            self.assertIn("--branch=pr-head", explicit)
            self.assertIn("--perf-record-out", explicit)
            self.assertNotIn("--allow-unknown-git", explicit)

            # 2. `.git`-less sandbox without CI revision env falls back to
            # `--allow-unknown-git` cleanly and skips 1970 perf records.
            gitless = eval_args(root, {"PATH": "/usr/bin:/bin"})
            self.assertIn("--allow-unknown-git", gitless)
            self.assertIn("--branch=offline-ws-test", gitless)
            self.assertNotIn("--perf-record-out", gitless)

            # 3. Live git checkout uses git metadata without unknown-git.
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(
                ["git", "config", "user.name", "Test"], cwd=root, check=True
            )
            subprocess.run(
                ["git", "config", "user.email", "test@example.com"],
                cwd=root,
                check=True,
            )
            (root / "f.txt").write_text("x\n", encoding="utf-8")
            subprocess.run(["git", "add", "f.txt"], cwd=root, check=True)
            subprocess.run(
                ["git", "commit", "-q", "-m", "init"], cwd=root, check=True
            )
            with_git = eval_args(root, {})
            self.assertNotIn("--allow-unknown-git", with_git)
            self.assertIn("--perf-record-out", with_git)
            self.assertFalse(any("offline-ws-test" in a for a in with_git))

            # 4. Partial revision overrides fail closed in both `.git`-less
            # sandboxes and live Git checkouts instead of silently falling back.
            with tempfile.TemporaryDirectory() as gitless_tmp:
                for cwd in (Path(gitless_tmp), root):
                    for bad_env in (
                        {"ANNEAL_DIFF_COMMIT_SHA": "ab" * 20},
                        {"ANNEAL_DIFF_COMMIT_UNIX_TS": "1785000123"},
                        {
                            "ANNEAL_DIFF_COMMIT_SHA": "ab" * 20,
                            "ANNEAL_DIFF_COMMIT_UNIX_TS": "",
                        },
                        {
                            "ANNEAL_DIFF_COMMIT_SHA": "",
                            "ANNEAL_DIFF_COMMIT_UNIX_TS": "1785000123",
                        },
                        {
                            "ANNEAL_DIFF_COMMIT_SHA": "",
                            "ANNEAL_DIFF_COMMIT_UNIX_TS": "",
                        },
                    ):
                        with self.subTest(cwd=cwd.name, bad_env=bad_env):
                            env = {
                                k: v
                                for k, v in os.environ.items()
                                if not k.startswith("ANNEAL_DIFF_")
                            }
                            env.update(bad_env)
                            proc = subprocess.run(
                                [
                                    "bash",
                                    "-euo",
                                    "pipefail",
                                    "-c",
                                    f"{fn_src}\n"
                                    "build_differential_check_args /bin/diff /tmp/diag\n",
                                ],
                                cwd=cwd,
                                env=env,
                                capture_output=True,
                                text=True,
                                check=False,
                            )
                            self.assertNotEqual(proc.returncode, 0)
                            self.assertIn("must both be non-empty", proc.stderr)
