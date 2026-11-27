# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Qualification, publication, and GitHub release action contracts."""

from __future__ import annotations

from .support import (
    load_workflow,
    os,
    Path,
    PUBLISH_ACTION,
    subprocess,
    tempfile,
    WorkflowRepoFixture,
    WORKFLOWS,
)


class ReleaseContractCases:
    """Release contract tests of `ReleaseWorkflowTests`."""

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
