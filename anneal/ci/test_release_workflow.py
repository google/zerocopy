# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check Anneal release triggers, permissions, and source binding."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from workflow_yaml import load_workflow_yaml


WORKFLOWS = Path(__file__).resolve().parents[2] / ".github/workflows"
PUBLISH_ACTION = "./.github/actions/publish-github-release"
MANIFEST = "anneal/trusted/cargo-anneal/Cargo.toml"


class ReleaseWorkflowTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.workflow = load_workflow_yaml((WORKFLOWS / "release.yml").read_text())
        cls.preparation = load_workflow_yaml((WORKFLOWS / "release-crate-version.yml").read_text())
        cls.jobs = cls.workflow["jobs"]

    def test_shared_manual_entry_point_routes_each_project(self):
        choice = self.workflow["on"]["workflow_dispatch"]["inputs"]["project"]
        self.assertEqual(choice["options"], ["zerocopy", "anneal"])
        self.assertEqual(choice["default"], "zerocopy")
        self.assertEqual(set(self.preparation["on"]), {"workflow_dispatch", "workflow_call"})
        zerocopy = self.jobs["prepare-zerocopy"]
        self.assertEqual(zerocopy["uses"], "./.github/workflows/release-crate-version.yml")
        self.assertEqual(zerocopy["with"]["version"], "${{ inputs.version }}")
        self.assertEqual(set(zerocopy["secrets"]), {"GOOGLE_PR_CREATION_BOT_TOKEN"})
        caller = self.jobs["anneal-build-archive"]
        self.assertNotIn("secrets", caller)
        self.assertEqual(caller["permissions"], {"contents": "read"})
        self.assertEqual(
            " ".join(caller["if"].split()),
            "github.event_name == 'workflow_dispatch' && inputs.project == 'anneal'"
            " && inputs.branch == 'main' && github.ref == 'refs/heads/main'"
            " && github.repository == 'google/zerocopy'",
        )

    def test_preparation_is_dispatched_and_publish_detection_runs_on_a_push(self):
        events = self.workflow["on"]
        self.assertEqual(set(events), {"push", "workflow_dispatch"})
        self.assertEqual(self.workflow["permissions"], {})
        self.assertEqual(events["push"]["branches"], ["main"])
        self.assertEqual(set(events["push"]["paths"]), {
            "zerocopy/Cargo.toml", "zerocopy/zerocopy-derive/Cargo.toml", MANIFEST,
        })
        self.assertEqual(
            " ".join(self.jobs["check-anneal-release"]["if"].split()),
            "github.event_name == 'push' && github.ref == 'refs/heads/main'"
            " && github.repository == 'google/zerocopy'",
        )

    def test_privileged_jobs_require_successful_read_only_jobs(self):
        for consumer, prerequisite, permissions in (
            ("anneal-host-archive", "anneal-build-archive", {"contents": "write"}),
            (
                "anneal-publish-crate",
                "anneal-qualify-package",
                {"contents": "read", "id-token": "write"},
            ),
        ):
            with self.subTest(job=consumer):
                job = self.jobs[consumer]
                producer = self.jobs[prerequisite]
                self.assertIn(job["needs"], (prerequisite, [prerequisite]))
                self.assertNotIn("if", job)
                self.assertEqual(job["permissions"], permissions)
                self.assertEqual(producer["permissions"], {"contents": "read"})
                for runner in (job, producer):
                    self.assertNotIn("continue-on-error", runner)
                    for step in runner["steps"]:
                        self.assertNotIn("continue-on-error", step)
                        self.assertNotIn("always(", step.get("if", ""))

    def test_publication_uses_qualified_revision_and_dedicated_environment(self):
        publisher = self.jobs["anneal-publish-crate"]
        self.assertEqual(publisher["environment"], "anneal-release")
        self.assertNotEqual(publisher["environment"], self.jobs["release"]["environment"])
        self.assertEqual(self.jobs["check-anneal-release"]["outputs"], {
            "version": "${{ steps.check.outputs.version }}",
            "commit": "${{ steps.check.outputs.commit }}",
        })
        self.assertEqual(self.jobs["anneal-qualify-package"]["outputs"], {
            "version": "${{ needs.check-anneal-release.outputs.version }}",
            "commit": "${{ needs.check-anneal-release.outputs.commit }}",
        })
        pinned_refs = {
            "anneal-qualify-package": "${{ needs.check-anneal-release.outputs.commit }}",
            "anneal-publish-crate": "${{ needs.anneal-qualify-package.outputs.commit }}",
        }
        for name in (
            "anneal-build-archive",
            "anneal-host-archive",
            "check-anneal-release",
            "anneal-qualify-package",
            "anneal-publish-crate",
        ):
            with self.subTest(job=name):
                [checkout] = [
                    step for step in self.jobs[name]["steps"]
                    if step.get("uses", "").startswith("actions/checkout@")
                ]
                self.assertNotIn("repository", checkout["with"])
                ref = checkout["with"].get("ref")
                if name in pinned_refs:
                    self.assertEqual(ref, pinned_refs[name])
                else:
                    self.assertIn(ref, (None, "${{ github.sha }}"))
                self.assertEqual(checkout["with"]["persist-credentials"], "false")
        [publish] = [step["run"] for step in publisher["steps"] if "run" in step]
        self.assertEqual(publish, "cargo publish --locked -p cargo-anneal --registry crates-io")

    def test_qualification_checks_environment_and_exercises_the_packaged_cli(self):
        detect = self.jobs["check-anneal-release"]
        [check] = [step for step in detect["steps"] if "run" in step]
        self.assertEqual(check["env"]["BEFORE"], "${{ github.event.before }}")
        self.assertIn('--changed-since "$BEFORE" >> "$GITHUB_OUTPUT"', check["run"])
        qualify = self.jobs["anneal-qualify-package"]
        self.assertEqual(qualify["needs"], "check-anneal-release")
        self.assertEqual(qualify["if"], "needs.check-anneal-release.outputs.commit != ''")
        self.assertEqual(qualify["runs-on"], "ubuntu-24.04")
        steps = qualify["steps"]
        [protections, package] = [step for step in steps if "run" in step]
        self.assertNotIn("if", protections)
        self.assertNotIn("if", package)
        self.assertIn("/environments/anneal-release", protections["run"])
        self.assertIn("required_reviewers", protections["run"])
        self.assertIn("deployment-branch-policies", protections["run"])
        self.assertIn("--require-pinned --archive-base", package["run"])
        self.assertIn("cargo package --locked -p cargo-anneal", package["run"])
        self.assertIn("ci/probe_alpha.py", package["run"])

    def test_anneal_github_release_uses_the_successfully_published_commit(self):
        announcement = self.jobs["anneal-publish-github"]
        self.assertEqual(announcement["needs"], [
            "anneal-qualify-package", "anneal-publish-crate",
        ])
        self.assertNotIn("if", announcement)
        self.assertNotIn("continue-on-error", announcement)
        self.assertEqual(announcement["permissions"], {
            "contents": "write", "issues": "read", "pull-requests": "read",
        })
        self.assertEqual(announcement["env"]["RELEASE_COMMIT"],
                         "${{ needs.anneal-qualify-package.outputs.commit }}")
        version = "${{ needs.anneal-qualify-package.outputs.version }}"
        self.assertEqual(announcement["env"]["RELEASE_TAG"], "anneal-v" + version)
        checkout, notes, publish = announcement["steps"]
        self.assertTrue(checkout["uses"].startswith("actions/checkout@"))
        self.assertEqual(checkout["with"], {
            "ref": "${{ github.sha }}", "fetch-depth": "0",
            "persist-credentials": "false",
        })
        self.assertIn('python3 .github/release_notes.py --tag "$RELEASE_TAG"', notes["run"])
        self.assertIn('--target "$RELEASE_COMMIT" --path anneal', notes["run"])
        self.assertEqual(publish["uses"], PUBLISH_ACTION)
        self.assertEqual(publish["with"], {
            "tag": "${{ env.RELEASE_TAG }}", "commit": "${{ env.RELEASE_COMMIT }}",
            "notes-file": "${{ runner.temp }}/release-notes.md",
        })
        zerocopy = self.jobs["release"]
        [zerocopy_publish] = [step for step in zerocopy["steps"] if step.get("uses") == PUBLISH_ACTION]
        self.assertEqual(zerocopy["env"]["RELEASE_TAG"], "v${{ needs.check-version.outputs.version }}")
        self.assertEqual(zerocopy_publish["with"]["tag"], "${{ env.RELEASE_TAG }}")
        self.assertEqual(zerocopy_publish["with"]["commit"], "${{ github.sha }}")

    def test_shared_github_release_action_selects_status_and_retries(self):
        action_path = WORKFLOWS.parents[1] / PUBLISH_ACTION / "action.yml"
        action = load_workflow_yaml(action_path.read_text())
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
            with self.subTest(tag=tag, remote=remote, existing=existing), tempfile.TemporaryDirectory() as directory:
                notes = Path(directory) / "release-notes.md"
                notes.write_text("Release notes\n")
                result = subprocess.run(
                    [step["shell"], "-c", simulate_commands + step["run"]],
                    env={**os.environ, "RELEASE_TAG": tag, "RELEASE_COMMIT": commit,
                         "GITHUB_ACTION_PATH": str(action_path.parent), "NOTES_FILE": str(notes),
                         "EXISTING": existing, "REMOTE_COMMIT": remote, "OBJECT_ID": "2" * 40},
                    capture_output=True, text=True,
                )
                self.assertEqual(result.returncode, expected_exit, result.stderr)
                git_writes = [line for line in result.stdout.splitlines() if line.startswith("git ")]
                if remote:
                    self.assertEqual(git_writes, [])
                else:
                    self.assertEqual(len(git_writes), 2)
                    self.assertIn(f"-- {tag} {commit}", git_writes[0])
                    self.assertTrue(git_writes[1].endswith(f"push origin refs/tags/{tag}"))
                args = [line for line in result.stdout.splitlines() if not line.startswith("git ")]
                if not existing:
                    self.assertEqual(args[:2], ["release", "create"])
                    self.assertIn("--verify-tag", args)
                    self.assertEqual(args[-2:], ["--", tag])
                else:
                    self.assertNotIn("create", args)
                self.assertEqual(set(args) & {"--latest", "--latest=false", "--prerelease"},
                                 expected_flags)

    def test_archive_source_and_release_pr_are_bound_to_the_prepared_commit(self):
        build = self.jobs["anneal-build-archive"]
        host = self.jobs["anneal-host-archive"]
        [stage] = [step["run"] for step in build["steps"] if step.get("id") == "prepare"]
        self.assertIn('git checkout --detach "$source"', stage)
        [recreate, upload] = [step["run"] for step in host["steps"] if "run" in step]
        self.assertIn('test "$source" = "$SOURCE_SHA"', recreate)
        self.assertIn('push origin "$SOURCE_SHA:refs/tags/$tag"', upload)
        self.assertIn('--archive-base "$target" --archive-tree "$SOURCE_SHA"', upload)
        [propose] = [
            step for step in host["steps"]
            if step.get("uses", "").startswith("peter-evans/create-pull-request@")
        ]
        self.assertEqual(propose["with"]["base"], "main")
        self.assertEqual(propose["with"]["add-paths"].splitlines(), [
            MANIFEST, "anneal/Cargo.lock", "anneal/trusted/root-manifest.sha256",
        ])


if __name__ == "__main__":
    unittest.main()
