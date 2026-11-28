# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The `anneal-pr-hygiene.yml` workflow that runs `check_pr_hygiene.py`."""

from .support import (
    find_workflow_step,
    load_workflow,
    os,
    re,
    REPO_ROOT,
    SOURCE,
    tomllib,
    WorkflowRepoFixture,
)


class PrHygieneWorkflowCases:
    """`check_pr_hygiene.py` reads Git history and PR event metadata, which
    `ci-core` sandboxes do not provide, so it runs in its own workflow. The
    job is required, but its diff and commit-message checks are waivable
    with a `Skip-pr-hygiene:` trailer on the PR's tip commit."""

    PATH = REPO_ROOT / ".github/workflows/anneal-pr-hygiene.yml"
    ON_PR = "github.event_name == 'pull_request'"
    ON_MERGE_GROUP = "github.event_name == 'merge_group'"

    def setUp(self):
        self.workflow = load_workflow(self.PATH)
        self.job = self.workflow["jobs"]["pr-hygiene"]
        self.step = find_workflow_step(
            self.workflow, "pr-hygiene", step_name="Run PR hygiene check"
        )

    def test_pr_hygiene_workflow_is_read_only(self):
        wf = self.workflow
        self.assertEqual(wf["name"], "Anneal PR Hygiene")
        self.assertEqual(wf["permissions"], {})
        # Merge group runs have no checkout, so no `anneal/` directory
        # exists for a workflow-level default to enter.
        self.assertNotIn("defaults", wf)
        self.assertEqual(list(wf["jobs"]), ["pr-hygiene"])
        job = self.job
        self.assertEqual(job["name"], "PR hygiene")
        self.assertEqual(job["runs-on"], "ubuntu-latest")
        self.assertEqual(job["permissions"], {"contents": "read"})
        self.assertNotIn("defaults", job)
        self.assertEqual(job["env"], {
            "ACTIONS_CACHE_URL": "",
            "ACTIONS_RESULTS_URL": "",
            "ACTIONS_RUNTIME_TOKEN": "",
            "ACTIONS_RUNTIME_URL": "",
        })

    def test_triggers_and_concurrency(self):
        wf = self.workflow
        self.assertEqual(set(wf["on"]), {"pull_request", "merge_group"})
        # `edited` re-checks retitled and retargeted PRs.
        self.assertEqual(
            wf["on"]["pull_request"],
            {"types": ["opened", "synchronize", "reopened", "edited"]},
        )
        self.assertIn(wf["on"]["merge_group"], (None, "", {}))
        # A merge group run must report for its exact commit.
        self.assertEqual(wf["concurrency"], {
            "group": "${{ github.workflow }}-${{ github.ref }}",
            "cancel-in-progress": "${{ " + self.ON_PR + " }}",
        })

    def test_every_pull_request_event_runs_the_full_check(self):
        # A fast path for description-only edits would let an edit replace
        # a failing result for the same head with a passing one.
        self.assertNotIn("github.event.changes", self.PATH.read_text())
        steps = self.job["steps"]
        self.assertEqual(
            [s.get("if") for s in steps],
            [self.ON_PR, self.ON_PR, self.ON_MERGE_GROUP],
        )
        checkout = steps[0]
        self.assertEqual(
            checkout["uses"],
            "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
        )
        # `merge_base(base, head)` needs history; no token may persist.
        self.assertEqual(
            checkout["with"],
            {"fetch-depth": "0", "persist-credentials": "false"},
        )
        self.assertIs(steps[1], self.step)
        self.assertEqual(self.step["working-directory"], "anneal")

    def test_merge_group_step_needs_no_checkout(self):
        step = self.job["steps"][2]
        self.assertEqual(step["name"], "Skip PR hygiene on merge groups")
        self.assertNotIn("uses", step)
        self.assertNotIn("working-directory", step)
        self.assertNotIn("${{", step["run"])
        with WorkflowRepoFixture(prefix="anneal-pr-hygiene-mq-") as fx:
            empty = fx.mkdir("workspace")
            res = fx.run_bash(step["run"], cwd=empty)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertIn("::notice::", res.stdout)

    def test_title_regex_matches_commit_policy(self):
        checks_cfg = tomllib.loads((REPO_ROOT / "ci/checks.toml").read_text())
        policy = checks_cfg["commit_policy"]["forbid_message_regex"]
        self.assertEqual(policy, r"\b[T]ODO\b")
        flags = re.findall(r"--forbid-pr-title-regex '([^']*)'",
                           self.step["run"])
        self.assertEqual(flags, [policy])
        # Title equality applies only to single-commit PRs and is checked
        # by publishing tooling, not here.
        self.assertNotIn("--pr-title ", self.step["run"])

    def test_pr_hygiene_step_reads_event_data_from_env(self):
        step = self.step
        # Event data reaches the script only through `env`, never by
        # template expansion inside `run`.
        self.assertNotIn("${{", step["run"])
        self.assertEqual(step["env"], {
            "PR_BASE_SHA": "${{ github.event.pull_request.base.sha }}",
            "PR_HEAD_SHA": "${{ github.event.pull_request.head.sha }}",
            "PR_AUTHOR_TYPE": "${{ github.event.pull_request.user.type }}",
            "PR_TITLE": "${{ github.event.pull_request.title }}",
        })
        self.assertIn("set -euo pipefail", step["run"])

    def test_pr_hygiene_step_behavior(self):
        step = self.step
        marker = "TO" + "DO"
        trailer = "Agent-authored-by: AI agent acting on joshlf's behalf"
        with WorkflowRepoFixture(prefix="anneal-pr-hygiene-step-") as fx:
            root = fx.init_repo("repo")
            project = fx.mkdir("repo/anneal")
            fx.write_bytes(
                "repo/anneal/ci/check_pr_hygiene.py",
                (SOURCE / "check_pr_hygiene.py").read_bytes(),
            )
            rules = (
                "<!-- code-review-rules:begin -->\nR\n"
                "<!-- code-review-rules:end -->\n"
            )
            fx.write_file("repo/anneal/AGENTS.md", rules)
            fx.write_file("repo/anneal/.gemini/styleguide.md", rules)
            base = fx.commit_all(root, "init")
            fx.write_file("repo/anneal/ci/new.py", "X = 1\n")
            head = fx.commit_all(root, "[ci] Add a file without a header")
            summary = fx.root / "summary.md"

            def run(author_type="User", title="[ci] Add a file", sha=None):
                env = os.environ.copy()
                env.pop("GITHUB_STEP_SUMMARY", None)
                env.update(
                    PR_BASE_SHA=base,
                    PR_HEAD_SHA=sha or head,
                    PR_AUTHOR_TYPE=author_type,
                    PR_TITLE=title,
                    GITHUB_STEP_SUMMARY=str(summary),
                )
                return fx.run_bash(step["run"], cwd=project, env=env)

            res = run()
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[header] anneal/ci/new.py", res.stderr)
            self.assertNotIn("--skip-commit-messages", res.stderr)
            res = run(author_type="Bot")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("skipped: --skip-commit-messages", res.stderr)
            res = run(title=f"[ci] Add a file ({marker})")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[pr-title-policy]", res.stderr)
            self.assertFalse(summary.exists())

            # The tip commit waives the header finding loudly.
            fx.git(root, "commit", "-q", "--amend", "-m",
                   "[ci] Add a file without a header\n\n"
                   "Skip-pr-hygiene: header -- Fixture without a header.\n"
                   f"{trailer}\n")
            waived = fx.git(root, "rev-parse", "HEAD").stdout.strip()
            res = run(sha=waived)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn("::warning file=anneal/ci/new.py,line=1,",
                          res.stdout)
            self.assertIn("Fixture without a header.", summary.read_text())
            # A waiver cannot cover the title policy.
            res = run(sha=waived, title=f"{marker}: header")
            self.assertEqual(res.returncode, 1, res.stdout + res.stderr)
            self.assertIn("[pr-title-policy]", res.stderr)
