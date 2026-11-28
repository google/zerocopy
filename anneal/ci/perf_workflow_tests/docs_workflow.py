# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workflow tests for the docs workflow."""

from __future__ import annotations

from .support import (
    ANNEAL_DIR,
    DOCS_WORKFLOW_PATH,
    json,
    load_workflow,
    os,
    shutil,
    WorkflowRepoFixture,
)


class DocsWorkflowStaticCases:
    """`DocsWorkflowStaticTests` methods for the docs workflow's static
    structure."""

    def setUp(self):
        self.workflow = load_workflow(DOCS_WORKFLOW_PATH)

    def test_triggers_permissions_and_perf_coordination(self):
        wr = self.workflow["on"]["workflow_run"]
        self.assertEqual(
            wr["workflows"],
            ["CI (Trusted)", "Anneal Performance Tracking"],
        )
        self.assertEqual(wr["types"], ["completed"])
        self.assertEqual(wr["branches"], ["main"])
        self.assertEqual(self.workflow["permissions"], {})

        coord = self.workflow["jobs"]["coordinate"]
        self.assertIn("github.repository == 'google/zerocopy'", coord["if"])
        self.assertIn(
            "github.event.workflow_run.head_repository.full_name == github.repository",
            coord["if"],
        )
        self.assertIn("github.event.workflow_run.head_branch == 'main'", coord["if"])
        self.assertIn("Anneal Performance Tracking", coord["if"])
        self.assertNotIn("pull_request", coord["if"])

        script = coord["steps"][0]["run"]
        self.assertIn(".github/workflows/anneal-perf.yml", script)
        self.assertIn("workflows/anneal-perf.yml/runs", script)
        self.assertIn("Publish telemetry and dashboard", script)
        self.assertIn('PUBLISH_CONCLUSION" != "success"', script)
        self.assertIn("workflows/ci-core-trusted.yml/runs", script)
        self.assertIn("repos/$REPOSITORY/git/ref/heads/main", script)
        self.assertNotIn("${{", script)

        build = self.workflow["jobs"]["build"]
        self.assertEqual(build["needs"], "coordinate")
        self.assertEqual(build["if"], "needs.coordinate.outputs.deploy == 'true'")
        checkouts = [
            s
            for s in build["steps"]
            if s.get("uses", "").startswith("actions/checkout@")
        ]
        self.assertEqual(len(checkouts), 2)
        for co in checkouts:
            self.assertEqual(co["with"]["persist-credentials"], "false")
        self.assertEqual(checkouts[0]["with"]["ref"], "${{ needs.coordinate.outputs.sha }}")
        self.assertEqual(checkouts[1]["with"]["ref"], "benchmark-data")

        deploy = self.workflow["jobs"]["deploy"]
        self.assertEqual(deploy["needs"], ["coordinate", "build"])
        self.assertIn(
            "repos/$REPOSITORY/git/ref/heads/main", deploy["steps"][0]["run"]
        )
        self.assertNotIn("${{", deploy["steps"][0]["run"])


class DocsWorkflowExecutionCases:
    """`DocsWorkflowExecutionTests` methods for executing the docs workflow's
    coordination step."""

    def setUp(self):
        if shutil.which("jq") is None:
            self.skipTest("jq is required to execute docs.yml coordinate script")
        self.workflow = load_workflow(DOCS_WORKFLOW_PATH)
        self.coord_script = self.workflow["jobs"]["coordinate"]["steps"][0]["run"]

    def _run_coordinate(
        self,
        *,
        source_sha: str,
        main_sha: str,
        trigger_run_id: int,
        runs_by_id: dict[int, dict],
        workflow_runs: dict[str, list[dict]],
        jobs_by_run_id: dict[int, list[dict]],
    ):
        with WorkflowRepoFixture(prefix="anneal-docs-coord-") as fx:
            fixtures = {
                "main_sha": main_sha,
                "runs_by_id": {str(k): v for k, v in runs_by_id.items()},
                "workflow_runs": workflow_runs,
                "jobs_by_run_id": {str(k): v for k, v in jobs_by_run_id.items()},
            }
            fixtures_path = fx.write_file("fixtures.json", json.dumps(fixtures))
            fake_bin = fx.mkdir("bin")
            fx.write_executable(
                "bin/gh",
                f"""#!/usr/bin/env python3
import json, pathlib, sys
data = json.loads(pathlib.Path({str(fixtures_path)!r}).read_text())
args = sys.argv[1:]
jq_expr = None
if "--jq" in args:
    idx = args.index("--jq")
    jq_expr = args[idx + 1]
endpoint = next(a for a in args if a.startswith("repos/"))
if endpoint.endswith("/git/ref/heads/main"):
    payload = {{"object": {{"sha": data["main_sha"]}}}}
elif "/actions/runs/" in endpoint and endpoint.endswith("/jobs?per_page=100"):
    run_id = endpoint.split("/actions/runs/", 1)[1].split("/", 1)[0]
    payload = {{"jobs": data["jobs_by_run_id"].get(run_id, [])}}
elif "/actions/runs/" in endpoint:
    run_id = endpoint.split("/actions/runs/", 1)[1]
    payload = data["runs_by_id"][run_id]
elif "/actions/workflows/" in endpoint and "/runs" in endpoint:
    wf = endpoint.split("/actions/workflows/", 1)[1].split("/runs", 1)[0]
    payload = {{"workflow_runs": data["workflow_runs"].get(wf, [])}}
else:
    sys.stderr.write(f"unexpected endpoint: {{endpoint}}\\n")
    sys.exit(2)
raw = json.dumps(payload)
if jq_expr is not None:
    import subprocess
    res = subprocess.run(["jq", "-r", jq_expr], input=raw, text=True, check=True, capture_output=True)
    sys.stdout.write(res.stdout)
else:
    sys.stdout.write(raw)
""",
            )

            gh_output = fx.write_file("github_output.txt", "")
            gh_summary = fx.write_file("github_summary.md", "")

            env = os.environ.copy()
            env["PATH"] = f"{fake_bin}:{env['PATH']}"
            env["GH_TOKEN"] = "mock-token"
            env["REPOSITORY"] = "google/zerocopy"
            env["SOURCE_SHA"] = source_sha
            env["TRIGGER_RUN_ID"] = str(trigger_run_id)
            env["GITHUB_OUTPUT"] = str(gh_output)
            env["GITHUB_STEP_SUMMARY"] = str(gh_summary)

            res = fx.run_bash(
                self.coord_script, cwd=ANNEAL_DIR, env=env, strict=False
            )
            return (
                res,
                fx.parse_kv_file(gh_output, strict=False),
                gh_summary.read_text(encoding="utf-8"),
            )

    def _ci_fixtures(self, sha: str, *, status: str = "completed", conclusion: str = "success"):
        trusted_run = {
            "id": 102,
            "name": "CI (Trusted)",
            "path": ".github/workflows/ci-core-trusted.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": status,
            "conclusion": conclusion,
            "updated_at": "2026-11-23T17:15:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/102",
        }
        return trusted_run

    def test_perf_run_deploys_even_when_budget_check_fails_after_publish(self):
        sha = "a" * 40
        trusted_run = self._ci_fixtures(sha)
        perf_run = {
            "id": 103,
            "name": "Anneal Performance Tracking",
            "path": ".github/workflows/anneal-perf.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": "completed",
            "conclusion": "failure",
            "updated_at": "2026-11-23T17:20:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/103",
        }
        res, outputs, summary = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=103,
            runs_by_id={102: trusted_run, 103: perf_run},
            workflow_runs={
                "ci-core-trusted.yml": [trusted_run],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id={
                103: [
                    {
                        "name": "Collect and publish performance telemetry",
                        "steps": [
                            {"name": "Publish telemetry and dashboard", "conclusion": "success"},
                            {"name": "Check performance budgets", "conclusion": "failure"},
                        ],
                    }
                ]
            },
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertEqual(
            outputs,
            {"deploy": "true", "sha": sha},
        )
        self.assertIn("publish=success", summary)

    def test_perf_run_skips_deploy_when_publish_did_not_succeed(self):
        sha = "b" * 40
        trusted_run = self._ci_fixtures(sha)
        perf_run = {
            "id": 203,
            "name": "Anneal Performance Tracking",
            "path": ".github/workflows/anneal-perf.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": "completed",
            "conclusion": "failure",
            "updated_at": "2026-11-23T17:20:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/203",
        }
        res, outputs, summary = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=203,
            runs_by_id={102: trusted_run, 203: perf_run},
            workflow_runs={
                "ci-core-trusted.yml": [trusted_run],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id={
                203: [
                    {
                        "name": "Collect and publish performance telemetry",
                        "steps": [
                            {"name": "Collect and validate performance metrics", "conclusion": "failure"},
                            {"name": "Publish telemetry and dashboard", "conclusion": "skipped"},
                        ],
                    }
                ]
            },
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertEqual(outputs, {})
        self.assertIn("did not publish telemetry", summary)

    def test_perf_run_waits_for_ci_and_blocks_stale_main(self):
        sha = "c" * 40
        trusted_pending = self._ci_fixtures(
            sha, status="in_progress", conclusion=None
        )
        perf_run = {
            "id": 303,
            "name": "Anneal Performance Tracking",
            "path": ".github/workflows/anneal-perf.yml",
            "event": "schedule",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": "completed",
            "conclusion": "success",
            "updated_at": "2026-11-23T17:20:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/303",
        }
        jobs = {
            303: [
                {
                    "name": "Collect and publish performance telemetry",
                    "steps": [
                        {"name": "Publish telemetry and dashboard", "conclusion": "success"},
                    ],
                }
            ]
        }
        res_wait, outputs_wait, summary_wait = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=303,
            runs_by_id={102: trusted_pending, 303: perf_run},
            workflow_runs={
                "ci-core-trusted.yml": [trusted_pending],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id=jobs,
        )
        self.assertEqual(res_wait.returncode, 0, res_wait.stdout + res_wait.stderr)
        self.assertEqual(outputs_wait, {})
        self.assertIn("CI (Trusted) has not succeeded", summary_wait)

        # Once CI (Trusted) succeeds on MAIN_SHA, schedule/workflow_dispatch
        # perf deploys.
        trusted_ok = self._ci_fixtures(sha)
        res_ok, outputs_ok, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=303,
            runs_by_id={102: trusted_ok, 303: perf_run},
            workflow_runs={
                "ci-core-trusted.yml": [trusted_ok],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id=jobs,
        )
        self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)
        self.assertEqual(outputs_ok["deploy"], "true")

        # Stale SOURCE_SHA != MAIN_SHA must be rejected.
        res_stale, outputs_stale, summary_stale = self._run_coordinate(
            source_sha=sha,
            main_sha="d" * 40,
            trigger_run_id=303,
            runs_by_id={102: trusted_ok, 303: perf_run},
            workflow_runs={
                "ci-core-trusted.yml": [trusted_ok],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id=jobs,
        )
        self.assertEqual(res_stale.returncode, 0, res_stale.stdout + res_stale.stderr)
        self.assertEqual(outputs_stale, {})
        self.assertIn("Refusing to replace", summary_stale)

    def test_spoofed_name_and_latest_run_winner_deduplication(self):
        sha = "e" * 40
        older_trusted = self._ci_fixtures(sha)
        older_trusted["id"] = 101
        older_trusted["updated_at"] = "2026-11-23T17:10:00Z"
        newer_trusted = self._ci_fixtures(sha)
        spoofed_run = {
            "id": 999,
            "name": "Anneal Performance Tracking",
            "path": ".github/workflows/spoof.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": "completed",
            "conclusion": "success",
            "updated_at": "2026-11-23T17:30:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/999",
        }
        # Spoofed workflow path is rejected by WINNER_RUN_ID != TRIGGER_RUN_ID.
        res_spoof, out_spoof, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=999,
            runs_by_id={101: older_trusted, 102: newer_trusted, 999: spoofed_run},
            workflow_runs={"ci-core-trusted.yml": [older_trusted, newer_trusted]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_spoof.returncode, 0, res_spoof.stdout + res_spoof.stderr)
        self.assertEqual(out_spoof, {})

        # Superseded CI (Trusted) run (101) defers to latest run (102).
        res_old, out_old, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=101,
            runs_by_id={101: older_trusted, 102: newer_trusted},
            workflow_runs={"ci-core-trusted.yml": [older_trusted, newer_trusted]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_old.returncode, 0, res_old.stdout + res_old.stderr)
        self.assertEqual(out_old, {})

        # Winning CI (Trusted) run (102) deploys.
        res_new, out_new, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=102,
            runs_by_id={101: older_trusted, 102: newer_trusted},
            workflow_runs={"ci-core-trusted.yml": [older_trusted, newer_trusted]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_new.returncode, 0, res_new.stdout + res_new.stderr)
        self.assertEqual(
            out_new,
            {"deploy": "true", "sha": sha},
        )

    def test_perf_run_rejects_mismatched_repository_or_event(self):
        sha = "f" * 40
        trusted_run = self._ci_fixtures(sha)
        jobs = {
            403: [
                {
                    "name": "Collect and publish performance telemetry",
                    "steps": [
                        {"name": "Publish telemetry and dashboard", "conclusion": "success"},
                    ],
                }
            ]
        }
        for label, overrides in (
            ("fork_repo", {"head_repository": {"full_name": "fork/zerocopy"}}),
            ("pr_event", {"event": "pull_request"}),
        ):
            with self.subTest(label=label):
                bad_perf = {
                    "id": 403,
                    "name": "Anneal Performance Tracking",
                    "path": ".github/workflows/anneal-perf.yml",
                    "event": "push",
                    "head_branch": "main",
                    "head_sha": sha,
                    "head_repository": {"full_name": "google/zerocopy"},
                    "status": "completed",
                    "conclusion": "success",
                    "updated_at": "2026-11-23T17:25:00Z",
                    "html_url": "https://github.com/google/zerocopy/actions/runs/403",
                }
                bad_perf.update(overrides)
                res, out, summary = self._run_coordinate(
                    source_sha=sha,
                    main_sha=sha,
                    trigger_run_id=403,
                    runs_by_id={102: trusted_run, 403: bad_perf},
                    workflow_runs={
                        "ci-core-trusted.yml": [trusted_run],
                        "anneal-perf.yml": [bad_perf],
                    },
                    jobs_by_run_id=jobs,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertEqual(out, {})
                self.assertIn("Ignoring non-main or incomplete performance run", summary)
