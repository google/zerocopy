# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests for `.github/workflows/anneal-perf.yml` and `.github/workflows/docs.yml`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import unittest

from anneal_ci_lib import WorkflowRepoFixture, find_workflow_step, load_workflow
import perf_tracking


CI_DIR = Path(__file__).resolve().parent
ANNEAL_DIR = CI_DIR.parent
WORKFLOW_PATH = ANNEAL_DIR.parent / ".github/workflows/anneal-perf.yml"
DOCS_WORKFLOW_PATH = ANNEAL_DIR.parent / ".github/workflows/docs.yml"
BUDGETS_PATH = CI_DIR / "perf_budgets.json"


def _make_record(sha_idx: int, unix_ts: int, subject: str = "Test") -> dict:
    sha = f"{sha_idx:040x}"
    return {
        "schema": perf_tracking.RECORD_SCHEMA,
        "commit": {
            "sha": sha,
            "short_sha": sha[:12],
            "timestamp": "2026-11-23T06:00:00Z",
            "unix_ts": unix_ts,
            "subject": subject,
            "branch": "main",
        },
        "environment": {
            "profile": "github-ubuntu-24.04-x86_64",
            "os": "Linux",
            "arch": "x86_64",
            "cpu_model": "AMD EPYC 7763 64-Core Processor",
            "vcpu_count": 4,
            "ram_total_kib": 16374212,
            "lean_version": "4.34.1",
            "rustc_version": "rustc 1.98.0-nightly",
        },
        "sampling": {
            "verify_repeats": 3,
            "aggregation": "median",
            "rss_method": "usr_bin_time",
        },
        "metrics": {
            "verify.scalar.cold_prebuilt_total_ms": 10000.0 + sha_idx,
            "memory_rss.verify_scalar.cold_prebuilt_maxrss_kib": 500000,
            "artifact_size.bundled_olean.total_bytes": 12000000,
            "zerocopy_proofs.suite.verified_units_count": 4,
        },
    }


class PerfWorkflowStaticTests(unittest.TestCase):
    def setUp(self):
        self.workflow = load_workflow(WORKFLOW_PATH)

    def test_triggers_permissions_and_concurrency_are_fork_safe(self):
        on_cfg = self.workflow["on"]
        self.assertEqual(on_cfg["push"], {"branches": ["main"]})
        self.assertEqual(on_cfg["schedule"], [{"cron": "17 04 * * *"}])
        self.assertEqual(on_cfg["workflow_dispatch"], {})
        for unsafe_trigger in (
            "pull_request",
            "pull_request_target",
            "issue_comment",
            "workflow_run",
        ):
            self.assertNotIn(unsafe_trigger, on_cfg)

        self.assertEqual(self.workflow["permissions"], {})
        self.assertEqual(
            self.workflow["concurrency"],
            {"group": "anneal-perf-tracking", "cancel-in-progress": "false"},
        )

    def test_job_pinning_env_stripping_and_token_scoping(self):
        jobs = self.workflow["jobs"]
        self.assertEqual(list(jobs.keys()), ["collect-and-publish"])
        job = jobs["collect-and-publish"]
        self.assertEqual(job["if"], "github.repository == 'google/zerocopy'")
        self.assertEqual(job["runs-on"], "ubuntu-24.04")
        self.assertEqual(job["timeout-minutes"], "45")
        self.assertEqual(job["permissions"], {"contents": "write"})
        for tok in (
            "ACTIONS_CACHE_URL",
            "ACTIONS_RESULTS_URL",
            "ACTIONS_RUNTIME_TOKEN",
            "ACTIONS_RUNTIME_URL",
        ):
            self.assertEqual(job["env"][tok], "")

        steps = job["steps"]
        sandbox = next(s for s in steps if s.get("id") == "sandbox")
        self.assertIn("bubblewrap", sandbox["run"])
        self.assertIn("/etc/apparmor.d/bwrap", sandbox["run"])
        self.assertIn("bwrap --unshare-all", sandbox["run"])
        self.assertIn("-- /true", sandbox["run"])
        checkout = next(s for s in steps if s.get("id") == "checkout")
        self.assertRegex(
            checkout["uses"],
            r"^actions/checkout@[0-9a-f]{40}$",
        )
        self.assertEqual(checkout["with"]["persist-credentials"], "false")

        nix = next(s for s in steps if s.get("id") == "nix")
        self.assertRegex(
            nix["uses"],
            r"^DeterminateSystems/determinate-nix-action@[0-9a-f]{40}$",
        )

        # `collect` must only collect+validate, `publish` must run next with
        # `GH_TOKEN` scoped strictly to it, and `check-budgets` must run last
        # without `GH_TOKEN`. No `${{ ... }}` expression may appear inside any
        # `run:` script.
        step_ids = [s.get("id") for s in steps]
        collect_idx = step_ids.index("collect")
        publish_idx = step_ids.index("publish")
        check_idx = step_ids.index("check-budgets")
        self.assertLess(collect_idx, publish_idx)
        self.assertEqual(publish_idx + 1, check_idx)
        self.assertEqual(check_idx, len(steps) - 1)

        collect = steps[collect_idx]
        self.assertIn("perf_tracking.py collect", collect["run"])
        self.assertIn("perf_tracking.py validate", collect["run"])
        self.assertNotIn("check-budgets", collect["run"])

        publish = steps[publish_idx]
        self.assertEqual(publish["env"]["GH_TOKEN"], "${{ github.token }}")

        check_budgets = steps[check_idx]
        self.assertIn("perf_tracking.py check-budgets", check_budgets["run"])
        self.assertIn("--budgets ci/perf_budgets.json", check_budgets["run"])

        for step in steps:
            if step.get("id") != "publish":
                self.assertNotIn("GH_TOKEN", step.get("env", {}))
            self.assertNotIn("${{", step.get("run", ""))

        manifest_step = next(s for s in steps if s.get("id") == "manifest")
        self.assertIn(
            "sha256sum --check --strict trusted/root-manifest.sha256",
            manifest_step["run"],
        )
        for forbidden in (".cargo", "rust-toolchain", "rust-toolchain.toml", ".gitmodules"):
            self.assertIn(forbidden, manifest_step["run"])


class PerfWorkflowPublishExecutionTests(unittest.TestCase):
    def setUp(self):
        self.workflow = load_workflow(WORKFLOW_PATH)
        self.publish_script = find_workflow_step(
            self.workflow, "collect-and-publish", step_id="publish"
        )["run"]
        self.check_budgets_script = find_workflow_step(
            self.workflow, "collect-and-publish", step_id="check-budgets"
        )["run"]

    def _run_publish(
        self,
        *,
        fx: WorkflowRepoFixture,
        bare_repo: Path,
        record: dict,
        tmp_root: Path,
        summary_path: Path,
    ):
        rec_path = tmp_root / "record.json"
        rec_path.write_text(json.dumps(record), encoding="utf-8")
        runner_temp = tmp_root / "runner_temp"
        runner_temp.mkdir(exist_ok=True)
        env = os.environ.copy()
        env.update(
            {
                "GH_TOKEN": "",
                "ORIGIN_URL": bare_repo.as_uri(),
                "REPO_REMOTE_URL": bare_repo.as_uri(),
                "RECORD_PATH": str(rec_path),
                "PROFILE_NAME": "github-ubuntu-24.04-x86_64",
                "RUNNER_TEMP": str(runner_temp),
                "GITHUB_STEP_SUMMARY": str(summary_path),
            }
        )
        return fx.run_bash(self.publish_script, cwd=ANNEAL_DIR, env=env, strict=False)

    def test_orphan_creation_cotenancy_idempotency_and_cas_retry(self):
        with WorkflowRepoFixture(prefix="anneal-perf-pub-") as fx:
            root = fx.root
            bare = fx.init_repo("remote.git", bare=True)
            summary = root / "step_summary.md"

            # 1. Initial creation on empty remote creates orphan benchmark-data.
            rec1 = _make_record(1, 1000, subject="First commit")
            res1 = self._run_publish(
                fx=fx, bare_repo=bare, record=rec1, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res1.returncode, 0, res1.stdout + res1.stderr)
            self.assertIn("First commit", summary.read_text(encoding="utf-8"))

            inspect = fx.clone_repo(bare, "inspect", branch="benchmark-data")
            self.assertTrue((inspect / "anneal/records.jsonl").is_file())
            self.assertTrue((inspect / "dashboard/anneal/index.html").is_file())
            self.assertTrue((inspect / "dashboard/anneal/data.json").is_file())

            # 2. Add pre-existing sibling Criterion dashboard files and verify
            # they survive subsequent publishes untouched.
            (inspect / "dashboard/index.html").write_text(
                "<html>Criterion</html>\n", encoding="utf-8"
            )
            (inspect / "dashboard/data.js").write_text(
                "window.BENCHMARK_DATA = {};\n", encoding="utf-8"
            )
            fx.git(inspect, "config", "user.name", "Test")
            fx.git(inspect, "config", "user.email", "t@example.com")
            fx.commit_all(
                inspect,
                "Add root dashboard",
                paths=("dashboard/index.html", "dashboard/data.js"),
            )
            fx.git(inspect, "push", "-q", "origin", "benchmark-data")

            # 3. Idempotent same-SHA rerun keeps exactly 1 record and preserves
            # sibling Criterion files.
            res_dup = self._run_publish(
                fx=fx, bare_repo=bare, record=rec1, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res_dup.returncode, 0, res_dup.stdout + res_dup.stderr)

            # 4. Concurrent-writer CAS retry: install a pre-receive hook that
            # commits a concurrent record on the first push attempt and rejects
            # attempt 1, forcing the publish script's CAS loop to re-fetch,
            # merge both records, and succeed on attempt 2.
            rec_concurrent = _make_record(2, 2000, subject="Concurrent commit")
            concurrent_work = fx.clone_repo(
                bare, "concurrent_work", branch="benchmark-data"
            )
            fx.git(concurrent_work, "config", "user.name", "Other")
            fx.git(concurrent_work, "config", "user.email", "o@example.com")
            perf_tracking.append_record(
                concurrent_work / "anneal/records.jsonl", rec_concurrent
            )
            concurrent_sha = fx.commit_all(
                concurrent_work, "Concurrent push", paths=("anneal/records.jsonl",)
            )
            fx.git(
                bare,
                "--git-dir",
                str(bare),
                "fetch",
                "--quiet",
                str(concurrent_work),
                f"{concurrent_sha}:refs/tmp/concurrent",
            )

            marker = root / "cas_hook_fired"
            fx.write_executable(
                bare / "hooks/pre-receive",
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "unset GIT_QUARANTINE_PATH\n"
                f"if [ ! -f '{marker}' ]; then\n"
                f"  touch '{marker}'\n"
                f"  git update-ref refs/heads/benchmark-data '{concurrent_sha}'\n"
                "  echo 'simulated concurrent push race' >&2\n"
                "  exit 1\n"
                "fi\n",
            )

            rec3 = _make_record(3, 3000, subject="Third commit")
            res_cas = self._run_publish(
                fx=fx, bare_repo=bare, record=rec3, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res_cas.returncode, 0, res_cas.stdout + res_cas.stderr)
            self.assertIn("conflicted; retrying", res_cas.stderr)

            fx.git(inspect, "fetch", "--quiet", "origin", "benchmark-data")
            fx.git(inspect, "checkout", "--quiet", "FETCH_HEAD")
            self.assertEqual(
                (inspect / "dashboard/index.html").read_text(encoding="utf-8"),
                "<html>Criterion</html>\n",
            )
            self.assertEqual(
                (inspect / "dashboard/data.js").read_text(encoding="utf-8"),
                "window.BENCHMARK_DATA = {};\n",
            )
            final_records = perf_tracking.load_records_jsonl(
                inspect / "anneal/records.jsonl"
            )
            self.assertEqual(
                [r["commit"]["sha"] for r in final_records],
                [rec1["commit"]["sha"], rec_concurrent["commit"]["sha"], rec3["commit"]["sha"]],
            )

    def test_ls_remote_error_surfaces_stderr_and_fails_closed(self):
        with WorkflowRepoFixture(prefix="anneal-perf-lsremote-") as fx:
            root = fx.root
            missing_remote = root / "nonexistent-remote.git"
            summary = root / "summary.md"
            res = self._run_publish(
                fx=fx,
                bare_repo=missing_remote,
                record=_make_record(1, 1000),
                tmp_root=root,
                summary_path=summary,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("Failed probing remote benchmark-data branch", res.stderr)
            self.assertIn("does not appear to be a git repository", res.stderr)

    def test_publish_persists_budget_breach_before_check_budgets_fails(self):
        with WorkflowRepoFixture(prefix="anneal-perf-breach-") as fx:
            root = fx.root
            bare = fx.init_repo("remote.git", bare=True)
            summary = root / "step_summary.md"

            breach_rec = _make_record(1, 1000, subject="Breach archive budget")
            breach_rec["metrics"]["artifact_size.archive.omnibus_tar_zst_bytes"] = (
                2_000_000_000
            )
            pub_res = self._run_publish(
                fx=fx, bare_repo=bare, record=breach_rec, tmp_root=root, summary_path=summary
            )
            self.assertEqual(pub_res.returncode, 0, pub_res.stdout + pub_res.stderr)
            self.assertIn("budget_breach", summary.read_text(encoding="utf-8"))

            inspect = fx.clone_repo(bare, "inspect", branch="benchmark-data")
            dash_data = json.loads(
                (inspect / "dashboard/anneal/data.json").read_text(encoding="utf-8")
            )
            self.assertEqual(len(dash_data["commits"]), 1)
            self.assertTrue(
                any(
                    a["kind"] == "budget_breach"
                    and a["metric"] == "artifact_size.archive.omnibus_tar_zst_bytes"
                    for a in dash_data["anomalies"]
                )
            )

            rec_path = fx.write_file("breach_record.json", json.dumps(breach_rec))
            env = os.environ.copy()
            env["RECORD_PATH"] = str(rec_path)
            chk_res = fx.run_bash(
                self.check_budgets_script, cwd=ANNEAL_DIR, env=env, strict=False
            )
            self.assertNotEqual(chk_res.returncode, 0)
            self.assertIn("BUDGET VIOLATION", chk_res.stderr)
            self.assertIn("omnibus_tar_zst_bytes", chk_res.stderr)

    def test_omnibus_budget_ceiling_accommodates_current_archive_with_headroom(self):
        budgets = json.loads(BUDGETS_PATH.read_text(encoding="utf-8"))
        rule = next(
            r
            for r in budgets["budgets"]
            if r.get("pattern") == "artifact_size.archive.omnibus_tar_zst_bytes"
        )
        self.assertEqual(rule["max_value"], 943_718_400)

        rec = _make_record(1, 1000)
        rec["metrics"]["artifact_size.archive.omnibus_tar_zst_bytes"] = 802_309_416
        with WorkflowRepoFixture(prefix="anneal-perf-ok-") as fx:
            rec_path = fx.write_file("record.json", json.dumps(rec))
            env = os.environ.copy()
            env["RECORD_PATH"] = str(rec_path)
            chk_res = fx.run_bash(
                self.check_budgets_script, cwd=ANNEAL_DIR, env=env, strict=False
            )
            self.assertEqual(chk_res.returncode, 0, chk_res.stdout + chk_res.stderr)


class DocsWorkflowStaticTests(unittest.TestCase):
    def setUp(self):
        self.workflow = load_workflow(DOCS_WORKFLOW_PATH)

    def test_triggers_permissions_and_perf_coordination(self):
        wr = self.workflow["on"]["workflow_run"]
        self.assertEqual(
            wr["workflows"],
            ["Build & Tests", "Anneal Tests", "Anneal Performance Tracking"],
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
        self.assertIn("for WORKFLOW in ci.yml anneal.yml", script)
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


class DocsWorkflowExecutionTests(unittest.TestCase):
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

    def _ci_fixtures(self, sha: str, *, anneal_status: str = "completed", anneal_conclusion: str = "success"):
        ci_run = {
            "id": 101,
            "name": "Build & Tests",
            "path": ".github/workflows/ci.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": "completed",
            "conclusion": "success",
            "updated_at": "2026-11-23T17:10:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/101",
        }
        anneal_run = {
            "id": 102,
            "name": "Anneal Tests",
            "path": ".github/workflows/anneal.yml",
            "event": "push",
            "head_branch": "main",
            "head_sha": sha,
            "head_repository": {"full_name": "google/zerocopy"},
            "status": anneal_status,
            "conclusion": anneal_conclusion,
            "updated_at": "2026-11-23T17:15:00Z",
            "html_url": "https://github.com/google/zerocopy/actions/runs/102",
        }
        return ci_run, anneal_run

    def test_perf_run_deploys_even_when_budget_check_fails_after_publish(self):
        sha = "a" * 40
        ci_run, anneal_run = self._ci_fixtures(sha)
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
            runs_by_id={101: ci_run, 102: anneal_run, 103: perf_run},
            workflow_runs={
                "ci.yml": [ci_run],
                "anneal.yml": [anneal_run],
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
            {"deploy": "true", "sha": sha, "anneal_run_id": "102"},
        )
        self.assertIn("publish=success", summary)

    def test_perf_run_skips_deploy_when_publish_did_not_succeed(self):
        sha = "b" * 40
        ci_run, anneal_run = self._ci_fixtures(sha)
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
            runs_by_id={101: ci_run, 102: anneal_run, 203: perf_run},
            workflow_runs={
                "ci.yml": [ci_run],
                "anneal.yml": [anneal_run],
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
        ci_run, anneal_run = self._ci_fixtures(
            sha, anneal_status="in_progress", anneal_conclusion=None
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
            runs_by_id={101: ci_run, 102: anneal_run, 303: perf_run},
            workflow_runs={
                "ci.yml": [ci_run],
                "anneal.yml": [anneal_run],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id=jobs,
        )
        self.assertEqual(res_wait.returncode, 0, res_wait.stdout + res_wait.stderr)
        self.assertEqual(outputs_wait, {})
        self.assertIn("Both CI workflows have not succeeded", summary_wait)

        # Once both CI workflows succeed on MAIN_SHA, schedule/workflow_dispatch perf deploys.
        _, anneal_ok = self._ci_fixtures(sha)
        res_ok, outputs_ok, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=303,
            runs_by_id={101: ci_run, 102: anneal_ok, 303: perf_run},
            workflow_runs={
                "ci.yml": [ci_run],
                "anneal.yml": [anneal_ok],
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
            runs_by_id={101: ci_run, 102: anneal_ok, 303: perf_run},
            workflow_runs={
                "ci.yml": [ci_run],
                "anneal.yml": [anneal_ok],
                "anneal-perf.yml": [perf_run],
            },
            jobs_by_run_id=jobs,
        )
        self.assertEqual(res_stale.returncode, 0, res_stale.stdout + res_stale.stderr)
        self.assertEqual(outputs_stale, {})
        self.assertIn("Refusing to replace", summary_stale)

    def test_spoofed_name_and_ci_pair_winner_deduplication(self):
        sha = "e" * 40
        ci_run, anneal_run = self._ci_fixtures(sha)
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
            runs_by_id={101: ci_run, 102: anneal_run, 999: spoofed_run},
            workflow_runs={"ci.yml": [ci_run], "anneal.yml": [anneal_run]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_spoof.returncode, 0, res_spoof.stdout + res_spoof.stderr)
        self.assertEqual(out_spoof, {})

        # Earlier CI run (101) defers to later Anneal run (102).
        res_ci, out_ci, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=101,
            runs_by_id={101: ci_run, 102: anneal_run},
            workflow_runs={"ci.yml": [ci_run], "anneal.yml": [anneal_run]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_ci.returncode, 0, res_ci.stdout + res_ci.stderr)
        self.assertEqual(out_ci, {})

        # Winning Anneal run (102) deploys.
        res_anneal, out_anneal, _ = self._run_coordinate(
            source_sha=sha,
            main_sha=sha,
            trigger_run_id=102,
            runs_by_id={101: ci_run, 102: anneal_run},
            workflow_runs={"ci.yml": [ci_run], "anneal.yml": [anneal_run]},
            jobs_by_run_id={},
        )
        self.assertEqual(res_anneal.returncode, 0, res_anneal.stdout + res_anneal.stderr)
        self.assertEqual(
            out_anneal,
            {"deploy": "true", "sha": sha, "anneal_run_id": "102"},
        )

    def test_perf_run_rejects_mismatched_repository_or_event(self):
        sha = "f" * 40
        ci_run, anneal_run = self._ci_fixtures(sha)
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
                    runs_by_id={101: ci_run, 102: anneal_run, 403: bad_perf},
                    workflow_runs={
                        "ci.yml": [ci_run],
                        "anneal.yml": [anneal_run],
                        "anneal-perf.yml": [bad_perf],
                    },
                    jobs_by_run_id=jobs,
                )
                self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
                self.assertEqual(out, {})
                self.assertIn("Ignoring non-main or incomplete performance run", summary)


if __name__ == "__main__":
    unittest.main()
