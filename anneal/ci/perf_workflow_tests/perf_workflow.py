# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workflow tests for the performance workflow."""

from __future__ import annotations

from .support import (
    ANNEAL_DIR,
    BUDGETS_PATH,
    find_workflow_step,
    json,
    load_workflow,
    _make_record,
    os,
    Path,
    perf_tracking,
    WORKFLOW_PATH,
    WorkflowRepoFixture,
)


class PerfWorkflowStaticCases:
    """`PerfWorkflowStaticTests` methods for the performance workflow's static
    structure."""

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


class PerfWorkflowPublishExecutionCases:
    """`PerfWorkflowPublishExecutionTests` methods for executing the performance
    workflow's publish step."""

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
