# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tests for `.github/workflows/anneal-perf.yml` security and CAS publishing."""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import stat
import subprocess
import tempfile
import unittest

import perf_tracking
from workflow_yaml import load_workflow_yaml


CI_DIR = Path(__file__).resolve().parent
ANNEAL_DIR = CI_DIR.parent
WORKFLOW_PATH = ANNEAL_DIR.parent / ".github/workflows/anneal-perf.yml"


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
        self.workflow = load_workflow_yaml(WORKFLOW_PATH.read_text(encoding="utf-8"))

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

        # GH_TOKEN must be scoped strictly to the final publish step, and no
        # `${{ ... }}` expression may appear inside any `run:` script.
        for step in steps[:-1]:
            self.assertNotIn("GH_TOKEN", step.get("env", {}))
            self.assertNotIn("${{", step.get("run", ""))
        publish = steps[-1]
        self.assertEqual(publish["id"], "publish")
        self.assertEqual(publish["env"]["GH_TOKEN"], "${{ github.token }}")
        self.assertNotIn("${{", publish["run"])

        manifest_step = next(s for s in steps if s.get("id") == "manifest")
        self.assertIn(
            "sha256sum --check --strict trusted/root-manifest.sha256",
            manifest_step["run"],
        )
        for forbidden in (".cargo", "rust-toolchain", "rust-toolchain.toml", ".gitmodules"):
            self.assertIn(forbidden, manifest_step["run"])


class PerfWorkflowPublishExecutionTests(unittest.TestCase):
    def setUp(self):
        self.workflow = load_workflow_yaml(WORKFLOW_PATH.read_text(encoding="utf-8"))
        self.publish_script = self.workflow["jobs"]["collect-and-publish"]["steps"][-1][
            "run"
        ]

    def _run_publish(
        self,
        *,
        bare_repo: Path,
        record: dict,
        tmp_root: Path,
        summary_path: Path,
    ) -> subprocess.CompletedProcess[str]:
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
        return subprocess.run(
            ["bash", "--noprofile", "--norc", "-c", self.publish_script],
            cwd=ANNEAL_DIR,
            env=env,
            capture_output=True,
            text=True,
        )

    def test_orphan_creation_cotenancy_idempotency_and_cas_retry(self):
        with tempfile.TemporaryDirectory(prefix="anneal-perf-pub-") as tmp:
            root = Path(tmp)
            bare = root / "remote.git"
            subprocess.run(["git", "init", "--bare", "-q", str(bare)], check=True)
            summary = root / "step_summary.md"

            # 1. Initial creation on empty remote creates orphan benchmark-data.
            rec1 = _make_record(1, 1000, subject="First commit")
            res1 = self._run_publish(
                bare_repo=bare, record=rec1, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res1.returncode, 0, res1.stdout + res1.stderr)
            self.assertIn("First commit", summary.read_text(encoding="utf-8"))

            inspect = root / "inspect"
            subprocess.run(
                [
                    "git",
                    "clone",
                    "--quiet",
                    "--branch",
                    "benchmark-data",
                    bare.as_uri(),
                    str(inspect),
                ],
                check=True,
            )
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
            subprocess.run(
                ["git", "-C", str(inspect), "config", "user.name", "Test"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(inspect), "config", "user.email", "t@example.com"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(inspect), "add", "dashboard/index.html", "dashboard/data.js"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(inspect), "commit", "-qm", "Add root dashboard"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(inspect), "push", "-q", "origin", "benchmark-data"],
                check=True,
            )

            # 3. Idempotent same-SHA rerun keeps exactly 1 record and preserves
            # sibling Criterion files.
            res_dup = self._run_publish(
                bare_repo=bare, record=rec1, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res_dup.returncode, 0, res_dup.stdout + res_dup.stderr)

            # 4. Concurrent-writer CAS retry: install a pre-receive hook that
            # commits a concurrent record on the first push attempt and rejects
            # attempt 1, forcing the publish script's CAS loop to re-fetch,
            # merge both records, and succeed on attempt 2.
            rec_concurrent = _make_record(2, 2000, subject="Concurrent commit")
            concurrent_work = root / "concurrent_work"
            subprocess.run(
                [
                    "git",
                    "clone",
                    "--quiet",
                    "--branch",
                    "benchmark-data",
                    bare.as_uri(),
                    str(concurrent_work),
                ],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(concurrent_work), "config", "user.name", "Other"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(concurrent_work), "config", "user.email", "o@example.com"],
                check=True,
            )
            perf_tracking.append_record(
                concurrent_work / "anneal/records.jsonl", rec_concurrent
            )
            subprocess.run(
                ["git", "-C", str(concurrent_work), "add", "anneal/records.jsonl"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(concurrent_work), "commit", "-qm", "Concurrent push"],
                check=True,
            )
            concurrent_sha = subprocess.check_output(
                ["git", "-C", str(concurrent_work), "rev-parse", "HEAD"],
                text=True,
            ).strip()
            subprocess.run(
                [
                    "git",
                    "--git-dir",
                    str(bare),
                    "fetch",
                    "--quiet",
                    str(concurrent_work),
                    f"{concurrent_sha}:refs/tmp/concurrent",
                ],
                check=True,
            )

            marker = root / "cas_hook_fired"
            hook = bare / "hooks/pre-receive"
            hook.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                "unset GIT_QUARANTINE_PATH\n"
                f"if [ ! -f '{marker}' ]; then\n"
                f"  touch '{marker}'\n"
                f"  git update-ref refs/heads/benchmark-data '{concurrent_sha}'\n"
                "  echo 'simulated concurrent push race' >&2\n"
                "  exit 1\n"
                "fi\n",
                encoding="utf-8",
            )
            hook.chmod(stat.S_IRWXU)

            rec3 = _make_record(3, 3000, subject="Third commit")
            res_cas = self._run_publish(
                bare_repo=bare, record=rec3, tmp_root=root, summary_path=summary
            )
            self.assertEqual(res_cas.returncode, 0, res_cas.stdout + res_cas.stderr)
            self.assertIn("conflicted; retrying", res_cas.stderr)

            subprocess.run(
                ["git", "-C", str(inspect), "fetch", "--quiet", "origin", "benchmark-data"],
                check=True,
            )
            subprocess.run(
                ["git", "-C", str(inspect), "checkout", "--quiet", "FETCH_HEAD"],
                check=True,
            )
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
        with tempfile.TemporaryDirectory(prefix="anneal-perf-lsremote-") as tmp:
            root = Path(tmp)
            missing_remote = root / "nonexistent-remote.git"
            summary = root / "summary.md"
            res = self._run_publish(
                bare_repo=missing_remote,
                record=_make_record(1, 1000),
                tmp_root=root,
                summary_path=summary,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("Failed probing remote benchmark-data branch", res.stderr)
            self.assertIn("does not appear to be a git repository", res.stderr)


if __name__ == "__main__":
    unittest.main()
