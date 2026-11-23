# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `check_job_dependencies.sh` and `check_actions.sh`."""

import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import unittest


CI_DIR = Path(__file__).resolve().parent
SCRIPT = CI_DIR / "check_job_dependencies.sh"
CHECK_ACTIONS = CI_DIR / "check_actions.sh"

VALID_GATE_WORKFLOW = """\
on:
  pull_request:
jobs:
  build:
    runs-on: ubuntu-latest
    steps: []
  all-jobs-succeed:
    runs-on: ubuntu-latest
    needs: [build]
    steps: []
"""

VALID_DISPATCH_WORKFLOW = """\
'on':
  workflow_dispatch:
jobs:
  diagnose:
    runs-on: ubuntu-latest
    steps: []
"""


class CheckJobDependenciesTests(unittest.TestCase):
    def run_synthetic(
        self,
        *,
        anneal_yml: str = VALID_GATE_WORKFLOW,
        anneal_current_yml: str = VALID_GATE_WORKFLOW,
        extra_workflows: dict[str, str] | None = None,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory(prefix="anneal-job-deps-") as tmp:
            root = Path(tmp) / "repo"
            root_wf = root / ".github/workflows"
            anneal_dir = root / "anneal"
            anneal_wf = anneal_dir / ".github/workflows"
            anneal_ci = anneal_dir / "ci"
            root_wf.mkdir(parents=True)
            anneal_wf.mkdir(parents=True)
            anneal_ci.mkdir(parents=True)

            script_copy = anneal_ci / "check_job_dependencies.sh"
            shutil.copyfile(SCRIPT, script_copy)
            script_copy.chmod(script_copy.stat().st_mode | stat.S_IXUSR)

            (root_wf / "anneal.yml").write_text(anneal_yml, encoding="utf-8")
            (root_wf / "anneal-current.yml").write_text(
                anneal_current_yml, encoding="utf-8"
            )
            for name, content in (extra_workflows or {}).items():
                (anneal_wf / name).write_text(content, encoding="utf-8")

            env = os.environ.copy()
            env.pop("GITHUB_STEP_SUMMARY", None)
            if extra_env:
                env.update(extra_env)

            return subprocess.run(
                [str(script_copy)],
                cwd=anneal_dir,
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )

    def test_real_repo_workflows_pass(self):
        res = subprocess.run(
            [str(SCRIPT)],
            cwd=CI_DIR.parent,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_check_actions_includes_anneal_yml(self):
        text = CHECK_ACTIONS.read_text(encoding="utf-8")
        self.assertIn("../.github/workflows/anneal.yml", text)
        self.assertIn("../.github/workflows/anneal-current.yml", text)

    def test_valid_workflows_pass_for_map_sequence_and_scalar_on(self):
        cases = {
            "seq_pr.yml": (
                "on: [push, pull_request]\n"
                "jobs:\n"
                "  build: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
            "scalar_pr.yml": (
                "on: pull_request\n"
                "jobs:\n"
                "  build: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
            "scalar_call.yml": (
                "on: workflow_call\n"
                "jobs:\n"
                "  build: {}\n"
                "  all-jobs-succeed:\n"
                "    needs: [build]\n"
            ),
            "dispatch.yml": VALID_DISPATCH_WORKFLOW,
            "non_pr_seq.yml": "on: [push, pull_request_target]\njobs:\n  a: {}\n",
        }
        res = self.run_synthetic(extra_workflows=cases)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_malformed_yaml_fails_closed(self):
        res = self.run_synthetic(
            extra_workflows={"broken.yml": "on: [\njobs:\n  a: {}\n"}
        )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("failed to parse workflow YAML", res.stderr)

    def test_empty_yaml_fails_closed(self):
        res = self.run_synthetic(extra_workflows={"empty.yml": ""})
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("failed to parse workflow YAML", res.stderr)

    def test_sequence_on_omitting_job_fails_closed(self):
        res = self.run_synthetic(
            extra_workflows={
                "seq_missing.yml": (
                    "on: [pull_request]\n"
                    "jobs:\n"
                    "  build: {}\n"
                    "  lint: {}\n"
                    "  all-jobs-succeed:\n"
                    "    needs: [build]\n"
                )
            }
        )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("missing dependencies on some jobs: lint", res.stderr)

    def test_scalar_on_omitting_job_fails_closed(self):
        res = self.run_synthetic(
            extra_workflows={
                "scalar_missing.yml": (
                    "on: pull_request\n"
                    "jobs:\n"
                    "  build: {}\n"
                    "  lint: {}\n"
                    "  all-jobs-succeed:\n"
                    "    needs: [build]\n"
                )
            }
        )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("missing dependencies on some jobs: lint", res.stderr)

    def test_missing_all_jobs_succeed_fails_closed(self):
        for label, wf in (
            ("map_on", "on:\n  pull_request:\njobs:\n  build: {}\n"),
            ("seq_on", "on: [workflow_call]\njobs:\n  build: {}\n"),
            ("scalar_on", "on: pull_request\njobs:\n  build: {}\n"),
            ("empty_jobs", "on: pull_request\njobs: {}\n"),
        ):
            with self.subTest(case=label):
                res = self.run_synthetic(extra_workflows={"missing_gate.yml": wf})
                self.assertNotEqual(res.returncode, 0, res.stdout)
                self.assertIn("missing required all-jobs-succeed job", res.stderr)

    def test_anneal_yml_is_checked(self):
        bad_anneal = (
            "on:\n"
            "  pull_request:\n"
            "jobs:\n"
            "  current_anneal: {}\n"
            "  extra_job: {}\n"
            "  all-jobs-succeed:\n"
            "    needs: [current_anneal]\n"
        )
        res = self.run_synthetic(anneal_yml=bad_anneal)
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("anneal.yml", res.stderr)
        self.assertIn("extra_job", res.stderr)

    def test_scalar_needs_fails_closed(self):
        res = self.run_synthetic(
            extra_workflows={
                "scalar_needs.yml": (
                    "on: pull_request\n"
                    "jobs:\n"
                    "  build: {}\n"
                    "  all-jobs-succeed:\n"
                    "    needs: build\n"
                )
            }
        )
        self.assertNotEqual(res.returncode, 0, res.stdout)
        self.assertIn("must be a YAML sequence", res.stderr)

    def test_mikefarah_yq_v4_type_tags_supported(self):
        real_yq = shutil.which("yq")
        self.assertIsNotNone(real_yq)
        with tempfile.TemporaryDirectory(prefix="anneal-yq-shim-") as shim_tmp:
            shim_bin = Path(shim_tmp) / "yq"
            # Wrap the host `yq` and rewrite `type` outputs from jq names to
            # mikefarah/yq v4 YAML tags (`!!str`/`!!seq`/`!!map`/`!!null`).
            shim_bin.write_text(
                "#!/usr/bin/env python3\n"
                "import subprocess, sys\n"
                f"proc = subprocess.run([{real_yq!r}, *sys.argv[1:]], "
                "capture_output=True, text=True)\n"
                "out = proc.stdout\n"
                "if any('| type' in a for a in sys.argv[1:]):\n"
                "    mapping = {'string': '!!str', 'array': '!!seq', "
                "'object': '!!map', 'null': '!!null', 'boolean': '!!bool'}\n"
                "    out = '\\n'.join(mapping.get(line, line) for line in out.splitlines()) + ('\\n' if out else '')\n"
                "sys.stdout.write(out)\n"
                "sys.stderr.write(proc.stderr)\n"
                "sys.exit(proc.returncode)\n",
                encoding="utf-8",
            )
            shim_bin.chmod(stat.S_IRWXU)
            env_override = {"PATH": f"{shim_tmp}:{os.environ.get('PATH', '')}"}

            ok = self.run_synthetic(
                extra_workflows={
                    "seq_ok.yml": (
                        "on: [pull_request]\n"
                        "jobs:\n"
                        "  build: {}\n"
                        "  all-jobs-succeed:\n"
                        "    needs: [build]\n"
                    ),
                    "scalar_ok.yml": (
                        "on: workflow_call\n"
                        "jobs:\n"
                        "  build: {}\n"
                        "  all-jobs-succeed:\n"
                        "    needs: [build]\n"
                    ),
                },
                extra_env=env_override,
            )
            self.assertEqual(ok.returncode, 0, ok.stdout + ok.stderr)

            bad = self.run_synthetic(
                extra_workflows={
                    "seq_bad.yml": (
                        "on: [pull_request]\n"
                        "jobs:\n"
                        "  build: {}\n"
                        "  lint: {}\n"
                        "  all-jobs-succeed:\n"
                        "    needs: [build]\n"
                    )
                },
                extra_env=env_override,
            )
            self.assertNotEqual(bad.returncode, 0, bad.stdout)
            self.assertIn("lint", bad.stderr)


if __name__ == "__main__":
    unittest.main()
