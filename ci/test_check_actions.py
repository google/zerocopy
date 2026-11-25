# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for local action/workflow link checks in `ci/check_actions.sh`."""

import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import tomllib
import unittest


REPO_ROOT = Path(__file__).resolve().parents[1]
CHECK_ACTIONS = REPO_ROOT / "ci" / "check_actions.sh"
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"


class CheckActionsLocalLinksTests(unittest.TestCase):
    def run_links_check(
        self,
        repo_root: Path,
        *,
        links_only: bool = True,
        extra_env: dict[str, str] | None = None,
    ) -> subprocess.CompletedProcess[str]:
        env = os.environ.copy()
        env["CHECK_ACTIONS_REPO_ROOT"] = str(repo_root)
        env.pop("CHECK_ACTIONS_LINKS_ONLY", None)
        env.pop("CHECK_ACTIONS_FORCE_YQ", None)
        if extra_env:
            env.update(extra_env)
        cmd = [str(CHECK_ACTIONS)]
        if links_only:
            cmd.append("--links-only")
        return subprocess.run(
            cmd,
            cwd=repo_root,
            env=env,
            capture_output=True,
            text=True,
            check=False,
        )

    def write_files(self, root: Path, files: dict[str, str]) -> None:
        for rel, content in files.items():
            path = root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")

    def test_real_repo_local_links_pass(self):
        res = self.run_links_check(REPO_ROOT)
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_valid_local_actions_and_reusable_workflows_pass(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/actions/act-yml/action.yml": (
                        "name: Act Yml\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/actions/act-yaml/action.yaml": (
                        "name: Act Yaml\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/actions/act-composite/action.yml": (
                        "name: Composite\n"
                        "runs:\n"
                        "  using: composite\n"
                        "  steps:\n"
                        "    - uses: ./.github/actions/act-yml\n"
                    ),
                    ".github/workflows/reusable.yml": (
                        "on:\n  workflow_call:\njobs:\n  noop:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/caller.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  call-reusable:\n"
                        "    uses: ./.github/workflows/reusable.yml # inline comment\n"
                        "  run-actions:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/act-yml\n"
                        "      - uses: './.github/actions/act-yaml/' # single-quoted\n"
                        "      - name: Nested\n"
                        '        "uses": "./.github/actions/act-composite" # quoted\n'
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_missing_local_action_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/does-not-exist\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/actions/does-not-exist", res.stderr)
            self.assertIn("ci.yml (jobs.build.steps[0].uses)", res.stderr)

    def test_local_action_dir_missing_manifest_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/actions/empty-action/README.md": "not an action\n",
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/empty-action\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/actions/empty-action", res.stderr)

    def test_missing_local_reusable_workflow_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/caller.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  call:\n"
                        "    uses: ./.github/workflows/missing-reusable.yml\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/workflows/missing-reusable.yml", res.stderr)

    def test_missing_local_action_inside_composite_action_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/actions/outer/action.yml": (
                        "name: Outer\n"
                        "runs:\n"
                        "  using: composite\n"
                        "  steps:\n"
                        "    - uses: ./.github/actions/missing-inner\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/actions/missing-inner", res.stderr)

    def test_external_actions_ignored(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  call-ext:\n"
                        "    uses: org/repo/.github/workflows/ext.yml@0123456789abcdef\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1\n"
                        "      - uses: docker://alpine:3.19\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_commented_out_and_block_scalar_uses_ignored(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      # uses: ./.github/actions/missing-comment\n"
                        "      # - uses: ./.github/workflows/missing.yml\n"
                        "      - name: Script containing example text\n"
                        "        run: |\n"
                        "          cat <<'EOF'\n"
                        "          uses: ./.github/actions/missing-in-heredoc\n"
                        "          EOF\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

    def test_excluded_files_and_invalid_local_paths_rejected(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/dependabot.yml": (
                        "uses: ./.github/actions/ignored-by-exclude\n"
                    ),
                    ".github/ISSUE_TEMPLATE/anneal.yml": (
                        "uses: ./.github/actions/ignored-by-exclude\n"
                    ),
                    ".github/actions/valid/action.yml": (
                        "name: Valid\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/workflows/ok.yml": (
                        "on: push\njobs:\n  a:\n    runs-on: ubuntu-latest\n"
                        "    steps:\n      - uses: ./.github/actions/valid\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            for idx, bad_target in enumerate(
                (
                    "./.github/actions/../../etc",
                    "../outside-action",
                    "./.github/actions//valid",
                    "./.github/actions/valid//",
                )
            ):
                wf = root / ".github/workflows/bad_path.yml"
                wf.write_text(
                    "on: push\n"
                    "jobs:\n"
                    "  a:\n"
                    "    runs-on: ubuntu-latest\n"
                    "    steps:\n"
                    f"      - uses: {bad_target}\n",
                    encoding="utf-8",
                )
                res_bad = self.run_links_check(root)
                self.assertNotEqual(res_bad.returncode, 0, f"case {idx}: {bad_target}")
                self.assertIn("invalid path", res_bad.stderr)

    def test_block_scalar_inside_list_item_does_not_swallow_sibling_uses(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - name: >-\n"
                        "          folded\n"
                        "        uses: ./.github/actions/missing1\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/actions/missing1", res.stderr)

    def test_flow_mappings_sequences_and_multiline_flow_checked(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    "tools/local-ok/action.yml": (
                        "name: Local\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/actions/flow-ok/action.yml": (
                        "name: Flow\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/workflows/ok.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps: [\n"
                        "      { name: 'step #1', uses: ./.github/actions/flow-ok },\n"
                        "      { name: 'step #2', env: {},\n"
                        "        uses: './tools/local-ok' }\n"
                        "    ]\n"
                    ),
                },
            )
            res_ok = self.run_links_check(root)
            self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

            # Test multi-line flow mapping, inline flow sequence, and two flow
            # items on a single line.
            self.write_files(
                root,
                {
                    ".github/workflows/bad-flow.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  j1:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - { name: step1,\n"
                        "          env: {}, uses: ./.github/actions/missing-ml }\n"
                        "  j2:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps: [{uses: ./.github/actions/flow-ok}, "
                        "{uses: ./.github/actions/missing-seq2}]\n"
                    ),
                },
            )
            res_bad = self.run_links_check(root)
            self.assertNotEqual(res_bad.returncode, 0)
            self.assertIn("./.github/actions/missing-ml", res_bad.stderr)
            self.assertIn("./.github/actions/missing-seq2", res_bad.stderr)

    def test_symlink_action_and_manifest_rejected(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "action.yml").write_text(
                "name: Outside\nruns:\n  using: composite\n  steps: []\n",
                encoding="utf-8",
            )
            root = Path(tmp) / "repo"
            (root / ".github" / "actions").mkdir(parents=True)
            os.symlink(outside, root / ".github" / "actions" / "link")
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/link\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("symlink", res.stderr)

            # Also verify a symlinked `action.yml` inside a real directory fails closed.
            (root / ".github" / "actions" / "link").unlink()
            real_dir = root / ".github" / "actions" / "link"
            real_dir.mkdir()
            os.symlink(outside / "action.yml", real_dir / "action.yml")
            res2 = self.run_links_check(root)
            self.assertNotEqual(res2.returncode, 0)
            self.assertIn("symlink", res2.stderr)

            # Verify unreferenced symlinked workflow and action YAML files are
            # discovered and rejected (including a symlink aliasing an already
            # cached valid workflow).
            (real_dir / "action.yml").unlink()
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\njobs:\n  b:\n    runs-on: ubuntu-latest\n"
                        "    steps:\n      - uses: actions/checkout@v4\n"
                    ),
                },
            )
            (outside / "evil.yml").write_text(
                "on: push\njobs:\n  b:\n    runs-on: ubuntu-latest\n"
                "    steps:\n      - uses: ./.github/actions/missing\n",
                encoding="utf-8",
            )
            os.symlink(
                outside / "evil.yml", root / ".github" / "workflows" / "link.yml"
            )
            res3 = self.run_links_check(root)
            self.assertNotEqual(res3.returncode, 0)
            self.assertIn("expected non-symlink regular file", res3.stderr)
            (root / ".github" / "workflows" / "link.yml").unlink()

            os.symlink("ci.yml", root / ".github" / "workflows" / "z_alias.yml")
            res4 = self.run_links_check(root)
            self.assertNotEqual(res4.returncode, 0)
            self.assertIn("expected non-symlink regular file", res4.stderr)
            (root / ".github" / "workflows" / "z_alias.yml").unlink()

            os.symlink(outside / "action.yml", real_dir / "action.yml")
            res5 = self.run_links_check(root)
            self.assertNotEqual(res5.returncode, 0)
            self.assertIn("expected non-symlink regular file", res5.stderr)

            # Verify symlinked `.github/workflows` directory and symlinked
            # `.github` root directory both fail closed.
            ext_wf_dir = Path(tmp) / "ext_workflows"
            ext_wf_dir.mkdir()
            (ext_wf_dir / "ci.yml").write_text(
                "on: push\njobs:\n  b:\n    runs-on: ubuntu-latest\n"
                "    steps:\n      - uses: ./.github/actions/missing\n",
                encoding="utf-8",
            )
            root_sym_wf = Path(tmp) / "repo_sym_wf"
            (root_sym_wf / ".github").mkdir(parents=True)
            os.symlink(ext_wf_dir, root_sym_wf / ".github" / "workflows")
            res6 = self.run_links_check(root_sym_wf)
            self.assertNotEqual(res6.returncode, 0)
            self.assertIn("symlink", res6.stderr)

            root_sym_gh = Path(tmp) / "repo_sym_gh"
            root_sym_gh.mkdir()
            os.symlink(root / ".github", root_sym_gh / ".github")
            res7 = self.run_links_check(root_sym_gh)
            self.assertNotEqual(res7.returncode, 0)
            self.assertIn("symlink", res7.stderr)

    def test_nested_reusable_workflow_and_wrong_level_uses_rejected(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/sub/r.yml": (
                        "on:\n  workflow_call:\njobs:\n  noop:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/top.yml": (
                        "on:\n  workflow_call:\njobs:\n  noop:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/actions/act/action.yml": (
                        "name: Act\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/workflows/caller.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  nested-wf:\n"
                        "    uses: ./.github/workflows/sub/r.yml\n"
                        "  trailing-slash-wf:\n"
                        "    uses: ./.github/workflows/top.yml/\n"
                        "  job-calls-action:\n"
                        "    uses: ./.github/actions/act\n"
                        "  step-calls-wf:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/workflows/top.yml\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("directly under ./.github/workflows/", res.stderr)
            self.assertIn("must not end with '/'", res.stderr)
            self.assertIn("Job-level local uses must target", res.stderr)
            self.assertIn("Step-level uses cannot target", res.stderr)

    def test_local_action_dir_with_only_dockerfile_fails(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/actions/docker-only/Dockerfile": "FROM scratch\n",
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/docker-only\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("./.github/actions/docker-only", res.stderr)

    def test_quoted_uses_keys_and_duplicate_keys_checked(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        '      - "uses": ./.github/actions/missing-dq\n'
                        "      - 'uses': ./.github/actions/missing-sq\n"
                        '      - { "uses": ./.github/actions/missing-flow-dq }\n'
                        "      - { name: a, 'uses': ./.github/actions/missing-flow-sq }\n"
                    ),
                },
            )
            res = self.run_links_check(root)
            self.assertNotEqual(res.returncode, 0)
            for name in (
                "missing-dq",
                "missing-sq",
                "missing-flow-dq",
                "missing-flow-sq",
            ):
                self.assertIn(f"./.github/actions/{name}", res.stderr)

            # Valid block scalar containing repeated `uses:` lines must pass.
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - run: |\n"
                        "          uses: a\n"
                        "          uses: a\n"
                    ),
                },
            )
            res_block = self.run_links_check(root)
            self.assertEqual(res_block.returncode, 0, res_block.stdout + res_block.stderr)

            # Duplicate `uses:` key, duplicate `on:`/`'on':` key, duplicate `<<:`
            # key, and block scalar with repeated `uses:` lines.
            for label, bad_yaml in (
                (
                    "dup-step-uses",
                    (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/shadowed-missing\n"
                        "        uses: actions/checkout@0123456789abcdef\n"
                    ),
                ),
                (
                    "dup-on",
                    (
                        "on: push\n"
                        "'on': workflow_call\n"
                        "jobs: {}\n"
                    ),
                ),
                (
                    "dup-merge",
                    (
                        "x-a: &a\n  name: a\n"
                        "x-b: &b\n  uses: actions/checkout@0123456789abcdef\n"
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: *a\n"
                        "        <<: *b\n"
                    ),
                ),
                (
                    "inline-dup-in-merge",
                    (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: { uses: ./.github/actions/a, uses: ./.github/actions/b }\n"
                    ),
                ),
            ):
                self.write_files(root, {".github/workflows/ci.yml": bad_yaml})
                res_dup = self.run_links_check(root)
                self.assertNotEqual(res_dup.returncode, 0, label)
                self.assertIn("duplicate YAML mapping key", res_dup.stderr)

    def test_merge_keys_and_non_coerced_boolean_trigger_keys(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            # 1. Valid merge-key override (`<<: *d` + explicit `uses:`) must pass.
            self.write_files(
                root,
                {
                    ".github/actions/ok/action.yml": (
                        "name: Ok\nruns:\n  using: composite\n  steps: []\n"
                    ),
                    ".github/workflows/ci.yml": (
                        "x-def: &d\n"
                        "  uses: ./.github/actions/ok\n"
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: *d\n"
                        "        uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1\n"
                    ),
                },
            )
            res_ok = self.run_links_check(root)
            self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

            # 2. Inherited bad `uses:` via `<<: *bad` must fail closed.
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "x-def: &bad\n"
                        "  uses: ./.github/actions/missing-via-merge\n"
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: *bad\n"
                    ),
                },
            )
            res_bad_merge = self.run_links_check(root)
            self.assertNotEqual(res_bad_merge.returncode, 0)
            self.assertIn("./.github/actions/missing-via-merge", res_bad_merge.stderr)

            # 3. Chained merge-key overrides (`&base` -> `&derived` -> step)
            # must pass when overridden and fail closed when inheriting a
            # broken `uses:`, and `tag:yaml.org,2002:value` (`=:`) must not
            # misbehave or recurse as a merge target.
            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "x-base: &base\n"
                        "  uses: ./.github/actions/missing-base\n"
                        "  name: base\n"
                        "x-derived: &derived\n"
                        "  <<: *base\n"
                        "  uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1\n"
                        "x-value-tag:\n"
                        "  =:\n"
                        "    note: default-value\n"
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: *derived\n"
                    ),
                },
            )
            res_chain_ok = self.run_links_check(root)
            self.assertEqual(
                res_chain_ok.returncode,
                0,
                res_chain_ok.stdout + res_chain_ok.stderr,
            )

            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "x-base: &base\n"
                        "  uses: ./.github/actions/missing-chained\n"
                        "x-derived: &derived\n"
                        "  <<: *base\n"
                        "  name: derived\n"
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - <<: *derived\n"
                    ),
                },
            )
            res_chain_bad = self.run_links_check(root)
            self.assertNotEqual(res_chain_bad.returncode, 0)
            self.assertIn("./.github/actions/missing-chained", res_chain_bad.stderr)

            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "x-dup-val:\n"
                        "  =: one\n"
                        "  =: two\n"
                        "on: push\n"
                        "jobs: {}\n"
                    ),
                },
            )
            res_dup_val = self.run_links_check(root)
            self.assertNotEqual(res_dup_val.returncode, 0)
            self.assertIn("duplicate YAML mapping key", res_dup_val.stderr)

            # Cyclic non-merge aliases must fail cleanly without a traceback.
            for label, bad_cyclic in (
                ("direct-map", "x: &x\n  self: *x\non: push\njobs: {}\n"),
                ("direct-seq", "a: &a [1, *a]\non: push\njobs: {}\n"),
                (
                    "indirect",
                    "x: &x\n  y: &y\n    z: *x\non: push\njobs: {}\n",
                ),
            ):
                self.write_files(root, {".github/workflows/ci.yml": bad_cyclic})
                res_cyclic = self.run_links_check(root)
                self.assertNotEqual(res_cyclic.returncode, 0, label)
                self.assertNotIn("Traceback", res_cyclic.stderr)
                self.assertIn("Invalid workflow file", res_cyclic.stderr)
                self.assertIn("cyclic YAML alias", res_cyclic.stderr)

            # 4. `true: workflow_call` and `yes: workflow_call` must NOT match `on:`.
            for bad_on_key in ("true", "yes"):
                self.write_files(
                    root,
                    {
                        ".github/workflows/reusable_bool.yml": (
                            f"{bad_on_key}: workflow_call\n"
                            "jobs:\n  a:\n    runs-on: ubuntu-latest\n    steps: []\n"
                        ),
                        ".github/workflows/ci.yml": (
                            "on: push\n"
                            "jobs:\n"
                            "  call:\n"
                            "    uses: ./.github/workflows/reusable_bool.yml\n"
                        ),
                    },
                )
                res_bool = self.run_links_check(root)
                self.assertNotEqual(res_bool.returncode, 0, bad_on_key)
                self.assertIn("workflow_call", res_bool.stderr)

    def test_reusable_workflow_must_declare_top_level_workflow_call(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp)
            self.write_files(
                root,
                {
                    ".github/workflows/r_scalar.yml": (
                        "on: workflow_call\njobs:\n  a:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/r_seq.yml": (
                        "on: [push, workflow_call]\njobs:\n  a:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/r_map.yml": (
                        "'on':\n  push:\n  workflow_call:\njobs:\n  a:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/r_flow_map.yml": (
                        "on: { workflow_call: {} }\njobs:\n  a:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/r_comment.yml": (
                        "on: # reusable trigger\n"
                        "  workflow_call:\njobs:\n  a:\n"
                        "    runs-on: ubuntu-latest\n    steps: []\n"
                    ),
                    ".github/workflows/caller_ok.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  j1:\n    uses: ./.github/workflows/r_scalar.yml\n"
                        "  j2:\n    uses: ./.github/workflows/r_seq.yml\n"
                        "  j3:\n    uses: ./.github/workflows/r_map.yml\n"
                        "  j4:\n    uses: ./.github/workflows/r_flow_map.yml\n"
                        "  j5:\n    uses: ./.github/workflows/r_comment.yml\n"
                    ),
                },
            )
            res_ok = self.run_links_check(root)
            self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

            # Both block and single-line flow decoys where `workflow_call` is
            # nested inside `workflow_dispatch.inputs` (not a top-level trigger)
            # must be rejected.
            for decoy_on in (
                (
                    "on:\n"
                    "  workflow_dispatch:\n"
                    "    inputs:\n"
                    "      workflow_call:\n"
                    "        description: decoy\n"
                ),
                (
                    "on: { workflow_dispatch: { inputs: "
                    "{ workflow_call: { type: string } } } }\n"
                ),
                "on: # push-only\n  push:\n",
            ):
                self.write_files(
                    root,
                    {
                        ".github/workflows/not_reusable.yml": (
                            decoy_on
                            + "jobs:\n  a:\n    runs-on: ubuntu-latest\n"
                            "    steps: []\n"
                        ),
                        ".github/workflows/caller_bad.yml": (
                            "on: push\n"
                            "jobs:\n"
                            "  bad:\n"
                            "    uses: ./.github/workflows/not_reusable.yml\n"
                        ),
                    },
                )
                res_bad = self.run_links_check(root)
                self.assertNotEqual(res_bad.returncode, 0, decoy_on)
                self.assertIn("workflow_call", res_bad.stderr)

    def test_yq_fallback_rejects_non_mikefarah_and_handles_v4_stub(self):
        # 1. Verify non-mikefarah `yq` fails closed (both synthetic and real
        # host `yq` if present and not mikefarah).
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-oldyq-") as tmp:
            root = Path(tmp) / "repo"
            bin_dir = Path(tmp) / "bin"
            bin_dir.mkdir(parents=True)
            old_yq = bin_dir / "yq"
            old_yq.write_text(
                f"#!{sys.executable}\n"
                "import sys\n"
                "if '--version' in sys.argv:\n"
                "    print('yq 3.4.3')\n"
                "    sys.exit(0)\n"
                "print('{}')\n",
                encoding="utf-8",
            )
            old_yq.chmod(old_yq.stat().st_mode | stat.S_IXUSR)
            self.write_files(
                root,
                {".github/workflows/ok.yml": "on: push\njobs: {}\n"},
            )
            res_old = self.run_links_check(
                root,
                extra_env={
                    "CHECK_ACTIONS_FORCE_YQ": "1",
                    "PATH": f"{bin_dir}:{os.environ.get('PATH', '')}",
                },
            )
            self.assertNotEqual(res_old.returncode, 0)
            self.assertIn("unsupported yq binary", res_old.stderr)

        host_yq = shutil.which("yq")
        if host_yq:
            ver = subprocess.run(
                [host_yq, "--version"], capture_output=True, text=True, check=False
            )
            res_host = self.run_links_check(
                REPO_ROOT, extra_env={"CHECK_ACTIONS_FORCE_YQ": "1"}
            )
            if "mikefarah" in (ver.stdout + ver.stderr).lower():
                self.assertEqual(
                    res_host.returncode, 0, res_host.stdout + res_host.stderr
                )
                with tempfile.TemporaryDirectory(
                    prefix="anneal-check-actions-real-yq-"
                ) as tmp:
                    root = Path(tmp)
                    self.write_files(
                        root,
                        {
                            ".github/workflows/ok.yml": (
                                "x-bad: &bad\n"
                                "  uses: ./.github/actions/missing\n"
                                "x-derived: &derived\n"
                                "  <<: *bad\n"
                                "  uses: actions/checkout@v4\n"
                                "on: push\n"
                                "jobs:\n"
                                "  b:\n"
                                "    steps:\n"
                                "      - <<: *bad\n"
                                "        uses: actions/checkout@v4\n"
                                "      - <<: *derived\n"
                            ),
                        },
                    )
                    res_override = self.run_links_check(
                        root, extra_env={"CHECK_ACTIONS_FORCE_YQ": "1"}
                    )
                    self.assertEqual(
                        res_override.returncode,
                        0,
                        res_override.stdout + res_override.stderr,
                    )
                    for content, err_sub in (
                        (
                            "x-bad: &bad\n  uses: ./.github/actions/missing\n"
                            "x-ok: &ok\n  uses: actions/checkout@v4\n"
                            "on: push\njobs:\n  b:\n    steps:\n"
                            "      - <<: *bad\n        <<: *ok\n",
                            "duplicate YAML mapping key",
                        ),
                        (
                            "x-bad: &bad\n  uses: ./.github/actions/missing\n"
                            "on: push\njobs:\n  b:\n    steps:\n"
                            "      - <<: *bad\n",
                            "./.github/actions/missing",
                        ),
                        (
                            "x-bad: &bad\n  uses: ./.github/actions/missing-chain\n"
                            "x-derived: &derived\n  <<: *bad\n  name: d\n"
                            "on: push\njobs:\n  b:\n    steps:\n"
                            "      - <<: *derived\n",
                            "./.github/actions/missing-chain",
                        ),
                        (
                            "x-base: &base\n  name: base\n"
                            "on: push\njobs:\n  b:\n    steps:\n"
                            "      - <<: *base\n"
                            "        uses: ./.github/actions/missing\n"
                            "        uses: actions/checkout@v4\n",
                            "duplicate YAML mapping key",
                        ),
                        (
                            "x: &x\n  self: *x\n"
                            "on: push\njobs: {}\n",
                            "cyclic YAML alias",
                        ),
                    ):
                        self.write_files(
                            root, {".github/workflows/bad.yml": content}
                        )
                        res_bad = self.run_links_check(
                            root, extra_env={"CHECK_ACTIONS_FORCE_YQ": "1"}
                        )
                        self.assertNotEqual(res_bad.returncode, 0)
                        self.assertIn(err_sub, res_bad.stderr)
            else:
                self.assertNotEqual(res_host.returncode, 0)
                self.assertIn("unsupported yq binary", res_host.stderr)

        # 2. Verify `mikefarah/yq` v4 CLI contract (duplicate-key and
        # cyclic-alias pre-checks + `eval explode(.) -o=json <path>`): valid
        # merged output passes, duplicate JSON keys fail, duplicate `<<`,
        # duplicate explicit keys alongside `<<`, and cyclic aliases fail even
        # though `explode(.)` would apply last-wins or silently truncate,
        # unexpanded `<<` fails, and `<<: *bad` fails.
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-yq-") as tmp:
            root = Path(tmp) / "repo"
            bin_dir = Path(tmp) / "bin"
            bin_dir.mkdir(parents=True)
            yq_stub = bin_dir / "yq"
            dup_expr = (
                '[.. | select(tag == "!!map") | keys | group_by(.) '
                "| map(length) | max // 0] | max // 0"
            )
            cyclic_expr = (
                '[.. | select(anchor != "") | anchor as $a '
                '| .. | select(kind == "alias" and alias == $a)] | length'
            )
            yq_stub.write_text(
                f"#!{sys.executable}\n"
                "import json, sys\n"
                "if '--version' in sys.argv:\n"
                "    print('yq (https://github.com/mikefarah/yq/) version v4.44.1')\n"
                "    sys.exit(0)\n"
                f"DUP_EXPR = {dup_expr!r}\n"
                f"CYCLIC_EXPR = {cyclic_expr!r}\n"
                "if sys.argv[1:3] == ['eval', DUP_EXPR] and len(sys.argv) == 4:\n"
                "    text = open(sys.argv[3], encoding='utf-8').read()\n"
                "    if 'dup-merge' in text or 'dup-key-with-merge' in text:\n"
                "        print('2')\n"
                "    else:\n"
                "        print('1')\n"
                "    sys.exit(0)\n"
                "if sys.argv[1:3] == ['eval', CYCLIC_EXPR] and len(sys.argv) == 4:\n"
                "    text = open(sys.argv[3], encoding='utf-8').read()\n"
                "    print('1' if 'cyclic-alias' in text else '0')\n"
                "    sys.exit(0)\n"
                "assert sys.argv[1:4] == ['eval', 'explode(.)', '-o=json'] and len(sys.argv) == 5, sys.argv\n"
                "path = sys.argv[4]\n"
                "text = open(path, encoding='utf-8').read()\n"
                "if 'dup-json' in text:\n"
                '    print(\'{"on": "push", "jobs": {"b": {"steps": [{"uses": "./.github/actions/a", "uses": "actions/checkout@v4"}]}}}\')\n'
                "elif 'dup-merge' in text or 'dup-key-with-merge' in text or 'cyclic-alias' in text:\n"
                "    # Simulate `explode(.)` silently applying last-wins or truncating.\n"
                '    doc = {"on": "push", "jobs": {"b": {"steps": [{"uses": "actions/checkout@v4"}]}}}\n'
                "    print(json.dumps(doc))\n"
                "elif 'unexpanded-merge' in text:\n"
                '    doc = {"on": "push", "jobs": {"b": {"steps": [{"<<": {"uses": "./.github/actions/ok"}}]}}}\n'
                "    print(json.dumps(doc))\n"
                "elif 'bad-merged-uses' in text:\n"
                '    doc = {"on": "push", "jobs": {"b": {"steps": [{"uses": "./.github/actions/missing-via-v4"}]}}}\n'
                "    print(json.dumps(doc))\n"
                "else:\n"
                '    doc = {"on": {"workflow_call": None}, "jobs": {"b": {"steps": [{"uses": "actions/checkout@v4"}]}}}\n'
                "    print(json.dumps(doc))\n",
                encoding="utf-8",
            )
            yq_stub.chmod(yq_stub.stat().st_mode | stat.S_IXUSR)

            env_v4 = {
                "CHECK_ACTIONS_FORCE_YQ": "1",
                "PATH": f"{bin_dir}:{os.environ.get('PATH', '')}",
            }
            self.write_files(
                root,
                {
                    ".github/workflows/ok.yml": (
                        "on:\n  workflow_call:\njobs:\n  b:\n    steps: []\n"
                    ),
                    ".github/workflows/single-merge.yml": "single-merge\n",
                },
            )
            res_ok = self.run_links_check(root, extra_env=env_v4)
            self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

            for marker_text, expected_err in (
                ("bad-merged-uses", "./.github/actions/missing-via-v4"),
                ("dup-json", "duplicate YAML mapping key"),
                ("dup-merge", "duplicate YAML mapping key"),
                ("dup-key-with-merge", "duplicate YAML mapping key"),
                ("cyclic-alias", "cyclic YAML alias"),
                ("unexpanded-merge", "unexpanded YAML merge key '<<'"),
            ):
                self.write_files(
                    root,
                    {".github/workflows/bad.yml": f"{marker_text}\n"},
                )
                res_bad = self.run_links_check(root, extra_env=env_v4)
                self.assertNotEqual(res_bad.returncode, 0, marker_text)
                self.assertIn(expected_err, res_bad.stderr)

    def test_checks_toml_skills_check_inputs_cover_action_tests(self):
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        self.assertIn("skills-check", checks)
        includes = {
            pat
            for inp in checks["skills-check"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        for required in ("ci/*.py", "ci/check_actions.sh", ".github/**"):
            self.assertIn(required, includes)

    def test_full_script_enforces_local_links_alongside_validator(self):
        with tempfile.TemporaryDirectory(prefix="anneal-check-actions-") as tmp:
            root = Path(tmp) / "repo"
            bin_dir = Path(tmp) / "bin"
            bin_dir.mkdir(parents=True)
            stub = bin_dir / "action-validator"
            stub.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
            stub.chmod(stub.stat().st_mode | stat.S_IXUSR)

            self.write_files(
                root,
                {
                    ".github/workflows/ci.yml": (
                        "on: push\n"
                        "jobs:\n"
                        "  build:\n"
                        "    runs-on: ubuntu-latest\n"
                        "    steps:\n"
                        "      - uses: ./.github/actions/missing-with-stub-validator\n"
                    ),
                },
            )
            res = self.run_links_check(
                root,
                links_only=False,
                extra_env={"PATH": f"{bin_dir}:{os.environ.get('PATH', '')}"},
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn("missing-with-stub-validator", res.stderr)


if __name__ == "__main__":
    unittest.main()
