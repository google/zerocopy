# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workflow YAML tests for `_mounted_yaml_targets`, status functions in `env`,
and wildcard artifact downloads."""

from .support import (
    ACTIONS_DIR,
    _find_download_artifact_pattern_violations,
    _find_env_status_violations,
    load_workflow_yaml,
    PUBLISH_ACTION,
    REPO_ROOT,
    WORKFLOWS_DIR,
)


class EnvAndArtifactCases:
    """`WorkflowPolicyLintTests` methods for `_mounted_yaml_targets`, status
    functions in `env`, and wildcard artifact downloads."""

    def _mounted_yaml_targets(
        self, workflows_dir=WORKFLOWS_DIR, actions_dir=ACTIONS_DIR
    ):
        workflows = sorted(
            [
                *workflows_dir.glob("*.yml"),
                *workflows_dir.glob("*.yaml"),
            ]
        )
        self.assertTrue(
            workflows, f"expected workflow YAML files under {workflows_dir}"
        )
        actions = sorted(
            {
                *actions_dir.rglob("action.yml"),
                *actions_dir.rglob("action.yaml"),
            }
        )
        if actions_dir == ACTIONS_DIR:
            self.assertIn(
                PUBLISH_ACTION,
                actions,
                f"missing composite action {PUBLISH_ACTION}",
            )
        return [*workflows, *actions]

    def test_workflows_forbid_status_functions_in_env(self):
        violations = []
        for path in self._mounted_yaml_targets():
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(_find_env_status_violations(doc, rel))
        self.assertEqual(violations, [])

        for bad_expr in (
            "cancelled()",
            "Cancelled()",
            "failure()",
            "FAILURE()",
            "success()",
            "always()",
            "ALWAYS()",
            "format('{0}', success())",
            "format('failure() ok {0}', cancelled())",
        ):
            for scope, yaml_text in (
                ("workflow", f"env:\n  BAD: ${{{{ {bad_expr} }}}}\n"),
                (
                    "job",
                    "jobs:\n  b:\n    env:\n"
                    f"      BAD: ${{{{ {bad_expr} }}}}\n",
                ),
                (
                    "step",
                    "jobs:\n  b:\n    steps:\n      - name: s\n"
                    f"        env:\n          BAD: ${{{{ {bad_expr} }}}}\n",
                ),
            ):
                with self.subTest(expr=bad_expr, scope=scope):
                    hits = _find_env_status_violations(
                        load_workflow_yaml(yaml_text), "synthetic.yml"
                    )
                    self.assertEqual(len(hits), 1, yaml_text)

        safe_wf = load_workflow_yaml(
            "env:\n"
            '  OK: "${{ format(\'failure() was reported: {0}\', '
            'github.ref) }}"\n'
        )
        self.assertEqual(_find_env_status_violations(safe_wf, "safe.yml"), [])

    def test_workflows_forbid_wildcard_download_artifact_pattern(self):
        violations = []
        for path in self._mounted_yaml_targets():
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(
                _find_download_artifact_pattern_violations(doc, rel)
            )
        self.assertEqual(violations, [])

        for bad_pat in (
            "'{plan-a1,img-meta-*}'",
            "'img-meta-?'",
            "'shard-[01]'",
            "'+(plan-a|plan-b)'",
            "'@(a|b)'",
            "'!exclude-me'",
        ):
            bad_wf = load_workflow_yaml(
                "jobs:\n  gate:\n    steps:\n"
                "      - uses: Actions/Download-Artifact@abc\n"
                f"        with:\n          pattern: {bad_pat}\n"
                "          merge-multiple: false\n          path: meta-in\n"
            )
            self.assertEqual(
                len(_find_download_artifact_pattern_violations(bad_wf, "b")),
                1,
                bad_pat,
            )

        for good_yaml in (
            "jobs:\n  gate:\n    steps:\n"
            "      - uses: actions/download-artifact@abc\n"
            "        with:\n          name: plan-a1\n          path: meta-in\n",
            "jobs:\n  gate:\n    steps:\n"
            "      - uses: actions/download-artifact@abc\n"
            "        with:\n          pattern: 'img-meta-*'\n"
            "          Merge-Multiple: 'True'\n          path: meta-in\n",
        ):
            self.assertEqual(
                _find_download_artifact_pattern_violations(
                    load_workflow_yaml(good_yaml), "good.yml"
                ),
                [],
            )
