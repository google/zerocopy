# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Workflow YAML tests for audited YAML tree mounts and local `uses`."""

from .support import (
    CHECKS_TOML,
    _find_unmounted_local_uses,
    _find_unpinned_download_steps,
    load_workflow_yaml,
    Path,
    REPO_ROOT,
    tempfile,
    tomllib,
)


class MountedTreeCases:
    """`WorkflowPolicyLintTests` methods for audited YAML tree mounts and local
    `uses`."""

    def test_checks_toml_mounts_audited_github_yaml_trees(self):
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data.get("checks", [])}
        self.assertIn("anneal-ci-tests", checks)
        includes = {
            pat
            for inp in checks["anneal-ci-tests"].get("inputs", [])
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        }
        for required in (
            ".github/workflows/*.yml",
            ".github/workflows/*.yaml",
            ".github/actions/**",
            "ci/checks.toml",
        ):
            self.assertIn(required, includes)

    def test_nested_actions_and_local_uses_are_audited(self):
        targets = self._mounted_yaml_targets()
        mounted_resolved = {p.resolve() for p in targets}
        violations = []
        for path in targets:
            doc = load_workflow_yaml(path.read_text(encoding="utf-8"))
            rel = path.relative_to(REPO_ROOT).as_posix()
            violations.extend(
                _find_unmounted_local_uses(
                    doc, rel, REPO_ROOT, mounted_resolved
                )
            )
        self.assertEqual(violations, [])

        with tempfile.TemporaryDirectory(prefix="anneal-nested-act-") as tmp:
            root = Path(tmp)
            wf_dir = root / ".github" / "workflows"
            act_dir = root / ".github" / "actions"
            nested_dir = act_dir / "a" / "b"
            wf_dir.mkdir(parents=True)
            nested_dir.mkdir(parents=True)
            wf_path = wf_dir / "main.yml"
            wf_path.write_text(
                "jobs:\n  b:\n    steps:\n"
                "      - uses: ./.github/actions/a/b\n"
                "      - uses: ./.github/actions/missing\n",
                encoding="utf-8",
            )
            nested_action = nested_dir / "action.yml"
            nested_action.write_text(
                "runs:\n  using: composite\n  steps:\n"
                "    - shell: bash\n"
                "      run: curl https://example.com/x | bash\n",
                encoding="utf-8",
            )
            found = self._mounted_yaml_targets(
                workflows_dir=wf_dir, actions_dir=act_dir
            )
            self.assertIn(nested_action, found)
            nested_rel = nested_action.relative_to(root).as_posix()
            nested_hits = _find_unpinned_download_steps(
                load_workflow_yaml(nested_action.read_text(encoding="utf-8")),
                nested_rel,
            )
            self.assertEqual(len(nested_hits), 1)
            self.assertIn("unpinned curl/wget step", nested_hits[0])
            wf_hits = _find_unmounted_local_uses(
                load_workflow_yaml(wf_path.read_text(encoding="utf-8")),
                wf_path.relative_to(root).as_posix(),
                root,
                {p.resolve() for p in found},
            )
            self.assertEqual(len(wf_hits), 1)
            self.assertIn("./.github/actions/missing", wf_hits[0])
