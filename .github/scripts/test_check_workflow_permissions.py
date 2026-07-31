#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

from __future__ import annotations

import contextlib
import importlib.util
import io
import os
import pathlib
import sys
import tempfile
import textwrap
import unittest


_SCRIPT = pathlib.Path(__file__).with_name("check-workflow-permissions.py")
_SPEC = importlib.util.spec_from_file_location("check_workflow_permissions", _SCRIPT)
assert _SPEC is not None and _SPEC.loader is not None
checker = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = checker
_SPEC.loader.exec_module(checker)

_YQ = os.environ.get("YQ", "yq")


def _workflow(source: str) -> str:
    return textwrap.dedent(source).lstrip()


class WorkflowPermissionTests(unittest.TestCase):
    def analyze(self, source: str) -> list[checker.Issue]:
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "workflow.yml"
            path.write_text(_workflow(source), encoding="utf-8")
            workflow = checker.load_workflow(path, _YQ)
        return checker.analyze_workflow(workflow)

    def assert_safe(self, source: str) -> None:
        self.assertEqual(self.analyze(source), [])

    def assert_finding(self, source: str, fragment: str) -> None:
        issues = self.analyze(source)
        self.assertTrue(issues, "expected a workflow-permission finding")
        self.assertTrue(
            any(fragment in issue.message for issue in issues),
            f"{fragment!r} not found in {[issue.message for issue in issues]!r}",
        )

    def assert_parse_error(self, source: str, fragment: str) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "workflow.yml"
            path.write_text(_workflow(source), encoding="utf-8")
            with self.assertRaisesRegex(checker.WorkflowLoadError, fragment):
                checker.load_workflow(path, _YQ)

    def test_safe_read_permissions(self) -> None:
        self.assert_safe(
            """
            name: Safe
            on:
              pull_request:
              merge_group:
            permissions:
              contents: read
            jobs:
              test:
                permissions:
                  actions: read
                  contents: none
                runs-on: ubuntu-latest
                steps: []
            """
        )
        self.assert_safe(
            """
            name: Empty but harmless
            on: pull_request
            permissions: read-all
            jobs: {}
            """
        )

    def test_compact_trigger_forms(self) -> None:
        for trigger in (
            "pull_request",
            "[push, pull_request]",
            "{push: {}, merge_group: {types: [checks_requested]}}",
        ):
            with self.subTest(trigger=trigger):
                self.assert_safe(
                    f"""
                    name: Compact
                    on: {trigger}
                    permissions: {{contents: read}}
                    jobs:
                      test:
                        runs-on: ubuntu-latest
                        steps: []
                    """
                )

    def test_yaml_aliases_and_tags_are_resolved(self) -> None:
        self.assert_finding(
            """
            name: &pr pull_request
            on:
              *pr:
            permissions: {contents: write}
            jobs: {}
            """,
            "workflow grants `contents: write`",
        )
        self.assert_finding(
            """
            on:
              !!str pull_request:
            permissions: {contents: write}
            jobs: {}
            """,
            "workflow grants `contents: write`",
        )
        self.assert_safe(
            """
            on: pull_request
            permissions: &read_only
              contents: read
            jobs:
              test:
                permissions: *read_only
                runs-on: ubuntu-latest
                steps: []
            """
        )

    def test_top_level_write_permission(self) -> None:
        self.assert_finding(
            """
            name: Unsafe
            on: [push, pull_request]
            permissions:
              contents: write
            jobs: {}
            """,
            "workflow grants `contents: write`",
        )
        self.assert_finding(
            """
            name: Unsafe
            on: merge_group
            permissions: write-all
            jobs: {}
            """,
            "workflow grants `write-all`",
        )

    def test_untrusted_workflow_requires_explicit_permission_cap(self) -> None:
        for event in ("pull_request", "merge_group"):
            for jobs in (
                "jobs: {}",
                """jobs:
  test:
    permissions: {contents: read}
    runs-on: ubuntu-latest
    steps: []""",
            ):
                with self.subTest(event=event, jobs=jobs):
                    self.assert_finding(
                        f"""
                        name: Inherits mutable repository default
                        on: {event}
                        {textwrap.indent(jobs, " " * 24).lstrip()}
                        """,
                        "must declare explicit top-level `permissions`",
                    )

        self.assert_safe(
            """
            name: Explicitly no token permissions
            on: merge_group
            permissions: {}
            jobs: {}
            """
        )

    def test_job_write_permission(self) -> None:
        self.assert_finding(
            """
            name: Unsafe job
            on:
              merge_group:
            permissions: {}
            jobs:
              publish:
                permissions: {packages: write, contents: read}
                runs-on: ubuntu-latest
                steps: []
            """,
            "job `publish` grants `packages: write`",
        )

    def test_unrelated_workflow_may_write(self) -> None:
        self.assert_safe(
            """
            name: Trusted workflow may inherit repository policy
            on: push
            jobs: {}
            """
        )
        self.assert_safe(
            """
            name: Trusted deployment
            on:
              push:
                branches: [main]
              workflow_dispatch:
            permissions: write-all
            jobs:
              publish:
                permissions:
                  contents: write
                runs-on: ubuntu-latest
                steps: []
            """
        )

    def test_non_permission_write_values_are_ignored(self) -> None:
        self.assert_safe(
            """
            name: Words are not authority
            on: pull_request
            permissions: {contents: read}
            env:
              ACCESS: write
            jobs:
              test:
                permissions:
                  contents: read
                runs-on: ubuntu-latest
                steps:
                  - uses: example/action@0123456789abcdef
                    with:
                      permissions: write
                      contents: write
                  - name: Mention permissions in a script
                    run: |
                      permissions:
                        contents: write
            """
        )

    def test_ambiguous_permission_shapes_fail_closed(self) -> None:
        for permissions in (
            "${{ fromJSON(inputs.permissions) }}",
            "[contents, read]",
            "null",
        ):
            with self.subTest(permissions=permissions):
                self.assert_finding(
                    f"""
                    name: Ambiguous
                    on: pull_request
                    permissions: {permissions}
                    jobs: {{}}
                    """,
                    "cannot safely interpret workflow permissions",
                )

        for permission in ("[read]", "{level: read}"):
            with self.subTest(permission=permission):
                self.assert_finding(
                    f"""
                    name: Ambiguous scope
                    on: pull_request
                    permissions: {{contents: {permission}}}
                    jobs: {{}}
                    """,
                    "cannot safely interpret workflow permission",
                )

    def test_invalid_decoded_shapes_fail_closed(self) -> None:
        for source, fragment in (
            (
                """
                on: [pull_request, 1]
                permissions: {}
                jobs: {}
                """,
                "trigger list must contain only event names",
            ),
            (
                """
                on: pull_request
                permissions: {}
                jobs: []
                """,
                "workflow `jobs` must be a mapping",
            ),
            (
                """
                on: pull_request
                permissions: {}
                jobs: {test: null}
                """,
                "job must be a mapping",
            ),
        ):
            with self.subTest(fragment=fragment):
                self.assert_finding(source, fragment)

        self.assert_finding("[]", "workflow document must be a mapping")

    def test_duplicate_keys_and_multiple_documents_are_rejected(self) -> None:
        self.assert_parse_error(
            """
            on: push
            on: pull_request
            permissions: {}
            jobs: {}
            """,
            "duplicate mapping key 'on'",
        )
        self.assert_parse_error(
            """
            on: pull_request
            permissions: {contents: read, contents: write}
            jobs: {}
            """,
            "duplicate mapping key 'contents'",
        )
        self.assert_parse_error(
            """
            on: push
            jobs: {}
            ---
            on: pull_request
            permissions: {contents: write}
            jobs: {}
            """,
            "expected exactly one YAML document",
        )

    def test_malformed_yaml_is_rejected(self) -> None:
        self.assert_parse_error(
            """
            on: [pull_request
            permissions: {}
            jobs: {}
            """,
            ".+",
        )

    def test_cli_accepts_directories_and_paths_with_spaces(self) -> None:
        with tempfile.TemporaryDirectory(prefix="workflow permissions ") as directory:
            root = pathlib.Path(directory)
            (root / "safe.yml").write_text(
                _workflow(
                    """
                    on: pull_request
                    permissions: read-all
                    jobs: {}
                    """
                ),
                encoding="utf-8",
            )
            nested = root / "nested directory"
            nested.mkdir()
            (nested / "unsafe workflow.yaml").write_text(
                _workflow(
                    """
                    on: merge_group
                    permissions: {contents: write}
                    jobs: {}
                    """
                ),
                encoding="utf-8",
            )

            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                result = checker.main(["--yq", _YQ, str(root)])
            self.assertEqual(result, 1)
            self.assertIn("unsafe workflow.yaml", stderr.getvalue())
            self.assertIn("contents: write", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
