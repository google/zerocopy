#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reject write-capable tokens in workflows which execute proposed changes.

The repository's workflow validators own GitHub schema validation. This
checker owns one additional policy: workflows triggered by ``pull_request``
or ``merge_group`` must explicitly cap their token permissions at read-only.

YAML syntax is intentionally handled by the pinned mikefarah/yq binary which
``ci/check_actions.sh`` supplies. Keeping parsing outside this script avoids a
partial YAML implementation in security-sensitive code. The remaining Python
operates only on decoded objects and fails closed on shapes whose authority it
cannot establish.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import os
import pathlib
import subprocess
import sys
from collections.abc import Iterable, Mapping, Sequence
from typing import Any


_UNTRUSTED_EVENTS = frozenset({"merge_group", "pull_request"})
_WORKFLOW_SUFFIXES = frozenset({".yaml", ".yml"})


@dataclasses.dataclass(frozen=True)
class Issue:
    location: str
    message: str


class WorkflowLoadError(ValueError):
    """Raised when a workflow cannot be decoded unambiguously."""


class _DuplicateKey(ValueError):
    pass


def _object_without_duplicate_keys(
    pairs: list[tuple[str, Any]],
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateKey(f"duplicate mapping key {key!r}")
        result[key] = value
    return result


def load_workflow(path: pathlib.Path, yq: str) -> Any:
    """Decodes exactly one YAML document using the supplied yq binary.

    yq resolves YAML anchors, aliases, tags, and merge keys before producing
    JSON. Its JSON output can still contain duplicate object members, so the
    JSON loader must reject duplicates rather than silently keeping the last
    value. Parsing one JSON value also makes multiple YAML documents fail with
    ``Extra data`` instead of inspecting only one of them.
    """

    try:
        result = subprocess.run(
            [
                yq,
                "eval",
                "--output-format=json",
                "--no-colors",
                ".",
                "--",
                str(path),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as error:
        raise WorkflowLoadError(f"could not execute yq: {error}") from error

    if result.returncode != 0:
        detail = result.stderr.strip() or f"yq exited with status {result.returncode}"
        raise WorkflowLoadError(detail)

    try:
        return json.loads(
            result.stdout,
            object_pairs_hook=_object_without_duplicate_keys,
        )
    except _DuplicateKey as error:
        raise WorkflowLoadError(str(error)) from error
    except json.JSONDecodeError as error:
        if error.msg == "Extra data":
            detail = "expected exactly one YAML document"
        else:
            detail = f"yq produced invalid JSON: {error}"
        raise WorkflowLoadError(detail) from error


def _job_location(name: str) -> str:
    return f".jobs[{json.dumps(name)}]"


def _events(value: Any) -> tuple[set[str], list[Issue]]:
    if isinstance(value, str):
        return {value}, []
    if isinstance(value, list):
        if all(isinstance(event, str) for event in value):
            return set(value), []
        return set(), [
            Issue(".on", "workflow trigger list must contain only event names")
        ]
    if isinstance(value, Mapping):
        # JSON object keys are strings. yq has already resolved aliases and
        # explicit YAML tags, so an aliased ``pull_request`` key is visible
        # here just like a literal one.
        return set(value), []
    return set(), [
        Issue(
            ".on",
            "workflow triggers must be a string, list, or mapping",
        )
    ]


def _permission_issues(
    value: Any, *, location: str, owner: str
) -> list[Issue]:
    if value == "read-all":
        return []
    if value == "write-all":
        return [Issue(location, f"{owner} grants `write-all`")]
    if not isinstance(value, Mapping):
        return [
            Issue(location, f"cannot safely interpret {owner} permissions")
        ]

    issues: list[Issue] = []
    for scope, permission in value.items():
        scope_location = f"{location}[{json.dumps(scope)}]"
        if permission == "write":
            issues.append(
                Issue(scope_location, f"{owner} grants `{scope}: write`")
            )
        elif not isinstance(permission, str) or permission not in {
            "none",
            "read",
        }:
            issues.append(
                Issue(
                    scope_location,
                    f"cannot safely interpret {owner} permission "
                    f"`{scope}: {permission}`",
                )
            )
    return issues


def analyze_workflow(workflow: Any) -> list[Issue]:
    """Returns security or ambiguity findings for one decoded workflow."""

    if not isinstance(workflow, Mapping):
        return [Issue("$", "workflow document must be a mapping")]
    if "on" not in workflow:
        return [Issue(".on", "workflow has no top-level `on` key")]

    events, issues = _events(workflow["on"])
    if issues:
        return issues

    jobs = workflow.get("jobs")
    if not isinstance(jobs, Mapping):
        issues.append(Issue(".jobs", "workflow `jobs` must be a mapping"))
        jobs = {}
    else:
        for name, job in jobs.items():
            location = _job_location(name)
            if not isinstance(job, Mapping):
                issues.append(Issue(location, "job must be a mapping"))

    if not events.intersection(_UNTRUSTED_EVENTS):
        return sorted(issues, key=lambda issue: (issue.location, issue.message))

    # Without a workflow-level cap, jobs which omit ``permissions`` inherit the
    # repository or organization default. That default is mutable external
    # state and may be read/write, so explicit job permissions are not enough
    # to establish a safe baseline.
    if "permissions" not in workflow:
        issues.append(
            Issue(
                ".permissions",
                "untrusted workflow must declare explicit top-level "
                "`permissions`",
            )
        )
    else:
        issues.extend(
            _permission_issues(
                workflow["permissions"],
                location=".permissions",
                owner="workflow",
            )
        )

    for name, job in jobs.items():
        if not isinstance(job, Mapping) or "permissions" not in job:
            continue
        location = f"{_job_location(name)}.permissions"
        issues.extend(
            _permission_issues(
                job["permissions"],
                location=location,
                owner=f"job `{name}`",
            )
        )

    return sorted(issues, key=lambda issue: (issue.location, issue.message))


def _workflow_paths(arguments: Iterable[str]) -> tuple[list[pathlib.Path], list[str]]:
    paths: list[pathlib.Path] = []
    errors: list[str] = []
    seen: set[pathlib.Path] = set()
    for argument in arguments:
        candidate = pathlib.Path(argument)
        if candidate.is_dir():
            discovered = sorted(
                path
                for path in candidate.rglob("*")
                if path.is_file() and path.suffix.lower() in _WORKFLOW_SUFFIXES
            )
            if not discovered:
                errors.append(f"{candidate}: directory contains no workflow YAML files")
            candidates = discovered
        elif candidate.is_file():
            candidates = [candidate]
        else:
            errors.append(f"{candidate}: no such workflow file or directory")
            continue

        for path in candidates:
            resolved = path.resolve()
            if resolved not in seen:
                seen.add(resolved)
                paths.append(path)
    return paths, errors


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--yq",
        default=os.environ.get("YQ", "yq"),
        help="mikefarah/yq binary supplied by ci/check_actions.sh",
    )
    parser.add_argument(
        "paths",
        nargs="+",
        help="workflow YAML files or directories to scan recursively",
    )
    arguments = parser.parse_args(argv)

    paths, errors = _workflow_paths(arguments.paths)
    for error in errors:
        print(error, file=sys.stderr)

    failed = bool(errors)
    for path in paths:
        try:
            workflow = load_workflow(path, arguments.yq)
        except WorkflowLoadError as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue
        for issue in analyze_workflow(workflow):
            print(
                f"{path}:{issue.location}: {issue.message}",
                file=sys.stderr,
            )
            failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
