#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Fail closed unless every required GitHub Actions job succeeded."""

from __future__ import annotations

import json
import os
import sys
from collections.abc import Mapping, Sequence
from pathlib import Path


KNOWN_RESULTS = frozenset({"success", "failure", "cancelled", "skipped"})


class InputError(ValueError):
    """An action input does not have the required shape."""


def parse_json_object(value: str, description: str) -> dict[str, object]:
    try:
        parsed = json.loads(value)
    except json.JSONDecodeError as error:
        raise InputError(f"{description} is not valid JSON: {error}") from error
    if not isinstance(parsed, dict):
        raise InputError(f"{description} must be a JSON object")
    return parsed


def parse_allowed_skips(value: str) -> list[str]:
    try:
        parsed = json.loads(value)
    except json.JSONDecodeError as error:
        raise InputError(
            f"allowed-skipped-jobs is not valid JSON: {error}"
        ) from error
    if not isinstance(parsed, list) or not all(
        isinstance(job, str) and job for job in parsed
    ):
        raise InputError(
            "allowed-skipped-jobs must be a JSON array of nonempty job IDs"
        )
    if len(parsed) != len(set(parsed)):
        raise InputError("allowed-skipped-jobs contains duplicate job IDs")
    return parsed


def job_results(needs: Mapping[str, object]) -> dict[str, str]:
    if not needs:
        raise InputError("needs-json must contain at least one required job")

    results = {}
    for job, value in needs.items():
        if not isinstance(job, str) or not job:
            raise InputError("needs-json contains an invalid job ID")
        if not isinstance(value, Mapping):
            raise InputError(f"needs-json entry {job!r} must be an object")
        result = value.get("result")
        if not isinstance(result, str):
            raise InputError(f"needs-json entry {job!r} has no string result")
        if result not in KNOWN_RESULTS:
            raise InputError(
                f"needs-json entry {job!r} has unknown result {result!r}"
            )
        results[job] = result
    return results


def evaluate(
    results: Mapping[str, str],
    *,
    allowed_skipped_jobs: Sequence[str],
) -> list[str]:
    """Returns every reason that the required gate must fail."""

    errors = []
    allowed = set(allowed_skipped_jobs)
    missing_allowed = allowed - set(results)
    if missing_allowed:
        errors.append(
            "skip policy names jobs absent from needs: "
            + ", ".join(sorted(missing_allowed))
        )
    for job, result in sorted(results.items()):
        if result == "success":
            continue
        if result == "skipped" and job in allowed:
            continue
        if result == "skipped":
            errors.append(f"{job} was unexpectedly skipped")
        else:
            errors.append(f"{job} concluded {result}")
    return errors


def summary(results: Mapping[str, str], allowed_skipped_jobs: Sequence[str]) -> str:
    allowed = set(allowed_skipped_jobs)
    lines = [
        "## Required job results",
        "",
        "| Job | Result | Policy |",
        "| --- | --- | --- |",
    ]
    for job, result in sorted(results.items()):
        policy = "skip allowed" if job in allowed else "must succeed"
        lines.append(f"| `{job}` | `{result}` | {policy} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    try:
        needs = parse_json_object(
            os.environ.get("REQUIRED_JOBS_NEEDS_JSON", ""), "needs-json"
        )
        allowed = parse_allowed_skips(
            os.environ.get("REQUIRED_JOBS_ALLOWED_SKIPPED", "")
        )
        results = job_results(needs)
        errors = evaluate(
            results,
            allowed_skipped_jobs=allowed,
        )
    except InputError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1

    report = summary(results, allowed)
    summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
    if summary_path:
        with Path(summary_path).open("a", encoding="utf-8") as output:
            output.write(report)
    else:
        print(report, end="")

    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
