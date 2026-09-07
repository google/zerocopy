#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Require every Kani 0.67 cover property to be satisfied.

Kani 0.67 deliberately excludes `kani::cover!` properties from its overall
verification status. Its exact renderer and per-harness file writer are:

https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/cbmc_property_renderer.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/call_cbmc.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/harness_runner.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/cbmc_output_parser.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani_metadata/src/lib.rs

This checker consumes one fresh `--target-dir` produced by a single Kani
invocation with `-Zunstable-options --output-into-files`. It independently
requires a complete per-harness result inventory, the exact Kani 0.67 result
structure, and a SATISFIED status for every cover-class property.

In that exact release, `Property::property_name` renders either
`<function>.cover.<integer>` or `cover.<integer>` when `is_cover_property`
recognizes the `cover` class. `COVER_PROPERTY_RE` mirrors only that audited
format; it is deliberately not a version-independent Kani format claim.
"""

import json
import re
import stat
import sys
from pathlib import Path, PurePosixPath


CHECK_RE = re.compile(r"Check ([1-9][0-9]*): (.+)")
STATUS_RE = re.compile(r"\t - Status: ([A-Z]+)")
MAIN_SUMMARY_RE = re.compile(
    r" \*\* ([0-9]+) of ([0-9]+) failed(?: \(([^()]*)\))?"
)
COVER_SUMMARY_RE = re.compile(
    r" \*\* ([0-9]+) of ([0-9]+) cover properties satisfied(?: \(([^()]*)\))?"
)
SUCCESS_RE = re.compile(
    r"VERIFICATION:- SUCCESSFUL"
    r"(?: \(encountered one or more panics as expected\))?"
)
TIME_RE = re.compile(
    r"Verification Time: (?:0|[1-9][0-9]*)"
    r"(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?s"
)
COVER_PROPERTY_RE = re.compile(r"(?:^|\.)cover\.[0-9]+$")
NONCOVER_STATUSES = {
    "FAILURE",
    "SUCCESS",
    "UNDETERMINED",
    "UNREACHABLE",
}
COVER_STATUSES = {"SATISFIED", "UNDETERMINED", "UNREACHABLE", "UNSATISFIABLE"}
KNOWN_STATUSES = NONCOVER_STATUSES | COVER_STATUSES


class ValidationError(Exception):
    """A fail-closed Kani output validation error."""


def _read_text(path):
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise ValidationError(f"cannot read {path}: {error}") from error
    if not text:
        raise ValidationError(f"empty result file: {path}")
    if not text.endswith("\n"):
        raise ValidationError(f"result file lacks Kani's final newline: {path}")
    return text


def _only_match(lines, pattern, description, path):
    matches = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := pattern.fullmatch(line))
    ]
    if len(matches) != 1:
        raise ValidationError(
            f"{path}: expected exactly one {description}; found {len(matches)}"
        )
    return matches[0]


def _expected_breakdown(statuses):
    breakdown = []
    for status_value, label in (
        ("UNDETERMINED", "undetermined"),
        ("UNREACHABLE", "unreachable"),
    ):
        count = statuses.count(status_value)
        if count:
            breakdown.append(f"{count} {label}")
    return ",".join(breakdown) or None


def _parse_result(path):
    lines = _read_text(path).splitlines()
    cursor = 0
    if lines and re.fullmatch(r"Thread [0-9]+:", lines[0]):
        cursor += 1
    if lines[cursor : cursor + 2] != ["", "RESULTS:"]:
        raise ValidationError(f"{path}: missing exact Kani RESULTS header")
    results_index = cursor + 1

    if sum(line == "RESULTS:" for line in lines) != 1:
        raise ValidationError(f"{path}: duplicate Kani RESULTS header")
    summary_indices = [index for index, line in enumerate(lines) if line == "SUMMARY:"]
    if len(summary_indices) != 1:
        raise ValidationError(
            f"{path}: expected exactly one Kani SUMMARY header; found {len(summary_indices)}"
        )
    summary_index = summary_indices[0]
    if summary_index <= results_index:
        raise ValidationError(f"{path}: Kani SUMMARY precedes RESULTS")

    check_headers = []
    for index, line in enumerate(lines):
        match = CHECK_RE.fullmatch(line)
        if line.startswith("Check ") and match is None:
            raise ValidationError(f"{path}:{index + 1}: malformed Kani check header")
        if match is not None:
            if not results_index < index < summary_index:
                raise ValidationError(f"{path}:{index + 1}: check outside RESULTS section")
            check_headers.append((index, match))

    cover_statuses = []
    noncover_statuses = []
    for ordinal, (index, match) in enumerate(check_headers, start=1):
        if int(match.group(1)) != ordinal:
            raise ValidationError(
                f"{path}:{index + 1}: noncontiguous check number {match.group(1)}; "
                f"expected {ordinal}"
            )
        block_end = (
            check_headers[ordinal][0] if ordinal < len(check_headers) else summary_index
        )
        block = lines[index + 1 : block_end]
        status_matches = [STATUS_RE.fullmatch(line) for line in block]
        statuses = [status.group(1) for status in status_matches if status is not None]
        if len(statuses) != 1:
            raise ValidationError(
                f"{path}:{index + 1}: expected exactly one status for check {ordinal}"
            )
        status_value = statuses[0]
        if status_value not in KNOWN_STATUSES:
            raise ValidationError(
                f"{path}:{index + 1}: unknown Kani status {status_value!r}"
            )
        descriptions = [line for line in block if line.startswith('\t - Description: "')]
        if len(descriptions) != 1:
            raise ValidationError(
                f"{path}:{index + 1}: expected exactly one description for check {ordinal}"
            )

        property_name = match.group(2)
        if COVER_PROPERTY_RE.search(property_name):
            if status_value not in COVER_STATUSES:
                raise ValidationError(
                    f"{path}:{index + 1}: cover-class property has impossible "
                    f"Kani 0.67 status {status_value!r}"
                )
            cover_statuses.append((property_name, status_value))
        else:
            if status_value not in NONCOVER_STATUSES:
                raise ValidationError(
                    f"{path}:{index + 1}: non-cover property has impossible "
                    f"Kani 0.67 status {status_value!r}"
                )
            noncover_statuses.append(status_value)

    main_index, main_match = _only_match(
        lines, MAIN_SUMMARY_RE, "normal-property summary", path
    )
    if not summary_index < main_index:
        raise ValidationError(f"{path}: normal-property summary precedes SUMMARY header")
    reported_failed = int(main_match.group(1))
    reported_noncover = int(main_match.group(2))
    reported_breakdown = main_match.group(3)
    failed_noncover_checks = noncover_statuses.count("FAILURE")
    actual_noncover = len(noncover_statuses)
    if (reported_failed, reported_noncover) != (failed_noncover_checks, actual_noncover):
        raise ValidationError(
            f"{path}: normal-property summary reports {reported_failed} of "
            f"{reported_noncover}, but parsed {failed_noncover_checks} of {actual_noncover}"
        )
    expected_breakdown = _expected_breakdown(noncover_statuses)
    if reported_breakdown != expected_breakdown:
        raise ValidationError(
            f"{path}: normal-property summary breakdown is {reported_breakdown!r}, "
            f"but parsed {expected_breakdown!r}"
        )

    cover_summaries = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := COVER_SUMMARY_RE.fullmatch(line))
    ]
    malformed_cover_summaries = [
        index
        for index, line in enumerate(lines)
        if "cover properties satisfied" in line and COVER_SUMMARY_RE.fullmatch(line) is None
    ]
    if malformed_cover_summaries:
        raise ValidationError(
            f"{path}:{malformed_cover_summaries[0] + 1}: malformed cover summary"
        )

    satisfied = sum(status_value == "SATISFIED" for _, status_value in cover_statuses)
    cover_index = None
    if cover_statuses:
        if len(cover_summaries) != 1:
            raise ValidationError(
                f"{path}: expected exactly one cover summary for "
                f"{len(cover_statuses)} cover checks; found {len(cover_summaries)}"
            )
        cover_index, cover_match = cover_summaries[0]
        if not main_index < cover_index:
            raise ValidationError(f"{path}: cover summary precedes normal-property summary")
        reported_satisfied = int(cover_match.group(1))
        reported_cover = int(cover_match.group(2))
        reported_breakdown = cover_match.group(3)
        if (reported_satisfied, reported_cover) != (satisfied, len(cover_statuses)):
            raise ValidationError(
                f"{path}: cover summary reports {reported_satisfied} of {reported_cover}, "
                f"but parsed {satisfied} of {len(cover_statuses)}"
            )
        expected_breakdown = _expected_breakdown(
            [status_value for _, status_value in cover_statuses]
        )
        if reported_breakdown != expected_breakdown:
            raise ValidationError(
                f"{path}: cover summary breakdown is {reported_breakdown!r}, "
                f"but parsed {expected_breakdown!r}"
            )
    elif cover_summaries:
        raise ValidationError(f"{path}: cover summary exists without cover-class checks")

    success_index, _ = _only_match(lines, SUCCESS_RE, "successful verification result", path)
    time_index, _ = _only_match(lines, TIME_RE, "verification-time footer", path)
    summary_order = [summary_index, main_index]
    if cover_index is not None:
        summary_order.append(cover_index)
    summary_order.extend((success_index, time_index))
    if summary_order != sorted(summary_order) or len(summary_order) != len(set(summary_order)):
        raise ValidationError(f"{path}: malformed Kani summary/footer ordering")
    if any(line for line in lines[time_index + 1 :]):
        raise ValidationError(f"{path}: nonempty data follows Kani's verification-time footer")

    unsatisfied = [
        (property_name, status_value)
        for property_name, status_value in cover_statuses
        if status_value != "SATISFIED"
    ]
    if unsatisfied:
        property_name, status_value = unsatisfied[0]
        raise ValidationError(
            f"{path}: cover property {property_name!r} is {status_value}, not SATISFIED"
        )
    return len(cover_statuses)


def _load_expected_harnesses(target_dir):
    metadata_dir = target_dir / "kani"
    if not metadata_dir.is_dir():
        raise ValidationError(f"missing Kani metadata directory: {metadata_dir}")
    metadata_files = sorted(metadata_dir.rglob("*.kani-metadata.json"))
    if len(metadata_files) != 1:
        raise ValidationError(
            "fresh Kani target must contain exactly one metadata inventory; "
            f"found {len(metadata_files)}"
        )

    metadata_path = metadata_files[0]
    try:
        data = json.loads(metadata_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot parse {metadata_path}: {error}") from error
    if not isinstance(data, dict):
        raise ValidationError(f"{metadata_path}: Kani metadata root is not an object")

    expected_names = []
    for key in ("proof_harnesses", "test_harnesses"):
        harnesses = data.get(key)
        if not isinstance(harnesses, list):
            raise ValidationError(f"{metadata_path}: metadata field {key!r} is not an array")
        for index, harness in enumerate(harnesses):
            if not isinstance(harness, dict):
                raise ValidationError(f"{metadata_path}: {key}[{index}] is not an object")
            name = harness.get("pretty_name")
            if not isinstance(name, str) or not name:
                raise ValidationError(
                    f"{metadata_path}: {key}[{index}].pretty_name is not a nonempty string"
                )
            parsed_name = PurePosixPath(name)
            if parsed_name.is_absolute() or any(
                part in ("", ".", "..") for part in parsed_name.parts
            ):
                raise ValidationError(
                    f"{metadata_path}: unsafe harness result path in pretty_name {name!r}"
                )
            expected_names.append(name)

    if not expected_names:
        raise ValidationError(f"{metadata_path}: metadata contains no selected harnesses")
    if len(expected_names) != len(set(expected_names)):
        raise ValidationError(f"{metadata_path}: duplicate harness pretty_name")
    return set(expected_names)


def _load_result_files(target_dir):
    result_dir = target_dir / "result_output_dir"
    if not result_dir.is_dir():
        raise ValidationError(f"missing Kani result directory: {result_dir}")

    results = {}
    for path in result_dir.rglob("*"):
        try:
            mode = path.lstat().st_mode
        except OSError as error:
            raise ValidationError(f"cannot inspect {path}: {error}") from error
        if stat.S_ISDIR(mode):
            continue
        if not stat.S_ISREG(mode):
            raise ValidationError(f"non-regular Kani result path: {path}")
        name = path.relative_to(result_dir).as_posix()
        results[name] = path
    if not results:
        raise ValidationError(f"no per-harness result files below {result_dir}")
    return results


def _abbreviate(names):
    ordered = sorted(names)
    shown = ", ".join(repr(name) for name in ordered[:10])
    if len(ordered) > 10:
        shown += f", ... ({len(ordered) - 10} more)"
    return shown


def validate(target_dir):
    expected = _load_expected_harnesses(target_dir)
    results = _load_result_files(target_dir)
    actual = set(results)
    missing = expected - actual
    unexpected = actual - expected
    if missing or unexpected:
        details = []
        if missing:
            details.append(f"missing: {_abbreviate(missing)}")
        if unexpected:
            details.append(f"unexpected: {_abbreviate(unexpected)}")
        raise ValidationError("Kani result inventory mismatch (" + "; ".join(details) + ")")

    cover_count = sum(_parse_result(results[name]) for name in sorted(expected))
    return len(expected), cover_count


def main(argv):
    if len(argv) != 2:
        print(f"usage: {argv[0]} KANI_TARGET_DIR", file=sys.stderr)
        return 2
    target_dir = Path(argv[1])
    try:
        harness_count, cover_count = validate(target_dir)
    except ValidationError as error:
        print(f"{Path(argv[0]).name}: {error}", file=sys.stderr)
        return 1
    print(
        f"validated {harness_count} Kani harness result files; "
        f"all {cover_count} cover properties are SATISFIED"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
