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
verification status. Its exact property parser, renderer, per-harness writer,
and metadata schema are pinned here:

https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/cbmc_output_parser.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/cbmc_property_renderer.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/call_cbmc.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani-driver/src/harness_runner.rs
https://github.com/model-checking/kani/blob/4feaaad1d6a2378a6ff6caa3b4fc5d6999c7bb5d/kani_metadata/src/lib.rs

This checker consumes one fresh, private `--target-dir` produced by a single,
unfiltered Kani invocation with `-Zunstable-options --output-into-files`. Kani
metadata describes the harnesses discovered in the crate, so result/metadata
inventory equality is intentionally also a no-filter protocol check. Each
filesystem component below the target must be an actual directory or regular
file, never a symlink.

The result parser accepts only the Kani 0.67 regular renderer's ordered record
grammar. The renderer does not escape descriptions, so this parser supports
the multiline descriptions present in the audited zerocopy corpus but rejects
control-record text inside a multiline description. This conservative subset
avoids treating an injected record as verification evidence.
"""

import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath

U32_MAX = (1 << 32) - 1
U64_MAX = (1 << 64) - 1
UINT_RE = re.compile(r"0|[1-9][0-9]*")
PROPERTY_CLASS_RE = re.compile(r"NaN|[a-z_-]+")
CHECK_RE = re.compile(r"Check ([1-9][0-9]*): (.+)")
THREAD_RE = re.compile(r"Thread (0|[1-9][0-9]*):")
STATUS_RE = re.compile(r"\t - Status: ([A-Z]+)")
LOCATION_RE = re.compile(r"\t - Location: (.+)")
FAILURE_LOCATION_RE = re.compile(r' File: "(.*)", line (0|[1-9][0-9]*), in (.*)')
# `Duration::as_secs_f32()` is rendered with Rust's ordinary `Display`, not
# exponential formatting. `Display` omits redundant leading/trailing zeroes.
TIME_RE = re.compile(r"Verification Time: (?:0|[1-9][0-9]*)(?:\.[0-9]*[1-9])?s")
DESCRIPTION_PREFIX = '\t - Description: "'
NONCOVER_STATUSES = {
    "FAILURE",
    "SUCCESS",
    "UNDETERMINED",
    "UNREACHABLE",
}
COVER_STATUSES = {"SATISFIED", "UNDETERMINED", "UNREACHABLE", "UNSATISFIABLE"}
KNOWN_STATUSES = NONCOVER_STATUSES | COVER_STATUSES
MULTILINE_DESCRIPTION_CONTROL_PREFIXES = (
    "Check ",
    "\t - Status:",
    "\t - Description:",
    "\t - Location:",
    "SUMMARY:",
    " ** ",
    "Failed Checks:",
    " File:",
    "VERIFICATION:-",
    "Verification Time:",
    "Thread ",
)


class ValidationError(Exception):
    """A fail-closed Kani output validation error."""


def _read_lines(path):
    try:
        text = path.read_bytes().decode("utf-8")
    except (OSError, UnicodeError) as error:
        raise ValidationError(f"cannot read {path}: {error}") from error
    if not text:
        raise ValidationError(f"empty result file: {path}")
    if "\r" in text or "\0" in text:
        raise ValidationError(f"{path}: result contains a non-Kani control character")
    if not text.endswith("\n"):
        raise ValidationError(f"result file lacks Kani's final newline: {path}")
    lines = text.split("\n")
    lines.pop()
    return lines


def _canonical_uint(token, maximum, description, path, line_number=None):
    where = str(path)
    if line_number is not None:
        where += f":{line_number}"
    if UINT_RE.fullmatch(token) is None:
        raise ValidationError(f"{where}: noncanonical {description} {token!r}")
    value = int(token)
    if value > maximum:
        raise ValidationError(f"{where}: {description} exceeds {maximum}: {token}")
    return value


def _property_class(property_name, path, line_number):
    if property_name != property_name.strip() or any(
        ord(character) < 0x20 or ord(character) == 0x7F for character in property_name
    ):
        raise ValidationError(
            f"{path}:{line_number}: noncanonical whitespace/control in Kani property name"
        )
    attributes = property_name.rsplit(".", 2)
    if len(attributes) == 2:
        property_class, property_id = attributes
    elif len(attributes) == 3:
        function, property_class, property_id = attributes
        if not function:
            raise ValidationError(
                f"{path}:{line_number}: empty function in Kani property name"
            )
    else:
        raise ValidationError(
            f"{path}:{line_number}: malformed Kani property name {property_name!r}"
        )
    if PROPERTY_CLASS_RE.fullmatch(property_class) is None:
        raise ValidationError(
            f"{path}:{line_number}: malformed Kani property class {property_class!r}"
        )
    _canonical_uint(property_id, U32_MAX, "Kani property id", path, line_number)
    return property_class


def _need_line(lines, cursor, expected, path, description):
    if cursor >= len(lines) or lines[cursor] != expected:
        actual = "end of file" if cursor >= len(lines) else repr(lines[cursor])
        raise ValidationError(
            f"{path}:{cursor + 1}: expected {description} {expected!r}; found {actual}"
        )
    return cursor + 1


def _parse_description(lines, cursor, path, ordinal):
    if cursor >= len(lines) or not lines[cursor].startswith(DESCRIPTION_PREFIX):
        actual = "end of file" if cursor >= len(lines) else repr(lines[cursor])
        raise ValidationError(
            f"{path}:{cursor + 1}: expected description for check {ordinal}; found {actual}"
        )

    first = lines[cursor][len(DESCRIPTION_PREFIX) :]
    cursor += 1
    if first.endswith('"'):
        return first[:-1], cursor
    if '"' in first:
        raise ValidationError(
            f"{path}:{cursor}: ambiguous quote in multiline description for check {ordinal}"
        )

    description_lines = [first]
    while cursor < len(lines):
        line = lines[cursor]
        if line.startswith(MULTILINE_DESCRIPTION_CONTROL_PREFIXES):
            raise ValidationError(
                f"{path}:{cursor + 1}: control record in unterminated description "
                f"for check {ordinal}"
            )
        cursor += 1
        if line.endswith('"'):
            if '"' in line[:-1]:
                raise ValidationError(
                    f"{path}:{cursor}: ambiguous quote in multiline description "
                    f"for check {ordinal}"
                )
            description_lines.append(line[:-1])
            return "\n".join(description_lines), cursor
        if '"' in line:
            raise ValidationError(
                f"{path}:{cursor}: ambiguous quote in multiline description for check {ordinal}"
            )
        description_lines.append(line)

    raise ValidationError(f"{path}: unterminated description for check {ordinal}")


def _parse_check(lines, cursor, ordinal, path):
    line_number = cursor + 1
    match = CHECK_RE.fullmatch(lines[cursor])
    if match is None:
        raise ValidationError(f"{path}:{line_number}: malformed Kani check header")
    rendered_ordinal = _canonical_uint(
        match.group(1), sys.maxsize, "Kani check number", path, line_number
    )
    if rendered_ordinal != ordinal:
        raise ValidationError(
            f"{path}:{line_number}: noncontiguous check number {rendered_ordinal}; "
            f"expected {ordinal}"
        )
    property_name = match.group(2)
    property_class = _property_class(property_name, path, line_number)
    cursor += 1

    if cursor >= len(lines):
        raise ValidationError(f"{path}: missing status for check {ordinal}")
    status_match = STATUS_RE.fullmatch(lines[cursor])
    if status_match is None:
        raise ValidationError(
            f"{path}:{cursor + 1}: malformed status for check {ordinal}"
        )
    status_value = status_match.group(1)
    if status_value not in KNOWN_STATUSES:
        raise ValidationError(
            f"{path}:{cursor + 1}: unknown Kani status {status_value!r}"
        )
    cursor += 1

    description, cursor = _parse_description(lines, cursor, path, ordinal)
    if cursor < len(lines) and lines[cursor].startswith("\t - Location:"):
        if LOCATION_RE.fullmatch(lines[cursor]) is None:
            raise ValidationError(
                f"{path}:{cursor + 1}: malformed location for check {ordinal}"
            )
        cursor += 1
    cursor = _need_line(
        lines, cursor, "", path, f"record terminator for check {ordinal}"
    )

    is_cover = property_class == "cover"
    allowed_statuses = COVER_STATUSES if is_cover else NONCOVER_STATUSES
    if status_value not in allowed_statuses:
        kind = "cover" if is_cover else "non-cover"
        raise ValidationError(
            f"{path}:{line_number}: {kind} property has impossible Kani 0.67 "
            f"status {status_value!r}"
        )
    return {
        "name": property_name,
        "class": property_class,
        "status": status_value,
        "description": description,
    }, cursor


def _expected_breakdown(statuses):
    breakdown = []
    for status_value, label in (
        ("UNDETERMINED", "undetermined"),
        ("UNREACHABLE", "unreachable"),
    ):
        count = statuses.count(status_value)
        if count:
            breakdown.append(f"{count} {label}")
    return ",".join(breakdown)


def _expected_summary(kind, statuses):
    if kind == "normal":
        summary = f" ** {statuses.count('FAILURE')} of {len(statuses)} failed"
    else:
        summary = (
            f" ** {statuses.count('SATISFIED')} of {len(statuses)} "
            "cover properties satisfied"
        )
    breakdown = _expected_breakdown(statuses)
    if breakdown:
        summary += f" ({breakdown})"
    return summary


def _parse_failure_details(lines, cursor, failed_checks, path):
    for check in failed_checks:
        description_lines = check["description"].split("\n")
        cursor = _need_line(
            lines,
            cursor,
            "Failed Checks: " + description_lines[0],
            path,
            f"failure detail for {check['name']!r}",
        )
        for description_line in description_lines[1:]:
            cursor = _need_line(
                lines,
                cursor,
                description_line,
                path,
                f"multiline failure detail for {check['name']!r}",
            )
        if cursor < len(lines) and lines[cursor].startswith(" File:"):
            location_match = FAILURE_LOCATION_RE.fullmatch(lines[cursor])
            if location_match is None:
                raise ValidationError(
                    f"{path}:{cursor + 1}: malformed failed-check location"
                )
            _canonical_uint(
                location_match.group(2),
                U64_MAX,
                "failed-check line number",
                path,
                cursor + 1,
            )
            cursor += 1
    return cursor


def _parse_result(path, should_panic):
    lines = _read_lines(path)
    cursor = 0
    if cursor < len(lines) and lines[cursor].startswith("Thread "):
        thread_match = THREAD_RE.fullmatch(lines[cursor])
        if thread_match is None:
            raise ValidationError(f"{path}:1: malformed Kani thread header")
        _canonical_uint(
            thread_match.group(1), sys.maxsize, "Kani thread index", path, 1
        )
        cursor += 1
    cursor = _need_line(lines, cursor, "", path, "blank line before RESULTS")
    cursor = _need_line(lines, cursor, "RESULTS:", path, "Kani RESULTS header")

    checks = []
    while cursor < len(lines):
        if lines[cursor].startswith("Check "):
            check, cursor = _parse_check(lines, cursor, len(checks) + 1, path)
            checks.append(check)
            continue
        if (
            lines[cursor] == ""
            and cursor + 1 < len(lines)
            and lines[cursor + 1] == "SUMMARY:"
        ):
            cursor += 2
            break
        raise ValidationError(
            f"{path}:{cursor + 1}: unexpected record in Kani RESULTS section: "
            f"{lines[cursor]!r}"
        )
    else:
        raise ValidationError(f"{path}: missing Kani SUMMARY header")

    cover_checks = [check for check in checks if check["class"] == "cover"]
    noncover_checks = [check for check in checks if check["class"] != "cover"]
    cover_statuses = [check["status"] for check in cover_checks]
    noncover_statuses = [check["status"] for check in noncover_checks]

    expected_main = _expected_summary("normal", noncover_statuses)
    cursor = _need_line(
        lines, cursor, expected_main, path, "canonical normal-property summary"
    )
    if cover_checks:
        cursor = _need_line(lines, cursor, "", path, "blank line before cover summary")
        expected_cover = _expected_summary("cover", cover_statuses)
        cursor = _need_line(
            lines, cursor, expected_cover, path, "canonical cover-property summary"
        )
        cursor = _need_line(lines, cursor, "", path, "blank line after cover summary")

    failed_checks = [check for check in noncover_checks if check["status"] == "FAILURE"]
    if failed_checks:
        cursor = _parse_failure_details(lines, cursor, failed_checks, path)
    cursor = _need_line(lines, cursor, "", path, "blank line before result banner")

    if should_panic:
        if not failed_checks:
            raise ValidationError(
                f"{path}: expected-panic success contains no failed assertion property"
            )
        non_assertion_failure = next(
            (check["name"] for check in failed_checks if check["class"] != "assertion"),
            None,
        )
        if non_assertion_failure is not None:
            raise ValidationError(
                f"{path}: expected-panic success contains non-assertion failure "
                f"{non_assertion_failure!r}"
            )
        expected_banner = (
            "VERIFICATION:- SUCCESSFUL " "(encountered one or more panics as expected)"
        )
    else:
        if failed_checks:
            raise ValidationError(
                f"{path}: ordinary successful verification contains failed property "
                f"{failed_checks[0]['name']!r}"
            )
        expected_banner = "VERIFICATION:- SUCCESSFUL"
    cursor = _need_line(lines, cursor, expected_banner, path, "Kani success banner")

    if cursor >= len(lines) or TIME_RE.fullmatch(lines[cursor]) is None:
        actual = "end of file" if cursor >= len(lines) else repr(lines[cursor])
        raise ValidationError(
            f"{path}:{cursor + 1}: expected canonical verification-time footer; "
            f"found {actual}"
        )
    cursor += 1
    cursor = _need_line(lines, cursor, "", path, "writer's final blank line")
    if cursor != len(lines):
        raise ValidationError(f"{path}:{cursor + 1}: nonempty data follows Kani footer")

    undetermined_noncover = next(
        (
            check["name"]
            for check in noncover_checks
            if check["status"] == "UNDETERMINED"
        ),
        None,
    )
    if undetermined_noncover is not None:
        raise ValidationError(
            f"{path}: successful verification contains undetermined non-cover property "
            f"{undetermined_noncover!r}"
        )
    unsatisfied_cover = next(
        (check for check in cover_checks if check["status"] != "SATISFIED"), None
    )
    if unsatisfied_cover is not None:
        raise ValidationError(
            f"{path}: cover property {unsatisfied_cover['name']!r} is "
            f"{unsatisfied_cover['status']}, not SATISFIED"
        )
    return len(cover_checks)


def _require_real_directory(path, description):
    try:
        mode = path.lstat().st_mode
    except OSError as error:
        raise ValidationError(
            f"cannot inspect {description} {path}: {error}"
        ) from error
    if not stat.S_ISDIR(mode):
        raise ValidationError(f"{description} is not a real directory: {path}")


def _walk_real_files(root, description):
    """Yield regular files without following any symlink below `root`."""

    try:
        with os.scandir(root) as entries:
            ordered_entries = sorted(entries, key=lambda entry: entry.name)
    except OSError as error:
        raise ValidationError(
            f"cannot inspect {description} {root}: {error}"
        ) from error
    for entry in ordered_entries:
        path = Path(entry.path)
        try:
            mode = entry.stat(follow_symlinks=False).st_mode
        except OSError as error:
            raise ValidationError(f"cannot inspect {path}: {error}") from error
        if stat.S_ISLNK(mode):
            raise ValidationError(f"symlink is forbidden in {description}: {path}")
        if stat.S_ISDIR(mode):
            yield from _walk_real_files(path, description)
        elif stat.S_ISREG(mode):
            yield path
        else:
            raise ValidationError(f"non-regular path in {description}: {path}")


def _load_expected_harnesses(target_dir):
    _require_real_directory(target_dir, "Kani target")
    metadata_dir = target_dir / "kani"
    _require_real_directory(metadata_dir, "Kani metadata root")
    metadata_files = [
        path
        for path in _walk_real_files(metadata_dir, "Kani metadata tree")
        if path.name.endswith(".kani-metadata.json")
    ]
    if len(metadata_files) != 1:
        raise ValidationError(
            "fresh Kani target must contain exactly one metadata inventory; "
            f"found {len(metadata_files)}"
        )
    metadata_path = metadata_files[0]

    def object_without_duplicate_keys(pairs):
        value = {}
        for key, member in pairs:
            if key in value:
                raise ValidationError(
                    f"{metadata_path}: duplicate JSON object key {key!r}"
                )
            value[key] = member
        return value

    def reject_nonfinite_constant(token):
        raise ValidationError(f"{metadata_path}: non-finite JSON constant {token!r}")

    try:
        data = json.loads(
            metadata_path.read_text(encoding="utf-8"),
            object_pairs_hook=object_without_duplicate_keys,
            parse_constant=reject_nonfinite_constant,
        )
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise ValidationError(f"cannot parse {metadata_path}: {error}") from error
    if not isinstance(data, dict):
        raise ValidationError(f"{metadata_path}: Kani metadata root is not an object")

    expected = {}
    for key in ("proof_harnesses", "test_harnesses"):
        harnesses = data.get(key)
        if not isinstance(harnesses, list):
            raise ValidationError(
                f"{metadata_path}: metadata field {key!r} is not an array"
            )
        for index, harness in enumerate(harnesses):
            if not isinstance(harness, dict):
                raise ValidationError(
                    f"{metadata_path}: {key}[{index}] is not an object"
                )
            name = harness.get("pretty_name")
            if not isinstance(name, str) or not name:
                raise ValidationError(
                    f"{metadata_path}: {key}[{index}].pretty_name is not a nonempty string"
                )
            parsed_name = PurePosixPath(name)
            if (
                parsed_name.is_absolute()
                or parsed_name.as_posix() != name
                or any(part in ("", ".", "..") for part in parsed_name.parts)
            ):
                raise ValidationError(
                    f"{metadata_path}: unsafe harness result path in pretty_name {name!r}"
                )
            attributes = harness.get("attributes")
            if not isinstance(attributes, dict) or not isinstance(
                attributes.get("should_panic"), bool
            ):
                raise ValidationError(
                    f"{metadata_path}: {key}[{index}].attributes.should_panic "
                    "is not a boolean"
                )
            if name in expected:
                raise ValidationError(f"{metadata_path}: duplicate harness pretty_name")
            expected[name] = attributes["should_panic"]

    if not expected:
        raise ValidationError(
            f"{metadata_path}: metadata contains no discovered harnesses"
        )
    return expected


def _load_result_files(target_dir):
    result_dir = target_dir / "result_output_dir"
    _require_real_directory(result_dir, "Kani result root")
    results = {}
    for path in _walk_real_files(result_dir, "Kani result tree"):
        name = path.relative_to(result_dir).as_posix()
        if name in results:
            raise ValidationError(f"duplicate Kani result path: {name!r}")
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
    expected_names = set(expected)
    missing = expected_names - actual
    unexpected = actual - expected_names
    if missing or unexpected:
        details = []
        if missing:
            details.append(f"missing: {_abbreviate(missing)}")
        if unexpected:
            details.append(f"unexpected: {_abbreviate(unexpected)}")
        raise ValidationError(
            "Kani result inventory mismatch (" + "; ".join(details) + ")"
        )

    cover_count = sum(
        _parse_result(results[name], expected[name]) for name in sorted(expected)
    )
    if cover_count == 0:
        raise ValidationError(
            "unfiltered Kani result inventory contains no cover properties"
        )
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
