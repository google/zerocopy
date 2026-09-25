#!/usr/bin/env python3
"""Validate and index the reference corpus containing this script."""

from __future__ import annotations

import argparse
import datetime as _datetime
import json
import os
import re
import stat
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

REQUIRED_ROOT_FILES = ("AGENTS.md", "FORMAT.md", "README.md")
REQUIRED_ROOT_DIRS = ("tools", "tests")
METADATA_KEYS = frozenset({"topics", "subjects", "observed_at"})
SUBJECT_KEYS = frozenset({"name", "identity"})
TOPIC_RE = re.compile(r"^[a-z0-9][a-z0-9._+-]*(?:/[a-z0-9][a-z0-9._+-]*)*$")
PACKAGE_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")


@dataclass(frozen=True)
class Problem:
    path: Path
    message: str

    def render(self, root: Path) -> str:
        try:
            rel = self.path.relative_to(root)
        except ValueError:
            rel = self.path
        return f"{rel}: {self.message}"


@dataclass(frozen=True)
class Entry:
    path: Path
    kind: str


@dataclass(frozen=True)
class Report:
    directory: Path
    metadata: dict[str, Any]


class ValidationFailure(Exception):
    """Raised when corpus machine data cannot be read or interpreted safely."""


def _candidate_root() -> Path:
    # abspath keeps the invoked path lexical instead of resolving symlinks.
    return Path(os.path.abspath(__file__)).parent.parent


def _read_bytes(path: Path) -> bytes:
    try:
        return path.read_bytes()
    except OSError as exc:
        raise ValidationFailure(f"cannot read file: {exc}") from exc


def _read_text(path: Path) -> str:
    try:
        return _read_bytes(path).decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationFailure(f"not valid UTF-8: {exc}") from exc


def _directory_entries(path: Path) -> tuple[dict[str, Entry], list[Problem]]:
    """Enumerate exact entry names and no-follow types for one structural directory."""
    try:
        mode = os.lstat(path).st_mode
    except OSError as exc:
        return {}, [Problem(path, f"cannot inspect directory: {exc}")]
    if not stat.S_ISDIR(mode):
        return {}, [Problem(path, "must be an ordinary directory")]

    entries: dict[str, Entry] = {}
    problems: list[Problem] = []
    try:
        with os.scandir(path) as iterator:
            raw_entries = sorted(iterator, key=lambda entry: entry.name)
    except OSError as exc:
        return {}, [Problem(path, f"cannot enumerate directory: {exc}")]

    for raw in raw_entries:
        entry_path = Path(raw.path)
        try:
            if raw.is_symlink():
                kind = "symlink"
            elif raw.is_file(follow_symlinks=False):
                kind = "file"
            elif raw.is_dir(follow_symlinks=False):
                kind = "directory"
            else:
                kind = "other"
        except OSError as exc:
            problems.append(Problem(entry_path, f"cannot inspect entry: {exc}"))
            continue
        entries[raw.name] = Entry(entry_path, kind)
    return entries, problems


def _require_entry(
    entries: dict[str, Entry],
    parent: Path,
    name: str,
    kind: str,
) -> tuple[Path | None, list[Problem]]:
    entry = entries.get(name)
    path = parent / name
    if entry is None:
        return None, [Problem(path, f"required {kind} {name} is missing")]
    if entry.kind != kind:
        return None, [Problem(path, f"must be an ordinary {kind}; found {entry.kind}")]
    return entry.path, []


def _no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate object key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"invalid JSON constant {value}")


def _load_json(path: Path) -> Any:
    try:
        value = json.loads(
            _read_text(path),
            object_pairs_hook=_no_duplicate_keys,
            parse_constant=_reject_constant,
        )
        json.dumps(value, ensure_ascii=False).encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValidationFailure("JSON strings must contain valid Unicode scalar text") from exc
    except ValueError as exc:
        raise ValidationFailure(f"invalid JSON: {exc}") from exc
    return value


def _validate_metadata(metadata: Any, path: Path) -> list[Problem]:
    if not isinstance(metadata, dict):
        return [Problem(path, "report metadata must be a JSON object")]

    problems: list[Problem] = []
    unknown = sorted(set(metadata) - METADATA_KEYS)
    missing = sorted(METADATA_KEYS - set(metadata))
    if unknown:
        problems.append(Problem(path, f"unknown metadata keys: {', '.join(map(repr, unknown))}"))
    if missing:
        problems.append(Problem(path, f"missing metadata keys: {', '.join(missing)}"))

    topics = metadata.get("topics")
    if not isinstance(topics, list) or not topics:
        problems.append(Problem(path, "metadata 'topics' must be a non-empty array"))
    else:
        seen: set[str] = set()
        for idx, topic in enumerate(topics):
            if not isinstance(topic, str) or not topic:
                problems.append(Problem(path, f"topics[{idx}] must be a non-empty string"))
                continue
            if not TOPIC_RE.fullmatch(topic):
                problems.append(
                    Problem(
                        path,
                        f"topics[{idx}]={topic!r} must be lowercase slash-separated retrieval labels",
                    )
                )
            if topic in seen:
                problems.append(Problem(path, f"duplicate topic {topic!r}"))
            seen.add(topic)

    subjects = metadata.get("subjects")
    if not isinstance(subjects, list) or not subjects:
        problems.append(Problem(path, "metadata 'subjects' must be a non-empty array"))
    else:
        for idx, subject in enumerate(subjects):
            prefix = f"subjects[{idx}]"
            if not isinstance(subject, dict):
                problems.append(Problem(path, f"{prefix} must be an object"))
                continue
            unknown_subject = sorted(set(subject) - SUBJECT_KEYS)
            missing_subject = sorted(SUBJECT_KEYS - set(subject))
            if unknown_subject:
                problems.append(
                    Problem(path, f"{prefix} has unknown keys: {', '.join(map(repr, unknown_subject))}")
                )
            if missing_subject:
                problems.append(Problem(path, f"{prefix} is missing keys: {', '.join(missing_subject)}"))

            name = subject.get("name")
            if not isinstance(name, str) or not name.strip():
                problems.append(Problem(path, f"{prefix}.name must be a non-empty string"))

            identity = subject.get("identity")
            if not isinstance(identity, dict) or not identity:
                problems.append(Problem(path, f"{prefix}.identity must be a non-empty object"))
                continue
            for key, value in identity.items():
                if not key.strip():
                    problems.append(Problem(path, f"{prefix}.identity keys must be non-empty strings"))
                if not isinstance(value, str) or not value.strip():
                    problems.append(
                        Problem(path, f"{prefix}.identity[{key!r}] must be a non-empty string")
                    )

    observed_at = metadata.get("observed_at")
    if not isinstance(observed_at, str):
        problems.append(Problem(path, "metadata 'observed_at' must be a YYYY-MM-DD string"))
    else:
        try:
            parsed = _datetime.date.fromisoformat(observed_at)
        except ValueError:
            problems.append(Problem(path, "metadata 'observed_at' must be a valid YYYY-MM-DD date"))
        else:
            if parsed.isoformat() != observed_at:
                problems.append(Problem(path, "metadata 'observed_at' must use canonical YYYY-MM-DD form"))
    return problems


def _root_structure(root: Path) -> tuple[dict[str, Entry], list[Problem]]:
    entries, problems = _directory_entries(root)
    if problems:
        return entries, problems

    for name in REQUIRED_ROOT_FILES:
        path, entry_problems = _require_entry(entries, root, name, "file")
        problems.extend(entry_problems)
        if path is not None:
            try:
                _read_text(path)
            except ValidationFailure as exc:
                problems.append(Problem(path, str(exc)))

    for directory_name, file_name in (("tools", "reference.py"), ("tests", "test_reference.py")):
        directory, entry_problems = _require_entry(entries, root, directory_name, "directory")
        problems.extend(entry_problems)
        if directory is None:
            continue
        nested, nested_problems = _directory_entries(directory)
        problems.extend(nested_problems)
        if nested_problems:
            continue
        file_path, file_problems = _require_entry(nested, directory, file_name, "file")
        problems.extend(file_problems)
        if file_path is not None:
            try:
                _read_text(file_path)
            except ValidationFailure as exc:
                problems.append(Problem(file_path, str(exc)))
    return entries, problems


def _load_report(package: Path) -> tuple[Report | None, list[Problem]]:
    entries, problems = _directory_entries(package)
    if problems:
        return None, problems

    metadata_path, metadata_problems = _require_entry(entries, package, "REPORT.json", "file")
    prose_path, prose_problems = _require_entry(entries, package, "REPORT.md", "file")
    problems.extend(metadata_problems)
    problems.extend(prose_problems)

    metadata: Any | None = None
    if metadata_path is not None:
        try:
            metadata = _load_json(metadata_path)
        except ValidationFailure as exc:
            problems.append(Problem(metadata_path, str(exc)))
        else:
            problems.extend(_validate_metadata(metadata, metadata_path))

    if prose_path is not None:
        try:
            _read_text(prose_path)
        except ValidationFailure as exc:
            problems.append(Problem(prose_path, str(exc)))

    if problems or metadata is None:
        return None, problems
    return Report(directory=package, metadata=metadata), []


def _load_reports(root: Path, root_entries: dict[str, Entry]) -> tuple[list[Report], list[Problem]]:
    reports_entry = root_entries.get("reports")
    if reports_entry is None:
        return [], []
    if reports_entry.kind != "directory":
        return [], [Problem(reports_entry.path, f"reports must be an ordinary directory; found {reports_entry.kind}")]

    entries, problems = _directory_entries(reports_entry.path)
    reports: list[Report] = []
    if problems:
        return reports, problems

    for name, entry in entries.items():
        if entry.kind != "directory":
            problems.append(Problem(entry.path, "entries directly under reports/ must be directories"))
            continue
        if not PACKAGE_RE.fullmatch(name):
            problems.append(
                Problem(entry.path, "report package names must be lowercase ASCII words separated by single hyphens")
            )
            continue
        report, package_problems = _load_report(entry.path)
        problems.extend(package_problems)
        if report is not None:
            reports.append(report)
    return reports, problems


def _catalog_bytes(reports: Sequence[Report]) -> bytes:
    entries = {report.directory.name: report.metadata for report in reports}
    return (
        json.dumps({"reports": entries}, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    ).encode("ascii")


def _check_root(root: Path) -> list[Problem]:
    root_entries, problems = _root_structure(root)
    reports, report_problems = _load_reports(root, root_entries)
    problems.extend(report_problems)

    catalog_entry = root_entries.get("CATALOG.json")
    catalog_path = root / "CATALOG.json"
    if catalog_entry is None:
        problems.append(Problem(catalog_path, "generated catalog is missing"))
    elif catalog_entry.kind != "file":
        problems.append(Problem(catalog_entry.path, f"generated catalog must be an ordinary file; found {catalog_entry.kind}"))
    elif not report_problems:
        try:
            actual = _read_bytes(catalog_entry.path)
        except ValidationFailure as exc:
            problems.append(Problem(catalog_entry.path, str(exc)))
        else:
            if actual != _catalog_bytes(reports):
                problems.append(
                    Problem(catalog_entry.path, "generated catalog is stale; run 'tools/reference.py catalog'")
                )
    return sorted(problems, key=lambda problem: (problem.path.as_posix(), problem.message))


def check() -> list[Problem]:
    return _check_root(_candidate_root())


def _replace_catalog(path: Path, content: bytes) -> None:
    try:
        path.unlink()
    except FileNotFoundError:
        pass
    path.write_bytes(content)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check", help="validate this candidate tree and generated catalog")
    subparsers.add_parser("catalog", help="replace CATALOG.json from valid report metadata")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    root = _candidate_root()
    root_entries, source_problems = _root_structure(root)

    if args.command == "catalog":
        reports, report_problems = _load_reports(root, root_entries)
        problems = source_problems + report_problems
        if problems:
            for problem in sorted(problems, key=lambda p: (p.path.as_posix(), p.message)):
                print(problem.render(root), file=sys.stderr)
            return 1
        try:
            _replace_catalog(root / "CATALOG.json", _catalog_bytes(reports))
        except OSError as exc:
            print(f"CATALOG.json: cannot replace generated catalog: {exc}", file=sys.stderr)
            return 1
        print(f"wrote CATALOG.json ({len(reports)} reports)")
        return 0

    if args.command == "check":
        problems = _check_root(root)
        if problems:
            for problem in problems:
                print(problem.render(root), file=sys.stderr)
            print(f"reference check failed with {len(problems)} problem(s)", file=sys.stderr)
            return 1
        print("reference check passed")
        return 0

    raise AssertionError(f"unhandled command {args.command!r}")


if __name__ == "__main__":
    raise SystemExit(main())
