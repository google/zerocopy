#!/usr/bin/env python3
"""Validate and index the reference corpus containing this script."""

from __future__ import annotations

import argparse
import datetime as _datetime
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Sequence

REQUIRED_SOURCE_FILES = (
    "AGENTS.md",
    "FORMAT.md",
    "README.md",
    "tools/reference.py",
    "tests/test_reference.py",
)
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
class Report:
    directory: Path
    metadata: dict[str, Any]


class ValidationFailure(Exception):
    """Raised when corpus machine data cannot be read or interpreted safely."""


def _candidate_root() -> Path:
    # abspath normalizes a relative invocation without following symlinks. That
    # keeps the running validator bound to the tree through which it was invoked.
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
        # Python's JSON parser accepts escaped lone surrogates. Reject them at
        # the JSON boundary by requiring the decoded value to encode as UTF-8.
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
                    Problem(
                        path,
                        f"{prefix} has unknown keys: {', '.join(map(repr, unknown_subject))}",
                    )
                )
            if missing_subject:
                problems.append(
                    Problem(path, f"{prefix} is missing keys: {', '.join(missing_subject)}")
                )

            name = subject.get("name")
            if not isinstance(name, str) or not name.strip():
                problems.append(Problem(path, f"{prefix}.name must be a non-empty string"))

            identity = subject.get("identity")
            if not isinstance(identity, dict) or not identity:
                problems.append(Problem(path, f"{prefix}.identity must be a non-empty object"))
                continue
            for key, value in identity.items():
                if not key.strip():
                    problems.append(
                        Problem(path, f"{prefix}.identity keys must be non-empty strings")
                    )
                if not isinstance(value, str) or not value.strip():
                    problems.append(
                        Problem(
                            path,
                            f"{prefix}.identity[{key!r}] must be a non-empty string",
                        )
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
                problems.append(
                    Problem(path, "metadata 'observed_at' must use canonical YYYY-MM-DD form")
                )

    return problems


def _ordinary_file(path: Path) -> bool:
    return not path.is_symlink() and path.is_file()


def _validate_sources(root: Path) -> list[Problem]:
    problems: list[Problem] = []
    for name in REQUIRED_SOURCE_FILES:
        path = root / name
        if path.is_symlink():
            problems.append(Problem(path, "required corpus files must not be symlinks"))
        elif not path.is_file():
            problems.append(Problem(path, f"required corpus file {name} is missing"))
        else:
            try:
                _read_text(path)
            except ValidationFailure as exc:
                problems.append(Problem(path, str(exc)))
    return problems


def _list_packages(root: Path) -> tuple[list[Path], list[Problem]]:
    reports_root = root / "reports"
    if reports_root.is_symlink():
        return [], [Problem(reports_root, "reports must not be a symlink")]
    if not reports_root.exists():
        return [], []
    if not reports_root.is_dir():
        return [], [Problem(reports_root, "reports must be a directory")]

    try:
        entries = sorted(os.scandir(reports_root), key=lambda entry: entry.name)
    except OSError as exc:
        return [], [Problem(reports_root, f"cannot enumerate reports: {exc}")]

    packages: list[Path] = []
    problems: list[Problem] = []
    for entry in entries:
        path = Path(entry.path)
        try:
            if entry.is_symlink():
                problems.append(Problem(path, "report packages must not be symlinks"))
            elif not entry.is_dir(follow_symlinks=False):
                problems.append(Problem(path, "entries directly under reports/ must be directories"))
            elif not PACKAGE_RE.fullmatch(entry.name):
                problems.append(
                    Problem(
                        path,
                        "report package names must be lowercase ASCII words separated by single hyphens",
                    )
                )
            else:
                packages.append(path)
        except OSError as exc:
            problems.append(Problem(path, f"cannot inspect reports entry: {exc}"))
    return packages, problems


def _load_report(package: Path) -> tuple[Report | None, list[Problem]]:
    metadata_path = package / "REPORT.json"
    prose_path = package / "REPORT.md"
    problems: list[Problem] = []

    for path in (metadata_path, prose_path):
        if path.is_symlink():
            problems.append(Problem(path, f"{path.name} must not be a symlink"))
        elif not path.is_file():
            problems.append(Problem(path, f"report package requires ordinary file {path.name}"))

    metadata: Any | None = None
    if _ordinary_file(metadata_path):
        try:
            metadata = _load_json(metadata_path)
        except ValidationFailure as exc:
            problems.append(Problem(metadata_path, str(exc)))
        else:
            problems.extend(_validate_metadata(metadata, metadata_path))

    if _ordinary_file(prose_path):
        try:
            _read_text(prose_path)
        except ValidationFailure as exc:
            problems.append(Problem(prose_path, str(exc)))

    if problems or metadata is None:
        return None, problems
    return Report(directory=package, metadata=metadata), []


def load_reports(root: Path) -> tuple[list[Report], list[Problem]]:
    packages, problems = _list_packages(root)
    reports: list[Report] = []
    for package in packages:
        report, package_problems = _load_report(package)
        problems.extend(package_problems)
        if report is not None:
            reports.append(report)
    return reports, problems


def _catalog_bytes(reports: Sequence[Report]) -> bytes:
    entries = {report.directory.name: report.metadata for report in reports}
    text = json.dumps({"reports": entries}, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    return text.encode("ascii")


def _check_root(root: Path) -> list[Problem]:
    problems = _validate_sources(root)
    reports, report_problems = load_reports(root)
    problems.extend(report_problems)

    catalog_path = root / "CATALOG.json"
    if not catalog_path.is_file() or catalog_path.is_symlink():
        problems.append(Problem(catalog_path, "generated catalog is missing or not a regular file"))
    elif not report_problems:
        try:
            actual = _read_bytes(catalog_path)
        except ValidationFailure as exc:
            problems.append(Problem(catalog_path, str(exc)))
        else:
            if actual != _catalog_bytes(reports):
                problems.append(
                    Problem(
                        catalog_path,
                        "generated catalog is stale; run 'tools/reference.py catalog'",
                    )
                )

    return sorted(problems, key=lambda problem: (problem.path.as_posix(), problem.message))


def check() -> list[Problem]:
    return _check_root(_candidate_root())


def _replace_bytes(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(content)
        os.chmod(temporary, 0o644)
        os.replace(temporary, path)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check", help="validate this candidate tree and generated catalog")
    subparsers.add_parser("catalog", help="replace CATALOG.json from valid report metadata")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    root = _candidate_root()

    if args.command == "catalog":
        problems = _validate_sources(root)
        reports, report_problems = load_reports(root)
        problems.extend(report_problems)
        if problems:
            for problem in problems:
                print(problem.render(root), file=sys.stderr)
            return 1
        try:
            _replace_bytes(root / "CATALOG.json", _catalog_bytes(reports))
        except OSError as exc:
            print(f"CATALOG.json: cannot replace generated catalog: {exc}", file=sys.stderr)
            return 1
        print(f"wrote CATALOG.json ({len(reports)} reports)")
        return 0

    if args.command == "check":
        problems = check()
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
