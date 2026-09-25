#!/usr/bin/env python3
"""Validate and index the `reference` branch technical report corpus."""

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

REQUIRED_ROOT_FILES = ("AGENTS.md", "FORMAT.md", "README.md", "CATALOG.json")
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
    """Raised when a corpus file cannot be parsed or generated safely."""


class DuplicateKeyError(ValueError):
    pass


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationFailure(f"not valid UTF-8: {exc}") from exc
    except OSError as exc:
        raise ValidationFailure(f"cannot read file: {exc}") from exc


def _no_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate object key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise ValueError(f"invalid JSON constant {value}")


def _validate_unicode_scalars(value: Any) -> None:
    try:
        json.dumps(value, ensure_ascii=False).encode("utf-8")
    except UnicodeEncodeError as exc:
        raise ValidationFailure("JSON strings must contain valid Unicode scalar text") from exc


def _load_json(path: Path) -> Any:
    text = _read_text(path)
    try:
        value = json.loads(
            text,
            object_pairs_hook=_no_duplicate_keys,
            parse_constant=_reject_constant,
        )
    except ValueError as exc:
        raise ValidationFailure(f"invalid JSON: {exc}") from exc
    _validate_unicode_scalars(value)
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
        seen_topics: set[str] = set()
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
            if topic in seen_topics:
                problems.append(Problem(path, f"duplicate topic {topic!r}"))
            seen_topics.add(topic)

    subjects = metadata.get("subjects")
    if not isinstance(subjects, list) or not subjects:
        problems.append(Problem(path, "metadata 'subjects' must be a non-empty array"))
    else:
        seen_names: set[str] = set()
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
            elif name in seen_names:
                problems.append(Problem(path, f"duplicate subject name {name!r}"))
            else:
                seen_names.add(name)

            identity = subject.get("identity")
            if not isinstance(identity, dict) or not identity:
                problems.append(Problem(path, f"{prefix}.identity must be a non-empty object"))
                continue
            for key, item in identity.items():
                if not isinstance(key, str) or not key.strip():
                    problems.append(
                        Problem(path, f"{prefix}.identity keys must be non-empty strings")
                    )
                if not isinstance(item, str) or not item.strip():
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
    return path.exists() and not path.is_symlink() and path.is_file()


def _validate_root(root: Path) -> list[Problem]:
    problems: list[Problem] = []
    for name in REQUIRED_ROOT_FILES:
        path = root / name
        if path.is_symlink():
            problems.append(Problem(path, "required root files must not be symlinks"))
            continue
        if not path.is_file():
            problems.append(Problem(path, f"required root file {name} is missing"))
            continue
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

    packages: list[Path] = []
    problems: list[Problem] = []
    try:
        entries = sorted(os.scandir(reports_root), key=lambda entry: entry.name)
    except OSError as exc:
        return [], [Problem(reports_root, f"cannot enumerate reports: {exc}")]

    for entry in entries:
        path = Path(entry.path)
        try:
            if entry.is_symlink():
                problems.append(Problem(path, "entries directly under reports/ must not be symlinks"))
            elif entry.is_dir(follow_symlinks=False):
                if not PACKAGE_RE.fullmatch(entry.name):
                    problems.append(
                        Problem(
                            path,
                            "report package names must be lowercase ASCII words separated by single hyphens",
                        )
                    )
                else:
                    packages.append(path)
            else:
                problems.append(
                    Problem(path, "entries directly under reports/ must be report directories")
                )
        except OSError as exc:
            problems.append(Problem(path, f"cannot inspect reports entry: {exc}"))
    return packages, problems


def _load_report(package: Path) -> tuple[Report | None, list[Problem]]:
    problems: list[Problem] = []

    metadata_path = package / "REPORT.json"
    prose_path = package / "REPORT.md"
    for path in (metadata_path, prose_path):
        if path.is_symlink():
            problems.append(Problem(path, "symlinks are not allowed under reports/"))
        elif not path.is_file():
            problems.append(Problem(path, f"report package requires ordinary file {path.name}"))

    def onerror(exc: OSError) -> None:
        path = Path(exc.filename) if exc.filename else package
        problems.append(Problem(path, f"cannot enumerate report package: {exc}"))

    for dirpath, dirnames, filenames in os.walk(
        package,
        topdown=True,
        followlinks=False,
        onerror=onerror,
    ):
        directory = Path(dirpath)
        for name in (*dirnames, *filenames):
            path = directory / name
            try:
                if path.is_symlink():
                    problems.append(Problem(path, "symlinks are not allowed under reports/"))
                elif name in filenames and not path.is_file():
                    problems.append(
                        Problem(
                            path,
                            "report packages may contain only regular files and directories",
                        )
                    )
            except OSError as exc:
                problems.append(Problem(path, f"cannot inspect report package entry: {exc}"))

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

    if metadata is None:
        return None, problems
    return Report(directory=package, metadata=metadata), problems


def load_reports(root: Path) -> tuple[list[Report], list[Problem]]:
    packages, problems = _list_packages(root)
    reports: list[Report] = []
    for package in packages:
        report, package_problems = _load_report(package)
        problems.extend(package_problems)
        if report is not None:
            reports.append(report)
    return reports, problems


def generate_catalog(root: Path, reports: Sequence[Report] | None = None) -> str:
    if reports is None:
        reports, problems = load_reports(root)
        if problems:
            raise ValidationFailure("cannot generate catalog from invalid reports")

    entries = {
        report.directory.name: report.metadata
        for report in sorted(reports, key=lambda item: item.directory.name)
    }
    return json.dumps({"reports": entries}, indent=2, ensure_ascii=True, sort_keys=True) + "\n"


def check(root: Path) -> list[Problem]:
    root = root.resolve()
    problems = _validate_root(root)
    reports, report_problems = load_reports(root)
    problems.extend(report_problems)

    catalog_path = root / "CATALOG.json"
    if _ordinary_file(catalog_path) and not report_problems:
        expected = generate_catalog(root, reports)
        try:
            actual = _read_text(catalog_path)
        except ValidationFailure as exc:
            problems.append(Problem(catalog_path, str(exc)))
        else:
            if actual != expected:
                problems.append(
                    Problem(
                        catalog_path,
                        "generated catalog is stale; run 'tools/reference.py catalog'",
                    )
                )

    return sorted(problems, key=lambda problem: (problem.path.as_posix(), problem.message))


def _write_atomic(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as handle:
            handle.write(content)
            temporary = Path(handle.name)
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass


def _default_root() -> Path:
    return Path(__file__).resolve().parents[1]


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=Path,
        default=_default_root(),
        help="reference corpus root (default: repository root containing this script)",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("check", help="validate corpus structure and generated catalog")
    subparsers.add_parser("catalog", help="regenerate CATALOG.json from report metadata")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    root = args.root.resolve()

    if args.command == "catalog":
        reports, problems = load_reports(root)
        if problems:
            for problem in problems:
                print(problem.render(root), file=sys.stderr)
            return 1
        try:
            _write_atomic(root / "CATALOG.json", generate_catalog(root, reports))
        except OSError as exc:
            print(f"CATALOG.json: cannot write generated catalog: {exc}", file=sys.stderr)
            return 1
        print(f"wrote CATALOG.json ({len(reports)} reports)")
        return 0

    if args.command == "check":
        problems = check(root)
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
