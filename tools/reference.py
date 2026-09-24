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
TOPIC_RE = re.compile(r"^[a-z0-9][a-z0-9._+\-]*(?:/[a-z0-9][a-z0-9._+\-]*)*$")
METADATA_RE = re.compile(r"\A<!-- reference-metadata\n(?P<json>.*?)\n-->\n", re.DOTALL)


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
    path: Path
    metadata: dict[str, Any]


class ValidationFailure(Exception):
    """Raised when a corpus file cannot be parsed or generated safely."""


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationFailure(f"not valid UTF-8: {exc}") from exc
    except OSError as exc:
        raise ValidationFailure(f"cannot read file: {exc}") from exc


def _validate_metadata(metadata: Any, path: Path) -> list[Problem]:
    if not isinstance(metadata, dict):
        return [Problem(path, "reference metadata must be a JSON object")]

    problems: list[Problem] = []
    unknown = sorted(set(metadata) - METADATA_KEYS)
    missing = sorted(METADATA_KEYS - set(metadata))
    if unknown:
        problems.append(Problem(path, f"unknown metadata keys: {', '.join(unknown)}"))
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
                    Problem(path, f"{prefix} has unknown keys: {', '.join(unknown_subject)}")
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
            for key, value in identity.items():
                if not isinstance(key, str) or not key.strip():
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


def parse_report(path: Path) -> tuple[Report | None, list[Problem]]:
    try:
        text = _read_text(path)
    except ValidationFailure as exc:
        return None, [Problem(path, str(exc))]

    match = METADATA_RE.match(text)
    if not match:
        return None, [Problem(path, "REPORT.md must begin with a reference-metadata JSON comment")]

    try:
        metadata = json.loads(match.group("json"))
    except json.JSONDecodeError as exc:
        return None, [Problem(path, f"invalid reference metadata JSON: {exc.msg} at line {exc.lineno}")]

    problems = _validate_metadata(metadata, path)
    return Report(path=path, metadata=metadata), problems


def _walk_reports_tree(root: Path) -> tuple[list[Path], list[Path], list[Problem]]:
    reports_root = root / "reports"
    if not reports_root.exists():
        return [], [], []
    if reports_root.is_symlink():
        return [], [], [Problem(reports_root, "symlinks are not allowed under reports/")]
    if not reports_root.is_dir():
        return [], [], [Problem(reports_root, "reports must be a directory")]

    files: list[Path] = []
    symlinks: list[Path] = []
    for dirpath, dirnames, filenames in os.walk(reports_root, topdown=True, followlinks=False):
        directory = Path(dirpath)
        kept_dirs: list[str] = []
        for name in sorted(dirnames):
            path = directory / name
            if path.is_symlink():
                symlinks.append(path)
            else:
                kept_dirs.append(name)
        dirnames[:] = kept_dirs
        for name in sorted(filenames):
            path = directory / name
            if path.is_symlink():
                symlinks.append(path)
            else:
                files.append(path)

    problems = [Problem(path, "symlinks are not allowed under reports/") for path in symlinks]
    report_paths = sorted(
        (path for path in files if path.name == "REPORT.md"),
        key=lambda path: path.relative_to(root).as_posix(),
    )
    return report_paths, files, problems


def _validate_report_tree(root: Path) -> tuple[list[Path], list[Problem]]:
    report_paths, files, problems = _walk_reports_tree(root)
    report_dirs = {path.parent.resolve() for path in report_paths}

    for report_dir in sorted(report_dirs):
        if any(parent.resolve() in report_dirs for parent in report_dir.parents):
            problems.append(
                Problem(report_dir, "report directories must not be nested inside other reports")
            )

    for path in files:
        if not any(report_dir in path.resolve().parents for report_dir in report_dirs):
            problems.append(
                Problem(path, "files under reports/ must belong to a directory containing REPORT.md")
            )

    return report_paths, problems


def load_reports(root: Path) -> tuple[list[Report], list[Problem]]:
    report_paths, problems = _validate_report_tree(root)
    reports: list[Report] = []
    for path in report_paths:
        report, report_problems = parse_report(path)
        problems.extend(report_problems)
        if report is not None:
            reports.append(report)
    return reports, problems


def generate_catalog(root: Path, reports: Sequence[Report] | None = None) -> str:
    if reports is None:
        reports, problems = load_reports(root)
        if problems:
            raise ValidationFailure("cannot generate catalog from invalid reports")

    entries = []
    for report in sorted(reports, key=lambda item: item.path.relative_to(root).as_posix()):
        entries.append(
            {
                "path": report.path.relative_to(root).as_posix(),
                **report.metadata,
            }
        )
    return json.dumps({"reports": entries}, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def validate_root(root: Path) -> list[Problem]:
    problems: list[Problem] = []
    for name in REQUIRED_ROOT_FILES:
        path = root / name
        if not path.is_file():
            problems.append(Problem(path, f"required root file {name} is missing"))
    return problems


def check(root: Path) -> list[Problem]:
    root = root.resolve()
    problems = validate_root(root)
    reports, report_problems = load_reports(root)
    problems.extend(report_problems)

    catalog_path = root / "CATALOG.json"
    if catalog_path.is_file() and not report_problems:
        expected = generate_catalog(root, reports)
        try:
            actual = _read_text(catalog_path)
        except ValidationFailure as exc:
            problems.append(Problem(catalog_path, str(exc)))
        else:
            if actual != expected:
                problems.append(
                    Problem(catalog_path, "generated catalog is stale; run 'tools/reference.py catalog'")
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
        reports = load_reports(root)[0]
        print(f"reference check passed ({len(reports)} reports)")
        return 0

    raise AssertionError(f"unhandled command {args.command!r}")


if __name__ == "__main__":
    raise SystemExit(main())
