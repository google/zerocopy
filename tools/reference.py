#!/usr/bin/env python3
"""Validate and index the `reference` branch technical report corpus."""

from __future__ import annotations

import argparse
import datetime as _datetime
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence
from urllib.parse import unquote

REQUIRED_ROOT_FILES = ("AGENTS.md", "FORMAT.md", "README.md", "CATALOG.md")
REQUIRED_SECTIONS = (
    "Summary",
    "Applicability",
    "Findings",
    "Boundaries",
    "Evidence",
    "Revalidation",
)
METADATA_KEYS = frozenset({"topics", "subjects", "observed_at", "observed_under"})
SUBJECT_KEYS = frozenset({"name", "identity"})
TOPIC_RE = re.compile(r"^[a-z0-9][a-z0-9._+\-]*(?:/[a-z0-9][a-z0-9._+\-]*)*$")
METADATA_RE = re.compile(r"\A<!-- reference-metadata\n(?P<json>.*?)\n-->\n", re.DOTALL)
H1_RE = re.compile(r"^# (\S.*)$")
H2_RE = re.compile(r"^## (\S.*)$")
LINK_RE = re.compile(r"!?\[[^\]]*\]\((?P<target><[^>]+>|[^\s)]+)(?:\s+[^)]*)?\)")
FENCE_RE = re.compile(r"^ {0,3}(?P<fence>`{3,}|~{3,})")
REMOTE_SCHEMES = ("http://", "https://", "mailto:", "data:", "javascript:")


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
    title: str
    summary: str
    metadata: dict[str, Any]


class ValidationFailure(Exception):
    """Raised when parsing cannot produce a meaningful report object."""


def _read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError as exc:
        raise ValidationFailure(f"not valid UTF-8: {exc}") from exc
    except OSError as exc:
        raise ValidationFailure(f"cannot read file: {exc}") from exc


def _validate_metadata(metadata: Any, path: Path) -> list[Problem]:
    problems: list[Problem] = []
    if not isinstance(metadata, dict):
        return [Problem(path, "reference metadata must be a JSON object")]

    unknown = sorted(set(metadata) - METADATA_KEYS)
    missing = sorted({"topics", "subjects", "observed_at"} - set(metadata))
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
            else:
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

    if "observed_under" in metadata:
        observed_under = metadata["observed_under"]
        if not isinstance(observed_under, dict) or not observed_under:
            problems.append(Problem(path, "metadata 'observed_under' must be a non-empty object"))
        elif any(not isinstance(k, str) or not k.strip() for k in observed_under):
            problems.append(
                Problem(path, "metadata 'observed_under' keys must be non-empty strings")
            )

    return problems


def _visible_markdown_lines(text: str) -> list[str]:
    """Return lines with fenced-code contents blanked while preserving line numbers."""
    visible: list[str] = []
    fence_char: str | None = None
    fence_len = 0
    for line in text.splitlines():
        match = FENCE_RE.match(line)
        if fence_char is None:
            if match is not None:
                fence = match.group("fence")
                fence_char = fence[0]
                fence_len = len(fence)
                visible.append("")
            else:
                visible.append(line)
            continue

        if match is not None:
            fence = match.group("fence")
            if fence[0] == fence_char and len(fence) >= fence_len:
                fence_char = None
                fence_len = 0
        visible.append("")
    return visible


def _heading_map(body: str, path: Path) -> tuple[str | None, dict[str, tuple[int, int]], list[Problem]]:
    """Return title, H2 ranges, and heading-related problems."""
    raw_lines = body.splitlines()
    lines = _visible_markdown_lines(body)
    problems: list[Problem] = []

    title: str | None = None
    h1_lines: list[int] = []
    h2s: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        if match := H1_RE.fullmatch(line):
            h1_lines.append(idx)
            if title is None:
                title = match.group(1).strip()
        elif match := H2_RE.fullmatch(line):
            h2s.append((idx, match.group(1).strip()))

    if not h1_lines:
        problems.append(Problem(path, "report must contain one H1 title"))
    elif len(h1_lines) > 1:
        problems.append(Problem(path, "report must contain exactly one H1 title"))

    first_nonempty = next((i for i, line in enumerate(lines) if line.strip()), None)
    if first_nonempty is not None and (not h1_lines or h1_lines[0] != first_nonempty):
        problems.append(Problem(path, "the first non-empty line after metadata must be the H1 title"))

    positions: list[int] = []
    for required in REQUIRED_SECTIONS:
        matches = [line_no for line_no, name in h2s if name == required]
        if not matches:
            problems.append(Problem(path, f"missing required section '## {required}'"))
            continue
        if len(matches) > 1:
            problems.append(Problem(path, f"duplicate required section '## {required}'"))
        positions.append(matches[0])

    if len(positions) == len(REQUIRED_SECTIONS) and positions != sorted(positions):
        problems.append(
            Problem(path, "required sections must appear in FORMAT.md order")
        )

    ranges: dict[str, tuple[int, int]] = {}
    for line_no, name in h2s:
        next_h2 = next((other for other, _ in h2s if other > line_no), len(raw_lines))
        ranges.setdefault(name, (line_no + 1, next_h2))

    for required in REQUIRED_SECTIONS:
        if required not in ranges:
            continue
        start, end = ranges[required]
        content = "\n".join(raw_lines[start:end]).strip()
        if not content:
            problems.append(Problem(path, f"required section '## {required}' must not be empty"))

    return title, ranges, problems


def _extract_summary(body: str, ranges: dict[str, tuple[int, int]]) -> str:
    lines = body.splitlines()
    start, end = ranges["Summary"]
    return " ".join(line.strip() for line in lines[start:end] if line.strip())


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
    body = text[match.end() :]
    title, ranges, heading_problems = _heading_map(body, path)
    problems.extend(heading_problems)

    if title is None or "Summary" not in ranges:
        return None, problems

    summary = _extract_summary(body, ranges)
    report = Report(path=path, title=title, summary=summary, metadata=metadata)
    return report, problems


def _local_link_targets(text: str) -> Iterable[str]:
    visible_text = "\n".join(_visible_markdown_lines(text))
    for match in LINK_RE.finditer(visible_text):
        target = match.group("target")
        if target.startswith("<") and target.endswith(">"):
            target = target[1:-1]
        if not target or target.startswith("#") or target.startswith(REMOTE_SCHEMES):
            continue
        yield target


def _validate_local_links(path: Path, root: Path) -> list[Problem]:
    try:
        text = _read_text(path)
    except ValidationFailure as exc:
        return [Problem(path, str(exc))]

    problems: list[Problem] = []
    for target in _local_link_targets(text):
        target_without_fragment = target.split("#", 1)[0].split("?", 1)[0]
        if not target_without_fragment:
            continue
        decoded = unquote(target_without_fragment)
        if decoded.startswith("/"):
            resolved = root / decoded.lstrip("/")
        else:
            resolved = path.parent / decoded
        try:
            resolved_abs = resolved.resolve(strict=False)
            resolved_abs.relative_to(root.resolve())
        except ValueError:
            problems.append(Problem(path, f"local link escapes corpus root: {target!r}"))
            continue
        if not resolved_abs.exists():
            problems.append(Problem(path, f"broken local link: {target!r}"))
    return problems


def discover_report_paths(root: Path) -> list[Path]:
    reports_root = root / "reports"
    if not reports_root.exists():
        return []
    return sorted(reports_root.rglob("REPORT.md"), key=lambda p: p.relative_to(root).as_posix())


def _validate_report_tree(root: Path, report_paths: Sequence[Path]) -> list[Problem]:
    reports_root = root / "reports"
    if not reports_root.exists():
        return []
    if not reports_root.is_dir():
        return [Problem(reports_root, "reports must be a directory")]

    report_dirs = {path.parent.resolve() for path in report_paths}
    problems: list[Problem] = []

    for report_dir in sorted(report_dirs):
        if any(parent.resolve() in report_dirs for parent in report_dir.parents):
            problems.append(Problem(report_dir, "report directories must not be nested inside other reports"))

    for path in sorted(reports_root.rglob("*")):
        if path.is_dir():
            continue
        parent_report: Path | None = None
        for ancestor in (path.parent, *path.parents):
            if ancestor.resolve() in report_dirs:
                parent_report = ancestor
                break
            if ancestor == reports_root:
                break
        if parent_report is None:
            problems.append(
                Problem(path, "files under reports/ must belong to a directory containing REPORT.md")
            )
            continue

        rel = path.relative_to(parent_report)
        if rel == Path("REPORT.md"):
            continue
        if not rel.parts or rel.parts[0] not in {"evidence", "probes"}:
            problems.append(
                Problem(
                    path,
                    "report support files must be under evidence/ or probes/",
                )
            )

    return problems


def load_reports(root: Path) -> tuple[list[Report], list[Problem]]:
    report_paths = discover_report_paths(root)
    problems = _validate_report_tree(root, report_paths)
    reports: list[Report] = []
    for path in report_paths:
        report, report_problems = parse_report(path)
        problems.extend(report_problems)
        problems.extend(_validate_local_links(path, root))
        if report is not None:
            reports.append(report)
        for support_md in sorted(path.parent.rglob("*.md")):
            if support_md != path:
                problems.extend(_validate_local_links(support_md, root))
    return reports, problems


def _identity_text(identity: dict[str, Any]) -> str:
    return ", ".join(f"{key}={identity[key]}" for key in sorted(identity))


def _catalog_summary(summary: str) -> str:
    # Catalog entries are rooted at CATALOG.md, while report summaries are rooted
    # at each report directory. Copying relative Markdown links verbatim would
    # silently change their meaning. Render link text only in the derived index.
    summary = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", summary)
    return " ".join(summary.split())


def generate_catalog(root: Path, reports: Sequence[Report] | None = None) -> str:
    if reports is None:
        reports, problems = load_reports(root)
        if problems:
            raise ValidationFailure("cannot generate catalog from invalid reports")

    lines = [
        "# Reference catalog",
        "",
        "<!-- Generated by tools/reference.py. Do not edit manually. -->",
        "",
        "This file indexes the reports in the current `reference` tree. Technical",
        "claims live in the reports themselves; this catalog is navigation only.",
        "",
    ]

    if not reports:
        lines.extend(["No reports are currently present.", ""])
        return "\n".join(lines)

    for report in sorted(reports, key=lambda r: r.path.relative_to(root).as_posix()):
        rel = report.path.relative_to(root).as_posix()
        topics = ", ".join(f"`{topic}`" for topic in report.metadata["topics"])
        subjects = "; ".join(
            f"{subject['name']} ({_identity_text(subject['identity'])})"
            for subject in report.metadata["subjects"]
        )
        summary = _catalog_summary(report.summary)
        lines.extend(
            [
                f"## [{report.title}]({rel})",
                "",
                f"- Topics: {topics}",
                f"- Subjects: {subjects}",
                f"- Observed: {report.metadata['observed_at']}",
                f"- Summary: {summary}",
                "",
            ]
        )
    return "\n".join(lines)


def validate_root(root: Path) -> list[Problem]:
    problems: list[Problem] = []
    for name in REQUIRED_ROOT_FILES:
        path = root / name
        if not path.is_file():
            problems.append(Problem(path, f"required root file {name} is missing"))
    for name in ("AGENTS.md", "FORMAT.md", "README.md", "CATALOG.md"):
        path = root / name
        if path.is_file():
            problems.extend(_validate_local_links(path, root))
    return problems


def check(root: Path) -> list[Problem]:
    root = root.resolve()
    problems = validate_root(root)
    reports, report_problems = load_reports(root)
    problems.extend(report_problems)

    catalog_path = root / "CATALOG.md"
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

    return sorted(problems, key=lambda p: (p.path.as_posix(), p.message))


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
    subparsers.add_parser("catalog", help="regenerate CATALOG.md from reports")
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
        catalog = generate_catalog(root, reports)
        try:
            (root / "CATALOG.md").write_text(catalog, encoding="utf-8")
        except OSError as exc:
            print(f"CATALOG.md: cannot write generated catalog: {exc}", file=sys.stderr)
            return 1
        print(f"wrote CATALOG.md ({len(reports)} reports)")
        return 0

    if args.command == "check":
        problems = check(root)
        if problems:
            for problem in problems:
                print(problem.render(root), file=sys.stderr)
            print(f"reference check failed with {len(problems)} problem(s)", file=sys.stderr)
            return 1
        reports = discover_report_paths(root)
        print(f"reference check passed ({len(reports)} reports)")
        return 0

    raise AssertionError(f"unhandled command {args.command!r}")


if __name__ == "__main__":
    raise SystemExit(main())
