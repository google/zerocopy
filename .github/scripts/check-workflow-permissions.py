#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reject write-capable tokens in workflows which execute proposed changes.

This checker deliberately does not try to be a general YAML parser. GitHub's
workflow validator owns syntax validation; this script recognizes only the
small, security-sensitive subset needed to answer two questions:

* Does a workflow run for ``pull_request`` or ``merge_group``?
* Does an untrusted workflow declare an explicit read-only permission baseline,
  and does any workflow-level or job-level ``permissions`` grant write access?

The scanner tracks YAML mapping indentation so a step input such as
``with: {access: write}`` cannot be mistaken for a token permission. It accepts
the block and compact trigger/permission forms supported below and fails closed
when an untrusted workflow uses aliases, expressions, or another permissions
shape whose authority cannot be established from the text.
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import pathlib
import re
import sys
from collections.abc import Iterable, Sequence


_UNTRUSTED_EVENTS = frozenset({"merge_group", "pull_request"})
_WORKFLOW_SUFFIXES = frozenset({".yaml", ".yml"})
_PLAIN_NAME = re.compile(r"^[A-Za-z0-9_-]+$")
_BLOCK_SCALAR = re.compile(r"^[|>][0-9+-]*$")


@dataclasses.dataclass(frozen=True)
class Issue:
    line: int
    message: str


@dataclasses.dataclass
class _PermissionBlock:
    line: int
    owner: str
    saw_entry: bool = False


class _Unsupported(ValueError):
    pass


def _strip_comment(text: str) -> str:
    """Removes an unquoted YAML comment from one physical line."""

    single = False
    double = False
    escaped = False
    index = 0
    while index < len(text):
        character = text[index]
        if double:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                double = False
        elif single:
            if character == "'":
                # YAML escapes a single quote inside a single-quoted scalar by
                # doubling it.
                if index + 1 < len(text) and text[index + 1] == "'":
                    index += 1
                else:
                    single = False
        elif character == '"':
            double = True
        elif character == "'":
            single = True
        elif character == "#" and (
            index == 0 or text[index - 1].isspace()
        ):
            return text[:index].rstrip()
        index += 1
    return text.rstrip()


def _split_mapping_entry(text: str) -> tuple[str, str] | None:
    """Splits ``key: value`` at an unquoted, top-level colon."""

    single = False
    double = False
    escaped = False
    square_depth = 0
    curly_depth = 0
    for index, character in enumerate(text):
        if double:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                double = False
            continue
        if single:
            if character == "'":
                if index + 1 < len(text) and text[index + 1] == "'":
                    continue
                single = False
            continue
        if character == '"':
            double = True
        elif character == "'":
            single = True
        elif character == "[":
            square_depth += 1
        elif character == "]":
            square_depth -= 1
        elif character == "{":
            curly_depth += 1
        elif character == "}":
            curly_depth -= 1
        elif character == ":" and square_depth == 0 and curly_depth == 0:
            return text[:index].strip(), text[index + 1 :].strip()
    return None


def _split_flow_items(text: str) -> list[str]:
    """Splits a flow sequence/map body at top-level commas."""

    items: list[str] = []
    start = 0
    single = False
    double = False
    escaped = False
    square_depth = 0
    curly_depth = 0
    for index, character in enumerate(text):
        if double:
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                double = False
            continue
        if single:
            if character == "'":
                if index + 1 < len(text) and text[index + 1] == "'":
                    continue
                single = False
            continue
        if character == '"':
            double = True
        elif character == "'":
            single = True
        elif character == "[":
            square_depth += 1
        elif character == "]":
            square_depth -= 1
        elif character == "{":
            curly_depth += 1
        elif character == "}":
            curly_depth -= 1
        elif character == "," and square_depth == 0 and curly_depth == 0:
            items.append(text[start:index].strip())
            start = index + 1
    items.append(text[start:].strip())
    if any(not item for item in items):
        raise _Unsupported("empty item in a compact YAML collection")
    return items


def _scalar(text: str) -> str:
    """Returns a quoted or plain scalar without YAML type coercion."""

    text = text.strip()
    if len(text) >= 2 and text[0] == text[-1] == "'":
        return text[1:-1].replace("''", "'")
    if len(text) >= 2 and text[0] == text[-1] == '"':
        try:
            value = json.loads(text)
        except json.JSONDecodeError as error:
            raise _Unsupported(f"unsupported quoted scalar: {error}") from error
        if not isinstance(value, str):
            raise _Unsupported("expected a string scalar")
        return value
    return text


def _name(text: str) -> str:
    value = _scalar(text)
    if not _PLAIN_NAME.fullmatch(value):
        raise _Unsupported(f"unsupported name {text!r}")
    return value


def _flow_sequence(text: str) -> list[str]:
    if text == "[]":
        return []
    return [_name(item) for item in _split_flow_items(text[1:-1])]


def _flow_mapping(text: str) -> list[tuple[str, str]]:
    if text == "{}":
        return []
    entries: list[tuple[str, str]] = []
    for item in _split_flow_items(text[1:-1]):
        entry = _split_mapping_entry(item)
        if entry is None:
            raise _Unsupported(f"unsupported compact mapping entry {item!r}")
        key, value = entry
        entries.append((_name(key), value))
    return entries


def _compact_events(value: str) -> set[str]:
    if value.startswith("[") and value.endswith("]"):
        return set(_flow_sequence(value))
    if value.startswith("{") and value.endswith("}"):
        return {key for key, _ in _flow_mapping(value)}
    return {_name(value)}


def _permission_value(
    value: str, *, line: int, owner: str, scope: str
) -> Issue | None:
    value = _scalar(value)
    if value == "write":
        return Issue(line, f"{owner} grants `{scope}: write`")
    if value not in {"none", "read"}:
        return Issue(
            line,
            f"cannot safely interpret {owner} permission `{scope}: {value}`",
        )
    return None


def _compact_permissions(value: str, *, line: int, owner: str) -> list[Issue]:
    scalar = _scalar(value)
    if scalar == "write-all":
        return [Issue(line, f"{owner} grants `write-all`")]
    if scalar in {"read-all", "{}"}:
        return []
    if not (value.startswith("{") and value.endswith("}")):
        return [
            Issue(line, f"cannot safely interpret {owner} permissions `{value}`")
        ]

    issues: list[Issue] = []
    try:
        entries = _flow_mapping(value)
    except _Unsupported as error:
        return [Issue(line, f"cannot safely interpret {owner} permissions: {error}")]
    for scope, permission in entries:
        issue = _permission_value(
            permission, line=line, owner=owner, scope=scope
        )
        if issue is not None:
            issues.append(issue)
    return issues


def analyze_workflow(text: str) -> list[Issue]:
    """Returns security or ambiguity findings for one workflow's YAML text."""

    stack: list[tuple[int, str]] = []
    permission_blocks: dict[tuple[str, ...], _PermissionBlock] = {}
    permission_issues: list[Issue] = []
    structure_issues: list[Issue] = []
    trigger_issues: list[Issue] = []
    events: set[str] = set()
    on_line: int | None = None
    on_is_block = False
    workflow_permissions_declared = False
    block_scalar_indent: int | None = None

    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        if "\t" in raw_line[: len(raw_line) - len(raw_line.lstrip())]:
            trigger_issues.append(
                Issue(line_number, "tab indentation cannot be interpreted safely")
            )
            continue

        indent = len(raw_line) - len(raw_line.lstrip(" "))
        content = _strip_comment(raw_line[indent:])
        if not content:
            continue
        if block_scalar_indent is not None:
            if indent > block_scalar_indent:
                continue
            block_scalar_indent = None
        if content in {"---", "..."}:
            continue

        while stack and indent <= stack[-1][0]:
            stack.pop()
        parent = tuple(key for _, key in stack)

        if content.startswith("- "):
            if parent == ("on",):
                try:
                    events.add(_name(content[2:].strip()))
                except _Unsupported as error:
                    trigger_issues.append(Issue(line_number, str(error)))
            elif parent in permission_blocks:
                block = permission_blocks[parent]
                permission_issues.append(
                    Issue(
                        line_number,
                        f"cannot safely interpret {block.owner} permissions as a list",
                    )
                )
            continue

        entry = _split_mapping_entry(content)
        if entry is None:
            # Plain scalar lines are valid inside block scalars (handled above)
            # but not in a mapping structure relevant to this checker.
            if parent == ("on",):
                trigger_issues.append(
                    Issue(line_number, "cannot safely interpret workflow triggers")
                )
            elif parent in permission_blocks:
                block = permission_blocks[parent]
                permission_issues.append(
                    Issue(
                        line_number,
                        f"cannot safely interpret {block.owner} permissions",
                    )
                )
            continue

        raw_key, value = entry
        try:
            key = _name(raw_key)
        except _Unsupported:
            key = _scalar(raw_key)
        path = parent + (key,)

        if path == ("on",):
            if indent != 0 or on_line is not None:
                trigger_issues.append(
                    Issue(line_number, "workflow must have one top-level `on` key")
                )
            on_line = line_number
            if not value:
                on_is_block = True
            else:
                try:
                    events.update(_compact_events(value))
                except _Unsupported as error:
                    trigger_issues.append(
                        Issue(
                            line_number,
                            f"cannot safely interpret workflow triggers: {error}",
                        )
                    )
        elif len(path) == 2 and path[0] == "on" and on_is_block:
            events.add(key)

        if path == ("jobs",) and value and value != "{}":
            structure_issues.append(
                Issue(line_number, "cannot safely inspect compact or aliased `jobs`")
            )
        elif len(path) == 2 and path[0] == "jobs" and value:
            structure_issues.append(
                Issue(
                    line_number,
                    f"cannot safely inspect compact or aliased job `{path[1]}`",
                )
            )
        if key == "<<" and (
            not parent or (len(parent) == 2 and parent[0] == "jobs")
        ):
            structure_issues.append(
                Issue(line_number, "YAML merge may conceal token permissions")
            )

        permission_owner: str | None = None
        if path == ("permissions",):
            permission_owner = "workflow"
            workflow_permissions_declared = True
        elif len(path) == 3 and path[0] == "jobs" and path[2] == "permissions":
            permission_owner = f"job `{path[1]}`"

        if permission_owner is not None:
            if path in permission_blocks:
                permission_issues.append(
                    Issue(line_number, f"duplicate {permission_owner} permissions")
                )
            if value:
                permission_issues.extend(
                    _compact_permissions(
                        value, line=line_number, owner=permission_owner
                    )
                )
            else:
                permission_blocks[path] = _PermissionBlock(
                    line=line_number, owner=permission_owner
                )
        else:
            for prefix, block in permission_blocks.items():
                if path[: len(prefix)] != prefix:
                    continue
                if len(path) == len(prefix) + 1:
                    block.saw_entry = True
                    if not value:
                        permission_issues.append(
                            Issue(
                                line_number,
                                f"cannot safely interpret {block.owner} permission `{key}`",
                            )
                        )
                    else:
                        issue = _permission_value(
                            value,
                            line=line_number,
                            owner=block.owner,
                            scope=key,
                        )
                        if issue is not None:
                            permission_issues.append(issue)
                elif len(path) > len(prefix) + 1:
                    permission_issues.append(
                        Issue(
                            line_number,
                            f"cannot safely interpret nested {block.owner} permissions",
                        )
                    )

        if not value:
            stack.append((indent, key))
        elif _BLOCK_SCALAR.fullmatch(value):
            block_scalar_indent = indent

    if on_line is None:
        trigger_issues.append(Issue(1, "workflow has no top-level `on` key"))
    if on_is_block and not events:
        trigger_issues.append(
            Issue(on_line or 1, "workflow trigger block does not name an event")
        )

    # Syntax/trigger ambiguity prevents this checker from establishing whether
    # proposed code can execute, so it is always fatal. Permission ambiguity is
    # relevant only after an untrusted trigger has been positively identified;
    # release and deployment workflows are intentionally allowed to write.
    if trigger_issues:
        return trigger_issues
    if not events.intersection(_UNTRUSTED_EVENTS):
        return []

    # Without a workflow-level cap, jobs which omit `permissions` inherit the
    # repository or organization default. That default is mutable external
    # state and may be read/write, so inspecting only the permissions which are
    # present cannot prove that proposed code receives a read-only token. An
    # explicit empty map, read-all, or read/none mapping provides the required
    # fail-closed baseline. Individual jobs may replace that baseline and are
    # checked independently below.
    if not workflow_permissions_declared:
        permission_issues.append(
            Issue(
                on_line or 1,
                "untrusted workflow must declare explicit top-level `permissions`",
            )
        )

    for block in permission_blocks.values():
        if not block.saw_entry:
            permission_issues.append(
                Issue(
                    block.line,
                    f"cannot safely interpret empty {block.owner} permissions block",
                )
            )
    return sorted(
        permission_issues + structure_issues,
        key=lambda issue: (issue.line, issue.message),
    )


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
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            print(f"{path}: {error}", file=sys.stderr)
            failed = True
            continue
        for issue in analyze_workflow(text.lstrip("\ufeff")):
            print(f"{path}:{issue.line}: {issue.message}", file=sys.stderr)
            failed = True
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
