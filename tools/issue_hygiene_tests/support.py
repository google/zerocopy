# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared fixtures for the `issue_hygiene` tests."""

from __future__ import annotations

import issue_hygiene as ih


def _make_issue(
    number: int,
    *,
    title: str = "Sample issue",
    body: str = "",
    labels: tuple[str, ...] = (),
    issue_type: str | None = "Task",
    milestone: ih.Milestone | None = None,
    parent_number: int | None = None,
    sub_issues: tuple[int, ...] = (),
    has_sub_issues: bool | None = None,
    blocked_by: tuple[ih.Blocker, ...] = (),
    relates_to: tuple[int, ...] = (),
) -> ih.Issue:
    return ih.Issue(
        node_id=f"I_{number}",
        number=number,
        title=title,
        body=body,
        labels=frozenset(labels),
        issue_type=issue_type,
        milestone=milestone,
        parent_number=parent_number,
        sub_issues=frozenset(sub_issues),
        has_sub_issues=(
            has_sub_issues if has_sub_issues is not None else bool(sub_issues)
        ),
        blocked_by=blocked_by,
        relates_to=frozenset(relates_to),
    )
