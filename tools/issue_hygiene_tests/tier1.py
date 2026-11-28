# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tier 1 checks: primary-scope labels, issue types, PR-only labels, and
closed milestones.
"""

from __future__ import annotations

import issue_hygiene as ih

from issue_hygiene_tests.support import _make_issue


class Tier1Cases:
    """Test methods of `IssueHygieneTier1Tests`."""

    def test_subcrate_implies_primary_scope(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(10, labels=("zerocopy-derive",)),
                _make_issue(20, labels=("exocrate",)),
                _make_issue(30, labels=("zerocopy", "zerocopy-derive")),
            )
        )
        rep = ih.analyze_repo(snap)
        self.assertEqual(
            rep.actions,
            (
                ih.AddLabels(
                    10,
                    ("zerocopy",),
                    "sub-crate implies primary scope umbrella",
                ),
                ih.AddLabels(
                    20, ("anneal",), "sub-crate implies primary scope umbrella"
                ),
            ),
        )
        self.assertEqual(rep.diagnostics, ())

    def test_single_project_ancestor_propagates_primary_scope_only(
        self,
    ) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(1, labels=("anneal", "exocrate"), sub_issues=(2,)),
                _make_issue(2, labels=(), parent_number=1, sub_issues=(3,)),
                _make_issue(3, labels=("ci",), parent_number=2),
            )
        )
        rep = ih.analyze_repo(snap)
        # Both #2 and #3 inherit `anneal` directly from #1 (citing #1, never
        # auto-inheriting sub-crate `exocrate`).
        self.assertEqual(
            rep.actions,
            (
                ih.AddLabels(
                    2, ("anneal",), "inherits single-project scope from #1"
                ),
                ih.AddLabels(
                    3, ("anneal",), "inherits single-project scope from #1"
                ),
            ),
        )
        self.assertEqual(rep.diagnostics, ())

    def test_multi_project_parent_does_not_auto_propagate(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(1, labels=("zerocopy", "anneal"), sub_issues=(2,)),
                _make_issue(2, labels=(), parent_number=1),
            )
        )
        rep = ih.analyze_repo(snap)
        self.assertEqual(rep.actions, ())
        self.assertEqual(
            [(d.code, d.target) for d in rep.diagnostics],
            [("missing-primary-scope", "#2")],
        )

    def test_legacy_type_migration_and_conflicts_fail_closed(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(1, labels=("zerocopy", "bug"), issue_type=None),
                _make_issue(
                    2, labels=("zerocopy", "enhancement"), issue_type="Feature"
                ),
                _make_issue(
                    3,
                    labels=("zerocopy", "bug", "enhancement"),
                    issue_type=None,
                ),
                _make_issue(4, labels=("anneal", "bug"), issue_type="Task"),
                _make_issue(
                    5, labels=("zerocopy", "enhancement"), issue_type="Bug"
                ),
            )
        )
        rep = ih.analyze_repo(snap)
        # #1 sets Type before removing `bug`; #2 removes matching `enhancement`;
        # #3, #4, #5 all conflict and must not be mutated.
        self.assertEqual(
            [
                (type(a).__name__, a.number)
                for a in rep.actions
            ],
            [
                ("SetIssueType", 1),
                ("RemoveLabels", 1),
                ("RemoveLabels", 2),
            ],
        )
        codes = {(d.code, d.target) for d in rep.diagnostics}
        self.assertIn(("conflicting-legacy-type", "#3"), codes)
        self.assertIn(("missing-type", "#3"), codes)
        self.assertIn(("conflicting-legacy-type", "#4"), codes)
        self.assertIn(("conflicting-legacy-type", "#5"), codes)

    def test_strip_pr_only_labels_and_clear_closed_milestone(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    859,
                    labels=("zerocopy", "hide-from-release-notes", "codex"),
                    milestone=ih.Milestone("0.9", "CLOSED"),
                ),
                _make_issue(
                    900,
                    labels=("zerocopy",),
                    milestone=ih.Milestone("0.10", "OPEN"),
                ),
            )
        )
        rep = ih.analyze_repo(snap)
        self.assertEqual(
            rep.actions,
            (
                ih.RemoveLabels(
                    859,
                    ("codex", "hide-from-release-notes"),
                    "PR/bot-only label is forbidden on Issues",
                ),
                ih.ClearMilestone(
                    859, "0.9", "open issue references a closed milestone"
                ),
            ),
        )
