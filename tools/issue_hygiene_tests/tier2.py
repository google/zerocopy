# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tier 2 checks: title tags, code stripping, advisories, JSON output, and
tracker options.
"""

from __future__ import annotations

import json

import issue_hygiene as ih

from issue_hygiene_tests.support import _make_issue


class Tier2Cases:
    """Test methods of `IssueHygieneTier2Tests`."""

    def test_title_tag_mismatches_and_multi_hop_ptr_ancestor(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    1,
                    title="[anneal][reference] Research study",
                    labels=("anneal",),
                ),
                _make_issue(
                    2,
                    title="[docs] Fix Rust Reference links",
                    labels=("zerocopy", "documentation"),
                ),
                _make_issue(
                    3,
                    title="[pointer] Unparented Ptr invariant",
                    labels=("zerocopy",),
                ),
                _make_issue(859, title="Ptr tracker", labels=("zerocopy",)),
                _make_issue(
                    860,
                    title="Ptr sub-epic",
                    labels=("zerocopy",),
                    parent_number=859,
                ),
                _make_issue(
                    861,
                    title="[ptr] Grandchild under #859",
                    labels=("zerocopy",),
                    parent_number=860,
                ),
            ),
            ptr_tracker=859,
        )
        rep = ih.analyze_repo(snap)
        self.assertEqual(
            [(d.code, d.target) for d in rep.diagnostics],
            [
                ("title-label-mismatch", "#1"),
                ("title-label-mismatch", "#3"),
            ],
        )

    def test_code_stripping_entities_bullets_and_dedup(self) -> None:
        body = (
            "- [ ] Land #100\n"
            "* [ ] Also mentions #100 again\n"
            "+ [ ] Track #101\n"
            "See #102 and inline `#102` and entity &#102; for context.\n"
            "````rust\n"
            "```\n"
            "- [ ] #100 inside 4-backtick fence\n"
            "```\n"
            "````\n"
            "~~~\n"
            "- [ ] #100 inside tilde fence\n"
            "#102 inside tilde fence\n"
            "~~~\n"
        )
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    50, labels=("zerocopy",), body=body, has_sub_issues=True
                ),
                _make_issue(
                    51,
                    labels=("zerocopy",),
                    body=(
                        "See `#102` and &#100;\n"
                        "- [ ]\n"
                        "- [x] Completed #100\n"
                        "~~~ \n- [ ] #100\n~~~\n"
                        "```inline``` still sees prose below:\n"
                        "Actual ref: #102\n"
                    ),
                ),
                _make_issue(101, labels=("zerocopy",)),
            ),
            refs={
                100: ih.RefState("Issue", "CLOSED"),
                102: ih.RefState("PullRequest", "CLOSED"),
            },
        )
        rep = ih.analyze_repo(snap)
        # Note: #101 is synthesized as OPEN from `snapshot.issues`, #100 is
        # deduplicated once despite appearing in two unchecked items, and #51
        # ignores inline/entity/tilde-fenced refs while still seeing prose
        # after a line-leading inline triple-backtick span.
        self.assertEqual(
            [(d.code, d.target) for d in rep.diagnostics],
            [
                ("stale-checklist-ref", "#50"),
                ("closed-unmerged-pr-ref", "#50"),
                ("unlinked-tasklist-ref", "#50"),
                ("closed-unmerged-pr-ref", "#51"),
            ],
        )

    def test_advisories_cross_repo_blockers_compat_and_external_refs(
        self,
    ) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    3642,
                    title="Yank vulnerable versions",
                    labels=("zerocopy", "zerocopy-derive"),
                    blocked_by=(ih.Blocker("#3613", "OPEN", 3613),),
                    relates_to=(3612,),
                ),
                _make_issue(
                    3612,
                    title="Security Advisory: Exocrate staging",
                    labels=("anneal", "exocrate"),
                    issue_type="Bug",
                ),
                _make_issue(
                    3613,
                    title="Soundness Advisory: Read witness",
                    labels=("zerocopy",),
                    issue_type="Bug",
                ),
                _make_issue(
                    3619,
                    title="Security Advisory: Unlinked enum bug",
                    labels=("zerocopy", "zerocopy-derive"),
                    issue_type="Bug",
                ),
                _make_issue(
                    500,
                    labels=(
                        "zerocopy",
                        "compatibility-breaking",
                        "compatibility-nonbreaking",
                    ),
                    blocked_by=(
                        ih.Blocker("rust-lang/rust#400", "CLOSED", None),
                    ),
                ),
            ),
            external_refs=(
                ih.ExternalIssueRef(
                    "rust-lang",
                    "rust",
                    57349,
                    "Source",
                    "zerocopy/src/wrappers.rs:310",
                ),
                ih.ExternalIssueRef(
                    "Rust-Lang", "Rust", 57349, "Issue", "#208"
                ),
                ih.ExternalIssueRef(
                    "rust-lang", "rust", 73255, "Issue", "#208"
                ),
            ),
            external_states={
                ("rust-lang", "rust", 57349): "CLOSED",
                ("rust-lang", "rust", 73255): "OPEN",
            },
            advisory_tracker=3642,
        )
        rep = ih.analyze_repo(snap)
        self.assertEqual(
            {(d.code, d.target_kind, d.target) for d in rep.diagnostics},
            {
                ("unlinked-advisory", "Issue", "#3619"),
                ("conflicting-compatibility", "Issue", "#500"),
                ("resolved-blockers", "Issue", "#500"),
                (
                    "closed-upstream-blocker",
                    "Source",
                    "zerocopy/src/wrappers.rs:310",
                ),
                ("closed-upstream-blocker", "Issue", "#208"),
            },
        )

    def test_advisory_linked_via_native_sub_issues_not_flagged(self) -> None:
        snap = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    3642,
                    title="Yank vulnerable versions",
                    labels=("zerocopy",),
                    sub_issues=(3615,),
                ),
                _make_issue(
                    3614,
                    title="Security Advisory: Linked by parent only",
                    labels=("zerocopy",),
                    issue_type="Bug",
                    parent_number=3642,
                ),
                _make_issue(
                    3615,
                    title="Soundness Advisory: Linked by tracker sub_issues",
                    labels=("zerocopy",),
                    issue_type="Bug",
                ),
                _make_issue(
                    3619,
                    title="Security Advisory: Truly unlinked",
                    labels=("zerocopy",),
                    issue_type="Bug",
                ),
            ),
            advisory_tracker=3642,
        )
        rep = ih.analyze_repo(snap)
        unlinked = [d for d in rep.diagnostics if d.code == "unlinked-advisory"]
        self.assertEqual([(d.target, d.code) for d in unlinked], [("#3619", "unlinked-advisory")])
        self.assertIn("subIssues/blockedBy/relatesTo", unlinked[0].message)

        # Also verify parent_number works when the tracker issue is absent from
        # the open-issue snapshot (e.g. closed tracker).
        snap_missing_tracker = ih.RepoSnapshot(
            issues=(
                _make_issue(
                    3614,
                    title="Security Advisory: Child of closed tracker",
                    labels=("zerocopy",),
                    issue_type="Bug",
                    parent_number=3642,
                ),
            ),
            advisory_tracker=3642,
        )
        rep_missing = ih.analyze_repo(snap_missing_tracker)
        self.assertEqual(rep_missing.diagnostics, ())

    def test_json_formatting_and_cli_tracker_disable(self) -> None:
        rep = ih.analyze_repo(
            ih.RepoSnapshot(
                issues=(_make_issue(1, labels=("exocrate",), issue_type=None),)
            )
        )
        parsed = json.loads(ih.format_report(rep, as_json=True))
        self.assertEqual(parsed["actions"][0]["kind"], "add_labels")
        self.assertEqual(len(parsed["diagnostics"]), 1)

        args = ih.parse_args(
            ["--advisory-tracker", "0", "--ptr-tracker", "0"]
        )
        self.assertIsNone(args.advisory_tracker)
        self.assertIsNone(args.ptr_tracker)
