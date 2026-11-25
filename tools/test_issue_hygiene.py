# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit tests for `tools/issue_hygiene.py`."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import unittest
from unittest import mock

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


class IssueHygieneTier1Tests(unittest.TestCase):
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


class IssueHygieneTier2Tests(unittest.TestCase):
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


class IssueHygieneIoAndCliTests(unittest.TestCase):
    def test_extract_external_refs_filters_self_repo_and_code_blocks(
        self,
    ) -> None:
        iss = _make_issue(
            208,
            body=(
                "See https://github.com/CustomOrg/CustomRepo/issues/9\n"
                "And https://github.com/rust-lang/rust/issues/57349\n"
                "```\nhttps://github.com/rust-lang/rust/issues/99999\n```\n"
            ),
        )
        refs = ih.extract_issue_external_refs(
            (iss,), repo_owner="customorg", repo_name="customrepo"
        )
        self.assertEqual(
            refs,
            (
                ih.ExternalIssueRef(
                    "rust-lang", "rust", 57349, "Issue", "#208"
                ),
            ),
        )

    def test_scan_repo_external_markers_skips_self_repo(self) -> None:
        # Construct marker dynamically so live `--check-upstream` source scans
        # do not match this test fixture line.
        tag = "FIX" + "ME"
        stdout = (
            f"zerocopy/src/a.rs:10:// {tag}"
            "(https://github.com/google/zerocopy/issues/1)\n"
            f"zerocopy/src/b.rs:20:// {tag}"
            "(https://github.com/example/upstream/issues/123)\n"
        )
        fake = subprocess.CompletedProcess(
            args=["git"], returncode=0, stdout=stdout, stderr=""
        )
        with mock.patch("subprocess.run", return_value=fake) as run_mock:
            refs = ih.scan_repo_external_markers(Path("/tmp/repo"))
        self.assertIn("-I", run_mock.call_args[0][0])
        self.assertIn(":(glob,exclude)**/vendor/**", run_mock.call_args[0][0])
        self.assertEqual(
            refs,
            (
                ih.ExternalIssueRef(
                    "example",
                    "upstream",
                    123,
                    "Source",
                    "zerocopy/src/b.rs:20",
                ),
            ),
        )

    def test_graphql_not_found_and_error_handling(self) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        not_found_out = json.dumps(
            {
                "data": {"repository": {"r9999": None}},
                "errors": [{"type": "NOT_FOUND", "message": "not found"}],
            }
        )
        fake_nf = subprocess.CompletedProcess(
            args=["gh"], returncode=1, stdout=not_found_out, stderr="404"
        )
        with mock.patch("subprocess.run", return_value=fake_nf):
            data = gh.graphql("query {}", allow_not_found=True)
            self.assertEqual(data, {"repository": {"r9999": None}})
            with self.assertRaises(RuntimeError):
                gh.graphql("query {}", allow_not_found=False)

        null_repo = json.dumps(
            {
                "data": {"repository": None},
                "errors": [{"type": "NOT_FOUND", "message": "repo not found"}],
            }
        )
        fake_null = subprocess.CompletedProcess(
            args=["gh"], returncode=1, stdout=null_repo, stderr="404"
        )
        with mock.patch("subprocess.run", return_value=fake_null):
            self.assertEqual(gh.fetch_refs([1]), {})

    def test_fetch_open_issues_paginates_connections_and_filters_cross_repo(
        self,
    ) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        page1 = {
            "repository": {
                "issues": {
                    "pageInfo": {"hasNextPage": False, "endCursor": None},
                    "nodes": [
                        {
                            "id": "I_10",
                            "number": 10,
                            "title": "Epic",
                            "body": "",
                            "issueType": {"name": "Task"},
                            "milestone": None,
                            "labels": {
                                "pageInfo": {
                                    "hasNextPage": False,
                                    "endCursor": None,
                                },
                                "nodes": [{"name": "zerocopy"}],
                            },
                            "parent": {
                                "number": 1,
                                "repository": {"nameWithOwner": "other/repo"},
                            },
                            "subIssues": {
                                "pageInfo": {
                                    "hasNextPage": True,
                                    "endCursor": "C1",
                                },
                                "nodes": [
                                    {
                                        "number": 11,
                                        "repository": {
                                            "nameWithOwner": "google/zerocopy"
                                        },
                                    }
                                ],
                            },
                            "subIssuesSummary": {"total": 3},
                            "blockedBy": {
                                "pageInfo": {
                                    "hasNextPage": False,
                                    "endCursor": None,
                                },
                                "nodes": [
                                    {
                                        "number": 99,
                                        "state": "CLOSED",
                                        "repository": {
                                            "nameWithOwner": "other/repo"
                                        },
                                    },
                                    None,
                                ],
                            },
                            "relatesTo": {
                                "pageInfo": {
                                    "hasNextPage": False,
                                    "endCursor": None,
                                },
                                "nodes": [],
                            },
                        }
                    ],
                }
            }
        }
        sub_page2 = {
            "node": {
                "subIssues": {
                    "pageInfo": {"hasNextPage": False, "endCursor": None},
                    "nodes": [
                        {
                            "number": 12,
                            "repository": {"nameWithOwner": "google/zerocopy"},
                        },
                        {
                            "number": 13,
                            "repository": {"nameWithOwner": "other/repo"},
                        },
                        None,
                    ],
                }
            }
        }
        with mock.patch.object(
            gh, "graphql", side_effect=[page1, sub_page2]
        ) as gql_mock:
            issues = gh.fetch_open_issues()
        followup_query = gql_mock.call_args_list[1][0][0]
        self.assertEqual(followup_query.count("{"), followup_query.count("}"))
        self.assertEqual(len(issues), 1)
        iss = issues[0]
        self.assertIsNone(iss.parent_number)
        self.assertEqual(iss.sub_issues, frozenset({11, 12}))
        # Inaccessible `None` blocker stays UNKNOWN so `resolved-blockers` does
        # not falsely fire on issue #10.
        self.assertEqual(
            iss.blocked_by,
            (
                ih.Blocker("other/repo#99", "CLOSED", None),
                ih.Blocker("<inaccessible>", "UNKNOWN", None),
            ),
        )
        rep = ih.analyze_repo(ih.RepoSnapshot(issues=issues))
        self.assertNotIn(
            "resolved-blockers", {d.code for d in rep.diagnostics}
        )

    def test_apply_actions_prevalidates_before_mutating(self) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        issues_by_num = {1: _make_issue(1, labels=("bug",), issue_type=None)}
        actions: tuple[ih.Action, ...] = (
            ih.SetIssueType(1, "Bug", "migrate"),
            ih.AddLabels(1, ("missing-label",), "needs label"),
        )
        with (
            mock.patch.object(
                gh,
                "fetch_metadata",
                return_value=({"bug": "L1"}, {"Bug": "T1"}),
            ),
            mock.patch.object(gh, "graphql") as gql_mock,
        ):
            with self.assertRaisesRegex(
                RuntimeError, "Aborting before any mutation"
            ):
                gh.apply_actions(actions, issues_by_num)
            # Zero mutations were sent because pre-validation failed closed.
            gql_mock.assert_not_called()

    def test_apply_actions_order_and_mid_batch_failure_reporting(self) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        issues_by_num = {1: _make_issue(1, labels=("bug",), issue_type=None)}
        actions: tuple[ih.Action, ...] = (
            ih.SetIssueType(1, "Bug", "migrate"),
            ih.RemoveLabels(1, ("bug",), "migrated"),
            ih.ClearMilestone(1, "0.9", "closed"),
        )
        with (
            mock.patch.object(
                gh,
                "fetch_metadata",
                return_value=({"bug": "L1"}, {"Bug": "T1"}),
            ),
            mock.patch.object(
                gh,
                "graphql",
                side_effect=[{}, RuntimeError("rate limited")],
            ) as gql_mock,
            mock.patch("sys.stderr"),
        ):
            with self.assertRaisesRegex(
                RuntimeError, r"Applied 1/3 actions before failure"
            ):
                gh.apply_actions(actions, issues_by_num)
            self.assertEqual(gql_mock.call_count, 2)
            self.assertIn(
                "updateIssueIssueType", gql_mock.call_args_list[0][0][0]
            )
            self.assertIn(
                "removeLabelsFromLabelable", gql_mock.call_args_list[1][0][0]
            )

    def test_fetch_metadata_paginates_labels_and_types(self) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        pages = [
            {
                "repository": {
                    "labels": {
                        "pageInfo": {"hasNextPage": True, "endCursor": "L1"},
                        "nodes": [{"id": "id1", "name": "zerocopy"}],
                    }
                }
            },
            {
                "repository": {
                    "labels": {
                        "pageInfo": {"hasNextPage": False, "endCursor": None},
                        "nodes": [{"id": "id2", "name": "anneal"}],
                    }
                }
            },
            {
                "repository": {
                    "issueTypes": {
                        "pageInfo": {"hasNextPage": True, "endCursor": "T1"},
                        "nodes": [
                            {"id": "t1", "name": "Bug", "isEnabled": True},
                            {"id": "t0", "name": "Old", "isEnabled": False},
                        ],
                    }
                }
            },
            {
                "repository": {
                    "issueTypes": {
                        "pageInfo": {"hasNextPage": False, "endCursor": None},
                        "nodes": [
                            {"id": "t2", "name": "Task", "isEnabled": True}
                        ],
                    }
                }
            },
        ]
        with mock.patch.object(gh, "graphql", side_effect=pages):
            labels, types = gh.fetch_metadata()
        self.assertEqual(labels, {"zerocopy": "id1", "anneal": "id2"})
        self.assertEqual(types, {"Bug": "t1", "Task": "t2"})

    def test_fetch_metadata_handles_null_issue_types_and_missing_cursor(
        self,
    ) -> None:
        gh = ih.GitHubCli("user", "personal-repo")
        pages = [
            {
                "repository": {
                    "labels": {
                        "pageInfo": {"hasNextPage": False, "endCursor": None},
                        "nodes": [{"id": "id1", "name": "zerocopy"}, None],
                    }
                }
            },
            {"repository": {"issueTypes": None}},
        ]
        with mock.patch.object(gh, "graphql", side_effect=pages) as gql_mock:
            labels, types = gh.fetch_metadata()
        self.assertEqual(gql_mock.call_count, 2)
        self.assertEqual(labels, {"zerocopy": "id1"})
        self.assertEqual(types, {})

        bad_cursor = {
            "repository": {
                "labels": {
                    "pageInfo": {"hasNextPage": True, "endCursor": None},
                    "nodes": [{"id": "id1", "name": "zerocopy"}],
                }
            }
        }
        with mock.patch.object(gh, "graphql", return_value=bad_cursor):
            with self.assertRaisesRegex(RuntimeError, "Missing `endCursor`"):
                gh.fetch_metadata()

    def test_fetch_refs_and_external_states_enforce_graphql_int_and_vars(
        self,
    ) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        with mock.patch.object(
            gh,
            "graphql",
            return_value={
                "repository": {"r42": {"__typename": "Issue", "state": "OPEN"}}
            },
        ) as gql_mock:
            refs = gh.fetch_refs([-5, 0, 42, 2_147_483_648, 999_999_999_999])
        self.assertEqual(refs, {42: ih.RefState("Issue", "OPEN")})
        query = gql_mock.call_args[0][0]
        self.assertIn("r42:", query)
        self.assertNotIn("2147483648", query)
        self.assertNotIn("r0:", query)

        ext_refs = (
            ih.ExternalIssueRef("rust-lang\n", "rust", 1, "Issue", "#208"),
            ih.ExternalIssueRef("rust-lang", "rust", 0, "Issue", "#208"),
            ih.ExternalIssueRef(
                "rust-lang", "rust", 2_147_483_648, "Issue", "#208"
            ),
            ih.ExternalIssueRef("rust-lang", "rust", 57349, "Issue", "#208"),
        )
        with mock.patch.object(
            gh,
            "graphql",
            return_value={"e0": {"issue": {"state": "CLOSED"}}},
        ) as gql_mock:
            states = gh.fetch_external_states(ext_refs)
        self.assertEqual(states, {("rust-lang", "rust", 57349): "CLOSED"})
        q_ext, vars_ext = gql_mock.call_args[0][0], gql_mock.call_args[0][1]
        self.assertNotIn('"rust-lang"', q_ext)
        self.assertEqual(
            vars_ext, {"ow0": "rust-lang", "rp0": "rust", "num0": 57349}
        )

    def test_graphql_invalid_json_raises_runtime_error_without_retrying(
        self,
    ) -> None:
        gh = ih.GitHubCli("google", "zerocopy")
        bad_json = subprocess.CompletedProcess(
            args=["gh"],
            returncode=0,
            stdout="not valid json",
            stderr="unexpected token",
        )
        with (
            mock.patch("subprocess.run", return_value=bad_json) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(
                RuntimeError,
                r"invalid JSON.*unexpected token.*not valid json",
            ):
                gh.graphql("query { ok }")
        self.assertEqual(run_mock.call_count, 1)
        self.assertEqual(
            run_mock.call_args.kwargs["timeout"],
            ih.DEFAULT_GRAPHQL_TIMEOUT_SECONDS,
        )
        sleep_mock.assert_not_called()

        non_obj = subprocess.CompletedProcess(
            args=["gh"], returncode=0, stdout="[]", stderr=""
        )
        with (
            mock.patch("subprocess.run", return_value=non_obj) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "non-object JSON"):
                gh.graphql("query { ok }")
        self.assertEqual(run_mock.call_count, 1)
        sleep_mock.assert_not_called()

    def test_graphql_transient_and_timeout_retries_vs_permanent_errors(
        self,
    ) -> None:
        gh = ih.GitHubCli("google", "zerocopy", timeout=15.0)

        # Transient timeout + HTTP 502 recover on retry.
        side_effects = [
            subprocess.TimeoutExpired(
                cmd=["gh", "api", "graphql"], timeout=15.0, stderr="timed out"
            ),
            subprocess.CompletedProcess(
                args=["gh"],
                returncode=1,
                stdout="",
                stderr="HTTP 502 Bad Gateway",
            ),
            subprocess.CompletedProcess(
                args=["gh"],
                returncode=0,
                stdout=json.dumps({"data": {"ok": True}}),
                stderr="",
            ),
        ]
        with (
            mock.patch(
                "subprocess.run", side_effect=side_effects
            ) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            data = gh.graphql("query { ok }")
        self.assertEqual(data, {"ok": True})
        self.assertEqual(run_mock.call_count, 3)
        self.assertTrue(
            all(
                call.kwargs["timeout"] == 15.0
                for call in run_mock.call_args_list
            )
        )
        self.assertEqual(
            [c.args[0] for c in sleep_mock.call_args_list],
            list(ih.RETRY_BACKOFF_SECONDS),
        )

        # Transient HTML 503 page (non-JSON) retries and recovers on valid JSON.
        html_503_seq = [
            subprocess.CompletedProcess(
                args=["gh"],
                returncode=1,
                stdout="<html>503 Service Unavailable</html>",
                stderr="",
            ),
            subprocess.CompletedProcess(
                args=["gh"],
                returncode=0,
                stdout=json.dumps({"data": {"ok": True}}),
                stderr="",
            ),
        ]
        with (
            mock.patch(
                "subprocess.run", side_effect=html_503_seq
            ) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            self.assertEqual(gh.graphql("query { ok }"), {"ok": True})
        self.assertEqual(run_mock.call_count, 2)
        self.assertEqual(
            [c.args[0] for c in sleep_mock.call_args_list],
            [ih.RETRY_BACKOFF_SECONDS[0]],
        )

        # Exhausted timeouts raise RuntimeError after bounded retries.
        timeout_exc = subprocess.TimeoutExpired(
            cmd=["gh", "api", "graphql"], timeout=15.0, stderr=b"still hung"
        )
        with (
            mock.patch("subprocess.run", side_effect=timeout_exc) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(
                RuntimeError, r"timed out after 15\.0s: still hung"
            ):
                gh.graphql("query { ok }")
        self.assertEqual(
            run_mock.call_count, len(ih.RETRY_BACKOFF_SECONDS) + 1
        )
        self.assertEqual(
            sleep_mock.call_count, len(ih.RETRY_BACKOFF_SECONDS)
        )

        # NOT_FOUND without allow_not_found fails immediately without sleeping.
        not_found = subprocess.CompletedProcess(
            args=["gh"],
            returncode=1,
            stdout=json.dumps(
                {
                    "data": {"repository": None},
                    "errors": [{"type": "NOT_FOUND", "message": "not found"}],
                }
            ),
            stderr="",
        )
        with (
            mock.patch("subprocess.run", return_value=not_found) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "NOT_FOUND"):
                gh.graphql("query { ok }", allow_not_found=False)
        self.assertEqual(run_mock.call_count, 1)
        sleep_mock.assert_not_called()

        # Permanent GraphQL schema error fails immediately with zero sleeps.
        perm = subprocess.CompletedProcess(
            args=["gh"],
            returncode=1,
            stdout=json.dumps(
                {
                    "errors": [
                        {
                            "type": "FIELD_ERROR",
                            "message": "Field 'bad' doesn't exist",
                        }
                    ]
                }
            ),
            stderr="",
        )
        with (
            mock.patch("subprocess.run", return_value=perm) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "GraphQL errors"):
                gh.graphql("query { bad }")
        self.assertEqual(run_mock.call_count, 1)
        sleep_mock.assert_not_called()

        # Transient GraphQL RATE_LIMITED retries, whereas NOT_FOUND does not.
        rate_limited = subprocess.CompletedProcess(
            args=["gh"],
            returncode=1,
            stdout=json.dumps(
                {
                    "errors": [
                        {"type": "RATE_LIMITED", "message": "API rate limit"}
                    ]
                }
            ),
            stderr="",
        )
        with (
            mock.patch(
                "subprocess.run", return_value=rate_limited
            ) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "RATE_LIMITED"):
                gh.graphql("query { ok }")
        self.assertEqual(
            run_mock.call_count, len(ih.RETRY_BACKOFF_SECONDS) + 1
        )
        self.assertEqual(
            sleep_mock.call_count, len(ih.RETRY_BACKOFF_SECONDS)
        )

        # NOT_FOUND without allow_not_found fails immediately without sleeping.
        not_found = subprocess.CompletedProcess(
            args=["gh"],
            returncode=1,
            stdout=json.dumps(
                {
                    "data": {"repository": None},
                    "errors": [{"type": "NOT_FOUND", "message": "not found"}],
                }
            ),
            stderr="",
        )
        with (
            mock.patch("subprocess.run", return_value=not_found) as run_mock,
            mock.patch("time.sleep") as sleep_mock,
        ):
            with self.assertRaisesRegex(RuntimeError, "NOT_FOUND"):
                gh.graphql("query { ok }", allow_not_found=False)
        self.assertEqual(run_mock.call_count, 1)
        sleep_mock.assert_not_called()


if __name__ == "__main__":
    unittest.main()
