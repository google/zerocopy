# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Gate 2 cross-family tests for `deleted_through` snapshots, same-tree
findings, and advisories."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    hashlib,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    parse_gate2_payload,
    patch,
    reconcile,
    review_result,
    summary,
    TREE,
)


class Gate2TombstoneTests:
    """Part of `Gate2CrossFamilyTests`."""

    def test_gate2_deleted_through_snapshot_and_same_tree_findings(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: edit commit message\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "path": "anneal/ci/codex_review.py", "line": 657, "summary": "Live finding"}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        pr_multi = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}

        # Live undeleted Gate 2 finding comments <= deleted_through still block
        # clean Gate 2 comment #30 and clean review #5; live Codex finding
        # comments <= deleted_through still block fallback Codex clean #30
        # while authentic Gate 2 clean verdicts remain authoritative.
        live_g2_finding_head = gate2_comment(
            comment_id=12, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        live_g2_finding_hist = gate2_comment(
            comment_id=12, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        live_codex_finding_head = summary(
            HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        live_codex_finding_head["id"] = 10
        live_codex_finding_hist = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        live_codex_finding_hist["id"] = 10
        clean_codex_30 = summary(HEAD)
        clean_codex_30["id"] = 30
        clean_cmt_30 = gate2_comment(
            comment_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        clean_rev_5 = gate2_review(
            review_id=5, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, cmts, revs, expected in (
            ("g2_head_cmt_vs_clean_cmt", [live_g2_finding_head, clean_cmt_30], [], "failure"),
            ("g2_head_cmt_vs_clean_rev", [live_g2_finding_head], [clean_rev_5], "failure"),
            ("g2_head_cmt_sole_tombstoned", [live_g2_finding_head], [], "failure"),
            ("g2_hist_cmt_vs_clean_cmt", [live_g2_finding_hist, clean_cmt_30], [], "failure"),
            ("g2_hist_cmt_vs_clean_rev", [live_g2_finding_hist], [clean_rev_5], "failure"),
            ("codex_head_vs_clean_codex", [live_codex_finding_head, clean_codex_30], [], "failure"),
            ("codex_hist_vs_clean_codex", [live_codex_finding_hist, clean_codex_30], [], "failure"),
            ("codex_head_vs_clean_cmt", [live_codex_finding_head, clean_cmt_30], [], "success"),
            ("codex_head_vs_clean_rev", [live_codex_finding_head], [clean_rev_5], "success"),
            ("codex_hist_vs_clean_cmt", [live_codex_finding_hist, clean_cmt_30], [], "success"),
            ("codex_hist_vs_clean_rev", [live_codex_finding_hist], [clean_rev_5], "success"),
        ):
            with self.subTest(live_finding_comment=label):
                gh = FakeGitHub(
                    [pr_amended],
                    {1: cmts},
                    reviews={1: revs},
                    deleted={1: 20},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh, publish=True)[HEAD].state, expected)

        # Live tombstoned-era Gate 2 finding on 404 OTHER_HEAD fails closed.
        gh_live_g2_404 = FakeGitHub(
            [pr_amended],
            {1: [live_g2_finding_hist, clean_cmt_30]},
            deleted={1: 20},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_live_g2_404, publish=True)
        self.assertEqual(gh_live_g2_404.writes[-1][1].state, "failure")

        # Older clean comment <= deleted_through still cannot approve.
        old_clean_cmt_10 = gate2_comment(
            comment_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            created_at="2026-11-23T01:00:00Z",
        )
        old_clean_codex_10 = summary(HEAD)
        old_clean_codex_10["id"] = 10
        for label, cmts in (
            ("clean_g2_blocked_by_deletion", [old_clean_cmt_10]),
            ("clean_codex_blocked_by_deletion", [old_clean_codex_10]),
        ):
            with self.subTest(tombstoned_clean=label):
                gh_pend = FakeGitHub(
                    [pr_amended],
                    {1: cmts},
                    deleted={1: 20},
                    trees={HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                self.assertEqual(reconcile(gh_pend, publish=True)[HEAD].state, "pending")

        # Concurrent in-place edit of a non-latest Codex summary from
        # running to completed findings invalidates the snapshot -> pending.
        codex_10_running = summary(HEAD, status="running")
        codex_10_running["id"] = 10
        codex_10_findings = summary(
            HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        codex_10_findings["id"] = 10
        codex_10_hist_findings = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        codex_10_hist_findings["id"] = 10
        codex_11_clean = summary(HEAD)
        codex_11_clean["id"] = 11
        codex_11_running = summary(HEAD, status="running")
        codex_11_running["id"] = 11
        for label, init_cmts, changed_cmts, revs in (
            (
                "head_codex_vs_clean_codex",
                [codex_10_running, codex_11_clean],
                [codex_10_findings, codex_11_clean],
                [],
            ),
            (
                "hist_codex_vs_clean_gate2",
                [codex_10_running, codex_11_running],
                [codex_10_hist_findings, codex_11_running],
                [clean_rev_5],
            ),
        ):
            with self.subTest(codex_summary_edit=label):
                gh_toctou = FakeGitHub(
                    [pr_amended],
                    {1: init_cmts},
                    changed_comments={1: changed_cmts},
                    reviews={1: revs},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh_toctou, publish=True)[HEAD].state, "pending")

        # Multi-commit HEAD preserving TREE still blocks on prior same-tree
        # Gate 2 findings (or fallback Codex findings without Gate 2), while an
        # authentic clean Gate 2 review on HEAD is authoritative over Codex.
        live_g2_rev_hist = gate2_review(
            review_id=59, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        multi_clean = gate2_review(
            review_id=60, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            identity_key=f"multi:{OTHER_BASE}:{HEAD}",
            submitted_at="2026-11-23T03:00:00Z",
        )
        for label, cmts, revs, expected_state, expected_substr in (
            ("multi_same_tree_g2", [], [live_g2_rev_hist, multi_clean], "failure", "finding"),
            ("multi_same_tree_codex_fallback", [live_codex_finding_hist, clean_codex_30], [], "failure", "Codex findings"),
            ("multi_same_tree_codex_with_gate2", [live_codex_finding_hist], [multi_clean], "success", "Clean Gate 2"),
        ):
            with self.subTest(same_tree_rewrite=label):
                gh_multi_same_tree = FakeGitHub(
                    [pr_multi],
                    {1: cmts},
                    reviews={1: revs},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: "9" * 40},
                    parents={HEAD: [BASE, OTHER_BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                verdict = reconcile(gh_multi_same_tree, publish=True)[HEAD]
                self.assertEqual(verdict.state, expected_state)
                self.assertIn(expected_substr, verdict.reason)

        # Direct review_result() keeps same-head, same-tree findings
        # blocking across base_sha retargets without historical_trees[head],
        # and reconcile() reuses tree_sha without a second commit_tree(head).
        retarget_finding = gate2_review(
            review_id=70, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings", findings=[finding],
        )
        retarget_clean = gate2_review(
            review_id=71, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            submitted_at="2026-11-23T03:00:00Z",
        )
        for label, revs in (
            ("sole_after_retarget", [retarget_finding]),
            ("followed_by_clean", [retarget_finding, retarget_clean]),
        ):
            with self.subTest(same_head_retarget=label):
                verdict = review_result(
                    HEAD, [], reviews=revs, base_sha=OTHER_BASE, tree_sha=TREE,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn("finding", verdict.reason)

        gh_retarget = FakeGitHub(
            [pr_multi], {1: []},
            reviews={1: [retarget_finding, retarget_clean]},
            trees={HEAD: TREE, BASE: parent_tree, OTHER_BASE: "9" * 40},
            parents={HEAD: [OTHER_BASE]},
            messages={HEAD: msg},
        )
        with patch.object(
            gh_retarget, "commit_tree", wraps=gh_retarget.commit_tree
        ) as tree_spy:
            self.assertEqual(reconcile(gh_retarget, publish=True)[HEAD].state, "failure")
            self.assertEqual(
                [call.args for call in tree_spy.call_args_list].count((HEAD,)),
                1,
            )

        # Earlier non-finding failures (CHANGES_REQUESTED, APPROVED,
        # same-family, wrong commit_id) on exact (HEAD, BASE, TREE) block.
        valid_clean_after = gate2_review(
            review_id=81, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, bad_rev, expected_substr in (
            (
                "changes_requested",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    state="CHANGES_REQUESTED", submitted_at="2026-11-23T01:00:00Z",
                ),
                "CHANGES_REQUESTED",
            ),
            (
                "approved",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    state="APPROVED", submitted_at="2026-11-23T01:00:00Z",
                ),
                "APPROVE",
            ),
            (
                "same_family",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    reviewer_family="claude", author_family="claude",
                    submitted_at="2026-11-23T01:00:00Z",
                ),
                "differ",
            ),
            (
                "wrong_commit_id",
                gate2_review(
                    review_id=80, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    commit_id=OTHER_HEAD, submitted_at="2026-11-23T01:00:00Z",
                ),
                "commit_id",
            ),
        ):
            with self.subTest(exact_non_finding_failure=label):
                verdict = review_result(
                    HEAD, [], reviews=[bad_rev, valid_clean_after],
                    base_sha=BASE, tree_sha=TREE, identity_key=ik,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn(expected_substr, verdict.reason)

        # A keyed clean review recorded against the current base_sha
        # (exact head, or a verified historical head on the same base) must
        # postdate base_changed_at; a verified cross-base transfer still works.
        changed = "2026-11-23T02:00:00Z"
        same_base_hist = {(OTHER_HEAD, BASE): (TREE, ik)}
        cross_base_hist = {(OTHER_HEAD, OTHER_BASE): (TREE, ik)}
        for label, rev_head, rev_base, submitted, hist, expected in (
            ("exact_stale", HEAD, BASE, "2026-11-23T01:00:00Z", None, "pending"),
            ("exact_fresh", HEAD, BASE, "2026-11-23T03:00:00Z", None, "success"),
            ("same_base_hist_stale", OTHER_HEAD, BASE, "2026-11-23T01:00:00Z",
             same_base_hist, "pending"),
            ("same_base_hist_fresh", OTHER_HEAD, BASE, "2026-11-23T03:00:00Z",
             same_base_hist, "success"),
            ("cross_base_hist_stale", OTHER_HEAD, OTHER_BASE,
             "2026-11-23T01:00:00Z", cross_base_hist, "success"),
        ):
            keyed_clean = gate2_review(
                review_id=90, head_sha=rev_head, base_sha=rev_base,
                tree_sha=TREE, identity_key=ik, submitted_at=submitted,
            )
            with self.subTest(keyed_freshness=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[keyed_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                        base_changed_at=changed,
                        historical_identities=hist,
                    ).state,
                    expected,
                )
        stale_keyed_comment = gate2_comment(
            comment_id=91, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [stale_keyed_comment], base_sha=BASE, tree_sha=TREE,
                identity_key=ik, base_changed_at=changed,
            ).state,
            "pending",
        )
        pr_same_base = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        gh_stale_keyed = FakeGitHub(
            [pr_same_base], {1: []},
            reviews={1: [gate2_review(
                review_id=92, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T01:00:00Z",
            )]},
            bases={1: changed},
            trees={HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        self.assertEqual(reconcile(gh_stale_keyed, publish=True)[HEAD].state, "pending")

        self._check_gate2_historical_failures_and_tombstones(
            msg=msg,
            parent_tree=parent_tree,
            ik=ik,
            pr_multi=pr_multi,
            changed=changed,
            same_base_hist=same_base_hist,
        )

    def test_gate2_advisories(self):
        advisory = {"severity": "P3", "summary": "Wording nit"}
        blocking = {"severity": "P2", "summary": "Real defect"}
        p3_finding = {"severity": "P3", "summary": "Blocking P3"}

        # Advisories are P3-only and never block a clean review; a P3 in
        # findings[] keeps blocking.
        for label, rev, expected in (
            ("clean_with_advisory",
             gate2_review(advisories=[advisory]), "success"),
            ("clean_with_empty_advisories", gate2_review(advisories=[]),
             "success"),
            ("p3_finding_blocks", gate2_review(
                verdict="findings", findings=[p3_finding]), "failure"),
            ("findings_with_advisory", gate2_review(
                verdict="findings", findings=[blocking],
                advisories=[advisory]), "failure"),
        ):
            with self.subTest(valid=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[rev], base_sha=BASE, tree_sha=TREE,
                    ).state,
                    expected,
                )
        for label, extra in (
            ("p2_advisory", {"advisories": [blocking]}),
            ("malformed_advisory", {"advisories": [{"severity": "P3"}]}),
            ("advisories_not_list", {"advisories": 5}),
            ("advisories_null", {"advisories": None}),
            ("unhashable_advisory_severity", {
                "advisories": [{"severity": [], "summary": "note"}]}),
            ("unhashable_finding_severity", {
                "verdict": "findings",
                "findings": [{"severity": {}, "summary": "note"}]}),
            # The only review modes are "full" and "delta", and delta_from
            # needs delta mode (see Gate2DeltaReviewTests).
            ("unknown_review_mode", {"review_mode": "partial"}),
            ("delta_from_without_mode", {"delta_from": OTHER_HEAD}),
            ("delta_from_with_full_mode",
             {"review_mode": "full", "delta_from": OTHER_HEAD}),
        ):
            with self.subTest(malformed=label):
                with self.assertRaises(ValueError):
                    parse_gate2_payload(gate2_review(**extra)["body"])
                # A malformed payload fails closed instead of crashing.
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[gate2_review(**extra)],
                        base_sha=BASE, tree_sha=TREE,
                    ).state,
                    "failure",
                )
