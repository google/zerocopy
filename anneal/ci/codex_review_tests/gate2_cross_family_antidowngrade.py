# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Gate 2 cross-family anti-downgrade tests against mismatched, malformed,
legacy, merge-base, and tombstoned history."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    hashlib,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    patch,
    reconcile,
    review_result,
    summary,
    TREE,
)


class Gate2AntiDowngradeTests:
    """Part of `Gate2CrossFamilyTests`."""

    def test_gate2_antidowngrade_preserves_mismatched_malformed_and_legacy_findings(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: fix wording\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        other_parent_tree = "5" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "summary": "Soundness gap"}

        later_clean_exact = gate2_review(
            review_id=20, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        # Exact-head findings with mismatched structured key,
        # malformed one:/multi: key, or contradictory key still block a later
        # clean review on the exact commit.
        prior_exact_cases = [
            ("mismatched_structured", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
            ("malformed_one", {"identity_key": "one:not-a-valid-key"}),
            ("malformed_multi", {"identity_key": "multi:bad"}),
            ("whitespace_ik", {"identity_key": " "}),
            ("contradictory_parent_tree", {"parent_tree": other_parent_tree, "identity_key": ik}),
        ]
        for label, extra in prior_exact_cases:
            with self.subTest(case=label):
                prior_bad = gate2_review(
                    review_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    verdict="findings", findings=[finding], **extra,
                )
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[prior_bad, later_clean_exact],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )
        # A malformed prior clean review does not poison a newer clean one.
        prior_bad_clean = gate2_review(
            review_id=11, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key="one:not-a-valid-key",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[prior_bad_clean, later_clean_exact],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "success",
        )

        # Legacy (no identity_key or custom legacy key) findings on
        # OTHER_HEAD still block HEAD after squash-rebase onto OTHER_BASE or
        # no-op amend on BASE when historical commit identity matches.
        pr_rebased = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        for label, extra in (("keyless", {}), ("legacy_key", {"identity_key": "legacy-v1"})):
            old_findings = gate2_review(
                review_id=30, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
                verdict="findings", findings=[finding], **extra,
            )
            clean_rebased = gate2_review(
                review_id=31, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(mode="squash_rebase", label=label):
                gh_rebase = FakeGitHub(
                    [pr_rebased], {1: []},
                    reviews={1: [old_findings, clean_rebased]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
                    parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh_rebase, publish=True)[HEAD].state, "failure")

            clean_amended = gate2_review(
                review_id=32, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(mode="noop_amend", label=label):
                gh_amend = FakeGitHub(
                    [pr_amended], {1: []},
                    reviews={1: [old_findings, clean_amended]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh_amend, publish=True)[HEAD].state, "failure")

        # Changing only the commit message while preserving the tree
        # keeps prior same-tree Gate 2 findings blocking (keyless and one:).
        for label, extra in (
            ("keyless", {}),
            ("one_key", {"identity_key": f"one:{parent_tree}:{TREE}:{hashlib.sha256(other_msg.encode('utf-8')).hexdigest()}"}),
        ):
            old_same_tree_findings = gate2_review(
                review_id=40, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
                verdict="findings", findings=[finding], **extra,
            )
            new_msg_clean = gate2_review(
                review_id=41, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(msg_changed=label):
                gh_msg_changed = FakeGitHub(
                    [pr_amended], {1: []},
                    reviews={1: [old_same_tree_findings, new_msg_clean]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: other_msg},
                )
                self.assertEqual(reconcile(gh_msg_changed, publish=True)[HEAD].state, "failure")

        # Spoofed same tree_sha in a prior OTHER_HEAD payload does not block
        # when GitHub confirms OTHER_HEAD actually had a different tree.
        spoofed_tree_findings = gate2_review(
            review_id=42, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            verdict="findings", findings=[finding],
        )
        new_msg_clean = gate2_review(
            review_id=41, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        gh_spoofed_tree = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [spoofed_tree_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: OTHER_TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(reconcile(gh_spoofed_tree, publish=True)[HEAD].state, "success")

        # Needed by gh_same_tree_404 below.
        old_keyless_findings = gate2_review(
            review_id=40, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            verdict="findings", findings=[finding],
        )

        # Changing the tree after a keyless finding also passes without needing
        # the superseded OTHER_HEAD commit to still exist in GitHub.
        old_tree_findings = gate2_review(
            review_id=50, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=OTHER_TREE,
            verdict="findings", findings=[finding],
        )
        gh_tree_changed_404 = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [old_tree_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        self.assertEqual(reconcile(gh_tree_changed_404, publish=True)[HEAD].state, "success")

        # Missing (404) same-tree historical keyless findings fail closed.
        gh_same_tree_404 = FakeGitHub(
            [pr_amended], {1: []},
            reviews={1: [old_keyless_findings, new_msg_clean]},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_same_tree_404, publish=True)
        self.assertEqual(gh_same_tree_404.writes[-1][1].state, "failure")

        # Sole/latest keyless findings on OTHER_HEAD still block HEAD after
        # squash-rebase or no-op amend, even with a clean Codex summary on HEAD.
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_keyless_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                HEAD, [summary()], reviews=[old_keyless_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "failure",
        )
        gh_sole_finding_with_codex = FakeGitHub(
            [pr_rebased], {1: [summary()]},
            reviews={1: [old_keyless_findings]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
            parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(
            reconcile(gh_sole_finding_with_codex, publish=True)[HEAD].state,
            "failure",
        )

    def test_gate2_antidowngrade_codex_merge_base_clean_poison_and_tombstone(self):
        msg = "feat: add identity check\n\nBody"
        other_msg = "feat: edit message\n\nBody"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        parent_tree = "4" * 40
        other_parent_tree = "5" * 40
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        finding = {"severity": "P1", "summary": "Soundness defect"}

        # Exact-(HEAD, BASE, TREE) findings without matching one:
        # identity_key still block after a base_changed_at event on exact BASE.
        for label, extra in (
            ("keyless", {}),
            ("legacy_key", {"identity_key": "legacy-v1"}),
            ("malformed_one", {"identity_key": "one:bad"}),
            ("mismatched_one", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
        ):
            r_findings = gate2_review(
                review_id=10, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T01:00:00Z",
                verdict="findings", findings=[finding], **extra,
            )
            r_clean_after = gate2_review(
                review_id=11, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )
            with self.subTest(exact_finding_without_key=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[r_findings],
                        base_changed_at="2026-11-23T02:00:00Z",
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[r_findings, r_clean_after],
                        base_changed_at="2026-11-23T02:00:00Z",
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "failure",
                )

        # Clean keyless exact-head review still turns pending after base change.
        stale_clean = gate2_review(
            review_id=12, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_clean],
                base_changed_at="2026-11-23T02:00:00Z",
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "pending",
        )

        # Authentic cross-family Gate 2 clean verdicts covering HEAD's current
        # identity are authoritative over prior or running legacy Codex
        # summaries, while legacy Codex fallback still blocks same-tree
        # findings when no authentic Gate 2 review covers HEAD.
        codex_old_findings = summary(
            OTHER_HEAD, status="completed",
            has_any_findings=True, has_unresolved_findings=True,
        )
        clean_rebased_g2 = gate2_review(
            review_id=20, head_sha=HEAD, base_sha=OTHER_BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        clean_old_g2 = gate2_review(
            review_id=21, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
        )
        pr_rebased = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
        pr_amended = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        for label, pr_obj, g2_rev in (
            ("squash_rebase_new_g2", pr_rebased, clean_rebased_g2),
            ("squash_rebase_reused_g2", pr_rebased, clean_old_g2),
            ("noop_amend", pr_amended, gate2_review(
                review_id=22, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )),
        ):
            with self.subTest(historical_codex_findings=label):
                gh = FakeGitHub(
                    [pr_obj], {1: [codex_old_findings]},
                    reviews={1: [g2_rev]},
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
                    parents={HEAD: [pr_obj["base"]["sha"]], OTHER_HEAD: [BASE]},
                    messages={HEAD: msg, OTHER_HEAD: msg},
                )
                self.assertEqual(reconcile(gh, publish=True)[HEAD].state, "success")

        codex_running_new = summary(HEAD, status="running")
        codex_running_new["id"] = 11
        gh_codex_running = FakeGitHub(
            [pr_rebased], {1: [codex_old_findings, codex_running_new]},
            reviews={1: [clean_rebased_g2]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree, OTHER_BASE: parent_tree},
            parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(reconcile(gh_codex_running, publish=True)[HEAD].state, "success")

        # Without an authentic Gate 2 review, a newer clean or running Codex
        # summary on HEAD does not mask an older completed-findings Codex
        # summary on HEAD or on a same-tree historical commit.
        codex_old_findings_head = summary(
            HEAD, has_any_findings=True, has_unresolved_findings=True,
        )
        codex_old_findings_head["id"] = 10
        codex_old_findings_hist = summary(
            OTHER_HEAD, has_any_findings=True, has_unresolved_findings=True,
        )
        codex_old_findings_hist["id"] = 10
        codex_clean_new = summary(
            HEAD, created_at="2026-11-08T11:00:00Z",
            completed_at="2026-11-08T11:01:00Z",
        )
        codex_clean_new["id"] = 11
        for label, cmts, hist_trees, expected in (
            ("clean_only", [codex_clean_new], None, "success"),
            ("older_findings_on_head",
             [codex_old_findings_head, codex_clean_new], None, "failure"),
            ("older_findings_same_tree",
             [codex_old_findings_hist, codex_clean_new],
             {OTHER_HEAD: TREE}, "failure"),
            ("older_findings_other_tree",
             [codex_old_findings_hist, codex_clean_new],
             {OTHER_HEAD: OTHER_TREE}, "success"),
        ):
            with self.subTest(codex_clean_after_findings=label):
                self.assertEqual(
                    review_result(
                        HEAD, cmts, tree_sha=TREE, historical_trees=hist_trees,
                    ).state,
                    expected,
                )

        # In legacy Codex fallback mode (no Gate 2 review), changing only the
        # commit message keeps historical same-tree Codex findings blocking,
        # while changing the tree or adding an authentic clean Gate 2 review
        # on HEAD passes.
        gh_codex_fallback_same_tree_msg = FakeGitHub(
            [pr_amended], {1: [codex_old_findings, codex_clean_new]},
            reviews={1: []},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(
            reconcile(gh_codex_fallback_same_tree_msg, publish=True)[HEAD].state,
            "failure",
        )
        gh_codex_same_tree_msg = FakeGitHub(
            [pr_amended], {1: [codex_old_findings]},
            reviews={1: [gate2_review(
                review_id=23, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
            )]},
            trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: other_msg},
        )
        self.assertEqual(reconcile(gh_codex_same_tree_msg, publish=True)[HEAD].state, "success")
        gh_codex_changed_tree = FakeGitHub(
            [pr_amended], {1: [codex_old_findings, codex_clean_new]},
            reviews={1: []},
            trees={HEAD: TREE, OTHER_HEAD: OTHER_TREE, BASE: parent_tree},
            parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
            messages={HEAD: msg, OTHER_HEAD: msg},
        )
        self.assertEqual(reconcile(gh_codex_changed_tree, publish=True)[HEAD].state, "success")

        # A historical completed Codex commit that GitHub cannot resolve
        # (404/422) carries no tree claim, so like any other-tree finding it
        # does not block a clean Gate 2 review of the current identity; other
        # read errors (HTTP 500) still fail closed.
        for label, err, expected in (
            ("http_404", "GitHub GET: HTTP 404", "success"),
            ("http_422", "GitHub GET: HTTP 422", "success"),
            ("http_500", "GitHub GET: HTTP 500", "failure"),
        ):
            with self.subTest(codex_unresolvable=label):
                gh_codex_missing = FakeGitHub(
                    [pr_amended], {1: [codex_old_findings]},
                    reviews={1: [gate2_review(
                        review_id=24, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                        identity_key=ik,
                    )]},
                    trees={HEAD: TREE, OTHER_HEAD: RuntimeError(err), BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                if expected == "failure":
                    with self.assertRaises(RuntimeError):
                        reconcile(gh_codex_missing, publish=True)
                    self.assertEqual(gh_codex_missing.writes[-1][1].state, "failure")
                else:
                    self.assertEqual(
                        reconcile(gh_codex_missing, publish=True)[HEAD].state,
                        expected,
                    )

        # Exact-head review with merge_base != base_sha fails closed
        # even when base_changed_at is None and identity_key matches.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(
                    head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                    merge_base=OTHER_BASE, identity_key=ik,
                )],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "failure",
        )

        # Prior clean review with valid-syntax mismatched structured
        # identity_key (or bad merge_base) does not poison a valid clean retry.
        for label, bad_clean_kwargs in (
            ("mismatched_one", {"identity_key": f"one:{other_parent_tree}:{TREE}:{msg_hash}"}),
            ("mismatched_multi", {"identity_key": f"multi:{BASE}:{HEAD}"}),
            ("bad_merge_base", {"identity_key": ik, "merge_base": OTHER_BASE}),
        ):
            bad_clean = gate2_review(
                review_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                submitted_at="2026-11-23T01:00:00Z", **bad_clean_kwargs,
            )
            good_clean = gate2_review(
                review_id=31, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key=ik, submitted_at="2026-11-23T02:00:00Z",
            )
            with self.subTest(bad_clean_no_poison=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[bad_clean, good_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                    ).state,
                    "success",
                )

        # deleted_through stops older comments (<= deleted_through)
        # from approving, skips historical lookups for still-present clean
        # comments <= deleted_through, and keeps live finding comments blocking.
        # The tombstoned comment carries the matching identity_key and its
        # commit raises an unswallowed HTTP 500, so any historical lookup for
        # it fails the PR instead of passing.
        tombstoned_clean_g2 = gate2_comment(
            comment_id=10, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T01:00:00Z",
        )
        fresh_clean_cmt = gate2_comment(
            comment_id=30, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        gh_tombstoned_clean = FakeGitHub(
            [pr_amended],
            {1: [tombstoned_clean_g2, fresh_clean_cmt]},
            deleted={1: 20},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 500"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with patch.object(
            gh_tombstoned_clean, "commit_identity",
            wraps=gh_tombstoned_clean.commit_identity,
        ) as identity_spy:
            self.assertEqual(reconcile(gh_tombstoned_clean, publish=True)[HEAD].state, "success")
            self.assertEqual(
                [call.args for call in identity_spy.call_args_list],
                [(HEAD, BASE)],
            )
        # Control: the same comment above deleted_through is looked up, so the
        # HTTP 500 surfaces and fails closed.
        gh_untombstoned_clean = FakeGitHub(
            [pr_amended],
            {1: [tombstoned_clean_g2, fresh_clean_cmt]},
            deleted={1: 5},
            trees={HEAD: TREE, OTHER_HEAD: RuntimeError("GitHub GET: HTTP 500"), BASE: parent_tree},
            parents={HEAD: [BASE]},
            messages={HEAD: msg},
        )
        with self.assertRaises(RuntimeError):
            reconcile(gh_untombstoned_clean, publish=True)
        self.assertEqual(gh_untombstoned_clean.writes[-1][1].state, "failure")
