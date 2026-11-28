# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The historical-commit half of the Gate 2 `deleted_through` test."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    HEAD,
    OTHER_BASE,
    OTHER_HEAD,
    reconcile,
    review_result,
    summary,
    TREE,
)


class Gate2HistoricalFailureChecks:
    """Part of `Gate2CrossFamilyTests`."""

    def _check_gate2_historical_failures_and_tombstones(
        self,
        msg,
        parent_tree,
        ik,
        pr_multi,
        changed,
        same_base_hist,
    ):
        """The second half of
        `test_gate2_deleted_through_snapshot_and_same_tree_findings`: failures
        on historical commits, keyless and stale reviews, and failures below
        and above `deleted_through`."""
        # Non-finding failures on a verified historical commit with
        # the current one-commit identity keep blocking a clean verdict that
        # transfers from that identity, with or without a payload identity_key.
        hist_clean = gate2_review(
            review_id=101, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        hist_failures = []
        for keyed in (True, False):
            key_kwargs = {"identity_key": ik} if keyed else {}
            suffix = "keyed" if keyed else "keyless"
            hist_failures.extend((
                (f"changes_requested_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, state="CHANGES_REQUESTED",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "CHANGES_REQUESTED"),
                (f"approved_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, state="APPROVED",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "APPROVE"),
                (f"same_family_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, reviewer_family="claude",
                    author_family="claude",
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "differ"),
                (f"wrong_commit_id_{suffix}", gate2_review(
                    review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                    tree_sha=TREE, commit_id=HEAD,
                    submitted_at="2026-11-23T01:00:00Z", **key_kwargs,
                ), "commit_id"),
            ))
        for label, bad_rev, expected_substr in hist_failures:
            with self.subTest(historical_non_finding_failure=label):
                verdict = review_result(
                    HEAD, [], reviews=[bad_rev, hist_clean],
                    base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                    historical_identities=same_base_hist,
                )
                self.assertEqual(verdict.state, "failure")
                self.assertIn(expected_substr, verdict.reason)
                # Without the historical failure, the clean verdict transfers.
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[hist_clean],
                        base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                        historical_identities=same_base_hist,
                    ).state,
                    "success",
                )

        # A keyless historical failure that is the sole or latest Gate 2 item
        # still blocks (it evaluates as pending when treated as the latest
        # item) and is not masked by a clean legacy Codex summary on HEAD; a
        # sole keyless historical clean review stays pending.
        clean_codex_head = summary(HEAD)
        for label, failing_kwargs, expected_substr in (
            ("changes_requested", {"state": "CHANGES_REQUESTED"},
             "CHANGES_REQUESTED"),
            ("same_family", {"reviewer_family": "claude",
                             "author_family": "claude"}, "differ"),
        ):
            latest_keyless = gate2_review(
                review_id=102, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, submitted_at="2026-11-23T04:00:00Z",
                **failing_kwargs,
            )
            for order_label, revs in (
                ("sole", [latest_keyless]),
                ("latest_after_clean", [hist_clean, latest_keyless]),
            ):
                for codex_label, cmts in (
                    ("no_codex", []),
                    ("clean_codex_head", [clean_codex_head]),
                ):
                    with self.subTest(latest_historical_failure=(
                            label, order_label, codex_label)):
                        verdict = review_result(
                            HEAD, cmts, reviews=revs,
                            base_sha=OTHER_BASE, tree_sha=TREE,
                            identity_key=ik,
                            historical_identities=same_base_hist,
                        )
                        self.assertEqual(verdict.state, "failure")
                        self.assertIn(expected_substr, verdict.reason)
        sole_keyless_clean = gate2_review(
            review_id=103, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T04:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[sole_keyless_clean],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=same_base_hist,
            ).state,
            "pending",
        )

        # Failures on unverified or different identities do not block.
        third_head = "7" * 40
        for label, bad_rev in (
            ("unverified_commit", gate2_review(
                review_id=100, head_sha=third_head, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                submitted_at="2026-11-23T01:00:00Z",
            )),
            ("mismatched_structured_key", gate2_review(
                review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                identity_key=f"multi:{BASE}:{OTHER_HEAD}",
                submitted_at="2026-11-23T01:00:00Z",
            )),
            ("stale_merge_base", gate2_review(
                review_id=100, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED", identity_key=ik,
                merge_base=OTHER_BASE, submitted_at="2026-11-23T01:00:00Z",
            )),
        ):
            with self.subTest(unverified_or_mismatched_failure=label):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[bad_rev, hist_clean],
                        base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                        historical_identities=same_base_hist,
                    ).state,
                    "success",
                )

        # reconcile() verifies a keyless same-tree failure's commit identity
        # even when it sits on a different historical commit than the clean
        # review that transfers.
        third_base = "8" * 40
        keyless_cr_third = gate2_review(
            review_id=100, head_sha=third_head, base_sha=third_base,
            tree_sha=TREE, state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T01:00:00Z",
        )
        recon_trees = {
            HEAD: TREE, OTHER_HEAD: TREE, third_head: TREE,
            BASE: parent_tree, OTHER_BASE: parent_tree, third_base: parent_tree,
        }
        recon_parents = {
            HEAD: [OTHER_BASE], OTHER_HEAD: [BASE], third_head: [third_base],
        }
        recon_messages = {HEAD: msg, OTHER_HEAD: msg, third_head: msg}
        for label, revs, expected in (
            ("clean_only", [hist_clean], "success"),
            ("keyless_failure_elsewhere", [keyless_cr_third, hist_clean], "failure"),
        ):
            with self.subTest(reconcile_historical_failure=label):
                gh_hist_failure = FakeGitHub(
                    [pr_multi], {1: []},
                    reviews={1: revs},
                    trees=recon_trees,
                    parents=recon_parents,
                    messages=recon_messages,
                )
                self.assertEqual(
                    reconcile(gh_hist_failure, publish=True)[HEAD].state,
                    expected,
                )

        # A base change never makes a failing review on the exact
        # identity stop blocking, keyed or keyless; it only stops a stale
        # review from passing.
        fresh_keyed_clean = gate2_review(
            review_id=111, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, stale_kwargs, expected_substr in (
            ("changes_requested", {"state": "CHANGES_REQUESTED"},
             "CHANGES_REQUESTED"),
            ("approved", {"state": "APPROVED"}, "APPROVE"),
            ("same_family", {"reviewer_family": "claude",
                             "author_family": "claude"}, "differ"),
            ("wrong_commit_id", {"commit_id": OTHER_HEAD}, "commit_id"),
        ):
            for keyed in (False, True):
                key_kwargs = {"identity_key": ik} if keyed else {}
                stale_failure = gate2_review(
                    review_id=110, head_sha=HEAD, base_sha=BASE,
                    tree_sha=TREE, submitted_at="2026-11-23T01:00:00Z",
                    **stale_kwargs, **key_kwargs,
                )
                with self.subTest(failure_predating_base_change=(label, keyed)):
                    verdict = review_result(
                        HEAD, [], reviews=[stale_failure, fresh_keyed_clean],
                        base_sha=BASE, tree_sha=TREE, identity_key=ik,
                        base_changed_at=changed,
                    )
                    self.assertEqual(verdict.state, "failure")
                    self.assertIn(expected_substr, verdict.reason)
        stale_keyless_clean = gate2_review(
            review_id=112, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_keyless_clean],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                base_changed_at=changed,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[stale_keyless_clean, fresh_keyed_clean],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                base_changed_at=changed,
            ).state,
            "success",
        )

        # reconcile() fails closed when a blocking same-tree
        # non-finding failure sits on a historical commit GitHub cannot
        # resolve (404/422), even next to a clean review on HEAD, while an
        # unresolvable clean review or a stale-merge_base failure only
        # loses reuse.
        pr_head_base = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
        clean_on_head = gate2_review(
            review_id=121, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, submitted_at="2026-11-23T03:00:00Z",
        )
        for label, hist_rev, err, expected in (
            ("keyless_cr_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED",
                submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "failure"),
            ("keyed_same_family_422", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, identity_key=ik, reviewer_family="claude",
                author_family="claude", submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 422", "failure"),
            ("keyed_clean_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, identity_key=ik,
                submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "success"),
            ("stale_merge_base_cr_404", gate2_review(
                review_id=120, head_sha=OTHER_HEAD, base_sha=BASE,
                tree_sha=TREE, state="CHANGES_REQUESTED", identity_key=ik,
                merge_base=OTHER_BASE, submitted_at="2026-11-23T01:00:00Z",
            ), "GitHub GET: HTTP 404", "success"),
        ):
            with self.subTest(unresolvable_historical_failure=label):
                gh_unverifiable = FakeGitHub(
                    [pr_head_base], {1: []},
                    reviews={1: [hist_rev, clean_on_head]},
                    trees={HEAD: TREE, OTHER_HEAD: RuntimeError(err), BASE: parent_tree},
                    parents={HEAD: [BASE]},
                    messages={HEAD: msg},
                )
                if expected == "failure":
                    with self.assertRaises(RuntimeError):
                        reconcile(gh_unverifiable, publish=True)
                    self.assertEqual(gh_unverifiable.writes[-1][1].state, "failure")
                else:
                    self.assertEqual(
                        reconcile(gh_unverifiable, publish=True)[HEAD].state,
                        expected,
                    )

        # A non-finding failure in an issue comment with id <= deleted_through
        # no longer blocks a later clean review above the tombstone, while the
        # same comment above deleted_through still blocks.
        same_family_cmt = gate2_comment(
            comment_id=130, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            reviewer_family="claude", author_family="claude",
            created_at="2026-11-23T01:00:00Z",
        )
        clean_cmt_above = gate2_comment(
            comment_id=140, head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
            identity_key=ik, created_at="2026-11-23T03:00:00Z",
        )
        for label, deleted, expected in (
            ("tombstoned", 135, "success"),
            ("live", 0, "failure"),
        ):
            with self.subTest(non_finding_comment=label):
                self.assertEqual(
                    review_result(
                        HEAD, [same_family_cmt, clean_cmt_above],
                        deleted_through=deleted, base_sha=BASE, tree_sha=TREE,
                        identity_key=ik,
                    ).state,
                    expected,
                )
