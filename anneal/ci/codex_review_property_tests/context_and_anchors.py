# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Concurrent context mutation fuzzing and anchor pinning properties."""

from __future__ import annotations

from .support import (
    ANCHOR_HEAD,
    ANCHOR_IK,
    AUTH_REVIEWERS,
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    HEAD,
    MSG,
    MSG_HASH,
    NEW_BASE,
    NEW_HEAD,
    OLD_BASE,
    OTHER_BASE,
    OTHER_HEAD,
    PARENT_TREE,
    patch,
    pull,
    random,
    reconcile,
    review_result,
    summary,
    TREE,
)


class ContextAndAnchorPropertyCases:
    """Context-mutation and anchor tests of `CodexReviewPropertyTests`."""

    def test_concurrent_context_mutation_fuzzing_never_publishes_success(
        self,
    ) -> None:
        rng = random.Random(20261125 + 4)
        mut_kinds = [
            "head_changed",
            "base_changed",
            "pr_closed",
            "deleted_jumped",
            "queue_changed",
            "base_ts_changed",
            "comment_findings_added",
            "review_findings_added",
        ]

        # Cover all 8 classes multiple times with randomized PR numbers,
        # timestamps, comment/review IDs, and benign noise items, plus an
        # unmutated control trial proving the baseline publishes `success`.
        for trial in range(160):
            pr_num = rng.randint(1, 50)
            mut_kind = mut_kinds[trial % len(mut_kinds)]
            base_pull = pull(pr_num, HEAD, "main")
            rev_id = rng.randint(10, 80)
            later_id = rev_id + rng.randint(5, 40)
            ts1 = f"2026-11-23T0{rng.randint(0, 9)}:10:00Z"
            ts2 = f"2026-11-24T0{rng.randint(0, 9)}:20:00Z"
            clean_rev = gate2_review(
                review_id=rev_id,
                head_sha=HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                identity_key=ANCHOR_IK,
                submitted_at=ts1,
            )
            noise_comments = (
                [
                    summary(
                        head=HEAD,
                        created_at=ts1,
                        completed_at=ts1,
                        status="completed",
                        has_any_findings=False,
                        has_unresolved_findings=False,
                    )
                ]
                if rng.random() < 0.5
                else []
            )
            initial = [base_pull]
            final = [base_pull]
            deleted = {pr_num: 0}
            queues = {}
            bases = {pr_num: None}
            comments = {pr_num: list(noise_comments)}
            changed_comments = {}
            reviews = {pr_num: [clean_rev]}
            changed_reviews = {}

            # Periodically verify unmutated baseline on this PR topology.
            if trial % len(mut_kinds) == 0:
                ctrl_gh = FakeGitHub(
                    initial,
                    comments,
                    final=final,
                    deleted=deleted,
                    queues=queues,
                    bases=bases,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
                with patch("sys.stdout"):
                    ctrl_res = reconcile(ctrl_gh, publish=True)
                self.assertEqual(ctrl_res[HEAD].state, "success")
                self.assertTrue(
                    any(res.state == "success" for _, res in ctrl_gh.writes)
                )

            if mut_kind == "head_changed":
                final = [pull(pr_num, OTHER_HEAD, "main")]
            elif mut_kind == "base_changed":
                final = [
                    {
                        "number": pr_num,
                        "head": {"sha": HEAD},
                        "base": {"ref": "main", "sha": OTHER_BASE},
                        "draft": False,
                    }
                ]
            elif mut_kind == "pr_closed":
                final = []
            elif mut_kind == "deleted_jumped":
                deleted_calls = [0]
                jump_to = rng.randint(25, 200)

                class MutFakeGitHub(FakeGitHub):
                    def deleted_summaries(self):
                        val = 0 if deleted_calls[0] == 0 else jump_to
                        deleted_calls[0] += 1
                        return {pr_num: val}

                gh = MutFakeGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "queue_changed":
                q_calls = [0]

                class MutQueueGitHub(FakeGitHub):
                    def queue_groups(self):
                        val = (
                            {}
                            if q_calls[0] == 0
                            else {"9" * 40: {pr_num: HEAD}}
                        )
                        q_calls[0] += 1
                        return val

                gh = MutQueueGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "base_ts_changed":
                b_calls = [0]

                class MutBaseGitHub(FakeGitHub):
                    def base_changes(self):
                        val = (
                            {pr_num: None} if b_calls[0] == 0 else {pr_num: ts2}
                        )
                        b_calls[0] += 1
                        return val

                gh = MutBaseGitHub(
                    initial,
                    comments,
                    reviews=reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE]},
                    messages={HEAD: MSG},
                )
            elif mut_kind == "comment_findings_added":
                changed_comments = {
                    pr_num: noise_comments
                    + [
                        gate2_comment(
                            comment_id=later_id,
                            head_sha=HEAD,
                            base_sha=BASE,
                            tree_sha=TREE,
                            verdict="findings",
                            findings=[
                                {
                                    "severity": "P1",
                                    "path": "x.rs",
                                    "line": 1,
                                    "summary": "bad",
                                }
                            ],
                            created_at=ts2,
                        )
                    ]
                }
            elif mut_kind == "review_findings_added":
                changed_reviews = {
                    pr_num: [
                        clean_rev,
                        gate2_review(
                            review_id=later_id,
                            head_sha=HEAD,
                            base_sha=BASE,
                            tree_sha=TREE,
                            verdict="findings",
                            findings=[
                                {
                                    "severity": "P1",
                                    "path": "x.rs",
                                    "line": 1,
                                    "summary": "bad",
                                }
                            ],
                            submitted_at=ts2,
                        ),
                    ]
                }

            if mut_kind not in (
                "deleted_jumped",
                "queue_changed",
                "base_ts_changed",
            ):
                gh = FakeGitHub(
                    initial,
                    comments,
                    final=final,
                    changed_comments=changed_comments,
                    deleted=deleted,
                    queues=queues,
                    bases=bases,
                    reviews=reviews,
                    changed_reviews=changed_reviews,
                    authorized_reviewers=AUTH_REVIEWERS,
                    trees={HEAD: TREE, OTHER_HEAD: TREE, BASE: PARENT_TREE},
                    parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                    messages={HEAD: MSG, OTHER_HEAD: MSG},
                )

            with patch("sys.stdout"):
                try:
                    reconcile(gh, publish=True)
                except RuntimeError:
                    pass
            self.assertFalse(
                any(res.state == "success" for _, res in gh.writes),
                f"trial={trial} mut_kind={mut_kind} published: {gh.writes}",
            )

    def test_keyless_legacy_and_structured_anchor_pin(self) -> None:
        # Per docs/codex-review.md:102-103 and 114-149:
        # - Non-structured legacy keys never transfer via historical_identities.
        # - Under GitHub-verified rebase carry-forward, a clean keyless or
        #   exact-anchor legacy review carries forward only with `verifier`,
        #   never without it.
        # - A contradicting structured key (`multi:` or wrong `one:`) never
        #   carries forward, even with `verifier`.
        keyless_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        legacy_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key="custom:legacy-v1-key",
            submitted_at="2026-11-23T01:00:00Z",
        )
        multi_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"multi:{OLD_BASE}:{ANCHOR_HEAD}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        wrong_one_keyed = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"one:{'2' * 40}:{TREE}:{MSG_HASH}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK

        hist = {(ANCHOR_HEAD, OLD_BASE): (TREE, ANCHOR_IK)}
        no_hist_transfer = review_result(
            NEW_HEAD,
            [],
            reviews=[legacy_keyed],
            base_sha=NEW_BASE,
            tree_sha=TREE,
            authorized_reviewers=AUTH_REVIEWERS,
            identity_key=ANCHOR_IK,
            historical_identities=hist,
        )
        self.assertEqual(no_hist_transfer.state, "pending", no_hist_transfer)

        for label, rev in (
            ("keyless", keyless_anchor),
            ("legacy", legacy_keyed),
        ):
            with self.subTest(carry_allowed=label):
                carried = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                    carry_forward_verifier=verifier,
                )
                self.assertEqual(carried.state, "success", carried)
                self.assertIn("carried forward", carried.reason)
                unverified = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                )
                self.assertEqual(unverified.state, "pending", unverified)

        for label, rev in (
            ("multi", multi_keyed),
            ("wrong_one", wrong_one_keyed),
        ):
            with self.subTest(carry_blocked=label):
                blocked = review_result(
                    NEW_HEAD,
                    [],
                    reviews=[rev],
                    base_sha=NEW_BASE,
                    tree_sha=TREE,
                    authorized_reviewers=AUTH_REVIEWERS,
                    identity_key=ANCHOR_IK,
                    carry_forward_verifier=verifier,
                )
                self.assertNotEqual(blocked.state, "success", blocked)
