# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Sections 4-6 of the carry-forward probe suite: carry-forward results
against review history, direct Gate 2 versus legacy Codex precedence, and
`reconcile` wiring."""

from __future__ import annotations

from collections.abc import Callable

from .support import (
    ANCHOR_HEAD,
    ANCHOR_IK,
    AUTH_REVIEWERS,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    MSG,
    MSG_HASH,
    NEW_BASE,
    NEW_HEAD,
    OLD_BASE,
    OTHER_BASE,
    OTHER_TREE,
    PARENT_TREE,
    patch,
    summary,
    TREE,
    types,
)


class HistoryPrecedenceAndReconcileProbes:
    """Sections 4-6 of `CarryForwardProbeSuite`."""

    def _probe_history_precedence_and_reconcile(
        self,
        mod: types.ModuleType,
        clean_anchor: dict[str, object],
        verifier: Callable[..., str],
    ) -> None:
        # 4. `_carry_forward_result`, `_carry_forward_blocked_by_history`,
        # and `review_result`:
        # Same head/base rejected:
        self.assertNotEqual(
            mod.review_result(
                ANCHOR_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Multi / invalid identity_key rejected:
        keyless_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=f"multi:{NEW_BASE}:{NEW_HEAD}",
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[keyless_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=lambda *_: "custom:bad",
            ).state,
            "success",
        )
        # Anchor eval must check anchor_ik (contradictory anchor_ik fails):
        wrong_ik_rev = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=f"one:{'2' * 40}:{TREE}:{MSG_HASH}",
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[wrong_ik_rev],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Anchor eval failure (`CHANGES_REQUESTED` on anchor) fails:
        cr_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[cr_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # History findings on another head with the anchor's tree block:
        other_head_same_tree_finding = gate2_comment(
            comment_id=10,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T00:10:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [other_head_same_tree_finding],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted `OTHER_TREE` findings on anchor head still block
        # (`history_findings_off`):
        anchor_diff_tree_finding = gate2_comment(
            comment_id=11,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T00:11:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [anchor_diff_tree_finding],
                deleted_through=11,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # History non-finding failure on anchor head (`OTHER_BASE`) blocks:
        cr_earlier = gate2_review(
            review_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T00:30:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [],
                reviews=[cr_earlier, clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted earlier non-finding comment does NOT block carry-forward
        # (`deleted_through=15`):
        cmt_cr_earlier = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            reviewer_family="claude",
            author_family="claude",
            created_at="2026-11-23T00:30:00Z",
        )
        self.assertEqual(
            mod.review_result(
                NEW_HEAD,
                [cmt_cr_earlier],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Deleted latest clean comment (`id=30 <= deleted_through=30`) MUST NOT
        # carry forward or fall back to older clean `id=20`
        # (`latest_excludes_tombstoned` & `earliest_anchor` &
        # `latest_tomb_check_off`):
        cmt_clean_latest = gate2_comment(
            comment_id=30,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            created_at="2026-11-23T02:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [cmt_clean_latest],
                deleted_through=30,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Earliest clean + later findings (`earliest_anchor`):
        finding_latest = gate2_comment(
            comment_id=30,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a",
                    "line": 1,
                    "summary": "f",
                }
            ],
            created_at="2026-11-23T02:00:00Z",
        )
        self.assertNotEqual(
            mod.review_result(
                NEW_HEAD,
                [finding_latest],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        # Legacy Codex blocking summary does NOT poison carry-forward when
        # authentic cross-family Gate 2 history exists
        # (`history_gate2_decouple_off`), while still blocking
        # `_carry_forward_blocked_by_history` when zero valid cross-family
        # Gate 2 items exist (`history_codex_off` and
        # `history_gate2_auth_off`):
        bad_codex = summary(
            head="9" * 40,
            status="completed",
            has_any_findings=True,
            has_unresolved_findings=True,
        )
        self.assertEqual(
            mod.review_result(
                NEW_HEAD,
                [bad_codex],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "success",
        )
        self.assertTrue(
            mod._carry_forward_blocked_by_history(
                [bad_codex], [], AUTH_REVIEWERS, ANCHOR_HEAD, TREE
            )
        )
        same_fam_other = gate2_review(
            review_id=29,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            reviewer_family="claude",
            author_family="claude",
            submitted_at="2026-11-23T00:30:00Z",
        )
        self.assertTrue(
            mod._carry_forward_blocked_by_history(
                [bad_codex], [same_fam_other], AUTH_REVIEWERS, ANCHOR_HEAD, TREE
            )
        )
        dismissed_other = gate2_review(
            review_id=28,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            state="DISMISSED",
            submitted_at="2026-11-23T00:30:00Z",
        )
        self.assertTrue(
            mod._carry_forward_blocked_by_history(
                [bad_codex], [dismissed_other], AUTH_REVIEWERS,
                ANCHOR_HEAD, TREE,
            )
        )
        multi_inc_same_fam = gate2_review(
            review_id=27,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            reviewer_family="multi",
            author_family="claude",
            verdict="incomplete",
            findings=[],
            panel_seats=[
                {
                    "seat": "s1",
                    "family": "claude",
                    "status": "completed",
                    "verdict": "incomplete",
                }
            ],
            submitted_at="2026-11-23T00:30:00Z",
        )
        self.assertTrue(
            mod._carry_forward_blocked_by_history(
                [bad_codex], [multi_inc_same_fam], AUTH_REVIEWERS,
                ANCHOR_HEAD, TREE,
            )
        )
        tombstoned_other_cmt = gate2_comment(
            comment_id=26,
            head_sha="9" * 40,
            base_sha=OLD_BASE,
            tree_sha=OTHER_TREE,
            created_at="2026-11-23T00:30:00Z",
        )
        self.assertTrue(
            mod._carry_forward_blocked_by_history(
                [bad_codex, tombstoned_other_cmt], [], AUTH_REVIEWERS,
                ANCHOR_HEAD, TREE, deleted_through=26,
            )
        )

        # 5. Direct Gate 2 vs. legacy Codex precedence (`gate2_precedence_off`,
        # `gate2_failure_precedence_off`, and
        # `pending_gate2_masks_codex_failure`):
        bad_codex_anchor = summary(
            head=ANCHOR_HEAD,
            status="completed",
            has_any_findings=True,
            has_unresolved_findings=True,
        )
        self.assertEqual(
            mod.review_result(
                ANCHOR_HEAD,
                [bad_codex_anchor],
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "success",
        )
        incomplete_anchor = gate2_review(
            review_id=25,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="incomplete",
            findings=[],
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            mod.review_result(
                ANCHOR_HEAD,
                [bad_codex_anchor],
                reviews=[incomplete_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        malformed_anchor = {
            **clean_anchor,
            "body": "<!-- anneal-gate2-review:v1 [] -->",
        }
        self.assertEqual(
            mod.review_result(
                ANCHOR_HEAD,
                [summary(head=ANCHOR_HEAD)],
                reviews=[malformed_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )

        # 6. `reconcile` wiring (`reconcile_unwired`):
        class ReconcileCarryGH(FakeGitHub):
            def verify_rebase_carry_forward(
                self, o_head, o_base, o_tree, n_head, n_base, other_heads=()
            ):
                return ANCHOR_IK

        gh_rec = ReconcileCarryGH(
            [
                {
                    "number": 1,
                    "head": {"sha": NEW_HEAD},
                    "base": {"ref": "main", "sha": NEW_BASE},
                    "draft": False,
                }
            ],
            {1: []},
            reviews={1: [clean_anchor]},
            authorized_reviewers=AUTH_REVIEWERS,
            trees={NEW_HEAD: TREE, OLD_BASE: PARENT_TREE, NEW_BASE: "2" * 40},
            parents={NEW_HEAD: [NEW_BASE]},
            messages={NEW_HEAD: MSG},
        )
        with patch("sys.stdout"):
            res_rec = mod.reconcile(gh_rec, publish=False)
        self.assertEqual(res_rec[NEW_HEAD].state, "success")
