# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""The carry-forward probe suite that the single-guard mutation test runs
against `codex_review` and each of its mutants."""

from __future__ import annotations

from .support import (
    _commit_obj,
    _diff_text,
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


class CarryForwardProbeSuite:
    """The probe suite of `CodexReviewPropertyTests`."""

    def _run_carry_forward_probe_suite(self, mod: types.ModuleType) -> None:
        """Exercise all 42 carry-forward guards in-memory (no disk writes)."""
        clean_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T01:00:00Z",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK

        # 1. `patch` / `rebase_only_patch_equivalent` checks:
        patch_old = (
            "@@ -1,3 +1,3 @@\n ctx1\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        patch_ctx = (
            "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n"
            "\\ No newline at end of file\n"
        )
        f_old = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        f_ctx = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_ctx,
            }
        ]
        self.assertTrue(mod.rebase_only_patch_equivalent(f_old, f_ctx))
        f_noeols = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": "@@ -10,3 +10,3 @@\n ctx2\n-old\n+new\n",
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_noeols))
        f_ren = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "a",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_ren))
        f_ren2 = [
            {
                "filename": "anneal/ci/x.py",
                "status": "renamed",
                "previous_filename": "b",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_ren, f_ren2))
        f_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "sha": "8" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_blob))
        f_add = [
            {
                "filename": "anneal/ci/x.py",
                "status": "added",
                "sha": "9" * 40,
                "patch": patch_old,
            }
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_add))
        f_no_blob = [
            {
                "filename": "anneal/ci/x.py",
                "status": "modified",
                "patch": patch_old,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(f_no_blob, f_no_blob)
        )
        try:
            mod._file_change_key(f_no_blob[0], frozenset())
            self.fail("expected ValueError on missing blob sha")
        except ValueError:
            pass
        self.assertFalse(mod.rebase_only_patch_equivalent(f_old, f_old + f_old))
        many_300 = [
            {
                "filename": f"f{i}.py",
                "status": "modified",
                "sha": "9" * 40,
                "patch": patch_old,
            }
            for i in range(300)
        ]
        self.assertFalse(mod.rebase_only_patch_equivalent(many_300, many_300))
        self.assertFalse(mod.rebase_only_patch_equivalent([], []))
        rm_path = "anneal/trusted/root-manifest.sha256"
        rm_patch = "@@ -1 +1 @@\n-a\n+b\n"
        rm_old = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        rm_new = [
            {
                "filename": rm_path,
                "status": "modified",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertTrue(
            mod.rebase_only_patch_equivalent(
                rm_old, rm_new, frozenset({rm_path})
            )
        )
        rm_add = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "2" * 40,
                "patch": rm_patch,
            }
        ]
        rm_add_other = [
            {
                "filename": rm_path,
                "status": "added",
                "sha": "1" * 40,
                "patch": rm_patch,
            }
        ]
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add, rm_new, frozenset({rm_path})
            )
        )
        self.assertFalse(
            mod.rebase_only_patch_equivalent(
                rm_add_other, rm_add, frozenset({rm_path})
            )
        )

        # 2. `base_drift_allows_carry_forward`:
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "identical",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward("ahead", [], {"anneal/ci/x.py"})
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}] * 300,
                {"anneal/ci/x.py"},
            )
        )
        self.assertEqual(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "other.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            ),
            frozenset(),
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "anneal/ci/x.py", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "y.py",
                        "status": "renamed",
                        "previous_filename": "anneal/ci/x.py",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "unrelated.py",
                        "status": "modified",
                        "previous_filename": "",
                    }
                ],
                {"y.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [
                    {
                        "filename": "anneal/docs/codex-review.md",
                        "status": "modified",
                    }
                ],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "AGENTS.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )
        self.assertIsNone(
            mod.base_drift_allows_carry_forward(
                "ahead",
                [{"filename": "skills/foo.md", "status": "modified"}],
                {"anneal/ci/x.py"},
            )
        )

        # 3. `diff_file_modes` & `GitHub.verify_rebase_carry_forward`:
        self.assertIsNone(mod.diff_file_modes(_diff_text() + _diff_text()))

        class StubGH(mod.GitHub):
            def __init__(
                self,
                *,
                same_base_compare=False,
                bad_msg=False,
                bad_tree=False,
                bad_parents=False,
                bad_modes=False,
                extra_mode=False,
                extra_both=False,
                diff_other=False,
            ):
                super().__init__("google/zerocopy", "tok", AUTH_REVIEWERS)
                self.same_base_compare = same_base_compare
                self.bad_msg = bad_msg
                self.bad_tree = bad_tree
                self.bad_parents = bad_parents
                self.bad_modes = bad_modes
                self.extra_mode = extra_mode
                self.extra_both = extra_both
                self.diff_other = diff_other

            def request(self, path, data=None):
                if path == f"commits/{ANCHOR_HEAD}":
                    return _commit_obj(
                        ANCHOR_HEAD,
                        "9" * 40 if self.bad_parents else OLD_BASE,
                        OTHER_TREE if self.bad_tree else TREE,
                    )
                if path == f"commits/{NEW_HEAD}":
                    return _commit_obj(
                        NEW_HEAD,
                        OLD_BASE if self.same_base_compare else NEW_BASE,
                        TREE,
                        message="changed" if self.bad_msg else MSG,
                    )
                if path == f"commits/{'9' * 40}":
                    patch_s = (
                        "@@ -1 +1 @@\n-a\n+c\n"
                        if self.diff_other
                        else "@@ -1 +1 @@\n-a\n+b\n"
                    )
                    return _commit_obj(
                        "9" * 40, OLD_BASE, TREE, patch_text=patch_s
                    )
                if path == f"commits/{OLD_BASE}":
                    return {
                        "sha": OLD_BASE,
                        "commit": {
                            "tree": {"sha": PARENT_TREE},
                            "message": "base",
                        },
                    }
                if path.startswith("compare/"):
                    return {
                        "status": "ahead",
                        "files": [
                            {"filename": "unrelated.txt", "status": "modified"}
                        ],
                    }
                raise AssertionError(path)

            def request_text(self, path, accept):
                if path == f"commits/{ANCHOR_HEAD}":
                    if self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                if path == f"commits/{NEW_HEAD}":
                    if self.bad_modes:
                        return _diff_text(mode="100755")
                    if self.extra_mode or self.extra_both:
                        return _diff_text() + _diff_text("anneal/ci/extra.py")
                    return _diff_text()
                raise AssertionError(path)

        self.assertEqual(
            StubGH().verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            ),
            ANCHOR_IK,
        )
        self.assertEqual(
            StubGH(diff_other=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            ),
            ANCHOR_IK,
        )
        self.assertIsNone(
            StubGH(diff_other=False).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE, ["9" * 40]
            )
        )
        self.assertIsNone(
            StubGH(same_base_compare=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, OLD_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_msg=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_tree=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_parents=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(bad_modes=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_mode=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )
        self.assertIsNone(
            StubGH(extra_both=True).verify_rebase_carry_forward(
                ANCHOR_HEAD, OLD_BASE, TREE, NEW_HEAD, NEW_BASE
            )
        )

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
        # Legacy Codex blocking summary on unrelated head blocks carry-forward
        # (`history_codex_off`):
        bad_codex = summary(
            head="9" * 40,
            status="completed",
            has_any_findings=True,
            has_unresolved_findings=True,
        )
        self.assertNotEqual(
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

        # 5. Isolated direct unit mock for `codex_gate_off`:
        with (
            patch.object(
                mod,
                "review_codex_result",
                side_effect=[
                    mod.Result("failure", "mock codex failure"),
                    mod.Result("pending", "anchor codex clear"),
                ],
            ),
            patch.object(
                mod, "_carry_forward_blocked_by_history", return_value=False
            ),
        ):
            res_codex_off = mod.review_result(
                NEW_HEAD,
                [],
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )
            self.assertNotEqual(res_codex_off.state, "success")

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
