# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Gate 2 cross-family tests for one-commit identity keys and their
`reconcile` and transport handling."""

from .support import (
    BASE,
    FakeGitHub,
    gate2_comment,
    gate2_review,
    GitHub,
    hashlib,
    HEAD,
    io,
    OTHER_BASE,
    OTHER_HEAD,
    OTHER_TREE,
    parse_gate2_payload,
    patch,
    reconcile,
    review_result,
    TREE,
)


class Gate2IdentityKeyTests:
    """Part of `Gate2CrossFamilyTests`."""

    def test_one_commit_identity_key_reuse_and_fail_closed_invalidation(self):
        parent_tree = "1" * 40
        other_parent_tree = "2" * 40
        msg = "Subject\n\nBody text."
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        other_msg_hash = hashlib.sha256(b"Changed subject").hexdigest()
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"
        verified_hist = {(OTHER_HEAD, BASE): (TREE, ik)}

        # Clean review on OLD_HEAD/BASE transfers to rebased HEAD/OTHER_BASE
        # when historical head/base identity is verified to match current ik.
        old_clean_rev = gate2_review(
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            parent_tree=parent_tree,
            commit_msg_sha256=msg_hash,
            identity_key=ik,
            submitted_at="2026-11-23T01:00:00Z",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                base_changed_at="2026-11-23T02:00:00Z",
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )
        old_clean_cmt = gate2_comment(
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            parent_tree=parent_tree,
            commit_msg_sha256=msg_hash,
            identity_key=ik,
        )
        self.assertEqual(
            review_result(
                HEAD, [old_clean_cmt],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )

        # Cross-head reuse fails closed without verified historical head/base
        # identity, or if historical commit actually had a different identity.
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities={
                    (OTHER_HEAD, BASE): (TREE, f"one:{parent_tree}:{TREE}:{other_msg_hash}"),
                },
            ).state,
            "pending",
        )

        # Any change to tree, commit message, parent_tree, or multi-commit
        # shape fails closed to pending (never reuses prior review).
        for changed_ik in (
            f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}",
            f"one:{parent_tree}:{TREE}:{other_msg_hash}",
            f"one:{other_parent_tree}:{TREE}:{msg_hash}",
            f"multi:{OTHER_BASE}:{HEAD}",
            None,
        ):
            target_tree = OTHER_TREE if changed_ik == f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}" else TREE
            with self.subTest(changed_ik=changed_ik):
                self.assertEqual(
                    review_result(
                        HEAD, [], reviews=[old_clean_rev],
                        base_sha=OTHER_BASE, tree_sha=target_tree,
                        identity_key=changed_ik,
                        historical_identities=verified_hist,
                    ).state,
                    "pending",
                )

        # Legacy or custom v1 identity_key values remain valid on exact
        # head/base/tree, but never transfer across heads.
        legacy_rev = gate2_review(identity_key="custom:legacy-v1-key")
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[legacy_rev],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
            ).state,
            "success",
        )
        legacy_old = gate2_review(
            head_sha=OTHER_HEAD, base_sha=BASE,
            identity_key="custom:legacy-v1-key",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[legacy_old],
                base_sha=BASE, tree_sha=TREE, identity_key=ik,
                historical_identities={(OTHER_HEAD, BASE): (TREE, ik)},
            ).state,
            "pending",
        )

        # Malformed structured or self-contradictory identity_key fields fail
        # closed.
        bad_ik_reviews = [
            gate2_review(identity_key=" "),
            gate2_review(identity_key="one:not-a-valid-key"),
            gate2_review(identity_key=" one:bad"),
            gate2_review(identity_key="multi:bad"),
            gate2_review(identity_key=f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}"),
            gate2_review(
                parent_tree=other_parent_tree,
                identity_key=ik,
            ),
            gate2_review(
                commit_msg_sha256=other_msg_hash,
                identity_key=ik,
            ),
            gate2_review(identity_key=f"multi:{OTHER_BASE}:{HEAD}"),
            gate2_review(identity_key=f"multi:{BASE}:{OTHER_HEAD}"),
        ]
        for bad_rev in bad_ik_reviews:
            for caller_ik in (ik, None):
                with self.subTest(bad_ik=bad_rev["body"], caller_ik=caller_ik):
                    self.assertEqual(
                        review_result(
                            HEAD, [], reviews=[bad_rev],
                            base_sha=BASE, tree_sha=TREE, identity_key=caller_ik,
                        ).state,
                        "failure",
                    )
        # parse_gate2_payload's own consistency checks reject these, with no
        # caller identity_key to mask a disabled check.
        for bad_rev, expected_msg in (
            (bad_ik_reviews[4], "identity_key tree_sha mismatch"),
            (bad_ik_reviews[5], "identity_key parent_tree mismatch"),
            (bad_ik_reviews[6], "identity_key commit_msg_sha256 mismatch"),
            (bad_ik_reviews[7], "identity_key base/head mismatch"),
            (bad_ik_reviews[8], "identity_key base/head mismatch"),
        ):
            with self.subTest(parser_only=bad_rev["body"]):
                with self.assertRaisesRegex(ValueError, expected_msg):
                    parse_gate2_payload(bad_rev["body"])
        # Contradictory identity_key on exact head/base fails closed.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(identity_key=ik)],
                base_sha=BASE, tree_sha=TREE,
                identity_key=f"one:{other_parent_tree}:{TREE}:{msg_hash}",
            ).state,
            "failure",
        )
        # Base retarget without rebase (unchanged head, changed base_sha) stays
        # pending rather than failing on identity_key mismatch.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(identity_key=f"multi:{BASE}:{HEAD}")],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=f"multi:{OTHER_BASE}:{HEAD}",
            ).state,
            "pending",
        )
        # Payload claiming one: identity_key with stale merge_base != base_sha
        # cannot match across rebases.
        self.assertEqual(
            review_result(
                HEAD, [],
                reviews=[gate2_review(
                    head_sha=OTHER_HEAD,
                    base_sha=BASE,
                    merge_base=OTHER_BASE,
                    identity_key=ik,
                )],
                base_sha=OTHER_BASE, tree_sha=TREE,
                identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "pending",
        )

        # Anti-downgrade: findings on OLD_HEAD block NEW_HEAD with the same
        # identity_key, even if a clean review is posted on NEW_HEAD.
        finding = {"severity": "P1", "summary": "Soundness defect"}
        old_findings = gate2_review(
            review_id=10,
            head_sha=OTHER_HEAD,
            base_sha=BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T01:00:00Z",
            verdict="findings",
            findings=[finding],
        )
        new_clean = gate2_review(
            review_id=11,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T02:00:00Z",
            verdict="clean",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings, new_clean],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "failure",
        )
        # Once the tree changes (new identity_key), a clean review passes.
        new_ik = f"one:{parent_tree}:{OTHER_TREE}:{msg_hash}"
        fixed_clean = gate2_review(
            review_id=12,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=OTHER_TREE,
            identity_key=new_ik,
            submitted_at="2026-11-23T03:00:00Z",
            verdict="clean",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_findings, fixed_clean],
                base_sha=OTHER_BASE, tree_sha=OTHER_TREE, identity_key=new_ik,
                historical_identities=verified_hist,
            ).state,
            "success",
        )
        # Incomplete review on NEW_HEAD supersedes clean review on OLD_HEAD.
        new_incomplete = gate2_review(
            review_id=13,
            head_sha=HEAD,
            base_sha=OTHER_BASE,
            tree_sha=TREE,
            identity_key=ik,
            submitted_at="2026-11-23T02:30:00Z",
            verdict="incomplete",
            findings=[],
        )
        self.assertEqual(
            review_result(
                HEAD, [], reviews=[old_clean_rev, new_incomplete],
                base_sha=OTHER_BASE, tree_sha=TREE, identity_key=ik,
                historical_identities=verified_hist,
            ).state,
            "pending",
        )

    def test_reconcile_and_transport_identity_key(self):
        parent_tree = "1" * 40
        other_parent_tree = "2" * 40
        msg = "[anneal] Clean single commit"
        msg_trailing_nl = "[anneal] Clean single commit\n"
        msg_hash = hashlib.sha256(msg.encode("utf-8")).hexdigest()
        msg_nl_hash = hashlib.sha256(msg_trailing_nl.encode("utf-8")).hexdigest()
        ik = f"one:{parent_tree}:{TREE}:{msg_hash}"

        with patch("sys.stdout", new=io.StringIO()):
            # End-to-end reconcile reuses a clean review on OTHER_HEAD after a
            # squash-rebase onto OTHER_BASE only when OTHER_HEAD/BASE also
            # resolves to the same 1-commit identity on GitHub.
            pr1 = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": OTHER_BASE}, "draft": False}
            old_clean = gate2_review(
                head_sha=OTHER_HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                parent_tree=parent_tree,
                commit_msg_sha256=msg_hash,
                identity_key=ik,
                submitted_at="2026-11-23T01:00:00Z",
            )
            github = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                bases={1: "2026-11-23T02:00:00Z"},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts = reconcile(github, publish=True)
            self.assertEqual(verdicts[HEAD].state, "success")

            # Spoofed/miscomputed identity_key on historical OTHER_HEAD must not
            # transfer when GitHub shows OTHER_HEAD actually had a different
            # message or parent.
            github_mismatch = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                bases={1: "2026-11-23T02:00:00Z"},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg_trailing_nl},
            )
            verdicts_mismatch = reconcile(github_mismatch, publish=True)
            self.assertEqual(verdicts_mismatch[HEAD].state, "pending")

            # Missing (404) historical commit denies cross-head reuse on clean
            # review without hiding a fresher review on HEAD, while failing
            # closed if an unverified 404/500 blocks a historical findings item.
            github_404 = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            verdicts_404 = reconcile(github_404, publish=True)
            self.assertEqual(verdicts_404[HEAD].state, "pending")

            # A 404 on PR #1's historical item must not poison PR #2 when PR #2
            # uses that same (head, base) as its live head (no TypeError).
            pr2_same_missing = {
                "number": 2, "head": {"sha": OTHER_HEAD},
                "base": {"ref": "main", "sha": BASE}, "draft": False,
            }
            pr2_rev = gate2_review(
                review_id=19, head_sha=OTHER_HEAD, base_sha=BASE, tree_sha=TREE,
            )
            github_shared_404 = FakeGitHub(
                [pr1, pr2_same_missing],
                {1: [], 2: []},
                reviews={1: [old_clean], 2: [pr2_rev]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            with self.assertRaises(RuntimeError):
                reconcile(github_shared_404, publish=True)
            written_shared = dict(github_shared_404.writes)
            self.assertEqual(written_shared[HEAD].state, "pending")
            self.assertEqual(written_shared[OTHER_HEAD].state, "failure")

            old_findings_404 = gate2_review(
                review_id=20,
                head_sha=OTHER_HEAD,
                base_sha=BASE,
                tree_sha=TREE,
                parent_tree=parent_tree,
                commit_msg_sha256=msg_hash,
                identity_key=ik,
                verdict="findings",
                findings=[{"severity": "P1", "summary": "Bug"}],
            )
            github_findings_404 = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_findings_404]},
                trees={
                    HEAD: TREE,
                    OTHER_HEAD: RuntimeError("GitHub GET: HTTP 404"),
                    OTHER_BASE: parent_tree,
                },
                parents={HEAD: [OTHER_BASE]},
                messages={HEAD: msg},
            )
            with self.assertRaises(RuntimeError):
                reconcile(github_findings_404, publish=True)
            self.assertEqual(github_findings_404.writes[-1][1].state, "failure")

            # Legacy v1 identity_key remains accepted on exact head/base/tree.
            pr_legacy = {"number": 1, "head": {"sha": HEAD}, "base": {"ref": "main", "sha": BASE}, "draft": False}
            legacy_clean = gate2_review(
                head_sha=HEAD, base_sha=BASE, tree_sha=TREE,
                identity_key="legacy-v1-key",
            )
            github_legacy = FakeGitHub(
                [pr_legacy],
                {1: []},
                reviews={1: [legacy_clean]},
                trees={HEAD: TREE, BASE: parent_tree},
                parents={HEAD: [BASE]},
                messages={HEAD: msg},
            )
            self.assertEqual(reconcile(github_legacy, publish=True)[HEAD].state, "success")

            # Rebase onto a base commit with a different parent tree waits.
            github_changed_base = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: other_parent_tree, BASE: parent_tree},
                parents={HEAD: [OTHER_BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts_changed = reconcile(github_changed_base, publish=True)
            self.assertEqual(verdicts_changed[HEAD].state, "pending")

            # Multi-commit PR (parent != base) stays pending with same tree.
            github_multi = FakeGitHub(
                [pr1],
                {1: []},
                reviews={1: [old_clean]},
                trees={HEAD: TREE, OTHER_HEAD: TREE, OTHER_BASE: parent_tree, BASE: parent_tree},
                parents={HEAD: [BASE], OTHER_HEAD: [BASE]},
                messages={HEAD: msg, OTHER_HEAD: msg},
            )
            verdicts_multi = reconcile(github_multi, publish=True)
            self.assertEqual(verdicts_multi[HEAD].state, "pending")

        # Transport: GitHub.commit_info and GitHub.commit_identity hash the
        # UTF-8 bytes of GitHub REST's `commit.message` verbatim (GitHub's
        # commits API omits the raw commit object's trailing newlines, so
        # local producers must hash that same canonical message).
        gh = GitHub("google/zerocopy", "not-a-real-token")
        head_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": BASE}],
        }
        head_nl_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg_trailing_nl},
            "parents": [{"sha": BASE}],
        }
        base_resp = {"sha": BASE, "commit": {"tree": {"sha": parent_tree}}}
        with patch.object(gh, "request", side_effect=[head_resp, base_resp]):
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, ik))
        with patch.object(gh, "request", side_effect=[head_nl_resp, base_resp]):
            self.assertEqual(
                gh.commit_identity(HEAD, BASE),
                (TREE, f"one:{parent_tree}:{TREE}:{msg_nl_hash}"),
            )
        self.assertNotEqual(msg_hash, msg_nl_hash)
        merge_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": BASE}, {"sha": OTHER_HEAD}],
        }
        with patch.object(gh, "request", return_value=merge_resp):
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, f"multi:{BASE}:{HEAD}"))
        # A single parent other than base_sha (a multi-commit PR) is never a
        # one-commit identity, and GitHub is not asked for that parent's tree.
        other_parent_resp = {
            "sha": HEAD,
            "commit": {"tree": {"sha": TREE}, "message": msg},
            "parents": [{"sha": OTHER_BASE}],
        }
        with patch.object(gh, "request", side_effect=[other_parent_resp]) as req:
            self.assertEqual(gh.commit_identity(HEAD, BASE), (TREE, f"multi:{BASE}:{HEAD}"))
            self.assertEqual(req.call_count, 1)
        # Malformed parent SHAs and non-string messages fail closed.
        for bad_commit_payload in (
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg},
             "parents": [{"sha": "not-a-sha"}]},
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg},
             "parents": ["bad"]},
            {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": None},
             "parents": [{"sha": BASE}]},
        ):
            with self.subTest(bad_commit_payload=bad_commit_payload):
                with patch.object(gh, "request", return_value=bad_commit_payload):
                    with self.assertRaises(RuntimeError):
                        gh.commit_info(HEAD)
        with self.assertRaises(ValueError):
            gh.commit_identity(HEAD, "bad-base")
        bad_commit = {"sha": HEAD, "commit": {"tree": {"sha": TREE}, "message": msg}, "parents": "bad"}
        with patch.object(gh, "request", return_value=bad_commit):
            with self.assertRaises(RuntimeError):
                gh.commit_info(HEAD)
        for bad_payload in (
            {"sha": HEAD, "commit": "bad"},
            {"sha": HEAD, "commit": {"tree": "bad"}},
        ):
            with self.subTest(bad_payload=bad_payload):
                with patch.object(gh, "request", return_value=bad_payload):
                    with self.assertRaises(RuntimeError):
                        gh.commit_info(HEAD)
