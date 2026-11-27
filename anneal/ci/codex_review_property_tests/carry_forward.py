# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Carry-forward safety fuzzing, tombstoned-comment, and single-guard
mutation properties."""

from __future__ import annotations

from .support import (
    _compile_mutant,
    _oracle_has_active_blocker_for_head,
    ANCHOR_HEAD,
    ANCHOR_IK,
    AUTH_REVIEWERS,
    CF_MUTANTS,
    codex_review,
    gate2_comment,
    gate2_review,
    MSG_HASH,
    NEW_BASE,
    NEW_HEAD,
    OLD_BASE,
    OTHER_TREE,
    Path,
    random,
    review_result,
    summary,
    sys,
    TREE,
)


class CarryForwardPropertyCases:
    """Carry-forward tests of `CodexReviewPropertyTests`."""

    def test_carry_forward_safety_and_deletion_monotonicity_fuzzer(
        self,
    ) -> None:
        rng = random.Random(20261125)
        unrelated_head = "9" * 40
        alt_ik = f"one:{'2' * 40}:{TREE}:{MSG_HASH}"

        def verifier(o_head, o_base, o_tree, n_head, n_base, other_heads=()):
            if (o_head, o_base, o_tree, n_head, n_base) == (
                ANCHOR_HEAD,
                OLD_BASE,
                TREE,
                NEW_HEAD,
                NEW_BASE,
            ):
                return ANCHOR_IK
            return None

        carry_forward_hits = 0
        direct_failure_checked = 0
        cf_non_success_checked = 0
        direct_unblock_hits = 0
        cf_carry_unblock_hits = 0
        cf_direct_unblock_hits = 0

        for trial in range(1500):
            skew_window = trial >= 1000
            comments = []
            reviews = []
            gen_items = []
            n_items = rng.randint(2, 4) if skew_window else rng.randint(1, 5)
            next_id = 100
            for idx in range(n_items):
                next_id += rng.randint(1, 5)
                ts = f"2026-11-23T0{idx // 6}:{(idx * 7) % 60:02d}:00Z"
                if skew_window and idx == 0:
                    kind = rng.choice(["g2_cmt", "g2_cmt", "codex"])
                elif skew_window and idx == n_items - 1:
                    kind = "g2_rev"
                else:
                    kind = rng.choice(["g2_rev", "g2_rev", "g2_cmt", "codex"])
                if kind == "codex":
                    c_head = rng.choice(
                        [ANCHOR_HEAD, NEW_HEAD, unrelated_head]
                    )
                    c_status = rng.choice(
                        ["completed", "completed", "in_progress"]
                    )
                    c_any = rng.choice([False, False, True, None])
                    c_unres = rng.choice([False, False, True, None])
                    item = summary(
                        head=c_head,
                        created_at=ts,
                        completed_at=ts,
                        status=c_status,
                        has_any_findings=c_any,
                        has_unresolved_findings=c_unres,
                    )
                    item["id"] = next_id
                    malformed = rng.random() < (0.2 if skew_window else 0.08)
                    if malformed:
                        item["body"] = (
                            "<!-- codex-pull-request-review-summary -->\n"
                            "<!-- codex-review-state:v99 {} -->"
                        )
                    comments.append(item)
                    gen_items.append(
                        {
                            "kind": "codex",
                            "id": next_id,
                            "head": c_head,
                            "status": c_status,
                            "any_findings": c_any,
                            "unres": c_unres,
                            "malformed": malformed,
                        }
                    )
                    continue

                verdict = (
                    rng.choice(["clean", "clean", "findings"])
                    if skew_window
                    else rng.choice(
                        ["clean", "clean", "clean", "findings", "incomplete"]
                    )
                )
                findings = (
                    [
                        {
                            "severity": "P1",
                            "path": "a.rs",
                            "line": 1,
                            "summary": "bug",
                        }
                    ]
                    if verdict == "findings"
                    else []
                )
                if skew_window:
                    r_head = rng.choice([ANCHOR_HEAD, NEW_HEAD])
                    r_base = OLD_BASE if r_head == ANCHOR_HEAD else NEW_BASE
                    r_tree = TREE
                    ik_choice = ANCHOR_IK
                    r_fam = (
                        "gemini"
                        if idx == n_items - 1
                        else rng.choice(["gemini", "claude", "claude"])
                    )
                    if idx == n_items - 1:
                        verdict = "clean"
                        findings = []
                else:
                    r_head = rng.choice(
                        [
                            ANCHOR_HEAD,
                            ANCHOR_HEAD,
                            ANCHOR_HEAD,
                            NEW_HEAD,
                            unrelated_head,
                        ]
                    )
                    r_base = (
                        OLD_BASE
                        if r_head == ANCHOR_HEAD
                        else rng.choice([OLD_BASE, NEW_BASE])
                    )
                    r_tree = rng.choice([TREE, TREE, OTHER_TREE])
                    r_fam = rng.choice(["gemini", "gemini", "claude"])
                    ik_choice = rng.choice(
                        [ANCHOR_IK, ANCHOR_IK, alt_ik, "custom:legacy", None]
                    )
                extra = {}
                if ik_choice is not None:
                    extra["identity_key"] = ik_choice
                if kind == "g2_rev":
                    state = (
                        "COMMENTED"
                        if skew_window
                        else rng.choice(
                            [
                                "COMMENTED",
                                "COMMENTED",
                                "COMMENTED",
                                "CHANGES_REQUESTED",
                                "APPROVED",
                                "PENDING",
                            ]
                        )
                    )
                    cid = (
                        r_head
                        if skew_window or rng.random() < 0.85
                        else unrelated_head
                    )
                    reviews.append(
                        gate2_review(
                            review_id=next_id,
                            head_sha=r_head,
                            base_sha=r_base,
                            tree_sha=r_tree,
                            reviewer_family=r_fam,
                            author_family="claude",
                            verdict=verdict,
                            findings=findings,
                            state=state,
                            commit_id=cid,
                            submitted_at=ts,
                            **extra,
                        )
                    )
                    gen_items.append(
                        {
                            "kind": "g2_rev",
                            "id": next_id,
                            "head": r_head,
                            "base": r_base,
                            "tree": r_tree,
                            "reviewer_fam": r_fam,
                            "verdict": verdict,
                            "findings": bool(findings),
                            "state": state,
                            "cid": cid,
                            "ik": ik_choice,
                            "malformed": False,
                        }
                    )
                else:
                    comments.append(
                        gate2_comment(
                            comment_id=next_id,
                            head_sha=r_head,
                            base_sha=r_base,
                            tree_sha=r_tree,
                            reviewer_family=r_fam,
                            author_family="claude",
                            verdict=verdict,
                            findings=findings,
                            created_at=ts,
                            **extra,
                        )
                    )
                    gen_items.append(
                        {
                            "kind": "g2_cmt",
                            "id": next_id,
                            "head": r_head,
                            "base": r_base,
                            "tree": r_tree,
                            "reviewer_fam": r_fam,
                            "verdict": verdict,
                            "findings": bool(findings),
                            "state": None,
                            "cid": r_head,
                            "ik": ik_choice,
                            "malformed": False,
                        }
                    )

            comment_ids = sorted(c["id"] for c in comments)
            tail = [comment_ids[-1] + 10] if comment_ids else [10]
            watermarks = [0] + comment_ids + tail
            if skew_window:
                d1, d2 = 0, tail[0]
            else:
                d1 = rng.choice(watermarks)
                d2 = rng.choice([w for w in watermarks if w >= d1])

            direct_d1 = review_result(
                ANCHOR_HEAD,
                comments,
                deleted_through=d1,
                reviews=reviews,
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            )
            direct_d2 = review_result(
                ANCHOR_HEAD,
                comments,
                deleted_through=d2,
                reviews=reviews,
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            )
            # Omit `historical_identities` so carry-forward actually runs
            # whenever ANCHOR_HEAD clears and NEW_HEAD lacks a direct pass.
            cf_d1 = review_result(
                NEW_HEAD,
                comments,
                deleted_through=d1,
                reviews=reviews,
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )
            cf_d2 = review_result(
                NEW_HEAD,
                comments,
                deleted_through=d2,
                reviews=reviews,
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            )

            # CI-01: Carried-forward success requires anchor success at that
            # same deletion watermark.
            for watermark, anchor_r, cf_r in (
                (d1, direct_d1, cf_d1),
                (d2, direct_d2, cf_d2),
            ):
                if "carried forward" in cf_r.reason:
                    carry_forward_hits += 1
                    self.assertEqual(
                        anchor_r.state,
                        "success",
                        f"trial={trial} d={watermark}: "
                        f"direct={anchor_r} cf={cf_r}",
                    )

            # CI-02a: For direct `review_gate2_result`, increasing
            # `deleted_through` (`d1 <= d2`) never waives an active finding or
            # failing PR review on `(ANCHOR_HEAD, OLD_BASE, TREE)`; any unblock
            # requires a tombstoned comment or Codex summary in `(d1, d2]`.
            if direct_d1.state == "failure":
                direct_failure_checked += 1
                if direct_d2.state == "success":
                    direct_unblock_hits += 1
                    self.assertFalse(
                        _oracle_has_active_blocker_for_head(
                            gen_items,
                            ANCHOR_HEAD,
                            OLD_BASE,
                            TREE,
                            ANCHOR_IK,
                            d2,
                        ),
                        f"trial={trial} direct: tombstoning waived finding "
                        f"or failing review on {d1}->{d2}: "
                        f"{direct_d1} -> {direct_d2}",
                    )
                    self.assertTrue(
                        any(d1 < c["id"] <= d2 for c in comments),
                        f"trial={trial} direct: no comment in ({d1}, {d2}]",
                    )

            # CI-02b: On NEW_HEAD (`cf_d1 -> cf_d2`), branch by whether `cf_d2`
            # passed via rebase carry-forward or direct review on NEW_HEAD.
            # Raising `deleted_through` can unblock a tombstoned non-finding
            # comment or Codex summary in `(d1, d2]`, but never waive an active
            # finding or failing PR review on the winning path.
            if cf_d1.state != "success":
                cf_non_success_checked += 1
                if cf_d2.state == "success":
                    if "carried forward" in cf_d2.reason:
                        cf_carry_unblock_hits += 1
                        self.assertFalse(
                            _oracle_has_active_blocker_for_head(
                                gen_items,
                                ANCHOR_HEAD,
                                OLD_BASE,
                                TREE,
                                ANCHOR_IK,
                                d2,
                                is_carry_forward=True,
                            ),
                            f"trial={trial} cf: tombstoning waived anchor "
                            f"blocker on {d1}->{d2}: {cf_d1} -> {cf_d2}",
                        )
                    else:
                        cf_direct_unblock_hits += 1
                        self.assertFalse(
                            _oracle_has_active_blocker_for_head(
                                gen_items,
                                NEW_HEAD,
                                NEW_BASE,
                                TREE,
                                ANCHOR_IK,
                                d2,
                            ),
                            f"trial={trial} cf direct: tombstoning waived "
                            f"NEW_HEAD blocker on {d1}->{d2}: "
                            f"{cf_d1} -> {cf_d2}",
                        )
                    self.assertTrue(
                        any(d1 < c["id"] <= d2 for c in comments),
                        f"trial={trial} cf: no comment in ({d1}, {d2}]",
                    )

        # Thresholds set comfortably below the multi-seed observed minima.
        self.assertGreaterEqual(carry_forward_hits, 20)
        self.assertGreaterEqual(direct_failure_checked, 40)
        self.assertGreaterEqual(cf_non_success_checked, 80)
        self.assertGreaterEqual(direct_unblock_hits, 5)
        self.assertGreaterEqual(cf_carry_unblock_hits, 5)
        self.assertGreaterEqual(cf_direct_unblock_hits, 5)

    def test_tombstoned_non_finding_comment_unblocks_only_comment_failures(
        self,
    ) -> None:
        # Positive + negative control for docs/codex-review.md:313-327:
        # tombstoning a non-finding issue comment unblocks a later clean review,
        # while a finding comment or failing PR review stays blocking.
        clean_anchor = gate2_review(
            review_id=20,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            identity_key=ANCHOR_IK,
            submitted_at="2026-11-23T02:00:00Z",
        )
        non_finding_cmt = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            reviewer_family="claude",
            author_family="claude",
            created_at="2026-11-23T01:00:00Z",
        )
        finding_cmt = gate2_comment(
            comment_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            verdict="findings",
            findings=[
                {
                    "severity": "P1",
                    "path": "a.rs",
                    "line": 1,
                    "summary": "bug",
                }
            ],
            created_at="2026-11-23T01:00:00Z",
        )
        blocking_rev = gate2_review(
            review_id=15,
            head_sha=ANCHOR_HEAD,
            base_sha=OLD_BASE,
            tree_sha=TREE,
            state="CHANGES_REQUESTED",
            submitted_at="2026-11-23T01:00:00Z",
        )

        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=0,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "success",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        self.assertEqual(
            review_result(
                ANCHOR_HEAD,
                [non_finding_cmt],
                deleted_through=15,
                reviews=[blocking_rev, clean_anchor],
                base_sha=OLD_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
            ).state,
            "failure",
        )
        verifier = lambda oh, ob, ot, nh, nb, other_heads=(): ANCHOR_IK
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [non_finding_cmt],
                deleted_through=0,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "pending",
        )
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [non_finding_cmt],
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
        self.assertEqual(
            review_result(
                NEW_HEAD,
                [finding_cmt],
                deleted_through=15,
                reviews=[clean_anchor],
                base_sha=NEW_BASE,
                tree_sha=TREE,
                authorized_reviewers=AUTH_REVIEWERS,
                identity_key=ANCHOR_IK,
                carry_forward_verifier=verifier,
            ).state,
            "pending",
        )

    def test_carry_forward_single_guard_mutations_100_percent_killed(
        self,
    ) -> None:
        source = Path(codex_review.__file__).read_text(encoding="utf-8")
        # Baseline unmutated source must pass the entire probe suite cleanly.
        base_name, base_mod = _compile_mutant(source, "baseline")
        try:
            self._run_carry_forward_probe_suite(base_mod)
        finally:
            sys.modules.pop(base_name, None)

        survivors = []
        for idx, (name, (needle, replacement)) in enumerate(
            CF_MUTANTS.items()
        ):
            count = source.count(needle)
            self.assertEqual(
                count, 1, f"{name}: expected unique anchor, got {count}"
            )
            mutated = source.replace(needle, replacement, 1)
            mod_name, mod = _compile_mutant(mutated, f"{idx}_{name}")
            killed = False
            try:
                self._run_carry_forward_probe_suite(mod)
            except AssertionError:
                killed = True
            finally:
                sys.modules.pop(mod_name, None)
            if not killed:
                survivors.append(name)

        self.assertEqual(survivors, [], f"surviving mutants: {survivors}")
