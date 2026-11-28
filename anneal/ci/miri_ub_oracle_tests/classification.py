# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Miri UB oracle tests for evaluator result classification and the Tier A
gate."""

from __future__ import annotations

from .support import (
    json,
    oracle,
    _sample_pin,
)


class ClassificationCases:
    """`ClassificationAndGateTests` methods for evaluator result classification
    and the Tier A gate."""

    def test_classify_eval_result_cross_checks_rc_and_json(self):
        returned_json = json.dumps({"outcome": {"kind": "returned", "value": {"kind": "returned"}}})
        unwound_json = json.dumps({"outcome": {"kind": "returned", "value": {"kind": "unwound"}}})
        ub_json = json.dumps({
            "outcome": {"kind": "fault", "value": {"kind": "undefined", "reason": "div zero"}}
        })
        unsup_json = json.dumps({
            "outcome": {"kind": "fault", "value": {"kind": "unsupported", "reason": "op"}}
        })
        oof_json = json.dumps({"outcome": {"kind": "out_of_fuel"}})
        abort_json = json.dumps({"outcome": {"kind": "aborted", "value": {}}})

        self.assertEqual(
            oracle.classify_eval_result(0, returned_json, "", expect_valid=False)[0],
            "unsound_accept",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, returned_json, "", expect_valid=True)[0],
            "accepted_valid",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, unwound_json, "", expect_valid=False)[0],
            "unsound_accept",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, unwound_json, "", expect_valid=True)[0],
            "eval_fail_closed",
        )
        self.assertEqual(
            oracle.classify_eval_result(2, ub_json, "", expect_valid=False),
            ("caught_ub", None, "div zero"),
        )
        self.assertEqual(
            oracle.classify_eval_result(3, unsup_json, "", expect_valid=False)[0],
            "eval_fail_closed",
        )
        self.assertEqual(
            oracle.classify_eval_result(3, oof_json, "", expect_valid=False)[:2],
            ("eval_fail_closed", "out_of_fuel"),
        )
        self.assertEqual(
            oracle.classify_eval_result(4, abort_json, "", expect_valid=False)[:2],
            ("unsound_accept", "aborted"),
        )
        self.assertEqual(
            oracle.classify_eval_result(4, abort_json, "", expect_valid=True)[:2],
            ("eval_fail_closed", "unexpected_abort"),
        )
        # Exit code / JSON mismatches must fail closed as tool_error.
        self.assertEqual(
            oracle.classify_eval_result(2, unsup_json, "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result(0, ub_json, "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result(2, "not-json", "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result("timeout", "", "", expect_valid=False)[0],
            "tool_error",
        )
        self.assertEqual(
            oracle.classify_eval_result("output_limit", "", "", expect_valid=False)[:2],
            ("tool_error", "output_limit"),
        )

    def test_classify_eval_result_pre_eval_unsupported_rc3(self):
        reason = (
            "Profile v2 only supports little-endian targets "
            "(Trusted.MirSemantics.profileV2TargetEndian)"
        )
        stderr = f"unsupported program: {reason}\n"
        self.assertEqual(
            oracle.classify_eval_result(3, "", stderr, expect_valid=False),
            ("eval_fail_closed", "pre_eval_unsupported", reason),
        )
        self.assertEqual(
            oracle.classify_eval_result(3, "   \n", stderr, expect_valid=True),
            ("eval_fail_closed", "pre_eval_unsupported", reason),
        )
        # Non-rc3, non-empty stdout, empty reason, extra stderr lines, or
        # unrelated stderr must all remain fail-closed `tool_error`.
        for rc, out, err in (
            (2, "", stderr),
            (1, "", stderr),
            (3, "not-json", stderr),
            (3, "", "unsupported program:   \n"),
            (3, "", f"extra noise\n{stderr}"),
            (3, "", "error: failed to parse MIR\n"),
            (3, "", ""),
        ):
            self.assertEqual(
                oracle.classify_eval_result(rc, out, err, expect_valid=False)[:2],
                ("tool_error", "invalid_eval_json"),
                f"expected tool_error for rc={rc!r}, out={out!r}, err={err!r}",
            )

    def test_tier_a_gate_enforces_unsound_ratchet_and_tool_error(self):
        pin = _sample_pin(expected_file_count=3, min_caught_ub=2)
        ok_units = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "capture_refused"},
        ]
        passed, failures, counts = oracle.evaluate_tier_a_gate(
            ok_units, total_files=3, pin=pin
        )
        self.assertTrue(passed, failures)
        self.assertEqual(counts["caught_ub"], 2)

        # Unsound accept fails hard.
        bad_unsound = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "unsound_accept"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_unsound, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("unsound_accept=1" in f for f in failures))

        # Ratchet drop (caught_ub < min_caught_ub) fails hard.
        bad_ratchet = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "capture_refused"},
            {"file": "fail/c.rs", "revision": None, "bucket": "capture_refused"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_ratchet, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("regressed below pinned ratchet" in f for f in failures))

        # Tool error fails hard.
        bad_tool = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/c.rs", "revision": None, "bucket": "tool_error"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            bad_tool, total_files=3, pin=pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("tool_error=1" in f for f in failures))

        # Set ratchet catches swapping one caught unit for another.
        set_pin = dict(pin)
        set_pin["expected_caught_ub_units"] = ["fail/a.rs", "fail/b.rs"]
        set_pin["expected_unit_count"] = 3
        set_pin["max_harness_skips"] = 0
        swapped = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "capture_refused"},
            {"file": "fail/c.rs", "revision": None, "bucket": "caught_ub"},
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            swapped, total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("pinned caught_ub units regressed: fail/b.rs" in f for f in failures))

        # Exceeding max_harness_skips or changing unit count fails closed.
        skipped = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {
                "file": "fail/c.rs",
                "revision": None,
                "bucket": "rustc_or_harness_rejected",
                "sub_bucket": "harness_target",
            },
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            skipped, total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("max_harness_skips" in f for f in failures))

        # Exceeding max_rustc_or_harness_rejected fails closed even for
        # non-harness-target rustc rejections.
        rej_pin = dict(set_pin)
        rej_pin["max_harness_skips"] = 1
        rej_pin["max_rustc_or_harness_rejected"] = 0
        rustc_rejected = [
            {"file": "fail/a.rs", "revision": None, "bucket": "caught_ub"},
            {"file": "fail/b.rs", "revision": None, "bucket": "caught_ub"},
            {
                "file": "fail/c.rs",
                "revision": None,
                "bucket": "rustc_or_harness_rejected",
                "sub_bucket": "rustc_error",
            },
        ]
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            rustc_rejected, total_files=3, pin=rej_pin
        )
        self.assertFalse(passed)
        self.assertTrue(
            any("max_rustc_or_harness_rejected" in f for f in failures)
        )

        # File-count and unit-count drift must fail closed explicitly.
        passed, failures, _ = oracle.evaluate_tier_a_gate(
            ok_units, total_files=2, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("file count mismatch" in f for f in failures))

        passed, failures, _ = oracle.evaluate_tier_a_gate(
            ok_units[:2], total_files=3, pin=set_pin
        )
        self.assertFalse(passed)
        self.assertTrue(any("unit count mismatch" in f for f in failures))
