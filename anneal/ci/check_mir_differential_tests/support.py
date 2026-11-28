# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`_sample_diff_report`, the differential report fixture shared by the
`check_mir_differential.py` tests."""

from __future__ import annotations

import check_mir_differential as cmd



def _sample_diff_report(*, unsound: int = 0, killed: int = 5, total: int = 5) -> dict:
    cases = [
        {
            "id": "arith_u32_wrapping_add",
            "source": "src/arith_pass.rs",
            "function": "u32_wrapping_add",
            "category": "arith",
            "expected": "pass",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "lean": {
                "kind": "returned",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
            "verdict": {
                "kind": "agree_value",
                "value": {"kind": "int", "int_kind": "u32", "bits": "4"},
            },
        },
        {
            "id": "ub_div_zero_u32",
            "source": "src/ub_corpus.rs",
            "function": "div_zero_u32",
            "category": "ub",
            "expected": "ub",
            "allow_conservative_unsupported": False,
            "kernel_checked": True,
            "miri": {
                "kind": "undefined_behavior",
                "detail": "error: Undefined Behavior: dividing by zero",
            },
            "lean": {"kind": "undefined_behavior", "detail": "undefined"},
            "verdict": (
                {"kind": "unsound_missed_fault"}
                if unsound > 0
                else {"kind": "agree_undefined_behavior"}
            ),
        },
        {
            "id": "unsup_diverging_abort_call",
            "source": "src/unsupported_controls.rs",
            "function": "abort_control",
            "category": "unsupported_control",
            "expected": "unsupported_control",
            "allow_conservative_unsupported": True,
            "kernel_checked": False,
            "miri": {"kind": "abnormal_abort", "detail": "aborted"},
            "lean": {"kind": "unsupported", "detail": "unsupported"},
            "verdict": {
                "kind": "sound_conservative_abstraction",
                "miri": {"kind": "abnormal_abort", "detail": "aborted"},
                "lean_detail": "unsupported",
            },
        },
    ]
    return {
        "schema": "anneal-differential-run/v1",
        "alpha_notice": cmd.ALPHA_NOTICE,
        "mir_dialect": "profile_v1",
        "manifest_path": "tests/corpora/differential/profile_v1/manifest.toml",
        "capture_bin_source": "env_anneal_capture",
        "capture_bin_sha256": "c" * 64,
        "prebuilt_overlay": "staged:26/29",
        "legs": [
            "miri",
            "lean_step_core_captured",
            "lean_wp_kernel_single_block",
        ],
        "metrics": {
            "compared_count": 3,
            "pass_agreed_count": 1,
            "ub_agreed_count": 0 if unsound > 0 else 1,
            "conservative_unsupported_count": 1,
            "kernel_checked_pass_count": 1,
            "kernel_checked_ub_count": 0 if unsound > 0 else 1,
            "unsound_missed_fault_count": unsound,
            "value_mismatch_count": 0,
            "unexpected_conservative_count": 0,
            "leg_divergence_count": 0,
        },
        "red_flags_passed": 0 if unsound > 0 else 7,
        "red_flag_error": "unsound fault present" if unsound > 0 else None,
        "cases": cases,
        "mutant_check": {
            "total_mutants": total,
            "killed_mutants": killed,
            "killed_pct": (killed * 100.0 / total) if total else 0.0,
            "results": [],
            "synthetic_lean_probes": [
                {
                    "probe_id": "probe_move_deinit_ignored",
                    "description": "synthetic move-deinit check",
                    "passed": True,
                    "expected_kill_verdict": "UnsoundMissedFault",
                    "actual_verdict": "UnsoundMissedFault",
                }
            ],
        },
    }
