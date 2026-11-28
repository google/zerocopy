# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Tier A and Tier B pass/fail gates."""

from __future__ import annotations

from collections import Counter

from .common import BUCKETS


def _count_buckets(units: list[dict[str, object]]) -> dict[str, int]:
    ctr = Counter(str(u.get("bucket", "tool_error")) for u in units)
    counts = {b: ctr.get(b, 0) for b in BUCKETS}
    for key, val in sorted(ctr.items()):
        if key not in counts:
            counts[key] = val
    return counts


def evaluate_tier_a_gate(
    units: list[dict[str, object]],
    *,
    total_files: int,
    pin: dict[str, object],
) -> tuple[bool, list[str], dict[str, int]]:
    """Evaluate Tier A soundness and ratchet invariants fail-closed."""
    counts = _count_buckets(units)
    failures: list[str] = []

    expected_files = int(pin["expected_file_count"])  # type: ignore[arg-type]
    if total_files != expected_files:
        failures.append(
            f"file count mismatch: ran {total_files}, expected {expected_files}"
        )
    if not units:
        failures.append("no Tier A units executed")

    if "expected_unit_count" in pin:
        exp_units_cnt = int(pin["expected_unit_count"])  # type: ignore[arg-type]
        if len(units) != exp_units_cnt:
            failures.append(
                f"unit count mismatch: ran {len(units)}, expected {exp_units_cnt}"
            )

    if "max_harness_skips" in pin:
        max_skips = int(pin["max_harness_skips"])  # type: ignore[arg-type]
        skips = sum(
            1
            for u in units
            if u.get("sub_bucket")
            in ("harness_target", "harness_unforwarded_flags")
        )
        if skips > max_skips:
            failures.append(
                f"harness skips={skips} exceeded max_harness_skips={max_skips}"
            )

    if "max_rustc_or_harness_rejected" in pin:
        max_rejected = int(pin["max_rustc_or_harness_rejected"])  # type: ignore[arg-type]
        rejected = counts.get("rustc_or_harness_rejected", 0)
        if rejected > max_rejected:
            failures.append(
                f"rustc_or_harness_rejected={rejected} exceeded "
                f"max_rustc_or_harness_rejected={max_rejected}"
            )

    unsound = counts.get("unsound_accept", 0)
    if unsound != 0:
        offenders = [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "unsound_accept"
        ][:10]
        failures.append(
            f"unsound_accept={unsound} (must be 0): {', '.join(offenders)}"
        )

    tool_errors = counts.get("tool_error", 0)
    if tool_errors != 0:
        offenders = [
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "tool_error"
        ][:10]
        failures.append(
            f"tool_error={tool_errors} (must be 0): {', '.join(offenders)}"
        )

    min_caught = int(pin["min_caught_ub"])  # type: ignore[arg-type]
    caught = counts.get("caught_ub", 0)
    if caught < min_caught:
        failures.append(
            f"caught_ub={caught} regressed below pinned ratchet "
            f"min_caught_ub={min_caught}"
        )

    if "expected_caught_ub_units" in pin:
        caught_labels = {
            f"{u['file']}" + (f"[{u['revision']}]" if u.get("revision") else "")
            for u in units
            if u.get("bucket") == "caught_ub"
        }
        required_units = [str(x) for x in pin["expected_caught_ub_units"]]  # type: ignore[union-attr]
        missing = sorted(u for u in required_units if u not in caught_labels)
        if missing:
            failures.append(
                f"pinned caught_ub units regressed: {', '.join(missing)}"
            )

    return len(failures) == 0, failures, counts


def evaluate_tier_b_gate(
    results: list[dict[str, object]],
) -> tuple[bool, list[str], dict[str, int]]:
    """Enforce strict per-fixture expectations on Tier B corpus."""
    counts = _count_buckets(results)
    failures: list[str] = []

    if not results:
        failures.append("no Tier B fixtures executed")

    valid_controls_accepted = 0
    ub_caught_verified = 0

    for res in results:
        fid = str(res["id"])
        kind = str(res["kind"])
        bucket = str(res["bucket"])
        detail = str(res.get("detail") or "")
        expected_sub = res.get("expected_fault_substring")

        if kind in ("rust_ub_caught", "mir_ub_caught"):
            if bucket != "caught_ub":
                failures.append(
                    f"{fid} ({kind}): expected caught_ub, got {bucket} ({detail})"
                )
            else:
                if isinstance(expected_sub, str) and expected_sub:
                    if expected_sub.lower() not in detail.lower():
                        failures.append(
                            f"{fid} ({kind}): fault detail {detail!r} missing "
                            f"expected substring {expected_sub!r}"
                        )
                    else:
                        ub_caught_verified += 1
                else:
                    ub_caught_verified += 1
        elif kind == "rust_ub_fail_closed":
            if bucket not in ("caught_ub", "capture_refused", "eval_fail_closed"):
                failures.append(
                    f"{fid} ({kind}): expected caught_ub or fail-closed refusal, "
                    f"got {bucket} ({detail})"
                )
        elif kind in ("rust_valid_control", "mir_valid_control"):
            if bucket != "accepted_valid":
                failures.append(
                    f"{fid} ({kind}): valid control MUST be accepted_valid, "
                    f"got {bucket} ({detail})"
                )
            else:
                valid_controls_accepted += 1
        else:
            failures.append(f"{fid}: unknown kind {kind!r}")

    if ub_caught_verified < 1:
        failures.append("anti-vacuity: zero UB fixtures verified as caught_ub")
    if valid_controls_accepted < 1:
        failures.append("anti-vacuity: zero valid control fixtures accepted")

    return len(failures) == 0, failures, counts
