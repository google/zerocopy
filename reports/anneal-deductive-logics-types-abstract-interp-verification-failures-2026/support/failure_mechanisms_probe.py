#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Deterministic finite witnesses for verification failure classes in Sub-Domain 1.

Each check demonstrates a concrete historical failure mechanism from deductive
verifiers, separation logics, aliasing models, or abstract interpreters, and
verifies how Anneal's four trusted/lean/ primitives reject the unsoundness.
"""

from __future__ import annotations
import json
from pathlib import Path


def check_1_prophecy_vacuity_vs_productive_on() -> dict[str, object]:
    """Witness 1: Over-constrained prophecy / demonic miracle vs. ProductiveOn."""
    domain = [0, 1, 2]
    # A buggy prophetic translation emits an unsatisfiable prophecy constraint
    # (v_final == v_prophecy and v_final != v_prophecy), yielding an empty
    # outcome set while remaining 'defined' (no UB step).
    sem_buggy = {q: {"defined": True, "outcomes": set()} for q in domain}
    # Impossible postcondition: ensures false
    post_false = lambda _o: False

    # Naive partial-correctness check: defined and all outcomes satisfy post_false
    naive_vc_accepts_false = all(
        sem_buggy[q]["defined"]
        and all(post_false(o) for o in sem_buggy[q]["outcomes"])
        for q in domain
    )
    # Anneal's ProductiveOn requires at least one valid outcome for every q in pre
    productive_on_holds = all(
        sem_buggy[q]["defined"] and len(sem_buggy[q]["outcomes"]) > 0
        for q in domain
    )
    assert naive_vc_accepts_false is True
    assert productive_on_holds is False
    return {
        "naive_vc_accepts_ensures_false": naive_vc_accepts_false,
        "anneal_productive_on_accepts": productive_on_holds,
    }


def check_2_contradictory_pre_vs_inhabited_pre() -> dict[str, object]:
    """Witness 2: Contradictory refinement / prelude axiom vs. InhabitedPre."""
    domain = list(range(-16, 17))
    # Contradictory refinement precondition: x > 10 and x < 5
    pre_contradictory = lambda q: (q > 10) and (q < 5)
    # Program triggers immediate UB (defined = False) on all concrete inputs
    sem_ub = {q: {"defined": False, "outcomes": set()} for q in domain}

    # Both SpecOn and ProductiveOn quantify universally over {q | pre(q)}, so
    # both hold vacuously when pre is uninhabited.
    spec_on_holds = all(
        sem_ub[q]["defined"] for q in domain if pre_contradictory(q)
    )
    productive_on_holds = all(
        sem_ub[q]["defined"] and len(sem_ub[q]["outcomes"]) > 0
        for q in domain
        if pre_contradictory(q)
    )
    inhabited_pre_holds = any(pre_contradictory(q) for q in domain)

    assert spec_on_holds is True
    assert productive_on_holds is True
    assert inhabited_pre_holds is False
    return {
        "spec_on_vacuously_holds": spec_on_holds,
        "productive_on_vacuously_holds": productive_on_holds,
        "anneal_inhabited_pre_accepts": inhabited_pre_holds,
    }


def check_3_antecedent_waiver_vs_positive_verification_result() -> dict[str, object]:
    """Witness 3: Antecedent axiom waiver contamination vs. VerificationResult."""
    # Obligation 1 is an inconsistent helper lemma (False) that the user waived.
    # Obligation 2 is an unwaived memory-safety check that is also False (buggy).
    obligations = {1: False, 2: False}
    waived = {1}
    allowed_waivers = {1}

    # Antecedent-assumption style: waived obligations are injected as hypotheses
    # (/\_{i in waived} ob_i) -> (/\_{j not in waived} ob_j).
    antecedent_hyp = all(obligations[i] for i in waived)
    antecedent_goal = all(obligations[j] for j in obligations if j not in waived)
    antecedent_style_accepts = (not antecedent_hyp) or antecedent_goal

    # Anneal's positive per-obligation VerificationResult:
    # AllHold(waived.map policy.isAllowed) /\ AllHold(obligations.map (id in waived \/ prop))
    anneal_verification_result = all(w in allowed_waivers for w in waived) and all(
        (ob_id in waived) or prop for ob_id, prop in obligations.items()
    )

    assert antecedent_style_accepts is True
    assert anneal_verification_result is False
    return {
        "antecedent_waiver_accepts_unwaived_bug": antecedent_style_accepts,
        "anneal_positive_verification_result_accepts": anneal_verification_result,
    }


def check_4_reentrancy_and_unwind_vs_external_call() -> dict[str, object]:
    """Witness 4: Mid-method broken AdtInv across callback/unwind vs. externalCall."""
    # Simulate a Vec::dedup_by-like method that sets len=2 while only 1 slot is
    # initialized (AdtInv broken), calls user closure f(), and only repairs
    # len=1 on the normal return path.
    init_state = {"len": 2, "initialized": 1}
    adt_inv = lambda s: s["len"] <= s["initialized"]

    # Step 1: Method enters callback f() while AdtInv is false.
    boundary_inv_at_call = adt_inv(init_state)
    # Normal return path after callback repairs state:
    normal_exit_state = {"len": 1, "initialized": 1}
    # Panic/unwind path from callback skips repair and drops uninitialized slot:
    unwind_exit_state = init_state

    naive_normal_return_post_only = adt_inv(normal_exit_state)
    anneal_external_call_safe = boundary_inv_at_call and adt_inv(normal_exit_state)
    anneal_unwind_terminal_safe = adt_inv(unwind_exit_state)

    assert naive_normal_return_post_only is True
    assert anneal_external_call_safe is False
    assert anneal_unwind_terminal_safe is False
    return {
        "naive_normal_post_only_accepts": naive_normal_return_post_only,
        "anneal_external_call_boundary_inv_accepts": anneal_external_call_safe,
        "anneal_unwind_terminal_check_accepts": anneal_unwind_terminal_safe,
    }


def check_5_stacked_vs_tree_borrows_two_phase() -> dict[str, object]:
    """Witness 5: Stacked Borrows vs. Tree Borrows on two-phase borrow read-before-write."""
    # Pattern: v.push(v.len())
    # 1. Create mutable borrow child tag_mut from parent tag_parent.
    # 2. Read through tag_parent (evaluating v.len()).
    # 3. Write through tag_mut (performing v.push(...)).
    sb_stack = ["tag_parent", "tag_mut_unique"]
    # In pure Stacked Borrows, a read through tag_parent pops Unique tags above it:
    sb_stack_after_parent_read = sb_stack[: sb_stack.index("tag_parent") + 1]
    sb_write_tag_mut_valid = "tag_mut_unique" in sb_stack_after_parent_read

    # In Tree Borrows, tag_mut starts as Reserved; a read through tag_parent
    # keeps tag_mut Reserved, and the subsequent write activates tag_mut:
    tb_state = {"tag_parent": "Active", "tag_mut": "Reserved"}
    # Read through tag_parent: Reserved child tolerates foreign reads
    tb_after_parent_read = dict(tb_state)
    # Write through tag_mut: transitions Reserved -> Active
    tb_write_tag_mut_valid = tb_after_parent_read["tag_mut"] in ("Reserved", "Active")
    tb_after_child_write = {"tag_parent": "Active", "tag_mut": "Active"}
    # Conflicting read through tag_parent AFTER tag_mut is Active disables tag_mut:
    tb_child_after_conflicting_parent_read = (
        "Disabled" if tb_after_child_write["tag_mut"] == "Active" else "Active"
    )

    assert sb_write_tag_mut_valid is False
    assert tb_write_tag_mut_valid is True
    assert tb_child_after_conflicting_parent_read == "Disabled"
    return {
        "stacked_borrows_accepts_two_phase_pattern": sb_write_tag_mut_valid,
        "tree_borrows_accepts_two_phase_pattern": tb_write_tag_mut_valid,
        "tree_borrows_state_after_conflicting_read": tb_child_after_conflicting_parent_read,
    }


def check_6_ebpf_cve_2021_31440_subreg_bounds() -> dict[str, object]:
    """Witness 6: eBPF CVE-2021-31440 64-to-32-bit bounds projection unsoundness."""
    # Concrete 64-bit interval [0x0_ffffffff, 0x1_00000000] crosses a 32-bit boundary.
    u64_min = 0x0_FFFFFFFF
    u64_max = 0x1_00000000
    concrete_u32_values = {x & 0xFFFFFFFF for x in (u64_min, u64_max)}

    # Buggy projection (missing upper-32-bit equality guard): projects endpoints
    # directly by low-32-bit truncation, producing [0xffffffff, 0x00000000] or
    # after 32-bit ALU op collapsing bounds unsoundly.
    buggy_u32_min = u64_min & 0xFFFFFFFF
    buggy_u32_max = u64_max & 0xFFFFFFFF
    buggy_interval_well_formed_and_sound = (
        buggy_u32_min <= buggy_u32_max
        and all(buggy_u32_min <= v <= buggy_u32_max for v in concrete_u32_values)
    )

    # Fixed projection (torvalds/linux@10bf4e83167c): only project 64-bit bounds
    # into 32-bit bounds when upper 32 bits of u64_min and u64_max match;
    # otherwise widen 32-bit bounds to [0, 0xffffffff].
    if (u64_min >> 32) == (u64_max >> 32):
        fixed_u32_min = u64_min & 0xFFFFFFFF
        fixed_u32_max = u64_max & 0xFFFFFFFF
    else:
        fixed_u32_min = 0
        fixed_u32_max = 0xFFFFFFFF

    fixed_interval_well_formed_and_sound = (
        fixed_u32_min <= fixed_u32_max
        and all(fixed_u32_min <= v <= fixed_u32_max for v in concrete_u32_values)
    )

    assert buggy_interval_well_formed_and_sound is False
    assert fixed_interval_well_formed_and_sound is True
    return {
        "buggy_64_to_32_projection_sound": buggy_interval_well_formed_and_sound,
        "fixed_64_to_32_projection_sound": fixed_interval_well_formed_and_sound,
    }


def main() -> None:
    results = {
        "witness_1_prophecy_vacuity": check_1_prophecy_vacuity_vs_productive_on(),
        "witness_2_contradictory_pre": check_2_contradictory_pre_vs_inhabited_pre(),
        "witness_3_antecedent_waiver": check_3_antecedent_waiver_vs_positive_verification_result(),
        "witness_4_reentrancy_unwind": check_4_reentrancy_and_unwind_vs_external_call(),
        "witness_5_stacked_vs_tree_borrows": check_5_stacked_vs_tree_borrows_two_phase(),
        "witness_6_ebpf_cve_2021_31440": check_6_ebpf_cve_2021_31440_subreg_bounds(),
    }
    out_path = Path(__file__).with_name("probe-results.json")
    out_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
