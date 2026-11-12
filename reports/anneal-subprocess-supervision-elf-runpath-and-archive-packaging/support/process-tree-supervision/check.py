#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Offline validator for support/process-tree-supervision/results.json."""

import json
from pathlib import Path
import sys


def main() -> None:
    here = Path(__file__).resolve().parent
    data = json.loads((here / "results.json").read_text())

    by_strategy = {item["strategy"]: item for item in data["rust_supervisor_strategies"]}
    assert by_strategy["A_direct_child_kill"]["p1_alive_after_reap"] is False
    assert by_strategy["A_direct_child_kill"]["p2_alive_after_reap"] is True
    assert by_strategy["A_direct_child_kill"]["lock_held_by_orphan_after_reap"] is True

    assert by_strategy["B_process_group_killpg"]["p1_alive_after_reap"] is False
    assert by_strategy["B_process_group_killpg"]["p2_alive_after_reap"] is False
    assert by_strategy["B_process_group_killpg"]["lock_held_by_orphan_after_reap"] is False

    assert by_strategy["C1_subreaper_pdeathsig_on_p1_only"]["p1_alive_after_reap"] is False
    assert by_strategy["C1_subreaper_pdeathsig_on_p1_only"]["p2_alive_after_reap"] is True
    assert by_strategy["C1_subreaper_pdeathsig_on_p1_only"]["p2_reparented_to_subreaper"] is True
    assert by_strategy["C1_subreaper_pdeathsig_on_p1_only"]["lock_held_by_orphan_after_reap"] is True

    assert by_strategy["C2_pdeathsig_on_p2_early_p1_exit"]["p1_exited_zero"] is True
    assert by_strategy["C2_pdeathsig_on_p2_early_p1_exit"]["p2_prematurely_killed_by_sigkill"] is True
    assert by_strategy["C2_pdeathsig_on_p2_early_p1_exit"]["p2_alive"] is False

    assert by_strategy["D_combined_pgroup_and_subreaper_waitpid"]["p1_alive_after_reap"] is False
    assert by_strategy["D_combined_pgroup_and_subreaper_waitpid"]["p2_alive_after_reap"] is False
    assert by_strategy["D_combined_pgroup_and_subreaper_waitpid"]["descendant_reap_count"] == 1
    assert by_strategy["D_combined_pgroup_and_subreaper_waitpid"]["lock_held_by_orphan_after_reap"] is False

    by_case = {item["case"]: item for item in data["reproduce_py_cases"]}
    assert by_case["E1_unfixed_reproduce_timeout"]["exit_code"] == 124
    assert by_case["E1_unfixed_reproduce_timeout"]["p2_alive_after_exit"] is True
    assert by_case["E1_unfixed_reproduce_timeout"]["lock_held_by_orphan_after_exit"] is True

    assert by_case["E2_pgroup_reproduce_sigint_without_forwarding"]["exit_code"] == -2
    assert by_case["E2_pgroup_reproduce_sigint_without_forwarding"]["p1_alive_after_sigint"] is True
    assert by_case["E2_pgroup_reproduce_sigint_without_forwarding"]["p2_alive_after_sigint"] is True
    assert by_case["E2_pgroup_reproduce_sigint_without_forwarding"]["lock_held_by_orphan_after_sigint"] is True

    assert by_case["E3a_fixed_pgroup_reproduce_timeout"]["exit_code"] == 124
    assert by_case["E3a_fixed_pgroup_reproduce_timeout"]["p1_alive_after_exit"] is False
    assert by_case["E3a_fixed_pgroup_reproduce_timeout"]["p2_alive_after_exit"] is False
    assert by_case["E3a_fixed_pgroup_reproduce_timeout"]["lock_held_by_orphan_after_exit"] is False

    assert by_case["E3b_fixed_pgroup_reproduce_sigint"]["exit_code"] == -2
    assert by_case["E3b_fixed_pgroup_reproduce_sigint"]["p1_alive_after_sigint"] is False
    assert by_case["E3b_fixed_pgroup_reproduce_sigint"]["p2_alive_after_sigint"] is False
    assert by_case["E3b_fixed_pgroup_reproduce_sigint"]["lock_held_by_orphan_after_sigint"] is False

    print("process-tree-supervision check passed")


if __name__ == "__main__":
    main()
