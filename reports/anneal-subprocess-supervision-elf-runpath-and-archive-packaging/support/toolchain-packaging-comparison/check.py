#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Offline validator for support/toolchain-packaging-comparison/results.json."""

import json
from pathlib import Path


def main() -> None:
    here = Path(__file__).resolve().parent
    data = json.loads((here / "results.json").read_text())

    by_variant = {item["variant"]: item for item in data["packaging_variants_comparison"]}

    v1 = by_variant["1_split_archive_manual_env_and_test_reexec"]
    assert v1["required_manual_env_vars_workspace"] == 5
    assert v1["required_manual_env_vars_smoke_test"] == 4
    assert v1["bundles_anneal_audit_in_archive"] is False
    assert v1["reexecs_cargo_test_binary_for_setup"] is True

    v2 = by_variant["2_include_str_embedded_per_run_recompilation"]
    assert v2["embedded_files_count"] == 11
    assert v2["lean_prefix_compilations_per_verify"] == 7
    assert v2["lean_target_compilations_per_verify"] == 4
    assert v2["total_compile_ms"] > v2["target_compile_ms"]

    v4 = by_variant["4_unified_zero_env_precompiled_archive"]
    assert v4["required_manual_env_vars_workspace"] == 0
    assert v4["required_manual_env_vars_smoke_test"] == 0
    assert v4["bundles_anneal_audit_in_archive"] is True
    assert v4["bundles_trusted_boundary_in_archive"] is True
    assert v4["bundles_precompiled_prefix_oleans"] is True
    assert v4["reexecs_cargo_test_binary_for_setup"] is False
    assert v4["lean_prefix_compilations_per_verify"] == 0
    assert v4["lean_target_compilations_per_verify"] == 4
    assert v4["speedup_ratio"] > 1.5

    print("toolchain-packaging-comparison check passed")


if __name__ == "__main__":
    main()
