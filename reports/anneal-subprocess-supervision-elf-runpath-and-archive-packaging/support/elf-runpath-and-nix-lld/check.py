#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Offline validator for support/elf-runpath-and-nix-lld/results.json."""

import json
from pathlib import Path


def main() -> None:
    here = Path(__file__).resolve().parent
    data = json.loads((here / "results.json").read_text())

    cells = {item["cell"]: item for item in data["synthetic_five_cell_dl_load_matrix"]}
    assert cells["1_main_runpath_leaf_runpath_uncolocated"]["exit_code"] == 127
    assert cells["1_main_runpath_leaf_runpath_uncolocated"]["stderr_contains_libdep_missing"] is True

    assert cells["2_main_rpath_blocked_by_leaf_runpath"]["exit_code"] == 127
    assert cells["2_main_rpath_blocked_by_leaf_runpath"]["stderr_contains_libdep_missing"] is True

    assert cells["3_main_rpath_succeeds_when_leaf_has_no_runpath"]["exit_code"] == 0
    assert cells["3_main_rpath_succeeds_when_leaf_has_no_runpath"]["stdout"] == "44"

    assert cells["4_consumer_add_needed_on_main"]["exit_code"] == 0
    assert cells["4_consumer_add_needed_on_main"]["stdout"] == "44"

    assert cells["5_producer_colocation_in_leaf_runpath_without_add_needed"]["exit_code"] == 0
    assert cells["5_producer_colocation_in_leaf_runpath_without_add_needed"]["stdout"] == "44"

    rust_info = data["rust_toolchain_and_nix_lld"]
    dup = rust_info["duplicate_shared_objects"]
    assert dup["libllvm_top_sha256"] == dup["libllvm_rustlib_sha256"]
    assert dup["librustc_driver_top_sha256"] == dup["librustc_driver_rustlib_sha256"]
    assert dup["total_duplicate_bytes"] == 357599568

    lld_probe = rust_info["nix_sandbox_rustc_1_98_lld_probe"]
    assert lld_probe["default_lld_enabled"]["exit_code"] == 1
    assert lld_probe["default_lld_enabled"]["contains_gcc_ld_B_flag"] is True
    assert lld_probe["default_lld_enabled"]["contains_fuse_ld_lld"] is True
    assert lld_probe["default_lld_enabled"]["contains_collect2_posix_spawnp_enoent"] is True
    assert lld_probe["with_linker_features_minus_lld"]["exit_code"] == 0
    assert lld_probe["with_linker_features_minus_lld"]["compiled_binary_stdout"] == "sandbox_ok"

    print("elf-runpath-and-nix-lld check passed")


if __name__ == "__main__":
    main()
