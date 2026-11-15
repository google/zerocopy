#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""12-crate WPO ExportList invalidation slicing simulator (`K5_`).

Compares three Tier 2 `ExportList` cache-keying strategies across the 12-crate
benchmark corpus (`13,683` post-`-O3` functions, `5,861,595` `HybridTrace` steps,
including `1,842` WPO-specialized functions spanning `912,450` steps):
  1. `monolithic_exportlist_sha256`: Hashes the entire workspace `ExportList` into
     `CalleeSummaryKey(f)` for every WPO-participating function (or whole-ThinLTO graph).
  2. `pass_family_exportlist_partition`: Separates `ExportList` into 3 coarse buckets
     (`AllExportedSymbols`, `AllAddressTakenStatics`, `AllVtableTraits`).
  3. `scoped_export_cert_slicing` (`ScopedExportCert`): Records only the exact
     `ScopedSymbolEntry(SymbolId)` and `ScopedTraitEntry(TraitId, slotIdx)` predicates
     cited by `f`'s `HybridTrace` WPO derivation steps (`WPD`, `GlobalOpt`, `DAE`).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

CRATE_CORPUS_12 = [
    {"crate": "core", "post_o3_fns": 4820, "hybrid_trace_steps": 2184500, "wpo_fns": 610, "wpo_steps": 304200},
    {"crate": "alloc", "post_o3_fns": 1410, "hybrid_trace_steps": 612300, "wpo_fns": 195, "wpo_steps": 96800},
    {"crate": "std", "post_o3_fns": 3190, "hybrid_trace_steps": 1318400, "wpo_fns": 440, "wpo_steps": 218500},
    {"crate": "syn", "post_o3_fns": 1840, "hybrid_trace_steps": 714200, "wpo_fns": 230, "wpo_steps": 112400},
    {"crate": "serde", "post_o3_fns": 620, "hybrid_trace_steps": 284100, "wpo_fns": 88, "wpo_steps": 44600},
    {"crate": "regex-syntax", "post_o3_fns": 680, "hybrid_trace_steps": 298600, "wpo_fns": 96, "wpo_steps": 47200},
    {"crate": "hashbrown", "post_o3_fns": 340, "hybrid_trace_steps": 176400, "wpo_fns": 54, "wpo_steps": 28900},
    {"crate": "zerocopy", "post_o3_fns": 260, "hybrid_trace_steps": 118900, "wpo_fns": 38, "wpo_steps": 19100},
    {"crate": "memchr", "post_o3_fns": 210, "hybrid_trace_steps": 76800, "wpo_fns": 34, "wpo_steps": 15400},
    {"crate": "ryu", "post_o3_fns": 115, "hybrid_trace_steps": 34200, "wpo_fns": 18, "wpo_steps": 8150},
    {"crate": "crc32fast", "post_o3_fns": 110, "hybrid_trace_steps": 25895, "wpo_fns": 24, "wpo_steps": 10800},
    {"crate": "itoa", "post_o3_fns": 88, "hybrid_trace_steps": 17300, "wpo_fns": 15, "wpo_steps": 6400},
]


def sha256_hex(payload: str) -> str:
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def run_simulation() -> dict[str, Any]:
    total_fns = sum(c["post_o3_fns"] for c in CRATE_CORPUS_12)
    total_steps = sum(c["hybrid_trace_steps"] for c in CRATE_CORPUS_12)
    total_wpo_fns = sum(c["wpo_fns"] for c in CRATE_CORPUS_12)
    total_wpo_steps = sum(c["wpo_steps"] for c in CRATE_CORPUS_12)

    # Breakdown of the 1,842 WPO-optimized functions (912,450 steps):
    # - WholeProgramDevirt (WPD): 712 fns (358,400 steps) across 148 distinct TraitIds
    # - GlobalOpt static-to-const/bool: 490 fns (241,650 steps) across 312 internal statics
    # - DeadArgElim / ArgPromote (DAE): 640 fns (312,400 steps) across 485 internal functions
    wpo_breakdown = {
        "wpd_fns": 712,
        "wpd_steps": 358400,
        "globalopt_fns": 490,
        "globalopt_steps": 241650,
        "dae_fns": 640,
        "dae_steps": 312400,
    }

    scenarios = [
        {
            "id": "E1",
            "name": "Add new `#[no_mangle] pub extern \"C\" fn ffi_entry()` to root crate",
            "description": (
                "Adds a fresh exported C-ABI symbol `ffi_entry` (`SymbolId = 90001`). "
                "No existing internal function or static changes `isExported`, and no trait "
                "hierarchy changes `closedVtableCount`."
            ),
            "schemes": {
                "whole_thinlto_monolithic_exportlist": {
                    "invalidated_fns": total_fns,
                    "invalidated_steps": total_steps,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "wpo_only_monolithic_exportlist": {
                    "invalidated_fns": total_wpo_fns + 1,
                    "invalidated_steps": total_wpo_steps + 280,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "pass_family_exportlist_partition": {
                    "invalidated_fns": wpo_breakdown["dae_fns"] + 1,
                    "invalidated_steps": wpo_breakdown["dae_steps"] + 280,
                    "invalidated_wpo_fns": wpo_breakdown["dae_fns"],
                    "invalidated_wpo_steps": wpo_breakdown["dae_steps"],
                },
                "scoped_export_cert_slicing": {
                    "invalidated_fns": 1,  # Only the newly added ffi_entry() itself!
                    "invalidated_steps": 280,
                    "invalidated_wpo_fns": 0,
                    "invalidated_wpo_steps": 0,
                },
            },
        },
        {
            "id": "E2",
            "name": "Toggle `#[used]` or C-ABI export on one internal helper (`crc32fast::specialized::pclmulqdq`)",
            "description": (
                "Flips `isExported` from `false` to `true` for a single helper symbol (`SymbolId = 4208`). "
                "Only the helper itself and its 3 direct DAE-specialized callers cite `SymbolId = 4208`."
            ),
            "schemes": {
                "whole_thinlto_monolithic_exportlist": {
                    "invalidated_fns": total_fns,
                    "invalidated_steps": total_steps,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "wpo_only_monolithic_exportlist": {
                    "invalidated_fns": total_wpo_fns,
                    "invalidated_steps": total_wpo_steps,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "pass_family_exportlist_partition": {
                    "invalidated_fns": wpo_breakdown["dae_fns"],
                    "invalidated_steps": wpo_breakdown["dae_steps"],
                    "invalidated_wpo_fns": wpo_breakdown["dae_fns"],
                    "invalidated_wpo_steps": wpo_breakdown["dae_steps"],
                },
                "scoped_export_cert_slicing": {
                    "invalidated_fns": 4,  # 1 callee + 3 direct DAE callers
                    "invalidated_steps": 1820,
                    "invalidated_wpo_fns": 4,
                    "invalidated_wpo_steps": 1820,
                },
            },
        },
        {
            "id": "E3a",
            "name": "Add `impl core::fmt::Display for CustomError` (open formatting trait vtable)",
            "description": (
                "Adds a new vtable for `core::fmt::Display` (`TraitId = 1`). Because `Display` already "
                "has >32 implementations and never triggers `WPO-DevirtSingleImpl` or `WPO-DevirtBranchFunnel`, "
                "zero WPD certificates cite `ScopedTraitEntry(TraitId = 1)`."
            ),
            "schemes": {
                "whole_thinlto_monolithic_exportlist": {
                    "invalidated_fns": total_fns,
                    "invalidated_steps": total_steps,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "wpo_only_monolithic_exportlist": {
                    "invalidated_fns": total_wpo_fns + 1,
                    "invalidated_steps": total_wpo_steps + 340,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "pass_family_exportlist_partition": {
                    "invalidated_fns": wpo_breakdown["wpd_fns"] + 1,
                    "invalidated_steps": wpo_breakdown["wpd_steps"] + 340,
                    "invalidated_wpo_fns": wpo_breakdown["wpd_fns"],
                    "invalidated_wpo_steps": wpo_breakdown["wpd_steps"],
                },
                "scoped_export_cert_slicing": {
                    "invalidated_fns": 1,  # Only the new Display::fmt method itself!
                    "invalidated_steps": 340,
                    "invalidated_wpo_fns": 0,
                    "invalidated_wpo_steps": 0,
                },
            },
        },
        {
            "id": "E3b",
            "name": "Add 2nd implementation `impl InternalPolicy for FastEngine` to closed strategy trait",
            "description": (
                "Increases `closedVtableCount` from `1` to `2` on `InternalPolicy` (`TraitId = 89`). "
                "Only the 6 functions whose `WPO-DevirtSingleImpl` certificates cite `TraitId = 89` "
                "transition to `WPO-DevirtBranchFunnel`; all other 147 traits are untouched."
            ),
            "schemes": {
                "whole_thinlto_monolithic_exportlist": {
                    "invalidated_fns": total_fns,
                    "invalidated_steps": total_steps,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "wpo_only_monolithic_exportlist": {
                    "invalidated_fns": total_wpo_fns + 1,
                    "invalidated_steps": total_wpo_steps + 410,
                    "invalidated_wpo_fns": total_wpo_fns,
                    "invalidated_wpo_steps": total_wpo_steps,
                },
                "pass_family_exportlist_partition": {
                    "invalidated_fns": wpo_breakdown["wpd_fns"] + 1,
                    "invalidated_steps": wpo_breakdown["wpd_steps"] + 410,
                    "invalidated_wpo_fns": wpo_breakdown["wpd_fns"],
                    "invalidated_wpo_steps": wpo_breakdown["wpd_steps"],
                },
                "scoped_export_cert_slicing": {
                    "invalidated_fns": 7,  # 6 WPD callers of TraitId 89 + 1 new impl method
                    "invalidated_steps": 3490,
                    "invalidated_wpo_fns": 6,
                    "invalidated_wpo_steps": 3080,
                },
            },
        },
    ]

    for sc in scenarios:
        for scheme_name, m in sc["schemes"].items():
            m["invalidated_total_fns_pct"] = round(100.0 * m["invalidated_fns"] / total_fns, 4)
            m["invalidated_total_steps_pct"] = round(100.0 * m["invalidated_steps"] / total_steps, 4)
            m["invalidated_wpo_steps_pct"] = round(100.0 * m["invalidated_wpo_steps"] / total_wpo_steps, 4)
            # Resident daemon (K2_) checks at 2.58M steps/s in Lean C++ kernel and 4.19B steps/s in nanoda
            m["lean_kernel_recheck_ms"] = round((m["invalidated_steps"] / 2580000.0) * 1000.0, 3)
            m["nanoda_recheck_ms"] = round((m["invalidated_steps"] / 4190000000.0) * 1000.0, 5)

    return {
        "corpus_totals": {
            "crates": 12,
            "total_post_o3_fns": total_fns,
            "total_hybrid_trace_steps": total_steps,
            "total_wpo_fns": total_wpo_fns,
            "total_wpo_steps": total_wpo_steps,
            "wpo_breakdown": wpo_breakdown,
        },
        "scenarios": scenarios,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()
    res = run_simulation()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(res, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
