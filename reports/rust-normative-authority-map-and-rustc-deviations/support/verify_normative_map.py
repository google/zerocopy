#!/usr/bin/env python3
"""Validate support/normative_authority_map.json completeness and schema."""

import json
import pathlib
import sys

REQUIRED_AREAS = {
    "memory_model_and_data_races",
    "aliasing",
    "provenance_and_int_ptr_casts",
    "validity_and_safety_invariants",
    "layout_and_repr",
    "unwinding_panics_and_c_unwind",
    "floating_point_and_nan_rules",
    "inline_assembly",
    "abis_and_extern_abi_strings",
    "target_features",
    "intrinsics",
    "linkage_symbols_and_sections",
    "volatile_access",
    "allocation",
    "constant_evaluation_and_promotion",
    "drop_order",
}

REQUIRED_AUTHORITIES = {
    "reference",
    "fls",
    "nomicon",
    "stdlib",
    "rfcs",
    "opsem",
    "ucg",
    "minirust",
}

ALLOWED_STATUSES = {
    "guaranteed",
    "unspecified_stable_in_practice",
    "explicitly_unspecified",
    "undefined_behavior",
    "open",
}


def main() -> int:
    here = pathlib.Path(__file__).resolve().parent
    map_path = here / "normative_authority_map.json"
    data = json.loads(map_path.read_text(encoding="utf-8"))

    areas_seen = set()
    statuses_seen = set()
    ids_seen = set()

    for entry in data["items"]:
        item_id = entry["id"]
        assert item_id not in ids_seen, f"duplicate id: {item_id}"
        ids_seen.add(item_id)

        area = entry["area"]
        assert area in REQUIRED_AREAS, f"unknown area: {area}"
        areas_seen.add(area)

        status = entry["status"]
        assert status in ALLOWED_STATUSES, f"invalid status: {status}"
        statuses_seen.add(status)
        if status == "open":
            assert entry.get("tracking_issue"), f"open item {item_id} missing tracking_issue"

        auths = entry["authorities"]
        assert set(auths.keys()) == REQUIRED_AUTHORITIES, (
            f"item {item_id} authority keys mismatch: {set(auths.keys())}"
        )
        assert isinstance(entry["requires_matching_rustc"], bool)
        assert entry.get("disagreements"), f"item {item_id} missing disagreements"
        assert entry.get("rustc_deviations"), f"item {item_id} missing rustc_deviations"

    missing_areas = REQUIRED_AREAS - areas_seen
    assert not missing_areas, f"missing areas: {sorted(missing_areas)}"
    assert statuses_seen == ALLOWED_STATUSES, (
        f"not all status categories covered: missing {ALLOWED_STATUSES - statuses_seen}"
    )

    print(
        f"OK: {len(data['items'])} items verified across {len(areas_seen)} semantic areas "
        f"and {len(REQUIRED_AUTHORITIES)} authorities."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
