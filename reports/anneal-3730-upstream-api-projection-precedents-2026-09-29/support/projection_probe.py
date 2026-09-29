#!/usr/bin/env python3
"""Bounded source-map contract fixture; no Volar or Lean process is invoked.

The range enumeration and first-result behavior intentionally mirror the
identified operations in pinned Volar sourceMap.ts and featureWorkers.ts.
They are a small independent model, not an import of the Volar implementation.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path


SOURCE = (
    "fn first() {\n"
    "    /// @lean by rfl\n"
    "}\n"
    "fn second() {\n"
    "    /// @lean by rfl\n"
    "}\n"
)
GENERATED = "by rfl\n-- generated wrapper\nby rfl\n"
TEXT = "by rfl"


@dataclass(frozen=True)
class Mapping:
    name: str
    source_start: int
    generated_start: int
    length: int

    def map_offset(self, offset: int) -> int | None:
        if self.generated_start <= offset <= self.generated_start + self.length:
            return self.source_start + offset - self.generated_start
        return None


def all_source_ranges(mappings: list[Mapping], start: int, end: int,
                      fallback_to_any_match: bool = True) -> list[dict[str, object]]:
    """Mirror pinned SourceMap.findMatchingStartEnd for equal-length spans."""
    starts = [(m.map_offset(start), m) for m in mappings]
    starts = [(mapped, m) for mapped, m in starts if mapped is not None]
    same = []
    for mapped_start, mapping in starts:
        mapped_end = mapping.map_offset(end)
        if mapped_end is not None:
            same.append({"source_range": [mapped_start, mapped_end],
                         "start_mapping": mapping.name, "end_mapping": mapping.name})
    if same or not fallback_to_any_match:
        return same

    result = []
    ends = [(m.map_offset(end), m) for m in mappings]
    ends = [(mapped, m) for mapped, m in ends if mapped is not None]
    for mapped_start, start_mapping in starts:
        for mapped_end, end_mapping in ends:
            if mapped_end >= mapped_start:
                result.append({"source_range": [mapped_start, mapped_end],
                               "start_mapping": start_mapping.name,
                               "end_mapping": end_mapping.name})
                break
    return result


def strict_edit_result(mappings: list[Mapping], start: int, end: int) -> dict[str, object]:
    """Proposed Anneal policy: one same-segment mapping or reject the edit."""
    ranges = all_source_ranges(mappings, start, end)
    if any(item["start_mapping"] != item["end_mapping"] for item in ranges):
        return {"accepted": False, "reason": "cross-segment"}
    if len(ranges) != 1:
        return {"accepted": False, "reason": "ambiguous-or-unmapped"}
    item = ranges[0]
    return {"accepted": True, "source_range": item["source_range"]}


def main() -> None:
    source_offsets = [SOURCE.index(TEXT), SOURCE.index(TEXT, SOURCE.index(TEXT) + 1)]
    generated_offsets = [GENERATED.index(TEXT), GENERATED.rindex(TEXT)]
    mappings = [
        Mapping("first-source-to-first-virtual", source_offsets[0], generated_offsets[0], len(TEXT)),
        Mapping("second-source-to-first-virtual", source_offsets[1], generated_offsets[0], len(TEXT)),
        Mapping("second-source-to-second-virtual", source_offsets[1], generated_offsets[1], len(TEXT)),
    ]
    assert all(SOURCE[m.source_start:m.source_start + m.length] == TEXT for m in mappings)
    assert all(GENERATED[m.generated_start:m.generated_start + m.length] == TEXT for m in mappings)

    ambiguous = all_source_ranges(mappings, 0, len(TEXT))
    reversed_order = all_source_ranges([mappings[1], mappings[0], mappings[2]], 0, len(TEXT))
    assert len(ambiguous) == 2 and len(reversed_order) == 2
    assert ambiguous[0]["source_range"] != reversed_order[0]["source_range"]
    assert not strict_edit_result(mappings, 0, len(TEXT))["accepted"]

    cross_start, cross_end = 3, generated_offsets[1] + 3
    cross = all_source_ranges(mappings, cross_start, cross_end)
    assert cross and cross[0]["start_mapping"] != cross[0]["end_mapping"]
    assert "fn second()" in SOURCE[slice(*cross[0]["source_range"])]
    assert strict_edit_result(mappings, cross_start, cross_end)["reason"] == "cross-segment"

    # One mapped and one synthetic-wrapper additional edit. The pinned Volar
    # transformCompletionItem maps then filters unmappable additionalTextEdits.
    main_edit = [generated_offsets[1], generated_offsets[1] + 2]
    additions = [[generated_offsets[1] + 2, generated_offsets[1] + 4], [10, 12]]
    assert GENERATED[10:12] == "ge"  # within the generated-only wrapper
    mapped_main = all_source_ranges(mappings, *main_edit)
    mapped_additions = [all_source_ranges(mappings, *edit) for edit in additions]
    assert len(mapped_main) == 1 and len(mapped_additions[0]) == 1 and not mapped_additions[1]
    volar_like_kept = [ranges[0]["source_range"] for ranges in mapped_additions if ranges]
    strict_completion = all(strict_edit_result(mappings, *edit)["accepted"] for edit in [main_edit, *additions])
    assert len(volar_like_kept) == 1 and not strict_completion

    result = {
        "basis": "Python standard-library contract model; upstream packages were source-reviewed, not executed",
        "source_sha256": hashlib.sha256(SOURCE.encode()).hexdigest(),
        "generated_sha256": hashlib.sha256(GENERATED.encode()).hexdigest(),
        "source_offsets": source_offsets,
        "generated_offsets": generated_offsets,
        "ambiguous_same_generated_edit": {
            "generated_range": [0, len(TEXT)],
            "all_candidates": ambiguous,
            "first_choice_original_order": ambiguous[0]["source_range"],
            "first_choice_reversed_order": reversed_order[0]["source_range"],
            "strict_policy": strict_edit_result(mappings, 0, len(TEXT)),
        },
        "cross_segment_edit": {
            "generated_range": [cross_start, cross_end],
            "fallback_candidates": cross,
            "first_candidate_source_excerpt": SOURCE[slice(*cross[0]["source_range"])],
            "strict_policy": strict_edit_result(mappings, cross_start, cross_end),
        },
        "completion_additional_edits": {
            "main_generated_range": main_edit,
            "additional_generated_ranges": additions,
            "volar_like_kept_source_ranges": volar_like_kept,
            "volar_like_dropped_count": len(additions) - len(volar_like_kept),
            "strict_atomic_candidate_accepted": strict_completion,
        },
    }
    path = Path(__file__).with_name("projection-results.json")
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"assertions": "passed", "results": str(path),
                      "ambiguous_candidates": len(ambiguous),
                      "cross_candidates": len(cross),
                      "dropped_additional_edits": len(additions) - len(volar_like_kept)}, sort_keys=True))


if __name__ == "__main__":
    main()
