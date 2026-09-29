#!/usr/bin/env python3
"""Illustrative piecewise projection properties; not Anneal's parser or generator."""

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import platform
import random
import sys


SEED = 0x3730029
STEPS = 800
PREFIX = "//| "
HEADER = "namespace Generated\n"
FOOTER = "\nend Generated\n"
OUT = Path(__file__).with_name("raw-results.json")


def digest(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def byte_offset(s, char_index):
    return len(s[:char_index].encode("utf-8"))


@dataclass(frozen=True)
class Segment:
    source_start: int
    source_end: int
    projected_start: int
    projected_end: int

    def as_list(self):
        return [self.source_start, self.source_end, self.projected_start, self.projected_end]


@dataclass(frozen=True)
class Projection:
    text: str
    segments: tuple[Segment, ...]


def project_full(host):
    pieces = [HEADER]
    segments = []
    source_at = 0
    projected_at = len(HEADER.encode("utf-8"))
    for line in host.splitlines(keepends=True):
        line_bytes = len(line.encode("utf-8"))
        if line.startswith(PREFIX):
            payload = line[len(PREFIX):]
            payload_bytes = len(payload.encode("utf-8"))
            segments.append(Segment(source_at + len(PREFIX), source_at + line_bytes,
                                    projected_at, projected_at + payload_bytes))
            pieces.append(payload)
            projected_at += payload_bytes
        source_at += line_bytes
    pieces.append(FOOTER)
    return Projection("".join(pieces), tuple(segments))


def authored_range(projection, start, end):
    """Return exact source bytes only for one authored segment.

    Insertions on segment borders are rejected, because ownership there is
    ambiguous with synthetic text or a neighboring source segment.
    """
    if start < 0 or end < start or end > len(projection.text.encode("utf-8")):
        return None
    for seg in projection.segments:
        if start == end:
            if seg.projected_start < start < seg.projected_end:
                return seg.source_start + start - seg.projected_start, seg.source_start + end - seg.projected_start
        elif seg.projected_start <= start and end <= seg.projected_end:
            return seg.source_start + start - seg.projected_start, seg.source_start + end - seg.projected_start
    return None


def line_entries(text):
    entries = []
    offset = 0
    for raw in text.splitlines(keepends=True):
        if raw.endswith("\r\n"):
            content = raw[:-2]
        elif raw.endswith("\n") or raw.endswith("\r"):
            content = raw[:-1]
        else:
            content = raw
        entries.append((offset, content))
        offset += len(raw.encode("utf-8"))
    if not entries or text.endswith("\n") or text.endswith("\r"):
        entries.append((offset, ""))
    return entries


def byte_to_coords(text, byte):
    for line, (start, content) in enumerate(line_entries(text)):
        prefix = ""
        for scalar_col in range(len(content) + 1):
            at = start + len(prefix.encode("utf-8"))
            if at == byte:
                return (line, scalar_col, len(prefix.encode("utf-16-le")) // 2)
            if scalar_col < len(content):
                prefix += content[scalar_col]
    return None


def utf16_to_byte(text, line, utf16_col):
    entries = line_entries(text)
    if not (0 <= line < len(entries)) or utf16_col < 0:
        return None
    start, content = entries[line]
    units = 0
    offset = start
    for char in content:
        if units == utf16_col:
            return offset
        units += len(char.encode("utf-16-le")) // 2
        offset += len(char.encode("utf-8"))
        if units > utf16_col:
            return None  # interior of a UTF-16 surrogate pair
    return offset if units == utf16_col else None


def coordinate_probe():
    rng = random.Random(SEED)
    specimens = ["", "a", "é🙂a\u0301\t界", "x\r\ny", "🙂\n", "\t\r\n\u0301"]
    alphabet = ["a", "é", "🙂", "\u0301", "\t", "界", "0"]
    for _ in range(100):
        lines = ["".join(rng.choice(alphabet) for _ in range(rng.randrange(0, 20)))
                 for _ in range(rng.randrange(1, 6))]
        specimens.append(rng.choice(["\n", "\r\n"]).join(lines))
    checked = 0
    units_differ = 0
    for specimen in specimens:
        for line, (start, content) in enumerate(line_entries(specimen)):
            for col in range(len(content) + 1):
                byte = start + byte_offset(content, col)
                coords = byte_to_coords(specimen, byte)
                assert coords is not None and coords[:2] == (line, col)
                assert utf16_to_byte(specimen, line, coords[2]) == byte
                checked += 1
                if byte - start != coords[2] or coords[1] != coords[2]:
                    units_differ += 1
    # Negative controls: an interior surrogate unit and an interior UTF-8 byte.
    assert utf16_to_byte("🙂", 0, 1) is None
    assert byte_to_coords("é", 1) is None
    return {"specimens": len(specimens), "valid_boundaries": checked,
            "numeric_unit_differences": units_differ,
            "mid_surrogate_rejected": True, "mid_utf8_rejected": True,
            "sample": {"text": "é🙂a\u0301\t界", "after_emoji": byte_to_coords("é🙂a\u0301\t界", len("é🙂".encode("utf-8")))}}


def apply_projected_patch(host, projection, version, patch):
    if version != patch["version"] or digest(host) != patch["host_hash"] or digest(projection.text) != patch["projected_hash"]:
        return None, "stale-snapshot"
    source_range = authored_range(projection, patch["start"], patch["end"])
    if source_range is None:
        return None, "not-exactly-editable"
    lo, hi = source_range
    original = host.encode("utf-8")
    if original[lo:hi] != patch["expected"].encode("utf-8"):
        return None, "expected-bytes-mismatch"
    updated = original[:lo] + patch["replacement"].encode("utf-8") + original[hi:]
    return updated.decode("utf-8"), "applied"


def patch_probe():
    host = "fn f() {}\r\n//| theorem demo : True := by\r\n//|   trivial\r\n"
    projection = project_full(host)
    needle = "trivial"
    start = projection.text.encode("utf-8").index(needle.encode("utf-8"))
    patch = {"version": 7, "host_hash": digest(host), "projected_hash": digest(projection.text),
             "start": start, "end": start + len(needle), "expected": needle,
             "replacement": "exact True.intro"}
    applied, status = apply_projected_patch(host, projection, 7, patch)
    assert status == "applied" and applied is not None
    assert "exact True.intro" in project_full(applied).text
    moved_host = "// unrelated\n" + host
    moved, stale = apply_projected_patch(moved_host, projection, 7, patch)
    assert moved is None and stale == "stale-snapshot"
    same_host_new_projection = Projection("-- changed wrapper\n" + projection.text, projection.segments)
    _, projected_stale = apply_projected_patch(host, same_host_new_projection, 7, patch)
    assert projected_stale == "stale-snapshot"
    _, version_stale = apply_projected_patch(host, projection, 8, patch)
    assert version_stale == "stale-snapshot"
    synthetic_start = projection.text.encode("utf-8").index(b"namespace")
    synthetic = authored_range(projection, synthetic_start, synthetic_start + len("namespace"))
    assert synthetic is None
    first, second = projection.segments[:2]
    crossing = authored_range(projection, first.projected_end - 1, second.projected_start + 1)
    assert crossing is None
    border_insertion = authored_range(projection, first.projected_start, first.projected_start)
    assert border_insertion is None
    # The old offset still points somewhere plausible after an unrelated insert.
    naive_offset = authored_range(projection, start, start + len(needle))
    assert naive_offset is not None
    naive_bytes = moved_host.encode("utf-8")
    naive_corruption = (naive_bytes[:naive_offset[0]] + b"exact True.intro" + naive_bytes[naive_offset[1]:]).decode("utf-8")
    assert naive_corruption != "// unrelated\n" + applied
    return {"normal_apply": status, "host_edit": stale, "projection_edit": projected_stale,
            "version_change": version_stale, "synthetic_rejected": synthetic is None,
            "cross_segment_rejected": crossing is None, "border_insertion_rejected": border_insertion is None,
            "naive_old_offset_corrupts": naive_corruption != "// unrelated\n" + applied,
            "original_host": host, "original_projection": projection.text,
            "segment_map": [s.as_list() for s in projection.segments]}


def incremental_or_full(host, projection, char_start, char_end, replacement):
    lo, hi = byte_offset(host, char_start), byte_offset(host, char_end)
    deleted = host[char_start:char_end]
    new_host = host[:char_start] + replacement + host[char_end:]
    if (any(c in deleted + replacement for c in "\r\n")
            or (char_start > 0 and host[char_start - 1] in "\r\n")
            or (char_end < len(host) and host[char_end] in "\r\n")):
        return new_host, project_full(new_host), "full"
    targets = [i for i, s in enumerate(projection.segments) if s.source_start < lo <= hi < s.source_end]
    if len(targets) != 1:
        return new_host, project_full(new_host), "full"
    index = targets[0]
    segment = projection.segments[index]
    p_lo = segment.projected_start + lo - segment.source_start
    p_hi = segment.projected_start + hi - segment.source_start
    old_projected = projection.text.encode("utf-8")
    replacement_bytes = replacement.encode("utf-8")
    new_projected = (old_projected[:p_lo] + replacement_bytes + old_projected[p_hi:]).decode("utf-8")
    delta = len(replacement_bytes) - (hi - lo)
    segments = []
    for i, s in enumerate(projection.segments):
        if i < index:
            segments.append(s)
        elif i == index:
            segments.append(Segment(s.source_start, s.source_end + delta,
                                    s.projected_start, s.projected_end + delta))
        else:
            segments.append(Segment(s.source_start + delta, s.source_end + delta,
                                    s.projected_start + delta, s.projected_end + delta))
    return new_host, Projection(new_projected, tuple(segments)), "incremental"


def newline_boundary_probe():
    host = "//| a\r\n"
    projection = project_full(host)
    at = host.index("\n")
    new_host = host[:at] + "é" + host[at:]
    splice_at = projection.text.encode("utf-8").index(b"\n", len(HEADER.encode("utf-8")))
    projected_bytes = projection.text.encode("utf-8")
    unsafe_splice = (projected_bytes[:splice_at] + "é".encode("utf-8") + projected_bytes[splice_at:]).decode("utf-8")
    full = project_full(new_host)
    assert unsafe_splice != full.text
    result_host, guarded, mode = incremental_or_full(host, projection, at, at, "é")
    assert result_host == new_host and guarded == full and mode == "full"
    return {"host_before": host, "host_after": new_host, "unsafe_projected": unsafe_splice,
            "regenerated_projected": full.text, "unsafe_splice_differs": True,
            "guarded_mode": mode}


def random_edit_probe():
    rng = random.Random(SEED + 1)
    host = "fn α() { let s = \"🙂\"; }\r\n//| theorem first : True := by\r\n//|   trivial\r\nfn β() {}\n//| theorem second : True := by\n//|   trivial\n"
    initial_host = host
    projection = project_full(host)
    trace = []
    modes = {"incremental": 0, "full": 0}
    alphabet = ["a", "é", "🙂", "\u0301", "\t", "界", "_", "", "\n", "\r\n", "//| "]
    for step in range(STEPS):
        chosen = None
        if projection.segments and rng.random() < 0.65:
            segment = rng.choice(projection.segments)
            candidates = [i for i in range(len(host) + 1)
                          if segment.source_start < byte_offset(host, i) < segment.source_end]
            if candidates:
                at = rng.choice(candidates)
                chosen = (at, at, rng.choice(alphabet[:8]))
        if chosen is None:
            at = rng.randrange(len(host) + 1)
            end = min(len(host), at + rng.randrange(0, 3))
            chosen = (at, end, rng.choice(alphabet))
        start, end, replacement = chosen
        host, projection, mode = incremental_or_full(host, projection, start, end, replacement)
        ground_truth = project_full(host)
        assert projection == ground_truth, (step, mode, chosen, host,
                                            projection.text, ground_truth.text,
                                            [s.as_list() for s in projection.segments],
                                            [s.as_list() for s in ground_truth.segments])
        modes[mode] += 1
        trace.append({"step": step, "char_range": [start, end], "replacement": replacement,
                      "mode": mode, "host_sha256": digest(host),
                      "projection_sha256": digest(projection.text),
                      "segments": [s.as_list() for s in projection.segments],
                      "matches_full_regeneration": True})
    # Comparator sensitivity: deliberately shift a map endpoint by one byte.
    if ground_truth.segments:
        first = ground_truth.segments[0]
        corrupted = Projection(ground_truth.text, (Segment(first.source_start + 1, first.source_end,
                                                          first.projected_start, first.projected_end),)
                               + ground_truth.segments[1:])
        assert corrupted != ground_truth
    else:
        corrupted = Projection(ground_truth.text + "x", ground_truth.segments)
        assert corrupted != ground_truth
    return {"seed": SEED + 1, "steps": STEPS, "mode_counts": modes,
            "initial_host": initial_host, "final_host": host,
            "final_projection": projection.text,
            "injected_corruption_detected": corrupted != ground_truth,
            "trace": trace}


def main():
    output = {"environment": {"python": sys.version, "platform": platform.platform(),
                              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
              "coordinates": coordinate_probe(), "patches": patch_probe(),
              "newline_boundary": newline_boundary_probe(),
              "edit_stream": random_edit_probe()}
    OUT.write_text(json.dumps(output, indent=2, ensure_ascii=False, sort_keys=True) + "\n")
    print(json.dumps({"valid_boundaries": output["coordinates"]["valid_boundaries"],
                      "steps": STEPS, "mode_counts": output["edit_stream"]["mode_counts"],
                      "corruption_detected": output["edit_stream"]["injected_corruption_detected"]},
                     sort_keys=True))


if __name__ == "__main__":
    main()
