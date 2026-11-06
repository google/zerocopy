#!/usr/bin/env python3
"""Predeclare byte-grounded item ranges and competing column hypotheses."""

import hashlib
import json
from pathlib import Path
import unicodedata

HERE = Path(__file__).resolve().parent
RAW = (HERE / "fixture/generated_template.rs").read_bytes()
assert RAW.count(b"\r\n") == 6 and RAW.count(b"\n") == 6
TEXT = RAW.decode("utf-8")
LINES = TEXT.splitlines(keepends=True)
assert len(LINES) == 6 and all(line.endswith("\r\n") for line in LINES)


def coordinate(index):
    prefix = TEXT[:index]
    line = prefix.count("\n") + 1
    segment = prefix.rsplit("\n", 1)[-1]
    return line, segment


def columns(segment):
    result = {
        "utf8_bytes": len(segment.encode("utf-8")),
        "unicode_scalars": len(segment),
        "utf16_code_units": len(segment.encode("utf-16-le")) // 2,
    }
    for mode in ("tab_one", "tab_fixed_four", "tab_fixed_eight", "tab_stop_four", "tab_stop_eight"):
        col = 0
        for char in segment:
            if char == "\t":
                if mode == "tab_one":
                    col += 1
                elif mode == "tab_fixed_four":
                    col += 4
                elif mode == "tab_fixed_eight":
                    col += 8
                elif mode == "tab_stop_four":
                    col += 4 - col % 4
                else:
                    col += 8 - col % 8
            elif unicodedata.combining(char):
                col += 0
            elif unicodedata.east_asian_width(char) in ("W", "F"):
                col += 2
            else:
                col += 1
        result[mode] = col
    return result


def item(name, start_anchor, end_anchor):
    assert TEXT.count(start_anchor) == TEXT.count(end_anchor) == 1
    start = TEXT.index(start_anchor)
    end = TEXT.index(end_anchor) + len(end_anchor)
    assert start < end
    begin_line, begin_segment = coordinate(start)
    end_line, end_segment = coordinate(end)
    return {
        "name": name,
        "source_text": TEXT[start:end],
        "source_utf8_sha256": hashlib.sha256(TEXT[start:end].encode("utf-8")).hexdigest(),
        "begin": {"line": begin_line, "columns": columns(begin_segment)},
        "end": {"line": end_line, "columns": columns(end_segment)},
        "scalar_range": [start, end],
        "byte_range": [len(TEXT[:start].encode("utf-8")), len(TEXT[:end].encode("utf-8"))],
    }


data = {
    "schema": 1,
    "source_sha256": hashlib.sha256(RAW).hexdigest(),
    "source_bytes": len(RAW),
    "source_line_ending": "CRLF",
    "items": [
        item("generated_span_probe::PREFIX", "pub const PREFIX", '"😀é";'),
        item("generated_span_probe::after_prefix", "pub fn after_prefix", "{ 1 }"),
        item("generated_span_probe::tabbed_multiline", "pub fn tabbed_multiline", "\t}"),
        item("generated_span_probe::AFTER", "pub const AFTER", '"é";'),
    ],
}
assert [row["name"] for row in data["items"]] == [
    "generated_span_probe::PREFIX", "generated_span_probe::after_prefix",
    "generated_span_probe::tabbed_multiline", "generated_span_probe::AFTER"]
(HERE / "predeclared.json").write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({"source_sha256": data["source_sha256"],
                  "items": [(row["name"], row["begin"], row["end"])
                            for row in data["items"]]}, ensure_ascii=False))
