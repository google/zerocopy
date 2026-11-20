#!/usr/bin/env python3
"""Supplement the kernel axiom audit with a narrow source-level failure lint.

Lean panic/default-returning collection access is not a faithful encoding of a
Rust panic. Reject those constructs in semantic code; use explicit outcomes or
proved bounds. This is a supplementary lint, not a soundness/completeness proof.
"""
import argparse
from pathlib import Path
import re


def code_only(text):
    out = list(text)
    pos, depth, string = 0, 0, False
    while pos < len(text):
        if depth:
            if text.startswith("/-", pos):
                depth += 1
                out[pos:pos + 2] = "  "
                pos += 2
            elif text.startswith("-/", pos):
                depth -= 1
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif string:
            if text[pos] == "\\" and pos + 1 < len(text):
                out[pos:pos + 2] = "  "
                pos += 2
            else:
                if text[pos] == '"':
                    string = False
                if text[pos] != "\n":
                    out[pos] = " "
                pos += 1
        elif text.startswith("/-", pos):
            depth = 1
            out[pos:pos + 2] = "  "
            pos += 2
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            if end < 0:
                end = len(text)
            out[pos:end] = " " * (end - pos)
            pos = end
        elif text[pos] == '"':
            string = True
            out[pos] = " "
            pos += 1
        else:
            pos += 1
    return "".join(out)


PATTERN = re.compile(r"\b(?:panic!|unreachable!|get!|set!)|\]\s*!|\bunsafe\s+(?:def|theorem|axiom)\b")


def violations(text):
    stripped = code_only(text)
    return [(stripped.count("\n", 0, match.start()) + 1, match.group())
            for match in PATTERN.finditer(stripped)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    found = []
    for path in sorted((args.root / "Miri").rglob("*.lean")):
        for line, match in violations(path.read_text()):
            found.append(f"{path.relative_to(args.root)}:{line}: default-returning/unsafe construct {match!r}")
    if found:
        print("\n".join(found))
        return 1
    print("Semantic-source lint passed: no panic/default-returning unsafe access constructs.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
