#!/usr/bin/env python3
"""Executable DRAFT word counter: Python Unicode whitespace splitting, version 1."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ALGORITHM_ID = "unicode-whitespace-runs-python-v1"


def count_words(data: bytes) -> int:
    """Decode strict UTF-8 and count maximal non-whitespace runs via str.split()."""

    return len(data.decode("utf-8", errors="strict").split())


def receipt(path: Path, cap: int) -> dict[str, object]:
    if type(cap) is not int or cap < 1:
        raise ValueError("word cap must be a positive integer")
    data = path.read_bytes()
    count = count_words(data)
    return {
        "schema_version": 1,
        "status": "COUNTED",
        "algorithm_id": ALGORITHM_ID,
        "report_sha256": hashlib.sha256(data).hexdigest(),
        "word_count": count,
        "word_cap": cap,
        "valid": count <= cap,
    }


def self_test() -> None:
    cases = {
        b"": 0,
        b"one two\nthree": 3,
        "alpha\u00a0beta\tem dash—stays".encode("utf-8"): 4,
        "标识 符".encode("utf-8"): 2,
        b"```rust\nfn main() {}\n```": 5,
    }
    for data, expected in cases.items():
        actual = count_words(data)
        if actual != expected:
            raise AssertionError(f"word-count mismatch: {data!r}: {actual} != {expected}")
    try:
        count_words(b"\xff")
    except UnicodeDecodeError:
        pass
    else:
        raise AssertionError("invalid UTF-8 was accepted")
    print("DRAFT word counter self-test passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    subcommands.add_parser("self-test")
    count = subcommands.add_parser("count")
    count.add_argument("report", type=Path)
    count.add_argument("--cap", type=int, required=True)
    args = parser.parse_args()
    if args.command == "self-test":
        self_test()
    else:
        print(json.dumps(receipt(args.report, args.cap), sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
