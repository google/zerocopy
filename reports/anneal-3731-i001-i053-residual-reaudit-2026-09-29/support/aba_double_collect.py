#!/usr/bin/env python3
"""Deterministic APFS pointer-ABA counterexample for an unfenced double collect."""
import argparse
import hashlib
import json
import os
import tempfile
from pathlib import Path


def digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def run(scratch: Path) -> dict:
    events = []
    with tempfile.TemporaryDirectory(prefix="aba-double-collect-", dir=scratch) as tmp:
        root = Path(tmp)
        for generation in ("A", "B"):
            folder = root / generation
            folder.mkdir()
            for name in ("x", "y"):
                (folder / name).write_bytes(f"{generation}-{name}\n".encode())
        pointer = root / "current"

        def select(generation: str) -> None:
            replacement = root / "next"
            replacement.symlink_to(generation, target_is_directory=True)
            os.replace(replacement, pointer)
            events.append({"operation": "select", "generation": generation})

        def read(name: str) -> dict:
            selected = os.readlink(pointer)
            value = (pointer / name).read_bytes()
            event = {"operation": "read", "name": name, "selected_before_open": selected,
                     "value": value.decode(), "sha256": digest(value)}
            events.append(event)
            return {"name": name, "value": value.decode(), "sha256": digest(value)}

        select("A")
        first = [read("x")]
        select("B")
        first.append(read("y"))
        select("A")
        second = [read("x")]
        select("B")
        second.append(read("y"))
        naive_accepts = first == second
        select("A")
        pinned_generation = os.readlink(pointer)
        pinned = [(root / pinned_generation / name).read_bytes().decode() for name in ("x", "y")]
        expected = {g: [(root / g / name).read_bytes().decode() for name in ("x", "y")]
                    for g in ("A", "B")}
        assert first == second
        assert [item["value"] for item in first] not in expected.values()
        assert pinned == expected[pinned_generation]
        return {
            "fixture": "two immutable directories selected by atomic relative symlink replacement",
            "filesystem": "APFS on macOS 26.6.2 arm64",
            "first_collect": first,
            "second_collect": second,
            "unfenced_equal_collects_accept": naive_accepts,
            "complete_generations": expected,
            "mixed_collect_equal_to_complete_generation": [item["value"] for item in first] in expected.values(),
            "pinned_generation": pinned_generation,
            "pinned_values": pinned,
            "events": events,
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scratch", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if not args.scratch.is_dir():
        parser.error("--scratch must be an existing directory")
    result = run(args.scratch)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("PASS: two identical mixed full collects accepted; pinned generation remained coherent")


if __name__ == "__main__":
    main()
