#!/usr/bin/env python3
"""PREPARATION ONLY: integer/byte data, never compiler or subject execution.

The mathematical oracle uses Python unbounded nonnegative integers and lists;
it does not invoke the Rust baseline, assembler, emulator, or target program.
Write only beside this source. Keep emitted vectors fixed before compilation.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
MASK = (1 << 64) - 1
W = [0, 1, 2, 255, 256, (1 << 31) - 1, 1 << 31,
     (1 << 32) - 1, 1 << 32, (1 << 63) - 1, 1 << 63, MASK - 1,
     MASK, 0x0123456789abcdef, 0xfedcba9876543210,
     0xaaaaaaaaaaaaaaaa, 0x5555555555555555]
Q = [(0, 0), (1, 0), (MASK, 0), (0, 1), (MASK, 1), (0, MASK),
     (MASK, MASK), (MASK - 1, MASK), (1, MASK), (0, 1 << 63),
     (MASK, (1 << 63) - 1), (W[13], W[14])]
V = [[0] * 16, [255] * 16, list(range(16)), list(range(15, -1, -1)),
     [128] * 16, [127] * 16, [170] * 16, [85] * 16,
     [0, 255] * 8, [1 << (i % 8) for i in range(16)],
     [(i * 73 + 19) % 256 for i in range(16)],
     list(b"wire-header-0016")]


def rev64(x):
    # Defined by byte positions rather than the Rust swap_bytes implementation.
    return sum(((x // (256 ** i)) % 256) * (256 ** (7 - i))
               for i in range(8))


def helper(a, b):
    rot = ((a * (1 << 13)) % (1 << 64)) + (a // (1 << 51))
    return ((rot ^ ((b * 0x9e3779b185ebca87) % (1 << 64))) + 1) % (1 << 64)


def emit():
    mul = [(a, b, (a * b) % (1 << 64), (a * b) // (1 << 64))
           for a in W for b in W]
    add = []
    for al, ah in Q:
        for bl, bh in Q:
            n = al + (ah << 64) + bl + (bh << 64)
            add.append((al, ah, bl, bh, n % (1 << 64),
                        (n // (1 << 64)) % (1 << 64), n // (1 << 128)))
    carry = [(a, b, c, (a + b + c) % (1 << 64),
              (a + b + c) // (1 << 64)) for a in W for b in W for c in (0, 1)]
    vectors = {
        "words": W, "multiply": mul, "add128": add, "carry": carry,
        "swap": [(a, rev64(a)) for a in W], "vectors16": V,
        "helper": [(a, b, helper(a, b)) for a in W for b in W],
        "pointer_offsets": list(range(17)),
        "simd_add": [[i, j, [(a + b) % 256 for a, b in zip(x, y)]]
                     for i, x in enumerate(V) for j, y in enumerate(V)],
    }
    lines = ["// Fixed mathematical data. Generated before any target compilation."]
    for name, arity in (("multiply", 4), ("add128", 7), ("carry", 5),
                        ("swap", 2), ("helper", 3)):
        rows = vectors[name]
        lines.append(f"pub const {name.upper()}: [[u64; {arity}]; {len(rows)}] = [")
        lines += ["    [" + ", ".join(f"0x{v:016x}" for v in row) + "],"
                  for row in rows]
        lines.append("];")
    lines.append(f"pub const WORDS: [u64; {len(W)}] = [" +
                 ", ".join(f"0x{x:016x}" for x in W) + "];")
    lines.append(f"pub const VECTORS16: [[u8; 16]; {len(V)}] = [")
    lines += ["    [" + ", ".join(str(x) for x in row) + "]," for row in V]
    lines.append("];")
    rows = vectors["simd_add"]
    lines.append(f"pub const SIMD_ADD: [(usize, usize, [u8; 16]); {len(rows)}] = [")
    lines += [f"    ({i}, {j}, [" + ", ".join(map(str, out)) + "]),"
              for i, j, out in rows]
    lines.append("];")
    vector_bytes = ("\n".join(lines) + "\n").encode()
    (ROOT / "vectors.rs").write_bytes(vector_bytes)
    (ROOT / "expected.json").write_text(json.dumps(vectors, indent=2) + "\n")

    # These are nonexecuted records, not pointers/asm supplied to the target.
    controls = [
        {"id": "short-load-span", "kind": "admission-data", "width": 8,
         "available": 7, "expected": "reject"},
        {"id": "short-simd-span", "kind": "admission-data", "width": 16,
         "available": 15, "expected": "reject"},
        {"id": "misaligned-simd", "kind": "admission-data", "alignment": 16,
         "address_mod_alignment": 1, "expected": "reject"},
        {"id": "overlapping-copy", "kind": "admission-data", "src": [0, 16],
         "dst": [8, 24], "policy": "disjoint", "expected": "reject"},
        {"id": "outside-pointer-result", "kind": "admission-data",
         "region_size": 16, "offset": 17, "expected": "reject"},
        {"id": "bad-carry-input", "kind": "admission-data", "carry": 2,
         "expected": "reject"},
        {"id": "omit-upper-product", "kind": "oracle-data", "a": MASK,
         "b": MASK, "wrong_hi": 0, "correct_hi": MASK - 1,
         "expected": "distinguish"},
        {"id": "omit-carry-propagation", "kind": "oracle-data",
         "a": [MASK, 0], "b": [1, 0], "wrong": [0, 0, 0],
         "correct": [0, 1, 0], "expected": "distinguish"},
        {"id": "signed-saturating-byte-add", "kind": "oracle-data",
         "a": 127, "b": 1, "wrong": 127, "correct": 128,
         "expected": "distinguish"},
        {"id": "unrecorded-hidden-read", "kind": "footprint-data",
         "declared_reads": [[0, 16]], "changed_reads": [[0, 16], [16, 17]],
         "expected": "reject"},
        {"id": "changed-object-byte", "kind": "future-artifact-data",
         "action": "copy extracted function bytes, flip one bit, compare identity",
         "expected": "reject", "status": "no object exists yet"},
        {"id": "wrong-return-or-guard", "kind": "future-result-data",
         "action": "copy observed record, change return or guard, rerun data checker",
         "expected": "reject", "status": "no observed record exists yet"},
    ]
    (ROOT / "controls-proposed.json").write_text(json.dumps(controls, indent=2) + "\n")
    info = {"status": "preparation-data-only", "subject_compiled": False,
            "subject_executed": False, "generator_sha256": hashlib.sha256(
                Path(__file__).read_bytes()).hexdigest(),
            "vectors_sha256": hashlib.sha256(vector_bytes).hexdigest(),
            "case_counts": {k: len(v) for k, v in vectors.items()},
            "oracle": "unbounded integer arithmetic and explicit byte lists"}
    (ROOT / "oracle-preparation.json").write_text(json.dumps(info, indent=2) + "\n")
    print(json.dumps(info))


if __name__ == "__main__":
    emit()
