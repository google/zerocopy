#!/usr/bin/env python3
"""Data-only preflight; never compiles, links, runs or emulates a target."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def main():
    data = json.loads((ROOT / "expected.json").read_text())
    controls = json.loads((ROOT / "controls-proposed.json").read_text())
    checks = []

    def check(name, ok):
        checks.append({"id": name, "pass": bool(ok)})
        if not ok:
            raise SystemExit("Preparation disagreement: " + name)

    # Recover a product using independent byte-column schoolbook arithmetic.
    # This differs from the producer's direct unbounded a*b expression.
    for i, (a, b, lo, hi) in enumerate(data["multiply"]):
        aa = [(a >> (8 * j)) & 255 for j in range(8)]
        bb = [(b >> (8 * j)) & 255 for j in range(8)]
        columns = [0] * 17
        for j in range(8):
            for k in range(8):
                columns[j + k] += aa[j] * bb[k]
        for j in range(16):
            columns[j + 1] += columns[j] // 256
            columns[j] %= 256
        result = sum(x << (8 * j) for j, x in enumerate(columns[:16]))
        check(f"multiply-byte-columns-{i}", result == lo + (hi << 64) and columns[16] == 0)
    for i, (al, ah, bl, bh, lo, hi, carry) in enumerate(data["add128"]):
        first = al + bl
        second = ah + bh + (first >> 64)
        check(f"add128-limbs-{i}", (first & ((1 << 64) - 1),
              second & ((1 << 64) - 1), second >> 64) == (lo, hi, carry))
    for i, (a, b, c, lo, carry) in enumerate(data["carry"]):
        check(f"carry-reconstruction-{i}", c in (0, 1) and carry in (0, 1) and
              lo + (carry << 64) == a + b + c)
    for i, (a, rev) in enumerate(data["swap"]):
        check(f"swap-byte-sequences-{i}", a.to_bytes(8, "big") == rev.to_bytes(8, "little"))
    for i, (a, b, out) in enumerate(data["helper"]):
        bits = f"{a:064b}"
        rotated = int(bits[13:] + bits[:13], 2)
        n = (rotated ^ ((b * 0x9e3779b185ebca87) & ((1 << 64) - 1))) + 1
        check(f"helper-bitstring-rotation-{i}", out == (n & ((1 << 64) - 1)))
    for i, j, out in data["simd_add"]:
        check(f"lane-add-{i}-{j}", len(out) == 16 and all(
            (x + y - z) in (0, 256) for x, y, z in
            zip(data["vectors16"][i], data["vectors16"][j], out)))

    for c in controls:
        ident = c["id"]
        if ident in ("short-load-span", "short-simd-span"):
            check(ident, c["available"] < c["width"])
        elif ident == "misaligned-simd":
            check(ident, c["address_mod_alignment"] != 0)
        elif ident == "overlapping-copy":
            check(ident, max(c["src"][0], c["dst"][0]) < min(c["src"][1], c["dst"][1]))
        elif ident == "outside-pointer-result":
            check(ident, c["offset"] > c["region_size"])
        elif ident == "bad-carry-input":
            check(ident, c["carry"] not in (0, 1))
        elif ident == "omit-upper-product":
            check(ident, c["correct_hi"] == (c["a"] * c["b"]) >> 64 and
                  c["wrong_hi"] != c["correct_hi"])
        elif ident == "omit-carry-propagation":
            check(ident, c["wrong"] != c["correct"] and c["correct"] == [0, 1, 0])
        elif ident == "signed-saturating-byte-add":
            check(ident, c["correct"] == (c["a"] + c["b"]) % 256 and
                  c["wrong"] != c["correct"])
        elif ident == "unrecorded-hidden-read":
            # Detects unequal declared intervals, not actual machine reads.
            check(ident, c["declared_reads"] != c["changed_reads"])
        else:
            check(ident + "-pending-not-faked", c["status"].startswith("no "))
    check("expected-target-check-count", 1 + 289 * 2 + 144 * 2 + 578 * 3 +
          17 * 5 + 17 * 5 + 12 * (4 + 17) + 144 * 3 + 289 * 4 + 6 == 4617)
    check("both-architectures-ten-functions", all(
        (ROOT / arch).read_text().count(".global pilot_") == 10
        for arch in ("aarch64.s", "x86_64.s")))
    result = {
        "status": "preparation-data-checks-only", "subject_compiled": False,
        "subject_executed": False, "checks_passed": len(checks), "checks": checks,
        "inputs": {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
                   for name in ("prepare_oracles.py", "expected.json", "vectors.rs",
                                "controls-proposed.json", "pilot.rs", "aarch64.s",
                                "x86_64.s", "check_preparation.py")},
        "limits": "Owned unverified Python data checker; no ISA/Rust/provenance theorem; future object/result controls unperformed."
    }
    (ROOT / "preparation-checks.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "checks"}))


if __name__ == "__main__":
    main()
