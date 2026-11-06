#!/usr/bin/env python3
"""Read-only verification of this frozen evidence projection, not tool replay."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise SystemExit("REJECT: " + message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def parse_run(path, arch, endian, keys):
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    require(all(x.startswith(("META ", "CHECK ", "OBS ", "CHOICE ", "SUMMARY ")) for x in lines), "unknown output line")
    pairs = []
    for line in lines:
        if line.startswith("CHECK "):
            match = re.fullmatch(r"CHECK ([A-Za-z0-9_.]+)=(PASS|FAIL)", line)
            require(match is not None, "malformed CHECK")
            pairs.append(match.groups())
    require(len(pairs) == len(set(x[0] for x in pairs)), "duplicate CHECK key")
    require([x[0] for x in pairs] == keys, "missing, reordered or extra CHECK")
    require(all(x[1] == "PASS" for x in pairs), "failed CHECK")
    require([x for x in lines if x.startswith("SUMMARY ")] == ["SUMMARY checks=78 failures=0"], "summary")
    meta_pairs = [x[5:].split("=", 1) for x in lines if x.startswith("META ")]
    require(len(meta_pairs) == len(dict(meta_pairs)), "duplicate META")
    require(dict(meta_pairs) == {"suite": "valid-target-v1", "arch": arch, "os": "linux", "endian": endian, "pointer_bits": "64", "debug_assertions": "true"}, "target metadata")
    choices = dict(x[7:].split("=", 1) for x in lines if x.startswith("CHOICE "))
    expected = {"float.f32.arithmetic_nan_bits": (32, 0x7f800000, 0x007fffff), "float.f64.arithmetic_nan_bits": (64, 0x7ff0000000000000, 0x000fffffffffffff), "float.f64_to_f32.nan_bits": (32, 0x7f800000, 0x007fffff)}
    require(set(choices) == set(expected), "NaN choice key set")
    for name, (width, exponent, payload) in expected.items():
        value = int(choices[name], 16)
        require(0 <= value < (1 << width) and value & exponent == exponent and value & payload != 0, "NaN class")
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", required=True, type=Path, help="caller-selected frozen package directory")
    args = parser.parse_args()
    root = args.package.resolve(strict=True)
    manifest = json.loads((root / "package-manifest.json").read_text())
    listed = set()
    for item in manifest["files"]:
        rel = Path(item["path"])
        require(not rel.is_absolute() and ".." not in rel.parts and str(rel) not in listed, "manifest path")
        listed.add(str(rel))
        path = root / rel
        require(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root), "file identity")
        raw = path.read_bytes()
        require(len(raw) == item["bytes"] and digest(raw) == item["sha256"], "manifest bytes: " + str(rel))
    actual = {str(x.relative_to(root)) for x in root.rglob("*") if x.is_file()}
    require(actual == listed | {"package-manifest.json"}, "unlisted/missing file")
    for item in json.loads((root / "normalization-receipts.json").read_text())["files"]:
        current = (root / item["public"]).read_bytes()
        require(digest(current) == item["public_sha256"] and len(current) == item["public_bytes"], "projection receipt")
    prepared = json.loads((root / "preparation-manifest.json").read_text())
    for item in prepared["files"]:
        path = root / ("fixture/" + item["path"] if item["path"].endswith(".rs") else item["path"])
        require(digest(path.read_bytes()) == item["sha256"], "prepared input changed")
    keys = json.loads((root / "observed-check-keys.json").read_text())["keys"]
    require(len(keys) == len(set(keys)) == 78, "finite key set")
    native = parse_run(root / "captures/27-run-native.stdout", "aarch64", "little", keys)
    big = parse_run(root / "captures/28-run-big.stdout", "s390x", "big", keys)
    for label in ["22-compile-native", "23-compile-big", "27-run-native", "28-run-big"]:
        require(json.loads((root / ("captures/" + label + ".json")).read_text())["exit_code"] == 0, "process status")
        require((root / ("captures/" + label + ".stderr")).stat().st_size == 0, "process stderr")
    comparison = json.loads((root / "comparison.json").read_text())
    require(len(native) == len(big) == comparison["line_count_each"], "line count")
    diff = [{"native": a, "big": b} for a, b in zip(native, big) if a != b]
    require(diff == comparison["different_lines"] and len(diff) == 4, "frozen comparison")
    print("PASS: frozen package bytes, pre-execution inputs, statuses, 78 finite checks per subject, NaN-class oracles, and four recorded cross-target differences")
    print("Scope: evidence consistency only; no compiler/emulator execution, source-safety proof, E49 theorem, or new target applicability")


if __name__ == "__main__":
    main()
