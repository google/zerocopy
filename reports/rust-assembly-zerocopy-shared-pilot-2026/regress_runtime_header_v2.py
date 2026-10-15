"""Pure-data regression over retained actual library header records; no Docker."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent
OLD = ROOT / "runtime-captures-v1/aarch64-O0-positive-before-files.stdout"
STATIC = ROOT / "compile-static/inspection/runtime-library-files-read-only.stdout"
POLICY = ROOT / "runtime-capture-policy.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    old = json.loads(OLD.read_text())["runtime_libraries"]
    retained = json.loads(STATIC.read_text())
    expected = json.loads(POLICY.read_text())["runtime_library_files"]
    if len(old) != 7 or retained != expected:
        raise SystemExit("Retained header regression input identity/domain disagreement")
    rows = []
    for original, truncated, wanted in zip(retained, old, expected):
        raw = bytes.fromhex(original["ELF_identity"])
        if len(raw) != 20 or len(bytes.fromhex(truncated["ELF_identity"])) != 18:
            raise SystemExit("Unexpected retained header width")
        without_header = lambda x: {k: v for k, v in x.items() if k != "ELF_identity"}
        if without_header(original) != without_header(truncated):
            raise SystemExit("Unexpected non-header record difference")
        machine = bytearray(raw)
        machine[18] ^= 1
        early = bytearray(raw)
        early[0] ^= 1
        candidates = [
            ("old-18-reject", dict(truncated), False),
            ("exact-20-accept", dict(truncated, ELF_identity=raw.hex()), True),
            ("changed-e_machine-reject", dict(truncated, ELF_identity=bytes(machine).hex()), False),
            ("changed-earlier-byte-reject", dict(truncated, ELF_identity=bytes(early).hex()), False),
        ]
        for name, candidate, desired in candidates:
            accepted = candidate == wanted
            rows.append({"path": original["path"], "control": name,
                         "candidate_ELF_identity": candidate["ELF_identity"],
                         "accepted": accepted, "expected_acceptance": desired,
                         "pass": accepted == desired})
    if not all(row["pass"] for row in rows):
        raise SystemExit("Header-record admission regression disagreement")
    report = {"status": "pure-data-header-record-regression-passed",
              "checks_passed": len(rows), "checks": rows,
              "inputs": [{"path": str(p.relative_to(ROOT)), "sha256": digest(p)}
                         for p in [OLD, STATIC, POLICY]],
              "actual_static_header_bytes": 20, "failed_reader_header_bytes": 18,
              "target_or_docker_invoked": False, "mutant_executed": False,
              "limit": "Exact retained record equality only; no instruction semantics or new target observation."}
    with (ROOT / "runtime-header-v2-regression.json").open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({"checks_passed": len(rows), "target_or_docker_invoked": False}))


if __name__ == "__main__":
    main()
