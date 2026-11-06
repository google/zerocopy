#!/usr/bin/env python3
"""Offline integrity check for the I094 Lake consumer/server comparison."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(path):
    return json.loads(path.read_text())


def parse_frames(text):
    data = text.encode()
    out, pos = [], 0
    while pos < len(data):
        end = data.find(b"\r\n\r\n", pos)
        assert end >= 0, f"invalid LSP header at byte {pos}"
        m = re.search(rb"(?im)^Content-Length:\s*(\d+)\s*$", data[pos:end])
        assert m, f"missing Content-Length at byte {pos}"
        n = int(m.group(1))
        start = end + 4
        body = data[start:start + n]
        assert len(body) == n, f"incomplete LSP body at byte {pos}"
        out.append(json.loads(body))
        pos = start + n
    return out


def main():
    identity = read(ROOT / "identity.json")
    metadata = read(ROOT / "REPORT.json")
    for version in ("4.30.0-rc2", "4.34.1"):
        ident = identity[version]
        subject = next(s["identity"] for s in metadata["subjects"] if s["name"].endswith(version))
        assert ident["lean_sha256"] == subject["lean_sha256"]
        assert ident["lake_sha256"] == subject["lake_sha256"]
        before = read(ROOT / f"snap-{version}-before.json")
        after = read(ROOT / f"snap-{version}-after.json")
        final = read(ROOT / f"snap-{version}-final.json")
        assert before == after == final, f"read-only producer changed at {version}"

    runs = [json.loads(line) for line in (ROOT / "runs.jsonl").read_text().splitlines()]
    assert len(runs) == 18, f"expected 18 guarded Lake commands, got {len(runs)}"
    expected = {
        (v, label): code
        for v, codes in {
            "4.30.0-rc2": [0, 0, 0, 0, 0, 0, 1, 1, 1],
            "4.34.1": [0, 0, 0, 0, 0, 0, 0, 0, 0],
        }.items()
        for label, code in zip(
            ["producer-build", "consumer-initial-build", "seeded-no-build-dep",
             "seeded-consumer-build", "seeded-setup-file", "seeded-lean-json",
             "unseeded-setup-file", "unseeded-consumer-build", "unseeded-build-first"],
            codes,
        )
    }
    actual = {}
    for run in runs:
        key = (run["version"], run["label"])
        assert key not in actual, f"duplicate run {key}"
        actual[key] = run["exit"]
        assert run["abort"] is None
        assert max(s["rss_kib"] for s in run["samples"]) < 2 * 1024 * 1024
        assert min(s["memory_pressure_free_pct"] for s in run["samples"]) >= 10
        assert min(s["disk_free_bytes"] for s in run["samples"]) > 10 * 1024**3
    assert actual == expected

    server_paths = sorted(ROOT.glob("server-*.json"))
    assert len(server_paths) == 4
    observed = {}
    for path in server_paths:
        record = read(path)
        version = record["version"]
        unseeded = "fresh-server-unseeded" in path.name
        frames = parse_frames(record["wire_out"])
        publications = [f["params"] for f in frames if f.get("method") == "textDocument/publishDiagnostics"]
        values = [d["message"] for p in publications for d in p.get("diagnostics", [])]
        key = (version, unseeded)
        observed[key] = (record["exit"], values)
    assert observed[("4.30.0-rc2", False)][0] == 0
    assert "7" in observed[("4.30.0-rc2", False)][1]
    assert observed[("4.34.1", False)][0] == 0
    assert "7" in observed[("4.34.1", False)][1]
    assert observed[("4.30.0-rc2", True)][0] == 0
    assert "7" not in observed[("4.30.0-rc2", True)][1]
    assert any("permission" in x.lower() or "lakefile.olean.lock" in x
               for x in observed[("4.30.0-rc2", True)][1])
    assert observed[("4.34.1", True)][0] == 0
    assert "7" in observed[("4.34.1", True)][1]
    print("PASS: identities, producer snapshots, 18 guarded commands, and four LSP server transcripts")


if __name__ == "__main__":
    main()
