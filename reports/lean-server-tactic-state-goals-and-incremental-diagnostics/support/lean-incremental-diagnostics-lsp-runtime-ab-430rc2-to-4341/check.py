#!/usr/bin/env python3
"""Offline integrity check for retained Lean LSP and batch evidence."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RAW = ROOT / "raw"


def read_json(path):
    return json.loads(path.read_text())


def sha(data):
    return hashlib.sha256(data).hexdigest()


def frames(data):
    out = []
    pos = 0
    while pos < len(data):
        end = data.find(b"\r\n\r\n", pos)
        assert end >= 0, f"missing LSP header terminator at {pos}"
        header = data[pos:end]
        match = re.search(rb"(?im)^Content-Length:\s*(\d+)\s*$", header)
        assert match, f"missing Content-Length at {pos}"
        length = int(match.group(1))
        start = end + 4
        body = data[start:start + length]
        assert len(body) == length, f"short LSP body at {pos}"
        out.append((json.loads(body), sha(body)))
        pos = start + length
    return out


def main():
    expected = {
        "old-absent", "old-false", "old-true",
        "new-absent", "new-false", "new-true",
    }
    assert {p.name for p in RAW.iterdir() if p.is_dir() and "-" in p.name} >= expected
    for name in sorted(expected):
        d = RAW / name
        summary = read_json(d / "summary.json")
        assert summary["clean"] is True and summary["abort"] is None
        assert summary["peak_rss_kib"] > 0
        assert (d / "server.stderr").read_bytes() == b""
        parsed = frames((d / "server.stdout.lsp").read_bytes())
        events = [json.loads(line) for line in (d / "events.jsonl").read_text().splitlines()]
        server_events = [e for e in events if e["kind"] == "server"]
        server = [e["message"] for e in server_events]
        assert len(parsed) == len(server_events)
        assert summary["event_count"] == len(events)
        for (msg, body_sha), event in zip(parsed, server_events):
            assert msg == event["message"]
            assert body_sha == event["body_sha256"]
        pubs = [m for m in server if m.get("method") == "textDocument/publishDiagnostics"]
        if name == "new-true":
            substantive = [p["params"] for p in pubs if p["params"].get("diagnostics")]
            assert substantive and all(p.get("isIncremental") is False for p in substantive)
            assert not any(p.get("isIncremental") is True for p in (x["params"] for x in pubs))
        elif name.startswith("old-"):
            assert all("isIncremental" not in p["params"] for p in pubs)
    for version in ("old", "new"):
        for fixture in ("open", "edited"):
            d = RAW / f"batch-{version}-{fixture}"
            record = read_json(d / "record.json")
            assert sha((d / "stdout").read_bytes()) == record["stdout_sha256"]
            assert sha((d / "stderr").read_bytes()) == record["stderr_sha256"]
            assert record["returncode"] == 1
    expected_fixture = {
        "Open.lean": "d42fbf3d79611aa442bb233680e4f20af6848dc8f1f0c7be3c3dd4df22b5dcc7",
        "Edited.lean": "9caea97a94d2d9d37a3cb507278414674d173507a0ebf9db9e3c5024dc3ebfeb",
    }
    for name, digest in expected_fixture.items():
        assert sha((ROOT / "support" / "fixture" / name).read_bytes()) == digest
    assert read_json(ROOT / "results.json").keys() >= expected
    print("PASS: fixtures, six framed LSP transcripts, events, summaries, and four batch records")


if __name__ == "__main__":
    main()
