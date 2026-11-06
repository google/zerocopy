#!/usr/bin/env python3
"""Offline check of retained Rust, Lean batch, Lean LSP, and byte-map evidence."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
host = (HERE / "Host.rs").read_bytes()
projected = (HERE / "Projected.lean").read_bytes()
data = json.loads((HERE / "results.json").read_text())
trace = json.loads((HERE / "transcript.json").read_text())

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def line_at(raw, byte):
    before = raw[:byte]
    if before.endswith(b"\r"):
        raise ValueError("inside CRLF")
    line = before.count(b"\r\n")
    line_bytes = before.split(b"\r\n")[-1]
    text = line_bytes.decode("utf-8")
    return dict(line=line, scalar=len(text), utf16=len(text.encode("utf-16-le"))//2)

def byte_at(raw, line, column, unit):
    rows = raw.split(b"\r\n")
    text = rows[line].decode("utf-8")
    start = sum(len(row)+2 for row in rows[:line])
    count = 0
    for i, char in enumerate(text):
        if count == column:
            return start+len(text[:i].encode())
        count += 2 if unit == "utf16" and ord(char) > 0xffff else 1
        if count > column:
            raise ValueError("surrogate interior")
    if count == column:
        return start+len(rows[line])
    raise ValueError("out of range")

assert b"\r\n" in host and b"\r\n" in projected
assert "🙂".encode() in host and "e\u0301".encode() in host and b"\t" in host
assert data["source"]["host_sha256"] == sha(host)
assert data["source"]["projected_sha256"] == sha(projected)
assert data["subject"]["lean_sha256"] == "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
assert data["subject"]["rustc_sha256"] == "2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc"
hs = data["source"]["host_payload_start"]
ps = data["source"]["projected_payload_start"]
length = data["source"]["payload_length"]
assert host[hs-4:hs] == b"/// "
assert host[hs:hs+length] == projected[ps:ps+length]
assert len(data["boundaries"]) == 28
assert data["boundaries"][0]["host_byte"] == hs
assert data["boundaries"][-1]["host_byte"] == hs+length
for row in data["boundaries"]:
    hb, pb = row["host_byte"], row["projected_byte"]
    assert hs <= hb <= hs+length and pb == ps+hb-hs
    assert row["host"] == line_at(host, hb)
    assert row["projected"] == line_at(projected, pb)
    for raw, byte, pos in ((host, hb, row["host"]), (projected, pb, row["projected"])):
        assert byte_at(raw, pos["line"], pos["scalar"], "scalar") == byte
        assert byte_at(raw, pos["line"], pos["utf16"], "utf16") == byte
assert set(data["invalid"]) == {"host_interior_utf8", "projected_interior_utf8",
    "host_surrogate_interior", "projected_surrogate_interior", "host_crlf_interior",
    "synthetic_projected", "rust_outside_payload"}
assert all(data["invalid"].values())
for raw in (host, projected):
    emoji = raw.index("🙂".encode())
    try:
        line_at(raw, emoji+1)
    except UnicodeDecodeError:
        pass
    else:
        raise AssertionError("accepted interior UTF-8 byte")
    pos = line_at(raw, emoji)
    try:
        byte_at(raw, pos["line"], pos["utf16"]+1, "utf16")
    except ValueError:
        pass
    else:
        raise AssertionError("accepted surrogate interior")
    try:
        line_at(raw, raw.index(b"\r\n")+1)
    except ValueError:
        pass
    else:
        raise AssertionError("accepted CRLF interior")

assert data["rust"]["rc"] == 1 and data["lean_batch"]["rc"] == 1
rust_error = next(m for m in data["rust"]["messages"] if "missingRust" in m.get("message", ""))
rust_span = next(s for s in rust_error["spans"] if s["is_primary"])
assert host[rust_span["byte_start"]:rust_span["byte_end"]] == b"missingRust"
rp = line_at(host, rust_span["byte_start"])
assert (rust_span["line_start"], rust_span["column_start"]) == (rp["line"]+1, rp["scalar"]+1)
assert (rp["scalar"], rp["utf16"]) == (33, 34)
assert byte_at(host, rp["line"], rp["scalar"], "scalar") == rust_span["byte_start"]

lean_error = next(m for m in data["lean_batch"]["messages"] if "missingLean" in m.get("data", ""))
batch_pos = lean_error["pos"]
batch_start = byte_at(projected, batch_pos["line"]-1, batch_pos["column"], "scalar")
batch_end = byte_at(projected, lean_error["endPos"]["line"]-1,
                    lean_error["endPos"]["column"], "scalar")
assert projected[batch_start:batch_end] == b"missingLean"
assert batch_pos == {"line": 2, "column": 15}
assert host[hs+batch_start-ps:hs+batch_end-ps] == b"missingLean"

published = [d for notice in data["lean_lsp"]["notifications"]
             for d in notice["diagnostics"] if "missingLean" in d["message"]]
assert published
lsp = published[0]["range"]
lsp_start = byte_at(projected, lsp["start"]["line"], lsp["start"]["character"], "utf16")
lsp_end = byte_at(projected, lsp["end"]["line"], lsp["end"]["character"], "utf16")
assert (lsp_start, lsp_end) == (batch_start, batch_end)
assert lsp["start"] == {"line": 1, "character": 16}
assert data["lean_lsp"]["wait"].get("result") == {}

batch_events = [e for e in trace if e["kind"] == "batch"]
assert [(e["tool"], e["rc"]) for e in batch_events] == [("rustc", 1), ("lean", 1)]
assert [json.loads(row) for row in batch_events[0]["stderr"].splitlines()
        if row.startswith("{")] == data["rust"]["messages"]
assert [json.loads(row) for row in batch_events[1]["stdout"].splitlines()
        if row.startswith("{")] == data["lean_batch"]["messages"]
assert [e["rc"] for e in trace if e["kind"] == "stop"] == [0]
trace_notices = [e["message"]["params"] for e in trace if e["kind"] == "recv" and
                 e["message"].get("method") == "textDocument/publishDiagnostics"]
assert trace_notices == data["lean_lsp"]["notifications"]
print(json.dumps(dict(boundaries=len(data["boundaries"]), rejected=len(data["invalid"]),
    rust_byte=rust_span["byte_start"], rust_scalar_1based=rust_span["column_start"],
    lean_batch_scalar=batch_pos["column"], lean_lsp_utf16=lsp["start"]["character"],
    mapped_rust_host_byte=hs+batch_start-ps, server_exit=0), sort_keys=True))
