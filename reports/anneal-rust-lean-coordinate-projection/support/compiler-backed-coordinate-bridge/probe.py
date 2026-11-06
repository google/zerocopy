#!/usr/bin/env python3
"""Compiler-backed coordinates over one exact-copy Rust-doc to Lean bridge."""
import hashlib
import json
import os
import select
import subprocess
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUSTC = Path(os.environ.get("RUSTC_BIN", TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin/rustc"))
LEAN = Path(os.environ.get("LEAN_BIN", TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean"))
HEADER = b"import Lean\r\n"
PAYLOAD = '#check ("🙂e\u0301", missingLean)'.encode()
HOST = (b'// exact UTF-8 source; CRLF retained\r\n'
        + b'/// ' + PAYLOAD + b'\r\n'
        + 'pub fn probe() { let _ = ("🙂e\u0301",\tmissingRust); }\r\n'.encode())
PROJECTED = HEADER + PAYLOAD + b"\r\n"
HOST_START = HOST.index(PAYLOAD)
PROJ_START = len(HEADER)
T0 = time.monotonic()
EVENTS = []

def sha(value):
    return hashlib.sha256(value).hexdigest()

def event(kind, **fields):
    EVENTS.append(dict(seq=len(EVENTS), ms=round((time.monotonic()-T0)*1000, 1), kind=kind, **fields))

def lines(raw):
    result = []
    start = 0
    for whole in raw.splitlines(keepends=True):
        content = whole[:-2] if whole.endswith(b"\r\n") else whole.rstrip(b"\n")
        result.append((start, content))
        start += len(whole)
    return result

def positions(raw, absolute):
    for line, (start, content) in enumerate(lines(raw)):
        if start <= absolute <= start + len(content):
            prefix = raw[start:absolute].decode("utf-8")
            return dict(line=line, scalar=len(prefix), utf16=len(prefix.encode("utf-16-le"))//2)
    raise ValueError("outside line content or inside CRLF")

def offset(raw, line, column, unit):
    start, content = lines(raw)[line]
    text = content.decode("utf-8")
    count = 0
    for i, char in enumerate(text):
        if count == column:
            return start + len(text[:i].encode())
        count += 2 if unit == "utf16" and ord(char) > 0xffff else 1
        if count > column:
            raise ValueError("inside surrogate pair")
    if count == column:
        return start + len(content)
    raise ValueError("column beyond line")

def mapped_host(projected_byte):
    if not PROJ_START <= projected_byte <= PROJ_START + len(PAYLOAD):
        raise ValueError("synthetic or outside copied payload")
    # `positions` rejects interior UTF-8 bytes and CRLF interiors.
    positions(PROJECTED, projected_byte)
    return HOST_START + projected_byte - PROJ_START

def mapped_projected(host_byte):
    if not HOST_START <= host_byte <= HOST_START + len(PAYLOAD):
        raise ValueError("not inside authored payload")
    positions(HOST, host_byte)
    return PROJ_START + host_byte - HOST_START

class Server:
    def __init__(self):
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=HERE,
            env=dict(os.environ, LEAN_NUM_THREADS="1"), stdin=subprocess.PIPE,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.buf = b""
        self.n = 10
        self.send(dict(jsonrpc="2.0", id=1, method="initialize", params=dict(
            processId=os.getpid(), rootUri=HERE.as_uri(), capabilities={},
            initializationOptions={"hasWidgets": False})))
        self.until(1)
        self.send(dict(jsonrpc="2.0", method="initialized", params={}))

    def send(self, message):
        raw = json.dumps(message, ensure_ascii=False, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        self.p.stdin.flush()
        event("send", message=message)

    def read(self, timeout=20):
        deadline = time.monotonic()+timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buf:
                header, body = self.buf.split(b"\r\n\r\n", 1)
                length = next((int(x.split(b":",1)[1]) for x in header.split(b"\r\n")
                               if x.lower().startswith(b"content-length:")), None)
                if length is not None and len(body) >= length:
                    message = json.loads(body[:length])
                    self.buf = body[length:]
                    event("recv", message=message)
                    if message.get("method") == "client/registerCapability" and "id" in message:
                        self.send(dict(jsonrpc="2.0", id=message["id"], result=None))
                    return message
            ready, _, _ = select.select([self.p.stdout], [], [],
                                         min(.1, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    break
                self.buf += chunk
        raise TimeoutError("Lean server read")

    def until(self, rid):
        while True:
            message = self.read()
            if message.get("id") == rid:
                return message

    def request(self, method, params):
        rid = self.n
        self.n += 1
        self.send(dict(jsonrpc="2.0", id=rid, method=method, params=params))
        return self.until(rid)

    def stop(self):
        if self.p.poll() is not None:
            return
        try:
            self.send(dict(jsonrpc="2.0", id=99, method="shutdown", params=None))
            self.until(99)
            self.send(dict(jsonrpc="2.0", method="exit"))
            self.p.wait(timeout=5)
        finally:
            if self.p.poll() is None:
                self.p.kill()
                self.p.wait()
            event("stop", rc=self.p.returncode, stderr=self.p.stderr.read().decode(errors="replace"))

def main():
    (HERE / "Host.rs").write_bytes(HOST)
    (HERE / "Projected.lean").write_bytes(PROJECTED)
    assert (HERE / "Host.rs").read_bytes() == HOST
    assert (HERE / "Projected.lean").read_bytes() == PROJECTED
    rust_version = subprocess.check_output([str(RUSTC), "--version"], text=True).strip()
    lean_version = subprocess.check_output([str(LEAN), "--version"], text=True).strip()
    event("subject", rust_version=rust_version, lean_version=lean_version,
          rustc_sha256=sha(RUSTC.read_bytes()), lean_sha256=sha(LEAN.read_bytes()),
          host_sha256=sha(HOST), projected_sha256=sha(PROJECTED))
    rust = subprocess.run([str(RUSTC), "--crate-type=lib", "--edition=2021",
        "--crate-name=coordinate_bridge", "--error-format=json", "--emit=metadata",
        "Host.rs"], cwd=HERE, capture_output=True, text=True, timeout=20,
        env=dict(os.environ, RUSTUP_HOME=str(TOOLS/"rustup"), CARGO_HOME=str(TOOLS/"cargo")))
    lean = subprocess.run([str(LEAN), "--json", "Projected.lean"], cwd=HERE,
        capture_output=True, text=True, timeout=20,
        env=dict(os.environ, LEAN_NUM_THREADS="1"))
    event("batch", tool="rustc", rc=rust.returncode, stdout=rust.stdout, stderr=rust.stderr)
    event("batch", tool="lean", rc=lean.returncode, stdout=lean.stdout, stderr=lean.stderr)
    server = Server()
    try:
        uri = (HERE / "Projected.lean").as_uri()
        server.send(dict(jsonrpc="2.0", method="textDocument/didOpen", params=dict(
            textDocument=dict(uri=uri, languageId="lean", version=1,
                              text=PROJECTED.decode()))))
        wait = server.request("textDocument/waitForDiagnostics", dict(uri=uri, version=1))
        server.send(dict(jsonrpc="2.0", method="textDocument/didClose",
                         params=dict(textDocument=dict(uri=uri))))
    finally:
        server.stop()
    rust_messages = [json.loads(line) for line in rust.stderr.splitlines() if line.startswith("{")]
    lean_messages = [json.loads(line) for line in lean.stdout.splitlines() if line.startswith("{")]
    diagnostics = [e["message"]["params"] for e in EVENTS if e["kind"] == "recv"
                   and e["message"].get("method") == "textDocument/publishDiagnostics"]
    boundaries = []
    for i in range(len(PAYLOAD)+1):
        hb = HOST_START+i
        try:
            host_pos = positions(HOST, hb)
        except UnicodeDecodeError:
            continue
        pb = mapped_projected(hb)
        proj_pos = positions(PROJECTED, pb)
        assert mapped_host(pb) == hb
        assert offset(HOST, host_pos["line"], host_pos["scalar"], "scalar") == hb
        assert offset(HOST, host_pos["line"], host_pos["utf16"], "utf16") == hb
        assert offset(PROJECTED, proj_pos["line"], proj_pos["scalar"], "scalar") == pb
        assert offset(PROJECTED, proj_pos["line"], proj_pos["utf16"], "utf16") == pb
        boundaries.append(dict(host_byte=hb, projected_byte=pb, host=host_pos, projected=proj_pos))
    invalid = {}
    for label, fun in {
        "host_interior_utf8": lambda: positions(HOST, HOST.index("🙂".encode())+1),
        "projected_interior_utf8": lambda: positions(PROJECTED, PROJECTED.index("🙂".encode())+1),
        "host_surrogate_interior": lambda: offset(HOST, 1, positions(HOST, HOST.index("🙂".encode()))["utf16"]+1, "utf16"),
        "projected_surrogate_interior": lambda: offset(PROJECTED, 1, positions(PROJECTED, PROJECTED.index("🙂".encode()))["utf16"]+1, "utf16"),
        "host_crlf_interior": lambda: positions(HOST, HOST.index(b"\r\n")+1),
        "synthetic_projected": lambda: mapped_host(0),
        "rust_outside_payload": lambda: mapped_projected(HOST.index(b"missingRust")),
    }.items():
        try:
            fun()
        except (ValueError, UnicodeDecodeError) as exc:
            invalid[label] = type(exc).__name__
        else:
            raise AssertionError(f"accepted {label}")
    result = dict(subject=dict(rust_version=rust_version, lean_version=lean_version,
        rustc_sha256=sha(RUSTC.read_bytes()), lean_sha256=sha(LEAN.read_bytes())),
        source=dict(host_sha256=sha(HOST), projected_sha256=sha(PROJECTED),
                    host_payload_start=HOST_START, projected_payload_start=PROJ_START,
                    payload_length=len(PAYLOAD)),
        rust=dict(rc=rust.returncode, messages=rust_messages),
        lean_batch=dict(rc=lean.returncode, messages=lean_messages),
        lean_lsp=dict(wait=wait, notifications=diagnostics),
        boundaries=boundaries, invalid=invalid)
    raw = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    raw = raw.replace(HERE.as_uri(), "$HERE_URI").replace(str(HERE), "$HERE")
    (HERE / "results.json").write_text(raw)

try:
    main()
finally:
    raw = json.dumps(EVENTS, indent=2, ensure_ascii=False) + "\n"
    raw = raw.replace(HERE.as_uri(), "$HERE_URI").replace(str(HERE), "$HERE")
    raw = raw.replace(str(RUSTC), "$RUSTC_BIN").replace(str(LEAN), "$LEAN_BIN")
    (HERE / "transcript.json").write_text(raw)
