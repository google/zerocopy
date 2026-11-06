#!/usr/bin/env python3
"""Disposable Rust-comment -> real generated-model -> Lean LSP/batch seam.

The marker parser is deliberately fixture-local; this is not an Anneal parser.
Run with I137_WORK_ROOT pointing at an owned scratch directory.
"""
import hashlib
import json
import os
import select
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODEL = HERE / "model"
TOOLS = Path(os.environ.get("I137_TOOLS", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools"))
LEAN_ROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEAN_ROOT / "bin/lean"
BACKEND = TOOLS / "aeneas-release/backends/lean"
PACKAGES = ["Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible", "mathlib"]
SOURCE_BASE = (HERE / "base-lib.rs").read_bytes()
MARKER = b"// anneal: "
INITIAL = SOURCE_BASE + b"\n// anneal: theorem obl_inc : golden_vertical.inc 0#u32 = .ok 1#u32 := by\n// anneal:   exact ?_\n"
EDITED = SOURCE_BASE + b"\n// anneal: theorem obl_inc : golden_vertical.inc 0#u32 = .ok 1#u32 := by\n// anneal:   rfl\n"
EVENTS = []
START = time.monotonic()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def filehash(path):
    return digest(Path(path).read_bytes())

def record(kind, **data):
    EVENTS.append({"seq": len(EVENTS), "ms": round((time.monotonic() - START) * 1000), "kind": kind, **data})

def project(host):
    out = bytearray(b"import Current\n")
    spans = []
    offset = 0
    for line in host.splitlines(keepends=True):
        if line.startswith(MARKER):
            raw = line[len(MARKER):]
            start = len(out)
            out.extend(raw)
            spans.append({"host_start": offset + len(MARKER), "host_end": offset + len(line), "projected_start": start, "projected_end": len(out)})
        offset += len(line)
    assert len(spans) == 2
    return bytes(out), spans

def env_for(work):
    paths = [work, work / "model"]
    paths += [BACKEND / ".lake/packages" / p / ".lake/build/lib/lean" for p in PACKAGES]
    paths += [BACKEND / ".lake/build/lib/lean", LEAN_ROOT / "lib/lean"]
    env = os.environ.copy()
    env.update(LEAN_PATH=os.pathsep.join(str(p) for p in paths if p.is_dir()), LEAN_NUM_THREADS="1")
    return env

class Server:
    def __init__(self, work, env):
        self.proc = subprocess.Popen([str(LEAN), "--server"], cwd=work, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.buffer = b""
        self.next_id = 2
        record("server_start", pid=self.proc.pid)
        self.send({"jsonrpc":"2.0","id":1,"method":"initialize","params":{"processId":os.getpid(),"rootUri":work.as_uri(),"capabilities":{},"initializationOptions":{"hasWidgets":False}}})
        self.until(lambda m: m.get("id") == 1)
        self.send({"jsonrpc":"2.0","method":"initialized","params":{}})

    def send(self, msg):
        payload = json.dumps(msg, separators=(",", ":")).encode()
        self.proc.stdin.write(b"Content-Length: " + str(len(payload)).encode() + b"\r\n\r\n" + payload)
        self.proc.stdin.flush()
        record("lsp_client", message=msg)

    def read(self, timeout=20):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buffer:
                header, body = self.buffer.split(b"\r\n\r\n", 1)
                length = next((int(x.split(b":", 1)[1]) for x in header.split(b"\r\n") if x.lower().startswith(b"content-length:")), None)
                if length is not None and len(body) >= length:
                    raw, self.buffer = body[:length], body[length:]
                    msg = json.loads(raw)
                    record("lsp_server", message=msg)
                    if msg.get("method") in ("client/registerCapability", "workspace/semanticTokens/refresh") and "id" in msg:
                        self.send({"jsonrpc":"2.0","id":msg["id"],"result":None})
                    return msg
            ready, _, _ = select.select([self.proc.stdout], [], [], min(.1, max(0, deadline-time.monotonic())))
            if ready:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk: break
                self.buffer += chunk
        raise TimeoutError("Lean server response")

    def until(self, pred):
        while True:
            msg = self.read()
            if pred(msg): return msg

    def request(self, method, params):
        rid = self.next_id
        self.next_id += 1
        self.send({"jsonrpc":"2.0","id":rid,"method":method,"params":params})
        return self.until(lambda m: m.get("id") == rid and "method" not in m)

    def close(self):
        if self.proc.poll() is not None: return
        try:
            self.request("shutdown", None)
            self.send({"jsonrpc":"2.0","method":"exit"})
            self.proc.wait(timeout=5)
        except Exception:
            self.proc.kill(); self.proc.wait()
        record("server_exit", rc=self.proc.returncode, stderr=self.proc.stderr.read().decode(errors="replace"))

def command(label, args, cwd, env):
    proc = subprocess.run([str(a) for a in args], cwd=cwd, env=env, capture_output=True, text=True, timeout=60)
    record("command", label=label, argv=[str(a) for a in args], rc=proc.returncode, stdout=proc.stdout, stderr=proc.stderr)
    return proc

def main():
    assert LEAN.is_file()
    assert (MODEL / "Current.olean").is_file()
    root = Path(os.environ.get("I137_WORK_ROOT", tempfile.mkdtemp(prefix="i137-"))).resolve()
    root.mkdir(parents=True, exist_ok=True)
    work = root / "work"
    if work.exists(): shutil.rmtree(work)
    work.mkdir()
    shutil.copytree(MODEL, work / "model")
    (work / "Host.rs").write_bytes(SOURCE_BASE)  # only saved host; annotation stays unsaved
    (work / "Proof.lean").write_text("import Current\n-- stale disk shadow\n")
    initial, map_initial = project(INITIAL)
    edited, map_edited = project(EDITED)
    projected_patch_start = initial.index(b"exact ?_")
    projected_patch_end = projected_patch_start + len(b"exact ?_")
    authored = next(s for s in map_initial if s["projected_start"] <= projected_patch_start and projected_patch_end <= s["projected_end"])
    host_patch_start = authored["host_start"] + projected_patch_start - authored["projected_start"]
    host_patch_end = host_patch_start + len(b"exact ?_")
    assert INITIAL[host_patch_start:host_patch_end] == b"exact ?_"
    assert INITIAL[:host_patch_start] + b"rfl" + INITIAL[host_patch_end:] == EDITED
    initial_text, edited_text = initial.decode(), edited.decode()
    model_files = {p.relative_to(MODEL).as_posix(): filehash(p) for p in sorted(MODEL.rglob("*")) if p.is_file()}
    manifest = json.loads((HERE / "model-manifest.json").read_text())
    assert model_files == manifest["files"]
    generation = digest(json.dumps(manifest, sort_keys=True).encode())
    context = {"generation_id":generation,"source_base_sha256":digest(SOURCE_BASE),"unsaved_initial_host_sha256":digest(INITIAL),"initial_projection_sha256":digest(initial),"model_files_sha256":model_files,"lean_sha256":filehash(LEAN),"lean_version":subprocess.check_output([str(LEAN),"--version"],text=True).strip()}
    record("context", **context)
    record("projection_initial", host_sha256=digest(INITIAL), projected_sha256=digest(initial), spans=map_initial, text=initial_text)
    record("mapped_proof_patch", projected_byte_range=[projected_patch_start,projected_patch_end], host_byte_range=[host_patch_start,host_patch_end], expected_bytes="exact ?_", replacement_bytes="rfl")
    env = env_for(work)
    uri = (work / "Proof.lean").as_uri()
    server = Server(work, env)
    try:
        server.send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":uri,"languageId":"lean","version":1,"text":initial_text}}})
        wait1 = server.request("textDocument/waitForDiagnostics", {"uri":uri,"version":1})
        goal1 = server.request("$/lean/plainGoal", {"textDocument":{"uri":uri},"position":{"line":2,"character":len(initial_text.splitlines()[2])}})
        record("initial_query", wait=wait1, goal=goal1, disk_shadow_sha256=filehash(work / "Proof.lean"))
        assert "⊢" in str(goal1), goal1
        authority = {"host":INITIAL,"version":1,"projection_sha256":digest(initial),"generation_id":generation}
        def cas(expected_host, expected_version, expected_projection, expected_generation, new_host):
            ok = (digest(authority["host"]) == expected_host and authority["version"] == expected_version and authority["projection_sha256"] == expected_projection and authority["generation_id"] == expected_generation)
            if ok:
                authority["host"] = new_host
                authority["version"] += 1
                authority["projection_sha256"] = digest(project(new_host)[0])
            record("host_patch_cas", accepted=ok, expected_host_sha256=expected_host, actual_host_sha256=digest(authority["host"]), expected_version=expected_version, actual_version=authority["version"], expected_projection_sha256=expected_projection, expected_generation_id=expected_generation)
            return ok
        assert cas(digest(INITIAL), 1, digest(initial), generation, EDITED)
        assert not cas(digest(INITIAL), 1, digest(initial), generation, INITIAL)
        assert not cas(digest(EDITED), 2, digest(edited), "wrong-generation", INITIAL)
        record("projection_edited", host_sha256=digest(EDITED), projected_sha256=digest(edited), spans=map_edited, text=edited_text)
        server.send({"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":uri,"version":2},"contentChanges":[{"text":edited_text}]}})
        wait2 = server.request("textDocument/waitForDiagnostics", {"uri":uri,"version":2})
        goal2 = server.request("$/lean/plainGoal", {"textDocument":{"uri":uri},"position":{"line":2,"character":len(edited_text.splitlines()[2])}})
        record("edited_query", wait=wait2, goal=goal2, disk_shadow_sha256=filehash(work / "Proof.lean"))
        assert "no goals" in str(goal2).lower(), goal2
        assert (work / "Host.rs").read_bytes() == SOURCE_BASE
        assert (work / "Proof.lean").read_text() == "import Current\n-- stale disk shadow\n"
    finally:
        server.close()
    captured = work / "Captured.lean"
    captured.write_bytes(edited)
    batch = command("fresh-batch-captured", [LEAN,"--json",captured], work, env)
    assert batch.returncode == 0, batch.stdout
    compiled = command("compile-captured", [LEAN,"--json","-o",work / "Captured.olean",captured],work,env)
    assert compiled.returncode == 0, compiled.stdout
    oracle_text = "import Captured\nexample : golden_vertical.inc 0#u32 = .ok 1#u32 := obl_inc\n#print axioms obl_inc\n"
    (work / "Oracle.lean").write_text(oracle_text)
    oracle = command("fixed-proposition-and-axioms",[LEAN,"--json",work / "Oracle.lean"],work,env)
    assert oracle.returncode == 0 and "sorryAx" not in oracle.stdout, oracle.stdout
    assert filehash(work / "model/Current.olean") == model_files["Current.olean"]
    record("result", accepted=True, captured_sha256=filehash(captured), captured_olean_sha256=filehash(work / "Captured.olean"), oracle_sha256=digest(oracle_text.encode()), imported_model_olean_sha256=filehash(work / "model/Current.olean"), host_disk_sha256=filehash(work / "Host.rs"), shadow_disk_sha256=filehash(work / "Proof.lean"), generation_id=generation)
    text = json.dumps(EVENTS,indent=2,ensure_ascii=False) + "\n"
    text = text.replace(str(root), "$WORK").replace(str(TOOLS), "$TOOLS")
    (HERE / "transcript.json").write_text(text)
    (HERE / "captured-Proof.lean").write_bytes(edited)
    (HERE / "unsaved-host-before.rs").write_bytes(INITIAL)
    (HERE / "unsaved-host-after.rs").write_bytes(EDITED)
    print(json.dumps({"accepted":True,"generation_id":generation,"events":len(EVENTS),"captured_sha256":digest(edited)}))

if __name__ == "__main__": main()
