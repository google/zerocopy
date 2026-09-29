#!/usr/bin/env python3
"""Gated disposable publisher over retained real Charon/Aeneas/Lean artifacts."""
import hashlib
import json
import os
import select
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = Path(os.environ.get("I051_TOOLS", "/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools"))
LEAN_ROOT = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LEAN = LEAN_ROOT / "bin/lean"
BACKEND = TOOLS / "aeneas-release/backends/lean"
PACKAGES = ["Cli", "batteries", "Qq", "aesop", "proofwidgets", "importGraph", "LeanSearchClient", "plausible", "mathlib"]
FILES = ["current.llbc", "Current/Types.lean", "Current/Types.olean", "Current/Funs.lean", "Current/Funs.olean", "Current.lean", "Current.olean"]
INPUTS = HERE / "inputs"
SCRATCH = Path(os.environ.get("I051_SCRATCH", "/Users/josh/Codex/Meta/Data/20260929-153000-i051-real-publication")).resolve()

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def inventory(root):
    return {p.relative_to(root).as_posix(): sha(p) for p in root.rglob("*") if p.is_file()}

EXPECTED = {x: inventory(INPUTS / x) for x in "AB"}
IDS = {x: hashlib.sha256(json.dumps(EXPECTED[x], sort_keys=True, separators=(",", ":")).encode()).hexdigest() for x in "AB"}

def env_for(model):
    paths = [model]
    paths += [BACKEND / ".lake/packages" / p / ".lake/build/lib/lean" for p in PACKAGES]
    paths += [BACKEND / ".lake/build/lib/lean", LEAN_ROOT / "lib/lean"]
    env = os.environ.copy()
    env.update(LEAN_PATH=os.pathsep.join(str(p) for p in paths if p.is_dir()), LEAN_NUM_THREADS="1")
    return env

def oracle(model, value, work):
    work.mkdir(parents=True, exist_ok=True)
    proof = (INPUTS / ("full-model-change-old-Proof.lean" if value == 1 else "full-model-change-new-Proof.lean")).read_text()
    source = work / f"Proof{value}.lean"
    source.write_text(proof + f"example : golden_vertical.inc 0#u32 = .ok {value}#u32 := obl_inc\n#print axioms obl_inc\n")
    cmd = [str(LEAN), "--json", str(source)]
    p = subprocess.run(cmd, cwd=work, env=env_for(model), capture_output=True, text=True, timeout=90)
    family = inventory(model)
    label = next((x for x in "AB" if family == EXPECTED[x]), "mixed")
    return {"generation_path": str(model), "generation_id": IDS.get(label), "generation_classification": label, "proof_value": value, "source_sha256": sha(source), "argv": cmd, "rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr}

def selected(root):
    link = root / "current"
    target = link.resolve(strict=True)
    files = inventory(target)
    label = next((x for x in "AB" if files == EXPECTED[x]), "mixed")
    return {"generation_id": IDS.get(label), "classification": label, "resolved": str(target), "files": files}

def gate(root, name):
    gates = root / "gates"
    (gates / (name + ".entered")).write_text(name)
    deadline = time.monotonic() + 90
    while not (gates / (name + ".release")).exists():
        if time.monotonic() > deadline:
            raise TimeoutError(name)
        time.sleep(.01)

def child(root, mode):
    b = root / ("staging" if mode != "inplace" else "generations/A")
    if mode != "inplace": b.mkdir()
    for n, rel in enumerate(FILES):
        dest = b / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(INPUTS / "B" / rel, dest)
        gate(root, f"write-{n}")
    if mode == "inplace": return
    assert inventory(b) == EXPECTED["B"]
    before = {"exact_files": inventory(b), "generation_id": IDS["B"], "old_proof": oracle(b, 1, root / "validation-old"), "new_proof": oracle(b, 2, root / "validation-new")}
    assert before["old_proof"]["rc"] != 0 and before["new_proof"]["rc"] == 0
    assert "sorryAx" not in before["new_proof"]["stdout"]
    (root / "validation.json").write_text(json.dumps(before, indent=2) + "\n")
    gate(root, "validated")
    final = root / "generations/B"
    os.replace(b, final)
    gate(root, "generation-moved")
    tmp = root / "current.next"
    tmp.symlink_to("generations/B")
    gate(root, "before-publish")
    os.replace(tmp, root / "current")
    gate(root, "after-publish")

def await_gate(root, name, proc):
    marker = root / "gates" / (name + ".entered")
    deadline = time.monotonic() + 120
    while not marker.exists():
        if proc.poll() is not None: raise RuntimeError(f"publisher exited {proc.returncode} before {name}")
        if time.monotonic() > deadline: raise TimeoutError(name)
        time.sleep(.01)

def release(root, name):
    (root / "gates" / (name + ".release")).write_text(name)

def setup(root):
    if root.exists(): shutil.rmtree(root)
    (root / "generations").mkdir(parents=True)
    (root / "gates").mkdir()
    shutil.copytree(INPUTS / "A", root / "generations/A")
    (root / "current").symlink_to("generations/A")
    assert selected(root)["classification"] == "A"

class Server:
    def __init__(self, root, model):
        root.mkdir()
        self.root = root
        self.messages = []
        self.buffer = b""
        self.next_id = 2
        self.proc = subprocess.Popen([str(LEAN), "--server"], cwd=root, env=env_for(model), stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, bufsize=0)
        self.call("initialize", {"processId": os.getpid(), "rootUri": root.as_uri(), "capabilities": {}, "initializationOptions": {"hasWidgets": False}}, rid=1)
        self.send({"jsonrpc":"2.0", "method":"initialized", "params":{}})

    def send(self, msg):
        self.messages.append({"direction":"client", "message":msg})
        body = json.dumps(msg, separators=(",", ":")).encode()
        self.proc.stdin.write(b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body)
        self.proc.stdin.flush()

    def read(self):
        deadline = time.monotonic() + 90
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buffer:
                header, rest = self.buffer.split(b"\r\n\r\n", 1)
                n = next((int(line.split(b":",1)[1]) for line in header.split(b"\r\n") if line.lower().startswith(b"content-length:")), None)
                if n is not None and len(rest) >= n:
                    body, self.buffer = rest[:n], rest[n:]
                    msg = json.loads(body)
                    self.messages.append({"direction":"server", "message":msg})
                    if msg.get("method") in ("client/registerCapability", "workspace/semanticTokens/refresh") and "id" in msg:
                        self.send({"jsonrpc":"2.0", "id":msg["id"], "result":None})
                    return msg
            ready,_,_ = select.select([self.proc.stdout], [], [], .1)
            if ready:
                chunk = os.read(self.proc.stdout.fileno(), 65536)
                if not chunk: raise RuntimeError("server closed")
                self.buffer += chunk
        raise TimeoutError("server message")

    def call(self, method, params, rid=None):
        if rid is None: rid = self.next_id; self.next_id += 1
        self.send({"jsonrpc":"2.0", "id":rid, "method":method, "params":params})
        while True:
            msg = self.read()
            if msg.get("id") == rid and "method" not in msg: return msg

    def goal(self, open_file=False):
        uri = (self.root / "OldProof.lean").as_uri()
        proof = (INPUTS / "full-model-change-old-Proof.lean").read_text()
        if open_file:
            self.send({"jsonrpc":"2.0", "method":"textDocument/didOpen", "params":{"textDocument":{"uri":uri,"languageId":"lean","version":1,"text":proof}}})
            self.call("textDocument/waitForDiagnostics", {"uri":uri,"version":1})
        return self.call("$/lean/plainGoal", {"textDocument":{"uri":uri},"position":{"line":2,"character":len(proof.splitlines()[2])}})

    def close(self):
        self.call("shutdown", None)
        self.send({"jsonrpc":"2.0", "method":"exit", "params":{}})
        self.proc.stdin.close()
        self.proc.wait(timeout=10)
        return {"pid":self.proc.pid, "exit":self.proc.returncode, "messages":self.messages, "stderr":self.proc.stderr.read().decode(errors="replace")}

def run_case(label, mode, stop=None):
    root = SCRATCH / label
    setup(root)
    log = []
    server = Server(root / "server-old", root / "generations/A") if mode == "staged" and stop is None else None
    old_server_initial = {"generation_id":IDS["A"], "generation_classification":"A", "current_for_selected":True, "response":server.goal(open_file=True)} if server else None
    proc = subprocess.Popen([sys.executable, str(Path(__file__).resolve()), "--child", str(root), mode], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    for n, rel in enumerate(FILES):
        name = f"write-{n}"; await_gate(root, name, proc)
        snap = selected(root)
        values = (1,2) if mode == "inplace" else ()
        checks = [oracle(Path(snap["resolved"]), v, root / f"reader-{n}-{v}") for v in values]
        log.append({"gate": name, "written_file": rel, "selected": snap, "reader_oracles": checks})
        assert (snap["classification"] == "A") if mode == "staged" else True
        release(root, name)
    if mode == "staged":
        for name in ("validated", "generation-moved", "before-publish", "after-publish"):
            await_gate(root, name, proc)
            snap = selected(root)
            values = (1,2) if stop is None and name in ("validated", "after-publish") else ()
            log.append({"gate": name, "selected": snap, "reader_oracles": [oracle(Path(snap["resolved"]), v, root / f"reader-{name}-{v}") for v in values]})
            if stop == name:
                proc.kill(); out, err = proc.communicate(timeout=10)
                return {"mode": mode, "kill_at": name, "kill_rc": proc.returncode, "stdout": out, "stderr": err, "gates": log, "readback": selected(root), "validation": json.loads((root / "validation.json").read_text())}
            release(root, name)
    out, err = proc.communicate(timeout=30)
    assert proc.returncode == 0, err
    old_server_after = {"generation_id":IDS["A"], "generation_classification":"A", "current_for_selected":False, "response":server.goal()} if server else None
    server_record = server.close() if server else None
    if server_record: server_record.update(pinned_generation_id=IDS["A"], pinned_generation_classification="A")
    return {"mode": mode, "kill_at": None, "exit": proc.returncode, "stdout": out, "stderr": err, "gates": log, "readback": selected(root), "validation": json.loads((root / "validation.json").read_text()) if mode == "staged" else None, "old_server_initial_goal":old_server_initial, "old_server_after_goal":old_server_after, "old_server":server_record}

def main():
    assert set(FILES) == set(EXPECTED["A"]) == set(EXPECTED["B"])
    old_manifest = json.loads((INPUTS / "model-manifest.json").read_text())
    new_manifest = json.loads((INPUTS / "new-model-manifest.json").read_text())
    assert old_manifest["llbc_sha256"] == EXPECTED["A"]["current.llbc"]
    assert new_manifest["llbc_sha256"] == EXPECTED["B"]["current.llbc"]
    assert {k:v for k,v in EXPECTED["A"].items() if k != "current.llbc"} == old_manifest["files"]
    assert {k:v for k,v in EXPECTED["B"].items() if k != "current.llbc"} == new_manifest["files_sha256"]
    assert EXPECTED["A"]["Current.olean"] == EXPECTED["B"]["Current.olean"]
    assert EXPECTED["A"]["Current/Funs.olean"] != EXPECTED["B"]["Current/Funs.olean"]
    SCRATCH.mkdir(parents=True, exist_ok=True)
    result = {"tool": {"lean": str(LEAN), "lean_sha256": sha(LEAN), "python": sys.version, "scratch": str(SCRATCH)}, "expected": EXPECTED, "generation_ids": IDS}
    result["staged"] = run_case("staged", "staged")
    result["inplace"] = run_case("inplace", "inplace")
    result["kill_before"] = run_case("kill-before", "staged", "before-publish")
    result["kill_after"] = run_case("kill-after", "staged", "after-publish")
    (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    assert result["staged"]["readback"]["classification"] == "B"
    assert result["kill_before"]["readback"]["classification"] == "A"
    assert result["kill_after"]["readback"]["classification"] == "B"
    assert any(g["selected"]["classification"] == "mixed" for g in result["inplace"]["gates"])
    print(json.dumps({"generation_ids": IDS, "staged": "B", "inplace_mixed_gates": [g["gate"] for g in result["inplace"]["gates"] if g["selected"]["classification"] == "mixed"], "kill_before": "A", "kill_after": "B"}))

if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--child": child(Path(sys.argv[2]), sys.argv[3])
    else: main()
