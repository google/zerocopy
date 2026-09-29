#!/usr/bin/env python3
"""Bounded direct Lean context and incremental-prefix probes; stdlib only."""
import hashlib
import json
import os
from pathlib import Path
import select
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LEAN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean")
ENV = {**os.environ, "LEAN_NUM_THREADS": "1"}


def sha(data):
    if isinstance(data, Path):
        data = data.read_bytes()
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def batch(name, source):
    p = WORK / (name + ".lean")
    p.write_text(source)
    t0 = time.monotonic()
    x = subprocess.run([str(LEAN), "--json", str(p)], cwd=WORK, env=ENV,
                       capture_output=True, text=True, timeout=35)
    return {"source": source, "source_sha256": sha(source), "exit": x.returncode,
            "stdout": x.stdout, "stderr": x.stderr, "elapsed_ms": round((time.monotonic()-t0)*1000)}


class Server:
    def __init__(self):
        self.p = subprocess.Popen([str(LEAN), "--server"], cwd=WORK, env=ENV,
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, bufsize=0)
        self.buf = b""
        self.events = []
        self.n = 0
        self.request("initialize", {"processId": os.getpid(), "rootUri": WORK.as_uri(),
                                    "capabilities": {}, "initializationOptions": {"hasWidgets": False}})
        self.send({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send(self, m):
        b = json.dumps(m, separators=(",", ":")).encode()
        self.p.stdin.write(b"Content-Length: " + str(len(b)).encode() + b"\r\n\r\n" + b)
        self.p.stdin.flush()
        self.events.append({"direction": "client", "message": m})

    def recv(self, timeout=30):
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if b"\r\n\r\n" in self.buf:
                head, body = self.buf.split(b"\r\n\r\n", 1)
                size = int(next(line.split(b":", 1)[1] for line in head.split(b"\r\n")
                                if line.lower().startswith(b"content-length:")))
                if len(body) >= size:
                    m = json.loads(body[:size])
                    self.buf = body[size:]
                    self.events.append({"direction": "server", "message": m})
                    if m.get("method") == "client/registerCapability" and "id" in m:
                        self.send({"jsonrpc": "2.0", "id": m["id"], "result": None})
                    return m
            ready, _, _ = select.select([self.p.stdout], [], [], .1)
            if ready:
                chunk = os.read(self.p.stdout.fileno(), 65536)
                if not chunk:
                    raise RuntimeError("Lean server exited")
                self.buf += chunk
        raise TimeoutError("Lean server response")

    def request(self, method, params):
        self.n += 1
        key = self.n
        self.send({"jsonrpc": "2.0", "id": key, "method": method, "params": params})
        while True:
            m = self.recv()
            if m.get("id") == key and "method" not in m:
                return m

    def change(self, uri, version, source, first=False):
        if first:
            self.send({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {
                "textDocument": {"uri": uri, "languageId": "lean", "version": version, "text": source}}})
        else:
            self.send({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri, "version": version}, "contentChanges": [{"text": source}]}})
        t0 = time.monotonic()
        response = self.request("textDocument/waitForDiagnostics", {"uri": uri, "version": version})
        return {"version": version, "source_sha256": sha(source),
                "wait": response, "elapsed_ms": round((time.monotonic()-t0)*1000)}

    def close(self):
        try:
            self.request("shutdown", None)
            self.send({"jsonrpc": "2.0", "method": "exit"})
            self.p.wait(timeout=4)
        except Exception:
            self.p.kill()
            self.p.wait()
        self.events.append({"direction": "exit", "code": self.p.returncode,
                            "stderr": self.p.stderr.read().decode(errors="replace")})


def tick(tag):
    # The side effect records that Lean actually re-elaborated this command.
    return ("run_cmd do\n"
            "  let p := \"" + str(WORK / "ticks.txt") + "\"\n"
            "  let old ← liftIO <| IO.FS.readFile p <|> pure \"\"\n"
            "  liftIO <| IO.FS.writeFile p (old ++ \"" + tag + "\\n\")\n")


def prefix_source(import_line="import Lean", namespace="N", option="1000",
                  definition="1", tactic="decide"):
    return (import_line + "\nopen Lean Elab Command\n" + tick("A") +
            "namespace " + namespace + "\n" + tick("B") +
            "set_option maxRecDepth " + option + "\n" + tick("C") +
            "def generated : Nat := " + definition + "\n" + tick("D") +
            "theorem target : generated = 1 := by " + tactic + "\n" + tick("E") +
            "end " + namespace + "\n")


def context_cases():
    # The theorem source line is identical within each paired context.
    theorem = "theorem proof : (Marker.value : Nat) = 2 := by decide\n#print N.proof\n#print axioms N.proof\n"
    pre = "class Marker where\n  value : Nat\ninstance globalMarker : Marker where\n  value := 1\nnamespace N\n"
    local = "section\nlocal instance : Marker where\n  value := 2\n"
    return {
        "instance_in_scope": pre + local + theorem + "end\nend N\n",
        "instance_omitted": pre + theorem + "end N\n",
        "macro_left": "namespace N\nsyntax \"claim\" : term\nmacro_rules | `(claim) => `(0 = 0)\ntheorem proof : claim := by rfl\n#print N.proof\n#print axioms N.proof\nend N\n",
        "macro_right": "namespace N\nsyntax \"claim\" : term\nmacro_rules | `(claim) => `(1 = 1)\ntheorem proof : claim := by rfl\n#print N.proof\n#print axioms N.proof\nend N\n",
        "macro_missing": "namespace N\ntheorem proof : claim := by rfl\n#print N.proof\nend N\n",
        "option_strict": "set_option autoImplicit false\nnamespace N\naxiom proof : later = 1\ndef later : Nat := 1\n#print N.proof\nend N\n",
        "option_permissive": "set_option autoImplicit true\nnamespace N\naxiom proof : later = 1\ndef later : Nat := 1\n#print N.proof\nend N\n",
    }


def main():
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir()
    out = {"lean_sha256": sha(LEAN), "version": batch("Version", "#eval Lean.versionString\n"),
           "context": {}, "prefix": {"steps": [], "events": []}}
    for name, source in context_cases().items():
        out["context"][name] = batch(name, source)
    path = WORK / "Prefix.lean"
    base = prefix_source()
    path.write_text(base)
    server = Server()
    changes = [("base", base), ("late_tactic", prefix_source(tactic="rfl")),
               ("reset_late", base), ("definition", prefix_source(definition="2")),
               ("reset_definition", base), ("option", prefix_source(option="1001")),
               ("reset_option", base), ("namespace", prefix_source(namespace="M")),
               ("reset_namespace", base), ("import", prefix_source(import_line="import Lean\nimport Std")),
               ("reset_import", base)]
    try:
        for i, (name, source) in enumerate(changes, 1):
            result = server.change(path.as_uri(), i, source, first=i == 1)
            result["name"] = name
            result["normalized_source_sha256"] = sha(source.replace(str(WORK), "$WORK"))
            result["ticks"] = (WORK / "ticks.txt").read_text().splitlines() if (WORK / "ticks.txt").exists() else []
            previous_count = len(out["prefix"]["steps"][-1]["ticks"]) if out["prefix"]["steps"] else 0
            result["new_ticks"] = result["ticks"][previous_count:]
            out["prefix"]["steps"].append(result)
    finally:
        server.close()
    out["prefix"]["events"] = server.events
    out["prefix"]["sources"] = [{"name": n, "source": s, "sha256": sha(s)} for n, s in changes]
    raw = json.dumps(out, indent=2, ensure_ascii=False)
    raw = raw.replace(str(WORK), "$WORK").replace(str(LEAN.parent), "$LEAN_BIN")
    (ROOT / "raw.json").write_text(raw + "\n")
    print(json.dumps({"context_exits": {k: v["exit"] for k, v in out["context"].items()},
                      "prefix_steps": [(x["name"], x["new_ticks"], x["elapsed_ms"]) for x in out["prefix"]["steps"]]}, indent=2))


if __name__ == "__main__":
    main()
