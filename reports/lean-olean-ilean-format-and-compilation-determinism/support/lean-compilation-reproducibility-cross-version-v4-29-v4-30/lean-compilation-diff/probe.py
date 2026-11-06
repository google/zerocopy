import hashlib
import json
import os
import select
import shutil
import subprocess
import time
from pathlib import Path

TOOLS = Path(__file__).resolve().parents[2]
ROOT = Path(os.environ.get("ANNEAL_PROBE_ROOT", Path(__file__).resolve().parent)).resolve()
if not ROOT.is_relative_to(TOOLS / "scratch"):
    raise RuntimeError("probe root must stay under .anneal-local-tools/scratch")
PROJECT = ROOT / "project"
TC = Path(os.environ.get("ANNEAL_PROBE_TOOLCHAIN_DIR",
         TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2")).resolve()
if not TC.is_relative_to(TOOLS / "elan/toolchains"):
    raise RuntimeError("toolchain must stay under .anneal-local-tools/elan/toolchains")
TC_NAME = os.environ.get("ANNEAL_PROBE_TOOLCHAIN", "leanprover/lean4:v4.30.0-rc2")
BIN = TC / "bin"
LAKE = BIN / "lake"
LEAN = BIN / "lean"
ENV = os.environ.copy()
ENV.update({
    "ELAN_HOME": str(TOOLS / "elan"),
    "ELAN_TOOLCHAIN": TC_NAME,
    "PATH": str(BIN) + os.pathsep + ENV.get("PATH", ""),
    "LEAN_NUM_THREADS": "1",
    "LAKE_JOBS": "1",
    "LAKE_CACHE_DIR": str(ROOT / "cache"),
    "LAKE_ARTIFACT_CACHE": "true",
})
RUNS = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def file_hash(p):
    return sha(p.read_bytes())

def write(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(data)

def capture(name, argv, *, timeout=30, env=None, stdin=None):
    started = time.monotonic()
    e = ENV.copy()
    e.update(env or {})
    try:
        p = subprocess.run([str(x) for x in argv], cwd=PROJECT, env=e,
                           input=stdin, capture_output=True, text=True,
                           timeout=timeout)
        d = {"name": name, "argv": [str(x) for x in argv], "cwd": str(PROJECT),
             "exit": p.returncode, "elapsed_s": round(time.monotonic()-started, 3),
             "stdout": p.stdout, "stderr": p.stderr}
    except subprocess.TimeoutExpired as ex:
        d = {"name": name, "argv": [str(x) for x in argv], "cwd": str(PROJECT),
             "timeout_s": timeout, "elapsed_s": round(time.monotonic()-started, 3),
             "stdout": (ex.stdout or b"").decode(errors="replace") if isinstance(ex.stdout, bytes) else (ex.stdout or ""),
             "stderr": (ex.stderr or b"").decode(errors="replace") if isinstance(ex.stderr, bytes) else (ex.stderr or "")}
    RUNS.append(d)
    write(ROOT / "runs.json", json.dumps(RUNS, indent=2) + "\n")
    print(name, d.get("exit", "TIMEOUT"), d["elapsed_s"], flush=True)
    return d

def tree_snapshot(root):
    return {str(p.relative_to(root)): {"sha256": file_hash(p), "bytes": p.stat().st_size}
            for p in sorted(root.rglob("*")) if p.is_file()}

def semantic_cli(rec):
    messages = []
    other = []
    for line in rec.get("stdout", "").splitlines():
        try:
            d = json.loads(line)
            if isinstance(d, dict) and "severity" in d:
                messages.append({k:d.get(k) for k in ("severity", "pos", "endPos", "data")})
            else:
                other.append(d)
        except json.JSONDecodeError:
            other.append(line)
    return {"exit": rec.get("exit"), "messages": messages, "other": other}

def lsp_probe():
    goal = PROJECT / "Goal.lean"
    v1 = "import Probe\ntheorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  exact ?_\n"
    v2 = "import Probe\ntheorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  simpa using h\n"
    write(goal, v1)
    events = []
    started = time.monotonic()
    proc = subprocess.Popen([str(LAKE), "--keep-toolchain", "serve"], cwd=PROJECT,
                            env=ENV, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, bufsize=0)
    def rec(direction, value):
        events.append({"elapsed_ms": round((time.monotonic()-started)*1000),
                       "direction": direction, "message": value})
    rec("process", {"argv": [str(LAKE), "--keep-toolchain", "serve"],
                    "cwd": str(PROJECT), "pid": proc.pid})
    buf = b""
    def send(msg):
        raw = json.dumps(msg, separators=(",", ":")).encode()
        proc.stdin.write(b"Content-Length: " + str(len(raw)).encode() + b"\r\n\r\n" + raw)
        proc.stdin.flush()
        rec("client", msg)
    def receive(target):
        nonlocal buf
        deadline = min(started + 29, time.monotonic() + 10)
        while time.monotonic() < deadline:
            while b"\r\n\r\n" in buf:
                head, rest = buf.split(b"\r\n\r\n", 1)
                lengths = [int(x.split(b":",1)[1]) for x in head.split(b"\r\n") if x.lower().startswith(b"content-length:")]
                if not lengths:
                    raise ValueError("LSP frame has no length")
                if len(rest) < lengths[0]:
                    break
                raw, buf = rest[:lengths[0]], rest[lengths[0]:]
                msg = json.loads(raw)
                rec("server", msg)
                if msg.get("method") == "client/registerCapability" and "id" in msg:
                    send({"jsonrpc":"2.0","id":msg["id"],"result":None})
                if target(msg):
                    return msg
            readable, _, _ = select.select([proc.stdout], [], [], max(0,deadline-time.monotonic()))
            if not readable:
                break
            chunk = os.read(proc.stdout.fileno(), 65536)
            if not chunk:
                break
            buf += chunk
        raise TimeoutError("LSP response deadline")
    uri = goal.as_uri()
    results = {}
    try:
        send({"jsonrpc":"2.0","id":1,"method":"initialize","params":{
            "processId":os.getpid(),"rootUri":PROJECT.as_uri(),"capabilities":{},
            "initializationOptions":{"hasWidgets":False}}})
        results["initialize"] = receive(lambda m:m.get("id")==1)
        send({"jsonrpc":"2.0","method":"initialized","params":{}})
        send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{
            "textDocument":{"uri":uri,"languageId":"lean","version":1,"text":v1}}})
        for version, source in ((1,v1),(2,v2)):
            if version == 2:
                send({"jsonrpc":"2.0","method":"textDocument/didChange","params":{
                    "textDocument":{"uri":uri,"version":2},"contentChanges":[{"text":v2}]}})
            wait_id = 10 + version
            send({"jsonrpc":"2.0","id":wait_id,"method":"textDocument/waitForDiagnostics",
                  "params":{"uri":uri,"version":version}})
            results[f"wait_v{version}"] = receive(lambda m:m.get("id")==wait_id)
            for label, char in (("before",2),("after",len(source.splitlines()[2]))):
                query_id = (20 if label == "before" else 30) + version
                send({"jsonrpc":"2.0","id":query_id,"method":"$/lean/plainGoal",
                      "params":{"textDocument":{"uri":uri},"position":{"line":2,"character":char}}})
                results[f"goal_v{version}_{label}"] = receive(lambda m:m.get("id")==query_id)
        send({"jsonrpc":"2.0","id":40,"method":"$/lean/plainGoal",
              "params":{"textDocument":{"uri":uri},"position":{"line":0,"character":0}}})
        results["goal_outside_tactic"] = receive(lambda m:m.get("id")==40)
        send({"jsonrpc":"2.0","id":41,"method":"$/lean/nonexistentProbe",
              "params":{"textDocument":{"uri":uri}}})
        try:
            results["unsupported_method"] = receive(lambda m:m.get("id")==41)
        except TimeoutError as ex:
            results["unsupported_method"] = {"missing_response":repr(ex)}
        send({"jsonrpc":"2.0","id":99,"method":"shutdown","params":None})
        results["shutdown"] = receive(lambda m:m.get("id")==99)
        send({"jsonrpc":"2.0","method":"exit"})
    except Exception as ex:
        results["exception"] = repr(ex)
    finally:
        try:
            proc.wait(timeout=max(0.1, min(2, started+30-time.monotonic())))
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait(timeout=2)
        rec("process_exit", {"exit":proc.returncode,"stderr":proc.stderr.read().decode(errors="replace")})
        write(ROOT/"lsp-raw.json",json.dumps(events,indent=2)+"\n")
        write(ROOT/"lsp-results.json",json.dumps(results,indent=2)+"\n")
    return results

def main():
    ROOT.mkdir(parents=True, exist_ok=True)
    if not LEAN.is_file() or not LAKE.is_file():
        raise RuntimeError("requested local Lean/Lake binaries are absent")
    usage = shutil.disk_usage(ROOT)
    if usage.free < 1024**3:
        raise RuntimeError("less than 1 GiB free before probe")
    PROJECT.mkdir(exist_ok=True)
    mem = capture("host_memory_pressure", ["/usr/bin/memory_pressure","-Q"])
    if mem.get("exit") != 0:
        raise RuntimeError("cannot inspect memory pressure")
    write(ROOT/"bounds.json", json.dumps({"free_bytes_before":usage.free,
        "memory_pressure": mem["stdout"], "scratch_cap_bytes":1024**3,
        "child_timeout_s":30,"concurrent_servers":1},indent=2)+"\n")
    write(PROJECT/"lean-toolchain",TC_NAME+"\n")
    write(PROJECT/"lakefile.lean","import Lake\nopen Lake DSL\npackage compilation_probe\n@[default_target]\nlean_lib Probe\n")
    write(PROJECT/"lake-manifest.json",json.dumps({"version":"1.2.0","packagesDir":".lake/packages",
        "packages":[],"name":"compilation_probe","lakeDir":".lake","fixedToolchain":False},indent=2)+"\n")
    write(PROJECT/"Probe/Base.lean","namespace Probe\ndef inc (n : Nat) : Nat := n + 1\ntheorem inc_zero : inc 0 = 1 := by rfl\nend Probe\n")
    write(PROJECT/"Probe.lean","import Probe.Base\nnamespace Probe\ntheorem inc_four : inc 4 = 5 := by rfl\n#eval inc 4\n#print axioms inc_four\nend Probe\n")
    write(PROJECT/"Goal.lean","import Probe\ntheorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  exact ?_\n")
    inputs = {str(p.relative_to(PROJECT)):file_hash(p) for p in
              [PROJECT/"lean-toolchain",PROJECT/"lakefile.lean",PROJECT/"lake-manifest.json",
               PROJECT/"Probe/Base.lean",PROJECT/"Probe.lean",PROJECT/"Goal.lean"]}
    write(ROOT/"inputs.json",json.dumps(inputs,indent=2)+"\n")
    shutil.rmtree(ROOT/"cache",ignore_errors=True)
    builds = {}
    for name, cache in (("clean-1",False),("clean-2",False),("cache-seed",True),("cache-reuse-1",True),("cache-reuse-2",True)):
        shutil.rmtree(PROJECT/".lake",ignore_errors=True)
        mode_env = {} if cache else {"LAKE_ARTIFACT_CACHE":"false","LAKE_CACHE_DIR":""}
        args = [LAKE,"--keep-toolchain"] + ([] if cache else ["--no-cache"]) + ["--old","build","Probe"]
        build = capture(name,args,env=mode_env)
        snap = tree_snapshot(PROJECT/".lake/build") if (PROJECT/".lake/build").exists() else {}
        builds[name] = {"build":build,"artifacts":snap,"cache_files":len(tree_snapshot(ROOT/"cache")) if (ROOT/"cache").exists() else 0}
        if build.get("exit") != 0: break
        capture(name+"-setup",[LAKE,"--keep-toolchain","setup-file","Probe.lean"],env=mode_env)
        capture(name+"-batch",[LAKE,"--keep-toolchain","env","lean","--json","Probe.lean"],env=mode_env)
        if sum(p.stat().st_size for p in ROOT.rglob("*") if p.is_file()) > 1024**3:
            raise RuntimeError("scratch cap exceeded")
    write(ROOT/"builds.json",json.dumps(builds,indent=2)+"\n")
    capture("warm-no-build",[LAKE,"--keep-toolchain","--no-build","build","Probe"])
    capture("goal-setup",[LAKE,"--keep-toolchain","setup-file","Goal.lean"])
    capture("goal-batch-v1",[LAKE,"--keep-toolchain","env","lean","--json","Goal.lean"])
    lsp_probe()
    capture("materialize-without-cache",[LAKE,"--keep-toolchain","--no-cache","--old","build","Probe"],
            env={"LAKE_ARTIFACT_CACHE":"false","LAKE_CACHE_DIR":""})
    write(ROOT/"materialized-artifacts.json",json.dumps(tree_snapshot(PROJECT/".lake/build"),indent=2)+"\n")
    capture("materialized-batch",[LAKE,"--keep-toolchain","env","lean","--json","Probe.lean"],
            env={"LAKE_ARTIFACT_CACHE":"false","LAKE_CACHE_DIR":""})
    mode_env = {"LAKE_ARTIFACT_CACHE":"false","LAKE_CACHE_DIR":""}
    capture("materialized-goal-setup",[LAKE,"--keep-toolchain","setup-file","Goal.lean"],env=mode_env)
    capture("materialized-goal-batch-v1",[LAKE,"--keep-toolchain","env","lean","--json","Goal.lean"],env=mode_env)
    goal_file = PROJECT/"Goal.lean"
    original_goal = goal_file.read_text()
    write(goal_file,"import Probe\ntheorem demo (n : Nat) (h : n = 0) : n + 0 = 0 := by\n  simpa using h\n")
    try:
        capture("materialized-goal-batch-v2",[LAKE,"--keep-toolchain","env","lean","--json","Goal.lean"],env=mode_env)
    finally:
        write(goal_file,original_goal)
    write(ROOT/"identities.json",json.dumps({"lean_version":capture("lean-version",[LEAN,"--version"])["stdout"],
          "lake_version":capture("lake-version",[LAKE,"--version"])["stdout"],
          "lean_sha256":file_hash(LEAN),"lake_sha256":file_hash(LAKE)},indent=2)+"\n")
    write(ROOT/"summary.json",json.dumps({"inputs":inputs,
          "artifact_equal_clean":builds.get("clean-1",{}).get("artifacts")==builds.get("clean-2",{}).get("artifacts"),
          "artifact_equal_cache":builds.get("cache-reuse-1",{}).get("artifacts")==builds.get("cache-reuse-2",{}).get("artifacts"),
          "scratch_bytes":sum(p.stat().st_size for p in ROOT.rglob("*") if p.is_file())},indent=2)+"\n")

if __name__ == "__main__": main()
