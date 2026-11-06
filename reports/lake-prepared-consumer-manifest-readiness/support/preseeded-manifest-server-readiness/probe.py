#!/usr/bin/env python3
"""One-shot guarded Lake manifest and server didOpen readiness probe."""
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import select
import shutil
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
BIN = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin")
LAKE, LEAN = BIN / "lake", BIN / "lean"
LAKE_SHA = "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
LEAN_SHA = "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
MALFORMED = b"{\n"
PRODUCER_CONFIG = b"import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n"
PRODUCER_SOURCE = b"def depValue : Nat := 7\n"
CONSUMER_CONFIG = b'import Lake\nopen Lake DSL\nrequire probe_dep from "../producer"\npackage consumer\n@[default_target]\nlean_lib Generated\n'
CONSUMER_SOURCE = b"import Dep\ntheorem generatedEq : depValue = 7 := by rfl\n#eval depValue\n"


def sha(data): return hashlib.sha256(data).hexdigest()


def inv(root):
    return {str(p.relative_to(root)): {"sha256": sha(p.read_bytes()), "size": p.stat().st_size,
                                        "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}


def memory():
    txt = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", txt).group(1))
    vals = {k: int(v.replace(".", "")) for k, v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)", txt)}
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"]).strip())
    return {"fraction": page * sum(vals[k] for k in ("free", "inactive", "speculative")) / total,
            "page_bytes": page, "total_bytes": total, "pages": vals}


def scratch():
    return sum(p.stat().st_size for p in WORK.rglob("*") if p.is_file() and not p.is_symlink())


def ps_group(pid):
    raw = subprocess.check_output(["ps", "-axo", "pid=,ppid=,pgid=,rss=,comm="], text=True)
    out = []
    for line in raw.splitlines():
        x = line.split(None, 4)
        if len(x) == 5 and all(v.isdigit() for v in x[:4]) and int(x[2]) == pid:
            out.append({"pid": int(x[0]), "ppid": int(x[1]), "rss_kib": int(x[3]), "comm": x[4]})
    return out


def manifest(name, dependency=False):
    packages = [{"type": "path", "scope": "", "name": "probe_dep", "manifestFile": "lake-manifest.json",
                 "inherited": False, "dir": "../producer", "configFile": "lakefile.lean"}] if dependency else []
    return (json.dumps({"version": "1.2.0", "packagesDir": ".lake/packages", "packages": packages,
                        "name": name, "lakeDir": ".lake", "fixedToolchain": False}, indent=2) + "\n").encode()


def make_fixture():
    dep, consumer = WORK / "producer", WORK / "consumer"
    dep.mkdir(parents=True); consumer.mkdir()
    files = {dep / "lakefile.lean": PRODUCER_CONFIG, dep / "Dep.lean": PRODUCER_SOURCE,
             dep / "lake-manifest.json": manifest("probe_dep"),
             consumer / "lakefile.lean": CONSUMER_CONFIG,
             consumer / "Generated.lean": CONSUMER_SOURCE,
             consumer / "lake-manifest.json": manifest("consumer", True)}
    for path, data in files.items(): path.write_bytes(data)
    for root in (dep, consumer): (root / "lean-toolchain").write_text(TOOLCHAIN + "\n")
    return dep, consumer


def save(result):
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def prep_child(): resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


class Guard:
    def __init__(self, p):
        self.p = p; self.start = time.monotonic(); self.samples = []; self.reason = None
        self.stop = threading.Event(); self.thread = threading.Thread(target=self.loop, daemon=True)
        self.thread.start()
    def loop(self):
        while not self.stop.is_set() and self.p.poll() is None:
            elapsed = time.monotonic() - self.start
            mm = memory()["fraction"]; disk = shutil.disk_usage(ROOT).free
            size = scratch(); members = ps_group(self.p.pid)
            rss = sum(x["rss_kib"] for x in members)
            self.samples.append({"elapsed": round(elapsed, 4), "reclaimable": mm,
                                 "disk_free": disk, "scratch_bytes": size,
                                 "group_rss_kib": rss, "members": members})
            if mm < .20: self.reason = "reclaimable_below_20_percent"
            elif disk < 10 * 1024 ** 3: self.reason = "disk_below_10_gib"
            elif size > 100 * 1024 ** 2: self.reason = "scratch_over_100_mib"
            elif rss > 1200 * 1024: self.reason = "group_rss_over_1200_mib"
            elif elapsed > 30: self.reason = "process_over_30_seconds"
            if self.reason:
                try: os.killpg(self.p.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                break
            self.stop.wait(.08)
    def finish(self):
        self.stop.set(); self.thread.join(timeout=2)


def record(label, p, env, argv, cwd, before, stdout, stderr, guard, result, extra=None):
    raw = ROOT / "raw"; raw.mkdir(exist_ok=True)
    (raw / f"{label}.stdout").write_bytes(stdout)
    (raw / f"{label}.stderr").write_bytes(stderr)
    x = {"label": label, "argv": argv, "cwd": str(cwd), "pid": p.pid, "exit": p.returncode,
         "elapsed": round(time.monotonic() - guard.start, 4), "abort": guard.reason,
         "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr),
         "before": before, "after": inv(WORK), "resource_samples": guard.samples,
         "env_overrides": {k: env.get(k) for k in ("HOME", "XDG_CACHE_HOME", "LEAN_NUM_THREADS", "LAKE_NO_NET", "LAKE_NO_CACHE", "LAKE_ARTIFACT_CACHE", "LAKE_CACHE_DIR", "LEAN_PATH", "ELAN_TOOLCHAIN")}}
    if extra: x.update(extra)
    result["runs"].append(x); save(result)
    if guard.reason: raise RuntimeError(f"guard: {guard.reason}")
    return x


def command(label, argv, cwd, env, result):
    before = inv(WORK)
    p = subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         start_new_session=True, preexec_fn=prep_child)
    guard = Guard(p)
    try: stdout, stderr = p.communicate(timeout=32)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); stdout, stderr = p.communicate()
        guard.reason = guard.reason or "communicate_timeout"
    guard.finish()
    return record(label, p, env, argv, cwd, before, stdout, stderr, guard, result)


def frame(message):
    b = json.dumps(message, separators=(",", ":")).encode()
    return b"Content-Length: " + str(len(b)).encode() + b"\r\n\r\n" + b


def decoded_messages(raw):
    msgs = []; rest = raw
    while b"\r\n\r\n" in rest:
        header, body = rest.split(b"\r\n\r\n", 1)
        m = re.search(rb"Content-Length:\s*(\d+)", header, re.I)
        if not m: break
        length = int(m.group(1))
        if len(body) < length: break
        try: msgs.append(json.loads(body[:length]))
        except json.JSONDecodeError: break
        rest = body[length:]
    return msgs


def server(label, argv, cwd, env, result):
    admission = {"memory": memory(), "disk_free": shutil.disk_usage(ROOT).free}
    result.setdefault("server_admissions", {})[label] = admission
    save(result)
    if admission["memory"]["fraction"] <= .30 or admission["disk_free"] <= 10*1024**3:
        raise RuntimeError(f"{label}:fresh_admission_denied")
    before = inv(WORK)
    p = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True, preexec_fn=prep_child, bufsize=0)
    guard = Guard(p)
    errors = []; received = b""; sent = []; errchunks = []; events = []
    last_count = 0
    def send(msg):
        p.stdin.write(frame(msg)); p.stdin.flush()
        sent.append({"elapsed": round(time.monotonic()-guard.start,4), "message": msg})
    def pump(deadline, predicate=None):
        nonlocal received, last_count
        while time.monotonic() < deadline and p.poll() is None and not guard.reason:
            ready, _, _ = select.select([p.stdout, p.stderr], [], [], .05)
            if p.stderr in ready:
                chunk = os.read(p.stderr.fileno(), 65536)
                if chunk: errchunks.append(chunk)
            if p.stdout in ready:
                chunk = os.read(p.stdout.fileno(), 65536)
                if chunk: received += chunk
            msgs = decoded_messages(received)
            for msg in msgs[last_count:]:
                events.append({"elapsed": round(time.monotonic()-guard.start,4), "message":msg})
            last_count=len(msgs)
            if predicate is not None and predicate(msgs): return True
        return False
    init = {"jsonrpc":"2.0","id":1,"method":"initialize","params":{
        "processId":os.getpid(),"rootUri":cwd.as_uri(),"capabilities":{},
        "initializationOptions":{"hasWidgets":False}}}
    opened=False; first_diag=False; wait_elapsed=None
    readiness_quiescent=False; goal_response=None
    try:
        send(init)
        got_init = pump(time.monotonic()+8, lambda msgs:any(m.get("id")==1 and "result" in m for m in msgs))
        if got_init and not guard.reason:
            send({"jsonrpc":"2.0","method":"initialized","params":{}})
            uri=(cwd/"Generated.lean").as_uri()
            source=(cwd/"Generated.lean").read_text()
            send({"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{
                "uri":uri,"languageId":"lean4","version":1,"text":source}}})
            opened=True
            wait_start=time.monotonic()
            settle_by=min(wait_start+8,guard.start+20)
            # Require a diagnostic and a final processing-empty publication, then
            # a quiet interval. A bounded timeout is recorded, never interpreted as ready.
            while time.monotonic()<settle_by and p.poll() is None and not guard.reason:
                pump(min(time.monotonic()+.1,settle_by))
                diags=[e for e in events if e["message"].get("method")=="textDocument/publishDiagnostics"
                       and e["message"].get("params",{}).get("uri")==uri]
                progs=[e for e in events if e["message"].get("method")=="$/lean/fileProgress"
                       and e["message"].get("params",{}).get("textDocument",{}).get("uri")==uri]
                first_diag=bool(diags)
                last_event=events[-1]["elapsed"] if events else 0
                if first_diag and progs and progs[-1]["message"]["params"].get("processing")==[] and (
                        time.monotonic()-guard.start-last_event)>=.7:
                    readiness_quiescent=True
                    break
            wait_elapsed=round(time.monotonic()-wait_start,4)
            # The result is an observation even when readiness timed out.
            send({"jsonrpc":"2.0","id":2,"method":"$/lean/plainGoal","params":{
                "textDocument":{"uri":uri},"position":{"line":1,"character":40}}})
            got_goal=pump(time.monotonic()+5,lambda msgs:any(m.get("id")==2 and
                          ("result" in m or "error" in m) for m in msgs))
            if got_goal:
                goal_response=next(m for m in decoded_messages(received) if m.get("id")==2 and
                                   ("result" in m or "error" in m))
            send({"jsonrpc":"2.0","id":3,"method":"shutdown","params":None})
            got_shutdown=pump(time.monotonic()+4,lambda msgs:any(m.get("id")==3 and
                              "result" in m for m in msgs))
            if got_shutdown:
                send({"jsonrpc":"2.0","method":"exit"})
        else:
            errors.append("initialize_missing_or_guard")
    except (BrokenPipeError,OSError) as exc:
        errors.append(type(exc).__name__)
    if p.poll() is None:
        try: p.wait(timeout=3)
        except subprocess.TimeoutExpired:
            errors.append("server_stop_timeout")
            os.killpg(p.pid, signal.SIGKILL); p.wait(timeout=3)
    for _ in range(10):
        ready,_,_=select.select([p.stdout,p.stderr],[],[],.02)
        if not ready: break
        if p.stdout in ready:
            chunk=os.read(p.stdout.fileno(),65536)
            if chunk: received+=chunk
        if p.stderr in ready:
            chunk=os.read(p.stderr.fileno(),65536)
            if chunk: errchunks.append(chunk)
    msgs=decoded_messages(received)
    for msg in msgs[last_count:]:
        events.append({"elapsed":round(time.monotonic()-guard.start,4),"message":msg})
    guard.finish()
    return record(label,p,env,argv,cwd,before,received,b"".join(errchunks),guard,result,{
        "sent_events":sent,"received_events":events,"decoded_messages":msgs,
        "client_errors":errors,"opened":opened,"first_diagnostic_observed":first_diag,
        "diagnostic_wait_seconds":wait_elapsed,"readiness_quiescent":readiness_quiescent,
        "goal_response":goal_response})


def main():
    assert WORK.exists() and not (ROOT/"results.json").exists(), "preseed work and absent results required"
    assert sha(LAKE.read_bytes())==LAKE_SHA and sha(LEAN.read_bytes())==LEAN_SHA
    preseed=json.loads((ROOT/"preseed.json").read_text())
    published=Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/scratch/20260927-reference-experiments/reference-publish/reports/anneal-3731-i092-malformed-manifest-preflight-2026-09-30")
    assert preseed["source_package"]==published.name
    assert sha((published/"results.json").read_bytes())==preseed["source_results_sha256"]
    copied={str(p.relative_to(WORK)):sha(p.read_bytes()) for p in WORK.rglob("*") if p.is_file()}
    assert copied==preseed["work_sha256"] and len(copied)==36
    dep,consumer=WORK/"producer",WORK/"consumer"
    manifest_path=consumer/"lake-manifest.json"
    good=manifest("consumer",True);bad=MALFORMED;semantic=manifest("consumer",False)
    assert manifest_path.read_bytes()==good
    assert (dep/"Dep.lean").read_bytes()==PRODUCER_SOURCE
    assert (consumer/"Generated.lean").read_bytes()==CONSUMER_SOURCE
    assert sha((dep/".lake/build/lib/lean/Dep.olean").read_bytes())=="cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b"
    fixtures=ROOT/"fixtures";fixtures.mkdir()
    for name,data in (("valid",good),("malformed",bad),("semantic-no-dependency",semantic)):
        (fixtures/f"{name}-lake-manifest.json").write_bytes(data)
    admission={"memory":memory(),"disk_free":shutil.disk_usage(ROOT).free}
    result={"schema":2,"status":"prepared","admission":admission,"lake_sha256":LAKE_SHA,
            "lean_sha256":LEAN_SHA,"preseed_sha256":sha((ROOT/"preseed.json").read_bytes()),
            "manifest_sha256":{"valid":sha(good),"malformed":sha(bad),
                "semantic-no-dependency":sha(semantic)},
            "producer_source_sha256":sha(PRODUCER_SOURCE),
            "consumer_source_sha256":sha(CONSUMER_SOURCE),"runs":[],"phases":{}}
    save(result)
    if admission["memory"]["fraction"]<=.30 or admission["disk_free"]<=10*1024**3:
        result["status"]="admission_denied";save(result);return
    home,xdg,cache=WORK/"home",WORK/"xdg",WORK/"cache"
    assert home.is_dir() and xdg.is_dir() and cache.is_dir()
    env=dict(os.environ)
    env.update({"HOME":str(home),"XDG_CACHE_HOME":str(xdg),"ELAN_TOOLCHAIN":TOOLCHAIN,
                "LEAN_NUM_THREADS":"1","LAKE_NO_NET":"1","LAKE_CACHE_DIR":str(cache),
                "LAKE_ARTIFACT_CACHE":"false","LAKE_NO_CACHE":"1",
                "PATH":str(BIN)+os.pathsep+env.get("PATH","")})
    env.pop("LEAN_PATH",None)
    def lake(*args):return [str(LAKE),"--keep-toolchain","--no-ansi",*args]
    try:
        for phase,data in (("valid",good),("malformed",bad),("semantic-no-dependency",semantic)):
            if phase!="valid":manifest_path.write_bytes(data)
            result["phases"][phase]={"manifest_sha256":sha(manifest_path.read_bytes()),
                                     "producer_before":inv(dep),"cache_before":inv(cache)}
            server(phase+"-server",lake("--no-build","--no-cache","serve"),consumer,env,result)
            result["phases"][phase].update({"producer_after":inv(dep),"cache_after":inv(cache),
                                             "consumer_after":inv(consumer)})
            save(result)
        manifest_path.write_bytes(good)
        result["restored_manifest_sha256"]=sha(manifest_path.read_bytes())
        result["status"]="completed"
    except Exception as exc:
        result["status"]="stopped";result["error"]=str(exc)
    finally:
        result["final_memory"]=memory();result["final_disk_free"]=shutil.disk_usage(ROOT).free
        result["final_scratch_bytes"]=scratch();save(result)


if __name__=="__main__":main()
