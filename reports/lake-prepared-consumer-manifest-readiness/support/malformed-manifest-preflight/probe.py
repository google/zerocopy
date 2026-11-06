#!/usr/bin/env python3
"""One-shot guarded Lake valid/malformed/restored manifest entrypoint probe."""
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
    before = inv(WORK)
    p = subprocess.Popen(argv, cwd=cwd, env=env, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True, preexec_fn=prep_child, bufsize=0)
    guard = Guard(p)
    errors = []; received = b""; sent = []; errchunks = []
    init = {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {
        "processId": os.getpid(), "rootUri": cwd.as_uri(), "capabilities": {},
        "initializationOptions": {"hasWidgets": False}}}
    try:
        p.stdin.write(frame(init)); p.stdin.flush(); sent.append(init)
    except (BrokenPipeError, OSError) as exc: errors.append(f"initialize_write:{type(exc).__name__}")
    deadline = time.monotonic() + 10
    init_response = None
    while time.monotonic() < deadline and p.poll() is None and not guard.reason:
        ready, _, _ = select.select([p.stdout, p.stderr], [], [], .05)
        if p.stderr in ready: errchunks.append(os.read(p.stderr.fileno(), 65536))
        if p.stdout in ready:
            chunk = os.read(p.stdout.fileno(), 65536)
            if not chunk: break
            received += chunk
            matches = [m for m in decoded_messages(received) if m.get("id") == 1 and "result" in m]
            if matches:
                init_response = matches[0]
                break
    if init_response is not None and p.poll() is None and not guard.reason:
        for msg in ({"jsonrpc":"2.0","method":"initialized","params":{}},
                    {"jsonrpc":"2.0","id":2,"method":"shutdown","params":None}):
            try: p.stdin.write(frame(msg)); p.stdin.flush(); sent.append(msg)
            except (BrokenPipeError, OSError) as exc: errors.append(f"shutdown_write:{type(exc).__name__}")
        stop_by = time.monotonic() + 5
        while time.monotonic() < stop_by and p.poll() is None and not guard.reason:
            ready, _, _ = select.select([p.stdout, p.stderr], [], [], .05)
            if p.stderr in ready: errchunks.append(os.read(p.stderr.fileno(), 65536))
            if p.stdout in ready:
                chunk = os.read(p.stdout.fileno(), 65536)
                if not chunk: break
                received += chunk
                if any(m.get("id") == 2 and "result" in m for m in decoded_messages(received)):
                    try:
                        msg = {"jsonrpc":"2.0","method":"exit"}
                        p.stdin.write(frame(msg)); p.stdin.flush(); sent.append(msg)
                    except (BrokenPipeError, OSError): pass
                    break
    if p.poll() is None:
        try: p.wait(timeout=3)
        except subprocess.TimeoutExpired:
            errors.append("server_stop_timeout")
            os.killpg(p.pid, signal.SIGKILL); p.wait(timeout=3)
    # Bounded drain: descendants may retain inherited pipe descriptors.
    for _ in range(10):
        ready, _, _ = select.select([p.stdout, p.stderr], [], [], .02)
        if not ready: break
        if p.stdout in ready: received += os.read(p.stdout.fileno(), 65536)
        if p.stderr in ready: errchunks.append(os.read(p.stderr.fileno(), 65536))
    stderr = b"".join(errchunks)
    guard.finish()
    return record(label, p, env, argv, cwd, before, received, stderr, guard, result,
                  {"sent_messages": sent, "decoded_messages": decoded_messages(received),
                   "initialize_result": init_response, "client_errors": errors})


def main():
    assert not WORK.exists() and not (ROOT / "results.json").exists(), "one-shot absent work/result required"
    assert sha(LAKE.read_bytes()) == LAKE_SHA and sha(LEAN.read_bytes()) == LEAN_SHA
    admission = {"memory": memory(), "disk_free": shutil.disk_usage(ROOT).free}
    result = {"schema":1,"status":"prepared","admission":admission,"lake_sha256":LAKE_SHA,
              "lean_sha256":LEAN_SHA,"fixture_sha256":{
                  "producer_config":sha(PRODUCER_CONFIG),"producer_source":sha(PRODUCER_SOURCE),
                  "consumer_config":sha(CONSUMER_CONFIG),"consumer_source":sha(CONSUMER_SOURCE),
                  "valid_manifest":sha(manifest("consumer",True)),"malformed_manifest":sha(MALFORMED)},
              "runs":[],"phases":{}}
    save(result)
    if admission["memory"]["fraction"] <= .30 or admission["disk_free"] <= 10*1024**3:
        result["status"]="admission_denied";save(result);return
    WORK.mkdir(); dep, consumer = make_fixture()
    home, xdg, cache = WORK/"home",WORK/"xdg",WORK/"cache"
    for x in (home,xdg,cache):x.mkdir()
    env = dict(os.environ)
    env.update({"HOME":str(home),"XDG_CACHE_HOME":str(xdg),"ELAN_TOOLCHAIN":TOOLCHAIN,
                "LEAN_NUM_THREADS":"1","LAKE_NO_NET":"1","LAKE_CACHE_DIR":str(cache),
                "PATH":str(BIN)+os.pathsep+env.get("PATH", "")})
    env.pop("LEAN_PATH", None)
    def lake(*args):return [str(LAKE),"--keep-toolchain","--no-ansi",*args]
    manifest_path = consumer/"lake-manifest.json"
    good = manifest_path.read_bytes()
    try:
        seed_env = dict(env, LAKE_ARTIFACT_CACHE="true", LAKE_NO_CACHE="0")
        initial = command("seed-build",lake("build","Generated"),consumer,seed_env,result)
        if initial["exit"] != 0: raise RuntimeError("seed build failed")
        result["seed_cache"] = inv(cache)
        result["seed_producer"] = inv(dep)
        save(result)
        no_env = dict(env, LAKE_ARTIFACT_CACHE="false", LAKE_NO_CACHE="1")
        for phase in ("valid","malformed","restored"):
            if phase == "malformed":manifest_path.write_bytes(MALFORMED)
            if phase == "restored":manifest_path.write_bytes(good)
            result["phases"][phase] = {"manifest_sha256":sha(manifest_path.read_bytes()),
                                       "producer_before":inv(dep),"cache_before":inv(cache)}
            command(phase+"-setup",lake("--no-build","--no-cache","setup-file",str(consumer/"Generated.lean")),consumer,no_env,result)
            command(phase+"-batch",lake("--no-build","--no-cache","env","lean","--json","Generated.lean"),consumer,no_env,result)
            server(phase+"-server",lake("--no-build","--no-cache","serve"),consumer,no_env,result)
            if phase == "malformed":
                direct_env = dict(no_env, LEAN_PATH=str(dep/".lake/build/lib/lean"))
                command("malformed-direct-lean",[str(LEAN),"--json","Generated.lean"],consumer,direct_env,result)
            result["phases"][phase].update({"producer_after":inv(dep),"cache_after":inv(cache),
                                            "consumer_after":inv(consumer)})
            save(result)
        result["status"]="completed"
    except Exception as exc:
        result["status"]="stopped";result["error"]=str(exc)
    finally:
        result["final_memory"]=memory();result["final_disk_free"]=shutil.disk_usage(ROOT).free
        result["final_scratch_bytes"]=scratch();save(result)


if __name__ == "__main__": main()
