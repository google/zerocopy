#!/usr/bin/env python3
"""Guarded package-local Lake output interruption and repair, one acquisition."""
import hashlib
import argparse
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parent
WORK = ROOT / "work"
LAKE = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake")
LEAN = LAKE.with_name("lean")
LAKE_SHA = "9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb"
LEAN_SHA = "b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997"
TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
LIMIT_RSS_KIB = 1200 * 1024
LIMIT_DISK = 10 * 1024 ** 3
LIMIT_SCRATCH = 100 * 1024 ** 2
CONFIG = b'import Lake\nopen Lake DSL\npackage probe_dep\n@[default_target]\nlean_lib Dep\n'
OLD = b'def depValue : Nat := 7\n'
NEW = b'def depValue : Nat := 9\n'
CHECK = b'import Dep\n#eval depValue\n'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def inventory(root):
    return {str(p.relative_to(root)): {"sha256": sha(p.read_bytes()), "size": p.stat().st_size,
                                        "mtime_ns": p.stat().st_mtime_ns}
            for p in sorted(root.rglob("*")) if p.is_file() and not p.is_symlink()}


def mem():
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"]).strip())
    txt = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", txt).group(1))
    vals = {k: int(v.replace(".", "")) for k, v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)", txt)}
    return {"fraction": page * sum(vals[k] for k in ("free", "inactive", "speculative")) / total,
            "page_bytes": page, "total_bytes": total, "pages": vals}


def scratch():
    return sum(p.stat().st_size for p in WORK.rglob("*") if p.is_file() and not p.is_symlink())


def group_ps(pgid):
    raw = subprocess.check_output(["ps", "-axo", "pid=,ppid=,pgid=,rss=,comm="], text=True)
    rows = []
    for line in raw.splitlines():
        x = line.split(None, 4)
        if len(x) == 5 and all(y.isdigit() for y in x[:4]) and int(x[2]) == pgid:
            rows.append({"pid": int(x[0]), "ppid": int(x[1]), "pgid": int(x[2]),
                         "rss_kib": int(x[3]), "comm": x[4]})
    return rows


def save(result):
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")


def preexec(limit):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    if limit is not None:
        signal.signal(signal.SIGXFSZ, signal.SIG_DFL)
        resource.setrlimit(resource.RLIMIT_FSIZE, (limit, limit))


def invoke(label, argv, cwd, env, result, *, limit=None, track=None):
    before = inventory(WORK)
    start = time.monotonic()
    p = subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         start_new_session=True, preexec_fn=lambda: preexec(limit))
    payload = [None]
    thread = threading.Thread(target=lambda: payload.__setitem__(0, p.communicate()), daemon=True)
    thread.start()
    samples, events = [], []
    last = inventory(track) if track else None
    aborted = None
    next_resource = 0.0
    while thread.is_alive():
        elapsed = time.monotonic() - start
        if track:
            current = inventory(track)
            changed = {k: v for k, v in current.items() if last is None or last.get(k) != v}
            removed = sorted(set(last or {}) - set(current))
            if changed or removed:
                events.append({"elapsed": round(elapsed, 6), "changed": changed, "removed": removed})
            last = current
        if elapsed >= next_resource:
            mm = mem()
            free = shutil.disk_usage(ROOT).free
            sz = scratch()
            members = group_ps(p.pid)
            rss = sum(m["rss_kib"] for m in members)
            samples.append({"elapsed": round(elapsed, 6), "reclaimable": mm["fraction"],
                            "disk_free": free, "scratch_bytes": sz, "group_rss_kib": rss,
                            "members": members})
            if mm["fraction"] < .20: aborted = "memory_below_20_percent"
            elif free < LIMIT_DISK: aborted = "disk_below_10_gib"
            elif sz > LIMIT_SCRATCH: aborted = "scratch_over_100_mib"
            elif rss > LIMIT_RSS_KIB: aborted = "group_rss_over_1200_mib"
            next_resource = elapsed + .1
        if elapsed > 30: aborted = "process_over_30_seconds"
        if aborted:
            os.killpg(p.pid, signal.SIGKILL)
            break
        thread.join(.005)
    thread.join(3)
    stdout, stderr = payload[0] if payload[0] is not None else (b"", b"")
    raw = ROOT / "raw"
    raw.mkdir(exist_ok=True)
    (raw / f"{label}.stdout").write_bytes(stdout)
    (raw / f"{label}.stderr").write_bytes(stderr)
    rec = {"label": label, "pid": p.pid, "cwd": str(cwd), "argv": argv,
           "env_overrides": {k: env.get(k) for k in ("HOME", "XDG_CACHE_HOME", "LEAN_NUM_THREADS", "LAKE_NO_CACHE", "LAKE_NO_NET", "LAKE_ARTIFACT_CACHE", "ELAN_TOOLCHAIN", "LEAN_PATH")},
           "rlimit_fsize_bytes": limit, "exit": p.returncode, "aborted": aborted,
           "elapsed": round(time.monotonic() - start, 6), "stdout_sha256": sha(stdout),
           "stderr_sha256": sha(stderr), "before": before, "after": inventory(WORK),
           "resource_samples": samples, "observed_file_events": events}
    result["runs"].append(rec)
    save(result)
    if aborted:
        raise RuntimeError(f"guard: {aborted}")
    return rec


def snapshot(label, producer, result):
    files = inventory(producer)
    target = ROOT / "snapshots" / label
    target.mkdir(parents=True)
    for rel in files:
        dst = target / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(producer / rel, dst)
    result["snapshots"][label] = files
    save(result)


def main(phase):
    assert sha(LAKE.read_bytes()) == LAKE_SHA and sha(LEAN.read_bytes()) == LEAN_SHA
    if phase == "prepare":
        assert not WORK.exists() and not (ROOT / "results.json").exists(), "one-shot absent path required"
        admission = {"memory": mem(), "disk_free": shutil.disk_usage(ROOT).free}
        result = {"schema": 1, "status": "prepared", "lake_sha256": LAKE_SHA,
                  "lean_sha256": LEAN_SHA, "admission": admission, "runs": [], "snapshots": {},
                  "fixture_sha256": {"lakefile": sha(CONFIG), "old": sha(OLD), "new": sha(NEW), "check": sha(CHECK)}}
        save(result)
        if admission["memory"]["fraction"] <= .30 or admission["disk_free"] <= LIMIT_DISK:
            result["status"] = "admission_denied"
            save(result)
            return
        WORK.mkdir()
    else:
        assert phase == "continue" and WORK.is_dir() and (ROOT / "results.json").is_file()
        result = json.loads((ROOT / "results.json").read_text())
        assert result["status"] == "baseline_ready" and result["chosen_limit_bytes"] > 512
        admission = {"memory": mem(), "disk_free": shutil.disk_usage(ROOT).free}
        result["continuation_admission"] = admission
        save(result)
        if admission["memory"]["fraction"] <= .30 or admission["disk_free"] <= LIMIT_DISK:
            result["status"] = "continuation_admission_denied"
            save(result)
            return
    producer = WORK / "producer"
    if phase == "prepare":
        producer.mkdir()
        (producer / "lakefile.lean").write_bytes(CONFIG)
        (producer / "Dep.lean").write_bytes(OLD)
        (producer / "lean-toolchain").write_text(TOOLCHAIN + "\n")
        (producer / "Check.lean").write_bytes(CHECK)
    home = WORK / "home"
    cache = WORK / "cache"
    if phase == "prepare":
        home.mkdir()
        cache.mkdir()
    env = dict(os.environ)
    env.update({"HOME": str(home), "XDG_CACHE_HOME": str(cache), "ELAN_TOOLCHAIN": TOOLCHAIN,
                "LEAN_NUM_THREADS": "1", "LAKE_NO_CACHE": "1", "LAKE_NO_NET": "1",
                "LAKE_ARTIFACT_CACHE": "false", "PATH": str(LAKE.parent) + os.pathsep + env.get("PATH", ""),
                "LEAN_PATH": str(producer / ".lake/build/lib/lean")})
    def lake(*args):
        return [str(LAKE), "--keep-toolchain", "--no-cache", "--no-ansi", "-v", *args]
    try:
        old_olean = producer / ".lake/build/lib/lean/Dep.olean"
        if phase == "prepare":
            old = invoke("old-build", lake("build", "Dep"), producer, env, result, track=producer)
            if old["exit"] != 0: raise RuntimeError("old baseline build failed")
            assert old_olean.is_file()
            result["old_olean_bytes"] = old_olean.stat().st_size
            result["old_olean_sha256"] = sha(old_olean.read_bytes())
            limit = old_olean.stat().st_size // 2
            assert 512 < limit < old_olean.stat().st_size
            result["chosen_limit_bytes"] = limit
            snapshot("old-valid", producer, result)
            result["status"] = "baseline_ready"
            save(result)
            return
        limit = result["chosen_limit_bytes"]
        assert old_olean.is_file() and sha(old_olean.read_bytes()) == result["old_olean_sha256"]
        assert (producer / "Dep.lean").read_bytes() == OLD
        control = WORK / "fsize-control.bin"
        code = 'import pathlib; pathlib.Path("fsize-control.bin").write_bytes(b"x" * '+str(limit+1024)+')'
        invoke("rlimit-control", ["/usr/bin/python3", "-B", "-c", code], WORK, env, result, limit=limit, track=WORK)
        result["rlimit_control_size"] = control.stat().st_size if control.exists() else None
        if result["rlimit_control_size"] != limit:
            raise RuntimeError("RLIMIT_FSIZE child control did not cap exact bytes")
        (producer / "Dep.lean").write_bytes(NEW)
        result["source_after_edit_sha256"] = sha((producer / "Dep.lean").read_bytes())
        save(result)
        limited = invoke("limited-update", lake("build", "Dep"), producer, env, result, limit=limit, track=producer)
        snapshot("after-limited", producer, result)
        invoke("post-limit-no-build", lake("--no-build", "build", "Dep"), producer, env, result, track=producer)
        invoke("post-limit-direct", [str(LEAN), "--json", "Check.lean"], producer, env, result, track=producer)
        invoke("uncapped-repair", lake("build", "Dep"), producer, env, result, track=producer)
        snapshot("after-repair", producer, result)
        invoke("post-repair-no-build", lake("--no-build", "build", "Dep"), producer, env, result, track=producer)
        invoke("post-repair-direct", [str(LEAN), "--json", "Check.lean"], producer, env, result, track=producer)
        result["status"] = "completed"
    except Exception as exc:
        result["status"] = "stopped"
        result["error"] = str(exc)
    finally:
        result["final_memory"] = mem()
        result["final_disk_free"] = shutil.disk_usage(ROOT).free
        result["final_scratch_bytes"] = scratch()
        save(result)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("phase", choices=("prepare", "continue"))
    main(parser.parse_args().phase)
