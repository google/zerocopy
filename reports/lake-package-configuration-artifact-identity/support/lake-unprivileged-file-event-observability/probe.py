#!/usr/bin/env python3
"""Tiny offline Lake build with unprivileged, selected libc-call observations."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
LOGS = HERE / "logs"
LIB = HERE / "observe.dylib"
LAKE = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lake")
LEAN = LAKE.with_name("lean")


def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def snapshot():
    out = {}
    for p in sorted(WORK.rglob("*")):
        if p.is_file() and "logs" not in p.parts:
            st = p.stat()
            out[str(p.relative_to(WORK))] = {"sha256": digest(p), "size": st.st_size,
                                               "mtime_ns": st.st_mtime_ns}
    return out


def events(path):
    parsed = []
    for line in path.read_text().splitlines():
        pid, op, rc, arg, file = line.split("\t", 4)
        assert file.startswith(str(WORK)), file
        parsed.append({"pid": int(pid), "op": op, "result": int(rc),
                       "arg": int(arg), "path": "$WORK" + file[len(str(WORK)): ]})
    return parsed


def run(name, args, interpose=True):
    logfile = LOGS / (name + ".tsv")
    logfile.write_text("")
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "LAKE_ARTIFACT_CACHE": "false",
           "LAKE_NO_CACHE": "1", "ELAN_TOOLCHAIN": "leanprover/lean4:v4.30.0-rc2"}
    if interpose:
        env.update(DYLD_INSERT_LIBRARIES=str(LIB), OBSERVE_ROOT=str(WORK),
                   OBSERVE_LOG=str(logfile))
    else:
        for key in ("DYLD_INSERT_LIBRARIES", "OBSERVE_ROOT", "OBSERVE_LOG"):
            env.pop(key, None)
    before = snapshot()
    t0 = time.monotonic()
    p = subprocess.run([str(x) for x in args], cwd=WORK, env=env,
                       capture_output=True, text=True, timeout=35)
    after = snapshot()
    ev = events(logfile) if interpose else []
    change = {key: {"before": before.get(key), "after": after.get(key)}
              for key in sorted(before.keys() | after.keys()) if before.get(key) != after.get(key)}
    return {"name": name, "cmd": [str(x).replace(str(LAKE.parent), "$BIN") for x in args],
            "interposed": interpose, "exit": p.returncode,
            "stdout": p.stdout.replace(str(WORK), "$WORK").replace(str(LAKE.parent), "$BIN"),
            "stderr": p.stderr.replace(str(WORK), "$WORK").replace(str(LAKE.parent), "$BIN"),
            "elapsed_ms": round((time.monotonic()-t0)*1000), "events": ev,
            "event_count": len(ev), "pids": sorted({e["pid"] for e in ev}),
            "net_changes": change}


def main():
    free = shutil.disk_usage(HERE).free
    assert free >= 2_000_000_000, f"disk admission failed: {free}"
    if WORK.exists():
        shutil.rmtree(WORK)
    if LOGS.exists():
        shutil.rmtree(LOGS)
    WORK.mkdir()
    LOGS.mkdir()
    (WORK / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n")
    (WORK / "lakefile.lean").write_text("import Lake\nopen Lake DSL\npackage Probe where\nlean_lib Dep\n")
    dep = WORK / "Dep.lean"
    dep.write_text("def value : Nat := 7\n")
    (WORK / "Check.lean").write_text("import Dep\n#eval value\n")
    compile_cmd = ["/usr/bin/clang", "-dynamiclib", "-fPIC", "-O1",
                   "-Wno-deprecated-declarations", "-o", str(LIB), str(HERE / "observe.c")]
    compile_result = subprocess.run(compile_cmd, capture_output=True, text=True, timeout=20)
    assert compile_result.returncode == 0, compile_result.stderr
    clang_version = subprocess.run(["/usr/bin/clang", "--version"], capture_output=True,
                                   text=True, timeout=5).stdout.splitlines()[0]
    out = {"subject": {"lake_sha256": digest(LAKE), "lean_sha256": digest(LEAN),
                       "interposer_sha256": digest(LIB), "source_sha256": digest(HERE / "observe.c"),
                       "disk_free_before": free, "clang_version": clang_version,
                       "compile_cmd": [s.replace(str(HERE), "$SUPPORT") for s in compile_cmd],
                       "compile_stderr": compile_result.stderr}, "runs": []}
    base = [LAKE, "--keep-toolchain", "--no-cache", "--no-ansi", "-v"]
    out["runs"].append(run("cold", base + ["build", "Dep"]))
    out["runs"].append(run("warm", base + ["build", "Dep"]))
    before_mtime = dep.stat().st_mtime_ns
    dep.write_text("def value : Nat := 9\n")
    os.utime(dep, ns=(before_mtime, before_mtime))
    out["mutation"] = {"source_sha256": digest(dep), "mtime_restored_ns": before_mtime}
    out["runs"].append(run("changed_nobuild", base + ["--rehash", "--no-build", "build", "Dep"]))
    out["runs"].append(run("changed_build", base + ["--rehash", "build", "Dep"]))
    out["runs"].append(run("post_warm", base + ["build", "Dep"]))
    out["runs"].append(run("unhooked_postwarm", base + ["build", "Dep"], False))
    out["runs"].append(run("fresh_batch", [LAKE, "env", LEAN, "--json", "Check.lean"], False))
    (HERE / "results.json").write_text(json.dumps(out, indent=2) + "\n")
    for p in LOGS.iterdir():
        p.unlink()
    LOGS.rmdir()
    shutil.rmtree(WORK)
    LIB.unlink()
    for x in out["runs"]:
        print(x["name"], x["exit"], x["event_count"], len(x["pids"]), len(x["net_changes"]))


if __name__ == "__main__":
    main()
