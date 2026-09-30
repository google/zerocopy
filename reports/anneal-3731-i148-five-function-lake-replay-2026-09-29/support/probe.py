#!/usr/bin/env python3
"""Bounded, sequential Lake replay of the retained I148 five-function corpus."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPORT = HERE.parent
REPO = REPORT.parents[1]
PRIOR = REPO / "reports/anneal-3731-i148-multifunction-translation-repeat-2026-09-29"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
BACKEND = TOOLS / "aeneas-release/backends/lean"
LEANDIR = TOOLS / "elan/toolchains/leanprover--lean4---v4.30.0-rc2"
LAKE = LEANDIR / "bin/lake"
CHARON = TOOLS / "bin/charon"
AENEAS = TOOLS / "bin/aeneas"
RUSTBIN = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
WORK = HERE / "work"
LOGS = HERE / "logs"
RESULT = HERE / "results.json"
MODULES = ("Probe/Types", "Probe/Funs", "Probe", "Consumer")
GENERATED = {"Types.lean": "Probe/Types.lean", "Funs.lean": "Probe/Funs.lean", "Probe.lean": "Probe.lean"}
data = {"schema": 1, "status": "running", "identity": {}, "preflights": [], "commands": [], "builds": [], "generated": {}, "limits": {"free_memory_percent_min": 30, "disk_bytes_min": 10 * 1024**3, "process_tree_rss_bytes_max": int(2.5 * 1024**3), "build_seconds_max": 60}}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save():
    RESULT.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")

def measure(label):
    p = subprocess.run(["memory_pressure", "-Q"], capture_output=True, text=True, timeout=5)
    m = re.search(r"System-wide memory free percentage: (\d+)%", p.stdout)
    free_mem = int(m.group(1)) if p.returncode == 0 and m else -1
    disk = shutil.disk_usage(REPORT).free
    row = {"label": label, "memory_pressure_stdout": p.stdout, "memory_pressure_stderr": p.stderr,
           "free_memory_percent": free_mem, "free_disk_bytes": disk, "time_ns": time.time_ns()}
    data["preflights"].append(row)
    save()
    if free_mem < 30 or disk < 10 * 1024**3:
        raise RuntimeError(f"preflight guard failed at {label}: memory {free_mem}%, disk {disk} bytes")

def tree_rss(root):
    p = subprocess.run(["ps", "-axo", "pid=,ppid=,rss="], capture_output=True, text=True, timeout=5)
    table = {}
    for line in p.stdout.splitlines():
        try:
            pid, ppid, kb = map(int, line.split())
            table[pid] = (ppid, kb)
        except ValueError:
            pass
    children = {root}
    for _ in range(10):
        more = {pid for pid, (ppid, _) in table.items() if ppid in children}
        if more <= children:
            break
        children |= more
    return 1024 * sum(table.get(pid, (0, 0))[1] for pid in children)

def run(label, argv, cwd, env, timeout=60, is_build=False):
    measure(label)
    started = time.monotonic()
    LOGS.mkdir(exist_ok=True)
    out_path, err_path = LOGS / f"{label}.stdout", LOGS / f"{label}.stderr"
    out_file, err_file = out_path.open("wb"), err_path.open("wb")
    try:
        proc = subprocess.Popen([str(x) for x in argv], cwd=cwd, env=env, stdout=out_file,
                                stderr=err_file, start_new_session=True)
    except Exception:
        out_file.close()
        err_file.close()
        raise
    peak = 0
    guard = None
    while proc.poll() is None:
        elapsed = time.monotonic() - started
        try:
            rss = tree_rss(proc.pid)
            peak = max(peak, rss)
        except subprocess.SubprocessError:
            rss = 0
        if rss > int(2.5 * 1024**3):
            guard = f"RSS {rss} bytes exceeded 2.5 GiB"
        elif elapsed > timeout:
            guard = f"elapsed {elapsed:.2f}s exceeded {timeout}s"
        if guard:
            os.killpg(proc.pid, signal.SIGKILL)
            break
        time.sleep(0.2)
    proc.wait()
    out_file.close()
    err_file.close()
    elapsed = time.monotonic() - started
    stdout, stderr = out_path.read_bytes(), err_path.read_bytes()
    row = {"label": label, "argv": [str(x) for x in argv], "cwd": str(cwd),
           "env_overrides": {k: env[k] for k in ("LAKE_NO_NET", "LEAN_NUM_THREADS", "LAKE_JOBS", "CARGO_BUILD_JOBS", "CARGO_INCREMENTAL", "CARGO_NET_OFFLINE", "RAYON_NUM_THREADS", "CARGO_TARGET_DIR") if k in env},
           "exit": proc.returncode, "elapsed_seconds": round(elapsed, 3), "peak_tree_rss_bytes": peak,
           "guard_failure": guard, "stdout_sha256": sha(out_path),
           "stderr_sha256": sha(err_path)}
    data["commands"].append(row)
    save()
    if guard or proc.returncode != 0:
        raise RuntimeError(f"{label}: {guard or 'exit ' + str(proc.returncode)}; see retained logs")
    return (stdout + stderr).decode(errors="replace")

def files_state():
    root = WORK / "consumer"
    out = {}
    for rel in list(GENERATED.values()) + ["Consumer.lean"]:
        p = root / rel
        out[rel] = {"sha256": sha(p), "size": p.stat().st_size, "mtime_ns": p.stat().st_mtime_ns}
    for mod in MODULES:
        for ext in ("olean", "trace"):
            p = root / ".lake/build/lib/lean" / f"{mod}.{ext}"
            if not p.is_file():
                raise RuntimeError(f"missing Lake artifact: {p}")
            rel = str(p.relative_to(root))
            out[rel] = {"sha256": sha(p), "size": p.stat().st_size, "mtime_ns": p.stat().st_mtime_ns}
    return out

def lake_build(label):
    env = dict(os.environ, LAKE_NO_NET="1", LEAN_NUM_THREADS="1", LAKE_JOBS="1")
    output = run(label, [LAKE, "build", "-v"], WORK / "consumer", env, 60, True)
    jobs = [line for line in output.splitlines() if re.search(r"\b(?:Built|Replayed) (?:Probe(?:\.|\s|$)|Consumer(?:\s|$))", line)]
    data["builds"].append({"label": label, "own_job_lines": jobs, "state": files_state()})
    save()

def copy_generated(source):
    root = WORK / "consumer"
    for src, dst in GENERATED.items():
        shutil.copyfile(source / src, root / dst)

def setup():
    if WORK.exists() or LOGS.exists() or RESULT.exists():
        raise RuntimeError("use a fresh report support directory; existing evidence is preserved")
    measure("initial")
    for p in (LAKE, CHARON, AENEAS, RUSTBIN / "cargo", RUSTBIN / "rustc", BACKEND / "lake-manifest.json", BACKEND / ".lake/build/lib/lean/Aeneas.olean"):
        if not p.is_file():
            raise RuntimeError(f"missing local pin: {p}")
    sources = [PRIOR / "support/artifacts" / f"gen-{n}" for n in range(1, 6)]
    for source in sources:
        for name in GENERATED:
            if not (source / name).is_file():
                raise RuntimeError(f"missing retained generated source: {source / name}")
    data["identity"] = {"parent_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "prior_report_sha256": sha(PRIOR / "REPORT.md"),
        "prior_results_sha256": sha(PRIOR / "support/results.json"),
        "tools": {str(p): sha(p) for p in (LAKE, CHARON, AENEAS, RUSTBIN / "cargo", RUSTBIN / "rustc", BACKEND / "lake-manifest.json", BACKEND / ".lake/build/lib/lean/Aeneas.olean")},
        "prior_generated": {f"gen-{n}": {name: sha(source / name) for name in GENERATED} for n, source in enumerate(sources, 1)},
        "prior_llbc": {f"seq-{n}": sha(PRIOR / "support/artifacts" / f"seq-{n}.llbc") for n in range(1, 4)}}
    WORK.mkdir()
    consumer = WORK / "consumer"
    (consumer / "Probe").mkdir(parents=True)
    copy_generated(sources[0])
    (consumer / "Consumer.lean").write_text("import Probe\n" + "\n".join(
        f"theorem {name}_self (x : Aeneas.Std.U32) : i148_corpus.{name} " +
        ({"choose": "true x x", "pair_sum": "{left := x, right := x}", "make_pair": "x x", "combine": "true x x"}.get(name, "x")) +
        " = i148_corpus." + name + " " +
        ({"choose": "true x x", "pair_sum": "{left := x, right := x}", "make_pair": "x x", "combine": "true x x"}.get(name, "x")) + " := by rfl"
        for name in ("add_one", "choose", "pair_sum", "make_pair", "combine")) +
        "\n#print axioms combine_self\n")
    (consumer / "lakefile.lean").write_text(f'import Lake\nopen Lake DSL\nrequire aeneas from "{BACKEND}"\npackage i148_replay\nlean_lib Probe\n@[default_target]\nlean_lib Consumer\n')
    manifest = json.loads((BACKEND / "lake-manifest.json").read_text())
    manifest["packages"].append({"type": "path", "scope": "", "name": "aeneas", "manifestFile": "lake-manifest.json", "inherited": False, "dir": str(BACKEND), "configFile": "lakefile.lean"})
    manifest["name"] = "i148_replay"
    (consumer / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    (consumer / "lean-toolchain").write_text("leanprover/lean4:v4.30.0-rc2\n")
    (consumer / ".lake").mkdir()
    (consumer / ".lake/packages").symlink_to(BACKEND / ".lake/packages", target_is_directory=True)
    save()

def changed_function():
    fixture = WORK / "mutant"
    shutil.copytree(PRIOR / "support/fixture", fixture)
    src = fixture / "src/lib.rs"
    old = src.read_text()
    if old.count("x + 1") != 1:
        raise RuntimeError("source control must contain exactly one x + 1")
    src.write_text(old.replace("x + 1", "x + 2"))
    data["mutation"] = {"description": "add_one body x + 1 to x + 2", "original_sha256": sha(PRIOR / "support/fixture/src/lib.rs"), "changed_sha256": sha(src)}
    dest = WORK / "mutant.llbc"
    env = dict(os.environ, RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
               CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_BUILD_JOBS="1", CARGO_INCREMENTAL="0",
               CARGO_NET_OFFLINE="true", RAYON_NUM_THREADS="1", CARGO_TARGET_DIR=str(WORK / "target-mutant"),
               PATH=os.pathsep.join([str(RUSTBIN), str(TOOLS / "bin"), os.environ.get("PATH", "")]))
    run("charon-mutant", [CHARON, "cargo", "--preset", "aeneas", "--dest-file", dest, "--",
         "--manifest-path", fixture / "Cargo.toml", "--lib", "--offline", "--locked", "-j", "1"], fixture, env)
    doc = json.loads(dest.read_text())
    if doc.get("has_errors") is not False:
        raise RuntimeError("changed-function LLBC has translation errors")
    generated = WORK / "mutant-generated"
    generated.mkdir()
    inputdir = WORK / "mutant-input"
    inputdir.mkdir()
    shutil.copyfile(dest, inputdir / "probe.llbc")
    run("aeneas-mutant", [AENEAS, "-backend", "lean", "-no-progress-bar", "-sequential",
        "-split-files", "-gen-lib-entry", "-dest", generated, inputdir / "probe.llbc"], WORK, dict(os.environ))
    data["mutation"].update({"llbc_sha256": sha(dest), "generated": {name: sha(generated / name) for name in GENERATED}})
    save()
    return generated

def main():
    try:
        setup()
        lake_build("fresh-baseline")
        lake_build("warm-no-write")
        for n in range(2, 6):
            source = PRIOR / "support/artifacts" / f"gen-{n}"
            copy_generated(source)
            lake_build(f"identical-replace-{n}")
        mutated = changed_function()
        copy_generated(mutated)
        lake_build("function-change")
        lake_build("changed-no-write")
        data["status"] = "complete"
    except Exception as e:
        data["status"] = "aborted"
        data["error"] = str(e)
        raise
    finally:
        if (WORK / "consumer/.lake/packages").is_symlink():
            (WORK / "consumer/.lake/packages").unlink()
        save()

if __name__ == "__main__":
    main()
