#!/usr/bin/env python3
"""Two guarded concurrent Charon pairs with a read-only shared-destination poller."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import threading
import time
from datetime import datetime, timezone

HERE = Path(__file__).resolve().parent
WORK = HERE / "work"
FIXTURE = HERE / "fixture"
ARTIFACTS = HERE / "artifacts"
RAW = HERE / "raw"
RESULT = HERE / "results.json"
CONTROLS = HERE / "controls"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CHARON = TOOLS / "bin/charon"
CARGO = RUST / "cargo"
RUSTC = RUST / "rustc"
PINS = {
    "charon": "51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b",
    "cargo": "71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1",
    "rustc": "2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc",
    "fixture_source": "990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d",
    "control_release": "89a6ce7259eaf018a97e63c0e4833ac2cf521f50b9cd048e8728d065e53cb42d",
    "control_cfg_alt": "3460774c7dba8a7ff1760f4e6285067e8c5d71a8a63522865aef3765675fd06c",
}
MIN_ADMIT_MEMORY_PERCENT = 25.0
MIN_LIVE_MEMORY_PERCENT = 20.0
MIN_DISK_BYTES = 10 * 1024**3
MAX_COMBINED_RSS_KIB = 256 * 1024
MAX_SCRATCH_KIB = 100 * 1024
CONTROL_TIMEOUT = 15.0


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def host_headroom():
    out = subprocess.check_output(["/usr/bin/vm_stat"], text=True, timeout=5)
    page_size = int(re.search(r"page size of (\d+) bytes", out).group(1))
    names = ("free", "inactive", "speculative")
    pages = {name: int(re.search(rf"Pages {name}:\s+(\d+)\.", out).group(1))
             for name in names}
    physical = int(subprocess.check_output(
        ["/usr/sbin/sysctl", "-n", "hw.memsize"], text=True, timeout=5))
    return {
        "page_size": page_size,
        "pages": pages,
        "physical_memory_bytes": physical,
        "estimated_reclaimable_percent": round(
            100 * page_size * sum(pages.values()) / physical, 4),
        "free_disk_bytes": shutil.disk_usage(HERE).free,
    }


def rss_kib(pgids):
    out = subprocess.check_output(
        ["/bin/ps", "-axo", "pgid=,rss=,state="], text=True, timeout=5)
    totals = {str(pid): 0 for pid in pgids}
    for line in out.splitlines():
        cols = line.split()
        if len(cols) == 3 and cols[0] in totals and not cols[2].startswith("Z"):
            totals[cols[0]] += int(cols[1])
    return totals


def scratch_kib():
    if not WORK.exists():
        return 0
    return int(subprocess.check_output(
        ["/usr/bin/du", "-sk", WORK], text=True, timeout=5).split()[0])


def guard_sample(pgids, start):
    host = host_headroom()
    groups = rss_kib(pgids)
    sample = {
        "elapsed_seconds": round(time.monotonic() - start, 4),
        "host": host,
        "process_group_rss_kib": groups,
        "combined_rss_kib": sum(groups.values()),
        "scratch_kib": scratch_kib(),
    }
    if host["estimated_reclaimable_percent"] < MIN_LIVE_MEMORY_PERCENT:
        return sample, "memory_guard"
    if host["free_disk_bytes"] < MIN_DISK_BYTES:
        return sample, "disk_guard"
    if sample["combined_rss_kib"] > MAX_COMBINED_RSS_KIB:
        return sample, "rss_guard"
    if sample["scratch_kib"] > MAX_SCRATCH_KIB:
        return sample, "scratch_guard"
    return sample, None


def require_preflight():
    sample, reason = guard_sample([], time.monotonic())
    if reason:
        raise RuntimeError(f"preflight {reason}: {sample}")
    if sample["host"]["estimated_reclaimable_percent"] <= MIN_ADMIT_MEMORY_PERCENT:
        raise RuntimeError(f"preflight admission margin below {MIN_ADMIT_MEMORY_PERCENT}%: {sample}")
    return sample


def stop_group(proc):
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.wait(timeout=2)


def environment(target, rustflags=None):
    env = dict(os.environ)
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER",
                "RUSTC_WORKSPACE_WRAPPER"):
        env.pop(key, None)
    env.update({
        "RUSTUP_HOME": str(TOOLS / "rustup"),
        "CARGO_HOME": str(TOOLS / "cargo"),
        "CHARON_TOOLCHAIN_IS_IN_PATH": "1",
        "CARGO_NET_OFFLINE": "true",
        "CARGO_BUILD_JOBS": "1",
        "CARGO_INCREMENTAL": "0",
        "RAYON_NUM_THREADS": "1",
        "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS": "true",
        "CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS": "false",
        "CARGO_TARGET_DIR": str(target),
        "PATH": os.pathsep.join((str(RUST), str(TOOLS / "bin"), env.get("PATH", ""))),
        "DYLD_LIBRARY_PATH": os.pathsep.join((str(RUST.parent / "lib"),
            str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
            env.get("DYLD_LIBRARY_PATH", ""))),
    })
    if rustflags:
        env["RUSTFLAGS"] = rustflags
    return env


def selected_env(env):
    return {key: env.get(key) for key in (
        "RUSTUP_HOME", "CARGO_HOME", "CHARON_TOOLCHAIN_IS_IN_PATH",
        "CARGO_NET_OFFLINE", "CARGO_BUILD_JOBS", "CARGO_INCREMENTAL",
        "RAYON_NUM_THREADS", "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS",
        "CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS", "CARGO_TARGET_DIR", "RUSTFLAGS",
        "PATH", "DYLD_LIBRARY_PATH")}


def command(label, argv, cwd, env):
    return {"label": label, "argv": [str(x) for x in argv],
            "cwd": str(cwd), "environment": selected_env(env)}


def finish(proc, row):
    stdout, stderr = proc.communicate(timeout=3)
    out = RAW / f"{row['label']}.stdout"
    err = RAW / f"{row['label']}.stderr"
    out.write_text(stdout)
    err.write_text(stderr)
    row.update({"exit": proc.returncode, "stdout_sha256": sha(out),
                "stderr_sha256": sha(err), "stdout_bytes": out.stat().st_size,
                "stderr_bytes": err.stat().st_size,
                "driver_lines": [line for line in stderr.splitlines()
                                 if "charon-driver rustc" in line]})


def run_group(pair_name, specs, dest, delay_seconds, timeout):
    before = require_preflight()
    procs = []; rows = []; samples = []; observed = []; snapshots = {}
    start = time.monotonic()
    reason = None; poller_error = []; truncation = False
    stop_reader = threading.Event()
    def read_state():
        tick = time.monotonic_ns()
        try:
            with dest.open("rb") as stream:
                a = stream.read()
                first_inode = os.fstat(stream.fileno()).st_ino
            b = dest.read_bytes()
            second_inode = dest.stat().st_ino
            snapshots.setdefault(hashlib.sha256(a).hexdigest(), a)
            snapshots.setdefault(hashlib.sha256(b).hexdigest(), b)
            return {"monotonic_ns":tick,"elapsed_seconds":round(time.monotonic()-start,6),
                    "state":"read","first_size":len(a),"second_size":len(b),
                    "first_sha256":hashlib.sha256(a).hexdigest(),
                    "second_sha256":hashlib.sha256(b).hexdigest(),
                    "first_inode":first_inode,"second_inode":second_inode,
                    "double_read_equal":a==b}
        except FileNotFoundError:
            return {"monotonic_ns":tick,"elapsed_seconds":round(time.monotonic()-start,6),
                    "state":"absent_or_disappeared"}
        except OSError as exc:
            return {"monotonic_ns":tick,"elapsed_seconds":round(time.monotonic()-start,6),
                    "state":"read_error","errno":exc.errno,"error_type":type(exc).__name__}
    def reader():
        nonlocal truncation
        try:
            while not stop_reader.is_set():
                if len(observed) < 5000:
                    observed.append(read_state())
                else:
                    truncation = True
                stop_reader.wait(.001)
        except Exception as exc:
            poller_error.append(repr(exc))
    thread = threading.Thread(target=reader,daemon=True)
    thread.start()
    try:
        for i,(label, argv, cwd, env) in enumerate(specs):
            if i == 1 and delay_seconds:
                time.sleep(delay_seconds)
            row = command(f"{pair_name}-{label}", argv, cwd, env)
            row["preflight"] = before
            row["started_utc"] = datetime.now(timezone.utc).isoformat()
            row["start_monotonic_ns"] = time.monotonic_ns()
            proc = subprocess.Popen(row["argv"], cwd=cwd, env=env,
                                    stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                                    text=True,start_new_session=True)
            row["pid"] = proc.pid
            procs.append(proc); rows.append(row)
        while True:
            sample,reason = guard_sample([p.pid for p in procs],start)
            samples.append(sample)
            if not reason and sample["elapsed_seconds"] > timeout:
                reason = "timeout"
            if reason or all(p.poll() is not None for p in procs): break
            time.sleep(.01)
    finally:
        if reason:
            for proc in procs: stop_group(proc)
        for proc,row in zip(procs,rows):
            if proc.poll() is None: stop_group(proc)
            row["ended_utc"] = datetime.now(timezone.utc).isoformat()
            row["end_monotonic_ns"] = time.monotonic_ns()
            finish(proc,row)
        stop_reader.set();thread.join(timeout=2)
    snapshot_files = []
    for digest, data in sorted(snapshots.items()):
        out = ARTIFACTS / f"{pair_name}-observed-{digest}.llbc"
        out.write_bytes(data)
        snapshot_files.append({"path":str(out),"sha256":digest,"bytes":len(data)})
    result = {"preflight":before,"samples":samples,"guard_reason":reason,
              "elapsed_seconds":round(time.monotonic()-start,4),"commands":rows,
              "reader_observations":observed,"reader_truncated":truncation,
              "reader_errors":poller_error,"snapshot_files":snapshot_files,
              "reader_interval_first_ns":
                  observed[0]["monotonic_ns"] if observed else None,
              "reader_interval_last_ns":observed[-1]["monotonic_ns"] if observed else None}
    if reason or poller_error or any(row["exit"] != 0 for row in rows):
        raise RunFailure(result)
    return result


class RunFailure(Exception):
    def __init__(self, result):
        super().__init__(f"run failed: guard={result['guard_reason']}; "
                         f"exits={[r['exit'] for r in result['commands']]}")
        self.result = result


def charon_cmd(dest, flags):
    return [CHARON, "cargo", "--preset", "aeneas", "--dest-file", dest, "--",
            "--manifest-path", FIXTURE / "Cargo.toml", "--lib", *flags,
            "--offline", "--locked", "-v", "-j", "1"]


def scalar_literals(node):
    if isinstance(node, dict):
        if "Unsigned" in node and node["Unsigned"][0] == "U32":
            yield node["Unsigned"][1]
        for value in node.values():
            yield from scalar_literals(value)
    elif isinstance(node, list):
        for value in node:
            yield from scalar_literals(value)


def decode(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    translated = data["translated"]
    bodies = {}
    for decl in translated["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name = "::".join(part["Ident"][0] for part in
                             decl["item_meta"]["name"] if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True,
                              separators=(",", ":")).encode()
            bodies[name] = {"sha256": hashlib.sha256(body).hexdigest(),
                            "u32_literals": list(scalar_literals(decl["body"]))}
    return {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
            "crate_name": translated["crate_name"], "has_errors": data["has_errors"],
            "dest_file": translated["options"]["dest_file"],
            "local_bodies": bodies,
            "files": [{"name": f["name"], "contents_sha256":
                       hashlib.sha256(f["contents"].encode()).hexdigest()}
                      for f in translated["files"]]}


def main():
    if WORK.exists() or RESULT.exists() or ARTIFACTS.exists() or RAW.exists():
        raise RuntimeError("work/results/artifacts/raw already exist; use a fresh package")
    if not FIXTURE.is_dir() or not CONTROLS.is_dir():
        raise RuntimeError("retained fixture or controls missing")
    paths={"charon":CHARON,"cargo":CARGO,"rustc":RUSTC,
           "fixture_source":FIXTURE/"src/lib.rs",
           "control_release":CONTROLS/"release.llbc",
           "control_cfg_alt":CONTROLS/"cfg_alt.llbc"}
    actual={name:sha(path) for name,path in paths.items()}
    if actual != PINS: raise RuntimeError(f"pinned input mismatch: {actual}")
    expected={
       "release":{"unit_key_probe::profile_value":["11"],
                  "unit_key_probe::config_value":["23"]},
       "cfg_alt":{"unit_key_probe::profile_value":["7"],
                  "unit_key_probe::config_value":["29"]}}
    control_models={}
    for label in expected:
        decoded=decode(CONTROLS/f"{label}.llbc")
        literals={k:v["u32_literals"] for k,v in decoded["local_bodies"].items()}
        if decoded["has_errors"] or literals != expected[label] or len(decoded["files"])!=1 or \
           decoded["files"][0]["contents_sha256"]!=PINS["fixture_source"]:
            raise RuntimeError(f"published {label} control mismatch")
        control_models[label]={"sha256":decoded["sha256"],"selected_literals":literals}
    sample,reason=guard_sample([],time.monotonic())
    if not reason and sample["host"]["estimated_reclaimable_percent"]<=MIN_ADMIT_MEMORY_PERCENT:
        reason="admission_margin"
    if reason:
        RESULT.write_text(json.dumps({"schema":1,"status":"admission_denied",
             "reason":reason,"preflight":sample,"input_sha256":actual,
             "control_models":control_models,"pairs_launched":0},indent=2,sort_keys=True)+"\n")
        print(json.dumps({"status":"admission_denied","reason":reason}))
        return
    ARTIFACTS.mkdir();RAW.mkdir();WORK.mkdir()
    result={"schema":1,"status":"running","observed_utc":datetime.now(timezone.utc).isoformat(),
            "initial_preflight":sample,"input_sha256":actual,"control_models":control_models,
            "limits":{"minimum_admission_reclaimable_percent":MIN_ADMIT_MEMORY_PERCENT,
                      "minimum_live_reclaimable_percent":MIN_LIVE_MEMORY_PERCENT,
                      "minimum_free_disk_bytes":MIN_DISK_BYTES,
                      "maximum_combined_process_group_rss_kib":MAX_COMBINED_RSS_KIB,
                      "maximum_scratch_kib":MAX_SCRATCH_KIB,
                      "pair_timeout_seconds":CONTROL_TIMEOUT},
            "source_reports":["anneal-3731-i076-sequential-shared-destination-2026-09-30",
                              "anneal-3731-i076-concurrent-shared-destination-2026-09-30"],
            "pairs":[]}
    RESULT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    schedules=(("release-first",("release","cfg_alt")),
               ("cfg-first",("cfg_alt","release")))
    try:
        for pair_name,order in schedules:
            private=WORK/pair_name;private.mkdir()
            dest=private/"shared.llbc"
            pair={"name":pair_name,"launch_order":list(order),"stagger_seconds":.03,
                  "initial_destination_absent":not dest.exists()}
            if not pair["initial_destination_absent"]: raise RuntimeError("destination existed")
            specs=[]
            for label in order:
                target=private/f"{label}-target"
                flags=["--release"] if label=="release" else []
                env=environment(target,None if label=="release" else "--cfg probe_alt")
                specs.append((label,charon_cmd(dest,flags),FIXTURE,env))
            try:
                pair["run"]=run_group(pair_name,specs,dest,.03,CONTROL_TIMEOUT)
            except RunFailure as exc:
                pair["run"]=exc.result
                pair["failed"]=True
            if dest.exists():
                final=ARTIFACTS/f"{pair_name}-final.llbc"
                shutil.copy2(dest,final)
                pair["final_destination"]={"path":str(final),"sha256":sha(final),
                                           "bytes":final.stat().st_size}
                try:
                    pair["final_destination"]["decoded"]=decode(final)
                    pair["final_destination"]["parseable"]=True
                except Exception as exc:
                    pair["final_destination"]["parseable"]=False
                    pair["final_destination"]["parse_error"]=repr(exc)
            else: pair["final_destination"]=None
            run=pair["run"]
            if len(run["commands"])==2:
                commands=run["commands"]
                pair["collection_intervals_overlap"]=(max(x["start_monotonic_ns"] for x in commands) <
                    min(x["end_monotonic_ns"] for x in commands))
                pair["postrun_process_group_rss_kib"]=rss_kib([x["pid"] for x in commands])
            result["pairs"].append(pair)
            RESULT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
            if pair.get("failed"): raise RuntimeError(f"{pair_name} guard/command/poller failure")
        result["status"]="completed"
    except Exception as exc:
        result["status"]="stopped";result["error"]=str(exc)
    finally:
        result["postrun_host"]=host_headroom()
        result["scratch_kib"]=scratch_kib()
        RESULT.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":result["status"],"pairs":len(result["pairs"]),
                      "error":result.get("error")},sort_keys=True))


if __name__=="__main__": main()
