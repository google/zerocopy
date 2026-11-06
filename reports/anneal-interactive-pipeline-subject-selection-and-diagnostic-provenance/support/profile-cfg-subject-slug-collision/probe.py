#!/usr/bin/env python3
"""Offline, guarded profile/cfg Charon contrast against the V2 slug helper."""
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
WORK = Path(os.environ.get("I076_PROFILE_WORK_ROOT", HERE / "work")).resolve()
FIXTURE = HERE / "fixture"
HARNESS = HERE / "harness"
ARTIFACTS = HERE / "artifacts"
RAW = HERE / "raw"
TOOLS = Path("/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools")
RUST = TOOLS / "rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin"
CARGO = RUST / "cargo"
RUSTC = RUST / "rustc"
CHARON = TOOLS / "bin/charon"
MIN_RECLAIMABLE_PERCENT = 20.0
MIN_DISK_BYTES = 10 * 1024**3
MAX_GROUP_RSS_KIB = 1024 * 1024
TIMEOUT_SECONDS = 60

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def vm_estimate():
    out = subprocess.check_output(["/usr/bin/vm_stat"], text=True)
    page_size = int(re.search(r"page size of (\d+) bytes", out).group(1))
    counts = {name: int(re.search(rf"Pages {name}:\s+(\d+)\.", out).group(1))
              for name in ("free", "inactive", "speculative")}
    physical_bytes = int(subprocess.check_output(["/usr/sbin/sysctl", "-n", "hw.memsize"], text=True))
    reclaimable_bytes = page_size * sum(counts.values())
    return {"vm_page_size": page_size, "vm_pages": counts,
            "physical_memory_bytes": physical_bytes,
            "estimated_reclaimable_percent": round(100 * reclaimable_bytes / physical_bytes, 3)}

def headroom():
    return {**vm_estimate(), "free_disk_bytes": shutil.disk_usage(WORK.parent).free}

def require_headroom():
    h = headroom()
    if h["estimated_reclaimable_percent"] < MIN_RECLAIMABLE_PERCENT or h["free_disk_bytes"] < MIN_DISK_BYTES:
        raise RuntimeError("preflight headroom guard: " + repr(h))
    return h

def group_rss_kib(pid):
    out = subprocess.check_output(["/bin/ps", "-axo", "pgid=,rss=,state="], text=True)
    total = 0
    for line in out.splitlines():
        f = line.split()
        if len(f) == 3 and int(f[0]) == pid and not f[2].startswith("Z"):
            total += int(f[1])
    return total

def terminate(p):
    if p.poll() is None:
        os.killpg(p.pid, signal.SIGTERM)
        try:
            p.wait(timeout=2)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait(timeout=2)

def environment(target, rustflags=None):
    e = dict(os.environ)
    for key in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER"):
        e.pop(key, None)
    e.update(RUSTUP_HOME=str(TOOLS / "rustup"), CARGO_HOME=str(TOOLS / "cargo"),
             CHARON_TOOLCHAIN_IS_IN_PATH="1", CARGO_NET_OFFLINE="true",
             CARGO_BUILD_JOBS="1", CARGO_INCREMENTAL="0", RAYON_NUM_THREADS="1",
             CARGO_PROFILE_DEV_DEBUG_ASSERTIONS="true",
             CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS="false",
             CARGO_TARGET_DIR=str(target),
             PATH=os.pathsep.join((str(RUST), str(TOOLS / "bin"), e.get("PATH", ""))),
             DYLD_LIBRARY_PATH=os.pathsep.join((str(RUST.parent / "lib"),
                 str(RUST.parent / "lib/rustlib/aarch64-apple-darwin/lib"),
                 e.get("DYLD_LIBRARY_PATH", ""))))
    if rustflags:
        e["RUSTFLAGS"] = rustflags
    return e

def run(label, cmd, cwd, env):
    before = require_headroom()
    started = time.monotonic()
    p = subprocess.Popen([str(x) for x in cmd], cwd=cwd, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    samples = []
    reason = None
    try:
        while True:
            s = {"elapsed_seconds": round(time.monotonic() - started, 4),
                 **headroom(), "group_rss_kib": group_rss_kib(p.pid)}
            samples.append(s)
            if s["estimated_reclaimable_percent"] < MIN_RECLAIMABLE_PERCENT:
                reason = "memory_guard"
            elif s["free_disk_bytes"] < MIN_DISK_BYTES:
                reason = "disk_guard"
            elif s["group_rss_kib"] > MAX_GROUP_RSS_KIB:
                reason = "rss_guard"
            elif s["elapsed_seconds"] > TIMEOUT_SECONDS:
                reason = "timeout"
            if reason or p.poll() is not None:
                break
            time.sleep(0.1)
    finally:
        if reason or p.poll() is None:
            terminate(p)
    stdout, stderr = p.communicate(timeout=3)
    (RAW / f"{label}.stdout").write_text(stdout)
    (RAW / f"{label}.stderr").write_text(stderr)
    result = {"label": label, "argv": [str(x) for x in cmd], "cwd": str(cwd),
              "environment": {k: env.get(k) for k in
                              ("CARGO_TARGET_DIR", "CARGO_INCREMENTAL", "CARGO_BUILD_JOBS",
                               "CARGO_NET_OFFLINE", "RAYON_NUM_THREADS", "RUSTFLAGS",
                               "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS",
                               "CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS")},
              "preflight": before, "samples": samples, "guard_reason": reason,
              "exit": p.returncode, "elapsed_seconds": round(time.monotonic() - started, 4),
              "stdout_sha256": sha(RAW / f"{label}.stdout"),
              "stderr_sha256": sha(RAW / f"{label}.stderr"),
              "target_allocated_kib": int(subprocess.check_output(
                  ["/usr/bin/du", "-sk", env["CARGO_TARGET_DIR"]], text=True).split()[0])}
    if reason or p.returncode != 0:
        raise RuntimeError(f"{label}: guard={reason}, exit={p.returncode}; see raw stderr")
    return result

def scalar_literals(node):
    if isinstance(node, dict):
        if "Unsigned" in node and node["Unsigned"][0] == "U32":
            yield node["Unsigned"][1]
        for value in node.values():
            yield from scalar_literals(value)
    elif isinstance(node, list):
        for value in node:
            yield from scalar_literals(value)

def project(path):
    d = json.loads(path.read_text())
    t = d["translated"]
    bodies = {}
    for decl in t["fun_decls"]:
        if decl["item_meta"]["is_local"]:
            name = "::".join(part["Ident"][0] for part in decl["item_meta"]["name"]
                             if "Ident" in part)
            body = json.dumps(decl["body"], sort_keys=True, separators=(",", ":")).encode()
            bodies[name] = {"sha256": hashlib.sha256(body).hexdigest(),
                            "u32_literals": list(scalar_literals(decl["body"]))}
    files = [{"name": row["name"], "contents_sha256": hashlib.sha256(
        row["contents"].encode()).hexdigest()} for row in t["files"]]
    return {"sha256": sha(path), "bytes": path.stat().st_size,
            "crate_name": t["crate_name"], "has_errors": d["has_errors"],
            "local_bodies": bodies, "files": files}

def main():
    assert not WORK.exists(), WORK
    assert FIXTURE.is_dir() and HARNESS.is_dir() and CHARON.is_file()
    ARTIFACTS.mkdir(exist_ok=True)
    RAW.mkdir(exist_ok=True)
    preflight = require_headroom()
    WORK.mkdir(parents=True)
    results = {"preflight": preflight,
               "limits": {"minimum_estimated_reclaimable_percent": MIN_RECLAIMABLE_PERCENT,
                          "minimum_free_disk_bytes": MIN_DISK_BYTES,
                          "maximum_group_rss_kib": MAX_GROUP_RSS_KIB,
                          "per_command_timeout_seconds": TIMEOUT_SECONDS},
               "source_identity": {"reference_commit": "bd0956be95c5f798f0c0484921b9b9d1fc6e9988",
                   "scanner_sha256": sha(HARNESS / "src/scanner.rs"),
                   "harness_main_sha256": sha(HARNESS / "src/main.rs"),
                   "harness_manifest_sha256": sha(HARNESS / "Cargo.toml"),
                   "harness_lock_sha256": sha(HARNESS / "Cargo.lock"),
                   "fixture_source_sha256": sha(FIXTURE / "src/lib.rs"),
                   "fixture_manifest_sha256": sha(FIXTURE / "Cargo.toml"),
                   "fixture_lock_sha256": sha(FIXTURE / "Cargo.lock"),
                   "fixture_manifest_path": str(FIXTURE / "Cargo.toml"),
                   "tool_sha256": {"charon": sha(CHARON), "cargo": sha(CARGO), "rustc": sha(RUSTC)}},
               "commands": {}, "slug_rows": [], "artifacts": {}, "cleanup": None}
    try:
        harness_target = WORK / "harness-target"
        results["commands"]["harness_build"] = run("harness_build",
            [CARGO, "build", "--offline", "--locked", "-j", "1"], HARNESS,
            environment(harness_target))
        binary = harness_target / "debug/anneal-scanner-slug-probe"
        results["source_identity"]["harness_binary_sha256"] = sha(binary)
        results["commands"]["slug"] = run("slug", [binary, FIXTURE / "Cargo.toml"],
                                           HARNESS, environment(harness_target))
        results["slug_rows"] = [line.split("\t") for line in
                                (RAW / "slug.stdout").read_text().splitlines()]
        assert [row[0] for row in results["slug_rows"]] == ["debug", "release", "cfg_alt"]
        assert results["slug_rows"][0][1:] == results["slug_rows"][1][1:] == results["slug_rows"][2][1:]
        cases = (("debug", [], None),
                 ("release", ["--release"], None),
                 ("cfg_alt", [], "--cfg probe_alt"))
        for label, flags, rustflags in cases:
            target = WORK / f"target-{label}"
            dest = ARTIFACTS / f"{label}.llbc"
            env = environment(target, rustflags)
            cmd = [CHARON, "cargo", "--preset", "aeneas", "--dest-file", dest, "--",
                   "--manifest-path", FIXTURE / "Cargo.toml", "--lib", *flags,
                   "--offline", "--locked", "-v"]
            results["commands"][label] = run(label, cmd, FIXTURE, env)
            results["artifacts"][label] = project(dest)
        maps = {label: r["local_bodies"] for label, r in results["artifacts"].items()}
        names = {"unit_key_probe::profile_value", "unit_key_probe::config_value"}
        assert all(set(m) == names for m in maps.values())
        assert [maps[x]["unit_key_probe::profile_value"]["u32_literals"] for x in
                ("debug", "release", "cfg_alt")] == [["7"], ["11"], ["7"]]
        assert [maps[x]["unit_key_probe::config_value"]["u32_literals"] for x in
                ("debug", "release", "cfg_alt")] == [["23"], ["23"], ["29"]]
        assert all(r["crate_name"] == "unit_key_probe" and r["has_errors"] is False
                   for r in results["artifacts"].values())
        assert all(r["files"][0]["contents_sha256"] == results["source_identity"]["fixture_source_sha256"]
                   for r in results["artifacts"].values())
    finally:
        if WORK.exists():
            shutil.rmtree(WORK)
        results["cleanup"] = {"work_exists_after_removal": WORK.exists(),
                              "postrun_headroom": headroom()}
        (HERE / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps({"cases": list(results["artifacts"]),
                      "slug": results["slug_rows"][0][2],
                      "cleanup": results["cleanup"]["work_exists_after_removal"]}, indent=2))

if __name__ == "__main__":
    main()
