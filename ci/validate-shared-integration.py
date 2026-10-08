#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Temporary native recipe: execute production consumers, retain their evidence."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path.cwd()
EVIDENCE = ROOT / "validation-evidence"
EVIDENCE.mkdir(exist_ok=False)
BASE = "a19f20514751cf329455e471bcc2c7e3ae7f8b3e"
DEADLINE = time.monotonic() + 225 * 60
REPORT = {"validated": False, "prepared_from": BASE, "commands": []}
ENV = dict(os.environ, LEAN_NUM_THREADS="2", CARGO_BUILD_JOBS="2",
           PYTHONDONTWRITEBYTECODE="1", RUSTFLAGS="", RUSTDOCFLAGS="")
TOOLS = ROOT / "target/aeneas/toolchain"
ENV["AENEAS_TOOLCHAIN_DIR"] = str(TOOLS)
ENV["CARGO_HOME"] = str(ROOT / "target/aeneas/cargo-home")
ENV["CARGO_INCREMENTAL"] = "0"


def digest(path):
    value = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def save():
    (EVIDENCE / "status.json").write_text(json.dumps(REPORT, indent=2) + "\n")


def run(name, args, minutes=20):
    assert shutil.disk_usage(ROOT).free >= 3 * 1024**3, "Disk below 3 GiB"
    log = EVIDENCE / (name + ".log")
    errors = EVIDENCE / (name + ".stderr.log")
    entry = {"name": name, "argv": args, "status": None,
             "stdout": log.name, "stderr": errors.name}
    REPORT["commands"].append(entry)
    save()
    print("RUN", name, args, flush=True)
    end = min(DEADLINE, time.monotonic() + minutes * 60)
    with log.open("wb") as stream, errors.open("wb") as error_stream:
        process = subprocess.Popen(args, cwd=ROOT, env=ENV, stdout=stream,
                                   stderr=error_stream, start_new_session=True)
        while process.poll() is None:
            if time.monotonic() >= end or stream.tell() + error_stream.tell() > 64 * 1024**2:
                entry["bound_exceeded"] = True
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=20)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                break
            time.sleep(2)
    entry.update(status=process.returncode, bytes=log.stat().st_size,
                 sha256=digest(log), stderr_bytes=errors.stat().st_size,
                 stderr_sha256=digest(errors))
    save()
    assert not entry.get("bound_exceeded") and entry["status"] == 0, entry
    return log.read_text()


def shell(name, command, minutes=20):
    return run(name, ["bash", "-euo", "pipefail", "-c",
                      "source verification/aeneas/toolchain.sh\n" + command], minutes)


def source_snapshot():
    import stat
    entries = subprocess.check_output(["git", "ls-files", "--stage", "-z"], cwd=ROOT)
    snapshot = {}
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        mode, oid, stage = header.decode("ascii").split()
        assert stage == "0", "Unmerged tracked source: " + os.fsdecode(name)
        relative = os.fsdecode(name)
        path = ROOT / relative
        if mode in {"100644", "100755"}:
            actual = path.lstat().st_mode
            assert stat.S_ISREG(actual), "Expected regular tracked source: " + relative
            assert bool(actual & 0o111) == (mode == "100755"), "Executable mode mismatch: " + relative
            value = {"mode": mode, "sha256": digest(path)}
        elif mode == "120000":
            assert path.is_symlink(), "Expected tracked symlink: " + relative
            value = {"mode": mode, "target": os.fsdecode(os.readlink(os.fsencode(path)))}
        else:
            raise AssertionError("Unsupported tracked mode: " + mode)
        assert relative not in snapshot, "Duplicate tracked source: " + relative
        snapshot[relative] = value
    return snapshot


def clean_source(name):
    status = run(name, ["git", "status", "--porcelain", "--untracked-files=no"])
    assert not status.strip(), status
    assert source_snapshot() == REPORT["source_sha256"], "Tracked source changed"


def integrity(name, store):
    run(name, ["nix", "store", "verify", "--recursive", "--no-trust", store], 20)
    output = run(name + "-closure", ["nix", "path-info", "--recursive", "--json", store])
    data = json.loads(output)
    # Preserve scoped Nix identities, never a global store enumeration.
    return {item["path"]: item["narHash"] for item in data} if isinstance(data, list) else {
        path: item["narHash"] for path, item in data.items()}


backend = None
try:
    REPORT["head"] = run("head", ["git", "rev-parse", "HEAD"]).strip()
    assert REPORT["head"] == os.environ["EXPECTED_HEAD"]
    REPORT["system"] = run("native-system", ["nix", "eval", "--impure", "--raw",
                                             "--expr", "builtins.currentSystem"]).strip()
    assert REPORT["system"] == os.environ["EXPECTED_SYSTEM"]
    targets = {"aarch64-darwin": "aarch64-apple-darwin",
               "x86_64-darwin": "x86_64-apple-darwin",
               "x86_64-linux": "x86_64-unknown-linux-gnu"}
    assert REPORT["system"] in targets
    assert not (ROOT / "target/aeneas").exists(), "Cold setup requires fresh target"
    assert shutil.disk_usage(ROOT).free >= 20 * 1024**3, "Cold setup requires 20 GiB"
    REPORT["source_sha256"] = source_snapshot()
    clean_source("source-before")
    flake = "path:" + str(ROOT / "anneal")
    backend = run("backend-dependency", ["nix", "build", "--no-write-lock-file",
                  "--no-link", "--print-out-paths", "--max-jobs", "1", "--cores", "2",
                  flake + "#aeneas-compiled"], 150).strip()
    assert backend.startswith("/nix/store/") and "\n" not in backend, backend
    REPORT["dependency_closure_before"] = integrity("integrity-before", backend)
    run("cold-production-setup", ["bash", "verification/aeneas/setup.sh"], 150)
    assert integrity("integrity-after-setup", backend) == REPORT["dependency_closure_before"]
    REPORT["installation"] = json.loads((TOOLS / "aeneas-build.json").read_text())
    shutil.copyfile(TOOLS / "aeneas-build.json", EVIDENCE / "aeneas-build.json")
    archive = Path(run("archive-identity", ["nix", "eval", "--no-write-lock-file", "--raw",
                   flake + "#packages." + REPORT["system"] + ".omnibus-archive-ci.outPath"]).strip())
    assert archive.is_file() and str(archive).startswith("/nix/store/")
    REPORT["archive"] = {"store": str(archive), "bytes": archive.stat().st_size,
                         "sha256": digest(archive)}
    target = targets[REPORT["system"]]
    for manifest in ["zerocopy/Cargo.toml", "tools/Cargo.toml"]:
        shell("fetch-" + manifest.split("/")[0], "cargo fetch --locked --manifest-path "
              + manifest + " --target " + target, 10)
    # Nominal fixtures and the production proof baseline consume the installed
    # toolchain independently. Preserve a fixture failure without hiding the
    # separate production result; the final gate still requires both.
    try:
        run("nominal-tuples", ["bash", "verification/aeneas/tests/nominal-tuples.sh"], 15)
    except Exception as error:
        REPORT["nominal_error"] = str(error)
        save()
    run("production-check", ["bash", "verification/aeneas/run.sh"], 30)
    REPORT["proof_graphs"] = {}
    baselines = {}
    for name in ["golden-verification", "verification"]:
        workspace = ROOT / "target/aeneas" / name
        graph = workspace / "proof-dependencies.json"
        data = json.loads(graph.read_text())
        assert data and all(set(row) == {"theorem", "depends_on"} for row in data), graph
        destination = EVIDENCE / (name + "-proof-dependencies.json")
        shutil.copyfile(graph, destination)
        REPORT["proof_graphs"][name] = {"theorems": len(data), "sha256": digest(graph)}
        baselines[name] = {str(p.relative_to(workspace)): digest(p)
                           for p in workspace.rglob("*.lean") if ".lake" not in p.parts}
    # The production workflow also runs these independent generated projects
    # in parallel. Observe both statuses and retain each suite's raw streams.
    controls = r"""
evidence="$PWD/validation-evidence"
bash verification/aeneas/negative-controls.sh golden-verification > "$evidence/golden-verification-negative-controls.log" 2> "$evidence/golden-verification-negative-controls.stderr.log" &
golden_pid=$!
bash verification/aeneas/negative-controls.sh verification > "$evidence/verification-negative-controls.log" 2> "$evidence/verification-negative-controls.stderr.log" &
live_pid=$!
golden_status=0
wait "$golden_pid" || golden_status=$?
printf '%s\n' "$golden_status" > "$evidence/golden-verification-negative-controls.status"
live_status=0
wait "$live_pid" || live_status=$?
printf '%s\n' "$live_status" > "$evidence/verification-negative-controls.status"
cat "$evidence/golden-verification-negative-controls.log" "$evidence/verification-negative-controls.log"
cat "$evidence/golden-verification-negative-controls.stderr.log" "$evidence/verification-negative-controls.stderr.log" >&2
test "$golden_status" = 0 && test "$live_status" = 0
"""
    run("parallel-negative-controls", ["bash", "-euo", "pipefail", "-c", controls], 60)
    REPORT["negative_controls"] = {}
    for name in ["golden-verification", "verification"]:
        status = int((EVIDENCE / (name + "-negative-controls.status")).read_text())
        assert status == 0, (name, status)
        REPORT["negative_controls"][name] = {
            "status": status,
            "stdout_sha256": digest(EVIDENCE / (name + "-negative-controls.log")),
            "stderr_sha256": digest(EVIDENCE / (name + "-negative-controls.stderr.log")),
        }
        workspace = ROOT / "target/aeneas" / name
        current = {str(p.relative_to(workspace)): digest(p)
                   for p in workspace.rglob("*.lean") if ".lake" not in p.parts}
        assert current == baselines[name], "Negative control source restoration failed"
        assert digest(workspace / "proof-dependencies.json") == REPORT["proof_graphs"][name]["sha256"]
    shell("quick-unit-tests", "python3 -B -m unittest discover -s verification/aeneas/tests", 10)
    REPORT["validated"] = "nominal_error" not in REPORT
except Exception as error:
    REPORT["error"] = str(error)
finally:
    if REPORT.get("source_sha256"):
        try:
            clean_source("source-final")
        except Exception as error:
            REPORT["source_integrity_error"] = str(error)
            REPORT["validated"] = False
    if backend and REPORT.get("dependency_closure_before"):
        try:
            after = integrity("integrity-final", backend)
            assert after == REPORT["dependency_closure_before"], "Closure identity changed"
            REPORT["dependency_closure_after"] = after
        except Exception as error:
            REPORT["integrity_error"] = str(error)
            REPORT["validated"] = False
    save()
if not REPORT["validated"]:
    raise SystemExit("Integrated validation failed; see validation-evidence/status.json")
