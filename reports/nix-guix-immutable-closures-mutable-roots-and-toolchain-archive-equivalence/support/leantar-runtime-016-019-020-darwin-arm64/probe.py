#!/usr/bin/env python3
"""Tiny, bounded native leantar interoperability probe for R491."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
MIN_MEMORY = .20
MIN_DISK = 10 * 1024**3
EXPECTED = {"0.1.16": "74b681d647b5f288b7e3ba89b562808de656abcde72771e97170bc377137e20a",
            "0.1.19": "9bddd23bcddf44b27cf3a79e38dde45c53278721980695abdc76587fc3c89d41",
            "0.1.20": "97ddd119805f7d020bb823f818140b078eb37057b1b53174899c0d9aff0ea6c7"}

def sha(data): return hashlib.sha256(data).hexdigest()

def resources():
    vm = subprocess.check_output(["vm_stat"], text=True)
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    vals = {k: int(v.replace(".", "")) for k, v in re.findall(r"Pages ([\w ]+):\s+(\d+\.)", vm)}
    total = int(subprocess.check_output(["sysctl", "-n", "hw.memsize"]))
    return {"reclaimable_fraction": page * sum(vals[k] for k in ("free", "inactive", "speculative")) / total,
            "disk_free_bytes": shutil.disk_usage(ROOT).free}

def call(label, argv, *, stdin=None):
    sample = resources()
    if sample["reclaimable_fraction"] <= MIN_MEMORY or sample["disk_free_bytes"] <= MIN_DISK:
        raise RuntimeError(f"helper admission denied before {label}: {sample}")
    start = time.monotonic()
    p = subprocess.run(argv, cwd=ROOT, input=stdin, capture_output=True, timeout=8)
    row = {"label": label, "argv": [str(x) for x in argv], "returncode": p.returncode,
           "elapsed_seconds": round(time.monotonic() - start, 6), "admission": sample,
           "stdout_utf8": p.stdout.decode(errors="replace"), "stderr_utf8": p.stderr.decode(errors="replace"),
           "stdout_sha256": sha(p.stdout), "stderr_sha256": sha(p.stderr)}
    return row

def main():
    ap = argparse.ArgumentParser()
    for suffix in ("016", "019", "020"):
        ap.add_argument(f"--bin-{suffix}", type=Path, required=True)
    a = ap.parse_args()
    bins = {"0.1.16": a.bin_016.resolve(), "0.1.19": a.bin_019.resolve(), "0.1.20": a.bin_020.resolve()}
    for version, path in bins.items():
        assert sha(path.read_bytes()) == EXPECTED[version], (version, path)
    fixture = {p.name: sha(p.read_bytes()) for p in (ROOT / "fixture").iterdir() if p.is_file()}
    assert (ROOT / "fixture/build.trace").read_bytes() == b"123456789"
    assert (ROOT / "fixture/artifact.txt").read_bytes() == b"Anneal R491 helper comparison\n"
    work = ROOT / "work"
    if work.exists(): shutil.rmtree(work)
    work.mkdir()
    result = {"schema": 1, "status": "running", "binary_sha256": EXPECTED, "binary_paths": {k: str(v) for k,v in bins.items()},
              "fixture_sha256": fixture, "guard": {"minimum_memory_fraction": MIN_MEMORY, "minimum_disk_bytes": MIN_DISK},
              "calls": [], "archives": {}, "extractions": [], "stripped": {}}
    labels = {"0.1.16": "016", "0.1.19": "019", "0.1.20": "020"}
    for version, binary in bins.items():
        row = call(f"version-{labels[version]}", [str(binary), "--version"])
        result["calls"].append(row)
        assert row["returncode"] == 0 and row["stdout_utf8"].strip() == f"leantar {version}", row
    for producer, binary in bins.items():
        archive = work / f"by-{labels[producer]}.ltar"
        row = call(f"pack-{labels[producer]}", [str(binary), str(archive), "fixture/build.trace", "fixture/artifact.txt"])
        result["calls"].append(row)
        assert row["returncode"] == 0, row
        raw = archive.read_bytes()
        result["archives"][producer] = {"sha256": sha(raw), "size": len(raw), "magic": raw[:4].decode()}
        for consumer, unpacker in bins.items():
            dest = work / f"unpack-{labels[producer]}-with-{labels[consumer]}"
            dest.mkdir()
            row = call(f"unpack-{labels[producer]}-{labels[consumer]}",
                       [str(unpacker), "-d", "-f", "--jobs", "1", "-C", str(dest), str(archive)])
            result["calls"].append(row)
            paths = [dest / "fixture/build.trace", dest / "fixture/artifact.txt"]
            extracted = {p.name: sha(p.read_bytes()) if p.is_file() else None for p in paths}
            result["extractions"].append({"producer": producer, "consumer": consumer,
                                          "returncode": row["returncode"], "files_sha256": extracted})
    assert all(x["returncode"] == 0 and x["files_sha256"] == fixture for x in result["extractions"])
    # v0.1.20 adds -s and LTR4. An injected depHash is needed to reconstruct a trace.
    stripped = work / "stripped-020.ltar"
    row = call("pack-stripped-020", [str(bins["0.1.20"]), "-s", str(stripped),
                                      "fixture/build.trace", "fixture/artifact.txt"])
    result["calls"].append(row)
    assert row["returncode"] == 0, row
    raw = stripped.read_bytes()
    result["stripped"]["archive"] = {"sha256": sha(raw), "size": len(raw), "magic": raw[:4].decode()}
    assert raw[:4] == b"LTR4"
    for consumer in ("0.1.16", "0.1.19"):
        dest = work / f"unpack-stripped-with-{labels[consumer]}"
        dest.mkdir()
        row = call(f"unpack-stripped-{labels[consumer]}", [str(bins[consumer]), "-d", "-f",
                       "--jobs", "1", "-C", str(dest), str(stripped)])
        result["calls"].append(row)
        result["stripped"][consumer] = {"returncode": row["returncode"],
                                         "output_files": sorted(str(p.relative_to(dest)) for p in dest.rglob("*") if p.is_file())}
        assert row["returncode"] != 0 and not result["stripped"][consumer]["output_files"]
    dest = work / "unpack-stripped-with-020"
    dest.mkdir()
    request = b'[{"file":"work/stripped-020.ltar","hash":"75bcd15"}]\n'
    row = call("unpack-stripped-020", [str(bins["0.1.20"]), "-d", "-f", "--jobs", "1", "-C", str(dest), "-j", "-"], stdin=request)
    result["calls"].append(row)
    trace = (dest / "fixture/build.trace").read_bytes()
    artifact = (dest / "fixture/artifact.txt").read_bytes()
    result["stripped"]["0.1.20"] = {"returncode": row["returncode"], "request_sha256": sha(request),
                                      "trace_utf8": trace.decode(), "trace_sha256": sha(trace),
                                      "artifact_sha256": sha(artifact)}
    assert row["returncode"] == 0 and artifact == (ROOT / "fixture/artifact.txt").read_bytes()
    assert b'"depHash":"00000000075bcd15"' in trace
    result["status"] = "completed"
    (ROOT / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("PASS: 3 producers x 3 consumers, exact fixture bytes")

if __name__ == "__main__": main()
