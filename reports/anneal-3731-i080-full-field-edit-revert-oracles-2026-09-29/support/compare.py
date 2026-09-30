#!/usr/bin/env python3
"""Guarded, offline full-field comparison of 16 retained I080 LLBC files."""
import hashlib
import json
import re
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE / "artifacts"
SOURCE = json.loads((HERE / "source-results.json").read_text())
OUT = HERE / "comparison.json"
MAX_RSS = 64 * 1024 * 1024
MAX_SECONDS = 5.0
MIN_RECLAIMABLE = 20.0
started = time.monotonic()
samples = []

class GuardFailure(Exception): pass

def timeout(*_):
    raise GuardFailure("five-second wall-time cap")
signal.signal(signal.SIGALRM, timeout)
signal.setitimer(signal.ITIMER_REAL, MAX_SECONDS)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def guard(label):
    elapsed = time.monotonic() - started
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if rss > MAX_RSS: raise GuardFailure(f"RSS {rss} > {MAX_RSS} at {label}")
    if elapsed > MAX_SECONDS: raise GuardFailure(f"elapsed {elapsed} > {MAX_SECONDS} at {label}")
    vm = subprocess.run(["/usr/bin/vm_stat"], capture_output=True, text=True, timeout=1, check=True).stdout
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    counts = {}
    for name in ("free", "inactive", "speculative"):
        counts[name] = int(re.search(rf"Pages {name}:\s+(\d+)\.", vm).group(1))
    physical = int(subprocess.run(["/usr/sbin/sysctl", "-n", "hw.memsize"], capture_output=True,
                                  text=True, timeout=1, check=True).stdout.strip())
    reclaimable = 100 * page * sum(counts.values()) / physical
    samples.append({"label": label, "elapsed_seconds": elapsed, "max_rss_bytes": rss,
                    "reclaimable_percent": reclaimable, "physical_bytes": physical})
    if reclaimable < MIN_RECLAIMABLE:
        raise GuardFailure(f"reclaimable {reclaimable:.4f}% < {MIN_RECLAIMABLE}% at {label}")

def ptr(path, segment):
    return path + "/" + str(segment).replace("~", "~0").replace("/", "~1")

def differences(a, b, path=""):
    if type(a) is not type(b):
        return [{"path": path or "/", "left": a, "right": b}]
    if isinstance(a, dict):
        out = []
        for k in sorted(set(a) | set(b)):
            q = ptr(path, k)
            if k not in a: out.append({"path": q, "left_missing": True, "right": b[k]})
            elif k not in b: out.append({"path": q, "left": a[k], "right_missing": True})
            else: out.extend(differences(a[k], b[k], q))
        return out
    if isinstance(a, list):
        out = []
        for i in range(max(len(a), len(b))):
            q = ptr(path, i)
            if i >= len(a): out.append({"path": q, "left_missing": True, "right": b[i]})
            elif i >= len(b): out.append({"path": q, "left": a[i], "right_missing": True})
            else: out.extend(differences(a[i], b[i], q))
        return out
    return [] if a == b else [{"path": path or "/", "left": a, "right": b}]

def expected_hashes():
    found = {}
    for cell in SOURCE["cells"]:
        inc = cell["incremental"]
        for state, run in cell["oracle"].items():
            label = f"inc{inc}-oracle-{state}"
            assert run["label"] == label
            found[label] = run["output"]["sha256"]
        for phase in cell["phases"]:
            for name, run in phase["runs"].items():
                label = f"inc{inc}-{phase['name']}-{name}"
                assert run["label"] == label
                found[label] = run["output"]["sha256"]
    assert len(found) == 16
    assert {p.stem for p in ARTIFACTS.glob("*.llbc")} == set(found)
    return found

def main():
    guard("preflight-before-input")
    hashes = expected_hashes()
    documents = {}
    for label in sorted(hashes):
        raw = (ARTIFACTS / f"{label}.llbc").read_bytes()
        if sha(raw) != hashes[label]: raise GuardFailure(f"source hash mismatch: {label}")
        documents[label] = json.loads(raw)
        guard(f"decoded-{label}")
    pairs = []
    for inc in (0, 1):
        for state in ("baseline", "edited", "reverted"):
            for name in ("A", "B"):
                left = f"inc{inc}-{state}-{name}"
                oracle_state = "edited" if state == "edited" and name == "A" else "baseline"
                right = f"inc{inc}-oracle-{oracle_state}"
                diff = differences(documents[left], documents[right])
                pairs.append({"left": left, "right": right, "left_sha256": hashes[left],
                              "right_sha256": hashes[right], "difference_count": len(diff),
                              "differences": diff})
                guard(f"compared-{left}")
    negatives = []
    for inc in (0, 1):
        left, right = f"inc{inc}-oracle-edited", f"inc{inc}-oracle-baseline"
        diff = differences(documents[left], documents[right])
        if not diff: raise GuardFailure(f"negative control has no difference: inc{inc}")
        negatives.append({"left": left, "right": right, "left_sha256": hashes[left],
                          "right_sha256": hashes[right], "difference_count": len(diff),
                          "differences": diff})
        guard(f"negative-control-inc{inc}")
    result = {"status": "completed", "source_results_sha256": sha((HERE / "source-results.json").read_bytes()),
              "artifact_sha256": hashes, "limits": {"max_rss_bytes": MAX_RSS,
              "max_seconds": MAX_SECONDS, "min_reclaimable_percent": MIN_RECLAIMABLE},
              "samples": samples, "pairs": pairs, "negative_controls": negatives,
              "elapsed_seconds": time.monotonic() - started,
              "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    if result["elapsed_seconds"] > MAX_SECONDS or result["peak_rss_bytes"] > MAX_RSS:
        raise GuardFailure("final resource cap")
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(f"completed: {len(pairs)} oracle pairs, {len(negatives)} negative controls; peak RSS {result['peak_rss_bytes']}")

try:
    main()
except (GuardFailure, subprocess.SubprocessError, ValueError, AssertionError) as exc:
    refusal = {"status": "refused", "reason": str(exc), "samples": samples,
               "elapsed_seconds": time.monotonic() - started,
               "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    OUT.write_text(json.dumps(refusal, indent=2, sort_keys=True) + "\n")
    print(f"REFUSED: {exc}", file=sys.stderr)
    sys.exit(2)
finally:
    signal.setitimer(signal.ITIMER_REAL, 0)
