#!/usr/bin/env python3
"""One guarded offline decoded-field comparison of retained warm-bin LLBCs."""
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
SOURCE = json.loads((HERE / "source-results.json").read_text())
OUT = HERE / "comparison.json"
MAX_RSS = 64 * 1024**2
MAX_SECONDS = 5.0
MIN_RECLAIMABLE = 20.0
started = time.monotonic()
samples = []

class Refusal(Exception): pass

def on_timeout(*_):
    raise Refusal("five-second wall-time cap")
signal.signal(signal.SIGALRM, on_timeout)
signal.setitimer(signal.ITIMER_REAL, MAX_SECONDS)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def ptr(path, key): return path + "/" + str(key).replace("~", "~0").replace("/", "~1")

def guard(label):
    elapsed = time.monotonic() - started
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    if rss > MAX_RSS: raise Refusal(f"RSS {rss} > {MAX_RSS} at {label}")
    if elapsed > MAX_SECONDS: raise Refusal(f"elapsed {elapsed} > {MAX_SECONDS} at {label}")
    vm = subprocess.run(["/usr/bin/vm_stat"], capture_output=True, text=True, timeout=1, check=True).stdout
    page = int(re.search(r"page size of (\d+) bytes", vm).group(1))
    counts = [int(re.search(rf"Pages {name}:\s+(\d+)\.", vm).group(1))
              for name in ("free", "inactive", "speculative")]
    physical = int(subprocess.run(["/usr/sbin/sysctl", "-n", "hw.memsize"], capture_output=True,
                                  text=True, timeout=1, check=True).stdout.strip())
    reclaimable = 100 * page * sum(counts) / physical
    samples.append({"label": label, "elapsed_seconds": elapsed, "max_rss_bytes": rss,
                    "physical_bytes": physical, "reclaimable_percent": reclaimable})
    if reclaimable < MIN_RECLAIMABLE:
        raise Refusal(f"reclaimable {reclaimable:.4f}% < {MIN_RECLAIMABLE}% at {label}")

def diff(a, b, path=""):
    if type(a) is not type(b): return [{"path": path or "/", "left": a, "right": b}]
    if isinstance(a, dict):
        result = []
        for key in sorted(set(a) | set(b)):
            p = ptr(path, key)
            if key not in a: result.append({"path": p, "left_missing": True, "right": b[key]})
            elif key not in b: result.append({"path": p, "left": a[key], "right_missing": True})
            else: result.extend(diff(a[key], b[key], p))
        return result
    if isinstance(a, list):
        result = []
        for i in range(max(len(a), len(b))):
            p = ptr(path, i)
            if i >= len(a): result.append({"path": p, "left_missing": True, "right": b[i]})
            elif i >= len(b): result.append({"path": p, "left": a[i], "right_missing": True})
            else: result.extend(diff(a[i], b[i], p))
        return result
    return [] if a == b else [{"path": path or "/", "left": a, "right": b}]

def order_diff(a, b, path=""):
    if type(a) is not type(b): return []
    if isinstance(a, dict):
        result = ([{"path": path or "/", "left_keys": list(a), "right_keys": list(b)}]
                  if list(a) != list(b) else [])
        for key in a.keys() & b.keys(): result.extend(order_diff(a[key], b[key], ptr(path, key)))
        return result
    if isinstance(a, list):
        result = []
        for i in range(min(len(a), len(b))): result.extend(order_diff(a[i], b[i], ptr(path, i)))
        return result
    return []

def keyed_names(doc):
    out = {}
    for entry in doc["translated"]["short_names"]:
        key = json.dumps(entry["key"], sort_keys=True, separators=(",", ":"))
        if key in out: raise Refusal("duplicate short_names key")
        out[key] = entry["value"]
    return out

def main():
    guard("preflight-before-input")
    runs = {r["label"]: r for r in SOURCE["runs"]}
    if set(runs) != {"baseline", "warm_repeat"}: raise Refusal("unexpected source labels")
    docs, raw_hashes, roundtrip = {}, {}, {}
    for label in ("baseline", "warm_repeat"):
        raw = (HERE / "artifacts" / f"{label}.llbc").read_bytes()
        digest = sha(raw)
        if digest != runs[label]["dest_sha256"]: raise Refusal(f"source hash mismatch: {label}")
        doc = json.loads(raw)
        docs[label] = doc
        raw_hashes[label] = digest
        roundtrip[label] = json.dumps(doc, separators=(",", ":"), ensure_ascii=False).encode() == raw
        guard(f"decoded-{label}")
    differences = diff(docs["baseline"], docs["warm_repeat"])
    key_orders = order_diff(docs["baseline"], docs["warm_repeat"])
    maps_equal = keyed_names(docs["baseline"]) == keyed_names(docs["warm_repeat"])
    guard("compared")
    result = {"status": "completed", "source_results_sha256": sha((HERE / "source-results.json").read_bytes()),
              "artifact_sha256": raw_hashes, "roundtrip_exact": roundtrip,
              "difference_count": len(differences), "differences": differences,
              "object_key_order_differences": key_orders, "short_names_keyed_maps_equal": maps_equal,
              "limits": {"max_rss_bytes": MAX_RSS, "max_seconds": MAX_SECONDS,
                         "min_reclaimable_percent": MIN_RECLAIMABLE},
              "samples": samples, "elapsed_seconds": time.monotonic() - started,
              "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    if result["elapsed_seconds"] > MAX_SECONDS or result["peak_rss_bytes"] > MAX_RSS:
        raise Refusal("final resource cap")
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(f"completed: {len(differences)} decoded leaf differences, {len(key_orders)} object-key-order differences; peak RSS {result['peak_rss_bytes']}")

try:
    main()
except (Refusal, subprocess.SubprocessError, ValueError, AssertionError) as exc:
    OUT.write_text(json.dumps({"status": "refused", "reason": str(exc), "samples": samples,
                              "elapsed_seconds": time.monotonic() - started,
                              "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},
                             indent=2, sort_keys=True) + "\n")
    print(f"REFUSED: {exc}", file=sys.stderr)
    sys.exit(2)
finally:
    signal.setitimer(signal.ITIMER_REAL, 0)
