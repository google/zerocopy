#!/usr/bin/env python3
"""Guarded offline full-field LLBC matrix across layout, incremental mode and warmth."""
import copy
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

def timeout(*_): raise Refusal("five-second wall-time cap")
signal.signal(signal.SIGALRM, timeout)
signal.setitimer(signal.ITIMER_REAL, MAX_SECONDS)

def sha(raw): return hashlib.sha256(raw).hexdigest()
def path(label): return HERE / "artifacts" / label
def pointer(prefix, key): return prefix + "/" + str(key).replace("~", "~0").replace("/", "~1")

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
    if reclaimable <= MIN_RECLAIMABLE:
        raise Refusal(f"reclaimable {reclaimable:.4f}% <= {MIN_RECLAIMABLE}% at {label}")

def differences(a, b, prefix=""):
    if type(a) is not type(b):
        return [{"path": prefix or "/", "left": a, "right": b}]
    if isinstance(a, dict):
        out = []
        for key in sorted(set(a) | set(b)):
            p = pointer(prefix, key)
            if key not in a: out.append({"path": p, "left_missing": True, "right": b[key]})
            elif key not in b: out.append({"path": p, "left": a[key], "right_missing": True})
            else: out.extend(differences(a[key], b[key], p))
        return out
    if isinstance(a, list):
        out = []
        for i in range(max(len(a), len(b))):
            p = pointer(prefix, i)
            if i >= len(a): out.append({"path": p, "left_missing": True, "right": b[i]})
            elif i >= len(b): out.append({"path": p, "left": a[i], "right_missing": True})
            else: out.extend(differences(a[i], b[i], p))
        return out
    return [] if a == b else [{"path": prefix or "/", "left": a, "right": b}]

def short_name_map(document):
    out = {}
    for item in document["translated"]["short_names"]:
        key = json.dumps(item["key"], sort_keys=True, separators=(",", ":"))
        if key in out: raise Refusal("duplicate short-name key")
        out[key] = item["value"]
    return out

def label(layout, inc, phase, root):
    return f"{layout.ljust(7, '_')}-inc{inc}/{phase}-{root}.llbc"

def hashes_from_source():
    hashes = {}
    assert [(c["layout"], c["incremental"]) for c in SOURCE["cells"]] == [
        ("private", 0), ("private", 1), ("shared", 0), ("shared", 1)]
    for cell in SOURCE["cells"]:
        layout, inc = cell["layout"], cell["incremental"]
        assert [p["phase"] for p in cell["phases"]] == ["cold", "warm"]
        for phase in cell["phases"]:
            for root, run in phase["results"].items():
                assert root in ("A", "B")
                hashes[label(layout, inc, phase["phase"], root)] = run["output"]["sha256"]
    assert len(hashes) == 16
    assert {p.relative_to(HERE / "artifacts").as_posix() for p in (HERE / "artifacts").rglob("*.llbc")} == set(hashes)
    return hashes

def main():
    guard("preflight-before-input")
    hashes = hashes_from_source()
    docs = {}
    for name in sorted(hashes):
        raw = path(name).read_bytes()
        if sha(raw) != hashes[name]: raise Refusal(f"source hash mismatch: {name}")
        docs[name] = json.loads(raw)
        guard(f"decoded-{name}")
    pairs = []
    specs = []
    for layout in ("private", "shared"):
        for inc in (0, 1):
            for root in ("A", "B"):
                specs.append(("warm_vs_cold", label(layout, inc, "warm", root),
                              label(layout, inc, "cold", root)))
    for inc in (0, 1):
        for phase in ("cold", "warm"):
            for root in ("A", "B"):
                specs.append(("shared_vs_private", label("shared", inc, phase, root),
                              label("private", inc, phase, root)))
    for layout in ("private", "shared"):
        for phase in ("cold", "warm"):
            for root in ("A", "B"):
                specs.append(("inc1_vs_inc0", label(layout, 1, phase, root),
                              label(layout, 0, phase, root)))
    assert len(specs) == 24
    for axis, left, right in specs:
        delta = differences(docs[left], docs[right])
        pairs.append({"axis": axis, "left": left, "right": right,
                      "left_sha256": hashes[left], "right_sha256": hashes[right],
                      "difference_count": len(delta), "differences": delta,
                      "short_names_keyed_maps_equal": short_name_map(docs[left]) == short_name_map(docs[right])})
        guard(f"compared-{axis}-{left}")
    basis = docs[label("private", 0, "cold", "A")]
    controls = []
    for kind in ("crate_name", "function_body", "short_names_order"):
        mutant = copy.deepcopy(basis)
        if kind == "crate_name":
            mutant["translated"]["crate_name"] = "synthetic_other_crate"
            prefix = "/translated/crate_name"
        elif kind == "function_body":
            mutant["translated"]["fun_decls"][0]["body"] = "synthetic_changed_body"
            prefix = "/translated/fun_decls/0/body"
        else:
            names = mutant["translated"]["short_names"]
            if len(names) < 2 or names[0] == names[1]: raise Refusal("short-name control unavailable")
            names[0], names[1] = names[1], names[0]
            prefix = "/translated/short_names/"
        delta = differences(basis, mutant)
        if not any(x["path"].startswith(prefix) for x in delta):
            raise Refusal(f"synthetic control not detected: {kind}")
        controls.append({"kind": kind, "difference_count": len(delta), "differences": delta})
        guard(f"synthetic-control-{kind}")
    result = {"status": "completed", "source_results_sha256": sha((HERE / "source-results.json").read_bytes()),
              "artifact_sha256": hashes, "pairs": pairs, "synthetic_negative_controls": controls,
              "limits": {"max_rss_bytes": MAX_RSS, "max_seconds": MAX_SECONDS,
                         "min_reclaimable_percent": MIN_RECLAIMABLE},
              "samples": samples, "elapsed_seconds": time.monotonic() - started,
              "peak_rss_bytes": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    if result["elapsed_seconds"] > MAX_SECONDS or result["peak_rss_bytes"] > MAX_RSS:
        raise Refusal("final resource cap")
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n")
    print(f"completed: {len(pairs)} full-field pairs, {len(controls)} synthetic controls; peak RSS {result['peak_rss_bytes']}")

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
