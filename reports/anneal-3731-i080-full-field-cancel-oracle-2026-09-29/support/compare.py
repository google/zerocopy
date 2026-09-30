#!/usr/bin/env python3
"""Bounded read-only comparison of six retained Charon LLBC JSON objects."""

import hashlib
import json
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE / "artifacts"
RESULT = HERE / "comparison.json"
EXPECTED = {
    "companion-B.llbc": "12904a0345e2d16c1f89aa714a4fb98e5cff1295e0a3c87c46cff2979981d730",
    "oracle-baseline-B.llbc": "fe8b7fd5e4d4bde12b9ed3dc940adc4fb40f27933c1ead8a8121dbb7677d2bff",
    "oracle-edited-A.llbc": "1c4eafdbae3130cb169dbbe99cd04400896de772ee2796f5c91aaa35959c89ea",
    "prewarm-A.llbc": "4b3ee8e86b1b94a37760c8f0f0c021010ef3fde5b162d98f6e22c101faeb3f81",
    "prewarm-B.llbc": "af8c64477b1350fd2c62a5559d125f92f6efb3f4b9e3f860db91365d3880bdcc",
    "recovery-A.llbc": "2a9dc269ba89c215218772f110c59ce780eb020b765c29cb0ef19cd1e0ddc0a1",
}
SOURCE_RESULTS_SHA256 = "42822b050fc86ffa0506927e7ba19a9055c2b57c04d6914253b0682070667107"
MIN_RECLAIMABLE_PERCENT = 20.0
MAX_RSS_BYTES = 64 * 1024 * 1024
MAX_SECONDS = 5.0
PAIRS = (
    ("prewarm_A_to_baseline_oracle", "prewarm-A.llbc", "oracle-baseline-B.llbc"),
    ("prewarm_B_to_baseline_oracle", "prewarm-B.llbc", "oracle-baseline-B.llbc"),
    ("companion_B_to_baseline_oracle", "companion-B.llbc", "oracle-baseline-B.llbc"),
    ("recovery_A_to_edited_oracle", "recovery-A.llbc", "oracle-edited-A.llbc"),
    ("edited_to_baseline_negative_control", "oracle-edited-A.llbc", "oracle-baseline-B.llbc"),
)


class GuardRefusal(Exception):
    pass


def sha(data):
    return hashlib.sha256(data).hexdigest()


def headroom():
    out = subprocess.check_output(["/usr/bin/vm_stat"], text=True, timeout=1)
    page_size = int(re.search(r"page size of (\d+) bytes", out).group(1))
    pages = {name: int(re.search(rf"Pages {name}:\s+(\d+)\.", out).group(1))
             for name in ("free", "inactive", "speculative")}
    physical = int(subprocess.check_output(
        ["/usr/sbin/sysctl", "-n", "hw.memsize"], text=True, timeout=1))
    return {"page_size": page_size, "pages": pages,
            "physical_bytes": physical,
            "estimated_reclaimable_percent": round(
                100 * page_size * sum(pages.values()) / physical, 4)}


def peak_rss_bytes():
    value = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return value if sys.platform == "darwin" else value * 1024


def timeout_handler(signum, frame):
    raise GuardRefusal("wall_time_guard")


def pointer(path, component):
    return path + "/" + str(component).replace("~", "~0").replace("/", "~1")


def deep_diff(left, right, path="", output=None):
    if output is None:
        output = []
    if type(left) is not type(right):
        output.append({"path": path or "/", "left": left, "right": right})
    elif isinstance(left, dict):
        for key in sorted(left.keys() | right.keys()):
            at = pointer(path, key)
            if key not in left:
                output.append({"path": at, "left_missing": True, "right": right[key]})
            elif key not in right:
                output.append({"path": at, "left": left[key], "right_missing": True})
            else:
                deep_diff(left[key], right[key], at, output)
    elif isinstance(left, list):
        for index in range(max(len(left), len(right))):
            at = pointer(path, index)
            if index >= len(left):
                output.append({"path": at, "left_missing": True, "right": right[index]})
            elif index >= len(right):
                output.append({"path": at, "left": left[index], "right_missing": True})
            else:
                deep_diff(left[index], right[index], at, output)
    elif left != right:
        output.append({"path": path or "/", "left": left, "right": right})
    return output


def main():
    if RESULT.exists():
        raise RuntimeError("comparison.json exists; use a fresh copy")
    start = time.monotonic()
    signal.signal(signal.SIGALRM, timeout_handler)
    signal.setitimer(signal.ITIMER_REAL, MAX_SECONDS)
    record = {"schema": 1, "status": "running", "limits": {
        "minimum_estimated_reclaimable_percent": MIN_RECLAIMABLE_PERCENT,
        "maximum_self_peak_rss_bytes": MAX_RSS_BYTES,
        "maximum_wall_seconds": MAX_SECONDS},
        "input_sha256": EXPECTED, "source_results_sha256": SOURCE_RESULTS_SHA256,
        "samples": [], "pairs": {}, "artifacts": {}}

    def gate(stage):
        sample = {"stage": stage,
                  "elapsed_seconds": round(time.monotonic() - start, 5),
                  "self_peak_rss_bytes": peak_rss_bytes(),
                  "host": headroom()}
        record["samples"].append(sample)
        if sample["elapsed_seconds"] > MAX_SECONDS:
            raise GuardRefusal("wall_time_guard")
        if sample["self_peak_rss_bytes"] > MAX_RSS_BYTES:
            raise GuardRefusal("rss_guard")
        if sample["host"]["estimated_reclaimable_percent"] < MIN_RECLAIMABLE_PERCENT:
            raise GuardRefusal("host_memory_guard")
        return sample

    try:
        gate("preflight")
        if sha((HERE / "source-results.json").read_bytes()) != SOURCE_RESULTS_SHA256:
            raise RuntimeError("source results hash mismatch")
        files = {p.name for p in ARTIFACTS.glob("*.llbc")}
        if files != set(EXPECTED):
            raise RuntimeError(f"artifact inventory mismatch: {files}")
        data = {}
        for name in sorted(EXPECTED):
            raw = (ARTIFACTS / name).read_bytes()
            if sha(raw) != EXPECTED[name]:
                raise RuntimeError(f"artifact hash mismatch: {name}")
            data[name] = json.loads(raw)
            record["artifacts"][name] = {"bytes": len(raw), "sha256": sha(raw),
                "crate_name": data[name]["translated"]["crate_name"],
                "has_errors": data[name]["has_errors"]}
            gate("decoded:" + name)
        for label, left_name, right_name in PAIRS:
            differences = deep_diff(data[left_name], data[right_name])
            record["pairs"][label] = {
                "left": left_name, "right": right_name,
                "full_json_equal": not differences,
                "difference_count": len(differences),
                "differences": differences,
            }
            gate("compared:" + label)
        record["status"] = "completed"
    except GuardRefusal as exc:
        record["status"] = "guard_refused"
        record["reason"] = str(exc)
    except Exception as exc:
        record["status"] = "error"
        record["reason"] = repr(exc)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        record["elapsed_seconds"] = round(time.monotonic() - start, 5)
        record["self_peak_rss_bytes"] = peak_rss_bytes()
        RESULT.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"status": record["status"], "reason": record.get("reason"),
                      "elapsed_seconds": record["elapsed_seconds"],
                      "self_peak_rss_bytes": record["self_peak_rss_bytes"]}))
    if record["status"] != "completed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
