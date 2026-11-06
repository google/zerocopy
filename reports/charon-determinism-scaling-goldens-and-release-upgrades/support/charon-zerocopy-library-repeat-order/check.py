#!/usr/bin/env python3
"""Check the retained bounded observation and optionally the raw scratch LLBC."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from compare import array_end, KEY

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, help="optional original or replay scratch with raw LLBC")
    ap.add_argument("--exact-original", action="store_true",
                    help="require original raw LLBC and log hashes (with --work)")
    args = ap.parse_args()
    if args.exact_original and not args.work:
        ap.error("--exact-original requires --work")
    record = json.loads((HERE / "observations.json").read_text())
    comparison = json.loads((HERE / "comparison.json").read_text())
    replay = json.loads((HERE / "replay-comparison.json").read_text())
    assert record["comparison"] == comparison
    assert all(comparison["checks"].values())
    assert replay["checks"] == comparison["checks"]
    sample = json.loads((HERE / "first-order-differences.json").read_text())
    assert len(sample) == 3
    assert len({x["index"] for x in sample}) == 3
    for n in (1, 2, 3):
        key = f"run{n}"
        run = record["runs"][key]
        log = record["logs"][key]
        assert run["exit"] == 0 and run["stop_reason"] is None
        assert run["llbc_sha256"] == comparison[key]["raw_sha256"]
        assert run["llbc_bytes"] == comparison[key]["raw_bytes"]
        assert comparison[key]["has_errors"] is True
        assert replay[key]["short_names_multiset_sha256"] == comparison[key]["short_names_multiset_sha256"]
        assert replay[key]["short_names_entries"] == comparison[key]["short_names_entries"]
        assert replay[key]["has_errors"] is True
        assert log["charon_warning_count"] == 13 and log["summary_warning_line"] is True
        assert sha(HERE / f"{key}-stderr.txt") == log["redacted_stderr_sha256"]
        for item in sample:
            assert "key" in item[key] and "value" in item[key]
        if args.exact_original:
            source = args.work / key
            assert sha(source / "zerocopy.llbc") == run["llbc_sha256"]
            assert sha(source / "stderr.txt") == log["raw_stderr_sha256"]
            assert sha(source / "stdout.txt") == log["raw_stdout_sha256"]
        if args.exact_original:
            data = (args.work / key / "zerocopy.llbc").read_bytes()
            start = data.index(KEY) + len(KEY)
            names = json.loads(data[start:array_end(data, start)])
            for item in sample:
                assert names[item["index"]] == item[key]
    if args.work:
        subprocess.run([sys.executable, str(HERE / "compare.py"), str(args.work),
                        "--expected", str(HERE / "comparison.json")], check=True)
    print("retained evidence checks passed")


if __name__ == "__main__":
    main()
