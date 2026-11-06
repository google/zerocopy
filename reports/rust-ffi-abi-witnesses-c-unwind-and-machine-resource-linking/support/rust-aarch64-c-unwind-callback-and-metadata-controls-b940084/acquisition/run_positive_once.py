"""Parent-authorized ONE unchanged positive native run; no retry mode."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EXPECTED_IMAGE = "39fe9089fd8449dbe783bc1549daa67fc60d221982be1ecdf345c1b4a721cedf"


def sha(b):
    return hashlib.sha256(b).hexdigest()


def main():
    marker = ROOT / "native-execution-started.json"
    if marker.exists():
        raise ValueError("stop: positive native run already started; no retry authorized")
    image = ROOT / "build/specimen"
    before = sha(image.read_bytes())
    if before != EXPECTED_IMAGE:
        raise ValueError("stop: reviewed positive image changed")
    plan = json.loads((ROOT / "commands-proposed.json").read_text())
    for name, expected in plan["source_hashes"].items():
        if sha((ROOT / name).read_bytes()) != expected:
            raise ValueError("stop: reviewed source changed")
    marker.write_text(json.dumps({"argv": ["./build/specimen"], "image_sha256_before": before,
                                  "authority": "Parent reviewed metadata and authorized one positive serial run only",
                                  "timeout_seconds": 30, "retry_authorized": False}, indent=2) + "\n")
    env = dict(os.environ)
    env["TMPDIR"] = str(ROOT / "tmp") + "/"
    start = time.monotonic()
    try:
        result = subprocess.run(["./build/specimen"], cwd=ROOT, env=env, capture_output=True, timeout=30)
        status, stdout, stderr = result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired as e:
        status, stdout, stderr = "timeout", e.stdout or b"", e.stderr or b""
    for name, stream in [("stdout", stdout), ("stderr", stderr)]:
        (ROOT / "captures" / ("native-positive." + name)).write_bytes(stream)
    after = sha(image.read_bytes())
    record = {"argv": ["./build/specimen"], "cwd": "<OWNED_NATIVE_UNWIND_ROOT>", "exit": status,
              "seconds": time.monotonic() - start, "timeout_seconds": 30,
              "image_sha256_before": before, "image_sha256_after": after,
              "stdout_sha256": sha(stdout), "stderr_sha256": sha(stderr), "retry_authorized": False,
              "native_subject": "unchanged positive image only", "mutants_executed": False}
    (ROOT / "captures/native-positive.json").write_text(json.dumps(record, indent=2) + "\n")
    if status != 0 or after != before:
        raise ValueError("STOP: abnormal native status or changed image; inspect capture, no retry")
    text = stdout.decode()
    error_text = stderr.decode()
    expected_stderr = "EXPECTED_SUBJECT_PANIC marker=0x4534305f554e5744 value=0x1122334455667788\n" * 2
    if error_text != expected_stderr:
        raise ValueError("STOP: unexpected panic/diagnostic stream; no retry")
    pass_lines = re.findall(r"^CASE_PASS path=(Rust|Assembly) panic=(false|true) counts=\[1, 1, 1, 12, ([01])\] trace_status=([05]) ips=\[(.*?)\]$", text, re.M)
    expected_cases = [("Rust", "false", "0"), ("Rust", "true", "1"), ("Assembly", "false", "0"), ("Assembly", "true", "1")]
    if [(p, panic, hooks) for p, panic, hooks, status, ips in pass_lines] != expected_cases:
        raise ValueError("STOP: case/count/backtrace output mismatch; no retry")
    if re.findall(r"^NORMAL_RESULT path=(Rust|Assembly) value=0x336699cd00336699$", text, re.M) != ["Rust", "Assembly"]:
        raise ValueError("STOP: normal oracle output mismatch")
    payloads = re.findall(r"^EXPECTED_PAYLOAD_CONFIRMED path=(Rust|Assembly) marker=0x4534305f554e5744 value=0x1122334455667788$", text, re.M)
    if payloads != ["Rust", "Assembly"] or text.splitlines()[-1] != "ALL_FOUR_CASES_PASSED":
        raise ValueError("STOP: exact typed panic confirmation mismatch")
    print(json.dumps({"exit": status, "four_cases": True, "two_exact_expected_subject_panics": True,
                      "drop_counts_and_order": True, "image_unchanged": before == after,
                      "native_runs": 1, "mutants_executed": False}))


if __name__ == "__main__":
    main()
