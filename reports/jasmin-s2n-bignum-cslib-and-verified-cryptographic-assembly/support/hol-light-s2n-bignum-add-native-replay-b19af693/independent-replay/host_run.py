#!/usr/bin/env python3
"""Task-owned stream/status capture; never interprets source or changes argv."""
import datetime, hashlib, json, os, subprocess, sys, time
from pathlib import Path

root = Path(__file__).resolve().parent
label = sys.argv[1]
spec = json.loads((root / "specs" / (label + ".json")).read_text())
logs = root / "logs"
logs.mkdir(exist_ok=True)
receipt = logs / (label + ".json")
if receipt.exists():
    raise SystemExit("phase already exists; no implicit retry")
start = time.monotonic()
meta = {"argv": spec["argv"], "cwd": str(root),
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "classification": spec.get("classification", "task command")}
inp = (root / spec["stdin_file"]).read_bytes() if spec.get("stdin_file") else None
with (logs / (label + ".stdout")).open("wb") as so, (logs / (label + ".stderr")).open("wb") as se:
    proc = subprocess.Popen(spec["argv"], cwd=root, stdin=subprocess.PIPE if inp is not None else subprocess.DEVNULL, stdout=so, stderr=se)
    meta["host_pid"] = proc.pid
    (logs / (label + "-start.json")).write_text(json.dumps(meta, indent=2) + "\n")
    proc.communicate(inp)
    meta["returncode"] = proc.returncode
meta["elapsed_seconds"] = time.monotonic() - start
for stream in ("stdout", "stderr"):
    b = (logs / (label + "." + stream)).read_bytes()
    meta[stream + "_bytes"] = len(b)
    meta[stream + "_sha256"] = hashlib.sha256(b).hexdigest()
receipt.write_text(json.dumps(meta, indent=2) + "\n")
print(json.dumps(meta, indent=2))
raise SystemExit(0 if proc.returncode == 0 else 1)
