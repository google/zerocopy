#!/usr/bin/env python3
"""Copy only sixteen owned E46 pilot artifacts, verify bytes, never execute."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
CID = "c1bf0a443c09a62a7747793d9ce696edfea27dbdc58bbacc652a4d999212c2d5"
DOCKER = shutil.which("docker")
if DOCKER is None:
    raise SystemExit("docker missing")


def main():
    inventory = json.loads((ROOT / "compile-static/captures-v3/x86_64-O3-pilot-after.stdout").read_text())
    selected = [x for x in inventory["outputs"] if not x["path"].endswith(".rlib")]
    if len(selected) != 16:
        raise SystemExit("Unexpected artifact set")
    records = []
    for e in selected:
        dst = ROOT / "compile-static/artifacts" / e["path"]
        if dst.exists():
            raise SystemExit("No overwrite/retry: " + str(dst))
        dst.parent.mkdir(parents=True, exist_ok=True)
        argv = [DOCKER, "cp", CID + ":/e46/" + e["path"], str(dst)]
        started = time.monotonic()
        run = subprocess.run(argv, capture_output=True, timeout=60)
        label = e["path"].replace("/", "-")
        cap = ROOT / "compile-static/copy-captures" / label
        cap.parent.mkdir(parents=True, exist_ok=True)
        cap.with_suffix(cap.suffix + ".stdout").write_bytes(run.stdout)
        cap.with_suffix(cap.suffix + ".stderr").write_bytes(run.stderr)
        record = {"argv": argv, "exit": run.returncode,
                  "elapsed_seconds": time.monotonic() - started,
                  "stdout_sha256": hashlib.sha256(run.stdout).hexdigest(),
                  "stderr_sha256": hashlib.sha256(run.stderr).hexdigest(),
                  "expected": e, "evidence_copy_executed": False}
        if run.returncode or run.stderr:
            (ROOT / "compile-static/copy-failed.json").write_text(json.dumps(record, indent=2) + "\n")
            raise SystemExit("Copy diagnostic: stop")
        dst.chmod(0o644)  # Data evidence only; no container file mode changed.
        record["copy_sha256"] = hashlib.sha256(dst.read_bytes()).hexdigest()
        record["copy_bytes"] = dst.stat().st_size
        record["copy_mode"] = oct(dst.stat().st_mode & 0o777)
        if record["copy_sha256"] != e["sha256"] or record["copy_bytes"] != e["bytes"]:
            raise SystemExit("Artifact identity mismatch: stop")
        records.append(record)
    (ROOT / "compile-static/artifact-copies.json").write_text(json.dumps(records, indent=2) + "\n")
    print(json.dumps({"copies_verified": len(records), "copy_bytes": sum(x["copy_bytes"] for x in records),
                      "container_bytes_unchanged": True, "subject_executed": False}))


if __name__ == "__main__":
    main()
