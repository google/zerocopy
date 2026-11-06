#!/usr/bin/env python3
"""Read-only E46 object/static capture; never executes a target image."""
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
    raise SystemExit("docker executable missing")


def capture(ident, args):
    directory = ROOT / "compile-static" / "inspection"
    directory.mkdir(parents=True, exist_ok=True)
    prefix = directory / ident
    if prefix.with_suffix(".json").exists():
        raise SystemExit("No implicit inspection retry: " + ident)
    argv = [DOCKER, "exec", "--workdir", "/e46", CID, "/usr/bin/env", "-i",
            "PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "LC_ALL=C", "TZ=UTC"] + args
    started = time.monotonic()
    run = subprocess.run(argv, capture_output=True, timeout=60)
    prefix.with_suffix(".stdout").write_bytes(run.stdout)
    prefix.with_suffix(".stderr").write_bytes(run.stderr)
    receipt = {"argv": argv, "exit": run.returncode,
               "elapsed_seconds": time.monotonic() - started,
               "stdout_bytes": len(run.stdout), "stderr_bytes": len(run.stderr),
               "stdout_sha256": hashlib.sha256(run.stdout).hexdigest(),
               "stderr_sha256": hashlib.sha256(run.stderr).hexdigest(),
               "target_executed": False}
    prefix.with_suffix(".json").write_text(json.dumps(receipt, indent=2) + "\n")
    if run.returncode or run.stderr:
        raise SystemExit("Static tool diagnostic/status: stop " + ident)
    print(json.dumps({"id": ident, "exit": run.returncode, "bytes": len(run.stdout)}))


def main():
    freeze = ROOT / "PREPARATION-FREEZE.json"
    if hashlib.sha256(freeze.read_bytes()).hexdigest() != "42a976cc612912f2729197658b28910e61dd931cd45fb80052e63143f3076df5":
        raise SystemExit("Reviewed v3 freeze changed")
    for e in json.loads(freeze.read_text())["files"]:
        if hashlib.sha256((ROOT / e["path"]).read_bytes()).hexdigest() != e["sha256"]:
            raise SystemExit("Reviewed frozen entry changed: " + e["path"])
    plan = json.loads((ROOT / "commands-proposed.json").read_text())
    for command in plan["commands"]:
        if command["stage"] == "inspect":
            capture(command["id"], command["argv"])
    for arch in ["aarch64", "x86_64"]:
        for opt in [0, 3]:
            capture(f"{arch}-O{opt}-image-dynamic", ["/usr/bin/readelf", "-d", "--version-info",
                    f"build/{arch}/O{opt}/pilot"])
    # File reads only. Missing QEMU-prefix candidates are observations requiring
    # diagnosis before runtime, not instructions to create links or run loaders.
    script = '''from pathlib import Path
import hashlib,json
paths=['/lib/ld-linux-aarch64.so.1','/lib/aarch64-linux-gnu/libc.so.6','/lib/aarch64-linux-gnu/libgcc_s.so.1','/usr/x86_64-linux-gnu/lib/ld-linux-x86-64.so.2','/usr/x86_64-linux-gnu/lib64/ld-linux-x86-64.so.2','/usr/x86_64-linux-gnu/lib/libc.so.6','/usr/x86_64-linux-gnu/lib/libgcc_s.so.1']
out=[]
for name in paths:
 p=Path(name);exists=p.is_file();row={'path':name,'exists':exists,'symlink':p.is_symlink()}
 if exists:row.update({'resolved':str(p.resolve()),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'ELF_identity':p.read_bytes()[:20].hex()})
 out.append(row)
print(json.dumps(out,indent=2))'''
    capture("runtime-library-files-read-only", ["python3", "-c", script])


if __name__ == "__main__":
    main()
