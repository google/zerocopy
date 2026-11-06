"""Parent-authorized identity/positive compilation stage. Never runs the image."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
CAP = 50 * 1024 * 1024


def sha(b):
    return hashlib.sha256(b).hexdigest()


def size():
    return sum(f.stat().st_size for f in ROOT.rglob("*") if f.is_file())


def run(name, argv):
    if size() > CAP:
        raise ValueError("stop: current owned root exceeds 50MiB")
    logs = ROOT / "captures"
    logs.mkdir(exist_ok=True)
    tmp = ROOT / "tmp"
    tmp.mkdir(exist_ok=True)
    env = dict(os.environ)
    env["TMPDIR"] = str(tmp) + "/"
    start = time.monotonic()
    r = subprocess.run(argv, cwd=ROOT, env=env, capture_output=True, timeout=120)
    streams = {}
    for label, data in [("stdout", r.stdout), ("stderr", r.stderr)]:
        p = logs / (name + "." + label)
        p.write_bytes(data)
        streams[label] = {"path": p.relative_to(ROOT).as_posix(), "sha256": sha(data), "bytes": len(data)}
    record = {"argv": argv, "cwd": "<OWNED_NATIVE_UNWIND_ROOT>", "TMPDIR": "<OWNED_NATIVE_UNWIND_ROOT>/tmp/",
              "exit": r.returncode, "seconds": time.monotonic() - start, "streams": streams,
              "source_sha256": {n: sha((ROOT / n).read_bytes()) for n in ["bounce.s", "specimen.rs"]}}
    (logs / (name + ".json")).write_text(json.dumps(record, indent=2) + "\n")
    if r.returncode:
        raise ValueError("stop: nonzero command " + name + "; inspect captured diagnostics")
    if re.search(rb"(?:thread .* panicked|LLVM ERROR|Assertion .*failed|PLEASE submit a bug report)", r.stdout + r.stderr, re.I):
        raise ValueError("stop: unexpected tool panic/assertion diagnostic " + name)
    if size() > CAP:
        raise ValueError("stop: owned root output exceeds 50MiB")
    print(name + ": exit0", flush=True)
    return r.stdout


def main():
    plan = json.loads((ROOT / "commands-proposed.json").read_text())
    for name, expected in plan["source_hashes"].items():
        if sha((ROOT / name).read_bytes()) != expected:
            raise ValueError("stop: reviewed source changed " + name)
    if sys.argv[1:] == ["identities"]:
        version = run("rustc-version", ["rustc", "-Vv"]).decode()
        if plan["required_rustc_commit"] not in version or "LLVM version: 23.1.1" not in version or "host: aarch64-apple-darwin" not in version:
            raise ValueError("stop: reviewed compiler identity mismatch")
        sysroot = Path(run("rustc-sysroot", ["rustc", "--print", "sysroot"]).decode().strip()).resolve()
        rustc = sysroot / "bin/rustc"
        driver = sorted((sysroot / "lib").glob("librustc_driver-*.dylib"))
        if len(driver) != 1:
            raise ValueError("stop: ambiguous compiler driver identity")
        tools = [rustc, driver[0]]
        for name in ["llvm-objdump", "llvm-dwarfdump"]:
            tool = Path("/Library/Developer/CommandLineTools/usr/bin") / name
            run(name + "-version", [str(tool), "--version"])
            run(name + "-help", [str(tool), "--help"])
            tools.append(tool)
        for name in ["nm", "otool"]:
            tool = Path("/Library/Developer/CommandLineTools/usr/bin") / name
            if tool.is_file():
                tools.append(tool)
        identities = [{"path": str(p), "bytes": p.stat().st_size, "sha256": sha(p.read_bytes())} for p in tools]
        (ROOT / "tool-identities.json").write_text(json.dumps({"rustc_actual": str(rustc), "files": identities,
                                                               "rustc_version": version, "stage": "identities only; no image execution"}, indent=2) + "\n")
    elif sys.argv[1:] == ["compile"]:
        identity = json.loads((ROOT / "tool-identities.json").read_text())
        for item in identity["files"][:2]:
            if sha(Path(item["path"]).read_bytes()) != item["sha256"]:
                raise ValueError("stop: compiler identity changed")
        (ROOT / "build").mkdir(exist_ok=True)
        argv = plan["compile_argv"].copy()
        argv[0] = identity["rustc_actual"]
        run("positive-compile-direct", argv)
        outputs = []
        for name in ["specimen.o", "specimen.s", "specimen"]:
            f = ROOT / "build" / name
            outputs.append({"path": f.relative_to(ROOT).as_posix(), "bytes": f.stat().st_size, "sha256": sha(f.read_bytes())})
        (ROOT / "compile-outputs.json").write_text(json.dumps({"outputs": outputs, "source_hashes": plan["source_hashes"],
                                                               "native_executed": False, "owned_bytes": size()}, indent=2) + "\n")
    else:
        raise ValueError("choose identities or compile; no image-run mode exists")


if __name__ == "__main__":
    main()
