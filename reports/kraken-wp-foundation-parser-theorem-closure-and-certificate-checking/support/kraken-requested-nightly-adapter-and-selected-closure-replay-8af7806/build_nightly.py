"""Fresh requested-nightly build via serial actual Lake module targets.

No upstream source patches, installs, caches or old OLean imports. At most one
new module target per Lake invocation; LEAN_NUM_THREADS=2. Source globs match
the two selected library roots and all Kraken submodules, excluding executables.
"""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parent.parent
source = root / "kraken-source"
toolroot = Path(sys.argv[1]).resolve(strict=True)
lake = toolroot / "bin/lake"
env = dict(os.environ)
env.pop("LEAN_PATH", None)
env.update(PATH=str(toolroot / "bin") + os.pathsep + env["PATH"],
           LEAN_SYSROOT=str(toolroot), ELAN_HOME=str(toolroot.parent.parent),
           LEAN_NUM_THREADS="2")
paths = {p.relative_to(source).with_suffix("").as_posix().replace("/", "."): p
         for p in source.rglob("*.lean")}
selected = {name for name in paths if name.startswith("Kraken.") or name in {"Kraken", "KrakenAArch64"}}
deps = {}
for name in selected:
    imported = re.findall(r"^(?:(?:public|meta)\s+)*import\s+([A-Za-z0-9_.]+)", paths[name].read_text(), re.M)
    deps[name] = {n for n in imported if n in selected}
order, pending = [], set(selected)
while pending:
    ready = sorted(n for n in pending if not deps[n] & pending)
    if not ready:
        raise SystemExit("Local import cycle or incomplete dependency parser")
    order.extend(ready)
    pending.difference_update(ready)
(root / "build-order.json").write_text(json.dumps(dict(order=order, dependencies={n: sorted(ds) for n, ds in deps.items()},
    concurrency="serial Lake target invocations; LEAN_NUM_THREADS=2", excluded_executables=sorted(set(paths)-selected)), indent=2)+"\n")
rows = []
for name in order:
    argv = ["--no-cache", "--fail-fast", "build", "+" + name]
    started = time.monotonic()
    result = subprocess.run([str(lake)] + argv, cwd=source, env=env, capture_output=True, text=True)
    output = result.stdout + result.stderr
    log = "logs/build-" + name.replace(".", "-") + ".log"
    (root / log).write_text(output)
    row = dict(tool="requested-nightly lake", argv=argv, cwd="kraken-source", exit=result.returncode,
               log=log, elapsed_seconds=time.monotonic()-started,
               diagnostic_pretty_printer_fallbacks=output.count("Error pretty printing expression"),
               output_sha256=hashlib.sha256(output.encode()).hexdigest())
    rows.append(row)
    (root / "build-results.json").write_text(json.dumps(rows, indent=2)+"\n")
    print(json.dumps(row), flush=True)
    if result.returncode or re.search(r"(?i)panic|assertion failed", output):
        raise SystemExit("Stopped affected path for diagnosis")
    used = sum(p.stat().st_size for p in root.parent.rglob("*") if p.is_file())
    if used >= 500 * 1024 * 1024:
        raise SystemExit("Stopped at owned500MiB bound")
print(json.dumps(dict(status="pass", module_targets=len(rows), maximum_new_module_targets=1,
                     lean_runtime_threads=2, all_exit_zero=True)), flush=True)
