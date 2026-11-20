#!/usr/bin/env python3
"""Companion batch: all four models in the extended-corridor geometry (no wall behind exit).
Usage: PYTHONPATH=... jps_batch_ext.py <out.jsonl> [workers]"""
import concurrent.futures as cf, json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
cfgs = [{"study": "ext", "geometry": "ext", "model": m, "dt": dt, "seed": s}
        for m in ["SFM", "GCFM", "CFSM", "AVM"] for dt in [0.005, 0.01] for s in [0, 1, 2]]
def one(c):
    p = subprocess.run([sys.executable, os.path.join(HERE, "jps_probe.py"), json.dumps(c)], capture_output=True, text=True)
    return p.stdout.strip() if p.returncode == 0 else json.dumps(dict(c, error=p.stderr[-300:]))
with open(sys.argv[1], "w") as f, cf.ThreadPoolExecutor(int(sys.argv[2]) if len(sys.argv) > 2 else 24) as ex:
    for line in ex.map(one, cfgs):
        f.write(line + "\n"); f.flush()
