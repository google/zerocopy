#!/bin/sh
# Time/peak-RSS of bxb (C) and wfdb-python Comparitor (Python) on one large
# synthetic record. Usage:
#   WFDB_BIN=.../wfdb-10.7.0/app EVALUATE_PY=.../evaluate.py WORK=/tmp/aed-probe/big sh timing_probe.sh
set -eu
export PYTHONDONTWRITEBYTECODE=1
HERE=$(cd "$(dirname "$0")" && pwd)
: "${WORK:=/tmp/aed-probe/big}"
: "${WFDB_BIN:?}"; : "${EVALUATE_PY:?}"
rm -rf "$WORK"; mkdir -p "$WORK"; cd "$WORK"
export WFDB=.
python3 "$HERE/make_big_record.py"
"$WFDB_BIN/wrann" -r big -a atr < big.atr.txt
"$WFDB_BIN/wrann" -r big -a tst < big.tst.txt
wc -c big.atr big.tst | head -2
for i in 1 2 3; do
  /usr/bin/time -f "bxb wall=%es maxrss=%MkB" "$WFDB_BIN/bxb" -r big -a atr tst -c bxb_c.out 2>&1 | grep -E "wall|QRS"
done
grep -A6 "Algorithm" bxb_c.out | head -8
WFDB_BIN="$WFDB_BIN" python3 - <<'EOF'
import os, subprocess, time
b = os.path.join(os.environ["WFDB_BIN"], "bxb")
ts = []
for _ in range(20):
    t0 = time.perf_counter()
    subprocess.run([b, "-r", "big", "-a", "atr", "tst", "-c", os.devnull], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    ts.append(time.perf_counter() - t0)
ts.sort()
print("bxb 20 runs (incl. process start): min %.1f ms, median %.1f ms" % (1e3 * ts[0], 1e3 * ts[10]))
EOF
HERE="$HERE" python3 - "$EVALUATE_PY" <<'EOF'
import json, os, resource, sys, time
sys.path.insert(0, os.environ["HERE"])
import numpy as np
from comparitor_probe import load_evaluate
tmp, ev, digest = load_evaluate(sys.argv[1])
d = json.load(open("big.json"))
ref, test = np.array(d["ref"]), np.array(d["test"])
for w in (54, 55):
    best = None
    for _ in range(3):
        t0 = time.perf_counter(); c = ev.compare_annotations(ref, test, w); dt = time.perf_counter() - t0
        best = dt if best is None else min(best, dt)
    print("Comparitor window_width=%d: tp=%d fp=%d fn=%d Se=%.4f +P=%.4f best-of-3 %.2fs" % (
        w, c.tp, c.fp, c.fn, c.sensitivity, c.positive_predictivity, best))
print("python maxrss=%dkB" % resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
tmp.cleanup()
EOF
