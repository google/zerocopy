#!/usr/bin/env python3
"""Throughput / peak-RSS probe of the two annotation comparators on one large
synthetic record: 110,000 reference beats at ~1 s spacing (360 Hz), test beats
displaced by a deterministic pseudo-random offset in [-60, +60] samples, with
every 50th test beat deleted and an extra test beat every 70th beat.

Writes big.hea / big.atr.txt / big.tst.txt / big.json into the current
directory. The companion shell lines in timing_probe.sh run wrann + bxb under
/usr/bin/time -v, and run wfdb-python's Comparitor on the same arrays.
Synthetic data only: numbers characterize the scoring tools' cost.
"""
import json
import sys

FS = 360
N = 110_000


def main():
    state = 12345
    ref, test = [], []
    t = 301 * FS
    for k in range(N):
        state = (1103515245 * state + 12345) % (2**31)
        off = state % 121 - 60
        ref.append(t)
        if k % 50 != 7:
            test.append(t + off)
        if k % 70 == 3:
            test.append(t + FS // 2)
        t += FS + (state % 37) - 18
    test.sort()
    nsamp = t + 2 * FS
    with open("big.hea", "w") as f:
        f.write("big 0 %d %d\n" % (FS, nsamp))
    for name, arr in (("atr", ref), ("tst", test)):
        with open("big.%s.txt" % name, "w") as f:
            for s in arr:
                f.write("%12s %10d %5s %4d %4d %4d\n" % ("0:00.000", s, "N", 0, 0, 0))
    json.dump({"ref": ref, "test": test}, open("big.json", "w"))
    print("reference beats:", len(ref), "test beats:", len(test), "record samples:", nsamp)


if __name__ == "__main__":
    main()
