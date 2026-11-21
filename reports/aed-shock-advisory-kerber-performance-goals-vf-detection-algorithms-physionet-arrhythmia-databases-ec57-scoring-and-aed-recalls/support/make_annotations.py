#!/usr/bin/env python3
"""Generate synthetic WFDB records (header only, no signal files) and
text-format annotation files for the beat-by-beat (bxb), episode-by-episode
(epicmp), and aggregate (sumstats) comparators of the WFDB Software Package,
and for wfdb-python's Comparitor.

The records are synthetic annotation timelines, not ECGs: every number the
probe prints characterizes the scoring tools, not any detector or device.

Usage: make_annotations.py OUTDIR
Writes OUTDIR/<rec>.hea and OUTDIR/<rec>.<ann>.txt (rdann-style text that
`wrann -r <rec> -a <ann>` converts to binary annotation files).
"""
import json
import os
import sys

FS = 360  # samples per second (MIT-BIH Arrhythmia Database rate)


def tstr(sample):
    s = sample / FS
    m, sec = divmod(s, 60)
    return "%d:%06.3f" % (int(m), sec)


def line(sample, code, sub=0, chan=0, num=0, aux=None):
    s = "%12s %10d %5s %4d %4d %4d" % (tstr(sample), sample, code, sub, chan, num)
    if aux:
        s += "\t" + aux
    return s + "\n"


def write_record(outdir, rec, nsamp):
    # Header with zero signals: enough for sampfreq() and strtim("e").
    with open(os.path.join(outdir, rec + ".hea"), "w") as f:
        f.write("%s 0 %d %d\n" % (rec, FS, nsamp))


def write_ann(outdir, rec, ann, events):
    events = sorted(events, key=lambda e: (e[0], 0 if e[1] in "[" else 1))
    with open(os.path.join(outdir, "%s.%s.txt" % (rec, ann)), "w") as f:
        for ev in events:
            f.write(line(*ev))


def main(outdir):
    os.makedirs(outdir, exist_ok=True)
    meta = {}

    # Record "win": matching-window boundary. Reference normal beats every
    # 1 s from 301 s to 360 s; test beat k is displaced by OFFSETS[k % len].
    offsets = [0, 20, 35, 36, 53, 54, 55, -53, -54, -55]
    ref, test = [], []
    for k in range(60):
        t = (301 + k) * FS
        ref.append((t, "N"))
        test.append((t + offsets[k % len(offsets)], "N"))
    write_record(outdir, "win", 362 * FS)
    write_ann(outdir, "win", "atr", ref)
    write_ann(outdir, "win", "tst", test)
    meta["win"] = {"ref": [e[0] for e in ref], "test": [e[0] for e in test],
                   "offsets": offsets}

    # Record "vfx": reference VF episode (VFON..VFOFF) from 320 s to 330 s.
    # Reference beats every 1 s from 301-319 s and 331-350 s; test detector
    # emits beats every 1 s from 301-350 s INCLUDING inside reference VF,
    # plus a non-beat rhythm label at 340 s in the reference.
    ref, test = [], []
    for k in range(301, 351):
        if not (320 <= k <= 330):
            ref.append((k * FS, "N"))
        test.append((k * FS, "N"))
    ref.append((int(319.5 * FS), "["))
    ref.append((int(330.5 * FS), "]"))
    ref.append((int(340.2 * FS), "+", 0, 0, 0, "(N"))
    write_record(outdir, "vfx", 352 * FS)
    write_ann(outdir, "vfx", "atr", ref)
    write_ann(outdir, "vfx", "tst", test)

    # Record "lrn": learning period. Reference and test beats every 1 s from
    # 10 s to 360 s; the test detector misses EVERY beat before 300 s.
    ref, test = [], []
    for k in range(10, 361):
        ref.append((k * FS, "N"))
        if k >= 300:
            test.append((k * FS, "N"))
    write_record(outdir, "lrn", 362 * FS)
    write_ann(outdir, "lrn", "atr", ref)
    write_ann(outdir, "lrn", "tst", test)

    # Records "agA" and "agB": gross vs average aggregation.
    # agA: 60 beats after the learning period, test misses 1.
    # agB: 6 beats after the learning period, test misses 3.
    for rec, nbeats, missed in (("agA", 60, {5}), ("agB", 6, {1, 3, 5})):
        ref, test = [], []
        for k in range(nbeats):
            t = (301 + k) * FS
            ref.append((t, "N"))
            if k not in missed:
                test.append((t, "N"))
        write_record(outdir, rec, (302 + nbeats) * FS)
        write_ann(outdir, rec, "atr", ref)
        write_ann(outdir, rec, "tst", test)
        meta[rec] = {"ref": [e[0] for e in ref], "test": [e[0] for e in test]}

    # Record "epi": VF episode scoring.
    # Reference VF episodes: E1 310-330 s, E2 400-420 s.
    # Test VF episodes: T1 329.9-335 s (overlaps E1 by 0.1 s),
    #                   T2 420-425 s (starts exactly when E2 ends),
    #                   T3 500-502 s (no reference VF at all).
    ref = [(310 * FS, "["), (330 * FS, "]"), (400 * FS, "["), (420 * FS, "]")]
    test = [(int(329.9 * FS), "["), (335 * FS, "]"),
            (420 * FS, "["), (425 * FS, "]"),
            (500 * FS, "["), (502 * FS, "]")]
    write_record(outdir, "epi", 600 * FS)
    write_ann(outdir, "epi", "atr", ref)
    write_ann(outdir, "epi", "tst", test)

    with open(os.path.join(outdir, "beats.json"), "w") as f:
        json.dump(meta, f)


if __name__ == "__main__":
    main(sys.argv[1])
