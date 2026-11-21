#!/usr/bin/env python3
"""Compare SNOWPACK test outputs against the repository's reference outputs.

Standard-library approximation of the `numdiff -r 1e-3` comparison performed by
Source/snowpack/tests/res1exp/run_res1exp.sh: lines starting with `creator` are
ignored in .haz/.sno, line 11 of .met and line 10 of .pro (version and run date)
are dropped, files are tokenised on `,`, space, tab and newline, and numeric tokens
are compared with relative tolerance 1e-3 (a pair also passes when both values are
exactly equal).  Non-numeric tokens must match exactly.

Usage: python3 snowpack_ref_compare.py <output_dir> <output_ref_dir> <basename>
"""
import bz2
import os
import re
import sys


def load(path, drop_line=None, drop_creator=False):
    opener = bz2.open if path.endswith('.bz2') else open
    with opener(path, 'rt', errors='replace') as f:
        lines = f.read().splitlines()
    if drop_line is not None and len(lines) >= drop_line:
        del lines[drop_line - 1]
    if drop_creator:
        lines = [ln for ln in lines if not ln.startswith('creator')]
    return lines


def tokens(lines):
    return [t for ln in lines for t in re.split(r'[,\s]+', ln) if t]


def compare(a, b, rel=1e-3):
    ta, tb = tokens(a), tokens(b)
    n_num = n_bad = n_text_bad = 0
    max_rel = 0.0
    for x, y in zip(ta, tb):
        try:
            fx, fy = float(x), float(y)
        except ValueError:
            if x != y:
                n_text_bad += 1
            continue
        n_num += 1
        if fx == fy:
            continue
        d = abs(fx - fy) / max(abs(fx), abs(fy))
        max_rel = max(max_rel, d)
        if d > rel:
            n_bad += 1
    return {'tokens_out': len(ta), 'tokens_ref': len(tb), 'numeric_compared': n_num,
            'numeric_over_tol': n_bad, 'text_mismatch': n_text_bad, 'max_rel_diff': max_rel}


def main():
    out, ref, base = sys.argv[1], sys.argv[2], sys.argv[3]
    specs = [('.haz', None, True), ('.sno', None, True), ('.met', 11, False), ('.pro', 10, False)]
    for ext, drop, creator in specs:
        o = os.path.join(out, base + ext)
        r = os.path.join(ref, base + ext)
        if not os.path.exists(r) and os.path.exists(r + '.bz2'):
            r = r + '.bz2'
        if not (os.path.exists(o) and os.path.exists(r)):
            print(ext, 'missing', os.path.exists(o), os.path.exists(r))
            continue
        res = compare(load(o, drop, creator), load(r, drop, creator))
        print(ext, res)


if __name__ == '__main__':
    main()
