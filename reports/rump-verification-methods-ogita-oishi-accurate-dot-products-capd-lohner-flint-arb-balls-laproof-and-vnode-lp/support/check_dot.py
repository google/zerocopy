#!/usr/bin/env python3
"""Drive dotprobe binaries on GenDot-style ill-conditioned dot products and check exactly.

Usage: python3 check_dot.py <binary> [<binary> ...]
Writes temporary input files under /tmp. Reports, per anticipated condition decade, the
maximum relative error of each kernel, computed exactly with fractions.Fraction.
"""
import os
import random
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from eft_dot import gen_dot, dot_exact  # noqa: E402


def main():
    bins = sys.argv[1:]
    rng = random.Random(7)
    n, per = 100, 10
    print("# n=%d samples_per_decade=%d; columns per binary: max relerr naive / dot2_fma / dot2_dekker" % (n, per))
    print("# decade " + "  ".join(os.path.basename(b) for b in bins))
    with tempfile.TemporaryDirectory(dir="/tmp") as td:
        for dec in (8, 16, 24, 30):
            worst = {b: [0.0, 0.0, 0.0] for b in bins}
            for k in range(per):
                x, y = gen_dot(n, 10.0 ** dec, rng)
                ex = dot_exact(x, y)
                path = os.path.join(td, "v.bin")
                with open(path, "wb") as f:
                    f.write(struct.pack("<q", n))
                    for a, b in zip(x, y):
                        f.write(struct.pack("<dd", a, b))
                for b in bins:
                    out = subprocess.run([b, "acc", path], capture_output=True, text=True, check=True).stdout.split()
                    for j, h in enumerate(out):
                        rel = float(abs(Fraction(float.fromhex(h)) - ex) / abs(ex))
                        worst[b][j] = max(worst[b][j], rel)
            print("%3d  " % dec + "  ".join("%.1e/%.1e/%.1e" % tuple(worst[b]) for b in bins))


if __name__ == "__main__":
    main()
