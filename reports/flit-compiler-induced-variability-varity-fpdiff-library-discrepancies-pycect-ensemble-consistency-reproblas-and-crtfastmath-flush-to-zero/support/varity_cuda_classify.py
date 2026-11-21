"""Classify the 500 preserved CUDA inconsistency examples shipped with Varity.

Input: cuda_examples/outputs.txt from LLNL/Varity at the pinned revision.
These cases were *selected by the Varity authors because they are inconsistent*;
the counts below describe that curated set, not the frequency of inconsistency in
random programs.

Configuration labels (from cuda_examples/README.md): O3_nostrict = -O3 -use_fast_math,
O0_nofma = -O0 --fmad=false. O3_strict is not defined in that README.

Run: python3 varity_cuda_classify.py outputs.txt
"""
import collections
import math
import sys

FLT_MIN = 1.1754943508222875e-38  # smallest normal binary32


def parse(path):
    cases, cur = [], None
    for line in open(path):
        line = line.strip()
        if line.startswith("Case:"):
            cur = {"id": int(line.split()[1]), "vals": {}}
            cases.append(cur)
        elif cur is not None and ":" in line and not line.startswith(("File:", "Input:")):
            k, v = line.split(":", 1)
            cur["vals"][k.strip()] = v.strip()
    return cases


def num(s):
    try:
        return float(s)
    except ValueError:
        return None


def kind(v):
    f = num(v)
    if f is None:
        return "other"
    if math.isnan(f):
        return "nan"
    if math.isinf(f):
        return "inf"
    if f == 0.0:
        return "zero"
    if abs(f) < FLT_MIN:
        return "subnormal32"
    return "normal"


def main(path):
    cases = parse(path)
    labels = collections.Counter(k for c in cases for k in c["vals"])
    print(f"cases: {len(cases)}; configuration labels: {dict(labels)}")
    strict = ["O0", "O1", "O2", "O3"]
    cat = collections.Counter()
    fast_only = 0
    fma_only = 0
    ftz_like = 0
    nan_vs_num = 0
    for c in cases:
        v = c["vals"]
        s_vals = {v[k] for k in strict if k in v}
        fast = v.get("O3_nostrict")
        nofma = v.get("O0_nofma")
        strict_consistent = len(s_vals) == 1
        sv = next(iter(s_vals)) if strict_consistent else None
        if strict_consistent and nofma == sv and fast is not None and fast != sv:
            fast_only += 1
            ks, kf = kind(sv), kind(fast)
            if ks == "subnormal32" and kf == "zero":
                ftz_like += 1
                cat["fast-math differs: subnormal -> 0 (flush-to-zero pattern)"] += 1
            elif "nan" in (ks, kf) or "inf" in (ks, kf):
                nan_vs_num += 1
                cat[f"fast-math differs: {ks} -> {kf}"] += 1
            else:
                cat[f"fast-math differs: {ks} -> {kf}"] += 1
        elif strict_consistent and nofma is not None and nofma != sv:
            fma_only += 1
            cat[f"--fmad=false differs from O0..O3 ({kind(nofma)} vs {kind(sv)})"] += 1
        elif not strict_consistent:
            cat["O0..O3 disagree among themselves"] += 1
        else:
            cat["other pattern"] += 1
    for k, n in cat.most_common():
        print(f"  {n:4d}  {k}")
    eq_fast = sum(1 for c in cases if c["vals"].get("O3_strict") == c["vals"].get("O3_nostrict"))
    eq_o3 = sum(1 for c in cases if c["vals"].get("O3_strict") == c["vals"].get("O3"))
    print(f"O3_strict equals O3_nostrict in {eq_fast} cases and equals O3 in {eq_o3} cases")
    print(f"summary: fast-math-only differences {fast_only}; of which subnormal->0 {ftz_like}; "
          f"FMA-contraction-only differences {fma_only}")


if __name__ == "__main__":
    main(sys.argv[1])
