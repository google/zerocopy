#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical probe for DEFLATE/INFLATE Huffman table bounds, Package-Merge vs.
Kraft rebalancing, Q8 Jensen-Shannon block splitting, and adversarial decoding.

Run:
  python3 huffman_and_block_split_probe.py
"""

from __future__ import annotations

from functools import lru_cache
import json
import math
import random
from typing import List, Tuple
import zlib


# ---------------------------------------------------------------------------
# 1. Exact Mark Adler (`zlib/examples/enough.c`) canonical table-size DP
# ---------------------------------------------------------------------------

def max_inflate_table_entries(syms: int, root: int, max_bits: int = 15) -> int:
    """Compute exact worst-case primary + 2nd-level canonical Huffman table size.

    Follows the canonical prefix-tree dynamic program of `zlib/examples/enough.c`:
    codes are assigned in strictly non-decreasing length order `len = 1..max_bits`,
    filling lower-numbered prefixes at level `root` before descending into deeper
    2nd-level subtables aligned at the right end of the prefix space.
    """
    @lru_cache(maxsize=None)
    def best_extra(syms_rem: int, left: int, length: int) -> int:
        if syms_rem == left:
            return 0
        if syms_rem < left or left <= 0:
            return -10**9
        rem_depth = max_bits - length
        if rem_depth == 0:
            return -10**9

        max_per_node = 1 << rem_depth
        best = -10**9
        lo_put = max(0, 2 * left - syms_rem)
        hi_put = min(
            left - 1,
            syms_rem,
            (left * max_per_node - syms_rem) // (max_per_node - 1),
        )
        if lo_put > hi_put:
            return -10**9

        for put in range(lo_put, hi_put + 1):
            descend = left - put
            nxt_syms = syms_rem - put
            nxt_left = descend * 2
            sub = best_extra(nxt_syms, nxt_left, length + 1)
            if sub < 0:
                continue
            if length < root:
                add = 0
            elif length == root:
                add = 2 * descend
            else:
                d = length - root
                subtables_widened = (descend + (1 << d) - 1) >> d
                add = subtables_widened << d
            cand = add + sub
            if cand > best:
                best = cand
        return best

    extra = best_extra(syms, 2, 1)
    if extra < 0:
        raise ValueError(f"Unreachable canonical Huffman parameters: syms={syms}, root={root}, max_bits={max_bits}")
    return (1 << root) + extra


def verify_canonical_inflate_table_footprint_directly(lengths: List[int], root: int) -> int:
    """Count exact root + 2nd-level canonical Huffman entries by bucket scan."""
    max_len = max(lengths)
    bl_count = [0] * (max_len + 1)
    for l in lengths:
        if l > 0:
            bl_count[l] += 1
    if max_len <= root:
        return 1 << root
    bucket_max = [0] * (1 << root)
    pos = 0
    shift = max_len - root
    for length in range(1, max_len + 1):
        w = 1 << (max_len - length)
        for _ in range(bl_count[length]):
            if length > root:
                b = pos >> shift
                if length > bucket_max[b]:
                    bucket_max[b] = length
            pos += w
    assert pos == (1 << max_len)
    return (1 << root) + sum(1 << (m - root) for m in bucket_max if m > root)


# ---------------------------------------------------------------------------
# 2. Exact Package-Merge (Larmore-Hirschberg) vs. Moffat-Katajainen Kraft DP
# ---------------------------------------------------------------------------

def package_merge_code_lengths(freqs: List[int], max_bits: int) -> List[int]:
    """Compute exact minimum-redundancy length-limited Huffman code lengths."""
    active = [(f, i) for i, f in enumerate(freqs) if f > 0]
    lens = [0] * len(freqs)
    if not active:
        return lens
    if len(active) == 1:
        lens[active[0][1]] = 1
        return lens

    # Each item is (total_weight, [sym_indices])
    active.sort()
    singletons = [(f, [i]) for f, i in active]
    prev_list: List[Tuple[int, List[int]]] = []
    for _depth in range(max_bits):
        merged = list(singletons)
        for idx in range(0, len(prev_list) - 1, 2):
            w1, s1 = prev_list[idx]
            w2, s2 = prev_list[idx + 1]
            merged.append((w1 + w2, s1 + s2))
        merged.sort(key=lambda x: (x[0], len(x[1])))
        prev_list = merged

    need = 2 * len(active) - 2
    for _w, syms in prev_list[:need]:
        for s in syms:
            lens[s] += 1
    assert sum(1 << (max_bits - lens[i]) for _, i in active) == (1 << max_bits)
    return lens


def kraft_rebalanced_code_lengths(freqs: List[int], max_bits: int) -> List[int]:
    """Two-queue unbounded Huffman tree + bottom-up Kraft debt rebalancing."""
    active = sorted((f, i) for i, f in enumerate(freqs) if f > 0)
    lens = [0] * len(freqs)
    n = len(active)
    if n == 0:
        return lens
    if n == 1:
        lens[active[0][1]] = 1
        return lens

    parent = [0] * (2 * n)
    internal_w: List[int] = []
    leaf_idx = 0
    int_head = 0

    def next_min() -> Tuple[int, int]:
        nonlocal leaf_idx, int_head
        if leaf_idx < n and (int_head >= len(internal_w) or active[leaf_idx][0] <= internal_w[int_head]):
            w = active[leaf_idx][0]
            nid = leaf_idx
            leaf_idx += 1
            return w, nid
        w = internal_w[int_head]
        nid = n + int_head
        int_head += 1
        return w, nid

    for step in range(n - 1):
        w1, id1 = next_min()
        w2, id2 = next_min()
        internal_w.append(w1 + w2)
        parent[id1] = n + step
        parent[id2] = n + step

    root = 2 * n - 2
    depth = [0] * (2 * n - 1)
    bl_count = [0] * (max_bits + 1)
    for nid in range(root - 1, -1, -1):
        d = depth[parent[nid]] + 1
        depth[nid] = d
        if nid < n:
            bl_count[min(d, max_bits)] += 1

    kraft = sum(bl_count[b] << (max_bits - b) for b in range(1, max_bits + 1))
    target = 1 << max_bits
    while kraft > target:
        bits = max_bits - 1
        while bl_count[bits] == 0:
            bits -= 1
        bl_count[bits] -= 1
        bl_count[bits + 1] += 2
        bl_count[max_bits] -= 1
        kraft -= 1

    rank = n
    for bits in range(1, max_bits + 1):
        for _ in range(bl_count[bits]):
            rank -= 1
            lens[active[rank][1]] = bits
    return lens


# ---------------------------------------------------------------------------
# 3. Q8 Fixed-Point Shannon Entropy & Jensen-Shannon Divergence Splitters
# ---------------------------------------------------------------------------

def build_q8_log2_lut() -> List[int]:
    """Build 65536-entry Q8 fixed-point `round(256 * log2(x))` table (`lut[0] = 0`)."""
    lut = [0] * 65536
    for i in range(1, 65536):
        lut[i] = int(round(256.0 * math.log2(i)))
    return lut


def shannon_cost_bits_exact(counts: List[int]) -> float:
    total = sum(counts)
    if total == 0:
        return 0.0
    lt = math.log2(total)
    return sum(c * (lt - math.log2(c)) for c in counts if c > 0)


def shannon_cost_bits_q8(counts: List[int], lut: List[int]) -> float:
    total = sum(counts)
    if total == 0:
        return 0.0
    assert total < len(lut)
    num_q8 = total * lut[total] - sum(c * lut[c] for c in counts if c > 0)
    return num_q8 / 256.0


def jsd_split_gain_bits(left: List[int], right: List[int], lut: List[int] | None = None) -> float:
    merged = [a + b for a, b in zip(left, right)]
    if lut is None:
        return shannon_cost_bits_exact(merged) - (
            shannon_cost_bits_exact(left) + shannon_cost_bits_exact(right)
        )
    return shannon_cost_bits_q8(merged, lut) - (
        shannon_cost_bits_q8(left, lut) + shannon_cost_bits_q8(right, lut)
    )


# ---------------------------------------------------------------------------
# 4. Adversarial Canonical Table Validation (RFC 1951 Section 3.2.2 & 3.2.7)
# ---------------------------------------------------------------------------

def validate_rfc1951_code_lengths(lengths: List[int], allow_single_code_dist: bool = False) -> Tuple[bool, str]:
    max_len = max(lengths) if lengths else 0
    if max_len == 0:
        # Empty distance table (`left = 1 << max_bits`) is legal in RFC 1951 Section 3.2.7
        # when a dynamic block uses zero matches (only literals + EOB).
        return (True, "empty_ok") if allow_single_code_dist else (False, "empty_rejected")
    bl_count = [0] * (max_len + 1)
    for l in lengths:
        if l > 0:
            bl_count[l] += 1
    left = 1
    for bits in range(1, max_len + 1):
        left <<= 1
        left -= bl_count[bits]
        if left < 0:
            return False, f"oversubscribed_at_bit_{bits}"
    if left > 0:
        # RFC 1951 Section 3.2.7 permits a single-symbol distance code (`bl_count[1] == 1`)
        # with one unused code; all other incomplete tables must be rejected.
        if allow_single_code_dist and sum(1 for l in lengths if l > 0) == 1 and lengths.count(1) == 1:
            return True, "single_code_dist_ok"
        return False, f"incomplete_left_{left}"
    return True, "complete_ok"


def main() -> None:
    # Check 1: Exact Mark Adler `enough.c` canonical table footprints
    enough_targets = {
        (19, 7, 7): 128,
        (286, 9, 15): 852,
        (30, 9, 15): 592,
        (32, 9, 15): 594,
        (286, 11, 15): 2340,
        (288, 11, 15): 2342,
    }
    enough_results = {}
    for (syms, root, max_bits), expected in enough_targets.items():
        got = max_inflate_table_entries(syms, root, max_bits)
        assert got == expected, f"Mismatch for {(syms, root, max_bits)}: got {got}, want {expected}"
        enough_results[f"{syms}/{root}/{max_bits}"] = got

    # Cross-check concrete 30/9 tree achieving 592 = 512 + (6 * 2 + 4 + 64)
    # Spreading into 8 rightmost depth-9 slots beats two deep packed slots.
    witness_30_9 = (
        [2, 2, 2, 3, 4, 5, 6]
        + [10] * 13
        + [11] * 5
        + [12, 13, 14, 15, 15]
    )
    assert len(witness_30_9) == 30
    assert verify_canonical_inflate_table_footprint_directly(witness_30_9, 9) == 592

    # Check 2: Package-Merge vs. Kraft Rebalancing gap
    zipf_286 = [max(1, round(100_000 / (k + 1))) for k in range(286)]
    fib_25 = [1, 1]
    while len(fib_25) < 25:
        fib_25.append(fib_25[-1] + fib_25[-2])
    fib_12 = fib_25[:12]

    pm_zipf = package_merge_code_lengths(zipf_286, 15)
    kr_zipf = kraft_rebalanced_code_lengths(zipf_286, 15)
    cost_pm_zipf = sum(f * l for f, l in zip(zipf_286, pm_zipf))
    cost_kr_zipf = sum(f * l for f, l in zip(zipf_286, kr_zipf))

    pm_fib25 = package_merge_code_lengths(fib_25, 15)
    kr_fib25 = kraft_rebalanced_code_lengths(fib_25, 15)
    cost_pm_f25 = sum(f * l for f, l in zip(fib_25, pm_fib25))
    cost_kr_f25 = sum(f * l for f, l in zip(fib_25, kr_fib25))

    pm_fib12 = package_merge_code_lengths(fib_12, 7)
    kr_fib12 = kraft_rebalanced_code_lengths(fib_12, 7)
    cost_pm_f12 = sum(f * l for f, l in zip(fib_12, pm_fib12))
    cost_kr_f12 = sum(f * l for f, l in zip(fib_12, kr_fib12))

    # Search deterministically for minimal bit-length gap at max_bits=5 across small skewed vectors
    rng = random.Random(2026)
    max_rel_gap = 0.0
    worst_gap_case = None
    for _ in range(500):
        vec = [rng.randint(1, 5) for _ in range(4)] + [rng.randint(20, 200) for _ in range(5)]
        pl = package_merge_code_lengths(vec, 5)
        kl = kraft_rebalanced_code_lengths(vec, 5)
        cp = sum(f * l for f, l in zip(vec, pl))
        ck = sum(f * l for f, l in zip(vec, kl))
        assert cp <= ck
        gap = (ck - cp) / cp
        if gap > max_rel_gap:
            max_rel_gap = gap
            worst_gap_case = (vec, cp, ck, pl, kl)

    # Check 3: Q8 JSD block-splitting precision & stored fallback threshold
    lut = build_q8_log2_lut()
    rng2 = random.Random(42)
    text_block = [rng2.randint(97, 122) for _ in range(16000)]
    rand_block = [rng2.randint(0, 255) for _ in range(16000)]

    c_left = [0] * 256
    for b in text_block:
        c_left[b] += 1
    c_right = [0] * 256
    for b in rand_block:
        c_right[b] += 1

    exact_jsd = jsd_split_gain_bits(c_left, c_right, None)
    q8_jsd = jsd_split_gain_bits(c_left, c_right, lut)
    jsd_rel_err = abs(q8_jsd - exact_jsd) / exact_jsd

    # Stored fallback check: high-entropy random 32 KiB block -> dynamic Huffman overhead > stored 5B/chunk
    dyn_est_bits = shannon_cost_bits_exact(c_right) + 3 + 250 * 8  # rough tree header overhead
    stored_bits = 3 + 32 + len(rand_block) * 8

    # Check 4: Adversarial Huffman lengths (288-code oversubscribed / incomplete / single-code dist)
    ok_288_inc, tag_288_inc = validate_rfc1951_code_lengths([9] * 288, allow_single_code_dist=False)
    # `[9] * 288` sums 288 / 512 < 1 -> incomplete!
    ok_288_over, tag_288_over = validate_rfc1951_code_lengths([8] * 256 + [7] * 32, allow_single_code_dist=False)
    ok_single_dist, tag_single_dist = validate_rfc1951_code_lengths([1] + [0] * 29, allow_single_code_dist=True)
    ok_single_lit, tag_single_lit = validate_rfc1951_code_lengths([1] + [0] * 285, allow_single_code_dist=False)
    assert not ok_288_inc and not ok_288_over and ok_single_dist and not ok_single_lit

    # Check 5: High-compression output growth (exceeding 5x single-shot inflate heuristics)
    raw_64k_rep = (b"0" * 36 + b":<atom id=\"a1\"/>\n") * 1200
    comp_rep = zlib.compress(raw_64k_rep, level=6)[2:-4]
    expansion_ratio = len(raw_64k_rep) / len(comp_rep)
    assert expansion_ratio > 50.0

    out = {
        "status": "PASS",
        "enough_dp_entries": enough_results,
        "witness_30_9_footprint": verify_canonical_inflate_table_footprint_directly(witness_30_9, 9),
        "package_merge_vs_kraft": {
            "zipf_286_max15": {"pm_bits": cost_pm_zipf, "kraft_bits": cost_kr_zipf, "delta": cost_kr_zipf - cost_pm_zipf},
            "fib_25_max15": {"pm_bits": cost_pm_f25, "kraft_bits": cost_kr_f25, "delta": cost_kr_f25 - cost_pm_f25},
            "fib_12_max7": {"pm_bits": cost_pm_f12, "kraft_bits": cost_kr_f12, "delta": cost_kr_f12 - cost_pm_f12},
            "max5_skew_worst_delta_bits": (worst_gap_case[2] - worst_gap_case[1]) if worst_gap_case else 0,
            "max5_skew_rel_gap": round(max_rel_gap, 6),
        },
        "q8_jsd_split": {
            "text_vs_random_exact_bits": round(exact_jsd, 3),
            "text_vs_random_q8_bits": round(q8_jsd, 3),
            "rel_err": round(jsd_rel_err, 6),
            "random_16k_dyn_est_bits": round(dyn_est_bits, 1),
            "random_16k_stored_bits": stored_bits,
            "stored_wins": stored_bits < dyn_est_bits,
        },
        "rfc1951_table_validation": {
            "incomplete_288": tag_288_inc,
            "oversubscribed_288": tag_288_over,
            "single_code_dist": tag_single_dist,
            "single_code_lit_rejected": tag_single_lit,
        },
        "inflate_output_growth": {
            "raw_bytes": len(raw_64k_rep),
            "compressed_bytes": len(comp_rep),
            "expansion_ratio": round(expansion_ratio, 2),
        },
    }
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
