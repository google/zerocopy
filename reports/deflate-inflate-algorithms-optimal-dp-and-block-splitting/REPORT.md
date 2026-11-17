<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# DEFLATE/INFLATE Algorithms: Binary Trees, Optimal DP, and Huffman Bounds

## Summary

Optimal-parsing DEFLATE encoders and table-driven INFLATE decoders fail
along subtle algorithmic boundaries that bypass small unit tests: off-by-one
self-cycles in binary-tree match windows, invalid early-exit subtree splicing,
quadratic DP relaxation on long matches, tiny-input prior skew, suboptimal
Kraft debt rebalancing, and miscalculated canonical subtable sizes. We isolate
each mechanism with self-contained Rust and Python probes so implementers can
verify these invariants without trusting heuristics or unstated assumptions.

## Applicability

- LZ77 binary-tree match finders indexing a 32 KiB sliding window with
  distance bounds `32767` vs. `32768` (`BT_MAX_DIST`).
- Backward/forward Zopfli-style optimal-parsing dynamic programming (`OPT`
  arrays, `nice_len` early exits, suffix-matched RLE guards, and compact
  distance-symbol price tables).
- Length-limited canonical Huffman builders (Package-Merge vs. two-queue
  Huffman with bottom-up Kraft rebalancing, single-symbol `active_cl == 1`
  precodes, and multi-chunk `BTYPE=00` stored blocks).
- Fixed-point Jensen-Shannon divergence (JSD) block splitters (`Q8` `log2`
  tables) and canonical `inflate_table` root/subtable decoders under RFC 1951.

## Findings

### Binary-Tree Match-Finder Invariants

1. **`BT_MAX_DIST = 32767` Prevents Window-Wrap Self-Cycles:** When node links
   store `(pos - cand) & 0x7FFF` (indexing a `32768`-slot ring buffer), `pos`
   and `pos - 32768` alias the same slot `pos & 32767`. Allowing `dist == 32768`
   lets `pos` insert itself (`v = 1`) before zeroing the reused slot, turning
   `bt_child[0][0] = 1` into a self-loop until `max_depth` (`depth = 64`).
   Enforcing `BT_MAX_DIST = 32767` cleanly resets `bt_child[0] = [0, 0]` and
   keeps the next lookup at `depth = 1`.
2. **Splicing `cand`'s Children Preserves BST Order Only at `ml == 258`:**
   On a `nice_len` early exit at `ml < 258`, replacing `cand` with `pos` and
   splicing `cand`'s `<` and `>` children directly into `pending_lt`/`pending_gt`
   destroys `cand` and violates lexicographic ordering at byte `ml`. On a
   24-byte test fixture (`ml = 14`), evicting `cand` drops a subsequent identical
   query from `24` bytes down to `14` bytes. Zeroing both pending links at
   `ml < 258` (`Query match_len = 9`) preserves BST soundness at the cost of
   pruning deeper descendants; attaching `cand` on its comparison side at byte
   `ml` retains `24`-byte recall. Only when `ml == 258` (`MAX_MATCH`) are `pos`
   and `cand` identical across the full match bound, letting splice preserve both
   subtrees (`258` bytes recalled on both sides).
3. **`bt_head3` Requires a `cv != v` Distance-Shadowing Guard:** When probing a
   3-byte hash (`bt_head3`) before walking the 4-byte binary tree (`bt_head4`),
   accepting a 4-byte hit inside `bt_head3` without rejecting `cv == v` sets
   `best_len = 4` at a far distance (`d = 3000`, `10` extra bits). Because the
   BT walker only replaces `best_dist` on strict length improvement (`ml >
   best_len`), that stale hit shadows a closer 4-byte candidate in `bt_head4`
   (`d = 10`, `2` extra bits), wasting `8` extra bits per shadowed match.

### Optimal-Parsing DP Speed and Convergence

1. **Suffix Pruning (`OPT_NO_TRUNC`) and `!is_rle_interior` Acceleration:**
   Inside a `nice_len = 64` match on a `64 KiB` repetitive XML/RLE buffer,
   synthesizing suffix matches (`ml - k` down to `3`) forces backward/forward DP
   relaxation to test every truncated edge `(3..=rem_l)`, exploding DP edges to
   `7,100,043` (`5325 us`). Flagging suffix entries with `OPT_NO_TRUNC` (`0x8000`)
   restricts relaxation to exact length `rem_l`, cutting DP edges `36.32x` to
   `195,506` (`814 us`) with identical optimal terminal cost (`4888` bits).
   Adding the `!is_rle_interior` guard against indexing interior bytes of uniform
   runs reduces chain probes `6.69x` (`2514` to `376`, `786 us` combined).
2. **Pre-Encoded 5-Bit Distance Symbols Shrink Price Tables into L1d:** Storing
   `len_hi[259]` and `dist_sym_hi[32]` (`DpPrices`, `4376 B` = `4.27 KiB`) instead
   of a flat `dist_price[32768]` array (`64.0 KiB` as `u16`, `256.0 KiB` as
   `u64`) keeps DP prices inside L1d and shrinks each price-table rebuild from
   `32768` steps to `30` symbols (`1092x` fewer iterations). Packing `cost_q4`
   into the upper 32 bits (`<< 32`) with `dist - 1` (`0..32767`) in the low 32
   bits avoids carry into bit 32 across all lengths `3..=258` and distances.
3. **Pass-1 Unclamped Literal Priors Break Matches on Tiny and Prose Inputs:**
   Initializing Pass-1 literal costs from raw empirical byte counts (`from_raw`)
   underprices repeated literals on small buffers and English prose:
   - On `b"Deflate late"` (`12 B`), raw counts price 4 match bytes at `155` Q4
     units (`< 168` Q4 match cost), rejecting a valid match and emitting `14 B`
     (`106` static bits) instead of `11 B` (`86` bits).
   - On `[10, 10, 10, 10, 10, 55]` (`6 B`), raw priors yield `64` Q4 for four
     `10` bytes, producing `8 B` (`58` bits) instead of `5 B` (`38` bits).
   - Clamping Pass-1 inputs shorter than `48 B` to RFC 1951 static priors (`512`
     Q4 vs. `168` Q4) recovers both matches. Even on large prose, common letters
     make raw-byte trigrams (`176` Q4) cheaper than marginal `(len=3, d=128)`
     matches (`248` Q4), whereas post-LZ77 residual literals (`280` Q4) keep them.

### Huffman Construction, Kraft Rebalancing, and Block Accounting

1. **Bottom-Up Kraft Rebalancing Is Tight on Zipf but Trails Package-Merge on
   Skewed Caps:** Bottom-up Kraft rebalancing (`bl_count[b] -= 1; bl_count[b+1]
   += 2; bl_count[max] -= 1` while `kraft > 2^max`) hits exact Package-Merge
   cost on `Zipf-286` at `max_bits = 15` (`3,966,249` bits, `delta = 0`) because
   natural depths stay within `15`. However, on highly skewed distributions
   hitting the depth cap (`Fibonacci-25` at `max_bits = 15`: `514,968` vs.
   `514,209` bits, `+759` bits; `Fibonacci-12` at `max_bits = 7`: `1001` vs.
   `975` bits, `+26` bits / `+2.67%`; synthetic `max_bits = 5` caps: up to
   `+98` bits / `+7.95%`), bottom-up rebalancing pays measurable redundancy
   against $O(N \cdot L)$ Package-Merge.
2. **Single-Symbol Precode Trees Need a Symmetric Dummy Partner:** When a uniform
   block uses only one precode symbol (`active_cl == 1`, e.g., symbol `8` across
   all 256 literal lengths), assigning length `1` exclusively leaves Kraft
   capacity `1/2`. Pairing `sym ^ 1` (symbol `9`) with length `1` keeps both
   lengths positive and reaches exact `128/128` Kraft balance without corrupting
   RFC 1951 precode decoding.
3. **Exact `BTYPE=00` Stored-Block Accounting Must Track `first_pad` and Splits:**
   Emitting `raw_len > 65535` spans `chunks = 1 + (raw_len - 1) / 65535` stored
   headers. Only the initial chunk pays variable byte-alignment padding
   `first_pad = (8 - ((bit_offset + 3) & 7)) & 7`; subsequent chunks align
   cleanly (`32 + 5` bits = `40` bits per extra chunk). At `raw_len = 65536`,
   `bit_offset = 0` emits `524,368` bits (`80` header/pad bits) while
   `bit_offset = 3` emits `524,365` bits (`77` header/pad bits).

### Block Splitting, Canonical Table Bounds, and Inflate Safety

1. **`Q8` Fixed-Point `log2` Accurately Tracks Entropy Split Gains:** Precomputing
   `round(256 * log2(x))` across `65536` entries computes Jensen-Shannon
   divergence gains within `5e-6` relative error (`24361.816` vs. `24361.685`
   exact float64 bits on a `16 KB + 16 KB` text/random split) using pure
   integer arithmetic, while stored clamping detects when `16 KB` dynamic
   headers exceed stored `BTYPE=00` size (`128,035 < 129,811.5` bits).
2. **Canonical Table Footprint (`enough.c`) Hinges on Prefix Alignment:** Exhaustive
   canonical prefix DP confirms Mark Adler's worst-case root + 2nd-level entry
   counts: `128` (`19/7/7`), `852` (`286/9/15`), `592` (`30/9/15`), `594`
   (`32/9/15`), `2340` (`286/11/15`), and `2342` (`288/11/15`). Crucially, the
   `30/9/15 = 592` maximum arises not from packing two deep slots, which canonical
   sorting forbids, but from leaving `8` open depth-9 slots via `[2, 2, 2, 3, 4,
   5, 6] + [10]*13 + [11]*5 + [12, 13, 14, 15, 15]` (`512 + 6*2 + 4 + 64 = 592`).
3. **Exhaustive Distance Coding, Bitreader Refill, RFC 1951 Validation, and `>5x`
   Expansion:**
   - All `32768` RFC 1951 distances (`1..=32768`) round-trip identically through
     branchless MSB/leading-zero symbol indexing.
   - Branchless 64-bit LSB bitreader refill (`new_buf = old | (word << bitcnt)`,
     `advance = 7 - (bitcnt >> 3)`, `new_cnt = bitcnt | 56`) preserves every
     valid starting state `bitcnt in 0..=63` without overflow (`new_cnt in
     56..=63`).
   - RFC 1951 decoding must reject incomplete (`left > 0`) and oversubscribed
     (`left < 0`) tables—including `288`-code incomplete trees (`left = 224`)
     and single-symbol literal trees (`left = 1`)—while explicitly permitting
     single-code distance trees (`[1] + [0]*29`) and empty distance trees per
     Section 3.2.7. Meanwhile, repetitive inputs routinely exceed `275x`
     decompression expansion (`63,600 B -> 231 B`), breaking fixed `5x`
     single-shot buffer heuristics.

## Boundaries

- Probe timings (`us` counts) reflect relative single-threaded measurements of
  isolated kernels (`Probe 4`) rather than whole-corpus throughput; end-to-end
  Silesia benchmarks are separated into the dedicated compression benchmark
  package.
- Package-Merge (`O(N * L)`) cost deltas depend on input distribution skew
  hitting `max_bits` (`7` for precodes, `15` for litlen/dist). Unclamped
  natural frequencies typically incur zero gap.
- Branchless 64-bit refill assumes at least `8` readable bytes in the source
  slice (either in-buffer fast loop slack or an explicit safe tail loop).

## Evidence

| Probe | Verified Result | Source Artifact |
| :--- | :--- | :--- |
| `Probe 1` (`BT_MAX_DIST`) | `32768` self-loop (`depth=64`) vs. `32767` (`depth=1`) | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 2` (`ml==258` splice) | Evict loses `10 B` at `ml=14`; splice exact at `258` | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 3` (`bt_head3`) | `cv != v` stops `d=3000` shadowing `d=10` (`8` bits saved) | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 4` (`OPT_NO_TRUNC`) | `36.32x` fewer DP edges; `6.69x` fewer chain steps | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 5` (`DpPrices`) | `4376 B` vs. `64/256 KiB`; `12B`/`6B` trap `14->11 B`, `8->5 B` | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 6` (Kraft & `cl=1`) | `Fib(30)` tight at `15/14`; `precode[8]=1, [9]=1` | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 7` (`BTYPE=00`) | `48/48` pairs exact (`65536 B`: `524368` vs. `524365` bits) | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `Probe 8` (`dist`, refill) | `32768/32768` dists & `64/64` `bitcnt` states exact | [deflate_bt_dp_probe.rs](support/deflate_bt_dp_probe.rs) |
| `enough` DP & Package-Merge | Exact `128,852,592,594,2340,2342`; `+759` bits `Fib-25` | [huffman_and_block_split_probe.py](support/huffman_and_block_split_probe.py) |
| `Q8` JSD, RFC 1951 & RLE | `5e-6` JSD err; `288` checks; `275.32x` expansion | [huffman_and_block_split_probe.py](support/huffman_and_block_split_probe.py) |

## Revalidation

Run both self-contained probes inside `support/` and confirm `exit 0`:

```bash
rustc --edition 2021 -O support/deflate_bt_dp_probe.rs -o /tmp/deflate_bt_dp_probe
/tmp/deflate_bt_dp_probe
python3 support/huffman_and_block_split_probe.py
```
