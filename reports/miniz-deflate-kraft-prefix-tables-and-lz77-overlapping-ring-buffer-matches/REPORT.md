# Two-Level Kraft Prefix Tables, Degenerate Huffman Completeness, and Self-Overlapping LZ77 Circular Ring Copies across RFC 1951, miniz_oxide, zlib, and Anneal

## Summary

Verifying production RFC 1951 DEFLATE decompressors—**`Frommi/miniz_oxide`** (`b28c237471f63efebe152bddd962dc57bbb531eb`, v`0.9.1`, `#![forbid(unsafe_code)]`) and **`madler/zlib`** (`99623ef7097352da7993ba614161fd6a311e046e`, v`1.4`, and `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf`, `v1.3.1`)—requires invariants absent from stateless byte-slice parsers:

1. **Kraft-Coupled Two-Level Huffman Tables and `0i16` Sentinel Non-Collision (`miniz_oxide/src/inflate/core.rs:L47–143, L673–747, L884–1057`; `inftrees.c:L115–311`)**:
   - `miniz_oxide` pairs a 10-bit root table (`look_up: [i16; 1024]`) with a negative-offset binary trie (`tree: [i16; 576]`). Across bit lengths $k \in \{1..15\}$, `init_tree` maintains `total` and `left` under the exact invariant $\text{total}_k + 2 \cdot \text{left}_k = 2^{k+1}$, equating `miniz_oxide`'s `total == 65_536` (`L972`) with `zlib`'s `left == 0` (`inftrees.c:L146`). Both reject incomplete codes when `bt == HUFFLEN_TABLE` (`CODES`) or `max_code_len > 1`, while admitting `max_code_len <= 1` for literal/length and distance tables via `INVALID_CODE = (1 << 9) | 286` (`op = 64` in `zlib`).
   - Because `table.tree` is zero-filled (`L913`), stores literal `0x00` (`symbol_index == 0`) as `0i16` (`L1040`), and is indexed with panicking `[]` in `decode_huffman_code` (`L685`), both halves of Kraft (`left >= 0` + `total == 65_536` for `max_code_len > 1`) are load-bearing: exact dynamic programming bounds `table.tree` occupancy to **540 of 576 slots** (536 for `<= 286` dynamic symbols) and ensures every sibling slot below depth 10 is populated so unassigned bits never misdecode as `0x00`. By contrast, `zlib` builds flat multi-bit sub-tables bounded by `examples/enough.c` (`ENOUGH_LENS = 852`, `ENOUGH_DISTS = 592`).
2. **Self-Overlapping LZ77 Ring Copies (`core.rs:L1088–1224, L1353–1371`)**:
   - Matches with `1 <= dist < match_len` read bytes written earlier in the same copy. To hoist bounds checks safely under `#![forbid(unsafe_code)]`, `apply_match` (`L1180`) projects `&mut [u8]` to `&[Cell<u8>]` (`Cell::from_mut(...).as_slice_of_cells()`). All five `apply_match`/`transfer` arms refine $W_{\text{final}}[(\text{pos}+k)\bmod N] = W_0[(\text{pos}-\text{dist}+(k\bmod\text{dist}))\bmod N]$ under the sharp condition $1 \le \text{dist} \le N$ (`core.rs:L1355`).

Both subsystems mechanize cleanly in Pass-1 3-axiom Lean `v4.34.1` (`Anneal.Codec.PrefixLzRing`) with zero `sorry`, zero `._unsafe_rec`, and axiom footprint `[propext]`.

## Applicability

1. **`Frommi/miniz_oxide` v`0.9.1`** (`b28c237471f63efebe152bddd962dc57bbb531eb`): `miniz_oxide/Cargo.toml` (including `rustc-dep-of-std`), `src/lib.rs` (`#![forbid(unsafe_code)]`), `src/inflate/core.rs`, and `src/inflate/output_buffer.rs`, across power-of-2 wrapping (`out_buf_size_mask = 2^w - 1`) and non-wrapping (`usize::MAX`) output buffers on 32/64-bit targets.
2. **`madler/zlib` v`1.4` (`99623ef7097352da7993ba614161fd6a311e046e`) and `v1.3.1` (`51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf`)**: `inftrees.{h,c}`, `inffast.c`, and `examples/enough.c`. All `inflate_table` Kraft checks, `MAXBITS = 15`, and `ENOUGH_LENS = 852` / `ENOUGH_DISTS = 592` constants are shared identically across `v1.3.1` and `1.4`.
3. **Specifications & Mechanizations**: RFC 1951 (`10.17487/RFC1951`, §§3.2.2, 3.2.5–3.2.7), Huffman (`10.1109/JRPROC.1952.273898`), McMillan (`10.1109/TIT.1956.1056818`), Ziv & Lempel (`10.1109/TIT.1977.1055714`), Blanchette (`10.1007/s10817-009-9116-y`), and Senjak & Hofmann (`10.48550/arXiv.1609.01220`).
4. **Anneal & Lean `v4.34.1`**: `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) and `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`): `trusted/lean/foundation-lock.json` (51 `Init.*` modules, `{propext, Quot.sound, Classical.choice}`), `trusted/audit/TrustedBoundary.lean` (`L442–596`), `trusted/lean/Trusted/MirSemantics.lean` (`L1646–1706`), and `theory/Anneal/PureLift/SpatialPin.lean` (`L69–195`).

**Corpus relationship:** Companion reports `everparse-lowparse-strong-prefix-clens-and-nonmalleable-zero-copy-codecs` and `refinedrust-lithium-place-types-and-laid-out-spatial-nodes` cover stateless byte-prefix parsers and disjoint spatial places; this report covers bit-reversed Kraft prefix tables, degenerate 0/1-symbol DEFLATE trees, and overlapping `Cell` ring copies.

## Findings

### 1. Canonical Prefix-Code Kraft Algebra, Dual Accumulator Invariant, and Degenerate `max_code_len <= 1` Tables

Basis: normative (RFC 1951 §§3.2.2, 3.2.7; McMillan 1956 `10.1109/TIT.1956.1056818`) + source (`miniz_oxide@b28c2374`: `core.rs:L884–999, L1650–1694`; `zlib@99623ef7`: `inftrees.c:L115–157`) + execution (`Probe 1`, `Anneal.Codec.PrefixLzRing`)

RFC 1951 §3.2.2 defines canonical Huffman codes from per-symbol bit lengths $\ell_s \in \{0..15\}$ ($\ell_s = 0$ unused), assigning consecutive integers within each length and transmitting bits LSB-first. With $c_k = |\{s \mid \ell_s = k\}|$ ($1 \le k \le 15$), Kraft–McMillan states that a prefix-free binary code exists iff $\sum_{k=1}^{15} c_k 2^{-k} \le 1$ and is complete iff $\sum_{k=1}^{15} c_k 2^{-k} = 1$. In `miniz_oxide`'s `init_tree` (`core.rs:L932–958`), `total` and `left` evolve together from $(\text{total}_0, \text{left}_0) = (0, 1)$:

```rust
for (i, (&ts, next)) in total_symbols.iter().zip(next_code[1..].iter_mut()).enumerate().skip(1) {
    if ts > 0 { max_code_len = i as u32; }
    total += u32::from(ts); total <<= 1; *next = total;
    left <<= 1; left -= i32::from(ts);
    if left < 0 { return Some(Action::Jump(BadTotalSymbols)); }
}
```

1. **Shifted `next_code[17]` Indexing (`core.rs:L898, L938–950`)**: Zipping `next_code[1..]` *before* `.enumerate().skip(1)` pairs $i = 0$ with `next_code[1]` (left `0`) and writes iteration $i \in \{1..15\}$ into **`next_code[i + 1]`**, yielding $\text{next\_code}[k] = \sum_{j=1}^{k-1} c_j 2^{k-j}$ as required by RFC 1951 §3.2.2.
2. **Exact Dual Coupling**: Inducting on $k \in \{0..15\}$ (`kraft_dual_step_invariant` in Section 5):
   $$\text{total}_k = \sum_{j=1}^{k} c_j 2^{k+1-j}, \qquad \text{left}_k = 2^k - \sum_{j=1}^{k} c_j 2^{k-j}, \qquad \text{total}_k + 2 \cdot \text{left}_k = 2^{k+1}.$$
   At $k = 15$, $\text{total}_{15} + 2 \cdot \text{left}_{15} = 65\,536$: under $\text{left}_k \ge 0$, `miniz_oxide`'s `total != 65_536` (`L972`) and `zlib`'s `left > 0` (`inftrees.c:L146`) are identical.
3. **Degenerate `max_code_len <= 1` Admission and `INVALID_CODE` (`core.rs:L899–914, L960–974, L1302–1340`; `inftrees.c:L126–148, L300–305`)**:
   - `HUFFLEN_TABLE` / `CODES` (`bt == 2`) must always be complete (`total == 65_536`).
   - `LITLEN_TABLE` (`bt == 0`, dynamic `<= 286`, static `288`) and `DIST_TABLE` (`bt == 1`, dynamic `<= 30`, static `32`, `L1668`) admit incomplete histograms iff `max_code_len <= 1` (0 active distance symbols, or 1 active symbol with a 1-bit code `0`, leaving bit `1` unassigned).
   - `zlib` marks unassigned entries with `op = 64`. `miniz_oxide` pre-fills `look_up` with `INVALID_CODE = (1 << 9) | 286` (`798`: `code_len = 1, symbol = 286`), rejecting bogus inputs at `l.counter > 285` (`L1302, L1861`) or `symbol > 29` (`L1337, L1902`) with zero extra branch in `lookup`. Because `HUFFLEN_TABLE` is complete, all 1,024 `look_up` slots are overwritten for `bt == 2`.
   - **Comment vs. Spec Discrepancy (`core.rs:L908–914`)**: `L908` skips `table.tree.fill(0)` on `HUFFLEN_TABLE` claiming *"these codes can't be longer than 3 bits"*. Per RFC 1951 §3.2.7 (`L1681`: `read_bits(..., 3, ...)`), the 3-bit fields encode code *lengths* in **`0..=7` bits** (not `0..=3`); however, since $7 \le \text{FAST\_LOOKUP\_BITS} = 10$, `code_size <= 10` (`L1001`) still never touches `table.tree`, keeping the optimization sound.

---

### 2. Two-Level Table Topologies, Secondary Binary-Trie Capacity (`540 < 576`), and `0i16` Sentinel Non-Collision

Basis: source (`miniz_oxide@b28c2374`: `core.rs:L47–143, L673–747, L976–1042`; `zlib@99623ef7`: `inftrees.h:L24–58`, `inftrees.c:L204–296`, `examples/enough.c:L261–447`) + execution (`Probe 1`) + derived

| Dimension | `madler/zlib` (`inftrees.c` + `inffast.c`) | `Frommi/miniz_oxide` (`inflate/core.rs`) |
| :--- | :--- | :--- |
| **Root table** | `root = min(max, max(min, req))`, `req = 9` (`LENS`), `6` (`DISTS`) (`inftrees.c:L122–138, L340, L348`). | Fixed `FAST_LOOKUP_BITS = 10` (`1024` `i16`s) for all 3 tables (`core.rs:L134–136`). |
| **Secondary resolution** | 1-hop flat sub-table of size $2^{\text{curr}}$ (`curr = max_sub_len - root`), `code` = 4B (`inftrees.c:L265–295`). | Explicit binary trie `tree: [i16; 576]`; steps 1 bit/iter (`code_len = 10..15`) via `(!symbol + bit) as usize` (`L84–99`). |
| **Exact worst-case bound** | `enough(286,9,15) = 852` (`854` for 288); `enough(30,6,15) = 592` (`594` for 32) (`inftrees.h:L50–57`). | **540** of `576` `tree` slots for `<= 288` syms (**536** for `<= 286`); **42** for `<= 32` dists (**38** for `<= 30`), proved in `Probe 1`. |

1. **Complement Pair Addressing (`!symbol == -tree_cur - 1`)**: `init_tree` (`L976, L1012–1036`) allocates negative odd node pointers `tree_next = -1, -3, ...` (`tree_next -= 2`), writing child `bit` $\in \{0, 1\}$ at `-(tree_cur - bit) - 1`. In two's-complement `i32`, `!tree_cur + bit == (-tree_cur - 1) + bit == -(tree_cur - bit) - 1`, so `tree_lookup` (`L87`) and `decode_huffman_code` (`L686`) address the exact pair `(2j, 2j + 1)`.
2. **Discharging `decode_huffman_code`'s Panicking `tree[...]` Index (`core.rs:L685`)**: Unlike `tree_lookup`'s `.get()` (`L94`), `decode_huffman_code` (`L685–686`) indexes `r.tables[table].tree[...]` directly with `[]`. Under Kraft completeness, if $R \ge 1$ 10-bit root entries are internal, filling the remaining $1024 - R$ root entries uses at least $\text{popcount}(1024 - R)$ short symbols, while each of the $R$ subtrees has max depth $15 - 10 = 5$ ($M_r \in [2, 32]$ leaves) and allocates $2(M_r - 1)$ slots:
   $$\text{slots} = 2(M_{>10} - R) \le 2\bigl(288 - \text{popcount}(1024 - R) - R\bigr), \qquad M_{>10} \le 32 R.$$
   Maximizing over $1 \le R \le 144$ (`Probe 1`) peaks uniquely at **$R = 9$** ($\text{popcount}(1015) = 9$ short symbols at $\{1,2,3,4,5,6,8,9,10\}$ plus $9$ at length 14 and $270$ at length 15: $M_{>10} = 279$), consuming **$2(279 - 9) = 540 < 576$ slots** ($536 < 576$ for `<= 286` dynamic symbols).
3. **`0i16` Sentinel Non-Collision (`core.rs:L96, L913, L1025, L1040`)**: `table.tree` is zero-initialized (`L913`) yet writes leaf `symbol_index == 0` (literal `0x00`) as raw `0i16` (`L1040`). Prefix-freeness ($\text{left}_k \ge 0$) guarantees no strict prefix visited at `L1025` holds leaf `0`, while completeness (`total == 65_536` for `max_code_len > 1`) guarantees every allocated sibling pair in `table.tree` has both children overwritten—otherwise (`Probe 1`, single 11-bit symbol `5`) `tree[1]` stays `0i16` and input `1 << 10` silently misdecodes as literal `0x00`! Moreover, `code_len` advances monotonically `10..15`, terminating `tree_lookup` in $\le 5$ steps.

---

### 3. Self-Overlapping LZ77 Ring Copies (`dist < match_len`), `Cell` Aliasing, and Window Accounting

Basis: normative (RFC 1951 §3.2.5; Ziv & Lempel 1977 `10.1109/TIT.1977.1055714`) + source (`miniz_oxide@b28c2374`: `core.rs:L1088–1260, L1353–1371, L1464–1474`; `zlib@99623ef7`: `inffast.c:L25–49, L197–262`) + execution (`Probe 1`, `Anneal.Codec.PrefixLzRing`)

Over a ring buffer $W$ of size $N = 2^w$ (`out_buf_size_mask = N - 1`, `out_pos + match_len <= N`), sequential LZ77 copying executes $W_{k+1}[\text{pos} + k] = W_k[(\text{pos} + k - \text{dist}) \bmod N]$ for $0 \le k < \text{match\_len}$.

1. **Sharp Periodic Modular Law ($1 \le \text{dist} \le N$)**: For $0 \le j < k < \text{dist}$, $1 \le \text{dist} - (k - j) \le \text{dist} - 1$. Whenever **$1 \le \text{dist} \le N$**, $\text{dist} - (k - j) \in [1, N-1]$ is never $0 \pmod N$, so induction on $k$ yields $W_{\text{match\_len}}[\text{pos}+k] = W_0[(\text{pos} - \text{dist} + (k \bmod \text{dist})) \bmod N]$. At $\text{dist} = N + 1$ (`Probe 1`: $N=16, \text{dist}=17$), step $j=0$ overwrites slot `0` before step $k=1$ reads it, confirming `core.rs:L1355` (`l.dist as usize > out_buf.get_ref().len()`) is exact.
2. **`Cell::as_slice_of_cells()` Aliasing and Five-Arm Equivalence (`core.rs:L1088–1223`)**:
   - In `apply_match` (`L1179–1197`), `match_len == 3` converts `&mut [u8]` to `&[Cell<u8>]` so `dst = out_slice.get(out_pos..out_pos+3)` and `src = (a, b, c)` can hoist bounds checks ahead of interleaved `dst[0..3].set({a,b,c}.get())` even when `dist ∈ {1, 2}` causes `b, c` to alias `dst[0..2]` (`UnsafeCell` interior mutability under `#![forbid(unsafe_code)]`).
   - Across `transfer` and `apply_match`, all five arms—(i) `Cell` triple (`match_len == 3`), (ii) `dist == 1` 4-byte `fill` (`L1112–1117`), (iii) `dist >= 4` 4-byte stepped `copy_within` (`L1121–1127`, disjoint per 4-byte chunk since `source_pos + 4 <= out_pos`, unlike bulk `copy_within` which fails when `4 <= dist < match_len`!), (iv) non-overlapping `split_at_mut` + `copy_from_slice` (`L1207–1220`, guarded against ring-wraparound overlap `source_pos >= out_pos && source_pos - out_pos < match_len`), and (v) byte-by-byte `& out_buf_size_mask` (`L1128–1163`)—produce identical bytes across all 19,072 `(N, out_pos, dist, match_len)` states in `Probe 1`.
3. **Single-Add History Check & Fast-Loop Headroom (`core.rs:L1257, L1354, L1473`)**: Setting `dist_limit_offset = history_before.wrapping_sub(out_pos)` makes `position.wrapping_add(dist_limit_offset)` equal `history_before + (position - out_pos)` in one register add. And because `decompress_fast` (`L1264–1293`) can emit one literal *before* a 258-byte match in a single outer iteration, it requires `out_buf.bytes_left() >= 259` and `in_iter.bytes_left() >= 14` (vs. `zlib` `inflate_fast`'s `258` and `6` at `inffast.c:L26–27`).

---

### 4. Pass-1 3-Axiom Lean 4 (`v4.34.1`) Mechanization (`Anneal.Codec.PrefixLzRing`)

Basis: source (`joshlf/anneal@c131b320`: `trusted/lean/foundation-lock.json`, `trusted/audit/TrustedBoundary.lean:L442–596`, `theory/Anneal/PureLift/SpatialPin.lean:L69–195`) + execution (Lean `v4.34.1` kernel audit) + derived

The self-contained Pass-1 `theory/` module below compiles under Lean `v4.34.1` (`0` errors, `0` `sorry`, `0` `._unsafe_rec`, axiom footprint `[propext]`), using `@Nat.rec` and `List.foldr` so `SpatialPin.mutateSpatialBlockAt` (`SpatialPin.lean:L170–195`) can lift the entire circular `Cell` slice as a single unsplit `SpatialBlock` (`activeSubSplits == 0`) via `lz77RingStep_length`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

namespace Anneal.Codec.PrefixLzRing

/-- Continuation-passing left fold via `List.foldr` (zero `._unsafe_rec`). -/
def listFoldl {α β : Type} (f : β → α → β) (init : β) (xs : List α) : β :=
  xs.foldr (fun x k acc => k (f acc x)) (fun acc => acc) init

/-- Total O(n) functional index lookup over `List Nat` without partial recursion. -/
def listGetNat (xs : List Nat) (targetIdx : Nat) : Option Nat :=
  (listFoldl
    (fun (st : Nat × Option Nat) elem =>
      match st with
      | (idx, some v) => (idx + 1, some v)
      | (idx, none) =>
        match Nat.beq idx targetIdx with
        | true  => (idx + 1, some elem)
        | false => (idx + 1, none))
    (0, none) xs).2

/-- Total length-preserving functional update at `targetIdx` via `List.foldr`. -/
def listSetNat (xs : List Nat) (targetIdx val : Nat) : List Nat :=
  (xs.foldr
    (fun elem (acc : Nat × List Nat) =>
      match acc with
      | (remIdx, out) =>
        let curIdx := remIdx - 1
        let elem' := match Nat.beq curIdx targetIdx with
          | true  => val
          | false => elem
        (curIdx, elem' :: out))
    (xs.length, [])).2

theorem listSetNat_step_len (xs : List Nat) (targetIdx val : Nat) :
    ∀ n : Nat,
      (xs.foldr
        (fun elem (acc : Nat × List Nat) =>
          match acc with
          | (remIdx, out) =>
            let curIdx := remIdx - 1
            let elem' := match Nat.beq curIdx targetIdx with
              | true  => val
              | false => elem
            (curIdx, elem' :: out))
        (n, [])).2.length = xs.length := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons hd tl ih =>
    intro n
    dsimp [List.foldr, List.length]
    rw [ih n]

/-- Updating a circular ring slot preserves spatial block length (`SpatialPin.lean:L188`). -/
theorem listSetNat_length (xs : List Nat) (targetIdx val : Nat) :
    (listSetNat xs targetIdx val).length = xs.length :=
  listSetNat_step_len xs targetIdx val xs.length

/-- State of the joint `miniz_oxide` (`total`) + `zlib` (`left`) Kraft scan across bit depths 1..15. -/
structure KraftScanState where
  ok         : Bool
  depth      : Nat
  left       : Nat
  total      : Nat
  maxUsedLen : Nat

def kraftScanStep (st : KraftScanState) (cnt : Nat) : KraftScanState :=
  let nextDepth := st.depth + 1
  match st.ok with
  | false => ⟨false, nextDepth, 0, st.total, st.maxUsedLen⟩
  | true  =>
    let maxLen' := match Nat.beq cnt 0 with
      | true  => st.maxUsedLen
      | false => nextDepth
    let total' := Nat.mul 2 (st.total + cnt)
    let avail  := Nat.mul 2 st.left
    match Nat.ble cnt avail with
    | true  => ⟨true, nextDepth, avail - cnt, total', maxLen'⟩
    | false => ⟨false, nextDepth, 0, total', maxLen'⟩

def runKraftScan15 (counts1To15 : List Nat) : KraftScanState :=
  listFoldl kraftScanStep ⟨true, 0, 1, 0, 0⟩ counts1To15

/-- Exact RFC 1951 / `miniz_oxide` (`core.rs:L953-974`) / `zlib` (`inftrees.c:L140-147`) admission gate:
    15 bit-length buckets, non-negative `left` at every step, and either Kraft-complete (`total == 65536`)
    or non-`HUFFLEN` degenerate table (`maxUsedLen <= 1`). -/
def acceptsDeflateTable (isHufflen : Bool) (counts1To15 : List Nat) : Bool :=
  match Nat.beq counts1To15.length 15 with
  | false => false
  | true  =>
    let st := runKraftScan15 counts1To15
    match st.ok with
    | false => false
    | true  =>
      match Nat.beq st.total 65536 with
      | true  => true
      | false =>
        match isHufflen with
        | true  => false
        | false => Nat.ble st.maxUsedLen 1

/-- Inductive algebraic coupling proving `total_k + 2 * left_k = 2^(k+1)` across every non-oversubscribed step:
    `(2 * (total + cnt)) + 2 * (2 * left - cnt) = 2 * (total + 2 * left)`. -/
theorem kraft_dual_step_invariant (total left cnt cap : Nat)
    (hInv : total + 2 * left = cap)
    (hFit : cnt ≤ 2 * left) :
    2 * (total + cnt) + 2 * (2 * left - cnt) = 2 * cap := by
  have hSub : cnt + (2 * left - cnt) = 2 * left := Nat.add_sub_of_le hFit
  have hMul : 2 * cnt + 2 * (2 * left - cnt) = 2 * (2 * left) := by
    rw [← Nat.mul_add 2 cnt (2 * left - cnt)]
    rw [hSub]
  rw [Nat.mul_add 2 total cnt]
  rw [Nat.add_assoc (2 * total) (2 * cnt) (2 * (2 * left - cnt))]
  rw [hMul]
  rw [← Nat.mul_add 2 total (2 * left)]
  rw [hInv]

/-- RFC 1951 §3.2.6 fixed 288-symbol LITLEN code (`24@7, 152@8, 112@9`) is Kraft-complete (`total == 65536, left == 0`). -/
theorem rfc1951_fixed_litlen_accepted :
    acceptsDeflateTable false [0, 0, 0, 0, 0, 0, 24, 152, 112, 0, 0, 0, 0, 0, 0] = true := rfl

/-- Worst-case 288-symbol secondary-trie histogram (`540 < 576` slots) is Kraft-complete. -/
theorem miniz_worst_case_288_accepted :
    acceptsDeflateTable false [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 9, 270] = true := rfl

/-- Single-symbol 1-bit EOB table (`maxUsedLen == 1`) is admitted for LITLEN/DIST (`core.rs:L966-972`). -/
theorem single_eob_litlen_accepted :
    acceptsDeflateTable false [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := rfl

/-- Identical 1-bit incomplete table is rejected for `HUFFLEN_TABLE` (`inftrees.c:L146`, `core.rs:L972`). -/
theorem single_hufflen_rejected :
    acceptsDeflateTable true [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = false := rfl

/-- Incomplete table with `maxUsedLen = 2 > 1` (`1/2 + 1/4 < 1`) is rejected. -/
theorem incomplete_depth2_rejected :
    acceptsDeflateTable false [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = false := rfl

/-- Over-subscribed table (`1/2 + 2/4 + 1/8 > 1`) is rejected at bit length 3 (`left < 0`). -/
theorem oversubscribed_rejected :
    acceptsDeflateTable false [1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = false := rfl

/-- Single circular LZ77 byte copy step over a power-of-2 window (`winMask = 2^w - 1`). -/
def lz77RingStep (winMask : Nat) (win : List Nat) (pos dist : Nat) : List Nat :=
  let winSize := winMask + 1
  let srcIdx  := Nat.land (pos + winSize - Nat.mod dist winSize) winMask
  let dstIdx  := Nat.land pos winMask
  let b       := match listGetNat win srcIdx with | some v => v | none => 0
  listSetNat win dstIdx b

/-- Fuel-free `@Nat.rec` iteration of `matchLen` sequential overlapping LZ77 copies (`0` `._unsafe_rec`). -/
def lz77ApplyMatch (winMask : Nat) (win : List Nat) (pos dist matchLen : Nat) : List Nat :=
  (@Nat.rec (fun _ => Nat → List Nat → List Nat)
    (fun _ curWin => curWin)
    (fun _ ih curPos curWin =>
      let nextWin := lz77RingStep winMask curWin curPos dist
      ih (curPos + 1) nextWin)
    matchLen) pos win

theorem lz77RingStep_length (winMask : Nat) (win : List Nat) (pos dist : Nat) :
    (lz77RingStep winMask win pos dist).length = win.length :=
  listSetNat_length win (Nat.land pos winMask)
    (match listGetNat win (Nat.land (pos + (winMask + 1) - Nat.mod dist (winMask + 1)) winMask) with
     | some v => v | none => 0)

/-- Self-overlapping periodic run-length expansion (`dist = 3 < matchLen = 10`) repeats `[10, 20, 30]`. -/
theorem lz77_overlap_dist3_len10_periodic :
    lz77ApplyMatch 15 [10, 20, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 3 3 10 =
      [10, 20, 30, 10, 20, 30, 10, 20, 30, 10, 20, 30, 10, 0, 0, 0] := rfl

/-- Simultaneous circular wraparound (`pos = 0, dist = 2` reading `6, 7`) and self-overlap (`matchLen = 5 > 2`). -/
theorem lz77_wrap_and_overlap_canary :
    lz77ApplyMatch 7 [99, 88, 0, 0, 0, 0, 11, 22] 0 2 5 =
      [11, 22, 11, 22, 11, 0, 11, 22] := rfl

end Anneal.Codec.PrefixLzRing
```

## Boundaries

- **not examined**: DEFLATE compression-side LZ77 hash chains, package-merge length-limited Huffman encoders (`miniz_oxide/src/deflate/core.rs`), `simd-adler32`, and RFC 1952 `gzip` CRC-32 trailers.
- **unknown**: Lean `v4.34.1` kernel reduction latency when symbolically unfolding all 32+ state transitions of `decompress_with_limit` (`core.rs:L1486–2044`) without per-state CFG cutpoints.
- **known not to apply**:
  - Disjoint `&mut` splitting (`split_at_mut`) **cannot** verify `apply_match` when `dist < match_len` or when ring wraparound satisfies `source_pos >= out_pos && source_pos - out_pos < match_len` (`core.rs:L1179–1197, L1207`).
  - Bulk `copy_within` (`memmove`) **fails** when `4 <= dist < match_len`; only chunk widths `<= dist` (4-byte steps under `dist >= 4`, `L1121–1127`) preserve periodic extension.
  - Periodic ring equivalence **fails** whenever $\text{dist} > N$ (`Probe 1`: $N=16, \text{dist}=17$ clobbers slot `0`), and `core.rs:L908`'s *"3 bits"* comment does not hold literally for `HUFFLEN_TABLE` code lengths (`0..=7 <= 10`).
- **unsupported**: In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirSemantics` fails closed (`FaultKind.unsupported`) on `&mut [u8]` / `&[Cell<u8>]` entry slices, non-empty `CallerMemory`, and interprocedural calls (`MirSemantics.lean:L1686–1694`).

## Evidence

| Subject | Immutable Identity | Inspected Paths & Line Ranges |
| :--- | :--- | :--- |
| **`miniz_oxide` `0.9.1`** | `Frommi/miniz_oxide` @ `b28c237471f63efebe152bddd962dc57bbb531eb` | `miniz_oxide/Cargo.toml` (`L1–54`); `src/lib.rs` (`L25`); `src/inflate/core.rs` (`L1–143`, `L645–748`, `L884–1057`, `L1088–1377`, `L1433–1476`, `L1650–1978`, `L2070–2112`); `src/inflate/output_buffer.rs` (`L1–124`) |
| **`zlib` `1.4` & `v1.3.1`** | `madler/zlib` @ `99623ef7097352da7993ba614161fd6a311e046e` & `51b7f2abdade71cd9bb0e7a373ef2610ec6f9daf` | `zlib.h` (`L1–50`); `inftrees.h` (`L24–70`); `inftrees.c` (`L46–372`); `inffast.c` (`L15–305`); `examples/enough.c` (`L261–447`) |
| **Anneal & Lean `v4.34.1`** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `trusted/lean/foundation-lock.json` (`L1–22`); `trusted/audit/TrustedBoundary.lean` (`L442–596`); `trusted/lean/Trusted/MirSemantics.lean` (`L1646–1706`); `theory/Anneal/PureLift/SpatialPin.lean` (`L69–195`) |
| **Specs & Literature** | `10.17487/RFC1951`; `10.1109/TIT.1977.1055714`; `10.1109/JRPROC.1952.273898`; `10.1109/TIT.1956.1056818`; `10.1007/s10817-009-9116-y`; `10.48550/arXiv.1609.01220` | Deutsch (RFC 1951); Ziv & Lempel (1977); Huffman (1952); McMillan (1956); Blanchette (2009); Senjak & Hofmann (2016) |

### Standalone Executable Probe 1 (`CPython 3.13.15`, `x86_64`, `2026-11-20`)

```python
from functools import lru_cache

FAST_BITS, FAST_SIZE, TREE_MAX, INV = 10, 1024, 576, (1 << 9) | 286

def rev16(n: int) -> int:
    return sum(((n >> i) & 1) << (15 - i) for i in range(16))

def miniz_init_tree(cs_list: list[int], hufflen: bool = False, skip_comp: bool = False):
    ts, nc, lu, tr = [0] * 16, [0] * 17, [INV] * FAST_SIZE, [0] * TREE_MAX
    for cs in cs_list:
        if cs >= 16: return ("ERR_RANGE", None, None, None)
        ts[cs] += 1
    tot = mlen = 0
    left = 1
    for i in range(1, 16):
        if ts[i] > 0: mlen = i
        tot = (tot + ts[i]) << 1
        nc[i + 1] = tot
        left = (left << 1) - ts[i]
        assert tot + 2 * left == (1 << (i + 1))
        if left < 0: return ("ERR_OVER", None, None, None)
    if not skip_comp and tot != 65536 and (hufflen or mlen > 1):
        return ("ERR_INC", None, None, None)
    tnext = -1
    for sym, cs in enumerate(cs_list):
        cs &= 15
        if cs == 0: continue
        cur = nc[cs]; nc[cs] += 1
        rev = rev16(cur & (0xFFFFFFFF >> (32 - cs))) >> (16 - cs)
        if cs <= FAST_BITS:
            k = (cs << 9) | sym
            while rev < FAST_SIZE:
                lu[rev] = k; rev += 1 << cs
            continue
        tcur = lu[rev & 1023]
        if tcur == INV:
            lu[rev & 1023] = tcur = tnext; tnext -= 2
        rev >>= FAST_BITS - 1
        for _ in range(FAST_BITS + 1, cs):
            rev >>= 1; tcur -= rev & 1; idx = -tcur - 1
            if idx >= TREE_MAX: return ("ERR_OOB", lu, tr, -tnext - 1)
            if tr[idx] == 0: tr[idx] = tcur = tnext; tnext -= 2
            else: tcur = tr[idx]
        rev >>= 1; tcur -= rev & 1; idx = -tcur - 1
        if idx >= TREE_MAX: return ("ERR_OOB", lu, tr, -tnext - 1)
        tr[idx] = sym
    return ("OK", lu, tr, -tnext - 1)

def miniz_lookup(lu: list[int], tr: list[int], bb: int) -> tuple[int, int]:
    s = lu[bb & 1023]
    if s >= 0: return (s & 511, s >> 9)
    cl = FAST_BITS
    while True:
        s = tr[(~s) + ((bb >> cl) & 1)]; cl += 1
        if s >= 0: return (s, cl)

def max_miniz_slots(max_syms: int, root: int = 10, mbits: int = 15):
    @lru_cache(maxsize=None)
    def sdp(d: int, open_n: int, sleft: int):
        if open_n > sleft: return (-10**9, ())
        if d == mbits: return (0, (open_n,))
        best = (-10**9, ())
        for c in range(max(0, (open_n << 1) - sleft), open_n + 1):
            rem = open_n - c
            if 2 * rem > sleft - c: continue
            sv, sh = sdp(d + 1, 2 * rem, sleft - c)
            if sv >= 0 and 2 * rem + sv > best[0]: best = (2 * rem + sv, (c,) + sh)
        return best
    best = (0, (0,) * mbits)
    for rr in range(1, min((1 << root) - 1, max_syms // 2) + 1):
        w = (1 << root) - rr
        ms = w.bit_count()
        if ms + 2 * rr > max_syms: continue
        sv, sh = sdp(root + 1, 2 * rr, max_syms - ms)
        if sv >= 0 and 2 * rr + sv > best[0]:
            best = (2 * rr + sv, tuple((w >> (root - d)) & 1 for d in range(1, root + 1)) + sh)
    return best

def zlib_enough(max_syms: int, root: int, mbits: int = 15) -> int:
    @lru_cache(maxsize=None)
    def ex(syms: int, left: int, ln: int, rem: int) -> int:
        if syms == left:
            ext, cl, cr = 0, left, rem
            while cr < cl: cl -= cr; cr = 1 << (ln - root); ext += cr
            return ext
        if syms < left or left <= 0 or ln >= mbits or syms > (left << (mbits - ln)): return -10**9
        least = max(0, (left << 1) - syms)
        most = ((left << (mbits - ln)) - syms) // ((1 << (mbits - ln)) - 1)
        ab, u, cr, best = 0, least, rem, -10**9
        while cr < u: u -= cr; cr = 1 << (ln - root); ab += cr
        cr -= u
        for use in range(least, most + 1):
            sm = ab + ((1 << (ln - root)) if cr else 0)
            sub = ex(syms - use, (left - use) << 1, ln + 1, cr << 1)
            if sub >= 0 and sm + sub > best: best = sm + sub
            if cr == 0: cr = 1 << (ln - root); ab += cr
            cr -= 1
        return best
    bt = 1 << root
    for rr in range(1, min((1 << root) - 1, max_syms // 2) + 1):
        ms = ((1 << root) - rr).bit_count()
        for ss in range(2 * rr, max_syms - ms + 1):
            sub = ex(ss, 2 * rr, root + 1, 0)
            if sub >= 0: bt = max(bt, (1 << root) + sub)
    return bt

b288, h288 = max_miniz_slots(288)
b286, _ = max_miniz_slots(286)
zl = (zlib_enough(286, 9), zlib_enough(288, 9), zlib_enough(30, 6), zlib_enough(32, 6))
assert zl == (852, 854, 592, 594) and (b288, b286) == (540, 536)
w288 = [i for i, c in enumerate(h288, 1) for _ in range(c)] + [0] * (288 - sum(h288))
assert miniz_init_tree(w288)[3] == 540
_, lu_i, tr_i, _ = miniz_init_tree([0] * 5 + [11] + [0] * 282, skip_comp=True)
assert miniz_lookup(lu_i, tr_i, 1 << 10) == (0, 11)

def apply_miniz(buf: bytearray, op: int, dist: int, mlen: int, mask: int):
    sp = (op - dist) & mask
    if mlen == 3:
        for j, idx in enumerate([sp, (sp + 1) & mask, (sp + 2) & mask]): buf[op + j] = buf[idx]
        return
    if not (sp >= op and sp - op < mlen) and mlen <= dist and sp + mlen < len(buf):
        buf[op : op + mlen] = buf[sp : sp + mlen]; return
    nw = (sp + mlen - 3) % (1 << 64) < len(buf)
    ep = ((mlen >> 2) * 4) + op
    if nw and op > sp and op - sp == 1:
        buf[op:ep] = bytes([buf[op - 1]]) * (ep - op); op, sp = ep, ep - 1
    elif nw and op > sp and op - sp >= 4:
        lim = min(ep, max(0, len(buf) - 3))
        while op < lim: buf[op : op + 4] = buf[sp : sp + 4]; sp += 4; op += 4
    else:
        lim = min(ep, max(0, len(buf) - 3))
        while op < lim:
            for j in range(4): buf[op + j] = buf[(sp + j) & mask]
            sp += 4; op += 4
    for j in range(mlen & 3): buf[op + j] = buf[(sp + j) & mask]

lz_ok = 0
for N in [16, 32]:
    base = bytearray((i * 37 + 11) & 0xFF for i in range(N))
    for op in range(N):
        for mlen in range(1, N - op + 1):
            for dist in range(1, N + 1):
                b = bytearray(base); apply_miniz(b, op, dist, mlen, N - 1)
                assert all(b[op + k] == base[(op - dist + (k % dist)) % N] for k in range(mlen))
                lz_ok += 1
print("PROBE_DEFLATE_OK", {"miniz_288": b288, "miniz_286": b286, "zlib": zl, "lz_cases": lz_ok})
```

Observed output (`2026-11-20`, `CPython 3.13.15`):
`PROBE_DEFLATE_OK {'miniz_288': 540, 'miniz_286': 536, 'zlib': (852, 854, 592, 594), 'lz_cases': 19072}`

## Revalidation

1. **Source diff**: Diff `miniz_oxide/src/inflate/core.rs` (`HuffmanTable`, `decode_huffman_code`, `init_tree`, `transfer`, `apply_match`) against `b28c237471f63efebe152bddd962dc57bbb531eb` and `inftrees.{h,c}` / `inffast.c` against `99623ef7097352da7993ba614161fd6a311e046e`.
2. **Lean `v4.34.1` kernel audit**: Check Section 4's `Anneal.Codec.PrefixLzRing` module with `lean -DElab.async=false -Ddebug.skipKernelTC=false` (`0` errors, `0` `sorry`, axioms $\subseteq \{\texttt{propext}\}$).
3. **Executable probe**: Run Python 3 (`>= 3.10`) on **Standalone Executable Probe 1** (`~4 s`) and confirm `PROBE_DEFLATE_OK` exits `0`.
