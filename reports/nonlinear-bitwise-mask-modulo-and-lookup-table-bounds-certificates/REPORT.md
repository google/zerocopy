# Nonlinear Bitwise-Mask, Unsigned-Modulo, and Lookup-Table Bounds Certificates (`BitwiseModFarkasCert`)

## Summary

In `type-validity-seeded-range-and-farkas-bounds-check-elimination`, linear Farkas certificates discharged `100%` of linear counted-loop bounds checks (`while i + K <= slice.len()`), but left **`770` non-linear / bitwise-computed array index checks** across `core`, `alloc`, `std`, `zlib-rs`, `regex-automata`, `hashbrown`, `serde_json`, and `memchr` untouched because linear combinations cannot directly bound bitwise masks (`table[bits & 0x1FF]`, `buckets[hash & mask]`), logical right shifts (`TRANSITIONS[state + (byte >> 4)]`), unsigned remainders (`buf[seq % cap]`), or bit-counting intrinsics (`CLASSES[64 - x.leading_zeros()]`). By coupling five universal nonlinear bitvector-to-linear bridge rules (`BRIDGE-AND-CONST`, `BRIDGE-AND-VAR`, `BRIDGE-LSHR`, `BRIDGE-UREM`, `BRIDGE-BITCOUNT`) with a $k$-ary Farkas linear inequality checker (`FarkasCertList`) in Lean `v4.34.1` ([`support/BitwiseModFarkasBoundsChecker.lean`](support/BitwiseModFarkasBoundsChecker.lean), `402` lines, checked in `1,213.28 ms` with **`0` `sorryAx`** and **`0` `Lean.ofReduceBool`**) and evaluating the pass across the 8-crate benchmark corpus ([`support/run_bitwise_mod_farkas_bench.py`](support/run_bitwise_mod_farkas_bench.py), [`support/bitwise_mod_bounds_results.json`](support/bitwise_mod_bounds_results.json)), we establish four governing results:

1. **Zero-Bit-Blasting Universal Bitwise-AND and Modulo Bridge Theorems in Lean `v4.34.1`:**
   - Proving `(x & m) < len` via bit-blasting (`bv_decide`) or by unfolding Anneal's recursive `bitwiseAndBits w x m` over symbolic `x, m : Nat` causes elaborator/kernel `whnf` blowup.
   - Instead, [`support/BitwiseModFarkasBoundsChecker.lean`](support/BitwiseModFarkasBoundsChecker.lean#L46-L138) proves once-and-for-all by symbolic bit-width recursion (`0` `sorryAx`, `0` `Lean.ofReduceBool`):
     - `bitwiseAndBits_le_right : ∀ w x m : Nat, bitwiseAndBits w x m ≤ m`
     - `bitwiseAndBits_le_left : ∀ w x m : Nat, bitwiseAndBits w x m ≤ x`
     - `nat_land_le_right : ∀ x m : Nat, (x &&& m) ≤ m`
     - `nat_mod_lt_of_pos : ∀ x d : Nat, 1 ≤ d → x % d ≤ d - 1 ∧ x % d < d`
     - `nat_shiftr_upper_bound : ∀ x u k : Nat, x ≤ u → x >>> k ≤ u / (2 ^ k)`
   - Notice that `0 ≤ (x &&& m) ≤ m` holds for **every** pair of unsigned integers $x, m \in \mathbb{N}$—even when $m + 1$ is **not** a power of two! Consequently, for any hash table or ring buffer where `cap = mask + 1` (or `mask < len`), `BRIDGE-AND-VAR` emits the linear inequality $\text{idx} - \text{cap} + 1 \le 0$ directly into the Farkas context without requiring a power-of-two proof on `cap`.
2. **$k$-ary `FarkasCertList` and Unified `BitwiseModFarkasCert` Checker (`checkBitwiseModFarkasCert_sound`):**
   - Extending `unified-farkas-knownbits-and-aegraph-side-condition-certificates` (`FarkasCert2`, which was restricted to 2 hypotheses over 2 variables), `checkFarkasCertList` folds an arbitrary list `List (Nat × LinearConstraint4)` of non-negative multipliers over the 4-variable index context `(idx, aux, cap, len)` and verifies that `foldFarkasList hyps + negBoundsTarget` cancels all variable coefficients (`aIdx = aAux = aCap = aLen = 0`) and yields a positive constant `c ≥ 1`.
   - All five canonical ecosystem patterns (`zlib_huffman_table_lookup_verified`, `hashbrown_probe_slot_verified`, `utf8_dfa_byte_class_verified`, `ring_buffer_modulo_verified`, and `alloc_size_class_ctlz_verified`) check by kernel `rfl` with **zero axioms (`[]`)**.
3. **Eliminating `512 / 770` (`66.49%`) of Previously Uneliminated Non-Linear Bounds Checks Across the 8-Crate Corpus:**
   - Across the `770` non-linear check sites in `zlib-rs`, `regex-automata`, `hashbrown`, `serde_json`, `memchr`, and the `1.99.1` sysroot (`core`, `alloc`, `std`), `BitwiseModFarkasCert` discharges **`512` (`66.49%`)** at an average binary certificate size of **`25.6 B`**, leaving only the `258` genuinely input-dependent dynamic checks (`table[untrusted_state_id]`).
4. **Direct Ergonomic Reuse in Anneal Source Proofs (`Proof/<Crate>/<Item>.lean`):**
   - Because `bitwiseAndBits_le_right` applies to Anneal's `Trusted.bitwiseAndBits` without unfolding the bit-width recursion at `w = 32` or `w = 64`, Anneal proof scripts can discharge masked lookup-table and ring-buffer obligations in $O(1)$ kernel time (`apply checkBitwiseModFarkasCert_sound ... rfl`) instead of manually rewriting `bitwiseAndBits` with `Hold` wrappers.

## Applicability

- **Extends:** `type-validity-seeded-range-and-farkas-bounds-check-elimination`, `unified-farkas-knownbits-and-aegraph-side-condition-certificates`, `verified-side-condition-decision-procedures-and-certificate-checkers`
- **Subjects:**
  - **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel typechecker (`-DElab.async=false -Ddebug.skipKernelTC=false`).
  - **Rust Compiler (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`)** and **LLVM (`rust-lang/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, `23.1.1`)**: Non-linear bounds-check survival in `InstCombine`, `SelectionDAG` `KnownBits`, and `ConstraintElimination`.
  - **Anneal (`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`)**: `bitwiseAndBits` symbolic evaluation and `TrustedBoundary` axiom rules.

## Findings

### 1. The Five Canonical Nonlinear-to-Linear Bridge Rules (`BitwiseModBridgeKind`)

`Basis: derived + execution (support/BitwiseModFarkasBoundsChecker.lean)`

Table 1 defines the five algebraic bridge rules mechanized in [`support/BitwiseModFarkasBoundsChecker.lean`](support/BitwiseModFarkasBoundsChecker.lean#L247-L287) that translate nonlinear bitvector operations on an index `idx` into linear constraints `aIdx * idx + aAux * aux + aCap * cap + aLen * len + c ≤ 0`:

| Bridge Rule ID | Source `MiniSSA` / MIR Index Expression | Required Side Condition | Emitted Linear Inequality ($L(\text{idx}, \text{aux}, \text{cap}, \text{len}) \le 0$) | Underlying Lean `v4.34.1` Theorem |
| :--- | :--- | :--- | :--- | :--- |
| **`BRIDGE-AND-CONST`** | `idx = x & C` (or `KnownBits` zero-mask $z_x$ with $C = 2^W - 1 - z_x$) | Constant unsigned mask $C \ge 0$ | $1 \cdot \text{idx} - C \le 0$ ($\text{idx} \le C$) | `bitwiseAndBits_le_right`, `nat_land_le_right` |
| **`BRIDGE-AND-VAR`** | `idx = x & mask` where `cap = mask + 1` (e.g. `mask = cap - 1`) | `cap >= 1` (`capIsMaskPlusOne = true`, so `mask = cap - 1 >= 0`) | $1 \cdot \text{idx} - 1 \cdot \text{cap} + 1 \le 0$ ($\text{idx} \le \text{cap} - 1$) | `bitwiseAndBits_le_right`, `nat_land_le_right` |
| **`BRIDGE-LSHR`** | `idx = aux + (x >> k)` where $0 \le x \le U$ | `shiftMax = ⌊U / 2^k⌋` (e.g. `u8 >> 4` $\implies \text{shiftMax} = 15$) | $1 \cdot \text{idx} - 1 \cdot \text{aux} - \text{shiftMax} \le 0$ | `nat_shiftr_upper_bound` |
| **`BRIDGE-UREM`** | `idx = x % cap` | Dominating guard or `NonZeroUsize` proving `cap >= minDivisor >= 1` | $1 \cdot \text{idx} - 1 \cdot \text{cap} + 1 \le 0$ ($\text{idx} \le \text{cap} - 1$) | `nat_mod_lt_of_pos` |
| **`BRIDGE-BITCOUNT`** | `idx = ctlz(x)` / `cttz(x)` / `ctpop(x)` / `W - ctlz(x)` | $W$-bit integer operand ($W \in \{8, 16, 32, 64, 128\}$) | $1 \cdot \text{idx} - W \le 0$ ($\text{idx} \le W$) | `bridgeConstraintOf (.bridgeBitCount W)` |

---

### 2. Kernel-Checked Theorems and Archetype Certificates in `BitwiseModFarkasBoundsChecker.lean`

`Basis: execution (support/BitwiseModFarkasBoundsChecker.lean, support/bitwise_mod_bounds_results.json)`

Table 2 summarizes the 13 kernel-checked theorems in [`support/BitwiseModFarkasBoundsChecker.lean`](support/BitwiseModFarkasBoundsChecker.lean) (`402` lines, verified in `1,213.28 ms` with **`0` `sorryAx`** and **`0` `Lean.ofReduceBool`**):

| Theorem Name | Category | Verified Property / Pattern | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `bitwiseAndBits_le_right` | Universal Bitwise Bridge | $\forall w, x, m \in \mathbb{N},\; \texttt{bitwiseAndBits}(w, x, m) \le m$ | `[propext, Classical.choice, Quot.sound]` |
| `bitwiseAndBits_le_left` | Universal Bitwise Bridge | $\forall w, x, m \in \mathbb{N},\; \texttt{bitwiseAndBits}(w, x, m) \le x$ | `[propext, Classical.choice, Quot.sound]` |
| `nat_land_le_right` | Universal `Nat.land` Bridge | $\forall x, m \in \mathbb{N},\; (x \mathbin{\&\&\&} m) \le m$ | `[propext, Quot.sound]` |
| `nat_mod_lt_of_pos` | Universal Modulo Bridge | $\forall x, d \in \mathbb{N},\; 1 \le d \implies x \bmod d \le d - 1 \land x \bmod d < d$ | `[propext, Quot.sound]` |
| `nat_shiftr_upper_bound` | Universal Shift Bridge | $\forall x, u, k \in \mathbb{N},\; x \le u \implies (x \ggg k) \le u / 2^k$ | `[propext]` |
| `checkFarkasCertList_sound` | $k$-ary Farkas Checker | `checkFarkasCertList hyps = true` $\wedge$ `AllConstraintsHold` $\implies \text{idx} < \text{len}$ | `[propext, Quot.sound]` |
| `checkBitwiseModFarkasCert_sound` | Master Certificate Bridge | `checkBitwiseModFarkasCert cert = true` $\implies \text{idx} < \text{len}$ | `[propext, Quot.sound]` |
| `zlib_huffman_table_lookup_verified` | Archetype 1 (`zlib-rs`) | `table[bits & 511]` with `len >= 512` (`BRIDGE-AND-CONST`) | **None (`[]`)** |
| `hashbrown_probe_slot_verified` | Archetype 2 (`hashbrown`) | `buckets[hash & bucket_mask]` with `cap = bucket_mask + 1 <= len` (`BRIDGE-AND-VAR`) | **None (`[]`)** |
| `utf8_dfa_byte_class_verified` | Archetype 3 (`regex-automata`) | `TRANSITIONS[state + (byte >> 4)]` with `state <= 240, len >= 256` (`BRIDGE-LSHR`) | **None (`[]`)** |
| `ring_buffer_modulo_verified` | Archetype 4 (`tokio` / ring) | `buf[seq % cap]` with `1 <= cap <= len` (`BRIDGE-UREM`) | **None (`[]`)** |
| `alloc_size_class_ctlz_verified` | Archetype 5 (`alloc`) | `CLASSES[64 - x.leading_zeros()]` with `len == 65` (`BRIDGE-BITCOUNT`) | **None (`[]`)** |
| `zeroDivisorModulo_rejected` | Negative Soundness Guard | Rejects `seq % cap` when `minDivisor == 0` (`= false`) | **None (`[]`)** |

---

### 3. Corpus Evaluation Across `zlib-rs`, `regex-automata`, `hashbrown`, `serde_json`, `memchr`, and the `1.99.1` Sysroot

`Basis: execution + derived (support/run_bitwise_mod_farkas_bench.py, support/bitwise_mod_bounds_results.json)`

Table 3 classifies how many of the `770` non-linear bounds checks from `type-validity-seeded-range-and-farkas-bounds-check-elimination` are discharged by `BitwiseModFarkasCert`:

| Crate / Suite | Non-Linear Checks Remaining After Linear Farkas | `BRIDGE-AND-CONST` (`x & C`) | `BRIDGE-AND-VAR` (`x & mask`) | `BRIDGE-LSHR` (`x >> k`) | `BRIDGE-UREM` (`x % d`) | `BRIDGE-BITCOUNT` (`ctlz`/`cttz`) | **Total Discharged by `BitwiseModFarkasCert`** | Truly Dynamic Untrusted Index Remaining |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `zlib-rs 0.4.0` | `32` | `18` | `6` | `4` | `0` | `2` | **`30` (`93.8%`)** | `2` (`6.2%`) |
| `regex-automata 0.4.8` | `156` | `42` | `14` | `38` | `4` | `6` | **`104` (`66.7%`)** | `52` (`33.3%`) |
| `hashbrown 0.15.1` | `12` | `2` | `8` | `1` | `0` | `1` | **`12` (`100.0%`)** | `0` (`0.0%`) |
| `serde_json 1.0.132` | `66` | `24` | `4` | `16` | `6` | `4` | **`54` (`81.8%`)** | `12` (`18.2%`) |
| `memchr 2.7.4` | `8` | `4` | `2` | `0` | `0` | `2` | **`8` (`100.0%`)** | `0` (`0.0%`) |
| `core + alloc + std` (`1.99.1`) | `496` | `112` | `48` | `64` | `38` | `42` | **`304` (`61.3%`)** | `192` (`38.7%`) |
| **Total Across Corpus** | **`770`** | **`202`** | **`82`** | **`123`** | **`48`** | **`57`** | **`512` (`66.49%`)** | **`258` (`33.51%`)** |

## Boundaries

1. **Unmasked Data-Dependent Lookup Tables (`known not to apply` without a memory-content invariant):**
   - The `258` remaining checks (`33.51%`, such as `dfa.states[next_state_id]` in `regex-automata` when `next_state_id` is loaded from a heap-allocated transition table without a bitmask `& state_mask`) depend on a quantified heap invariant ($\forall i,\, \text{table}[i] < \text{states.len}()$) that cannot be established by local bitvector or linear range analysis alone.
2. **Signed Remainder (`srem` / `%` on `i32`/`i64`/`isize`) With Negative Dividends (`known not to apply` for `BRIDGE-UREM`):**
   - In Rust, signed `x % d` preserves the sign of the dividend `x` (`(-5i32) % 3 == -2`), which wraps to a large unsigned `usize` if cast directly without `.rem_euclid(d)` or a non-negative guard `x >= 0`. `BRIDGE-UREM` applies strictly to unsigned `urem` (or signed `srem` where `0 <= x` and `1 <= d` are already established).

## Evidence

1. **Kernel-Checked Lean 4.34.1 Bitwise-Modulo-Farkas Checker:**
   - [`support/BitwiseModFarkasBoundsChecker.lean`](support/BitwiseModFarkasBoundsChecker.lean): Proves `bitwiseAndBits_le_right`, `bitwiseAndBits_le_left`, `nat_land_le_right`, `nat_mod_lt_of_pos`, `nat_shiftr_upper_bound`, `checkFarkasCertList_sound`, `checkBitwiseModFarkasCert_sound`, 5 ecosystem archetype certificates, and `zeroDivisorModulo_rejected` in `1,213.28 ms` (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
2. **Corpus Benchmark Runner and JSON Dataset:**
   - [`support/run_bitwise_mod_farkas_bench.py`](support/run_bitwise_mod_farkas_bench.py)
   - [`support/bitwise_mod_bounds_results.json`](support/bitwise_mod_bounds_results.json)

## Revalidation

Run the Lean `v4.34.1` certificate checker and corpus benchmark script:

```bash
python3 reports/nonlinear-bitwise-mask-modulo-and-lookup-table-bounds-certificates/support/run_bitwise_mod_farkas_bench.py
```
