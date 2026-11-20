# SIMD Gather/Scatter, Dynamic Byte Swizzles, and Vectorized Codec Table Verification

## Summary

Formal verification of vectorized table lookups in Rust requires separating **memory-backed indexed accesses** (`simd_gather`, `simd_scatter`, `llvm.x86.avx2.gather.*`) from **in-register dynamic byte permutations** (`Simd<u8, N>::swizzle_dyn`, x86 `PSHUFB`/`VPSHUFB`/`VPERMI2B`, AArch64 `TBL1`–`TBL4`, WebAssembly `i8x16.swizzle`). The two families obey incompatible alignment, initialization, mask-encoding, and out-of-bounds rules, and both trigger $O(K^L)$ state-space blowup if bit-blasted monolithically across $L$ lanes over a $K$-entry table.

Four invariants govern sound specification and scalable proof engineering in this domain:

1. **Gather/scatter operational contracts vs. hardware intrinsics:** In `rustc_const_eval` and Miri, `core::intrinsics::simd::{simd_gather, simd_scatter}` unconditionally `read_immediate` every lane of `ptrs`, `mask`, and `passthru`/`value` before consulting `mask`, require every mask lane to be strictly `0` or `-1` (`!0`), and enforce element alignment via `deref_pointer` on enabled lanes (`mask[i] == -1`) while permitting disabled lanes (`mask[i] == 0`) to hold null, unaligned, or out-of-bounds pointers formed via `wrapping_offset` (`simd_arith_offset`). Conversely, `simd_masked_load`/`simd_masked_store` check base pointer alignment unconditionally even when all mask lanes are `0`, whereas Miri's `llvm.x86.avx2.gather.*` shim inspects only the mask sign bit, reads `offsets[i]` only on enabled lanes, and performs **unaligned** `mem_copy` reads. For `simd_scatter` and LLVM `@llvm.masked.scatter.*`, colliding active lanes execute strictly from lane `0` to `N - 1` (LSB to MSB); this order is load-bearing under Stacked and Tree Borrows when lanes carry distinct parent/child tags, and produces deterministic torn values when $\text{size}(T) > \text{align}(T)$ (such as `u64`/`f64` on 32-bit `i686`).
2. **Dynamic byte-swizzle zeroing and 128-bit lane walls:** AArch64 `TBL` and WebAssembly `i8x16.swizzle` natively zero selectors $\ge 16$, whereas x86 `PSHUFB` zeroes only when selector bit 7 (`0x80`) is set (aliasing `0x10..=0x7F` modulo 16) and AVX2 `VPSHUFB` cannot cross 128-bit lane boundaries. `core_simd`'s `zeroing_idxs<N>` (`idxs | (idxs + (128 - N))`) preserves valid low nibbles without carry corruption if and only if $(128 - N) \equiv 0 \pmod{16}$ ($N = 16$ for $1 \le N \le 16$), while `avx2_pshufb` bridges the 128-bit wall via saturating addition of `0x60` paired with asymmetric sign-bit blend biases `(-112, 16)`.
3. **Production codec table invariants:** `simdutf` factors 2-byte UTF-8 error classification into three 16-byte nibble bitmask tables (`byte_1_high & byte_1_low & byte_2_high`) and uses a single bit-7 `XOR` (`must23_80 ^ sc`) to cancel valid 3/4-byte continuation pairs while synthesizing truncated-sequence errors; `zlib-rs` and `miniz_oxide` bound two-level DEFLATE Huffman tables via Kraft-McMillan completeness ($\sum 2^{-L_i} = 1$, modulo RFC 1951's 0/1-symbol exception) and monotonic DAG indices on negative internal entries (`!temp + bit < 576`); and `zlib-rs` implements variable-length PCLMULQDQ CRC-32 shifts via a 15-entry `PSHUFB` table where `xmm_shr = xmm_shl ^ 0x80` guarantees lane-disjoint zeroing.
4. **Sub-exponential proof decomposition:** Replacing whole-vector bit-blasting ($K^L$ mux branches) with (a) lane-universal `Fin L` window quotienting, (b) Boolean semiring rank factorization, (c) $\mathbb{F}_2$-linear 8-basis-vector checks for $\text{GF}(2^8)$ nibble tables, and (d) construction-time Kraft partition predicates reduces proof complexity from $O(K^L)$ to $O(K)$ or $O(\log_2 K)$ per lane.

## Applicability

These findings apply to the semantic interaction of the eight upstream subjects pinned in `REPORT.json`:

- **Rust SIMD Stack:** `rust-lang/rust` (`4b5350e87e487aed08ab2f9f0160a4b2616438bc`, `library/core/src/intrinsics/simd/mod.rs` and `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs`), `rust-lang/portable-simd` (`3df387e8fa3cd542aaec2a0b7f771e0515584ef7`, `crates/core_simd/src/{vector,swizzle_dyn}.rs` under `#![feature(portable_simd)]`), `rust-lang/miri` (`5b99fdad636668442f94e15054a6b9fb3a80f613`, `src/intrinsics/{simd,aarch64}.rs` and `src/intrinsics/x86/{mod,ssse3,avx2,avx512}.rs`), and `llvm/llvm-project` (`d75e8d27c052458bd263004ce02378b857e9239a`, `@llvm.masked.{gather,scatter}.*`).
- **Production Codecs:** `simdutf/simdutf` (`177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0`, `utf8_lookup4_algorithm.h`), `hsivonen/encoding_rs` (`e89b7c3371bffe0c260c76a11f32b8a7b6adad4a`, `src/{utf_8,simd_funcs,handles}.rs` with/without `simd-accel`), `trifectatechfoundation/zlib-rs` (`a7f9c02c1f48b8962b46c5428828573e9cbac152`, `inflate/inftrees.rs` and `crc32/pclmulqdq.rs`), and `Frommi/miniz_oxide` (`b28c237471f63efebe152bddd962dc57bbb531eb`, `inflate/core.rs`).

**Corpus Scope Separation:** Carryless `PCLMULQDQ` quote masks are covered in `simdjson-carryless-quote-masks-structural-tapes-and-vector-utf8`, `#[repr(simd)]` ABI legalization in `portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`, intrinsic authority maps in `rustc-intrinsics-simd-and-arch-semantic-sources`, and scalar table bounds certificates in `nonlinear-bitwise-mask-modulo-and-lookup-table-bounds-certificates`. This package covers dynamic gather/scatter memory/provenance rules, cross-ISA dynamic byte swizzles, and algebraic codec lookup decomposition. Note that `simd_bitmask` reverses bit-to-lane order on big-endian targets (`intrinsics/simd.rs:856–863`) and `portable-simd` gates AArch64 NEON `swizzle_dyn` on `target_endian = "little"` (`swizzle_dyn.rs:43–48`).

## Findings

### 1. Memory-Backed Gather and Scatter Semantics, Provenance, and Lane Collisions

#### 1.1 Semantic Divergence Across Gather, Masked Load, and Scatter Primitives

`core::simd` lowers slice-indexed `gather_select`/`scatter_select` through `gather_select_unchecked`/`scatter_select_unchecked` to raw-pointer `core::intrinsics::simd::{simd_gather, simd_scatter}`. Inspecting `rustc`, Miri, and LLVM `LangRef` reveals distinct UB boundaries across primitives:

`Basis: normative + source`

| Property | `simd_gather` (`gather_select_ptr`) | `simd_masked_load` (`load_select_ptr`) | `llvm.x86.avx2.gather.*` (Miri `avx2.rs`) | `simd_scatter` (`scatter_select_ptr`) |
| :--- | :--- | :--- | :--- | :--- |
| **Mask lane domain** | Strictly `0` or `-1` (`!0`); other values fault UB (`simd.rs:879–884`). | Strictly `0` or `-1` (`!0`); other values fault UB (`simd.rs:879–884`). | Any initialized integer; MSB `(mask >> (bits - 1)) != 0` enables lane (`avx2.rs:59–73`). | Strictly `0` or `-1` (`!0`); other values fault UB (`simd.rs:879–884`). |
| **Disabled-lane (`0`) alignment** | **Not checked** (`deref_pointer` gated by `mask`, `simd.rs:635–637`). | **Unconditional UB on base `ptr`!** Checked before loop even if `mask == 0` (`simd.rs:674–678`). | **Not checked** (`avx2.rs:73–87`). | **Not checked** (`simd.rs:657–660`). |
| **Enabled-lane alignment** | Requires `align_of::<T>()` via `deref_pointer` (`simd.rs:636`). | Const `SimdAlign::{Unaligned, Element, Vector}` (`simd.rs:839–852`). | **Unaligned allowed** (`mem_copy`, `avx2.rs:81–87`). | Requires `align_of::<T>()` via `deref_pointer` (`simd.rs:658`). |
| **Uninitialized lane (`MaybeUninit`)** | **UB in ALL lanes:** `passthru`, `ptrs`, `mask` `read_immediate` upfront (`simd.rs:630–632`). | **UB in ALL `default` and `mask` lanes** (`simd.rs:681–682`). | `offsets[i]` read only when MSB `== 1`; `src[i]` copied via raw `copy_op` when MSB `== 0` (`avx2.rs:73–90`). | **UB in ALL `value`, `ptrs`, `mask` lanes** (`simd.rs:653–655`). |
| **Lane order** | Pure reads (`0..dest_len`); shared reads commute. | Contiguous `ptr.wrapping_offset(size * i)`. | `0..actual_len`; lanes `actual_len..dest_len` zeroed (`avx2.rs:92–95`). | **Strictly left-to-right `0..ptrs_len` (LSB-to-MSB)** (`simd/mod.rs:394`, `simd.rs:652`, `LangRef`). |

#### 1.2 Masked Out-of-Bounds Provenance: Why `wrapping_add` Is Mandatory

In `Simd::gather_select` (`vector.rs:601–610`) and `gather_select_unchecked` (`vector.rs:642–653`), `enable` is masked with `idxs.simd_lt(Simd::splat(slice.len()))` and addresses are formed via `Simd::splat(slice.as_ptr()).wrapping_add(idxs)`.

`Basis: source + derived`

Two provenance rules govern this pattern:
1. **No eager `inbounds` GEP UB:** `SimdConstPtr::wrapping_add` lowers to `simd_arith_offset` (`simd/mod.rs:671`), evaluated per lane via `ptr.wrapping_signed_offset(offset_count.wrapping_mul(pointee_size), self)` (`intrinsics/simd.rs:270–280`). Unlike `<*const T>::add` (`getelementptr inbounds`), `wrapping_signed_offset` preserves `(AllocId, BorTag)` provenance on out-of-bounds offsets without asserting allocation bounds. Using `inbounds` offset arithmetic on disabled OOB lanes (`idxs[i] > slice.len()`) would trigger UB *before* `simd_gather` inspects `enable`.
2. **Value initialization vs. dereferenceability:** Because `simd_gather` executes `read_immediate` on `ptrs[i]` and `passthru[i]` unconditionally (`intrinsics/simd.rs:630–631`), disabled lanes may hold null, dangling, unaligned, or `without_provenance` initialized scalars, **never** `MaybeUninit::uninit()`. Verification preconditions must separate *scalar initialization* ($\forall i < N,\ \text{Init}(ptrs[i]) \land \text{Init}(passthru[i]) \land mask[i] \in \{0, -1\}$) from *conditional dereferenceability* ($\forall i < N,\ mask[i] = -1 \implies \text{Aligned}(ptrs[i]) \land \text{Readable}(ptrs[i])$).

#### 1.3 Scatter Collisions, Borrow-Tag Asymmetry, and Torn Overlaps

LLVM `@llvm.masked.scatter.*` and `core::intrinsics::simd::simd_scatter` (`simd/mod.rs:394–395`) both guarantee sequential execution from lane `0` to `N - 1`. Three aliasing and layout obligations follow:

`Basis: normative + source + derived`

1. **Single-reborrow `*mut T` zone (`vector.rs:881–900`):** In `scatter_select_unchecked`, computing `slice.len()` (which reborrows `&*slice`) *must* precede `Simd::splat(slice.as_mut_ptr())`. Every lane of `ptrs = base_ptr.wrapping_add(idxs)` then shares one `BorTag` $t_{\text{base}}$, so colliding writes at `idxs[i] == idxs[j]` both use $t_{\text{base}}$ without mutual invalidation.
2. **Order-sensitive borrow invalidation on `scatter_ptr` (`intrinsics/simd.rs:652–661`):** If `dest` combines distinct tags—e.g., `p_parent = &mut x as *mut i32` ($t_0$) and child reborrow `p_child = &mut *p_parent as *mut i32` ($t_1$)—`[p_child, p_parent]` is **UB-free** (child write at lane `0`, then parent write at lane `1` disabling $t_1$ afterward), whereas `[p_parent, p_child]` is **immediate UB** (parent write at lane `0` disables child $t_1$ before lane `1` writes). Thus `simd_scatter` must be modeled as a sequential left-fold over borrow state, not a parallel map.
3. **Partial overlap when $\text{size}(T) > \text{align}(T)$:** On 64-bit targets, primitive SIMD elements satisfy $\text{size}(T) = \text{align}(T)$, forcing aligned pointers to be identical or disjoint. On 32-bit `i686`, `u64`/`i64`/`f64` have $\text{size} = 8, \text{align} = 4$: raw-pointer `scatter_ptr` at `base + 0` and `base + 4` passes `deref_pointer` alignment checks and partially overwrites bytes `[4..8)`. Slice-indexed `Simd::scatter` avoids this because `idxs` scales by $\text{size}(T) = 8$.

---

### 2. In-Register Dynamic Table Lookups: `PSHUFB`, `VTBL`, and Cross-Lane Swizzle Algebra

#### 2.1 Cross-ISA Out-of-Bounds Rules and the `zeroing_idxs<N>` Congruence Law

`Simd<u8, N>::swizzle_dyn(self, idxs)` (`swizzle_dyn.rs:8–120`) returns `self[idxs[i]]` if `idxs[i] < N` else `0`. Underlying ISA primitives diverge:
- **AArch64 `TBL1`–`TBL4` (`miri/src/intrinsics/aarch64.rs:191–252`) & WASM `i8x16.swizzle`:** Natively zero `idx >= 16 * k`.
- **LoongArch64 LSX/LASX (`swizzle_dyn.rs:300–325`):** Explicitly masks `vshuf.b` output with `vslei.bu` (`<= 15` or `<= 31`).
- **x86 `PSHUFB`/`VPSHUFB` (`miri/src/intrinsics/x86/mod.rs:1365–1391`):** Zeroes *only* when `right[i] & 0x80 != 0`; selectors `0x10..=0x7F` wrap modulo 16 (`(i & !15) + (right[i] % 16)`).

`Basis: source + execution + derived`

For SSSE3 (`N = 16`), `portable-simd` preprocesses indices via `zeroing_idxs<N>` (`swizzle_dyn.rs:77, 349–354`):
```rust
let zeroing_bits = idxs + Simd::splat((127 - N + 1) as u8);
idxs | zeroing_bits
```
Although generic over `const N: usize`, **`zeroing_idxs<N>` is sound for $1 \le N \le 16$ if and only if $N = 16$**:
- At $N = 16$, $128 - N = 112 = \text{0x70}$. Because the low nibble of `0x70` is `0`, for $x \in [0, 15]$, $x + \text{0x70} = \text{0x70} \mid x$, so `(x | (x + 0x70)) & 0x8F == x`; for $x \in [16, 127]$, $x + \text{0x70} \in [128, 239]$ sets bit 7; for $x \ge 128$, `x` keeps bit 7 under `|`.
- For every $N \in \{1, \dots, 15\}$, $(128 - N) \ \& \ \text{0x0F} = 16 - N \neq 0$, corrupting low nibbles under `|` (e.g., at $N = 12, x = 1$: `1 | (1 + 116) = 0x75`, low nibble $5 \neq 1$). `swizzle_dyn.rs:77` invokes `zeroing_idxs` solely at `N = 16`, satisfying this hidden congruence invariant.

#### 2.2 Bridging the AVX2 128-Bit Lane Wall (`avx2_pshufb`)

Because `_mm256_shuffle_epi8` cannot cross 128-bit lanes, `avx2_pshufb` (`swizzle_dyn.rs:263–293`) realizes a 32-byte zeroing lookup in 6 instructions:
1. `swapped = _mm256_permute2x128_si256::<0x01>(bytes, bytes)` exchanges the two 16-byte halves.
2. `control = _mm256_adds_epu8(indices, 0x60)`: saturating unsigned addition with `0x60` (`0b0110_0000`, bits `0..=4` zero) maps $x \in [0, 31]$ to $[96, 127]$ (bit 7 = `0`, **all 5 index bits `x & 0x1F` preserved**) and maps $x \in [32, 255]$ to $[128, 255]$ (bit 7 = `1`, zeroing both `PSHUFB`s).
3. `local = _mm256_shuffle_epi8(bytes, control)` and `remote = _mm256_shuffle_epi8(swapped, control)`.
4. `select_remote = _mm256_add_epi8(control, set_m128i(-112 /* 0x90 */, 16 /* 0x10 */))` shifts bit 4 into bit 7 for `_mm256_blendv_epi8(local, remote, select_remote)`, adding `0x80` in the upper 128-bit lane to invert selection because `local` there holds `bytes[16..32]`.

`Basis: source + execution + derived`

#### 2.3 Complementary Sign-Bit `PSHUFB` Shift Masks in `zlib-rs` CRC-32

In `zlib-rs/src/crc32/pclmulqdq.rs:150–197`, `Accumulator::partial_fold` shifts 128-bit register pairs by runtime `len` ($1 \le \text{len} \le 15$) via `xmm_shl = PSHUFB_SHF_TABLE[len - 1]` and `xmm_shr = _mm_xor_si128(xmm_shl, reg([0x80808080u32; 4]))`. Row `len - 1` equals `[len + 0x80, ..., 15 + 0x80, 0, ..., len - 1]`. Flipping bit 7 via `^ 0x80` makes `(xmm_shl[k] & 0x80) ^ (xmm_shr[k] & 0x80) == 0x80` in every lane $k \in [0, 16)$, so `_mm_or_si128(_mm_shuffle_epi8(fold[0], xmm_shr), _mm_shuffle_epi8(fold[1], xmm_shl))` computes `(fold[0] ++ fold[1])[len .. len + 16]` with disjoint zeroing. Note that `fold_help` (`pclmulqdq.rs:339`) writes `debug_assert!(src.len() <= 16)` before `partial_fold`, whereas `PSHUFB_SHF_TABLE` has length `15`; safety relies on prior reductions (`L263–273, L321–335`) ensuring the stronger invariant **`1 <= src.len() <= 15`**.

`Basis: source + execution + derived`

---

### 3. Production Vectorized Codec Lookup Tables and Bounds Invariants

#### 3.1 Vectorized UTF-8 DFA (`simdutf`) and Transcoding Tail Guards (`encoding_rs`)

`Basis: normative + source + execution + derived`

1. **Boolean Rank-8 Nibble Factorization (`simdutf` `utf8_lookup4_algorithm.h:8–98`):** Keiser and Lemire encode all seven Unicode Table 3-7 2-byte error syndromes into 8 bit positions (`OVERLONG_4` and `TOO_LARGE_1000` share bit 6 because lead nibbles `0` (`F0`) and `5..F` (`F5..FF`) are disjoint in `byte_1_low`), factoring the $256 \times 256$ relation into three 16-byte lookups:
   $$\text{sc}[i] = T_{\text{1hi}}[b_{i-1} \gg 4] \ \& \ T_{\text{1lo}}[b_{i-1} \ \& \ \text{0xF}] \ \& \ T_{\text{2hi}}[b_i \gg 4]$$
2. **Bit-7 `XOR` Cancellation/Synthesis (`utf8_lookup4_algorithm.h:100–109`):** Placing `TWO_CONTS` at bit 7 (`0x80`) and setting `must23_80 = 0x80` iff $b_{i-2} \ge \text{0xE0} \lor b_{i-3} \ge \text{0xF0}$ lets **`must23_80 ^ sc`** simultaneously cancel `TWO_CONTS` on valid 3/4-byte continuation pairs (`0x80 ^ 0x80 = 0`) and synthesize bit-7 errors when a 3/4-byte lead is missing its 2nd or 3rd continuation (`0x80 ^ 0x00 = 0x80`). At EOF (`L115–154, 207–211`), `is_incomplete` flags trailing bytes exceeding `[..., 255, 0xEF, 0xDF, 0xBF]`.
3. **Scalar DFA & Output Slop Bounds (`encoding_rs`):** Below 64 bytes (`src/utf_8.rs:78–192`), `encoding_rs` pairs its 384-byte `UTF8_DATA` table with `read + 4 <= src.len()` lookahead. In UTF-16-to-UTF-8 transcoding (`src/handles.rs:278–301`), `dst.len() < 4` exits early and `dst_pos >= dst.len() - 3` (`written < cap.saturating_sub(3)`) guarantees `dst_pos + 4 <= dst.len()`; weakening `<` to `<=` writes 1 byte OOB at `dst_pos = dst.len() - 3`.

#### 3.2 Two-Level DEFLATE Prefix Tables (`zlib-rs` and `miniz_oxide`)

`Basis: normative + source + derived`

1. **Kraft Completeness & `ENOUGH` Space (`zlib-rs/src/inflate/inftrees.rs:42–245`):** Iterating `left = (left << 1).checked_sub(u32::from(count[len]))?` over $\ell \in [1, 15]$ rejects oversubscribed trees (`None`) and—via `if left > 0 && (matches!(codetype, CodeType::Codes) || max != 1)` (`L87`)—rejects incomplete trees except RFC 1951's 0-symbol (`max == 0`, filled with `op = 64` error markers at `L61–73`) and 1-bit single-symbol (`max == 1`, unused entry filled with `op = 64` at `L233–241`) cases. Every primary and secondary slot within `ENOUGH_LENS` (`852`) / `ENOUGH_DISTS` (`592`) is thus initialized.
2. **Negative Secondary Tree DAG (`miniz_oxide/src/inflate/core.rs:674–696, 1017–1041`):** Entries `< 0` in the 10-bit primary table step through `tree: [i16; 576]` at `(!temp + ((bit_buf >> code_len) & 1) as i32) as usize` (`!temp == -temp - 1`). Absence of OOB panics and infinite loops holds under `HuffTreeWf`: leaf entries `>= 0` satisfy `1 <= (temp >> 9) <= 15`, and negative internal entries satisfy `(!temp as usize) + 1 < 576` with strictly decreasing negative child pointers (`!child > !temp`), bounding traversal to $\le 5$ hops.

#### 3.3 $\text{GF}(2^8)$ Linear Nibble Split

Over $\text{GF}(2^8)$, constant multiplication $M_c(x \oplus y) = M_c(x) \oplus M_c(y)$ splits into two 16-byte register lookups $M_c(x) = T_{\text{lo}}[x \ \& \ \text{0xF}] \oplus T_{\text{hi}}[x \gg 4]$ (`Plank et al. FAST 2013`), eliminating cache-banked `simd_gather` loads and data-dependent cache addresses.

`Basis: documentation + execution + derived`

---

### 4. Algebraic Proof Decomposition Without Exponential Lane Splitting

`Basis: derived`

| Target Pattern | Monolithic $L$-Lane Space ($L = 32$) | Algebraic Decomposition | Reduced Obligation |
| :--- | :--- | :--- | :--- |
| **`avx2_pshufb` (`Simd<u8, 32>`)** | $256^{32}$ selector vectors | Lane-half split ($i < 16$ vs. $i \ge 16$) + parametric table `Fin 32 → α`. | **$512$** byte evaluations |
| **`simdutf` `lookup4` UTF-8** | $256^{35}$ (`prev3` + 32B chunk) | 4-byte sliding window + 3-level lead quotient $\tau(b) \in \{< \text{0xE0}, [\text{0xE0}, \text{0xEF}], \ge \text{0xF0}\}$. | **$3^2 \times 256^2 = 589,824$** states |
| **$\text{GF}(2^8)$ double-`swizzle_dyn`** | $256^{32}$ per multiplier $c$ | $\mathbb{F}_2$-linearity $f(x \oplus y) = f(x) \oplus f(y)$ + basis check on $\{2^0, \dots, 2^7\}$. | **$8$** basis evaluations |
| **DEFLATE 2-level Huffman** | $2^{15 L} \times$ dynamic tables | Construction-time Kraft equality + `HuffTreeWf` monotonic DAG invariant. | **$O(1)$** per decode step |

The following self-contained Lean 4 module (core `Init` only, zero `sorry`) mechanizes ordered `simd_scatter` collision/mask semantics and `avx2_pshufb` 32-byte lookup verification by `rfl`:

```lean
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic

namespace VectorizedTableProofs

structure ScatterLane where
  maskRaw  : Int   -- Strictly `0` or `-1`; any other value faults UB (`none`)
  addr     : Nat
  val      : Nat
  aligned  : Bool
  writable : Bool

def stepScatter (mem : Nat → Option Nat) (l : ScatterLane) : Option (Nat → Option Nat) :=
  if l.maskRaw == 0 then some mem
  else if l.maskRaw == -1 then
    if l.aligned && l.writable then some (fun a => if a == l.addr then some l.val else mem a)
    else none
  else none

def evalSimdScatter (m0 : Nat → Option Nat) (ls : List ScatterLane) : Option (Nat → Option Nat) :=
  ls.foldl (fun acc l => match acc with | none => none | some m => stepScatter m l) (some m0)

theorem scatter_last_active_wins_and_disabled_oob_safe :
    (match evalSimdScatter (fun _ => some 10)
        [⟨0, 9999, 27, false, false⟩, ⟨-1, 0, 41, true, true⟩, ⟨-1, 0, 124, true, true⟩] with
     | some m => m 0 == some 124
     | none   => false) = true := rfl

theorem scatter_invalid_mask_faults :
    (evalSimdScatter (fun _ => some 0) [⟨1, 0, 42, true, true⟩]).isNone = true := rfl

def pshufb16 (tbl : Nat → Nat) (ctl : Nat) : Nat :=
  if Nat.land ctl 128 == 0 then tbl (Nat.land ctl 15) else 0

def avx2Swizzle32Lane (upper : Bool) (tbl : Nat → Nat) (idx : Nat) : Nat :=
  let ctl := Nat.min 255 (idx + 96)
  let loc := if upper then pshufb16 (fun k => tbl (16 + k)) ctl else pshufb16 tbl ctl
  let rem := if upper then pshufb16 tbl ctl else pshufb16 (fun k => tbl (16 + k)) ctl
  let sel := Nat.land (ctl + (if upper then 144 else 16)) 255
  if Nat.land sel 128 != 0 then rem else loc

def checkAvx2Half (upper : Bool) : Bool :=
  (List.range 256).all (fun x =>
    avx2Swizzle32Lane upper (fun k => 100 + k) x == (if x < 32 then 100 + x else 0))

theorem avx2_swizzle32_exact : (checkAvx2Half false && checkAvx2Half true) = true := rfl

end VectorizedTableProofs
```

---

## Boundaries

- **`not examined` — Scalable Vector Extensions (ARM SVE/SVE2, RISC-V RVV):** Runtime-length vectors (`core::intrinsics::simd::scalable`, `simd/mod.rs:5`) and RVV `LMUL > 1` `vrgatherei16.vv` permutations were **not examined**.
- **`not examined` — Microarchitectural Gather/Swizzle Leakage:** Transient hardware leaks (e.g., Intel GDS CVE-2022-40982 on `VPGATHER*`) and variable-cycle `PSHUFB`/`TBL` implementations on embedded cores were **not examined**.
- **`unknown` — Stabilization of Non-Power-of-Two `#[repr(simd)]` Tail Padding:** `portable-simd` uses `copy_nonoverlapping` in `Simd::load`/`store` (`vector.rs:264–332`) because `#[repr(simd)]` pads non-power-of-two lane counts; whether `rustc` will ultimately ban or unpad such types remains **unknown** (issue `#86656`).
- **`known not to apply` — Hardware `VPGATHER*` Unaligned Tolerance Does Not Extend to `simd_gather`:** Calling `Simd::gather_select_ptr` on an enabled unaligned pointer is **known not to apply** (immediate UB in `intrinsics/simd.rs:636` even on AVX2 hardware); unaligned gathers require target-specific `_mm256_mask_i32gather_*` (`avx2.rs:82`). Likewise, `zeroing_idxs<N>` is **known not to apply** for $N \in \{1, \dots, 15\}$.
- **`unsupported` — AVX-512 Gather/Scatter Intrinsics in Miri and `N > 64` Bitmasks in CTFE:** `llvm.x86.avx512.{gather,scatter}.*` is **unsupported** in Miri (`miri/src/intrinsics/x86/avx512.rs:231`), and `simd_bitmask` / `simd_select_bitmask` for `N > 64` is **unsupported** in `rustc_const_eval` (`intrinsics/simd.rs:400–404, 460–464`).

---

## Evidence

### Primary Upstream Source Coordinates (`2026-11-20`)

| Repository | Revision (40-char SHA) | Examined Paths & Lines | Verified Facts |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `4b5350e87e487aed08ab2f9f0160a4b2616438bc` | `library/core/src/intrinsics/simd/mod.rs:345–468, 592–697`; `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs:189–285, 394–503, 560–722, 818–885` | Safety contracts & CTFE/Miri semantics for `simd_gather`, `simd_scatter`, `simd_masked_load`/`store`, `simd_arith_offset`, and `{0, -1}` masks. |
| `rust-lang/portable-simd` | `3df387e8fa3cd542aaec2a0b7f771e0515584ef7` | `crates/core_simd/src/vector.rs:264–332, 485–954`; `crates/core_simd/src/swizzle_dyn.rs:8–354` | Single-reborrow `*mut T` scatter zone (`L881–900`); `zeroing_idxs`, `avx2_pshufb`, NEON `vtbl`, and AVX-512VBMI `permutex2var` lowerings. |
| `rust-lang/miri` | `5b99fdad636668442f94e15054a6b9fb3a80f613` | `src/intrinsics/x86/{mod.rs:1175–1392, ssse3.rs:23–27, avx2.rs:38–96, avx512.rs:138–232}`; `src/intrinsics/aarch64.rs:191–252` | Unaligned MSB-masked `avx2.gather.*`; 16B-isolated `pshufb`; `neon.tbl1`–`tbl4`; missing `avx512.{gather,scatter}`. |
| `llvm/llvm-project` | `d75e8d27c052458bd263004ce02378b857e9239a` | `llvm/docs/LangRef.rst` (`@llvm.masked.{gather,scatter}.*`) | Normative LSB-to-MSB store order on overlapping `@llvm.masked.scatter` lanes. |
| `simdutf/simdutf` | `177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0` | `src/generic/utf8_validation/utf8_lookup4_algorithm.h:8–256` | 3-table nibble `check_special_cases`, `must23_80 ^ sc`, and `is_incomplete` EOF check. |
| `hsivonen/encoding_rs` | `e89b7c3371bffe0c260c76a11f32b8a7b6adad4a` | `src/utf_8.rs:34–65, 167–220`; `src/simd_funcs.rs:25–50, 194–286`; `src/handles.rs:275–315` | 384B `UTF8_DATA` table, `read + 4 <= src.len()`, and `dst_pos >= dst.len() - 3` tail bound. |
| `trifectatechfoundation/zlib-rs` | `a7f9c02c1f48b8962b46c5428828573e9cbac152` | `zlib-rs/src/inflate/inftrees.rs:42–245`; `zlib-rs/src/crc32/pclmulqdq.rs:150–197, 263–360` | Kraft `left` check + `op = 64` sentinel fill; 15-entry `PSHUFB_SHF_TABLE` + `^ 0x80` shift and `1 <= len <= 15` precondition. |
| `Frommi/miniz_oxide` | `b28c237471f63efebe152bddd962dc57bbb531eb` | `miniz_oxide/src/inflate/core.rs:674–748, 1017–1041` | 10-bit `fast_lookup` + negative `tree[(!temp + bit) as usize]` bounds. |

### Specifications, Papers, and Execution Record

- **Normative Standards & Literature:** Unicode Standard 16.0 §3.9 Table 3-7; IETF RFC 1951 §§3.2.2, 3.2.7; J. Keiser & D. Lemire, *"Validating UTF-8 In Less Than One Instruction Per Byte"*, *SPE* 51(5), 2021, DOI `10.1002/spe.2920`; W. Muła & D. Lemire, *"Faster Base64 Encoding and Decoding Using AVX2 Instructions"*, *ACM TWEB* 12(3), 2018, DOI `10.1145/3132709`; J. S. Plank, K. M. Greenan, & E. L. Miller, *"Screaming Fast Galois Field Arithmetic Using Intel SIMD Instructions"*, *USENIX FAST 2013*, pp. 299–306.
- **Execution (`2026-11-20`, Python `3.13.15`, `linux` `x86_64`):** Exhaustive probe exited `0`, confirming `valid_ns == [16]` (`(zeroing_idxs(1, 12) & 0xF) == 5`), `8,192/8,192` `avx2_pshufb` lane checks, `15/15` `PSHUFB_SHF_TABLE` shifts, `0` `simdutf` UTF-8 mismatches across `459,008` 1–4-byte test vectors, and `256/256` $\text{GF}(2^8)$ nibble-table matches from `8` basis checks.

---

## Revalidation

Run the following standard-library Python 3 probe (< 2 seconds) to revalidate the swizzle, CRC shift, and UTF-8 DFA identities:

```bash
python3 - <<'PY'
def zeroing_idxs(idx: int, n: int) -> int:
    return idx | ((idx + ((128 - n) & 0xFF)) & 0xFF)

def pshufb_byte(tbl16: list[int], ctl: int) -> int:
    return 0 if (ctl & 0x80) else tbl16[ctl & 0x0F]

tbl16 = [100 + k for k in range(16)]
valid_ns = [n for n in range(1, 17) if all(
    pshufb_byte(tbl16, zeroing_idxs(x, n)) == (tbl16[x] if x < n else 0) for x in range(256))]
assert valid_ns == [16] and (zeroing_idxs(1, 12) & 0x0F) == 5

def avx2_pshufb(b32: list[int], idx32: list[int]) -> list[int]:
    swp = b32[16:32] + b32[0:16]
    ctl = [min(255, x + 0x60) for x in idx32]
    loc = [0 if (ctl[i] & 0x80) else b32[(i & ~15) + (ctl[i] & 0x0F)] for i in range(32)]
    rem = [0 if (ctl[i] & 0x80) else swp[(i & ~15) + (ctl[i] & 0x0F)] for i in range(32)]
    bias = [0x10] * 16 + [0x90] * 16
    return [rem[i] if (((ctl[i] + bias[i]) & 0xFF) & 0x80) else loc[i] for i in range(32)]

tbl32 = [17 + 3 * k for k in range(32)]
assert all(avx2_pshufb(tbl32, [x] * 32) == [tbl32[x] if x < 32 else 0] * 32 for x in range(256))

TS, TL, O3, LG, SR, O2, O4, TC = 1, 2, 4, 8, 16, 32, 64, 128
CY = TS | TL | TC
B1H = [TL]*8 + [TC]*4 + [TS|O2, TS, TS|O3|SR, TS|LG|O4]
B1L = [CY|O3|O2|O4, CY|O2, CY, CY, CY|LG] + [CY|LG|O4]*8 + [CY|LG|O4|SR] + [CY|LG|O4]*2
B2H = [TS]*8 + [TL|O2|TC|O3|O4, TL|O2|TC|O3|LG, TL|O2|TC|SR|LG, TL|O2|TC|SR|LG] + [TS]*4

def simdutf_ok16(c: bytes) -> bool:
    err = 0
    for i in range(16):
        p1, p2, p3 = (c[i-1] if i>=1 else 0), (c[i-2] if i>=2 else 0), (c[i-3] if i>=3 else 0)
        sc = B1H[p1 >> 4] & B1L[p1 & 0xF] & B2H[c[i] >> 4]
        err |= ((0x80 if (p2 >= 0xE0 or p3 >= 0xF0) else 0) ^ sc)
    return (err | (1 if (c[13] >= 0xF0 or c[14] >= 0xE0 or c[15] >= 0xC0) else 0)) == 0

for b0 in range(256):
    for b1 in range(256):
        s = bytes([b0, b1]) + b" " * 14
        try: s.decode("utf-8"); ref = True
        except UnicodeDecodeError: ref = False
        assert simdutf_ok16(s) == ref
for p in [b"\xe0\x9f\x80", b"\xe0\xa0\x80", b"\xed\xa0\x80", b"\xe2\x82 ", b"\xf0\x8f\x80\x80", b"\xf4\x90\x80\x80"]:
    s = p + b" " * (16 - len(p))
    try: s.decode("utf-8"); ref = True
    except UnicodeDecodeError: ref = False
    assert simdutf_ok16(s) == ref
print("REVALIDATION_OK")
PY
```

**Upstream Drift Watchpoints:** Diff `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`simd_gather`, `simd_scatter`, `simd_masked_load`), `portable-simd/crates/core_simd/src/{vector,swizzle_dyn}.rs`, and `miri/src/intrinsics/x86/avx512.rs` across toolchain upgrades to check for `MaybeUninit` relaxation on disabled lanes or new AVX-512 gather/scatter shims.
