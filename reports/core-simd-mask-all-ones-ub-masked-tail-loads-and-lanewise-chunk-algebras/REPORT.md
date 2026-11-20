# Rust `core::simd` Mask Validity UB, Masked Tail-Load Alignment Semantics, and Lanewise Chunk Algebras in 3-Axiom Lean 4

## Summary

Rust's `#[repr(simd)]` intrinsics (`core::intrinsics::simd`) and `core::simd` (`portable-simd`) enforce three operational invariants that diverge from scalar `[bool; N]` and slice-indexing intuition and must be modeled explicitly by any sound MIR verifier:

1. **Signed `{-1, 0}` Mask-Lane Validity UB (`1` Is Immediate Undefined Behavior):** Every mask-consuming SIMD intrinsic (`simd_select`, `simd_masked_load`, `simd_masked_store`, `simd_gather`, `simd_scatter`, `simd_bitmask`, `simd_reduce_all`, `simd_reduce_any`) converts each integer mask lane via signed `to_int(size)` (`IntrinsicSimd.lean:75–80`, `rustc_const_eval` `simd.rs:889–901`). Only `0` (`false`, all-zero bits) and `-1` (`true`, all-one bits `2^w - 1`) are valid; any other bit pattern—including unsigned `1` (`0x01`, such as a raw byte transmuted from `[bool; N]`)—triggers immediate Undefined Behavior (`FaultKind.undefined`). In `core::simd::Mask::from_simd_unchecked` (`masks.rs:199–205`), UB fires at construction via `core::intrinsics::assume(<T as PrivateMethods>::valid(value))`. This invariant is forced by hardware/codegen non-confluence: `rustc_codegen_llvm` (`intrinsic.rs:2131–2143`) and x86 `vpblendvb`/`vpmovmskb` (`jasmin` `word.v:1855–1866`) inspect the **most significant bit (MSB)** of each lane, whereas `Mask::to_array` (`masks.rs:186–189`) masks the **least significant bit (LSB, `& 1`)** and NEON `vbsl` / `Mask::not` (`masks.rs:650`) operate **bitwise** across all `w` bits. The two-element set `{0, 2^w - 1}` is the unique fixed point on which MSB extraction, LSB truncation, and bitwise selection commute.
2. **Unconditional Base-Pointer Alignment vs. Inactive-Lane OOB Exemption in `simd_masked_load` / `simd_masked_store`:** Both `rustc_const_eval` (`simd.rs:666–670, 696–700`) and `lean-miri` (`IntrinsicSimd.lean:444–445`) run `checkPointerAlignment` on `ptr` against `SimdAlign` (`Unaligned = 1`, `Element = align_of::<T>()`, `Vector = align_of::<Simd<T, N>>()`) **unconditionally before reading any mask lane**, and `rustc_codegen_llvm` (`intrinsic.rs:2769–2773`) attaches an `align` parameter attribute to `Argument(0)` of `@llvm.masked.load` / `@llvm.masked.store`. Passing a misaligned pointer with an all-`false` mask (`[0; N]`) is therefore immediate UB—exposing an upstream contract discrepancy in `core::simd::Simd::load_select_ptr` and `store_select_ptr` (`vector.rs:447–464, 705–719`), whose `# Safety` comments restrict preconditions to *enabled* elements despite delegating to `simd_masked_load<..., { SimdAlign::Element }>`. Conversely, once base alignment holds, lane addresses use `ptr.wrapping_offset` (`IntrinsicSimd.lean:454, 460`) and dereference memory **only** when `mask[i] == -1`, exempting disabled tail lanes (`mask[i] == 0`) from bounds and provenance checks. By contrast, `simd_gather` and `simd_scatter` (`IntrinsicSimd.lean:424–434`) check alignment and bounds strictly on active (`-1`) pointer lanes.
3. **Endian-Reversed Bitmasks and 64-Lane Ceiling:** `simd_bitmask` and `simd_select_bitmask` (`IntrinsicSimd.lean:168–197, 346–383`; `simd.rs:386–495, 872–879`) pack `N` lanes into `ceil(N / 8) * 8` bits (throwing `FaultKind.unsupported` when `bitmask_len > 64`), mapping lane `i` to bit `i` on little-endian targets and bit `N - 1 - i` on big-endian targets. `core::simd::Mask::to_bitmask` (`masks.rs:302–337`) restores canonical lane-`i`-at-bit-`i` ordering on big-endian targets by resizing to `M ∈ {8, 16, 32, 64}` and applying `uM::reverse_bits`.
4. **Zero-TCB 3-Axiom Lean 4 Strip-Mining Algebra (`SimdVec ↔ ListChunks`):** Outside the Trusted Computing Base (`theory/`), `#[repr(simd)]` vectors lift onto unbundled `List α` values with propositional length invariants (`v.length = N`), avoiding dependent `Fin N` / `HEq` proof-term blowup while satisfying `TrustedBoundary.lean`'s 51-module `Init.*` ceiling, pure tactic allowlist, prefix bitwise/shift syntax rules, Statement-Origin Separation, and constructive `{propext, Quot.sound}` axiom footprint. Composing `slice::as_chunks::<N>()` (`slice/mod.rs:1399–1409`) with a prefix-masked `simd_masked_load` tail reduces vectorized loop proofs to single-chunk lanewise homomorphism (`evalVecChunk c = List.map f c`) plus tail-mask prefix soundness.

## Applicability

These findings govern operational semantics, compiler lowering, and deductive verification across the eight pinned subjects in `REPORT.json`:

- **Compiler intrinsics, portable library, and LLVM backend (`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`):** Covers `core::intrinsics::simd` (`library/core/src/intrinsics/simd/mod.rs`), `core::simd` (`library/portable-simd/crates/core_simd/src/{masks.rs, vector.rs}`), `core::slice::as_chunks` (`library/core/src/slice/mod.rs`), CTFE/Miri shared SIMD evaluation (`compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs`), and LLVM IR intrinsic codegen (`compiler/rustc_codegen_llvm/src/intrinsic.rs`).
- **Dynamic and mechanized MIR reference interpreters (`rust-lang/miri` @ `7fa591d7d4dd9af8154becbc8332f8096f8323b1` and `proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Covers `src/intrinsics/simd.rs`, `Miri/Interpreter/IntrinsicSimd.lean`, and `Miri/Interpreter/IntrinsicX86/Chunks.lean`.
- **Zero-TCB Lean 4 verification boundary (`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` and `leanprover/lean4` `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`):** Covers untrusted `SourceRole.theory` modules compiled under `trusted/audit/TrustedBoundary.lean` (`"preflight"` and `"audit"`, lines 442–596) over the 51 locked `Init.*` modules in `trusted/lean/foundation-lock.json` and anchored via `Trusted.MirSemantics`.
- **Cryptographic SIMD comparators (`microsoft/SymCrypt` @ `286762b7730e2b780678f5ab11fef2b1bad639e0`, `jasmin-lang/jasmin` @ `8c3279973a89afd969e50301f71563bb40d55724`, and `formosa-crypto/libjade` @ `89c38602783d9c90dda11a9b8053295a8a088597`):** Compares multi-target XMM/NEON implementations (`SymCRust/src/aes/{aes_xmm.rs, aes_neon.rs}`, `SymCRust/proof/Symcrust.lean`) and Jasmin's Coq sub-word vector/byte-array model (`proofs/lang/word.v`, `proofs/lang/warray_.v`).

**Prior Corpus Coverage:** Earlier packages examine `rustc` SIMD intrinsic catalogs (`rustc-intrinsics-simd-and-arch-semantic-sources`), ABI legalization (`portable-simd-repr-simd-legalization-and-cross-arch-cost-certificates`), floating-point reassociation (`ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`), and inline assembly SIMD (`rust-inline-assembly-contracts-relocations-and-simd-correspondence`). This report focuses on `{-1, 0}` mask UB, `simd_masked_load`/`store` alignment-vs-OOB polarity, `load_select_ptr`'s contract gap, and Pass-1 Lean 4 chunk algebras.

## Findings

### 1. Signed `{-1, 0}` Mask-Lane Validity and Hardware/Codegen MSB-vs-LSB Non-Confluence

`Basis: normative + source + derived`

In Rust's `#[repr(simd)]` semantics, comparison intrinsics (`simd_eq`, `simd_ne`, `simd_lt`, `simd_le`, `simd_gt`, `simd_ge`) output an integer vector `U` of matching lane count and lane byte width, encoding `false` as `0` and `true` as signed `-1` (`!0`). In `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, lines 881–901) and `Miri/Interpreter/IntrinsicSimd.lean` (`proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, lines 75–81):

```lean
def elementToBool [PointerProvenance P] (h : IntrinsicSimdHooks P S C V) (choice : C) (value : RvalueImmTy P) : RvalueM S Bool := do
  let _ ← h.floatOps.integerKindOf choice value.layout.ty
  let value ← liftResult ((← scalar value).toInt value.layout.layout.size |>.mapError ScalarOps.scalarError)
  if value == 0 then pure false else if value == -1 then pure true
  else ub "each SIMD mask element must be all-zero or all-one bits"
```

`elementToBool` runs on every mask-consuming intrinsic (`simd_reduce_any`, `simd_reduce_all`, `simd_select`, `simd_bitmask`, `simd_gather`, `simd_scatter`, `simd_masked_load`, `simd_masked_store`), calling `.toInt` even when the mask vector has an *unsigned* lane type (`Simd<u8, N>` or `Simd<u32, N>`, accepted by `mod.rs:367, 425, 633`). At width $w \ge 2$, signed `-1` corresponds uniquely to unsigned $2^w - 1$; passing unsigned `1` (`0x01`) yields `toInt = 1` and faults with `StepError.undefinedBehavior`.

In `core::simd` (`library/portable-simd/crates/core_simd/src/masks.rs:73–85, 157–205`), `Mask::from_simd_unchecked` injects UB even earlier via `core::intrinsics::assume(<T as PrivateMethods>::valid(value))`, whereas `Mask::from_array(array: [bool; N])` (`L165–169`) `transmute_copy`s `[bool; N]` to `[u8; N]` and evaluates `simd_ne(Simd::from_array(bytes), Simd::splat(0u8))` to widen `0x01` to `0xFF` (`-1i8`).

**Architectural Cause:** Comparing `rustc_codegen_llvm`, `core_simd`, and `jasmin` shows why `1` cannot be admitted as a truthy mask lane:

| Consumer / Lowering Site | Source Location | Lane Bit Operation ($w \ge 8$) | $m = 0$ | $m = 2^w - 1$ (`-1`) | Invalid $m = 1$ (`0x01`) | `!m` (`m ^ -1` = `0xFE`) |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: |
| `rustc_codegen_llvm` `vector_mask_to_bitmask` | `intrinsic.rs:2131–2143` | `trunc(lshr(m, w - 1))` to `i1` (**MSB**) | `0` | `1` | **`0` (`false`)** | **`1` (`true`)** |
| Jasmin x86 `movemask` / `blendv` (`vpblendvb`) | `jasmin` `word.v:1855–1866` | `map msb (split_vec ve m)` (**MSB**) | `false` | `true` | **`false`** | **`true`** |
| `core::simd::Mask::to_array` | `masks.rs:186–189` | `(simd_cast::<i8>(m) & 1)` (**LSB**) | `0` | `1` | **`1` (`true`)** | **`0` (`false`)** |
| ARM NEON `vbsl` / bitwise blend | `(m & yes) \| (!m & no)` | Per-bit multiplex across all $w$ bits | `no` | `yes` | **Bit 0 `yes`, `1..w-1` `no`** | **Bit 0 `no`, `1..w-1` `yes`** |

Solving $\mathrm{msb}_w(m) = \mathrm{lsb}_w(m)$ and $\forall j < w,\, \mathrm{bit}_j(m) = \mathrm{lsb}_w(m)$ yields $m \in \{0, 2^w - 1\}$ uniquely.

---

### 2. Unconditional Base Alignment vs. Inactive-Lane OOB Exemption in `simd_masked_load` and `simd_masked_store`

`Basis: normative + documentation + source + derived`

#### 2.1 Four-Phase Operational Execution

In `Miri/Interpreter/IntrinsicSimd.lean` (`L157–167, 434–462`) and `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`L655–714, 834–870`), `simd_masked_load<V, U, T, const ALIGN: SimdAlign>(mask, ptr, val)` and `simd_masked_store` execute in four phases:

1. **Operand Projection (`IntrinsicSimd.lean:235, 435–443`):** Force destination allocation, verify `#[repr(simd)]` layout and equal lane counts `destLen == maskLen == len`, and extract `ptr` via `toPointer` without dereferencing it.
2. **Unconditional Base-Pointer Alignment Check (`IntrinsicSimd.lean:444–445, 157–167`; `simd.rs:666–670, 855–869`):** Decode `ALIGN : SimdAlign` (`Unaligned = 0` $\to 1$, `Element = 1` $\to \text{align\_of::\textless T\textgreater()}$, `Vector = 2` $\to \text{align\_of::\textless Simd\textless T, N\textgreater\textgreater()}$) and call `checkAlign ptr align` **before** entering the lane loop—even if `mask` is `[0; N]`. Likewise, `rustc_codegen_llvm` (`intrinsic.rs:2677–2688, 2764–2774`) emits `@llvm.masked.load` / `@llvm.masked.store` with `CreateAlignmentAttr(bx.llcx, alignment)` on `Argument(0)` (`ptr`), making misaligned `ptr` immediate LLVM IR UB even on a `zeroinitializer` mask.
3. **Unconditional Mask & Passthrough Immediate Reads (`IntrinsicSimd.lean:446–451`; `simd.rs:672–677`):** Every lane `i ∈ 0..N` reads `masks[i]` and `values[i]` via `readImmediate` and validates `masks[i] ∈ {0, -1}` via `elementToBool`.
4. **Active-Lane-Only Wrapping-Offset Dereference (`IntrinsicSimd.lean:451–462`; `simd.rs:677–686, 706–713`):** Only when `masks[i] == -1` does execution compute `ptr.wrapping_offset(elem_size * i)` (wrapping arithmetic, *not* `inbounds` `BinOp::Offset`) and access `ptr_to_mplace_unaligned`. Disabled lanes (`masks[i] == 0`) perform **zero** pointer arithmetic or memory dereference, legally permitting `[ -1, -1, -1, 0 ]` tail loads on a 3-element (`12`-byte) `[u32; 3]` allocation where lane `3` (`+12..+16`) lies outside the allocation.

#### 2.2 Contrast With `simd_gather` / `simd_scatter` and the `load_select_ptr` Contract Discrepancy

Unlike `simd_masked_load`, `simd_gather` and `simd_scatter` (`IntrinsicSimd.lean:416–434`, `simd.rs:611–654`) take a pointer vector `Simd<*const T, N>`, perform **no** upfront vector/base alignment check, and call `deref_pointer` (checking `align_of::<T>()` and bounds) strictly on lanes where `mask[i] == -1` (committing overlapping `simd_scatter` writes left-to-right `0..N`).

In `library/portable-simd/crates/core_simd/src/vector.rs` (`L447–464` and `705–719`), `Simd::load_select_ptr` and `store_select_ptr` state:

```rust
/// # Safety
/// Enabled `ptr` elements must be safe to read as if by `core::ptr::read`.
pub unsafe fn load_select_ptr(
    ptr: *const T, enable: Mask<<T as SimdElement>::Mask, N>, or: Self,
) -> Self {
    unsafe {
        core::intrinsics::simd::simd_masked_load::<_, _, _, { SimdAlign::Element }>(
            enable.to_simd(), ptr, or,
        )
    }
}
```

At `ptr = core::ptr::without_provenance::<u32>(1)` and `enable = Mask::splat(false)`, zero lanes are enabled—satisfying the `# Safety` comment vacuously—yet `simd_masked_load<..., { SimdAlign::Element }>` triggers immediate alignment UB in CTFE, Miri, and LLVM! By contrast, safe `Simd::load_select(slice: &[T], ...)` (`vector.rs:410–419`) is sound even on `&[]` because every valid `&[T]` guarantees `slice.as_ptr().is_aligned()`. Formal specs for `load_select_ptr` / `store_select_ptr` must require `ptr.addr() % align_of::<T>() == 0` unconditionally.

---

### 3. Endian-Indexed Bitmasks, 64-Lane Ceiling, and Crypto SIMD Comparators

`Basis: normative + source`

1. **`simd_bitmask` and `simd_select_bitmask` (`mod.rs:592–660`, `IntrinsicSimd.lean:168–197, 346–383`, `simd.rs:386–495, 872–879`):** Both intrinsics round `N` up to $B = \lceil N / 8 \rceil \cdot 8$ bits, throwing `FaultKind.unsupported` if $B > 64$. Because `rustc_codegen_llvm` (`intrinsic.rs:2468–2469`) bitcasts `<N x i1>` directly to `iN`, lane `i` maps to bit `i` on little-endian targets and bit `N - 1 - i` on big-endian targets. `Mask::to_bitmask` (`masks.rs:9–30, 302–337`) normalizes big-endian bit order by resizing `Mask<T, N>` to $M \in \{8, 16, 32, 64\}$ before calling `simd_bitmask::<_, uM>` and `uM::reverse_bits()`.
2. **Comparison With `SymCRust` and `Jasmin`:** In `microsoft/SymCrypt` (`286762b7730e2b780678f5ab11fef2b1bad639e0`), `SymCRust/proof/Symcrust.lean` (`L24–95`) extracts scalar ML-KEM arrays via Aeneas as length-bundled `Array U16 256#usize`, while XMM/NEON AES-GCM modules (`SymCRust/src/aes/aes_xmm.rs:31–126`, `aes_neon.rs:24–116`, `README.md:61–64`) use `core::arch` `__m128i` / `uint8x16_t` intrinsics (`_mm_loadu_si128`, `vld1q_u8`) outside portable extraction. Jasmin (`jasmin@8c3279973a89`, `word.v:1786–1866, 2304–2306`; `warray_.v:25–153`; Almeida et al., CCS 2017, DOI `10.1145/3133956.3134078`) factors SIMD instructions via `split_vec` / `make_vec` over flat `word U256` integers and byte-indexed `WArray`. Under Lean 4's Pass-1 kernel, keeping `SimdVec` as unbundled `List α` (bridged to bytes only at memory boundaries) avoids both dependent `Fin N` `HEq` terms and `2^256` division/modulo WHNF blowup.

---

### 4. Pass-1 3-Axiom Lean 4 Lanewise Chunk Algebra (`SimdVec ↔ ListChunks`)

`Basis: source + derived`

Under `joshlf/anneal`'s `TrustedBoundary.lean` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`, `L442–596`), `theory/` modules must start with `prelude`, import only from the 51 locked `Init.*` modules in `trusted/lean/foundation-lock.json`, use only allowlisted pure tactics, avoid banned operator notations (`&&&`, `|||`, `^^^`, `<<<`, `>>>`, `^`, unary `-x`, `/`, `%`, `|>`), contain zero `._unsafe_rec` or `termination_by` clauses, depend only on `{propext, Quot.sound, Classical.choice}`, and obey Statement-Origin Separation. The self-contained Pass-1 Lean 4 (`v4.34.1`) module below mechanizes `{-1, 0}` mask validity, `SimdMaskedAccessSafe`, endian `packBitmask`, and the constructive (`{propext, Quot.sound}`-only) strip-mining homomorphism theorem `simd_stripMine_map_homomorphism`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Option.Basic

namespace Anneal.Simd.LaneAlgebra

inductive SimdAlignMode where
  | unaligned
  | element (elemAlignLog2 : Nat)
  | vector  (vecAlignLog2 : Nat)

def requiredAlignMask : SimdAlignMode → Nat
  | .unaligned   => 0
  | .element lg2 => Nat.shiftLeft 1 lg2 - 1
  | .vector  lg2 => Nat.shiftLeft 1 lg2 - 1

inductive EndianKind where
  | little
  | big

def allOnesBits (widthBits : Nat) : Nat :=
  Nat.shiftLeft 1 widthBits - 1

def encodeMaskLane (widthBits : Nat) (b : Bool) : Nat :=
  match b with
  | false => 0
  | true  => allOnesBits widthBits

/-- Partial `simd_element_to_bool` (`IntrinsicSimd.lean:75-79`): `0 -> false`, `2^w - 1 -> true`, else `none` (UB). -/
def decodeMaskLane? (widthBits : Nat) (rawBits : Nat) : Option Bool :=
  if Nat.beq rawBits 0 then
    some false
  else if Nat.ble 1 widthBits && Nat.beq rawBits (allOnesBits widthBits) then
    some true
  else
    none

theorem maskLane_one_is_ub_i8 :
    decodeMaskLane? 8 1 = none ∧ decodeMaskLane? 8 255 = some true :=
  ⟨rfl, rfl⟩

def decodeMaskVec? (widthBits : Nat) : List Nat → Option (List Bool)
  | [] => some []
  | m :: ms =>
    match decodeMaskLane? widthBits m, decodeMaskVec? widthBits ms with
    | some b, some bs => some (b :: bs)
    | _, _ => none

def activeLanesInBounds (ptrAddr elemSz allocLo allocHi idx : Nat) : List Bool → Prop
  | [] => True
  | b :: bs =>
    (match b with
     | false => True
     | true  =>
       Nat.ble allocLo (ptrAddr + idx * elemSz) = true ∧
       Nat.ble (ptrAddr + (idx + 1) * elemSz) allocHi = true) ∧
    activeLanesInBounds ptrAddr elemSz allocLo allocHi (idx + 1) bs

/-- Exact `simd_masked_load`/`store` safety (`IntrinsicSimd.lean:444-461`): unconditional base alignment +
    `{-1, 0}` mask validity on all lanes + bounds required ONLY on active (`true`) lanes. -/
def SimdMaskedAccessSafe
    (alignMode : SimdAlignMode) (ptrAddr elemSz lanes allocLo allocHi widthBits : Nat)
    (rawMask : List Nat) : Prop :=
  Nat.beq (Nat.land ptrAddr (requiredAlignMask alignMode)) 0 = true ∧
  ∃ maskBools : List Bool,
    decodeMaskVec? widthBits rawMask = some maskBools ∧
    maskBools.length = lanes ∧
    activeLanesInBounds ptrAddr elemSz allocLo allocHi 0 maskBools

theorem allFalse_unaligned_rejected :
    ¬ SimdMaskedAccessSafe (.element 2) 1 4 4 0 64 8 [0, 0, 0, 0] := by
  intro h
  cases h with
  | intro hAlign _ => injection hAlign

theorem aligned_oob_tail_accepted :
    SimdMaskedAccessSafe (.element 2) 16 4 4 16 28 8 [255, 255, 255, 0] := by
  refine ⟨rfl, [true, true, true, false], rfl, rfl, ?_⟩
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial, trivial⟩

def bitmaskIndex (endian : EndianKind) (idx lanes : Nat) : Nat :=
  match endian with
  | .little => idx
  | .big    => lanes - 1 - idx

def packBitmaskAux (endian : EndianKind) (lanes idx : Nat) : List Bool → Nat
  | [] => 0
  | b :: bs =>
    let rest := packBitmaskAux endian lanes (idx + 1) bs
    match b with
    | false => rest
    | true  => Nat.lor (Nat.shiftLeft 1 (bitmaskIndex endian idx lanes)) rest

def packBitmask (endian : EndianKind) (mask : List Bool) : Option Nat :=
  let bitWidth := Nat.mul (Nat.div (mask.length + 7) 8) 8
  if Nat.blt 64 bitWidth then none else some (packBitmaskAux endian mask.length 0 mask)

theorem packBitmask_mod_rs_example :
    packBitmask .little [true, false, true, true] = some 13 ∧
    packBitmask .big [true, false, true, true] = some 11 :=
  ⟨rfl, rfl⟩

/-- Structural prefix mask (`rem` active `true` lanes out of `lanes` total). -/
def prefixMask : Nat → Nat → List Bool
  | 0, 0 => []
  | 0, k + 1 => false :: prefixMask 0 k
  | _ + 1, 0 => []
  | r + 1, k + 1 => true :: prefixMask r k

def maskedSelectTail {α : Type} : List Bool → List α → List α → List α
  | [], _, _ => []
  | false :: ms, xs, p :: ps => p :: maskedSelectTail ms xs ps
  | true :: ms, x :: xs, _ :: ps => x :: maskedSelectTail ms xs ps
  | true :: ms, [], p :: ps => p :: maskedSelectTail ms [] ps
  | _ :: _, _, [] => []

private theorem list_append_assoc {α : Type} :
    ∀ (xs ys zs : List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  intro xs
  induction xs with
  | nil => intro _ _; rfl
  | cons x rest ih =>
    intro ys zs
    dsimp only [List.append]
    rw [ih ys zs]

private theorem list_map_append {α β : Type} (f : α → β) :
    ∀ (xs ys : List α), List.map f (xs ++ ys) = List.map f xs ++ List.map f ys := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons x rest ih =>
    intro ys
    dsimp only [List.append, List.map]
    rw [ih ys]

private theorem list_take_map {α β : Type} (f : α → β) :
    ∀ (k : Nat) (xs : List α), List.take k (List.map f xs) = List.map f (List.take k xs) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ m ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons x rest =>
      dsimp only [List.map, List.take]
      rw [ih rest]

theorem take_maskedSelectTail_prefix {α : Type} :
    ∀ (remElems passthru : List α),
      Nat.ble remElems.length passthru.length = true →
      List.take remElems.length
        (maskedSelectTail (prefixMask remElems.length passthru.length) remElems passthru)
      = remElems := by
  intro remElems
  induction remElems with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro passthru hBle
    cases passthru with
    | nil => injection hBle
    | cons p ps =>
      dsimp only [List.length, prefixMask, maskedSelectTail, List.take]
      have hSub : Nat.ble xs.length ps.length = true :=
        Nat.ble_eq_true_of_le (Nat.le_of_succ_le_succ (Nat.le_of_ble_eq_true hBle))
      rw [ih ps hSub]

def chunksOfFuel {α : Type} (n : Nat) : Nat → List α → List (List α) × List α
  | 0, rem => ([], rem)
  | fuel + 1, xs =>
    if Nat.ble n xs.length then
      let res := chunksOfFuel n fuel (List.drop n xs)
      (List.take n xs :: res.1, res.2)
    else
      ([], xs)

theorem take_append_drop_eq {α : Type} :
    ∀ (n : Nat) (xs : List α), List.take n xs ++ List.drop n xs = xs := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro xs
    cases xs with
    | nil => rfl
    | cons x rest =>
      dsimp only [List.take, List.drop, List.append]
      rw [ih rest]

def flattenChunks {α : Type} : List (List α) → List α
  | [] => []
  | c :: cs => c ++ flattenChunks cs

theorem map_flattenChunks {α β : Type} (f : α → β) :
    ∀ (chunks : List (List α)),
      flattenChunks (List.map (List.map f) chunks) = List.map f (flattenChunks chunks) := by
  intro chunks
  induction chunks with
  | nil => rfl
  | cons c cs ih =>
    dsimp only [List.map, flattenChunks]
    rw [list_map_append f c (flattenChunks cs), ih]

theorem chunksOfFuel_reconstruct {α : Type} (n : Nat) :
    ∀ (fuel : Nat) (xs : List α),
      let res := chunksOfFuel n fuel xs
      flattenChunks res.1 ++ res.2 = xs := by
  intro fuel
  induction fuel with
  | zero => intro _; rfl
  | succ k ih =>
    intro xs
    dsimp only [chunksOfFuel]
    cases Nat.ble n xs.length with
    | false => rfl
    | true =>
      dsimp only [flattenChunks]
      rw [list_append_assoc (List.take n xs) (flattenChunks (chunksOfFuel n k (List.drop n xs)).1)]
      rw [ih (List.drop n xs)]
      exact take_append_drop_eq n xs

/-- Master SIMD Strip-Mining Homomorphism Theorem (`SimdVec <-> ListChunks`). -/
theorem simd_stripMine_map_homomorphism {α β : Type}
    (f : α → β) (evalVecChunk : List α → List β) (passthru : List α) (n : Nat)
    (hChunkHom : ∀ c : List α, evalVecChunk c = List.map f c)
    (xs : List α)
    (hTailFits : Nat.ble (chunksOfFuel n xs.length xs).2.length passthru.length = true) :
    let res := chunksOfFuel n xs.length xs
    let bodyOut := flattenChunks (List.map evalVecChunk res.1)
    let maskedIn := maskedSelectTail (prefixMask res.2.length passthru.length) res.2 passthru
    let tailOut := List.take res.2.length (evalVecChunk maskedIn)
    bodyOut ++ tailOut = List.map f xs := by
  dsimp only []
  have hMapChunks :
      List.map evalVecChunk (chunksOfFuel n xs.length xs).1 =
      List.map (List.map f) (chunksOfFuel n xs.length xs).1 := by
    induction (chunksOfFuel n xs.length xs).1 with
    | nil => rfl
    | cons c cs ih =>
      dsimp only [List.map]
      rw [hChunkHom c, ih]
  rw [hMapChunks, map_flattenChunks f, hChunkHom]
  rw [list_take_map f]
  rw [take_maskedSelectTail_prefix (chunksOfFuel n xs.length xs).2 passthru hTailFits]
  rw [← list_map_append f]
  rw [chunksOfFuel_reconstruct n xs.length xs]

end Anneal.Simd.LaneAlgebra
```

---

### 5. Evaluation Across the Zero-TCB Verification Rubric

`Basis: source + derived`

| Criterion | Grade | Assessment & Separating Justification |
| :--- | :---: | :--- |
| **`(T1)` 0-TCB Bridge** | **Minimal Hook + 0-TCB Algebra** | `Anneal.Simd.LaneAlgebra` lives 100% in untrusted `theory/`. `Trusted.MirSemantics` needs only thin `IntrinsicSimd` dispatch anchored in Pass 2 to `Miri/Interpreter/IntrinsicSimd.lean`. |
| **`(P1)` Human Spec Auditability** | **Strong** | Crate specs stay purely scalar (`List.map f xs`, `List.foldl op init xs`) with zero `SimdAlign` or `{-1, 0}` mask encodings in `Expected` theorems (Statement-Origin Separation). |
| **`(P2)` Authoring & Day-2 Locality** | **Strong** | Changing SIMD width (`4 -> 8 -> 16`) leaves `simd_stripMine_map_homomorphism` unchanged; per-chunk `evalVecChunk c = List.map f c` discharges by `rfl` or congruence closure. |
| **`(P3)` Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP** | **Strong** | Unbundled `List α` avoids dependent `Fin N` / `HEq` motive growth across `take`/`drop`, keeping WHNF linear in `N <= 64`. |
| **`(P4)` Heterogeneous Composability** | **Strong** | Composes directly with `slice::as_chunks` (`slice/mod.rs:1399`), `LeBytes` endian codecs, and `#[target_feature]` wrappers (`SymCRust/src/aes/`). |
| **`(P5)` Failure Legibility** | **Strong** | `SimdMaskedAccessSafe` separates misaligned all-false base pointers (`allFalse_unaligned_rejected`), `1`-lane mask UB (`maskLane_one_is_ub_i8`), and active-lane OOB reads. |
| **`(C1–C2)` Conceptual Minimality** | **Locally Minimal** | Reuses plain `List` chunking (`chunksOfFuel`); every retained predicate has a separating counterexample: (1) `SimdMask` $\neq$ `List Bool` (`maskLane_one_is_ub_i8`); (2) `simd_masked_load` $\neq$ `simd_gather` (`allFalse_unaligned_rejected`); (3) `simd_masked_load` $\neq$ full `ptr::read` + `simd_select` (`aligned_oob_tail_accepted`). |

## Boundaries

- **Scalable Vector Intrinsics (`core::intrinsics::simd::scalable`, SVE / RVV):** **not examined** mechanically and **unsupported** in `rustc_const_eval` and `lean-miri` (`IntrinsicSimd.lean:60` requires fixed `[Elem; N]` arrays, whereas `rustc_codegen_llvm` `intrinsic.rs:2426–2438` uses `ty::Bool` mask lanes on scalable vectors). Thus the `{-1, 0}` integer-lane rule is **known not to apply** to scalable `bool`-element masks.
- **Bitmasks Above 64 Lanes (`N > 64`):** Explicitly **unsupported** in `rustc_const_eval` (`simd.rs:392, 452`), `lean-miri` (`IntrinsicSimd.lean:173`), and `Mask::to_bitmask` (`masks.rs:304`).
- **Unordered Float Reductions (`simd_reduce_add_unordered`, `simd_reduce_mul_unordered`):** **known not to apply** to exact `List.foldl` strip-mining because `mod.rs:496–505` permits arbitrary tree reassociation (covered by `ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`).
- **`f128` Transcendental SIMD Intrinsics (`simd_fsin`..`simd_flog10`):** Explicitly **unsupported** in pinned Miri (`src/intrinsics/simd.rs:75`) and `lean-miri` (`IntrinsicSimd.lean:525`).
- **Upstream Stabilization of `load_select_ptr` / `store_select_ptr`:** Whether `portable-simd` will switch `vector.rs:458, 713` to `SimdAlign::Unaligned` or strengthen `# Safety` docs to require unconditional alignment is **unknown**; verifiers targeting `8144389c895d` must enforce unconditional element alignment.

## Evidence

- **`rust-lang/rust` @ `8144389c895da997dbdecaa635e41d6a50be6ffd`:** `library/core/src/intrinsics/simd/mod.rs` (`L361–468, 527–545, 592–660`), `library/portable-simd/crates/core_simd/src/masks.rs` (`L9–30, 60–116, 157–205, 302–337, 643–652`), `library/portable-simd/crates/core_simd/src/vector.rs` (`L410–464, 526–642, 663–719, 763–878`), `library/core/src/slice/mod.rs` (`L1399–1430`), `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs` (`L365–495, 611–714, 834–901`), `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`L2131–2179, 2417–2500, 2584–2800`).
- **`proofs-rs/lean-miri` @ `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` & `rust-lang/miri` @ `7fa591d7d4dd9af8154becbc8332f8096f8323b1`:** `Miri/Interpreter/IntrinsicSimd.lean` (`L75–81, 157–197, 231–257, 346–383, 416–462, 525`), `Miri/Interpreter/IntrinsicX86/Chunks.lean` (`L5–105`), `src/intrinsics/simd.rs` (`L21–108`).
- **`joshlf/anneal` @ `20aa204315cd36aaf944778b7d33c0d609ced8e8` & `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** `trusted/audit/TrustedBoundary.lean` (`L442–596`), `trusted/lean/foundation-lock.json` (`L1–1335`), `trusted/lean/Trusted/MirSemantics.lean` (`L48–108`).
- **Comparators & Literature:** `microsoft/SymCrypt` @ `286762b7730e2b780678f5ab11fef2b1bad639e0` (`SymCRust/README.md` `L61–64`, `SymCRust/proof/Symcrust.lean` `L1–140`, `SymCRust/src/aes/{aes_xmm.rs, aes_neon.rs}`), `jasmin-lang/jasmin` @ `8c3279973a89afd969e50301f71563bb40d55724` & `formosa-crypto/libjade` @ `89c38602783d9c90dda11a9b8053295a8a088597` (`proofs/lang/word.v` `L1786–1866, 2304–2306`; `proofs/lang/warray_.v` `L25–153`), Almeida et al., *"Jasmin: High-Assurance and High-Speed Cryptography,"* CCS 2017, DOI `10.1145/3133956.3134078`.

## Revalidation

1. **Source Diff (< 1 minute):** Diff `simd_element_to_bool`, `simd_masked_load`, and `check_simd_ptr_alignment` in `compiler/rustc_const_eval/src/interpret/intrinsics/simd.rs`, `vector_mask_to_bitmask` and `sym::simd_masked_load` in `compiler/rustc_codegen_llvm/src/intrinsic.rs`, and `Simd::load_select_ptr` in `library/portable-simd/crates/core_simd/src/vector.rs`.
2. **Miri Discriminator Probe (`cargo +nightly miri run`, plus `--target s390x-unknown-linux-gnu`):**
   ```rust
   #![feature(portable_simd, core_intrinsics)]
   use core::intrinsics::simd::{SimdAlign, simd_bitmask, simd_masked_load, simd_select};
   use core::simd::{Mask, Simd};

   #[repr(simd)] #[derive(Copy, Clone)] struct I8x4([i8; 4]);

   fn main() {
       let buf = Box::new([10u32, 20, 30]);
       let mask = Simd::<i32, 4>::from_array([-1, -1, -1, 0]);
       let out: Simd<u32, 4> = unsafe {
           simd_masked_load::<_, _, _, { SimdAlign::Element }>(mask, buf.as_ptr(), Simd::splat(99))
       };
       assert_eq!(out.to_array(), [10, 20, 30, 99]); // OOB lane 3 exempt when mask = 0
       assert_eq!(Mask::<i8, 4>::from_array([true, false, true, true]).to_bitmask(), 0b1101);
       let raw: u8 = unsafe { simd_bitmask(I8x4([-1, 0, -1, -1])) };
       assert_eq!(raw, if cfg!(target_endian = "little") { 0b1101 } else { 0b1011 });
       // Uncommenting either line below must trigger immediate Miri Undefined Behavior:
       // let _ = unsafe { simd_select(I8x4([1, 0, 0, 0]), I8x4([1; 4]), I8x4([0; 4])) };
       // let _ = unsafe { Simd::<u32, 4>::load_select_ptr(1usize as *const u32, Mask::splat(false), Simd::splat(0)) };
   }
   ```
3. **Pass-1 Lean 4 Audit:** Check `Anneal.Simd.LaneAlgebra` under `TrustedBoundary.lean` `"preflight"` + `"audit"` to confirm zero warnings, zero `._unsafe_rec`, and axioms `⊆ {propext, Quot.sound}`.
