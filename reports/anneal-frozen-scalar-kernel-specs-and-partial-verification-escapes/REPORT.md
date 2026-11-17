# Frozen Scalar Kernel Specifications, Enum `DefIndex` Invariance, and Partial-Verification Boundary Escapes

## Summary

Verifying low-level compression and bit-manipulation kernels incrementally in
Rust exposes four structural failure modes at the specification and module
boundaries:

1. **Unconstrained wire-format contracts and encoder-decoder collusion:** Proving
   a symmetric round-trip against an unpinned candidate decoder admits trivial
   identity codecs (`CoupledRoundTrip id some`), while proving totality or a
   round-trip against a locked decoder (`LockedRoundTrip`) without an
   output-size ratchet admits degenerate stored-block codecs that double encoded
   size on repetitive runs (`stored_ratio_collapse`: `6` bytes vs. `3`). Pairing
   a locked reference decoder with a verified size arbitrator (`pickSmaller`)
   eliminates both regressions while preserving stream validity.
2. **Crate-local `DefIndex` fragility across specification targets:** Because
   MIR extraction identifies Rust enums by `adt.did().index.as_u32()`
   (`joshlf/anneal@31b91b61b84e:trusted/rustc-capture/src/extract.rs:148`),
   adding or reordering items shifts hardcoded integer enum identifiers (`7 ->
   42`). Resolving the expected enum descriptor dynamically from `body.locals`
   (`resolveArg0EnumVal`) restores specification invariance by `rfl` across
   reordered builds.
3. **Partial-boundary escapes inside individually verified kernels:** A kernel
   specification that discharges pure arithmetic checks or bounded loop guards
   still misses whole-function memory-safety defects across three uncoupled seams:
   - *Match-tail truncation (`256` vs. `258`):* Checking an 8-byte prefix plus 31
     8-byte words covers `8 + 31 * 8 = 256` bytes while returning `min(max,
     258)`, silently emitting corrupted distance/length pairs when bytes `256`
     and `257` differ (`findMatch_256_prefix_violates_full_match_258`).
   - *Fused literal-plus-wild-copy margin escapes:* When a fast loop fuses
     trailing literals before a wide match copy, the write footprint is
     `lLit + ceil(matchLen / w) * w` bytes. Zero literals fit (`0 + 264 <=
     266`), yet three preceding literals exceed an 8-byte wild-copy guard (`3 +
     264 = 267 > 266`), and two 2-byte literal bursts before a 32-byte splat
     touch `4 + 288 = 292 > 290` bytes (rescued only if the outer caller sets
     an unverified `304`-byte slack constant).
   - *Logical `out_max` vs. physical capacity and cyclic ring clobber:*
     Observational slice-prefix refinement (`ObsSlicePrefixEquiv`) absorbs slack
     writes only within allocated capacity (`oob_write_not_absorbed`), cannot
     justify uninitialized 8-byte lookbacks at `dist < 8`
     (`wildCopy_8byte_read_strictly_initialized_iff`), fails unless scalar
     `out_max` guards are coupled to `dst.len()`, and overlooks `w`-byte ring
     overshoot overwriting live history at distances `(R - w, R]` (including all
     RFC 1951 distances `32764..=32768` under an 8-byte wild copy in a `32 KiB`
     window).

All specification theorems, `DefIndex`-invariance proofs, and boundary escapes
are mechanized without `sorry` or `native_decide` in
[`support/SpecRatchetAndEscapes.lean`](support/SpecRatchetAndEscapes.lean) and
tested dynamically in
[`support/partial_boundary_escapes.rs`](support/partial_boundary_escapes.rs).

---

## Applicability

These findings govern:

- **Rust/Lean MIR verification architectures (`joshlf/anneal`):** Applicable to
  the MIR semantics and extractor introduced on the `joshlf/anneal` MIR
  integration baseline (`31b91b61b84e0058db44cacbd6d189a90433c2d1`, forked from
  `origin/main` `5c960dd3f1b94321307d4500a4e180c753bfaad0`, pinning
  `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` in
  `vendor/lean-miri/UPSTREAM_PIN.json`). Note that `origin/main` (`5c960dd3f`)
  contains the `PureLift` evaluator (`theory/Anneal/PureLift/*`) without the
  `Trusted.MirAst` / `Trusted.MirSemantics` extractor (`trusted/rustc-capture/src/{capture,extract,ir,lean}.rs`).
- **Incremental kernel verification and RFC 1951 DEFLATE/LZ77 engines:** Applies
  to any Rust verification boundary that stabilizes low-level scalar helpers
  (bit-packing, bounds guards, arithmetic ratchets) before whole-slice borrow
  checking or cyclic ring-buffer modeling is attached, and to unsafe wild-copy
  decode loops checked under Miri or `MaybeUninit<u8>`.
- **Pinned toolchains:** Verified against Lean `v4.34.1` (`5045d0056413`) and
  Rust `1.102.0-nightly` (`3ef0c22cdb86`). Closed-namespace `FileLoader` source
  macro refusals in `RecordingLoader` (`31b91b61b:capture.rs:86-231`) are
  analyzed separately in
  [`compiler-concurrent-source-modification-and-hermetic-input-binding`](../compiler-concurrent-source-modification-and-hermetic-input-binding/REPORT.md);
  Lean `v4.34.1` bitvector `whnf` barriers (`signExtendBits`, `ScalarVal.wf`,
  `truncateScalar`) live in
  [`lean-mir-semantics-scalar-truncation-idempotence-and-fast-step-transfer`](../lean-mir-semantics-scalar-truncation-idempotence-and-fast-step-transfer/REPORT.md).

---

## Findings

### 1. Frozen Positional Contracts, Grounding Ratchets, and `DefIndex` Invariance

`Basis: source + execution`

#### 1.1 Wire-Format Collusion, Stored Collapse, and Size Arbitration

A common specification hazard in verified lossless codecs is validating the
compressor only against a symmetric helper proof:

1. **Encoder-decoder collusion (`CoupledRoundTrip`):** Quantifying `∀ d, dec
   (enc d) = some d` over *both* a candidate encoder and a candidate decoder
   admits trivial bypasses (`id` paired with `some`, proved in
   `collusion_passes_coupled`), which a fixed RFC 1951 decoder immediately rejects
   (`collusion_fails_locked` on `[5]`).
2. **Stored-block ratio collapse:** Grounding the encoder against a *locked*
   reference decoder (`LockedRoundTrip enc := ∀ d, refDecode (enc d) = some d`)
   eliminates invalid streams, yet still admits an all-stored fallback
   (`fun d => 0 :: d`, `stored_passes_locked`) that emits `6` bytes where valid
   run-length encoding needs `3` (`stored_ratio_collapse`). Similarly, proving
   totality alone provides zero correctness guarantee (`totality_unconstraining`).
3. **Reference-stream arbitration (`pickSmaller`):** Checking both `ValidStream
   optStream` and `ValidStream refStream` and emitting `pickSmaller optStream
   refStream := if optStream.length ≤ refStream.length then optStream else
   refStream` preserves arbitrary stream-validity predicates while enforcing a
   monotonic byte-length ceiling (`pickSmaller_valid_and_no_larger`), rejecting
   stored collapse (`pickSmaller_blocks_stored_collapse`).

#### 1.2 Eliminating Brittle MIR Enum `DefIndex` Coupling (`resolveArg0EnumVal`)

In `joshlf/anneal@31b91b61b84e:trusted/rustc-capture/src/extract.rs:148-159`,
enum types carry `EnumTy { id: adt.did().index.as_u32(), ... }` directly from
`rustc`'s crate-local `DefId`. Later, `Trusted.MirSemantics.evalConstLit`
(`MirSemantics.lean:830-839`) decodes `.enumVal ety v` using `ety.tagWidth` and
`findDiscrVariant?`, comparing against the exact `EnumTy` stored in the
program's own `Body.locals` or `Body.ret`.

If a frozen specification hardcodes `EnumTy.id = 7`, adding a single helper
function upstream in the same module shifts `adt.did().index.as_u32()` (for
example from `7` to `42`) and fails the specification check
(`brittleEnumCheck_breaks_on_defIndex_shift`). Inspecting `body.locals` at the
argument position (`resolveArg0EnumVal`: pattern-matching `_ :: .enum ety :: _`)
constructs the matching `.enumVal ety variantIdx` without guessing `id`, making
state predicates invariant under arbitrary `DefIndex` renumbering by `rfl`
(`resolveArg0EnumVal_defIndex_invariant`).

### 2. Three Partial-Verification Boundary Escapes

`Basis: execution + formal`

Verifying isolated pure arithmetic or guard helpers against frozen scalar MIR
contracts leaves three classes of real memory- and functional-soundness defects
invisible unless pointer/slice bounds and outer caller constants are coupled to
the verified term.

#### 2.1 Off-by-Two Match Comparison Tail (`256` vs. `258`)

An 8-byte initial comparison plus `31` loop iterations of 8-byte XOR checks
covers `8 + 31 * 8 = 256` bytes (`findMatch_compared_bytes`). If the function
returns `min(max_match_len, 258)` upon exhausting those `31` words without
checking bytes `256` and `257`, two `258`-byte slices matching on `take 256` and
differing at byte `256` produce an unsound back-reference
(`findMatch_256_prefix_violates_full_match_258`). Adding the missing 2-byte tail
check restores slice equality (`findMatch_256_plus_tail2_sound`), while bounding
scalar read offsets via `matchTailBoundNat` proves `p1 + ret ≤ inputLen ∧ p2 +
ret ≤ inputLen ∧ ret ≤ 258` (`matchTailBound_sound`). Crucially, because a
corrupted length-`258` match still outputs `258` bytes, length-only decompressor
checks (`decoded.len() == raw.len()`) never detect this bug.

#### 2.2 Fused Literal-Plus-Wild-Copy Footprints and Uncoupled `out_max`

Suppose a fast decode loop guards capacity with `out_rem >= G`, emits `lLit`
literal bytes, and then runs a `w`-byte-stride wild copy for a match of length
`matchLen <= 258`. Its worst-case write reach is:
$$\text{wildCopyTouchedBytes}(l_{\text{lit}}, L, w) = l_{\text{lit}} + \left\lceil\frac{L}{w}\right\rceil w$$

| Configuration | Guard Verified | Literal Prefix ($l_{\text{lit}}$) | Stride ($w$) | Touched Bytes | Outcome |
| :--- | :---: | :---: | :---: | :---: | :--- |
| Bare 8-byte wild match | `266` (`258 + 8`) | `0` | `8` | `264` | Safe (`264 <= 266`) |
| 3 literals + 8-byte match | `266` | `3` | `8` | **`267`** | **Escapes guard (`267 > 266`)** |
| Bare 32-byte SIMD splat (`dist=1`) | `290` (`258 + 32`) | `0` | `32` | `288` | Safe (`288 <= 290`) |
| Two 2-byte literal pairs + 32-byte splat | `290` | `4` | `32` | **`292`** | **Escapes `290` (`292 > 290`), hits `Err(2)` unless `304` slack holds** |
| Two 2-byte literal pairs + 16-byte splat | `290` | `4` | `16` | `276` | Safe (`276 <= 290`) |

Both `wildCopy_margin_266_violated` (`3 + 264 = 267 > 266`) and
`simd_guard_290_vs_292` (`4 + 288 = 292 > 290 <= 304`) are verified by `decide`
in [`SpecRatchetAndEscapes.lean`](support/SpecRatchetAndEscapes.lean) and
reproduced dynamically in
[`partial_boundary_escapes.rs`](support/partial_boundary_escapes.rs)
(`literal_prefixed_292_escapes_290_guard`). Furthermore, even checking `out_pos +
guard ≤ out_max` at the scalar level cannot prevent slice overrun if `out_max`
exceeds physical `dst.len()` (`scalar_guard_insufficient_without_coupling`) or if
slack writes step outside the allocated vector (`oob_write_not_absorbed`:
`ObsSlicePrefixEquiv k (buf ++ extra) buf → extra = []`).

#### 2.3 Prefix Absorption Boundaries: Uninitialized `MaybeUninit` Loads and Ring Clobber

Observational prefix equivalence `ObsSlicePrefixEquiv` successfully models
in-bounds slack writes over an initialized buffer (`wildMatch_satisfies_prefix_equiv`
where bit-exact equality `wildMatch_violates_bit_exact` fails), but two aliasing
mechanisms defeat it when unmodeled:

1. **Uninitialized suffix reads on small distances:** When `[0, outPos)` is
   initialized and `[outPos, buf.len())` is uninitialized (`MaybeUninit<u8>`),
   an unaligned 8-byte load at `outPos - dist` remains within `[0, outPos)` if
   and only if `dist ≥ 8` (`wildCopy_8byte_read_strictly_initialized_iff`). Any
   `dist < 8` read straddles uninitialized slack bytes and triggers immediate
   Undefined Behavior (see
   [`x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width`](../x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width/REPORT.md)
   for Miri traces on `dist = 4` vs. `dist = 8`).
2. **Wrapping ring-buffer history overwrite:** In a circular buffer of size `R >=
   w`, a `w`-byte-stride copy of a `matchLen`-byte match overshoots by
   `wildOvershoot matchLen w := ceil(matchLen / w) * w - matchLen < w` bytes
   (`wildOvershoot_lt`). Those overshoot writes wrap into history positions at
   distances `R - j ∈ (R - w, R]` from the updated write head
   (`ring_clobber_distance`). For a standard `32 KiB` (`R = 32,768`) ring:
   - An 8-byte wild copy of length `3` overshoots by `5` bytes, corrupting legal
     DEFLATE distances `32,764..=32,768` (`ring_32768_instances`);
   - A 32-byte wild copy of length `3` overshoots by `29` bytes, corrupting `29`
     legal distances in `[32,740, 32,768]`;
   - An executable `16`-byte ring witness confirms `ringCopy` overwrites index
     `3` (`distance 16`) from `3` to `11` (`ring16_wild_clobbers_distance_R`,
     reproduced dynamically in `wrapping_ring_clobbers_max_distance`).

---

## Boundaries

- **Scope of MIR semantics extraction:** The Lean probe in
  [`SpecRatchetAndEscapes.lean`](support/SpecRatchetAndEscapes.lean) models
  `EnumTy`/`Body` lookup, codec ratchets, and array/ring arithmetic in core
  Lean `Init` so it executes standalone without compiling `Anneal`'s `Trusted`
  `.olean` tree. Full crate-level end-to-end MIR proofs depend on `Trusted.MirAst`
  / `Trusted.MirSemantics` admission (which in `joshlf/anneal@31b91b61b84e`
  omits `UnOp` and fieldless-enum aggregate lowering unless extended in
  `rustc-capture`).
- **Capture-time `FileLoader` closure:** When crates under verification expand
  standard-library formatting macros (`unreachable!("...")`, `todo!("...")`) on
  dead branches, hermetic `RecordingLoader` input policies refuse unread stdlib
  source paths; that mechanism is scoped to
  [`compiler-concurrent-source-modification-and-hermetic-input-binding`](../compiler-concurrent-source-modification-and-hermetic-input-binding/REPORT.md).
- **Miri execution of small-distance uninitialized reads:**
  [`partial_boundary_escapes.rs`](support/partial_boundary_escapes.rs) runs the
  initialized `dist = 8` lookback test cleanly under `rustc --test`; explicit
  Miri UB failure/pass probes live alongside the SIMD overlap study in
  [`x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width`](../x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width/REPORT.md).

---

## Evidence

### 1. Primary Upstream Sources Examined

- **`joshlf/anneal` (`31b91b61b84e0058db44cacbd6d189a90433c2d1`):**
  - `trusted/rustc-capture/src/extract.rs:148-159` (`EnumTy { id: adt.did().index.as_u32(), ... }`), `:254-281` (`bin_op` admission), `:384-418` (`rvalue` admission).
  - `trusted/rustc-capture/src/capture.rs:86-231` (`RecordingLoader`), `:740-742` (fail-closed refusal check).
  - `trusted/lean/Trusted/MirSemantics.lean:830-839` (`evalConstLit (.enum ety)`).
  - `trusted/cargo-anneal/src/lib.rs:169` (`LOCKED_MIRI_COMMIT = "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a"` matching `vendor/lean-miri/UPSTREAM_PIN.json`).
- **`joshlf/anneal` (`5c960dd3f1b94321307d4500a4e180c753bfaad0`):**
  - `theory/Anneal/PureLift/*` and scaffold `trusted/rustc-capture/src/{driver,main}.rs`.

### 2. Preserved Package Support Artifacts

- [`support/SpecRatchetAndEscapes.lean`](support/SpecRatchetAndEscapes.lean):
  Standalone `395`-line Lean `v4.34.1` proof suite verifying `23` theorems with
  matching `#guard_msgs in #print axioms` receipts (zero `sorry`, zero
  `native_decide`, standard Lean axioms `[propext, Classical.choice, Quot.sound]`
  only).
- [`support/partial_boundary_escapes.rs`](support/partial_boundary_escapes.rs):
  Standalone Rust unit tests demonstrating `4 + 288 = 292 > 290` guard escape,
  `304`-byte slack absorption, wrapping `16`-byte ring history clobber, and `dist
  = 8` initialized lookback.
- [`support/verify_escapes.py`](support/verify_escapes.py): Combined driver that
  checks [`SpecRatchetAndEscapes.lean`](support/SpecRatchetAndEscapes.lean)
  under `leanprover/lean4:v4.34.1` and compiles/executes
  [`partial_boundary_escapes.rs`](support/partial_boundary_escapes.rs).

---

## Revalidation

Run the standalone validation suite from the repository root:

```console
python3 reports/anneal-frozen-scalar-kernel-specs-and-partial-verification-escapes/support/verify_escapes.py
```

The command must exit `0` with `"status": "PASS"`, empty Lean output (confirming
all `23` `#guard_msgs` axiom checks), and `3 passed; 0 failed` from the Rust test
binary.
