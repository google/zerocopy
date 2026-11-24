# rustc MIR CastKind Lowering: IntToInt Sign/Zero Extension, Saturating FloatToInt, Ties-to-Even IntToFloat, PtrToPtr Wide-to-Thin, and Strict vs. Exposed Provenance

## Summary

This report establishes primary-source, empirical, and kernel-checked ground truth for how `rustc` and Miri define and lower MIR `Rvalue::Cast(CastKind, Operand, Ty)` across integer width/signedness conversions (`CastKind::IntToInt`), saturating floating-point-to-integer conversions (`CastKind::FloatToInt`), IEEE-754 integer-to-floating-point and floating-point width conversions (`CastKind::IntToFloat`, `CastKind::FloatToFloat`), pointer re-typing and wide-to-thin projection (`CastKind::PtrToPtr`, `CastKind::FnPtrToPtr`), and pointer-address/provenance transitions (`CastKind::PointerExposeProvenance`, `CastKind::PointerWithExposedProvenance`, and strict-provenance `Transmute` wrappers `core::ptr::const_ptr::addr`, `with_addr`, and `without_provenance`).

Seven core conclusions emerge from cross-auditing `rust-lang/rust` (primary snapshot `058c701055c4b6f60f622d616afc0349911c38c3` plus diffs against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `llvm/llvm-project` (`7ebbe97cef9e1aca651aa6df26ccf0441f1f6f88`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), alongside live `rustc 1.98.0-nightly` / `LLVM 22.1.6` / `miri 0.1.0` probes (`support/probe_cast_kind_sat_and_strict_prov.py`, `support/probe_results.json`) and a standalone, axiom-clean `Lean v4.34.1` formalization (`support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean`, `2,262` LOC, `73` named theorems, `[Quot.sound, propext]` only):

1. **`CastKind::IntToInt` Signedness-Keyed Extension (`sext` vs. `zext` vs. `trunc`)** — `Basis: normative + source + execution`. In `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`cast_immediate`), integer-to-integer casts dispatch exclusively on `from_scalar.primitive()`'s `is_signed` flag (passing `to_scalar`'s signedness nowhere to `bx.intcast`), while `Bool <-> Int` and `Bool <-> Bool` always pass `is_signed = false`. Consequently, widening a negative signed integer to a wider unsigned integer sign-extends before treating the two's-complement bit pattern as unsigned (`-1i8 as u32 == 0xffff_ffff` via `sext i8 %x to i32`), whereas widening via an unsigned intermediate zero-extends (`-1i8 as u8 as u32 == 255` via `trunc`/cast + `zext i8 %x to i32`), and narrowing always truncates (`trunc iN %x to iM`) independently of sign.
2. **Unconditional Total Saturating `CastKind::FloatToInt` Lowering (`@llvm.fptosi.sat` / `@llvm.fptoui.sat`)** — `Basis: normative + source + execution`. Both SSA codegen (`cast_float_to_int` in `traits/builder.rs`, dispatching unconditionally to `fptosi_sat` / `fptoui_sat`) and CTFE/Miri (`cast_from_float` in `interpret/cast.rs`, invoking `rustc_apfloat` `to_u128` / `to_i128` saturating helpers) guarantee total, UB-free clamping for all finite values, infinities, and quiet/signaling NaNs: `NaN -> 0`, `+Inf -> MAX`, `-Inf -> MIN` (`0` for unsigned), `-1.0 as u32 -> 0`, `(2^31)f32 as i32 -> i32::MAX`, with zero Miri UB across all four Miri modes (`default`, `-Zmiri-strict-provenance`, `-Zmiri-permissive-provenance`, `-Zmiri-tree-borrows`). Unchecked UB remains strictly confined to `core::intrinsics::float_to_int_unchecked` (`to_int_unchecked`), which emits raw `fptosi`/`fptoui` (`llvm.wasm.trunc.*` on Wasm targets).
3. **IEEE-754 Round-to-Nearest Ties-to-Even for `CastKind::IntToFloat` (`sitofp`/`uitofp`) and Narrowing `FloatToFloat` (`fptrunc`)** — `Basis: normative + source + execution`. Integer-to-float casts lower directly to LLVM `sitofp`/`uitofp` (and `rustc_apfloat` `from_i128`/`from_u128` in CTFE/Miri), obeying IEEE-754 `roundTiesToEven` with overflow to `±Inf` when the rounded magnitude exceeds `f32::MAX`: live execution and kernel-reduced Lean proofs both verify `(1<<24)+1 -> 16777216.0` (tie down to even LSB `0x4b800000`), `(1<<24)+2 -> 16777218.0` (`0x4b800001`), `(1<<24)+3 -> 16777220.0` (tie up to even LSB `0x4b800002`), `(1<<24)+4 -> 16777220.0`, `i32::MAX -> 2147483648.0`, and `u128::MAX as f32 -> +inf` (`0x7f800000`), whereas `i128::MIN as f32 -> -2^127` (`0xff000000`) remains finite.
4. **Wide-to-Thin `CastKind::PtrToPtr` Projection Is Pure Provenance-Preserving Extraction (`ScalarPair(data, _) -> Scalar(data)`)** — `Basis: source + execution`. Under `rustc`'s ABI and interpreter, wide-to-thin casts project `.0` from `OperandValue::Pair(data_ptr, meta)` (`Immediate::ScalarPair(data, _)` in CTFE/Miri) without exposing or scrubbing provenance, whereas Rust vs. C ABI changes LLVM signature lowering (`ptr %p.0, i64 %p.1 -> ret ptr %p.0` vs. `{ i64, i64 }` -> `extractvalue` + `inttoptr` under `-O2` or `alloca`/`memcpy` without passes). Note also a `main` (`058c70105`) vs. `1.98.0-nightly` (`14210df0e`) divergence: `interpret/cast.rs:45-56` on `main` runs pre-cast `enforce_validity` (`deref_pointer` on wide `RawPtr`, `get_ptr_fn` on `FnPtr`) before `ptr_to_ptr` executes.
5. **Strict vs. Exposed Provenance Soundness and `ptrtoint` Backend Codegen Gap** — `Basis: source + execution + derived`. Both Miri source and live execution demonstrate an asymmetric refinement: (a) calling `addr()` (`Transmute`) or `without_provenance` ZST non-null reads produces zero diagnostics in all four Miri modes (`default`, `strict`, `permissive`, `tree_borrows`); (b) calling `expose_provenance()` alone *without* `with_exposed_provenance()` also succeeds in `-Zmiri-strict-provenance` because Miri makes `expose_provenance` a no-op in `Strict` mode; (c) calling `with_exposed_provenance` (`PointerWithExposedProvenance`) unconditionally terminates with an unsupported-operation stop under `-Zmiri-strict-provenance`, emits a deduplicated non-halting warning in `default` and `-Zmiri-tree-borrows`, creates a deferred `Provenance::Wildcard` pointer checked lazily against `exposed` allocations on dereference (so shifting via `wrapping_byte_offset` onto a distinct *exposed* allocation succeeds while hitting an *unexposed* allocation fails with `no provenance`); and (d) LLVM codegen on `1.98.0-nightly` / `LLVM 22.1.6` and `main` (`rvalue.rs:1135-1138`) still emits `ptrtoint` even for `core::ptr::const_ptr::addr()` (`FIXME: this exposes the provenance`) rather than LLVM `main` LangRef's `ptrtoaddr`.
6. **Lean `v4.34.1` Mechanization With Zero `Classical.choice` (`[Quot.sound, propext]`)** — `Basis: execution + derived`. `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean` formalizes five mathematical and operational models (`BitVec` `IntToInt`, `Dyadic`/`FloatVal` saturating `FloatToInt` and open-interval refinement over `uncheckedFloatToInt`, constructive `F32Val` `roundNatToF32`/`roundIntToF32` ties-to-even, and the strict-vs-exposed pointer-provenance machine) with `73` theorems and `50` `noncomputable def`s, passing `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with exit code `0`, `0` `._unsafe_rec` constants, `0` `partial def`s, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, and `0` `sorryAx`.
7. **Direct Impact on `joshlf/anneal` (`c131b320e`)** — `Basis: source + derived`. Live `joshlf/anneal` HEAD fails closed on every cast (`Trusted/MirAst.lean:612-613` parses `Rvalue::Cast` as `.unsupported`, `MirTy::Float` fails closed at `L308`, and `Trusted/Correspondence.lean:1858` sets `cast := fun ... => .error .unsupported`), while `vendor/lean-miri/Miri/Interpreter/Cast.lean` already sketches a full `CastKind` interpreter hook. Any Anneal extension enabling `Rvalue::Cast` must preserve exact MIR `CastKind` distinctions (`PointerExposeProvenance` vs. `Transmute` for `addr()`, `FloatToInt` unconditional saturation, and two's-complement signedness propagation on `IntToInt`) or else risk unsoundly equating exposing and non-exposing casts or miscompiling mixed-sign widening.

## Applicability

This package applies to engineers and verification researchers formalizing Rust MIR semantics, translation validators (`MIR -> LLVM IR` / `MIR -> MiniSSA`), or `cargo anneal` backend support for raw casts (`as`), float-to-integer coercions, floating-point representation rounding, and pointer provenance boundaries.

- **Compiler versions covered (`Basis: source + execution`):**
  - Primary source analysis reflects `rust-lang/rust` `main` at `058c701055c4b6f60f622d616afc0349911c38c3` (`2026-11-24`), cross-diffed against intermediate snapshot `49d734536222bf28bb6d07d885b3a81d145981da`, toolchain reference `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`), and the live local execution toolchain `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `LLVM 22.1.6`, `miri 0.1.0`) running on `x86_64-unknown-linux-gnu`.
  - Upstream Rust language rules (`r[expr.as.*]`) reflect `rust-lang/reference` commit `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`.
  - LLVM IR instruction and saturating-intrinsic semantics reflect `llvm/llvm-project` `main` at `7ebbe97cef9e1aca651aa6df26ccf0441f1f6f88` (`llvm/docs/LangRef.md`).
  - Downstream verification consumer alignment reflects `joshlf/anneal` `main` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`.
- **Execution targets and architectures (`Basis: execution`):**
  - Native binaries, `--emit=mir`, `--emit=llvm-ir` (`-O2` and `-C no-prepopulate-passes`), and all four `cargo +nightly miri run` modes were executed directly on `x86_64-unknown-linux-gnu`.
  - WebAssembly (`target_family = "wasm"` non-saturating intrinsic paths in `compiler/rustc_codegen_llvm/src/builder.rs:1030-1060`) and `aarch64`/`i686` codegen outputs were inspected at source level only, not executed.
- **Model–system relation (`Basis: derived`):**
  - The mechanized artifact (`support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean`) is a **standalone mathematical and operational formalization** verified under `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). It does **not** import `joshlf/anneal`'s `Trusted.MirSemantics` or machine-parse `rustc` MIR/LLVM ASTs directly; alignment between `rustc`/Miri and the Lean model rests on line-by-line source inspection (`source`) plus matching empirical outputs (`execution`).
  - Within this corpus ecosystem, the pure-math float NaN/open-interval and `ScalarPair` representation-lowering boundaries also align with standalone Lean toy-model studies (`float-nan-set-semantics-refinement-tiers-truncating-cast-open-interval-and-saturation` and `scalarpair-register-lowering-refinement-init-uniform-scalars-and-provenance-boundaries`), while this report adds `rustc` primary-source audit, live `rustc`/LLVM/Miri execution, `BitVec` `IntToInt` two's-complement asymmetry proofs, `F32Val` `IntToFloat` ties-to-even proofs, and strict-vs-exposed provenance simulation.

## Findings

### 1. MIR `CastKind` Taxonomy and `ty::cast` Lowering Boundary (`Basis: source + normative`)

In `compiler/rustc_middle/src/mir/syntax.rs` (`058c70105` L1493–1552; unchanged in core variants from `14210df0e` L1491–1542 and `49d734536` L1491–1549), `Rvalue::Cast(CastKind, Operand<'tcx>, Ty<'tcx>)` partitions casts into twelve variants:

| MIR `CastKind` Variant | `syntax.rs` Line (`058c70105`) | Source / Dest Domain | Primary SSA Lowering Mechanism | Primary CTFE/Miri Dispatch |
| :--- | :--- | :--- | :--- | :--- |
| `PointerExposeProvenance` | L1497 | `*const/*mut T` or `fn(...)` -> integer (`usize` etc.) | `bx.ptrtoint` (`rvalue.rs:514-520`) | `pointer_expose_provenance_cast` -> `M::expose_provenance` (`interpret/cast.rs:287-305`) |
| `PointerWithExposedProvenance` | L1500 | integer -> `*const/*mut T` | `bx.intcast` (if needed) + `bx.inttoptr` (`rvalue.rs:484-487, 598-624`) | `pointer_with_exposed_provenance_cast` -> `M::ptr_from_addr_cast` (`interpret/cast.rs:307-323`) |
| `PointerCoercion(PointerCoercion, CoercionSource)` | L1510 | ReifyFnPointer, ClosureFnPointer, UnsafeFnPointer, Unsize, (borrowck-only ArrayToPointer/MutToConstPointer) | `get_fn_addr`, no-op, or `base::unsize_ptr` (`rvalue.rs:521-576`) | `Unsize` -> `unsize_into`; FnPtr -> `ImmTy::from_immediate` (`interpret/cast.rs:82-135`) |
| `IntToInt` | L1511 | `Int`/`Uint`/`Bool`/`Char` <-> `Int`/`Uint`/`Bool` | `bx.intcast(imm, to_backend_ty, is_signed)` (`rvalue.rs:467-470`) | `cast_from_int_like` (`interpret/cast.rs:327-381`) |
| `FloatToInt` | L1512 | `f16`/`f32`/`f64`/`f128` -> integer | `bx.cast_float_to_int` -> `fptosi_sat` / `fptoui_sat` (`traits/builder.rs:400-418`) | `cast_from_float` -> `apfloat` saturating `to_i128` / `to_u128` (`interpret/cast.rs:384-429`) |
| `FloatToFloat` | L1513 | float -> float | `fpext` / `fptrunc` / identity (`rvalue.rs:471-475`) | `cast_from_float` (`rustc_apfloat` `convert`) |
| `IntToFloat` | L1514 | integer -> float | `sitofp` / `uitofp` (`rvalue.rs:476-482`) | `cast_from_int_like` (`rustc_apfloat` `from_i128` / `from_u128`) |
| `PtrToPtr` | L1515 | thin/wide raw ptr -> thin/wide raw ptr | `ScalarPair` extract `data_ptr` or `bx.pointercast` (`rvalue.rs:483, 577-588`) | `ptr_to_ptr` -> `Immediate::ScalarPair(data, _)` -> `data` (`interpret/cast.rs:257-285`) |
| `FnPtrToPtr` | L1516 | `fn(...)` -> `*const ()` / thin raw ptr | `bx.pointercast` (`rvalue.rs:483, 594`) | `ptr_to_ptr` (`interpret/cast.rs:265-268`) |
| `Transmute` | L1521 | Same-size arbitrary layout bits (`mem::transmute`, `const_ptr::addr`, `without_provenance`) | `codegen_transmute_operand` / `transmute_scalar` (`rvalue.rs:1093-1161`) | `transmute` (`copy_op_allow_transmute` semantics) |
| `BoxDerefTransmute` | L1529 | `Box<T>` / newtype -> raw pointer | Backend treats as `Transmute` (`syntax.rs:1522-1528`) | Validates `Box` validity invariants |
| `Subtype` | L1541 | Lifetime/subtyping coercion via `Subtyper` MIR pass | Backend `Transmute`/no-op for trait/`TypeId` | Identity copy (`interpret/cast.rs`) |

**Key MIR-phase invariant (`syntax.rs:1501-1510`, `rvalue.rs:571-576`) [`source`]:** `PointerCoercion::ArrayToPointer` and `PointerCoercion::MutToConstPointer` are permitted only in `AnalysisPhase::Initial` (borrowck) and are **forbidden in runtime MIR and codegen** (`bug!("{kind:?} is for borrowck, and should never appear in codegen")`); runtime MIR replaces both with `CastKind::PtrToPtr`. Similarly, `&x as *const T` does not produce a `CastKind` at all—`rustc` lowers reference-to-raw-pointer casts directly to `&raw const *x` (`syntax.rs:1501-1502`).

**Type-classification rule (`compiler/rustc_middle/src/ty/cast.rs:1-73`) [`source`]:** `CastTy::from_ty` classifies source and target types into `Int(IntTy)` (covering `Int`, `Uint`, `Bool`, `Char`), `Float`, `Ptr`, and `FnPtr`, and `mir_cast_kind` enforces at MIR construction time that mixed pointer/integer casts are tagged distinctly (`PointerExposeProvenance` vs. `PointerWithExposedProvenance`) rather than conflated with `IntToInt` or `PtrToPtr`. Note, however, that `std::ptr::const_ptr::addr()` and `std::ptr::without_provenance()` bypass `PointerExposeProvenance`/`PointerWithExposedProvenance` by using `Transmute` (`rvalue.rs:1093-1161`, verified directly in `--emit=mir`).

---

### 2. `CastKind::IntToInt`: Signedness-Keyed Extension, Truncation, and Provenance of `-1i8 as u32` (`Basis: normative + source + execution + Lean proof`)

#### 2.1 Primary-Source Lowering and Normative Rules

Under the Rust Reference (`rust-lang/reference` `c9cc32825`, `src/expressions/operator-expr.md` L545–720, `r[expr.as.*]` [`normative`]):
- Casting between integers of equal bit width (`T -> U`) preserves the bit pattern verbatim (no-op in two's complement).
- Casting from a narrower integer (`M < N`) zero-extends if the **source** type is unsigned (`Bool`, `u*`, `char`) and sign-extends if the **source** type is signed (`i*`), regardless of whether the destination type is signed or unsigned.
- Casting from a wider integer (`M > N`) truncates the upper `M - N` bits, preserving bits `0..N-1` modulo `2^N`, independent of either source or destination signedness.

In `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:467-470` (`058c70105`; identical in `14210df0e:362-365`) [`source`]:

```rust
(Int(_, is_signed), Int(..)) => bx.intcast(imm, to_backend_ty, is_signed),
(Bool, Int(..)) | (Int(..), Bool) | (Bool, Bool) => {
    bx.intcast(imm, to_backend_ty, false)
}
```

In `compiler/rustc_codegen_llvm/src/builder.rs:1092-1102` [`source`], `intcast` delegates directly to LLVM's `LLVMBuildIntCast2(llbuilder, val, dest_ty, is_signed.to_llvm_bool(), UNNAMED)`. Notice that `to_scalar`'s signedness never appears: `LLVMBuildIntCast2` emits `trunc` when `src_width > dst_width`, `sext` when `src_width < dst_width && is_signed`, `zext` when `src_width < dst_width && !is_signed`, and returns `val` unchanged when widths are equal (`llvm/docs/LangRef.md`, `7ebbe97ce`, L13185–13310 [`normative`]). Meanwhile `assume_scalar_range(bx, imm, from_scalar, from_backend_ty, None)` (`rvalue.rs:464`) attaches LLVM range assumptions for non-full-width types such as `bool` (`[0, 2)`) or `char`.

#### 2.2 Live `rustc` MIR, LLVM IR, and Multi-Mode Execution (`Basis: execution`)

Executing `support/probe_cast_kind_sat_and_strict_prov.py` against `rustc 1.98.0-nightly (14210df0e)` with `LLVM 22.1.6` confirms the exact IR and runtime values across `-O0`, `-O2`, Miri default, and Miri deterministic floats:

| Rust Expression | MIR `CastKind` | Emitted LLVM IR (`-O2` / `nopass`) | Observed Output (`-O0` = `-O2` = Miri) |
| :--- | :--- | :--- | :--- |
| `-1i8 as u32` (`cast_i8_u32`) | `IntToInt` | `define noundef range(i32 -128, 128) i32 @cast_i8_u32(i8 noundef signext %x)` -> `%_0 = sext i8 %x to i32` | `0xffffffff` (`4294967295`) |
| `(-1i8 as u8) as u32` (`cast_i8_u8_u32`) | `IntToInt` -> `IntToInt` | `define noundef range(i32 0, 256) i32 @cast_i8_u8_u32(i8 noundef signext %x)` -> `%_0 = zext i8 %x to i32` | `255` (`0x000000ff`) |
| `0x1234_5678u32 as i8` (`cast_u32_i8`) | `IntToInt` | `%_0 = trunc i32 %x to i8` | `120` (`0x78`) |
| `0x1234_56ffu32 as i8` | `IntToInt` | `trunc i32 %x to i8` | `-1` (`0xff`) |
| `-1i16 as u8` | `IntToInt` | `trunc i16 %x to i8` | `255` (`0xff`) |
| `u32::MAX as i32` | `IntToInt` | identity same-width bitcast-free move | `-1` (`0xffff_ffff`) |
| `true as u32` / `false as i32` | `IntToInt` | `zext i1 %x to i32` | `1` / `0` |

Notice how LLVM's optimizer even propagates input value ranges onto the return attribute (`range(i32 -128, 128)` for `i8 -> u32` vs. `range(i32 0, 256)` for `i8 -> u8 -> u32`) strictly because `cast_i8_u32` uses `sext` while `cast_i8_u8_u32` re-interprets the 8-bit width as unsigned before widening with `zext`.

#### 2.3 Lean `v4.34.1` Mechanization of `IntToInt` (`Basis: execution + derived`)

In Section 2 of `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean`, instead of relying on Lean core `BitVec.toNat_signExtend` or `BitVec.toInt_signExtend_of_le` (which pull `Classical.choice` in Lean `v4.34.1`), we define constructive `bvIsNeg`, `bvToInt`, `bvZeroExtend`, `bvTruncate`, `bvSignExtend`, `castIntToInt`, and `castBoolToInt`, proving constructively without `Classical.choice` (global module axiom footprint `[Quot.sound, propext]`):

- **`castIntToInt_same_width_noop`**: Same-width casts (`dstWidth = srcWidth`) preserve `BitVec` values identically regardless of `srcSigned` or `dstSigned`.
- **`castIntToInt_narrow_truncates_independently_of_sign`**: Narrowing (`dstWidth ≤ srcWidth`) equals `bvTruncate dstWidth x` (`BitVec.ofNat dstWidth x.toNat`) independently of `srcSigned` and `dstSigned`.
- **`castIntToInt_trunc_composition`**: Chained narrowing (`w₃ ≤ w₂ ≤ w₁`) collapses strictly to `bvTruncate w₃ x`.
- **`castIntToInt_zext_composition` and `castIntToInt_sext_composition`**: Chained widening collapses cleanly for unsigned-source (`zext`), signed-source (`sext`), and two's-complement value preservation (`bvToInt (bvSignExtend hi x) = bvToInt x`).
- **`castIntToInt_sext_vs_zext_neg_exact`**: For any negative source `x : BitVec lo` (`0 < lo < hi` and `bvIsNeg x = true`), widening directly with `srcSigned = true` returns `(2^hi - 2^lo) + x.toNat`, whereas widening via an unsigned intermediate (`castIntToInt false ...`) returns `x.toNat`, with exact difference `(2^hi - 2^lo) > 0` — explaining `-1i8 as u32` (`4294967295`) vs. `-1i8 as u8 as u32` (`255`) with difference `2^32 - 2^8 = 4294967040` (`witness_intToInt_asymmetry_and_trunc`, proved by kernel `rfl`).
- **`castIntToInt_widen_then_narrow_roundtrip`**: Widening (`lo ≤ hi`) followed by narrowing back (`≤ lo`) recovers exact `bvTruncate mid x`, ensuring round-trip fidelity when casting `i8 -> u32 -> u8` or `u8 -> u32 -> i8`.

---

### 3. `CastKind::FloatToInt`: Total Saturating Lowering (`@llvm.fptosi.sat` / `@llvm.fptoui.sat`) and Zero-UB Guarantees (`Basis: normative + source + execution + Lean proof`)

#### 3.1 Normative Rule, SSA Lowering, and CTFE/Miri Implementation

Since Rust 1.45 (`RFC 2705`, reflected in `rust-lang/reference` `c9cc32825` `operator-expr.md` L640–668 [`normative`]), `expr as int_type` on any floating-point operand is a **total, UB-free saturating cast** (`float_to_int` coercion):
1. Truncate toward zero (`trunc(x)`): discard the fractional part of any finite float.
2. If `x` is any NaN (quiet or signaling, either sign, any payload), the result is `0`.
3. If `x` is `±Inf` or `trunc(x)` exceeds the destination integer range `[MIN, MAX]`, saturate to `MAX` (when positive / `+Inf`) or `MIN` (when negative / `-Inf`, which is `0` for `u*`).

**Source trace in `rustc` (`058c70105`, unchanged across `14210df0e` and `49d734536`) [`source`]:**
- `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:488` dispatches `(Float(_), Int(_, is_signed)) => bx.cast_float_to_int(is_signed, imm, to_backend_ty)`.
- `compiler/rustc_codegen_ssa/src/traits/builder.rs:400-418` implements `cast_float_to_int`:
  ```rust
  assert!(self.cx().float_type(float_ty).is_some_and(|f| f.is_ieee()));
  assert!(self.cx().int_width(int_ty).is_some());
  if signed { self.fptosi_sat(x, dest_ty) } else { self.fptoui_sat(x, dest_ty) }
  ```
- `compiler/rustc_codegen_llvm/src/builder.rs:1007-1013` unconditionally emits `@llvm.fptoui.sat.*` and `@llvm.fptosi.sat.*`. Critically, `rustc` uses non-saturating `fptoui`/`fptosi` (`builder.rs:1015-1062`, including `llvm.wasm.trunc.{unsigned,signed}` on Wasm targets) **only** for `core::intrinsics::float_to_int_unchecked` (`to_int_unchecked`), never for `CastKind::FloatToInt`.
- **LLVM IR semantics (`llvm/docs/LangRef.md`, `7ebbe97ce`, L22195–22286 [`normative`]):** `@llvm.fptoui.sat.iN.fM(val)` and `@llvm.fptosi.sat.iN.fM(val)` are side-effect-free (`readnone`), never produce `poison` or UB on finite, infinite, or NaN inputs unless `val` itself is already `poison`/`undef`, and clamp NaN to `0`.
- **CTFE & Miri (`compiler/rustc_const_eval/src/interpret/cast.rs:384-429`, [`source`]):** `cast_from_float` converts via `rustc_apfloat` `to_i128` / `to_u128` (where `to_{i,u}128` takes bit width directly and clamps `NaN -> 0`, `> MAX -> MAX`, `< MIN -> MIN`, never returning `Err` or throwing UB!).

#### 3.2 Empirical Differential Matrix (`rustc` `-O0`, `-O2`, LLVM IR, Miri) (`Basis: execution`)

Live `rustc 1.98.0-nightly` emits `@llvm.fptosi.sat.i32.f64`, `@llvm.fptoui.sat.i32.f64`, `@llvm.fptosi.sat.i8.f32`, and `@llvm.fptoui.sat.i8.f32` under both `-O2` and `-C no-prepopulate-passes`, and executes identically across native `-O0`, native `-O2`, Miri (`default`), and Miri (`-Zmiri-deterministic-floats`):

| Rust Expression (`as`) | MIR & LLVM Lowering | Native `-O0` = `-O2` = Miri Output | Unchecked Intrinsic (`to_int_unchecked`) Status |
| :--- | :--- | :--- | :--- |
| `f64::NAN as i32` / `-f64::NAN as i32` / `f64::NAN as u32` | `@llvm.fptosi.sat.i32.f64` / `@llvm.fptoui.sat.i32.f64` | `0` / `0` / `0` | **UB** (poison / instant UB in Miri) |
| signaling `f32::from_bits(0x7f80_0001) as i32` | `@llvm.fptosi.sat.i32.f32` | `0` | **UB** |
| `f64::INFINITY as u32` / `f64::INFINITY as i32` | `@llvm.fptoui.sat` / `@llvm.fptosi.sat` | `4294967295` / `2147483647` | **UB** |
| `f64::NEG_INFINITY as u32` / `f64::NEG_INFINITY as i32` | `@llvm.fptoui.sat` / `@llvm.fptosi.sat` | `0` / `-2147483648` | **UB** |
| `(-1.0_f64) as u32` | `@llvm.fptoui.sat.i32.f64` | `0` (`0` UB warnings) | **UB** (because `-1.0` fails `-1.0 < x`) |
| `(-0.999_f64) as u32` / `(-0.999_f64) as i32` | `@llvm.fptoui.sat` / `@llvm.fptosi.sat` | `0` / `0` | **Defined** (`trunc(-0.999) = 0`, in open interval `(-1, MAX+1)`) |
| `(2147483648.0_f32) as i32` (`2^31`) | `@llvm.fptosi.sat.i32.f32` | `2147483647` (`i32::MAX`) | **UB** (`>= 2^31`, outside `(-2^31 - 1, 2^31)`) |
| `(-2147483904.0_f32) as i32` (below `i32::MIN - 1`) | `@llvm.fptosi.sat.i32.f32` | `-2147483648` (`i32::MIN`) | **UB** |
| `42.9_f64 as i32` / `-42.9_f64 as i32` | `@llvm.fptosi.sat.i32.f64` | `42` / `-42` | **Defined** (`trunc` toward zero) |
| `300.0_f32 as u8` / `-200.0_f32 as i8` | `@llvm.fptoui.sat.i8.f32` / `@llvm.fptosi.sat.i8.f32` | `255` / `-128` | **UB** (out of 8-bit target range) |
| `1e-310_f64 as i32` (subnormal) | `@llvm.fptosi.sat.i32.f64` | `0` | **Defined** (`trunc = 0`) |

#### 3.3 Lean `v4.34.1` Mechanization: Exact Open-Interval Bridge & Total Saturation (`Basis: execution + derived`)

In Section 3 of `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean`, we model IEEE floating values via `Dyadic := { num : Int, exp : Nat }` (`num / 2^exp`), `FloatVal` (`.nan sign isQuiet payload`, `.inf neg`, `.finite d`), exact toward-zero integer truncation `truncDivPow2`, clamping helper `clampInt (intMin signed w) (intMax signed w)`, `satFloatToInt`, `satFloatToIntBV`, and `uncheckedFloatToInt`:

- **`satFloatToInt_bounds`**: For all `0 < w` and **any** `f : FloatVal` (NaN, `±Inf`, arbitrary finite `Dyadic`), `intMin signed w ≤ satFloatToInt signed w f ≤ intMax signed w` (total UB-freedom).
- **`satFloatToInt_nan_zero` & `satFloatToInt_inf_clamps`**: Kernel `rfl` proof that every NaN maps to `0`, `+Inf` maps to `intMax signed w`, and `-Inf` maps to `intMin signed w`.
- **`satFloatToInt_finite_clamps`**: Exhaustive 3-way split for finite inputs (`< intMin -> intMin`, `> intMax -> intMax`, inside `[intMin, intMax] -> truncDivPow2 d.num d.exp`).
- **`satFloatToInt_monotone_non_nan` & `witness_nan_breaks_full_monotonicity`**: Preserves `floatOrderedLe` over `[-∞, +∞]`, while proving `satFloatToInt true 32 (.inf true) < satFloatToInt true 32 (.nan false true 0)` (`-2^31 < 0`), confirming IEEE partial order vs. NaN total ordering hazard.
- **`truncDivPow2_bounds_iff_open_interval` & `satFloatToInt_refines_unchecked`**: Constructively proves `(intMin ≤ truncDivPow2 d.num d.exp ≤ intMax) ↔ inOpenInterval signed w d` (`(intMin - 1) * 2^exp < num ∧ num < (intMax + 1) * 2^exp`) without `Classical.choice` (`nat_div_pow2_lt_of_lt_mul`, `nat_le_div_pow2_of_mul_le`), and proves that on every input where `uncheckedFloatToInt` is defined (`some z`), `satFloatToInt` returns `z` identically.

---

### 4. `CastKind::IntToFloat` & `FloatToFloat`: Ties-to-Even Rounding and Overflow (`Basis: normative + source + execution + Lean proof`)

#### 4.1 Codegen, IEEE-754 Mode, and Concrete Tie/Overflow Probes

Under default Rust floating-point semantics (`rust-lang/reference` `c9cc32825` `operator-expr.md` L612–638 [`normative`]), `IntToFloat` and narrowing `FloatToFloat` round under IEEE-754 `roundTiesToEven`: values strictly between two adjacent representable significands pick the nearest; exact halfway ties (`r = half`) pick the candidate whose least significant significand bit (`q % 2`) is **even** (`0`), carrying into the exponent if `sig = 2^24`. If the rounded magnitude meets or exceeds `2^128` for `f32` (`(2^24 - 1/2) * 2^104 = 2^128 - 2^103`), the result overflows to `±Inf` rather than clamping.
- In SSA codegen (`rvalue.rs:471-482`), signed/unsigned integers emit `sitofp` / `uitofp`, while float narrowing/widening emits `fptrunc` / `fpext`.
- In CTFE/Miri (`interpret/cast.rs:327-429`), `cast_from_int_like` calls `rustc_apfloat`'s `from_i128`/`from_u128` and `cast_from_float` calls `convert`, deterministically implementing `roundTiesToEven` (ignoring host MXCSR flags).

Our live probe binary verifies every `f32` ties-to-even and overflow boundary across `-O0`, `-O2`, and Miri:

| Rust Cast Expression | Mathematical Value | Significand / Halfway State | Observed `f32` Output (`-O0` = `-O2` = Miri) | IEEE `f32` Bits (`to_bits`) |
| :--- | :--- | :--- | :--- | :--- |
| `((1u32 << 24) + 1) as f32` | `16,777,217` | `q = 2^23` (even), `r = 1 = half` | `16777216.0` (tie **down** to even) | `0x4b800000` |
| `((1u32 << 24) + 2) as f32` | `16,777,218` | exact `(2^23 + 1) * 2` | `16777218.0` | `0x4b800001` |
| `((1u32 << 24) + 3) as f32` | `16,777,219` | `q = 2^23 + 1` (odd), `r = 1 = half` | `16777220.0` (tie **up** to even) | `0x4b800002` |
| `((1u32 << 24) + 4) as f32` | `16,777,220` | exact `(2^23 + 2) * 2` | `16777220.0` | `0x4b800002` |
| `i32::MAX as f32` | `2,147,483,647` | rounds up to `2^31` | `2147483648.0` | `0x4f000000` |
| `u128::MAX as f32` | `2^128 - 1` | `≥ 2^128 - 2^103` overflow | `+inf` (`is_infinite() == true`) | `0x7f800000` |
| `i128::MIN as f32` | `-2^127` | exact `-2^23 * 2^104` | `-170141183460469231731687303715884105728.0` (finite!) | `0xff000000` |
| `(((1u64 << 24) + 1) as f64) as f32` | `16,777,217.0` | `fptrunc` tie down to even | `16777216.0` | `0x4b800000` |
| `(1e40_f64) as f32` | `1e40 > f32::MAX` | `fptrunc` overflow to `+inf` | `+inf` | `0x7f800000` |

#### 4.2 Lean `v4.34.1` Mechanization of `IntToFloat` (`Basis: execution + derived`)

Section 4 of `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean` defines constructive `F32Val`, bounded binary-logarithm search `findExp2Aux` (with proved bounds theorem `findExp2Aux_spec`), `roundNatToF32`, and `roundIntToF32`:
- **`roundNatToF32_zero` & `roundNatToF32_exact_below_2p24`**: Every unsigned integer `n < 2^24` converts bit-exactly with zero rounding error.
- **`roundNatToF32_ties_to_even_invariant`**: For every `2^24 ≤ n < 2^130`, proves `24 ≤ e`, `1 ≤ shift`, `2^23 ≤ q < 2^24` (normalized 24-bit significand), and that whenever `r = 2^(shift - 1)` (exact midpoint), the rounded significand satisfies `sig % 2 = 0`.
- **`witness_intToFloat_ties_to_even_and_overflow`**: Kernel-reduced `rfl` proof verifying all four tie/exact steps `(2^24 + 1..4)`, `i32::MAX -> 2^31`, `u128::MAX -> +inf`, `f32::MAX` finite boundary `(2^24 - 1) * 2^104 + 2^103 - 1`, and `i128::MIN -> f32Finite true (2^23) 104`.

---

### 5. `CastKind::PtrToPtr` Wide-to-Thin Lowering & Pre-Cast Validity Diff (`Basis: source + execution + Lean proof`)

#### 5.1 MIR, CTFE/Miri, and ABI Codegen Asymmetry

Casting a wide pointer (`*const [T]` or `*const dyn Trait`, represented as `BackendRepr::ScalarPair` in SSA and `Immediate::ScalarPair(data, meta)` in CTFE/Miri) to a thin pointer (`*const ()` or `*const T` where `T: Sized`) uses `CastKind::PtrToPtr`:
- **SSA Codegen (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:577-588`, [`source`]):**
  ```rust
  mir::CastKind::PtrToPtr if let BackendRepr::ScalarPair { .. } = operand.layout.backend_repr => {
      if let OperandValue::Pair(data_ptr, meta) = operand.val {
          if let BackendRepr::ScalarPair { .. } = cast.layout.backend_repr {
              OperandValue::Pair(data_ptr, meta)
          } else {
              // Cast of wide-ptr to thin-ptr is an extraction of data-ptr.
              OperandValue::Immediate(data_ptr)
          }
      } ...
  }
  ```
- **CTFE/Miri (`compiler/rustc_const_eval/src/interpret/cast.rs:257-285`, [`source`]):** `ptr_to_ptr` returns `ImmTy::from_scalar(data, cast_to)` for wide-to-thin casts (`Scalar(data)` carries `M::Provenance` untouched and discards metadata) or `ImmTy::from_immediate(**src, cast_to)` when sizes match (`2 * ptr_size` wide-to-wide re-type).
- **Important `1.98.0-nightly` -> `main` (`058c70105`) Version Difference (`interpret/cast.rs:35-79`, [`source`]):** On `main` (`058c70105`) and `49d734536`, `interpret::cast` added a pre-cast `M::enforce_validity(self, src.layout)` check prior to `CastKind` dispatch: when validating a wide `RawPtr` (`ScalarPair`), it calls `self.deref_pointer(src)?` (checking wide pointer validity), and on a `FnPtr` input to `FnPtrToPtr`/`PointerExposeProvenance`, it calls `self.get_ptr_fn(ptr)?`. Under `1.98.0-nightly` (`14210df0e`), `ptr_to_ptr` did not run that upfront wide-pointer check prior to `cast_kind` dispatch.
- **Rust ABI vs. `extern "C"` LLVM IR (`Basis: execution`):** Our live `rustc 1.98.0-nightly` probe reveals why Rust ABI functions preserve provenance transparently in LLVM IR while `extern "C"` forces scalarized packing:
  - **`cast_wide_to_thin_rust_abi` (`-O2` and `nopass`):**
    ```llvm
    define noundef ptr @cast_wide_to_thin_rust_abi(
        ptr noundef readnone returned captures(ret: address, provenance) %p.0,
        i64 noundef %p.1) unnamed_addr #0 {
    start:
      ret ptr %p.0
    }
    ```
    Notice `%p.0` keeps LLVM `ptr` type and `captures(ret: address, provenance)` directly!
  - **`cast_wide_to_thin_c_abi` (`extern "C"`, `-O2`):** Passes `{ i64, i64 }` in registers by C ABI struct-lowering rules, extracts element `.0` via `extractvalue { i64, i64 } %p, 0`, and reconstructs `ptr` with **`inttoptr i64 %_0.i to ptr`** (and in `nopass` allocates a temporary `alloca [16 x i8]` + `memcpy`)! Thus while MIR `CastKind::PtrToPtr` never touches integer provenance, crossing a C ABI boundary with a fat pointer struct induces integer-to-pointer round-tripping in LLVM IR!

In Section 5 of our Lean formalization, `ptrToPtrWideToThin w := w.thin` proves `ptrToPtrWideToThin_preserves_addr_and_prov` (`rfl`) and `wideToThin_strict_provenance_witness` cleanly across both `.strict` and `.exposedPermissive` machine modes.

---

### 6. `PointerExposeProvenance`, `PointerWithExposedProvenance`, Strict Provenance, and Miri's Lazy Wildcard Resolution (`Basis: source + execution + Lean proof`)

#### 6.1 Primary-Source Architecture Across `core::ptr`, `rustc`, `LLVM`, and `Miri`

Rust separates *strict-provenance* operations from *exposed-provenance* casts at both library and MIR levels:

1. **Standard Library Provenance API (`library/core/src/ptr/{const_ptr.rs,mod.rs}`, `058c70105`) [`source`]:**
   - `p.addr()` (`const_ptr.rs:152-159`): implemented as `unsafe { mem::transmute(self.cast::<()>()) }` -> lowers to MIR `CastKind::Transmute` (verified via `--emit=mir`: `copy _1 as usize (Transmute)`). Does **not** mark the allocation as exposed in Miri.
   - `p.expose_provenance()` (`const_ptr.rs:186-188`): implemented as `self.cast::<()>() as usize` -> lowers to MIR `CastKind::PointerExposeProvenance` (`copy _1 as usize (PointerExposeProvenance)`).
   - `p.with_addr(addr)` (`const_ptr.rs:204-212`): computes `let self_addr = self.addr() as isize; let dest_addr = addr as isize; let offset = dest_addr.wrapping_sub(self_addr); self.wrapping_byte_offset(offset)` -> preserves `self`'s `Provenance` tag (including `AllocId` or `Wildcard`) with zero int-to-ptr cast! (`--emit=mir` shows `Transmute` + `IntToInt` + `PtrToPtr`).
   - `ptr::without_provenance(addr)` (`mod.rs:929-976`): implemented as `mem::transmute(addr)` -> `CastKind::Transmute`, yielding `Provenance::None` (no provenance).
   - `ptr::with_exposed_provenance(addr)` (`mod.rs:1032-1075`): implemented as `addr as *const T` -> `CastKind::PointerWithExposedProvenance` (`copy _1 as *const u32 (PointerWithExposedProvenance)`).

2. **LLVM Codegen Gap on `addr()` (`rvalue.rs:1135-1138` vs. `LangRef.md:13612-13654`) [`source + execution`]:**
   - Even though `llvm/docs/LangRef.md` (`7ebbe97ce` L13612–13654) defines `ptrtoaddr <ty> <value> to <ty2>` ("captures the address but not the provenance"), `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1135-1138` in `transmute_scalar` contains the explicit upstream comment:
     ```rust
     (Pointer(..), Bool | Int(..)) => {
         // FIXME: this exposes the provenance, which shouldn't be necessary.
         bx.ptrtoint(imm, to_backend_ty)
     }
     ```
   - Live `rustc 1.98.0-nightly --emit=llvm-ir` proves this directly: **both** `cast_ptr_expose` (`PointerExposeProvenance`) **and** `cast_ptr_addr_strict` (`p.addr()`, MIR `Transmute`) lower to `%_0 = ptrtoint ptr %p to i64` on LLVM 22.1.6! At the LLVM IR level today, only Miri/CTFE (because MIR distinguishes `Transmute` from `PointerExposeProvenance`) tracks `addr()` without exposing provenance, whereas LLVM backend passes still observe `ptrtoint` on `addr()`.

3. **Miri `AllocAddresses` (`src/tools/miri/src/alloc_addresses/mod.rs:237-388`, `diagnostics.rs:748`) [`source`]:**
   - `expose_provenance` (`mod.rs:327-358`):
     - If `provenance == Provenance::Wildcard`, returns immediately (already exposed).
     - If `global_state.provenance_mode == ProvenanceMode::Strict`, returns `interp_ok(())` immediately as a **no-op** ("In strict mode, we don't need this, so we can save some cycles by not tracking it"). Therefore, calling `p.expose_provenance()` or `p as usize` **without** a subsequent integer-to-pointer cast does **not** error under `-Zmiri-strict-provenance`!
     - Otherwise marks `global_state.exposed.insert(alloc_id)` (and calls `ecx.expose_tag(alloc_id, tag)?` for Stacked/Tree Borrows).
   - `ptr_from_addr_cast` (`mod.rs:360-388`):
     - `ProvenanceMode::Strict` -> `throw_machine_stop!(TerminationInfo::Int2PtrWithStrictProvenance)`.
     - `ProvenanceMode::Default` -> emits deduplicated warning `NonHaltingDiagnostic::Int2Ptr`, then continues.
     - `ProvenanceMode::Permissive` -> silent, continues.
     - Returns `Pointer::new(Some(Provenance::Wildcard), Size::from_bytes(addr))` — Miri explicitly does **not** resolve the `AllocId` during `int as ptr`, deferring resolution to every memory access (`alloc_id_from_addr`, `mod.rs:237-274`)!
   - Under `-Zmiri-tree-borrows`, `diagnostics.rs:748` additionally warns that Tree Borrows + `int2ptr` weakens alias tracking when wildcard pointers are created.

#### 6.2 Empirical 9-Program × 4-Mode Miri Provenance Matrix (`Basis: execution`)

Live `cargo +nightly miri run` across all four Miri provenance/aliasing flags confirms every branch of `alloc_addresses/mod.rs` with zero discrepancies:

| Probe ID & Behavior Tested | Default Miri | `-Zmiri-strict-provenance` | `-Zmiri-permissive-provenance` | `-Zmiri-tree-borrows` |
| :--- | :--- | :--- | :--- | :--- |
| **`expose_and_with_exposed_cast`** (`p.expose_provenance()`, `with_exposed_provenance(a).read()`) | `rc=0` + warning (`integer-to-pointer cast` + `exposed.insert`) | **`rc=1`** (`unsupported operation: integer-to-pointer casts and ptr::with_exposed_provenance are not supported with -Zmiri-strict-provenance`) | `rc=0`, **no warning** (`OUT=42`) | `rc=0` + Tree Borrows `int2ptr` warning (`OUT=42`) |
| **`expose_fn_and_with_exposed_fn`** (fn ptr expose -> cast back -> call) | `rc=0` + warning (`FN=77`) | **`rc=1`** (strict stop on `Int2Ptr`) | `rc=0`, no warning (`FN=77`) | `rc=0` + Tree Borrows warning (`FN=77`) |
| **`expose_only_no_int_to_ptr`** (`p.expose_provenance()` printed without int2ptr) | `rc=0`, no warning | **`rc=0`, no error** (confirms `expose_provenance` no-op in Strict mode!) | `rc=0`, no warning | `rc=0`, no warning |
| **`strict_provenance_addr_with_addr`** (`p.addr()` + `p.with_addr()` + `read()`) | `rc=0`, **0 warnings** (`STRICT=42`) | **`rc=0`, 0 warnings** | `rc=0`, **0 warnings** | `rc=0`, **0 warnings** |
| **`addr_without_expose_then_int_to_ptr_ub`** (`p.addr()` + `with_exposed_provenance(a).read()`) | **`rc=1` UB** (`pointer ... has no provenance` on deref) | **`rc=1`** (unsupported strict `int2ptr` at cast) | **`rc=1` UB** (`no provenance` on deref) | **`rc=1` UB** (`no provenance` on deref) |
| **`without_provenance_deref_ub`** (`ptr::without_provenance::<u32>(a).read()`) | **`rc=1` UB** (`no provenance`) | **`rc=1` UB** (`no provenance`) | **`rc=1` UB** (`no provenance`) | **`rc=1` UB** (`no provenance`) |
| **`without_provenance_zst_ok`** (`ptr::without_provenance::<[u8; 0]>(0x10).read()`) | `rc=0` (`ZST_OK`) | `rc=0` (`ZST_OK`) | `rc=0` (`ZST_OK`) | `rc=0` (`ZST_OK`) |
| **`wildcard_wrapping_offset_to_exposed_alloc_ok`** (expose `x`, expose `y`, cast `x_addr -> wildcard`, `.wrapping_byte_offset(y - x).read()`) | `rc=0` + warning (`WILDCARD_SHIFT_OK=22`) | **`rc=1`** (strict `int2ptr` stop) | `rc=0`, no warning (`=22`) | `rc=0` + Tree Borrows warning (`=22`) |
| **`wildcard_unexposed_target_alloc_ub`** (expose `x` only, `y` via `addr()` unexposed, shift wildcard `x -> y`, `.read()`) | **`rc=1` UB** (`no provenance`) | **`rc=1`** (strict `int2ptr` stop) | **`rc=1` UB** (`no provenance`) | **`rc=1` UB** (`no provenance`) |

#### 6.3 Lean `v4.34.1` Strict Provenance Refinement & Separation Proofs (`Basis: execution + derived`)

Section 5 of `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean` formalizes a register-plus-allocation small-step provenance machine (`ProvTag := .none | .concrete id | .wildcard`, `ProvMode := .strict | .exposedPermissive`, `AllocEntry`, `Stmt`, `stepStmt`, `evalProg`) faithfully capturing every case in the empirical 9×4 table:

1. **No-Expose Invariant (`ptrAddrStrict_preserves_mem`, `castPtrExposeProv_strict_preserves_mem`, `withAddrPtr_preserves_prov`)**: `p.addr()` leaves all memory allocations and `exposed` flags unmodified in every mode; `CastKind::PointerExposeProvenance` in `.strict` mode leaves `mem` unmodified; `p.with_addr(newAddr)` preserves `p.prov` verbatim (including `.concrete id`, `.none`, or `.wildcard`).
2. **No-Wildcard Invariant (`strict_step_preserves_no_wildcard`)**: Every terminating step under `.strict` preserves `RegsNoWildcard` (no thin or wide register holds `.wildcard`).
3. **Strict-to-Exposed Forward Simulation & Program Refinement (`strict_step_simulates_to_exposed`, `strict_provenance_refinement_aux`, `strict_provenance_refinement`)**: Relating strict and permissive states by `StatesRelated s₁ s₂ := (s₁.regs = s₂.regs ∧ MemSameIgnoringExposed s₁.mem s₂.mem ∧ s₁.trace = s₂.trace)`, every program `prog : List Stmt` that executes cleanly from `initState .strict` (`evalProg prog (initState .strict) = .ok s₁'`) is **guaranteed** to execute cleanly under `initState .exposedPermissive` with identical observable trace (`s₂'.trace = s₁'.trace`), even if the strict execution contains `CastKind::PointerExposeProvenance` (as long as `CastKind::PointerWithExposedProvenance` is never reached).
4. **Six Machine-Checked Differential & Negative Witnesses (`exposed_provenance_separation_witness`, `exposeOnly_succeeds_both_modes`, `addrWithoutExpose_rejected_both_modes`, `wildcardCrossAlloc_separation_witness`, `withoutProvenance_zst_vs_nonzst_witness`, `wideToThin_strict_provenance_witness`)**: Formalizes both the strict-vs-exposed separation (valid `42` under `.exposedPermissive`, `.error .unsupportedStrictIntToPtr` under `.strict`) and every empirical distinction from the 9×4 Miri suite (ZST vs. non-ZST `without_provenance`, cross-allocation `.wildcard` offset onto exposed vs. unexposed target, `expose_only` passing in `.strict`, and wide-to-thin strict roundtrip).

---

### 7. `joshlf/anneal` Gap Assessment (`c131b320e`) (`Basis: source + derived`)

Inspecting `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` confirms why cast semantics require careful extension before any `Rvalue::Cast` support is enabled:
- **`Trusted/MirAst.lean:308 & L612-613` [`source`]:** `MirTy` rejects floating-point types (`Float` -> `.unsupported`), and `Rvalue.Cast` translation fails closed (`Cast` -> `.unsupported`).
- **`Trusted/Correspondence.lean:1858` [`source`]:** `Trusted` correspondence semantics explicitly sets `cast := fun ... => .error .unsupported`.
- **`vendor/lean-miri/Miri/Interpreter/Cast.lean` & `Miri/MIR/Syntax.lean` [`source`]:** Already model `CastKind` interpreter dispatch on the `lean-miri` side, creating an architectural gap between `vendor/lean-miri` (which tracks casts) and `Trusted/MirAst.lean` + `Trusted/MirSemantics.lean` (which reject casts).
- **Mandatory Anneal soundness requirements when adding `CastKind` support [`derived`]:**
  1. Preserve signedness metadata from the **source** MIR operand on `IntToInt` (`sext` vs. `zext`), never inferring extension sign from destination types.
  2. Lower `FloatToInt` strictly as total clamping (`NaN -> 0`, `±Inf -> MIN/MAX`), isolating non-saturating UB solely to `float_to_int_unchecked`.
  3. Separate `CastKind::PointerExposeProvenance` from `Transmute` (`addr()`), rejecting `PointerWithExposedProvenance` whenever targeting strict-provenance verification obligations while allowing wide-to-thin `PtrToPtr` projection without exposing provenance.

## Boundaries

### Not Examined (`not examined`)
- **Non-x86_64 Target Execution:** WebAssembly (`llvm.wasm.trunc.{unsigned,signed}` for unchecked `fptoui`/`fptosi`), ARM64 (`aarch64`), 32-bit `i686`, and strict-aligned/big-endian targets were not compiled or executed locally (`rustc_codegen_llvm/src/builder.rs:1030-1060` was audited by source only).
- **`rustc_apfloat` Precision Internals for `f16` / `f128`:** `f16` and `f128` bit-rounding internals inside `compiler/rustc_const_eval/src/interpret/cast.rs:384-429` and nightly unstable `f16`/`f128` hardware legalization were not probed empirically in `probe_cast_kind_sat_and_strict_prov.py`.
- **SIMD Vector Casts:** Lane-wise SIMD `IntToInt`/`FloatToInt` (`traits/builder.rs:407-413`) and portable `Simd::cast` vector intrinsics were not executed.
- **Cranelift and GCC Codegen Backends:** `rustc_codegen_cranelift` and `rustc_codegen_gcc` cast builders were not audited or executed; findings cover `rustc_codegen_ssa` -> `rustc_codegen_llvm` and CTFE/Miri only.

### Unknown (`unknown`)
- **LLVM `main` `ptrtoaddr` Migration Timeline in `rustc` (`rvalue.rs:1135-1138`):** Whether upstream `rustc` will switch `(Pointer(..), Bool | Int(..))` transmutes (`const_ptr::addr()`) from `bx.ptrtoint` to `llvm/docs/LangRef.md`'s `ptrtoaddr` (`7ebbe97ce:13612-13654`) in an upcoming nightly, and whether LLVM's AliasAnalysis behaves identically for all `Transmute` callers under `ptrtoaddr`, is unknown from audited snapshots.
- **Runtime Performance Impact of Eliminating `exposed` Tracking in LLVM IR:** We did not benchmark downstream optimization improvements unlocked by replacing `ptrtoint` with `ptrtoaddr` on real crates.io binaries.

### Known Not to Apply (`known not to apply`)
- **Pre-`enforce_validity` Behavior on `1.98.0-nightly` vs. `main` (`058c70105`):** The upfront wide-raw-pointer `deref_pointer` and `FnPtr` `get_ptr_fn` validity check in `compiler/rustc_const_eval/src/interpret/cast.rs:37-79` on `main` (`058c70105`) and `49d734536` does **not** apply identically to older `1.98.0-nightly` (`14210df0e`), which dispatched `CastKind` without that pre-cast branch.
- **Tautological Reverse Provenance Refinement:** Permissive/exposed-provenance programs do **not** refine into `-Zmiri-strict-provenance`: as both live Miri (`expose_and_with_exposed_cast`) and Lean witness `exposed_provenance_separation_witness` demonstrate, `PointerWithExposedProvenance` succeeds under `default`/`-Zmiri-permissive-provenance`/`-Zmiri-tree-borrows` yet aborts under `-Zmiri-strict-provenance`.
- **Unchecked Float-to-Int Open-Interval Guarantees for `as`:** Preconditions requiring `-1 < x < 2^w` (`inOpenInterval`) apply **only** to `core::intrinsics::float_to_int_unchecked` (`to_int_unchecked`); ordinary `as` (`CastKind::FloatToInt`) is defined for every float value including `NaN`, `±Inf`, and `-1.0 as u32`.
- **Unconditional Lean Soundness Extrapolation:** `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean` is a standalone Lean `v4.34.1` formalization using constructive `BitVec`, `Dyadic`, normalized `F32Val`, and an abstract 11-statement `MachineState`; it does **not** formally refine LLVM's C++ optimizer, IEEE subnormal arithmetic edge cases beyond `f32` integers, Stacked/Tree Borrows tag-tree protector rules, or `joshlf/anneal`'s `Trusted.MirSemantics`.

### Unsupported (`unsupported`)
- **`joshlf/anneal` (`c131b320e`) `Trusted` Cast & Float Pipeline:** Both `MirTy::Float` (`Trusted/MirAst.lean:308`), `Rvalue::Cast` (`Trusted/MirAst.lean:612-613`), and `Trusted/Correspondence.lean:1858` explicitly fail closed with `.error .unsupported`.
- **`PointerWithExposedProvenance` Under `-Zmiri-strict-provenance`:** Rejected deterministically (`rc=1`, `TerminationInfo::Int2PtrWithStrictProvenance`) for both data pointers and function pointers.
- **Lean Kernel Forbidden Shortcuts Excluded by Design:** This package avoids `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `._unsafe_rec`, and `sorry` across all `2,262` Lean lines; extending the `F32Val` model to arbitrary-precision hardware IEEE bit-vectors without `Classical.choice` would require explicitly porting full IEEE-754 subnormal rounding lemmas.

## Evidence

### 1. Support Artifacts Included in Package

| Artifact Relative Path | Size / Scale | Verification Status & Purpose |
| :--- | :--- | :--- |
| `support/probe_cast_kind_sat_and_strict_prov.py` | Python probe harness | Compiles and executes real `rustc 1.98.0-nightly`, `--emit=mir`, `--emit=llvm-ir` (`-O2` & `-C no-prepopulate-passes`), native `-O0`/`-O2`, Miri `default`, Miri `-Zmiri-deterministic-floats`, and 9×4 Miri provenance matrix inside `tempfile.TemporaryDirectory()`. |
| `support/probe_results.json` | Machine-readable probe receipts | Exited `0`; records `all_outputs_identical: true`, full MIR/LLVM IR excerpts, and all 36 provenance matrix outcomes. |
| `support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean` | `2,262` lines (`95,467` bytes); `73` theorems, `50` `noncomputable def`s, `8` `inductive`s, `5` `structure`s | Typechecked cleanly with `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`); also passes under `-M1024`; MetaM audit (`Elab.runFrontend`) reports `total_added_constants=555`, `in_ns=537`, `theorems=188`, `defs=301`, `inductives=13`, `unsafe_constants=0`, `unsafe_recs=[]`, `distinct_axioms_used=[Quot.sound, propext]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`. |

### 2. Primary Source & Normative Audit Index

| Repository & Verified Commit SHA | Audited File Paths & Lines | Key Verified Fact |
| :--- | :--- | :--- |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`, `main`) | `compiler/rustc_middle/src/mir/syntax.rs` L1493–1552 | `CastKind` 12 variants (`PointerExposeProvenance`, `PointerWithExposedProvenance`, `PointerCoercion`, `IntToInt`, `FloatToInt`, `FloatToFloat`, `IntToFloat`, `PtrToPtr`, `FnPtrToPtr`, `Transmute`, `BoxDerefTransmute`, `Subtype`); borrowck-only `ArrayToPointer`/`MutToConstPointer` note at L1504–1509. |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `compiler/rustc_middle/src/ty/cast.rs` L1–73 | `CastTy` and `mir_cast_kind` MIR cast-kind assignment. |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` L449–634, L1093–1161 | `cast_immediate` (`Int` source-signedness `intcast`, `FloatToInt` via `cast_float_to_int`); `PtrToPtr` wide-to-thin `ScalarPair` extract (L577–588); `PointerExposeProvenance` `bx.ptrtoint` (L514–520); `transmute_scalar` `FIXME` emitting `ptrtoint` on pointer->int transmutes (L1135–1138). |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `compiler/rustc_codegen_ssa/src/traits/builder.rs` L400–418 | `cast_float_to_int` unconditionally calls `fptosi_sat` / `fptoui_sat`. |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `compiler/rustc_codegen_llvm/src/builder.rs` L1003–1105, L1526 | `sext`, `fptoui_sat`, `fptosi_sat`, non-saturating `fptoui`/`fptosi` + Wasm `llvm.wasm.trunc.*` (only used for unchecked intrinsics), `uitofp`, `sitofp`, `fptrunc`, `fpext`, `ptrtoint`, `inttoptr`, `intcast`, `pointercast`, `zext`. |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `compiler/rustc_const_eval/src/interpret/cast.rs` L35–85, L224–429 | Pre-cast `enforce_validity` (`L37–79`); `ptr_to_ptr` `ScalarPair(data, _)` extraction (`L257–285`); `pointer_expose_provenance_cast` (`L287–305`); `pointer_with_exposed_provenance_cast` (`L307–323`); `cast_from_float` saturating `apfloat` conversions (`L384–429`). |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `library/core/src/ptr/{const_ptr.rs,mod.rs}` L152–212, L929–1075 | `addr()` (`mem::transmute`), `expose_provenance()` (`as usize`), `with_addr()` (`wrapping_byte_offset`), `without_provenance` (`mem::transmute`), `with_exposed_provenance` (`as *const T`). |
| `rust-lang/rust` (`058c701055c4b6f60f622d616afc0349911c38c3`) | `src/tools/miri/src/alloc_addresses/mod.rs` L237–388; `diagnostics.rs` L748 | `expose_provenance` no-op in `Strict` mode (`L340–343`); `ptr_from_addr_cast` `TerminationInfo::Int2PtrWithStrictProvenance` / `Wildcard` construction (`L360–388`); `alloc_id_from_addr` lazy deref resolution (`L237–274`); Tree Borrows warning note. |
| `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly`) | Same paths (`syntax.rs:1491`, `rvalue.rs:349-519`, `traits/builder.rs:379-397`, `llvm/builder.rs:960-1463`) | Executed live locally (`LLVM 22.1.6`, `miri 0.1.0`); pre-cast `enforce_validity` check was added in `interpret/cast.rs` later in `49d734536` / `058c70105`, while all `CastKind` SSA and Miri rules match. |
| `rust-lang/rust` (`49d734536222bf28bb6d07d885b3a81d145981da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) | Seed reference / `1.102.0-nightly` toolchain baseline | Confirms continuity of `CastKind` SSA/CTFE lowering rules across intermediate and `1.102.0-nightly` snapshots. |
| `llvm/llvm-project` (`7ebbe97cef9e1aca651aa6df26ccf0441f1f6f88`, `main`) | `llvm/docs/LangRef.md` L13185–13720, L22195–22286 | Definitions of `trunc`, `zext`, `sext`, `fptrunc`, `fpext`, `fptoui`, `fptosi`, `uitofp`, `sitofp`, `ptrtoint`, `ptrtoaddr` (L13612–13654), `inttoptr`, `llvm.fptoui.sat.*`, `llvm.fptosi.sat.*`. |
| `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `master`) | `src/expressions/operator-expr.md` L545–720 | Normative `r[expr.as.*]` rules for integer, saturating float-to-int, ties-to-even int-to-float, and pointer casts. |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `main`) | `trusted/lean/Trusted/MirAst.lean:308,612-613`, `Correspondence.lean:1858`, `vendor/lean-miri/Miri/Interpreter/Cast.lean` | Current `Trusted` pipeline fails closed on `MirTy.Float` and `Rvalue.Cast`; `vendor/lean-miri` holds full `CastKind` interpreter hooks. |

### 3. Selected Kernel-Checked Lean Theorems & Purity Audit (`MirCastKindSaturatingAndStrictProvenanceSoundness.lean`)

Static grep across all `2,262` lines for `\bsorry\b`, `Classical.choice`, `\bomega\b`, `\bbv_decide\b`, `\bnative_decide\b`, `\bpartial\b`, `\bderiving\b`, `noncomputable section`, `_unsafe_rec`, and `\bunsafe\b` returned **`0` matches** (`STATIC_GREP_ZERO_MATCHES`). Lean MetaM inspection reported `0` unsafe constants, `0` `._unsafe_rec` constants, `user_computable_defs` restricted purely to structure field projections, and `distinct_axioms_used=[Quot.sound, propext]`:

| Section | Principal Theorems / Witnesses | Established Guarantee |
| :--- | :--- | :--- |
| Section 1 (Div/Pow2) | `nat_div_pow2_bounds`, `truncDivPow2_mono`, `truncDivPow2_scale`, `nat_div_pow2_lt_of_lt_mul`, `nat_le_div_pow2_of_mul_le`, `nat_div_pow2_le_iff_lt_mul` | Constructive arithmetic foundation avoiding `Classical.choice` from core `Init.Data.BitVec` / `Nat` division lemmas. |
| Section 2 (`IntToInt`) | `castIntToInt_same_width_noop`, `castIntToInt_narrow_truncates_independently_of_sign`, `castIntToInt_trunc_composition`, `castIntToInt_zext_composition`, `castIntToInt_sext_composition`, `castIntToInt_sext_vs_zext_neg_exact`, `castIntToInt_widen_then_narrow_roundtrip`, `witness_intToInt_asymmetry_and_trunc` | Sign- vs. zero-extension two's-complement asymmetry, sign-independent narrowing truncation, and `-1i8 as u32` vs. `-1i8 as u8 as u32` exact witness. |
| Section 3 (`FloatToInt`) | `satFloatToInt_bounds`, `satFloatToInt_nan_zero`, `satFloatToInt_inf_clamps`, `satFloatToInt_finite_clamps`, `satFloatToInt_monotone_non_nan`, `witness_nan_breaks_full_monotonicity`, `truncDivPow2_bounds_iff_open_interval`, `satFloatToInt_refines_unchecked`, `witness_floatToInt_sat_vs_unchecked` | Total `[MIN, MAX]` boundedness, `NaN -> 0`, infinity/out-of-range clamping, non-NaN monotonicity, and exact equivalence between unchecked `inOpenInterval` and saturation agreement. |
| Section 4 (`IntToFloat`) | `findExp2Aux_spec`, `roundNatToF32_zero`, `roundNatToF32_exact_below_2p24`, `roundNatToF32_ties_to_even_invariant`, `witness_intToFloat_ties_to_even_and_overflow` | Exact `< 2^24` conversion, normalized 24-bit significand bounds for `2^24 ≤ n < 2^130`, tie-evenness (`sig % 2 = 0`), and `u128::MAX` overflow vs. `i128::MIN` finiteness. |
| Section 5 (`PtrToPtr` & Provenance) | `ptrToPtrWideToThin_preserves_addr_and_prov`, `withAddrPtr_preserves_prov`, `ptrAddrStrict_preserves_mem`, `castPtrExposeProv_strict_preserves_mem`, `strict_step_preserves_no_wildcard`, `strict_step_simulates_to_exposed`, `strict_provenance_refinement_aux`, `strict_provenance_refinement`, `exposed_provenance_separation_witness`, `exposeOnly_succeeds_both_modes`, `addrWithoutExpose_rejected_both_modes`, `wildcardCrossAlloc_separation_witness`, `withoutProvenance_zst_vs_nonzst_witness`, `wideToThin_strict_provenance_witness` | Wide-to-thin provenance preservation, `strict` no-wildcard invariant, full-program simulation from `.strict` to `.exposedPermissive`, separation counterexample, and all 6 empirical Miri distinctions. |

## Revalidation

Revalidate every claim, probe measurement, Lean proof, and corpus schema constraint using the following self-contained commands from the package / corpus root (using a fresh temporary workspace and pinned commit SHAs):

1. **Re-run Live `rustc`, LLVM IR, and Multi-Mode Miri Probes:**
   ```bash
   python3 reports/rustc-mir-cast-kind-saturating-float-to-int-ties-to-even-and-strict-provenance/support/probe_cast_kind_sat_and_strict_prov.py \
     --out /tmp/probe_results_recheck.json
   ```
   Verify `exit 0`, `all_outputs_identical == true`, presence of `@llvm.fptosi.sat` / `@llvm.fptoui.sat`, `sext` vs. `zext`, `ptrtoint` on `cast_ptr_addr_strict`, `ret ptr %p.0` on `cast_wide_to_thin_rust_abi`, and matching 9×4 Miri exit codes.

2. **Re-check the Lean `v4.34.1` Proof Under Zero-Warning Kernel Enforcement:**
   ```bash
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean" \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-mir-cast-kind-saturating-float-to-int-ties-to-even-and-strict-provenance/support/MirCastKindSaturatingAndStrictProvenanceSoundness.lean
   ```
   Confirm `exit 0` with zero compiler errors or warnings, plus static grep confirming zero `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial`, `deriving`, or `_unsafe_rec`.

3. **Diff Upstream Commits When Tracking Post-`058c70105` `rustc` Changes (Read-Only GitHub API):**
   ```bash
   gh api repos/rust-lang/rust/compare/058c701055c4b6f60f622d616afc0349911c38c3...HEAD \
     --jq '.files[].filename' | grep -E 'mir/syntax\.rs|mir/rvalue\.rs|traits/builder\.rs|llvm/builder\.rs|interpret/cast\.rs|alloc_addresses|const_ptr\.rs'
   ```
   If any listed file changes upstream—in particular if `transmute_scalar` in `rvalue.rs` migrates pointer-to-integer transmutes from `ptrtoint` to `ptrtoaddr`, or if `interpret/cast.rs` modifies `cast_from_float` / `ptr_to_ptr`—re-run step 1 and update the affected sections and `subjects` revisions in `REPORT.json`.

4. **Validate Corpus Schema, Topic Policy, and Catalog Generation:**
   ```bash
   python3 tools/reference.py catalog
   python3 tools/reference.py check
   python3 -m unittest discover -s tests -v
   ```
   All checks must exit `0` with zero validator problems.
