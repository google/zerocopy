# rustc `CastKind::{Transmute, BoxDerefTransmute, Subtype}`: `cg_transmute` 6-Arm `BackendRepr` Dispatch, `@llvm.assume` Scalar-Range Injection, Pointer-to-Integer Provenance Asymmetry, and `AbstractByte` Padding Semantics

## Summary

**Observation boundary.** Primary source claims in this report are established by direct inspection of `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, 2026-11-11, LLVM 23.1.5) and cross-checked against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, 2026-05-31, LLVM 22.1.6), together with `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`. Live compiler, MIR-dump, CTFE, and Miri executions (`22/22` automated checks in `support/probe_transmute_backend_repr_and_provenance.py`) were run on `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`x86_64-unknown-linux-gnu`) and paired with a retained Miri + LLVM 23.1.5 execution record from `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`support/recorded_observation_rustc_3ef0c22c.json`). Formal semantic claims are kernel-checked in `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) in `support/TransmuteByteModelAndCodegenRefinement.lean` (`0` `sorry`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, `0` `._unsafe_rec`).

1. **Three MIR `CastKind` variants share `rustc`'s transmute machinery, split across two codegen entry points.** `LowerIntrinsics` lowers both `core::mem::transmute` and `core::intrinsics::transmute_unchecked` to `Rvalue::Cast(CastKind::Transmute, ..)` (`lower_intrinsics.rs:289-313`); `Subtyper` inserts `CastKind::Subtype` wherever type erasure leaves distinct source and destination types on an assignment (`add_subtyping_projections.rs:21-72`); and `ElaborateBoxDerefs` (at `3ef0c22cd`) emits `CastKind::BoxDerefTransmute` from `BoxRaw<T>` to `*const T` (`elaborate_box_derefs.rs:60-68`). When the destination local is backed by a memory `PlaceRef`, `codegen_rvalue` routes `Transmute | Subtype` to `codegen_transmute`, which stores into the destination at the **destination's** alignment (`rvalue.rs:186-193, 306-329`). When the destination is an SSA `LocalRef::PendingOperand`, `codegen_rvalue_operand` routes `Transmute | BoxDerefTransmute | Subtype` to `codegen_transmute_operand` (`rvalue.rs:335-443, 618-620`).
2. **`codegen_transmute_operand` (`cg_transmute`) dispatches across six `BackendRepr` arms after layout-pointer-equality and size/inhabitedness guards (`rvalue.rs:341-442`).** After rejecting non-ZST `BackendRepr::Memory` destinations (`span_bug!`), short-circuiting interned `abi::Layout::eq`, and emitting `unreachable` + `poison` on size mismatch or uninhabited types, it selects: (Arm 1) `OperandValue::ZeroSized` when `cast.is_zst()`; (Arm 2) typed load from `OperandValue::Ref` at the **source** place's alignment when the source is `BackendRepr::Memory` (`[u8; 16] -> u128` emits `load i128, ptr %_2, align 1`); (Arm 3) `transmute_scalar` for same-size `Scalar -> Scalar`; (Arm 4a/4b) SSA `bitcast` for `SimdVector` and `SimdScalableVector` strictly when both lane scalars are initialized `Int` or `Float` (`vector_can_bitcast`, excluding pointer-lane SIMD); (Arm 5) in-register pair `transmute_scalar` for `ScalarPair -> ScalarPair` strictly when `in_a.size == out_a.size && in_b.size == out_b.size && in_offset == out_offset` (the explicit `in_offset == out_offset` guard was added between `14210df0e` and `3ef0c22cd`); and (Arm 6) stack `PlaceValue::alloca(max(src.size, dst.size), max(src.align, dst.align))` bracketed by `@llvm.lifetime.start.p0` / `@llvm.lifetime.end.p0` for `Scalar ⇌ ScalarPair`, mismatched `Scalar` union sizes, mismatched `ScalarPair` offsets/sizes, and pointer-lane SIMD (`<4 x ptr> -> <4 x i64>`).
3. **`transmute_scalar` injects `@llvm.assume` at the cast site whenever `-C opt-level != 0` and the target (or source) scalar `WrappingRange` is strictly narrower than the counterpart's known range (`rvalue.rs:1118, 1146, 1156-1194`).** `BuilderMethods::assume_integer_range` (`traits/builder.rs:289-304`) encodes any contiguous or modular-wrapping `WrappingRange { start, end }` into a single unsigned comparison: `shifted = (start == 0) ? imm : sub(imm, start)`, `width = wrapping_sub(end, start)`, `icmp ule shifted, width`, `call void @llvm.assume(i1 cmp)`. Consequently, `let _ = transmute::<u32, NonZeroU32>(x); x == 0` emits `sub i32 %x, 1; icmp ule i32 %0, -2; call void @llvm.assume(i1 %1)` even when the `NonZeroU32` result is immediately discarded and never crosses a function ABI boundary (`range(...)` attribute), allowing LLVM `-C opt-level=2` to fold `x == 0` to `ret i1 false`.
4. **Pointer-to-integer transmutation exhibits a strict semantic asymmetry between Rust OpSem/Miri and LLVM codegen.** In `rustc_const_eval` / Miri, `p as usize` (`CastKind::PointerExposeProvenance`) calls `M::expose_provenance` (`cast.rs:298`, `alloc_addresses/mod.rs:327-358`), recording `alloc_id` in `global_state.exposed` so `core::ptr::with_exposed_provenance(addr)` (`Provenance::Wildcard`) recovers access (`rc = 0`). By contrast, `transmute::<*const T, usize>(p)` (`CastKind::Transmute`) executes `copy_op_allow_transmute`, validating the destination as `usize` via `Allocation::read_scalar(..., read_provenance: false)` (`allocation.rs:717-725`) and `clear_provenance` (`validity.rs:901`) **without** calling `M::expose_provenance`: at compile time (`Prov::OFFSET_IS_ADDR == false`) CTFE rejects it with `error[E0080]: unable to turn pointer into integer`, and at runtime in Miri (`OFFSET_IS_ADDR == true`) `with_exposed_provenance(addr)` yields `0x...[noalloc]` dangling-pointer UB (`rc = 1`) even under `-Zmiri-permissive-provenance`. Meanwhile, LLVM codegen lowers `(Pointer, Int)` and `(Pointer, Float)` via `bx.ptrtoint` (`rvalue.rs:1124-1127, 1133-1136`, annotated `// FIXME: this exposes the provenance, which shouldn't be necessary`). Thus LLVM codegen is a **strict one-way forward refinement** (`OpSem ⊑ LLVM`) of Rust OpSem: programs that pass LLVM execution can still be immediate Undefined Behavior in Rust/Miri.
5. **Typed copies and transmutes operate on byte-level `AbstractByte` state (`Uninit`, `Init(b)`, `PtrFrag(alloc, ofs, b)`), actively resetting struct padding to `Uninit` while preserving full byte state only across union data ranges.** In `copy_op_allow_transmute` (`place.rs:911-943`), whenever `src.ty != dest.ty`, Miri runs `validate_place` with `reset_provenance_and_padding = true` first at `src.layout` and then at `dest.layout`. `ValidityVisitor::reset_padding` (`validity.rs:1126-1174`) overwrites every byte outside `data_bytes` with `Uninit`: transmuting `0xFF22_3311u32 -> PadPair(u8, u16) -> u32` wipes byte `1` (`0xFF`) to `Uninit` during the first transmute and faults with uninitialized-memory UB on the second (`rc = 1`). Conversely, `[MaybeUninit<u8>; N]` hits `visit_union` (`validity.rs:1307-1337`), whose `union_data_range` covers all `N` bytes without reading scalars or clearing provenance, preserving `Uninit` padding (`PadPair -> [MaybeUninit<u8>; 4]`, `rc = 0`) and pointer provenance (`*const u32 -> [MaybeUninit<u8>; 8] -> *const u32`, `rc = 0` under `-Zmiri-strict-provenance`, whereas `[u8; 8]` calls `alloc.clear_provenance()` at `validity.rs:1480` and faults `rc = 1`).
6. **`CastKind::BoxDerefTransmute` is strictly stronger than `CastKind::Transmute` in OpSem and identical in codegen.** Before calling `copy_op_allow_transmute`, `eval_rvalue_into_place` (`cast.rs:206-214`) transmutes the source immediate to `Box<T>` and executes `self.deref_pointer(&ptr)?`, enforcing non-null, aligned, live-allocation `Box<T>` dereferenceability even when the raw-pointer result is never dereferenced in MIR.
7. **The Lean 4.34.1 formalization (`TransmuteByteModelAndCodegenRefinement.lean`) kernel-checks 12 principal theorems with zero non-constructive axioms.** For the mechanized model, it proves: (i) exact equivalence of `assume_integer_range`'s single `sub + icmp ule` formula with `WrappingRange.contains` across both contiguous and wrapping ranges (`assumeIntegerRangeCheck_eq_contains`); (ii) necessary and sufficient scalar `SafeTransmute` conditions (`nSrc = nDst ∧ RangeContainsOpt rSrc rDst nSrc`, `safeTransmute_scalar_iff`) and padding-to-initialized byte UB (`uninit_byte_violates_initBits_dst`); (iii) end-to-end forward refinement `evalTransmuteOpSem ⊑ evalCgTransmuteLLVM` (`cgTransmuteLLVM_refines_opSem_end_to_end`) together with a constructive disproof of reverse refinement (`ce1`, `not_opSem_refines_from_cgTransmuteLLVM`); (iv) exact equivalence of Arm 5 register-pair `ScalarPair` transmutation and Arm 6 `alloca` spill/reload whenever `outA = aSz`, `outB = bSz`, and `outBOfs = bOfs` (`scalarPair_reg_transmute_eq_alloca_spill`), paired with a constructive byte-corruption/UB counterexample when `inBOfs != outBOfs` (`ce3`); and (v) constructive witnesses for padding reset (`ce2`), `BoxDerefTransmute` dangling-pointer rejection (`boxDerefTransmute_rejects_dangling_ptr_unlike_transmute`), and `0u32 -> NonZeroU32` UB (`zero_u32_to_nonZeroU32_is_ub`).
8. **Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) currently rejects all `Rvalue::Cast` variants fail-closed (`Rvalue.unsupported` -> `FaultKind.unsupported`), whereas vendored `lean-miri` already models `Transmute | Subtype | BoxDerefTransmute`.** Extending Anneal's trusted MIR semantics to admit transmute casts or post-inlining MIR bodies requires tracking per-byte initialization and provenance (`AbstractByte`), enforcing two-pass `src`/`dst` validity and padding reset, discharging target `WrappingRange` proof obligations at every transmute site (even when the destination local is unused), and treating OpSem-to-LLVM correspondence as a one-way refinement rather than a bisimulation.

## Applicability

### Covered Subjects and Roles

| Short handle | Subject in `REPORT.json` | Role in this report |
|---|---|---|
| `3ef0c22cd` | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, 2026-11-11, LLVM 23.1.5) | **Primary source baseline** (all unqualified `rustc` file paths and line numbers refer to `3ef0c22cd`) and source of the retained Miri + LLVM 23.1.5 execution record (`support/recorded_observation_rustc_3ef0c22c.json`). |
| `14210df0e` | `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, 2026-05-31, LLVM 22.1.6, `x86_64-unknown-linux-gnu`) | **Executed toolchain** (`rustc` LLVM IR, MIR pass dumps, CTFE, and Miri for all 22 automated checks in `support/probe_results_rustc_14210df0e.json`) and **cross-version source comparison** point. |
| `anneal@c131b320e` | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | Audited for `Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`, and `vendor/lean-miri` handling of `Rvalue::Cast` and `copy_op_allow_transmute`. |
| `lean@5045d0056` | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`) | Kernel typechecker and `Lean.Environment` axiom auditor executed on `support/TransmuteByteModelAndCodegenRefinement.lean`. |

### Shared vs. Version-Specific `rustc` Behavior (`14210df0e` vs. `3ef0c22cd`)

Direct source comparison across `14210df0e` and `3ef0c22cd` establishes which mechanisms are invariant across both revisions and where `rustc` changed between 2026-05-31 and 2026-11-11:

| Subsystem / Mechanism | `14210df0e` (`1.98.0-nightly`, LLVM 22.1.6) | `3ef0c22cd` (`1.102.0-nightly`, LLVM 23.1.5) | Impact on Claims |
|---|---|---|---|
| `LowerIntrinsics` lowering of `transmute` and `transmute_unchecked` | Emits `Rvalue::Cast(CastKind::Transmute, ..)`; unreachable destination becomes `TerminatorKind::Unreachable` | Identical semantics (`lower_intrinsics.rs:289-313`) | Shared across both revisions. |
| `Subtyper` (`add_subtyping_projections.rs`) | Inserts `CastKind::Subtype` after borrowck when erased region types still differ | Identical algorithm (`add_subtyping_projections.rs:21-72`) | Shared across both revisions. |
| `CastKind::BoxDerefTransmute` & `BoxRaw<T>` | **Absent**; `ElaborateBoxDerefs` projects to `NonNull<T>` and emits `CastKind::Transmute` | **Present** (`syntax.rs:1537`, `elaborate_box_derefs.rs:60-68`, `cast.rs:206-218`, `validate.rs:1404-1445`) | `BoxDerefTransmute` claims apply to `3ef0c22cd` (source + Lean model), not `14210df0e`. |
| `BackendRepr::ScalarPair` representation & Arm 5 guard in `codegen_transmute_operand` | Tuple variant `BackendRepr::ScalarPair(in_a, in_b)` (`b_offset` computed implicitly from `in_a.size.align_to(in_b.align)`); Arm 5 checks `in_a.size(cx) == out_a.size(cx) && in_b.size(cx) == out_b.size(cx)` (`rvalue.rs:312-320`) | Struct variant `BackendRepr::ScalarPair { a, b, b_offset }`; Arm 5 checks `in_a.size(cx) == out_a.size(cx) && in_b.size(cx) == out_b.size(cx) && in_offset == out_offset` (`rvalue.rs:410-422`, mirrored in `gvn.rs:747`) | Explicit `b_offset` decouples second-element offset from `in_b.align` (needed when field alignment exceeds scalar primitive alignment); Lean theorem `scalarPair_reg_transmute_eq_alloca_spill` and counterexample `ce3` formalize why `in_offset == out_offset` is both necessary and sufficient. |
| `codegen_transmute_operand` 6-arm structure, `vector_can_bitcast`, `alloca` + `lifetime.start/end` | Present (`rvalue.rs:248-340`) | Present (`rvalue.rs:335-443`); adds `SimdScalableVector` arm (`:403-409`) alongside `SimdVector` (`:395-401`) | All 6 non-scalable dispatch arms produce identical pre-pass LLVM IR instructions across LLVM 22.1.6 and LLVM 23.1.5 (modulo `!guid` function metadata in `3ef0c22cd`). |
| `transmute_scalar` & `assume_scalar_range` (`assume_integer_range`, `assume_nonnull`) | Identical dual-site `assume_scalar_range` calls and `sub` + `icmp ule` + `@llvm.assume` lowering | Identical (`rvalue.rs:1082-1194`, `traits/builder.rs:289-317`) | Shared across both revisions; verified by byte-matching IR bodies in `14210df0e` and `3ef0c22cd`. |
| Miri `CastKind::Transmute` vs `PointerExposeProvenance` & `reset_padding` / `visit_union` | Identical two-pass `copy_op_allow_transmute`, `read_scalar(..., false)`, `clear_provenance`, `reset_padding`, and `visit_union` | Identical (`cast.rs:96-106, 192-218, 287-323`, `place.rs:883-943`, `validity.rs:889-905, 1126-1174, 1307-1337`) | Shared across both revisions; all 5 overlapping Miri matrix cases produce identical exit codes and UB diagnostics on `14210df0e` and `3ef0c22cd`. |

### Configuration, Target, ABI, and Optimization Scope

1. **Target architecture and endianness**: All live executions and retained records use `x86_64-unknown-linux-gnu` (64-bit pointers, little-endian byte order, `Align(8)` for `u64`/pointers, `Align(16)` for `i128` on LLVM 22/23 x86-64). The primary-source dispatch rules in `rustc_codegen_ssa` and `rustc_const_eval` are target-independent, except where concrete layouts depend on pointer width or endianness (`decodeLE` in the Lean model fixes little-endian byte order; concrete counterexamples `ce1`–`ce3` instantiate 4-byte layouts for compact kernel reduction, while universal theorems quantify over arbitrary byte lengths `n`, `aSz`, `bSz`, `bOfs`, and `totalSize`).
2. **Pre-pass vs. post-optimization LLVM IR**: Pre-pass LLVM IR observations use `-C opt-level=1 -Z no-prepopulate-passes -C codegen-units=1`. `-C opt-level=1` is mandatory to observe `assume_scalar_range` because `assume_scalar_range` returns immediately when `sess().opts.optimize` is `OptLevel::No` (`rvalue.rs:1163-1165`); `-Z no-prepopulate-passes` disables LLVM's middle-end optimization pipeline so the emitted `.ll` file records `rustc_codegen_ssa`'s exact instruction selection before SROA, InstCombine, or GVN rewrite `alloca`s and `@llvm.assume` calls. One probe (`tm_9_opt_level_2_ir`) additionally runs with `-C opt-level=2` (without `-Z no-prepopulate-passes`) to demonstrate LLVM's downstream folding of `x == 0` under `@llvm.assume`.
3. **Calling convention interaction for SIMD probes**: Under the default `"Rust"` calling convention on `x86_64-unknown-linux-gnu`, `#[repr(simd)]` arguments and return values are passed indirectly in memory (`PassMode::Indirect` / `sret`), which places the MIR return local `_0` in memory (`LocalRef::Place`) and routes `_0 = move _1 as F32x4 (Transmute)` through `codegen_transmute` rather than `codegen_transmute_operand`. Using `extern "C"` (and `#[target_feature(enable = "avx")]` for 256-bit `<4 x ptr>`) passes SIMD vectors in SSA vector registers (`PassMode::Direct` -> `OperandValue::Immediate` / `LocalRef::PendingOperand`), exercising Arms 4a and 6 of `codegen_transmute_operand` directly.
4. **Miri provenance flags**: Miri's default mode warns on integer-to-pointer casts while allowing exposed-provenance lookup; `-Zmiri-permissive-provenance` suppresses the warning while keeping the exact same `global_state.exposed` semantics (`alloc_addresses/mod.rs:367-379`); `-Zmiri-strict-provenance` rejects `usize as *const T` / `with_exposed_provenance` unconditionally (`TerminationInfo::Int2PtrWithStrictProvenance`) while still permitting pointer-preserving byte copies through `[MaybeUninit<u8>; N]`.
5. **Model boundary**: Theorems in `support/TransmuteByteModelAndCodegenRefinement.lean` are machine-checked mathematical theorems about the formalized byte/layout/provenance semantics defined in that file. Their connection to `rustc` rests on the explicit line-by-line source correspondence and the 22 empirical `rustc`/Miri checks documented below, not on automated extraction from `rustc`'s Rust source.

## Findings

### 1. MIR Transmute Cast Kinds, Creation Passes, Validator Invariants, and the Two-Path Codegen Split

Basis: source (`3ef0c22cd`, `14210df0e`) + execution (`14210df0e` MIR pass dumps and LLVM IR) + retained record (`3ef0c22cd`).

#### 1.1 The Three Transmute-Family `CastKind` Variants

`compiler/rustc_middle/src/mir/syntax.rs:1492-1541` defines `CastKind`. Alongside value-converting casts (`PointerExposeProvenance`, `PointerWithExposedProvenance`, `PointerCoercion`, `IntToInt`, `FloatToInt`, `FloatToFloat`, `IntToFloat`, `PtrToPtr`, `FnPtrToPtr`), three variants perform layout-reinterpreting transmutation:

```rust
// compiler/rustc_middle/src/mir/syntax.rs:1533-1540 (@ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1)
Transmute,
/// Identical to `Transmute`, except that the source must be valid as a `Box`
/// of the target's pointee type (i.e., non-null, aligned, dereferenceable).
/// Target must be a raw pointer.
BoxDerefTransmute,
Subtype,
```

Each variant enters MIR through a distinct `PassPolicy::Required` pass in `compiler/rustc_mir_transform/`:

1. **`CastKind::Transmute` via `LowerIntrinsics` (`compiler/rustc_mir_transform/src/lower_intrinsics.rs:289-313`)**: Both `sym::transmute` (type-checked for equal sizes at HIR/typeck when monomorphic, though post-monomorphization or unreachable polymorphic instantiations can still differ) and `sym::transmute_unchecked` (which explicitly skips compile-time size-equality checking) are lowered in-place from a `TerminatorKind::Call` into an assignment plus `Goto` (or `TerminatorKind::Unreachable` when `target` is `None`, e.g., transmuting to an uninhabited type such as `!` or `core::convert::Infallible`):
   ```rust
   // compiler/rustc_mir_transform/src/lower_intrinsics.rs:289-313
   sym::transmute | sym::transmute_unchecked => {
       let dst_ty = destination.ty(local_decls, tcx).ty;
       let [arg] = take_array(&mut args);
       if let Some(target) = *target {
           *terminator = TerminatorKind::goto(target);
       } else {
           // We can get here even for reachable code, e.g. when transmuting to an
           // uninhabited type. Look at the type so `rustc_monomorphize` sees errors.
           let _ = tcx.layout_of(typing_env.as_query_input(dst_ty));
           *terminator = TerminatorKind::Unreachable;
       }
       // Always emit the cast, even if we transmute to an uninhabited type: that makes sure
       // people cannot transmute uninit data to `!` without triggering UB, and it makes
       // sure that `rustc_monomorphize` sees errors when computing the layout of the source type.
       patch.add_assign(
           block_end,
           destination,
           Rvalue::Cast(CastKind::Transmute, arg.node, dst_ty),
       );
   }
   ```
   Confirmed empirically in `probe_results_rustc_14210df0e.json` (`mir_lower_intrinsics_after_cast_lines`): `LowerIntrinsics.after.mir` rewrites `std::mem::transmute::<u32, NonZero<u32>>(move _2)` into `_0 = move _2 as std::num::NonZero<u32> (Transmute);`.
2. **`CastKind::Subtype` via `Subtyper` (`compiler/rustc_mir_transform/src/add_subtyping_projections.rs:21-72`)**: During MIR borrowck, `compiler/rustc_borrowck/src/type_check/mod.rs:1603-1604` explicitly forbids `CastKind::Subtype` (`bug!("CastKind::Subtype shouldn't exist in borrowck")`) because borrowck checks subtyping directly on plain assignments (`_0 = move _1`, e.g. coercing `for<'a> fn(&'a u8) -> &'a u8` to `fn(&'static u8) -> &'static u8` or `&'static T` to `&'a T`). Immediately after borrowck transitions MIR out of analysis, `Subtyper` compares `tcx.erase_and_anonymize_regions(place_ty)` against `tcx.erase_and_anonymize_regions(rval_ty)` on every non-reborrow, non-deref-temp assignment; when higher-ranked binder erasure leaves distinct `Ty`s (such as `for<'a> fn(&'a u8) -> &'a u8` vs `fn(&u8) -> &u8`), it introduces a fresh local `temp` and emits `place = move temp as place_ty (Subtype)`. Confirmed empirically (`mir_subtyper_after_cast_lines`): `_0 = move _2 as fn(&u8) -> &u8 (Subtype);`.
3. **`CastKind::BoxDerefTransmute` via `ElaborateBoxDerefs` (`compiler/rustc_mir_transform/src/elaborate_box_derefs.rs:51-68` at `3ef0c22cd`)**: Rewrites every `Deref` of a `Box<T, A>` local `_b` by projecting field `0` (`_b.0: BoxRaw<T>`) and assigning `_ptr = copy (_b.0: BoxRaw<T>) as *const T (BoxDerefTransmute)`.

MIR validation (`compiler/rustc_mir_transform/src/validate.rs:1404-1453`) enforces structural well-formedness on all three variants:
- `CastKind::Transmute` (`:1404-1424`): requires both source and target types to be `Sized` (`check_sized`). Size equality is **not** required by MIR validation because `transmute_unchecked` with unequal sizes is valid MIR whose execution is runtime Undefined Behavior.
- `CastKind::BoxDerefTransmute` (`:1425-1445`): requires both source and target types to be `Sized`, and requires `target_type.is_raw_ptr()`.
- `CastKind::Subtype` (`:1446-1453`): checks `util::sub_types(self.tcx, self.typing_env, operand_ty, target_type)`.

#### 1.2 The Two-Path Codegen Split (`codegen_transmute` vs. `codegen_transmute_operand`)

In `compiler/rustc_codegen_ssa/src/mir/statement.rs:20-68`, `FunctionCx::codegen_statement` inspects the destination `Place`:
- If the destination has projections or its base local was allocated as `LocalRef::Place` / `LocalRef::UnsizedPlace` (which includes all `BackendRepr::Memory` locals, any local whose address is taken, and indirect ABI return places), `statement.rs:23, 64` calls `self.codegen_rvalue(bx, llval, rvalue)`.
- If the destination is an unprojected SSA local in `LocalRef::PendingOperand` (possible only for ZST, `Scalar`, `ScalarPair`, `SimdVector`, or `SimdScalableVector`), `statement.rs:38` calls `self.codegen_rvalue_operand(bx, rvalue)`.

This creates a critical **alignment and dispatch split** across `rvalue.rs:186-193, 295-298, 306-363, 618-620`:

1. **Memory-destination path (`codegen_transmute`, `rvalue.rs:186-193, 306-329`)**:
   - `codegen_rvalue` matches `Rvalue::Cast(CastKind::Transmute | CastKind::Subtype, ref operand, _)` and delegates to `codegen_transmute(bx, src, dest)`.
   - If `src.layout.size != dst.layout.size || src.layout.is_uninhabited() || dst.layout.is_uninhabited()`, it emits `bx.unreachable_nonterminator()`.
   - Otherwise it executes `src.store_with_annotation(bx, dst.val.with_type(src.layout))` (`rvalue.rs:327`). Because `PlaceValue::with_type` changes only the Rust layout while preserving `dst.val.align`, the store uses the **destination place's alignment** even when `src.layout.align > dst.layout.align` (for example, transmuting an SSA `u32` into `[u8; 4]` emits an `align 1` store).
   - **Subtlety for `CastKind::BoxDerefTransmute`**: `rvalue.rs:187` matches only `CastKind::Transmute | CastKind::Subtype`, omitting `CastKind::BoxDerefTransmute`! If a `BoxDerefTransmute` ever assigns into a memory-backed `PlaceRef` (for instance, if the raw-pointer temporary has its address taken or `-C opt-level=0` spills locals), `codegen_rvalue` falls through to the catch-all `_ =>` arm (`rvalue.rs:295-298`), which calls `self.codegen_rvalue_operand(bx, rvalue)` followed by `val.store_with_annotation(bx, dest)`. That fallthrough **never triggers** the `BackendRepr::Memory` `span_bug!` at `rvalue.rs:341-345` because MIR validation guarantees `BoxDerefTransmute`'s target type is a raw pointer (`*const T` / `*mut T`), whose `BackendRepr` is always `Scalar` (thin pointer) or `ScalarPair` (wide pointer), never `Memory`!
2. **SSA-destination path (`codegen_transmute_operand`, `rvalue.rs:335-443, 618-620`)**:
   - `codegen_rvalue_operand` matches `Rvalue::Cast(CastKind::Transmute | CastKind::BoxDerefTransmute | CastKind::Subtype, ref operand, cast_ty)` and calls `self.codegen_transmute_operand(bx, operand, cast)`. Note that `BoxDerefTransmute` emits **zero extra dereferenceability checks or `@llvm.assume(dereferenceable)` calls** in codegen: `rustc` relies solely on `NonNull<T>`'s niche (`WrappingRange` excluding `0`) and treats `BoxDerefTransmute` identically to `Transmute`.

### 2. `FunctionCx::codegen_transmute_operand` Pre-Guards and the 6 `BackendRepr` Dispatch Arms

Basis: source (`3ef0c22cd` `rvalue.rs:335-443`, `14210df0e` `rvalue.rs:248-340`, `3ef0c22cd` `gvn.rs:733-760`) + execution (`14210df0e` `tm_1`..`tm_11` and `subtype_hrtb_fn_ptr`) + retained record (`3ef0c22cd` `tm_1`..`tm_6`).

#### 2.1 The Three Pre-Guards (`rvalue.rs:341-363`)

Before inspecting `BackendRepr` arms, `codegen_transmute_operand` executes three sequential guards:

1. **Non-ZST `Memory` destination ICE guard (`rvalue.rs:341-345`)**: If `cast.backend_repr` is `BackendRepr::Memory { .. }` and `!cast.is_zst()`, it aborts compilation with `span_bug!(self.mir.span, "Use codegen_transmute to transmute to {cast:?}")`. SSA locals with `BackendRepr::Memory` (unless ZST) are always allocated as `LocalRef::Place` during function prologue setup, so reaching `codegen_transmute_operand` with a non-ZST `Memory` target indicates a broken caller invariant.
2. **Interned `abi::Layout::eq` fast path (`rvalue.rs:349-351`)**: Because `LayoutData` is interned (`Layout<'tcx>` wraps `Interned<'tcx, LayoutData>`), pointer equality `abi::Layout::eq(&operand.layout.layout, &cast.layout)` immediately returns `operand.val` with zero instructions emitted. This fast path handles `CastKind::Subtype` (such as `subtype_hrtb_fn_ptr`: `for<'a> fn(&'a u8) -> &'a u8` to `fn(&'static u8) -> &'static u8`, which compiles to `ret ptr %f` with zero instructions) and transparent wrapper transmutes (`Newtype(u32) -> u32`).
3. **Unconditional-UB guard (`rvalue.rs:354-363`)**: If `operand.layout.size != cast.size || operand.layout.is_uninhabited() || cast.is_uninhabited()`, `rustc` emits `bx.unreachable_nonterminator()` (`unreachable` in LLVM IR) and synthesizes `OperandValue::poison(bx, cast)` so subsequent SSA instructions in the basic block remain type-correct in LLVM IR.

#### 2.2 Complete 6-Arm `BackendRepr` Dispatch Table (`rvalue.rs:379-442`)

| Arm | Source `(operand.val, operand.layout.backend_repr)` | Target `cast.backend_repr` | Side Condition (`rvalue.rs`) | Emitted Backend Operations | Empirical Probe Witness |
|---|---|---|---|---|---|
| **1 (ZST)** | Any `(val, repr)` | Any with `cast.is_zst() == true` | `cast.is_zst()` (`:380`) | Returns `OperandValue::ZeroSized` (0 LLVM instructions; note any ZST with `is_uninhabited()` was already caught at `:356`). | `tm_11_zst_transmute`: `() -> PhantomZst` -> `ret void` |
| **2 (`Memory -> SSA`)** | `(OperandValue::Ref(source_place_val), BackendRepr::Memory { .. })` | Non-ZST `Scalar`, `ScalarPair`, or `Simd*` | `assert_eq!(source_place_val.llextra, None)` (`:381-386`) | `bx.load_operand(source_place_val.with_type(cast)).val` using **`source_place_val.align`** (never `cast.align`!). Attaches `!noundef` / `!range` load metadata from `cast`. | `tm_7_memory_to_scalar_source_align`: `[u8; 16] -> u128` -> `load i128, ptr %_2, align 1, !noundef !4` |
| **3 (`Scalar -> Scalar`)** | `(OperandValue::Immediate(imm), BackendRepr::Scalar(from_scalar))` | `BackendRepr::Scalar(to_scalar)` | `from_scalar.size(cx) == to_scalar.size(cx)` (`:388-393`) | `OperandValue::Immediate(transmute_scalar(bx, imm, from_scalar, to_scalar))` (`from_immediate`, dual `assume_scalar_range`, `bitcast`/`pointercast`/`inttoptr`/`ptrtoint`, `to_immediate_scalar`). | `tm_1` (`u32 -> NonZeroU32`), `tm_2` (`u32 -> f32`), `tm_6` (`*const u32 -> usize`), `tm_9`, `tm_10` |
| **4a / 4b (`SimdVector` & `SimdScalableVector`)** | `(OperandValue::Immediate(imm), SimdVector { element: from_s, .. })` (or `SimdScalableVector`) | `SimdVector { element: to_s, .. }` (matching scalable vs fixed) | `vector_can_bitcast(from_s) && vector_can_bitcast(to_s)` (`:368-376, 395-409`) | `bx.bitcast(imm, bx.cx().immediate_backend_type(cast))` in SSA vector registers (permitted **only** when both lane scalars are `Scalar::Initialized { value: Int(..) \| Float(..), .. }`). | `tm_3_simd_bitcast` (`extern "C"` `I32x4 -> F32x4`): `bitcast <4 x i32> %x to <4 x float>` |
| **5 (`ScalarPair -> ScalarPair`)** | `(OperandValue::Pair(imm_a, imm_b), ScalarPair { a: in_a, b: in_b, b_offset: in_offset })` | `ScalarPair { a: out_a, b: out_b, b_offset: out_offset }` | `in_a.size(cx) == out_a.size(cx) && in_b.size(cx) == out_b.size(cx) && in_offset == out_offset` (`:410-422`) | `OperandValue::Pair(transmute_scalar(bx, imm_a, in_a, out_a), transmute_scalar(bx, imm_b, in_b, out_b))` purely in SSA registers (`0` `alloca`s). | `tm_4_scalarpair_in_regs`: `(u32, u32) -> (f32, NonZeroU32)` -> `bitcast i32 %x.0 to float` + `@llvm.assume` on `%x.1` |
| **6 (`alloca` Spill Fallback)** | Any remaining combination (`Scalar ⇌ ScalarPair`, `Scalar` with `Scalar::Union` size mismatch, `ScalarPair` with size/offset mismatch, pointer-lane `SimdVector`, `SimdVector ⇌ Scalar/ScalarPair`) | Non-ZST SSA `BackendRepr` | `_ =>` (`:423-441`) | `PlaceValue::alloca(bx, max(src.size, dst.size), max(src.align, dst.align))`, `bx.lifetime_start`, `operand.store_with_annotation`, `bx.load_operand(temp.with_type(cast))`, `bx.lifetime_end`. | `tm_5_scalar_to_scalarpair_alloca` (`u64 -> (u32, u32)`) and `tm_8_simd_ptr_to_int_alloca` (`<4 x ptr> -> <4 x i64>`) |

#### 2.3 Three Non-Obvious Corner Cases in the 6-Arm Dispatch

1. **When two equal-sized `BackendRepr::Scalar` types have `from_scalar.size(cx) != to_scalar.size(cx)` (Arm 3 -> Arm 6 fallthrough)**: A `union` containing a 1-byte `u8` field and a 4-byte `[MaybeUninit<u8>; 4]` (or padding) can receive `BackendRepr::Scalar(Scalar::Union { value: Int(I8, false) })` while `operand.layout.size == Size::from_bytes(4)`! Transmuting that 4-byte union to `u32` passes the outer `operand.layout.size == cast.size` check (`4 == 4`), reaches Arm 3 with `from_scalar.size(cx) == 1 != 4 == to_scalar.size(cx)`, fails the Arm 3 guard, and safely falls through to Arm 6 (`alloca [4 x i8]`), avoiding an invalid `i8 -> i32` SSA `bitcast`.
2. **Why pointer-lane SIMD vectors (`<4 x ptr>`) fall through to Arm 6 (`tm_8_simd_ptr_to_int_alloca`)**: LLVM's `bitcast` instruction rejects pointer-to-integer conversions (`bitcast <4 x ptr> %v to <4 x i64>` is ill-typed in LLVM IR; LLVM requires `ptrtoint <4 x ptr> %v to <4 x i64>`, and `f64x4 ⇌ ptrx4` requires two steps). Rather than replicating multi-step vector `ptrtoint`/`inttoptr`/`bitcast` logic, `vector_can_bitcast` (`rvalue.rs:368-376`) restricts Arm 4 to `Scalar::Initialized { value: Int(..) | Float(..), .. }`. On `tm_8_simd_ptr_to_int_alloca`, `rustc` emits:
   ```llvm
   define <4 x i64> @tm_8_simd_ptr_to_int_alloca(<4 x ptr> %v) unnamed_addr #2 {
   start:
     %0 = alloca [32 x i8], align 32
     call void @llvm.lifetime.start.p0(ptr %0)
     store <4 x ptr> %v, ptr %0, align 32
     %_0 = load <4 x i64>, ptr %0, align 32
     call void @llvm.lifetime.end.p0(ptr %0)
     ret <4 x i64> %_0
   }
   ```
   Notice an additional provenance consequence at the LLVM IR level: whereas `transmute::<*const u32, usize>` in Arm 3 emits `ptrtoint ptr %p to i64`, `<4 x *const u32> -> <4 x usize>` in Arm 6 emits a typed memory `store <4 x ptr>` + `load <4 x i64>` through stack `alloca` without an explicit `ptrtoint` instruction before SROA!
3. **Why `in_offset == out_offset` in Arm 5 (`3ef0c22cd` `rvalue.rs:416`) is essential for soundness**: Suppose `src` is a 4-byte `ScalarPair` with `in_a: u8` (`size = 1`, offset `0`), `in_b: u16`-sized scalar at `in_offset = 1` (e.g., inside a `#[repr(packed)]` field or custom alignment wrapper, with 1 trailing padding byte at index `3`), while `dst` is `#[repr(C)] struct PadPair(u8, u16)` with `out_a: u8` (`size = 1`, offset `0`), 1 internal padding byte at index `1`, and `out_b: u16` at `out_offset = 2`. Both types have `size == 4`, `in_a.size == out_a.size == 1`, and `in_b.size == out_b.size == 2`! If Arm 5 checked only component sizes and transmuted `(imm_a, imm_b)` directly in registers, `dst.1` would receive bytes `1..3` (`imm_b`) instead of bytes `2..4` (where byte `3` is `Uninit`!), silently corrupting byte offsets and masking uninitialized-memory UB. At `14210df0e`, `BackendRepr::ScalarPair(a, b)` implicitly derived `b_offset = a.size.align_to(b.align)` so `in_b` could not carry an independent offset; when `BackendRepr::ScalarPair` gained an explicit `b_offset: Size` field in `3ef0c22cd`, both `codegen_transmute_operand` (`rvalue.rs:416`) and MIR `GVN` (`compiler/rustc_mir_transform/src/gvn.rs:747`) had to add `in_offset == out_offset` to preserve soundness (mechanized in `scalarPair_reg_transmute_eq_alloca_spill` and `ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes`).

### 3. `transmute_scalar` and `assume_scalar_range`: Single-Comparison `WrappingRange` `@llvm.assume` Injection

Basis: source (`3ef0c22cd` `rvalue.rs:1082-1194`, `traits/builder.rs:289-317`, `rustc_codegen_llvm/src/builder.rs:667-680`) + execution (`14210df0e` `tm_1`, `tm_4`, `tm_9`, `tm_10`) + retained record (`3ef0c22cd` `tm_1`, `tm_4`) + Lean proof (`assumeIntegerRangeCheck_eq_contains`).

#### 3.1 The 5-Step Execution Pipeline of `transmute_scalar` (`rvalue.rs:1082-1150`)

Whenever Arm 3 (`Scalar -> Scalar`) or Arm 5 (`ScalarPair -> ScalarPair`) invokes `transmute_scalar(bx, imm, from_scalar, to_scalar)`:

1. **Exact `abi::Scalar` equality check (`rvalue.rs:1098-1100`)**: If `from_scalar == to_scalar` (same `Primitive` AND same `valid_range`, e.g., `u32 -> i32` or `&u32 -> NonNull<u32>`), returns `imm` immediately (`0` instructions).
2. **Immediate widening (`bx.from_immediate(imm)`, `rvalue.rs:1103`)**: Converts `i1` (`bool` SSA representation) to `i8` (`zext i1 %imm to i8`) so byte-sized conversions operate on `i8`.
3. **Pre-conversion `assume_scalar_range` on `from_scalar` (`rvalue.rs:1118`)**: Calls `assume_scalar_range(bx, imm, from_scalar, from_backend_ty, Some(&to_scalar))`. If `from_scalar` has a narrower range than `to_scalar` (e.g., `transmute::<NonZeroU32, u32>(nz)`), `rustc` emits `@llvm.assume` on the **input** before widening the type so downstream uses of the resulting `u32` retain the non-zero fact even if `nz` came from an unannotated intra-procedural computation.
4. **Primitive conversion (`rvalue.rs:1120-1137`)**:
   - `(Int | Float, Int | Float)` -> `bx.bitcast(imm, to_backend_ty)` (a no-op in LLVM when `from_backend_ty == to_backend_ty`, such as `i32 -> i32` for `u32 -> NonZeroU32`).
   - `(Pointer, Pointer)` -> `bx.pointercast(imm, to_backend_ty)` (a no-op under LLVM opaque pointers `ptr` in identical address spaces).
   - `(Int, Pointer)` -> `bx.inttoptr(imm, to_backend_ty)`.
   - `(Pointer, Int)` -> `bx.ptrtoint(imm, to_backend_ty)`.
   - `(Float, Pointer)` -> `bx.bitcast(imm, type_isize())` followed by `bx.inttoptr(..., to_backend_ty)`.
   - `(Pointer, Float)` -> `bx.ptrtoint(imm, type_isize())` followed by `bx.bitcast(..., to_backend_ty)`.
5. **Post-conversion `assume_scalar_range` on `to_scalar` (`rvalue.rs:1146`) + `to_immediate_scalar` (`:1148`)**: Calls `assume_scalar_range(bx, imm, to_scalar, to_backend_ty, Some(&from_scalar))`, then truncates `i8` back to `i1` (`trunc nuw i8 %imm to i1`) when `to_scalar` is `bool`.

#### 3.2 Elision Conditions and the Modular Single-`icmp ule` Encoding

`assume_scalar_range` (`rvalue.rs:1156-1194`) suppresses `@llvm.assume` in exactly three cases:
1. `OptLevel::No` (`-C opt-level=0`, `:1163-1165`);
2. `abi::Scalar::Union { .. }` (`:1168`), which applies to `MaybeUninit<NonZeroU32>` (`u32_zero_to_maybe_uninit_nonzero_u32_ok` exits `0` in Miri and emits zero `@llvm.assume` calls in LLVM IR);
3. `valid_range.contains_range(known_range, scalar.size(bx.cx()))` (`:1174-1179`), meaning the target scalar's `WrappingRange` already contains every bit pattern permitted by `known`.

When none of those three guards fires:
- For `Primitive::Pointer(AddressSpace::ZERO)` where `!valid_range.contains(0)` (`rvalue.rs:1187-1191`, e.g., `transmute::<*const u32, NonNull<u32>>(p)` or `transmute::<*const u32, &u32>(p)`), `assume_nonnull` (`traits/builder.rs:309-317`) emits `icmp ne ptr %val, null` + `call void @llvm.assume(i1 ...)`. (Note: non-zero address spaces skip `assume_nonnull`, and `Float` scalars emit no range assume because IEEE-754 floats in Rust currently carry full bit-pattern validity.)
- For `Primitive::Int(..)` (`rvalue.rs:1183-1186`), `assume_integer_range` (`traits/builder.rs:289-304`) emits:
  ```rust
  let shifted = if start == 0 {
      imm
  } else {
      let low = self.const_uint_big(ty, start);
      self.sub(imm, low)
  };
  let width = self.const_uint_big(ty, u128::wrapping_sub(end, start));
  let cmp = self.icmp(IntPredicate::IntULE, shifted, width);
  self.assume(cmp);
  ```

Because modular subtraction by `start` rotates the modular circle $\mathbb{Z} / 2^w \mathbb{Z}$ so that `start` maps to `0` and `end` maps to `(end - start) mod 2^w`, this single `sub + icmp ule` instruction sequence handles **both** contiguous and wrapping `WrappingRange`s without branching:

- **Contiguous niche (`NonZeroU32`, `WrappingRange { start: 1, end: 0xFFFF_FFFF }` mod $2^{32}$)**: `start = 1`, `width = (0xFFFF_FFFF - 1) mod 2^32 = 0xFFFF_FFFE` (`-2` in signed `i32` printing). For `x = 0`, `shifted = (0 - 1) mod 2^32 = 0xFFFF_FFFF > 0xFFFF_FFFE` (`false`); for every `x ∈ [1, 0xFFFF_FFFF]`, `shifted = x - 1 ≤ 0xFFFF_FFFE` (`true`). Observed in `tm_1_scalar_nonzero_assume` on both `14210df0e` and `3ef0c22cd`:
  ```llvm
  define noundef range(i32 1, 0) i32 @tm_1_scalar_nonzero_assume(i32 noundef %x) unnamed_addr #0 {
  start:
    %0 = sub i32 %x, 1
    %1 = icmp ule i32 %0, -2
    call void @llvm.assume(i1 %1)
    ret i32 %x
  }
  ```
- **Wrapping niche (`core::cmp::Ordering`, `#[repr(i8)] { Less = -1, Equal = 0, Greater = 1 }`, `WrappingRange { start: 255, end: 1 }` mod $2^8$)**: Here `end < start` (`1 < 255`), representing `[255, 256) ∪ [0, 1] = {255, 0, 1}`. `low = 255` (`-1` in `i8`), `width = (1 - 255) mod 256 = 2`. Subtracting `-1` adds `1` mod `256`, mapping `{255, 0, 1}` to `{0, 1, 2} ≤ 2` and mapping `[2, 254]` to `[3, 255] > 2`! Observed in `tm_10_wrapping_niche_ordering_assume`:
  ```llvm
  define noundef range(i8 -1, 2) i8 @tm_10_wrapping_niche_ordering_assume(i8 noundef %x) unnamed_addr #0 {
  start:
    %0 = sub i8 %x, -1
    %1 = icmp ule i8 %0, 2
    call void @llvm.assume(i1 %1)
    ret i8 %x
  }
  ```

#### 3.3 Intra-Procedural UB Contamination When a Transmute Result Is Unused (`tm_9`)

A pervasive misconception in MIR verification is that validity constraints on a local only take effect when that local is read, returned (`range(i32 1, 0)` return attribute), or passed to a call (`range(...)` parameter attribute). As `rvalue.rs:1141-1146` explicitly documents, MIR inlining eliminates call boundaries; if a helper function containing `transmute::<u32, NonZeroU32>(x)` is inlined and its return value is unused (`let _ = unsafe { core::mem::transmute::<u32, NonZeroU32>(x) }; x == 0`), `codegen_transmute_operand` **still** emits `@llvm.assume` directly on `%x`:

```llvm
; Pre-pass IR (-C opt-level=1 -Z no-prepopulate-passes):
define noundef zeroext i1 @tm_9_discarded_nonzero_assume_eq_zero(i32 noundef %x) unnamed_addr #0 {
start:
  %0 = sub i32 %x, 1
  %1 = icmp ule i32 %0, -2
  call void @llvm.assume(i1 %1)
  %_0 = icmp eq i32 %x, 0
  ret i1 %_0
}

; Post-optimization IR (-C opt-level=2):
define noundef zeroext i1 @tm_9_discarded_nonzero_assume_eq_zero(i32 noundef %x) unnamed_addr #1 {
start:
  ret i1 false
}
```

At `-C opt-level=2`, LLVM exploits `call void @llvm.assume(i1 %1)` on the discarded transmute to fold `x == 0` unconditionally to `false` (`probe_results_rustc_14210df0e.json`, `tm_9_opt_level_2_ir`). Any sound MIR verification model must therefore enforce target layout validity **eagerly at the `CastKind::Transmute` statement itself**, never lazily on subsequent reads of the destination local.

### 4. Operational Semantics vs. LLVM Codegen Provenance Asymmetry: `CastKind::Transmute` vs. `PointerExposeProvenance`

Basis: source (`3ef0c22cd` `cast.rs:96-106, 192-218, 287-323`, `validity.rs:889-905`, `rustc_middle/src/mir/interpret/allocation.rs:687-726`, `src/tools/miri/src/alloc_addresses/mod.rs:237-388`, `rvalue.rs:1124-1136`) + execution (`14210df0e` Miri, CTFE, and LLVM IR) + retained record (`3ef0c22cd` Miri and LLVM IR) + Lean proofs (`cgTransmuteLLVM_refines_opSem_end_to_end`, `ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast`, `not_opSem_refines_from_cgTransmuteLLVM`).

#### 4.1 Exact Source Mechanism in `rustc_const_eval` and Miri

Consider two functions that convert a raw pointer `p: *const u32` into a `usize` `addr` and reconstruct `q = core::ptr::with_exposed_provenance::<u32>(addr)` before reading `*q`:
- **Program A (`p as usize` / `p.expose_provenance()`)**: Lowers in MIR to `CastKind::PointerExposeProvenance` followed by `CastKind::PointerWithExposedProvenance`.
  1. `InterpCx::pointer_expose_provenance_cast` (`cast.rs:287-305`) extracts `ptr` and calls `M::expose_provenance(self, ptr.provenance)?` (`:298`).
  2. In Miri (`src/tools/miri/src/alloc_addresses/mod.rs:327-358`), `expose_provenance` checks `ecx.is_alloc_live(alloc_id)` and inserts `alloc_id` into `global_state.exposed` (`global_state.exposed.insert(alloc_id)` at `:350`), also exposing the borrow-tracker tag (`ecx.expose_tag(alloc_id, tag)` at `:355`).
  3. `pointer_with_exposed_provenance_cast` (`cast.rs:307-323` -> `alloc_addresses/mod.rs:360-388`) returns `Pointer::new(Some(Provenance::Wildcard), Size::from_bytes(addr))`.
  4. When `*q` is dereferenced, `alloc_id_from_addr` (`alloc_addresses/mod.rs:237-274`) binary-searches `int_to_ptr_map` for `addr`, finds `alloc_id`, checks `global_state.exposed.contains(&alloc_id)` (`:267` -> `true`), and succeeds (`miri_rc = 0`).
- **Program B (`unsafe { core::mem::transmute::<*const u32, usize>(p) }`)**: Lowers in MIR to `CastKind::Transmute` followed by `CastKind::PointerWithExposedProvenance`.
  1. `eval_rvalue_into_place` (`cast.rs:192-218`) calls `self.copy_op_allow_transmute(src, dest)?` (`place.rs:883-943`).
  2. `copy_op_no_validate` copies `(addr, Provenance::Concrete { alloc_id, .. })` into `dest`, then `validate_place` at `usize` invokes `ValidityVisitor::try_visit_primitive` on `ty::Uint(UintTy::Usize)` (`validity.rs:889-905`).
  3. `self.read_scalar(value, ExpectedKind::Int)` calls `Allocation::read_scalar` with `read_provenance = false` (`rustc_middle/src/mir/interpret/allocation.rs:716-725`):
     ```rust
     // compiler/rustc_middle/src/mir/interpret/allocation.rs:716-725
     } else {
         // We are *not* reading a pointer.
         // If we can just ignore provenance or there is none, that's easy.
         if Prov::OFFSET_IS_ADDR || self.provenance.range_empty(range, cx) {
             // We just strip provenance.
             return Ok(Scalar::from_uint(bits, range.size));
         }
         // There is some provenance and we don't have OFFSET_IS_ADDR. This doesn't work.
         return Err(AllocError::ReadPointerAsInt(None));
     }
     ```
     - **In CTFE (`CompileTimeMachine`)**: `CtfeProvenance::OFFSET_IS_ADDR` is `false` because compile-time allocations have no concrete machine addresses! `Allocation::read_scalar` immediately returns `Err(AllocError::ReadPointerAsInt(None))`, which `rustc` reports as `error[E0080]: unable to turn pointer into integer` (`ctfe_ptr_to_usize_transmute`, `rustc_rc = 1`).
     - **In Miri (`MiriMachine`)**: `miri::Provenance::OFFSET_IS_ADDR` is `true`. `Allocation::read_scalar` returns `Ok(Scalar::from_uint(bits, range.size))`—**silently stripping provenance**—and `validity.rs:901` immediately executes `self.ecx.clear_provenance(value)?` on the destination allocation. Crucially, **`M::expose_provenance` is never called**!
  4. When `with_exposed_provenance::<u32>(addr)` creates `Provenance::Wildcard` and `*q` is dereferenced, `alloc_id_from_addr` finds `alloc_id` in `int_to_ptr_map`, checks `global_state.exposed.contains(&alloc_id)` (`:267` -> **`false`**!), returns `None`, and aborts with Undefined Behavior even under `-Zmiri-permissive-provenance`:
     ```text
     error: Undefined Behavior: memory access failed: attempting to access 4 bytes, but got 0x2013c[noalloc] which is a dangling pointer (it has no provenance)
     ```

#### 4.2 Why LLVM Codegen Emits Identical `ptrtoint` IR for Both Casts (One-Way Refinement `OpSem ⊑ LLVM`)

In `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:1124-1127`, `transmute_scalar` lowers `(Pointer(..), Int(..))` via:

```rust
(Pointer(..), Int(..)) => {
    // FIXME: this exposes the provenance, which shouldn't be necessary.
    bx.ptrtoint(imm, to_backend_ty)
}
```

Both `tm_6_ptr_to_usize_ptrtoint` (`CastKind::Transmute`) and `tm_6b_as_cast_ptr_to_usize` (`CastKind::PointerExposeProvenance`) therefore emit byte-for-byte identical LLVM IR:

```llvm
define noundef i64 @tm_6_ptr_to_usize_ptrtoint(ptr noundef %p) unnamed_addr #0 {
start:
  %_0 = ptrtoint ptr %p to i64
  ret i64 %_0
}
```

Because LLVM IR lacks a provenance-stripping `ptrtoint` instruction that extracts address bits without exposing provenance (unless simulated via an unexposed poison/freeze construct that LLVM does not currently provide for pointer addresses), `bx.ptrtoint` conservatively exposes provenance in LLVM's memory model. This is **sound** for compilation because exposing strictly more allocations (`st_op.exposed ⊆ st_llvm.exposed`) refines every defined Rust OpSem behavior (`evalTransmuteOpSem ⊑ evalCgTransmuteLLVM`)—any program that is UB-free in Rust OpSem remains UB-free in LLVM IR. However, **reverse refinement (`LLVM ⊑ OpSem`) is false**: testing or verifying only the lowered LLVM IR (or assuming `transmute::<*const T, usize>` behaves like `p as usize`) accepts programs that exhibit immediate Undefined Behavior under Rust's operational semantics and Miri, and that future LLVM provenance-stripping intrinsics are explicitly permitted to miscompile.

### 5. Byte-Level `AbstractByte` Representation, Padding Reset, Union Data Ranges, and `CastKind::BoxDerefTransmute`

Basis: source (`3ef0c22cd` `place.rs:883-1000`, `validity.rs:472-522, 1126-1250, 1307-1370, 1470-1485`, `cast.rs:206-218`, `rustc_middle/src/mir/interpret/allocation.rs:95-117`) + execution (`14210df0e` 9-case Miri matrix) + retained record (`3ef0c22cd` 5-case Miri matrix) + Lean proofs (`uninit_byte_violates_initBits_dst`, `ce2_padding_byte_transmute_to_u32_ub_vs_maybe_uninit_array_ok`, `boxDerefTransmute_rejects_dangling_ptr_unlike_transmute`).

#### 5.1 `Allocation`'s Three-Plane Byte Representation (`AbstractByte`)

In `compiler/rustc_middle/src/mir/interpret/allocation.rs:95-117`, an interpreter `Allocation` stores three orthogonal planes over byte indices `0 .. size`:
1. `bytes: Box<[u8]>` (raw byte values);
2. `init_mask: InitMask` (1 bit per byte recording initialized vs. `Uninit`);
3. `provenance: ProvenanceMap<Prov>` (sparse map associating pointer fragment offsets with `(Prov, frag_idx)`).

Semantically, each byte of a value or memory allocation inhabits the three-variant `AbstractByte` sum type mechanized in `TransmuteByteModelAndCodegenRefinement.lean`:
- `Uninit` (`init_mask[i] == false`);
- `Init(b: u8)` (`init_mask[i] == true`, no entry in `provenance`);
- `PtrFrag(prov, ofs, b: u8)` (`init_mask[i] == true`, fragment `ofs` of pointer provenance `prov`).

#### 5.2 Two-Pass `copy_op_allow_transmute` and Active Padding Reset (`reset_padding`)

When `CastKind::{Transmute, Subtype, BoxDerefTransmute}` invokes `self.copy_op_allow_transmute(src, dest)` (`place.rs:883-943`):

1. **`src_has_padding` forces memory-to-memory copy (`place.rs:970-997`)**: `copy_op_no_validate` computes `src_has_padding`: `false` for `BackendRepr::Scalar` and wide raw/reference pointers, `left.size + right.size != src.layout.size` for non-pointer `BackendRepr::ScalarPair` (for `#[repr(C)] struct PadPair(u8, u16)`, `1 + 2 = 3 != 4`, so `src_has_padding == true`), and `true` for `SimdVector`, `SimdScalableVector`, and `Memory`.
2. **Pass 1 (`src.layout` validation and reset, `place.rs:928-934`)**: Whenever `src.layout().ty != dest.layout().ty`, Miri runs `self.validate_place(&dest.transmute(src.layout(), self)?, ..., /*reset_provenance_and_padding*/ true)?`.
3. **Pass 2 (`dest.layout` validation and reset, `place.rs:935-939`)**: Miri runs `self.validate_place(&dest, ..., /*reset_provenance_and_padding*/ true)?`.

During each `validate_place` pass with `reset_provenance_and_padding = true`, `ValidityVisitor` accumulates a sorted `RangeSet` `data_bytes` recording the exact sub-ranges visited as non-padding fields. At the end of `validate_place`, `ValidityVisitor::reset_padding` (`validity.rs:1126-1174`) iterates over `0 .. size` and executes `alloc.write_uninit(range)` (`:1168`) on every gap between consecutive `data_bytes` intervals!

This produces three empirically verified consequences across our 9-test Miri matrix (`probe_results_rustc_14210df0e.json`):

1. **Reading struct padding as an integer is immediate UB (`pad_pair_to_u32_uninit_ub`, `miri_rc = 1`)**: Constructing `PadPair(0x11, 0x2233)` leaves byte `1` `Uninit` (`data_bytes = [0..1, 2..4]`). Transmuting to `u32` fails Pass 2 (`Allocation::read_scalar` at `allocation.rs:694-698`) with:
   `Undefined Behavior: constructing invalid value of type u32: encountered uninitialized memory, but expected an integer`.
2. **Typed copies through a padded struct actively destroy prior initialization (`pad_pair_typed_copy_resets_prior_init_padding_ub`, `miri_rc = 1`)**: Even when starting from a 100% initialized `u32` (`0xFF22_3311u32`, where byte `1` is `Init(0xFF)`), transmuting `u32 -> PadPair` executes Pass 2 at `PadPair`, where `reset_padding` calls `alloc.write_uninit(1..2)`, actively wiping byte `1` back to `Uninit`! Transmuting that `PadPair` back to `u32` immediately faults with uninitialized-memory UB (`miri_rc = 1`).
3. **`[MaybeUninit<u8>; N]` preserves `Uninit`, `Init`, and `PtrFrag` provenance, whereas `[u8; N]` strips provenance and rejects `Uninit`**:
   - `MaybeUninit<T>` is a `#[repr(transparent)] union { uninit: (), value: ManuallyDrop<T> }`. Validating `[MaybeUninit<u8>; N]` enters `ValidityVisitor::visit_union` (`validity.rs:1307-1337`), which neither reads scalars nor calls `clear_provenance`, and adds `Self::union_data_range(self.ecx, val.layout)` (`0..N`) to `data_bytes` (`:1331-1334`), preventing `reset_padding` from touching any byte!
   - Consequently:
     - `PadPair(0x11, 0x2233) -> [MaybeUninit<u8>; 4]` succeeds (`pad_pair_to_maybe_uninit_bytes_ok`, `miri_rc = 0`), preserving `[Init(0x11), Uninit, Init(0x33), Init(0x22)]` so bytes `0`, `2`, and `3` can be safely read via `assume_init()` (`0x11`, `0x33`, `0x22`).
     - `*const u32 -> [MaybeUninit<u8>; 8] -> *const u32` succeeds even under `-Zmiri-strict-provenance` (`ptr_transmute_through_maybe_uninit_bytes_strict_ok`, `miri_rc = 0`), preserving all 8 `PtrFrag` bytes intact.
     - By contrast, `[u8; 8]` hits the fast-path integer-array validator (`validity.rs:1470-1484`), which checks `init_mask` and executes `alloc.clear_provenance()` (`:1480`). Thus `*const u32 -> [u8; 8] -> *const u32` strips all provenance without exposing it and faults with `0x2013c[noalloc]` dangling-pointer UB on dereference (`ptr_transmute_through_u8_array_strips_provenance_ub`, `miri_rc = 1` even under `-Zmiri-permissive-provenance`).
     - Likewise, `0u32 -> NonZeroU32` faults with scalar-niche UB (`u32_zero_to_nonzero_u32_ub`, `miri_rc = 1`), whereas `0u32 -> MaybeUninit<NonZeroU32>` hits `visit_union` in Miri and `Scalar::Union` in `assume_scalar_range` (`rvalue.rs:1168`), succeeding with `miri_rc = 0` (`u32_zero_to_maybe_uninit_nonzero_u32_ok`).

#### 5.3 `CastKind::BoxDerefTransmute` Dereferenceability Pre-Validation (`cast.rs:206-214`)

At `3ef0c22cd`, `ElaborateBoxDerefs` lowers `*b` (for `b: Box<T>`) by projecting `b.0: BoxRaw<T>` and casting `(b.0: BoxRaw<T>) as *const T (BoxDerefTransmute)`. Why could `rustc` not use ordinary `CastKind::Transmute` from `BoxRaw<T>` to `*const T`?
- `BoxRaw<T>` is a `#[repr(transparent)]` struct around `NonNull<T>`, whose validity invariant requires only a **non-null** raw pointer (`WrappingRange` `1..=usize::MAX`), **not** a live, aligned, dereferenceable allocation!
- However, in surface Rust, evaluating a place projection `*b` on a dangling or misaligned `Box<T>` (even without reading or writing `*b`, e.g., `let _ = &raw const *b;`) is Undefined Behavior because `Box<T>` carries `dereferenceable` / `noalias` semantics like references.
- `cast.rs:206-214` enforces that exact invariant at the `BoxDerefTransmute` cast:
  ```rust
  if matches!(cast_kind, CastKind::BoxDerefTransmute) {
      // Do the extra UB checking by making the input an actual `Box<T>` pointer
      // and dereferencing it.
      let ptr = self.read_immediate(src)?;
      let pointee_ty = cast_ty.builtin_deref(true).unwrap();
      let box_ty = Ty::new_box(*self.tcx, pointee_ty);
      let ptr = ptr.transmute(self.layout_of(box_ty)?, self)?;
      self.deref_pointer(&ptr)?;
  }
  ```
  On a non-null dangling pointer (`alloc = 99 ∉ liveAllocs`), `CastKind::Transmute` from `BoxRaw<u32>` to `*const u32` succeeds, whereas `CastKind::BoxDerefTransmute` invokes `deref_pointer` as `Box<u32>` and faults with Undefined Behavior (mechanized in `boxDerefTransmute_rejects_dangling_ptr_unlike_transmute`).

### 6. Kernel-Checked Lean 4.34.1 Mechanization: `SafeTransmute` Iff, Forward Refinement, `ScalarPair` Equivalence, and Counterexamples

Basis: derived (mechanized and kernel-verified in `support/TransmuteByteModelAndCodegenRefinement.lean` under `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` via `support/verify_lean.py`; full audit output in `support/lean_verification_result.json`).

#### 6.1 Model Architecture and Constructive Kernel Audit

`support/TransmuteByteModelAndCodegenRefinement.lean` (1,445 lines, 62,076 bytes, core prelude only, `0` `import`s) mechanizes the byte-level operational model and 6-arm codegen lowering with every value declaration marked `noncomputable def` so Lean generates zero `._unsafe_rec` compiler definitions:

- **Byte & State Domain**: `AbstractByte` (`.uninit | .bits (b : UInt8) | .ptrByte (alloc : Nat) (ofs : Nat) (b : UInt8)`), `Outcome α` (`.ok (val : α) | .ub`), `Outcome.Refines src tgt` (`∀ v, src = .ok v → tgt = .ok v`), `ProvState` (`liveAllocs`, `exposedAllocs`), `ProvState.Sub`, `coherentPtrAlloc?`, and little-endian `decodeLE`.
- **Layout & Two-Pass OpSem**: `WrappingRange` (`modulus`, `start`, `end_`) with `WrappingRange.contains` and `assumeIntegerRangeCheck`; `ByteSpec` (`.pad | .maybeUninit | .initBits | .ptrFrag ofs`); `PtrKindSpec` (`.none | .rawPtr | .safeBoxOrRef`); `BackendRepr` (`.zst | .memory | .scalar sz | .simdVector lanes elemSz hasPtrElem | .scalarPair aSz bSz bOffset aRange bRange`); `validateAndReset`; `evalTransmuteOpSem` (equal-size check + two-pass `validateAndReset` at `src` then `dst`, leaving `st.exposedAllocs` unchanged); `evalBoxDerefTransmuteOpSem`; `evalExposeCastOpSem`; `evalWithExposedProv`; and `derefPtrBytes`.
- **6-Arm Codegen Lowering & Stack Buffer Memory**: `CgArmChosen` (`.zstArm | .memoryLoadArm | .scalarTransmuteArm | .simdBitcastArm | .scalarPairRegsArm | .allocaSpillArm`), `selectCgArm`, `llvmExposesPtrToInt` (exposing `coherentPtrAlloc? mid` into `st.exposedAllocs` when lowering `Scalar -> Scalar` or matching `ScalarPair -> ScalarPair` from pointer to integer/float via `ptrtoint`), `evalCgTransmuteLLVM`, `readSlice` / `writeSlice`, `evalScalarPairInRegs` (Arm 5), and `evalScalarPairAllocaSpill` (Arm 6).

`support/verify_lean.py` runs three independent invocations of `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` plus a comment-stripped source token scan (`support/lean_verification_result.json`):
- `all_checks_held`: `true` (`90` theorem constants, `232` definition constants, `0` offending constants);
- `axioms_used_by_any_constant`: `["Quot.sound", "propext"]` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`);
- `unsafe_partial_axiom_opaque_or_unsafe_rec_constants`: `0`;
- `code_token_scan_occurrences`: `0` occurrences each of `sorry`, `admit`, `axiom`, `unsafe`, `partial def`, `Classical.`, `omega`, `bv_decide`, `native_decide`, `import`, and plain `def`;
- `negative_control`: `rejected = true` (`exit_code = 1` on injected false theorem `0 = 1`).

#### 6.2 Theorem-by-Theorem Summary and `rustc` Correspondence

| Lean 4 Theorem (`TransmuteByteModel.*`) | Statement Summary | Axioms Used | `rustc` Primary-Source & Empirical Counterpart |
|---|---|---|---|
| `assumeIntegerRangeCheck_eq_contains` | `∀ r v, r.start < r.modulus → r.end_ < r.modulus → v < r.modulus → assumeIntegerRangeCheck r v = WrappingRange.contains r v` (covers both `start ≤ end_` and wrapping `end_ < start`). | `[propext]` | `BuilderMethods::assume_integer_range` (`traits/builder.rs:289-304`); probes `tm_1`, `tm_4`, `tm_9`, `tm_10`. |
| `safeTransmute_scalar_iff` | For inhabited scalar layouts `mkScalarBitsLayout nSrc rSrc` and `mkScalarBitsLayout nDst rDst`, `SemanticallySafeTransmute` holds **iff** `nSrc = nDst ∧ RangeContainsOpt rSrc rDst nSrc`. | `[propext, Quot.sound]` | `cast.rs:196-204`, `rvalue.rs:354-363, 1174-1179`; Miri `u32_zero_to_nonzero_u32_ub`. |
| `uninit_byte_violates_initBits_dst` | For any `n`, transmuting from a layout with `.pad` at byte `0` into a layout with `.initBits` at byte `0` evaluates to `.ub` for every input `(b0 :: rest)` (because Pass 1 resets `.pad` to `.uninit` and Pass 2 rejects `.uninit`). | `[propext, Quot.sound]` | `ValidityVisitor::reset_padding` (`validity.rs:1126-1174`) + `allocation.rs:694-699`; Miri `pad_pair_typed_copy_resets_prior_init_padding_ub`. |
| `evalTransmuteOpSem_simulates_cgTransmuteLLVM` | Forward simulation: whenever `evalTransmuteOpSem src dst bytes st = .ok (out, st')`, there exists `stLlvm` with `evalCgTransmuteLLVM src dst bytes st = .ok (out, stLlvm)` and `ProvState.Sub st' stLlvm`. | `[propext, Quot.sound]` | `rvalue.rs:379-442, 1124-1136` vs `cast.rs:192-218`. |
| `cgTransmuteLLVM_refines_opSem_end_to_end` | Universal end-to-end forward refinement: `Outcome.Refines (runTransmuteThenExposeDeref evalTransmuteOpSem ...) (runTransmuteThenExposeDeref evalCgTransmuteLLVM ...)` across all `src`, `dst`, heaps, byte vectors, and provenance states. | `[propext, Quot.sound]` | Soundness of `bx.ptrtoint` lowering (`rvalue.rs:1125-1126`) as a one-way refinement of OpSem. |
| `scalarPair_reg_transmute_eq_alloca_spill` | Universal memory equivalence: for all `totalSize`, `aSz`, `bSz`, `bOfs` with `aSz ≤ bOfs` and `bOfs + bSz ≤ totalSize`, `evalScalarPairInRegs ... aBytes bBytes = evalScalarPairAllocaSpill totalSize bOfs aSz bSz bOfs ... aBytes bBytes`. | `[propext]` | Arm 5 vs Arm 6 equivalence under `in_a.size == out_a.size && in_b.size == out_b.size && in_offset == out_offset` (`rvalue.rs:410-441`); probes `tm_4`, `tm_5`. |
| `ce1_transmute_ptr_to_usize_lacks_exposed_provenance_unlike_as_cast` | Constructive triple witness on `alloc = 1` at `0x0002_0100`: (1) `p as usize` (`evalExposeCastOpSem`) + `with_exposed_provenance` + deref = `.ok 0xCAFEBABE`; (2) `transmute` (`evalTransmuteOpSem`) + `with_exposed_provenance` + deref = `.ub`; (3) LLVM `cgTransmute` (`evalCgTransmuteLLVM`) + `with_exposed_provenance` + deref = `.ok 0xCAFEBABE`. | `[propext, Quot.sound]` | Miri `as_cast_exposes_provenance_ok` (`rc = 0`) vs `transmute_ptr_to_usize_strips_without_exposing_ub` (`rc = 1`) vs LLVM `tm_6` (`ptrtoint`). |
| `not_opSem_refines_from_cgTransmuteLLVM` | Refutes reverse refinement: `¬ Outcome.Refines (runTransmuteThenExposeDeref evalCgTransmuteLLVM ...) (runTransmuteThenExposeDeref evalTransmuteOpSem ...)`. | `[propext, Quot.sound]` | Proves LLVM IR execution / equivalence cannot be used to conclude Miri/OpSem validity for pointer-to-int transmutes. |
| `ce2_padding_byte_transmute_to_u32_ub_vs_maybe_uninit_array_ok` | Constructive triple witness on `PadPair`: (1) `PadPair -> u32` = `.ub`; (2) `PadPair -> [MaybeUninit<u8>; 4]` = `.ok` preserving `[.bits 0x11, .uninit, .bits 0x33, .bits 0x22]`; (3) round-tripping all-initialized `0xFF22_3311u32 -> PadPair -> u32` = `.ub`. | `[propext, Quot.sound]` | Miri `pad_pair_to_u32_uninit_ub` (`rc = 1`), `pad_pair_to_maybe_uninit_bytes_ok` (`rc = 0`), and `pad_pair_typed_copy_resets_prior_init_padding_ub` (`rc = 1`). |
| `ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes` | Constructive triple witness for `(aSz=1, bSz=2, totalSize=4)` with `inBOfs=1` vs `outBOfs=2`: (1) `selectCgArm` selects `.allocaSpillArm`; (2) `evalScalarPairAllocaSpill` reads trailing `.uninit` byte and faults `.ub`; (3) unguarded `evalScalarPairInRegs` fabricates `.ok ([0xAA], [0xBB, 0xCC])`. | `[propext]` | Explains why `3ef0c22cd` added `&& in_offset == out_offset` at `rvalue.rs:416` and `gvn.rs:747`. |
| `boxDerefTransmute_rejects_dangling_ptr_unlike_transmute` | On dangling non-null `alloc = 99 ∉ liveAllocs`, `evalTransmuteOpSem boxRaw4Layout rawPtr4Layout` returns `.ok`, whereas `evalBoxDerefTransmuteOpSem` returns `.ub`. | `[propext, Quot.sound]` | `cast.rs:206-214` (`CastKind::BoxDerefTransmute` `deref_pointer` check). |
| `zero_u32_to_nonZeroU32_is_ub` | On `0u32`, both `evalTransmuteOpSem u32Layout nonZeroU32Layout` and `evalCgTransmuteLLVM u32Layout nonZeroU32Layout` return `.ub`. | `[propext, Quot.sound]` | Miri `u32_zero_to_nonzero_u32_ub` (`rc = 1`) and LLVM `@llvm.assume` (`tm_1`, `tm_9`). |

### 7. Implications for Anneal's Trusted MIR Boundary, MIR Pass Admission, and `lean-miri` Correspondence

Basis: source (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `vendor/lean-miri/Miri/Interpreter/{Rvalue,Cast,Place}.lean`) + derived.

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` establishes the exact boundary between Anneal's current trusted kernel (`Trusted.*`) and vendored `lean-miri` (`Miri.*`):

1. **Current fail-closed status in `Trusted.MirAst` and `Trusted.MirSemantics`**:
   - In `trusted/lean/Trusted/MirAst.lean:562-628`, `Rvalue` has constructors `.use`, `.repeat`, `.ref`, `.rawPtr`, `.len`, `.binaryOp`, `.nullaryOp`, `.unaryOp`, `.discriminant`, `.aggregate`, `.shallowInitBox`, `.copyForDeref`, and `.unsupported`—there is **no `Rvalue.cast` constructor**. Any MIR body containing `Rvalue::Cast(CastKind::Transmute | CastKind::Subtype | CastKind::BoxDerefTransmute, ..)` lowers via the JSON deserializer catch-all (`MirAst.lean:627`) to `Rvalue.unsupported`.
   - In `trusted/lean/Trusted/MirSemantics.lean:49-53, 327-335`, evaluating `Rvalue.unsupported` transitions deterministically to `FaultKind.unsupported`, which verification obligations (`verifyMirNoPanicSym` / `wpMirSym`) reject fail-closed.
   - Even if Anneal consumes pre-optimization MIR (`mir_built` / `mir_promoted`), note that `LowerIntrinsics` (`transmute` -> `CastKind::Transmute`), `Subtyper` (`CastKind::Subtype`), and `ElaborateBoxDerefs` (`CastKind::BoxDerefTransmute`) are all `PassPolicy::Required` passes in `rustc`'s runtime MIR lowering pipeline! Consequently, any verified `rustc` backend or correspondence proof operating on runtime MIR (`Runtime(Optimized)` / Miri input MIR) encounters all three `CastKind` variants unavoidably.
2. **Current gap vs. `vendor/lean-miri` in `Trusted.Correspondence`**:
   - Vendored `lean-miri` already mechanizes `CastKind.Transmute | .Subtype | .BoxDerefTransmute` (`vendor/lean-miri/Miri/Interpreter/Cast.lean:143-165, 276-398`), `pointerExposeProvenance` vs `pointerWithExposedProvenance`, and two-pass `copyRuntimePlace` (`vendor/lean-miri/Miri/Interpreter/Place.lean:348-389`).
   - However, Anneal's correspondence adapter (`trusted/correspondence/Trusted/Correspondence.lean:1709-1713, 1824-1825, 1858-1859`) currently stubs both `copyOpAllowTransmute` and `cast` in `refRvalueHooks` as `.unsupported "copyOpAllowTransmute unavailable in Day-1"`.
3. **Four mandatory soundness requirements when extending Anneal to admit transmute-family casts**:
   - **Requirement A (Three-state `AbstractByte`, never pure `UInt8` bitvectors)**: Modeling memory or SSA values as flat initialized bitvectors `List UInt8` would falsely validate `PadPair(u8, u16) -> u32` (`ce2`) and `*const T -> [u8; 8] -> *const T`. Every byte must distinguish `uninit`, pure `bits`, and `ptrByte` fragments.
   - **Requirement B (Active `reset_padding` on typed copies)**: Typed assignment/transmute into a struct with padding must actively overwrite padding offsets with `uninit`, because Miri's `reset_padding` (`validity.rs:1168`) invalidates previously initialized bytes at padding positions (`pad_pair_typed_copy_resets_prior_init_padding_ub`). Only union data ranges (`MaybeUninit<T>`) preserve arbitrary `AbstractByte`s.
   - **Requirement C (Eager cast-site validity obligations, even for dead locals)**: Because `transmute_scalar` emits `call void @llvm.assume(...)` at the `CastKind::Transmute` statement (`tm_9`), Anneal's weakest-precondition evaluator `wpMirSym` must assert `src.size == dst.size`, `dst.is_inhabited`, and `dst` byte/range validity **at the statement itself**—dead-store elimination or unused-local pruning in symbolic execution must never erase a `Transmute` or `BoxDerefTransmute` obligation!
   - **Requirement D (Directional refinement `OpSem ⊑ LLVM` for provenance)**: Any Anneal-to-LLVM backend theorem must formulate compilation correctness as forward refinement (`Outcome.Refines opSem llvmSem`, matching `cgTransmuteLLVM_refines_opSem_end_to_end`), never bidirectional equivalence (`ce1` / `not_opSem_refines_from_cgTransmuteLLVM`).

## Boundaries

1. **`SimdScalableVector` runtime/codegen execution (`not examined` by live execution; `source` only)**: Arm 4b of `codegen_transmute_operand` (`rvalue.rs:403-409`, scalable SVE vectors) was audited in `3ef0c22cd` source (`bx.bitcast` gated by `vector_can_bitcast`) but was not executed because our host target is `x86_64-unknown-linux-gnu` rather than `aarch64` with SVE scalable vector types.
2. **Non-LLVM backends (`Cranelift` and `rustc_codegen_gcc`, `not examined`)**: `codegen_transmute_operand` and `transmute_scalar` live in shared `rustc_codegen_ssa`, so all `BackendRepr` dispatch arms and `BuilderMethods::assume_integer_range` calls apply across SSA backends; however, how `rustc_codegen_cranelift` or `rustc_codegen_gcc` implement `BuilderMethods::assume` (`llvm/builder.rs:667-680` emits `@llvm.assume` specifically in the LLVM backend) was not examined.
3. **Live execution of `CastKind::BoxDerefTransmute` (`known not to apply` on `14210df0e`; `source` + Lean model on `3ef0c22cd`)**: As documented under **Applicability**, the locally executed compiler `14210df0e` (2026-05-31) predates the introduction of `BoxRaw<T>` and `CastKind::BoxDerefTransmute`, and `recorded_observation_rustc_3ef0c22c.json` did not include a separate `Box` deref test case. All `BoxDerefTransmute` claims in this report rest on primary-source inspection of `3ef0c22cd` (`elaborate_box_derefs.rs:60-68`, `cast.rs:206-218`, `rvalue.rs:187, 618-620`, `validate.rs:1425-1445`) and the mechanized Lean theorem `boxDerefTransmute_rejects_dangling_ptr_unlike_transmute`.
4. **Future LLVM provenance-stripping `ptrtoint` intrinsics (`unknown` upstream timeline)**: `rvalue.rs:1125` and `:1133` carry `// FIXME: this exposes the provenance, which shouldn't be necessary`. Whether and when LLVM introduces a non-exposing pointer-address extraction instruction is an open upstream LLVM design question; Rust OpSem/Miri already enforces the stricter non-exposing semantics today.
5. **Attractive stronger conclusions that are `known not to apply` (refuted by evidence)**:
   - *False claim*: "Because `transmute::<*const T, usize>(p)` and `p as usize` emit identical `ptrtoint` LLVM IR, they are semantically equivalent in Rust." **Refuted** by Miri execution (`transmute_ptr_to_usize_strips_without_exposing_ub` `rc = 1` vs `as_cast_exposes_provenance_ok` `rc = 0`), CTFE execution (`E0080`), and `not_opSem_refines_from_cgTransmuteLLVM`.
   - *False claim*: "If a `transmute::<u32, NonZeroU32>(x)` result is immediately dropped (`let _ = ...`) without being read or returned, `x == 0` remains possible in LLVM IR." **Refuted** by `tm_9_discarded_nonzero_assume_eq_zero`, where `-C opt-level=2` folds `x == 0` to `ret i1 false` via intra-procedural `@llvm.assume`.
   - *False claim*: "Initializing all bytes of an allocation before transmuting through a struct with padding preserves those initialized bytes." **Refuted** by `pad_pair_typed_copy_resets_prior_init_padding_ub` (`0xFF22_3311u32 -> PadPair -> u32` faults UB in Miri because `reset_padding` overwrites byte `1` with `Uninit`) and `ce2`.
   - *False claim*: "Any two `ScalarPair` layouts with matching component sizes (`in_a.size == out_a.size && in_b.size == out_b.size`) can be transmuted componentwise in SSA registers." **Refuted** when `in_offset != out_offset` (`ce3_scalarpair_mismatched_b_offset_register_transmute_corrupts_bytes`; guarded at `3ef0c22cd` `rvalue.rs:416`).
   - *False claim*: "Every `#[repr(simd)]` transmute between equal-sized vector types compiles to an SSA `bitcast`." **Refuted** for pointer-lane SIMD (`tm_8_simd_ptr_to_int_alloca`: `<4 x ptr> -> <4 x i64>` fails `vector_can_bitcast` and spills to `alloca [32 x i8]`) and under the `"Rust"` calling convention where indirect `sret` routing invokes `codegen_transmute` instead of `codegen_transmute_operand`.
6. **Anneal `Rvalue::Cast` support (`unsupported` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)**: Anneal's trusted MIR AST and operational semantics explicitly map all `Rvalue::Cast` forms to `Rvalue.unsupported` / `FaultKind.unsupported`.

## Evidence

### Primary Git Source Inventory

All primary source citations were inspected directly at the exact 40-hex commit hashes below:

| Repository & 40-Hex Commit | File Path | Lines / Symbols | Evidence Role |
|---|---|---|---|
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_middle/src/mir/syntax.rs` | `:1492-1541` (`enum CastKind`, `Transmute`, `BoxDerefTransmute`, `Subtype`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/lower_intrinsics.rs` | `:289-313` (`LowerIntrinsics`: `sym::transmute \| sym::transmute_unchecked`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/add_subtyping_projections.rs` | `:21-72` (`Subtyper` emitting `CastKind::Subtype`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs` | `:51-68` (`ElaborateBoxDerefs` emitting `CastKind::BoxDerefTransmute` on `BoxRaw<T>`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/validate.rs` | `:1404-1453` (MIR validator rules for `Transmute`, `BoxDerefTransmute`, `Subtype`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/gvn.rs` | `:733-760` (`GVN` `ScalarPair` transmute constant folding with `in_offset == out_offset` at `:747`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_borrowck/src/type_check/mod.rs` | `:1603-1604` (`bug!("CastKind::Subtype shouldn't exist in borrowck")`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_ssa/src/mir/statement.rs` | `:20-68` (`LocalRef::Place` -> `codegen_rvalue` vs `LocalRef::PendingOperand` -> `codegen_rvalue_operand`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | `:186-193, 295-298, 306-443, 618-620, 1082-1194` (`codegen_transmute`, `codegen_transmute_operand`, `vector_can_bitcast`, `transmute_scalar`, `assume_scalar_range`) | `source` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | `:248-340` (`BackendRepr::ScalarPair(in_a, in_b)` prior to explicit `b_offset`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_ssa/src/traits/builder.rs` | `:289-317` (`assume_integer_range` single-`icmp ule` encoding, `assume_nonnull`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_codegen_llvm/src/builder.rs` | `:667-680` (`Builder::assume` lowering to `@llvm.assume`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_const_eval/src/interpret/cast.rs` | `:96-106, 192-218, 287-323` (`PointerExposeProvenance`, `PointerWithExposedProvenance`, `Transmute \| Subtype \| BoxDerefTransmute`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_const_eval/src/interpret/place.rs` | `:883-1000` (`copy_op_allow_transmute`, two-pass `validate_place`, `src_has_padding`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_const_eval/src/interpret/validity.rs` | `:889-905, 1126-1250, 1307-1337, 1470-1485` (`try_visit_primitive` `clear_provenance`, `reset_padding` `write_uninit`, `visit_union` `union_data_range`, `[u8; N]` `clear_provenance`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_middle/src/mir/interpret/allocation.rs` | `:95-117, 687-726` (`Allocation` planes, `read_scalar` `Prov::OFFSET_IS_ADDR` vs `ReadPointerAsInt`) | `source` |
| `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `src/tools/miri/src/alloc_addresses/mod.rs` | `:237-274, 327-388` (`alloc_id_from_addr` `exposed.contains`, `expose_provenance`, `ptr_from_addr_cast` `Provenance::Wildcard`) | `source` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` & `MirSemantics.lean` | `MirAst.lean:562-628` (`Rvalue.unsupported`), `MirSemantics.lean:49-53, 327-335` (`FaultKind.unsupported`) | `source` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/correspondence/Trusted/Correspondence.lean` & `vendor/lean-miri/Miri/Interpreter/{Cast,Place}.lean` | `Correspondence.lean:1709-1713, 1824-1825, 1858-1859`; `Cast.lean:143-165, 276-398`; `Place.lean:348-389` | `source` |

### Empirical Execution Summary (`22/22` Live Checks on `14210df0e` + Retained `3ef0c22cd` Record)

Acquired on `2026-11-22` (`support/probe_results_rustc_14210df0e.json`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6, Miri `14210df0e`, `x86_64-unknown-linux-gnu`; self-contained offline `#![no_std]` Miri sysroot compiled directly from toolchain `rust-src` inside `support/probe_transmute_backend_repr_and_provenance.py`) and cross-verified against the retained record on `3ef0c22cd` (`support/recorded_observation_rustc_3ef0c22c.json`, `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5):

| Check ID in `probe_results_rustc_14210df0e.json` | Subject / Mode | Observed Outcome | Retained `3ef0c22cd` Match |
|---|---|---|---|
| `miri_as_cast_exposes_provenance_ok` | Miri `-Zmiri-permissive-provenance` | `miri_rc = 0` (`p as usize` exposes provenance; `*with_exposed_provenance(addr) == 42`) | Yes (`miri_rc = 0`) |
| `miri_transmute_ptr_to_usize_strips_without_exposing_ub` | Miri `-Zmiri-permissive-provenance` | `miri_rc = 1` (`0x2013c[noalloc] which is a dangling pointer (it has no provenance)`) | Yes (`miri_rc = 1`, `0x212d4[noalloc]`) |
| `miri_ptr_transmute_through_maybe_uninit_bytes_strict_ok` | Miri `-Zmiri-strict-provenance` | `miri_rc = 0` (`*const u32 -> [MaybeUninit<u8>; 8] -> *const u32` preserves provenance) | Tested on `14210df0e` |
| `miri_ptr_transmute_through_u8_array_strips_provenance_ub` | Miri `-Zmiri-permissive-provenance` | `miri_rc = 1` (`*const u32 -> [u8; 8] -> *const u32` clears provenance at `validity.rs:1480`) | Tested on `14210df0e` |
| `miri_pad_pair_to_u32_uninit_ub` | Miri default | `miri_rc = 1` (`PadPair(0x11, 0x2233) -> u32` faults on uninitialized padding byte `1`) | Yes (`miri_rc = 1`) |
| `miri_pad_pair_to_maybe_uninit_bytes_ok` | Miri default | `miri_rc = 0` (`PadPair -> [MaybeUninit<u8>; 4]` preserves bytes `0, 2, 3`) | Yes (`miri_rc = 0`) |
| `miri_pad_pair_typed_copy_resets_prior_init_padding_ub` | Miri default | `miri_rc = 1` (`0xFF22_3311u32 -> PadPair -> u32` wipes byte `1` in `reset_padding`) | Tested on `14210df0e` |
| `miri_u32_zero_to_nonzero_u32_ub` | Miri default | `miri_rc = 1` (`encountered 0, but expected something greater or equal to 1`) | Yes (`miri_rc = 1`) |
| `miri_u32_zero_to_maybe_uninit_nonzero_u32_ok` | Miri default | `miri_rc = 0` (`0u32 -> MaybeUninit<NonZeroU32>` valid via `visit_union`) | Tested on `14210df0e` |
| `ctfe_rejects_ptr_to_usize_transmute` | `rustc` CTFE (`const`) | `rustc_rc = 1` (`error[E0080]: unable to turn pointer into integer`) | Tested on `14210df0e` |
| `tm_1_injects_llvm_assume_without_alloca` | Pre-pass LLVM IR | Arm 3 (`u32 -> NonZeroU32`): `sub i32 %x, 1; icmp ule i32 %0, -2; call void @llvm.assume(i1 %1)`, `alloca = false` | Yes (identical IR body) |
| `tm_2_emits_scalar_bitcast` | Pre-pass LLVM IR | Arm 3 (`u32 -> f32`): `bitcast i32 %x to float`, `alloca = false`, `assume = false` | Yes (identical IR body) |
| `tm_3_emits_simd_vector_bitcast` | Pre-pass LLVM IR (`extern "C"`) | Arm 4a (`I32x4 -> F32x4`): `bitcast <4 x i32> %x to <4 x float>`, `alloca = false` | Yes (identical IR body) |
| `tm_4_transmutes_scalarpair_in_registers_with_assume` | Pre-pass LLVM IR | Arm 5 (`(u32, u32) -> (f32, NonZeroU32)`): `bitcast` + `@llvm.assume` in regs, `alloca = false` | Yes (identical IR body) |
| `tm_5_falls_back_to_alloca_and_lifetime_start` | Pre-pass LLVM IR | Arm 6 (`u64 -> (u32, u32)`): `alloca [8 x i8], align 8` + `@llvm.lifetime.start.p0` + `store` + 2 `load`s + `@llvm.lifetime.end.p0` | Yes (identical IR body) |
| `tm_6_lowers_ptr_to_usize_via_ptrtoint` | Pre-pass LLVM IR | Arm 3 (`*const u32 -> usize`): `ptrtoint ptr %p to i64` (identical to `tm_6b_as_cast_ptr_to_usize`) | Yes (identical IR body) |
| `tm_7_memory_to_scalar_uses_source_align_1` | Pre-pass LLVM IR | Arm 2 (`[u8; 16] -> u128`): `load i128, ptr %_2, align 1, !noundef !4` | Tested on `14210df0e` |
| `tm_8_pointer_simd_uses_alloca_not_bitcast` | Pre-pass LLVM IR (`extern "C"`, AVX) | Arm 6 (`PtrX4 -> UsizeX4`): `alloca [32 x i8], align 32` + `store <4 x ptr>` + `load <4 x i64>`, `bitcast = false` | Tested on `14210df0e` |
| `tm_9_discarded_transmute_injects_assume_and_folds_eq_zero_to_false` | Pre-pass IR & `-C opt-level=2` IR | Discarded `transmute::<u32, NonZeroU32>(x)` emits `@llvm.assume` and folds `x == 0` to `ret i1 false` at `-O2` | Tested on `14210df0e` |
| `tm_10_wrapping_niche_ordering_emits_single_icmp_ule_assume` | Pre-pass LLVM IR | Arm 3 (`i8 -> cmp::Ordering`): `sub i8 %x, -1; icmp ule i8 %0, 2; call void @llvm.assume(i1 %1)` | Tested on `14210df0e` |
| `mir_lower_intrinsics_emits_castkind_transmute` | `-Z dump-mir=all` | `LowerIntrinsics.after.mir` emits `_0 = move _2 as std::num::NonZero<u32> (Transmute);` | Tested on `14210df0e` |
| `mir_subtyper_emits_castkind_subtype` | `-Z dump-mir=all` | `Subtyper.after.mir` emits `_0 = move _2 as fn(&u8) -> &u8 (Subtype);` | Tested on `14210df0e` |

### Preserved Package Support Artifacts

- `support/probe_transmute_backend_repr_and_provenance.py` — standalone, deterministic Python 3 harness compiling a minimal `#![no_std]` Miri sysroot from toolchain `rust-src` and executing all 22 Miri, CTFE, pre-pass/post-opt LLVM IR, and MIR-dump checks with path scrubbing.
- `support/probe_results_rustc_14210df0e.json` — recorded output of `probe_transmute_backend_repr_and_provenance.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`held_count = 22`, `failed_count = 0`).
- `support/recorded_observation_rustc_3ef0c22c.json` — retained Miri + LLVM 23.1.5 observation record from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`.
- `support/TransmuteByteModelAndCodegenRefinement.lean` — 1,445-line self-contained Lean `v4.34.1` mechanization (core prelude only, `0` `sorry`, `0` `Classical.choice`, `0` `omega`/`bv_decide`/`native_decide`, `0` `._unsafe_rec`).
- `support/verify_lean.py` — automated 3-run Lean kernel and `Lean.Environment` axiom auditor + false-theorem negative control + comment-stripped token scanner.
- `support/lean_verification_result.json` — recorded output of `verify_lean.py` on `Lean v4.34.1` (`all_checks_held = true`).

## Revalidation

To check whether the findings in this report continue to hold on a newer `rustc` nightly, Miri build, Anneal commit, or Lean 4 toolchain, run the three narrow checks below from the package directory (`reports/rustc-transmute-backend-repr-provenance-padding-and-llvm-assume/`):

1. **Rerun the 22-check empirical `rustc` + Miri probe (~15–25 seconds on any nightly toolchain with `rustc-src` and `miri` components installed)**:
   ```bash
   python3 support/probe_transmute_backend_repr_and_provenance.py \
     --rustc /path/to/toolchain/bin/rustc \
     --miri /path/to/toolchain/bin/miri \
     --out /tmp/revalidated_probe_results.json
   ```
   Exit code `0` confirms all 9 Miri provenance/padding/niche cases, the CTFE `E0080` pointer-to-integer rejection, all 6 `codegen_transmute_operand` `BackendRepr` arms (including `@llvm.assume` wrapping/contiguous ranges, source-alignment `Memory` load, pointer-SIMD `alloca` fallback, and `-C opt-level=2` discarded-transmute folding), and the `LowerIntrinsics`/`Subtyper` MIR dumps.

2. **Rerun the 3-step Lean 4 kernel, `Lean.Environment` axiom, and negative-control audit (~5–10 seconds)**:
   ```bash
   python3 support/verify_lean.py \
     --lean /path/to/lean4/bin/lean \
     --sysroot /path/to/lean4 \
     --out /tmp/revalidated_lean_audit.json
   ```
   Exit code `0` confirms `all_checks_held: true`, `axioms_used_by_any_constant` subset of `["Quot.sound", "propext"]` (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`), `0` `unsafe`/`partial`/`opaque`/`._unsafe_rec` constants, and rejection of the negative-control false theorem.

3. **Targeted upstream `git diff` on the five behavioral decision points in `rust-lang/rust` and `joshlf/anneal`**:
   - In `rust-lang/rust`, diff from `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` on:
     1. `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` (`codegen_transmute`, `codegen_transmute_operand`, `transmute_scalar`, `assume_scalar_range` — watch especially for any replacement of `bx.ptrtoint` at `:1124-1136` or changes to the `ScalarPair` `b_offset` guard at `:410-422`);
     2. `compiler/rustc_codegen_ssa/src/traits/builder.rs` (`assume_integer_range`, `assume_nonnull` — watch for migration to LLVM `@llvm.assume` operand bundles);
     3. `compiler/rustc_const_eval/src/interpret/{cast.rs,place.rs,validity.rs}` and `compiler/rustc_middle/src/mir/interpret/allocation.rs` (`CastKind::{Transmute, BoxDerefTransmute, Subtype}`, `copy_op_allow_transmute`, `reset_padding`, `visit_union`);
     4. `src/tools/miri/src/alloc_addresses/mod.rs` (`expose_provenance`, `alloc_id_from_addr`).
   - In `joshlf/anneal`, diff from `c131b320eeeb26ef692e5afd5ec8db49ee518613` on `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `trusted/correspondence/Trusted/Correspondence.lean` to check whether `Rvalue::Cast` has been promoted out of `Rvalue.unsupported`.
