# Anneal Profile v2 Wave 3 & Wave 4 Minimal-TCB Lean Semantics Specification

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

This report records the pre-implementation architectural specification for extending Anneal's `Trusted.MirSemantics` and `anneal-rustc-capture` across **Wave 3** (byte-level initialization, `#[repr(C)] union`, `MaybeUninit<T>`, `ManuallyDrop<T>`, eager two-pass `CastKind::{Transmute, Subtype, BoxDerefTransmute}`, unsized slice layouts `[T]`, and core pointer byte intrinsics) and **Wave 4** (strict `Type 0` open generics `<T: ?Sized>`, coherence-keyed `TraitContract`s, associated-type projections, and polar CTFE admission for `Body::required_consts` post-monomorphization errors).

Key architectural results (`source` + `derived` + `[kernel-checked proof] [toy model]`):

1. **Coverage leap (`source` inspection of `google/zerocopy` `src/`):** Waves 1–2 cover `388 / 546` (`71.1%`) callable `unsafe` blocks under concrete monomorphization; Wave 3 raises concrete coverage to `416 / 546` (`76.2%`) callable `unsafe` blocks and `57 / 63` (`90.5%`) `#[kani::proof]` harnesses; Wave 4 raises universal (`∀ T`) library verification from `16 / 546` (`2.9%`) monomorphic blocks to **`462 / 546` (`84.6%`)** directly (`488–503 / 546`, `89.4%–92.1%`, with macro-rule templates) and **`62 / 63` (`98.4%`)** Kani proof contracts.
2. **Unified `AllocByte` + `Option PtrFrag` vs. Split `InitMask`:** Keeping unified `List AllocByte` in Ring-1 `Trusted.MirModel` (`~35` LOC delta) and proving a quotient Galois insertion (`projectToMiri` / `liftFromMiri`) in Ring-2 `Trusted.Correspondence` avoids importing `vendor/lean-miri`'s `1,734`-LOC `InitMask.lean` and `507`-LOC `ProvenanceMap.lean` (`2,241` LOC + `Array.qsort` outside `foundation-lock.json`) into Ring 1.
3. **Eager Two-Pass Transmute & Padding Reset:** `CastKind::{Transmute, Subtype, BoxDerefTransmute}` validates `src.isSized && dst.isSized && src.size == dst.size` (`FaultKind.undefined` on mismatch), validates `src` while resetting padding to `.uninit` and stripping scalar provenance, and validates `dst` eagerly at the cast statement (matching LLVM `@llvm.assume` emission).
4. **Universe-Monomorphic (`Type 0`) Open Generics & Polar PME Admission:** Open generics use first-order de Bruijn indices (`TyParamId`, `ConstParamId`) over `TypeLayoutSpec : Type 0` (`ci.levelParams.isEmpty == true`), coherence-keyed trait registries `(ClosedMirTy, TraitDefId, List ClosedMirTy)`, and three-outcome `ConstMirMachine` (`.compiled | .rejectedE0080 | .unsupportedConstOp`) preventing Quadrant-4 implication vacuity.
5. **Minimal-TCB Budget:** Estimated incremental Ring-1 TCB is `+4,000–5,900` LOC (`+1,500–2,200` Rust capture + `+2,500–3,700` `Trusted.*` Lean) over the measured `6,096`-LOC `Trusted.*` Lean and `8,390`-LOC `rustc-capture` baselines at `google/zerocopy@d3362d9a657e`.

Full specification details are preserved in [support/profile_v2_wave34_semantics_spec.md](support/profile_v2_wave34_semantics_spec.md).

## Applicability

These architectural design findings apply to:
- **`google/zerocopy` (`d3362d9a657e`):** Specifically `anneal/trusted/rustc-capture/src/`, `anneal/trusted/lean/Trusted/`, `anneal/trusted/correspondence/Trusted/`, `anneal/trusted/audit/TrustedBoundary.lean`, `anneal/theory/`, and `zerocopy/src/` (`546` callable `unsafe` blocks and `63` `#[kani::proof]` harnesses).
- **Pinned Toolchains:** `anneal-rustc-capture` on `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `vendor/lean-miri` aligned to `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`, and Lean `v4.34.1` / `v4.35.0` (`module` + `prelude` mode with `foundation-lock.json` restricting Ring 1 to `51` `Init.*` modules).
- **Relationship among subjects:** `google/zerocopy`'s Ring-1 `Trusted.*` Lean AST/semantics and Rust capture frontend are designed to match `vendor/lean-miri`'s operational memory/cast semantics via Ring-2 `Trusted.Correspondence`, while `google/zerocopy/src/` serves as the first-customer target corpus.

Four open human policy decisions (`D1`–`D4` in the companion spec) govern exact interface locks (`Option PtrFrag` in Wave 3 vs. Wave 5; strict `IntoBytes` union policy over operational `union_data_range`; pre-monomorphization open `Body` capture; mandatory `MonoInhabitedSafe` non-vacuity witness).

## Findings

### Four-Ring Trust Architecture & Live Baseline LOC

Basis: `source` inspection of `google/zerocopy@d3362d9a657e` (`[real measurement]`) + `derived` incremental budget (`[engineering estimate]`).

- **Ring 0 (`trusted/audit/`, `~5.4K` LOC):** Enforces `foundation-lock.json` (`prelude` + `51` `Init.*` modules), `ci.levelParams.isEmpty == true` (`TrustedBoundary.lean:2838, 2857`), `0` custom axioms (`⊆ {propext, Classical.choice, Quot.sound}`), and Pass-2 `verifyRefEvaluatorIndependence` (`M_anneal` imports nothing from `M_ref`, and `M_ref` imports no step rules from `Trusted.MirSemantics.*`).
- **Ring 1 Baseline (`[real measurement]` at `d3362d9a657e`):**
  - `anneal/trusted/rustc-capture/src/*.rs`: `8,390` LOC (`extract.rs` `1,316`, `identity.rs` `2,397`, `ir.rs` `1,730`, `capture.rs` `1,412`, `lean.rs` `801`, `main.rs` `369`, `publication.rs` `188`, `driver.rs` `177`).
  - `anneal/trusted/lean/Trusted/**/*.lean`: `6,096` LOC (`MirModel.lean` `262`, `MirAst/*` `1,175`, `MirSemantics/*` `4,659` including `782` LOC in `CanaryFixtures.lean`).
- **Ring 2 Baseline (`[real measurement]` at `d3362d9a657e`, `0` Ring-1 TCB):**
  - `anneal/trusted/correspondence/Trusted/**/*.lean`: `4,264` LOC (`Correspondence.lean` `692`, `Config.lean` `1,309`, `State.lean` `1,272`, `Codec.lean` `419`, `Eval.lean` `220`, `Simulation.lean` `191`, `CanaryFixtures.lean` `161`).
- **Projected Incremental Deltas (`[engineering estimate]`):**
  - **W3:** `+650–950` Rust capture, `+1,100–1,600` Ring-1 Lean (`MirModel`, `MirAst`, `MirSemantics/{Bytes,Layout,Transmute,Intrinsics}`), `+600–900` Ring-2 `Correspondence`.
  - **W4:** `+850–1,250` Rust capture, `+1,400–2,100` Ring-1 Lean (`MirAst/{Types,Generic,Body}`, `MirSemantics/{TypeSpec,Contract,ConstPme}`), `+550–800` Ring-2 `GenericErasure`.
  - **Ring 3 (`theory/Anneal/{DstLayoutAlgebra,ZerocopyTraits}.lean`, `0` TCB):** `+1,800–2,600` LOC.

### Wave 3 Byte, Union, Provenance, and Two-Pass Transmute Semantics

Basis: `source` (`vendor/lean-miri` `InitMask.lean`, `ProvenanceMap.lean`, `ValidityVisitor.lean`, `Cast.lean`, `Place.lean`) + `derived` design + `[kernel-checked proof] [toy model]` (`Wave34Semantics.lean` Theorems `W3-1`–`W3-8`).

1. **`AllocByte` & `PtrFrag` Representation:**
   - `PtrFrag` records `{ allocId : AllocId, borrowTag : Nat, ptrAddrBits : BitVec 64, byteIdx : UInt8 }`; `AllocByte` is `.uninit | .init (byte : UInt8) (prov : Option PtrFrag := none)`.
   - `projectToMiri` maps `.uninit` to `(0, false, none)` and `.init b p` to `(b, true, p)`; `liftFromMiri` maps indices with `initMask.get i = false` to `.uninit` (erasing dead `rawBytes`) and initialized indices to `.init bytes[i] (provenance.getFrag i)`.
   - Companion toy theorems `W3-1` (`lift_project_id`) and `W3-2` (`liftFromSplit_quotient_uninit`) confirm the quotient Galois insertion.
2. **Pointer-Fragment Reassembly Asymmetry:**
   - Copying through typed scalars (`u8`, `u32`, `usize`, `BackendRepr::Scalar(Scalar::Initialized ...)`) executes `readScalar(..., readProvenance := false)`, stripping provenance (`prov := none`).
   - Copying through `MaybeUninit<u8>` (`Scalar::Union`), `#[repr(C)] union`, or `ptr::copy_nonoverlapping` uses `copyRepeatedly`, preserving `.uninit` and `PtrFrag`.
   - `reassemblePtrVal` restores full `PtrVal` provenance iff all `8` bytes `b₀..b₇` are `.init`, carry `some ⟨aid, tag, snapBits, k⟩` with identical `(aid, tag, snapBits)` and matching `addr.toBitVec == snapBits`; chimeric splices or byte-mutated fragments downgrade to `allocId := none` (`ProvenanceMap.inspectFragments` lines `328–358`; toy theorem `W3-6`).
3. **`ByteRole` Layout Lowering & Unions:**
   - `ByteRole` has four variants: `.padding`, `.unionData`, `.scalarByte (grpId byteIdx width : Nat) (v : ScalarValidity)`, and `.ptrByte (grpId byteIdx : Nat) (nonNull : Bool)`.
   - `ManuallyDrop<T>` preserves layout identically while turning `TerminatorKind::Drop` into a no-op (`StorageDead` still deallocates).
   - `MaybeUninit<T>` sets `inhabited := true` unconditionally (even for `Infallible`, though `assume_init` faults `.undefined` on `!dst.inhabited`, `W3-7`), sets `largest_niche = none`, and sets all `T.size` roles to `.unionData`.
   - `#[repr(C)] union` sets `inhabited := true` unconditionally; `joinUnionRoles` assigns `.unionData` where at least one field has a non-`.padding` role and `.padding` only where every field has `.padding` or is out of range (`ValidityVisitor.unionRanges:245-295`). Writing a smaller field `u.a` leaves `[size(a)..size(U))` unchanged (`.uninit` if previously uninitialized), so reading larger `u.b` faults `.undefined` (`W3-8`).
4. **Eager Two-Pass `CastKind::{Transmute, Subtype, BoxDerefTransmute}`:**
   - Gate: `!srcTy.isSized || !dstTy.isSized || srcTy.size != dstTy.size` $\mapsto$ `.fault .undefined` (matching `Cast.lean:388`).
   - Pass 1 (`validateAtLayout srcLayout rawBytes`): checks `srcLayout.inhabited`, resets `.padding` to `.uninit` unconditionally (even on pre-zeroed memory), preserves `.unionData`, validates `.scalarByte` bit ranges while stripping provenance, and validates `.ptrByte` (`nonNull`, reference alignment, pointee inhabitedness).
   - Pass 2 (`validateAtLayout dstLayout afterSrc`): executes eagerly at the `Rvalue::Cast` step to match `@llvm.assume` emission (`CastKind::Transmute(2u8 : u8 -> bool)` in a discarded `let _ = ...` is immediate UB; `PadPair(u8, u16) -> u32` faults because Pass 1 reset padding byte `1` to `.uninit`, `W3-4`, whereas `PadPair -> [MaybeUninit<u8>; 4]` succeeds, `W3-5`).
5. **Fat Slices & Pointer Intrinsics:** `PtrMeta := .thin | .sliceLen (elems : UInt64)` enforces `elems * elemSize <= isize::MAX`; `core::ptr::{read, write, read_unaligned, write_unaligned, copy_nonoverlapping, write_bytes}` check alignment even at `count == 0` for `copy_nonoverlapping` and preserve `.uninit`/`PtrFrag` on untyped copies.

### Wave 4 Open Generics, `TraitContract`, Coherence, and Polar PME

Basis: `source` (`TrustedBoundary.lean`, `zerocopy/src/`) + `derived` + `[kernel-checked proof] [toy model]` (`Wave34Semantics.lean` Theorems `W4-0`–`W4-7`).

1. **First-Order `Type 0` Representation:** `MirTy` adds `.param (id : TyParamId)`, `.slice`, `.array (elem) (len : ConstExpr)`, `.adtSliceDst`, and `.assocProj (selfTy) (traitId) (assocIdx)`. `Body` adds `typeParamCount`, `constParamCount`, `whereClauses`, and `requiredConsts`. `TypeLayoutSpec : Type 0` stores `{ isSized, alignLog2, sizeForMeta : PtrMeta → Option Nat, inhabited, freezeProfile : PtrMeta → FreezeProfile, rolesForMeta : PtrMeta → Option (List ByteRole) }`, paired with `FullValid := LangValid ∧ LibValid`.
2. **`Immutable` vs. `Freeze` Separation (`W4-7`):** `FreezeProfile` separates `hasUnsafeCellAt : Nat → Bool` (Tree Borrows `readonly` suppression) from `zcImmutable : Bool` (`zerocopy::Immutable`), admitting `zerocopy::ReadOnly<UnsafeCell<U>>` (`hasUnsafeCellAt = true`, `zcImmutable = true`).
3. **Coherence-Keyed Trait Registry:** Implementations in `Program.traitRegistry` are keyed by `(ClosedMirTy, TraitDefId, List ClosedMirTy)` with pairwise-distinct keys (`TraitRegistryWf`) and `ProductiveUnsafeImpl` witnesses, eliminating dictionary spoofing (where two call sites pass inconsistent `LAYOUT` or `MaybeUninit` types for the same Rust type).
4. **Polar CTFE Admission (`ConstMirMachine`):** `zerocopy` uses `static_assert!` / `const_assert!` across `23` `unsafe` blocks (`17` generic functions) stored in `Body::required_consts`. Placing unpolarized `evalConst == .succeeded` in negative precondition polarity creates Quadrant-4 vacuity (`unsupportedConstOp → RuntimeWellFormed`). `SafePolarMirSem` uses three outcomes (`.compiled | .rejectedE0080 | .unsupportedConstOp`), 4-place `substTySizes` (`locals`, `Cast`, `SizeOf`/`AlignOf`, transitive `const fn` helpers), mandatory positive `ConstIsSafe` (`≠ .unsupportedConstOp` for all valid `σ`), and `MonoInhabitedSafe` witness `σ₀`.
5. **Universal `ClosedInstantiationTransfer` (`W4-4`):** Proved once in Ring 2 (`Trusted/Correspondence/GenericErasure.lean`), erasing `ParametricBodyVerified` + `AllSubstTypesWellFormed σ` + `AllWhereClausesDischarged` + `AllRequiredConstsCompiled` directly to closed `M_anneal` `BodyVerified` and `M_ref` (`vendor/lean-miri`) UB-freedom with `0` edits to `vendor/lean-miri`.

### Eliminated Alternatives & 12-Mutant Canary Suite

Basis: `source` + `derived` + external counterexamples.

- **Eliminated (`E1`–`E7`):** (E1) Embedding `lean-miri`'s `2,241`-LOC split `InitMask`/`ProvenanceMap` in Ring 1; (E2) trusting `rustc_transmute` (`rust-lang/rust#164247` accepts `&Cell<T> -> &T`); (E3) lazy-on-read transmute validation; (E4) higher-order `∀ (T : Type)` universe-polymorphic embeddings; (E5) finite `--mono-instance` matrices (`2.9%` coverage); (E6) omitting `required_consts` or unpolarized CTFE; (E7) unindexed `TraitDict` records or equating `Immutable` with `Freeze`.
- **Mandatory 12-Mutant Negative Suite (`M1`–`M12`):** Covers struct padding transmute read (`M1`), discarded invalid transmute (`M2`), transmute size mismatch (`M3`), pointer provenance loss across `[u8; 8]` (`M4`), chimeric pointer fragment splicing (`M5`), `MaybeUninit<Infallible>::assume_init` (`M6`), union partial-write tail read (`M7`), `&Cell<u8> -> &u8` (`M8`), omitted PME size guard (`M9`), `.unsupportedConstOp` PME vacuity (`M10`), contradictory PME guard (`M11`), and trait dictionary spoofing (`M12`).

## Boundaries

- **Pre-implementation specification (`not yet implemented` in `google/zerocopy`):** None of the Ring-1 Rust capture extensions, Ring-1 `Trusted.*` Lean modules, Ring-2 correspondence modules, or Ring-3 `theory/` libraries described in the RFC have been merged into `google/zerocopy@d3362d9a657e`. Incremental LOC numbers are `[engineering estimate]` projections.
- **Toy-model boundary (`model-system relation: none proved`):** All 16 theorems (`W3-1`–`W3-8`, `W4-0`–`W4-7`) in the companion `Wave34Semantics.lean` artifact (`1,119` lines, `0` `sorry`) prove soundness properties over `H3Wave34Toy` rather than the full `Trusted.MirSemantics` AST.
- **Unsupported / deferred capabilities (`known not to apply` / `unsupported`):** Integer-to-pointer provenance exposure (`CastKind::{PointerExposeProvenance, PointerWithExposedProvenance}`, deferred to Wave 5), weak-memory concurrency and concurrent `UnsafeCell` (`src/sync.rs`, Wave 6), `dyn Trait` vtables, SIMD (`core::arch::*`), inline `asm!`, and trusting `rustc_transmute` (`core::mem::TransmuteFrom`).
- **Pending policy choices (`unknown` until human sign-off):** Decisions `D1` (`Option PtrFrag` in W3 vs. W5), `D2` (union `IntoBytes` vs. `union_data_range`), `D3` (pre-monomorphization open `Body` capture), and `D4` (mandatory `MonoInhabitedSafe`) remain open for maintainer selection.

## Evidence

- **Primary archived specification:** [support/profile_v2_wave34_semantics_spec.md](support/profile_v2_wave34_semantics_spec.md) (`537` lines, observed `2026-11-23`).
- **Source baselines inspected:** `google/zerocopy@d3362d9a657e` (`anneal/trusted/rustc-capture/src/*.rs`, `anneal/trusted/lean/Trusted/**/*.lean`, `anneal/trusted/correspondence/Trusted/**/*.lean`, `anneal/trusted/audit/TrustedBoundary.lean:2838, 2857`, `src/{lib,wrappers,impls}.rs`, `src/util/{mod,macro_util}.rs`, `src/pointer/inner.rs`); `vendor/lean-miri` at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`InitMask.lean`, `ProvenanceMap.lean:17-21, 315-360`, `ValidityVisitor.lean:245-295, 494-505`, `Cast.lean:385-398`, `Place.lean:383-389`).
- **Measured companion mechanization execution:** `Wave34Semantics.lean` (`1,119` lines, `16` theorems, `0` `sorry`) compiled in `4.56 s` on Lean `v4.34.1` (axioms `{propext, Quot.sound}`) and `4.82 s` on Lean `v4.35.0` (axioms `{propext, Classical.choice, Quot.sound}`).

## Revalidation

1. **TCB baseline LOC check:** On `google/zerocopy`, inspect line counts across `anneal/trusted/rustc-capture/src/*.rs`, `anneal/trusted/lean/Trusted/**/*.lean`, and `anneal/trusted/correspondence/Trusted/**/*.lean` to verify whether Wave 3/4 deltas have landed relative to the `d3362d9a657e` baseline (`8,390`, `6,096`, `4,264` LOC).
2. **Audit lock verification:** Inspect `anneal/trusted/audit/TrustedBoundary.lean` (`levelParams.isEmpty` and `foundation-lock.json` checks) and `anneal/trusted/lean/foundation-lock.json` to confirm `Init.*` closure and `Type 0` constraints remain intact.
3. **Reference semantics alignment:** Diff `Miri/Memory/{InitMask,ProvenanceMap}.lean` and `Miri/Interpreter/{ValidityVisitor,Cast}.lean` in `proofs-rs/lean-miri` to check whether fragment reassembly or two-pass transmute validation changed since `8144389c895da997`.
