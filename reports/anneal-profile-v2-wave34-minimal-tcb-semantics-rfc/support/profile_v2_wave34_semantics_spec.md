# Profile v2 Wave 3 & Wave 4 Minimal-TCB Lean Semantics Specification

> **Document Class:** Pre-Implementation Standalone RFC (Three-Partition Architectural Specification)
> **Target Repository:** `google/zerocopy` (`anneal/trusted/`, `anneal/theory/`, `anneal/correspondence/`, `src/`)
> **Pinned Toolchain Baselines:** `anneal-rustc-capture` (`rust-lang/rust` `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `vendor/lean-miri` (`rust-lang/rust` `8144389c895da997dbdecaa635e41d6a50be6ffd`), Lean `v4.34.1` / `v4.35.0` (`module` mode, `#4139`)
> **Companion Mechanization:** `Wave34Semantics.lean` (`H3Wave34Toy`, 16 theorems, `0` `sorry`, `[kernel-checked proof] [toy model]`)

---

# Partition 1 — Normative Architecture Specification

## 1. Purpose, Scope, Guarantees, and Non-Goals

### 1.1 Purpose and Coverage Scope

Anneal's `Profile v1` (`mirProfileVersion = 1` on `main`) models fixed-width integers, `bool`, `char`, `Ordering`, fieldless enums, value tuples, stack allocations, and `CastKind::IntToInt` over single-body closed MIR. Extending `Trusted.MirSemantics` through Waves 1–2 (local references, raw pointers, `#[repr(C)]` / `#[repr(transparent)]` / `#[repr(packed)]` structs, payload enums, `SpecCore` `#4102`, and modular `TerminatorKind::Call` summaries) covers concrete scalar, pointer, and aggregate control flow across `388 / 546` (`71.1%`) of `zerocopy`'s callable `unsafe` blocks under concrete monomorphization (`[source inspection]` of `src/`).

Two foundational semantic capabilities separate Wave 2 from universal verification of `zerocopy` as a generic systems library:

1. **Wave 3 — Byte-Level Initialization, Unions, Uninitialized Wrappers, Padding Reset, and Transmutation:** Operational semantics for per-byte initialization and pointer-fragment provenance (`AllocByte` / `InitMask` / `PtrFrag`), `#[repr(C)] union` (`union_data_range`), `core::mem::MaybeUninit<T>`, `core::mem::ManuallyDrop<T>`, two-pass `CastKind::{Transmute, Subtype, BoxDerefTransmute}` with eager padding reset and scalar provenance stripping, unsized slice layouts `[T]` / `&[T]` / `&mut [T]` (`size <= isize::MAX`), and core pointer byte intrinsics (`ptr::{read, write, read_unaligned, write_unaligned, copy_nonoverlapping, copy, write_bytes}`). Wave 3 raises concrete monomorphized coverage to `416 / 546` (`76.2%`) callable `unsafe` blocks and `57 / 63` (`90.5%`) `#[kani::proof]` harnesses (`[source inspection]`).
2. **Wave 4 — Universe-Monomorphic (`Type 0`) Parametric `<T: ?Sized>`, Coherence-Keyed `TraitContract`s, Associated Types, and Polar PME Admission:** Parametric verification of generic Rust functions and `unsafe impl`s directly over open type parameters (`MirTy.param`), const parameters (`ConstExpr.param`), associated-type projections (`MirTy.assocProj`), declarative `TraitContract` bounds (`KnownLayout`, `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`, `TransmuteFromPtr`, `HasField`), and compile-time `Body::required_consts` (`const { assert!(...) }`) post-monomorphization errors (PME) — **without** monomorphizing every concrete client type `T`. Wave 4 raises universal (`∀ T`) library verification from `16 / 546` (`2.9%`) monomorphic callable blocks in Waves 1–3 to **`462 / 546` (`84.6%`)** directly and **`488–503 / 546` (`89.4%–92.1%`)** with declarative macro-rule templates, plus **`62 / 63` (`98.4%`)** Kani proof contracts (`[source inspection]`).

### 1.2 End-to-End Soundness Guarantees

1. **Byte-Exact Correspondence with `vendor/lean-miri` (`M_anneal` $\leftrightarrow$ `M_ref`):** Every Wave 3 step on `AllocByte` buffers commutes with `vendor/lean-miri`'s split `(rawBytes : ByteArray, initMask : InitMask, provenance : ProvenanceMap)` state via a quotient Galois insertion (`projectToSplit` / `liftFromSplit`) that erases unobserved `rawBytes` wherever `initMask.get i = false`.
2. **Eager Two-Pass Transmute Soundness:** `CastKind::{Transmute, Subtype, BoxDerefTransmute}` enforces `src.isSized && dst.isSized && src.size == dst.size` (`FaultKind.undefined` on size mismatch), validates `src` while resetting struct/enum padding to `.uninit` and stripping provenance on non-pointer scalars, and **eagerly** validates `dst` at the cast statement itself (matching `rustc`'s LLVM `@llvm.assume` emission even when the destination value is never read).
3. **Pointer-Fragment Fidelity vs. Scalar Provenance Stripping:** Byte copies through `MaybeUninit<u8>` or `#[repr(C)] union` data ranges preserve byte-indexed `PtrFrag` provenance across 8-byte pointer snapshots, whereas typed scalar copies/transmutes through integer types (`u8`, `u32`, `usize`) strip provenance (`prov := none`).
4. **Universal Parametric Soundness (`∀ σ`) in Strict `Type 0`:** Every Wave 4 `ParametricBodyVerified` theorem is universe-monomorphic (`ci.levelParams.isEmpty == true`, enforced by `TrustedBoundary.lean:2838, 2857`). Through `ClosedInstantiationTransfer` (proved once in `correspondence/` with `0` custom axioms), any closed substitution `σ` whose concrete types satisfy `WellFormedTypeLayoutSpec`, whose `ImplBinding` witnesses discharge all `Body.whereClauses` in the coherence-keyed trait registry, and whose `Body.requiredConsts` evaluate to `.ok true` under `ConstMirMachine` yields concrete `BodyVerified` in `M_anneal` (and, via Pass-2 simulation, UB-freedom in `M_ref` / `lean-miri`) with zero re-elaboration of the generic body proof.
5. **Polar Anti-Vacuity on Compile-Time `const { assert! }` Guards:** Generic `required_consts` (`static_assert!`, `static_assert_dst_is_not_zst!`) are evaluated under `SafePolarMirSem`: CTFE `.stuck` / `.unsupported` states never count as a rejected monomorphization that vacuously discharges runtime verification obligations.

### 1.3 Explicit Non-Goals and Fail-Closed Boundaries

Wave 3 and Wave 4 step to `FaultKind.unsupported` (refuting `WellFormed` fail-closed) on:

- **Integer-to-pointer provenance angelism (`CastKind::PointerExposeProvenance` / `PointerWithExposedProvenance`, `.addr()` / `with_exposed_provenance`):** Deferred to Wave 5 (`PtrInner::as_non_null` alignment checks and pointer-bit tagging). Note that `CastKind::Transmute` between pointers and integers does *not* expose provenance in `rustc`/Miri and is modeled directly in Wave 3 (§3.4).
- **Shared-memory concurrency, atomic memory orderings, and concurrent `UnsafeCell` mutation (`src/sync.rs`):** Deferred to Wave 6. Wave 4 models sequential `UnsafeCell` (`FreezeSensitivity`) and `ReadOnly<T>` encapsulation (`zerocopy::Immutable` vs. `rustc` `Freeze`, §4.3) without weak-memory thread interleavings.
- **Dynamic trait objects (`dyn Trait`) and indirect vtable dispatch:** Out of scope for `zerocopy`'s core hierarchy (which uses `Sized` types, `[E]` slices, and `#[repr(C)]` slice DSTs).
- **Target-specific SIMD intrinsics (`core::arch::*`) and inline assembly (`asm!`):** Deferred beyond Wave 4.
- **Reliance on `rustc_transmute` (`core::mem::TransmuteFrom`) as a trusted soundness oracle:** Strictly forbidden (§7, E2); Anneal verifies operational byte and borrow semantics from first principles.

---

## 2. Trust Boundary, Module Topology, and Minimal-TCB LOC Budget

### 2.1 Four-Ring Trust Architecture

Wave 3 and Wave 4 preserve Anneal's strict separation between Pass-1 candidate TCB (`trusted/lean/`), Pass-2 correspondence (`trusted/correspondence/`), standalone audit (`trusted/audit/TrustedBoundary.lean`), and `0`-TCB library proof automation (`theory/`):

```
┌──────────────────────────────────────────────────────────────────────────────┐
│  Ring 0: Standalone Audit Kernel & Inspector (`trusted/audit/`, ~5.4K LOC)   │
│  - Enforces `foundation-lock.json` (51 `Init.*` modules, `prelude` only)     │
│  - Enforces `ci.levelParams.isEmpty == true` (`Type 0`), `0` custom axioms   │
│  - Enforces Pass-2 `verifyRefEvaluatorIndependence` (`M_anneal` ∩ `M_ref`=∅) │
└──────────────────────────────────────┬───────────────────────────────────────┘
                                       │ audits
        ┌──────────────────────────────┴───────────────────────────────┐
        ▼                                                              ▼
┌───────────────────────────────────────┐    ┌─────────────────────────────────┐
│ Ring 1: Candidate TCB (`trusted/`)    │    │ Ring 2: Pass-2 Correspondence   │
│ - `rustc-capture`: polymorphic +      │    │ (`trusted/correspondence/` +    │
│   layout/union/PME extractor          │◄──►│  `vendor/lean-miri`)            │
│ - `Trusted.MirModel`: `AllocByte`,    │    │ - `projectToSplit`/`liftFromSplit`
│   `PtrFrag`, `PtrMeta`                │    │ - Wave 3 simulation on concrete │
│ - `Trusted.MirAst`: `CastKind`,       │    │   closed bodies                 │
│   `MirTy.param/slice/union/assocProj` │    │ - `ClosedInstantiationTransfer` │
│ - `Trusted.MirSemantics`: two-pass    │    │   erasing `ParametricVerified`  │
│   `evalTransmute`, `TypeLayoutSpec`,  │    │   to closed `M_anneal` -> `M_ref`
│   `TraitContract`, `ConstMirMachine`  │    └─────────────────────────────────┘
└───────────────────┬───────────────────┘
                    │ imported read-only by
                    ▼
┌──────────────────────────────────────────────────────────────────────────────┐
│  Ring 3: Zero-TCB Proof Automation (`anneal/theory/Anneal/`, `0` TCB LOC)    │
│  - `Anneal.ByteSubLens`: compositional byte-slice lenses & disjoint framing  │
│  - `Anneal.DstLayoutAlgebra`: `TrailingSliceLayout`, `extend`, `pad_to_align`│
│  - `Anneal.ZerocopyTraits`: reusable lemmas for `#[derive(FromBytes, ...)]`, │
│    `HasField` projections, `TransmuteFromPtr`, and `SplitByteSlice`          │
└──────────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Audited Baseline and Incremental TCB LOC Budget

Live baseline measurements (`[real measurement]` on `main` at `d3362d9a657e`):
- `anneal/trusted/rustc-capture/src/*.rs`: `8,390` LOC (`extract.rs` `1,316`, `identity.rs` `2,397`, `ir.rs` `1,730`, `capture.rs` `1,412`, `lean.rs` `801`, `main.rs` `369`, `publication.rs` `188`, `driver.rs` `177`).
- `anneal/trusted/lean/Trusted/**/*.lean`: `6,096` LOC (`MirModel.lean` `262`, `MirAst/*` `1,175`, `MirSemantics/*` `4,659` including `782` LOC in `CanaryFixtures.lean`).
- `anneal/trusted/correspondence/Trusted/**/*.lean`: `4,264` LOC (`Correspondence.lean` `692`, `Config.lean` `1,309`, `State.lean` `1,272`, `Codec.lean` `419`, `Eval.lean` `220`, `Simulation.lean` `191`, `CanaryFixtures.lean` `161`).

Incremental TCB budget (`[engineering estimate]`, targeting minimal Ring-1 surface by keeping `lean-miri`'s `1,734`-LOC `InitMask.lean` and `507`-LOC `ProvenanceMap.lean` out of Ring 1):

| Component / File | Wave | Ring | Est. Delta LOC | Core Responsibility |
| :--- | :---: | :---: | :---: | :--- |
| `rustc-capture` (`extract.rs`, `ir.rs`, `lean.rs`) | W3 | Ring 1 (Rust) | `+650–950` | Extract `FieldsShape::Union` (`union_data_range`), `ManuallyDrop`, `MaybeUninit`, `[T]`/`&[T]`, `CastKind::{Transmute, Subtype, BoxDerefTransmute}`, and `ptr::*` intrinsics. |
| `Trusted/MirModel.lean` & `MirAst/*` | W3 | Ring 1 (Lean) | `+180–260` | Upgrade `AllocByte.init` with `Option PtrFrag` *(qualified by Open Decision `D1`)*; add `PtrMeta`, `UnionTy`, `MirTy.{slice, array, union, maybeUninit}`, `CastKind.{transmute, subtype, boxDerefTransmute}`. |
| `Trusted/MirSemantics/{Bytes,Layout,Transmute,Intrinsics}.lean` | W3 | Ring 1 (Lean) | `+920–1,340` | `ByteRole` layout lowering, `validateAndResetBytes`, two-pass `evalTransmute`, fat-slice bounds (`<= isize::MAX`), and `ptr::{read, write, read_unaligned, copy_nonoverlapping, write_bytes}`. |
| `Trusted/Correspondence/{State,Simulation}.lean` | W3 | Ring 2 (Lean) | `+600–900` (`0` Ring-1 TCB) | `projectToSplit` / `liftFromSplit` Galois simulation against `vendor/lean-miri`'s `Allocation`, `ValidityVisitor`, and `Cast.evalCast`. |
| `rustc-capture` (polymorphic `Body`, `where`, `required_consts`) | W4 | Ring 1 (Rust) | `+850–1,250` | Extract open `MirTy.param`, `ConstExpr.param`, `MirTy.assocProj`, normalized `ParamEnv` `whereClauses`, `ImplBinding` headers, and `Body::required_consts` CTFE bodies *(qualified by Open Decision `D3`)*. |
| `Trusted/MirAst/{Types,Generic,Body}.lean` | W4 | Ring 1 (Lean) | `+280–400` | `TyParamId`, `ConstParamId`, `TraitDefId`, `MirTy.{param, assocProj}`, `WhereClause`, `ImplKey`, and `Body.{typeParamCount, constParamCount, whereClauses, requiredConsts}`. |
| `Trusted/MirSemantics/{TypeSpec,Contract,ConstPme}.lean` | W4 | Ring 1 (Lean) | `+1,120–1,700` | `TypeLayoutSpec` (`<T: ?Sized>`), `InvariantEnv` (`FullValid`), coherence-keyed `TraitRegistry` (`TraitContract` / `ImplBinding`), polar `ConstMirMachine` (`ConstIsSafe` + 4-place `substTySizes`), and `ParametricBodyVerified`. |
| `Trusted/Correspondence/GenericErasure.lean` | W4 | Ring 2 (Lean) | `+550–800` (`0` Ring-1 TCB) | `ClosedInstantiationTransfer` (`∀ σ`) erasing `ParametricBodyVerified` to closed concrete `BodyVerified` -> `M_ref` (`lean-miri`). |
| `theory/Anneal/{DstLayoutAlgebra,ZerocopyTraits}.lean` | W3–W4 | Ring 3 (`0` TCB) | `+1,800–2,600` (`0` TCB) | Zero-TCB `TrailingSliceLayout` rounding/extend/split proofs, `#[derive]` soundness combinators, and `HasField` tuple lenses. |
| **Total Incremental Ring-1 TCB** | **W3 + W4** | **Ring 1** | **`+4,000–5,900`** | **`+1,500–2,200` Rust capture + `+2,500–3,700` `Trusted.*` Lean** (strictly within `foundation-lock.json` 51-module `Init.*` closure). |

---

## 3. Wave 3 Normative Semantics: `AllocByte`, `InitMask`, Unions, `MaybeUninit`, and Two-Pass `Transmute`

### 3.1 Unified `AllocByte` + `PtrFrag` Representation and `lean-miri` Galois Correspondence

`Trusted/MirModel.lean:86-88` already represents an abstract memory byte as a unified sum type rather than three parallel mutable arrays. Wave 3 retains this unified representation and refines its provenance payload from whole-allocation `Option AllocId` to `Option PtrFrag` *(qualified inline by Open Decision `D1` in Partition 3)*:

```lean
-- Trusted/MirModel.lean (Wave 3 refinement; strict Type 0, foundation-lock clean)
structure PtrFrag where
  allocId     : AllocId
  borrowTag   : Nat          -- Tree Borrows BorTag (`0` prior to TB activation)
  ptrAddrBits : BitVec 64    -- Snapshot of full 8-byte pointer offset at fragment creation
  byteIdx     : UInt8        -- Fragment index `0 ..< 8` within the 8-byte pointer
  deriving DecidableEq

inductive AllocByte where
  | uninit
  | init (byte : UInt8) (prov : Option PtrFrag := none)
  deriving DecidableEq
```

**Why unified `AllocByte` instead of importing `Miri.Memory.InitMask` into Ring 1:**
`vendor/lean-miri/Miri/Memory/InitMask.lean` (`1,734` LOC) implements a imperative 64-bit block-chunked bitset (`inlineBlocks` + `Array UInt64`), and `ProvenanceMap.lean` (`507` LOC) implements sorted `Array` binary searches with `Array.qsort`. Both are execution-speed optimizations for an interpreter; importing them into `Trusted.MirSemantics` would add `2,241` LOC to Ring 1, violate `foundation-lock.json` (`Std` / `Array.qsort`), and force `Anneal.ByteSubLens` proofs to reason over 64-bit word-boundary bitmasks.

Instead, Ring 2 (`Trusted.Correspondence.State`) relates `List AllocByte` in $M_{\text{anneal}}$ to `Miri.Memory.Allocation` `(bytes : ByteArray, initMask : InitMask, provenance : ProvenanceMap)` in $M_{\text{ref}}$ via two canonical maps:

1. **Concrete Projection (`projectToMiri : List AllocByte → SplitMiriBuf`):** Maps `.uninit` at index `i` to `(rawByte := 0, initBit := false, prov := none)` and `.init b p` to `(rawByte := b, initBit := true, prov := p)`.
2. **Quotient Abstraction (`liftFromMiri : ByteArray → InitMask → ProvenanceMap → List AllocByte`):** Maps index `i` to `.uninit` whenever `initMask.get i = false` (ignoring `bytes[i]` and any stale fragment) and to `.init bytes[i] (provenance.getFrag i)` whenever `initMask.get i = true`.

`liftFromMiri` and `projectToMiri` form a **quotient Galois insertion** (`Wave34Semantics.lean`, Theorems `W3-1` `lift_project_id` and `W3-2` `liftFromSplit_quotient_uninit`, `[kernel-checked proof] [toy model]`):
- **Left Inverse:** `liftFromMiri (projectToMiri buf) = buf` for every `buf : List AllocByte`.
- **Dead-Byte Quotient:** For any two `M_ref` allocations `(bs₁, mask, prov)` and `(bs₂, mask, prov)` agreeing on all indices where `mask.get i = true`, `liftFromMiri bs₁ mask prov = liftFromMiri bs₂ mask prov` regardless of dead bytes left in `rawBytes` behind uninitialized mask bits (such as `Allocation.writeUninit` leaving old raw bytes in place while clearing `initMask`).
- **Initialization Monotonicity (`AllocByte.Subsumes`):** Defining `.uninit ⊑ x` for all `x` and `.init b₁ p₁ ⊑ .init b₂ p₂ ↔ b₁ = b₂ ∧ p₁ = p₂` mirrors Miri's `InitSubsumes` preorder: overwriting `.uninit` with `.init` refines state monotonically, while resetting padding clears `.init` back to `.uninit`.

### 3.2 `PtrFrag` Reassembly and the `MaybeUninit<u8>` vs. `u8` Provenance Asymmetry

In `rustc` and `vendor/lean-miri` (`Miri/Memory/ProvenanceMap.lean:17-21, 315-360` and `Miri/Interpreter/Place.lean`), copying memory byte-by-byte through `[u8; N]` vs. `[MaybeUninit<u8>; N]` has **observable UB consequences**:

1. **Typed integer byte copy (`u8`, `u32`, `usize`):** `u8` has ABI `BackendRepr::Scalar(Scalar::Initialized { value: Int(I8, false), valid_range: 0..=255 })`. Reading `u8` executes `readScalar(..., readProvenance := false)`, which faults with `FaultKind.undefined` on `.uninit` and **strips provenance** (`prov := none`). Reassembling a pointer from `[u8; 8]` produces an integer-derived pointer (`allocId = none`), which faults with `FaultKind.undefined` on dereference.
2. **Untyped byte copy (`MaybeUninit<u8>`, `#[repr(C)] union`, `ptr::copy_nonoverlapping`):** `MaybeUninit<u8>` has ABI `BackendRepr::Scalar(Scalar::Union { value: Int(I8, false) })`. Miri routes `Scalar::Union` copies through `Allocation.copyRepeatedly` (never `readScalar`), preserving `.uninit` bytes AND decomposing 8-byte pointers into 8 per-byte `PtrFrag { allocId, borrowTag, ptrAddrBits, byteIdx := k }` entries (`k = 0..7`).
3. **8-Byte Pointer Reassembly (`reassemblePtrVal`):** Reading a 64-bit pointer (`MirTy.rawPtr` / `MirTy.ref`) from 8 bytes `b₀ .. b₇` in `Trusted.MirSemantics.Bytes`:
   - If any `bₖ = .uninit`, fault with `FaultKind.undefined` (reading uninitialized pointer bytes is immediate UB).
   - Let `addr : UInt64` be the target-endian 64-bit word assembled from `b₀.byte .. b₇.byte`.
   - If **every** `k ∈ 0..7` carries `some ⟨aid, tag, snapBits, idx⟩` with the **same** `(aid, tag, snapBits)`, `idx == k`, and `addr.toBitVec == snapBits`, return `PtrVal { allocId := some aid, borrowTag := tag, offsetBytes := addr }` (full provenance preserved!).
   - Otherwise (if any byte has `prov = none`, if fragments come from two different pointers — *chimeric pointer splicing* — or if a single byte was mutated after fragment creation so `addr.toBitVec != snapBits`), return provenance-free `PtrVal { allocId := none, borrowTag := 0, offsetBytes := addr }` (matching `ProvenanceMap.inspectFragments` in `vendor/lean-miri/Miri/Memory/ProvenanceMap.lean:328-358`!).

Theorem `W3-6` (`maybeUninit_preserves_provenance_while_u32_strips` in `Wave34Semantics.lean`) mechanically verifies this exact asymmetry: `Ptr -> MaybeUninit -> Ptr` is the identity on `samplePtrBytes`, whereas `Ptr -> u32 -> Ptr` strips all `PtrFrag` tags (`stripProv samplePtrBytes ≠ samplePtrBytes`).

### 3.3 `ByteRole` Layout Lowering: Struct Padding, `ManuallyDrop<T>`, `MaybeUninit<T>`, and `#[repr(C)] union`

Every sized layout of byte length `S` lowers to a canonical `Vector ByteRole S` (`List ByteRole` of length `S` in `Trusted.MirSemantics.Layout`) paired with `alignLog2 : Nat` and `inhabited : Bool`:

```lean
inductive ScalarValidity where
  | allBits                                      -- u8..u128, i8..i128
  | boolRange                                    -- 0x00 or 0x01
  | charUnicode                                  -- ≤ 0x10FFFF ∧ ¬(0xD800..0xDFFF)
  | validRange (lo hi : BitVec 128)              -- NonZero<T>, rustc_layout_scalar_valid_range
  | enumDiscr (allowed : List (BitVec 128))      -- fieldless / direct-tag #[repr(int)] enum

inductive ByteRole where
  | padding                                      -- outside all field data ranges
  | unionData                                    -- inside `FieldsShape::Union` `union_data_range`
  | scalarByte (grpId : Nat) (byteIdx : Nat) (width : Nat) (v : ScalarValidity)
  | ptrByte    (grpId : Nat) (byteIdx : Nat) (nonNull : Bool)
```

Exact lowering rules matching `rustc_abi` and `vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean` (`[source inspection]`):

1. **`#[repr(C)]` / `#[repr(Rust)]` / `#[repr(packed(k))]` Structs & Tuples (`FieldsShape::Arbitrary`):**
   - `inhabited = ∀ f ∈ fields, f.inhabited`.
   - Each field `f` placed at `[offset_f .. offset_f + size_f)` contributes its shifted `ByteRole` slice; every inter-field and trailing gap byte outside `⋃_f [offset_f .. offset_f + size_f)` receives `ByteRole.padding`.
2. **`core::mem::ManuallyDrop<T>` (`#[repr(transparent)] struct ManuallyDrop<T: ?Sized>`):**
   - Identical `size`, `alignLog2`, `inhabited`, `FreezeSensitivity`, `largest_niche`, and `roles` to `T` (`specManuallyDrop inner := inner`).
   - Only `TerminatorKind::Drop` changes: dropping `ManuallyDrop<T>` is a no-op (`StatementKind::StorageDead` still deallocates the stack slot when going out of scope).
3. **`core::mem::MaybeUninit<T>` (`#[repr(transparent)] union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }`):**
   - Preserves `size = T.size` and `alignLog2 = T.alignLog2`.
   - Sets **`inhabited := true` unconditionally** — even when `T` is uninhabited (`Infallible` / `!`, `size = 0`)! By contrast, `assume_init` (`CastKind::Transmute` from `MaybeUninit<Infallible>` to `Infallible`) checks `dst.inhabited` and immediately faults with `FaultKind.undefined` (Theorem `W3-7` `maybeUninit_infallible_inhabited_but_assume_init_ub`).
   - Erases all scalar niches (`largest_niche = none`, so `Option<MaybeUninit<bool>>` has `size = 2`, never `1`) and sets all `T.size` byte roles to `ByteRole.unionData`.
   - Note on `zerocopy::MaybeUninit<T: ?Sized + KnownLayout>` (`src/wrappers.rs:492`): `zerocopy`'s wrapper is a `#[repr(transparent)] struct MaybeUninit<T: ?Sized + KnownLayout>(T::MaybeUninit)` delegating unsized `[E]` to `[core::mem::MaybeUninit<E>]` via associated type `KnownLayout::MaybeUninit` (covered seamlessly by Wave 4 `MirTy.assocProj`, §4.1).
4. **`#[repr(C)] union` (`FieldsShape::Union`):**
   - `size = alignTo (max_{f ∈ fields} f.size) align`, `alignLog2 = max_{f ∈ fields} f.alignLog2`, and **`inhabited := true` unconditionally** (`NeverUnion` has `size = 0, inhabited = true`, so `Option<NeverUnion>` has `size = 1`, whereas `struct NeverStruct(Never)` is uninhabited so `Option<NeverStruct>` has `size = 0`).
   - **`union_data_range` (`joinUnionRoles`):** Offset `i ∈ [0, size)` receives `ByteRole.unionData` if **at least one** union field `f` has a non-`.padding` role at `i`, and `ByteRole.padding` **only** if offset `i` is `.padding` (or out of range `i >= f.size`) in **every** field `f` (`ValidityVisitor.unionRanges` in `vendor/lean-miri/Miri/Interpreter/ValidityVisitor.lean:245-295`). *(Interaction with `zerocopy::IntoBytes` is governed by Open Decision `D2` in Partition 3.)*
   - **Partial Union Field Writes (`PlaceElem::Field(idx, fieldTy)` on `MirTy.union`):** Writing a smaller variant `u.a = val` (`size(a) < size(U)`) overwrites bytes `[0 .. size(a))` only and leaves trailing bytes `[size(a) .. size(U))` untouched! Consequently, if `u` started uninitialized, `[size(a) .. size(U))` remains `.uninit`, and subsequently reading larger field `u.b` (`size(b) > size(a)`) faults with `FaultKind.undefined` (Theorem `W3-8` `reprC_union_partial_write_leaves_tail_uninit_ub`, matching `Toy.Zc` `R4c`).

### 3.4 Two-Pass `CastKind::{Transmute, Subtype, BoxDerefTransmute}` Semantics

In `Runtime(PostCleanup)` MIR, `Rvalue::Cast(kind, operand, dstTy)` lowers `core::mem::transmute`, `transmute_copy` patterns, variance subtype coercions (`CastKind::Subtype`), and `Box` deref transmutations (`CastKind::BoxDerefTransmute`). Following `vendor/lean-miri/Miri/Interpreter/{Cast.lean:385-398, Place.lean:383-389, ValidityVisitor.lean:494-505}` and `rustc_codegen_ssa::mir::rvalue::cg_transmute`:

1. **Sizedness & Exact Byte-Length Gate (`FaultKind.undefined`, NOT `.unsupported`):**
   - If `!srcTy.isSized || !dstTy.isSized` or `srcTy.size != dstTy.size`, step immediately to `.fault .undefined` (matching `Cast.lean:388`: `if src.layout.isUnsized || dest.layout.isUnsized || src.layout.size != dest.layout.size then throwUb (.transmuteSizeDiff ...)`).
2. **Pass 1 — Source Validation & Padding/Provenance Reset (`validateAtLayout srcLayout rawBytes`):**
   - Check `srcLayout.inhabited == true` (else `.fault .undefined`).
   - For each offset `i ∈ 0 ..< size`:
     - `ByteRole.padding` $\mapsto$ unconditionally reset byte `i` to **`AllocByte.uninit`** (`resetProvenanceAndPadding = true`) — **even if** the backing memory slot previously held initialized bytes!
     - `ByteRole.unionData` $\mapsto$ preserve `AllocByte` unchanged (`.uninit`, `.init b none`, or `.init b (some frag)`).
     - `ByteRole.scalarByte` $\mapsto$ require every byte of the scalar group to be `.init`, validate the assembled bit-pattern against `ScalarValidity` (`boolRange`, `charUnicode`, `validRange`, `enumDiscr`), and strip provenance (`AllocByte.init b none`).
     - `ByteRole.ptrByte` $\mapsto$ require every byte of the 8-byte pointer group to be `.init`, reassemble `PtrVal` via §3.2, enforce `addr != 0` when `nonNull = true` (`&T`, `&mut T`, `Box<T>`, `NonNull<T>`), and when the destination of the transmute is a reference (`MirTy.ref`), enforce pointer alignment `addr % dstPointee.align == 0` and pointee inhabitedness (and recursive value validity under Miri's `RefTracking` boundary).
3. **Pass 2 — Eager Destination Validation & Reset (`validateAtLayout dstLayout afterSrc`):**
   - Run the exact same `validateAtLayout` pass at `dstLayout` on `afterSrc` **at the `Rvalue::Cast` step itself** — never deferring validation until `_dst` is later read!
   - **Why eager Pass 2 is soundness-critical:** `rustc_codegen_ssa` emits `@llvm.assume` (`range`, `noundef`, non-null, alignment) on `CastKind::Transmute` scalar/pair outputs immediately at the cast site (`let _ = unsafe { transmute::<u8, bool>(2) }` is immediate UB at `-O2` and in Miri even though `_` is never read).
   - **Sharpness (`W3-4` vs. `W3-5` in `Wave34Semantics.lean`):** Transmuting `#[repr(C)] struct PadPair(u8, u16)` (`size = 4`, padding at byte `1`) to `u32` (`size = 4`, 4 scalar bytes) faults in Pass 2 (`evalTransmute = none`) even if byte `1` of stack memory happened to hold `0xFF`, because Pass 1 resets byte `1` to `.uninit`! Conversely, transmuting `PadPair(u8, u16)` to `[MaybeUninit<u8>; 4]` succeeds (`some [.init b0, .uninit, .init b2, .init b3]`).

### 3.5 Fat Slice Metadata (`[T]`, `&[T]`, `&mut [T]`) and Pointer Byte Intrinsics

To unlock `zerocopy`'s `416 / 546` Wave 3 target (`src/pointer/inner.rs`, `src/util/mod.rs`, `src/wrappers.rs`):

- **Pointer Metadata (`PtrMeta`):** `PtrVal` gains `meta : PtrMeta` (`inductive PtrMeta | thin | sliceLen (elems : UInt64)`). `UnOp::PtrMetadata` extracts `Val.unit` for `.thin` and `Val.scalar ⟨.isize, false, elems⟩` for `.sliceLen elems`. `AggregateKind::RawPtr(pointeeTy, mutability)` constructs fat raw pointers `*const [E]` / `*mut [E]` from `(dataPtr, elems)` (`src/pointer/inner.rs` `raw_from_ptr_len`).
- **`isize::MAX` Allocation & Slice Size Invariant:** Any slice dereference or `KnownLayout` slice computation requires `elems * elemSize <= (2^63 - 1)` (`isize::MAX` on 64-bit targets); overflow faults with `FaultKind.undefined`.
- **Core Pointer Intrinsics (`Trusted.MirSemantics.Intrinsics`):**
  - `core::ptr::read<T>(src)` / `read_unaligned<T>(src)`: checks `src` liveness, bounds `offset + size(T) <= alloc.len`, alignment (`align(T)` for `read`; `1` for `read_unaligned`), and `validateAtLayout T` (`read` copies without deinitializing `*src`).
  - `core::ptr::write<T>(dst, val)` / `write_unaligned<T>(dst, val)`: checks `dst` liveness, mutability, bounds, alignment (`align(T)` vs. `1`), and writes `validateAtLayout T valBytes` without reading or dropping old `*dst` (so writing into `.uninit` memory succeeds!).
  - `core::ptr::copy_nonoverlapping<T>(src, dst, count)`: checks `count * size(T) <= isize::MAX`, alignment of both `src` and `dst` to `align(T)` (even when `count == 0`!), non-overlap `[src .. src + n) ∩ [dst .. dst + n) = ∅` when `n > 0`, and copies raw `AllocByte`s verbatim (preserving `.uninit` and `PtrFrag` without running `validateAtLayout T`, matching Miri's untyped `copy_nonoverlapping`!).
  - `core::ptr::write_bytes<T>(dst, val_u8, count)`: checks `dst` alignment to `align(T)`, `n = count * size(T) <= isize::MAX`, and writes `List.replicate n (AllocByte.init val_u8 none)` (unlocking `FromZeros::zero` and `write_zeros`!).

---

## 4. Wave 4 Normative Semantics: `<T: ?Sized>`, `TraitContract`, Polar PME, and Universal Instantiation Transfer

### 4.1 Universe-Monomorphic (`Type 0`) Open Generic MIR Representation

`Trusted/audit/TrustedBoundary.lean:2838, 2857` enforces a non-negotiable invariant across every claim and theorem in Anneal:
```lean
unless claimCi.levelParams.isEmpty do
  fail s!"claim {claimName} must have no universe parameters"
```
If generic Rust functions `fn foo<T: ?Sized + IntoBytes>(x: &T)` were encoded by quantifying over Lean types `(T : Type)`, `ProgramVerified` would quantify over `Type 0` and live in `Prop` with universe-level or `Type 1` carrier structures that break `Type 0` value embeddings and `MirAst` decidability.

Wave 4 stays **100% in `Type 0`** by representing open generic parameters as **first-order de Bruijn / index identifiers** inside `Trusted.MirAst.Types` *(qualified inline by Open Decision `D3`)*:

```lean
abbrev TyParamId    := Nat
abbrev ConstParamId := Nat
abbrev TraitDefId   := Nat
abbrev AssocItemIdx := Nat

inductive ConstExpr where
  | lit   (val : BitVec 128) (width : IntWidth) (signed : Bool)
  | param (id : ConstParamId)

-- Wave 4 constructors added to `Trusted.MirAst.MirTy`:
  | param     (id : TyParamId)
  | slice     (elem : MirTy)
  | array     (elem : MirTy) (len : ConstExpr)
  | adtSliceDst (adtId : DefId) (headFields : List (Nat × MirTy)) (tailElem : MirTy)
  | assocProj (selfTy : MirTy) (traitId : TraitDefId) (assocIdx : AssocItemIdx)
```

An open `Body` (`Trusted.MirAst.Body`) carries its generic binder signature and `ParamEnv` explicitly:
```lean
inductive WhereClause where
  | isSized     (ty : MirTy)
  | traitBound  (selfTy : MirTy) (traitId : TraitDefId) (args : List MirTy)
  | typeEq      (lhs rhs : MirTy)    -- e.g., `<T as KnownLayout>::PointerMetadata == usize`

structure PmeConstBody where
  constBodyDefId : DefId             -- Index into `Program.constBodies`
  substTyArgs    : List MirTy        -- Open generic args passed into `const { assert!(...) }`
  substConstArgs : List ConstExpr

structure Body where
  argumentCount   : Nat
  locals          : List MirTy
  basicBlocks     : List BasicBlock
  isUnsafe        : Bool := false
  identity        : String := ""
  -- Wave 4 parametric extensions (empty `0` / `[]` for closed Wave 1–3 bodies):
  typeParamCount  : Nat := 0
  constParamCount : Nat := 0
  whereClauses    : List WhereClause := []
  requiredConsts  : List PmeConstBody := []
```

### 4.2 Semantic Domain `TypeLayoutSpec` + `InvariantEnv` for `<T: ?Sized>`

To interpret an open type `MirTy` under an arbitrary closed instantiation `σ` — uniformly covering `Sized` types (`u32`, `[u8; N]`, `PadPair`), unsized slices (`[E]`), and `#[repr(C)]` trailing-slice DSTs (`struct Packet { hdr: u16, body: [u8] }`) — `Trusted.MirSemantics.TypeSpec` defines a `Type 0` semantic descriptor `TypeLayoutSpec`:

```lean
/-- Freeze / interior-mutability map at byte offset `i` for metadata `m`:
distinguishes `rustc`'s `UnsafeCell` (`hasUnsafeCell = true`, disabling `readonly`
under Tree Borrows) from `zerocopy::Immutable` (`zcImmutable = true` when wrapped
in `zerocopy::ReadOnly<T>`!). -/
structure FreezeProfile where
  hasUnsafeCellAt : Nat → Bool
  zcImmutable     : Bool

structure TypeLayoutSpec where
  isSized         : Bool
  alignLog2       : Nat                        -- Alignment = 2 ^ alignLog2
  /-- Exact byte size for pointer metadata `m` (`PtrMeta.thin` iff `isSized = true`,
  `PtrMeta.sliceLen elems` for slice DSTs; `none` if metadata kind mismatches or
  `size > isize::MAX`). -/
  sizeForMeta     : PtrMeta → Option Nat
  inhabited       : Bool
  freezeProfile   : PtrMeta → FreezeProfile
  /-- Language-level byte validity & padding/provenance reset (`LangValid`),
  parameterized by `PtrMeta`. -/
  rolesForMeta    : PtrMeta → Option (List ByteRole)
```

`WellFormedTypeLayoutSpec (L : TypeLayoutSpec) : Prop` enforces:
1. **Metadata Kind Exactness:** If `L.isSized = true`, `L.sizeForMeta .thin = some sz` (`sz ≤ 2^63 - 1`) and `L.sizeForMeta (.sliceLen _) = none`. If `L.isSized = false`, `L.sizeForMeta .thin = none` and for every `elems`, `L.sizeForMeta (.sliceLen elems) = some sz` iff the trailing-slice formula `padToAlign (offset + elems * elemSize) (2 ^ L.alignLog2) ≤ 2^63 - 1`.
2. **Role-Length Agreement:** Whenever `L.sizeForMeta m = some sz`, `L.rolesForMeta m = some roles` with `roles.length = sz`.
3. **Combined Language + Library Validity (`FullValid` from `SpecCore` `#4102`):** Following `SpecCore` (`#4102`), `TypeLayoutSpec` defines language-level `LangValid` (absence of immediate `rustc`/Miri UB), while `InvariantEnv` supplies optional user/library safety invariants `LibValid : DefId → PtrMeta → List AllocByte → Prop` (defaulting to `True` for raw types and carrying user invariants on types like `NonZero` wrappers or bounded indices), with **`FullValid := LangValid ∧ LibValid`**.

### 4.3 Declarative `TraitContract` Specifications for `zerocopy`'s Core Hierarchy

Every `unsafe trait` in `zerocopy` receives a canonical `TraitContract` (`SpecCore` `#4102` Primitive 3) over `(T : TypeLayoutSpec, LibValid_T)`. Crucially, none of these contracts enumerate concrete types — they state the exact **semantic byte/layout algebra** that `#[derive(...)]` and manual `unsafe impl`s prove once at impl sites and generic methods assume at call sites:

| `zerocopy` `unsafe trait` | Associated Items Bound | Exact Semantic `TraitContract` Obligation (`SatisfiesTraitSem`) |
| :--- | :--- | :--- |
| **`KnownLayout`** (`src/layout.rs`) | `PointerMetadata` (`()` or `usize`), `MaybeUninit : ?Sized + KnownLayout`, `LAYOUT : DstLayout` | `WellFormedTypeLayoutSpec T` ∧ `T.LAYOUT` (`align = 2^alignLog2`, `size_info = Sized(sz)` or `SliceDst(TrailingSliceLayout { offset, elem_size })`) matches `T.sizeForMeta` for every `m` with `size ≤ isize::MAX`, and `T::MaybeUninit` has `sizeForMeta = T.sizeForMeta`, `alignLog2 = T.alignLog2`, `inhabited = true`, and `roles = replicate sz .unionData`. |
| **`Immutable`** (`src/lib.rs`) | — | `(∀ m, (T.freezeProfile m).zcImmutable = true)`. **Critical Distinction (`W4-7`):** Does **not** require `hasUnsafeCellAt = false`! `zerocopy::ReadOnly<UnsafeCell<U>>` has `hasUnsafeCellAt = true` (`rustc` `Freeze = false`, so Tree Borrows suppresses LLVM `readonly` on `&ReadOnly<UnsafeCell<U>>`), yet `zcImmutable = true` because `ReadOnly` exposes no shared-reference interior-mutating API (`Toy.Zc` `R7a`). |
| **`TryFromBytes`** (`src/lib.rs`) | `fn is_bit_valid(Ptr<'_, Self, (Shared, Aligned, Initialized)>) -> bool` | `SatisfiesTraitSem KnownLayout T` ∧ whenever `T::is_bit_valid(cand)` returns `true` on initialized bytes `bs` at metadata `m`, `(validateAtLayout (T.layoutAt m) bs).isSome = true ∧ LibValid_T m bs` (`FullValid`). |
| **`FromZeros`** (`src/lib.rs`) | Supertrait: `TryFromBytes` | `SatisfiesTraitSem TryFromBytes T` ∧ `T.inhabited = true` ∧ `∀ m sz, T.sizeForMeta m = some sz → FullValid T m (List.replicate sz (.init 0 none))`. |
| **`FromBytes`** (`src/lib.rs`) | Supertrait: `FromZeros` | `SatisfiesTraitSem FromZeros T` ∧ `∀ m sz (bs : List AllocByte), T.sizeForMeta m = some sz → bs.length = sz → AllBytesInit bs → FullValid T m bs` (accepts **every** initialized byte sequence, with provenance stripped on scalar reads). |
| **`IntoBytes`** (`src/lib.rs`) | Supertrait: `KnownLayout` | `SatisfiesTraitSem KnownLayout T` ∧ `∀ m bs after, FullValid T m bs → validateAtLayout (T.layoutAt m) bs = some after → AllBytesInit after` (**zero** `.uninit` padding or uninitialized union bytes at any valid metadata `m`, including dynamic slice-DST trailing padding!). *(Union `IntoBytes` policy governed by Open Decision `D2`.)* |
| **`Unaligned`** (`src/lib.rs`) | — | `T.alignLog2 = 0` (`align == 1`). *(Note: for unsized slice DSTs `#[repr(packed)] struct P { h: u8, s: [u16] }`, `Unaligned` requires `align == 1`; dynamic size rounding is already captured by `KnownLayout::LAYOUT`.)* |
| **`HasField<Field, VariantId, FieldId>`** (`src/lib.rs`, `src/impls.rs`) | `type Type: ?Sized` | Projected field offset `off(m)` and `Field::Type` layout form a valid sub-range `[off(m) .. off(m) + size_Field(m)) ⊆ [0 .. size_Self(m))` preserving `Ptr` alignment/validity invariants (`Anneal.ByteSubLens`, unlocking `351` tuple `impls.rs` blocks in one family!). |
| **`TransmuteFromPtr<Src, SV, DV, _>`** (`src/pointer/transmute.rs`) | — | Operational pointer/reference cast contract parameterized by validity wrappers `(SV, DV)` (`Uninit`, `Initialized`, `AsInitialized`, `Valid`): `sizeForMeta_Src = sizeForMeta_Dst` and every byte buffer satisfying `SV(Src)` satisfies `DV(Dst)` after `validateAtLayout Src`. |

### 4.4 Coherence-Keyed Trait Registry (Preventing Dictionary Spoofing)

A well-known soundness pitfall in dictionary-passing encodings of Rust traits (`PROBED: falsified` in `closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws`, §7 E6) is **dictionary spoofing**: if a generic function takes an unconstrained Lean record `dict : TraitDict T` as an argument, two call sites could pass *inconsistent* `KnownLayout::LAYOUT` constants or associated types `T::MaybeUninit` for the **same** concrete Rust type `MyStruct`, violating Rust's global trait coherence!

Wave 4 closes this hole structurally in `Trusted.MirSemantics.Contract`:
- Every trait implementation is keyed canonically in `Program.traitRegistry` by **`ImplKey := (selfTy : ClosedMirTy, traitId : TraitDefId, args : List ClosedMirTy)`** (mirroring `rustc`'s coherence key).
- `TraitRegistryWf` checks that keys are **pairwise distinct** (at most one `ImplBinding` per `(selfTy, traitId, args)`), that every `unsafe impl` in the crate supplies a kernel-checked `ProductiveUnsafeImpl` proof of `SatisfiesTraitSem` (`SpecCore` `#4102` coinductive productive cycles), and that `evalOpenTy σ (.assocProj base tr idx)` looks up the **unique** associated type registered at `(evalOpenTy σ base, tr)`!

### 4.5 Polar CTFE Admission (`ConstMirMachine`) for Generic `const { assert! }` (PME)

In `zerocopy`, `Wrap::transmute_ref`, `Wrap::transmute_mut`, `util::transmute_unchecked`, and `static_assert_dst_is_not_zst!` rely on inline `const { assert!(...) }` blocks (`C06c`, `23` `unsafe` blocks across `17` generic functions). In `rustc`'s `Runtime(PostCleanup)` MIR, inline `const { ... }` assertions **disappear** from runtime `basic_blocks` and are stored in **`Body::required_consts`**!

As established by two `PROBED` counterexamples in `google/zerocopy:reference`:
1. **Omission Unsoundness (`W4-6` `pme_guard_rejects_size_mismatch_and_opSafe_false` in `Wave34Semantics.lean`):** If `Body::required_consts` is ignored, `Wrap::<&mut u8, &mut [u8; 4]>::transmute_mut` satisfies **every** `where`-clause trait bound (`u8` and `[u8; 4]` are both `Sized + FromBytes + IntoBytes`), yet `size_of::<u8>() != size_of::<[u8; 4]>()` causes immediate 4-byte out-of-bounds memory corruption!
2. **Quadrant-4 Polarity Inversion (`anneal-pme-mir-semantics-and-polar-ctfe-admission`):** In `ParametricBodyVerified`, `MonoCompiled σ b.requiredConsts` sits on the **left (negative polarity)** of an implication (`MonoCompiled σ → RuntimeWellFormed σ`). If `ConstMirMachine` models an unimplemented CTFE opcode as `.stuck` / `.failed` and defines `MonoCompiled := (evalConst == .succeeded)`, then **every** unmodeled CTFE op evaluates `MonoCompiled` to `False`, **vacuously proving** `False → RuntimeWellFormed σ` (a catastrophic fail-open soundness bug!).

Wave 4 enforces **Polar CTFE Admission (`SafePolarMirSem`)** in `Trusted.MirSemantics.ConstPme`:
1. **Three-Way CTFE Outcome:** `ConstOutcome := .compiled | .rejectedE0080 | .unsupportedConstOp`.
2. **4-Place Transitive Substitution (`substTySizes`):** Instantiating `PmeConstBody` under `σ` substitutes open types/consts across (i) `locals`, (ii) `Cast` target types, (iii) `NullaryOp::SizeOf` / `AlignOf` operands, and (iv) **transitively called `const fn` helper bodies** in `Program.constBodies`.
3. **Polar Precondition Obligation:** To verify a generic `Body` `b` with `b.requiredConsts ≠ []`, the prover must establish **both**:
   - **Positive CTFE Modeling Completeness (`ConstIsSafe`):** For every `σ` satisfying `AllWhereHold σ b.whereClauses`, every `c ∈ b.requiredConsts` evaluates strictly to `.compiled` **or** `.rejectedE0080` (**never** `.unsupportedConstOp`!), AND
   - **Conditional Runtime Safety:** Whenever every `c ∈ b.requiredConsts` evaluates to `.compiled`, the instantiated runtime body `instBody σ b` is `WellFormed` and satisfies `FnContract.post`.
   - **Non-Vacuity Witness (`MonoInhabitedSafe`, *qualified by Open Decision `D4`*):** At least one concrete closed substitution `σ₀` satisfies `AllWhereHold σ₀ b.whereClauses ∧ AllPmeCompiled σ₀ b.requiredConsts`, ruling out contradictory PME guards (`size_of::<T>() == 4 && size_of::<T>() == 8`) that reject every possible Rust type.

### 4.6 Universal `ClosedInstantiationTransfer` Theorem ($\forall \sigma$) and Pass-2 Erasure Bridge

Wave 4 keeps `vendor/lean-miri` (`M_ref`, which executes closed monomorphic Rust types) completely untouched! Instead, Ring 2 (`Trusted/Correspondence/GenericErasure.lean`) proves one universal erasure meta-theorem (`Wave34Semantics.lean`, Theorem `W4-4` `closed_instantiation_soundness_transfer`, `[kernel-checked proof] [toy model]`):

```lean
theorem ClosedInstantiationTransfer
    (prog : OpenProgram) (b : Body)
    (hParam : ParametricBodyVerified prog b)
    (σ : ClosedSubst)
    (hWf    : AllSubstTypesWellFormed σ)
    (hWhere : AllWhereClausesDischarged prog.traitRegistry σ b.whereClauses)
    (hCtfe  : AllRequiredConstsCompiled prog.constBodies σ b.requiredConsts) :
    Trusted.MirSemantics.BodyVerified (eraseProgram σ prog) (eraseBody σ b)
```

Composed with Ring 2's closed-body simulation theorem (`M_anneal` `BodyVerified` $\implies$ `M_ref` `lean-miri` UB-freedom):
- **Library verification (`cargo anneal verify --package zerocopy`):** Proves `ParametricBodyVerified` **once** per generic function (`O(1)` per generic item in `zerocopy`, zero monomorphization blowup!).
- **Downstream concrete caller (`zerocopy` user instantiating `u32::as_bytes`, `[u16]::as_bytes`, or `Packet::read_from_bytes`):** Applies `ClosedInstantiationTransfer` directly to the pre-proved library theorem + concrete `ImplBinding` + concrete `ConstMirMachine` reduction (`rfl`), transferring UB-freedom down to closed `lean-miri` execution with **zero** custom axioms and **zero** re-verification of `zerocopy`'s MIR bodies!

---

## 5. End-to-End Verification Workflows on Verbatim `zerocopy` Items & Negative Mutant Suite

### 5.1 Verbatim First-Customer Walkthroughs (`src/`)

| Verbatim `zerocopy` Item | Location in `src/` | Wave | Exercised Semantics & Proof Discharge |
| :--- | :--- | :---: | :--- |
| `util::transmute_unchecked<Src, Dst>(src: Src) -> Dst` | `src/util/mod.rs:582` | W3 + W4 | `ManuallyDrop::new(src)` (identity layout) + `transmute_copy` (`&ManuallyDrop<Src> as *const Src as *const Dst` + `ptr::read`) + PME `static_assert!(Src, Dst => size_of::<Dst>() == size_of::<Src>())`. Discharged universally (`∀ Src, Dst`) under `FnContract.safetyPre`: `SemIntoBytes`/`BitValid(Src -> Dst)` + PME `sizeEq`. |
| `MaybeUninit::<T>::{uninit, new, assume_init}` | `src/wrappers.rs:510–575` | W3 + W4 | Unconditional inhabitedness of `T::MaybeUninit` (`MirTy.assocProj`), `.unionData` preservation of `.uninit` and `PtrFrag`, and `assume_init` safety precondition `FullValid T m bytes` (rejecting `MaybeUninit::<Infallible>::uninit().assume_init()`, `W3-7`). |
| `IntoBytes::as_bytes<Self: ?Sized + IntoBytes + Immutable>(&self) -> &[u8]` | `src/lib.rs:6089` | W4 | Fat-pointer metadata extraction (`KnownLayout::size_of_val_raw`), `AggregateKind::RawPtr([u8], .shared)` re-slicing, `Immutable` (`zcImmutable = true`, allowing `ReadOnly<UnsafeCell<T>>`), and `IntoBytes` (`0` `.uninit` bytes across `[0, sizeForMeta m)` $\implies$ valid `&[u8]` slice, `W4-1` & `W4-5`). |
| `FromZeros::zero<Self: ?Sized + FromZeros>(&mut self)` | `src/lib.rs:3838` | W3 + W4 | Exclusive `&mut Self` borrow + `ptr::write_bytes(ptr, 0u8, size_of_val(self))` + `TraitContract(FromZeros)` proving `replicate sz (.init 0 none)` restores `FullValid Self m` (`W4-2`). |
| `Wrap::<&mut Src, &mut Dst>::transmute_mut` | `src/util/macro_util.rs:845` | W4 | Bidirectional mutable reference transmutation (`Src, Dst: Sized + FromBytes + IntoBytes`), PME `sizeEq Src Dst` + `alignLe Dst Src`, `aligned_of_pow2_le` (`W4-0`), forward `evalTransmute Src Dst` at reborrow entry, and write-back `evalTransmute Dst Src` on protector release (`W4-3`, `Toy.Transmute` `R3`!). |
| `SplitByteSlice::split_at_unchecked` / `PtrInner::split_at_unchecked` | `src/pointer/inner.rs` | W3 + W4 | `TrailingSliceLayout` rounding phase (`Anneal.DstLayoutAlgebra`): verifies prefix slice DST `[0 .. prefixBytes)` and suffix `[E]` `[suffixOffset .. totalSize)` stay disjoint even when trailing struct padding follows the slice prefix (`zerocopy-knownlayout-slicedst-rounding-phase-and-split-at-padding-overlap`). |
| Tuple `unsafe impl HasField for (T0, ..., Tn)` (`351` blocks) | `src/impls.rs` | W4 | Single declarative projection-lens schema (`Anneal.ByteSubLens`) discharging field-offset bounds and alignment preservation across all `351` generated tuple impl blocks. |

### 5.2 Mandatory 12-Mutant Negative Soundness Suite (Fail-Closed Canaries)

Every Wave 3 and Wave 4 PR MUST ship negative canary tests in `CanaryFixtures.lean` and `anneal-audit` proving that `WellFormed` / `ParametricBodyVerified` is **refuted** (never vacuously satisfied) on all 12 bug classes:

1. **M1 (Struct Padding Transmute Read):** `transmute::<PadPair(u8, u16), u32>(x)` even when stack memory was pre-zeroed (`W3-4`).
2. **M2 (Discarded Eager Invalid Transmute):** `let _ = transmute::<u8, bool>(2u8);` (must fault at the `Cast` statement, matching `@llvm.assume`).
3. **M3 (Transmute Size Mismatch):** `CastKind::Transmute` from `u16` to `u32` (must fault `.undefined`, not `.unsupported`).
4. **M4 (Pointer Provenance Loss Across `[u8; 8]`):** Transmuting `&u32 -> [u8; 8] -> &u32` and dereferencing (must fault `.undefined` on provenance-stripped pointer).
5. **M5 (Chimeric Pointer Fragment Splicing):** Combining bytes `0..4` of `ptr1` (`MaybeUninit<u8>`) with bytes `4..8` of `ptr2` and reading as `*const u8` (must strip provenance in `reassemblePtrVal`).
6. **M6 (`MaybeUninit<Infallible>::assume_init`):** Constructing `MaybeUninit::<Infallible>::uninit()` succeeds, while `assume_init()` faults `.undefined` (`W3-7`).
7. **M7 (Union Partial-Write Tail Read):** Writing `u.a = 7u8` into uninitialized `#[repr(C)] union { a: u8, b: u16 }` and reading `u.b` (`W3-8`).
8. **M8 (`&Cell<u8> -> &u8` Shared-Reference Interior Mutability):** Rejected by `Immutable` (`zcImmutable = false` on `Cell<u8>`) and Tree Borrows `Freeze` rules — catching the exact bug where upstream `rustc_transmute` (`#164247`) is unsound!
9. **M9 (Omitted PME Size Guard):** `transmute_mut::<Src, Dst>` without `const { assert!(size_of::<Src>() == size_of::<Dst>()) }` refuted at `Src = u8, Dst = [u8; 4]` (`W4-6`).
10. **M10 (Quadrant-4 `.unsupportedConstOp` PME Vacuity):** Generic function with a `required_consts` block invoking an unmodeled CTFE op MUST fail `ConstIsSafe` rather than vacuously passing `ParametricBodyVerified`.
11. **M11 (Contradictory PME Guard):** Generic function guarded by `const { assert!(size_of::<T>() == 4 && size_of::<T>() == 8) }` rejected by `MonoInhabitedSafe`.
12. **M12 (Trait Dictionary Spoofing):** Supplying a forged `KnownLayout` impl claiming `size_of::<u8>() == 4` rejected by `TraitRegistryWf` coherence indexing.

---

## 6. Interface Locks and PR Sequencing

Wave 3 and Wave 4 layer cleanly onto Anneal's active foundation locks without breaking `mirProfileVersion = 1` proofs during staging:

1. **Lean `module` Mode & `v4.35.0` Alignment (`#4139`):** Once `#4139` lands (and using plain `prelude` prior to `#4139`, while `TrustedBoundary.lean` rejects `module` headers), all new Ring-1 modules (`Trusted/MirSemantics/{Transmute,Intrinsics,TypeSpec,Contract,ConstPme}.lean`), Ring-2 modules (`Trusted/Correspondence/GenericErasure.lean`), and Ring-3 libraries (`Anneal/{DstLayoutAlgebra,ZerocopyTraits}.lean`) declare `module` + `prelude`, explicit `public import` / `public section` boundaries, and stay strictly inside `trusted/lean/foundation-lock.json`'s 51 `Init.*` modules.
2. **Pass-2 Correspondence Module-Origin Lock (`#3977` / `#4005`):** Shared pure data types (`PtrFrag`, `AllocByte`, `PtrMeta`) live strictly in `Trusted/MirModel.lean` (imported by both `M_anneal` and `M_ref`), preserving `verifyRefEvaluatorIndependence` (`M_ref` imports zero operational step rules from `Trusted.MirSemantics.*`).
3. **`SpecCore` Three-Primitive Alignment (`#4102`):** Wave 4 reuses `FnContract` (`safetyPre` vs. `behaviorPre`), `InvariantEnv` (`FullValid := LangValid ∧ LibValid`), and `TraitContract` / `ImplBinding` (`ProductiveUnsafeImpl`) verbatim rather than introducing a parallel specification AST.
4. **Linear PR Stack (`gh stack --base main`):**
   - **PR W3-1:** `Trusted.MirModel` (`PtrFrag` / `PtrMeta`) + `MirAst` (`MirTy.{union, maybeUninit, slice, array}`, `CastKind.{transmute, subtype, boxDerefTransmute}`) + `rustc-capture` extraction (`mirProfileVersion` bumped to `2` or feature-gated behind `mirProfileVersion = 2`).
   - **PR W3-2:** `Trusted.MirSemantics.{Layout, Transmute, Intrinsics}` (`ByteRole`, `validateAtLayout`, two-pass `evalTransmute`, `ptr::*` byte intrinsics) + Mutants `M1`–`M7`.
   - **PR W3-3:** `Trusted.Correspondence` Wave 3 Galois simulation (`projectToMiri` / `liftFromMiri`) against `vendor/lean-miri` + first-customer verification of concrete `zerocopy` `wrappers::MaybeUninit` and `util::transmute_unchecked`.
   - **PR W4-1:** `Trusted.MirAst` open generics (`MirTy.{param, assocProj}`, `WhereClause`, `PmeConstBody`) + `rustc-capture` polymorphic pre-monomorphization `Runtime(PostCleanup)` extractor.
   - **PR W4-2:** `Trusted.MirSemantics.{TypeSpec, Contract, ConstPme}` (`TypeLayoutSpec` for `<T: ?Sized>`, coherence-keyed `TraitRegistry`, polar `ConstMirMachine`) + Mutants `M8`–`M12`.
   - **PR W4-3:** `Trusted.Correspondence.GenericErasure` (`ClosedInstantiationTransfer`) + Ring-3 `Anneal.{DstLayoutAlgebra, ZerocopyTraits}` + universal (`∀ T`) verification of `zerocopy`'s `IntoBytes`, `FromZeros`, `FromBytes`, `TryFromBytes`, `Wrap::transmute_{ref,mut}`, and `HasField` methods.

---

# Partition 2 — Decision Rationale and Eliminated Alternatives

## 7. Eliminated Architectural Candidates and Comparative Basis

Every candidate below was evaluated against the sealed `(C+, C-)` outcome contract (§9.1), live `Trusted.*` / `vendor/lean-miri` source code, and primary counterexamples in `google/zerocopy:reference` and `Wave34Semantics.lean`:

| ID | Eliminated Alternative | Disqualification / Dominance Classification | Governing Contract Clause & Primary Falsification / Dominance Basis |
| :--- | :--- | :--- | :--- |
| **E1** | **Embed `vendor/lean-miri`'s Split `(ByteArray, InitMask, ProvenanceMap)` Directly in Ring-1 `Trusted.MirSemantics`** | Comparative dominance + `C+.3` (`foundation-lock.json` & minimal TCB) | `Miri/Memory/InitMask.lean` (`1,734` LOC, 64-bit word-chunked bitsets) and `ProvenanceMap.lean` (`507` LOC, `Array.qsort` binary search) pull `2,241` LOC and `Std`/array-sorting dependencies outside `trusted/lean/foundation-lock.json` into Ring 1, and complicate compositional byte-slice framing in `Anneal.ByteSubLens`. Retaining unified `List AllocByte` in Ring 1 (`~35` LOC delta) and proving the quotient Galois insertion `projectToMiri` / `liftFromMiri` (`W3-1`, `W3-2`) in Ring 2 (`Trusted.Correspondence`) achieves identical Miri fidelity at `< 2%` of the Ring-1 TCB cost. |
| **E2** | **Trust Upstream `rustc_transmute` (`core::mem::TransmuteFrom`) as a Soundness Oracle in `rustc-capture`** | Absolute disqualification (`PROBED: falsified` + `C-.1`) | Upstream `rustc_transmute` contains live soundness bug `rust-lang/rust#164247`: `Assume::NOTHING` accepts `&Cell<T> -> &T` because `SharedRef` records no `Freeze` side-condition on its referent, causing LLVM `-O2` `readonly` miscompilation and Miri Tree Borrows UB (`rustc-transmute-dfa-validity-safety-invariants-and-reference-soundness`). Furthermore, `rustc_transmute`'s DFA abstracts away operational source padding resets (`W3-4`) and pointer-provenance fragment stripping (`W3-6`). |
| **E3** | **Lazy-on-Read Transmute Validation (Unchecked Byte Copy at `CastKind::Transmute`, Validating Only When Read)** | Absolute disqualification (`PROBED: falsified` + `C+.1`) | `rustc_codegen_ssa::mir::rvalue::cg_transmute` emits immediate `@llvm.assume` metadata (`range`, `noundef`, non-null, alignment) at the `CastKind::Transmute` statement itself (`rustc-transmute-backend-repr-provenance-padding-and-llvm-assume`, case `tm_9`), and `vendor/lean-miri` validates both source and destination eagerly inside `copy_op_allow_transmute`. Lazy validation would verify `let _ = unsafe { transmute::<u8, bool>(2) }` as safe when `rustc -O2` and Miri treat it as immediate UB. |
| **E4** | **Higher-Order / Universe-Polymorphic Shallow Embedding (`∀ (T : Type), ...`) for Wave 4 Generics** | Absolute disqualification (`PROBED: falsified` + `C+.3` / `C-.2`) | `Trusted/audit/TrustedBoundary.lean:2838, 2857` rejects any claim or proof constant with non-empty `levelParams` (`Type 0` monomorphism). Moreover, shallow Lean types `T : Type` cannot model unsized Rust slice DSTs (`[E]` / `TrailingSliceLayout`), uninitialized struct padding resets (`W3-4`), or `PtrFrag` provenance stripping (`W3-6`). First-order `MirTy.param` indices interpreted over `TypeLayoutSpec : Type 0` stay strictly universe-monomorphic while handling `Sized` and `!Sized` types uniformly. |
| **E5** | **Monomorphization-Only Verification (`--mono-instance` Matrix Without Open Wave 4 `TraitContract`s)** | Absolute disqualification (`C+.2`) | Only `16 / 546` (`2.9%`) callable `unsafe` blocks in `zerocopy` are monomorphic; the remaining `530` blocks are parameterized over `<T: ?Sized>`, `<Src, Dst>`, or `HasField` tuple arities. Finite monomorphization proves safety only for tested primitives (`u8`, `u32`), leaving `zerocopy` callers unverified for arbitrary downstream `#[derive(FromBytes, IntoBytes)]` structs and dynamic slice lengths. |
| **E6** | **Definition-Site-Only Generic Checks or Unpolarized `ConstSucceeds` Admission for `Body::required_consts`** | Absolute disqualification (`PROBED: falsified` + `C+.2`) | Definition-site layout checks without `ParamEnv` / PME guards fail on non-substitution-stable layouts (`Packed<T0>`, `Toy.SubstStable` `R3`); omitting `Body::required_consts` admits out-of-bounds transmutation (`W4-6`); and placing unpolarized `evalConst == .succeeded` in negative precondition polarity turns `.unsupportedConstOp` into a vacuous `False → Safe` pass (`anneal-pme-mir-semantics-and-polar-ctfe-admission`). `SafePolarMirSem` (`ConstIsSafe` + `ConstSucceeds` + 4-place `substTySizes`) eliminates both failure modes. |
| **E7** | **Unindexed Dictionary-Passing Records for Traits, or Equating `zerocopy::Immutable` with `rustc` `Freeze`** | Absolute disqualification (`PROBED: falsified` + `C+.2`) | Passing free `TraitDict` records allows call sites to spoof `KnownLayout::LAYOUT` or associated types with inconsistent witnesses (`closure-upvar-defunctionalization-symbolic-vtables-and-trait-coherence-laws`), while equating `Immutable` with `Freeze` falsely rejects `zerocopy::ReadOnly<UnsafeCell<T>>` (`isFreeze = false`, `zcImmutable = true`, `W4-7`, `Toy.Zc` `R7a`). Coherence-keyed `(ClosedMirTy, TraitDefId, List ClosedMirTy)` indexing and distinct `(hasUnsafeCellAt, zcImmutable)` fields resolve both. |

---

# Partition 3 — Open Decisions, Outcome Contract, and Epistemic Calibration

## 8. Open Architectural Decisions for Human Resolution

Four bounded design decisions require sign-off before locking Ring-1 `Trusted.*` interfaces in PRs `W3-1` and `W4-1`:

### Decision D1 — `AllocByte` Pointer-Fragment Granularity in Wave 3 (`Option PtrFrag` vs. Deferred Wave 5 `Option AllocId`)

- **Context:** `Trusted/MirModel.lean:88` currently carries `prov : Option AllocId` on `AllocByte.init`. In `vendor/lean-miri`, copying a pointer through `[MaybeUninit<u8>; 8]` or `ptr::copy_nonoverlapping` requires 4 fields per fragment (`allocId`, `borrowTag`, 8-byte `ptrAddrBits` snapshot, and `byteIdx : 0..7`) so `inspectFragments` can reject chimeric half-pointer splices and byte-mutated pointers (§3.2).
- **Options:**
  - **Option D1-A (Recommended):** Upgrade `AllocByte.init` to `prov : Option PtrFrag` immediately in PR `W3-1` (`+~35` Ring-1 TCB LOC in `MirModel.lean` and `Bytes.lean`).
  - **Option D1-B:** Keep `prov : Option AllocId` in Wave 3 and fail closed (`FaultKind.unsupported`) whenever a sub-pointer read/write splits an 8-byte pointer across `MaybeUninit<u8>` bytes, deferring `PtrFrag` to Wave 5.
- **Trade-Offs:** D1-A adds `~35` LOC once and makes Wave 3's `projectToMiri` / `liftFromMiri` correspondence with `lean-miri` exact on day one (including `MaybeUninit<&T>` and `util::transmute_unchecked` over pointer-bearing structs) with zero second migration of `Trusted.MirModel`. D1-B saves `~35` LOC in Wave 3 but forces a breaking `AllocByte` signature churn across all Wave 3–4 proofs in Wave 5.
- **Recommendation, Confidence, & Default:** **Option D1-A** (**High confidence**; proposed default if approved).
- **Blast Radius:** Touches `Trusted/MirModel.lean`, `Trusted/MirSemantics/Bytes.lean`, and `Trusted/Correspondence/State.lean` (`3` files).

### Decision D2 — `#[repr(C)] union` `IntoBytes` Contract Policy (Strict Every-Field Full-Size vs. `union_data_range`)

- **Context:** In `rustc` / `vendor/lean-miri`, `ValidityVisitor.visit_union` preserves initialized bytes across `union_data_range` (the union of all fields' non-padding byte ranges). However, `zerocopy-derive`'s `PaddingCheck::Union` (`src/util/macro_util.rs`, formalized in `Toy.Zc` `R4a`–`R4d`) enforces a **strictly stronger** conservative rule for `#[derive(IntoBytes)]` on unions: *every* field must have `size(field) == size(Union)` and `IntoBytes(field)` (because writing a smaller field `u.a` leaves `[size(a)..size(U))` uninitialized, `W3-8`, and Rust has not yet stabilized cross-field padding guarantees in `rust-lang/unsafe-code-guidelines#438`).
- **Options:**
  - **Option D2-A (Recommended):** Model `rustc`/Miri's exact `union_data_range` in operational `Trusted.MirSemantics` (so Miri correspondence is byte-exact), while defining `zerocopy`'s `TraitContract(IntoBytes)` and `#[derive(IntoBytes)]` combinators to require full initialization across `[0, size)` on every `FullValid` instance — matching `zerocopy`'s strict `PaddingCheck::Union` (`∀ f, size(f) == size(U) ∧ IntoBytes(f)`) for safe unions without baking `zerocopy` conservatism into Rust's operational semantics.
  - **Option D2-B:** Restrict `MirSemantics` union byte preservation itself to `⋂_f data_bytes(f)` (intersection rather than union of field data ranges).
- **Trade-Offs:** D2-A keeps Ring-1 operational semantics faithful to `rustc` and `lean-miri` (allowing manual `unsafe` code that initializes the largest union variant first to be verified!) while keeping `TraitContract(IntoBytes)` 100% sound against partial-write UB (`W3-8`). D2-B diverges from `lean-miri` (`ValidityVisitor.unionRanges`) and breaks Pass-2 simulation equivalence on valid Rust unions.
- **Recommendation, Confidence, & Default:** **Option D2-A** (**High confidence**; proposed default if approved).
- **Blast Radius:** Scoped to `Trusted/MirSemantics/Layout.lean` (`joinUnionRoles`) and Ring-3 `Anneal/ZerocopyTraits.lean` (`0` Ring-1 TCB impact for the derive rule).

### Decision D3 — Wave 4 Polymorphic Capture Boundary (Pre-Monomorphization Open `Body` vs. Macro/Derive-Only Parametricity)

- **Context:** `anneal-rustc-capture` currently extracts closed monomorphic `Instance` MIR via `tcx.instance_mir(...)`. Achieving universal (`∀ T`) verification across `462–488 / 546` callable `unsafe` blocks in `zerocopy` requires verifying generic functions (`IntoBytes::as_bytes`, `FromZeros::zero`, `Wrap::transmute_{ref,mut}`, `PtrInner::*`) once over open `MirTy.param` / `MirTy.assocProj` types.
- **Options:**
  - **Option D3-A (Recommended):** Extend `anneal-rustc-capture` in PR `W4-1` to extract polymorphic `tcx.mir_drops_elaborated_and_const_checked(def_id)` (or post-cleanup polymorphic `optimized_mir(def_id)` prior to `Instance` substitution), lowering `TyKind::Param`, `ConstKind::Param`, `TyKind::Alias(Projection, ..)`, normalized `tcx.param_env(def_id)` bounds, and `Body::required_consts` into open `Trusted.MirAst.Body`. Retain `--mono-instance` as a fallback flag for concrete caller specialization.
  - **Option D3-B:** Keep `rustc-capture` strictly monomorphic (`--mono-instance` only) in Wave 4 and prove parametric theorems only at the semantic trait-law level in `theory/`, leaving generic Rust function bodies verified only on a finite canary matrix.
- **Trade-Offs:** D3-A costs `+850–1,250` Rust LOC in `rustc-capture` and `+550–800` Ring-2 LOC for `ClosedInstantiationTransfer`, but delivers true `O(1)` universal (`∀ T`) library verification of `zerocopy`'s `462+` generic `unsafe` blocks. D3-B avoids polymorphic MIR extraction but leaves `97%` of `zerocopy`'s callable `unsafe` blocks unverified for unseen downstream types (failing `C+.2`).
- **Recommendation, Confidence, & Default:** **Option D3-A** (**High confidence**; required to satisfy `C+.2`).
- **Blast Radius:** `anneal/trusted/rustc-capture/src/{extract.rs, ir.rs, identity.rs, lean.rs}`, `Trusted/MirAst/{Types,Body}.lean`, and `Trusted/Correspondence/GenericErasure.lean`.

### Decision D4 — `MonoInhabitedSafe` Non-Vacuity Gate on PME-Guarded Generic Functions

- **Context:** A generic function with `Body::required_consts` (`const { assert!(...) }`) could accidentally write mutually inconsistent compile-time guards (or have a buggy `where` clause) such that *zero* concrete Rust types pass CTFE — making `∀ σ, AllPmeCompiled σ → Safe σ` vacuously true.
- **Options:**
  - **Option D4-A (Recommended):** Enforce `MonoInhabitedSafe` as a mandatory lint/audit gate (`anneal-audit` anti-vacuity check): every verified generic `Body` with non-empty `requiredConsts` (or `safetyPre`) must exhibit at least one concrete closed witness `σ₀` (auto-synthesized at `u8` / `[u8; 1]` when trivial, or supplied in `Spec.lean`) satisfying `AllWhereHold σ₀ ∧ AllPmeCompiled σ₀` by kernel reduction.
  - **Option D4-B:** Emit a non-blocking CLI warning when no `σ₀` witness is provided, requiring `MonoInhabitedSafe` only under `--strict-anti-vacuity`.
- **Trade-Offs:** D4-A completely closes dead-PME vacuity (Mutant `M11`) and composes naturally with Anneal's anti-vacuity audit philosophy (`0` extra Ring-1 `MirSemantics` LOC if checked as an auxiliary theorem obligation in `TrustedBoundary.lean`). D4-B reduces proof friction by ~3 lines on exotic multi-parameter generics at the cost of allowing dead PME functions to appear "verified".
- **Recommendation, Confidence, & Default:** **Option D4-A** (**High confidence**; auto-witnessed at `u8` for `>90%` of `zerocopy` items).
- **Blast Radius:** `anneal/trusted/audit/TrustedBoundary.lean` and `cargo-anneal` proof template generator (`~80` LOC).

---

## 9. Outcome Contract Ledger and Epistemic Calibration

### 9.1 Sealed Outcome Contract `(C+, C-)` and Confirmed Cliffs

**Positive Obligations (`C+`):**
- **`C+.1` (Wave 3 Byte/Union/Transmute Fidelity):** Model per-byte initialization and pointer-fragment provenance, `#[repr(C)] union` (`union_data_range`), `MaybeUninit<T>`, `ManuallyDrop<T>`, two-pass eager `CastKind::{Transmute, Subtype, BoxDerefTransmute}` padding reset & scalar provenance stripping, fat slices `[T]`/`&[T]`/`&mut [T]` (`<= isize::MAX`), and `ptr::{read, write, read_unaligned, copy_nonoverlapping, write_bytes}`, with Pass-2 correspondence against `vendor/lean-miri`.
- **`C+.2` (Wave 4 Universal `<T: ?Sized>` Parametric Verification):** Verify `zerocopy`'s generic `KnownLayout`, `Immutable`, `TryFromBytes`, `FromZeros`, `FromBytes`, `IntoBytes`, `Unaligned`, `HasField`, and `TransmuteFromPtr` methods universally (`∀ T: ?Sized`) without per-type monomorphization, handling associated types and `Body::required_consts` (`const { assert! }`) soundly and connecting parametric proofs to concrete closed types via a kernel-checked instantiation transfer theorem.
- **`C+.3` (Minimal-TCB & Audit Lock Compliance):** Minimize Ring-1 TCB LOC while preserving `TrustedBoundary.lean` `Type 0` monomorphism (`ci.levelParams.isEmpty == true`), `foundation-lock.json` (`prelude` + 51 `Init.*` modules), `0` custom axioms (`⊆ {propext, Classical.choice, Quot.sound}`), and Pass-2 `verifyRefEvaluatorIndependence`.
- **`C+.4` (OSS-Clean Deliverable & Kernel-Checked Toy Mechanization):** Produce a 100% OSS-clean 3-partition specification paired with a `0`-`sorry` Lean 4 mechanization of core `InitMask` transmute and parametric `TraitContract` instantiation theorems.

**Exclusions and Non-Goals (`C-`):**
- **`C-.1`:** Zero reliance on upstream `rustc_transmute` (`TransmuteFrom`) as a trusted oracle (`PROBED: falsified` via `rust-lang/rust#164247`).
- **`C-.2`:** Zero universe-polymorphic or `Type 1` carrier encodings in Ring-1 `Trusted.*`.
- **`C-.3`:** Exclude Wave 5/6 orthogonal axes (`PointerExposeProvenance` / `PointerWithExposedProvenance` integer-pointer angelism, concurrent atomics / weak-memory `UnsafeCell`, `dyn Trait` vtables, SIMD, inline `asm!`), failing closed with `FaultKind.unsupported`.
- **`C-.4`:** Zero production repository mutations during pre-implementation specification design.

**Confirmed Clause-to-Machinery Cliffs:**
1. **`C+.2` (`<T: ?Sized>` Slice DSTs vs. `T: Sized` Only):** Indexing `TypeLayoutSpec` by `PtrMeta` (`Option UInt64`) and verifying `TrailingSliceLayout` `isize::MAX` bounds adds `~280` Ring-1 LOC over a `Sized`-only `Nat` layout record, directly required because `IntoBytes::as_bytes`, `FromZeros::zero`, `TryFromBytes::try_read_from_bytes`, and `PtrInner::split_at_unchecked` are all `<Self: ?Sized>`.
2. **`C+.2` (Polar CTFE `ConstMirMachine` for `Body::required_consts`):** Modeling three-valued `ConstOutcome` (`ConstIsSafe` + 4-place `substTySizes`) adds `~420` Ring-1 LOC, directly required because `Runtime(PostCleanup)` MIR erases `zerocopy`'s `static_assert!` blocks into `Body::required_consts` and unpolarized CTFE evaluation causes Quadrant-4 vacuity (`§4.5`, E6).

### 9.2 Epistemic Calibration and Companion Mechanization Inventory

- **Stopping Status & Deliverability:** **`bounded stop` $\to$ Qualified Partial Spec (Standalone RFC)**. Core ground premises are `PROBED` against live `main` (`d3362d9a657e`), `vendor/lean-miri`, `google/zerocopy:reference`, and `Wave34Semantics.lean`, and pre-delivery read-only audit passed across all 6 invariants (`0` falsified claims shown as viable). Convergence is capped at `bounded stop` solely on (a) human sign-off on Open Decisions `D1`–`D4` (§8) and (b) single-author design synthesis without independent multi-model blind-holdout review.
- **Unblocking Check to Advance to `Settled Spec` (Tracked `anneal/docs/` Doc):** Human resolution of `D1`–`D4` in §8 (confirming defaults `D1-A`, `D2-A`, `D3-A`, `D4-A` or selecting alternatives), after which Partition 1 projects directly into `anneal/docs/` with zero structural redesign.
- **Evidence Classification Summary:**
  - **`[real measurement]`:** Live `anneal/trusted/` and `src/` baseline LOC counts (§2.2) and `Wave34Semantics.lean` kernel compilation / axiom audit timings across `Lean v4.34.1` (`4.56s`, `{propext, Quot.sound}`, `0` `Classical.choice`) and `Lean v4.35.0` (`4.82s`, `{propext, Classical.choice, Quot.sound}`).
  - **`[source inspection]`:** `zerocopy` `546`-callable `unsafe` block Wave 3/4 coverage counts (§1.1), `TrustedBoundary.lean` `levelParams.isEmpty` invariant, and `vendor/lean-miri` `ValidityVisitor` / `Cast` / `ProvenanceMap` exact semantics (§3).
  - **`[engineering estimate]`:** Incremental Wave 3 and Wave 4 LOC ranges in §2.2.
  - **`[kernel-checked proof] [toy model]` (`model-system relation: none proved`):** All 16 theorems in companion `Wave34Semantics.lean` (`1,119` lines, `0` `sorry`, strict `Type 0`), summarized below:

| Theorem ID | `H3Wave34Toy` Declaration | Mechanized Property (`[kernel-checked proof] [toy model]`) |
| :--- | :--- | :--- |
| `W3-1` | `lift_project_id` | Left-inverse abstraction round-trip `liftFromSplit (projectToSplit buf) = buf`. |
| `W3-2` | `liftFromSplit_quotient_uninit` | Dead-byte quotient invariance across arbitrary `rawBytes` behind `initMask[i] = false`. |
| `W3-3` | `evalTransmute_sound_of_intoBytes_fromBytes` | `src.size = dst.size ∧ SemIntoBytes src ∧ SemFromBytes dst` implies two-pass `evalTransmute` succeeds (`isSome = true`). |
| `W3-4` | `padPair_to_u32_transmute_is_ub` | Struct padding reset in Pass 1 makes `PadPair(u8, u16) -> u32` fault (`none`) even on `0xFF`-initialized backing bytes. |
| `W3-5` | `padPair_to_maybeUninit_u32_ok` | `PadPair(u8, u16) -> MaybeUninit<u32>` succeeds (`some`), resetting offset `1` to `.uninit` while preserving field bytes. |
| `W3-6` | `maybeUninit_preserves_provenance_while_u32_strips` | `Ptr -> MaybeUninit -> Ptr` preserves `PtrFrag` provenance, whereas `Ptr -> u32 -> Ptr` strips provenance (`stripProv ≠ id`). |
| `W3-7` | `maybeUninit_infallible_inhabited_but_assume_init_ub` | `MaybeUninit<Infallible>` is inhabited (`some []`), while `assume_init` to `Infallible` faults (`none`). |
| `W3-8` | `reprC_union_partial_write_leaves_tail_uninit_ub` | Partial write `u.a = 7` on `#[repr(C)] union { a: u8, b: u16 }` leaves byte `1` `.uninit`, faulting on `u.b` read. |
| `W4-0` | `aligned_of_pow2_le` | Constructive power-of-two alignment divisibility (`IsPow2 d → IsPow2 s → d ≤ s → addr % s = 0 → addr % d = 0`). |
| `W4-1` | `parametric_intoBytes_as_bytes_verified` | Universal (`∀ σ`) proof of `IntoBytes::as_bytes<Self: ?Sized + IntoBytes + Immutable>(&self) -> &[u8]`. |
| `W4-2` | `parametric_fromZeros_zero_verified` | Universal (`∀ σ`) proof of `FromZeros::zero<Self: ?Sized + FromZeros>(&mut self)`. |
| `W4-3` | `parametric_transmute_mut_verified` | Universal (`∀ σ`) bidirectional proof of `Wrap::<&mut Src, &mut Dst>::transmute_mut` under PME `sizeEq` + `alignLe`. |
| `W4-4` | `closed_instantiation_soundness_transfer` | Closed-instantiation soundness transfer (`ParametricVerified` + `AllWhereHold σ` + `AllPmeCompiled σ` $\implies$ `OpSafeAt σ`). |
| `W4-5` | `slice_u8_as_bytes_instantiated` | Concrete `!Sized` slice-DST instantiation of `parametric_intoBytes_as_bytes_verified` at `Self = [u8]` for all lengths `m`. |
| `W4-6` | `pme_guard_rejects_size_mismatch_and_opSafe_false` | Negative PME control: `Src = u8, Dst = [u8; 4]` satisfies all trait bounds yet fails `evalPmeGuard` (`some false`) and `¬OpSafeAt`. |
| `W4-7` | `readOnly_unsafeCell_immutable_separation` | `zerocopy::Immutable` vs. `rustc` `Freeze` separation on `ReadOnly<UnsafeCell<u8>>` and coherence-keyed trait indexing. |

*Authored by an AI agent acting on joshlf's behalf.*
