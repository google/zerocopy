<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Zero-TCB Anneal–Aeneas Interoperability Architecture

> **Status: Planned Interop Architecture.**
>
> **Shipped today (Stage 0 alpha, [`#4095`](https://github.com/google/zerocopy/issues/4095)):**
> Core `anneal/` has zero dependency on Aeneas or Mathlib and verifies small
> scalar Rust crates on Lean `v4.34.1` (see [alpha guide](alpha.md)).
>
> **Planned architecture described here:** `anneal/interop/aeneas-bridge/` is
> an opt-in, zero-TCB interoperability package sequenced after Lean toolchain
> alignment ([`#4016`](https://github.com/google/zerocopy/issues/4016)) and
> MIR Profile v2+ slice, borrow, endianness, and abort support
> ([`#4097`](https://github.com/google/zerocopy/issues/4097),
> [`#4102`](https://github.com/google/zerocopy/issues/4102)).

## 1. Motivation and zero-TCB architecture

[Aeneas](https://github.com/AeneasVerif/aeneas) verifies safe Rust crates by
translating Charon LLBC into pure Lean 4 functional programs over
`Aeneas.Std.Result α := ITree RustEffect α` with Hoare-logic specifications
`WP.spec` (total, panic-free) and `WP.dspec` (partial, panic-free). When a safe
crate calls an `unsafe` or unextracted leaf function—such as a byte-cast
routine, a `copy_nonoverlapping` buffer writer, a `MaybeUninit` initializer, or
a mutable slice splitter—Aeneas leaves an external hook in `FunsExternal.lean`.

Even when an engineer fills that hook with a constructive pure Lean `def`
rather than an `axiom`, nothing links the hand-written Lean `def` to the real
Rust implementation: a missing bounds check, wrong byte order, or `unsafe` UB
in the Rust leaf silently invalidates the Aeneas caller proof.

`anneal/interop/aeneas-bridge/` closes this correspondence gap inside Lean 4
with **zero additions to Anneal's Trusted Computing Base** (`0` LOC added to
`anneal/trusted/lean/`, `anneal/trusted/audit/`, or
`anneal/trusted/rustc-capture/`) and **zero custom Lean axioms**:

1. **Constructive `FunsExternal.lean`:** Author the external leaf as a
   constructive pure Lean `def leaf_fn : α -> Aeneas.Std.Result β` with its
   usual `@[step]` Hoare triple so existing Aeneas caller proofs and tactics
   (`step*`, `scalar_tac`, `bv_tac`) continue working unchanged.
2. **Operational MIR refinement in Anneal:** Capture the real Rust leaf's
   `Runtime(PostCleanup)` MIR with Anneal and prove `AnnealRefinesAeneas`
   relating `Trusted.MirSemantics` execution of the leaf to `leaf_fn`.
3. **Zero-axiom composition and multi-kernel replay:** Combine the Aeneas
   caller proof and the Anneal leaf refinement proof via transfer theorems
   (`transfer_wp_spec`, `transfer_wp_dspec`) inside one Lean 4 build graph, and
   replay the composed theorem under independent external kernels (`nanoda_bin`,
   `con-ron`, `lake check --paranoid`) strictly within
   `{propext, Classical.choice, Quot.sound}`.

### Opt-in package layout (`anneal/interop/aeneas-bridge/`)

Core `anneal/` never depends on Aeneas or `mathlib4`. The bridge lives in an
isolated opt-in Lake package excluded from default `cargo anneal` builds and
validated in a dedicated optional CI job:

```text
anneal/interop/aeneas-bridge/
├── lean-toolchain               # Shared pinned Lean version (matching Aeneas)
├── lakefile.toml                # Requires anneal_trusted and aeneas
├── AnnealAeneasBridge.lean      # Root module barrel (`module`, `public import`)
├── AnnealAeneasBridge/
│   ├── Platform.lean            # 64-bit platform witness (System.Platform.numBits = 64)
│   ├── Rep/
│   │   ├── Scalar.lean          # ValRefinesUScalar, ValRefinesIScalar, Bool, Char
│   │   ├── Memory.lean          # InFootprint, DisjointFootprints, FramePreserved
│   │   ├── Slice.lean           # MemRefinesByteSlice, MemRefinesByteSliceMut, SliceOf
│   │   ├── Collections.lean     # MemRefinesArray, MemRefinesVec, MemRefinesBox
│   │   └── Adt.lean             # ValRefinesOption, ValRefinesResult, ValRefinesEnum
│   ├── Refine.lean              # AnnealRefinesAeneas, AnnealRefinesAeneasLiberal,
│   │                            # AnnealRefinesAeneasPartial, transfer_wp_{spec,dspec}
│   ├── Prophecy.lean            # AnnealRefinesAeneasBack (backward-function closure)
│   └── Audit.lean               # Axiom-cone check rejecting Aeneas.Std axiomatic leaves
└── examples/
    ├── ReadU64Canary/           # Canary 1A: read-only &[u8] leaf + caller composition
    └── WriteUintSplitCanary/    # Canary 1B: unsafe &mut [u8] copy + split_at_mut
```

All bridge modules use Lean 4 `module` headers (`public import`, `@[expose]
public section`) for compatibility with upstream Aeneas while keeping proof
bodies in `.olean.private`.

## 2. Value, memory, and framing representations

The representation layer (`AnnealAeneasBridge.Rep`) maps Anneal's concrete MIR
values and `CallerMemory` onto Aeneas's pure functional types:

- **Scalars and pointer width:** `ValRefinesUScalar` and `ValRefinesIScalar`
  relate Anneal's truncated `BitVec 128` scalar encoding to Aeneas's `BitVec`-
  backed `UScalar` / `IScalar` values. Theorems involving `usize` or `isize`
  take an explicit 64-bit platform witness `System.Platform.numBits = 64`;
  fixed-width scalars require no platform assumption.
- **Byte slices, typed slices, ZSTs, and internal `MaybeUninit`:**
  `MemRefinesByteSlice`, `MemRefinesByteSliceMut`, and `MemRefinesSliceOf`
  enforce `len * sizeOf(T) <= isize::MAX` and handle both boundary regimes:
  - When `len * sizeOf(T) = 0` (empty slice or zero-sized element type), the
    pointer must be non-null and aligned without requiring a live allocation
    (matching `Trusted.MirSemantics.Memory.readBytes`).
  - When `len * sizeOf(T) > 0`, the pointer must reference a live, aligned,
    in-bounds allocation (mutable for `&mut [T]`) whose bytes decode
    element-wise to the Aeneas slice.
  - Because `Trusted.MirSemantics` separates local stack storage from
    `callerMem`, an `unsafe` leaf can freely use uninitialized `MaybeUninit`
    scratch buffers internally while guaranteeing fully initialized outputs at
    the Aeneas boundary.
- **Spatial disjointness and frame preservation:** `DisjointFootprints` forbids
  aliasing between mutable and shared slice footprints, and `FramePreserved`
  guarantees that every allocation and byte outside the leaf's `&mut`
  footprints remains identical after the call. Both predicates are mandatory:
  omitting disjointness allows aliased mutation to diverge from Aeneas's pure
  values, and omitting framing allows silent corruption of unrelated caller
  state.
- **Collections and ADTs:** `Array` maps to contiguous inline bytes; `Box<T>`
  maps to a unique live mutable allocation (or dangling non-null aligned
  pointer for ZSTs); `Vec<T>` quantifies existentially over spare capacity
  `cap >= len` (matching Aeneas's capacity-erased `Vec`, so capacity-observing
  leaves cannot refine standard `Aeneas.Std.alloc.vec.Vec`); and `Option`,
  `Result`, and enums decode via captured `EnumLayout` tags and niches.

## 3. Refinement predicates and opt-in liberal variant

### Strict default: `AnnealRefinesAeneas`

One unified predicate aligns Anneal's four-way MIR outcomes (`returned`,
`unwound`, `aborted`, `Diverges`) with Aeneas's three-way `Result β` (`ok`,
`fail`, `div`):

```lean
def AnnealRefinesAeneas
    {α β : Type}
    (p : Program) (defId : DefId)
    (aeneasFn : α -> Aeneas.Std.Result β)
    (SafetyPre : α -> Prop)
    (R_in : α -> Query -> Prop)
    (R_out : α -> β -> Query -> Out -> Prop) : Prop :=
  ∀ a q, SafetyPre a -> R_in a q ->
    let ep := entryProgForBody p defId
    WellFormed ep q ∧
    match (aeneasFn a).match with
    | .ok b =>
        ¬ Diverges ep q ∧
        (∀ m, ¬ Behavior ep q (.unwound m)) ∧
        (∀ m, ¬ Behavior ep q (.aborted m)) ∧
        (∀ o, Behavior ep q (.returned o) -> R_out a b q o)
    | .div =>
        (∀ m, ¬ Behavior ep q (.unwound m)) ∧
        (∀ m, ¬ Behavior ep q (.aborted m)) ∧
        (∀ o, ¬ Behavior ep q (.returned o))
    | .vis (.fail _) _ =>
        ∀ o, ¬ Behavior ep q (.returned o)
```

For safe-API leaves containing internal `unsafe` blocks, `SafetyPre` is
`fun _ => True`, proving UB-freedom (`WellFormed`) on every valid Rust input—
including panicking inputs. On `.fail _`, the strict default requires
`∀ o, ¬ Behavior ep q (.returned o)` so that an `unsafe` leaf missing a bounds
check cannot silently return a bogus value where the Aeneas model specifies a
panic.

### Opt-in liberal refinement (~10 LOC, 0 TCB)

When an Aeneas external model intentionally over-approximates failure (modeling
`.fail` on inputs where the real Rust implementation cleanly succeeds without
UB), `AnnealAeneasBridge.Refine` exposes an opt-in
**`AnnealRefinesAeneasLiberal`** predicate (~10 LOC, `0` TCB). It retains
unconditional `WellFormed ep q` and identical `.ok`/`.div` clauses, while
omitting `∀ o, ¬ Behavior ep q (.returned o)` on the `.fail _` branch. Both
transfer theorems hold identically under strict and liberal refinement because
`WP.spec (.fail _) _ = False` and `WP.dspec (.fail _) _ = False`:

- **`transfer_wp_spec`:** Composes `AnnealRefinesAeneas` (or
  `AnnealRefinesAeneasLiberal`) with an Aeneas `WP.spec (aeneasFn a) P` caller
  proof to yield `WellFormed ∧ ¬ Diverges ∧ noUnwind ∧ noAbort` and
  `∃ b, P b ∧ R_out a b q o` on return.
- **`transfer_wp_dspec`:** Composes `AnnealRefinesAeneasPartial` (dropping
  `¬ Diverges` on `.ok`) with an Aeneas `WP.dspec (aeneasFn a) P` proof to
  transfer partial panic-free correctness.

### Backward-function / prophecy closure (`AnnealRefinesAeneasBack`)

For mutable borrow-returning leaves such as `split_at_mut`, Aeneas emits a
pair `(β × (β -> γ))` containing the borrowed view and a backward function
reconstructing the parent value after caller mutations.
`AnnealRefinesAeneasBack` specializes `AnnealRefinesAeneas` by requiring both
initial disjoint sub-footprint refinement (`R_borrow`) and universal closure
over all valid future caller mutations `ValidSubMutation` on those disjoint
sub-footprints, proving that the resulting parent memory refines `back b_final`
and preserves the surrounding frame.

## 4. MIR Profile and toolchain prerequisites

Core Anneal currently operates on the Stage 0 scalar MIR profile (`v4.34.1`).
Executing real Rust leaves through `anneal/interop/aeneas-bridge/` requires
four upstream prerequisites:

1. **Parameterized target endianness (`Program.targetEndian`):** MIR Profile v1
   currently fixes `Layout.profileTargetEndian` to `.big` because byte-
   reinterpreting operations are forbidden in Profile v1. MIR Profile v2+ must
   thread concrete target endianness (`.little` on `x86_64`/`aarch64`) into
   `Trusted.MirAst.Program` before proving little-endian byte-cast refinement.
2. **Slice, raw-pointer, and mutable-borrow MIR support:** Profile v2+ capture
   and semantics must admit `&[T]`/`&mut [T]` fat pointers, place projections,
   pointer casts, `copy_nonoverlapping`, and `CallerMemory` allocations.
3. **`TerminalOut.aborted`:** Needed in `Trusted.MirModel` (introduced in
   [Specification Core v2](spec-core-and-golden-closure.md)) to model
   `-C panic=abort` leaves accurately.
4. **Shared Lean 4 toolchain alignment (`#4016`):** Lean `.olean` files are
   minor-version-locked, so `anneal-trusted` and `aeneas` must compile under
   one shared Lean 4 toolchain (`v4.35.0+` / `v4.36.0` matching upstream
   Aeneas, which also enables `lake check --paranoid`).

## 5. Staged canary validation path and capability limits

Bridge implementation follows a two-step public canary path, each gated by
`lake check --paranoid` with zero custom axioms:

1. **Canary 1A (`byteorder::LittleEndian::read_u64`):** Exercises a read-only
   `&[u8]` slice leaf matching an existing constructive `FunsExternal.lean`
   definition (as used in `AeneasVerif/jxl-proofs`), validating `len >= 8`
   decoding, `len < 8` safe-panic UB-freedom (`¬ Behavior (.returned _)`),
   `len = 0` dangling-pointer handling, and zero-axiom composition via
   `transfer_wp_spec`. A negative mutant removing the `buf.len() >= 8` check
   must fail Anneal verification.
2. **Canary 1B (`byteorder::BigEndian::write_uint` and `split_at_mut`):**
   Exercises genuine `unsafe` `&mut [u8]` raw-pointer mutation
   (`copy_nonoverlapping` and internal `MaybeUninit` scratch storage) under
   `MemRefinesByteSliceMut` + `DisjointFootprints` + `FramePreserved`, together
   with `AnnealRefinesAeneasBack` prophecy closure for `split_at_mut`. Negative
   mutants violating bounds checks or writing outside the mutable footprint
   must fail closed.

### Axiom audit and Receipt v3 TCB accounting

`AnnealAeneasBridge.Audit` confirms that `#print axioms` on every composed
theorem stays strictly within `{propext, Classical.choice, Quot.sound}`—
verifying that none of `Aeneas.Std`'s axiomatic leaves (`get_unchecked` specs,
atomics, `Pin`, `PanicInfo`, or target-feature axioms) entered the transitive
proof cone. Receipt v3 logs the safe-caller Charon/Aeneas translation boundary
explicitly in `tcb_shims[]` while recording the verified leaf as discharged by
Anneal MIR refinement.

### Explicit capability matrix and hard limits

| Tier | Rust pattern | Bridge handling |
| :--- | :--- | :--- |
| **Supported** | Pure scalar, `&[u8]`, and `[T; N]` `unsafe` leaves (endian codecs, byte casts). | `ValRefines*` + `MemRefinesByteSlice` + `AnnealRefinesAeneas`. |
| **Supported** | Disjoint `&mut [u8]` / `&[u8]` mutators with internal `MaybeUninit` scratch buffers. | `MemRefinesByteSliceMut` + `DisjointFootprints` + `FramePreserved`. |
| **Supported** | Mutable borrow-returning splitters (`split_at_mut`). | `AnnealRefinesAeneasBack` universal prophecy closure. |
| **Supported** | Safe-API panicking leaves (`assert!`). | Unconditional `WellFormed` + strict `¬ Behavior (.returned _)` on `.fail` (or opt-in `AnnealRefinesAeneasLiberal`). |
| **Wrapper needed** | Capacity-observing `Vec<T>` or stateless pure `Fn(A) -> B` callbacks. | Explicit ghost capacity wrapper in `FunsExternal.lean` or assumed read-only total `FnContract`. |
| **Out of scope** | Re-entrant `FnMut` callbacks over shared memory, cross-call `UnsafeCell`/atomics, custom `#[global_allocator]` / pointer-address observation (`ptr as usize`), and `catch_unwind` recovery across panicking `unsafe` leaves. | Outside Aeneas's pure aliasing-XOR-mutability functional model; excluded from this first-order bridge. |
