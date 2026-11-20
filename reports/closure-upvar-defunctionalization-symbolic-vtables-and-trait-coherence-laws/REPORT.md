# Closure Upvar Defunctionalization, Symbolic VTable Dispatch, Dynamic Freeze Unpacking, and Trait Coherence Laws

## Summary

Verifying Rust closures (`Fn`, `FnMut`, `FnOnce`, `fn` pointers) and dynamic trait objects (`&dyn Trait`, `Box<dyn Trait>`, custom unsized-tail DSTs) inside a universe-monomorphic (`Type 0`) Lean 4 foundation requires matching `rustc`'s `Runtime(PostCleanup)` MIR lowering and `lean-miri`'s symbolic vtable rules rather than lifting closures to higher-order Lean functions or modeling vtables as raw memory arrays. Primary-source inspection establishes three invariants:

1. **`Type 0` Upvar Defunctionalization Across `rustc` Call Shims:**
   In `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`, `compiler/rustc_middle/src/ty/closure.rs` and `compiler/rustc_mir_transform/src/shim.rs`), `rustc` defunctionalizes closures before `PostCleanup` capture into an aggregate environment at `CAPTURE_STRUCT_LOCAL` (`_1`) holding minimally captured places (`ByValue`, `ByUse`, `ByRef(Immutable | UniqueImmutable | Mutable)`) plus four synthesized shims (`ClosureOnce`, `FnPtr`, `Reify`, `VTable`). Translating closures to higher-order Lean functions creates dependent-arity blowups on mutable captures and bumps universes to `Type 1` when open callbacks mutate `CallerMemory` (violating `TrustedBoundary.lean`'s `ci.levelParams.isEmpty` gate). Keeping concrete closures as first-order product environments and specifying open `F: FnMut` / `dyn FnMut` parameters via `Type 0` relational `ClosureContract` records (`inv`, `unnest`, `postReturn`, `postUnwind`, `dropEnv`) covers both normal returns and `ClosureOnce`'s 5-block unwind-drop ladder in `Type 0`.
2. **Symbolic VTables Prevent Forgery and Drive Runtime `FreezeVisitor` Unpacking:**
   In `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `Miri/Interpreter/{VTable,VTableMachine,VirtualCalls}.lean` and `Miri/TreeBorrows/FreezeVisitor.lean`), vtable pointers never load forgeable size, alignment, or function-pointer integers from raw memory. `VTableMachine` reserves zero-sized symbolic `.vtable` globals keyed by `(erasedConcreteTy, existentialPredicates, salt : Fin 32)`, enforces `offset == 0` and normalized non-auto-trait predicate equality (`InvalidVTableTrait` UB on forged casts), and dispatches `VTableEntry.method` while rejecting header/`vacant`/`traitVPtr` slots as UB. Because `dyn Trait` is **not** statically `Freeze`, `FreezeVisitor` (`visit_freeze_sensitive`) invokes `unpack_dyn_trait` on `&dyn Trait` retags to inspect the **concrete runtime type's** `UnsafeCell` byte intervals—marking `&dyn Counter` `Frozen` when backed by `u64` and `SharedReadWrite` on `[4, 8)` when backed by `Mixed { hdr: u32, c: Cell<u32> }`.
3. **Coherence-Keyed `(MirTy, TraitDefId)` Law Registries Prevent Dictionary Spoofing:**
   Passing trait laws (`Ord`, `Eq`, `zerocopy::IntoBytes`, `zerocopy::Immutable`) as free Lean record arguments lets an adversarial proof pass distinct `Ord` dictionaries to `BTreeMap::insert` and `BTreeMap::get`, breaking `unsafe` sortedness invariants. Indexing implementations and laws canonically by `(MirTy, TraitDefId, GenericArgs)` reflects `rustc`'s `TypingMode::Coherence` non-overlap check (`coherence.rs`) so `impl₁ = impl₂` holds by `rfl`.

---

## Applicability

This report governs the eleven subjects in `REPORT.json`:

- **Target Verification Boundary:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `TrustedBoundary.lean`, `foundation-lock.json`, `Trusted/{MirAst,MirSemantics}.lean`, `theory/Anneal/MirWp.lean`) on `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), enforcing `prelude` + 51 `Init.*` modules, `levelParams.isEmpty` (`L1335`, `L1354`), Statement-Origin Separation, `{propext, Quot.sound, Classical.choice}`, and closed tactic/notation allowlists.
- **Compiler & Reference Semantics:** `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`, `shim.rs`, `ty/{closure,vtable}.rs`, `interpret/{traits,call,visitor}.rs`, `traits/{vtable,coherence}.rs`), `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, `src/helpers.rs`), and `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`).
- **Unsafe-Trait & Verifier Precedents:** `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`), `verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`), `AeneasVerif/aeneas` (`d86aa34c75fd036ac139eb6e65da1cacc5492d0f`), `creusot-rs/creusot` (`601d97891bb0bc0b569686cc946ef4980560b5d8`), Reynolds (`10.1145/800194.805852`), and Pottier & Gauthier (`10.1145/964001.964009`).

**Scope Differentiation:** Prior corpus packages cover Charon/Aeneas external trait translation (`aeneas-types-traits-closures-and-external-models`, `charon-closures-traits-generics-and-item-provenance`), scalar-pair transmutes (`rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute`), LTO/CGU vtable symbols (`rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`, `cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts`), and surface orphan rules (`coherence-orphan-instances-and-module-system-compilation`). This report specifies `Type 0` shim-accurate closure defunctionalization, symbolic `VTable` + runtime `FreezeVisitor` unpacking, and coherence-keyed law registries under Anneal's Pass-1 ceiling.

---

## Findings

### 1. `rustc` Closure Capture Modes, Call Shims, and `Type 0` Defunctionalization

`Basis: source + derived`

In `rust-lang/rust` (`8144389c895d`), closures reach `Runtime(PostCleanup)` MIR already defunctionalized into aggregate environments and explicit call shims:

1. **Minimal Upvar Captures & `UniqueImmutable` (`ty/closure.rs` L21–108, L222, L374–453):**
   Closure environments pass at `CAPTURE_STRUCT_LOCAL = Local::arg(0)` (`_1`). RFC 2229 (`closure_min_captures_flattened`) captures minimal place paths `x.f.g` (`CapturedPlace`) under `ByValue`, `ByUse`, or `ByRef(Immutable | UniqueImmutable | Mutable)`. Notably, **`BorrowKind::UniqueImmutable`** (`L378–451`) handles closures mutating through an immutable binding holding `&mut T` (`let x: &mut i32 = &mut z; let c = || *x += 5;`): `to_mutbl_lossy` (`L441–452`) lowers the capture field in MIR to `&mut (&mut i32)`, granting exclusive Tree Borrows permission without requiring `let mut x`.
2. **`ExternAbi::RustCall` Untupling & ZST Receiver Skipping (`interpret/call.rs` L568–576, L856–876):**
   `Fn::call`, `FnMut::call_mut`, and `FnOnce::call_once` pass user arguments as a single tuple local under `ExternAbi::RustCall`; frame initialization (`call.rs` L856–872, `Call.lean` L99–107) untuples the final argument across callee locals via `fn_arg_project_field`. Non-capturing closures (`upvar_tys().is_empty()`, `call.rs` L568–576) coerce to bare `fn` pointers (`ClosureFnPointer`), skipping 1-ZST `args[0]`.
3. **The Four `make_shim` Bodies (`rustc_mir_transform/src/shim.rs` L32–74, L764–992):**
   - **`ShimKind::ClosureOnce` (`L63–73`, `L854–982`):** Adapts `Fn`/`FnMut` to `FnOnce` via `Adjustment::RefMut` across **5 basic blocks**: `BB0` borrows `_ref = &mut _1` and calls `FnMut::call_mut([_ref, _2], target=BB1, unwind=Cleanup(BB3))`; `BB1` runs `Drop(_1, target=BB2, unwind=Continue)` -> `BB2: Return`; `BB3` (`is_cleanup = true`) runs `Drop(_1, target=BB4, unwind=Terminate(InCleanup))` -> `BB4: UnwindResume`. Thus captured by-value upvars are dropped on **both** normal return and unwind, and double-panics abort via `InCleanup`!
   - **`ShimKind::FnPtr(def_id, fnty)` (`L40–54`, `L773–823`):** Dereferences `&fnty`/`&mut fnty` (or moves `fnty`), untuples `Args`, and emits an indirect `FnPtr` call.
   - **`ShimKind::Reify(def_id, _)` (`L60–62`):** Allocates an addressable function pointer (`FunctionPointers.lean` L60–90, salted by `Fin 32` when generic or inlinable).
   - **`ShimKind::VTable(def_id)` (`L36–39`, `L827–834`):** Rewrites by-value `fn(self, ...)` to `fn(self: *mut Self, ...)` (`Operand::Move(*_1)`) for `Box<dyn Trait>`.
4. **Reynolds / Pottier–Gauthier `Type 0` Encoding vs. Higher-Order Functions:**
   Translating closures to higher-order Lean functions (`AeneasVerif/aeneas` `d86aa34c75fd`) entangles backward-function arities when closures mutate both captured `&mut` upvars and `&mut` parameters, while encoding `CallerMemory`-mutating callbacks in `PFunctor` trees bumps universes to `Type 1` (rejected by `TrustedBoundary.lean` `L1335` `levelParams.isEmpty`). Following Reynolds (`10.1145/800194.805852`), Pottier–Gauthier (`10.1145/964001.964009`), and Creusot's `postcondition_mut`/`unnest` laws (`creusot` `601d97891bb0`), crate-local closures verify directly as concrete `ClosureEnv` product values, while open generic `F: FnMut` / `&mut dyn FnMut` callbacks use a `Type 0` relational `ClosureContract` carrying both `postReturn` and `postUnwind` (closing safe-Rust `catch_unwind(AssertUnwindSafe(...))` invariant-corruption holes!).

---

### 2. Symbolic `VTable` Allocation, Forgery Prevention, and Virtual Dispatch

`Basis: source + normative + derived`

In `ty/vtable.rs` (`L13–52`, `L84–156`) and `traits/vtable.rs` (`L18–308`), `prepare_vtable_segments` lays out slots `0..3` as `[MetadataDropInPlace, MetadataSize, MetadataAlign]`, followed by `Method(Instance)` (or `Vacant` for unsatisfiable `where`-clauses, `L278–281`) and `TraitVPtr(TraitRef)` pointers for 1-indirection multi-supertrait upcasting.

Crucially, `interpret/traits.rs` (`L38–103`) and `lean-miri` (`VTable.lean` L83–157, `VTableMachine.lean` L9–122) **never load raw size, alignment, or method addresses from memory bytes** (which `unsafe` code could spoof via a fake `[usize; 4]` array!):
- `VTableMachine.reserve` (`L98–115`) allocates a **zero-sized (`Size.ZERO`), immutable `GlobalKind.vtable` symbolic allocation** keyed by `(typeId, dynamicType, salt : Fin 32)`, disjoint from `FunctionPointers.Registry` (`ensureDisjointFromFunctions`, `L44–50`).
- `VTable.getPtrVTableTypeRead` (`VTable.lean` L83–93) enforces: (i) valid pointer provenance (dangling integers throw `ub "InvalidVTablePointer"`), (ii) `offset == Size.ZERO`, (iii) presence in `globalVTable`, and (iv) `checkForTypeRead` (`L72–82`), which strips auto-traits, sorts/deduplicates by `stableKey`, normalizes late-bound regions, and throws `ub "InvalidVTableTrait"` on mismatch.
- `VirtualCalls.resolveVirtual` (`VirtualCalls.lean` L109–166, porting `interpret/call.rs` L890–1007): (i) extracts `(data_ptr, vptr)` via `immPtrToMPlace` **without dereferencing `data_ptr`** (so calling `fn f(self: *const Self)` on null `*const dyn Trait` with a valid vtable is legal!), (ii) unwraps `DispatchFromDyn` smart pointers via `nonOneZstField` and locates custom DST tails via `structTailForCodegen`, (iii) checks `entries[slot]? == some (.method concreteInstance)` (faulting with UB on header/`vacant`/`traitVPtr` slots) and `assertConcrete` (`rebaseVirtualArgs`), and (iv) patches `args[0]` to a thin `*mut dynTy` immediate.

---

### 3. The `&dyn Trait` Interior-Mutability Trap and Runtime `FreezeVisitor` Unpacking

`Basis: source + derived`

Retagging `&T` under Tree Borrows grants `Frozen` (read-only; justifying CSE/load-forwarding across unknown calls) outside `UnsafeCell` bytes and `SharedReadWrite` (mutable via shared aliases; CSE unsound!) inside `UnsafeCell` bytes. Inspection of `miri/src/helpers.rs` (`L469–613`), `interpret/visitor.rs` (`L81–100`), and `Miri/TreeBorrows/FreezeVisitor.lean` (`L49–136`) reveals five distinct regimes:

| Pointee `T` of `&T` | Static `typeIsFreeze` | `FreezeVisitor.visitValue` (`FreezeVisitor.lean` L80–132) | Byte Permissions over `[0, size)` |
| :--- | :---: | :--- | :--- |
| `u64` / `(u32, u32)` | `true` | Fast-path `pure ()` (`L83`) + trailing 0-sized end flush (`L132`). | `[0, size) ↦ Frozen` |
| `Cell<u64>` | `false` | `isUnsafeCell` (`L81`) -> `wholeUnsafeCell`. | `[0, 8) ↦ SharedReadWrite` |
| `#[repr(C)] Mixed { hdr: u32, c: Cell<u32> }` | `false` | `Variants.Single` + `Fields.Arbitrary` walks `memoryOrder` (`L105–109`). | **`[0, 4) ↦ Frozen`**, **`[4, 8) ↦ SharedReadWrite`** |
| `Option<Cell<u32>>` / non-Freeze `union` | `false` | `Fields.Union` (`L85`) or `Variants.Multiple` (`L87`) **never reads discriminant**; marks whole span! | **`[0, size) ↦ SharedReadWrite`** (even if `None`!) |
| **`dyn Trait`** (`&dyn Counter`) | **`false`** | `isDynamic` (`L92`) calls **`unpackDynTrait place`** (`VTable.lean` L160–174) and **recurses on concrete `ty`**! | **Runtime-vtable-dependent** (`Frozen` if `u64`; split if `Mixed`)! |
| **`dyn Sub` (`Sub: zerocopy::Immutable`)** | `false` | Concrete `ty` implements object-safe `unsafe trait Immutable` (`zerocopy/src/lib.rs` L1729–1736), forbidding `UnsafeCell`! | Proven **`[0, size) ↦ Frozen`** via trait safety law! |

Consequently, `AdtDesc` and `SymVTableDesc` must store exact `unsafeCellRanges : List (Nat × Nat)` rather than a coarse boolean; open `&dyn Trait` values with unknown vtables must default conservatively to `SharedReadWrite` unless bounded by an audited immutability law such as `zerocopy::Immutable`.

---

### 4. Trait Coherence vs. Dictionary-Passing Soundness

`Basis: source + derived`

`rustc_trait_selection/src/traits/coherence.rs` (`L85–245`) enforces global non-overlap of `(TraitDefId, SelfTy, Args)` under `TypingMode::Coherence`. Standard and `unsafe` Rust libraries rely on coherence for soundness: `BTreeMap::insert` and `BTreeMap::get` must invoke the **identical** `<K as Ord>::cmp` implementation, and `zerocopy::IntoBytes` / `KnownLayout` (`zerocopy/src/lib.rs` L746–785, L6005) bind unique layout invariants to `Self`.

If `theory/` passes trait implementations as unconstrained Lean record parameters `(ord : OrdDict K)`, an adversarial proof can supply ascending `ord₁` to `insert` and descending `ord₂` to `get`! Keying implementations in a single crate-global `CoherentTraitRegistry` by `(traitId, selfTy, traitArgs)` guarantees `impl₁ = impl₂` by `rfl`, while cleanly separating:
- **`unsafe trait` Soundness Laws (`IntoBytesLaw`, `ImmutableLaw`):** Mandatory at `unsafe impl` sites (unproved impls surface on the **TCB Audit Log**).
- **Safe `trait` Spec Laws (`LawfulEq`, `LawfulOrd`, cf. Verus `vstd/laws_eq.rs` `obeys_eq`):** Never assumed for `unsafe` memory safety on unconstrained generic `K: Ord` (since safe callers can write non-transitive `Ord`), and required explicitly on **Stated Specifications** only for functional lookup postconditions.

---

### 5. Pass-1 Pure `prelude` Lean 4 Realization

`Basis: source + derived`

Every declaration below obeys `TrustedBoundary.lean`'s Pass-1 allowlists (`prelude`, locked `Init.*` only, `Type 0` monomorphic, zero banned operators/tactics/attributes):

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.Dispatch

abbrev UnsafeRange := Nat × Nat

def byteInUnsafeRanges (off : Nat) (ranges : List UnsafeRange) : Bool :=
  ranges.foldr
    (fun r acc => match r with | (lo, sz) => (Nat.ble lo off && Nat.blt off (lo + sz)) || acc)
    false

inductive SymVTableEntry where
  | dropInPlace : Option Nat → SymVTableEntry
  | size        : Nat → SymVTableEntry
  | alignLog2   : Nat → SymVTableEntry
  | vacant      : SymVTableEntry
  | method      : Nat → SymVTableEntry
  | traitVPtr   : Nat → SymVTableEntry

/-- Symbolic `.vtable` descriptor (`VTableMachine.lean:14-18` + `FreezeVisitor.lean:92-95`). -/
structure SymVTableDesc where
  allocId          : Nat
  concreteTyId     : Nat
  predicatesKey    : List Nat
  salt             : Nat
  sizeBytes        : Nat
  alignLog2        : Nat
  unsafeCellRanges : List UnsafeRange
  entries          : List SymVTableEntry

def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => Nat.beq x y && natListBeq xs ys
  | _, _ => false

/-- Checked symbolic vtable lookup enforcing `offset == 0` and predicate match (`VTable.lean:83-93`). -/
def lookupValidVTable (vtables : List SymVTableDesc)
    (vptrAllocId vptrOffset : Nat) (expectedPreds : List Nat) : Option SymVTableDesc :=
  if !Nat.beq vptrOffset 0 then none
  else
    vtables.foldr
      (fun vt acc =>
        if Nat.beq vt.allocId vptrAllocId then
          if natListBeq vt.predicatesKey expectedPreds then some vt else none
        else acc)
      none

/-- Virtual slot dispatch rejecting header, `vacant`, and `traitVPtr` entries (`VirtualCalls.lean:150`). -/
def resolveVirtualSlot (vtables : List SymVTableDesc)
    (vptrAllocId vptrOffset : Nat) (expectedPreds : List Nat) (slot : Nat) : Option (Nat × Nat) :=
  match lookupValidVTable vtables vptrAllocId vptrOffset expectedPreds with
  | none => none
  | some vt =>
    match getElem? vt.entries slot with
    | some (.method fnDefId) => some (fnDefId, vt.concreteTyId)
    | _ => none

/-- Dynamic `&dyn Trait` byte-level `Freeze` lookup via concrete vtable unpacking. -/
def dynByteIsFrozen (vtables : List SymVTableDesc)
    (vptrAllocId vptrOffset : Nat) (expectedPreds : List Nat) (off : Nat) : Option Bool :=
  match lookupValidVTable vtables vptrAllocId vptrOffset expectedPreds with
  | none => none
  | some vt =>
    if Nat.blt off vt.sizeBytes then some (!byteInUnsafeRanges off vt.unsafeCellRanges) else none

/-- Universe-monomorphic (`Type 0`) contract covering `Fn`, `FnMut`, `FnOnce`, and `ClosureOnce` unwind drop. -/
structure ClosureContract (Env Arg Out : Type) where
  inv        : Env → Prop
  unnest     : Env → Env → Prop
  postReturn : Env → Arg → Out → Env → Prop
  postUnwind : Env → Arg → Env → Prop
  dropEnv    : Env → Prop

abbrev TraitKey := Nat × Nat

def lookupCoherentImpl (reg : List (TraitKey × Nat)) (k : TraitKey) : Option Nat :=
  reg.foldr (fun e acc => if Nat.beq e.1.1 k.1 && Nat.beq e.1.2 k.2 then some e.2 else acc) none

theorem coherent_impl_unique (reg : List (TraitKey × Nat)) (k : TraitKey) (i1 i2 : Nat)
    (h1 : lookupCoherentImpl reg k = some i1)
    (h2 : lookupCoherentImpl reg k = some i2) : i1 = i2 := by
  rw [h1] at h2
  injection h2

end Anneal.Dispatch
```

---

### 6. Evaluation Across the Anneal Untrusted-Theory Architecture Rubric

`Basis: derived + source`

| Criterion | Grade | Assessment |
| :--- | :---: | :--- |
| **`(T1)` 0-TCB Bridge** | **Minimal `Trusted.*` Hook (`G` / `S`)** | Known closures are already structs + direct `Call`s in `PostCleanup` MIR (needing only `Drop` + `UnwindAction.terminate`). Dynamic dispatch adds `Program.vtables` + `CallIndirect` in `Trusted.MirSemantics`, Pass-2-certified against `vendor/lean-miri`. `ClosureContract` and `CoherentTraitRegistry` stay **100% in `theory/`**. |
| **`(P1)` Human Spec Auditability** | **Strong (`S`)** | Separates TCB-logged `unsafe trait` safety laws from spec-only `LawfulOrd` axioms so proofs never assume safe caller `Ord` impls are bug-free for memory safety. |
| **`(P2)` Authoring & Day-2 Locality** | **Strong (`S`)** | New `impl Trait for T` items verify against the trait contract without touching existing `&dyn Trait` caller proofs. |
| **`(P3)` Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **Strong (`S`)** | First-order `Type 0` `ClosureEnv` avoids higher-order continuation blowups, `HEq`, and `Type 1` `PFunctor` trees; `coherent_impl_unique` closes by `injection`. |
| **`(P4)` Heterogeneous Composability** | **Strong (`S`)** | Unifies `&dyn Trait` wrapping `Cell<u32>`, `ClosureOnce` 5-block unwind drops, `UniqueImmutable` captures, and `zerocopy::Immutable` object-safe bounds. |
| **`(P5)` Failure Legibility** | **Moderate–Strong (`M–S`)** | Pinpoints `InvalidVTablePointer`, `InvalidVTableTrait`, non-method `Vacant`/`TraitVPtr` calls, and unsound CSE across `!Freeze` bytes. |
| **`(C1–C2)` Conceptual Minimality** | **Locally Minimal (`S`)** | `postUnwind` cannot collapse into `postReturn` (`catch_unwind` safe-Rust exploit); `unsafeCellRanges` on vtables cannot collapse into static `MirTy` (`dyn Trait` erases `Freeze`); `CoherentTraitRegistry` cannot collapse into free dictionary arguments (`BTreeMap` incoherence). |

---

## Boundaries

1. **Auto-Trait Forgery in `check_vtable_for_type` (`known not to apply`):** `interpret/traits.rs` (`L76–78`, `FIXME`) and `VTable.lean` (`L68`) strip auto-traits (`!·.autoTrait`), so transmuting `*const dyn Trait` (`!Send`) to `*const (dyn Trait + Send)` is **known not to apply** to `InvalidVTableTrait` checks unless `rustc-capture` retains auto-trait IDs in `predicatesKey`.
2. **Dynamic Foreign `FnVal::Other` in VTables (`unsupported`):** `FunctionPointers.lean` (`L206–209`) throws `StepError.unsupported` if a vtable slot references a non-`CallInstance` machine extra function (`dlsym`), failing closed in `WellFormed`.
3. **Raw VTable / Function-Pointer Address Equality (`known not to apply`):** Miri's `Fin 32` allocation salt (`FunctionPointers.lean` L60–67, `VTableMachine.lean` L98–115) models cross-CGU duplication; `std::ptr::eq` on two `&dyn Trait` vtables for the same `T` is **known not to apply**.
4. **Async Coroutine-Closures (`ConstructCoroutineInClosure`) (`not examined`):** Multi-poll suspension and cancellation-drop verification of `AsyncFnOnce` child futures (`shim.rs` L75–106, `closure.rs` L455–503) was **not examined** in full detail here.
5. **Lifetime-Dependent Trait Specialization (`unknown`):** Extending `CoherentTraitRegistry` to unstable `#![feature(specialization)]` with region-sensitive dispatch remains **unknown** and must fail closed in `rustc-capture`.

---

## Evidence

All evidence was inspected on `2026-11-20` at immutable revisions:

1. **`rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`):** `compiler/rustc_mir_transform/src/shim.rs` (`L32–177`, `L764–992`); `compiler/rustc_middle/src/ty/{closure.rs, vtable.rs}` (`closure.rs` L21–109, L374–520; `vtable.rs` L13–156); `compiler/rustc_trait_selection/src/traits/{vtable.rs, coherence.rs}` (`vtable.rs` L18–447; `coherence.rs` L85–250); `compiler/rustc_const_eval/src/interpret/{traits.rs, call.rs, visitor.rs}` (`traits.rs` L19–128; `call.rs` L568–576, L856–1007; `visitor.rs` L81–100).
2. **`rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):** `src/helpers.rs` (`L469–613`, `visit_freeze_sensitive` & `UnsafeCellVisitor`).
3. **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** `Miri/Interpreter/{VTable,VTableMachine,VirtualCalls,FunctionPointers,Call}.lean`; `Miri/TreeBorrows/{FreezeVisitor,FreezeMap}.lean`.
4. **Ecosystem & Literature:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `TrustedBoundary.lean` L442–596, L1316–1366); `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`, `zerocopy/src/lib.rs` L746–785, L1729–1736, L6005); `verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`, `source/vstd/laws_eq.rs` L14–58); `AeneasVerif/aeneas` (`d86aa34c75fd036ac139eb6e65da1cacc5492d0f`); `creusot-rs/creusot` (`601d97891bb0bc0b569686cc946ef4980560b5d8`); Reynolds (`10.1145/800194.805852`, `10.1023/A:1010027404223`); Pottier & Gauthier (`10.1145/964001.964009`, `10.1007/s10990-006-8611-7`).

---

## Revalidation

1. **Diff `rustc` Shims & Closure Captures (<10s):** Diff `shim.rs` (`make_shim`, `build_call_shim`) and `ty/closure.rs` (`UpvarCapture`, `BorrowKind::UniqueImmutable`) against `8144389c895da997dbdecaa635e41d6a50be6ffd` to verify the 5-block `ClosureOnce` cleanup-drop ladder and `to_mutbl_lossy` lowering.
2. **Diff `lean-miri` VTable & `FreezeVisitor` (<10s):** Diff `Miri/Interpreter/{VTable,VTableMachine,VirtualCalls}.lean` and `Miri/TreeBorrows/FreezeVisitor.lean` against `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` to check `!·.autoTrait` filtering (`VTable.lean` L68) and `isDynamic -> unpackDynTrait` recursion (`FreezeVisitor.lean` L92–95).
3. **Pass-1 Syntax & Kernel Replay Probe (<2s):** Run `anneal-audit` `"preflight"` and `lean -DElab.async=false -Ddebug.skipKernelTC=false` on the `Anneal.Dispatch` snippet in **Findings §5** against `foundation-lock.json` (`5045d0056413266e57c625dcd7c365b10e377c52`) to confirm 0 syntax violations and `coherent_impl_unique` replay.
