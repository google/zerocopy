# Hybrid Functional Lifting and Separation Logic for Unsafe Rust and Interior Mutability

## Summary

Pure functional borrow-erasure verifiers—Aeneas, Creusot's prophetic core, and Anneal's `PureLift`—avoid heap addresses and separation-logic framing on safe `Freeze` Rust by translating `&mut T` and `&T` borrows into pure values paired with backward update functions or final prophecies. That representation breaks whenever code converts references to raw pointers, manipulates uninitialized or padded bytes, or mutates data through shared aliases inside `core::cell::UnsafeCell<T>`.

Across extant Rust verifiers and mechanized prototypes, four architectures extend pure functional reasoning to unsafe Rust and interior mutability:

1. **Scoped spatial heaplet pinning inside a pure loan graph (`Anneal.PureLift.SpatialPin`)**: Pure locals and `Freeze` borrows remain in a value-level permission trie (`PermTree`), while selected loans export into a disjoint spatial zone (`LoanPhase.spatialPinned`). Supporting general unsafe Rust and interior mutability requires adding partial-field `Freeze`/`UnsafeCell` splitting, raw-to-safe pure loan checkout (`as_mut` / `as_shr`) with scoped return authority, affine `PartialCommMonoid` (`PCM`) framing, and a 4-law Galois-connection byte codec tolerating uninitialized padding.
2. **Effectful backward continuations with view-indexed byte separation logic (Aeneas stateful lifetimes + `SepLogic`)**: Annotating raw-pointer bridge operations (`Ptr::from_mut`, `Ptr::as_mut`) with liveness-guided lifetime tiers (`short`, `default`, `long`) replaces pure `T -> T` backward functions with monadic `Result`-returning continuations backed by an upward-closed first-order `IProp` logic whose resources split logical view indices rather than physical addresses.
3. **Ghost linear permission tokens (`Verus` `PPtr`/`PCell`/`Tracked`, `Creusot` `Perm<C>`/`PCell`/`Ghost`)**: Physical containers (`*const T`, `PCell<T>`) are separated from zero-sized ghost ownership tokens (`Tracked<PointsTo<T>>`, `Ghost<Perm<PCell<T>>>`), keeping ordinary variables pure while threading linear tokens (or packaging them inside `InvCell` / `PredCell` invariants) at pointer and cell accesses.
4. **Foundational separation logic with syntax-directed pure unfolding (`RefinedRust` / `Lithium`)**: All safe and unsafe MIR executes inside step-indexed Iris separation logic in Rocq, while ownership refinement types and Lithium's deterministic subsumption engine automatically reduce safe owned/borrowed code to pure Rocq obligations.

Soundly bridging any hybrid state to operational post-cleanup MIR and Tree Borrows requires enforcing three boundaries verified in `rust-lang/miri`: (a) per-byte `Freeze` splitting (`InsideFrozen` vs. `InsideUnsafeCell` vs. `Outside`), (b) function-entry `StrongProtector` promotion forcing `ReservedFrz` even on `&mut UnsafeCell<T>` and `Box<UnsafeCell<T>>`, and (c) frame-quantified weakest-precondition adequacy (`sepWpState`) preventing duplicate authority between pure loans and spatial fragments.

## Applicability

This report compares the eight durable subjects in `REPORT.json`: Anneal (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), Aeneas (`AeneasVerif/aeneas` at `2e3d4488280bb8a95411db81019a7854a784861f`), Creusot (`creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`), Verus (`verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`), Miri's Tree Borrows interpreter (`rust-lang/miri` at `5a2649e9c3bfbada72665448bddf8b54021bec2e`), the Rust compiler and standard library (`rust-lang/rust` at `ec65cd52bba13d491ff65c9d218b39753755c84a`), RefinedRust (DOI `10.1145/3656422`), and `tiny-iris` (`JoJoDeveloping/tiny-iris` at `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`).

Version and branch scope qualifications:

- **Anneal (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**: Covers `theory/Anneal/PureLift/{Lens,PermTree,LoanGraph,SpatialPin,Plan,BlockCfg,Adapter,MirBridge}.lean` and `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`. Under `trusted/audit/TrustedBoundary.lean`, `theory/` is restricted to Lean `v4.34.1` with `prelude` + `Init.*` only, standard axioms `{propext, Quot.sound, Classical.choice}`, and a closed syntax allowlist forbidding `Std.*`, `Mathlib`, `Lean.*` meta tactics (`elab`, `macro_rules`, `syntax`), `omega`, `grind`, `native_decide`, `coinductive`, `partial_fixpoint`, and `_unsafe_rec`.
- **Aeneas (`2e3d4488280bb8a95411db81019a7854a784861f`) vs. unmerged upstream PRs**: Published `AeneasVerif/aeneas` `main` performs pure functional borrow erasure without raw-pointer dereferencing or byte-heap separation logic (`backends/lean/Aeneas/Std/Core/Ptr.lean`). Section 3 also analyzes four public, **unmerged** `AeneasVerif/aeneas` pull requests: PR `#1447` (`2a1dd75567517e078f90b1df746af7373fe24cbc`, Galois-connection layouts), PR `#1497` (`d17ca83fc07d712d1785f650840cb2073c259e69`, byte heap and `ClosedViews`), PR `#1537` (`5c28fe8def8db99041d22503175591ba1fa47915`, `#[verify::stateful_lifetime]`), and PR `#1551` (`1d8f9aa0121faca8ff113c1b9b742b333e3e1519`, `IProp` and `SepAC`). Claims about those unmerged prototypes do not apply to `AeneasVerif/aeneas` `main` unless merged.
- **Creusot (`601d97891bb0bc0b569686cc946ef4980560b5d8`)**: Historical `PermCell<T>`, `PtrOwn<T>`, and `GhostBox<T>` are unified in current `creusot-std` (and Golfouse, Guéneau, and Jourdan, CPP 2026, DOI `10.1145/3779031.3779086`) as `Perm<C: ?Sized + PermTarget>`, `PCell<T>`, `PredCell<T>`, `Ghost<T>`, and `Perm<*const T>`.
- **Verus (`0dab219272ac2353320bd177ebb3929453b90a9e`)**: `vstd::cell::PCell` and `vstd::cell::InvCell` (`source/vstd/cell.rs`) are deprecated in favor of `vstd::cell::pcell::PCell<T>` (`ManuallyDrop<UnsafeCell<T>>`), `vstd::cell::pcell_maybe_uninit::PCell<T>`, and `vstd::cell::invcell::InvCell<T, Pred>`.
- **Corpus cross-references**: Complements `hybrid-functional-spatial-and-plan-guided-shallow-translation-in-lean4`, `aeneas-borrows-symbolic-ownership-and-resource-semantics`, `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses`, and `tree-borrows-two-stage-protector-release-and-reborrow-contracts`.

## Findings

### 1. Breakdown of Pure Functional Erasure at Raw Pointers and `UnsafeCell`

`Basis: normative + source + derived`

Pure functional borrow erasure relies on two properties restricted to safe `Freeze` types (`rust-lang/rust` `compiler/rustc_middle/src/ty/util.rs:1177–1208`, where `Ty::is_freeze` holds iff no `UnsafeCell` appears outside pointer/reference indirection): (1) `&'a T` referents are immutable for `'a`, erasing to a pure value `T`, and (2) `&'a mut T` mutations form a static tree summarized at region end by a pure backward function `T -> T` or final prophecy `^x : T`. Three patterns break this model:

- **Safe-to-raw-to-safe lifetime erasure (`&mut T -> *mut T -> &mut T`)**: `from_mut<'a>(r: &'a mut T) -> *mut T` returns a lifetime-free raw pointer. Standard borrow erasure sees no output reference using `'a` and eagerly ends `'a` upon return (`T -> (*mut T × T)`), reclaiming `T` *before* any raw write through `*mut T` occurs. Conversely, `as_mut<'a>(p: *mut T) -> &'a mut T` lacks a pure local parent, so a pure backward function `T -> Unit` drops mutations instead of writing to memory, and nothing forces one `as_mut` borrow to end before a second `as_mut` dereference.
- **Duplicate-call / CSE unsoundness on effectful continuations**: Deduplicating or dead-code-eliminating identical calls to a backward continuation is sound for pure `T -> T` functions, but becomes unsound once continuations mutate heap cells or retire borrow exposures (`simplify_duplicate_calls` had to be disabled for effectful continuations in Aeneas PR `#1537`, `src/pure/PureMicroPassesGeneral.ml`).
- **Aliased shared `!Freeze` mutation (`&Cell<T>`, `&[Cell<u8>]`, `&RefCell<T>`)**: When `c1, c2 : &Cell<u32>` alias (or slice elements alias via `Cell::<[u8]>::as_slice_of_cells`, `library/core/src/cell.rs:737–740`), caching pure values `v1, v2 : u32` predicts `c1.set(7); c2.get() == v2` instead of `7`. Cyclic/bipartite shared aliasing admits arbitrarily interleaved writes that no static tree of pure backward functions or single final prophecy `^c` can represent.

### 2. Hybrid Pure-Loan and Spatial-Heaplet Pinning in `PureLift`

`Basis: source + derived`

In `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`theory/Anneal/PureLift/{PermTree,LoanGraph,SpatialPin}.lean`), `SymState Val` combines a `List.foldr`-computable permission trie (`PermTree`) and pure loan graph (`loans : List (LoanEntry Val)`) with a spatial heaplet (`spatial : List (SpatialBlock Val)`):

```lean
-- joshlf/anneal @ c131b320eeeb..., theory/Anneal/PureLift/LoanGraph.lean:537-550
structure SpatialCodec (Val : Type) where
  codecId : Nat
  encode : Val → List (CellVal Val)
  decode : List (CellVal Val) → Option Val
  decode_encode : ∀ v : Val, decode (encode v) = some v

inductive LoanPhase (Val : Type) where
  | activeShared : LoanPhase Val
  | activeMut : LoanPhase Val
  | spatialPinned (bid : BlockId) (codec : SpatialCodec Val) : LoanPhase Val
  | ended : LoanPhase Val
```

`freezeToSpatialInState` (`SpatialPin.lean:206–235`) verifies `e.phase.isActiveMut`, `isUnborrowed e.cell.perm`, and absence of active child loan/region edges, encodes `e.cell.val` via `codec`, rejects `.uninit` cells, sets `.spatialPinned bid codec` (preserving `e.target : BackTarget Val`), and appends `⟨bid, lid, .readWrite, bid, 0, cells⟩` to `st.spatial`. `mutateSpatialInState` (lines 240–247) updates `bid` in place without disturbing pure loans in `st.loans`. `reabsorbFromSpatialInState` (lines 254–294) decodes using the original `pinnedCodec` bound inside `.spatialPinned` (defeating colliding `codecId` attacks, `spatial_roundtrip_and_codec_binding_test`, lines 330–354), checks `!hasUninitCell blk.cells` and `replaceableVal alg st.loans e.cell.val v'` (blocking fabricated borrow handles, lines 283, 560–579), and restores `.activeMut`.

Five exact architectural gaps separate baseline `SpatialPin` (`c131b320eeeb...`) from general unsafe Rust and interior mutability, each admitting an `Init.*`-compliant resolution:

1. **Exclusive-only whole-loan pinning vs. partial-field `Freeze`/`UnsafeCell` splitting**: `freezeToSpatialInState` (line 214) rejects `.activeShared` loans (line 430) and pins entire loans. For `struct Packet { hdr: u32, hits: Cell<u32> }`, adding a `SubPerm.spatialExported (bid : BlockId)` leaf to `PermTree.split` (`PermTree.lean:57`) at `!Freeze` sub-paths `p_im` keeps disjoint `Freeze` paths `p_frz` (`subPathOverlaps p_frz p_im = false`, line 124) in zero-overhead pure lens evaluation while routing `p_im` accesses to spatial block `bid`.
2. **Order-sensitive non-affine `SpatialProp` vs. upward-closed `IProp` + reflective `SepTree`**: `SpatialProp Val := List (SpatialBlock Val) -> Prop` (`SpatialPin.lean:63–90`) uses list append `blocks = h1 ++ h2`, requiring manual reassociation lemmas while `TrustedBoundary.lean` bans `Lean.Meta` framing tactics. Upgrading to an upward-closed `IProp` over a first-order `PartialCommMonoid` with a reflective `SepTree` normalizer (`bagPerm src.atoms (req.atoms ++ frame.atoms) = true`) discharges arbitrary AC frame splits in one kernel `rfl`/`decide` step without metaprogramming.
3. **Missing raw-to-safe checkout (`checkoutFromSpatial` / `writebackToSpatial`)**: Adding `BackTargetStep.spatialSlice` lets a pinned `SpatialBlock` temporarily check out a pure `&mut U` / `&U` loan into `st.loans` (incrementing `activeSubSplits`) and write back on loan end, governed by a transitive `ClosedSpatialScopes st0 st1` relation so nested checkouts preserve outer reabsorption authority.
4. **Hard `hasUninitCell` rejection vs. 4-law Galois-connection codecs**: `SpatialPin` (lines 220, 276, 358–374) rejects `.uninit` cells unconditionally, blocking `MaybeUninit<T>`, unions, and structs with alignment padding. Replacing 1-law `SpatialCodec` with the 4-law MiniRust Galois connection over `AbstractByte := uninit | init UInt8` (`uninit <= b`: `decode_valid`, `decode_mono`, `decode_encode`, and `encode_decode_le : decode bs = some v -> leDefined (encode v) bs`, as in `AeneasVerif/aeneas` PR `#1447`) allows `encode` to emit `.uninit` at padding indices and `reabsorb` to rely on `pinnedCodec.decode blk.cells = some v'` directly. Quantifying universally over `∀ l : Layout ty, l.Valid -> ...` avoids `Classical.choice` while keeping `#[repr(Rust)]` field offsets abstract.
5. **By-value, empty-memory `MirBridge` barrier**: `MirArgsMatch` (`MirBridge.lean:1344–1384`) enforces `mirAllByValParams params = true`, `q.callerMem = ⟨[]⟩`, and `out.mutFinals = []`. Supporting reference and raw-pointer parameters requires coupling `(SymState, IProp)` to non-empty `q.callerMem` via a frame-quantified `sepWpState` (Section 7).

### 3. Stateful Lifetimes and View-Indexed Byte Separation Logic in Aeneas

`Basis: source + documentation + derived`

The four unmerged `AeneasVerif/aeneas` prototypes (`#1537`, `#1551`, `#1497`, `#1447`) extend Aeneas's translation pipeline with monadic backward continuations and a step-index-free byte-heap separation logic:

- **Effectful backward continuations and 3-tier liveness scheduling (`#1537` at `5c28fe8def8db99041d22503175591ba1fa47915`)**: `tests/src/stateful-lifetime.rs:27–71` and `tests/lean/StatefulLifetime.lean:59–80` annotate pointer-bridge methods with `#[verify::stateful_lifetime(short | default | long)]`, setting `is_effectful : bool` (`SymbolicToPureCore.ml`) to emit monadic `Result` backward thunks:
  ```lean
  -- AeneasVerif/aeneas PR #1537 @ 5c28fe8def..., tests/lean/StatefulLifetime.lean:59-75
  axiom Ptr.as_shr   {T : Type _} : Ptr T → Result (T × (Result Unit))
  axiom Ptr.as_mut   {T : Type _} : Ptr T → Result (T × (T → Result Unit))
  axiom Ptr.from_mut {T : Type _} : T → Result ((Ptr T) × (Result T))
  axiom Ptr.from_shr {T : Type _} : T → Result ((Ptr T) × (Result Unit))
  ```
  `long` abstractions (`from_mut`, `from_shr`) stay alive across control-flow joins via two-step join retry in `InterpJoin.ml` until the source local is accessed or returned; `short` abstractions (`as_mut`, `as_shr`) end as early as possible via backward local-variable liveness in `InterpLiveness.ml` so sequential `ptr.as_mut()` calls do not conflict. Unlike `PureLift` (where scheduling lives in untrusted `theory/` plans checked against `Trusted.MirSemantics`), Aeneas places `InterpLiveness.ml` and `InterpJoin.ml` inside its OCaml translation TCB.
- **View-indexed `Resource`, integer sharing depth, and `ClosedViews` (`#1551` at `1d8f9aa0121faca8ff113c1b9b742b333e3e1519` and `#1497` at `d17ca83fc07d712d1785f650840cb2073c259e69`)**:
  1. *Affine upward-closed `IProp`* (`SepLogic/IProp.lean:17–114`, matching `tiny-iris` `theories/heapprop.v:7–10`): `IProp` pairs `holds : Fragment -> Prop` with `up_closed : Subheap h h' -> holds h -> holds h'`, dropping unused spatial assertions affinely (`emp.holds _ := True`).
  2. *Logical view separation* (`SepLogic/Resource.lean:19–63`): `Resource` has `.cell base index bptr value` and `.cleanup base size bptr owned`, with `Compatible a b := a.base ≠ b.base ∨ a.key ≠ b.key`. Distinct views (`i ≠ j`) are separable by `∗` even when overlapping physically (`a.val + x = b.val + y`); `Heap.Inv` enforces `Cell.compatible` across overlapping active views (`Holds.overlapCompatible`, line 58), using `Cell := .shared (depth : Nat) Byte | .borrowed` (`depth = 0` exclusive, `depth = d + 1` shared) without rational fractions.
  3. *Scoped return authority* (`Std/Heap/ScopedView.lean:48–179`, `Std/WPDef.lean:50–64`): Separating `block.active` (view status) from `root.alive` (allocation lifetime, `Model.lean:48–53`) prevents ending a parent borrow while a child view remains active. `ClosedViews s₀ s₁` preserves `returnShape` on IDs `< s₀.next`, requires `blk.active = false` on all new IDs `≥ s₀.next`, and leaves byte contents unrestricted—allowing `RootReturn.after_closed_views` (line 111) to preserve outer return authority across arbitrarily nested scopes.
  4. *Unified `iwp` and `SepAC.Tree`* (`Std/WPDef.lean:76–95`, `Tactic/Normalize.lean:18–64`): Frame-quantified `iwp` recovers pure specs via `spec m p := ispec emp m (fun v => ⌜p v⌝)`, while `SepAC.Tree.denote_eq` proves AC equivalence via `l.atoms.isPerm r.atoms = true`.

### 4. Ghost Permission-Token Architectures: Creusot and Verus

`Basis: source + documentation + derived`

Creusot (`601d97891bb0bc0b569686cc946ef4980560b5d8`) and Verus (`0dab219272ac2353320bd177ebb3929453b90a9e`) represent points-to authority as zero-sized ghost Rust types, keeping ordinary values in pure first-order SMT logic:

- **Creusot `Perm<C>`, `PCell<T>`, and `PredCell<T>`** (`creusot-std/src/ghost/perm.rs:9–178`, `cell/pcell.rs:22–228`, `cell/predcell.rs:10–115`):
  - `Perm<C: ?Sized + PermTarget>` tracks `perm.ward() -> &C` and `perm.val() -> C::Value` for both `PCell<T>` and `*const T`.
  - Three soundness mechanisms govern `Perm<C>`: (i) unsized treatment prevents `mem::replace` from swapping a split permission out of a shorter-lived `&mut Perm<*const [T]>` (`perm.rs:36–39`); (ii) constructors carry `#[check(terminates)]` rather than pure `#[check(ghost)]` (`perm.rs:56–70`) so diverging ghost code cannot exhaust the finite `usize` address space and falsify `Perm::disjoint_lemma` (lines 150–155, which also exempts ZSTs at lines 112–114); and (iii) `PCell<T>` sets `type Objectiveness = NotObjective` (`pcell.rs:27–32`) to prevent unsynchronized concurrent sharing of `Perm<PCell<T>>` even though `PCell<T>` itself is `Send + Sync`.
  - Because Creusot uses prophecies, `PCell::from_mut(t: &mut T) -> (&PCell<T>, Ghost<&mut Perm<PCell<T>>>)` (`pcell.rs:201`) needs **no** liveness pass: `ensures(^t == *(^result.1).val_unsized())` directly equates `t`'s final value with the permission's final value. When linear token threading is impractical (aliased `&Cell<T>`), `PredCell<T>` (`predcell.rs:12–114`) attaches an immutable predicate `Mapping<T, bool>` supporting `get`, `set`, `swap`, and `as_slice_of_cells`.
- **Verus `vstd::cell::pcell::PCell`, `PPtr`, and `InvCell`** (`source/vstd/cell/pcell.rs:44–243`, `simple_pptr.rs:153–329`, `cell/invcell.rs:71–167`):
  - `PCell<T>` wraps `ManuallyDrop<UnsafeCell<T>>` (`pcell.rs:83–87`): dropping `PCell<T>` **must not** run `T::drop` unless `Tracked<PointsTo<T>>` is consumed via `into_inner` (lines 44–49, 184–196), preventing dangling borrows or uninitialized drops.
  - Because `PCell<T>` is movable, `pcell.id() : CellId` is move-invariant (`PointsTo::is_exclusive`, line 118), whereas `PPtr<V>` (`simple_pptr.rs:153–166`) is a `Copy` `usize` address whose `PointsTo<V>` bundles `(raw_ptr::PointsTo<V>, IsExposed, Option<Dealloc>)` and restricts `PointsTo::is_disjoint` to `size_of::<V>() != 0 && size_of::<S>() != 0` (lines 303–314) because ZST pointers may lie inside live allocations.
  - `InvCell<T, Pred>` (`invcell.rs:72–152`) stores `Tracked<LocalInvariant<(Pred, CellId), PointsTo<T>, InvCellPred>>` inside the cell, opening and closing it around single `pcell.borrow` / `pcell.replace` steps for aliased `&InvCell` callers.

### 5. Full Separation Logic with Pure Unfolding: RefinedRust and Lithium

`Basis: documentation + derived`

RefinedRust (Gäher et al., PLDI 2024, DOI `10.1145/3656422`) embeds *all* safe and unsafe MIR into foundational Iris separation logic in Rocq and recovers pure proof obligations through ownership refinement types (`l ◁ₗ (r @ T)`) and Lithium's syntax-directed subsumption engine (Sammler et al., PLDI 2021, DOI `10.1145/3453483.3454036`) over RustBelt's lifetime logic `[α]` (Jung et al., POPL 2018, DOI `10.1145/3158154`). Safe borrows cancel deterministically into pure Rocq side conditions without exposing Iris `∗` or `▷`, while unsafe code (`Vec`, raw pointers, `UnsafeCell`) drops seamlessly into Iris lemmas with zero `freeze`/`reabsorb` conversion boundary. The cost is universal step-indexing (`iProp Σ`, COFEs, `▷`), heavy elaborator automation incompatible with minimal tactic-free kernel boundaries (`TrustedBoundary.lean`), and monadic/WP specifications rather than pure `Init.*` functions on safe code.

### 6. Comparative Architecture Matrix

`Basis: source + documentation + derived`

| Dimension | `PureLift` + Extended `SpatialPin` | Aeneas `stateful_lifetime` + `SepLogic` | Ghost Permission Tokens (`Verus` / `Creusot`) | Full Iris SL + Pure Unfolding (`RefinedRust`) |
| :--- | :--- | :--- | :--- | :--- |
| **Safe `Freeze` representation** | Pure `PermTree` + `BackTarget` fold; zero heap state | Pure Lean functions (`T -> Result U`); `spec` = `ispec emp` | Pure SMT/Why3 values (+ prophecies `^x` in Creusot) | Iris `iProp Σ` types reduced to pure Rocq VCs by Lithium |
| **Safe -> raw bridge (`&mut T -> *mut T`)** | `freezeToSpatial` (`.spatialPinned`) + `reabsorbFromSpatial` | `#[verify::stateful_lifetime(long)]` (`Result (Ptr T × Result T)`) | `Perm::from_mut` (`^t == *(^perm).val()`); `PPtr` | Native pointer identity (`&mut T` already denotes `l` + `[α]`) |
| **Raw -> safe deref (`&mut *p`)** | Needs `checkoutFromSpatial` + `writebackToSpatial` + `ClosedSpatialScopes` | `#[verify::stateful_lifetime(short)]` + OCaml `InterpLiveness.ml` | `Perm::as_mut(p, Ghost(&mut perm))` / `PCell::borrow_mut` | Native place dereference under lifetime token `[α]` |
| **Aliased interior mutability** | Needs `.activeShared` spatial export or ghost/invariant PCM | View-indexed `Resource.cell` + heap overlap compatibility | Exact via `Ghost<&mut Perm>` / `Tracked<&mut PointsTo>`; invariant via `PredCell` / `InvCell` | Iris invariants (`inv N P`), custom CMRAs, RustBelt `Cell`/`RefCell` |
| **Mixed `Freeze` + `UnsafeCell` `&S`** | Partial-field `PermTree.split`: `Freeze` pure, `UnsafeCell` spatial | Per-field view exposure or whole-struct heap placement | Pure fields stay pure; cell field uses `PCell<U>` / `InvCell<U>` | Structural product refinement splits `Freeze` vs. `UnsafeCell` fields |
| **Padding, `MaybeUninit`, provenance** | Baseline rejects `.uninit`; fixed by 4-law Galois `LayoutCodec` | `#1447` 4-law Galois `Layout` + `#1497` 8-lane `Byte.pointer` | `pcell_maybe_uninit::PCell`, `PointsToRaw` + `IsExposed` + `Dealloc` | Byte-level `uninit` array refinements + provenance in Iris heap |
| **TCB & step-indexing footprint** | `Init.*` `Type 0` Lean 4, 0 step-indexing, 0 SMT, untrusted `theory/` | OCaml Charon+Aeneas in TCB; `Type 0` `IProp` + ITree `DWP` | VIR/Why3 + Z3/CVC5 in TCB; 0 step-indexing | Rocq kernel TCB, but requires full step-indexed `iProp Σ` (`▷`) |

### 7. Formal Soundness Bridges to Post-Cleanup MIR and Tree Borrows

`Basis: source + normative + derived`

Bridging a hybrid `(SymState, IProp)` state to `Trusted.MirSemantics` (`joshlf/anneal`) and Tree Borrows (`rust-lang/miri` at `5a2649e9c3bfbada72665448bddf8b54021bec2e`) rests on three formal mechanisms:

1. **Frame-quantified operational WP (`sepWpState`) and adequacy**:
   Following `tiny-iris` (`theories/adequacy.v:9–46`) and `Aeneas/Std/WPDef.lean:64–83`, fuel-bounded operational WP over `Trusted.MirSemantics.State` needs zero coinduction or step-indexing:
   ```lean
   def sepWpState (p : Program) (fuel : Nat) (P : IProp) (Q : TerminalOut → IProp) : Prop :=
     ∀ (F : IProp) (s : State),
       Realizes (sep P F) s →
       Anneal.MirWp.wpOutcomeState p fuel s
         (fun out => Realizes (sep (Q out) F) (terminalStateOf out))
   ```
   `Realizes` partitions concrete MIR bytes disjointly between active non-pinned pure loans in `SymState` and spatial `IProp` resources; `.spatialPinned bid codec` transfers byte authority from the pure loan to `IProp` while retaining `BackTarget` metadata. Instantiating `F := emp` discharges closed-program `wpOutcomeState` and transfers to `lean-miri` via `CorrespondenceClaim`.
2. **Per-byte `Freeze` splitting in Tree Borrows (`InsideFrozen`, `InsideUnsafeCell`, `Outside`)**:
   In `rust-lang/miri` `src/borrow_tracker/tree_borrows/mod.rs:110–221, 329–364` and `perms.rs:10–53`, retagging under `precise_interior_mut = true` runs `visit_freeze_sensitive` (`mod.rs:355`): non-`UnsafeCell` bytes get `freeze_perm` (`Frozen` for `&T`, `ReservedFrz` for `&mut T`), while `UnsafeCell` bytes get `nonfreeze_perm` (`PermissionPriv::Cell` for `&T`, `ReservedIM` for unprotected `&mut T`). `Cell` (`perms.rs:14, 74, 138–217`, corresponding to `SharedReadWrite`) allows all child and foreign reads/writes and never transitions. Outside `[base_offset, base_offset + ptr_size)`, `frozen` equals `ty_is_freeze` (`mod.rs:170`), so `&S` on a mixed `!Freeze` struct `S { pure: u32, cell: Cell<u32> }` gives `Frozen` to `pure` (justifying pure `PermTree` caching!), `Cell` to `cell`, and `Cell` to outside bytes in the same allocation.
3. **The Protected `&mut UnsafeCell<T>` Trap (`RetagMode::FnEntry`)**:
   In `miri/src/borrow_tracker/tree_borrows/mod.rs:185–205`:
   ```rust
   } else if is_protected || frozen {
       // We also use this for protected `&mut UnsafeCell` as otherwise adding
       // `noalias` would not be sound.
       Permission::new_reserved_frz()
   } else {
       Permission::new_reserved_im()
   }
   ```
   And `perms.rs:117, 168, 212` asserts `!protected` on `ReservedIM`. Function-entry parameters `x: &mut UnsafeCell<T>` and `Box<UnsafeCell<T>>` (`is_protected == true`) receive `ReservedFrz`, **never** `ReservedIM`! Any foreign write through an aliased `&Cell<T>` while `x` is protected disables `x` and triggers immediate UB. Thus, treating `&mut T` function parameters as exclusive pure loans in `PermTree` is sound even for `T: !Freeze`, whereas local unprotected `&mut *p` reborrows get `ReservedIM` and tolerate foreign writes prior to their first child write (`ReservedIM -> Unique`).

## Boundaries

- **Pure value caching on `!Freeze` shared borrows and CSE on effectful backward continuations (`known not to apply`)**: Caching `*r` in pure environments is **known not to apply** to `!Freeze` sub-places (`&UnsafeCell<T>`, `&Cell<T>`, `&RefCell<T>`), and duplicate-call/dead-binding elimination is **known not to apply** to effectful backward continuations (`AeneasVerif/aeneas#1537`).
- **`ReservedIM` foreign-write tolerance on function-entry `&mut UnsafeCell<T>` / `Box<UnsafeCell<T>>`, automatic `PCell` drop, and ZST address inequality (`known not to apply`)**: Protected function-entry retags (`RetagMode::FnEntry`) assign `ReservedFrz` rather than `ReservedIM` even inside `UnsafeCell` (`miri` `mod.rs:185–205`); automatic `T::drop` on `PCell<T>` scope exit without consuming `PointsTo<T>`/`Perm` is **known not to apply** (`verus` `pcell.rs:44–49, 83–87`); and `PointsTo`/`Perm` address disjointness is **known not to apply** when `size_of::<T>() == 0` (`creusot` `perm.rs:112–114`, `verus` `simple_pptr.rs:300–306`).
- **Shared pinning, raw-to-safe checkout, `.uninit` padding, and reference entry parameters in baseline `Anneal.PureLift` (`unsupported`)**: Pinning `.activeShared` loans, partial-field spatial export, `checkoutFromSpatial`, `.uninit` cells at reabsorption, and non-`.byVal` / non-empty `callerMem` entry signatures in `MirBridge.lean` are **unsupported** in `c131b320eeeb26ef692e5afd5ec8db49ee518613`.
- **`!Unpin` mutable retagging in Miri and meta-tactic framing in `TrustedBoundary.lean` (`unsupported`)**: Mutable/Box retagging on `!Unpin` types is currently **unsupported** (no-op `return None`) in Miri (`mod.rs:151–155`), and `Lean.Meta` framing tactics (`syntax`, `macro_rules`, `elab`) are **unsupported** in Anneal's `theory/` allowlist.
- **Completeness of compiler liveness scheduling (`InterpLiveness.ml`) on unstructured multi-pointer CFGs (`unknown`)**: Whether Aeneas PR `#1537`'s three-tier heuristics (`short`/`default`/`long`) suffice without manual placement annotations on arbitrary unstructured raw-pointer graphs (e.g., intrusive doubly linked list rotations) remains **unknown**.
- **Weak-memory atomics, volatile/MMIO traces, and inline assembly (`not examined`)**: C11/RC11 relaxed/release-acquire view logics, `read_volatile`/`write_volatile`, and `core::arch::asm!` were **not examined** here (for formal container protocols of `Cell`, `RefCell`, `GhostCell`, `OnceCell`, `Rc<RefCell<T>>`, and Landin's knot, see `unsafecell-cell-refcell-ghostcell-and-oncecell-formal-protocols-in-first-order-separation-logic`).

## Evidence

All findings were established from primary source inspection and peer-reviewed publications on `2026-11-20`:

1. **Anneal (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`)**:
   - `theory/Anneal/PureLift/PermTree.lean:40–394`: `SubPerm`, `PermTree.split`, `subPathOverlaps`, `getPathPerm`, `setChildPerm`.
   - `theory/Anneal/PureLift/LoanGraph.lean:53–178, 519–600`: `BackTarget`, `CellVal`, `hasUninitCell`, `SpatialCodec`, `LoanPhase`.
   - `theory/Anneal/PureLift/SpatialPin.lean:44–294, 330–631`: `SpatialProp`, `blocksDisjoint`, `SpatialTriple`, `freezeToSpatialInState`, `mutateSpatialInState`, `reabsorbFromSpatialInState`, and negative guard theorems.
   - `theory/Anneal/PureLift/MirBridge.lean:1285–1550`: `mirAllByValParams`, `MirArgsMatch`, `MirRunsTo`, `mirOperationalAdapter`, `mir_pure_lift_sound`.
2. **Aeneas (`AeneasVerif/aeneas` `main` at `2e3d4488280bb8a95411db81019a7854a784861f`, Ho and Protzenko, ICFP 2022, DOI `10.1145/3547647`) and unmerged upstream PRs**:
   - `main` (`2e3d4488280bb8a95411db81019a7854a784861f`): `backends/lean/Aeneas/Std/Core/Ptr.lean:1–81`.
   - Unmerged PR `#1537` (`5c28fe8def8db99041d22503175591ba1fa47915`): `tests/src/stateful-lifetime.rs:1–80`, `tests/lean/StatefulLifetime.lean:55–80`, `src/interp/{InterpLiveness,InterpJoin}.ml`, `src/symbolic/SymbolicToPureCore.ml`, `src/pure/PureMicroPassesGeneral.ml`.
   - Unmerged PR `#1551` (`1d8f9aa0121faca8ff113c1b9b742b333e3e1519`): `backends/lean/Aeneas/SepLogic/{PCM,IProp,Resource}.lean`, `backends/lean/Aeneas/Std/WPDef.lean:35–99`, `backends/lean/Aeneas/SepLogic/Tactic/Normalize.lean:18–64`.
   - Unmerged PR `#1497` (`d17ca83fc07d712d1785f650840cb2073c259e69`): `backends/lean/Aeneas/Std/Heap.lean:21–125`, `backends/lean/Aeneas/Std/Heap/{Model,ScopedView}.lean`.
   - Unmerged PR `#1447` (`2a1dd75567517e078f90b1df746af7373fe24cbc`): `backends/lean/Aeneas/Data/Layout/{Bytes,EncodeDecode,GaloisConnection,HasLayout}.lean`.
3. **`tiny-iris` (`JoJoDeveloping/tiny-iris` at `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`)**: `theories/heapprop.v:7–10, 117, 242` (`heapProp`, `heapProp_later := id`, `BiAffine`) and `theories/adequacy.v:9–46` (`wpbigstep`, `wp_soundness`).
4. **Creusot (`creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`; Denis et al., ICFEM 2022, DOI `10.1007/978-3-031-17244-1_6`; Golfouse et al., CPP 2026, DOI `10.1145/3779031.3779086`)**: `creusot-std/src/ghost/perm.rs:9–178`, `creusot-std/src/cell/pcell.rs:22–228`, `creusot-std/src/cell/predcell.rs:10–115`, `creusot-std/src/std/ptr.rs:15–250`.
5. **Verus (`verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`; Lattuada et al., OOPSLA 2023, DOI `10.1145/3586037`)**: `source/vstd/cell/pcell.rs:44–243`, `source/vstd/simple_pptr.rs:153–329`, `source/vstd/cell/invcell.rs:71–167`, `source/vstd/cell.rs:26–392`.
6. **Miri and Rust (`rust-lang/miri` at `5a2649e9c3bfbada72665448bddf8b54021bec2e`, Villani et al., PLDI 2025, DOI `10.1145/3735592`; `rust-lang/rust` at `ec65cd52bba13d491ff65c9d218b39753755c84a`)**: `miri` `src/borrow_tracker/tree_borrows/mod.rs:110–221, 328–364`, `perms.rs:10–233`; `rust` `compiler/rustc_middle/src/ty/util.rs:1177–1215`, `library/core/src/cell.rs:737–740, 2313–2388`.
7. **RefinedRust, Lithium, and RustBelt**: Gäher et al., PLDI 2024, DOI `10.1145/3656422`; Sammler et al., PLDI 2021, DOI `10.1145/3453483.3454036`; Jung et al., POPL 2018, DOI `10.1145/3158154`.

## Revalidation

To verify whether these findings remain valid after upstream changes without repeating the full study:

1. **Anneal `PureLift` and `TrustedBoundary`**: Diff `theory/Anneal/PureLift/{PermTree,LoanGraph,SpatialPin,MirBridge}.lean` and `trusted/audit/TrustedBoundary.lean` from `c131b320eeeb26ef692e5afd5ec8db49ee518613`, checking `freezeToSpatialInState` (`.activeMut` and `hasUninitCell` guards), `MirArgsMatch` (`mirAllByValParams` and `callerMem`), and `allowedTheoryTacticKinds`.
2. **Aeneas upstream merges**: Check `AeneasVerif/aeneas` `main` for `backends/lean/Aeneas/SepLogic/IProp.lean`, `backends/lean/Aeneas/Std/Heap/ScopedView.lean`, `backends/lean/Aeneas/Data/Layout/GaloisConnection.lean`, and `src/interp/InterpLiveness.ml`; if merged, inspect `Resource.Compatible` and `ClosedViews`.
3. **Creusot and Verus**: Check `creusot-std/src/ghost/perm.rs` (`#[check(terminates)]`, `disjoint_lemma`), `creusot-std/src/cell/pcell.rs` (`from_mut` prophecy), `vstd/cell/pcell.rs` (`ManuallyDrop<UnsafeCell<T>>`), and `vstd/simple_pptr.rs` (`is_disjoint` non-ZST precondition).
4. **Miri Tree Borrows**: Check `src/borrow_tracker/tree_borrows/{mod,perms}.rs` in `rust-lang/miri` to confirm `is_protected || frozen => Permission::new_reserved_frz()` and `visit_freeze_sensitive` byte-range splitting.
