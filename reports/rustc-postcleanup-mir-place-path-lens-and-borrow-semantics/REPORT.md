<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Place-Path (Lens) References vs. Address-Taken Memory in `Runtime(PostCleanup)` MIR

## Summary

In `rustc`'s `MirPhase::Runtime(RuntimePhase::PostCleanup)` dialect—the MIR
produced by the `mir_drops_elaborated_and_const_checked` query at the
`Runtime(PostCleanup)` phase transition—references (`&T`, `&mut T`) and place
projections obey strict structural invariants enforced by `rustc_mir_transform`
passes (`Derefer`, `EraseDerefTemps`, `CleanupPostBorrowck`, `Subtyper`,
`PostAnalysisNormalize`, and `ElaborateBoxDerefs`) and verified by `Validator`
(`compiler/rustc_mir_transform/src/validate.rs`).

An exhaustive `rustc_driver` census of all `1,148` `Runtime(PostCleanup)` MIR
bodies (`879` callable functions/closures and `269` constant bodies) in Fuchsia
Starnix's `ebpf_core` crate (`src/starnix/lib/ebpf_core`), combined with
synthetic edge-case probes under Miri (Stacked Borrows and Tree Borrows) and a
`1,346`-line Lean 4 (`v4.34.1`) mechanization
([`support/PlacePathMirSemantics.lean`](support/PlacePathMirSemantics.lean)),
establishes three primary conclusions:

1. **Canonical First-Projection `Deref` and `WithRetag::No` Reference Copies in
   `Runtime(PostCleanup)` MIR:**
   - Because `Derefer` (`compiler/rustc_mir_transform/src/deref_separator.rs`)
     is unconditionally enabled (`is_required() = true`, independent of
     `-Z mir-preserve-ub`), every operational `Place` in `Runtime(PostCleanup)`
     MIR has at most one `ProjectionElem::Deref`, strictly at projection index
     `0` (`validate.rs:841-849`). Across all `46,163` operational `Place`
     occurrences (`7,055` projected places) in `starnix/ebpf_core`,
     `deref_at_zero = 5,074` and **`deref_after_zero = 0`**.
   - Every `ProjectionElem::Downcast(_, variant_idx)` is immediately followed
     by `ProjectionElem::Field` (`validate.rs:852-865`; `1,277 / 1,277` in
     `ebpf_core`). `ProjectionElem::OpaqueCast` (`0`) and `Deref` on `Box<T>`
     (`0`) are completely eliminated before `Runtime(PostCleanup)`.
   - `EraseDerefTemps` (`erase_deref_temps.rs:16-31`) rewrites `Derefer`'s
     `Rvalue::CopyForDeref(place)` into
     `Rvalue::Use(Operand::Copy(place), WithRetag::No)` on synthetic locals
     allocated via `MirPatch::new_temp` (`patch.rs:156-163`), which emits **no
     `StorageLive` or `StorageDead` statements** (`666` such reference
     temporaries in `ebpf_core`). When dereferencing through a nested `&mut T`
     (such as `(*pair.0) += x` on `pair: (&mut u64, &mut u64)` or
     `verifier::Type::set_null::bb2[10]: _22 = no_retag copy (*_9)` on
     `_9: &&mut MemoryId`), `Runtime(PostCleanup)` MIR executes `Operand::Copy`
     on a non-`Copy` `&mut T` type with `WithRetag::No` (`validate.rs:645-657`).
   - Across all `5,016` `Rvalue::Ref` statements in `ebpf_core`, `3,946`
     (`78.7%`) are `BorrowKind::Shared`, `54` (`1.1%`) are
     `BorrowKind::Mut { kind: MutBorrowKind::Default }`, and **`1,016`
     (`20.3%` of all borrows, `95.0%` of all mutable borrows, spanning
     `335 / 879` functions)** are
     `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }` emitted by
     method-call autoref on `&mut self` receivers. Furthermore, `15` of those
     `1,016` two-phase borrows in `ebpf_core` execute an overlapping shared
     borrow of the same root local while the `&two_phase mut` reference local
     is already live and initialized (including same-path
     `instruction.set_code((instruction.code() & !BPF_SIZE_MASK) | BPF_DW)` at
     `program::apply_struct_access_mapping::bb24` and disjoint-field
     `self.deps.atomic(&self.context, ...)` across `12`
     `DependencyTracker::atomic_*` methods).

2. **Soundness Boundary of an Algebraic Place-Path (Lens) Store:**
   - Representing a reference value as
     `Val.ref (mutability : Mutability) (borrowId : Nat) (target : PlacePath)`,
     where `PlacePath = (root : Local, path : List PathStep)` indexes into the
     structured value tree of `locals[root]` via total algebraic path lenses
     `getPath` and `setPath`, satisfies the four classic lens laws
     (`getPath_setPath_same`, `setPath_getPath_self`, `setPath_setPath_same`,
     and `setPath_setPath_disjoint_comm`) and flattens arbitrary reborrow chains
     `&mut ((*_r).subpath)` in $O(1)$ (`reborrow_flattening_idempotent`) so
     reference indirection depth never exceeds `1`.
   - Comparing four candidate reference store models proves three strict
     separation results:
     - **Model 1 (Root-Local Eager Copy-In / Copy-Out) is unsound:** When a
       two-phase borrow's argument evaluation mutates a disjoint field of the
       root local before activation (`dt.deps.atomic({ dt.ctx.reg += 5; &dt.ctx }, 1)`),
       or when `Derefer` emits multiple `no_retag copy (_4.0: &mut T)` copies
       from a tuple of mutable references (`tuple_of_mut_refs`), eager
       copy-in/copy-out overwrites live updates with a stale snapshot
       (`eager_copy_in_out_stale_snapshot_unsoundness`).
     - **Model 2 (Eager Exclusive `PlacePath` Lock) is incomplete on safe Rust:**
       Treating `MutBorrowKind::TwoPhaseBorrow` as immediately exclusive
       falsely rejects Starnix's `program::apply_struct_access_mapping::bb24`
       (`two_phase_same_path_shared_read_separation`).
     - **Model 3 (Root-Local Granularity Lock) is incomplete on split-field
       borrows:** Locking `root : Local` instead of `PlacePath` falsely rejects
       Starnix's `12` `DependencyTracker::atomic_*` methods
       (`disjoint_field_two_phase_separation`).
     - **Model 4 (Algebraic `PlacePath` Lens with Two-Phase Reservation
       `.reserved → .active`, and its tag-erased counterpart
       `PurePlacePathLens`):** Soundly admits all `694` value/reference bodies
       in `starnix/ebpf_core`, conditional borrows (`if c { &mut a } else { &mut b }`),
       nested struct/enum/array projections, `WithRetag::No` reference copies,
       and two-phase borrows. By `runReservationTrace_implies_runPureLensTrace`,
       every execution accepted by the Stacked/Tree-Borrows two-phase
       reservation monitor produces the exact same `LocalStore` in the zero-tag
       `PurePlacePathLens` evaluator.

3. **Quantitative End-to-End Impact on `starnix/ebpf_core` (`879` Callables):**
   - Extending a scalar-only `PostCleanup` MIR semantics (`Tier 0`:
     `156 / 879 = 17.7%`) with structured value projections (`Tier 1`: `+47`)
     and the Algebraic Place-Path (Lens) Reference Store (`Tier 2a–2d`: `+491`)
     raises per-body admissibility from **`156 / 879` (`17.7%`) to `694 / 879`
     (`79.0%`)** of the entire crate (`582 / 879 = 66.2%` transitively closed
     under un-stubbed intra-crate calls, and `694 / 879 = 79.0%` when `Tier 4`
     boundaries carry `#[spec]` contracts), without byte-level address layout or
     heap separation logic.

---

## Applicability

The findings, compiler invariants, and mechanized theorems in this report apply
to the following subjects and revisions:

| Subject | Repository / Path | Version / Revision | Role in Report |
| :--- | :--- | :--- | :--- |
| `rustc` (primary) | `rust-lang/rust` | `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `nightly-2026-05-31`) | Primary `rustc_mir_transform` / `rustc_middle` source inspection and `place_path_mir_probe` execution |
| `rustc` (continuity) | `rust-lang/rust` | `1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `nightly-2026-09-30`) | Multi-version verification of `Derefer`, `EraseDerefTemps`, `CleanupPostBorrowck`, `Subtyper`, and `Validator` |
| Miri interpreter | `rust-lang/miri` | `0.1.0` (`19833af72f92c6731a621ca3db0455684003999e`, `1.101.0-nightly`) | Differential execution of synthetic edge-case probes under Stacked Borrows and Tree Borrows (`-Zmiri-tree-borrows`) |
| Starnix `ebpf_core` | `fuchsia/starnix` (`src/starnix/lib/ebpf_core`) | 10-file crate (`1,148` MIR bodies, `879` callables) | Empirical corpus for `Runtime(PostCleanup)` reference, projection, and two-phase borrow census |
| Lean 4 kernel | `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Kernel verification of `support/PlacePathMirSemantics.lean` (`-DwarningAsError=true`, zero `sorry`) |
| Anneal | `joshlf/anneal` | `a3fa446c8e0f1053bd86c970709da007a5f5eddf` | Target `Runtime(PostCleanup)` MIR capture (`anneal-rustc-capture`) and Lean `Trusted` operational semantics |

---

## Findings

### 1. Structural Invariants of References and Projections in `Runtime(PostCleanup)` MIR

In `rustc`, the `mir_drops_elaborated_and_const_checked` query transitions a
body from `MirPhase::Analysis(AnalysisPhase::PostCleanup)` to
`MirPhase::Runtime(RuntimePhase::PostCleanup)` by running the runtime lowering
passes in `compiler/rustc_mir_transform/src/lib.rs:589-623`:

```text
ElaborateBoxDerefs ->CoroutineState -> Lint ->
Derefer -> ElaborateDrops ->
PHASE_CHANGE to Runtime(Initial) ->
CleanupPostBorrowck -> EraseDerefTemps ->Subtyper ->
PostAnalysisNormalize -> RemoveNoopLandingPads -> SimplifyCfg(PromoteConsts) ->
PHASE_CHANGE to Runtime(PostCleanup)
```

Inspecting the pass implementations and `Validator` rules in `rust-lang/rust`
at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (and confirming continuity at
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`) reveals five structural invariants
that govern every `Runtime(PostCleanup)` MIR body:

#### 1.1 Canonical First-Projection `Deref` (`Derefer` + `Validator`)

- **Pass mechanism (`compiler/rustc_mir_transform/src/deref_separator.rs:20-95`):**
  `Derefer` (`deref_finder`) rewrites every operational `Place` (`PlaceContext`
  other than `NonUseContext::VarDebugInfo`) that contains `ProjectionElem::Deref`
  at projection index `idx >= 1`. It splits the place prefix `place.projection[..idx]`
  into a fresh local `temp` with `LocalInfo::DerefTemp`, emits
  `Assign(Place::from(temp), Rvalue::CopyForDeref(place_prefix))`, and replaces
  the prefix with `Place::from(temp).project_deeper(&[ProjectionElem::Deref], tcx)`.
- **Unconditional execution (`deref_separator.rs:97-105`):** Unlike
  `CopyProp` or `DestinationPropagation`, `Derefer::is_required()` returns
  `true` (`PassPolicy::Required` in `1.101.0-nightly`). It runs at `-C opt-level=0`
  and is **never disabled** by `-Z mir-preserve-ub` or `-Z mir-opt-level=0`.
- **Validator invariant (`compiler/rustc_mir_transform/src/validate.rs:841-849`):**
  Beginning at `MirPhase::Runtime(RuntimePhase::Initial)`, `Validator::visit_place`
  enforces:
  ```rust
  if idx > 0
      && self.mir_phase >= MirPhase::Runtime(RuntimePhase::Initial)
      && cntxt != PlaceContext::NonUse(NonUseContext::VarDebugInfo)
  {
      self.fail(location, "Deref Mid Projection, inRuntime dialect");
  }
  ```
- **Empirical confirmation on `starnix/ebpf_core`:** Across all `46,163`
  operational `Place` occurrences (`7,055` projected places) in `ebpf_core`'s
  `879` callable bodies, `deref_at_zero = 5,074` and **`deref_after_zero = 0`**.
  Every operational `Place` in `Runtime(PostCleanup)` MIR therefore has the
  canonical shape:
  $$\text{Place} = (\text{local} : \text{Local},\; \text{derefAtZero} : \text{Bool},\; \text{proj} : \text{List PathStep})$$
  where `proj` contains **zero** `ProjectionElem::Deref` elements.

#### 1.2 `EraseDerefTemps`: Synthetic `WithRetag::No` Reference Copies Without Storage Markers

- **Pass mechanism (`compiler/rustc_mir_transform/src/erase_deref_temps.rs:16-31`):**
  Immediately after `CleanupPostBorrowck`, `EraseDerefTemps` rewrites every
  `Rvalue::CopyForDeref(place)` into
  `Rvalue::Use(Operand::Copy(place), WithRetag::No)` and resets the temporary's
  `LocalInfo::DerefTemp` to `LocalInfo::Boring`.
- **Absence of `StorageLive` / `StorageDead` (`compiler/rustc_mir_transform/src/patch.rs:156-163`):**
  Because `Derefer` allocates its temporaries via `MirPatch::new_temp` (which
  pushes a `LocalDecl` without inserting `StorageLive` or `StorageDead`), all
  `666` `Derefer`-generated reference locals in `starnix/ebpf_core` have **no
  storage markers anywhere in the CFG**. An operational semantics must therefore
  initialize locals lacking storage markers to `.uninit` rather than `.dead`
  (matching `Trusted.Mvp.Semantics.hasStorageMarker`).
- **Non-`Copy` `&mut T` copied via `Operand::Copy` with `WithRetag::No`
  (`compiler/rustc_mir_transform/src/validate.rs:645-657`):**
  In `Runtime(PostCleanup)` MIR, `TypeChecker::check_operand` permits
  `Operand::Copy(place)` on a non-`Copy` type `&mut T` **only** when the enclosing
  `Rvalue::Use(_, retag)` carries `WithRetag::No` (`in_no_retag_use = true`,
  `validate.rs:766-768`). Furthermore, Miri's interpreter
  (`compiler/rustc_const_eval/src/interpret/step.rs:212-238`) skips Stacked/Tree
  Borrows `retag` when `WithRetag::No` is present, so the copied temporary
  inherits the exact borrow tag and target of the source reference.
- **Empirical occurrences in `starnix/ebpf_core` and edge-case fixtures:**
  In `ebpf_core`, there are `605` `WithRetag::No` reference copies across `32`
  functions: `604` on shared references `&T` (`31` functions, primarily
  `match (self, other)` in `PartialEq`/`PartialOrd`/`Display` and tuple matches
  in `verifier.rs`) and `1` on a mutable reference `&mut MemoryId` in
  `verifier::Type::set_null::bb2[10]`:
  ```text
  bb2[1]:  _9 = &(((*_1) as NullOr).0: &mut verifier::MemoryId)
  bb2[10]: _22 = no_retag copy (*_9)
  ```
  Similarly, in `tuple_of_mut_refs` (`let pair = (&mut a, &mut b); *pair.0 += delta; *pair.1 += *pair.0;`),
  `Derefer` + `EraseDerefTemps` emits **seven** separate
  `_temp = no_retag copy (_4.0: &mut u64)` statements without `StorageLive` or
  `StorageDead`.

#### 1.3 Paired `Downcast` + `Field` and Elimination of `Box` `Deref` and `OpaqueCast`

- **Paired `Downcast` + `Field` (`validate.rs:852-865`):** Every
  `ProjectionElem::Downcast(_, variant_idx)` must be immediately followed by
  `ProjectionElem::Field(field_idx, ty)`. In `ebpf_core`,
  `proj_downcast = 1,277`, `proj_field_enum = 1,277`, and
  `downcast_not_followed_by_field = 0`. Thus enum field access is a single
  composite step `PathStep.downcastField variant_idx field_idx`.
- **Elimination of `ProjectionElem::OpaqueCast` (`post_analysis_normalize.rs:34-59`,
  `validate.rs:798-804`):** `PostAnalysisNormalize` resolves all opaque types and
  strips `ProjectionElem::OpaqueCast` (`0` occurrences in `ebpf_core`).
- **Elimination of `Box<T>` `Deref` (`elaborate_box_derefs.rs:70-83`,
  `validate.rs:671-678`):** `ElaborateBoxDerefs` rewrites every `*(box_local)`
  into a pointer extraction `_ptr = Cast(CastKind::Transmute, Copy(box_local.0.0), *const T)`
  (or `CastKind::BoxDerefTransmute` in `1.101.0-nightly`) followed by `(*_ptr)`.
  In `ebpf_core`, `deref_base_box = 0`, `is_unsafe = 0` across all `879`
  callables, and **all `49` raw-pointer dereferences (`deref_base_raw_const = 49`
  across `21` functions in `verifier.rs`)** originate exclusively from
  `ElaborateBoxDerefs` on `Box<MemoryId>` and `Box<Type>` (`transmute_casts = 49`,
  `deref_base_raw_mut = 0`, `raw_ptr_rvalues = 0`).
- **`CleanupPostBorrowck` (`cleanup_post_borrowck.rs:20-75`):** Deletes all
  `StatementKind::Retag`, `StatementKind::FakeRead`, `StatementKind::PlaceMention`,
  and `StatementKind::AscribeUserType`, and converts `BorrowKind::Fake(_)` into
  `BorrowKind::Shared` (`ref_fake = 0`), while **preserving**
  `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }` on `Rvalue::Ref`!

---

### 2. Census of Reference & Projection Patterns Across `starnix/ebpf_core` (`879` Callables)

Running [`support/place_path_mir_probe.rs`](support/place_path_mir_probe.rs) on
`starnix/ebpf_core` yields the complete census in
[`support/ebpf_core_place_path_summary.json`](support/ebpf_core_place_path_summary.json):

#### 2.1 Operational `Place` Projection Chains (`7,055` Projected Places)

| Projection Chain Pattern | Count | Share of Projected Places | Semantic Interpretation |
| :--- | ---: | ---: | :--- |
| `Deref` | `2,673` | `37.89%` | Direct dereference `(*_r)` of `&T`, `&mut T`, or `Box`-lowered `*const T` |
| `Field` | `1,729` | `24.51%` | Direct local struct/tuple field `_local.f` (including `(u64, bool)` checked-op results) |
| `Deref->Field` | `1,095` | `15.52%` | Struct/tuple field through reference `((*_r).f)` |
| `Deref->Downcast->Field` | `1,041` | `14.76%` | Enum variant payload field through reference `(((*_r) as Variant).f)` |
| `Downcast->Field` | `230` | `3.26%` | Direct local enum variant payload field `((_local as Variant).f)` |
| `Deref->Field->Field` | `172` | `2.44%` | Nested struct field through reference `(((*_r).f1).f2)` (e.g., `(((*_1).3: U64Range).1: u64)`) |
| `Deref->Index` | `46` | `0.65%` | Indexing `(*_r)[_i]` through `&[T; N]` or `&[T]` |
| `Deref->Field->Index` | `25` | `0.35%` | Indexing fixed array field `((*_r).reg)[_i]` in `ComputationContext` / `DataDependencies` |
| `Field->Field` | `22` | `0.31%` | Nested struct field on value local `((_local.f1).f2)` |
| `Index` | `7` | `0.10%` | Direct indexing `_arr[_i]` on local fixed array |
| `Deref->Field->Field->Field` | `6` | `0.09%` | Depth-3 nested struct field through reference |
| Other (`Deref->Field->Index->Field`, `Deref->Downcast->Field->Field`, `Subslice`) | `9` | `0.13%` | Composite struct/enum/array chains (`max_proj_len = 4`) |
| **Total Projected Places** | **`7,055`** | **`100.00%`** | **`0` occurrences of `Deref` at index `>= 1` (`deref_after_zero = 0`)** |

#### 2.2 `Rvalue::Ref` Borrow Kinds and Target `Place` Shapes (`5,016` Borrows)

| Category | Variant / Shape | Count | Share | Notes |
| :--- | :--- | ---: | ---: | :--- |
| **`BorrowKind`** | `BorrowKind::Shared` | `3,946` | `78.67%` | Shared borrows `&place` |
| | `BorrowKind::Mut { kind: TwoPhaseBorrow }` | `1,016` | `20.26%` | **`95.0%` of all mutable borrows** (`335 / 879` functions); emitted for `&mut self` method autoref |
| | `BorrowKind::Mut { kind: Default }` | `54` | `1.08%` | Explicit `&mut place` expressions |
| | `BorrowKind::Mut { kind: ClosureCapture }` | `0` | `0.00%` | Zero mutable closure captures in `ebpf_core` |
| | `BorrowKind::Fake(_)` | `0` | `0.00%` | Converted to `Shared` by `CleanupPostBorrowck` |
| **Target `Place` Shape** | Direct reborrow `&(*_r)` / `&mut (*_r)` | `2,701` | `53.85%` | Flattens to `_r`'s `PlacePath` |
| | Direct local `&_x` / `&mut _x` | `1,029` | `20.51%` | Creates `PlacePath(x, [])` |
| | Enum payload sub-reborrow `&(((*_r) as V).f)` | `678` | `13.52%` | Appends `.downcastField V f` to `_r`'s `PlacePath` |
| | Struct field sub-reborrow `&((*_r).f...)` | `526` | `10.49%` | Appends `.field f...` to `_r`'s `PlacePath` |
| | Local field borrow `&(_x.f...)` | `32` | `0.64%` | Creates `PlacePath(x, [.field f...])` |
| | Indexed sub-reborrow `&((*_r)[_i])` | `25` | `0.50%` | Appends `.index val(_i)` to `_r`'s `PlacePath` |
| | Other chained reborrows `&(((*_r).f)[_i])` | `25` | `0.50%` | Appends `[.field f, .index val(_i)]` to `_r`'s `PlacePath` |

#### 2.3 Reference Locals Lifecycle and Two-Phase Reservation Intervals

- **Reference parameters (`1,044` across `879` callables: `471` `&T`, `573` `&mut T`):**
  **`0` reference parameters are ever re-assigned (`ref_param_reseated_count = 0`)**,
  and **`0` references are ever written into a dereferenced place (`ref_written_through_deref = 0`)**.
- **Reference temporaries (`5,834` across `879` callables):**
  - `68` temporaries across `18` functions are assigned more than once
    (`ref_local_multi_assign_count = 68`, arising from conditional/match-arm
    borrows `let r = if c { &a } else { &b }`).
  - `107` operands across `35` functions store references inside aggregates
    (`ref_in_aggregate_count = 107`, primarily `(&a, &b)` tuples for
    `match (self, other)` in `PartialEq`/`PartialOrd` and `core::fmt` argument
    slices).
  - Only `7` functions return a reference in `_0` (`DataWidth::str`,
    `Type::unwrap_releasable`, `VerifiedEbpfProgram::{code,args,struct_access_instructions,maps}`,
    and `Stack::get`).
- **Two-Phase Borrow Reservation-to-Activation Intervals (`1,016` instances):**
  Tracing the CFG from every `Assign(_tp, Rvalue::Ref(_, BorrowKind::Mut { kind: TwoPhaseBorrow }, place))`
  to the `TerminatorKind::Call` (or statement) that consumes `_tp` reveals:
  - **`72` (`7.1%`) `tp_immediate_call`:** Zero non-storage statements occur
    between `_tp = &two_phase mut ...` and the `TerminatorKind::Call` that
    consumes `_tp`.
  - **`929` (`91.4%`) `tp_disjoint_eval`:** Intervening statements evaluate
    other call arguments from disjoint locals while `_tp` is live and reserved.
  - **`15` (`1.5%`) `tp_overlapping_shared_read`:** While `_tp` is live and
    reserved, the body executes a shared borrow or read of the **same root local**:
    1. **Same-path shared borrow during reservation (`program::apply_struct_access_mapping::bb24`):**
       Source line `instruction.set_code((instruction.code() & !BPF_SIZE_MASK) | BPF_DW)`
       lowers to:
       ```text
       bb24[2]:  _78 = &two_phase mut _58
       bb24[7]:  _82 = &_58
       bb24 TERM: _81 = api::EbpfInstruction::code(move _82) -> [return: bb25]
       bb25 TERM: _77 = api::EbpfInstruction::set_code(move _78, move _79) -> [return: bb26]
       ```
       Here `_78` holds a live `&mut EbpfInstruction` targeting `_58` across the
       entire call `EbpfInstruction::code(move _82)` that reads `_58` via `&_58`!
    2. **Disjoint-field shared borrow during reservation (`12` `DependencyTracker::atomic_*`
       methods in `verifier.rs`):**
       Source line `self.deps.atomic(&self.context, dst, offset, src, false)`
       lowers to:
       ```text
       bb0[1]:  _7 = &two_phase mut ((*_1).1: verifier::DataDependencies)
       bb0[4]:  _9 = &((*_1).0: verifier::ComputationContext)
       bb0[5]:  _8 = &(*_9)
       bb0 TERM: _0 = verifier::DataDependencies::atomic(move _7, move _8, ...)
       ```
    3. **Multi-block loop re-borrows (`verifier::terminate_context_chain::bb14..bb15`).**
  - **`0` (`0.0%`) `tp_overlapping_mut_access`:** Zero two-phase borrows in
    `ebpf_core` perform an overlapping mutable access during reservation.

---

### 3. Algebraic Place-Path (Lens) Store Model and Four-Model Separation

To avoid byte-level address arithmetic and heap separation logic while remaining
100% faithful to `Runtime(PostCleanup)` MIR and Miri (Stacked Borrows / Tree
Borrows), [`support/PlacePathMirSemantics.lean`](support/PlacePathMirSemantics.lean)
formalizes the **Algebraic Place-Path (Lens) Store**:

$$\text{PathStep} ::= \text{field}(i) \mid \text{downcastField}(v, i) \mid \text{index}(i)$$

$$\text{PlacePath} ::= \langle \text{root} : \text{Local},\; \text{path} : \text{List PathStep} \rangle$$

$$\text{Val} ::= \text{scalar}(w) \mid \text{structVal}(\vec{v}) \mid \text{enumVal}(\text{var}, \vec{v}) \mid \text{array}(\vec{v}) \mid \text{ref}(m, \text{bid}, \text{target} : \text{PlacePath})$$

#### 3.1 Mechanized Algebraic Lens & Reborrow Flattening Laws

In [`support/PlacePathMirSemantics.lean`](support/PlacePathMirSemantics.lean),
total structural recursion defines `getPath : Val → List PathStep → Option Val`
and `setPath : Val → List PathStep → Val → Option Val`, with the following
kernel-checked theorems:

1. **`getPath_setPath_same` (Get-Put Law):**
   `setPath root path newVal = some root' → getPath root' path = some newVal`.
2. **`setPath_getPath_self` (Put-Get Law):**
   `getPath root path = some curVal → setPath root path curVal = some root`.
3. **`setPath_setPath_same` (Put-Put Law):**
   `setPath root path v1 = some root1 → setPath root1 path v2 = setPath root path v2`.
4. **`setStep_setStep_disjoint_comm` & `getPath_setPath_disjoint` (Disjoint-Path
   Commutativity and Frame Preservation):**
   Whenever `PathsDisjoint p1 p2` holds (i.e., `p1` and `p2` diverge at some step
   `s1 ≠ s2`), writing to `p1` preserves `getPath` on `p2` and commutes with
   writes to `p2`.
5. **`reborrow_flattening_idempotent` ($O(1)$ Reborrow Flattening):**
   Evaluating `Rvalue::Ref(_, m2, (*_r).subProj)` when `locals[_r] = Val.ref m1 bid1 ⟨root, basePath⟩`
   produces `Val.ref m2 bid2 ⟨root, basePath ++ subProj⟩`. Reference indirection
   depth is strictly `1` for arbitrary chains of reborrows.
6. **`no_retag_copy_preserves_ref_target` & `tuple_of_mut_refs_verified`:**
   Copying a reference from a tuple/struct field via `WithRetag::No` preserves
   its `PlacePath` lens target, so mutations through `Derefer`'s synthetic
   temporaries update `locals[target.root]` in place.

#### 3.2 Four-Model Soundness and Completeness Comparison

We compare four candidate operational models for references in
`Runtime(PostCleanup)` MIR across concrete Starnix `ebpf_core` and edge-case
programs (verified against Miri under both Stacked Borrows and Tree Borrows in
[`support/place_path_edge_cases.rs`](support/place_path_edge_cases.rs)):

| Operational Pattern / Program | Model 1: Root-Local Eager Copy-In / Copy-Out | Model 2: Eager Exclusive `PlacePath` Lock | Model 3: Root-Local Granularity Lock | Model 4: Algebraic `PlacePath` Lens (+ Two-Phase Reservation) | Miri (Stacked & Tree Borrows) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| Top-level `&T` / `&mut T` params (`U64Range::max`, `set_code`) | Sound (if non-aliasing) | Sound | Sound | **Sound** | Pass |
| Re-seated `&mut T` param (`param_reseated`) or conditional borrow (`if c { &mut a } else { &mut b }`) | Complex (must track active copy-back target at CFG merge) | Sound | Sound | **Sound** (`conditional_mut_borrow_verified`) | Pass |
| Tuple of `&mut T` + `Derefer` `no_retag copy` (`tuple_of_mut_refs`) | **Unsound** (multiple `no_retag copy` temps & pre-`StorageDead` reads see stale root) | Sound | Sound | **Sound** (`tuple_of_mut_refs_verified`) | Pass |
| Disjoint-field two-phase borrow (`DependencyTracker::atomic_add`: `&two_phase mut (*_1).1` + `&(*_1).0`) | Sound (if no root write during reservation) | Sound | **Incomplete** (false conflict on root `_1`) | **Sound** (`disjoint_field_two_phase_separation`) | Pass |
| Disjoint-field mutation during two-phase reservation (`dt.deps.atomic({ dt.ctx.reg += 5; &dt.ctx }, 1)`) | **Unsound** (copy-back overwrites `dt.ctx.reg` with stale snapshot) | Sound | **Incomplete** (false conflict on root `_1`) | **Sound** (`eager_copy_in_out_stale_snapshot_unsoundness`) | Pass |
| Same-path shared read during two-phase reservation (`apply_struct_access_mapping`: `insn.set_code(insn.code() ...)`) | Sound (if read-only during reservation) | **Incomplete** (false conflict at `_82 = &_58`) | **Incomplete** (false conflict at `_82 = &_58`) | **Sound** (`two_phase_same_path_shared_read_separation`) | Pass |
| Shared aliasing `f(&a, &a)` on `Freeze` types (no `UnsafeCell`) | Sound | Sound | Sound | **Sound** (`shared_alias_freeze_bisimulation`) | Pass |
| Shared aliasing `f(&c, &c)` on `Cell<u64>` (`UnsafeCell`) or active `&mut` + raw-pointer write | Unsound | Rejects | Rejects | **Gated by `bodyWF` (`is_freeze` & `has_raw_ptr = false`) / rejected by `stepReservation`** | UB (raw ptr) / Mutates (`Cell`) |

#### 3.3 Exact Operational Rule for Two-Phase Borrows and Tag-Erasure Theorem

In Miri's Stacked Borrows (`compiler/rustc_const_eval/src/interpret/step.rs:302-320`)
and Tree Borrows, `Rvalue::Ref(_, BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }, place)`
creates a **reserved** mutable borrow (`.reserved`) that acts like a shared
borrow until its first mutable use or call activation (`.active`):

- **Reservation (`BorrowKind::Mut { kind: TwoPhaseBorrow }`):** Requires
  `canReadPath entries target none` (no `.active` mutable borrow overlaps
  `target`) and inserts `⟨bid, target, .reserved, true⟩`. While `.reserved`,
  overlapping `BorrowKind::Shared` borrows and reads of `target` are permitted!
- **Activation (at `TerminatorKind::Call` consuming `_tp` or mutable dereference
  `*_tp = ...`):** Requires `canWritePath entries target (some bid)` (all
  overlapping shared borrows created during argument evaluation, such as `_82`
  in `EbpfInstruction::code(move _82)`, have already been retired) and
  transitions `bid` from `.reserved` to `.active`.
- **Tag-Erasure Soundness Theorem (`runReservationTrace_implies_runPureLensTrace`
  in [`support/PlacePathMirSemantics.lean`](support/PlacePathMirSemantics.lean)):**
  For every execution trace accepted by the Stacked/Tree-Borrows reservation
  monitor (`runReservationTrace`), the zero-tag `PurePlacePathLens` evaluator
  (`runPureLensTrace`, which represents references purely as
  `Val.ref mutability target` and evaluates `getPath`/`setPath` directly on
  `LocalStore` without dynamic borrow tags) succeeds and produces the **exact
  same `LocalStore`**. Consequently, for safe (`!is_unsafe`), borrow-checked
  `Runtime(PostCleanup)` MIR functions whose local types are `Freeze` (no
  `UnsafeCell`) and contain no raw pointers (`has_raw_ptr = false`),
  `PurePlacePathLens` is 100% sound without runtime borrow-tag tracking.

---

### 4. End-to-End Quantitative Impact on `starnix/ebpf_core` (`879` Callables)

Classifying all `879` callable MIR bodies in `starnix/ebpf_core` by the minimum
memory/value model tier required to capture and verify them yields:

| Tier | Model Fragment Required | Callable Bodies | Share (`%`) | Cumulative Bodies | Cumulative (`%`) |
| :--- | :--- | ---: | ---: | ---: | ---: |
| **Tier 0** | Pure scalar & fieldless enum (`0` refs, `0` projections) | `156` | `17.75%` | `156` | `17.75%` |
| **Tier 1** | Pure value ADTs (struct/tuple/enum `Field` & `Downcast->Field`, `0` refs) | `47` | `5.35%` | `203` | `23.09%` |
| **Tier 2a** | Place-Path Lens Refs: top-level `&T`/`&mut T` params + intra-body `&local.path` + reborrows | `244` | `27.76%` | `447` | `50.85%` |
| **Tier 2b** | Place-Path Lens Refs + `MutBorrowKind::TwoPhaseBorrow` (`&two_phase mut`) | `220` | `25.03%` | `667` | `75.88%` |
| **Tier 2c** | Place-Path Lens Refs + refs in tuples (`Derefer` `no_retag copy`) & conditional refs | `16` | `1.82%` | `683` | `77.70%` |
| **Tier 2d** | Place-Path Lens Refs + fixed-size array `[T; N]` `ProjectionElem::Index` | `11` | `1.25%` | **`694`** | **`78.95%`** |
| **Tier 3** | Slice / `str` fat-pointer references (`&[T]`, `&mut [T]`, `&str`) | `8` | `0.91%` | `702` | `79.86%` |
| **Tier 4a** | Recursive `Box<MemoryId>` / `Box<Type>` ADTs (`ElaborateBoxDerefs` `*const T`) | `21` | `2.39%` | `723` | `82.25%` |
| **Tier 4b** | Heap containers & formatting (`Vec`: `85`, `Formatter`: `54`, `Formatter+Vec`: `12`, `Box`: `5`) | `156` | `17.75%` | `879` | `100.00%` |
| **Tier 5** | Unsafe raw pointers, `UnsafeCell`, unions, or inline assembly | `0` | `0.00%` | `879` | `100.00%` |

#### Per-Module Admissibility under the Algebraic Value + Place-Path Lens Model (`Tiers 0 + 1 + 2`)

| Source Module (`starnix/ebpf_core`) | Total Callables | Tier 0 (Scalar) | Tier 1 (Value ADT) | Tier 2 (Place-Path Lens) | Total Admitted (`Tiers 0..2`) | Module Coverage (`%`) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| `scalar_value.rs` | `205` | `14` | `31` | `156` | **`201`** | **`98.05%`** |
| `executor.rs` | `80` | `0` | `0` | `78` | **`78`** | **`97.50%`** |
| `maps.rs` | `36` | `5` | `2` | `27` | **`34`** | **`94.44%`** |
| `api.rs` | `33` | `11` | `2` | `16` | **`29`** | **`87.88%`** |
| `visitor.rs` | `8` | `4` | `0` | `3` | **`7`** | **`87.50%`** |
| `verifier.rs` | `435` | `120` | `8` | `172` | **`300`** | **`68.97%`** |
| `program.rs` | `66` | `2` | `3` | `34` | **`39`** | **`59.09%`** |
| `error.rs` | `12` | `0` | `1` | `4` | **`5`** | **`41.67%`** |
| `conformance.rs` | `4` | `0` | `0` | `1` | **`1`** | **`25.00%`** |
| **Total (`ebpf_core`)** | **`879`** | **`156`** | **`47`** | **`491`** | **`694`** | **`78.95%`** |

- **Transitive Call-DAG Closure:** Of the `694` `Tier 0..2` callable bodies,
  **`582 / 879` (`66.21%`)** have **100% of their transitive intra-crate callees
  also inside `Tiers 0..2`** (requiring zero `#[spec]` boundary stubs on `Tier 4`
  containers). The remaining `112` `Tier 0..2` bodies call a small set of
  `Tier 4` container/logging methods—principally
  `VerificationContext::emit_log` (`13` callers),
  `VerificationContext::push_successor` (`11` callers),
  `ComputationContext::{load_memory,store_memory}` (`6` callers), and
  `Stack::get` (`3` callers)—and become modularly verifiable as soon as those
  helper methods carry `#[spec]` contracts.

---

## Boundaries

The zero-tag Algebraic Place-Path (Lens) Store (`PurePlacePathLens`) is sound
if and only if the target `Runtime(PostCleanup)` MIR body satisfies five explicit
`bodyWF` boundary conditions (or pairs the lens store with the dynamic
`PlacePathReservation` monitor):

1. **No Raw-Pointer Dereferences or Casts (`has_raw_ptr = false`):**
   Raw pointers (`*const T`, `*mut T`, `Rvalue::RawPtr`, `CastKind::PtrToPtr`,
   `CastKind::Transmute`) bypass `rustc_borrowck`'s lifetime and aliasing guarantees.
   Note that `ElaborateBoxDerefs` lowers safe `Box<T>` dereferences into
   `CastKind::Transmute` / `BoxDerefTransmute` to `*const T`; admitting `Box<T>`
   (`Tier 4a`, `21` functions in `ebpf_core`) requires recognizing the
   `ElaborateBoxDerefs` idiom (`box_local.0.0 as *const T`) as a value-tree step
   rather than an arbitrary raw pointer.
2. **All Referenced Types Are `Freeze` (`ty.is_freeze(tcx, typing_env) = true`,
   No `UnsafeCell`):**
   As demonstrated by `interior_mutability_cell(&cell, &cell)` in
   [`support/place_path_edge_cases.rs`](support/place_path_edge_cases.rs), shared
   references `&Cell<u64>` allow mutation through a shared borrow, violating
   `shared_alias_freeze_bisimulation`. Every local and parameter type reachable
   through a shared reference in `PurePlacePathLens` must satisfy `is_freeze`.
3. **Caller-Passed Reference Disjointness for `&mut T` Parameters:**
   At function entry, every `&mut T` parameter `_i` must be initialized to a
   `PlacePath` root `callerSlot(i)` disjoint from all other `&mut T` and `&T`
   parameters (guaranteed by `rustc_borrowck` at every safe call site, and
   enforced at inter-procedural `TerminatorKind::Call` boundaries by checking
   `canWritePath` / `canReadPath` across argument `PlacePath`s). By
   `shared_alias_freeze_bisimulation`, multiple shared `&T` parameters on `Freeze`
   types may safely alias the same caller slot or be modeled as distinct
   read-only caller slots initialized with equal values.
4. **No Returning References to Frame-Local Allocations:**
   When `_0` has a reference type (`7` functions in `ebpf_core`), the returned
   `Val.ref _ _ ⟨root, path⟩` must have `root` rooted in an input reference
   parameter (`1 <= root <= arg_count`) or static constant, never a frame-local
   variable (`root > arg_count`) whose storage dies upon `Return`.
5. **No Unsized Slice Coercions or Dynamic Heap Containers (`Tiers 3–4b`):**
   Fixed-size arrays `[T; N]` (`Tier 2d`) are finite value trees (`Val.array`)
   with bounds-checked `PathStep.index i`. Unsized slices `&[T]` / `&str`
   (`Tier 3`, `8` functions in `ebpf_core`) require a fat-pointer subslice lens
   `(root, basePath, offset, len)`, and `Vec<T>` / `HashMap<K, V>` (`Tier 4b`,
   `156` functions) require `#[spec]` contracts over logical sequence/map models.

---

## Evidence

All claims in this report are backed by primary source citations and four
reproducible artifacts under `support/`:

1. **`rustc` Primary Source Citations (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`
   and `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`):**
   - `compiler/rustc_mir_transform/src/lib.rs:589-623`: `Runtime(PostCleanup)`
     pass pipeline (`mir_drops_elaborated_and_const_checked`).
   - `compiler/rustc_mir_transform/src/deref_separator.rs:20-105`: `Derefer`
     pass (`is_required() = true`) splitting mid-projection `Deref` into
     `LocalInfo::DerefTemp` + `Rvalue::CopyForDeref`.
   - `compiler/rustc_mir_transform/src/erase_deref_temps.rs:16-31` and
     `compiler/rustc_mir_transform/src/patch.rs:156-163`: `EraseDerefTemps`
     lowering `CopyForDeref` to `Rvalue::Use(Operand::Copy(_), WithRetag::No)`
     without `StorageLive`/`StorageDead`.
   - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:20-75`:
     `CleanupPostBorrowck` stripping `Retag`/`FakeRead`/`PlaceMention`/`AscribeUserType`
     while preserving `MutBorrowKind::TwoPhaseBorrow`.
   - `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs:70-83`:
     `ElaborateBoxDerefs` lowering `Box<T>` dereferences to `Transmute` + `*const T`.
   - `compiler/rustc_mir_transform/src/validate.rs:645-680, 766-865`: `Validator`
     enforcing `idx == 0` for `Deref`, paired `Downcast` + `Field`, and
     `WithRetag::No` for non-`Copy` `Operand::Copy`.
   - `compiler/rustc_const_eval/src/interpret/step.rs:212-238, 302-320`: Miri
     operational semantics for `WithRetag::No` and `Rvalue::Ref`.
2. **[`support/place_path_mir_probe.rs`](support/place_path_mir_probe.rs):**
   Self-contained `rustc_driver` probe hooking `mir_drops_elaborated_and_const_checked`,
   asserting `body.phase == MirPhase::Runtime(RuntimePhase::PostCleanup)`, and
   extracting projection chains, `BorrowKind` distributions, `TwoPhaseBorrow`
   reservation-to-activation intervals, `WithRetag::No` reference copies, and
   call-DAG edges.
3. **[`support/ebpf_core_place_path_summary.json`](support/ebpf_core_place_path_summary.json):**
   Complete machine-readable census output across all `1,148` MIR bodies (`879`
   callables) of Starnix `ebpf_core`.
4. **[`support/place_path_edge_cases.rs`](support/place_path_edge_cases.rs):**
   Reproducible Rust + Miri test suite covering un-reseated and re-seated `&mut`
   parameters, chained projections `(((*_1).3).1)`, same-path and disjoint-field
   two-phase borrows, disjoint-field mutation during two-phase reservation,
   nested reborrows, conditional mutable borrows, tuples of `&mut` references
   (`Derefer` `WithRetag::No` copies), match guards over `&mut`, `Freeze` shared
   aliasing, and `Cell<u64>` interior mutability. Verified with `cargo +nightly miri test`
   under both Stacked Borrows and Tree Borrows (`-Zmiri-tree-borrows`).
5. **[`support/PlacePathMirSemantics.lean`](support/PlacePathMirSemantics.lean):**
   Self-contained, `1,346`-line Lean 4 (`v4.34.1`) mechanization proving all
   algebraic lens laws, $O(1)$ reborrow flattening, `WithRetag::No` tuple-of-refs
   and conditional-borrow verification, the three four-model separation theorems,
   the tag-erasure soundness theorem (`runReservationTrace_implies_runPureLensTrace`),
   and concrete Starnix `ebpf_core` function verification (`-DwarningAsError=true`,
   zero `sorry`, zero `native_decide`).

---

## Revalidation

To revalidate all probes, Miri differential tests, and Lean 4 proofs:

```bash
# 1. Verify the Lean 4 mechanization (v4.34.1, zero warnings, zero sorry)
lean -DwarningAsError=true \
  reports/rustc-postcleanup-mir-place-path-lens-and-borrow-semantics/support/PlacePathMirSemantics.lean

# 2. Compile and run the rustc_driver PostCleanup MIR probe on the edge-case suite
SYSROOT=$(rustc +nightly-2026-05-31 --print sysroot)
rustc +nightly-2026-05-31 --edition=2024 -O \
  reports/rustc-postcleanup-mir-place-path-lens-and-borrow-semantics/support/place_path_mir_probe.rs \
  -L "$SYSROOT/lib" -C link-args="-Wl,-rpath,$SYSROOT/lib" \
  -o place_path_mir_probe
./place_path_mir_probe --edition=2021 --crate-type=lib \
  reports/rustc-postcleanup-mir-place-path-lens-and-borrow-semantics/support/place_path_edge_cases.rs

# 3. Run the edge-case test suite under native rustc and Miri (Stacked & Tree Borrows)
rustc +nightly-2026-05-31 --edition=2021 --test \
  reports/rustc-postcleanup-mir-place-path-lens-and-borrow-semantics/support/place_path_edge_cases.rs \
  -o place_path_edge_cases_test && ./place_path_edge_cases_test
```
