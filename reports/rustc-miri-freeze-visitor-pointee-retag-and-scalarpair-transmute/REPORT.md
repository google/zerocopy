# `FreezeVisitor` Byte Intervals, `PointeeInfo` / `Box` / `Pin` Retag Semantics, and `BackendRepr::ScalarPair` Padding Reset in `rustc`, Miri, and `lean-miri`

## Summary

This report characterizes three layout- and type-driven mechanisms across
`rustc` (`8144389c895da997dbdecaa635e41d6a50be6ffd`), Miri
(`7fa591d7d4dd9af8154becbc8332f8096f8323b1`), and `lean-miri`
(`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):

1. **`visit_freeze_sensitive` (`UnsafeCellVisitor`) and Static Layout
   Extraction**: When Tree Borrows retags a reference or box to a place of size
   `size`, `visit_freeze_sensitive` walks `TyAndLayout` without reading memory
   and partitions `[0, size)` into `frozen = true` (`Permission::Frozen` or
   `Permission::ReservedFrz`) and `frozen = false` (`Permission::Cell` or
   `Permission::ReservedIM`) byte intervals:
   - **Struct padding is always frozen**: In `FieldsShape::Arbitrary`, all
     inter-field and trailing padding bytes—even padding immediately adjacent to
     or between `UnsafeCell<U>` fields—are swept into `frozen = true` intervals.
   - **Non-`Freeze` `Variants::Multiple` enums and `FieldsShape::Union`s are
     entirely unfrozen**: When `!ty.is_freeze` holds and `layout.variants` is
     `Variants::Multiple` (or `layout.fields` is `FieldsShape::Union`), the
     visitor marks the entire `[0, size)` extent (including discriminant tags
     and `Freeze` variant payloads) as `frozen = false`. Conversely, an enum
     with a single inhabited variant and uninhabited 1-ZST peer variants has
     `Variants::Single` under `repr(Rust)` (`!repr.inhibit_enum_layout_opt()`),
     causing the visitor to recurse into that single inhabited variant and
     freeze its `Freeze` fields and padding, whereas adding `#[repr(C)]` or
     `#[repr(Int)]` sets `inhibit_enum_layout_opt() = true`, forces
     `Variants::Multiple`, and leaves the entire enum unfrozen.
   - **Zero-sized `UnsafeCell<()>` causes in-bounds permissions and
     `outsidePermission` to diverge**: Because `UnsafeCell<()>` does not
     implement `Freeze`, `ty.is_freeze` for `(u32, UnsafeCell<()>)` is `false`.
     However, `visit_freeze_sensitive` ignores zero-sized `UnsafeCell`s
     (`if unsafe_cell_size != Size::ZERO`), flushing all 4 in-bounds bytes
     `[0, 4)` as `frozen = true`, while `NewPermission::new` computes
     `outside_perm` from `ty.is_freeze` (`false`). Consequently, static layout
     extraction for Tree Borrows retagging must record **both**
     `freezeRanges : List FreezeRange` (for in-bounds `[0, size)` permissions)
     and a separate `tyIsFreeze : Bool` flag (for `outsidePermission`); neither
     can be derived from the other.
2. **`PointeeInfo`, `Unpin ∧ UnsafeUnpin`, and `Box<T>` / `Pin<&mut T>`
   Retagging**:
   - Both `TyAndLayout::pointee_info_at` and Tree Borrows `NewPermission::new`
     define effective unpin as the conjunction
     `ty_is_unpin = pointee.is_unpin && pointee.is_unsafe_unpin`. Because
     `Pin<Ptr>` is a `Variants::Single` wrapper with field `0` at offset `0`,
     `Pin<&mut T>` and `Pin<Box<T>>` have the exact same `PointeeInfo` and
     `ValidityVisitor` traversal behavior as `&mut T` and `Box<T>`.
   - Whenever `!ty_is_unpin` holds (such as `PhantomPinned` or `UnsafePinned`),
     `NewPermission::new` returns `None` for both `Mutable` (`&mut T`,
     `Pin<&mut T>`) and `Box` (`Box<T>`, `Pin<Box<T>>`) in all `RetagMode`s
     (`Default`, `TwoPhase`, and `FnEntry`).
   - When `ty_is_unpin` is `true`, `ValidityVisitor::check_safe_pointer` retags
     `&T`, `&mut T`, `Pin<&mut T>`, `Box<T, Global>`, and `Pin<Box<T, Global>>`
     on **both** `RetagMode::Default` (intra-function copies/moves with
     `with_retag = true`) and `RetagMode::FnEntry` (argument passing in
     `init_stack_frame`). On `FnEntry`, references receive
     `Some(StrongProtector)` whereas `Box<T, Global>` receives
     `Some(WeakProtector)` (permitting in-callee deallocation). Furthermore,
     because `NewPermission::new` checks `if is_protected || frozen`, protected
     `FnEntry` retags of `&mut T` and `Box<T, Global>` (with default
     `implicit_writes = false`) assign `ReservedFrz`—never `ReservedIM`—even
     when `T` is `UnsafeCell<U>`.
3. **`BackendRepr::ScalarPair` `bOffset` and `Transmute` Padding Reset**:
   - For `BackendRepr::ScalarPair { a, b, b_offset }`, `LayoutData::scalar_pair`
     computes `b_offset = a.size(dl).align_to(b.default_align(dl).abi)`.
   - `read_immediate_from_mplace_raw` reads only `[0, a_size)` and
     `[b_offset, b_offset + b_size)`, ignoring inter-element alignment padding
     `[a_size, b_offset)` and trailing padding `[b_offset + b_size, size)`.
   - Both `write_immediate` and `copy_op_allow_transmute` (`Rvalue::Cast::Transmute`)
     enforce padding reset to `uninit`. In particular, `copy_op_inner` runs
     `validate_place` with `reset_provenance_and_padding = true` at **both**
     `src.layout()` (when `src.ty != dest.ty`) and `dest.layout()`. Therefore,
     transmuting **either** from `[u8; 8]` to `#[repr(C)] struct Pair(u8, u32)`
     **or** from an in-memory `Pair(u8, u32)` (whose padding bytes `[1..4)` were
     explicitly initialized via a raw pointer) to `[MaybeUninit<u8>; 8]` erases
     bytes `[1..4)` in the destination to `uninit`.

## Applicability

The findings in this report apply to the following concrete systems and
revisions identified in `REPORT.json`:

1. **`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`**:
   Defines `rustc_abi` layout computation (`Variants`, `FieldsShape`,
   `BackendRepr::ScalarPair`, `PointerKind`, `PointeeInfo`), `rustc_middle`
   trait and pointee queries (`Ty::is_freeze`, `Ty::is_unpin`,
   `Ty::is_unsafe_unpin`, `TyAndLayout::pointee_info_at`), and `rustc_const_eval`
   CTFE/Miri interpretation (`ValueVisitor::walk_value`, `ValidityVisitor`,
   `read_immediate_from_mplace_raw`, `write_immediate_to_mplace_no_validate`,
   `copy_op_inner`, and `copy_op_allow_transmute`).
2. **`rust-lang/miri` at `7fa591d7d4dd9af8154becbc8332f8096f8323b1`**:
   Implements `visit_freeze_sensitive` and `UnsafeCellVisitor`
   (`src/helpers.rs`) and Tree Borrows permission/retag policies
   (`src/borrow_tracker/tree_borrows/mod.rs`) against the `rustc_const_eval`
   hooks above.
3. **`proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`**:
   Provides the Lean 4 mechanization of `FreezeVisitor`, `FreezeMap`,
   `RetagPolicy`, `RetagPipeline`, `TypedRetag`, `ValidityVisitor`,
   `RuntimeLayout`, `Place`, and `Cast` under `Miri/`, porting the `rustc`
   (`8144389c895d`) and Miri (`7fa591d7d4dd`) semantics above.
4. **Live Miri Nightly Toolchain (`rust-lang/rust` at
   `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly` /
   `miri 0.1.0`, `2026-11-11`)**:
   Used to execute the 17-test empirical Miri suite in
   [`support/miri_layout_probe/src/lib.rs`](support/miri_layout_probe/src/lib.rs)
   with `MIRIFLAGS="-Zmiri-tree-borrows"`. All 17 behaviors observed under
   `3ef0c22cdb86` match the source semantics of `rustc@8144389c895d`,
   `miri@7fa591d7d4dd`, and `lean-miri@c92d1d9754c9`.
5. **Lean 4 Toolchains `v4.28.0-rc1` (`3b0f2862196c6a8af9eb0025ee650252694013dd`)
   and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)**:
   Both toolchains kernel-check the standalone formalization and equivalence
   proofs in
   [`support/LayoutFreezeAndScalarPairProbe.lean`](support/LayoutFreezeAndScalarPairProbe.lean)
   identically with zero `sorryAx` axioms.

Scope conditions that control the behavior described below:

- **Precise interior mutability (`precise_interior_mut`)**: Miri enables
  `precise_interior_mut = true` by default (`-Zmiri-Cid` / default borrow
  tracker configuration). If `-Zmiri-disable-precise-interior-mutability` is
  set, `tb_reborrow` skips `visit_freeze_sensitive` and uses `unfreeze_perm`
  uniformly across `[0, size)` whenever `!ty.is_freeze`.
- **Tree Borrows implicit writes (`implicit_writes`)**: By default in Miri,
  `implicit_writes` is `false`. Passing `-Zmiri-tree-borrows-implicit-writes`
  changes `FnEntry` permissions for `&mut T` and `Box<T>` (without
  `#[rustc_no_writable]`) from `ReservedFrz` to `Unique` on in-bounds locations
  and performs an initial `Write` access instead of `Read`.
- **Validation enforcement (`enforce_validity`)**: Padding reset during
  `copy_op_inner` (`Rvalue::Cast::Transmute` and typed copies) and value-validity
  retagging require `M::enforce_validity` to be enabled (the Miri default unless
  `-Zmiri-disable-validation` is passed).
- **Optimization level in `pointee_info_at`**: In `rustc_middle`,
  `ty_and_layout_pointee_info_at` gates `frozen` and `unpin` on
  `tcx.sess.opts.optimize != OptLevel::No` (for LLVM attribute emission),
  whereas Miri's `NewPermission::new` queries `is_freeze`, `is_unpin`, and
  `is_unsafe_unpin` unconditionally at all optimization levels.

## Findings

### 1. `visit_freeze_sensitive` (`UnsafeCellVisitor`) and Static `TyAndLayout` Extraction

`Basis: source + execution + derived`

#### 1.1 Operational Mechanism of `visit_freeze_sensitive` and `UnsafeCellVisitor`

When Tree Borrows reborrows a place `(place, size)` with
`precise_interior_mut == true` (`rust-lang/miri@7fa591d7d4dd`:
`src/borrow_tracker/tree_borrows/mod.rs:342-363`;
`proofs-rs/lean-miri@c92d1d9754c9`:
`Miri/TreeBorrows/RetagPipeline.lean:178-197` and
`Miri/Interpreter/TypedRetag.lean:56-72`), it constructs `inside_perms`
over `[0, size)` by calling `visit_freeze_sensitive(place, size, |range, frozen| ...)`
(`src/helpers.rs:469-539`, `Miri/TreeBorrows/FreezeVisitor.lean:49-136`):

1. **Monotonic Address Cursor `cur_addr`** (`src/helpers.rs:487-511`,
   `FreezeVisitor.lean:49-62`):
   - `visit_freeze_sensitive` initializes `start_addr = place.ptr().addr()` and
     `cur_addr = start_addr`.
   - Its helper `unsafe_cell_action(unsafe_cell_ptr, unsafe_cell_size)` takes
     the start address `unsafe_cell_addr = unsafe_cell_ptr.addr()` and byte
     length `unsafe_cell_size` of an interior-mutable subvalue:
     - Computes `frozen_size = unsafe_cell_addr - cur_addr` (asserting
       `unsafe_cell_addr >= cur_addr`).
     - If `frozen_size != Size::ZERO`, emits
       `action(alloc_range(cur_addr - start_addr, frozen_size), true)` (marking
       `[cur_addr - start_addr, unsafe_cell_addr - start_addr)` as
       **`frozen = true`**) and advances `cur_addr += frozen_size`.
     - If `unsafe_cell_size != Size::ZERO`, emits
       `action(alloc_range(cur_addr - start_addr, unsafe_cell_size), false)`
       (marking
       `[unsafe_cell_addr - start_addr, unsafe_cell_addr - start_addr + unsafe_cell_size)`
       as **`frozen = false`**) and advances `cur_addr += unsafe_cell_size`.
2. **Non-Zero Size Guard in Visitor Hook** (`src/helpers.rs:516-530`,
   `FreezeVisitor.lean:64-69`):
   - The closure stored in `UnsafeCellVisitor::unsafe_cell_action` computes
     `unsafe_cell_size` (via `size_and_align_of_val(place)`, falling back to
     `place.layout.size`) and guards the call on non-zero size:
     ```rust
     if unsafe_cell_size != Size::ZERO {
         unsafe_cell_action(&unsafe_cell_ptr, unsafe_cell_size)
     } else {
         interp_ok(())
     }
     ```
   - Consequently, **any zero-sized `UnsafeCell` (`unsafe_cell_size == 0`) is
     ignored**: it neither emits a `frozen = false` interval nor advances
     `cur_addr`.
3. **Final End-Pointer Flush** (`src/helpers.rs:536`,
   `FreezeVisitor.lean:129-132`):
   - After `UnsafeCellVisitor::visit_value(place)` finishes,
     `visit_freeze_sensitive` invokes:
     ```rust
     unsafe_cell_action(&place.ptr().wrapping_offset(size, this), Size::ZERO)
     ```
   - This flushes the remaining suffix `[cur_addr - start_addr, size)` as
     **`frozen = true`** whenever `cur_addr < start_addr + size`.

#### 1.2 Four Layout Regimes: Structs, Enums, Unions, and Zero-Sized `UnsafeCell<()>`

##### Regime 1: Structs Mixing `Freeze` Fields, Padding, and `UnsafeCell<U>` Fields

In `UnsafeCellVisitor::visit_value` (`src/helpers.rs:562-603`,
`FreezeVisitor.lean:80-90`), a struct containing an `UnsafeCell<U>` has
`is_unsafe_cell == false`, `type_is_freeze == false`, `FieldsShape::Arbitrary`,
and `Variants::Single { index: 0 }`. It calls `self.walk_value(v)`
(`compiler/rustc_const_eval/src/interpret/visitor.rs:148-153`,
`FreezeVisitor.lean:105-108`), which iterates over
`fields.index_by_increasing_offset()` (`in_memory_order`) in increasing byte
offset order:

- Visiting any `Freeze` field returns immediately because
  `self.ecx.type_is_freeze(v.layout.ty)` is `true` (`src/helpers.rs:572-574`,
  `FreezeVisitor.lean:83-84`), leaving `cur_addr` unchanged.
- Visiting a non-zero-sized `UnsafeCell<U>` field at offset `off` with size
  `sz > 0` calls `unsafe_cell_action`, which marks `[cur_addr - start_addr, off)`
  as **`frozen = true`** and `[off, off + sz)` as **`frozen = false`**, setting
  `cur_addr = start_addr + off + sz`.
- After all fields are visited, the final flush at `start_addr + size` marks
  `[cur_addr - start_addr, size)` as **`frozen = true`**.

Therefore, **all padding bytes inside a struct—whether before an `UnsafeCell`,
between a `Freeze` field and an `UnsafeCell` field, between two `UnsafeCell`
fields, or trailing after an `UnsafeCell` field at the end of the struct—are
marked `frozen = true` (`Permission::Frozen` for `&T`, `Permission::ReservedFrz`
for `&mut T` / `Box<T>`)**. Only the exact `[offset, offset + size)` byte
intervals of non-zero-sized interior-mutable leaves receive `frozen = false`.

In [`support/miri_layout_probe/src/lib.rs`](support/miri_layout_probe/src/lib.rs),
for `#[repr(C)] struct MixedStruct { a: u8, b: UnsafeCell<u32> }` (`size = 8`,
`a` at `0..1`, padding at `1..4`, `b` at `4..8`), writing to `b` (`4..8`)
through `&MixedStruct` succeeds (`struct_unsafecell_field_write_ok`), whereas
writing to inter-field padding byte `1` (`struct_padding_write_via_shared_ref_is_ub`)
or trailing padding byte `5` of `TrailingPadStruct`
(`struct_trailing_padding_write_via_shared_ref_is_ub`) triggers immediate Tree
Borrows UB (`the accessed tag has state Frozen which forbids this child write access`).

##### Regime 2: Multi-Variant Enums (`Variants::Multiple`) vs. Single-Inhabited-Variant Enums (`Variants::Single`)

In `UnsafeCellVisitor::visit_value` (`src/helpers.rs:585-594`,
`FreezeVisitor.lean:87-89`):

```rust
} else if matches!(v.layout.variants, Variants::Multiple { .. }) {
    // A multi-variant enum, or coroutine, where at least one variant is not `Freeze`.
    // Walking this value would read the discriminant, which we cannot do during
    // `visit_freeze_sensitive` as nobody should be able to observe that read (Wait:
    // reading the discriminant itself could trigger SB/TB errors or infinite recursion).
    // So we conservatively treat the entire enum as `UnsafeCell`.
    (self.unsafe_cell_action)(v)
```

When `E` is `!Freeze` and has `v.layout.variants == Variants::Multiple { .. }`:

1. `visit_freeze_sensitive` **does not read the discriminant** and **does not
   freeze the discriminant tag**.
2. Instead, it invokes `unsafe_cell_action` on the **entire enum
   `[0, size_of::<E>())`**, marking every byte `[0, size)` as
   **`frozen = false` (`Permission::Cell` for `&E`, `Permission::ReservedIM`
   for unprotected `&mut E`)**.
3. Consequently, while a shared reference `r: &E` is live—even when `e`
   currently holds a `Frozen(u64)` variant—mutating the `Frozen(u64)` payload or
   overwriting the discriminant tag itself to `SharedMut(UnsafeCell::new(...))`
   through a raw pointer derived from `r`, and subsequently reading `*r`, is
   permitted without UB in Miri Tree Borrows
   (`multivariant_enum_mutate_frozen_payload_and_discriminant_ok`).

**Interaction with uninhabited variants and `#[repr(C)]`**: In
`compiler/rustc_abi/src/layout.rs:360, 378`, if an enum has multiple syntactic
variants, all variants except one are `absent` (uninhabited and composed only of
1-ZST fields, `layout.rs:90-101`), **and** `!repr.inhibit_enum_layout_opt()`
holds (`repr(Rust)` without `#[repr(C)]` or `#[repr(Int)]`,
`compiler/rustc_abi/src/lib.rs:224-226`), `rustc_abi` computes
`v.layout.variants = Variants::Single { index }`. For `Variants::Single`,
`UnsafeCellVisitor` recurses into that single inhabited variant via
`walk_value` (`visitor.rs:116-123`) and freezes its `Freeze` fields and padding
(`single_inhabited_variant_enum_freezes_frozen_field_ub`). Adding `#[repr(C)]`
to the exact same enum (`SingleInhabitedReprCEnum`) sets
`repr.inhibit_enum_layout_opt() = true`, forcing `Variants::Multiple` and making
the entire enum `Permission::Cell`
(`repr_c_uninhabited_variant_forces_variants_multiple_cell_ok`).

##### Regime 3: Unions (`FieldsShape::Union`)

In `rustc`, a `union U` implements `Freeze` if and only if all of its fields
implement `Freeze`:

- **All-`Freeze` union**: `self.ecx.type_is_freeze(v.layout.ty)` returns `true`
  (`src/helpers.rs:572-574`, `FreezeVisitor.lean:83-84`). `visit_value` is a
  no-op, and the final flush marks `[0, size)` as **`frozen = true`**
  (`union_all_freeze_write_is_ub`).
- **Union with at least one `!Freeze` field**: `self.ecx.type_is_freeze(v.layout.ty)`
  returns `false`, and `matches!(v.layout.fields, FieldsShape::Union(..))`
  triggers (`src/helpers.rs:575-577`, `FreezeVisitor.lean:85-86`), calling
  `(self.unsafe_cell_action)(v)` on the **entire union `[0, size)`**. Even when
  the `UnsafeCell` field is smaller than the union (for example,
  `#[repr(C)] union UnionWithSmallCell { a: u64, b: ManuallyDrop<UnsafeCell<u32>> }`
  where `size = 8` and `b` occupies only `[0..4)`), all 8 bytes `[0..8)` are
  marked `frozen = false` (`Permission::Cell`), confirmed by
  `union_with_unsafecell_entire_size_is_cell_ok`.

##### Regime 4: Zero-Sized `UnsafeCell<()>` — Why Static Extraction Must Store Both `freezeRanges` and `tyIsFreeze`

In `core::cell`, `UnsafeCell<T>` is `#[fundamental]` and has no `Freeze`
implementation for any `T`, including `T = ()` or `[u8; 0]`. In
`Ty::is_trivially_freeze` (`compiler/rustc_middle/src/ty/util.rs:1203-1221`) and
`is_freeze_raw` (`compiler/rustc_ty_utils/src/common_traits.rs:25-27`),
`ty.is_freeze(tcx, typing_env)` queries `LangItem::Freeze` without inspecting
field sizes. Thus, for `WithZstCell = (u32, UnsafeCell<()>)` (`size = 4`),
**`ty.is_freeze` is `false`**.

However, when `visit_freeze_sensitive` walks `WithZstCell`:

1. Field `0` (`u32` at `[0..4)`) is `Freeze` and is skipped (`cur_addr` remains
   `start_addr + 0`).
2. Field `1` (`UnsafeCell<()>` at offset `4`, `size = 0`) has
   `is_unsafe_cell == true` and `unsafe_cell_size == Size::ZERO`. The closure in
   `visit_freeze_sensitive` (`src/helpers.rs:524`, `FreezeVisitor.lean:66`)
   checks `if unsafe_cell_size != Size::ZERO`, which is **`false`**, so it skips
   the zero-sized cell without calling `unsafe_cell_action`.
3. The final flush at `start_addr + 4` sees `frozen_size = 4 - 0 = 4 != 0` and
   marks **all 4 in-bounds bytes `[0..4)` as `frozen = true`**!

Meanwhile, `NewPermission::new` (`src/borrow_tracker/tree_borrows/mod.rs:138, 164-207`,
`Miri/TreeBorrows/RetagPolicy.lean:59, 77-92`) computes `outside_perm`
(the permission assigned to all offsets outside `[0, size)` in the same
allocation) from `Outside => ty_is_freeze` (`false`):

```rust
let frozen = match place {
    InsideFrozen => true,
    InsideUnsafeCell => false,
    Outside => ty_is_freeze,
};
```

Because `inside_perms` uses `visit_freeze_sensitive` whereas `outside_perm` uses
`ty_is_freeze`, retagging a pointer to `WithZstCell` (`(u32, UnsafeCell<()>)`)
produces an asymmetric `BorrowTree` node:

- **For `&(u32, UnsafeCell<()>)`**:
  - **In-bounds `[0..4)`**: `Permission::Frozen` (writing to `.0` through a raw
    pointer derived from `&WithZstCell` is **UB**, confirmed by
    `zst_unsafecell_inbounds_is_frozen_ub`).
  - **Out-of-bounds (`outsidePermission` outside `[0..4)`)**: `Permission::Cell`
    (writing to an adjacent field at `[4..8)` in the same allocation through a
    pointer derived from `&WithZstCell` via wrapping offset is **allowed**,
    confirmed by `zst_unsafecell_outside_perm_is_cell_ok`, whereas the same
    offset write from `&u32` fails with UB in
    `pure_freeze_outside_perm_is_frozen_ub`).
- **For unprotected `&mut (u32, UnsafeCell<()>)` (`RetagMode::Default`)**:
  - **In-bounds `[0..4)`**: `Permission::ReservedFrz { conflicted: false }`.
  - **Out-of-bounds (`outsidePermission`)**: `Permission::ReservedIM`.

**Architectural requirement for static layout extraction**: A static layout
extractor for Tree Borrows cannot infer `tyIsFreeze : Bool` from whether
`freezeRanges` covers `[0, size)` (nor can it skip `freezeRanges` when
`tyIsFreeze == false`). It must extract and store **both**
`freezeRanges : List FreezeRange` (to populate `inside_perms` over `[0, size)`)
and `tyIsFreeze : Bool` (to compute `outsidePermission`).

#### 1.3 Static Extraction Algorithm Over `rustc_middle::ty::layout::TyAndLayout`

Because `UnsafeCellVisitor` never reads memory, the exact `(tyIsFreeze, freezeRanges)`
pair for any sized `TyAndLayout<'tcx>` can be extracted statically at compile
time without runtime type traversal in Lean (proven equivalent to
`visitFreezeSensitive` in
[`support/LayoutFreezeAndScalarPairProbe.lean`](support/LayoutFreezeAndScalarPairProbe.lean)):

```rust
/// Static extraction over `rustc_middle::ty::layout::TyAndLayout<'tcx>` that produces the
/// exact `(ty_is_freeze, intervals)` used by Tree Borrows `NewPermission::new` and
/// `visit_freeze_sensitive`, where each interval is `(start_offset, size, frozen)`.
pub fn extract_static_freeze_intervals<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    root: TyAndLayout<'tcx>,
) -> (bool, Vec<(u64, u64, bool)>) {
    assert!(root.is_sized());
    let cx = LayoutCx::new(tcx, typing_env);
    let ty_is_freeze = root.ty.is_freeze(tcx, typing_env);
    let mut cur_offset: u64 = 0;
    let mut intervals: Vec<(u64, u64, bool)> = Vec::new();

    fn record_unsafe_cell(
        cur_offset: &mut u64,
        intervals: &mut Vec<(u64, u64, bool)>,
        cell_offset: u64,
        cell_size: u64,
    ) {
        assert!(cell_offset >= *cur_offset);
        let frozen_size = cell_offset - *cur_offset;
        if frozen_size != 0 {
            intervals.push((*cur_offset, frozen_size, true));
            *cur_offset += frozen_size;
        }
        if cell_size != 0 {
            intervals.push((*cur_offset, cell_size, false));
            *cur_offset += cell_size;
        }
    }

    fn walk<'tcx>(
        tcx: TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        cx: &LayoutCx<'tcx>,
        base_offset: u64,
        node: TyAndLayout<'tcx>,
        cur_offset: &mut u64,
        intervals: &mut Vec<(u64, u64, bool)>,
    ) {
        let is_unsafe_cell = node.ty.ty_adt_def().is_some_and(|def| def.is_unsafe_cell());
        if is_unsafe_cell {
            if node.size.bytes() != 0 {
                record_unsafe_cell(cur_offset, intervals, base_offset, node.size.bytes());
            }
            return;
        }
        if node.ty.is_freeze(tcx, typing_env) {
            return;
        }
        if matches!(node.fields, FieldsShape::Union(..))
            || matches!(node.variants, Variants::Multiple { .. })
        {
            if node.size.bytes() != 0 {
                record_unsafe_cell(cur_offset, intervals, base_offset, node.size.bytes());
            }
            return;
        }
        match node.variants {
            Variants::Empty => {}
            Variants::Multiple { .. } => unreachable!(),
            Variants::Single { index } => {
                let v_node = if matches!(node.ty.kind(), ty::Adt(def, _) if def.is_enum())
                    || matches!(node.ty.kind(), ty::Coroutine(..))
                {
                    node.for_variant(cx, index)
                } else {
                    node
                };
                match &v_node.fields {
                    FieldsShape::Primitive => {}
                    FieldsShape::Union(..) => {
                        if v_node.size.bytes() != 0 {
                            record_unsafe_cell(
                                cur_offset,
                                intervals,
                                base_offset,
                                v_node.size.bytes(),
                            );
                        }
                    }
                    &FieldsShape::Array { stride, count } => {
                        let elem = v_node.field(cx, 0);
                        if !elem.ty.is_freeze(tcx, typing_env) && elem.size.bytes() != 0 {
                            for i in 0..count {
                                walk(
                                    tcx,
                                    typing_env,
                                    cx,
                                    base_offset + i * stride.bytes(),
                                    elem,
                                    cur_offset,
                                    intervals,
                                );
                            }
                        }
                    }
                    FieldsShape::Arbitrary { offsets, in_memory_order } => {
                        for &field_idx in in_memory_order.iter() {
                            let f_offset = offsets[field_idx].bytes();
                            let f_node = v_node.field(cx, field_idx.as_usize());
                            walk(
                                tcx,
                                typing_env,
                                cx,
                                base_offset + f_offset,
                                f_node,
                                cur_offset,
                                intervals,
                            );
                        }
                    }
                }
            }
        }
    }

    walk(tcx, typing_env, &cx, 0, root, &mut cur_offset, &mut intervals);
    record_unsafe_cell(&mut cur_offset, &mut intervals, root.size.bytes(), 0);
    (ty_is_freeze, intervals)
}
```

For unsized pointees:

- If `root.ty.is_freeze(tcx, typing_env)` is `true` (covering `&str`, `&[u8]`,
  and any slice or unsized struct whose fields/elements are `Freeze`), the
  in-bounds interval is `[(0, dynamic_size, true)]`.
- If `root` is a slice `[Elem]` or unsized struct with a `[Elem]` tail at
  `tail_offset`, the fixed prefix `[0, tail_offset)` uses static intervals and
  each of the `len` runtime elements at `tail_offset + i * elem_stride` repeats
  `elem`'s static intervals.
- If `root` has a `dyn Trait` tail (`Ty::is_freeze` is `false` for `ty::Dynamic`),
  `walk_value` (`visitor.rs:106-113`, `FreezeVisitor.lean:94-97`) resolves the
  concrete sized pointee type from the vtable metadata and walks that concrete
  layout at `[tail_offset, tail_offset + dyn_size)`. Storing `(tyIsFreeze, freezeRanges)`
  in each vtable descriptor eliminates runtime layout traversal for `dyn Trait`
  as well.

---

### 2. `PointeeInfo`, `Unpin ∧ UnsafeUnpin`, and `Box<T>` / `Pin<&mut T>` Retag Semantics

`Basis: source + execution + derived`

#### 2.1 `TyAndLayout::pointee_info_at` Computation Across Pointer Carriers

In `compiler/rustc_middle/src/ty/layout.rs:1049-1226` (and
`compiler/rustc_abi/src/lib.rs:2359-2391`, `Miri/ABI/RuntimeLayout.lean:27-35`),
`ty_and_layout_pointee_info_at(this, cx, offset)` computes `Option<PointeeInfo>`
at offset `0` (with `let optimize = tcx.sess.opts.optimize != OptLevel::No;`) as
follows:

| Carrier Type `this.ty` | Offset | `pointee_info_at` Result (`optimize = true`) | Source Lines (`layout.rs`) |
| :--- | :--- | :--- | :--- |
| `*const T`, `*mut T`, `fn(...)` | `0` | `Some(PointeeInfo { safe: None, size: Size::ZERO, align: Align::ONE })` | `1059-1062` |
| `&T` (`T: Sized`) | `0` | `frozen = T.is_freeze`; `Some(PointeeInfo { safe: Some(PointerKind::SharedRef { frozen }), size: if frozen { sizeof(T) } else { 0 }, align: alignof(T) })` | `1063-1091` |
| `&mut T` (`T: Sized`) | `0` | `unpin = T.is_unpin && T.is_unsafe_unpin`; `Some(PointeeInfo { safe: Some(PointerKind::MutableRef { unpin }), size: if unpin { sizeof(T) } else { 0 }, align: alignof(T) })` | `1063-1096` |
| `&[T]` (wide reference, data ptr at `0`) | `0` | `layout_of([T])` has `size = 0, align = alignof(T)`; returns `SharedRef { frozen: [T].is_freeze }`, `size: Size::ZERO`, `align: alignof(T)` (and `None` at metadata offset) | `1063-1091, 1110-1215` |
| `&dyn Trait` (wide reference, data ptr at `0`) | `0` | `layout_of(dyn Trait)` has `size = 0, align = 1, is_freeze = false, is_unpin = true`; returns `SharedRef { frozen: false }`, `size: Size::ZERO`, `align: Align::ONE` | `1063-1091` |
| `Box<T, A>` (`#[rustc_box]`, `boxed_ty() == Some(T)`) | `0` | `unpin = T.is_unpin && T.is_unsafe_unpin`; `Some(PointeeInfo { safe: Some(PointerKind::Box { unpin, global: this.ty.is_box_global(tcx) }), size: if unpin { sizeof(T) } else { 0 }, align: alignof(T) })` | `1109-1126` |
| `Pin<&mut T>` | `0` | `Pin<Ptr>` is a `Variants::Single` struct with field `0` (`&mut T`) at offset `0`; recurses via `this.field(cx, 0).pointee_info_at(cx, 0)` $\rightarrow$ **identical to `&mut T`** (`PointerKind::MutableRef { unpin }`) | `1110-1215` |
| `Pin<Box<T, A>>` | `0` | Recurses into field `0` (`Box<T, A>`) $\rightarrow$ **identical to `Box<T, A>`** (`PointerKind::Box { unpin, global }`) | `1110-1215` |
| `Unique<T>` / `NonNull<T>` (standalone) | `0` | Recurses through `Unique<T> -> NonNull<T> -> *const T` (`ty::RawPtr`) $\rightarrow$ `Some(PointeeInfo { safe: None, size: Size::ZERO, align: Align::ONE })` | `1110-1215, 1059-1062` |
| `MaybeDangling<P>` (`is_like_maybe_dangling()`) | `0` | Recurses into `P`, then overwrites `safe = None` and `size = Size::ZERO` (preserving `align`) | `1217-1222` |

#### 2.2 Interaction of `Unpin` and `UnsafeUnpin`

Both `pointee_info_at` (`compiler/rustc_middle/src/ty/layout.rs:1081, 1117`) and
Tree Borrows `NewPermission::new` (`src/borrow_tracker/tree_borrows/mod.rs:133-134`,
`Miri/Interpreter/TypedRetag.lean:45-46`,
`Miri/TreeBorrows/RetagPolicy.lean:58`) compute the effective unpin
flag as:

$$\text{ty\_is\_unpin}(T) \;\triangleq\; T.\text{is\_unpin}() \;\land\; T.\text{is\_unsafe\_unpin}()$$

As documented in `compiler/rustc_middle/src/ty/util.rs:1223-1271` and
`compiler/rustc_ty_utils/src/common_traits.rs:29-38`, `Unpin` (`LangItem::Unpin`)
is a safe auto-trait (`PhantomPinned` is `!Unpin`), so user code can write a
safe `impl Unpin for Wrapper<T> {}` even when `Wrapper<T>` wraps an
`UnsafePinned<U>` field. `UnsafeUnpin` (`LangItem::UnsafeUnpin`) is an internal
unsafe auto-trait for which `UnsafePinned<T>` is `!UnsafeUnpin`. Requiring both
`is_unpin && is_unsafe_unpin` ensures that neither legacy `!Unpin` types
(`PhantomPinned`) nor `UnsafePinned<T>` wrappers receive mutable `noalias` or
Tree Borrows retagging unless the wrapper implements both `Unpin` and
`unsafe impl UnsafeUnpin`.

#### 2.3 Value-Validity Retagging of `&T`, `&mut T`, `Box<T>`, and `Pin<P>` Under Tree Borrows

In `rustc@8144389c895d`, `StatementKind::Retag` no longer exists; retagging is
performed by `ValidityVisitor::check_safe_pointer`
(`compiler/rustc_const_eval/src/interpret/validity.rs:622-644`,
`Miri/Interpreter/ValidityVisitor.lean:196-241`) whenever `validate_place`
runs with `reset_provenance_and_padding = true`:

- **Intra-function (`RetagMode::Default` and `RetagMode::TwoPhase`)**:
  - `Rvalue::Use(operand, with_retag)` (`step.rs:179-184`) sets
    `RetagMode::Default` when `with_retag.yes()` (or `RetagMode::None` when
    `false`) and invokes `copy_op`.
  - `Rvalue::Ref(_, borrow_kind, place)` (`step.rs:214-239`) sets
    `RetagMode::TwoPhase` (for two-phase borrows) or `RetagMode::Default` and
    invokes `write_immediate`.
- **Function entry (`RetagMode::FnEntry`)**:
  - `init_stack_frame` (`call.rs:599`, `Miri/Interpreter/Call.lean:281`)
    sets `RetagMode::FnEntry` while `pass_argument` copies each argument into
    the callee frame via `copy_op_allow_transmute`.
- **Why `Box<T, Global>`, `Pin<&mut T>`, and `Pin<Box<T, Global>>` retag in both
  `Default` and `FnEntry`**:
  - `ValidityVisitor` recursively walks all ADT fields (`validity.rs:1535`,
    `visitor.rs:139-155`).
  - When `ValidityVisitor` encounters a `#[rustc_box]` `Box<T, A>` (`def.is_box()`),
    `walk_value` projects two field levels (`Unique` at field `0`, `NonNull` at
    field `0`) to the inner `*const T` and calls `visit_box(box_ty, val)`
    (`visitor.rs:140-143`, `validity.rs:1327-1334`), which calls
    `check_safe_pointer(val, box_ty, PtrKind::Box)` $\rightarrow$
    `M::retag_ptr_value`. Standalone `Unique<T>` and `NonNull<T>` values do not
    satisfy `def.is_box()` and are never retagged. Custom-allocator boxes
    (`!ty.is_box_global(tcx)`) return `None` in `tb_retag_ptr_value`
    (`tree_borrows/mod.rs:481-497`, `TypedRetag.lean:185`).
  - Because `Pin<P>` is an ordinary single-variant struct, `walk_value` recurses
    into its `.pointer` field (`&mut T` or `Box<T, Global>`) and runs
    `check_safe_pointer` on that inner field.

The complete permission and protector matrix computed by `NewPermission::new`
(`src/borrow_tracker/tree_borrows/mod.rs:126-221`) and `RetagPolicy.create`
(`Miri/TreeBorrows/RetagPolicy.lean:52-92`) is:

| Pointer / Wrapper Kind | `ty_is_unpin` | `ty_is_freeze` | `RetagMode` | Retagged? | `freeze_perm` (`InsideFrozen`) | `unfreeze_perm` (`InsideUnsafeCell`) | `outside_perm` (`Outside`) | `protector` | Initial Parent Access on `[0, size)` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `&T` | `true` or `false` | `true` | `Default` | **Yes** | `Frozen` | `Cell` (unused) | `Frozen` | `None` | `Read` |
| `&T` | `true` or `false` | `false` | `Default` | **Yes** | `Frozen` | `Cell` | `Cell` | `None` | `Read` on `Frozen` ranges; **`None`** on `Cell` ranges |
| `&T` | `true` or `false` | `true` | `FnEntry` | **Yes** | `Frozen` | `Cell` (unused) | `Frozen` | `Some(StrongProtector)` | `Read` |
| `&T` | `true` or `false` | `false` | `FnEntry` | **Yes** | `Frozen` | `Cell` | `Cell` | `Some(StrongProtector)` | `Read` on `Frozen` ranges; **`None`** on `Cell` ranges |
| `&mut T` / `Pin<&mut T>` | **`false`** (`PhantomPinned`) | `true` or `false` | `Default`, `TwoPhase`, `FnEntry` | **No (`None`)** | — | — | — | `None` | None (no-op) |
| `Box<T, Global>` / `Pin<Box<T>>` | **`false`** (`Box<PhantomPinned>`) | `true` or `false` | `Default`, `FnEntry` | **No (`None`)** | — | — | — | `None` | None (no-op) |
| `&mut T` / `Pin<&mut T>` | `true` | `true` or `false` | `TwoPhase` | **Yes** | `ReservedIM` | `ReservedIM` | `ReservedIM` | `None` | **`None`** (`associated_access = None`) |
| `&mut T` / `Pin<&mut T>` | `true` | `true` | `Default` | **Yes** | `ReservedFrz { conflicted: false }` | `ReservedIM` (unused) | `ReservedFrz { conflicted: false }` | `None` | `Read` |
| `&mut T` / `Pin<&mut T>` | `true` | `false` (`UnsafeCell`) | `Default` | **Yes** | `ReservedFrz { conflicted: false }` | `ReservedIM` | `ReservedIM` | `None` | `Read` on `ReservedFrz` ranges; **`None`** on `ReservedIM` ranges |
| `Box<T, Global>` / `Pin<Box<T>>` | `true` | `true` | `Default` | **Yes** | `ReservedFrz { conflicted: false }` | `ReservedIM` (unused) | `ReservedFrz { conflicted: false }` | `None` | `Read` |
| `Box<T, Global>` / `Pin<Box<T>>` | `true` | `false` (`Box<UnsafeCell<u32>>`) | `Default` | **Yes** | `ReservedFrz { conflicted: false }` | `ReservedIM` | `ReservedIM` | `None` | `Read` on `ReservedFrz` ranges; **`None`** on `ReservedIM` ranges |
| `&mut T` / `Pin<&mut T>` | `true` | `true` or `false` | `FnEntry` (`implicit_writes = false`) | **Yes** | `ReservedFrz { conflicted: false }` | **`ReservedFrz { conflicted: false }`** | **`ReservedFrz { conflicted: false }`** | `Some(StrongProtector)` | `Read` on **all** `[0, size)` |
| `Box<T, Global>` / `Pin<Box<T>>` | `true` | `true` or `false` | `FnEntry` (`implicit_writes = false`) | **Yes** | `ReservedFrz { conflicted: false }` | **`ReservedFrz { conflicted: false }`** | **`ReservedFrz { conflicted: false }`** | **`Some(WeakProtector)`** | `Read` on **all** `[0, size)` |
| `&mut T` / `Box<T, Global>` | `true` | `true` or `false` | `FnEntry` (`implicit_writes = true`, `!no_writable`) | **Yes** | `Unique` | `Unique` | `ReservedFrz { conflicted: false }` | `Strong` (`&mut`) / `Weak` (`Box`) | `Write` on **all** `[0, size)` |

Three invariants in this table deserve particular attention:

1. **`!Unpin` (`PhantomPinned`) and `!UnsafeUnpin` disable all mutable and `Box`
   retags**: When `!ty_is_unpin` holds, neither `&mut T`, `Pin<&mut T>`,
   `Box<T>`, nor `Pin<Box<T>>` receives a new tag or protector on `Default` or
   `FnEntry` (`phantom_pinned_box_and_pin_mut_never_retagged_ok`).
2. **`Box<T, Global>` receives `WeakProtector` on `FnEntry`**: In
   `NewPermission::new` (`tree_borrows/mod.rs:213-219`, `RetagPolicy.lean:83-86`),
   `ref_mutability` is `None` for `Box`, selecting `ProtectorKind::WeakProtector`
   so the callee can deallocate the box before returning
   (`box_unpin_fn_entry_weak_protector_dealloc_ok`).
3. **Protected `FnEntry` retags never produce `ReservedIM`, even for
   `UnsafeCell`**: In `tree_borrows/mod.rs:193-197` (`RetagPolicy.lean:77-79`),
   the permission for `Mutable` and `Box` is chosen by:
   ```rust
   if is_protected || frozen {
       Permission::new_reserved_frz()
   } else {
       Permission::new_reserved_im()
   }
   ```
   Because `is_protected` is `true` on `FnEntry`, `is_protected || frozen` is
   unconditionally `true`. Thus `Box<UnsafeCell<u32>>` and `&mut UnsafeCell<u32>`
   receive `ReservedIM` on intra-function `Default` retags (surviving foreign
   writes through raw pointers before activation, as in
   `box_unsafecell_default_retag_allows_foreign_write_ok`), but receive
   **`ReservedFrz` with a protector** on `FnEntry` (causing a foreign write
   during the call to transition the tag to `Disabled` and trigger UB on a
   subsequent read, as in `box_unsafecell_fn_entry_is_reserved_frz_not_im_ub`).

---

### 3. `BackendRepr::ScalarPair` `bOffset`, Inter-Element Alignment Padding, and `Transmute`

`Basis: source + execution + derived`

#### 3.1 `bOffset` Computation in `rustc_abi` and `lean-miri`

In `LayoutData::scalar_pair` (`compiler/rustc_abi/src/layout/simple.rs:94-126`)
and `Miri.ABI.RuntimeLayout.scalarPairOffsets`
(`Miri/ABI/RuntimeLayout.lean:51-71`), the layout of
`BackendRepr::ScalarPair { a, b, b_offset }` (`compiler/rustc_abi/src/lib.rs:1852-1866`,
`Miri/ABI/Layout.lean:155-186`) is computed by:

```rust
let dl = cx.data_layout();
let b_align = b.default_align(dl).abi;
let align = a.default_align(dl).abi.max(b_align).max(dl.aggregate_align);
let b_offset = a.size(dl).align_to(b_align);
let size = (b_offset + b.size(dl)).align_to(align);
```

- Scalar `a` occupies `[0, a_size)`.
- Inter-element alignment padding occupies `[a_size, b_offset)` whenever
  `a_size < b_offset` (for example, `#[repr(C)] struct PairU8U32(u8, u32)` where
  `a_size = 1`, `b_align = 4`, `b_offset = 4`, and `[1..4)` is 3 bytes of
  inter-element padding; or `Result<u8, u64>` / `#[repr(C)] struct PairU8U64(u8, u64)`
  where `a_size = 1`, `b_align = 8`, `b_offset = 8`, and `[1..8)` is 7 bytes of
  inter-element padding).
- Scalar `b` occupies `[b_offset, b_offset + b_size)`.
- Trailing padding occupies `[b_offset + b_size, size)` whenever
  `b_offset + b_size < size` (note that for `repr(Rust)` `(u8, u64)`,
  `layout_of_univariant_biased` in `compiler/rustc_abi/src/layout.rs:1363-1401`
  places `u64` at offset `0` as `a` and `u8` at `b_offset = 8` as `b`, putting
  its 7 padding bytes in trailing position `[9..16)`).

#### 3.2 Fate of Padding Bytes Across Read, Write, Copy, and `Rvalue::Cast::Transmute`

1. **Reading a `ScalarPair` `Immediate` from memory
   (`read_immediate_from_mplace_raw`)**:
   In `compiler/rustc_const_eval/src/interpret/operand.rs:597-631`
   (`RuntimeLayout.lean:705-754`), reading a `ScalarPair` projects only
   `[0, a_size)` and `[b_offset, b_offset + b_size)` into
   `Immediate::ScalarPair(a_val, b_val)`. Bytes in `[a_size, b_offset)` and
   `[b_offset + b_size, size)` are never read and cannot be represented in
   `Immediate::ScalarPair`.
2. **Writing a `ScalarPair` `Immediate` to memory
   (`write_immediate_to_mplace_no_validate` and `write_immediate`)**:
   - In `write_immediate_to_mplace_no_validate` (`place.rs:795-821`,
     `RuntimeLayout.lean:756-797`), if `!will_later_validate && a_size + b_size != layout.size`,
     it calls `alloc.write_uninit_full()` on `[0, layout.size)` before writing
     `a_val` and `b_val`, resetting `[a_size, b_offset)` to `uninit`.
   - When `will_later_validate` is `true` (the Miri default), `write_immediate`
     (`place.rs:696-703`) follows `write_immediate_to_mplace_no_validate` with
     `validate_place(dest, recursive, reset_provenance_and_padding = true)`,
     whose `reset_padding` pass (`validity.rs:1113-1161`,
     `ValidityVisitor.lean:511-534`) calls `alloc.write_uninit(range)` on every
     non-data gap, resetting `[a_size, b_offset)` to `uninit`.
   - When spilling an `Immediate` local to stack memory via `force_allocation`
     (`place.rs:1066-1096`, `Place.lean:135-159`), `allocate_dyn` initializes
     the fresh allocation with `AllocInit::Uninit` before calling
     `write_immediate_to_mplace_no_validate`, so `[a_size, b_offset)` is `uninit`.
3. **Copying and `Rvalue::Cast::Transmute` (`copy_op_no_validate`,
   `copy_op_allow_transmute`, and `copy_op_inner`)**:
   In `cast.rs:192-218` (`Miri/Interpreter/Cast.lean:351-363`),
   `CastKind::Transmute` calls `copy_op_allow_transmute(&op, dest)`, which
   delegates to `copy_op_inner(src, dest, allow_transmute)` (`place.rs:912-1024`,
   `Place.lean:347-376`):
   - **Stage 1 (`copy_op_no_validate`, `place.rs:971-1024`)**: Computes
     `src_has_padding`:
     ```rust
     let src_has_padding = match src.layout().backend_repr {
         BackendRepr::Scalar(_) => false,
         BackendRepr::SimdVector { .. } => false,
         BackendRepr::ScalarPair { a: left, b: right, b_offset: _ } => {
             left.size(self) + right.size(self) != src.layout().size
         }
         BackendRepr::SimdScalableVector { .. } => false,
         BackendRepr::Memory { .. } => true,
     };
     ```
     When `src_has_padding` is `true` and `src` resides in memory (`Left(src_mplace)`),
     `copy_op_no_validate` performs a raw byte-for-byte `mem_copy` (`place.rs:1004-1010`),
     which temporarily copies any initialized bytes in `src`'s padding into `dest`.
   - **Stage 2 (Dual-layout `validate_place` in `copy_op_inner`, `place.rs:921-940`,
     `Place.lean:372-375`)**: Immediately after `copy_op_no_validate`, when
     `M::enforce_validity(self, dest.layout())` is `true`, `copy_op_inner` runs:
     ```rust
     if src.layout().ty != dest.layout().ty {
         self.validate_place(
             &dest.transmute(src.layout(), self)?,
             recursive,
             /*reset_provenance_and_padding*/ true,
         )?;
     }
     self.validate_place(
         dest,
         recursive,
         /*reset_provenance_and_padding*/ true,
     )?;
     ```
     Because `reset_provenance_and_padding` is `true` in **both** passes:
     - Transmuting **`src: [u8; 8]` (or `u64`) $\rightarrow$
       `dest: PairU8U32(u8, u32)`** runs the second `validate_place` at
       `PairU8U32`, which resets `dest[1..4]` to `uninit`
       (`transmute_init_bytes_to_scalar_pair_resets_padding_to_uninit`).
     - Transmuting **`src: PairU8U32(u8, u32)` (with `[1..4)` explicitly
       initialized in memory via a raw pointer) $\rightarrow$
       `dest: [MaybeUninit<u8>; 8]`** runs the first `validate_place` on `dest`
       viewed at `src.layout()` (`PairU8U32`), which resets `dest[1..4]` to
       `uninit` (`transmute_scalar_pair_with_init_padding_to_maybe_uninit_resets_padding`).
       And if `dest` is `[u8; 8]` or `u64`, the second `validate_place` at
       `dest.layout()` immediately fails with `Ub(InvalidUninitBytes)` because
       `dest[1..4]` was just reset to `uninit`.

## Boundaries

- **Variant-dependent padding in `Variants::Multiple` enums during
  `reset_padding` vs. `visit_freeze_sensitive` (`known not to apply`)**: The
  finding that `visit_freeze_sensitive` does not read the discriminant of a
  `Variants::Multiple` enum does **not** extend to `ValidityVisitor::walk_value`
  during `validate_place` / `reset_padding`. In `visitor.rs:157-184`
  (`ValidityVisitor.lean:456-480`), `ValidityVisitor` reads the active
  discriminant via `read_discriminant`, adds the tag field to `data_bytes`,
  projects to the active variant, and marks bytes belonging only to inactive
  larger variants as padding (`uninit`) on typed copies and transmutes.
- **In-place function argument protection (`protect_in_place_function_argument`)
  (`not examined` in execution probes)**: In `call.rs:443-445` (`Call.lean:222`,
  `TypedRetag.lean:192-201`), when a `Move(place)` argument is passed via
  `FnArg::InPlace(mplace)`, Miri calls `protect_in_place_function_argument(mplace)`
  after copying the argument to the callee local, retagging the caller's memory
  place (`ReservedFrz` with `Read` access; `rust-lang/miri`'s `tb_protect_place`
  in `src/borrow_tracker/tree_borrows/mod.rs:427` uses `ProtectorKind::WeakProtector`,
  whereas `lean-miri`'s `MachineHooks.protectionPolicy` in
  `Miri/Interpreter/MachineHooks.lean:352-361` uses `create ⟨true, true, true⟩ .Mutable .FnEntry ⟨false, false⟩`,
  which sets `some .StrongProtector`) and writing `uninit` to `mplace`.
- **Custom-allocator `Box<T, A>` (`known not to apply`)**: `Box<T, A>` where
  `!ty.is_box_global(tcx)` (`A != alloc::alloc::Global`) returns `None` in
  `tb_retag_ptr_value` (`src/borrow_tracker/tree_borrows/mod.rs:481-497`,
  `TypedRetag.lean:185`) and is never retagged under Tree Borrows.
- **Stacked Borrows (`not examined`)**: All borrow-tracker findings in this
  report apply to Tree Borrows (`-Zmiri-tree-borrows`), not Stacked Borrows.

## Evidence

### 1. Primary Source Coordinates (`source`)

- **`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`**:
  - `compiler/rustc_abi/src/lib.rs:224-226` (`ReprOptions::inhibit_enum_layout_opt`),
    `1852-1866` (`BackendRepr::ScalarPair`), `2359-2391` (`PointerKind`,
    `PointeeInfo`).
  - `compiler/rustc_abi/src/layout.rs:90-101, 360, 378` (uninhabited 1-ZST
    variant pruning and `Variants::Single` vs. `Variants::Multiple`),
    `999-1026, 1363-1401` (`ScalarPair` construction).
  - `compiler/rustc_abi/src/layout/simple.rs:94-126` (`LayoutData::scalar_pair`
    and `b_offset = a.size(dl).align_to(b_align)`).
  - `compiler/rustc_middle/src/ty/layout.rs:1049-1226`
    (`ty_and_layout_pointee_info_at`).
  - `compiler/rustc_middle/src/ty/util.rs:1183-1221` (`Ty::is_freeze`,
    `Ty::is_trivially_freeze`), `1223-1271` (`Ty::is_unsafe_unpin`,
    `Ty::is_unpin`).
  - `compiler/rustc_ty_utils/src/common_traits.rs:25-38, 47-56`
    (`is_freeze_raw`, `is_unsafe_unpin_raw`, `is_unpin_raw`).
  - `compiler/rustc_const_eval/src/interpret/visitor.rs:81-188`
    (`ValueVisitor::walk_value`).
  - `compiler/rustc_const_eval/src/interpret/operand.rs:597-631`
    (`read_immediate_from_mplace_raw`).
  - `compiler/rustc_const_eval/src/interpret/place.rs:688-706`
    (`write_immediate`), `767-825` (`write_immediate_to_mplace_no_validate`),
    `912-1051` (`copy_op_inner`, `copy_op_no_validate`,
    `copy_op_allow_transmute`), `1066-1096` (`force_allocation`).
  - `compiler/rustc_const_eval/src/interpret/validity.rs:560-682`
    (`check_safe_pointer`), `922-925, 1113-1161` (`reset_padding`), `1327-1334`
    (`visit_box`), `1609-1626` (`validate_place_internal`).
  - `compiler/rustc_const_eval/src/interpret/step.rs:179-184, 214-239`
    (`Rvalue::Use`, `Rvalue::Ref`).
  - `compiler/rustc_const_eval/src/interpret/call.rs:441-445, 599`
    (`RetagMode::FnEntry` in `init_stack_frame`).
  - `compiler/rustc_const_eval/src/interpret/cast.rs:192-218`
    (`CastKind::Transmute`).
- **`rust-lang/miri` at `7fa591d7d4dd9af8154becbc8332f8096f8323b1`**:
  - `src/helpers.rs:469-539` (`visit_freeze_sensitive`), `542-613`
    (`UnsafeCellVisitor`).
  - `src/borrow_tracker/tree_borrows/mod.rs:126-221` (`NewPermission::new`),
    `342-363` (`tb_reborrow` `inside_perms`), `427` (`tb_protect_place`),
    `474-507` (`tb_retag_ptr_value`).
- **`proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`**:
  - `Miri/TreeBorrows/FreezeVisitor.lean:49-136`
  - `Miri/TreeBorrows/FreezeMap.lean:45-53`
  - `Miri/TreeBorrows/RetagPolicy.lean:52-92`
  - `Miri/TreeBorrows/RetagPipeline.lean:178-197`
  - `Miri/Interpreter/MachineHooks.lean:352-361`
  - `Miri/Interpreter/TypedRetag.lean:42-72, 173-201`
  - `Miri/Interpreter/ValidityVisitor.lean:196-241, 419-425, 456-480, 511-534`
  - `Miri/ABI/Layout.lean:155-186`
  - `Miri/ABI/RuntimeLayout.lean:27-71, 705-797`
  - `Miri/Interpreter/Place.lean:135-159, 181-192, 347-376`
  - `Miri/Interpreter/Cast.lean:351-363`

### 2. Preserved Miri Execution Probe (`execution`)

Preserved in [`support/miri_layout_probe/Cargo.toml`](support/miri_layout_probe/Cargo.toml)
and [`support/miri_layout_probe/src/lib.rs`](support/miri_layout_probe/src/lib.rs)
and executed on `2026-11-12` under `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 2026-11-11)`
with `miri 0.1.0 (3ef0c22cdb 2026-11-11)`:

- **8 passing non-UB tests** (`MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test`):
  1. `struct_unsafecell_field_write_ok`
  2. `multivariant_enum_mutate_frozen_payload_and_discriminant_ok`
  3. `repr_c_uninhabited_variant_forces_variants_multiple_cell_ok`
  4. `union_with_unsafecell_entire_size_is_cell_ok`
  5. `zst_unsafecell_outside_perm_is_cell_ok`
  6. `box_unpin_fn_entry_weak_protector_dealloc_ok`
  7. `box_unsafecell_default_retag_allows_foreign_write_ok`
  8. `phantom_pinned_box_and_pin_mut_never_retagged_ok`
- **9 ignored expected-UB tests** (each verified individually via
  `MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test -- --ignored --exact <test_name>`):
  1. `struct_padding_write_via_shared_ref_is_ub` (`write access ... forbidden ... state Frozen`)
  2. `struct_trailing_padding_write_via_shared_ref_is_ub` (`write access ... forbidden ... state Frozen`)
  3. `single_inhabited_variant_enum_freezes_frozen_field_ub` (`write access ... forbidden ... state Frozen`)
  4. `union_all_freeze_write_is_ub` (`write access ... forbidden ... state Frozen`)
  5. `zst_unsafecell_inbounds_is_frozen_ub` (`write access ... forbidden ... state Frozen`)
  6. `pure_freeze_outside_perm_is_frozen_ub` (`write access ... forbidden ... state Frozen`)
  7. `box_unsafecell_fn_entry_is_reserved_frz_not_im_ub` (`read access ... forbidden ... state Disabled`)
  8. `transmute_init_bytes_to_scalar_pair_resets_padding_to_uninit` (`reading memory at alloc[0x1..0x2], but memory is uninitialized`)
  9. `transmute_scalar_pair_with_init_padding_to_maybe_uninit_resets_padding` (`using uninitialized data, but this operation requires initialized memory`)

### 3. Preserved Lean 4 Mechanization Probe (`execution` + `derived`)

Preserved in
[`support/LayoutFreezeAndScalarPairProbe.lean`](support/LayoutFreezeAndScalarPairProbe.lean)
and verified on `2026-11-12` on both Lean 4 `v4.28.0-rc1`
(`3b0f2862196c6a8af9eb0025ee650252694013dd`) and Lean 4 `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) with zero `sorryAx` axioms across
all 10 theorems:

- `FreezeRetagScalarPairProbe.thm_mixed_struct_and_trailing_padding`
- `FreezeRetagScalarPairProbe.thm_multi_variant_vs_single_inhabited_enum`
- `FreezeRetagScalarPairProbe.thm_union_unsafecell_vs_all_freeze`
- `FreezeRetagScalarPairProbe.thm_zst_unsafecell_inbounds_frozen`
- `FreezeRetagScalarPairProbe.thm_inbounds_vs_outside_permission_divergence`
- `FreezeRetagScalarPairProbe.thm_not_unpin_skips_mutable_and_box_retag`
- `FreezeRetagScalarPairProbe.thm_box_and_mut_unsafecell_default_vs_fn_entry`
- `FreezeRetagScalarPairProbe.thm_pointee_info_pin_and_unique`
- `FreezeRetagScalarPairProbe.thm_scalar_pair_offsets_and_padding`
- `FreezeRetagScalarPairProbe.thm_pair_u8_u32_padding_stripped_to_uninit`

## Revalidation

1. **Rerun the Miri execution probe**:
   Copy [`support/miri_layout_probe/`](support/miri_layout_probe/) to a
   temporary directory (so `target/` and `Cargo.lock` are not created inside the
   report package) and run:
   ```bash
   cp -r reports/rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute/support/miri_layout_probe /tmp/miri_layout_probe
   MIRIFLAGS="-Zmiri-tree-borrows" cargo +nightly miri test --manifest-path /tmp/miri_layout_probe/Cargo.toml
   ```
   Verify that all 8 non-ignored tests pass, and run each of the 9 `#[ignore]`
   tests with `-- --ignored --exact <name>` to verify that Miri rejects them
   with the expected Tree Borrows or uninitialized-memory UB diagnostic.
2. **Rerun the Lean 4 mechanization probe**:
   ```bash
   lean reports/rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute/support/LayoutFreezeAndScalarPairProbe.lean
   ```
   Verify that `lean` exits with status `0` and that `#print axioms` outputs
   only `[propext]` or `does not depend on any axioms` (never `sorryAx`).
3. **Diff upstream implementation regions when upgrading `rustc` or Miri**:
   - Diff `src/helpers.rs` (`visit_freeze_sensitive`, `UnsafeCellVisitor`) and
     `src/borrow_tracker/tree_borrows/mod.rs` (`NewPermission::new`,
     `tb_reborrow`, `tb_retag_ptr_value`) in `rust-lang/miri`.
   - Diff `compiler/rustc_middle/src/ty/layout.rs`
     (`ty_and_layout_pointee_info_at`), `compiler/rustc_abi/src/layout/simple.rs`
     (`LayoutData::scalar_pair`), and
     `compiler/rustc_const_eval/src/interpret/{place.rs,validity.rs,operand.rs}`
     in `rust-lang/rust`.
