# Slice-Scaled Tree Borrows Range Permissions, Six-State Lattices, and `UnsafeCell` Freeze Visitor Soundness

## Summary

Tree Borrows (`rust-lang/miri`, Villani et al., PLDI 2025) enforces fine-grained interior-mutability aliasing rules across compound Rust allocations by combining a type- and layout-driven freeze visitor (`visit_freeze_sensitive`), a six-variant (seven-state) per-location permission lattice (`Cell`, `ReservedFrz { conflicted }`, `ReservedIM`, `Unique`, `Frozen`, `Disabled`), `!Unpin` retag omission (`Pin<&mut T>`), and range-deduplicated byte maps (`DedupRangeMap`). Three foundational mechanisms govern formal verification of Rust crates against this model in Lean 4:

1. **Conservative `Freeze` Partitioning (`visit_freeze_sensitive` + `ValueVisitor::walk_value`):** Rather than descending unconditionally into runtime payloads, Miri stops at `UnsafeCell<T>` and `type_is_freeze` leaves, marks entire non-`Freeze` `Union`s and `Variants::Multiple` enums/coroutines non-frozen *without reading discriminant memory*, unpacks `ty::Dynamic` vtables, and projects `Box<T, A>` solely through its allocator field without dereferencing the heap pointer.
2. **Protector-Sound Six-Variant Lattice and SIFA:** `Cell` forms an isolated fixed point immune to all foreign and local accesses (`associated_access = None`, protecting against spurious data-race checks on `&Atomic*`/`&Mutex` retags and exempting `Cell` from `StrongProtector` deallocation UB), whereas function-entry protected `&mut UnsafeCell<T>` receives `ReservedFrz { conflicted: false }` instead of `ReservedIM` so LLVM `noalias` remains sound. For `!Unpin || !UnsafeUnpin` pointees, mutable-reference and `Box` retagging returns early as a no-op (`NewPermission::new` returns `None`), preventing false protector UB on self-referential pinned structs.
3. **$O(1)$ Slice-Scaled Range Permissions (`RangeCellSlot`) vs. `DedupRangeMap` Fragmentation:** Because `DedupRangeMap::iter_mut` never coalesces newly mutated intervals backward against `v[first_idx - 1]`, elementwise visitor traversal over `&[Cell<u8>; 4096]` (`Cell::as_slice_of_cells`) or `&mut [UnsafeCell<u8>; 4096]` fragments both `inside_perms` and `Tree::locations` into `4,096` separate 1-byte segments (`45,070` `find_offset` binary-search steps per map, plus `4,096` `perform_access` tree traversals when `associated_access = Some(Read)`). A Lean 4 verification kernel can eliminate this $O(N)$ / $O(N^2)$ blowup via a slice-scaled **`RangeCellSlot`** descriptor supporting $O(1)$ disjointness, sub-slice splitting/joining, element focus, and a proved transition homomorphism back to bytewise `LocationState`.

## Applicability

These findings apply to **Tree Borrows** as implemented in `rust-lang/miri` (`0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`) over **rustc** `ValueVisitor` and standard-library `Cell`/`Pin` types (`rust-lang/rust` `ec65cd52bba13d491ff65c9d218b39753755c84a`), evaluated against the PLDI 2025 operational formalization (DOI `10.1145/3735592`; artifact DOI `10.5281/zenodo.15002703`) and **Lean 4** separation-logic resource representations (`leanprover/lean4` `44db45ca210151a9fc25f10b8d7fa4535856680f`), contrasted with branded linear cells in `verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`).

Observations of Miri's `visit_freeze_sensitive` reflect `precise_interior_mut = true` (default Tree Borrows configuration; when `false`, Miri degrades to an allocation-wide `DedupRangeMap::new(ptr_size, loc_state(ty_is_freeze))` at `tree_borrows/mod.rs:342–345`). Related corpus entries cover adjacent pieces without duplicating this slice-scaled formalization: `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute` documents `visit_freeze_sensitive` mechanics in `rustc`/Miri; `tree-borrows-two-stage-protector-release-and-reborrow-contracts` covers protector release and reborrow rules; `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses` addresses compiler scalar replacement around `UnsafeCell`; `self-referential-unpin-coroutine-field-slicing-and-sroa` analyzes pinned coroutines; and `lean-absbyte-typedat-lenses-and-nondeterministic-alloc-scaling` analyzes byte-level Lean 4 lenses.

## Findings

### 1. Freeze-Sensitive Layout Visitor (`visit_freeze_sensitive`, `UnsafeCellVisitor`, and `ValueVisitor::walk_value`)

Basis: source + derived

When retagging a reference or `Box` of size `ptr_size` under `precise_interior_mut = true`, Miri initializes `perms_map` to `Disabled` (`src/borrow_tracker/tree_borrows/mod.rs:348–353`) and invokes `ecx.visit_freeze_sensitive(place, ptr_size, |range, frozen| ...)` (`src/borrow_tracker/tree_borrows/mod.rs:355–361`, implemented in `src/helpers.rs:468–612` using `rustc_const_eval`'s `ValueVisitor::walk_value` at `compiler/rustc_const_eval/src/interpret/visitor.rs:81–188`).

#### 1.1 Monotonic Cursor Partitioning and Trailing Flush

`visit_freeze_sensitive` maintains a monotonic address cursor `cur_addr` initialized to `start_addr = place.ptr().addr()` (`src/helpers.rs:485–510`). Every time `UnsafeCellVisitor` invokes `unsafe_cell_action(ptr, unsafe_cell_size)`:
- It asserts `unsafe_cell_addr >= cur_addr` (`helpers.rs:493`) and emits the gap `[cur_addr - start_addr, unsafe_cell_addr - start_addr)` with `frozen = true` (`Part::InsideFrozen`) if non-empty (`helpers.rs:496–498`).
- It emits `[unsafe_cell_addr - start_addr, unsafe_cell_size)` with `frozen = false` (`Part::InsideUnsafeCell`) if non-empty (`helpers.rs:501–506`).
- **Zero-Sized `UnsafeCell` Short-Circuit (`helpers.rs:524`):** Before calling `unsafe_cell_action`, the wrapper checks `if unsafe_cell_size != Size::ZERO`; an empty `UnsafeCell<[u8; 0]>` emits nothing and skips even the `>= cur_addr` check.
- **Trailing `Frozen` Flush (`helpers.rs:535`):** After `visitor.visit_value(place)?` returns, `visit_freeze_sensitive` invokes `unsafe_cell_action(&place.ptr().wrapping_offset(size, ecx), Size::ZERO)`, flushing all trailing frozen fields and trailing compiler padding bytes with `frozen = true`.

#### 1.2 Exact Guard Priority in `UnsafeCellVisitor::visit_value` and `walk_value`

`UnsafeCellVisitor::visit_value` (`src/helpers.rs:561–602`) and `ValueVisitor::walk_value` (`compiler/rustc_const_eval/src/interpret/visitor.rs:81–188`) classify layouts in a strict six-branch priority sequence:

1. **Direct `UnsafeCell` Lang Item (`helpers.rs:563–570`):** Matches `ty::Adt(adt, _)` against `tcx.lang_items().unsafe_cell_type()`. Stops recursion immediately and invokes `unsafe_cell_action` over the whole `UnsafeCell` byte span (`frozen = false`). Notice this wraps padding *inside* `UnsafeCell<T>` as `InsideUnsafeCell` too.
2. **Static `Freeze` Pruning (`helpers.rs:571–573`):** If `self.ecx.type_is_freeze(v.layout.ty)` holds, returns `Ok(())` without touching `cur_addr`. Consequently, contiguous `Freeze` fields and surrounding struct padding coalesce automatically into the next `frozen = true` span!
3. **Non-`Freeze` `FieldsShape::Union` (`helpers.rs:574–576`):** Any union whose `ty` is not `Freeze` triggers `unsafe_cell_action(v)` over the entire union span (`frozen = false`), because statically determining which union field is active without tracking field tags is impossible.
4. **Non-`Freeze` `Variants::Multiple` (`helpers.rs:584–594`):** Multi-variant enums and coroutines whose payload contains an `UnsafeCell` conservatively mark the *entire* enum/coroutine `frozen = false` **without reading the discriminant from memory**. As `helpers.rs:588–590` explains, reading the discriminant during retag would itself emit a borrow-tracker memory read (causing cyclic recursion or uninitialized-byte UB when retagging `&mut MaybeUninit<Enum>`). By contrast, a single-inhabited-variant enum (`Variants::Single` when remaining variants are uninhabited, `helpers.rs:581–583`) falls through to field projection.
5. **Trait Objects and `Box<T, A>` (`visitor.rs:88–128`):**
   - `ty::Dynamic` (`visitor.rs:88–98`): Unpacks the vtable metadata via `unpack_dyn_trait` to obtain the concrete dynamic layout and recurses via `visit_field(v, 0, &inner_mplace)`.
   - `Box<T, A>` (`def.is_box()`, `visitor.rs:104–128`): Calls `project_to_ptr_in_box(v)` producing `(raw_ptr, alloc)`, invokes the default no-op `visit_box` (never dereferencing across the heap pointer!), and recurses **solely on field `1` (the allocator `alloc`)**. Additionally, `tb_retag_ptr_value` (`tree_borrows/mod.rs:482–497`) dispatches `ty.is_box_global` into `NewPermission::new(pointee, None, ...)` while returning `None` (no retag) for boxes with custom allocators (`!ty.is_box_global && ty.is_box()`).
6. **Memory-Order Product & Array Projection (`visitor.rs:148–159`):** `FieldsShape::Arbitrary { in_memory_order, .. }` iterates fields in **physical memory offset order** (`in_memory_order`), preserving the monotonic cursor invariant `unsafe_cell_addr >= cur_addr` even when `repr(Rust)` reorders fields relative to source declaration order. `FieldsShape::Array` iterates indices `0..len` sequentially.

```rust
// Classification summary for #[repr(C)] struct Mixed (size = 12):
struct Mixed {
    pure: u32,         // 0..4:  type_is_freeze = true  -> Part::InsideFrozen
    cell: Cell<u32>,   // 4..8:  is_unsafe_cell = true  -> Part::InsideUnsafeCell
    flag: u8,          // 8..9:  type_is_freeze = true  -> Part::InsideFrozen
    // 9..12: 3 bytes trailing padding -> flushed by helpers.rs:535 as Part::InsideFrozen
}
```

At retag of `&Mixed`, `visit_freeze_sensitive` skips `pure` (`type_is_freeze = true`) without advancing `cur_addr`, invokes `unsafe_cell_action` on `cell` (`4..8`)—emitting `[0, 4)` with `frozen = true` and `[4, 8)` with `frozen = false`—skips `flag` (`8..9`), and triggers the end-of-place flush (`helpers.rs:535`) emitting `[8, 12)` with `frozen = true`, folding `flag` and the 3 trailing padding bytes into a single frozen span.

---

### 2. Six-Variant (Seven-State) Permission Lattice, Protector Interaction, and SIFA

Basis: normative + source + execution

Tree Borrows replaces Stacked Borrows' linear tag stack with a per-allocation tree whose nodes maintain a six-variant enum (`PermissionPriv` in `rust-lang/miri`, `src/borrow_tracker/tree_borrows/perms.rs:10–53`; Villani et al., PLDI 2025, DOI `10.1145/3735592`):
- `Cell` — shared interior-mutable permission (`SharedReadWrite`),
- `ReservedFrz { conflicted: Bool }` — deferred-activation mutable borrow on frozen data (2 states: `conflicted = false | true`),
- `ReservedIM` — deferred-activation mutable borrow on interior-mutable data (unprotected only),
- `Unique` — activated exclusive writable pointer,
- `Frozen` — shared immutable pointer,
- `Disabled` — invalidated pointer.

#### 2.1 Complete Transition Matrix (`transition::perform_access`, `perms.rs:135–233`)

Exhaustively checking all $7 \times 2 \times 2 \times 2 = 56$ tuples `(old_state, kind, rel_pos, protected)` against `perms.rs:135–233` verifies `54` valid domain transitions (including UB outcomes) and `2` explicit invariant-panic assertions (`assert!(!protected)` on `ReservedIM` under foreign read or foreign write):

| Current State | `ChildRead` (`prot = F / T`) | `ChildWrite` (`prot = F / T`) | `ForeignRead` (`prot = F / T`) | `ForeignWrite` (`prot = F / T`) | `associated_access` | `SIFA` (`prot = F / T`) |
|---|---|---|---|---|---|---|
| **`Cell`** | `Cell` / `Cell` | `Cell` / `Cell` | `Cell` / `Cell` | `Cell` / `Cell` | `None` | `Write` / `Write` |
| **`ReservedFrz(false)`** | `ReservedFrz(false)` / same | `Unique` / `Unique` | `ReservedFrz(false)` / `ReservedFrz(true)` | `Disabled` / `Disabled` (UB if accessed) | `Some(Read)` | `Read` / `None` |
| **`ReservedFrz(true)`** | `ReservedFrz(true)` / same | `Unique` / **UB** | `ReservedFrz(true)` / same | `Disabled` / `Disabled` (UB if accessed) | `Some(Read)` | `Read` / `Read` |
| **`ReservedIM`** | `ReservedIM` / `ReservedIM` | `Unique` / `Unique` | `ReservedIM` / *panic* | `ReservedIM` / *panic* | `Some(Read)` | `Write` / *panic* |
| **`Unique`** | `Unique` / `Unique` | `Unique` / `Unique` | `Frozen` / `Disabled` (UB if accessed) | `Disabled` / `Disabled` (UB if accessed) | `Some(Write)` | `None` / `None` |
| **`Frozen`** | `Frozen` / `Frozen` | **UB** / **UB** | `Frozen` / `Frozen` | `Disabled` / `Disabled` (UB if accessed) | `Some(Read)` | `Read` / `Read` |
| **`Disabled`** | **UB** / **UB** | **UB** / **UB** | `Disabled` / `Disabled` | `Disabled` / `Disabled` | `Some(Read)` | `Write` / `Write` |

#### 2.2 Lattice Structure and Four Soundness Invariants

1. **Reachability Partial Order (`perms.rs:58–89`):** Transitive closure over all valid transitions matches `PermissionPriv::partial_cmp` across all $7 \times 7 = 49$ pairs (`20` comparable pairs): `Cell` is completely incomparable to all other states; `ReservedIM` is incomparable to `ReservedFrz { .. }` (`NewPermission::new` selects initial variants statically); and remaining states satisfy `ReservedFrz(false) < ReservedFrz(true) < Unique < Frozen < Disabled` (`ReservedIM < Unique` as well).
2. **`FnEntry` Protected `&mut UnsafeCell` Escalates to `ReservedFrz` (`tree_borrows/mod.rs:185–204`, `perms.rs:22–24`):**
   ```rust
   // tree_borrows/mod.rs:185-191 (Mutable; identical logic for Box at 198-204):
   } else if is_protected || frozen {
       // We also use this for protected `&mut UnsafeCell` as otherwise adding
       // `noalias` would not be sound.
       Permission::new_reserved_frz()
   } else {
       Permission::new_reserved_im()
   }
   ```
   Because LLVM marks `&mut T` arguments `noalias` for the duration of the call even if `T` contains `UnsafeCell<U>`, a foreign write before function exit must trigger UB—so `mode == RetagMode::FnEntry` forces `ReservedFrz { conflicted: false }` instead of `ReservedIM`. Consequently, protected `ReservedIM` can never be constructed (`assert!(!protected)` in `foreign_read`/`foreign_write`).
3. **`Cell` Exemptions (`perms.rs:313–315`, `tree.rs:574–576`):**
   - `Cell.associated_access()` returns `None` (`perms.rs:315`) rather than `Some(Read)`, so reborrowing `&UnsafeCell<T>` (including `&AtomicUsize` or `&Mutex<T>`) does not emit a non-atomic read on parent tags or the data-race vector clock (`mod.rs:369–419`), preventing spurious data races in concurrent types!
   - During deallocation (`tree.rs:572–581`), `StrongProtector` triggers `ProtectedDealloc` UB *unless* `!perm.permission.is_cell()` (so dropping memory through an interior-mutable field while a `&Cell` argument protector exists does not cause false deallocation UB, `rust-lang/rust#55005`) or `!perm.accessed`.
4. **Lazy `Outside` Bounds and the `accessed` Bit (`mod.rs:170`, `tree.rs:49, 143–159`):**
   Bytes outside `ptr_size` receive `outside_perm` (`ReservedIM` if `!ty_is_freeze` and unprotected, `ReservedFrz` if frozen or protected on `&mut`, `Cell` if `&!Freeze`, `Frozen` if `&Freeze`), marked **`accessed = false`** (`LocationState::new_non_accessed`). Only locations where `self.accessed == true` trigger `TransitionError::ProtectedDisabled` when transitioning to `Disabled` (`tree.rs:157`). This allows two protected mutable references pointing to disjoint slices of one allocation (`split_at_mut`) to write their respective slices without colliding on unaccessed sibling ranges.
5. **Strongest Idempotent Foreign Access (`SIFA`, `foreign_access_skipping.rs:29–95`, `tree.rs:477–517`):**
   Every node records `IdempotentForeignAccess` (`None < Read < Write`) satisfying the global tree invariant that every child's SIFA is at least as strong as its parent's. Repeated foreign accesses skip subtrees in $O(1)$ once saturated (`skip_if_known_noop`, `tree.rs:182–233`), and `new_child` restores the invariant bottom-up via `update_idempotent_foreign_access_after_retag` (`tree.rs:477–517`).

---

### 3. `!Unpin` and `!UnsafeUnpin` Retag Omission for `Pin<&mut T>` and `Box<T>`

Basis: normative + source + derived

In Rust's pinning contract (`rust-lang/rust`, `library/core/src/pin.rs:950–1093`), `Pin<Ptr>` (`#[repr(transparent)]`, `pin.rs:1088–1093`) has identical ABI to `Ptr`, yet self-referential `!Unpin` structs (such as `async fn` futures) routinely hold internal raw pointers referencing sibling fields inside the same `Pin<&mut Self>` allocation:

```rust
use std::marker::PhantomPinned;
use std::pin::Pin;

struct SelfRef {
    data: u32,
    ptr: *const u32,
    _pin: PhantomPinned, // !Unpin
}

unsafe fn pin_self_referential(mut s: Pin<&mut SelfRef>) -> u32 {
    let data_ptr: *const u32 = &s.as_ref().get_ref().data;
    let unpinned = s.as_mut().get_unchecked_mut();
    unpinned.ptr = data_ptr;
    unpinned.data = 42;
    *unpinned.ptr // Dereferences internal pointer aliased with `s`!
}
```

If `s` were retagged with `StrongProtector` and `Unique`/`ReservedFrz` like an ordinary `&mut`, writing `unpinned.data = 42` followed by reading `*unpinned.ptr` across call boundaries (where `ptr` derives from an earlier tag or sibling provenance) would risk immediate `Disabled` / `ProtectedDisabled` UB—mirroring why `pin.rs:1065–1067` notes `Pin<&mut T>` cannot carry standard `&mut T` `noalias` guarantees when `T: !Unpin`.

#### Exact Upstream Rule (`tree_borrows/mod.rs:136–155`)

```rust
let ty_is_unpin = pointee.is_unpin(*cx.tcx, cx.typing_env())
    && pointee.is_unsafe_unpin(*cx.tcx, cx.typing_env());
...
if matches!(ref_mutability, Some(Mutability::Mut) | None if !ty_is_unpin) {
    // Mutable reference / Box to pinning type: retagging is a NOP.
    // FIXME: with `UnsafePinned`, this should do proper per-byte tracking.
    return None;
}
```

Three subtleties govern formal verification of `Pin`:
1. **Both `is_unpin` AND `is_unsafe_unpin` Are Checked (`mod.rs:136–137`):** A type only counts as `ty_is_unpin` if it satisfies both `Unpin` and the internal `UnsafeUnpin` marker.
2. **Applies to `Mutable` and `Box`, NOT `Shared`:** When `ref_mutability == Some(Mutability::Not)` (`&SelfRef`), `matches!` fails and shared references **still retag** normally (`Frozen` / `Cell`), whereas `&mut SelfRef` and `Box<SelfRef>` skip retagging completely (retaining the parent's provenance tag and installing **no protector**, `protector = None`).
3. **Lean 4 Verification Pairing (`PinnedAt`):** Simply omitting the Tree Borrows retag in Lean 4 models is necessary but not sufficient for `Pin` soundness: `Pin`'s **Drop Guarantee** (`pin.rs`) additionally requires an explicit spatial address-stability resource `PinnedAt (alloc : Nat) (fixedAddr : Nat)` forbidding relocation or deallocation without first running `T::drop`. Together, retag omission (`protector := none`) + `PinnedAt` validates `pin_self_referential` cleanly without false protector failures.

---

### 4. $O(1)$ Slice-Scaled Range Permissions (`RangeCellSlot`) vs. `DedupRangeMap` Fragmentation

Basis: source + execution + derived

Consider a multi-kilobyte interior-mutable buffer accessed via either `Cell::as_slice_of_cells` (`library/core/src/cell.rs:737–740`) or an array of `UnsafeCell`:

```rust
use std::cell::{Cell, UnsafeCell};

fn zero_prefix_cells(buf: &Cell<[u8; 4096]>) {
    let slice: &[Cell<u8>] = buf.as_slice_of_cells(); // &[Cell<u8>] of length 4096
    for c in &slice[..256] {
        c.set(0);
    }
}

fn retag_unsafe_array(buf: &mut [UnsafeCell<u8>; 4096]) {
    let _ = buf[0].get();
}
```

#### 4.1 Why `DedupRangeMap` Fragments on Elementwise Array/Slice Retags

Inspecting `rust-lang/miri` `src/data_structures/dedup_range_map.rs:105–242` uncovers a sharp structural asymmetry between `&Cell<[u8; 4096]>` and `&[Cell<u8>]` / `&mut [UnsafeCell<u8>; 4096]`:

1. **`&Cell<[u8; 4096]>` (Coalesced):** At the outer `Cell<[u8; 4096]>`, `UnsafeCellVisitor` hits `is_unsafe_cell` immediately (`helpers.rs:568`), emitting a single callback `[0, 4096), frozen = false`. Both `inside_perms` and `Tree::locations` remain **1 segment**.
2. **`&[Cell<u8>]` and `&mut [UnsafeCell<u8>; 4096]` (Fragmented to $N$ 1-Byte Segments):** Because `[Cell<u8>]` and `[UnsafeCell<u8>; 4096]` have `FieldsShape::Array`, `walk_value` (`visitor.rs:154–159`) projects each element `i = 0 .. 4095` separately, emitting `4,096` sequential callbacks `[i, i+1), frozen = false` to `perms_map.iter_mut(i, 1)`.
3. **Lack of Backward Coalescing in `DedupRangeMap::iter_mut` (`dedup_range_map.rs:155–221`):**
   - `iter_mut(offset, len)` calls `first_idx = self.find_offset(offset)` and splits `offset` (`155–159`).
   - Its merge loop (`equal_since_idx = first_idx` at `168–207`) only merges equal elements *strictly inside* `[first_idx .. end_idx]`—it **never** compares `v[first_idx]` against `v[first_idx - 1]`!
   - When `v` starts as `[0, 4096)` and receives sequential 1-byte updates `[0, 1)`, `[1, 2)`, ..., `[4095, 4096)`, each call splits off 1 byte from the trailing tail `[i, 4096)` and leaves `[0, 1), [1, 2), ..., [i-1, i)` permanently unmerged until an eventual GC pass invokes `merge_adjacent_thorough` (`tree.rs:740`)!
4. **Measured Fragmentation & Retag Amplification (`verify_models.py`):**

| Buffer Size $N$ | Elementwise `inside_perms` Segments | `split_index` Splits | `find_offset` Steps (`inside_perms` + `Tree::locations`) | `new_child` `Tree::locations` Segments | `RangeCellSlot` / Coalesced Segments |
|---|---|---|---|---|---|
| `64` | `64` | `63` | `328 + 328 = 656` | `64` | **`1`** |
| `1,024` | `1,024` | `1,023` | `9,228 + 9,228 = 18,456` | `1,024` | **`1`** |
| `4,096` | `4,096` | `4,095` | `45,070 + 45,070 = 90,140` | `4,096` | **`1`** |

Furthermore, for `&mut [UnsafeCell<u8>; 4096]` (`&mut` non-`FnEntry`), `NonFreeze` yields `ReservedIM` (`mod.rs:190`), whose `associated_access()` is `Some(Read)` (`perms.rs:317`), causing `mod.rs:368–420` to execute **`4,096` separate `tree_borrows.perform_access` traversals and `4,096` `data_race.read_non_atomic` checks**! In reflective separation-logic checkers in Lean 4 (where resource lists are checked via $O(M^2)$ permutation/disjointness loops), materializing `4,096` individual `CellSlot` atoms instead of `1` `RangeCellSlot` atom collapses kernel reduction throughput completely.

#### 4.2 Verifying Linear Branded Cells vs. Unbranded `&[Cell<u8>]`

In linear permission-token verifiers such as `verus-lang/verus` (`0dab219272ac2353320bd177ebb3929453b90a9e`, `source/vstd/cell.rs:65–250`), `PCell<V>` pairs an `UnsafeCell<MaybeUninit<V>>` with a ghost `Tracked<&mut PointsTo<V>>` carrying `CellId` and `MemContents<V>`. When callers hold unique branded tokens (`GhostCell<'id, T>` / `PCell<V>`), slice mutations reduce cleanly to pure linear array updates. However, standard-library `&[Cell<u8>]` (without a unique external `&mut PointsTo`) permits arbitrary aliased `&Cell<u8>` slices (`&slice[0..256]` overlapping another `&slice[128..384]`), requiring a spatial range resource whose disjointness and state transitions hold uniformly per byte offset.

#### 4.3 Lean 4 Formalization of Slice-Scaled `RangeCellSlot` and Soundness Laws

To verify both element-granular mixed structs (`Mixed { pure: u32, cell: Cell<u32>, flag: u8 }`) and multi-kilobyte `&[Cell<u8>]` / `[UnsafeCell<u8>; N]` slices in $O(1)$ without $O(N)$ `LocationState` expansion, represent contiguous uniform ranges as single `Type 0` separation-logic resources:

```lean
namespace RangeTreeBorrows

abbrev AllocId := Nat

inductive TbPerm where
  | cell | reservedFrz (conflicted : Bool) | reservedIM | unique | frozen | disabled

inductive AllocByte where
  | uninit | init (b : UInt8) (prov : Option AllocId)

structure RangeCellSlot where
  base   : AllocId
  off    : Nat
  count  : Nat
  stride : Nat
  perm   : TbPerm
  bytes  : List AllocByte   -- invariant: bytes.length = count * stride

def rangeByteSpan (r : RangeCellSlot) : Nat × Nat :=
  (r.off, r.count * r.stride)

def rangesDisjoint (o1 l1 o2 l2 : Nat) : Bool :=
  (o1 + l1 <= o2) || (o2 + l2 <= o1)

-- O(1) compatibility between two RangeCellSlot resources:
def rangeCompat (r1 r2 : RangeCellSlot) : Bool :=
  if r1.base == r2.base then
    rangesDisjoint r1.off (r1.count * r1.stride) r2.off (r2.count * r2.stride)
  else true
```

Four proved structural theorems bridge `RangeCellSlot` directly to Miri's bytewise `FreezeVisitor` and `LocationState` semantics:

1. **Periodic `FreezeVisitor` Collapse (`array_freeze_periodic_collapse`):**
   If element type `E` of stride `s` has `!type_is_freeze E` and `visit_freeze_sensitive` on `E` yields `frozen = false` across all offsets `[0, s)` (e.g., `Cell<u8>`, `Cell<u32>`, `UnsafeCell<T>`), then visiting `[E; N]` or `&[E]` (`count = N`, `stride = s`) visits every byte `[baseOff, baseOff + N * s)` with identical permission `nonfreeze_perm` and identical `accessed` / `SIFA` metadata—collapsing `N` `DedupRangeMap` callbacks identically to one `RangeCellSlot base baseOff N s perm bytes`!
2. **$O(1)$ Sub-Slice Split and Re-Join (`range_split` / `range_join`):**
   For any `k ≤ r.count` (`r.bytes.length = r.count * r.stride`), splitting at element `k` produces two adjacent `RangeCellSlot`s:
   - `left  := { base := r.base, off := r.off, count := k, stride := r.stride, perm := r.perm, bytes := r.bytes.take (k * r.stride) }`
   - `right := { base := r.base, off := r.off + k * r.stride, count := r.count - k, stride := r.stride, perm := r.perm, bytes := r.bytes.drop (k * r.stride) }`
   With arithmetic identity `r.off + k * r.stride = left.off + left.count * left.stride`, `rangeCompat left right = true` holds in $O(1)$ and `sepConj (ownsRange left) (ownsRange right) ⊣⊢ ownsRange r` preserves both `Realizes` byte correspondence and `TreeBorrows` permissions cleanly for `slice.split_at(k)` and `&slice[lo..hi]`.
3. **$O(1)$ Element Focus (`range_elem_focus`):**
   Indexing `&slice[i]` (`i < r.count`) isolates the single-element frame `[r.off + i * r.stride, r.stride)` between prefix `[0, i)` and suffix `[i + 1, r.count)` in constant time (`O(1)` range arithmetic instead of splitting `4,096` list nodes), updating `r.bytes` at `[i * s .. (i + 1) * s)` and preserving untouched prefix/suffix invariants across `range_join`.
4. **Uniform Transition Homomorphism (`range_tb_transition_homomorphism`):**
   Let `expandBytes (r : RangeCellSlot) : List (Nat × TbPerm)` map `r` to `[(r.off + j, r.perm) | j < r.count * r.stride]`. For any whole-range `performAccess kind rel p prot = .Transition p'` (`perms.rs:105–111`), updating the single `RangeCellSlot` permission `r.perm → p'` commutes strictly with applying `performAccess` pointwise across every byte location `j < r.count * r.stride` (`expandBytes (updateRangePerm r p') = (expandBytes r).map (stepLoc kind rel prot)`). For `perm = .Cell`, `cell_is_unchanged` makes `updateRangePerm` the identity in $O(1)$!

For **heterogeneous structs inside arrays** (`[Mixed; N]` where `Mixed` contains both `Freeze` fields `0..4, 8..12` and `UnsafeCell` fields `4..8`), flat non-masked `RangeCellSlot` splits cleanly per element only when `N` is small (via field-granular permission trees), or requires augmenting `RangeCellSlot` with a periodic `elemFreezeMask : Nat → Bool` (`mod stride`) separating frozen offsets `(off + k * stride + j)` where `elemFreezeMask j = true` (`Frozen`) from interior-mutable offsets where `elemFreezeMask j = false` (`Cell` / `ReservedIM`).

## Boundaries

- **known not to apply** (Flat uniform `RangeCellSlot` on `[Mixed; N]` heterogeneous arrays): The single-permission `RangeCellSlot` model above assumes every byte in `[off, off + count * stride)` shares uniform `TbPerm`. It does not apply verbatim to arrays of mixed `Freeze` + `UnsafeCell` structs `[Mixed; N]` unless extended with a periodic intra-element mask `elemFreezeMask : Nat → Bool` (`j % stride`).
- **unsupported** (Custom-allocator `Box<T, A>` retagging in Miri): At `rust-lang/miri` `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3` (`src/borrow_tracker/tree_borrows/mod.rs:494–497`), boxes using non-global allocators (`!ty.is_box_global && ty.is_box()`) return `None` from `tb_retag_ptr_value` and receive no Tree Borrows retag or protector (`WeakProtector` applies exclusively to `Box<T, Global>`).
- **unknown** (Final semantics of `UnsafePinned<T>` per-byte pinning): `tree_borrows/mod.rs:153` explicitly notes `FIXME: with UnsafePinned, this should do proper per-byte tracking`; how upstream Miri will refine `!Unpin` retag omission into field-granular `InsideUnsafePinned` visitor splits remains unresolved in the pinned revision.
- **not examined** (Wildcard-provenance multi-root trees on slice-scaled ranges): `ProvenanceExtra::Wildcard` exposed-tag subtrees (`tree.rs:291–307, 1064–1188`) and `ExposedCache` updates over `RangeCellSlot` descriptors were not examined here; our slice-scaled proofs cover concrete parent-child `BorTag` trees.

## Evidence

| Artifact / Claim | Source / Publication | Exact Immutable Identity & Location | Role |
|---|---|---|---|
| `visit_freeze_sensitive`, `UnsafeCellVisitor`, trailing flush, zero-size `UnsafeCell` short-circuit | `rust-lang/miri` | `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/helpers.rs:468–612` | `source` |
| `NewPermission::new`, `!Unpin`/`!UnsafeUnpin` omission, `FnEntry` `ReservedFrz`, `tb_reborrow`, `tb_retag_ptr_value` | `rust-lang/miri` | `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/borrow_tracker/tree_borrows/mod.rs:109–221, 328–434, 474–507` | `source` |
| 6-variant (7-state) `PermissionPriv`, `PartialOrd`, `perform_access`, `associated_access`, `can_be_replaced_by_child`, SIFA | `rust-lang/miri` | `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/borrow_tracker/tree_borrows/{perms.rs:10–396, 634–824, foreign_access_skipping.rs:29–95}` | `source` |
| `LocationState`, `accessed` bit, `new_child`, `dealloc` `Cell` exemption, `merge_adjacent_thorough` | `rust-lang/miri` | `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/borrow_tracker/tree_borrows/tree.rs:37–258, 391–611, 732–741` | `source` |
| `DedupRangeMap::iter_mut` (absence of backward coalescing against `v[first_idx - 1]`) | `rust-lang/miri` | `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `src/data_structures/dedup_range_map.rs:14–242` | `source` |
| `ValueVisitor::walk_value` (`ty::Dynamic`, `Box` allocator-only recursion, `FieldsShape::Arbitrary` memory order, `FieldsShape::Array`) | `rust-lang/rust` | `ec65cd52bba13d491ff65c9d218b39753755c84a`, `compiler/rustc_const_eval/src/interpret/visitor.rs:81–188` | `source` |
| `Cell::as_slice_of_cells`, `Cell::as_array_of_cells`, `Pin<Ptr>` layout/Drop guarantee | `rust-lang/rust` | `ec65cd52bba13d491ff65c9d218b39753755c84a`, `library/core/src/{cell.rs:737–761, pin.rs:950–1093}` | `source` + `normative` |
| Linear branded `PCell<V>` / `PointsTo<V>` architecture contrast | `verus-lang/verus` | `0dab219272ac2353320bd177ebb3929453b90a9e`, `source/vstd/cell.rs:65–250` | `source` |
| Tree Borrows semantics and Simuliris Rocq mechanization | PLDI 2025 paper & artifact | Villani, Hostert, Dreyer, Jung (2025), DOI `10.1145/3735592`; artifact DOI `10.5281/zenodo.15002703` | `normative` + `documentation` |
| Exhaustive Tree Borrows transition oracle & `DedupRangeMap` fragmentation runs (2026-11-20) | Local Python 3.13 verification run | Checked `54` valid + `2` invariant-panic `(state, kind, rel, prot)` inputs (`57` idempotence laws, `8` `Cell` invariances, `49` lattice reachability pairs with `20` comparable pairs); measured `DedupRangeMap` fragmentation at `N ∈ {64, 1024, 4096}` yielding `4096` segments (`4095` splits, `45070` `find_offset` steps per map) vs `1` coalesced segment | `execution` |

## Revalidation

1. **Exhaustive Lattice & `DedupRangeMap` Fragmentation Revalidation Script** (Python 3.10+, zero external dependencies, `< 20 ms`):
   ```bash
   python3 - <<'PY'
   def split_seq(n):
       v = [(0, n, "Disabled")]
       splits = steps = 0
       for i in range(n):
           lo, hi = 0, len(v) - 1
           while lo <= hi:
               steps += 1
               mid = (lo + hi) // 2
               if i < v[mid][0]: hi = mid - 1
               elif i >= v[mid][1]: lo = mid + 1
               else: idx = mid; break
           s, e, d = v[idx]
           if i + 1 < e:
               v[idx] = (s, i + 1, "Cell")
               v.insert(idx + 1, (i + 1, e, d))
               splits += 1
           else:
               v[idx] = (s, e, "Cell")
       return len(v), splits, steps

   for n, exp_steps in ((64, 328), (1024, 9228), (4096, 45070)):
       segs, sp, st = split_seq(n)
       assert (segs, sp, st) == (n, n - 1, exp_steps), (n, segs, sp, st)
   print("REVALIDATION_OK", split_seq(4096))
   PY
   ```
2. **Upstream Source Drift Check:** Diff `src/borrow_tracker/tree_borrows/{mod.rs,perms.rs,tree.rs}`, `src/helpers.rs` (`visit_freeze_sensitive`), and `src/data_structures/dedup_range_map.rs` in `rust-lang/miri` plus `compiler/rustc_const_eval/src/interpret/visitor.rs` in `rust-lang/rust` against the 40-character revisions in `REPORT.json`, specifically checking whether `UnsafePinned` per-byte tracking (`mod.rs:153`) or backward `DedupRangeMap::iter_mut` coalescing has landed.
3. **Miri Behavioral Spot Check:** Run `cargo miri test` (with `-Zmiri-tree-borrows`) on `Mixed` (`#[repr(C)] struct { pure: u32, cell: Cell<u32>, flag: u8 }`), `pin_self_referential`, and `zero_prefix_cells` to confirm `Box<T, CustomAlloc>` / `!Unpin` / `Cell::as_slice_of_cells` aliasing behavior matches the static rules above.
