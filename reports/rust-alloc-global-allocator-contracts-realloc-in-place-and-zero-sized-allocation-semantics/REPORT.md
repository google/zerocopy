# Formal Verification Contracts for Rust `GlobalAlloc` and `Allocator`: `Layout` Arithmetic, Zero-Sized Provenance, `realloc` Invalidation, Initialization Barriers, and Tree Borrows Soundness

## Summary

Sound verification of `unsafe` Rust containers (`Vec`, `RawVec`, `Box`) and custom Rust allocators requires tracking six distinct contracts across `core::alloc::Layout`, `core::alloc::GlobalAlloc`, `alloc::alloc::{alloc, dealloc, realloc, alloc_zeroed}`, `core::alloc::Allocator`, MiniRust `BasicMemory`, and Tree Borrows (`Villani et al., PLDI 2025`):

1. **`Layout` Well-Formedness vs. `GlobalAlloc` (`layout.rs:59–168`):** `Layout` enforces $\text{align} = 2^k \in [1, 2^{B-1}]$ and $0 \le \text{size} \le (\text{isize::MAX} + 1) - \text{align}$ (`777` valid / `64,759` invalid pairs in an exhaustive 8-bit `256 x 256` model). Because `Layout` permits `size == 0`—including `(0, 1 << (B - 1))`—`Layout` validity never discharges `GlobalAlloc::{alloc, alloc_zeroed}` (`size > 0` enforced via `assert_unchecked` in `global.rs:360, 378`).
2. **Three-Surface Contract Algebra (`global.rs:89–417`, `core/alloc/mod.rs:99–725`, `alloc.rs:94–626`):** `GlobalAlloc`, the free functions `alloc::alloc::*`, and `Allocator` enforce non-interchangeable rules. The free functions add six optimizer barriers—non-deterministic elision/merging/infallibility, exact `layout.size()` clipping, domain separation from raw `GlobalAlloc` methods, live-block internal-pointer exclusion, and logical de-initialization at *both* `alloc` exit and `dealloc` entry—while `Allocator` replaces exact `Layout` matching with **fitting** layouts (`align == orig_align` and `req_size <= layout.size() <= slice_len`), equivalence (`~_alloc`), and `StaticAllocator` `Pin` drop guarantees.
3. **Zero-Sized `NonNull::dangling` vs. Zero-Byte `AllocId` Provenance (`non_null.rs:98–133`, `raw_vec/mod.rs:479–669`):** `Layout::dangling_ptr` and `Global` (`size = 0`) return `NonNull::without_provenance(align)` (`Provenance::None`). Under `BasicMemory::check_ptr` (`basic.md:197–225`), 0-byte accesses check alignment only and ignore provenance, whereas `RawVecInner` stores `cap = ZERO_CAP` so `current_memory() == None` never frees `dangling()`. Under Tree Borrows (`miri/tree_borrows/mod.rs:274–286`), size-0 reborrows preserve `None` without an allocation, yet create a real child `BorTag` (`outside_perm = Reserved`) when inside a live `AllocId`.
4. **In-Place `realloc` Provenance Invalidation (`global.rs:273–347`, `rustc_interpret_memory.rs:301–332`):** Successful `realloc`, `grow`, and `shrink` **always** mint a fresh `AllocId'` and kill the old `AllocId`, even when virtual address `new_ptr.addr() == old_ptr.addr()`. Both external cached handles *and* **self-referential interior pointers stored inside `0..min(old, new)`** preserve dead `AllocId` provenance under bitwise `mem_copy` and cause immediate UB if dereferenced; failed `realloc` (`null`/`Err`) leaves the original block intact.
5. **Untyped Byte Preservation vs. `alloc_zeroed`/`grow_zeroed` (`ucg_glossary.md:38–46`):** `ptr::copy_nonoverlapping::<u8>` transfers `AbstractByte::Uninit` (padding, spare `MaybeUninit` capacity) and pointer provenance intact, whereas custom `GlobalAlloc::realloc` code forming `&[u8]` over uninitialized spare capacity triggers `InvalidUninitScalar` UB. `Allocator::allocate_zeroed` zeroes `0..ptr.len()` (including excess), `Global::grow_impl_runtime(..., true)` zeroes `old_size..new_size`, and `0x00` zeroing satisfies `MaybeUninit`/all-zero bytes without validating `NonZero*` or references.
6. **Allocator-Boundary Tree Borrows Soundness (`miri/tree_borrows/tree.rs:522–600`):** `Box<T>` uses a **weak protector** (allowing `deallocate` and dead-block `end_call`), while `&T`/`&mut T` use **strong protectors** (forbidding deallocation while locally accessed unless `UnsafeCell`, explaining why freeing `&self` in `Allocator::deallocate` is UB). Custom slab headers immediately before `sub_ptr` fail under Stacked Borrows range clipping, yet succeed under Tree Borrows `outside_perm = Reserved` iff no foreign write via the arena root touches `[0..HDR)` while `sub_ptr` is live.

## Applicability

These findings govern Rust verification contracts, operational memory models, and custom allocator audits across the ten subjects in `REPORT.json`:

- **Rust Standard Library (`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`):** Covers `library/core/src/alloc/{layout.rs, global.rs, mod.rs}`, `library/core/src/ptr/{non_null.rs, const_ptr.rs}`, and `library/alloc/src/{alloc.rs, boxed.rs, raw_vec/mod.rs}`. At this revision, `allocator_api` on `Allocator`, `AllocError`, `Global`, and `Box::{from_raw_in, into_raw_with_allocator}` carries `since = "1.100.0"`, while `GlobalAllocator`, `StaticAllocator`, `AllocatorClone`, and `AllocatorNightly` remain gated under `allocator_ext` (`#163177`) and `const fn` heap ops under `const_heap` (`#79597`).
- **Miri & Compiler Interpreter (`rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`, `rustc_const_eval/src/interpret/memory.rs` @ `ec65cd52bba1`):** Covers `src/shims/alloc.rs`, `src/alloc_addresses/mod.rs` (`ProvenanceMode::{Default, Permissive, Strict}`), and `src/borrow_tracker/tree_borrows/{mod.rs, tree.rs, perms.rs}`.
- **Formal Specifications & Literature:** Covers `minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568` (`spec/mem/basic.md`, `spec/mem/tree_borrows/{memory.md, tree.md, state_machine.md}`), `rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` (`src/behavior-considered-undefined.md`), `rust-lang/unsafe-code-guidelines` @ `d809f91e62968913d808e53397fbcf7cea762cce`, `verus-lang/verified-memory-allocator` @ `7d120970f8d63157ae9bf3b2361192d29bc0acaa` (`verus-mimalloc/linked_list.rs`), and PLDI/POPL/OOPSLA foundations (`10.1145/3735592`, `10.1145/3371109`, `10.1145/3158154`, `10.1145/3276495`).

**Prior Corpus Coverage:** Earlier corpus reports address complementary layers without deriving these contracts: `reports/rust-allocation-box-storage-transfer-and-drop-elaboration` covers `Box` raw pointer lifecycle and MIR `ElaborateDrops`; `reports/rust-allocation-provenance-and-stack-lifetime-semantics` analyzes LLVM `allockind` / `alloc-family` lowering, `__rust_no_alloc_shim_is_unstable_v2`, and strict vs. exposed provenance casts; `reports/tree-borrows-two-stage-protector-release-and-reborrow-contracts` covers Tree Borrows protector release semantics; and `reports/certigraph-localizations-slab-buddy-freelists-and-split-points-to-raw-framing` studies Verus `PointsTo<Node> * PointsToRaw` freelist splitting and buddy coalescing.

## Findings

### 1. `Layout` Arithmetic, Alignment Rounding, and Unsized Metadata Bounds

`Basis: source + normative + execution + derived`

In `library/core/src/alloc/layout.rs:30–168`, `Layout { size: usize, align: Alignment }` enforces two invariants across all safe and unsafe constructors (`L59–144`):

1. **Power-of-Two Alignment:** $\text{align} = 2^k$ for $0 \le k \le B - 1$ on a $B$-bit target ($\text{align} \in [1, \text{isize::MAX} + 1]$). Unlike `posix_memalign`, `Layout` allows sub-word alignments `1, 2` (`L39–40`).
2. **Exact Rounded-Up Upper Bound (`layout.rs:74–98`):** Because `align` divides $\text{isize::MAX} + 1 = 2^{B-1}$,
   $$\text{round\_up}(\text{size}, \text{align}) \le \text{isize::MAX} \iff 0 \le \text{size} \le (\text{isize::MAX} + 1) - \text{align}$$
   `Layout::max_size_for_alignment` (`L97`) evaluates `unchecked_sub(isize::MAX as usize + 1, align)` without overflow.
3. **Boundary Vectors (verified exhaustively on 8-bit `256 x 256` grid = `777` valid / `64,759` invalid pairs, plus 64-bit bounds):**
   - `(0, 1 << (B - 1))`: **Valid** ($\text{max\_size} = 0$, rounded $= 0 \le \text{isize::MAX}$).
   - `(1, 1 << (B - 1))`: **Invalid** (`LayoutError`; rounded $= 2^{B-1} = \text{isize::MAX} + 1$).
   - `(isize::MAX, 1)`: **Valid**; `(isize::MAX, 2)`: **Invalid** (rounded $= \text{isize::MAX} + 1$).
   - `from_size_align_unchecked` (`L132–144`) enforces this exact predicate via `assert_unsafe_precondition!(check_library_ub, ...)`.
4. **Combinators & Unsized Raw Pointers (`layout.rs:259–556`):** `pad_to_align()` (`L387–396`) rounds `size` up safely without overflow; `align_to` / `adjust_alignment_to` (`L297–323`) raises alignment to $\max(\text{self.align}, \text{align})$ *without* adding trailing padding; `repeat(n)` (`L435–450`) repeats `pad_to_align` $(n-1)$ times plus unpadded `*self` (omitting trailing padding!) and returns `(Layout(0, align), padded.size)` when `n == 0`. `Layout::for_value_raw<T: ?Sized>(val)` (`L259–264`) requires `size_of_val_raw(val) <= isize::MAX` for nonzero slices/`str`/`dyn Trait` (`ref_ub.md:155–162`). Crucially, `Layout` validity never proves `size > 0` for `GlobalAlloc`.

### 2. Three-Surface Contract Algebra: `GlobalAlloc` vs. `alloc::alloc::*` vs. `Allocator`

`Basis: source + documentation + derived`

Rust's heap allocation API separates three non-interchangeable contracts (`global.rs:89–417`, `core/alloc/mod.rs:99–725`, `alloc/src/alloc.rs:46–626`):

| Contract Dimension | `core::alloc::GlobalAlloc` (`global.rs:189–348`) | Free Shim `alloc::alloc::*` (`alloc/src/alloc.rs:94–325`) | `core::alloc::Allocator` (`core/alloc/mod.rs:235–618`) & `Global` |
| :--- | :--- | :--- | :--- |
| **Zero-sized `Layout`** | **UB** on `alloc` and `alloc_zeroed`; `realloc` requires `new_size > 0`. | **UB** on `alloc` and `alloc_zeroed`; `realloc` requires `new_size > 0`. | **Permitted.** `Global` returns `layout.dangling_ptr().cast_slice(0)` directly. |
| **Returned Handle & Capacity** | `*mut u8` (null on failure unless aborting). | `*mut u8`; logical bounds **clipped to `layout.size()`** (`global.rs:103–105`). | `Result<NonNull<[u8]>, AllocError>`; slice length $M \ge \text{layout.size}()$ exposes excess (`RawVec`). |
| **Deallocation `Layout`** | **Exact** `layout == orig_layout` (`global.rs:233–234`). | **Exact** `layout == orig_layout`; pointer must originate from `alloc::alloc::*` (`L112–114`). | **Fitting**: `layout.align() == orig.align()` and `req_size <= layout.size() <= M` (`mod.rs:182–190`). |
| **Resize Size & Align** | `realloc`: `new_size > 0`, rounded $\le \text{isize::MAX}$, same `align` only. | Same as `GlobalAlloc::realloc`, plus de-initializes grown/shrunk tails (`alloc.rs:233–236`). | `grow`/`grow_zeroed`: `new >= old`; `shrink`: `new <= old`; **`new.align()` may differ**. |
| **Unwinding** | Unwinding is **UB** (`global.rs:158–160`). | Callers must tolerate potential future unwinds (`alloc.rs:120`). | Non-unwinding mandatory on alloc/dealloc/`Drop` (`mod.rs:212–216`; `#156490`/`#159982`). |
| **Elision & Aliasing** | Must not touch live user blocks (`L155–156`). | Compiler may **elide, merge, stack-promote, or assume infallible** (`global.rs:99–148`). | Equivalence `~_alloc`, invalidation triggers, and `StaticAllocator` `Pin` contract (`mod.rs:99–171, 695–724`). |

Four subtle invariants follow directly from the source:

1. **Free-Function Shim Barriers (`global.rs:99–148`, `alloc.rs:100–325`):** Calling `alloc::alloc::alloc` is *not* equivalent to `<MyAlloc as GlobalAlloc>::alloc`. Even with a stateful `#[global_allocator]`, the compiler may elide or stack-promote unused allocations—making `assert_unchecked(alloc_count > 0)` after `drop(Box::new(42))` immediate UB (`global.rs:137–141`). Furthermore, `alloc`/`realloc` logically de-initialize newly exposed bytes and `dealloc`/`realloc` logically de-initialize returned/shrunk bytes (`global.rs:115–122`), forbidding caller/allocator payload smuggling outside `alloc_zeroed`, and pointers from `alloc::alloc::*` / `Global` may never be freed directly on a `GlobalAlloc` value (`global.rs:106–114`, `alloc.rs:60–73`).
2. **Allocator Equivalence (`~_alloc`) and Invalidation (`mod.rs:99–171`):** `Allocator` defines an equivalence relation preserved across moves, subtyping, unsizing, trait upcasting, `&A`/`&mut A`, `Box<A>`/`Rc<A>`/`Arc<A>`, and `AllocatorClone`. A live allocation becomes invalidated upon explicit deallocation (`deallocate` or `Ok` resize) **or** when, for *all* live equivalent instances, the allocator drops, is mutated via untrusted `&mut`, or a borrow lifetime in `A`'s type expires. Safe `&self` methods outside deallocation/resize must never invalidate allocations, justifying `RawVec::allocator(&self) -> &A` (`raw_vec/mod.rs:331`).
3. **`StaticAllocator` and `Pin` Drop Guarantees (`mod.rs:695–724`):** `Pin<Box<T, A>>` soundness requires `A: StaticAllocator`, ensuring no drop, safe API, or lifetime expiry (including covariant shortening `MyAlloc<'long> -> MyAlloc<'short>`, `#157089`) can invalidate allocations without explicit `deallocate`.
4. **Blanket `GlobalAllocator -> GlobalAlloc` Bridge (`global.rs:351–417`):** Every `A: GlobalAllocator` (`StaticAllocator + Sync + 'static`, `mod.rs:678`) implements `GlobalAlloc` using `hint::assert_unchecked(layout.size() != 0)` (`L360, 369, 378, 387, 389`), turning any zero-sized direct `GlobalAlloc` call into immediate LLVM `assume(false)` UB.

### 3. Zero-Sized Allocation (`NonNull::dangling`) vs. Non-Zero `AllocId` Provenance

`Basis: source + normative + execution + derived`

Formal models must distinguish **provenance-free dangling pointers** from **zero-length accesses into live `AllocId`s**:

1. **Dangling Representation (`non_null.rs:98–133`, `layout.rs:276–278`):** `NonNull::<T>::dangling()` and `Layout::dangling_ptr()` return `NonNull::without_provenance(align)`—a non-null, `align`-aligned pointer with **`Provenance::None`**. Because real allocations can share address `align`, `ptr == dangling()` **must never** be used as an unallocated sentinel (`layout.rs:268–271`, `non_null.rs:112–115`).
2. **0-Byte Operational Semantics (`basic.md:197–274`):** MiniRust `BasicMemory::load`/`store` enforce alignment (`L234, 260`) and then invoke `check_ptr(ptr, 0)`, which immediately returns `Ok(None)` (`L201–203`) without checking `ptr.provenance` or allocation liveness. Reading or writing `>= 1` byte via `without_provenance` fails with `NoProvenance` (`L206–208`). By provenance monotonicity (`L199–200`), any 0-byte access valid on `None` is valid on any aligned non-null provenance.
3. **`RawVecInner` ZST State Machine (`raw_vec/mod.rs:48–100, 479–669, 869–878`):** `RawVecInner::new_in` sets `ptr = without_provenance(align)` and `cap = ZERO_CAP`. While `RawVec::capacity()` exposes `usize::MAX` for ZSTs (`L640`), internal `self.cap` stays `0`, and `try_allocate_in` short-circuits whenever `layout.size() == 0` (`L480–482`, covering both ZSTs and `capacity == 0`). Because `current_memory` (`L654–668`) returns `None` when `elem_layout.size() == 0 || cap == 0`, `Drop` and `shrink_unchecked(0)` (`L872–877`, matching `Box::drop` at `boxed.rs:2137`) skip `deallocate` and reset `ptr = without_provenance(align)`.
4. **Tree Borrows Size-0 Retagging Split (`miri/tree_borrows/mod.rs:274–286`):** On `reborrow(ptr, ptr_size = 0)`, Miri checks `ptr_try_get_alloc_id(place.ptr(), 0)`: if `None` (e.g., `&()` from `NonNull::dangling()`), it preserves `None` (`L277–285`); if `Some((alloc_id, parent_tag))` (e.g., `&arr[..0]` or one-past-the-end slice), it allocates a **real child `BorTag`** with `outside_perm = Reserved` across the whole `AllocId` so subsequent valid pointer arithmetic through the parent range stays sound.

### 4. `realloc` / `grow` / `shrink` In-Place vs. Move Provenance Invalidation

`Basis: source + normative + execution + derived`

Both normative Rust docs (`global.rs:273–347`, `core/alloc/mod.rs:357–618`) and Miri (`rustc_interpret_memory.rs:301–332`, `miri/shims/alloc.rs:164–188`) treat successful reallocation as **unconditional allocation replacement**:

1. **Success vs. Failure Ownership Transfer:**
   - **On `Ok` / non-null return:** The old `AllocId` is immediately invalidated (`live = false`) and `new_ptr` receives a **fresh `AllocId'`** of size $M' \ge \text{new\_layout.size}()$ holding the abstract-byte prefix $0..\min(\text{old\_req}, \text{new\_size})$. Accessing `old_ptr` or any pointer derived from it is **immediate UB even when `new_ptr.addr() == old_ptr.addr()`** (`global.rs:278–280`, `mod.rs:363–365`).
   - **On `Err(AllocError)` / null return:** Ownership does *not* transfer; `old_ptr`'s `AllocId`, permissions, and contents remain intact (`global.rs:288–290`, `mod.rs:370–371`), which `RawVecInner::finish_grow` (`raw_vec/mod.rs:573–585`) relies on during OOM handling.
2. **Miri `reallocate_ptr` Semantics & Self-Referential Interior Pointers:**
   In `rustc_const_eval/src/interpret/memory.rs:317–331`, `reallocate_ptr` unconditionally executes `allocate_ptr` -> `mem_copy(old_size.min(new_size))` -> `deallocate_ptr`. Even when modeling an in-place OS `realloc` (`new_addr == old_addr`), two failure modes arise (`probe_alloc` check):
   - *Cached external handles:* Any saved `*mut T` or slice base from before `Vec::reserve` carries dead `AllocId_old`.
   - *Self-referential interior pointers stored inside the payload:* Bitwise `mem_copy` copies stored pointer provenance verbatim; an interior pointer saved at byte `0..8` pointing to byte `8` of `AllocId_old` **still carries dead `AllocId_old`** after an in-place `realloc`, causing immediate `DeadAllocation` UB on dereference! Verified self-referential growable buffers must store relative offsets or re-derive pointers from `new_ptr`.
3. **Cross-Alignment Fallback & Zero-Size Divergence (`alloc.rs:373–448`, `miri/shims/alloc.rs:226–257`):** `Global::grow_impl_runtime` handles `old_size == 0` via `alloc_impl`, `old_align == new_align` via `realloc_nonnull`, and cross-alignment growth via `alloc_impl + copy_nonoverlapping + deallocate`. `Global::shrink_impl_runtime` maps `new_size == 0` to `deallocate + dangling_ptr()`, avoiding C `realloc(ptr, 0)` (rejected as UB in `miri/shims/alloc.rs:241–245` per `WG14 N2464`), whereas `GlobalAlloc::dealloc(null, layout)` is UB (`alloc.rs:197`) unlike C `free(null)` (`miri/shims/alloc.rs:228–230`).

### 5. Uninitialized Memory Preservation vs. `alloc_zeroed` and `grow_zeroed`

`Basis: source + normative + execution + derived`

Every allocation byte in MiniRust (`basic.md:28, 132`) and Rust (`ucg_glossary.md:38–46`) is `AbstractByte::Uninit | Init(u8, Option<Prov>)`, inducing three boundary obligations:

1. **Untyped Byte Preservation vs. Scalar `InvalidUninitScalar` UB:** `ptr::copy_nonoverlapping::<u8>` (`global.rs:342`, `core/alloc/mod.rs:457, 612`) copies `Uninit` (struct padding, uninitialized `MaybeUninit` elements in `RawVec`) and `Init(b, Some(prov))` without forcing scalar initialization. Conversely, any custom `GlobalAlloc::realloc` or `Allocator::grow` that constructs `&[u8]` (`slice::from_raw_parts`) over `0..min(old, new)` containing any `Uninit` byte triggers immediate `r[undefined.validity.scalar]` (`InvalidUninitScalar`, `ref_ub.md:134`) UB.
2. **`allocate_zeroed` vs. `grow_zeroed` Boundaries:** `Allocator::allocate_zeroed` (`core/alloc/mod.rs:334`) zeroes `0..ptr.len()`—covering any overallocated excess past `layout.size()`. In `Global::grow_impl_runtime(..., zeroed = true)` (`alloc.rs:386–388`), `Global` invokes `realloc_nonnull` and explicitly runs `raw_ptr.add(old_size).write_bytes(0, new_size - old_size)`. Likewise, `Allocator::grow_zeroed` (`mod.rs:469–472`) preserves `0..old_layout.size()` and zeroes `old_layout.size()..actual_new_len`, while `shrink` (`mod.rs:535`) leaves any excess past `new_layout.size()` uninitialized.
3. **Byte-Zeroing vs. Type Validity:** `Init(0x00, None)` proves `[u8; N]`, `MaybeUninit<T>`, and all-zero scalar validity (`u*`/`bool`/`char`), **not** niche-constrained types (`NonZero*`, `&T`, `&mut T`, `Box<T>`, `fn()`, or enums lacking a valid `0` tag; `ref_ub.md:122–165`).

### 6. Allocator-Boundary Soundness Under Tree Borrows vs. Stacked Borrows

`Basis: source + normative + execution + derived`

Under Tree Borrows (`Villani et al., PLDI 2025`; `miri/tree_borrows/{mod.rs, tree.rs}`; `minirust/tree_borrows/{memory.md, tree.md}`), allocator boundaries obey three precise rules:

1. **`WeakProtector` (`Box<T>`) vs. `StrongProtector` (`&T`/`&mut T`) (`miri/tree_borrows/mod.rs:213–219`, `tree.rs:522–595`):** At function entry, references gain `StrongProtector` and `Box<T, Global>` gains `WeakProtector` (custom-allocator `Box<T, A>` skips retagging at `mod.rs:494–497`). In `Tree::dealloc` (`tree.rs:530–595`), `perform_access(prov, 0..size, Write, Dealloc)` runs first (enforcing write permission and catching foreign protector conflicts), followed by scanning all trees for `StrongProtector && !perm.is_cell() && perm.accessed` (`L572–581`). Thus moving and dropping a `Box<T>` inside a callee is sound (`WeakProtector` permits dead allocations on `end_call`, `memory.md:166–170`), whereas deallocating an allocation backing an accessed `&self`/`&mut self` (including a self-hosted allocator freeing its own storage in `Allocator::deallocate(&self, ...)`, `core/alloc/mod.rs:345–350`) is immediate `ProtectorViolation` / `ProtectedDealloc` UB.
2. **Custom Arena/Slab Header Metadata (`outside_perm = Reserved` vs. Stacked Borrows Clipping):** When a custom slab allocator reserves an `AllocId` `[0..HDR + sz)`, places a header in `[0..HDR)`, returns `sub_ptr = base.add(HDR)`, and later receives `sub_ptr` back after `Box::into_raw(Box::from_raw(sub_ptr))` (or `&mut`), **Stacked Borrows** (`POPL 2020`) clips the retagged pointer's span to `[HDR..HDR + sz)`—making `sub_ptr.sub(HDR)` UB. Under **Tree Borrows** (`miri/tree_borrows/mod.rs:164–212`, `memory.md:107`), `&mut`/`Box` assigns **`outside_perm = ReservedFrz`/`ReservedIM`** across the *entire* allocation outside `[HDR..HDR + sz)`, permitting `sub_ptr.sub(HDR)` header access **iff** no foreign write via the parent arena root mutated `[0..HDR)` while `sub_ptr` was live (which transitions `sub_ptr`'s outside permission to `Disabled`!). Even then, `Box<T, Global>` cannot use `reallocate_ptr`/`deallocate_ptr` directly on `sub_ptr` because Miri checks `offset == 0` (`rustc_interpret_memory.rs:311, 389`); portable custom arenas recover header provenance from an arena root via `arena_root.with_addr(...)` (`const_ptr.rs:204–212`) or `with_exposed_provenance` (`verus-mimalloc/linked_list.rs:205, 396`).
3. **Freelist Typed-to-Raw Erasure (`verus-mimalloc/linked_list.rs:197–206, 394–403`):** Intrusive freelists expose `ptr`, split `[ptr, ptr + sz)` into typed `Node { next }` plus uninitialized tail on `dealloc`, and recover `with_exposed_provenance(addr)` + `into_typed` -> `into_raw().join(...)` on `alloc` to restore uninitialized caller storage.

## Boundaries

- **`GlobalAlloc::alloc` / `alloc_zeroed` / `realloc` on Zero-Sized Requests:** **known not to apply** — zero-sized requests and `new_size == 0` in `realloc` are immediate UB (`global.rs:197–198, 245–246, 301`) and trigger `assert_unchecked(layout.size() != 0)` in the blanket `GlobalAllocator` bridge (`L360, 378, 387–389`). Only `Allocator` and `Global` accept `size == 0`.
- **Zero-Initialization as Universal Type Validity:** **known not to apply** — `alloc_zeroed`, `allocate_zeroed`, and `grow_zeroed` establish byte-level `0x00` (`Init(0x00, None)`), not validity for `NonZero*`, references, `Box<T>`, `fn` pointers, or zero-disallowing enums (`ref_ub.md:122–165`).
- **Allocator Unwinding and `-Zmiri-strict-provenance` with `with_exposed_provenance`:** **unsupported** — unwinding from `GlobalAlloc`/`Allocator` methods or `Allocator::drop` is UB (`global.rs:158–160`, `mod.rs:212–216`), and Miri `ProvenanceMode::Strict` (`src/alloc_addresses/mod.rs:375–377`) halts on `with_exposed_provenance` casts used by address-keyed freelists.
- **Normative OOM-Reducing Heap-Elision Semantics Under Address-Space Exhaustion:** **unknown** — `BasicMemory::allocate` (`basic.md:104–124`) uses daemonic address choice (`FIXME` at `L106`), and the exact Rust Abstract Machine model reconciling compiler heap elision with finite address-space exhaustion (`unsafe-code-guidelines#328`) remains open upstream.
- **OS Virtual-Memory Page Reclamation (`mmap`/`madvise`) and CHERI Hardware Capabilities:** **not examined** — kernel page-table zeroing/unmapping and hardware capability bounds compression were outside this study.

## Evidence

- **`rust-lang/rust` @ `ec65cd52bba13d491ff65c9d218b39753755c84a`:** `library/core/src/alloc/{layout.rs:30–168, 259–556, global.rs:89–417, mod.rs:99–945}`, `library/core/src/ptr/{non_null.rs:98–133, const_ptr.rs:204–225}`, `library/alloc/src/{alloc.rs:12–626, boxed.rs:1698–1825, 2126–2146, raw_vec/mod.rs:40–100, 466–669, 859–941}`, and `compiler/rustc_const_eval/src/interpret/memory.rs:251–435`.
- **`rust-lang/miri` @ `0a0ce195cb0e91890c21ed717cca6eefef5e1ff3`:** `src/shims/alloc.rs:89–257`, `src/alloc_addresses/mod.rs:20–29, 237–379`, and `src/borrow_tracker/tree_borrows/{mod.rs:109–288, 474–528, tree.rs:519–600}`.
- **`minirust/minirust` @ `063d784186d3252bee242217f218223205c0b568`:** `spec/mem/basic.md:18–41, 91–275` and `spec/mem/tree_borrows/{memory.md:82–267, tree.md:14–241, state_machine.md:11–88}`.
- **`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** `src/behavior-considered-undefined.md:15–169`; **`rust-lang/unsafe-code-guidelines` @ `d809f91e62968913d808e53397fbcf7cea762cce`:** `reference/src/glossary.md:18–220`; **`verus-lang/verified-memory-allocator` @ `7d120970f8d63157ae9bf3b2361192d29bc0acaa`:** `verus-mimalloc/linked_list.rs:190–210, 394–405`.
- **Papers:** Villani et al., PLDI 2025 (`doi:10.1145/3735592`); Jung et al., POPL 2020 (`doi:10.1145/3371109`); Jung et al., POPL 2018 (`doi:10.1145/3158154`); Lee et al., OOPSLA 2018 (`doi:10.1145/3276495`).
- **Execution (`python3` 3.13, `2026-11-20`):** Verified `777` valid / `64,759` invalid 8-bit `Layout` pairs + 64-bit bounds, `fits()` vs. exact match, in-place `realloc` stale-handle and interior self-referential pointer `DeadAllocation`, `Uninit` preservation vs. `&[u8]` `InvalidUninitScalar`, and Tree Borrows `Weak`/`Strong` protector + `outside_perm = ReservedFrz` checks (`exit 0`).

## Revalidation

1. **Upstream Diffs (< 1 min):** Diff `library/core/src/alloc/{layout.rs, global.rs, mod.rs}`, `library/alloc/src/{alloc.rs, raw_vec/mod.rs}` (`rust-lang/rust`), `src/shims/alloc.rs` and `src/borrow_tracker/tree_borrows/tree.rs` (`rust-lang/miri`), and `spec/mem/basic.md` (`minirust/minirust`) against the pinned SHAs.
2. **Self-Contained Executable Probe (`python3`, stdlib only, < 0.1s):**

```python
#!/usr/bin/env python3
"""Verify Layout bounds, fits(), ZST dangling, in-place realloc invalidation, and Tree Borrows."""
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple


def layout_ok(sz: int, al: int, bits: int) -> bool:
    imax = (1 << (bits - 1)) - 1
    return al > 0 and (al & (al - 1)) == 0 and al <= imax + 1 and 0 <= sz <= (imax + 1) - al


assert sum(layout_ok(s, a, 8) for a in range(256) for s in range(256)) == 777
assert layout_ok(0, 1 << 63, 64) and not layout_ok(1, 1 << 63, 64)
assert layout_ok((1 << 63) - 1, 1, 64) and not layout_ok((1 << 63) - 1, 2, 64)


class Ub(Exception):
    pass


@dataclass
class Byte:
    init: bool
    val: int = 0
    prov: Optional[Tuple[int, int]] = None


@dataclass
class Node:
    tag: int
    parent: Optional[int]
    perm_in: str
    perm_out: str
    lo: int
    hi: int
    acc_in: bool = False
    prot: Optional[str] = None


@dataclass
class Block:
    aid: int
    addr: int
    req: int
    act: int
    align: int
    live: bool
    data: List[Byte]
    nodes: Dict[int, Node]


class Mem:
    def __init__(self) -> None:
        self.b: Dict[int, Block] = {}
        self.nid, self.ntag, self.na = 1, 1, 0x10000

    def alloc(self, req: int, align: int, act: Optional[int] = None, zero: bool = False, addr: Optional[int] = None):
        assert layout_ok(req, align, 64)
        act = req if act is None else act
        if addr is None:
            self.na = (self.na + align - 1) & ~(align - 1)
            addr = self.na
            self.na += max(act, 64)
        aid, r = self.nid, self.ntag
        self.nid += 1
        self.ntag += 1
        self.b[aid] = Block(aid, addr, req, act, align, True, [Byte(zero) for _ in range(act)],
                            {r: Node(r, None, "Unique", "Unique", 0, act)})
        return ((aid, r), addr)

    def _tb(self, aid: int, tag: int, off: int, n: int, wr: bool) -> None:
        blk = self.b[aid]
        for nid, nd in blk.nodes.items():
            cur, loc = tag, False
            while cur is not None:
                if cur == nid:
                    loc = True
                    break
                cur = blk.nodes[cur].parent
            for p in range(off, off + n):
                inr = nd.lo <= p < nd.hi
                perm = nd.perm_in if inr else nd.perm_out
                if loc:
                    if perm == "Disabled" or (wr and perm == "Frozen"):
                        raise Ub(perm)
                    if inr:
                        nd.acc_in = True
                        if wr and perm == "ReservedFrz":
                            nd.perm_in = "Unique"
                    elif wr and perm == "ReservedFrz":
                        nd.perm_out = "Unique"
                elif wr:
                    if nd.prot and perm in ("Unique", "Frozen", "ReservedFrz"):
                        raise Ub("ProtectorViolation")
                    if perm in ("Unique", "Frozen", "ReservedFrz"):
                        if inr:
                            nd.perm_in = "Disabled"
                        else:
                            nd.perm_out = "Disabled"

    def reborrow(self, ptr, lo: int, ln: int, prot: Optional[str] = None):
        prov, addr = ptr
        if prov is None:
            assert ln == 0
            return ptr
        aid, ptag = prov
        t = self.ntag
        self.ntag += 1
        self.b[aid].nodes[t] = Node(t, ptag, "ReservedFrz", "ReservedFrz", lo, lo + ln, prot=prot)
        return ((aid, t), addr + lo)

    def load(self, ptr, n: int, align: int, typed_u8: bool = False) -> List[Byte]:
        prov, addr = ptr
        assert addr and addr % align == 0
        if n == 0:
            return []
        if prov is None:
            raise Ub("NoProvenance")
        blk = self.b[prov[0]]
        if not blk.live:
            raise Ub("DeadAlloc")
        off = addr - blk.addr
        assert 0 <= off and off + n <= blk.act
        self._tb(prov[0], prov[1], off, n, False)
        out = [Byte(x.init, x.val, x.prov) for x in blk.data[off:off + n]]
        if typed_u8 and any(not x.init for x in out):
            raise Ub("InvalidUninitScalar")
        return out

    def store(self, ptr, bs: List[Byte], align: int) -> None:
        prov, addr = ptr
        assert addr and addr % align == 0
        if not bs:
            return
        if prov is None:
            raise Ub("NoProvenance")
        blk = self.b[prov[0]]
        if not blk.live:
            raise Ub("DeadAlloc")
        off = addr - blk.addr
        assert 0 <= off and off + len(bs) <= blk.act
        self._tb(prov[0], prov[1], off, len(bs), True)
        for i, x in enumerate(bs):
            blk.data[off + i] = Byte(x.init, x.val, x.prov)

    def dealloc(self, ptr, req: int, align: int, exact: bool) -> None:
        aid, tag = ptr[0]
        blk = self.b[aid]
        assert blk.live and ptr[1] == blk.addr
        if exact and (req != blk.req or align != blk.align):
            raise Ub("ExactMismatch")
        if not exact and not (align == blk.align and blk.req <= req <= blk.act):
            raise Ub("FitsMismatch")
        self._tb(aid, tag, 0, blk.act, True)
        if any(nd.prot == "Strong" and nd.acc_in for nd in blk.nodes.values()):
            raise Ub("StrongProtectedDealloc")
        blk.live = False

    def realloc_in_place(self, ptr, old_sz: int, new_sz: int, align: int, typed_u8: bool = False):
        blk = self.b[ptr[0][0]]
        np = self.alloc(new_sz, align, addr=blk.addr)
        self.store(np, self.load(ptr, min(blk.req, new_sz), 1, typed_u8=typed_u8), 1)
        self.dealloc(ptr, old_sz, align, exact=True)
        return np


def must_ub(fn, msg: str) -> None:
    try:
        fn()
    except Ub as e:
        assert msg in str(e), e
        return
    raise AssertionError(msg)


m = Mem()
dangling = (None, 8)
assert m.load(dangling, 0, 8) == [] and m.reborrow(dangling, 0, 0) == dangling
must_ub(lambda: m.load(dangling, 1, 1), "NoProvenance")
p = m.alloc(16, 8)
m.store(p, [Byte(True, 1, p[0]), Byte(True, 2, None)], 1)
p2 = m.realloc_in_place(p, 16, 32, 8)
assert p2[1] == p[1]
must_ub(lambda: m.load(p, 1, 1), "DeadAlloc")
must_ub(lambda: m.load((m.load(p2, 1, 1)[0].prov, p[1]), 1, 1), "DeadAlloc")
must_ub(lambda: m.realloc_in_place(p2, 32, 64, 8, typed_u8=True), "InvalidUninitScalar")
s = m.alloc(32, 8, zero=True)
rp = m.reborrow(s, 0, 32, prot="Strong")
m.load(rp, 4, 4)
must_ub(lambda: m.dealloc(s, 32, 8, True), "ProtectorViolation")
must_ub(lambda: m.dealloc(rp, 32, 8, True), "StrongProtectedDealloc")
print("OK: Layout, ZST, fits, in-place realloc, uninit, and Tree Borrows checks passed.")
```
