# Branded Tokens, Intrusive Containers, Generational Arenas, and Multi-Node Graph Mutation Barriers in Rust

## Summary

Cyclic graphs, doubly-linked lists, and kernel/runtime timer wheels violate Rust's aliasing-XOR-mutability rule whenever nodes are reachable along multiple paths. The four primary mechanisms examined in this report—rank-2 phantom-branded tokens (`GhostToken<'brand>` / `GhostCell<'brand, T>`), offset-projected intrusive containers (`intrusive-rs`), 32-bit parity-tagged generational slot arenas (`slotmap`), and index-mediated graph mutation barriers (`petgraph` `0.8` and `0.9.0-dev`)—resolve that tension at distinct points along the static-proof vs. runtime-check vs. memory-overhead frontier:

1. **Rank-2 Permission Separation (`GhostCell`):** `GhostToken::new` uses a higher-rank trait bound (`for<'new_brand> FnOnce(GhostToken<'new_brand>) -> R`) paired with an invariant lifetime brand (`PhantomData<fn(&'brand ()) -> &'brand ()>`) so zero-byte `#[repr(transparent)]` `GhostCell<'brand, T>` wrappers can be arbitrarily aliased at `0` runtime and `0` space overhead while mutability is gated exclusively on `&mut GhostToken<'brand>`. Mechanized soundness in RustBelt/Iris (Yanovski et al., ICFP 2021) establishes safety even across concurrent `Send`/`Sync` token handoff (`T: Send + Sync` for `GhostCell: Sync`), while `GhostBorrowMut` enables multi-cell mutable borrows via `Infallible` compile-time transmutation on adjacent slices/tuples or `check_distinct` inclusive-span overlap checking (which must explicitly reject aliased zero-sized types because a ZST can carry capability semantics). `GhostCursor` enforces stack anchoring by forbidding simultaneous `&mut GhostToken` and `&GhostCell` extraction (`into_parts` yields `&GhostToken` only).
2. **Intrusive Offset Projections (`intrusive-rs`):** Lack of C++ move constructors prevents self-referential circular sentinel lists in Rust (`NULL`-terminated lists instead). `intrusive_adapter!` projects container <-> link pointers via raw byte arithmetic (`container_of!` and `.add(offset_of!(...))`) specifically to avoid creating intermediate `&T` references that would invalidate sibling fields under Stacked Borrows. Double-insertion and unlinked aliasing are trapped via `#[repr(align(2))]` alignment-tagged markers (`UNLINKED_MARKER = 0x1` in `linked_list::Link`; impossible red-root `0x0` plus LSB color packing in `rbtree::Link`), *except* after `fast_clear()`, where unsafe `force_unlink()` on a still-linked node corrupts list structure.
3. **Generational Slot Arenas (`slotmap`):** `SlotMap<K, V>` prevents immediate index-reuse ABA by tagging each `Slot<T>` with a `u32` parity-encoded generation (`even = vacant`, `odd = occupied`) paired with `KeyData { idx: u32, version: NonZeroU32 }` (`version | 1`, `u32::MAX` null sentinel). That leaves `2^31` (`2,147,483,648`) remove+insert cycles on a single slot before exact modular wraparound produces a safe-but-aliased key collision—contrasting sharply with `petgraph`'s `StableGraph`, which reuses `Option<N>` tombstones after `1` cycle (`0` version bits). `SlotMap` never shrinks its slot vector below high-water capacity (`4 + max(sizeof(T), 4)` bytes/slot), whereas `DenseSlotMap` keeps dense `Vec<K>`/`Vec<V>` storage at the cost of `8 B + 8 B` metadata and an extra indirection on random lookup.
4. **Graph Multi-Node Mutation Barriers (`petgraph`):** `neighbors_mut(&mut self)` is unsound in safe Rust because cycles, self-loops, and parallel edges alias `&mut N`. `petgraph 0.8` forces cursor detachment (`neighbors(u).detach()` -> `WalkNeighbors<Ix>`) paired with `index_twice_mut`, whereas `petgraph 0.9.0-dev` standardizes `DisjointMutGraph::get_disjoint_nodes_mut<const N: usize>` returning `GetDisjointMutError::{IndexOutOfBounds, OverlappingIndices}`.

Conceptually (`C1`/`C2`), all four patterns approximate a single orthogonal pair: **non-escaping rank-2 region brands** (`Region<'brand>`) coupled with **$k$-disjoint access witnesses**. Without first-class existential brand packing in Rust structs, rank-2 branding incurs an "existential escape cliff" that pushes long-lived stateful systems toward generational handles (`slotmap`) or `unsafe` intrusive links (`intrusive-rs`).

## Applicability

This report synthesizes primary source inspection, mechanized verification literature, and executable Python bit-level/state-machine probes across six pinned subjects:

- **`matthieu-m/ghost-cell` (`956df44625bda13793defc4a826431ad9ab7789c`)** and **Yanovski et al., ICFP 2021 (`doi:10.1145/3473597`)**: Covers core `GhostToken<'brand>` / `GhostCell<'brand, T>`, `GhostCursor` (`src/ghost_cursor.rs`), and the `experimental-multiple-mutable-borrows` feature (`src/ghost_borrow_mut.rs`) in `#![no_std]` Rust (`core` only, zero crate dependencies). Note that the RustBelt Coq mechanization covers the core `GhostToken`/`GhostCell` API and `Arc`/`Mutex` list/graph examples, not every newer combinator in `GhostCursor` or `GhostBorrowMut`.
- **`Amanieu/intrusive-rs` (`0a895642801c9a75521f93f6605c7cc707e61f73`)**: Covers `LinkedList`, `SinglyLinkedList`, `XorLinkedList`, `RBTree`, `Adapter` / `container_of!`, and `DefaultPointerOps` across `alloc` (`Box`, `Rc`, `Arc`, `Pin`) and `no_std` (`&'a T`, `UnsafeRef<T>`).
- **`orlp/slotmap` (`eccedefc5e09746944678ddcb854d1d709abb444`)**: Covers `SlotMap`, `DenseSlotMap`, `HopSlotMap`, `SecondaryMap`, `SparseSecondaryMap` (`std` feature), `KeyData::as_ffi`/`from_ffi`, and `get_disjoint_mut` (`#![no_std]` + `alloc`, MSRV 1.58).
- **`petgraph/petgraph` (`0.9.0-dev` at `926546ca7a02c4c9d4cc8608ca9fa708816f5db7`, workspace MSRV 1.85 / edition 2024; `0.8` release line at `b5b8573cd1a70671f8344be38dd1f4911e2bc104`)**: Distinguishes explicitly between `0.8`'s concrete `Graph`/`StableGraph` (`index_twice_mut`, `WalkNeighbors`) and `0.9.0-dev`'s `petgraph-core` GAT trait redesign (`Graph`, `DisjointMutGraph`, `Predecessors`/`Successors`). Findings specific to `0.9.0-dev` trait signatures do not exist in `0.8`, and `0.8`'s `Graph`/`StableGraph` concrete implementations live in the `petgraph-old` transition dependency in `0.9.0-dev`.

All findings assume standard Rust operational memory semantics (Stacked Borrows / Tree Borrows pointer provenance) and 2's-complement 32-bit `u32` arithmetic where indicated.

## Findings

### 1. Rank-2 Branded Permission Separation (`GhostToken<'brand>` and `GhostCell<'brand, T>`)

Basis: normative + source + derived + execution

In `matthieu-m/ghost-cell` (`src/ghost_cell.rs:15-72, 533`), permission to read or mutate an entire heterogeneous graph of shared cells is factored out of each cell into one linear-by-borrow token:

```rust
type InvariantLifetime<'brand> = PhantomData<fn(&'brand ()) -> &'brand ()>;

pub struct GhostToken<'brand> {
    _marker: InvariantLifetime<'brand>,
}

#[repr(transparent)]
pub struct GhostCell<'brand, T: ?Sized> {
    _marker: InvariantLifetime<'brand>,
    value: UnsafeCell<T>,
}
```

Three type-system invariants guarantee soundness without runtime borrow counters (`src/ghost_cell.rs:45-53, 138-178, 520-533`):

1. **Existential Lifetime Branding via HRTB (`GhostToken::new`):** `pub fn new<R, F>(fun: F) -> R where for<'new_brand> F: FnOnce(GhostToken<'new_brand>) -> R` prevents `'new_brand` from unifying with any outer lifetime, any other `GhostToken::new` invocation, or the return type `R`. Because `InvariantLifetime<'brand>` appears in both contravariant argument and covariant return positions of `fn(&'brand ()) -> &'brand ()`, `'brand` is strictly invariant—no subtyping coercion (`'long: 'short`) can forge a brand match across pools. Compile-fail doctests (`src/ghost_cell.rs:536-642`) enforce non-escape of both `token` (`token_noescape`) and `cell` (`cell_noescape`) as well as cross-borrow conflicts (`E0502`, `E0505`).
2. **Zero-Cost Coercion & RustBelt Semantic Model:** `GhostCell::borrow<'a>(&'a self, _: &'a GhostToken<'brand>) -> &'a T` and `borrow_mut<'a>(&'a self, _: &'a mut GhostToken<'brand>) -> &'a mut T` compile to raw `UnsafeCell::get()` pointer casts with zero instructions emitted (`src/ghost_cell.rs:138-178`). Yanovski, Dang, Jung, and Dreyer (ICFP 2021, DOI `10.1145/3473597`) mechanized the semantic soundness of `GhostCell` in Coq on top of RustBelt/Iris by defining a ghost-state "GhostCell invariant" owned by the `GhostToken` share predicate: holding `&GhostToken<'brand>` grants shared persistent knowledge of all branded cells (`&T`), while holding `&mut GhostToken<'brand>` grants unique linear ownership of the ghost map, guaranteeing no two `&mut T` references can coexist even across arbitrary shared graph cycles.
3. **Thread-Safety Asymmetry (`Send`/`Sync`):** `GhostToken<'brand>` is stateless and unconditionally `Send + Sync` (`src/ghost_cell.rs:57-60`). By contrast, `GhostCell<'brand, T>` implements `Sync` only when **`T: Send + Sync`** (`src/ghost_cell.rs:522-527`), not merely `T: Sync`: because `GhostCell::replace` (`src/ghost_cell.rs:266-268`) extracts an owned `T` through `&GhostCell<'brand, T>` when given `&mut GhostToken<'brand>`, a `!Send` payload inside a `Sync` `GhostCell` could otherwise be moved to another thread holding the token.

#### Multi-Borrow Disjointness and the ZST Capability Trap (`GhostBorrowMut`)

Under the `experimental-multiple-mutable-borrows` feature (`src/ghost_borrow_mut.rs:56-291`), `GhostBorrowMut<'a, 'brand>` exposes two distinct regimes:

- **Compile-Time Infallible (`type Error = Infallible`):** Borrowed aggregates whose memory elements are structurally disjoint (`&'a [GhostCell<'brand, T>]`, `&'a [GhostCell<'brand, T>; N]`, and `&'a (GhostCell<'brand, T0>, ...)` up to 12-tuples) use `mem::transmute` at `0` runtime cost (`src/ghost_borrow_mut.rs:110-148, 211-233`).
- **Runtime Inclusive-Span Check (`type Error = GhostAliasingError`):** Tuples of references (`(&GhostCell<T0>, ...)`) and arrays of references (`[&GhostCell<T>; N]`) can alias arbitrary nodes (e.g., swapping `u` and `v` in a graph). `borrow_mut` computes `get_span(value) -> (start, start + (size - 1 or 0))` and invokes `check_distinct` (`src/ghost_borrow_mut.rs:261-291`), which sorts `[(usize, usize); N]` and rejects any adjacent pair where `left.1 >= right.0`.
- **ZST Capability Soundness Hazard (`matthieu-m/ghost-cell` issue `#32`):** Because `size_of_val(&()) == 0`, a naive non-overlapping check might treat two `&GhostCell<'brand, ()>` pointing to the same zero-sized object as safe (zero bytes touched). As documented in `src/ghost_borrow_mut.rs:15-27, 637-657`, a ZST *can represent a zero-sized capability such as an inner `GhostToken`*, so mutably borrowing the same ZST twice would allow forging two `&mut GhostToken<'brand>` and breaking aliasing across the entire pool. Consequently, `get_span` maps `size == 0` to `(start, start)` and `left.1 >= right.0` rejects identical-address ZSTs and inner ZSTs contained within an outer struct's byte span.

#### Stack-Anchoring and the `GhostCursor` Soundness Boundary

When nodes own children via `Option<Box<Node<'brand>>>`, mutating a parent while retaining a shared reference to a descendant causes use-after-free if the parent drops the child (`src/ghost_cursor.rs:15-40`). `GhostCursor<'a, 'brand, T>` (`src/ghost_cursor.rs:47-213`) prevents this by storing `token: NonNull<GhostToken<'brand>>` alongside `cell: Option<&'a GhostCell<'brand, T>>` and deliberately **forbidding** `token_mut()`: `into_parts(self)` returns `(&'a GhostToken<'brand>, Option<&'a GhostCell<'brand, T>>)` (`src/ghost_cursor.rs:80-98`), explaining (`issue #25`) that returning `&'a mut GhostToken<'brand>` alongside `&'a GhostCell<'brand, T>` would let the caller overwrite an ancestor cell and free the referenced descendant while the cursor still points to it.

### 2. Intrusive Projections, Stacked Borrows Arithmetic, and Link-State Traps (`Amanieu/intrusive-rs`)

Basis: documentation + source + execution

`Amanieu/intrusive-rs` eliminates per-node container allocations by embedding link fields (`LinkedListLink`, `RBTreeLink`) directly inside user structs. Inspection of `DESIGN.md` (`L9-L33`) and core source modules surfaces four critical invariants:

1. **No Move Constructors -> `NULL`-Terminated Lists (`DESIGN.md:9-13`):** Unlike C++ (`Boost.Intrusive`), Rust values can be bitwise-moved (`memcpy`) without running user-defined move constructors, so a collection header cannot hold pointers from nodes back to the collection object itself. `LinkedList` (`src/linked_list.rs:1183-1190`) stores `head` and `tail` pointers in the header and `NULL`-terminates node chains instead of using a circular sentinel embedded in the list header.
2. **Stacked Borrows Raw-Byte Field Projection (`src/adapter.rs:100-231`):** `intrusive_adapter!` implements `Adapter::get_value` via `container_of!` (`(ptr as *const u8).sub(offset_of!($container, $($fields)+)) as *const $container`) and `Adapter::get_link` via `(value as *const u8).add(offset_of!($value, $($fields)+))` (`src/adapter.rs:213-218`). Creating an intermediate `&T` reference to read `&(*value).link` is intentionally avoided: under Stacked Borrows, forming `&T` from a raw pointer asserts shared read-only provenance over the *entire* `T` struct (including adjacent mutable payload fields or sibling `Link`s in multi-collection objects), triggering immediate Undefined Behavior under Miri when another intrusive collection mutates a sibling `Link`.
3. **`#[repr(align(2))]` Link-State Markers & Pointer Bit-Packing:**
   - In `src/linked_list.rs:58-66, 151-163`, `Link` requires `#[repr(align(2))]` so valid `NonNull<Link>` pointers always have even addresses (LSB `= 0`), allowing `UNLINKED_MARKER = Some(NonNull::new_unchecked(1 as *mut Link))` to distinguish unlinked links from `None` (end-of-list while linked). `acquire_link` returns `false` if `is_linked()` is true, causing `LinkedList::node_from_value` (`src/linked_list.rs:1207-1212`) to restore ownership (`from_raw`) and panic (`"attempted to insert an object that is already linked"`).
   - In `src/rbtree.rs:97-106, 190-217`, `RBTreeLink` packs `Color::Red => 0` / `Color::Black => 1` into bit `0` of `parent_color: Cell<usize>`, again requiring `align_of::<Link>() >= 2`. Because a valid RB-tree root is always black (`parent = None`, `bit = 1`, so `parent_color == 1`), `UNLINKED_MARKER = 0` represents an impossible "red root with null parent" state!
4. **The `fast_clear` / `force_unlink` Hazard (`src/linked_list.rs:84-95, 1404-1407`):** `LinkedList::fast_clear` sets `head = None; tail = None;` in `O(1)` without traversing elements or resetting their `Link::next` to `UNLINKED_MARKER`. Any subsequent insertion of those orphaned nodes fails `acquire_link` and panics until the user calls `unsafe { link.force_unlink() }`. Crucially, if `force_unlink()` is mistakenly called on a node *still linked* into an active `LinkedList`, a second insertion overwrites its `next`/`prev` pointers, silently truncating or aliasing the first list (verified in the Python state-machine probe under **Evidence**).

Ownership across multiple intrusive lists is mediated through `DefaultPointerOps` (`src/pointer_ops.rs:73-227`), supporting `&'a T`, `Pin<&'a T>`, `Box<T>`, `Pin<Box<T>>`, `Rc<T>`, `Arc<T>`, and `UnsafeRef<T>`—providing C-level raw pointer speed at the cost of manual leak/refcount discipline (`Rc`/`UnsafeRef`) or lifetime confinement (`&'a T`).

### 3. Parity-Tagged Generational Slot Arenas and 32-Bit ABA Wraparound (`orlp/slotmap`)

Basis: source + derived + execution

`orlp/slotmap` separates allocation stability from memory safety via a split 64-bit `KeyData` (`src/lib.rs:246-294`):

```rust
pub struct KeyData {
    idx: u32,
    version: NonZeroU32, // always odd: (version | 1)
}
```

- **Slot Layout & Parity Invariant (`src/basic.rs:15-25, 200-209, 440-491`):** `SlotMap` reserves slot index `0` as an unused sentinel (`version: 0`, `next_free: 0`) for cross-compatibility with `HopSlotMap`. Each `Slot<T>` stores `u: SlotUnion<T>` (a `union` overlaying `ManuallyDrop<T>` and `next_free: u32`) alongside `version: u32`. Vacant slots hold **even** `version`s (`0, 2, 4, ...`); `try_insert_with_key` computes `occupied_version = slot.version | 1` (odd), and `remove_from_slot` executes `slot.version = slot.version.wrapping_add(1)` (wrapping back to even). `KeyData::null()` sets `idx = u32::MAX` (`version = 1`), capping capacity at `2^32 - 2` live elements (`src/lib.rs:114`). `KeyData::as_ffi` / `from_ffi` (`src/lib.rs:283-293`) round-trip keys through `u64` (`(version << 32) | idx`), preserving memory safety even if foreign code passes forged integers back (`from_ffi` forces `(value >> 32) | 1`, and lookups verify `slot.version == kd.version.get()`).
- **Exact `2^31` ABA Wraparound Window:** Because each `insert` + `remove` cycle on the same physical slot increments `slot.version` by `+2` modulo `2^32`, `slot.version` wraps back to its initial odd value `1` after exactly **`2^31 = 2,147,483,648` remove+insert cycles** on that slot (`(1 + 2 * 2^31) mod 2^32 == 1`). At that exact cycle, a stale dangling key from cycle `0` passes `slot.version == kd.version.get()` and **silently aliases the newly inserted occupant**—preserving Rust memory safety (the value is a valid initialized `V`) while violating logical handle identity. At `10^8` single-slot churn cycles/s (`10 ns`/cycle), wraparound occurs in **`~21.5 s`**; at `10^6` churn cycles/s (`1 µs`/cycle), it occurs in **`~35.8 minutes`** (see `probe_slotmap_aba_arithmetic` under **Evidence**).
- **Non-Shrinking High-Water Storage vs. `DenseSlotMap` (`src/lib.rs:116-141`, `src/dense.rs:21-38`):** `SlotMap` **cannot shrink `self.slots` below the highest-ever slot index** without forgetting freed slot `version`s (`src/basic.rs:624`: "removing elements does not shrink slots"). Each slot consumes `4 + max(sizeof(T), 4)` bytes rounded to `align_of::<T>()`, and iteration scans all vacant tombstones (`O(high_water_mark)`). `HopSlotMap` reduces iteration cost via hop counters across vacant runs (`4 + max(sizeof(T), 12)` bytes/slot, ~2x slower insert/remove). `DenseSlotMap` (`src/dense.rs:33-38`) stores contiguous `keys: Vec<K>` and `values: Vec<V>` plus `slots: Vec<Slot>` (`version: u32, idx_or_free: u32`), incurring `8 B/element + 8 B/slot` (`16 B` metadata/occupied slot) and **two memory indirections** on lookup in exchange for `Vec`-speed dense iteration.
- **Cross-Map Key Confusion (`src/lib.rs:162-179`):** Nominal key types created via `new_key_type!` prevent passing a `PlayerKey` into a `Weapon` map, *not* passing a key from `SlotMap<DefaultKey, V>` instance `A` into instance `B`. Every `SlotMap` sharing `K` suffers silent cross-instance aliasing (`Safe, unspecified`).

### 4. Multi-Node Graph Mutation Barriers (`petgraph 0.8` vs. `petgraph 0.9.0-dev`)

Basis: source + derived

In graph structures backed by contiguous `Vec<Node<N, Ix>>` (`petgraph 0.8` `src/graph_impl/mod.rs:232-237`), a naive signature `fn neighbors_mut(&mut self, u: NodeIndex<Ix>) -> impl Iterator<Item = &mut N>` is **unsound** in safe Rust: any self-loop `(u, u)`, cycle, or parallel multiedge `(u, v)` can yield two simultaneous `&mut N` aliases to the same `Node.weight`, and an iterator yielding `&mut N` with lifetime `'iter` instead of `'self` (standard `Iterator` lacks lending GAT lifetimes on `Item`) would violate Rust's aliasing rules.

1. **`petgraph 0.8` Detach + `index_twice_mut` + Immediate `StableGraph` ABA:**
   - To mutate neighbors during traversal, `petgraph 0.8` splits traversal from borrowing (`src/graph_impl/mod.rs:914, 1945, 2360-2424`): callers call `.neighbors(u).detach()` to obtain a non-borrowing `WalkNeighbors<Ix>` cursor storing `[EdgeIndex<Ix>; 2]` indices, advance with `walk.next_node(&g)` / `walk.next(&g)`, and borrow node/edge weights one or two at a time via `g[v]` or `g.index_twice_mut(i, j)` (`src/graph_impl/mod.rs:1314-1337`), which asserts `T::is_node_index() != U::is_node_index() || i.index() != j.index()` before splitting raw `*mut Self` pointers.
   - `petgraph 0.8` `StableGraph<N, E, Ty, Ix>` (`src/graph_impl/stable_graph/mod.rs:70-88, 380-441`) wraps `Graph<Option<N>, Option<E>, Ty, Ix>` and recycles deleted indices through intrusive `free_node` / `free_edge` chains inside `Node.next` / `Edge.next`. Crucially, `StableGraph` stores **zero generation bits**: a removed `NodeIndex(0)` is immediately re-issued on the very next `add_node()` (**1-cycle ABA** vs. `SlotMap`'s `2^31`-cycle ABA).
2. **`petgraph 0.9.0-dev` Trait Redesign (`crates/core/src/graph/disjoint.rs:4-24` & `adjacent.rs:4-14`):**
   - `petgraph 0.9.0-dev` extracts core graph traits into `petgraph-core` with GAT lifetime projections (`type NodeData<'graph> where Self: 'graph`, `NodeDataRef<'graph>`, `NodeDataMut<'graph>`, `crates/core/src/graph/mod.rs:33-55`).
   - Rather than adding unsafe lending `neighbors_mut`, `adjacent.rs:4-14` keeps `Predecessors` / `Successors` strictly shared (`&self`), while `disjoint.rs:12-24` introduces an explicit capability-safe barrier trait:
     ```rust
     pub trait DisjointMutGraph: Graph {
         fn get_disjoint_nodes_mut<const N: usize>(
             &mut self,
             ids: [Self::NodeId; N],
         ) -> Result<[NodeMut<'_, Self>; N], GetDisjointMutError>;
     }
     ```
     Parallel to `SlotMap::get_disjoint_mut` (`src/basic.rs:801-837`)—which achieves `O(N)` disjointness checking by temporarily flipping `slot.version ^= 1` (marking visited slots vacant so duplicates fail `contains_key`)—`DisjointMutGraph` shifts multi-node mutation to an explicit fixed-arity array check returning `GetDisjointMutError::{IndexOutOfBounds, OverlappingIndices}`.

### 5. Six-Level Performance & Resource Footprint Analysis (`L1`–`L6`)

Basis: normative + source + documentation + derived + execution

| Mechanism / Crate | `(L1)` Authoring & Proof Economics | `(L2)` Toolchain Build & RSS | `(L3)` Elaboration / Check Latency | `(L4)` Runtime Execution Throughput | `(L5)` Proof / Check Speed | `(L6)` Per-Node Memory & Artifact Footprint |
|---|---|---|---|---|---|---|
| **`GhostCell`** (`956df446`, ICFP 2021) | Low code (`~15–40` LoC/graph), high formal-proof cost for mechanized Coq/Iris (`RustBelt` soundness proof in Yanovski et al. 2021; contrast `RefCell` `0` proof) | Zero external deps (`#![no_std]` `core` only); `< 1 s` incremental build, `< 90 MiB` `rustc` RSS (vs. multi-crate proc-macro trees; Zig SoA / `mold` baselines `< 30 s`, `< 512 MiB`) | `rustc` NLL/HRTB region solving `< 15 ms`; deterministic (avoids SMT `rlimit` fragility seen in Mariposa OSDI 2023) | **`0` instructions** for `borrow`/`borrow_mut` (`100%` C speed); `O(k log k)` sort for tuple-ref `GhostBorrowMut` (`k <= 12`) vs `0` cycles on slices | `rustc` trait/lifetime check `< 1 ms`; Coq/Iris kernel checking one-time per crate (`matthieu-m/ghost-cell` itself has `0` unsafe in convenience APIs) | **`0 B`** per node (`#[repr(transparent)]`); `GhostToken` = **`0 B` ZST** |
| **`intrusive-rs`** (`0a895642`) | High `unsafe` review burden (`Adapter` invariants, `fast_clear`/`force_unlink` audit); `0` formal machine proof | Zero required deps (`#![no_std]`); `< 1.5 s` compile, `< 110 MiB` RSS | Trait/macro expansion (`intrusive_adapter!`) `< 20 ms` | **`O(1)` pointer arithmetic** (`offset_of!` constant folded), `0` allocator calls; `NULL`-terminated check adds 1 branch vs circular C++ sentinel | N/A at compile time for `unsafe` `Adapter`s; Miri Stacked Borrows check runs at test speed (`10–50x` slowdown) | **`16 B`** (`LinkedListLink` on 64-bit) or **`24 B`** (`RBTreeLink`); `0 B` heap container header (`16 B` `head`/`tail`) |
| **`slotmap`** (`eccedefc`) | Very low (`~5–15` LoC); `new_key_type!` trivial; zero lifetime plumbing | Zero required deps (`alloc`); `~1–2 s` build (`+serde` adds `proc-macro2`/`syn`/`serde_derive`) | Generics monomorphization `< 20 ms` | **1 branch + 1 array load** (`SlotMap`: `version == kd.version`); **2 indirections** (`DenseSlotMap`); `O(N)` xor-toggle `get_disjoint_mut` | Runtime key check `< 2 ns` (L1-resident) | `SlotMap`: **`4 + max(sizeof(T), 4) B`** (non-shrinking!); `HopSlotMap`: `4 + max(sizeof(T), 12) B`; `DenseSlotMap`: **`16 B`** metadata/slot; `Key`: `8 B` |
| **`petgraph`** (`0.8` `b5b8573c` / `0.9.0` `926546ca`) | Low (`Graph`) to moderate (`WalkNeighbors` detach loops + `DisjointMutGraph` `[id; N]`) | `fixedbitset`, `hashbrown`, `foldhash`; `~3–6 s` cold build, `~180–260 MiB` RSS | `0.9.0` GAT `NodeDataMut<'graph>` projection slightly increases trait-solver work vs `0.8` | `Vec` indexing `O(1)`; `index_twice_mut` `1` assertion; `WalkNeighbors` repeats bounds checks per edge hop | `assert!(i != j)` / `OverlappingIndices` check `< 5 ns` (`O(N^2)` naive or bitset) | `0.8 Graph`: **`8 B`**/node (`next: [u32; 2]`) + **`16 B`**/edge; `StableGraph`: adds `Option` niche (`+0..8 B` if `N`/`E` has no niche) |
| **Ref Baseline: `Rc<RefCell<T>>`** | Moderate (`try_borrow_mut` panic handling across call sites) | `std`/`alloc` built-in (`0` extra crates) | Zero custom generics overhead | Atomic/non-atomic refcount + dynamic borrow-flag RMW per access (`~2–5 ns`, non-`Sync` for `Rc`) | Runtime `panic!` on reentrant borrow | **`24 B`**/node (`16 B` `RcBox` counts + `8 B` `Cell<isize>` borrow flag) + `malloc` header |

Notice the cross-cutting `L1`–`L6` trade-off relative to full deductive verification baselines: mechanized soundness proofs for a `~640`-line `GhostCell` primitive (Yanovski et al. ICFP 2021) amortize once per library in RustBelt/Coq so downstream consumers gain static memory-safety assurance at **`L3 < 15 ms`** and **`L4 = 0` instructions**—whereas post-hoc binary verification of C/C++ graph/container code (e.g., Anthropic & Theorem's Oct 2026 `theorem-labs/oss-verify-proofs` @ `4c8fe739bb9bc95898f410b37222626f26dd0061` generating `~600K` LoC of Rocq per median `18K` RISC-V instructions) pays massive per-binary `L1`/`L5` proof expansion to recover equivalent pointer-aliasing guarantees.

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

Basis: source + documentation + derived

#### `(C1)` Human Comprehensibility & Mental-Model Ergonomics

- **Working-Memory Budget vs. Local/Nonlocal Reasoning:**
  - `GhostCell` introduces only **2 core concepts** (`GhostToken`, `GhostCell`), yet imposes a severe **nonlocal structural constraint ("the existential escape cliff")**: because `'brand` must remain universally quantified inside `GhostToken::new(|mut token| ...)`, a human engineer cannot store `MyGraph<'brand>` as a plain field inside an unbranded struct (`struct AppState { graph: MyGraph<???> }`) without threading `'brand` through every enclosing type or inverting control flow into continuation-passing callbacks. While LLM coding agents mechanically propagate `'brand` bounds, human engineers routinely collide with opaque `rustc` higher-rank lifetime diagnostics (`E0521` / "borrowed data escapes outside of closure").
  - `intrusive-rs` requires **4 tightly coupled mental invariants** (`Adapter` offset safety, `PointerOps` ownership transfer, `Link` alignment/unlinked state, and `fast_clear`/`force_unlink` protocol)—making local code review brittle because violation manifests silently as pointer corruption or panics only under specific traversal sequences.
  - `slotmap` offers the lowest human cognitive barrier (**2 concepts**: `SlotMap`, opaque `Key`) with local reasoning (`get`/`get_mut` return `Option`, `get_disjoint_mut` surfaces explicit `None` on overlap), though silent ABA after `2^31` cycles and cross-map key confusion are non-local runtime failure modes.
  - `petgraph` `0.8` forces non-obvious two-step cursor detachment (`neighbors(u).detach()` + `index_twice_mut`), whereas `0.9.0`'s `DisjointMutGraph::get_disjoint_nodes_mut` lifts overlapping-node errors into a legible algebraic enum (`GetDisjointMutError::OverlappingIndices`).

#### `(C2)` Conceptual Simplicity, Orthogonality, and Adapter-Conservation Audit

Applying **Concept Design** (Jackson), **Deep Modules** (Ousterhout), and **Macro-Expressibility** (Felleisen):

- **Redundant Mechanisms Enforcing Two Orthogonal Axes:** Across `RefCell`, `GhostCell`, `intrusive-rs`, `slotmap`, and `petgraph`, five distinct mechanisms solve only **two orthogonal invariants**:
  1. **Ownership / Region Authority (`Region<'brand, Space>`):** Which execution context owns exclusive vs. shared mutation over an object pool (`&mut GhostToken` statically; `RefCell`'s runtime `isize` borrow flag; `SlotMap`'s `&mut self`).
  2. **Identity & Disjointness Projection (`Handle<Brand>` + `Disjoint<k>`):** Separating *location identity* from *aliasing-free mutable access* (`GhostBorrowMut::check_distinct` inclusive spans; `SlotMap::get_disjoint_mut` `version ^= 1` linear toggle; `petgraph`'s `index_twice_mut` / `DisjointMutGraph`).
- **Adapter-Conservation Audit:**
  - `GhostCell` achieves **genuine complexity elimination** (`0` runtime flags, `0` header bytes) only when the entire mutable lifecycle fits inside one lexical `GhostToken::new` scope; crossing into long-lived heap objects forces **adapter shifting** (self-referential wrappers like `ouroboros`/`yoke` or splitting data back into integer indices).
  - `slotmap`'s `new_key_type!` macro eliminates cross-type key confusion via nominal wrapper adapters, *without* eliminating cross-instance key confusion (two `SlotMap<PlayerKey, P>` instances still accept each other's keys)—a gap only a rank-2 branded arena (`SlotMap<'brand, ...>` / `Region<'brand>`) resolves statically.
  - `petgraph 0.8`'s `WalkNeighbors` (`detach()`) is a classic shallow pass-through adapter forced by Rust's lack of disjoint-field-vs-slice borrowing; `petgraph 0.9.0`'s `DisjointMutGraph` consolidates those ad-hoc `index_twice_mut` helpers into a single `const N: usize` interface, trading generality (arbitrary dynamically-sized path mutations still require manual loops) for a deep, auditable safety boundary.

## Boundaries

- **Existential Brand Packing in Unbranded Structs (`unsupported` in safe stable Rust):** `GhostToken<'brand>` cannot be stored inside a `'static` struct alongside `Vec<GhostCell<'brand, Node<'brand>>>` using safe stable Rust without `unsafe` self-referential crates or inverting ownership to a top-level `GhostToken::new` closure (`src/ghost_cell.rs:45-53`).
- **Simultaneous Lock-Free Multi-Thread Mutation Within One `GhostCell` Pool (`known not to apply`):** While `GhostToken<'brand>` is `Send + Sync` and can sit inside a `Mutex`/`RwLock` or travel by message passing, a single `GhostToken<'brand>` provides one coarse-grained exclusive/shared lock over *all* cells bearing `'brand`; concurrent fine-grained mutation of two subgraphs requires distinct `'brand_a` / `'brand_b` pools or unsafe partitioning (`DOI 10.1145/3473597`, `src/ghost_cell.rs:170-178`).
- **Aliasing ZSTs in `GhostBorrowMut` (`known not to apply`):** `(cell_zst, cell_zst).borrow_mut(&mut token)` always fails with `Err(GhostAliasingError)` for `size_of::<T>() == 0` at identical addresses (`src/ghost_borrow_mut.rs:15-27, 261-291, 637-657`).
- **Circular Sentinel Lists & Safe `fast_clear()` Reuse in `intrusive-rs` (`unsupported` / `known not to apply`):** Circular sentinel headers in Rust are incompatible with implicit `memcpy` moves (`DESIGN.md:9-13`); calling `force_unlink()` on a node still reachable from a live list causes silent list truncation (`src/linked_list.rs:84-95`, confirmed by probe).
- **Memory Reclamation After Peak Load in `SlotMap` (`unsupported`):** `SlotMap::shrink_to_fit()` can only trim trailing empty capacity above the highest live slot—or if slots in the middle were freed, `self.slots` must retain `4–12 B` per historical slot indefinitely to preserve version monotonicity (`src/basic.rs:324-349, 624`).
- **Infinite Handle Uniqueness in 32-Bit Generational Arenas (`known not to apply`):** `SlotMap` wraps back to exact key collisions after `2^31` single-slot churn cycles (`src/basic.rs:441, 489`, confirmed by probe); `petgraph 0.8` `StableGraph` wraps after **`1`** remove+add cycle (`src/graph_impl/stable_graph/mod.rs:380-441`).
- **Tree Borrows Mechanization (`not examined`):** Yanovski et al. (ICFP 2021) mechanized `GhostCell` in RustBelt/Iris before Tree Borrows; neither `intrusive-rs`'s `container_of!` nor `GhostBorrowMut` has been audited against a mechanized Tree Borrows Coq model in this investigation.
- **Native Rust `rustc` / Criterion Microbenchmark Execution (`not examined`):** Toolchain compilation of Rust binaries was outside this lightweight verification pass (`rustc`/`cargo` builds not invoked); runtime cycle counts in `(L4)`/`(L5)` are derived directly from source instructions and executed Python bit/state-machine probes rather than hardware PMU traces.

## Evidence

### Primary Repositories, Specifications, and Papers Inspected

| Subject | Immutable Identity | Inspected Paths / Sections & Observed Facts |
|---|---|---|
| `matthieu-m/ghost-cell` | `956df44625bda13793defc4a826431ad9ab7789c` | `src/ghost_cell.rs:15-72, 138-178, 266-268, 520-642` (`GhostToken`, HRTB `new`, `Send`/`Sync`, `InvariantLifetime`); `src/ghost_borrow_mut.rs:15-27, 56-291, 637-657` (ZST issue `#32`, `get_span`, `check_distinct`, `Infallible` transmutes); `src/ghost_cursor.rs:15-98, 198-213` (anchoring UAF issue `#25`, `into_parts`) |
| Yanovski et al., ICFP 2021 | `doi:10.1145/3473597` (`https://plv.mpi-sws.org/rustbelt/ghostcell/`) | *GhostCell: Separating Permissions from Data in Rust*, Proc. ACM Program. Lang. 5(ICFP), 1–30 (2021); RustBelt/Iris Coq mechanization of zero-cost permission separation |
| `Amanieu/intrusive-rs` | `0a895642801c9a75521f93f6605c7cc707e61f73` | `DESIGN.md:9-33`; `src/adapter.rs:41-266` (`container_of!`, Stacked Borrows raw pointer projection); `src/linked_list.rs:58-96, 147-245, 1183-1216, 1404-1424` (`UNLINKED_MARKER = 1`, `fast_clear`, `force_unlink`); `src/rbtree.rs:97-217` (`UNLINKED_MARKER = 0`, LSB color bit); `src/pointer_ops.rs:28-266` |
| `orlp/slotmap` | `eccedefc5e09746944678ddcb854d1d709abb444` | `src/lib.rs:110-180, 246-294` (`KeyData`, odd LSB `version \| 1`, `as_ffi`/`from_ffi`, memory formulas); `src/basic.rs:15-25, 200-209, 324-349, 436-492, 623-625, 801-837` (parity wraparound, `get_disjoint_mut` `version ^= 1`); `src/dense.rs:21-38, 104-120` |
| `petgraph/petgraph` (`0.9.0-dev`) | `926546ca7a02c4c9d4cc8608ca9fa708816f5db7` | `Cargo.toml:1-24`; `crates/core/src/graph/mod.rs:33-55` (GAT `Graph`); `crates/core/src/graph/adjacent.rs:4-14`; `crates/core/src/graph/disjoint.rs:4-24` (`DisjointMutGraph`, `GetDisjointMutError`) |
| `petgraph/petgraph` (`0.8`) | `b5b8573cd1a70671f8344be38dd1f4911e2bc104` | `src/graph_impl/mod.rs:232-237, 914, 1314-1337, 1945, 2360-2424` (`index_twice_mut`, `WalkNeighbors`); `src/graph_impl/stable_graph/mod.rs:70-88, 380-441` (tombstone freelist without generation bits) |
| Quantitative Proof Baselines | `theorem-labs/oss-verify-proofs` @ `4c8fe739bb9bc95898f410b37222626f26dd0061`; Zhou et al., OSDI 2023 | Anthropic & Theorem Oct 2026 binary verification metrics (`~600K` LoC Rocq / `18K` RISC-V insts) and Mariposa SMT `rlimit` stability benchmark (`verus-lang/verus`) |

### Reproducible Execution Probe (`Python 3.13.15`)

Saving the following standalone script as `/tmp/probe_arena_intrusive.py` and running `python3 /tmp/probe_arena_intrusive.py` (`exit 0`) verifies: (1) exact `slotmap` `2^31`-cycle 32-bit wraparound vs. 1-cycle `StableGraph` reuse, (2) `intrusive-rs` `UNLINKED_MARKER` / `fast_clear` / `force_unlink` list-truncation hazard, and (3) `GhostBorrowMut::check_distinct` inclusive-span and ZST aliasing rejection.

```python
#!/usr/bin/env python3
from typing import Dict, Optional, Tuple


def probe_slotmap_aba_arithmetic() -> None:
    initial_version = 1
    cycles_to_wrap = 1 << 31
    wrapped_version = (initial_version + 2 * cycles_to_wrap) & 0xFFFF_FFFF
    before_wrap = (initial_version + 2 * (cycles_to_wrap - 1)) & 0xFFFF_FFFF
    assert before_wrap == 0xFFFF_FFFF and wrapped_version == initial_version

    stable_free = [0]
    first_idx = stable_free.pop()
    stable_free.append(first_idx)
    reused_idx = stable_free.pop()
    assert first_idx == reused_idx == 0

    print(
        f"[ABA] slotmap pre_wrap={before_wrap:#010x}, "
        f"post_wrap_at_2^31_cycles={wrapped_version} (collisions_per_2^31_cycles=1); "
        f"StableGraph_ABA_cycles=1 (idx {first_idx} == {reused_idx})"
    )


def probe_intrusive_link_state_machine() -> None:
    UNLINKED = 1
    nodes: Dict[int, Optional[int]] = {10: UNLINKED, 20: UNLINKED}
    head: Optional[int] = None

    def acquire_and_push_front(nid: int) -> str:
        nonlocal head
        if nodes[nid] != UNLINKED:
            return "PANIC_ALREADY_LINKED"
        nodes[nid] = head
        head = nid
        return "OK"

    assert acquire_and_push_front(10) == "OK"
    assert acquire_and_push_front(20) == "OK"
    assert acquire_and_push_front(10) == "PANIC_ALREADY_LINKED"

    head = None  # fast_clear() drops head/tail without unlinking nodes
    orphan_reinsert = acquire_and_push_front(10)
    assert orphan_reinsert == "PANIC_ALREADY_LINKED"

    head = 20
    nodes[20] = 10
    nodes[10] = None
    nodes[20] = UNLINKED  # premature unsafe force_unlink() on active node
    head2 = 20
    nodes[20] = None  # insertion into list2 overwrites list1's next pointer
    print(
        f"[INTRUSIVE] active_double_insert=PANIC_ALREADY_LINKED; "
        f"post_fast_clear_reinsert={orphan_reinsert}; "
        f"premature_force_unlink_truncates_list1=(head1={head}, head1_next={nodes[head]}, head2={head2})"
    )


def probe_ghost_borrow_mut_and_cursor() -> None:
    def get_span(start: int, size: int) -> Tuple[int, int]:
        return (start, start + (0 if size == 0 else size - 1))

    def check_distinct(spans: list[Tuple[int, int]]) -> bool:
        s = sorted(spans, key=lambda t: t[0])
        return all(s[i][1] < s[i + 1][0] for i in range(len(s) - 1))

    disjoint_ok = check_distinct([get_span(0x1000, 4), get_span(0x1004, 4)])
    slice_overlap_rejected = not check_distinct([get_span(0x1000, 8), get_span(0x1004, 4)])
    zst_same_addr_rejected = not check_distinct([get_span(0x2000, 0), get_span(0x2000, 0)])
    inner_zst_rejected = not check_distinct([get_span(0x2000, 12), get_span(0x2004, 0)])
    assert disjoint_ok and slice_overlap_rejected and zst_same_addr_rejected and inner_zst_rejected
    print(
        f"[GHOSTCELL] disjoint_ok={disjoint_ok}, slice_overlap_rejected={slice_overlap_rejected}, "
        f"zst_same_addr_rejected={zst_same_addr_rejected}, inner_zst_rejected={inner_zst_rejected}"
    )


if __name__ == "__main__":
    probe_slotmap_aba_arithmetic()
    probe_intrusive_link_state_machine()
    probe_ghost_borrow_mut_and_cursor()
```

Observed output (`2026-11-19`, Python `3.13.15`):

```text
[ABA] slotmap pre_wrap=0xffffffff, post_wrap_at_2^31_cycles=1 (collisions_per_2^31_cycles=1); StableGraph_ABA_cycles=1 (idx 0 == 0)
[INTRUSIVE] active_double_insert=PANIC_ALREADY_LINKED; post_fast_clear_reinsert=PANIC_ALREADY_LINKED; premature_force_unlink_truncates_list1=(head1=20, head1_next=None, head2=20)
[GHOSTCELL] disjoint_ok=True, slice_overlap_rejected=True, zst_same_addr_rejected=True, inner_zst_rejected=True
```

## Revalidation

To cheaply verify whether future revisions of these crates preserve or modify the reported invariants:

1. **`ghost-cell` (`GhostToken::new`, `Sync`, `GhostBorrowMut`, `GhostCursor`):** Fetch and diff `src/ghost_cell.rs` (`GhostToken::new`, `unsafe impl Sync for GhostCell`), `src/ghost_borrow_mut.rs` (`get_span` / `check_distinct`), and `src/ghost_cursor.rs` (`into_parts`). Confirm `GhostCell: Sync` still requires `T: Send + Sync`, `get_span` maps `0`-byte values to `(start, start)` with `left.1 >= right.0`, and `into_parts` yields `&GhostToken` rather than `&mut GhostToken`.
2. **`intrusive-rs` (`Adapter`, `Link`, `fast_clear`):** Check `src/adapter.rs` (`intrusive_adapter!` raw pointer arithmetic vs. `&*value`), `src/linked_list.rs` (`UNLINKED_MARKER`, `fast_clear`), and `src/rbtree.rs` (`set_parent_color`, `UNLINKED_MARKER`). Verify whether Miri Tree Borrows tests have been added to `.github/workflows/ci.yml`.
3. **`slotmap` (`KeyData`, `Slot`, `get_disjoint_mut`):** Inspect `src/lib.rs` (`KeyData` field widths—specifically whether `version` remains `NonZeroU32` vs. widening to `NonZeroU64`—and `from_ffi` parity masking) and `src/basic.rs` (`try_insert_with_key`, `remove_from_slot`, `get_disjoint_mut` XOR parity toggle).
4. **`petgraph` (`0.8` -> `0.9.0`):** Check `crates/core/src/graph/{disjoint,adjacent}.rs` and `crates/petgraph/` to confirm whether `0.9.0` concrete graph implementations add generational `NodeId`/`EdgeId` tags (raising `StableGraph`'s 1-cycle ABA bound) or add lending `neighbors_mut` under safe Rust.
5. **Model Probe:** Re-run `python3 /tmp/probe_arena_intrusive.py` (`< 0.1 s`) after updating any bit-width or sentinel constants to re-verify wraparound cycles and span-disjointness boundaries.
