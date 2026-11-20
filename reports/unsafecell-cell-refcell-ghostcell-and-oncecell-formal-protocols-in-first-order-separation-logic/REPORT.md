# `UnsafeCell`, `Cell`, `RefCell`, `GhostCell`, and `OnceCell` Formal Protocols in First-Order Separation Logic

## Summary

Every safe interior-mutability type in Rust (`Cell<T>`, `RefCell<T>`, `OnceCell<T>`, `LazyCell<T, F>`, `Rc<T>`, `GhostCell<'brand, T>`, and `qcell::{LCell, TCell}`) lowers to `core::cell::UnsafeCell<T>`—the unique language primitive disabling Rust's `Freeze` marker and replacing Tree Borrows' `Frozen` shared-reference state with `PermissionPriv::Cell` (historically `SharedReadWrite`). Although RustBelt models these abstractions inside higher-order step-indexed Iris (`iProp Σ` with `▷`), **almost the entire single-threaded interior-mutability hierarchy admits sound, modular protocols in step-index-free first-order separation logic (`Type 0` Partial Commutative Monoids, `later P := P`)**:

- **`UnsafeCell<T>`**: Decouples pure pointer validity `IsUnsafeCellPtr(p, l, 'a)` from spatial points-to ownership `l ↦ v` via `PermissionPriv::Cell`, subject to the Tree Borrows rule that function-entry `StrongProtector`s (`RetagMode::FnEntry`) promote `&mut UnsafeCell<T>` to `ReservedFrz` rather than `ReservedIM`.
- **`Cell<T>` and `&[Cell<u8>]`**: Never yields interior references across user callbacks; verified either exactly via ghost tokens (`PCell`/`Perm`) or under unrestricted aliasing via a thread-local (`!Sync`) value-invariant PCM `CellInv(l, P)` with `P : Val -> Prop`, relying on `Cell::swap`'s byte-range non-overlap check (`abs_diff >= size_of::<T>()`) and `Cell::replace` ending its temporary `&mut T` before invoking `T::drop`.
- **`GhostCell<'brand, T>` and `qcell` (`LCell`, `TCell`)**: Separate duplicable cell handles from a linear finite-map token `Tok(γ, M : Loc ->_fin Val)` keyed by a rank-2 generative lifetime `'brand` (`GhostCell`, `LCell`) or singleton runtime `TypeId` (`TCellOwner<Q>`), giving exact zero-overhead `Type 0` reasoning over cyclic/intrusive graphs.
- **`RefCell<T>` and `Rc<RefCell<T>>`**: Governed by a signed `BorrowCounter` (`b == 0` idle, `b > 0` shared `Ref`, `b < 0` exclusive/split `RefMut` storing `NonNull<T>` rather than `&mut T` to avoid function-entry `noalias` UB) and `RcInner`'s collective weak-count protocol (`strong == 0` before `drop_in_place`, `_weak` held on stack to prevent `Weak::upgrade` resurrection and premature deallocation during reentrant `Drop`).
- **`OnceCell<T>` and `LazyCell<T, F>`**: Driven by monotonic write-once persistence (`None -> Some(v)` yielding guard-free `&'a T`), contrasting `OnceCell`'s two-state unpoisoned retry protocol against `LazyCell`'s three-state `Uninit(F) -> Poisoned -> Init(T)` latch.
- **Exact expressiveness boundary**: First-order `Type 0` PCMs suffice whenever stored invariants `P : Val -> Prop` quantify over `Type 0` data values (including cyclic `Rc<RefCell<Node>>` graphs). Impredicative step-indexed invariants (`▷`) or fuel-indexed stratification become mathematically mandatory—by Cantor diagonalization and **Landin's knot**—precisely when cells store **higher-order closures or trait objects** (`RefCell<Option<Box<dyn Fn()>>>`) whose specifications quantify over the heap invariants of their own containers.

## Applicability

This report specifies formal separation-logic protocols and operational invariants across the nine durable subjects in `REPORT.json`: Rust `core` and `alloc` (`rust-lang/rust` at `ec65cd52bba13d491ff65c9d218b39753755c84a`), Miri's Tree Borrows interpreter (`rust-lang/miri` at `5a2649e9c3bfbada72665448bddf8b54021bec2e`), The Rust Reference (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), `GhostCell` (`matthieu-m/ghost-cell` at `956df44625bda13793defc4a826431ad9ab7789c`), `qcell` (`uazu/qcell` at `a37533f68fda016ffb4078fd7523be3fe2873249`), Verus (`verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`), Creusot (`creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`), RustBelt (DOI `10.1145/3158154`), and `tiny-iris` (`JoJoDeveloping/tiny-iris` at `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`).

Scope qualifications:

- **Rust standard library (`ec65cd52bba13d491ff65c9d218b39753755c84a`)**: Covers `library/core/src/cell.rs`, `library/core/src/cell/{once,lazy}.rs`, `library/alloc/src/rcs/rc.rs`, and `compiler/rustc_middle/src/ty/util.rs`. Unstable nightly items (`CloneFromCell` issue `145329`, `once_cell_try` issue `109737`, `lazy_cell_into_inner` issue `125623`) are explicitly labeled.
- **Miri Tree Borrows (`5a2649e9c3bfbada72665448bddf8b54021bec2e`)**: Assumes default `precise_interior_mut = true` without `-Zmiri-tree-borrows-implicit-writes`. Miri names the shared interior-mutable permission `PermissionPriv::Cell` (corresponding to `SharedReadWrite` in Stacked Borrows) and the activated exclusive permission `PermissionPriv::Unique`.
- **First-order logic target**: Denotes upward-closed assertions `IProp := { holds : Fragment -> Prop, up_closed : ... }` over a `Type 0` `PartialCommMonoid` (`Fragment`) with trivial modality (`later P := P`, `tiny-iris` `theories/heapprop.v:117`) and zero COFEs or impredicative universe quantification.
- **Corpus cross-references**: Complements `ghostcell-branded-tokens-intrusive-containers-and-generational-arenas`, `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute`, `tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`, `iris-adequacy-transfinite-liveness-simuliris-and-lean-separation-logic`, and `hybrid-functional-lifting-and-separation-logic-for-unsafe-rust-and-interior-mutability`.

## Findings

### 1. `UnsafeCell<T>` and Tree Borrows `Cell` (`SharedReadWrite`) Exemption Rules

Basis: normative + source + derived

In `rust-lang/rust` `library/core/src/cell.rs:2311–2388`, `UnsafeCell<T>` is defined as:

```rust
#[repr(transparent)]
#[rustc_pub_transparent]
pub struct UnsafeCell<#[rustc_assert_variance(invariant)] T: ?Sized> { value: T }
impl<T: ?Sized> !Sync for UnsafeCell<T> {}
```

1. **Sole `Freeze` exemption and invariance**: `Ty::is_freeze` (`compiler/rustc_middle/src/ty/util.rs:1177–1208`) holds iff no `UnsafeCell` occurs inside `T` outside pointer/reference indirection (`&UnsafeCell<T>` and `*const UnsafeCell<T>` are themselves `Freeze`). Variance of `T` is `invariant` (line 2313), preventing `&UnsafeCell<&'long u8>` from coercing to `&UnsafeCell<&'short u8>`.
2. **Tree Borrows transitions on `UnsafeCell` bytes** (`rust-lang/miri` `src/borrow_tracker/tree_borrows/mod.rs:157–221, 342–363` and `perms.rs:10–233`):
   - **Shared retag (`&UnsafeCell<T>` or `&S` inside `UnsafeCell` byte ranges)**: Receives `Permission::new_cell()` (`PermissionPriv::Cell`). Under `perform_access` (`perms.rs:138–217`), `Cell` maps `child_read`, `foreign_read`, `child_write`, and `foreign_write` to `Some(Cell)` and has `IdempotentForeignAccess::Write`. Raw pointers `uc.get()` inherit the `Cell` tag, so writes through `*uc.get()` leave sibling `&UnsafeCell<T>` tags intact.
   - **Unprotected mutable retag (`let m = &mut uc;`)**: Receives `ReservedIM` (`mod.rs:190`). `foreign_write(ReservedIM) = Some(ReservedIM)` (`perms.rs:210–214`), tolerating foreign `&Cell<T>` writes until a child write activates `ReservedIM -> Unique` (`perms.rs:196`).
   - **Protected mutable retag (`fn f(m: &mut UnsafeCell<T>)` or `Box<UnsafeCell<T>>`, `RetagMode::FnEntry`)**: Receives `ReservedFrz { conflicted: false }` (`mod.rs:185–201`), **never** `ReservedIM`, to preserve LLVM `noalias`. Any foreign write while `f` executes disables protected `m` and triggers **immediate UB**.
3. **Separation-logic handle/payload split**: `&'a UnsafeCell<T>` denotes a pure persistent witness `IsUnsafeCellPtr(p, l, 'a)` carrying **zero** spatial ownership of `l ↦ v`. Dereferencing `*uc.get()` or calling `UnsafeCell::replace` (`cell.rs:2384–2387`) requires supplying `l ↦ v_old` from an external ghost token or shared invariant.

### 2. `Cell<T>` and `&[Cell<u8>]`: Protocols, Drop Order, Overlap, and `CloneFromCell`

Basis: source + derived

`Cell<T>` (`library/core/src/cell.rs:315–847`) wraps `UnsafeCell<T>` with `!Sync` (line 330) and zero borrow-counter overhead because shared `&Cell<T>` operations never expose interior `&T` or `&mut T` across user code.

- **Two `Type 0` separation-logic protocols**:
  1. *Exact Ghost-Permission Protocol* (`Creusot` `PCell<T>` + `Ghost<Perm<PCell<T>>>`, `Verus` `pcell::PCell<T>` + `Tracked<PointsTo<T>>`): `Cell::new(v)` yields `(c, Perm(id, v))`; `get` (`T: Copy`) reads `v` via `&Perm`; `replace(w)` updates `&mut Perm` to `Perm(id, w)`. Under potential aliasing `c1, c2 : &Cell<T>`, pointer comparison `ptr::eq(c1, c2)` decides whether one `Perm` governs both or whether two simultaneously held `&mut Perm` tokens imply `id1 != id2` (`Perm::disjoint_lemma`, `creusot-std/src/ghost/perm.rs:150–155`; `PointsTo::is_exclusive`, `vstd/cell/pcell.rs:118`).
  2. *Thread-Local Predicate-Invariant Protocol* (`Verus` `InvCell<T, Pred>`, `Creusot` `PredCell<T>`, RustBelt `NaInv`): Under unrestricted `&Cell<T>` aliasing, a thread-local (`!Sync`) token `NaTok` aggregates all closed cell invariants $\bigast_{(l, P) \in \mathcal{I}} \exists v : T.\; l \mapsto v \wedge \ulcorner P(v) \urcorner$ for `P : T -> Prop` (`Type 0`). Leaf operations `get`/`set`/`replace` open `NaTok`, update `l ↦ w` with `P(w)`, and close `NaTok` before returning, needing zero step-indexing.
- **Three subtle soundness requirements in `core::cell::Cell`**:
  1. *Destructor reentrancy in `Cell::set` / `Cell::replace`* (`cell.rs:438–443, 515–519`): `Cell::set` calls `self.replace(val)` (`mem::replace(unsafe { &mut *self.value.get() }, val)`), writing `val` and ending the temporary `&mut T` borrow **before** dropping `old_val`. Thus `NaTok` is already closed with `l ↦ val ∧ ⌜P(val)⌝` when `old_val`'s `Drop::drop` runs, making reentrant `cell.get()`/`cell.set(...)` inside `T::drop` completely UB-free!
  2. *Partial byte-range overlap in `as_slice_of_cells` and `Cell::swap`* (`cell.rs:470–495, 737–740`): `Cell::<[T]>::as_slice_of_cells` splits `CellInv(l, P_slice)` into `∗_{0 ≤ i < n} CellInv(l + i·sizeof(T), P_i)` (`creusot-std/src/cell/predcell.rs:103–114`). In `Cell::swap(&self, other: &Self)`, checking `ptr::eq` alone is unsound because unsafe code can form two partially overlapping `&Cell<[i32; 2]>` views (`rust-lang/rust#80778`). Lines 473–487 check `if ptr::eq(self, other) { return; }` **and** `if src.addr().abs_diff(dst.addr()) < size_of::<T>() { panic!(...); }` before calling `ptr::swap_nonoverlapping` (and under `PredCell::swap`, `predcell.rs:41`, require `∀ x, P_1(x) ↔ P_2(x)`).
  3. *Unsoundness of arbitrary `Clone` (`CloneFromCell`, `cell.rs:778–815`)*: Calling `T::clone(&*self.as_ptr())` holds an interior `&T` (`Frozen` on `Freeze` fields) across user code. As `cell.rs:784–800` demonstrates with `struct Bad<'a>(Option<&'a Cell<Bad<'a>>>, u8)`, `Bad::clone` holds `let a: &u8 = &self.1;` while calling `self.0.unwrap().set(Self(None, 1))`, mutating `self.1` under an active `Frozen` borrow! Hence `CloneFromCell` (line 804) is an `unsafe trait` restricted to non-reentrant types (`Option<T>`, `[T; N]`, `Rc<T>` at `rc.rs:361`).

### 3. `GhostCell<'brand, T>` and `qcell` (`LCell`, `TCell`): Branded Linear Map PCMs

Basis: source + documentation + derived

`GhostCell` (`matthieu-m/ghost-cell` at `956df44625bda13793defc4a826431ad9ab7789c`, `src/ghost_cell.rs:15–239`; Yanovski et al., ICFP 2021, DOI `10.1145/3473597`) and `qcell` (`uazu/qcell` at `a37533f68fda016ffb4078fd7523be3fe2873249`, `src/{lcell,tcell}.rs`) decouple shared container storage from a branded linear permission token:

```rust
pub fn new<R, F>(fun: F) -> R where for<'new_brand> F: FnOnce(GhostToken<'new_brand>) -> R
pub fn borrow<'a>(&'a self, _: &'a GhostToken<'brand>) -> &'a T
pub fn borrow_mut<'a>(&'a self, _: &'a mut GhostToken<'brand>) -> &'a mut T
```

- **First-order branded-map PCM (`GhostMapPCM`)**: For each fresh brand `γ` enforced by rank-2 universal quantification `for<'new_brand>` and invariant `PhantomData<fn(&'brand ()) -> &'brand ()>`, `Tok(γ, d, M)` tracks sharing depth `d : Nat` (`0` = exclusive, `d + 1` = shared) over a finite map `M : Loc ->_fin Val`, paired with persistent membership `CellHandle(γ, l, T)`:
  - `cell.borrow(&'a token)` shares `Tok` at depth `d + 1` and yields `&'a T` equal to `M[l]` simultaneously across **all** cells in `dom(M)`.
  - `cell.borrow_mut(&'a mut token)` locks `Tok` (`d = 0`), checking out a pure mutable loan `&'a mut T` initialized to `M[l]` whose backward writeback sets `M' := M[l := v_final]`.
  - Simultaneous multi-cell mutable checkout (`LCellOwner::rw2`, `uazu/qcell` `src/lcell.rs:106–116`) checks `!core::ptr::eq(lc1 as *const (), lc2 as *const ())` to split `M` across two non-overlapping keys `l_1 ≠ l_2`.
- **`LCell` vs. `TCell<Q, T>`**: To avoid threading `'brand` lifetimes through every struct definition, `qcell::TCell<Q, T>` (`src/tcell.rs:27–115`) brands cells by a `'static` marker type `Q` and enforces singleton uniqueness of `TCellOwner<Q>` once at construction via a global `TypeId` set (`SINGLETON_CHECK`), satisfying the exact same `Tok(Q, d, M)` first-order PCM.

### 4. `RefCell<T>` Runtime Borrow State Machine, `NonNull<T>` Guards, and `map_split`

Basis: source + normative + derived

`RefCell<T>` (`library/core/src/cell.rs:854–962, 1557–1637, 2050–2130`) pairs `borrow: Cell<BorrowCounter>` (`isize`, `UNUSED = 0`) with `value: UnsafeCell<T>`:

- **State-machine PCM (`RefCellPCM`)**:
  1. **Idle (`b == 0`)**: Invariant owns full exclusive `l.value ↦_0 v`.
  2. **Reading (`1 ≤ b ≤ isize::MAX`)**: `b` active `BorrowRef<'b>` guards share read permission `l.value ↦_b v`. `BorrowRef::new` (`cell.rs:1563–1583`) computes `let b = borrow.get().wrapping_add(1); if !is_reading(b) { None } else { ... }`. Testing `b > 0` after signed wrapping addition rejects **both** `b_old < 0` (active writer) **and** `b_old == isize::MAX` (`wrapping_add(1) == isize::MIN < 0`), preventing `mem::forget` leaks of `isize::MAX` `Ref` guards from overflowing into negative writer states! `BorrowRef::drop` (`lines 1589–1593`) decrements `b -> b - 1`, restoring exclusive ownership to the cell at `0`.
  3. **Writing (`isize::MIN ≤ b ≤ -1`)**: `|b|` active `BorrowRefMut<'b>` guards own pairwise-disjoint mutable sub-slices reconstructing `l.value`. `BorrowRefMut::new` (`lines 2066–2078`) **only** transitions `0 -> -1`; values `b ≤ -2` arise **exclusively** from `RefMut::map_split` calling `BorrowRefMut::clone` (`lines 2086–2093`, asserting `borrow != BorrowCounter::MIN`). Each `BorrowRefMut::drop` (`lines 2057–2061`) increments `b -> b + 1`, returning full `l.value ↦_0 v_final` only on `-1 -> 0`. Leaking a guard via `mem::forget` permanently pins `b ≠ 0`, safely causing conflicting future borrows to panic/return `Err`.
- **Why `Ref<'b, T>` and `RefMut<'b, T>` Store `NonNull<T>` Instead of `&'b T` / `&'b mut T`** (`cell.rs:1619–1625, 2102–2109`):
  ```rust
  pub struct RefMut<'b, T: ?Sized + 'b> {
      value: NonNull<T>,
      borrow: BorrowRefMut<'b>,
      marker: PhantomData<&'b mut T>,
  }
  ```
  In `fn f(c: &RefCell<i32>, g: RefMut<'_, i32>) { drop(g); *c.borrow_mut() = 42; }`, storing `&'b mut T` inside `RefMut` would attach a `RetagMode::FnEntry` `StrongProtector` lasting until `f` returns rather than until `drop(g)`, making `*c.borrow_mut() = 42` immediate Tree Borrows UB! Storing `NonNull<T>` restricts `&T`/`&mut T` retagging strictly to each `Deref::deref` / `DerefMut::deref_mut` invocation (`lines 1633, 2117, 2127`).

### 5. `OnceCell<T>` and `LazyCell<T, F>`: Monotonic Persistence and Poisoning

Basis: source + derived

`OnceCell<T>` (`library/core/src/cell/once.rs:35–378`) and `LazyCell<T, F>` (`library/core/src/cell/lazy.rs:6–260`) return guard-free `&'a T` references from `&'a Self` via monotonic state transitions:

- **`OnceCell<T>` (`UnsafeCell<Option<T>>`, `OptionAgree` PCM)**: Once transitioned from `None` to `Some(v)`, no `&OnceCell<T>` method can overwrite or drop `v` (`get_mut` and `take`, `once.rs:90, 375`, require exclusive `&mut OnceCell<T>`). Thus `Some(v)` yields a persistent shared points-to witness `□ (l ↦_shared Some(v))`, justifying `get(&self) -> Option<&T>` (`lines 80–83`). In `try_init` (`lines 316–326`), `let val = f()?;` executes while `inner` is still `None`: if `f()` panics or returns `Err`, `OnceCell` remains `None` (unpoisoned, retryable); if `f()` reentrantly initializes the cell to `v0` and returns `Ok(v1)`, `try_insert(v1)` sees `Some(v0)` (`lines 151–153`), preserves `v0` (keeping any already-issued `&T` valid!), and panics `"reentrant init"` (`line 325`).
- **`LazyCell<T, F>` (`UnsafeCell<State<T, F>>`, 3-state poisoning latch)**: To consume linear `F: FnOnce() -> T`, `really_init` (`lazy.rs:232–259`) executes `mem::replace(state, State::Poisoned)` (line 240) *before* calling `f()`. Panics inside `f()` leave `state` permanently `Poisoned` (panicking all subsequent `force` calls, `line 152`), and reentrant `force` calls during `f()` immediately panic on `State::Poisoned`. If `f()` catches that reentrant panic via `catch_unwind` and returns `data`, the reentrant `&*this.state.get()` read inside `force` invalidated the pre-call `state: &mut State<T, F>` borrow (`Unique -> Frozen`), which is why line 251 (`this.state.get().write(State::Init(data))`) must write through a freshly derived `UnsafeCell::get()` pointer (`Cell` permission).

### 6. `Rc<RefCell<T>>` Reference-Counting PCM and `Drop` Reentrancy

Basis: source + derived

`Rc<T>` (`library/alloc/src/rcs/rc.rs:285–444, 2654–2663`) combined with `RefCell<T>` exhibits two distinct `Drop` reentrancy regimes in `Type 0` separation logic:

1. **Live mutation `Drop` reentrancy (`strong ≥ 1`)**: Evaluating `*rc.borrow_mut() = new_t` keeps the temporary `RefMut` (`borrow == -1`) alive across `old_t`'s in-place `Drop::drop`. If `old_t::drop` holds a cloned `Rc<RefCell<T>>` and calls `rc.borrow()` or `rc.borrow_mut()`, `RefCell` sees `borrow == -1` and panics (`BorrowError`/`BorrowMutError`), preventing UB. By contrast, `let old = core::mem::replace(&mut *rc.borrow_mut(), new_t); drop(old);` releases `RefMut` (`-1 -> 0`) before `old::drop` runs.
2. **Terminal teardown `Drop` reentrancy (`Rc::drop` -> `drop_slow`, `rc.rs:405–417, 2654–2661`)**: `RcInner<T>` (`lines 286–290`) initializes `strong: Cell::new(1), weak: Cell::new(1)` (`lines 439–440`), representing one collective weak reference shared by all strong pointers (`weak == #Weak + [strong > 0]`). In `Rc::drop` (`lines 2657–2660`), `dec_strong()` sets `strong = 0` **before** calling `drop_slow()`, which binds `let _weak = Weak { ptr: self.ptr, alloc: &self.alloc };` on the stack before `ptr::drop_in_place(&mut (*self.ptr.as_ptr()).value)` (`lines 409–416`). Consequently, if `T` (`RefCell<Node>`) holds a self-`Weak<RefCell<Node>>` accessed in `Node::drop`: (a) `Weak::upgrade` observes `strong == 0` and returns `None`, preventing resurrection of `&RefCell<Node>` during `&mut value` destruction, and (b) dropping the embedded `Weak` decrements `weak` to `≥ 1` (held by `_weak`), preventing premature deallocation of `RcInner` during `drop_in_place` or unwind cleanup!

### 7. Expressiveness Boundary: Step-Index-Free `Type 0` PCMs vs. Step-Indexed Invariants (Landin's Knot)

Basis: source + documentation + derived

Comparing `tiny-iris` (`theories/heapprop.v:7–10, 117`, `heapProp_later P := P`), Verus (`PCell`, `InvCell`), Creusot (`PCell`, `PredCell`), and RustBelt (Jung et al., POPL 2018, DOI `10.1145/3158154`) establishes the exact expressiveness boundary of step-index-free `Type 0` separation logic:

| Abstraction / Idiom | Stored Payload `T` | Step-Index-Free `Type 0` SL? | Structural Reason |
| :--- | :--- | :--- | :--- |
| `UnsafeCell`, `GhostCell<'b, T>`, `LCell`, `TCell` | Any `T` (with stratified specs) | **Yes** | Ownership lives in external linear `Tok(γ, M)`; zero cyclic heap invariant |
| `Cell<T>`, `&[Cell<u8>]`, `OnceCell<T>` | Any `Type 0` data `T` (`u32`, structs, `Vec`, trees) | **Yes** | `CellInv(l, P)` / `OptionAgree(v)` quantifies over `Val : Type 0`, below `IProp` |
| `RefCell<T>`, `Rc<RefCell<Node>>` (cyclic graphs) | First-order `Node` (`Vec<Rc<RefCell<Node>>>`, `Weak`) | **Yes** | Finite graph PCM `∗_{(l, n) ∈ G} RcRefCell(l, n)` indexed by pure `Type 0` graph `G` |
| `LazyCell<T, F>` | First-order/non-self-aliasing closure `F` | **Yes** | Three-state `Uninit(F) -> Poisoned -> Init(T)` over `Type 0` values |
| **Landin's Knot**: `RefCell<Option<Box<dyn Fn()>>>` | Higher-order closure capturing `&RefCell` of **its own cell** | **No — Requires step-indexing (`▷`) or fuel stratification** | Semantic invariant $X \cong (X \to \mathsf{Prop})$ violates Cantor positivity and diverges without `loop` |

**Mathematical Proof of the Boundary (Landin's Knot)**:
In safe loop-free, recursion-free Rust:

```rust
fn landins_knot() {
    let node: Rc<RefCell<Option<Box<dyn Fn()>>>> = Rc::new(RefCell::new(None));
    let clone = Rc::clone(&node);
    *node.borrow_mut() = Some(Box::new(move || {
        if let Some(f) = clone.borrow().as_ref() { f(); }
    }));
    (node.borrow().as_ref().unwrap())(); // Diverges without `loop` or recursive `fn`!
}
```

To verify `(*node.borrow())()` modularly, the `RefCell` invariant at `l` must state that any stored `Box<dyn Fn()>` value `v` satisfies `⟦Fn()⟧(v)`. Because `v`'s environment captures `clone: Rc<RefCell<Option<Box<dyn Fn()>>>>`, `⟦Fn()⟧(v)` depends negatively on the `RefCell` invariant at `l` itself—requiring a fixed point $X \cong \mathcal{P}_{\uparrow}(\mathsf{Frag}) \text{ mentioning } (X \to \mathsf{Prop})$. By Cantor's theorem, no set-theoretic (`Type 0`) solution exists when `later P := P`, and any total-correctness logic admitting it would prove termination of `landins_knot()`!

Two mechanisms resolve this recursive domain equation:
1. **Impredicative step-indexing (Iris `iProp Σ`)**: Guards invariant opening behind `▷` (`inv N P` yields `▷P`), turning $X \cong \triangleright(X \to \mathsf{iProp}\;\Sigma)$ into a contractive COFE functor with a unique Banach fixed point matched to the operational call step.
2. **Fuel-indexed `Type 0` stratification (`@Nat.rec` on `fuel : Nat`)**: In fuel-bounded operational semantics (`wpOutcomeState p fuel`), defining `ValPred : Nat -> Val -> Prop` by structural recursion on `fuel` lets `RefCellInv (fuel + 1)` assert closure safety for `k ≤ fuel` steps—remaining inside `Init.*` `Type 0` without COFEs while leaving all first-order `Cell`/`RefCell`/`GhostCell`/`OnceCell`/`Rc` protocols completely fuel- and step-index-free.

## Boundaries

- **Unstratified step-index-free `Type 0` invariants over self-referential stored closures (`known not to apply`)**: Total-correctness `Type 0` invariants without step-indexing (`▷`) or `@Nat.rec` fuel stratification are **known not to apply** to higher-order stored closures capturing their own interior-mutable containers (`RefCell<Option<Box<dyn Fn()>>>`, Landin's knot).
- **Arbitrary `Clone` inside `Cell`, `ptr::eq`-only checks in `Cell::swap`, `&mut T` fields inside `RefMut`, and `OnceCell` panic poisoning (`known not to apply`)**: `Clone::clone` on interior `&T` of a `Cell` is **known not to apply** outside `CloneFromCell` (`cell.rs:784–805`); `ptr::eq` alone in `Cell::swap` is **known not to apply** on partially overlapping `&Cell<[T; N]>` slices (`cell.rs:473–487`); storing `&'b mut T` instead of `NonNull<T>` inside `RefMut<'b, T>` is **known not to apply** under Tree Borrows `FnEntry` protectors (`cell.rs:2102–2108`); and panic poisoning is **known not to apply** to `OnceCell::get_or_init` (`once.rs:168–169, 320`).
- **Cross-thread sharing (`Sync`) of `UnsafeCell`, `Cell`, `RefCell`, `OnceCell`, `LazyCell`, and `Rc` (`unsupported`)**: All six types implement `!Sync` (`cell.rs:318, 330`, `once.rs:435`, `rc.rs:338, 346`), so unsynchronized multi-threaded sharing without branded `Sync` tokens (`GhostCell`, `PCell`) is **unsupported**.
- **Final Tree Borrows protector rules on `PermissionPriv::Cell` arguments (`unknown`)**: As documented in `rust-lang/miri` `src/borrow_tracker/tree_borrows/perms.rs:100–103` (`TB-Cell` open design note in `compatible_with_protector`), whether Tree Borrows will refine function-entry protector semantics for `&Cell<T>` parameters remains **unknown**, though current Miri preserves full foreign-write immunity on `Cell`.
- **Concurrent `Sync` interior-mutability primitives (`not examined`)**: Weak-memory protocols for `Atomic*`, `Mutex`, `RwLock`, `OnceLock`, `LazyLock`, and `Arc` release-acquire drop fences were **not examined** in this report.

## Evidence

All findings were derived from pinned upstream sources and peer-reviewed publications inspected on `2026-11-20`:

1. **Rust `core` and `alloc` (`rust-lang/rust` at `ec65cd52bba13d491ff65c9d218b39753755c84a`)**:
   - `library/core/src/cell.rs:315–539, 721–741, 778–815`: `Cell<T>`, `set`, `swap` (`is_nonoverlapping`, issue `#80778`), `replace`, `as_slice_of_cells`, `CloneFromCell` (`Bad<'a>` counterexample).
   - `library/core/src/cell.rs:854–1032, 1557–1640, 2050–2130`: `RefCell<T>`, `BorrowCounter`, `BorrowRef` (`wrapping_add(1)` overflow guard), `Ref<'b, T>` (`NonNull<T>`), `BorrowRefMut` (`UNUSED -> UNUSED - 1`, `clone`), `RefMut<'b, T>` (`NonNull<T>`).
   - `library/core/src/cell.rs:2311–2395`: `UnsafeCell<T>` (`#[repr(transparent)]`, invariant `T`, `!Sync`, `replace`).
   - `library/core/src/cell/once.rs:35–161, 263–378, 435`: `OnceCell<T>`, `get`, `try_insert`, `try_init` (`panic!("reentrant init")`), `take`, `!Sync`.
   - `library/core/src/cell/lazy.rs:6–11, 54–154, 182–259`: `State<T, F>`, `LazyCell`, `force`, `force_mut`, `really_init` (`State::Poisoned` and raw `this.state.get().write`).
   - `library/alloc/src/rcs/rc.rs:285–444, 2654–2663`: `RcInner<T>`, `CloneFromCell for Rc<T>` (line 361), `drop_slow` (`_weak` guard before `ptr::drop_in_place`), `Rc::new`, `Rc::drop`.
   - `compiler/rustc_middle/src/ty/util.rs:1177–1215`: `Ty::is_freeze`.
2. **Miri Tree Borrows (`rust-lang/miri` at `5a2649e9c3bfbada72665448bddf8b54021bec2e`, Villani et al., PLDI 2025, DOI `10.1145/3735592`) and The Rust Reference (`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`)**: `src/borrow_tracker/tree_borrows/mod.rs:110–221, 329–364` and `perms.rs:10–233`.
3. **Branded and Ghost Permission Systems**: `GhostCell` (`matthieu-m/ghost-cell` at `956df44625bda13793defc4a826431ad9ab7789c`, `src/ghost_cell.rs:15–239`, Yanovski et al., ICFP 2021, DOI `10.1145/3473597`); `qcell` (`uazu/qcell` at `a37533f68fda016ffb4078fd7523be3fe2873249`, `src/tcell.rs:16–115`, `src/lcell.rs:45–120`); `Verus` (`verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`, `source/vstd/cell/{pcell,invcell}.rs`, Lattuada et al., OOPSLA 2023, DOI `10.1145/3586037`); `Creusot` (`creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`, `creusot-std/src/ghost/perm.rs`, `creusot-std/src/cell/{pcell,predcell}.rs`, Golfouse et al., CPP 2026, DOI `10.1145/3779031.3779086`).
4. **RustBelt and `tiny-iris`**: Jung et al., POPL 2018, DOI `10.1145/3158154`; `JoJoDeveloping/tiny-iris` at `5b18c311e746d2ae4170b0d253b5d7d36ee5d6d9`, `theories/{heapprop,adequacy}.v`.

## Revalidation

1. **`core::cell` and `alloc::rc` invariants (`rust-lang/rust`)**: Diff `library/core/src/cell.rs`, `library/core/src/cell/{once,lazy}.rs`, and `library/alloc/src/rcs/rc.rs` from `ec65cd52bba13d491ff65c9d218b39753755c84a` to verify `Cell::swap` (`ptr::eq` + `abs_diff >= size_of::<T>()`), `Cell::replace` (`mem::replace`), `Ref`/`RefMut` (`NonNull<T>` storage, `wrapping_add(1)` overflow check, `UNUSED -> UNUSED - 1`), `OnceCell::try_init` vs. `LazyCell::really_init` (`State::Poisoned`), and `Rc::drop` / `drop_slow` (`strong == 0` before `_weak` + `drop_in_place`).
2. **Tree Borrows `UnsafeCell` rules (`rust-lang/miri`)**: Check `src/borrow_tracker/tree_borrows/{mod,perms}.rs` against `5a2649e9c3bfbada72665448bddf8b54021bec2e` for `PermissionPriv::Cell`, `is_protected || frozen => ReservedFrz` on `&mut UnsafeCell<T>`, and `compatible_with_protector` (`perms.rs:99–104`).
3. **Branded/ghost token APIs**: Check `matthieu-m/ghost-cell` (`src/ghost_cell.rs`), `uazu/qcell` (`src/{lcell,tcell}.rs`), `verus-lang/verus` (`source/vstd/cell/{pcell,invcell}.rs`), and `creusot-rs/creusot` (`creusot-std/src/cell/{pcell,predcell}.rs`).
