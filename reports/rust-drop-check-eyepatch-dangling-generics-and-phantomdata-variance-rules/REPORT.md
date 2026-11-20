# Rust Drop Check (`dropck`), `#[may_dangle]` Eyepatch Soundness, `PhantomData` Variance Algebra, and Lifetime-Erased MIR Dangling Semantics

## Summary

Rust's ordinary outlives relation (`'a: 'b`) is reflexive: two values in the same lexical scope or aggregate can borrow each other (`'a == 'b`) safely when neither executes user-defined destruction code. Once a generic type implements `Drop` (or contains fields with drop glue), simultaneous scope exit ceases to exist operationally—one value is destroyed first while the other executes arbitrary `Drop::drop(&mut self)` code that could dereference freed borrows.

Primary-source analysis of `rust-lang/rust` (`c884ecfbabb0` and `14210df0e27c`), RFCs 0769, 1238, and 1327 (`f43d5789b838`), `SimonSapin/rust-typed-arena` (`f1f26c3994dc`), `proofs-rs/lean-miri` (`c92d1d9754c9`), and the RustBelt (`10.1145/3158154`) and Tree Borrows (`10.1145/3735592`) formalizations establishes five core invariants:

1. **Two-set `DropckOutlives` decomposition (`outlives` vs. `dtorck_types`):** `rustc` splits per-ADT drop-check obligations (`adt_dtorck_constraint` in `rustc_traits/src/dropck_outlives.rs:32–65`) into direct `outlives` (generic parameters of an `impl Drop` not marked `pure_wrt_drop` via `#[may_dangle]`, extracted by `destructor_constraints` in `ty/util.rs:466–532`) and transitive `dtorck_types` (field types expanded via cycle-breaking worklist `compute_dropck_outlives_with_errors` in `query/dropck_outlives.rs:108–253`).
2. **The `#[may_dangle]` $\times$ `PhantomData<T>` soundness coupling:** Since RFC 1238, a plain `impl<T> Drop for C<T>` places `T` directly into `outlives`, making `PhantomData<T>` redundant for `dropck` on stable Rust. Under `#![feature(dropck_eyepatch)]` (RFC 1327), `#[may_dangle] T` removes `T` from `outlives`. If `C<T>` stores elements behind raw pointers (`*const T`, `*mut T`, `NonNull<T>`, or `MaybeUninit<T>`)—all of which satisfy `trivial_dropck_outlives == true` (`query/dropck_outlives.rs:28–95`)—omitting `PhantomData<T>` drops `T` from `dtorck_types` as well, opening an immediate use-after-free (UAF) hole whenever `C<T>::drop` calls `ptr::drop_in_place` on an element `T` with a region-reading destructor.
3. **Orthogonality of variance (`Variance::xform`), auto-traits, and `dropck` ownership:** `PhantomData<T>`, `PhantomData<fn() -> T>`, and `PhantomData<*const T>` all induce **covariant** variance on `T`, yet diverge across `Send`/`Sync` and `dropck`: only `PhantomData<T>` pushes `T` into `dtorck_types` ("owns `T`"), whereas `fn() -> T` and `*const T` short-circuit at `trivial_dropck_outlives == true`. Meanwhile, `Unique<T>` (`14210df0e27c` `core/src/ptr/unique.rs:35–43`) has been removed on `rust-lang/rust` trunk (`c884ecfbabb0`), replaced by explicit `NonNull<T>` + `PhantomData<T>` (`BoxRaw<T>` in `boxed.rs:236–239`, `RawVec` in `raw_vec/mod.rs:67–81`).
4. **Container and arena drop-order discipline (`Vec`, `Box`, `BTreeMap`, `typed-arena`, `rustc_arena`):** `BTreeMap<K, V, A>` wraps `alloc: ManuallyDrop<A>` (`btree/map.rs:200–215`) so node deallocation precedes allocator destruction; because `ManuallyDrop<A>` satisfies `trivial_dropck_outlives == true`, `BTreeMap` keeps `A` un-eyepatched on `Drop` and carries `PhantomData<Box<(K, V), A>>` (`L202`, preserving unconditional `Unpin`). On stable Rust, `typed_arena::Arena<T>` (`src/lib.rs:103–110`) enables cyclic graphs (`Cell<Option<&'a Node<'a>>>`) without `#[may_dangle]` by omitting custom `Drop` and inheriting `Vec<T>`'s eyepatched drop glue, whereas `rustc_arena::TypedArena<T>` (`rustc_arena/src/lib.rs:104–118, 303–319`) defines custom `Drop` and therefore requires both `#[may_dangle] T` and `_own: PhantomData<T>`.
5. **Lifetime-erased MIR operational gap (`#[may_dangle]` vs. `MaybeDangling<P>`):** `#[may_dangle]` erases borrow-checker drop-liveness edges (`liveness/trace.rs:540–598`), allowing `StorageDead` of a borrowed local to precede `<G as Drop>::drop(&mut g)` in `Runtime(PostCleanup)` MIR without setting `is_like_maybe_dangling` on `G`. Operational models (`lean-miri` `Validity.lean:909–1121`, Tree Borrows `RetagPipeline.lean:291–361`) accept `Drop::drop(&mut self)` because tracked pointees *behind* `&mut self` are visited under `flags.mayDangle = true` (`Validity.lean:974–980`) and only outer `&mut self` receives a `StrongProtector`—whereas moving a dead `Box<T>` or `&'a T` *by value* (even into `mem::forget`, `maybe_dangling.rs:19–32`) faults under `mayDangle = false` unless wrapped in `MaybeDangling<P>` or `ManuallyDrop<P>`. In RustBelt (`10.1145/3158154`), this corresponds to separating active lifetime token $[\kappa]_q$ from raw memory ownership $\ell_{\text{self}} \mapsto \bar{v}$ once $\kappa$ expires.

## Applicability

This report characterizes static region/variance checking, stdlib container markers, and post-erasure MIR operational semantics across the fourteen subjects in `REPORT.json`:

- **Rust compiler and standard library (two revisions):**
  - `rust-lang/rust@c884ecfbabb04b04fa5054dafc67ec258ecde745`: `adt_dtorck_constraint`, `compute_dropck_outlives_with_errors`, `trivial_dropck_outlives`, `destructor_constraints`, MIR drop-liveness (`liveness/trace.rs`), variance (`variance/{terms,constraints,solve}.rs`), `rustc_arena::{TypedArena, DroplessArena, ArenaChunk}`, `MaybeDangling<P>`, `ManuallyDrop<T>`, `MaybeUninit<T>`, `NonNull<T>`, `Box<T, A>` (`BoxRaw<T>`), `RawVec<T, A>`, `Vec<T, A>`, and `BTreeMap<K, V, A>`.
  - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`): historical `core::ptr::Unique<T>` (`library/core/src/ptr/unique.rs`) compared against `BoxRaw<T>` and `RawVec` on `c884ecfbabb0`.
- **Specifications, RFCs, and Arena Crates:** `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFCs 0769, 1238, 1327), `rust-lang/nomicon@b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6`, `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `SimonSapin/rust-typed-arena@f1f26c3994dc881c35591cb629d8466df29e778a`, and `google/zerocopy@fd793268d403f83cd1fc9082b28097c5b0b92cbd`.
- **Operational Semantics and Verifiers:** `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `minirust/minirust@d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), RustBelt (`10.1145/3158154`), Stacked Borrows (`10.1145/3371109`), and Tree Borrows (`10.1145/3735592`).
- **Stability:** Variance inference, `PhantomData` patterns, `ManuallyDrop`, `MaybeUninit`, `NonNull`, and RFC 1238 parametric-drop defaults apply across all stable Rust editions (2015–2024). `#![feature(dropck_eyepatch)]` (`rust-lang/rust#34761`) and `#![feature(maybe_dangling)]` (`rust-lang/rust#118166`) remain unstable nightly features at `c884ecfbabb0`, though stable code relies on their stdlib instantiations in `Box`, `Vec`, `BTreeMap`, and `typed_arena::Arena`.
- **Adjacent corpus reports:** Complements [rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics](../rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics/REPORT.md) (`ElaborateDrops` ladders), [rust-allocation-box-storage-transfer-and-drop-elaboration](../rust-allocation-box-storage-transfer-and-drop-elaboration/REPORT.md) (`Box::into_raw`/`from_raw` and `Layout`), and [rust-drop-reentrancy-interior-mutability-and-arena-borrowing-invariants](../rust-drop-reentrancy-interior-mutability-and-arena-borrowing-invariants/REPORT.md) (synchronous `Drop` reentrancy).

## Findings

### 1. Evolution of Sound Generic Drop and the Exact `DropckOutlives` Algorithm

`Basis: normative + documentation + source + execution`

#### 1.1 Why Reflexive Outlives (`'a: 'a`) Fails Across Destructors (RFC 0769 $\to$ RFC 1238 $\to$ RFC 1327)

Without destructors, mutual borrows sharing region `'scope` (such as arena nodes mutating `Cell<Option<&'scope Node<'scope>>>`) are sound because neither value inspects the other during teardown (`nomicon` `src/dropck.md:49–71`). Adding `impl<'a> Drop for Inspector<'a>(&'a u8)` breaks symmetry: in `World<'a> { inspector: Option<Inspector<'a>>, days: Box<u8> }`, dropping `days` before `inspector`—or reallocating/dropping elements inside an opaque container—exposes freed memory to `Inspector::drop` (`dropck.md:74–118`).

Three RFCs (`rust-lang/rfcs@f43d5789b838`) established Rust's current rule:
1. **RFC 0769 (`text/0769-sound-generic-drop.md`):** Required regions reachable from a dropped value `v` with parametric destructors to strictly outlive `v`.
2. **RFC 1238 (`text/1238-nonparametric-dropck.md`):** Replaced parametricity inference with **nonparametric dropck**: *every* generic parameter of `impl<...> Drop for D<...>` must strictly outlive `v`, initially offering only the all-or-nothing escape hatch `#[unsafe_destructor_blind_to_params]`.
3. **RFC 1327 (`text/1327-dropck-param-eyepatch.md:88–176, 394–432`):** Showed that `#[unsafe_destructor_blind_to_params]` cannot soundly express `RawVec<T, A: Allocator>` (`L120–135`): `T` may dangle if trivial, **yet `A` (e.g., `&'a ArenaAllocator`) is called during `RawVec::drop` to free the buffer and must strictly outlive the `RawVec`**. RFC 1327 introduced per-parameter `#[may_dangle]` ("the eyepatch") requiring `unsafe impl<...> Drop`.

#### 1.2 Mechanized `adt_dtorck_constraint` and `DropckOutlives` Pipeline in `rustc`

In `rust-lang/rust@c884ecfbabb0`, `dropck` executes in three stages:

1. **Direct Destructor Constraints (`compiler/rustc_middle/src/ty/util.rs:466–532`):**
   `TyCtxt::destructor_constraints(def)` returns `vec![]` if `def.destructor(self)` is `None`. Otherwise, it inspects `impl_generics` on the `Drop` `impl` and collects every ADT generic parameter whose corresponding `impl` parameter lacks `pure_wrt_drop == true` (`#[may_dangle]`):
   ```rust
   // compiler/rustc_middle/src/ty/util.rs:508-526 (abridged)
   GenericArgKind::Lifetime(region) => match region.kind() {
       ty::ReEarlyParam(ebr) => !impl_generics.region_param(ebr, self).pure_wrt_drop,
       _ => false,
   },
   GenericArgKind::Type(ty) => match *ty.kind() {
       ty::Param(pt) => !impl_generics.type_param(pt, self).pure_wrt_drop,
       _ => false,
   },
   GenericArgKind::Const(ct) => match ct.kind() {
       ty::ConstKind::Param(pc) => !impl_generics.const_param(pc, self).pure_wrt_drop,
       _ => false,
   },
   ```
   Notably, `pure_wrt_drop` applies to lifetime, type, and `const` generic parameters (`L519–525`), mapping cleanly across arbitrary `impl` parameter permutations (`impl<#[may_dangle] P0, P1, P2> Drop for S<P1, P2, P0>`, `L483–505`).

2. **Triviality Short-Circuit (`compiler/rustc_trait_selection/src/traits/query/dropck_outlives.rs:28–95`):**
   `trivial_dropck_outlives(tcx, ty)` returns `true` when dropping `ty` imposes zero region obligations:
   - Primitives (`Bool`, `Int`, `Uint`, `Float`, `Char`, `Never`, `Str`), `FnDef`, `FnPtr`, **`RawPtr(_, _)`**, **`Ref(..)`**, and `Foreign(..)` return **`true`** (`L33–48`). Because `&'a T` and `&'a mut T` have no destructor, `trivial_dropck_outlives(&'a T) == true`.
   - `[T; 0]` returns **`true`** (`L52–55`, `rust-lang/rust#110288`), whereas `[T; N]` ($N > 0$) and `[T]` delegate to `T` (`L51, 56`).
   - `Adt(def, _)` returns **`true` iff `def.is_manually_drop()`** (`L69–79`). Although `mem::needs_drop::<PhantomData<T>>()` is `false`, `trivial_dropck_outlives` returns **`false`** for `PhantomData<T>` (`L74–78`) and for `union`s.

3. **Per-ADT Summary & Worklist Fixed Point (`rustc_traits/src/dropck_outlives.rs:32–65` & `query/dropck_outlives.rs:108–253`):**
   - For `PhantomData<T>`, `adt_dtorck_constraint` returns `DropckConstraint { outlives: vec![], dtorck_types: vec![T], overflows: vec![] }` (`L40–52`).
   - For any other non-`ManuallyDrop` ADT `D`, `adt_dtorck_constraint` walks `def.all_fields()` via `dtorck_constraint_for_ty_inner` and appends `tcx.destructor_constraints(def)` into `result.outlives` (`L54–60`).
   - At each initialized MIR `Drop` terminator (`rustc_borrowck/src/type_check/liveness/trace.rs:540–559`), `compute_dropck_outlives_with_errors` runs a `FxHashSet`-guarded DFS worklist (`ty_stack`, `ty_set` at `L155–249`) over `dtorck_types`. Unresolved `ty::Alias` projections (`L238–240`) and `ty::Dynamic` trait objects (`L402–406`) push directly to `outlives`. For coroutines (`L315–378`), if *any* region-erased witness field satisfies `needs_drop`, `rustc` conservatively pushes all upvars and `resume_ty` into `outlives` (requiring *use-liveness* rather than *drop-liveness*, `L353–360`).

---

### 2. `PhantomData` Variance Algebra (`Variance::xform`), Auto-Traits, and the Missing-`PhantomData` UAF Hole

`Basis: normative + source + execution + derived`

#### 2.1 Four-Point Variance Semiring (`compiler/rustc_hir_analysis/src/variance/`)

`variance/terms.rs:109–123` hardcodes variance for three lang items: `PhantomData<T>` $\mapsto$ `[Covariant]`, `UnsafeCell<T>` $\mapsto$ `[Invariant]`, and `CovariantUnsafeCell<T>` $\mapsto$ `[Covariant]`. All other ADTs start parameters at `Bivariant` (unused parameters trigger `E0392`) and accumulate constraints across fields (`constraints.rs:107–122`; struct/enum `where` bounds do **not** affect variance, `L109–113`). Nested positions compose via associative monoid `Variance::xform(v_outer, v_inner)` (`constraints.rs:168–179`) with identity `Covariant` ($+$):

- $+\times v = v$, $-\times + = -$, $-\times - = +$, $0 \times v = 0$ (for $v \neq \top$), and $\top \times v = v \times \top = \top$.
- `&'a T` and `*const T` are covariant (`L230–233, 249–251`); `&'a mut T` is covariant in `'a` and invariant in `T` (`L481–484`); `*mut T` is invariant in `T`.
- `fn(A) -> R` transforms `A` by `Contravariant` (`L429–432`) and `R` by `Covariant` (`L433`), making `fn(fn(T))` covariant and `fn(T) -> T` invariant.
- Unexpanded `Projection`/`Inherent`/`Opaque` aliases (`L263–272`) and trait arguments inside `dyn Trait<T> + 'a` (`L279–301`) force `Invariant` on `T` while keeping `'a` covariant.

#### 2.2 Complete 9-Pattern `PhantomData` Matrix

Wrapping `T` inside `PhantomData<P>` (`nomicon` `src/phantom-data.md:242–259`, `dropck_outlives.rs:28–95`) yields:

| Marker Type | `'a` Var | `T` Var | `Send` / `Sync` | `Unpin` | `DropckOutlives` (`#[may_dangle]`) |
| :--- | :---: | :---: | :--- | :---: | :--- |
| `PhantomData<T>` | — | Cov | Inherited (`T`) | `T: Unpin` | `dtorck_types: [T]` (**owns `T`**; blocks dangling if `T` has dtor) |
| `PhantomData<&'a T>` | Cov | Cov | `T: Sync` | `Unpin` | `trivial(&'a T) == true` (dangling allowed) |
| `PhantomData<&'a mut T>` | Cov | Inv | Inherited (`T`) | `Unpin` | `trivial(&'a mut T) == true` (dangling allowed) |
| `PhantomData<*const T>` | — | Cov | `!Send + !Sync` | `Unpin` | `trivial(*const T) == true` (dangling allowed) |
| `PhantomData<*mut T>` | — | Inv | `!Send + !Sync` | `Unpin` | `trivial(*mut T) == true` (dangling allowed) |
| `PhantomData<fn(T)>` | — | Contra | `Send + Sync` | `Unpin` | `trivial(fn(T)) == true` (dangling allowed) |
| `PhantomData<fn() -> T>` | — | Cov | `Send + Sync` | `Unpin` | `trivial(fn() -> T) == true` (dangling allowed) |
| `PhantomData<fn(T) -> T>` | — | Inv | `Send + Sync` | `Unpin` | `trivial(fn(T)->T) == true` (dangling allowed) |
| `PhantomData<Cell<&'a ()>>` | Inv | — | `Send + !Sync` | `Unpin` | `Cell -> UnsafeCell -> &'a ()` $\to$ `[]` (dangling allowed) |

#### 2.3 Exact Mechanism of the `#[may_dangle]`-Without-`PhantomData<T>` UAF Bug

Consider a custom vector storing `NonNull<T>` (whose sole field is `*const T`, `core/src/ptr/non_null.rs:73–78`) with `#[may_dangle] T` but **no** `PhantomData<T>`:

```rust
#![feature(dropck_eyepatch)]
use core::ptr::{self, NonNull};

pub struct VecNoPhantom<T> { ptr: NonNull<T>, len: usize }

unsafe impl<#[may_dangle] T> Drop for VecNoPhantom<T> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.ptr.as_ptr(), self.len)) };
    }
}
```

In `adt_dtorck_constraint(VecNoPhantom)`: (1) `destructor_constraints` yields `outlives = []` because `T` is `pure_wrt_drop`; (2) `NonNull<T>` $\to$ `*const T` satisfies `trivial_dropck_outlives == true`, yielding `dtorck_types = []`. When instantiated as `VecNoPhantom<Inspector<'s>>`, `DropckOutlives` terminates immediately without inspecting `Inspector<'s>`! Safe callers can drop `'s`'s referent before `VecNoPhantom` drops, causing `Inspector::drop` to dereference freed memory (`probe_dropck_and_operational_dangle.py`). Using `PhantomData<fn() -> T>` or `PhantomData<*const T>` causes the **identical UAF** because both inner types satisfy `trivial_dropck_outlives == true`. Conversely, on stable Rust (no `#[may_dangle]`), `destructor_constraints` puts `T` directly in `outlives`, so `PhantomData<T>` is dropck-redundant unless the struct has *no* custom `Drop` impl yet drops `T` via sibling drop glue (`nomicon` `src/phantom-data.md:88–117`).

---

### 3. Ownership, Drop Order, and `Unique<T>` Removal Across `Box`, `Vec`, `BTreeMap`, and Arenas

`Basis: source + documentation + execution + derived`

#### 3.1 From `Unique<T>` (`14210df0e27c`) to Unbundled `NonNull<T>` + `PhantomData<T>` (`c884ecfbabb0`)

At `14210df0e27c` (`core/src/ptr/unique.rs:34–58`), stdlib containers used `Unique<T> { pointer: NonNull<T>, _marker: PhantomData<T> }` with `Send`/`Sync` bounds. On `c884ecfbabb0`, `Unique<T>` is deleted and unbundled across containers:

| Container | Representation & Marker | `Drop` & `#[may_dangle]` Signature | Key Drop-Order / Trait Invariant |
| :--- | :--- | :--- | :--- |
| **`Box<T, A>`** (`boxed.rs:235–244, 2125–2143`) | `BoxRaw<T> { NonNull<T>, PhantomData<T> }`, `A` | `unsafe impl<#[may_dangle] T: ?Sized, A: Allocator> Drop` | Compiler ElaborateDrops drops `*self` *before* `Box::drop` calls `self.1.deallocate`; `A` is un-eyepatched so `A` outlives `Box`! |
| **`RawVec<T, A>`** (`raw_vec/mod.rs:67–82, 439`) | `RawVecInner<A>`, `_marker: PhantomData<T>` | `const unsafe impl<#[may_dangle] T, A: ...> Drop` | Frees buffer without dropping `T`; keeps `PhantomData<T>` for auto-traits & `may_dangle` (`L67`). |
| **`Vec<T, A>`** (`vec/mod.rs:448–451, 4594–4607`) | `buf: RawVec<T, A>`, `len: usize` | `const unsafe impl<#[may_dangle] T: ..., A: ...> Drop` | `Vec::drop` runs `cast_slice(self.len).drop_in_place()`; field drop glue then runs `RawVec::drop`. |
| **`BTreeMap<K, V, A>`** (`btree/map.rs:194–216`) | `Option<Root<K,V>>`, `ManuallyDrop<A>`, `PhantomData<Box<(K,V), A>>` | `unsafe impl<#[may_dangle] K, #[may_dangle] V, A: AllocatorClone> Drop` | `ManuallyDrop<A>` delays `A`'s drop past node frees; `Box` marker preserves unconditional `Unpin`! |
| **`rustc_arena::TypedArena<T>`** (`rustc_arena/src/lib.rs:104–118, 303–319`) | `Cell<*mut T>` $\times 2$, `RefCell<Vec<ArenaChunk<T>>>`, `_own: PhantomData<T>` | `unsafe impl<#[may_dangle] T> Drop` | `Cell<*mut T>` enforces invariance on `T`; `_own: PhantomData<T>` enforces `dropck`. |
| **`typed_arena::Arena<T>`** (`typed-arena` `src/lib.rs:103–110`) | `RefCell<ChunkList<T>>` (`Vec<T>`, `Vec<Vec<T>>`) | **No custom `Drop` impl** | Inherits invariance from `RefCell` and `#[may_dangle]` from `Vec<T>` on **stable Rust**! |

#### 3.2 `BTreeMap`'s `ManuallyDrop<A>` + `PhantomData<Box<(K, V), A>>` Coupling (`btree/map.rs:196–216`)

Struct fields drop in forward declaration order *after* `<BTreeMap as Drop>::drop(&mut self)` completes (`reference` `src/destructors.md`). Because `BTreeMap` nodes omit per-node allocator copies, `BTreeMap::drop` moves `alloc` by value into `root.into_dying().drop_tree(ManuallyDrop::take(&mut self.alloc))` (`L210`, or `ManuallyDrop::drop(&mut self.alloc)` when empty at `L213`). However, `trivial_dropck_outlives(ManuallyDrop<A>) == true` (`query/dropck_outlives.rs:70–72`), erasing `alloc` from field `dtorck_types`! `BTreeMap` preserves allocator liveness by keeping `A` **un-eyepatched** on `Drop` *and* embedding `A` inside `_marker: PhantomData<Box<(K, V), A>>` (`L202`). Wrapping `(K, V)` and `A` inside `Box<..., A>` inside `PhantomData` avoids tightening `BTreeMap`'s `Unpin` impl (since `Box<T, A>: Unpin` unconditionally, whereas `PhantomData<((K, V), A)>` would require `K: Unpin, V: Unpin, A: Unpin`).

#### 3.3 Arena Cycles on Stable vs. Nightly Rust (`typed_arena` vs. `rustc_arena`)

`typed_arena::Arena<T>` (`src/lib.rs:35–50, 187–205`) supports cyclic graphs (`CycleParticipant<'a> { other: Cell<Option<&'a CycleParticipant<'a>>> }`) on stable Rust through three interacting invariants:
1. **Invariance via `RefCell`:** `alloc(&'a self, value: T) -> &'a mut T` requires `T` to be invariant (`variance/terms.rs:113`); covariance would let `&Arena<&'static str>` coerce to `&Arena<&'short str>` and store dangling references.
2. **Delegating `#[may_dangle]` to `Vec<T>`:** Because `Arena<T>` and `ChunkList<T>` omit `impl Drop`, `adt_dtorck_constraint` expands `RefCell -> UnsafeCell -> ChunkList -> Vec<T>`. For `Drop`-free `CycleParticipant<'a>`, `ty_set` breaks the cycle (`query/dropck_outlives.rs:243`) with `outlives = []`; adding `impl<'a> Drop for CycleParticipant<'a>` injects `'a` into `outlives` and rejects the cycle with `E0597`.
3. **Stacked/Tree Borrows & panic-safety traps:** `typed_arena::alloc_fast_path` (`L198–201`) writes `&mut *chunks.current.as_mut_ptr().add(len)` rather than `&mut chunks.current[len]`, because `Vec::deref_mut` creates `&mut [T]` over `[0..len+1]`, invalidating prior `&'a mut T` arena allocations! Meanwhile, `rustc_arena::TypedArena::try_alloc_from_iter` (`rustc_arena/src/lib.rs:209–245`) collects into a stack `SmallVec<[T; 8]>` before `copy_to_nonoverlapping` + `vec.set_len(0)` so iterator panics or reentrant `alloc` calls never leave uninitialized slots inside `[start..ptr)` for `ArenaChunk::destroy` (`slice[..len].assume_init_drop()`, `L70`) to drop.

---

### 4. Lifetime-Erased MIR Operational Semantics: `#[may_dangle]` vs. `MaybeDangling<P>`, Tree Borrows, and RustBelt

`Basis: source + execution + derived`

#### 4.1 Why `Drop::drop(&mut self)` Entry Accepts Dangling Inner Refs Yet `mem::forget(dead_box)` Is UB

In `Runtime(PostCleanup)` MIR, lifetimes are erased, and `#[may_dangle]` does **not** set `AdtFlags::IS_MAYBE_DANGLING` (`ty/sty.rs:2184–2195`). Comparing two post-deallocation cases in `lean-miri` (`Miri/Memory/Validity.lean:909–1121`, `RetagPipeline.lean:31–48, 291–361`) and `core/src/mem/maybe_dangling.rs:19–74` explains the exact boundary:

1. **Entering `<EyepatchGuard<'a> as Drop>::drop(&mut _guard)` after `StorageDead(_pointee)`:**
   - Root argument `_1: &mut EyepatchGuard<'_>` is validated with `flags.mayDangle = false` (`Validity.lean:926`). Because `_guard`'s own stack slot is still **live**, `checkSafePointer` (`L1060`: `if !mayDangle`) succeeds, registers a Tree Borrows `StrongProtector` on `_1` (`RetagPipeline.lean:291`), and enqueues `*_1` in `RefTracking` (`L1120`).
   - When `validatePlace` drains `RefTracking` to inspect fields *behind* `_1` (including the dead inner `&'a u8`), line `976` sets **`trackedSession.flags := ⟨false, true⟩` (`mayDangle = true`)**!
   - Under `mayDangle = true` (`L1080–1110`), `checkSafePointer` **skips `checkAccess` and `retagPointer`**, verifying only address-space non-overflow (`endNat < targetUsizeMax`), non-nullness (`L1092–1098`), inhabitedness (`L1099–1103`), and alignment (`L1104–1106`), and halts deeper tracking (`L1110`).
   - However, executing even `let _copy = self.0;` inside `Drop::drop` loads `&'a u8` at root (`mayDangle = false`), faulting immediately in `checkAccess`!
2. **Moving a manually deallocated `Box<u32>` into `mem::forget(boxed)` (`maybe_dangling.rs:19–48`):**
   - `mem::forget(boxed)` moves `boxed` **by value** at root (`mayDangle = false`), running `checkSafePointer` + `tb_retag_ptr_value` on freed heap memory—**immediate UB** even though `Box::drop` never runs! Wrapping in `MaybeDangling<Box<u32>>` (`#[lang = "maybe_dangling"]`) or `ManuallyDrop<Box<u32>>` sets `isLikeMaybeDangling = true` (`Validity.lean:639, 839`), enabling `mayDangle = true` across by-value moves while keeping non-null and alignment checks active.

#### 4.2 RustBelt Semantic Interpretation & MIR Verifier Rule

In RustBelt (`10.1145/3158154`), shared reference ownership $\llbracket \&^\kappa\,\tau \rrbracket_{\text{own}}(t, [v])$ pairs non-null/aligned pointer bit-validity with persistent borrow $\llbracket \tau \rrbracket_{\text{shr}}(\kappa, t, \ell)$, readable **only** when combined with active fractional lifetime token $[\kappa]_q$. Normal `impl<'a> Drop for T<'a>` receives $[\kappa]_q * \ell_{\text{self}} \mapsto \bar{v} * \llbracket T(\kappa) \rrbracket_{\text{own}}(t, \bar{v})$; `unsafe impl<#[may_dangle] 'a> Drop` omits $[\kappa]_q$, leaving raw field layout bytes whose borrows cannot be opened—unless an owned `PhantomData<U>` element `U` requires $[\kappa]_q$ for `U::drop`, which `dropck` preserves via `dtorck_types: [U]`. Accordingly, `Runtime(PostCleanup)` MIR verifiers (`joshlf/anneal@20aa204315cd`) must validate dereferenceability at root retags/loads rather than recursively chasing references behind `&mut Self` at `Drop::drop` entry, while requiring `MaybeDangling`/`ManuallyDrop` on by-value moves of dead safe pointers.

## Boundaries

- **Known not to apply:**
  1. Adding `PhantomData<T>` to a type with a non-eyepatched `impl<T> Drop` is **known not to apply** any extra `dropck` constraint (`nomicon` `src/phantom-data.md:88–112`, `ty/util.rs:476–529`), affecting only variance and auto-traits.
  2. `MaybeDangling<P>` and `ManuallyDrop<P>` are **known not to apply** to null, misaligned, or uninhabited (`&!`) safe pointers (`Validity.lean:1092–1106`, `maybe_dangling.rs:50–51`; use `MaybeUninit` or raw pointers instead).
- **Unsupported:**
  1. `#![feature(dropck_eyepatch)]` and `#![feature(maybe_dangling)]` are **unsupported** on stable Rust; RFC 1327 (`L25–28`) explicitly marks `#[may_dangle]` as an interim unstable design, and usage-site or projection attributes (`T::Assoc`) are **unsupported** (`L219–225, 522–525`).
  2. In `joshlf/anneal@20aa204315cd` (`main`), heap allocations (`Box`, `Vec`), raw pointers, and dynamic `Drop` calls in `Trusted.MirSemantics` step to `FaultKind.unsupported`.
- **Unknown:**
  1. Whether Rust will stabilize a checked parametricity syntax (`T: ?Special` or `fn drop<'s>(&'s mut self) where A: 's`) to replace `#[may_dangle]` remains **unknown** (`rust-lang/rust#34761`).
  2. Exact LLVM `dereferenceable`/`noalias` lowering across all ABI modes once `BTreeMap` migrates to `MaybeDangling` (`btree/map.rs:1333, 1369`, `maybe_dangling.rs:35`) remains **unknown** beyond Miri's `ValidityVisitor`.
- **Not examined:**
  1. `Pin` + experimental `AsyncDrop` interactions with `DropckOutlives`, `-Zpolonius` loan-graph drop-liveness encodings, and `fitzgen/bumpalo` source internals were **not examined**.

## Evidence

### 1. Primary Source and Specification Matrix

| Subject & Revision | Path & Lines | Fact Established (`Basis`) |
| :--- | :--- | :--- |
| `rust-lang/rfcs` @ `f43d5789b838` | `text/{0769-sound-generic-drop,1238-nonparametric-dropck,1327-dropck-param-eyepatch}.md` | `normative`: Sound generic drop, nonparametric default, `RawVec<T, &ArenaAlloc>` counterexample, `patched(D)` rule. |
| `rust-lang/rust` @ `c884ecfbabb0` | `rustc_traits/src/dropck_outlives.rs:31–65`; `query/dropck_outlives.rs:28–253, 315–416`; `ty/util.rs:466–532`; `liveness/trace.rs:540–598` | `source`: `PhantomData` `dtorck_types: [T]`, `trivial_dropck_outlives`, `!pure_wrt_drop` extraction, and reverse-DFS `drop_live_at`. |
| `rust-lang/rust` @ `c884ecfbabb0` | `rustc_hir_analysis/src/variance/{terms.rs:109–123, constraints.rs:107–306, 422–490}` | `source`: Lang-item variances, `Variance::xform` monoid, ignored ADT `where` bounds, invariant aliases/`dyn Trait<T>`. |
| `rust-lang/rust` @ `14210df0e27c` & `c884ecfbabb0` | `core/src/ptr/unique.rs:34–58` (`14210df0`); `boxed.rs:235–244, 2125–2143`, `raw_vec/mod.rs:67–82, 439`, `vec/mod.rs:448–451, 4594–4607`, `btree/map.rs:194–216`, `maybe_dangling.rs:19–112` (`c884ecfb`) | `source`: `Unique<T>` removal in favor of `BoxRaw`/`RawVec` `NonNull<T>` + `PhantomData<T>`; `BTreeMap` `ManuallyDrop<A>` + `Box` marker; `MaybeDangling` `mem::forget` UB. |
| `SimonSapin/rust-typed-arena` @ `f1f26c3994dc` & `rustc_arena` (`c884ecfbabb0`) | `typed-arena` `src/lib.rs:35–50, 103–110, 193–205`; `rustc_arena/src/lib.rs:37–73, 104–118, 209–245, 303–319` | `source`: Stable `Vec<T>` dropck delegation vs. custom `#[may_dangle]` + `_own: PhantomData<T>` + `SmallVec` panic-safe copy. |
| `proofs-rs/lean-miri` @ `c92d1d9754c9` & literature | `Miri/Memory/Validity.lean:627–642, 838–840, 909–1121`; `RetagPipeline.lean:31–92, 291–361`; DOIs `10.1145/3158154`, `10.1145/3371109`, `10.1145/3735592` | `source` + `documentation`: `RefTracking` `mayDangle = true` behind `&mut self`, Tree Borrows protectors, and RustBelt $[\kappa]_q$ lifetime tokens. |

### 2. Executed Finite-State Verification Probe (`2026-11-20`)

`Basis: execution`

*(Under lightweight capsule mode, `rustc`/`lean` builds were not run; the self-contained Python 3.11 model checker below ran on `x86_64-unknown-linux-gnu` on `2026-11-20`, exit code `0`.)*

```python
#!/usr/bin/env python3
"""Self-contained checker for Variance::xform, DropckOutlives, and Miri mayDangle."""
from dataclasses import dataclass

COV, INV, CONTRA, BIV = "Covariant", "Invariant", "Contravariant", "Bivariant"

def xform(v1: str, v2: str) -> str:
    if v1 == BIV or v2 == BIV: return BIV
    if v1 == INV or v2 == INV: return INV
    if v2 == COV: return v1
    if v2 == CONTRA: return CONTRA if v1 == COV else COV
    raise ValueError((v1, v2))

for a in (COV, INV, CONTRA, BIV):
    assert xform(a, COV) == a and xform(COV, a) == a
    for b in (COV, INV, CONTRA, BIV):
        for c in (COV, INV, CONTRA, BIV):
            assert xform(xform(a, b), c) == xform(a, xform(b, c))

@dataclass(frozen=True)
class Ty:
    kind: str
    lt: str = "static"
    elem: "Ty | None" = None
    alloc: "Ty | None" = None

def collect_regions(ty: Ty | None) -> set[str]:
    if ty is None: return set()
    return ({ty.lt} if ty.lt != "static" else set()) | collect_regions(ty.elem) | collect_regions(ty.alloc)

def adt_dropck(ty: Ty) -> tuple[set[str], list[Ty]]:
    k = ty.kind
    if k in ("unit", "ref", "raw_const", "fn_ret", "manually_drop"): return set(), []
    if k == "phantom": return set(), [ty.elem]
    if k == "inspector": return ({ty.lt} if ty.lt != "static" else set()), [Ty("ref", lt=ty.lt)]
    if k == "vec_no_eyepatch":
        return collect_regions(ty.elem) | collect_regions(ty.alloc), [ty.elem] + ([ty.alloc] if ty.alloc else [])
    if k == "vec_no_phantom":
        return collect_regions(ty.alloc), ([ty.alloc] if ty.alloc else [])
    if k in ("vec_good", "box"):
        return collect_regions(ty.alloc), [ty.elem] + ([ty.alloc] if ty.alloc else [])
    if k == "btree_good":
        return collect_regions(ty.alloc), [Ty("box", elem=ty.elem, alloc=ty.alloc)]
    if k == "btree_bad_alloc": return set(), [ty.elem]
    if k == "typed_arena_std": return set(), [Ty("vec_good", elem=ty.elem, alloc=Ty("unit"))]
    raise ValueError(k)

def dropck_outlives(root: Ty) -> list[str]:
    stack, seen, live = [root], {root}, set()
    while stack:
        out, dtors = adt_dropck(stack.pop())
        live |= out
        for nxt in dtors:
            if nxt is not None and nxt not in seen:
                seen.add(nxt); stack.append(nxt)
    return sorted(live)

t_ref, t_insp, a_ref, a_glob = Ty("ref", lt="'s"), Ty("inspector", lt="'s"), Ty("ref", lt="'a"), Ty("unit")
assert dropck_outlives(Ty("vec_no_eyepatch", elem=t_ref, alloc=a_glob)) == ["'s"]
assert dropck_outlives(Ty("vec_good", elem=t_ref, alloc=a_glob)) == []
assert dropck_outlives(Ty("vec_good", elem=t_insp, alloc=a_glob)) == ["'s"]
assert dropck_outlives(Ty("vec_no_phantom", elem=t_insp, alloc=a_glob)) == []  # UAF hole!
assert dropck_outlives(Ty("vec_good", elem=t_ref, alloc=a_ref)) == ["'a"]
assert dropck_outlives(Ty("btree_good", elem=t_ref, alloc=a_ref)) == ["'a"]
assert dropck_outlives(Ty("btree_bad_alloc", elem=t_ref, alloc=a_ref)) == []   # Allocator UAF!
assert dropck_outlives(Ty("typed_arena_std", elem=t_ref)) == []
assert dropck_outlives(Ty("typed_arena_std", elem=t_insp)) == ["'s"]
assert dropck_outlives(Ty("phantom", elem=Ty("fn_ret", elem=t_insp))) == []
assert dropck_outlives(Ty("phantom", elem=Ty("raw_const", elem=t_insp))) == []
assert dropck_outlives(Ty("phantom", elem=t_insp)) == ["'s"]
print("ALL DROPCK & VARIANCE CHECKS PASSED")
```

## Revalidation

1. **Diff the three core `rustc` dropck functions (~250 LOC):** Compare `adt_dtorck_constraint` (`rustc_traits/src/dropck_outlives.rs`), `trivial_dropck_outlives` + `dtorck_constraint_for_ty_inner` (`query/dropck_outlives.rs`), and `destructor_constraints` (`ty/util.rs`). Confirm `PhantomData` still emits `dtorck_types: [T]`, `ManuallyDrop` still short-circuits in `trivial_dropck_outlives`, and `MaybeDangling` remains purely operational (not trivial for `dropck`, as `MaybeDangling` still runs `P`'s destructor, `maybe_dangling.rs:60–62`).
2. **Run a 20-line nightly `rustc` + `cargo miri` discriminator:** Verify `Vec<&'s u8>` compiles when `'s` expires before `Vec` drops while `Vec<Inspector<'s>>` fails with `E0597` unless `PhantomData<T>` is omitted from a custom `#[may_dangle]` struct; run `MIRIFLAGS="-Zmiri-tree-borrows"` on `dealloc(ptr); mem::forget(boxed)` vs. `mem::forget(MaybeDangling::new(boxed))` and on `EyepatchGuard::drop` with vs. without `let _copy = self.0;`.
3. **Check `BoxRaw`, `RawVec`, and `BTreeMap` markers:** Inspect `alloc/src/{boxed.rs, raw_vec/mod.rs, collections/btree/map.rs}` to check whether `BTreeMap`'s `MaybeDangling` `FIXME`s (`L1333, 1369`) have migrated node/allocator wrappers.
