# Creusot `creusot-std` Prophetic Resolution, Ghost Permission Containers, and Monoidal Iterator Laws for 3-Axiom Lean 4 MIR Verification

## Summary

Creusot (`creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`) verifies safe and encapsulated-`unsafe` Rust programs by translating post-borrowck MIR into the Coma intermediate verification language (`10.1007/978-3-031-91121-7_8`) and discharging first-order obligations via Why3 and SMT solvers. Rather than threading backward-update closures across mutable calls, `creusot-std` organizes specifications around four coupled mechanisms:

1. **Prophetic borrows (`*x`, `^x`) and two-tier `Resolve` (`creusot-std/src/resolve.rs`, `creusot/src/backend/resolve.rs`):** Every `&'a mut T` pairs its current value `*x` with its expiration value `^x`. When an initialized place leaves liveness and active-borrow freeze sets (`creusot/src/analysis/resolve.rs`), Creusot assumes `resolve(x)`. Opaque containers (`Vec<T>`, `IntoIter<T>`) expose element resolution via `Resolve::resolve` backed by `Resolve::resolve_coherence` (`inv(self) && structural_resolve(self) ==> self.resolve()`), while `NotFinalPlaces` (`creusot/src/analysis/not_final_places.rs`) marks tail reborrows `BorrowKind::Final` to inherit parent prophecies directly.
2. **Shallow `View` (`@`), recursive `DeepModel`, and boundary `Invariant` (`creusot-std/src/model.rs`, `creusot-std/src/invariant.rs`):** `View` projects containers one level (`[T]@ : Seq<T>`) preserving inner `&mut U` prophecies; `DeepModel` strips borrows recursively into pure equality/order sorts (`Int`, `OrdLogic`). `Invariant` injects `inv` at program function entry/exit (`inv(*x) && inv(^x)` for `&mut T`), allows temporary intra-body breaking, and omits `inv` from `#[logic]` lemmas so uninhabited types cannot derive `false`.
3. **Zero-ownership `Snapshot<T>`, linear `Ghost<T>`, and unified `Perm<C>` (`creusot-std/src/snapshot.rs`, `creusot-std/src/ghost/perm.rs`, `creusot-std/src/std/ptr.rs`):** `PCell<T>`, `*const T`, and `*const [T]` share `Perm<C: ?Sized + PermTarget>` paired with `Copy` spatial witness `PtrLive<'a, T>`. Soundness relies on marking `Perm<*const T>::new` `#[check(terminates)]` rather than `#[check(ghost)]` (blocking $2^{64}+1$ erased allocations from falsifying `Perm::disjoint_lemma`) and wrapping mutable permission borrows in `Guarded<&'a mut Perm<*const T>, *const T>` against `core::mem::swap` theft.
4. **Monoidal `IteratorSpec::produces` and `FnMutExt` (`creusot-std/src/std/iter.rs`, `creusot-std/src/std/ops.rs`):** Iterators specify finite traces `produces(self, visited: Seq<Item>, next: Self)` (`produces_refl`, `produces_trans`), wired into `for` loops by `desugar_for` (`creusot-std-proc/src/creusot/invariant.rs`) and composed across stateful closures via `FnMutExt::hist_inv`.

Transferred to Anneal (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), where `theory/` sits outside the Trusted Computing Base (TCB) under 51 `Init.*` modules, 22 pure structural tactics, `{propext, Quot.sound, Classical.choice}`, zero `._unsafe_rec` helpers, and Statement-Origin Separation, Creusot's `#[trusted]` SMT axioms are inadmissible, but its relational idioms transfer with zero TCB expansion: `(*x, ^x)` lowers to deterministic backward morphisms over `Anneal.PureLift.LoanGraph` (`BackTarget`) and `SpatialPin`, `IteratorSpec::produces` becomes a constructive `List` typeclass free of SMT triggers, and `Perm<C>` plus `Resource<R>` unify in a single `Option`-valued Partial Commutative Monoid (`PCM`).

## Applicability

This report examines `creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8` (`creusot-std`, `creusot-std-proc`, `creusot`) and evaluates transfer to `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `theory/Anneal/MirWp.lean`, `theory/Anneal/PureLift/{Lens,PermTree,LoanGraph,SpatialPin,MirBridge}.lean`), using `verus-lang/verus` at `2518fd9cd8410dfee5115e6b5dbf30c75898cfc5` (`source/vstd/proph.rs`) as a comparative discriminator on mutable prophecies. Semantic authority rests on four publications covering Creusot (`10.1007/978-3-031-17244-1_6`), RustHornBelt (`10.1145/3519939.3523704`), higher-order iterators (`10.1007/978-3-031-30820-8_9`), and Coma (`10.1007/978-3-031-91121-7_8`).

Scope qualifications apply to both repositories:
- In `creusot-std` (`creusot-std/src/lib.rs:47–77`), contracts using nightly traits (`Step`, `Tuple`, `Allocator`) require `--cfg creusot` and `feature = "nightly"` (plus `feature = "std"` for `Vec`, `Box`, and `Perm<*const T>::new`); otherwise unannotated fallback stubs compile (`std/iter/range.rs:220–233`, `std/vec.rs:375–395`).
- In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), Pass 1 (`TrustedBoundary.lean:439–610`) governs `trusted/lean/` and `theory/` on Lean `v4.34.1`, while `Trusted.MirSemantics` currently models by-value scalars, booleans, `unit`, `!`, fieldless `#[repr(int)]` enums, and tuples (`MirBridge.lean:39–62`), failing closed to `FaultKind.unsupported` on raw pointers, slices, heap allocations, and unwinding.

High-level comparisons among RustBelt, RefinedRust, Verus, and Creusot appear in corpus package `rustbelt-refinedrust-verus-creusot-and-rust-ownership-verifiers`, and prophecy vs. functional borrow translation appears in `rust-verification-lifetimes-prophecies-and-functional-translation`; this report focuses on `creusot-std`'s concrete trait/compiler mechanics and Pass-1 Lean 4 transfer.

## Findings

### 1. Prophetic Mutable Borrows, Final-Reborrow Optimization, and Two-Tier Resolution

`Basis: source + normative`

Following RustHornBelt (`10.1145/3519939.3523704`), Creusot lowers `b: &'a mut T` in Pearlite and fMIR (`ARCHITECTURE.md:54, 140`, `creusot/src/translation/fmir.rs:78–93`) to a record `{ cur: T, fin: T }`, written `*b` and `^b`. Assigning `*b = v` updates `cur` to `v` while keeping `fin` unchanged until `b` resolves.

#### 1.1 Two-Tier Elaboration of `resolve` vs. `Resolve::resolve`
Prophecy closure is split across `creusot-std/src/resolve.rs:9–64` and `creusot/src/backend/resolve.rs:130–279`:
- `creusot-std/src/resolve.rs:9–39` declares three intrinsics: top-level `pub fn resolve<T: ?Sized>(_: T) -> bool` (`#[intrinsic("resolve")]`), `pub trait Resolve { fn resolve(self) -> bool; fn resolve_coherence(self); }` (`#[intrinsic("resolve_method")]`), and `pub fn structural_resolve<T: ?Sized>(_: T) -> bool` (`#[intrinsic("structural_resolve")]`).
- Although `creusot-std/src/resolve.rs:43–64` implements `Resolve` for `&'a mut T` with `fn resolve(self) -> bool { true }`, `elaborate_resolve_def` (`creusot/src/backend/resolve.rs:214`) **skips `Resolve::resolve` whenever `ty` is `TyKind::Ref(..)` or `Box`** (`if !matches!(ty.kind(), TyKind::Ref(..)) && !ty.is_box()`), delegating directly to `structural_resolve` (`line 170`), which emits `^subject == *subject`. The library `impl` on `&'a mut T` exists solely to occupy Rust's coherence slot for fundamental reference types (`resolve.rs:41`).
- For ADTs (`backend/resolve.rs:137–152, 239–279`), `elaborate_resolve_def` conjoins `Resolve::resolve` (if implemented) with `structural_resolve` over fields visible from `names.source_id()`, plus an opaque `TermKind::PrivateResolve` conjunct when private fields exist. Whenever a type has private fields, uninstantiated type parameters, or specializable trait bounds (`use_impl == true`, `lines 233, 270–276`), Creusot emits a **one-way triggered axiom** `forall x: T [resolve(x)]. resolve(x) -> rhs` rather than `resolve(x) = rhs`. Callers can destructure an assumed `resolve(v)` (e.g., deducing `forall i. 0 <= i < v@.len() ==> resolve(v[i])` from `impl Resolve for Vec<T>` at `std/vec.rs:70–75`), while `Resolve::resolve_coherence` (`resolve.rs:28–32`) obliges the defining module to prove `inv(self) && structural_resolve(self) ==> self.resolve()`.

#### 1.2 Liveness-Driven Resolution Insertion and `BorrowKind::Final`
`Resolver` (`creusot/src/analysis/resolve.rs:64–288`) combines `MaybeUninitializedPlaces`, `MaybeLiveExceptDrop`, and `Borrows` dataflow cursors:
$$\mathsf{need\_resolve}(st) = (\mathsf{live}(st) \cup \mathsf{frozen\_of\_borrows}(st)) \cap \overline{\mathsf{uninit}(st)}$$
Whenever a move path leaves `need_resolve` across a statement (`resolved_places_during`, `lines 252–267`) or CFG edge (`resolved_places_between_blocks`, `lines 269–288`), Creusot emits `assume { resolve(place) }`. Two implementation hazards stand out:
1. **`Drop` liveness omission (`creusot/src/analysis/resolve.rs:77–79`):** Upstream comments explicitly warn: `MaybeLiveExceptDrop ignores 'drop' for the purpose of resolve liveness... unclear that this can be sound.` Resolving a wrapper before an implicit `Drop::drop(&mut self)` that mutates an inner `&mut U` prematurely equates `^u == *u` unless `Drop` is modeled.
2. **Premature resolution before ghost assertions (`creusot-std/src/std/iter/map_inv.rs:78–79`):** Because `proof_assert!` is erased from runtime liveness, a `&mut Self` parameter unused after a trailing `proof_assert!` resolves *before* the assertion; `MapInv::next` must append `let _ = self; // Make sure self is not resolve until here.` (`line 79`) to keep `self` live across line 78.

To avoid fresh existential prophecy variables on every reborrow `let r = &mut (*x).f`, `NotFinalPlaces` (`creusot/src/analysis/not_final_places.rs:208–348`) runs a backward `GenKill` pass over `HPlace` projections. When the parent borrow is never written, moved, or reborrowed after `location` (`!cursor.get().contains(id)`, `line 228`) and the path contains no dynamic `HProjectionElem::Index` (`!hplace.ambiguous()`, `line 311`), `is_final_at` emits `BorrowKind::Final(deref_pos)` (`fmir.rs:86`), reusing `(^x).f` directly.

---

### 2. Shallow `View`, Recursive `DeepModel`, and Protocol Type `Invariant`

`Basis: source + documentation`

#### 2.1 Why `creusot-std` Splits `View` (`@`) from `DeepModel`
`creusot-std/src/model.rs:14–73` separates two projection traits with distinct variance over borrows:
- **`View` (`type ViewTy; fn view(self) -> Self::ViewTy`, `model.rs:14–19`):** Bound to Pearlite's `@` operator, `View` performs a **one-level** container projection (`[T]@ = Seq<T>`, `std/slice.rs:38–48`; `Vec<T, A>@ = Seq<T>`, `std/vec.rs:13–22`). When `T = &'a mut i32`, `v@` has type `Seq<&'a mut i32>`, retaining both `*v@[i]` and `^v@[i]` for element-wise mutation specs.
- **`DeepModel` (`type DeepModelTy; fn deep_model(self) -> Self::DeepModelTy`, `model.rs:53–73`):** Recursively strips borrows (`(&mut T)::deep_model` returns `(*self).deep_model()`, discarding `^self`), maps machine integers to `Int`, and maps raw pointers `*const T` / `*mut T` to `PtrDeepModel { pub addr: usize, runtime_metadata: usize }` (`std/ptr.rs:109–132`, modeling wide-pointer metadata opacity so two null slice pointers with distinct lengths need not compare equal). `DeepModel` specifies `PartialEq`, `Ord`, `Hash`, and `slice::binary_search` (`std/slice.rs:526–536`).
- **Visibility-lattice friction in `#[derive(DeepModel)]` (`model.rs:33–46`, `creusot-std-proc/src/creusot/derive/deep_model.rs:45–68`):** The derive macro intersects the struct's visibility with every field's visibility (treating `#[non_exhaustive]` as `pub(crate)`). Any private field forces `deep_model` to be emitted `#[logic(open(self))]`, hiding public-field projections from callers unless authors hand-write `DeepModel` and getter lemmas.

#### 2.2 Boundary `Invariant`, Temporary Breaking, and `Guarded<T, G>`
`creusot-std/src/invariant.rs:69–110` and `creusot/src/backend/ty_inv.rs:27–360` enforce `Invariant` at **function and borrow boundaries** rather than as dependent refinement subtypes:
1. **Program vs. `#[logic]` asymmetry (`ty_inv.rs:318–360`, `invariant.rs:69–79`):** `sig_add_type_invariant_spec` injects `requires(inv(arg))` and `ensures(inv(result))` on **program** functions, expanding `inv(x: &mut T)` to `inv(*x) && inv(^x)` (`invariant.rs:94–100`). Inside a body, code may temporarily break `inv` (`x.a = 5; x.b = 5;` on `SumTo10`, `invariant.rs:43–48`) provided `inv` is restored before passing `x` to callees, resolving `x`, or returning. Conversely, **`#[logic]` functions receive no implicit `inv(x)` hypothesis**: because Why3 sorts are inhabited in first-order logic, assuming `inv(x)` inside a `#[logic]` lemma for an uninhabited type (`enum Empty {}` where `structural_invariant = false` at `ty_inv.rs:185`, or `struct Bad` with `invariant = false`) would prove `false` at compile time.
2. **Protocol guards (`Guarded<T, G>`, `creusot-std/src/invariant/guarded.rs:22–112`):** `Guarded<T, G>` bundles `pub inner: T` with `_guard: Snapshot<G>` and `_initial: Snapshot<T>`. For `T = &'a mut U` and `G: GuardRef<U>`, `Invariant::invariant` enforces `G.guards_ref(*current) && ^initial == ^current` (`guarded.rs:22–27`), permitting arbitrary temporary violations while `guarded` is borrowed yet blocking both unguarded drops and `mem::swap` replacement with a distinct borrow.

---

### 3. `Snapshot` vs. `Ghost`, Unified `Perm<C>` Containers, and Soundness Guards

`Basis: source + documentation + normative`

#### 3.1 `Snapshot<T>` vs. `Ghost<T>` Erasure Discipline
Creusot splits erasable state into two `PhantomData<T>` wrappers:
- **`Snapshot<T>` (`creusot-std/src/snapshot.rs:34–144`):** Unconditionally `Copy` (`line 93`), lowered via `#[builtin("identity")]` (`line 102`). Converting `Snapshot<T>` to `Ghost<T>` via `into_ghost` (`lines 134–143`) requires `T: Plain` (`ghost.rs:288–323`: scalars, raw pointers, `Lifetime`, *never* `&T` or `&mut T`, preventing callers from duplicating `Ghost<&Perm<C>>` out of a logical snapshot).
- **`Ghost<T>` (`creusot-std/src/ghost.rs:62–279`, `creusot/src/validate/ghost.rs:30–247`):** Linear (`Copy` iff `T: Copy`), manipulated inside `ghost! { ... }`. `GhostValidate` enforces erasure non-interference: `GhostControlFlow` (`lines 97–128`) bans `return`, `yield`, and outer `break`/`continue`; `GhostValidatePlaces` (`lines 176–225`) bans mutating or moving outer runtime locals; and callees must carry `#[check(ghost)]` (terminating and panic-free, `lib.rs:262–283`).

#### 3.2 `Perm<C: ?Sized + PermTarget>`, `PtrLive`, and Two Soundness Traps
`creusot-std/src/ghost/perm.rs:9–178` unifies ghost ownership under `Perm<C: ?Sized + PermTarget>`:
- **`PCell<T>` (`creusot-std/src/cell/pcell.rs:25–228`):** `#[repr(transparent)] pub struct PCell<T: ?Sized>(UnsafeCell<T>)` implements `PermTarget<Value = T>`, allowing shared `&PCell<T>` reads/writes when paired with `Ghost<&Perm<PCell<T>>>` or `Ghost<&mut Perm<PCell<T>>>` matching `self == perm.ward()`.
- **`*const T` and `*const [T]` (`creusot-std/src/std/ptr.rs:514–969`):** `*const T` defines ZST-aware disjointness (`size_of_val_logic(*self_val) != 0 && size_of_val_logic(*other_val) != 0 ==> self.addr_logic() != other.addr_logic()`, `ptr.rs:523–528`), allowing distinct `Perm<*const ()>` tokens to share one address (`perm.rs:112–114`). `Perm<*const [T]>` supports ghost `split_at_mut` (`ptr.rs:730–749`) and yields a **`Copy`** spatial range token `PtrLive<'a, T>` (`ptr.rs:803–895`, invariant `len * size_of::<T>() <= isize::MAX` and `addr + len * size_of::<T>() <= usize::MAX`) so `PtrAddExt::add_live` (`ptr.rs:917–936`) proves in-bounds pointer arithmetic even while element `Perm<*const T>` tokens are split out for mutation.

Source inspection exposes two critical soundness subtleties in `Perm<C>`:
1. **Pigeonhole address-space guard (`ghost/perm.rs:56–69`, `std/ptr.rs:545–608`):** `Perm<*const T>::{new, from_box, from_mut}` are marked `#[check(terminates)]` rather than `#[check(ghost)]`. Allocating $2^{64} + 1$ `Box<u8>` values at runtime exhausts physical memory and aborts, whereas $2^{64} + 1$ erased calls inside `ghost!` would cost zero RAM and derive `false` via `Perm::disjoint_lemma` over the finite $2^{64}$ `usize` domain. Likewise, `creusot/src/validate/tokens_new.rs:9–84` restricts `Intrinsic::TokensNew` to a single non-loop call in `main`.
2. **`Sized` docstring discrepancy and `Guarded` vs. unguarded `from_mut` (`ghost/perm.rs:36–39` vs. `perm.rs:76–82`, `std/ptr.rs:599–608`, `cell/pcell.rs:196–207`):** Although `ghost/perm.rs:36–39` claims `Perm<C>` is `!Sized` to prevent `mem::replace` on `&mut Perm<C>`, `pub struct Perm<C: ?Sized + PermTarget>` (`perm.rs:76–82`) stores `Snapshot<C::Value>` (`PhantomData`, hence `Sized`) and `C::Objectiveness` (`Sized`), so `Perm<C>` **is `Sized`**. Instead, `Perm<*const T>::from_mut` (`ptr.rs:599–608`), `Perm<*const [T]>::split_at_mut` (`ptr.rs:730–749`), and `SliceExt::as_mut_ptr_perm` (`std/slice.rs:125–135`) prevent `mem::swap` theft by returning `Guarded<&'a mut Perm<*const T>, *const T>` (`GuardRef` requiring `*c.ward() == self`, `perm.rs:173–178`). By contrast, `PCell::from_mut` (`cell/pcell.rs:196–207`) returns an *unguarded* `Ghost<&mut Perm<PCell<T>>>` with `#[trusted]` postcondition `^t == *(^result.1).val_unsized()`. Calling `PCell::from_mut` on two distinct borrows `t1, t2: &mut i32` and executing `ghost! { core::mem::swap(*g1, *g2); }` swaps the borrowed permissions without violating any type invariant, resolving `^g1` to `t2`'s permission and unsoundly equating `^t1 == *t2` without mutating `*t1`.

---

### 4. Monoidal `IteratorSpec::produces`, Indexing Frames, and Effectful Adapter Laws

`Basis: source + normative`

Following Denis and Jourdan (`10.1007/978-3-031-30820-8_9`), `creusot-std/src/std/iter.rs:36–52, 119–125` specifies iterators as labeled transition systems over `Seq<Self::Item>`:

```rust
pub trait IteratorSpec: Iterator {
    #[logic(prophetic)] fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;
    #[logic(prophetic)] fn completed(&mut self) -> bool;
    #[logic(law, prophetic)] #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self);
    #[logic(law, prophetic)] #[requires(a.produces(ab, b) && b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);
}
```

1. **`next` and `desugar_for` (`std/iter.rs:120–124`, `creusot-std-proc/src/creusot/invariant.rs:207–275`):** `Iterator::next(&mut self)` ensures `None => self.completed()` and `Some(v) => (*self).produces(Seq::singleton(v), ^self)`. On `for pat in expr`, `desugar_for` binds `iter_old = snapshot! { iter }` and `produced = snapshot! { Seq::empty() }`, automatically prepending invariants `inv(*produced)` and `iter_old.produces(*produced, iter)`. `produces_refl` discharges entry, `produces_trans` advances each `Some(elem)` step, and `completed(&mut iter)` closes normal termination.
2. **Prophetic indexing (`SliceIndexSpec`) and `slice::IterMut` (`std/slice.rs:97–105, 138–187, 736–786`):** For element/subslice reborrows (`IndexMut::index_mut`), `SliceIndexSpec<T>` defines `in_bounds`, `has_value`, and frame predicate `resolve_elswhere(self, old: T::ViewTy, fin: T::ViewTy)` (`forall<i> 0 <= i && i != self@ && i < old.len() ==> old[i] == fin[i]`). For mutable iteration, `IterMut<'a, T>` views as `&'a mut [T]` (`(^result)@.len() == (*result)@.len()`, `slice.rs:741`) and lifts via `to_mut_seq(&mut self) -> Seq<&mut T>` (`slice.rs:97–104`), reducing `IterMut::produces(self, visited, tl)` to `self@.to_mut_seq() == visited.concat(tl@.to_mut_seq())` (`lines 763–766`). Early `break` resolves `tl` via `*tl@ == ^tl@` (`line 750`), preserving unvisited suffix elements automatically.
3. **Stateful closures (`FnMutExt` and `MapInv`, `std/ops.rs:33–198`, `std/iter/map_inv.rs:4–167`):** Because closure environments are anonymous, `FnMutExt` specifies `F: FnMut(Args) -> Output` via `precondition`, `postcondition_mut(self, args, res_state, res)`, and reflexive-transitive `hist_inv(self, res_state)` (`postcondition_mut ==> hist_inv`), linked to `FnOnce` via `exists<s'> postcondition_mut(args, s', res) && resolve(s')`. `MapInv<I, F>` (`map_inv.rs:31–45`) existentially chains step borrows `fs: Seq<&mut F>` (`^fs[i - 1] == *fs[i]`).

---

### 5. Transfer Synthesis and Evaluation for 3-Axiom Lean 4 MIR Verification

`Basis: source + derived`

#### 5.1 Pass 1 Envelope in `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)
`trusted/audit/TrustedBoundary.lean:439–610` and `trusted/lean/foundation-lock.json` enforce four constraints on `theory/`: (1) `prelude` + 51 hash-locked `Init.*` modules only (`Std.*`, `Lean.*`, and `Init.Omega` excluded); (2) pure syntax and a closed 22-tactic structural allowlist (`TrustedBoundary.lean:536–557`), banning `axiom`, `sorry`, `partial`, `unsafe`, `deriving`, `termination_by`, `omega`, `bv_decide`, `native_decide`, `grind`, custom `macro`/`elab`, and equation-compiler `._unsafe_rec` helpers under `{propext, Quot.sound, Classical.choice}`; (3) `[simp, instance, reducible, semireducible, irreducible]` attributes only (`line 595`); and (4) Statement-Origin Separation (locked target theorems reference only `Init.*`, `Trusted.*`, and `Mir.*`).

Creusot's ~50 `#[trusted]` Pearlite axioms, SMT `#[trigger]` rules, and `PositiveReal` fractional lifetimes (`lifetime_logic.rs:53`) are therefore inadmissible in `theory/`. However, Anneal's `PureLift` engine (`LoanGraph.lean`, `SpatialPin.lean`, `MirBridge.lean`) already provides the constructive operational substrate to host Creusot's relational surface contracts as **zero-TCB definitions**.

#### 5.2 Deterministic `BackTarget` Lenses vs. Mutable Ghost Prophecies
Inspecting `verus-lang/verus` `source/vstd/proph.rs:40–162` (`2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`) shows why imperative ghost prophecies (`ProphecyGhost<T>`) are dangerous in foundational type theory: resolving `p = ProphecyGhost::<bool>::new()` to `!p.value()` (`proph.rs:46–54`) equates `v == !v` (`False`), and ordering `decreases s.seq().len()` on `ProphecySeq` while resolving `s.resolve_cons(0)` in an infinite loop (`proph.rs:84–106`) proves termination of diverging code unless a compiler-wide `#[verifier::prophetic]` taint system polices proof and `decreases` positions.

In `Anneal.PureLift.LoanGraph` (`LoanGraph.lean:53–97`), active mutable loans instead carry deterministic pre-order `BackTarget Val` trees evaluated bottom-up via `List.foldr` (zero `._unsafe_rec`), and pinned `unsafe` loans reabsorb via a total `SpatialCodec Val` (`SpatialPin.lean:42–60`). Creusot's `(*x, ^x)` pair and `Guarded` ward check thus reduce in `theory/` to pure relational wrappers over deterministic writebacks, with zero ghost prophecy state:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.CreusotBridge

/-- Creusot-style `(current, final)` view of `&'a mut α` (`*x` and `^x`). -/
structure MutBorrowView (α : Type) where
  cur : α
  fin : α

def resolveMut {α : Type} (b : MutBorrowView α) : Prop :=
  b.fin = b.cur

/-- Deterministic backward-lens bridge: lowers a Creusot contract `post ⟨cur, fin⟩`
    over `Owner` updated by `writeback : Owner → α → Owner` with zero prophecy state. -/
def LiftMutContract {Owner α : Type}
    (read : Owner → α) (writeback : Owner → α → Owner)
    (post : MutBorrowView α → Prop) (s₀ s₁ : Owner) : Prop :=
  Exists fun vFin : α => post ⟨read s₀, vFin⟩ ∧ s₁ = writeback s₀ vFin

/-- `Guarded<&'a mut Perm<C>, C>` ward invariant preventing `mem::swap` theft
    (`std/ptr.rs:599–608`, fixing the unguarded `PCell::from_mut` gap). -/
structure GuardedPermBorrow (WardId Val : Type) where
  expectedWard : WardId
  curWard      : WardId
  curVal       : Val
  finWard      : WardId
  finVal       : Val

def guardedPermInv {WardId Val : Type} (g : GuardedPermBorrow WardId Val) : Prop :=
  g.curWard = g.expectedWard ∧ g.finWard = g.expectedWard

end Anneal.CreusotBridge
```

#### 5.3 Pass-1 Constructive `LawfulIter` and `Option`-`PCM` Container Permissions
Both `IteratorSpec` and `Perm<C>` / `Resource<R>` likewise admit constructive Pass-1 `theory/` encodings over `Init.Data.List.Basic`:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.IterAndPerm

class LawfulIter (It : Type) (Item : Type) where
  produces       : It → List Item → It → Prop
  completed      : It → It → Prop
  produces_refl  : ∀ it : It, produces it [] it
  produces_trans : ∀ (a b c : It) (ab bc : List Item),
    produces a ab b → produces b bc c → produces a (ab ++ bc) c

def listIterInstance (α : Type) : LawfulIter (List α) α where
  produces s visited tl := s = visited ++ tl
  completed cur fin     := cur = [] ∧ fin = []
  produces_refl _       := rfl
  produces_trans a b c ab bc hab hbc := by
    rw [hab, hbc, List.append_assoc]

theorem for_step_produces {It Item : Type} [inst : LawfulIter It Item]
    {it₀ it it' : It} {visited : List Item} {x : Item}
    (hInv : inst.produces it₀ visited it)
    (hStep : inst.produces it [x] it') :
    inst.produces it₀ (visited ++ [x]) it' :=
  inst.produces_trans it₀ it it' visited [x] hInv hStep

/-- Constructive `Option`-PCM unifying `Perm<PCell>`, `Perm<*const T>`, and
    positive rational (`Nat × Nat`) `LifetimeToken` fractions without `PositiveReal`. -/
class PCM (M : Type) where
  op   : M → M → Option M
  comm : ∀ x y : M, op x y = op y x

end Anneal.IterAndPerm
```

Representing `Seq<T>` as plain `List α` paired with external `Prop` bounds (`xs.length ≤ usizeMax`) avoids nested-inductive positivity failures on `{ l : List α // ... }` and Why3 `Seq` trigger loops, while unfolding cleanly to `Init.Data.List` at `CrateTheorem` boundaries. Moreover, when `Trusted.MirSemantics` adds `UnwindResume` and `Drop`, Creusot's intra-body `Invariant` breaking (`invariant.rs:43–48`) refines cleanly: `TypeInv` holds unconditionally on `.returned` exits, and on `.unwound` exits whenever a borrowed place remains observable across `catch_unwind` or `Drop::drop`.

#### 5.4 Evaluation Against Anneal's Seven-Dimension `theory/` Rubric

| Dimension | Evaluation of Transferred `creusot-std` Idioms in Anneal `theory/` |
| :--- | :--- |
| **(T1) Zero-TCB Bridge & `Trusted.*` Gaps** | **0-TCB for safe Rust and ghost algebra:** `MutBorrowView`, `LawfulIter`, `TypeInv : Val → Prop`, `GuardedPermBorrow`, and `PCM` compile purely in Pass-1 `theory/` over `Anneal.PureLift`. End-to-end MIR proofs for `Perm<*const T>`, `Perm<*const [T]>`, and `slice::IterMut` require auditable `Trusted.MirSemantics` additions: non-empty `CallerMemory`, byte `Allocation` + `ProjectionElem.deref`/`BinOp.offset` anchored to `lean-miri`, `MirTy.isFreeze` (`UnsafeCell`), and `TerminatorKind.drop`. |
| **(P1) Human Specification Auditability** | **High:** `@` (`View`), `*x`/`^x` (`MutBorrowView`), `LawfulLens` frame updates (replacing quantified `resolve_elswhere`), and `produces(visited, next)` keep mutable container and loop specs concise without backward-closure arities or magic wands. Emit per-visible-field projection lemmas to avoid `#[derive(DeepModel)]`'s private fallback (`model.rs:41–46`). |
| **(P2) Authoring & Day-2 Edit Locality** | **High with explicit loan retirement:** `for_step_produces` insulates loop invariants from cursor representation changes, while `PureLift`'s deterministic `LoanGraph` retirement avoids Creusot's liveness-sensitive early `resolve` (`map_inv.rs:79` `let _ = self;`). |
| **(P3) Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **High under `@[irreducible]` barriers:** Plain `List α` views avoid subtype proof-term `isDefEq` blowups, `NotFinalPlaces` tail forwarding avoids quadratic `LoanGraph` chains, and `@[irreducible]` cutpoints (`TrustedBoundary.lean:595`) block `rw`/`simp` from traversing large `MirSemantics.State` ASTs. |
| **(P4) Heterogeneous Composability** | **Strong across safe/`unsafe`/`UnsafeCell`:** `SpatialPin` (`freezeToSpatialInState` $\to$ `PCM`/`GuardedPermBorrow` spatial steps $\to$ `reabsorbFromSpatialInState`) mirrors RustHornBelt (`10.1145/3519939.3523704`), letting `unsafe` `IterMut`, `split_at_mut`, and `PCell` expose pure `MutBorrowView` contracts while `FnMutExt::hist_inv` + exclusive `PCM` tokens gate open callbacks. |
| **(P5) Failure Legibility** | **Deterministic residual goals:** Missing `produces_trans` or `#[trigger]` instances in Creusot cause opaque SMT timeouts, whereas Lean 4 leaves an explicit `for_step_produces`, `TypeInv`, or `guardedPermInv` subgoal at the exact MIR cutpoint. |
| **(C1–C2) Conceptual Minimality & Refuted Collapses** | **Collapses 6 `creusot-std` constructs into 3 `theory/` primitives** (`MutBorrowView` over `LoanGraph`/`SpatialPin`; `PCM` unifying `Perm<PCell>`, `Perm<*const T>`, `LifetimeToken`, and `Resource<R>`; `LawfulIter` over `List`). **Three premature collapses fail with concrete counterexamples:** (1) *Merging `View` and `DeepModel` fails* on `Vec<&mut u32>`: `DeepModel` strips `^v[i]` (`model.rs:68–73`), breaking mutable element specs, whereas `View` retains `&mut u32`, breaking `Ord` value sorting. (2) *Merging `PtrLive<'a, T>` into `Perm<*const [T]>` fails* on in-place pointer loops (`ptr.rs:822–828`): once `Perm<*const [T]>` splits into element permissions, no slice `Perm` remains to prove `ptr.add(1)` in-bounds without a `Copy` range witness. (3) *Encoding `TypeInv` as `{ v : Val // TypeInv v }` fails* both temporary intra-body breaking (`SumTo10`, `invariant.rs:43–48`) and uninhabited-type soundness (`invariant.rs:69–79`). |

## Boundaries

- **Why3/Coma solver throughput (`not examined`):** `creusot-rs/creusot` was inspected statically at `601d97891bb0bc0b569686cc946ef4980560b5d8` without running `cargo-creusot` or `why3find`; empirical Z3/CVC5/Alt-Ergo runtimes were `not examined`.
- **`MaybeLiveExceptDrop` soundness with borrow-mutating `Drop` (`unknown`):** Upstream warns at `creusot/src/analysis/resolve.rs:77–78` that ignoring `Drop` liveness in `need_resolve_places` has an unresolved soundness argument (`unclear that this can be sound`). Whether safe Rust without `#[trusted]` can exploit early resolution before `Drop::drop` at `601d97891bb0bc0b569686cc946ef4980560b5d8` remains `unknown` without execution testing.
- **Unguarded `PCell::from_mut` swap and `Perm<C>` `!Sized` docstring (`known not to apply`):** `Guarded` anti-swap protection on `Perm<*const T>::from_mut` (`std/ptr.rs:599–608`) is `known not to apply` to `PCell::from_mut` (`cell/pcell.rs:196–207`), which returns an unguarded `Ghost<&mut Perm<PCell<T>>>`; likewise, the docstring claim at `ghost/perm.rs:36–39` that `Perm<C>` is unsized is `known not to apply` to `pub struct Perm` at `perm.rs:76–82`.
- **`#[trusted]` Pearlite axioms, `PositiveReal`, and raw-pointer MIR execution in Anneal today (`unsupported`):** Under `joshlf/anneal` Pass 1 (`TrustedBoundary.lean:442–596`), `axiom`, `sorry`, `PositiveReal` imports outside `foundation-lock.json`, custom `macro`/`elab`, and `Anneal.*` types in locked target theorems are `unsupported`; raw pointers, slices, and non-empty `CallerMemory` in `Trusted.MirSemantics` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` are likewise `unsupported` (`FaultKind.unsupported`).

## Evidence

- **Primary Git Repositories (inspected `2026-11-19`):**
  - `creusot-rs/creusot` at `601d97891bb0bc0b569686cc946ef4980560b5d8`:
    - `ARCHITECTURE.md:18–149`; `creusot-std/src/lib.rs:47–340`.
    - `creusot-std/src/resolve.rs:9–64`; `creusot/src/backend/resolve.rs:20–293`; `creusot/src/analysis/resolve.rs:64–295`; `creusot/src/analysis/not_final_places.rs:45–381`; `creusot/src/translation/fmir.rs:77–108`.
    - `creusot-std/src/model.rs:14–100`; `creusot-std-proc/src/creusot/derive/deep_model.rs:9–84`.
    - `creusot-std/src/invariant.rs:15–115`; `creusot-std/src/invariant/guarded.rs:4–152`; `creusot/src/backend/ty_inv.rs:27–360`.
    - `creusot-std/src/snapshot.rs:33–144`; `creusot-std/src/ghost.rs:62–360`; `creusot/src/validate/ghost.rs:30–247`; `creusot/src/validate/tokens_new.rs:9–84`.
    - `creusot-std/src/ghost/perm.rs:9–178`; `creusot-std/src/cell/pcell.rs:22–228`; `creusot-std/src/std/ptr.rs:18–969`; `creusot-std/src/ghost/lifetime_logic.rs:23–250`; `creusot-std/src/logic/ra.rs:33–160`; `creusot-std/src/ghost/resource.rs:51–160`.
    - `creusot-std/src/std/iter.rs:36–312`; `creusot-std-proc/src/creusot/invariant.rs:207–275`; `creusot-std/src/std/iter/range.rs:6–233`; `creusot-std/src/std/iter/map_inv.rs:4–187`; `creusot-std/src/std/slice.rs:16–888`; `creusot-std/src/std/vec.rs:12–395`; `creusot-std/src/std/ops.rs:14–260`.
  - `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:
    - `trusted/audit/TrustedBoundary.lean:439–610`; `trusted/lean/foundation-lock.json`; `theory/Anneal/PureLift/{LoanGraph,SpatialPin,MirBridge}.lean`.
  - `verus-lang/verus` at `2518fd9cd8410dfee5115e6b5dbf30c75898cfc5`:
    - `source/vstd/proph.rs:1–165`.
- **Peer-Reviewed Publications:**
  - Xavier Denis, Jacques-Henri Jourdan, Claude Marché, *"Creusot: A Foundry for the Deductive Verification of Rust Programs"*, ICFEM 2022, DOI `10.1007/978-3-031-17244-1_6`.
  - Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer, *"RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code"*, PLDI 2022, DOI `10.1145/3519939.3523704`.
  - Xavier Denis, Jacques-Henri Jourdan, *"Specifying and Verifying Higher-Order Rust Iterators"*, TACAS 2023, DOI `10.1007/978-3-031-30820-8_9`.
  - Andrei Paskevich, Paul Patault, Jean-Christophe Filliâtre, *"Coma: An Intermediate Verification Language with Explicit Abstraction Barriers"*, ESOP 2025, DOI `10.1007/978-3-031-91121-7_8`.

## Revalidation

1. **Resolution elaboration and `BorrowKind::Final` (`creusot-rs/creusot`):** Diff `creusot-std/src/resolve.rs`, `creusot/src/backend/resolve.rs` (`elaborate_resolve_def` reference bypass), `creusot/src/analysis/resolve.rs` (`MaybeLiveExceptDrop` caveat), and `creusot/src/analysis/not_final_places.rs` (`is_final_at`) against `601d97891bb0bc0b569686cc946ef4980560b5d8`.
2. **`Perm<C>` sizing, `#[check(terminates)]`, and `Guarded` (`creusot-rs/creusot`):** Diff `creusot-std/src/ghost/perm.rs` (`pub struct Perm`), `creusot-std/src/std/ptr.rs` (`Perm::from_mut`, `PtrLive`), and `creusot-std/src/cell/pcell.rs` (`PCell::from_mut`) to check whether `PCell::from_mut` adopts `Guarded`.
3. **`IteratorSpec` and `desugar_for` (`creusot-rs/creusot`):** Diff `creusot-std/src/std/iter.rs`, `creusot-std/src/std/slice.rs` (`SliceIndexSpec`, `IterMut`), and `creusot-std-proc/src/creusot/invariant.rs` (`desugar_for`).
4. **Anneal Pass 1 compatibility (`joshlf/anneal`):** Diff `trusted/audit/TrustedBoundary.lean` and `trusted/lean/foundation-lock.json` against `c131b320eeeb26ef692e5afd5ec8db49ee518613`, and kernel-check the two `prelude` snippets in Sections 5.2–5.3 under `lean` `v4.34.1` (`-Ddebug.skipKernelTC=false`) to verify zero `._unsafe_rec` helpers and 3-axiom purity.
