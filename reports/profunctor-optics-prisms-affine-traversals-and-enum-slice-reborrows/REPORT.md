# First-Order and Profunctor Optics for Rust Enum Variant, Partial-Initialization, and Slice Sub-Range Place Projections in Pass-1 Lean 4

## Summary

Rust Mid-level Intermediate Representation (MIR) place expressions address sub-storage through composite paths combining product fields (`ProjectionElem::Field`), sum-variant narrowing (`Downcast`), element and sub-range indexing (`Index`, `ConstantIndex`, `Subslice`), and pointer indirection (`Deref`). In functional borrow-lifting calculi such as `Anneal.PureLift` (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), every non-dereference projection and mutable-reborrow writeback is mediated by bidirectional accessors over pure value trees.

Evaluating first-order concrete optics against higher-order profunctor encodings across `purescript-profunctor-lenses`, `well-typed/optics`, `Monocle`, `AeneasVerif/aeneas`, and Lean 4 (`v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`) establishes five results:

1. **First-order `AffineOptic` strictly dominates rank-2 profunctor encodings in Pass-1 Lean 4:** Quantifying over `p : Type u → Type u → Type u` bumps the optic type into `Type (u + 1)`, prevents storing optics inside `Type u` `LoanEntry` tables, and adds `Strong`/`Choice` dictionary-projection overhead in `whnf`. By the Yoneda/Tambara isomorphism, concrete `AffineOptic S A` (`preview : S → Option A`, `set : S → A → Option S`) retains identical compositionality inside `Type u` with zero typeclasses and $O(\text{depth})$ constructor-headed reduction.
2. **Fallible `set : S → A → Option S` is required for Rust UB soundness, refuting total `Optional.replace` (`S → A → S`):** Standard `Stall`/`Optional` optics make writes to absent variants silent no-ops (`preview s = none → replace a s = s`), which would mask writes to inactive `Downcast` variants or length-corrupting `split_at_mut` writebacks. Fail-closed `AffineOptic` requires `preview_none_set_none : preview s = none → set s a = none`, mapping invalid writes to `EvalOutcome.fail`.
3. **Partially initialized `SlotVal.uninit` tuples require an asymmetric `PlaceSlotOptic`:** Under `deinitMovedPlace = true`, a moved-from field `_1.0` must reject reads (`readInit s = none`) while admitting re-initializing writes (`writeInit s v = some s'`). Collapsing `.uninit` field access and enum `Downcast` into a single symmetric optic law either blocks safe field re-initialization or masks inactive-variant UB.
4. **`SetDiscriminant` is `Prism.review`, not `AffineOptic.set`:** Variant tag assignment (`StatementKind::SetDiscriminant`) injects a variant without requiring prior inhabitation of that variant, whereas `Downcast` is `Prism.toAffineOptic` gated on `preview s = some _`.
5. **Plain `List Val` with `LawfulSliceBack` avoids Aeneas's `ListN` `HEq` and strict-positivity traps:** Encoding slice sub-ranges as `sliceRangeOptic lo hi` over `List α` with `sub.length == hi - lo` satisfies nested-inductive positivity, avoids `HEq` and Pass-1-banned `grind`, and lets `split_at_mut` install two independently expiring loans in `PermTree`.

## Applicability

This report applies to zero-TCB `theory/` place-projection and borrow-lifting modules in `joshlf/anneal` (`main` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`) audited on `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). Pass 1 (`trusted/audit/TrustedBoundary.lean:442–596` and `trusted/lean/foundation-lock.json`) enforces: (a) explicit `prelude` + 51 locked `Init.*` modules only (excluding `Std.*` and `Lean.*`); (b) a closed 22-tactic pure allowlist excluding `omega`, `grind`, `bv_decide`, `native_decide`, `aesop`, `deriving`, `partial`, `unsafe`, `termination_by`, `noncomputable section`, and `._unsafe_rec` compiler helpers; (c) kernel replay under `{propext, Quot.sound, Classical.choice}`; and (d) Statement-Origin Separation (`CrateTheorem`, `UnitTheorem`, and `BodyVerified` reference only `Init.*`, `Trusted.*`, and `Mir.*`).

Subject roles:
- `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`) defines `Runtime(PostCleanup)` MIR `ProjectionElem`, `SetDiscriminant`, and `core::slice::split_at_mut`, consumed by `joshlf/anneal` and downstream crates such as `google/zerocopy` (`ec133ce4d7993775413d852f91c9e3eb2a2a0897`).
- Pickering et al. (2017), Boisseau and Gibbons (2018), and Clarke et al. (2024) establish the categorical equivalences implemented in `purescript-contrib/purescript-profunctor-lenses` (`c479df47cc386b840c5e7238b4b5b1b3e9e2c4ff`), `well-typed/optics` (`dd0b30e144ad92f77584dc8357c381eed2243028`), and `optics-dev/Monocle` (`33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`).
- `AeneasVerif/aeneas` (`d86aa34c75fd036ac139eb6e65da1cacc5492d0f`) provides comparative Lean 4 `Slice` (`SliceDef.lean`, `Issue1138SlicePositivity.lean`) and `split_at_mut` (`Slice.lean`) baselines.

For general LLBC borrow translation, MIR phase ordering, `UnsafeCell` partial SROA, and binary wire codecs, see corpus packages `aeneas-borrows-symbolic-ownership-and-resource-semantics`, `rust-verification-lifetimes-prophecies-and-functional-translation`, `rustc-postcleanup-mir-place-path-lens-and-borrow-semantics`, `partial-sroa-escaping-fields-and-unsafecell-hybrid-memory-lenses`, and `bidirectional-lenses-resugaring-and-non-malleable-format-compilers`.

## Findings

### 1. Categorical Taxonomy Mapped to Rust MIR `ProjectionElem`

`Basis: normative + source + derived`

In `compiler/rustc_middle/src/mir/syntax.rs:1174–1255` (`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`), `Place<'tcx>` pairs `local: Local` with `&'tcx List<PlaceElem<'tcx>>` over `ProjectionElem<V, T>`:

```rust
pub enum ProjectionElem<V, T> {
    Deref,
    Field(FieldIdx, T),
    Index(V),
    ConstantIndex { offset: u64, min_length: u64, from_end: bool },
    Subslice { from: u64, to: u64, from_end: bool },
    Downcast(Option<Symbol>, VariantIdx),
    OpaqueCast(T),
    UnwrapUnsafeBinder(T),
    PhantomDeref,
}
```

In Clarke et al. (2024, §2–§4, `doi:10.32408/compositionality-6-1`) and Pickering, Gibbons, and Wu (2017, §3–§4, `doi:10.22152/programming-journal.org/2017/1/7`), monomorphic optics from $S$ to $A$ arise from monoidal actions $\bullet : \mathcal{M} \times \mathbf{Set} \to \mathbf{Set}$ via $\mathsf{Optic}_{\mathcal{M}}(S, A) \cong \int^{M \in \mathcal{M}} \mathbf{Set}(S, M \bullet A) \times \mathbf{Set}(M \bullet A, S)$:

| Optic Class | Action $M \bullet A$ | Concrete Signature | Rust MIR Projection / Reborrow Role |
| :--- | :--- | :--- | :--- |
| **`Iso`** | $A$ | `view : S → A`, `review : A → S` | `#[repr(transparent)]` newtype, `UnwrapUnsafeBinder` |
| **Total `Lens`** | $C \times A$ | `get : S → A`, `put : S → A → S` | Initialized struct or tuple `Field(f, T)` |
| **`Prism`** | $C + A$ | `preview : S → Option A`, `review : A → S` | Single-payload enum variant (`Some`, `Ok`) + `SetDiscriminant` |
| **Fallible `AffineOptic`** | $C_1 + C_2 \times A$ | `preview : S → Option A`, `set : S → A → Option S` | `Downcast(_, idx)` composed with `Field`, bounds-checked `Index`/`ConstantIndex`/`Subslice`, `split_at_mut` |
| **`PlaceSlotOptic`** | $C \times (1 + A)$ | `readInit : S → Option A`, `writeInit : S → A → Option S` | Partial-move `SlotVal.uninit` tuple/struct fields (`deinitMovedPlace = true`) |
| **`IndexedOptic`** | $C_1 + C_2 \times (I \times A)$ | `ipreview : S → Option (I × A)`, `iset : S → A → Option S` | `Index(local)`, `Subslice`, `split_at_mut(mid)` carrying `(lo, hi)` interval witness |

In `Anneal.PureLift.Lens` (`theory/Anneal/PureLift/Lens.lean:112–122` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Lens S A` (`get : S → Option A`, `put : S → A → Option S`) already uses the fallible `AffineOptic` carrier paired with `LawfulLens` (`get_put`, `put_get`, `put_put`). However, `PureLift` on `main` leaves two gaps:
1. `LawfulLens` omits the miss-rejection law `get s = none → put s a = none`. Notably, in `MirBridge.lean:404–422`, `getMirFieldAt d f (.tuple fields)` returns `none` when the existing child `c` fails `valDepthOk d c`, yet `setMirFieldAt d f (.tuple fields) child` succeeds (`some`) whenever `valDepthOk d child = true`!
2. `SubPath := List FieldIdx` (`Lens.lean:39`) and `ValAlgebra` (`Lens.lean:313–337`) index homogeneous `Val` solely by `FieldIdx := Nat` where `f ≠ g` implies disjoint storage; `Val.enumVal` and `Val.bytes` return `none` on all projections (`MirBridge.lean:404–422`).

### 2. Higher-Order Profunctor Optics vs. First-Order `AffineOptic` in Lean 4 (`v4.34.1`)

`Basis: source + derived`

In `purescript-contrib/purescript-profunctor-lenses` (`src/Data/Lens/Types.purs:60–153`, `src/Data/Lens/AffineTraversal.purs:23–52`, and `src/Data/Lens/Internal/Stall.purs:14–54` at `c479df47cc386b840c5e7238b4b5b1b3e9e2c4ff`), optics quantify universally over constrained profunctors:

```purescript
type Optic p s t a b = p a b -> p s t
type Lens s t a b = forall p. Strong p => Optic p s t a b
type Prism s t a b = forall p. Choice p => Optic p s t a b
type AffineTraversal s t a b = forall p. Strong p => Choice p => Optic p s t a b
```

Similarly, `well-typed/optics` (`optics-core/src/Optics/Internal/Optic.hs:51–130` and `Optics/Internal/Optic/Types.hs:48–60` at `dd0b30e144ad92f77584dc8357c381eed2243028`) wraps `forall p i. (Profunctor p, Constraints k p) => p i a b -> p (Curry is i) s t` and resolves heterogeneous composition via multi-parameter typeclasses `JoinKinds k l m` and `AppendIndices is js ks`.

In Lean 4 (`v4.34.1`), higher-order profunctor encodings suffer four structural defects under Pass 1:

1. **Universe-level bump (`Type (u + 1)`) and container impredicativity:** Because Lean 4's `Type u` hierarchy is predicative, quantifying over `p : Type u → Type u → Type u` forces:
   ```lean
   def ProfAffine (S T A B : Type u) : Type (u + 1) :=
     ∀ (p : Type u → Type u → Type u), [Strong p] → [Choice p] → p A B → p S T
   ```
   For `Val : Type 0`, `ProfAffine Val Val Val Val : Type 1` cannot be stored inside `Type 0` structures (`LoanEntry Val`, `RegionGroupEntry Val` in `LoanGraph.lean`) without bumping `SymState Val` to `Type 1`. Even in PureScript, constrained rank-2 optics fail record-field unification (`docs/Impredicativity.md:15–148`), forcing concrete `Shop`/`Market`/`Stall` (`AnAffineTraversal`) wrappers and `cloneAffineTraversal` conversions (`AffineTraversal.purs:46–52`).
2. **Zero expressiveness gain over concrete `AffineOptic` (Yoneda/Tambara isomorphism):** By Pickering et al. (2017, §4.3) and Boisseau and Gibbons (2018, §3–§4, `doi:10.1145/3236779`), `Stall A B` (`data Stall a b s t = Stall (s -> b -> t) (s -> Either t a)`, `Stall.purs:14`) is the free `Strong + Choice` Tambara module, so evaluating `l (Stall (fun _ b => b) .inr)` (`withAffineTraversal`, `AffineTraversal.purs:43–44`) establishes an exact isomorphism with concrete matcher/setter pairs.
3. **C++ kernel `whnf` and `isDefEq` overhead (`leanprover/lean4` `src/kernel/type_checker.cpp:393–407, 555–602`):** A chain of $k$ profunctor compositions builds nested `dimap` / `Strong.second` / `Choice.right` dictionary projections (`AffineTraversal.purs:36`) and `JoinKinds` cast wrappers (`Optic.hs:119–129`). During kernel `rfl` or `dsimp`, `whnf_core` must delta-unfold typeclass instances (`unfold_definition`, `type_checker.cpp:589–602`) and beta-reduce allocated closures, whereas first-order `AffineOptic.comp` unfolds to two flat `Option` pattern matches reduced directly by `inductive_reduce_rec` (`type_checker.cpp:399`).
4. **No free laws under `Classical.choice`:** Unlike Reynolds parametricity in pure System F, Lean 4 admits `Classical.choice`, so arbitrary `Type u → Type u → Type u` profunctor transformers can inspect types non-parametrically; proving lens/affine laws still requires reifying to `preview` and `set`.

### 3. Fallible `AffineOptic` (`S → A → Option S`) vs. Total `Optional` (`S → A → S`)

`Basis: source + derived`

In `optics-dev/Monocle` (`core/shared/src/main/scala/monocle/law/OptionalLaws.scala:9–20` at `33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05`), concrete `Optional[S, A]` uses a **total** setter `replace: A => S => S`:

```scala
def getOptionReplace(s: S): IsEq[S] =
  optional.getOrModify(s).fold(identity, optional.replace(_)(s)) <==> s
def replaceGetOption(s: S, a: A): IsEq[Option[A]] =
  optional.getOption(optional.replace(a)(s)) <==> optional.getOption(s).map(_ => a)
```

When `getOption(s) == None`, `getOptionReplace` forces `replace(a)(s) == s` (a silent no-op). For Rust MIR verification, total silent-no-op `replace` is **unsound**:

- **Inactive-variant `Downcast` write:** Writing `(_1 as Some).0 = 42` when `_1` holds `None` without updating the discriminant violates variant/niche validity; returning `.ok None` masks Undefined Behavior instead of faulting.
- **Length-violating `split_at_mut` writeback:** In `AeneasVerif/aeneas` (`backends/lean/Aeneas/Std/Slice.lean:745–752` at `d86aa34c75fd036ac139eb6e65da1cacc5492d0f`), `split_at_mut`'s backward closure `back : (Slice T × Slice T) → Slice T` uses `if h1 : s0'.length = s0.length ∧ s1'.length = s1.length then .from (s0'.val ++ s1'.val) ... else s`. While safe Rust callers preserve slice length automatically, in Anneal `PureLift` composes with `unsafe` `SpatialPin` blocks (`SpatialPin.lean:249–293`) and user-supplied `CallSummary` closures (`Plan.lean:226–240`); falling back to `else s` would silently discard an out-of-bounds spatial length mutation rather than rejecting it.

Anneal's canonical `AffineOptic` therefore uses `set : S → A → Option S` and enforces **four** laws—adding explicit fail-closed miss propagation `preview_none_set_none`:

```lean
prelude
import Init.Core

namespace Anneal.Optic

/-- Fail-closed first-order affine optic (`0`-or-`1` focus with fallible writeback). -/
structure AffineOptic (S A : Type) where
  preview : S → Option A
  set     : S → A → Option S

structure LawfulAffineOptic {S A : Type} (o : AffineOptic S A) : Prop where
  preview_set           : ∀ s a, o.preview s = some a → o.set s a = some s
  set_preview           : ∀ s a s', o.set s a = some s' → o.preview s' = some a
  set_set               : ∀ s a₁ a₂ s₁, o.set s a₁ = some s₁ → o.set s₁ a₂ = o.set s a₂
  preview_none_set_none : ∀ s a, o.preview s = none → o.set s a = none

def AffineOptic.comp {S A B : Type}
    (outer : AffineOptic S A) (inner : AffineOptic A B) : AffineOptic S B where
  preview s :=
    match outer.preview s with
    | some a => inner.preview a
    | none   => none
  set s b :=
    match outer.preview s with
    | some a =>
      match inner.set a b with
      | some a' => outer.set s a'
      | none    => none
    | none => none

end Anneal.Optic
```

`AffineOptic.comp` preserves all four `LawfulAffineOptic` laws via elementary Pass-1 tactics (`cases`, `injection`, `subst`, `rw`, `rfl`).

### 4. `Enum` `Downcast`, `SetDiscriminant`, and Partially Initialized `SlotVal.uninit`

`Basis: normative + source + derived`

#### 4.1 `Prism` (`SetDiscriminant`) vs. `Prism.toAffineOptic` (`Downcast`)

In `compiler/rustc_middle/src/mir/syntax.rs:365, 1245–1250` (`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`), `StatementKind::SetDiscriminant { place, variant_index }` sets the active variant tag, whereas `ProjectionElem::Downcast(_, variant_index)` narrows place typing to `variant_index`. A `Prism` separates these two roles cleanly:

```lean
structure Prism (S A : Type) where
  preview : S → Option A
  review  : A → S

structure LawfulPrism {S A : Type} (p : Prism S A) : Prop where
  preview_review : ∀ a, p.preview (p.review a) = some a
  review_preview : ∀ s a, p.preview s = some a → p.review a = s

def Prism.toAffineOptic {S A : Type} (p : Prism S A) : AffineOptic S A where
  preview := p.preview
  set s a :=
    match p.preview s with
    | some _ => some (p.review a)
    | none   => none
```

Gating `set` on `match p.preview s with | some _ => ...` is essential: without it, `preview_none_set_none` fails and writing through a `Downcast` projection on `Option::None` would silently flip the tag to `Option::Some` without a `SetDiscriminant` statement. Composing `structFieldOptic` with `somePrism.toAffineOptic` or `okPrism.toAffineOptic` models nested `&mut pkt.opt_len` (`if let Some(ref mut v) = pkt.opt_len`) directly.

#### 4.2 Partial Initialization (`SlotVal.uninit`) Requires Asymmetric `PlaceSlotOptic`

In `Trusted.MirSemantics` (`trusted/lean/Trusted/MirSemantics.lean:140–149, 621–624` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Operand.move` deinitializes non-ZST storage (`deinitMovedPlace = true`). Extending local frame slots from whole-local `Option Val` to field-granular partial moves introduces recursive `SlotVal`:

```lean
inductive SlotVal (Val : Type) where
  | uninit : SlotVal Val
  | init   : Val → SlotVal Val
  | tuple  : List (SlotVal Val) → SlotVal Val
  | adt    : Option Nat → List (SlotVal Val) → SlotVal Val
```

Consider `s = SlotVal.tuple [.uninit, .init v₁]` after `_tmp = move (_1.0)`:
- Reading `_1.0` (`Operand.copy (_1.0)`) MUST return `none` (reading uninitialized storage faults with `FaultKind.undefined`).
- Assigning `_1.0 = 5` (`StatementKind.assign`) MUST return `some (.tuple [.init 5, .init v₁])` (re-initializing a moved tuple field is valid safe Rust).

Hence `readInit s = none` while `writeInit s 5 = some s'`, **violating `preview_none_set_none`**. Frame-slot access therefore separates structural path validity (`canWrite : S → Bool`, checking tuple bounds and active ADT variant tag) from leaf initialization (`readInit : S → Option Val`):

```lean
structure PlaceSlotOptic (S Val : Type) where
  canWrite  : S → Bool
  readInit  : S → Option Val
  writeInit : S → Val → Option S
  deinit    : S → Option S

structure LawfulPlaceSlotOptic {S Val : Type} (p : PlaceSlotOptic S Val) : Prop where
  read_implies_canWrite     : ∀ s v, p.readInit s = some v → p.canWrite s = true
  canWrite_iff_write        : ∀ s v, p.canWrite s = true ↔ ∃ s', p.writeInit s v = some s'
  read_write                : ∀ s v, p.readInit s = some v → p.writeInit s v = some s
  write_read                : ∀ s v s', p.writeInit s v = some s' → p.readInit s' = some v
  write_write               : ∀ s v₁ v₂ s₁, p.writeInit s v₁ = some s₁ → p.writeInit s₁ v₂ = p.writeInit s v₂
  deinit_read_none          : ∀ s s', p.deinit s = some s' → p.readInit s' = none
  deinit_preserves_canWrite : ∀ s s', p.deinit s = some s' → p.canWrite s' = p.canWrite s
```

When `Rvalue.ref` creates a safe `&T` or `&mut T` borrow, Rust's reference validity invariant requires the target sub-place to be fully initialized (`readInit s = some v`), transitioning cleanly from frame-level `PlaceSlotOptic` to loan-level `LawfulAffineOptic`.

### 5. Disjoint Slice Sub-Ranges (`split_at_mut`) and `LawfulSliceBack`

`Basis: normative + source + derived`

In `library/core/src/slice/mod.rs:1997–2065` (`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`), `slice::split_at_mut(&mut self, mid: usize)` checks `mid <= self.len()` and partitions `[0, len)` into `[0, mid)` and `[mid, len)`. Inspecting `AeneasVerif/aeneas` (`backends/lean/Aeneas/Std/SliceDef.lean:10–69` and `Slice.lean:740–785` at `d86aa34c75fd036ac139eb6e65da1cacc5492d0f`) reveals three hazards in dependent Lean 4 slice encodings:

1. **Subtype strict-positivity rejection:** Defining `Slice α := { l : List α // l.length ≤ max }` causes Lean 4's kernel to reject recursive sum types such as `inductive E3 where | V : Slice E3 → E3` (`tests/lean/Issue1138SlicePositivity.lean:38–39`).
2. **`ListN` `HEq` and `grind` dependency:** Aeneas's `ListN α leng` workaround (`SliceDef.lean:15–18`) forces heterogeneous equality `s1.list ≍ s0.list` and `grind` in `Slice.eq_iff` (`SliceDef.lean:58–64`), violating Pass 1.
3. **Coupled pair-backward lifetimes:** Returning a single closure `((Slice T × Slice T) → Slice T)` (`Slice.lean:741`) keeps both halves lifetime-coupled until both borrows end.

Modeling slices over plain `List α` (keeping `xs.length ≤ usizeMax` as a separate `Prop` invariant) and defining range projections via `sliceRangeOptic lo hi` eliminates all three hazards:

```lean
def listSlice (lo hi : Nat) (xs : List α) : Option (List α) :=
  if Nat.ble lo hi && Nat.ble hi xs.length then
    some ((xs.drop lo).take (hi - lo))
  else
    none

def listSplice (lo hi : Nat) (xs sub : List α) : Option (List α) :=
  if Nat.ble lo hi && Nat.ble hi xs.length && Nat.beq sub.length (hi - lo) then
    some (xs.take lo ++ sub ++ xs.drop hi)
  else
    none

def sliceRangeOptic (lo hi : Nat) : AffineOptic (List α) (List α) where
  preview xs := listSlice lo hi xs
  set xs sub := listSplice lo hi xs sub

def LawfulSliceBack {α : Type} (o : AffineOptic (List α) (List α)) (len : Nat) : Prop :=
  ∀ xs sub xs', o.set xs sub = some xs' → sub.length = len ∧ xs'.length = xs.length
```

Enforcing `Nat.beq sub.length (hi - lo)` inside `listSplice` guarantees both `LawfulAffineOptic (sliceRangeOptic lo hi)` and `LawfulSliceBack (sliceRangeOptic lo hi) (hi - lo)`, while allowing `split_at_mut(mid)` to register **two independent loans** at `[.sliceRange 0 mid]` and `[.sliceRange mid len]` that reborrow and end independently.

### 6. `PathSeg` Permission Tries and First-Order `ProphecyPair` Duality

`Basis: source + derived`

Replacing `FieldIdx` in `Anneal.PureLift.PermTree` (`PermTree.lean:39–126`) with `PathSeg` unifies product, variant, element, and sub-slice disjointness in one trie:

```lean
inductive PathSeg where
  | field      (idx : Nat)
  | variant    (discrIdx : Nat)
  | sliceElem  (idx : Nat)
  | sliceRange (lo hi : Nat)

def PathSeg.disjoint : PathSeg → PathSeg → Bool
  | .field f, .field g => !Nat.beq f g
  | .variant u, .variant v => !Nat.beq u v
  | .sliceElem i, .sliceElem j => !Nat.beq i j
  | .sliceElem i, .sliceRange lo hi => Nat.blt i lo || Nat.ble hi i
  | .sliceRange lo hi, .sliceElem i => Nat.blt i lo || Nat.ble hi i
  | .sliceRange lo₁ hi₁, .sliceRange lo₂ hi₂ => Nat.ble hi₁ lo₂ || Nat.ble hi₂ lo₁
  | _, _ => false
```

- **Boundary empty slices (`lo == hi`):** For `split_at_mut(0)`, `PathSeg.disjoint (.sliceRange 0 0) (.sliceRange 0 len)` evaluates `Nat.ble 0 0 = true`, matching `core::slice::split_at_unchecked` (`slice_mod.rs:2026–2042`). Heterogeneous mismatches (`.field 0` vs `.variant 0`) return `false` (fail-closed overlap).
- **Uniform `Type 0` carrier:** Extending `Val` with `.adtVal typeId variant fields` and `.sliceVal elems` keeps `LoanEntry Val : Type 0` via `AffineOptic Val Val`, avoiding `Type 1` existential focus packing (`Σ A : Type, AffineOptic S A`).
- **Prophecy duality:** Any `unsafe` helper returning `&'a mut A` from `&'a mut S` (modeled in *RustHornBelt* via `(cur : A, fut : A)`) corresponds to an `AffineOptic`: borrow creation yields `cur` (`o.preview s = some cur`), and `endLoanInState` writes `fut` back (`o.set s fut = some s'`), keeping contracts first-order without mutable ghost prophecy cells.

### 7. Anneal `theory/` Evaluation Rubric (`T1`, `P1`–`P5`, `C1`–`C2`)

`Basis: source + derived`

| Dimension | First-Order `AffineOptic` + `PlaceSlotOptic` + `PathSeg` | Rank-2 Profunctor `Optic` (`Strong`/`Choice`) | Grounded Pass-1 Assessment (`TrustedBoundary.lean` & `Lean v4.34.1`) |
| :--- | :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | **Strong** | **Poor** | 100% `theory/` over `Init.*` today for tuples/pure models; minimal auditable `Trusted.*` extension needed for MIR ADTs, slices, and non-empty `CallerMemory`. Rank-2 optics bump `SymState` to `Type 1`. |
| **(P1) Human Spec Auditability** | **Strong** | **Weak** | Invisible in `CrateTheorem` / `Specs` under Statement-Origin Separation; specs use plain `Init.*` `Option`/`List` expressions without profunctor constraints. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | **Moderate** | Adding sibling fields or enum variants preserves existing `PathSeg` optics and `PathSeg.disjoint` proofs unchanged. |
| **(P3) Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **Strong** | **Poor** | Zero typeclasses, zero `._unsafe_rec` helpers, and $O(\text{depth})$ C++ `inductive_reduce_rec` steps (`<5 ms`), avoiding dictionary delta-unfolding in `whnf`. |
| **(P4) Heterogeneous Composability** | **Strong** | **Weak** | Composes safe `PermTree`, partial-init `PlaceSlotOptic`, `SpatialPin` slice freezing, unwind loan cleanup, and `(cur, fut)` prophecy writebacks at `unsafe` call boundaries. |
| **(P5) Failure Legibility** | **Strong** | **Weak** | Inactive variant, `.uninit` read, overlapping `sliceRange`, or mismatched `listSplice` length fails closed at the exact step instead of producing unsolved `Choice p` typeclass goals. |
| **(C1–C2) Conceptual Minimality** | **Strong** | **Weak** | Unifies `Lens`, `Prism.toAffineOptic`, `Option`/`Result`, and `sliceRangeOptic` into one `AffineOptic` carrier without needing `AnOptic`/`Stall`/`Market` clone boilerplate. |

#### Conceptual Minimality Counterexamples (`C1`–`C2`)

1. **`PlaceSlotOptic` cannot collapse into `LawfulAffineOptic`:** Enforcing `preview_none_set_none` on `SlotVal.tuple [.uninit, .uninit]` forces `set t 1 = none`, rejecting `t.0 = 1; t.1 = 2;` in safe Rust; conversely, dropping `preview_none_set_none` from `AffineOptic` lets ill-formed `Downcast` plans write to `Option::None` without `SetDiscriminant`.
2. **`Prism.review` cannot collapse into `AffineOptic`:** `AffineOptic.set` requires an existing `s` already matching the variant (`preview s = some _`); `SetDiscriminant` constructs a new active variant from `None`, requiring `review : A → S`.
3. **`LawfulSliceBack` cannot omit `sub.length = hi - lo`:** Without checking `sub.length == hi - lo`, splicing `sub = [99]` into `[0..2)` of `[10, 20, 30]` yields `[99, 30]`, whose `[0..2)` slice is `[99, 30] ≠ [99]`, violating `set_preview` and shifting sibling indices in `[2..3)`.

## Boundaries

- **End-to-end execution of `Downcast`, `Index`, `Subslice`, and `&mut` entry slices in `Trusted.MirSemantics` (`unsupported` on `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `Trusted.MirAst` currently maps non-fieldless ADTs, slices, `Downcast`, `Index`, and `Subslice` to `.unsupported` (`MirAst.lean:308–311, 469–475`), and `initState` rejects non-empty `q.callerMem.allocations` (`MirSemantics.lean:803–804`). End-to-end `CrateTheorem` discharge on Rust ADTs and slices requires extending `Trusted.*` and its `lean-miri` correspondence proofs.
- **Multi-focus `Wander` `Traversal`s (`known not to apply` to single `&mut` borrows):** `Traversal` (`Types.purs:106`, `OpticTypes.hs:55`) targets $0..N$ elements without pairwise address-disjointness guarantees; `slice::iter_mut()` should instead use inductive prefix/suffix `sliceRangeOptic` splits.
- **Predicate-filtered `unsafeFiltered` optics (`known not to apply`):** `unsafeFiltered p` (`OpticsAffineTraversal.hs:201–220`) violates `set_preview` whenever an update falsifies `p`; `Downcast` must key strictly on structural variant tags.
- **Symbolic index disjointness (`&mut xs[i]` vs `&mut xs[j]`, `not examined` in ground `Bool` tries):** `PathSeg.disjoint` decides concrete `Nat` indices by `rfl`; discharging symbolic `i ≠ j` or `hi₁ ≤ lo₂` requires propositional side-condition certificates (`not examined` here).
- **Niche-encoded multi-variant enum memory layouts (`unknown` pending `Trusted.MirAst` ADT layout design):** Whether `SetDiscriminant` in `Trusted.MirSemantics` will operate over algebraic `Val.adtVal` nodes or byte-level niche encodings (`Option<&T>`) is `unknown` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`.

## Evidence

1. **Anneal Pass-1 boundary and `PureLift` (`source`):** `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` — `trusted/lean/lean-toolchain:1`, `trusted/lean/foundation-lock.json:1–36`, `trusted/audit/TrustedBoundary.lean:442–596`, `trusted/lean/Trusted/MirAst.lean:312–321, 453–475`, `trusted/lean/Trusted/MirSemantics.lean:140–149, 550–557, 621–624, 803–804`, `theory/Anneal/PureLift/Lens.lean:39–225, 295–462`, `PermTree.lean:39–126`, `SpatialPin.lean:249–293`, and `MirBridge.lean:404–619`.
2. **Rust MIR and slice specifications (`normative` + `source`):** `rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd` — `compiler/rustc_middle/src/mir/syntax.rs:362–365, 1174–1255` and `library/core/src/slice/mod.rs:1997–2065`; `google/zerocopy` at `ec133ce4d7993775413d852f91c9e3eb2a2a0897`.
3. **Optics libraries and categorical papers (`source` + `documentation`):**
   - `purescript-contrib/purescript-profunctor-lenses` at `c479df47cc386b840c5e7238b4b5b1b3e9e2c4ff` (`src/Data/Lens/Types.purs:60–206`, `AffineTraversal.purs:23–52`, `Internal/Stall.purs:14–54`, `Prism.purs:40–123`, `Indexed.purs:20–50`, `docs/Impredicativity.md:1–151`).
   - `well-typed/optics` at `dd0b30e144ad92f77584dc8357c381eed2243028` (`optics-core/src/Optics/Internal/Optic.hs:51–147`, `Optic/Types.hs:16–60`, `AffineTraversal.hs:78–221`).
   - `optics-dev/Monocle` at `33bdd3fd63c8d30b778dfc68784e3c42bd2e9e05` (`core/shared/src/main/scala/monocle/law/OptionalLaws.scala:9–37`).
   - Pickering, Gibbons, and Wu (2017), `doi:10.22152/programming-journal.org/2017/1/7`, `arXiv:1703.10857`; Boisseau and Gibbons (ICFP 2018), `doi:10.1145/3236779`; Clarke et al. (*Compositionality* 2024), `doi:10.32408/compositionality-6-1`, `arXiv:2001.07488`.
4. **Aeneas slice backend and Lean 4 kernel (`source`):** `AeneasVerif/aeneas` at `d86aa34c75fd036ac139eb6e65da1cacc5492d0f` (`backends/lean/Aeneas/Std/SliceDef.lean:10–70`, `Slice.lean:728–798`, `tests/lean/Issue1138SlicePositivity.lean:23–40`); `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`src/kernel/type_checker.cpp:393–407, 555–602, 1171–1253`).

## Revalidation

1. **Diff Pass-1 boundary and `MirAst` projections:** Compare `trusted/audit/TrustedBoundary.lean`, `trusted/lean/foundation-lock.json`, and `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ProjectionElem`) against `c131b320eeeb26ef692e5afd5ec8db49ee518613`; verify any added `Downcast` or `Subslice` step fails closed on inactive variants and out-of-bounds ranges.
2. **Pass-1 compilation probe:** Compile the `Anneal.Optic` (`AffineOptic.comp`, `Prism.toAffineOptic`, `PlaceSlotOptic`, `sliceRangeOptic`, `PathSeg.disjoint`) definitions under `anneal-audit` (`-Ddebug.skipKernelTC=false`) importing only `Init.Core`, `Init.Data.List.Basic`, and `Init.Data.Nat.Basic`, confirming zero `._unsafe_rec` helpers and `rfl` reduction on concrete `split_at_mut` paths.
3. **Depth-overflow miss check:** Inspect `MirBridge.lean:404–422` (`setMirFieldAt`) if downstream lemmas assume `preview_none_set_none` on tuples exceeding `valDepthOk d`.
