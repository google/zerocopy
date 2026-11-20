/-
Toy.Lens.Classification
=======================

**F6 — classification of lawful puts for a fixed getter.**

Fix a getter `get : S → A`.  Which puts `put : S → A → S` make
`⟨get, put⟩` a very well-behaved lens, and what extra law singles one out?

* A put with `PutGet` is the same thing as a family of maps between the fibres
  of `get` (`ofPut`, `FiberMaps.toPut`).  Under this correspondence `GetPut`
  is \"the map from a fibre to itself is the identity\" and `PutPut` is \"maps
  compose\".  So very well-behaved puts correspond exactly to *coherent*
  families of fibre maps, and every map of a coherent family is a bijection.
* With a base view `a₀`, a coherent family is the same as a free choice of a
  bijection from the fibre over `a₀` to each other fibre; for `k` views and
  fibres of size `m` this gives `(m!)^(k-1)` very well-behaved puts.
* PutGet, GetPut and PutPut alone leave several choices (two for `fst` on
  `Bool × Bool`).  A frame law against a fixed complement view — a second view
  that together with `get` determines the state — singles out exactly one put.

Definitions, examples, supporting lemmas, all counterexamples and the F6 main
statements are proved.
-/
import Toy.Lens.Tightness

namespace Toy

namespace Lens

universe u v w

/-! ## Fibres of a bare getter and families of fibre maps -/

section Defs

variable {S : Type u} {A : Type v}

/-- The fibre of a getter `get : S → A` over a view `a`: the states in which
the field has the value `a`.  (For a lens `l`, `Fiber l a` is
`GetFiber l.get a`; see `fiber_eq_getFiber`.) -/
def GetFiber (get : S → A) (a : A) : Type u :=
  { s : S // get s = a }

/-- `Fiber` is the fibre of the lens's getter. -/
theorem fiber_eq_getFiber (l : Lens S A) (a₀ : A) : Fiber l a₀ = GetFiber l.get a₀ :=
  rfl

/-- Positive example for `GetFiber`: `(a, b)` lies in the fibre of the first
projection over `a`. -/
def getFiberFstMk {A : Type v} {B : Type w} (a : A) (b : B) :
    GetFiber (fun p : A × B => p.1) a :=
  ⟨(a, b), rfl⟩

/-- Negative example for `GetFiber`: the fibre of a constant getter over a
value it never takes is empty. -/
theorem getFiber_const_false_true_empty (x : GetFiber (fun _ : Bool => false) true) : False :=
  Bool.false_ne_true x.2

/--
A **family of fibre maps** for `get`: for every ordered pair of views `(a, a')`
a map from the fibre over `a` to the fibre over `a'`.

Meant to capture the raw data of a setter that really stores the written
value: \"where a write of `a'` sends a state whose field is `a`\".
-/
def FiberMaps (get : S → A) : Type (max u v) :=
  (a a' : A) → GetFiber get a → GetFiber get a'

/--
**Coherence** of a family of fibre maps: the map from a fibre to itself is the
identity, and maps compose (`φ a' a'' ∘ φ a a' = φ a a''`).

Meant to capture \"writing back the current value changes nothing\" and \"the
second write wins\" in terms of fibres.  A coherent family is a functor from
the category with one arrow between any two views to types; each of its maps
is a bijection (`FiberMaps.Coherent.leftInverse`).
-/
structure FiberMaps.Coherent {get : S → A} (φ : FiberMaps get) : Prop where
  /-- The map from a fibre to itself is the identity. -/
  map_self : ∀ a x, φ a a x = x
  /-- Maps compose. -/
  map_comp : ∀ a a' a'' x, φ a' a'' (φ a a' x) = φ a a'' x

/-- The put induced by a family of fibre maps: move a state `s` from its own
fibre (over `get s`) to the fibre over the written view. -/
def FiberMaps.toPut {get : S → A} (φ : FiberMaps get) : S → A → S :=
  fun s a => (φ (get s) a ⟨s, rfl⟩).1

/-- The family of fibre maps induced by a put satisfying `PutGet`:
`x ↦ put x a'` (it lands in the fibre over `a'` by `PutGet`). -/
def ofPut (get : S → A) (put : S → A → S) (h : (Lens.mk get put).PutGet) : FiberMaps get :=
  fun _ a' x => ⟨put x.1 a', h x.1 a'⟩

/-- Every family of fibre maps induces a put satisfying `PutGet` (no coherence
needed). -/
theorem toPut_putGet {get : S → A} (φ : FiberMaps get) : (Lens.mk get φ.toPut).PutGet :=
  fun s a => (φ (get s) a ⟨s, rfl⟩).2

/-- `toPut` undoes `ofPut`, by definition. -/
theorem toPut_ofPut (get : S → A) (put : S → A → S) (h : (Lens.mk get put).PutGet) :
    (ofPut get put h).toPut = put :=
  rfl

/-- In a coherent family, `φ a' a` is a left inverse of `φ a a'`; so every map
of a coherent family is a bijection, with inverse the map going back. -/
theorem FiberMaps.Coherent.leftInverse {get : S → A} {φ : FiberMaps get} (h : φ.Coherent)
    (a a' : A) (x : GetFiber get a) : φ a' a (φ a a' x) = x :=
  (h.map_comp a a' a x).trans (h.map_self a x)

end Defs

/-! ## Positive and negative examples for the definitions -/

/-- The first projection on `Bool × Bool`, as a bare getter. -/
abbrev getFst : Bool × Bool → Bool := fun p => p.1

/-- Positive example for `ofPut`, `FiberMaps` and `Coherent`: the fibre maps of
`fst` (keep the second field) are coherent. -/
theorem ofPut_fst_coherent : (ofPut getFst fstB.put (fun _ _ => rfl)).Coherent := by
  constructor
  · intro a ⟨⟨x, y⟩, hx⟩
    apply Subtype.ext
    show (a, y) = (x, y)
    rw [show x = a from hx]
  · intro _ _ _ _
    rfl

/-- Positive example for `Coherent` that is unintended: the fibre maps of the
state-twisting lens are coherent too. -/
theorem ofPut_twist_coherent : (ofPut getFst twist.put twist_veryWellBehaved.2.1).Coherent := by
  constructor
  · intro a ⟨⟨x, y⟩, hx⟩
    apply Subtype.ext
    have hx' : x = a := hx
    subst hx'
    exact twist_veryWellBehaved.1 (x, y)
  · intro a a' a'' ⟨⟨x, y⟩, hx⟩
    apply Subtype.ext
    exact twist_veryWellBehaved.2.2 (x, y) a' a''

/-- Negative example for `Coherent` (fails `map_self`): the fibre maps of the
sibling-resetting setter. -/
theorem ofPut_resetSibling_not_coherent :
    ¬ (ofPut getFst resetSibling.put resetSibling_putGet).Coherent := by
  intro h
  have := congrArg Subtype.val (h.map_self false ⟨(false, true), rfl⟩)
  exact absurd this (by decide)

/-- Negative example for `Coherent` (fails `map_comp`): the fibre maps of the
dirty-flag setter. -/
theorem ofPut_dirtyFlag_not_coherent :
    ¬ (ofPut getFst dirtyFlag.put dirtyFlag_putGet).Coherent := by
  intro h
  have := congrArg Subtype.val (h.map_comp false true false ⟨(false, false), rfl⟩)
  exact absurd this (by decide)

/-- Negative example for `FiberMaps`: if one fibre is empty and another is
not, there is no family of fibre maps at all. -/
theorem fiberMaps_empty_of_empty_fiber {S : Type u} {A : Type v} {get : S → A} {a a' : A}
    (hempty : GetFiber get a → False) (x : GetFiber get a') : FiberMaps get → False :=
  fun φ => hempty (φ a' a x)

/-- Positive example for `toPut`: the fibre maps of `fst` induce `fst.put`. -/
theorem toPut_ofPut_fst : (ofPut getFst fstB.put (fun _ _ => rfl)).toPut = fstB.put :=
  rfl

/-- Negative example for `toPut` being lawful without coherence: the
non-coherent fibre maps of `dirtyFlag` induce a put that is not very
well-behaved. -/
theorem toPut_ofPut_dirtyFlag_not_veryWellBehaved :
    ¬ (Lens.mk getFst (ofPut getFst dirtyFlag.put dirtyFlag_putGet).toPut).VeryWellBehaved :=
  fun h => absurd (h.2.2 (false, false) true false) (by decide)

/-! ## Empty fibres and non-surjective getters (proved) -/

section Degenerate

variable {S : Type u} {A : Type v}

/-- **A put with `PutGet` forces `get` to be surjective** as soon as `S` is
inhabited.  So for a non-surjective getter on an inhabited state type there is
no very well-behaved put at all. -/
theorem surjective_of_putGet_of_nonempty (get : S → A) (put : S → A → S)
    (h : (Lens.mk get put).PutGet) (hS : Nonempty S) : Function.Surjective get :=
  fun a => match hS with | ⟨s⟩ => ⟨put s a, h s a⟩

/-- **On an empty state type there is exactly one put, and it is very
well-behaved**, whatever `A` is (empty or not, `get` surjective or not). -/
theorem veryWellBehaved_put_unique_of_isEmpty (get : S → A) (hS : S → False) :
    (∀ put : S → A → S, (Lens.mk get put).VeryWellBehaved) ∧
    (∀ put put' : S → A → S, put = put') :=
  ⟨fun _ => ⟨fun s => (hS s).elim, fun s => (hS s).elim, fun s => (hS s).elim⟩,
   fun _ _ => funext fun s => (hS s).elim⟩

end Degenerate

/-! ## F6 — main statements -/

section Main

variable {S : Type u} {A : Type v}

/--
**F6 (classification of very well-behaved puts for a fixed getter).**  Fix
`get : S → A`.

1. Every coherent family of fibre maps induces, by `toPut`, a very
   well-behaved put for `get`.
2. Every very well-behaved put for `get` induces, by `ofPut`, a coherent
   family of fibre maps.
3. `ofPut` undoes `toPut` on *every* family of fibre maps (and `toPut` undoes
   `ofPut` by definition, `toPut_ofPut`).

Hence `toPut` is a bijection from coherent families of fibre maps onto very
well-behaved puts for `get`, with inverse `ofPut`.  No inhabitedness or
surjectivity assumption is made; for those cases see
`surjective_of_putGet_of_nonempty` and `veryWellBehaved_put_unique_of_isEmpty`.
-/
theorem coherent_fiberMaps_correspond_veryWellBehaved_puts (get : S → A) :
    (∀ φ : FiberMaps get, φ.Coherent → (Lens.mk get φ.toPut).VeryWellBehaved) ∧
    (∀ (put : S → A → S) (h : (Lens.mk get put).VeryWellBehaved),
      (ofPut get put h.2.1).Coherent) ∧
    (∀ φ : FiberMaps get, ofPut get φ.toPut (toPut_putGet φ) = φ) := by
  -- `ofPut` undoes `toPut`: a fibre element `⟨s, hs⟩` over `a` has `a = get s`
  have hret : ∀ φ : FiberMaps get, ofPut get φ.toPut (toPut_putGet φ) = φ := by
    intro φ
    funext a a' x
    rcases x with ⟨s, hs⟩
    subst hs
    rfl
  -- law-by-law reading of `GetPut` and `PutPut` for a put with `PutGet`
  have hll : ∀ (put : S → A → S) (h : (Lens.mk get put).PutGet),
      ((Lens.mk get put).GetPut ↔ ∀ a x, ofPut get put h a a x = x) ∧
      ((Lens.mk get put).PutPut ↔
        ∀ a a' a'' x, ofPut get put h a' a'' (ofPut get put h a a' x) = ofPut get put h a a'' x) := by
    intro put h
    refine ⟨⟨fun hgp a x => ?_, fun hid s => ?_⟩, ⟨fun hpp a a' a'' x => ?_, fun hcomp s a' a'' => ?_⟩⟩
    · rcases x with ⟨s, hs⟩
      apply Subtype.ext
      show put s a = s
      rw [← hs]
      exact hgp s
    · exact congrArg Subtype.val (hid (get s) ⟨s, rfl⟩)
    · exact Subtype.ext (hpp x.1 a' a'')
    · exact congrArg Subtype.val (hcomp (get s) a' a'' ⟨s, rfl⟩)
  refine ⟨?_, ?_, hret⟩
  · intro φ hcoh
    have hpg : (Lens.mk get φ.toPut).PutGet := toPut_putGet φ
    have h := hll φ.toPut hpg
    rw [hret φ] at h
    exact ⟨h.1.mpr hcoh.map_self, hpg, h.2.mpr hcoh.map_comp⟩
  · intro put hvwb
    have h := hll put hvwb.2.1
    exact ⟨h.1.mp hvwb.1, h.2.mp hvwb.2.2⟩

/--
**F6, law by law.**  For a put satisfying `PutGet`, `GetPut` holds exactly
when the induced map from each fibre to itself is the identity, and `PutPut`
holds exactly when the induced maps compose.  (So well-behaved puts
correspond to families whose diagonal maps are identities.)
-/
theorem getPut_iff_ofPut_map_self_and_putPut_iff_ofPut_map_comp (get : S → A)
    (put : S → A → S) (h : (Lens.mk get put).PutGet) :
    ((Lens.mk get put).GetPut ↔ ∀ a x, ofPut get put h a a x = x) ∧
    ((Lens.mk get put).PutPut ↔
      ∀ a a' a'' x, ofPut get put h a' a'' (ofPut get put h a a' x) = ofPut get put h a a'' x) := by
  refine ⟨⟨fun hgp a x => ?_, fun hid s => ?_⟩, ⟨fun hpp a a' a'' x => ?_, fun hcomp s a' a'' => ?_⟩⟩
  · rcases x with ⟨s, hs⟩
    apply Subtype.ext
    show put s a = s
    rw [← hs]
    exact hgp s
  · exact congrArg Subtype.val (hid (get s) ⟨s, rfl⟩)
  · exact Subtype.ext (hpp x.1 a' a'')
  · exact congrArg Subtype.val (hcomp (get s) a' a'' ⟨s, rfl⟩)

/-- Two bundled bijections with the same forward map are equal (the inverse
map is then determined). -/
theorem Equiv.ext_of_toFun_eq {α : Type u} {β : Type v} {e₁ e₂ : Equiv α β}
    (h : e₁.toFun = e₂.toFun) : e₁ = e₂ := by
  have hinv : e₁.invFun = e₂.invFun := by
    funext b
    apply e₂.injective
    rw [e₂.right_inv, ← h, e₁.right_inv]
  cases e₁
  cases e₂
  simp only at h hinv
  subst h
  subst hinv
  rfl

/--
**F6, base-fibre form.**  Fix a base view `a₀`.  Very well-behaved puts for
`get` correspond bijectively to families of bijections from the fibre over
`a₀` to each *other* fibre; the correspondence sends `put` to the family
`x ↦ put x a`.
-/
theorem veryWellBehaved_puts_equiv_baseFiber_bijections (get : S → A) (a₀ : A) :
    ∃ e : Equiv {put : S → A → S // (Lens.mk get put).VeryWellBehaved}
        ((a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1)),
      ∀ p a x, (((e.toFun p) a).toFun x).1 = p.1 x.1 a.1 := by
  letI : DecidableEq A := fun x y => Classical.propDecidable (x = y)
  have hcorr := coherent_fiberMaps_correspond_veryWellBehaved_puts get
  -- forward: a very well-behaved put gives the bijections `φ a₀ a` with inverses `φ a a₀`
  let toFam : {put : S → A → S // (Lens.mk get put).VeryWellBehaved} →
      ((a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1)) :=
    fun ⟨put, hvwb⟩ a =>
      let φ := ofPut get put hvwb.2.1
      have hcoh : φ.Coherent := hcorr.2.1 put hvwb
      { toFun := φ a₀ a.1
        invFun := φ a.1 a₀
        left_inv := hcoh.leftInverse a₀ a.1
        right_inv := hcoh.leftInverse a.1 a₀ }
  -- backward: route every move through the base fibre
  let toBase (ψ : (a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1))
      (a : A) : GetFiber get a → GetFiber get a₀ :=
    if ha : a = a₀ then fun y => ha ▸ y else (ψ ⟨a, ha⟩).invFun
  let fromBase (ψ : (a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1))
      (a' : A) : GetFiber get a₀ → GetFiber get a' :=
    if ha' : a' = a₀ then fun z => ha' ▸ z else (ψ ⟨a', ha'⟩).toFun
  let ofFamFiber (ψ : (a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1)) :
      FiberMaps get :=
    fun a a' x => fromBase ψ a' (toBase ψ a x)
  have to_from_base : ∀ ψ a x, fromBase ψ a (toBase ψ a x) = x := by
    intro ψ a x
    dsimp only [toBase, fromBase]
    split
    · next ha => subst ha; rfl
    · next ha => exact (ψ ⟨a, ha⟩).right_inv x
  have from_to_base : ∀ ψ a z, toBase ψ a (fromBase ψ a z) = z := by
    intro ψ a z
    dsimp only [toBase, fromBase]
    split
    · next ha => subst ha; rfl
    · next ha => exact (ψ ⟨a, ha⟩).left_inv z
  have ofFam_coherent : ∀ ψ, (ofFamFiber ψ).Coherent :=
    fun ψ => ⟨to_from_base ψ, fun a a' a'' x => by
      show fromBase ψ a'' (toBase ψ a' (fromBase ψ a' (toBase ψ a x))) =
        fromBase ψ a'' (toBase ψ a x)
      rw [from_to_base]⟩
  let ofFam : ((a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1)) →
      {put : S → A → S // (Lens.mk get put).VeryWellBehaved} :=
    fun ψ => ⟨(ofFamFiber ψ).toPut, hcorr.1 (ofFamFiber ψ) (ofFam_coherent ψ)⟩
  refine ⟨{ toFun := toFam, invFun := ofFam, left_inv := ?_, right_inv := ?_ },
    fun _ _ _ => rfl⟩
  · intro ⟨put, hvwb⟩
    apply Subtype.ext
    funext s a'
    let φ := ofPut get put hvwb.2.1
    have hcoh : φ.Coherent := hcorr.2.1 put hvwb
    show (fromBase (toFam ⟨put, hvwb⟩) a' (toBase (toFam ⟨put, hvwb⟩) (get s) ⟨s, rfl⟩)).1 =
      put s a'
    dsimp only [fromBase, toBase, toFam]
    split
    · next hs =>
      split
      · next ha' =>
        subst ha'
        cases hs
        exact (hvwb.1 s).symm
      · next ha' =>
        cases hs
        rfl
    · next hs =>
      split
      · next ha' =>
        subst ha'
        rfl
      · next ha' =>
        exact congrArg Subtype.val (hcoh.map_comp (get s) a₀ a' ⟨s, rfl⟩)
  · intro ψ
    funext ⟨a, ha⟩
    apply Equiv.ext_of_toFun_eq
    funext x
    apply Subtype.ext
    show (fromBase ψ a (toBase ψ (get x.1) ⟨x.1, rfl⟩)).1 = ((ψ ⟨a, ha⟩).toFun x).1
    rcases x with ⟨s, hs⟩
    subst hs
    dsimp only [fromBase, toBase]
    split
    · next h1 => exact absurd h1 ha
    · next h1 =>
      split
      · rfl
      · next h2 => exact absurd rfl h2

end Main

/-- The factorial function (core Lean has none). -/
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- Positive example for `factorial`. -/
theorem factorial_three : factorial 3 = 6 :=
  rfl

/-- Negative example for `factorial`: it is never zero. -/
theorem factorial_pos : ∀ n, 0 < factorial n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (factorial_pos n)

section Count

/-! ### Finite combinatorics used in the proof of the counting form

These definitions are used only inside the proof of
`card_veryWellBehaved_puts_of_card_views_card_fibers`. -/

/-- Composition of bundled bijections. -/
def equivTrans {α : Type u} {β : Type v} {γ : Type w}
    (e₁ : Equiv α β) (e₂ : Equiv β γ) : Equiv α γ where
  toFun a := e₂.toFun (e₁.toFun a)
  invFun c := e₁.invFun (e₂.invFun c)
  left_inv a := by rw [e₂.left_inv, e₁.left_inv]
  right_inv c := by rw [e₁.right_inv, e₂.right_inv]

/-- Inverse of a bundled bijection. -/
def equivSymm {α : Type u} {β : Type v} (e : Equiv α β) : Equiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

/-- `Fin a × Fin b ≃ Fin (a * b)` (row-major), for `0 < b`. -/
def finProdEquiv (a b : Nat) (hb : 0 < b) : Equiv (Fin a × Fin b) (Fin (a * b)) where
  toFun p := ⟨p.1.1 * b + p.2.1, by
    have h1 : p.1.1 + 1 ≤ a := p.1.2
    have h2 : (p.1.1 + 1) * b ≤ a * b := Nat.mul_le_mul_right b h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    have hj : p.2.1 < b := p.2.2
    omega⟩
  invFun n := (⟨n.1 / b, (Nat.div_lt_iff_lt_mul hb).mpr n.2⟩,
    ⟨n.1 % b, Nat.mod_lt n.1 hb⟩)
  left_inv := by
    intro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    apply Prod.ext
    · apply Fin.ext
      dsimp only
      have h1 : (i * b + j) / b = i + j / b := by
        rw [Nat.add_comm (i * b) j, Nat.mul_comm i b, Nat.add_mul_div_left j i hb, Nat.add_comm]
      rw [h1, Nat.div_eq_of_lt hj, Nat.add_zero]
    · apply Fin.ext
      dsimp only
      rw [Nat.add_comm (i * b) j, Nat.mul_comm i b, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  right_inv := by
    intro ⟨n, hn⟩
    apply Fin.ext
    dsimp only
    rw [Nat.mul_comm (n / b) b]
    exact Nat.div_add_mod n b

/-- The order embedding `Fin m → Fin (m + 1)` that skips `p`. -/
def finSuccAbove {m : Nat} (p : Fin (m + 1)) (i : Fin m) : Fin (m + 1) :=
  if i.1 < p.1 then ⟨i.1, by omega⟩ else ⟨i.1 + 1, by omega⟩

theorem finSuccAbove_ne {m : Nat} (p : Fin (m + 1)) (i : Fin m) :
    finSuccAbove p i ≠ p := by
  dsimp only [finSuccAbove]
  split <;> (intro h; have := congrArg Fin.val h; dsimp at this; omega)

/-- The inverse of `finSuccAbove p` on its range. -/
def finPredAbove {m : Nat} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p) : Fin m :=
  if h : x.1 < p.1 then ⟨x.1, by omega⟩
  else ⟨x.1 - 1, by
    have hne : x.1 ≠ p.1 := fun he => hx (Fin.ext he)
    omega⟩

theorem finSuccAbove_predAbove {m : Nat} (p : Fin (m + 1)) (x : Fin (m + 1)) (hx : x ≠ p) :
    finSuccAbove p (finPredAbove p x hx) = x := by
  have hne : x.1 ≠ p.1 := fun he => hx (Fin.ext he)
  apply Fin.ext
  dsimp only [finSuccAbove, finPredAbove]
  by_cases hlt : x.1 < p.1
  · simp [hlt]
  · have hlt2 : ¬ (x.1 - 1 < p.1) := by omega
    simp [hlt, hlt2]
    omega

theorem finPredAbove_succAbove {m : Nat} (p : Fin (m + 1)) (i : Fin m) :
    finPredAbove p (finSuccAbove p i) (finSuccAbove_ne p i) = i := by
  apply Fin.ext
  dsimp only [finSuccAbove, finPredAbove]
  by_cases hlt : i.1 < p.1
  · simp [hlt]
  · have hlt2 : ¬ (i.1 + 1 < p.1) := by omega
    simp [hlt, hlt2]

/-- Forward map of the permutation of `Fin (m + 1)` sending `0 ↦ p` and acting
by `σ` on the rest. -/
def permInsertFwd {m : Nat} (p : Fin (m + 1)) (σ : Equiv (Fin m) (Fin m)) (x : Fin (m + 1)) :
    Fin (m + 1) :=
  if hx : x.1 = 0 then p
  else finSuccAbove p (σ.toFun ⟨x.1 - 1, by omega⟩)

/-- Inverse map of `permInsertFwd p σ`. -/
def permInsertInv {m : Nat} (p : Fin (m + 1)) (σ : Equiv (Fin m) (Fin m)) (y : Fin (m + 1)) :
    Fin (m + 1) :=
  if hy : y = p then ⟨0, Nat.succ_pos m⟩
  else ⟨(σ.invFun (finPredAbove p y hy)).1 + 1, by omega⟩

theorem permInsert_left_inv {m : Nat} (p : Fin (m + 1)) (σ : Equiv (Fin m) (Fin m))
    (x : Fin (m + 1)) : permInsertInv p σ (permInsertFwd p σ x) = x := by
  dsimp only [permInsertFwd, permInsertInv]
  by_cases hx : x.1 = 0
  · simp [hx]; apply Fin.ext; dsimp; omega
  · simp only [hx, ↓reduceDIte]
    have hne : finSuccAbove p (σ.toFun ⟨x.1 - 1, by omega⟩) ≠ p := finSuccAbove_ne p _
    simp only [hne, ↓reduceDIte]
    apply Fin.ext; dsimp only
    rw [finPredAbove_succAbove, σ.left_inv]
    dsimp; omega

theorem permInsert_right_inv {m : Nat} (p : Fin (m + 1)) (σ : Equiv (Fin m) (Fin m))
    (y : Fin (m + 1)) : permInsertFwd p σ (permInsertInv p σ y) = y := by
  dsimp only [permInsertFwd, permInsertInv]
  by_cases hy : y = p
  · subst hy; simp
  · simp only [hy, ↓reduceDIte]
    have hnz : ¬ ((σ.invFun (finPredAbove p y hy)).1 + 1 = 0) := by omega
    simp only [hnz, ↓reduceDIte]
    have hidx : (⟨(σ.invFun (finPredAbove p y hy)).1 + 1 - 1, by omega⟩ : Fin m) =
        σ.invFun (finPredAbove p y hy) :=
      Fin.ext rfl
    rw [hidx, σ.right_inv, finSuccAbove_predAbove]

/-- Permutations of `Fin (m + 1)` are pairs (image of `0`, permutation of
`Fin m`). -/
def finSuccPermSplit (m : Nat) :
    Equiv (Equiv (Fin (m + 1)) (Fin (m + 1))) (Fin (m + 1) × Equiv (Fin m) (Fin m)) where
  toFun e :=
    let p := e.toFun ⟨0, Nat.succ_pos m⟩
    have hne : ∀ i : Fin m, e.toFun ⟨i.1 + 1, by omega⟩ ≠ p := by
      intro i heq
      have := e.injective heq
      have := congrArg Fin.val this; dsimp at this; omega
    have hne_inv : ∀ j : Fin m, e.invFun (finSuccAbove p j) ≠ ⟨0, Nat.succ_pos m⟩ := by
      intro j heq
      have h1 := congrArg e.toFun heq
      rw [e.right_inv] at h1
      exact finSuccAbove_ne p j h1
    (p,
     { toFun := fun i => finPredAbove p (e.toFun ⟨i.1 + 1, by omega⟩) (hne i)
       invFun := fun j =>
         ⟨(e.invFun (finSuccAbove p j)).1 - 1, by
           have h0 : (e.invFun (finSuccAbove p j)).1 ≠ 0 :=
             fun h => hne_inv j (Fin.ext h)
           have hlt := (e.invFun (finSuccAbove p j)).2
           omega⟩
       left_inv := fun i => by
         apply Fin.ext; dsimp only
         rw [finSuccAbove_predAbove, e.left_inv]
         rfl
       right_inv := fun j => by
         have h0 : (e.invFun (finSuccAbove p j)).1 ≠ 0 :=
           fun h => hne_inv j (Fin.ext h)
         have heq : (⟨(e.invFun (finSuccAbove p j)).1 - 1 + 1, by
             have := (e.invFun (finSuccAbove p j)).2; omega⟩ : Fin (m + 1)) =
             e.invFun (finSuccAbove p j) := by
           apply Fin.ext; dsimp; omega
         dsimp only
         have hsub : ∀ (x : Fin (m + 1)) (hx : x ≠ p),
             e.toFun ⟨(e.invFun (finSuccAbove p j)).1 - 1 + 1, by
               have := (e.invFun (finSuccAbove p j)).2; omega⟩ = x →
             finPredAbove p x hx = j := by
           intro x hx htx
           rw [heq, e.right_inv] at htx
           subst htx
           exact finPredAbove_succAbove p j
         exact hsub _ _ rfl })
  invFun := fun ⟨p, σ⟩ =>
    { toFun := permInsertFwd p σ
      invFun := permInsertInv p σ
      left_inv := permInsert_left_inv p σ
      right_inv := permInsert_right_inv p σ }
  left_inv := fun e => by
    apply Equiv.ext_of_toFun_eq
    funext ⟨xv, xlt⟩
    dsimp only [permInsertFwd]
    by_cases hx : xv = 0
    · subst hx; simp
    · simp only [hx, ↓reduceDIte]
      have hsub : (⟨xv - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨xv, xlt⟩ := by
        apply Fin.ext; dsimp; omega
      exact (finSuccAbove_predAbove _ _ _).trans (congrArg e.toFun hsub)
  right_inv := fun ⟨p, σ⟩ => by
    apply Prod.ext
    · dsimp only [permInsertFwd]; simp
    · apply Equiv.ext_of_toFun_eq
      funext i
      dsimp only [permInsertFwd]
      have hsub : ∀ (z : Fin (m + 1)) (hz : z ≠ p),
          z = finSuccAbove p (σ.toFun i) →
          finPredAbove p z hz = σ.toFun i := by
        intro z hz hzeq
        subst hzeq
        exact finPredAbove_succAbove p (σ.toFun i)
      refine hsub _ _ ?_
      simp

/-- There are `m!` permutations of `Fin m`. -/
def equivPermFin : (m : Nat) → Equiv (Equiv (Fin m) (Fin m)) (Fin (factorial m))
  | 0 =>
    { toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      invFun := fun _ => Equiv.refl (Fin 0)
      left_inv := fun _ => Equiv.ext_of_toFun_eq (funext fun i => i.elim0)
      right_inv := fun ⟨i, hi⟩ => by
        have hi' : i < 1 := hi
        exact Fin.ext (by show 0 = i; omega) }
  | m + 1 =>
    let e1 := finSuccPermSplit m
    let ih := equivPermFin m
    let e2 : Equiv (Fin (m + 1) × Equiv (Fin m) (Fin m)) (Fin (m + 1) × Fin (factorial m)) :=
      { toFun := fun p => (p.1, ih.toFun p.2)
        invFun := fun q => (q.1, ih.invFun q.2)
        left_inv := fun p => Prod.ext rfl (ih.left_inv p.2)
        right_inv := fun q => Prod.ext rfl (ih.right_inv q.2) }
    equivTrans e1 (equivTrans e2 (finProdEquiv (m + 1) (factorial m) (factorial_pos m)))

/-- There are `d ^ n` functions `Fin n → Fin d` (for `0 < d`). -/
def finFunEquivPow (d : Nat) (hd : 0 < d) : (n : Nat) → Equiv (Fin n → Fin d) (Fin (d ^ n))
  | 0 =>
    { toFun := fun _ => ⟨0, Nat.zero_lt_one⟩
      invFun := fun _ i => i.elim0
      left_inv := fun _ => funext fun i => i.elim0
      right_inv := fun ⟨i, hi⟩ => by
        have hi' : i < 1 := hi
        exact Fin.ext (by show 0 = i; omega) }
  | n + 1 =>
    let ih := finFunEquivPow d hd n
    let splitFun : Equiv (Fin (n + 1) → Fin d) (Fin (d ^ n) × Fin d) :=
      { toFun := fun f => (ih.toFun (fun i => f ⟨i.1, by omega⟩), f ⟨n, by omega⟩)
        invFun := fun ⟨q, last⟩ j =>
          if hj : j.1 < n then ih.invFun q ⟨j.1, hj⟩ else last
        left_inv := fun f => by
          funext ⟨j, hj⟩
          dsimp only
          split
          · next hjn =>
            have hrew := congrFun (ih.left_inv (fun i : Fin n => f ⟨i.1, by omega⟩)) ⟨j, hjn⟩
            exact hrew
          · next hjn =>
            congr 1; apply Fin.ext; dsimp; omega
        right_inv := fun ⟨q, last⟩ => by
          apply Prod.ext
          · dsimp only
            have hfun : (fun i : Fin n =>
                if hj : i.1 < n then ih.invFun q ⟨i.1, hj⟩ else last) = ih.invFun q := by
              funext i
              split
              · rfl
              · next h => exact absurd i.2 h
            rw [hfun, ih.right_inv]
          · dsimp only
            split
            · next h => exact absurd h (Nat.lt_irrefl n)
            · rfl }
    equivTrans splitFun (finProdEquiv (d ^ n) d hd)

variable {S : Type u} {A : Type v}

/--
**F6, counting.**  If the view type has exactly `k` elements and every fibre of
`get` has exactly `m` elements, then the very well-behaved puts for `get` are
in bijection with `Fin (k - 1) → Equiv (Fin m) (Fin m)` (a self-bijection of an
`m`-element set for each view other than a base view), and there are exactly
`(m!)^(k - 1)` of them.  (With truncated subtraction both forms also cover
`k = 0`, where `S` is empty and there is exactly one put.)
-/
theorem card_veryWellBehaved_puts_of_card_views_card_fibers (get : S → A) (k m : Nat)
    (hA : Nonempty (Equiv A (Fin k))) (hF : ∀ a, Nonempty (Equiv (GetFiber get a) (Fin m))) :
    Nonempty (Equiv {put : S → A → S // (Lens.mk get put).VeryWellBehaved}
      (Fin (k - 1) → Equiv (Fin m) (Fin m))) ∧
    Nonempty (Equiv {put : S → A → S // (Lens.mk get put).VeryWellBehaved}
      (Fin (factorial m ^ (k - 1)))) := by
  obtain ⟨eA⟩ := hA
  have eFirst : Nonempty (Equiv {put : S → A → S // (Lens.mk get put).VeryWellBehaved}
      (Fin (k - 1) → Equiv (Fin m) (Fin m))) := by
    cases k with
    | zero =>
      -- no views: `S` is empty and there is exactly one put
      have hS : S → False := fun s => (eA.toFun (get s)).elim0
      have hemp := veryWellBehaved_put_unique_of_isEmpty get hS
      let p₀ : {put : S → A → S // (Lens.mk get put).VeryWellBehaved} :=
        ⟨fun s => (hS s).elim, hemp.1 _⟩
      exact ⟨{
        toFun := fun _ i => i.elim0
        invFun := fun _ => p₀
        left_inv := fun _ => Subtype.ext (hemp.2 _ _)
        right_inv := fun _ => funext fun i => i.elim0
      }⟩
    | succ k' =>
      -- base view `a₀`; transport the base-fibre form along the counting bijections
      let a₀ : A := eA.invFun ⟨0, Nat.succ_pos k'⟩
      obtain ⟨eBase, _⟩ := veryWellBehaved_puts_equiv_baseFiber_bijections get a₀
      let eFib : (a : A) → Equiv (GetFiber get a) (Fin m) := fun a => Classical.choice (hF a)
      let conjFib (a : A) : Equiv (Equiv (GetFiber get a₀) (GetFiber get a))
          (Equiv (Fin m) (Fin m)) :=
        { toFun := fun g => equivTrans (equivSymm (eFib a₀)) (equivTrans g (eFib a))
          invFun := fun h => equivTrans (eFib a₀) (equivTrans h (equivSymm (eFib a)))
          left_inv := fun g => Equiv.ext_of_toFun_eq (funext fun x => by
            show (eFib a).invFun ((eFib a).toFun (g.toFun ((eFib a₀).invFun ((eFib a₀).toFun x)))) =
              g.toFun x
            rw [(eFib a₀).left_inv, (eFib a).left_inv])
          right_inv := fun h => Equiv.ext_of_toFun_eq (funext fun i => by
            show (eFib a).toFun ((eFib a).invFun (h.toFun ((eFib a₀).toFun ((eFib a₀).invFun i)))) =
              h.toFun i
            rw [(eFib a₀).right_inv, (eFib a).right_inv]) }
      let idxEquiv : Equiv {a : A // a ≠ a₀} (Fin k') :=
        { toFun := fun ⟨a, ha⟩ =>
            ⟨(eA.toFun a).1 - 1, by
              have h0 : (eA.toFun a).1 ≠ 0 := by
                intro hz
                apply ha
                have : eA.toFun a = ⟨0, Nat.succ_pos k'⟩ := Fin.ext hz
                have := congrArg eA.invFun this
                rwa [eA.left_inv] at this
              have := (eA.toFun a).2
              omega⟩
          invFun := fun i =>
            ⟨eA.invFun ⟨i.1 + 1, by omega⟩, by
              intro h
              have := congrArg eA.toFun h
              rw [eA.right_inv, eA.right_inv] at this
              have := congrArg Fin.val this; dsimp at this; omega⟩
          left_inv := fun ⟨a, ha⟩ => by
            apply Subtype.ext; dsimp only
            have h0 : (eA.toFun a).1 ≠ 0 := by
              intro hz
              apply ha
              have : eA.toFun a = ⟨0, Nat.succ_pos k'⟩ := Fin.ext hz
              have := congrArg eA.invFun this
              rwa [eA.left_inv] at this
            have hf : (⟨(eA.toFun a).1 - 1 + 1, by have := (eA.toFun a).2; omega⟩ : Fin (k' + 1)) =
                eA.toFun a := by
              apply Fin.ext; dsimp; omega
            rw [hf, eA.left_inv]
          right_inv := fun i => by
            apply Fin.ext; dsimp only
            rw [eA.right_inv]
            rfl }
      let domEquiv : Equiv ((a : {a : A // a ≠ a₀}) → Equiv (GetFiber get a₀) (GetFiber get a.1))
          (Fin k' → Equiv (Fin m) (Fin m)) :=
        { toFun := fun ψ i => (conjFib (idxEquiv.invFun i).1).toFun (ψ (idxEquiv.invFun i))
          invFun := fun χ a => (conjFib a.1).invFun (χ (idxEquiv.toFun a))
          left_inv := fun ψ => funext fun a => by
            have hsub : ∀ b : {a : A // a ≠ a₀}, b = idxEquiv.invFun (idxEquiv.toFun a) →
                (conjFib a.1).invFun ((conjFib b.1).toFun (ψ b)) = ψ a := by
              intro b hb
              have hab : b = a := hb.trans (idxEquiv.left_inv a)
              subst hab
              exact (conjFib b.1).left_inv (ψ b)
            exact hsub _ rfl
          right_inv := fun χ => funext fun i => by
            show (conjFib (idxEquiv.invFun i).1).toFun
              ((conjFib (idxEquiv.invFun i).1).invFun (χ (idxEquiv.toFun (idxEquiv.invFun i)))) = χ i
            rw [idxEquiv.right_inv, (conjFib (idxEquiv.invFun i).1).right_inv] }
      exact ⟨equivTrans eBase domEquiv⟩
  obtain ⟨e₁⟩ := eFirst
  let ep := equivPermFin m
  let mapPerm : Equiv (Fin (k - 1) → Equiv (Fin m) (Fin m)) (Fin (k - 1) → Fin (factorial m)) :=
    { toFun := fun f i => ep.toFun (f i)
      invFun := fun g i => ep.invFun (g i)
      left_inv := fun f => funext fun i => ep.left_inv (f i)
      right_inv := fun g => funext fun i => ep.right_inv (g i) }
  exact ⟨⟨e₁⟩, ⟨equivTrans e₁ (equivTrans mapPerm
    (finFunEquivPow (factorial m) (factorial_pos m) (k - 1)))⟩⟩

end Count

/-! ## F6 — which extra law singles out a unique put -/

section Unique

variable {S : Type u} {A : Type v} {C : Type w}

/--
**F6, uniqueness under a frame law against a complement view.**  Fix
`get : S → A` and a second lens `m : Lens S C` whose view, together with
`get`, determines the state (`hext`) and such that every pair of values is
realised (`hsurj`).  Then:

1. there is a put that satisfies `PutGet` and leaves the `m`-view unchanged
   (`PutIndep (Lens.mk get put) m`);
2. any two such puts are equal;
3. such a put is very well-behaved.

So a frame law against a fixed complement view singles out exactly one lawful
put.  Only `m.get` matters; `m.put` is not used.
-/
theorem existsUnique_put_putGet_putIndep_of_jointExt_surjective (get : S → A) (m : Lens S C)
    (hext : ∀ s t, get s = get t → m.get s = m.get t → s = t)
    (hsurj : ∀ a c, ∃ s, get s = a ∧ m.get s = c) :
    (∃ put : S → A → S, (Lens.mk get put).PutGet ∧ PutIndep (Lens.mk get put) m) ∧
    (∀ put put' : S → A → S,
      (Lens.mk get put).PutGet → PutIndep (Lens.mk get put) m →
      (Lens.mk get put').PutGet → PutIndep (Lens.mk get put') m → put = put') ∧
    (∀ put : S → A → S, (Lens.mk get put).PutGet → PutIndep (Lens.mk get put) m →
      (Lens.mk get put).VeryWellBehaved) := by
  refine ⟨?_, ?_, ?_⟩
  · -- existence: pick a state realising `(a, m.get s)`
    refine ⟨fun s a => Classical.choose (hsurj a (m.get s)),
      fun s a => (Classical.choose_spec (hsurj a (m.get s))).1,
      fun s a => (Classical.choose_spec (hsurj a (m.get s))).2⟩
  · -- uniqueness: both results have the same `get` and the same `m.get`
    intro put put' hpg₁ hind₁ hpg₂ hind₂
    funext s a
    exact hext _ _ ((hpg₁ s a).trans (hpg₂ s a).symm) ((hind₁ s a).trans (hind₂ s a).symm)
  · intro put hpg hind
    exact ⟨getPut_of_putGet_putIndep_jointExt hpg hind hext,
           hpg,
           putPut_of_putGet_putIndep_jointExt hpg hind hext⟩

end Unique

/-! ## Examples, non-vacuity witnesses and counterexamples for F6 (proved) -/

/-- **PutGet, GetPut and PutPut alone leave several lawful puts.**  `fst` and
the state-twisting lens have the same getter, are both very well-behaved, and
have different puts. -/
theorem fst_twist_two_veryWellBehaved_puts :
    fstB.get = twist.get ∧ fstB.VeryWellBehaved ∧ twist.VeryWellBehaved ∧ fstB.put ≠ twist.put :=
  ⟨rfl, fst_veryWellBehaved, twist_veryWellBehaved,
   fun h => absurd (congrFun (congrFun h (false, false)) true) (by decide)⟩

/-- **Exactly two very well-behaved puts for `fst` on `Bool × Bool`**: every
very well-behaved put for the first projection is `fst.put` or `twist.put`
(matching `(m!)^(k-1) = 2!^1 = 2`). -/
theorem veryWellBehaved_puts_getFst_eq_fst_or_twist (put : Bool × Bool → Bool → Bool × Bool)
    (h : (Lens.mk getFst put).VeryWellBehaved) : put = fstB.put ∨ put = twist.put := by
  obtain ⟨hgp, hpg, hpp⟩ := h
  have nf : ∀ s a, put s a = (a, (put s a).2) := fun s a => Prod.ext (hpg s a) rfl
  have gp : ∀ a b, put (a, b) a = (a, b) := fun a b => hgp (a, b)
  have back : ∀ b, put (true, (put (false, b) true).2) false = (false, b) := by
    intro b
    have h₁ : put (put (false, b) true) false = put (false, b) false := hpp (false, b) true false
    rw [nf (false, b) true] at h₁
    exact h₁.trans (gp false b)
  have v0 := nf (false, false) true
  have v1 := nf (false, true) true
  have b0 := back false
  have b1 := back true
  cases h0 : (put (false, false) true).2 <;> cases h1 : (put (false, true) true).2 <;>
    rw [h0] at v0 b0 <;> rw [h1] at v1 b1
  · exact absurd (b0.symm.trans b1) (by decide)
  · left
    funext s a
    obtain ⟨x, y⟩ := s
    cases x <;> cases y <;> cases a
    · exact gp false false
    · exact v0
    · exact gp false true
    · exact v1
    · exact b0
    · exact gp true false
    · exact b1
    · exact gp true true
  · right
    funext s a
    obtain ⟨x, y⟩ := s
    cases x <;> cases y <;> cases a
    · exact gp false false
    · exact v0
    · exact gp false true
    · exact v1
    · exact b1
    · exact gp true false
    · exact b0
    · exact gp true true
  · exact absurd (b0.symm.trans b1) (by decide)

/-- **Different complement views single out different puts.**  The
state-twisting put satisfies `PutGet` and the frame law against the XOR view,
and the first projection together with the XOR view determines the state; so
with complement view `xorView` it is the state-twisting put, not `fst.put`,
that F6-unique singles out. -/
theorem twist_putIndep_xorView_complement :
    twist.PutGet ∧ PutIndep twist xorView ∧
    (∀ s t : Bool × Bool, getFst s = getFst t → xorView.get s = xorView.get t → s = t) ∧
    ¬ PutIndep fstB xorView := by
  refine ⟨twist_veryWellBehaved.2.1, ?_, ?_, fst_xorView_not_putIndep⟩
  · intro ⟨a, b⟩ a'
    cases a <;> cases b <;> cases a' <;> rfl
  · intro ⟨a, b⟩ ⟨a', b'⟩ h₁ h₂
    have h₁' : a = a' := h₁
    subst h₁'
    cases a <;> cases b <;> cases b' <;> first | rfl | exact absurd h₂ (by decide)

/-- **Non-vacuity of F6 (ground instance).**  For the first projection on
`Bool × Bool`, the fibre maps of `fst` are coherent and `fst` is very
well-behaved. -/
theorem f6_nonvacuity :
    (ofPut getFst fstB.put (fun _ _ => rfl)).Coherent ∧
    (Lens.mk getFst fstB.put).VeryWellBehaved :=
  ⟨ofPut_fst_coherent, fst_veryWellBehaved⟩

/-- The fibre of `getFst` over any view has two elements. -/
def getFstFiberEquiv (a : Bool) : Equiv (GetFiber getFst a) (Fin 2) where
  toFun x := if x.1.2 then 1 else 0
  invFun i := ⟨(a, i == 1), rfl⟩
  left_inv := by
    intro ⟨⟨x, y⟩, hx⟩
    have hx' : x = a := hx
    subst hx'
    cases y <;> rfl
  right_inv := by
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- `Bool` has two elements. -/
def boolEquivFin2 : Equiv Bool (Fin 2) where
  toFun b := if b then 1 else 0
  invFun i := i == 1
  left_inv := by intro b; cases b <;> rfl
  right_inv := by
    intro i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl

/-- **Non-vacuity of the counting and base-fibre forms of F6 (ground
instance).**  For the first projection on `Bool × Bool`: two views, every fibre
has two elements, and `false` is a base view. -/
theorem f6_count_nonvacuity :
    Nonempty (Equiv Bool (Fin 2)) ∧ (∀ a, Nonempty (Equiv (GetFiber getFst a) (Fin 2))) ∧
    Nonempty Bool :=
  ⟨⟨boolEquivFin2⟩, fun a => ⟨getFstFiberEquiv a⟩, ⟨false⟩⟩

/-- A getter on `Option Bool` with fibres of different sizes: one state over
`false`, two states over `true`. -/
abbrev getIsSome : Option Bool → Bool := fun o => o.isSome

theorem eq_none_of_getIsSome_false (o : Option Bool) (h : getIsSome o = false) : o = none := by
  cases o with
  | none => rfl
  | some b => exact absurd h (fun h' => Bool.false_ne_true h'.symm)

/-- No very well-behaved put exists for `getIsSome`. -/
theorem getIsSome_no_veryWellBehaved_put (put : Option Bool → Bool → Option Bool) :
    ¬ (Lens.mk getIsSome put).VeryWellBehaved := by
  intro ⟨hgp, hpg, hpp⟩
  have e₀ : put (some false) false = none := eq_none_of_getIsSome_false _ (hpg (some false) false)
  have e₁ : put (some true) false = none := eq_none_of_getIsSome_false _ (hpg (some true) false)
  have k₀ : put none true = some false := by
    have : put (put (some false) false) true = put (some false) true := hpp (some false) false true
    rw [e₀] at this
    exact this.trans (hgp (some false))
  have k₁ : put none true = some true := by
    have : put (put (some true) false) true = put (some true) true := hpp (some true) false true
    rw [e₁] at this
    exact this.trans (hgp (some true))
  exact absurd (k₀.symm.trans k₁) (by decide)

/-- **F6-count needs uniform fibre size.**  For `getIsSome` the view type has
two elements, but no `m` is the size of every fibre, and for every `m` both
conclusions of the counting theorem fail (there is no very well-behaved put at
all). -/
theorem card_tight_uniform_fibers :
    Nonempty (Equiv Bool (Fin 2)) ∧
    (∀ m, ¬ ∀ a, Nonempty (Equiv (GetFiber getIsSome a) (Fin m))) ∧
    (∀ m, ¬ Nonempty (Equiv {put : Option Bool → Bool → Option Bool //
        (Lens.mk getIsSome put).VeryWellBehaved} (Fin (2 - 1) → Equiv (Fin m) (Fin m)))) ∧
    (∀ m, ¬ Nonempty (Equiv {put : Option Bool → Bool → Option Bool //
        (Lens.mk getIsSome put).VeryWellBehaved} (Fin (factorial m ^ (2 - 1))))) := by
  refine ⟨⟨boolEquivFin2⟩, ?_, ?_, ?_⟩
  · intro m hF
    obtain ⟨e₀⟩ := hF false
    obtain ⟨e₁⟩ := hF true
    let f : GetFiber getIsSome true → GetFiber getIsSome false := fun x => e₀.invFun (e₁.toFun x)
    have hf : Function.Injective f := by
      intro x y hxy
      have h₁ : e₁.toFun x = e₁.toFun y := by
        have := congrArg e₀.toFun hxy
        rwa [e₀.right_inv, e₀.right_inv] at this
      exact Equiv.injective e₁ h₁
    have hsame : f ⟨some false, rfl⟩ = f ⟨some true, rfl⟩ :=
      Subtype.ext ((eq_none_of_getIsSome_false _ (f ⟨some false, rfl⟩).2).trans
        (eq_none_of_getIsSome_false _ (f ⟨some true, rfl⟩).2).symm)
    exact absurd (congrArg Subtype.val (hf hsame)) (by decide)
  · intro m ⟨e⟩
    exact getIsSome_no_veryWellBehaved_put _ (e.invFun (fun _ => Equiv.refl _)).2
  · intro m ⟨e⟩
    have hpos : 0 < factorial m ^ (2 - 1) := by
      show 0 < factorial m ^ 1
      rw [Nat.pow_one]
      exact factorial_pos m
    exact getIsSome_no_veryWellBehaved_put _ (e.invFun ⟨0, hpos⟩).2

/-- **F6-count needs the number of views.**  For the first projection on
`Bool × Bool` every fibre has two elements but the view type does not have one
element, and for `k = 1` both conclusions of the counting theorem fail (there
are at least two very well-behaved puts). -/
theorem card_tight_views :
    (∀ a, Nonempty (Equiv (GetFiber getFst a) (Fin 2))) ∧
    ¬ Nonempty (Equiv Bool (Fin 1)) ∧
    ¬ Nonempty (Equiv {put : Bool × Bool → Bool → Bool × Bool //
        (Lens.mk getFst put).VeryWellBehaved} (Fin (1 - 1) → Equiv (Fin 2) (Fin 2))) ∧
    ¬ Nonempty (Equiv {put : Bool × Bool → Bool → Bool × Bool //
        (Lens.mk getFst put).VeryWellBehaved} (Fin (factorial 2 ^ (1 - 1)))) := by
  let p₁ : {put : Bool × Bool → Bool → Bool × Bool // (Lens.mk getFst put).VeryWellBehaved} :=
    ⟨fstB.put, fst_veryWellBehaved⟩
  let p₂ : {put : Bool × Bool → Bool → Bool × Bool // (Lens.mk getFst put).VeryWellBehaved} :=
    ⟨twist.put, twist_veryWellBehaved⟩
  have hne : p₁ ≠ p₂ := fun h => fst_twist_two_veryWellBehaved_puts.2.2.2 (congrArg Subtype.val h)
  refine ⟨fun a => ⟨getFstFiberEquiv a⟩, ?_, ?_, ?_⟩
  · intro ⟨e⟩
    have h₁ : e.toFun true = e.toFun false := Fin.ext (by omega)
    exact absurd (Equiv.injective e h₁) (by decide)
  · intro ⟨e⟩
    exact hne (Equiv.injective e (funext fun i => i.elim0))
  · intro ⟨e⟩
    have a₁ : (e.toFun p₁).val < 1 := (e.toFun p₁).2
    have a₂ : (e.toFun p₂).val < 1 := (e.toFun p₂).2
    have h₁ : e.toFun p₁ = e.toFun p₂ := Fin.ext (by omega)
    exact hne (Equiv.injective e h₁)

/-- **Non-vacuity of F6-unique (ground instance).**  The first projection with
complement view `snd` on `Bool × Bool`. -/
theorem f6_unique_nonvacuity :
    (∀ s t : Bool × Bool, getFst s = getFst t → sndB.get s = sndB.get t → s = t) ∧
    (∀ a c : Bool, ∃ s, getFst s = a ∧ sndB.get s = c) :=
  ⟨fun _ _ h₁ h₂ => Prod.ext h₁ h₂, fun a c => ⟨(a, c), rfl, rfl⟩⟩

/-- **F6-unique needs the complement view to determine the state.**  With the
one-point complement view `unitLensB`, every pair of values is realised, but
two different puts (`fst.put` and `twist.put`) satisfy `PutGet` and the frame
law, so uniqueness fails. -/
theorem existsUnique_put_tight_jointExt :
    ¬ (∀ s t : Bool × Bool, getFst s = getFst t → unitLensB.get s = unitLensB.get t → s = t) ∧
    (∀ (a : Bool) (c : Unit), ∃ s, getFst s = a ∧ unitLensB.get s = c) ∧
    ¬ (∀ put put' : Bool × Bool → Bool → Bool × Bool,
      (Lens.mk getFst put).PutGet → PutIndep (Lens.mk getFst put) unitLensB →
      (Lens.mk getFst put').PutGet → PutIndep (Lens.mk getFst put') unitLensB → put = put') :=
  ⟨fun h => absurd (h (false, false) (false, true) rfl rfl) (by decide),
   fun a _ => ⟨(a, false), rfl, rfl⟩,
   fun h => fst_twist_two_veryWellBehaved_puts.2.2.2
     (h fstB.put twist.put (fun _ _ => rfl) (fun _ _ => rfl) twist_veryWellBehaved.2.1
       (fun _ _ => rfl))⟩

/-- **F6-unique needs every pair of values to be realised.**  On the one-point
state type with the constant getter `false`, the complement view determines the
state, but the value `true` is never realised and no put satisfies `PutGet`. -/
theorem existsUnique_put_tight_surjective :
    (∀ s t : Unit, (fun _ : Unit => false) s = (fun _ : Unit => false) t →
      (unitLens : Lens Unit Unit).get s = (unitLens : Lens Unit Unit).get t → s = t) ∧
    ¬ (∀ (a : Bool) (c : Unit), ∃ s : Unit,
      (fun _ : Unit => false) s = a ∧ (unitLens : Lens Unit Unit).get s = c) ∧
    ¬ (∃ put : Unit → Bool → Unit, (Lens.mk (fun _ : Unit => false) put).PutGet ∧
      PutIndep (Lens.mk (fun _ : Unit => false) put) (unitLens : Lens Unit Unit)) :=
  ⟨fun _ _ _ _ => rfl,
   fun h => match h true () with | ⟨_, h₁, _⟩ => Bool.false_ne_true h₁,
   fun ⟨_, hpg, _⟩ => Bool.false_ne_true (hpg () true)⟩

/-! ## Edge cases and over-reading guards for F6 (proved) -/

/-- **Dropping `hext` from F6-unique also breaks the third conjunct, not only
uniqueness.**  With the one-point complement view `unitLensB` (which does not
determine the state) every pair of values is realised, and two puts satisfy
`PutGet` and the frame law against `unitLensB` while violating a classical law:
the dirty-flag setter violates `PutPut` and the sibling-resetting setter
violates `GetPut`. -/
theorem existsUnique_put_drop_jointExt_admits_unlawful_puts :
    ¬ (∀ s t : Bool × Bool, getFst s = getFst t → unitLensB.get s = unitLensB.get t → s = t) ∧
    (∀ (a : Bool) (c : Unit), ∃ s, getFst s = a ∧ unitLensB.get s = c) ∧
    ((Lens.mk getFst dirtyFlag.put).PutGet ∧ PutIndep (Lens.mk getFst dirtyFlag.put) unitLensB ∧
      ¬ (Lens.mk getFst dirtyFlag.put).PutPut) ∧
    ((Lens.mk getFst resetSibling.put).PutGet ∧ PutIndep (Lens.mk getFst resetSibling.put) unitLensB ∧
      ¬ (Lens.mk getFst resetSibling.put).GetPut) ∧
    ¬ (∀ put : Bool × Bool → Bool → Bool × Bool,
        (Lens.mk getFst put).PutGet → PutIndep (Lens.mk getFst put) unitLensB →
        (Lens.mk getFst put).VeryWellBehaved) :=
  ⟨existsUnique_put_tight_jointExt.1,
   existsUnique_put_tight_jointExt.2.1,
   ⟨dirtyFlag_putGet, fun _ _ => rfl, dirtyFlag_not_putPut⟩,
   ⟨resetSibling_putGet, fun _ _ => rfl, resetSibling_not_getPut⟩,
   fun h => dirtyFlag_not_veryWellBehaved (h dirtyFlag.put dirtyFlag_putGet (fun _ _ => rfl))⟩

/-- **The exact existence condition behind F6-unique.**  For any getter and any
second view `m`, a put with `PutGet` and the frame law against `m` exists if and
only if, from every state `s`, every view value `a` is realised by some state
with the same `m`-view as `s`.  (No joint extensionality is needed for this
equivalence; the hypothesis `hsurj` of F6-unique implies the right-hand side.) -/
theorem exists_put_putGet_putIndep_iff {S : Type u} {A : Type v} {C : Type w}
    (get : S → A) (m : Lens S C) :
    (∃ put : S → A → S, (Lens.mk get put).PutGet ∧ PutIndep (Lens.mk get put) m) ↔
      ∀ s a, ∃ s', get s' = a ∧ m.get s' = m.get s := by
  constructor
  · rintro ⟨put, hpg, hind⟩ s a
    exact ⟨put s a, hpg s a, hind s a⟩
  · intro h
    exact ⟨fun s a => Classical.choose (h s a),
      fun s a => (Classical.choose_spec (h s a)).1,
      fun s a => (Classical.choose_spec (h s a)).2⟩

/-- A constant complement view on `Bool` (its value is always `false`). -/
def constFalseView : Lens Bool Bool where
  get _ := false
  put s _ := s

/-- **`hsurj` is sufficient for F6-unique but not necessary for its
conclusion.**  For the identity getter on `Bool` with the constant complement
view `constFalseView`: the two views determine the state (`hext` holds), the
pair `(false, true)` is never realised (`hsurj` fails), and still there is
exactly one put with `PutGet` and the frame law, and it is very well-behaved. -/
theorem existsUnique_put_hsurj_not_necessary :
    (∀ s t : Bool, id s = id t → constFalseView.get s = constFalseView.get t → s = t) ∧
    ¬ (∀ a c : Bool, ∃ s : Bool, id s = a ∧ constFalseView.get s = c) ∧
    (∃ put : Bool → Bool → Bool, (Lens.mk id put).PutGet ∧ PutIndep (Lens.mk id put) constFalseView) ∧
    (∀ put put' : Bool → Bool → Bool,
      (Lens.mk id put).PutGet → PutIndep (Lens.mk id put) constFalseView →
      (Lens.mk id put').PutGet → PutIndep (Lens.mk id put') constFalseView → put = put') ∧
    (∀ put : Bool → Bool → Bool, (Lens.mk id put).PutGet → PutIndep (Lens.mk id put) constFalseView →
      (Lens.mk id put).VeryWellBehaved) := by
  refine ⟨fun _ _ h _ => h, ?_, ⟨fun _ a => a, fun _ _ => rfl, fun _ _ => rfl⟩, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, hs⟩ := h false true
    exact Bool.false_ne_true hs
  · intro put put' hpg₁ _ hpg₂ _
    funext s a
    exact (hpg₁ s a).trans (hpg₂ s a).symm
  · intro put hpg _
    have heq : put = fun _ a => a := funext fun s => funext fun a => hpg s a
    subst heq
    exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **Edge case `m = 0`, `k = 2` of F6-count.**  For the empty state type with
the two-element view type `Bool`, every fibre has `0` elements and there is
exactly `(0!)^(2 - 1) = 1` very well-behaved put (the empty function), although
the getter is not surjective. -/
theorem card_veryWellBehaved_puts_empty_state_two_views :
    Nonempty (Equiv Bool (Fin 2)) ∧
    (∀ a : Bool, Nonempty (Equiv (GetFiber (Empty.elim : Empty → Bool) a) (Fin 0))) ∧
    ¬ Function.Surjective (Empty.elim : Empty → Bool) ∧
    Nonempty (Equiv {put : Empty → Bool → Empty // (Lens.mk Empty.elim put).VeryWellBehaved}
      (Fin (factorial 0 ^ (2 - 1)))) := by
  have hA : Nonempty (Equiv Bool (Fin 2)) := ⟨boolEquivFin2⟩
  have hF : ∀ a : Bool, Nonempty (Equiv (GetFiber (Empty.elim : Empty → Bool) a) (Fin 0)) :=
    fun _ => ⟨{
      toFun := fun x => x.1.elim
      invFun := fun i => i.elim0
      left_inv := fun x => x.1.elim
      right_inv := fun i => i.elim0
    }⟩
  exact ⟨hA, hF, fun h => (h true).elim fun s _ => s.elim,
    (card_veryWellBehaved_puts_of_card_views_card_fibers Empty.elim 2 0 hA hF).2⟩

/-- **Edge case `k = 1` of F6-count: one view value, whatever the fibre size.**
If any two views are equal, the write that changes nothing is very well-behaved
and it is the only very well-behaved put (`GetPut` forces `put s a = s`), in
agreement with `(m!)^0 = 1`. -/
theorem veryWellBehaved_put_eq_self_of_subsingleton_view {S : Type u} {A : Type v}
    (get : S → A) (hA : ∀ a a' : A, a = a') :
    (Lens.mk get (fun s _ => s)).VeryWellBehaved ∧
    (∀ put : S → A → S, (Lens.mk get put).VeryWellBehaved → put = fun s _ => s) := by
  refine ⟨⟨fun _ => rfl, fun s a => hA (get s) a, fun _ _ _ => rfl⟩, ?_⟩
  intro put h
  funext s a
  rw [hA a (get s)]
  exact h.1 s

end Lens

end Toy
