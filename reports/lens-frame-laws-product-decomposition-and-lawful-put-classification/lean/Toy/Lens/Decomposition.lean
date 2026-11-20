/-
Toy.Lens.Decomposition
======================

* the notions that phrase the conclusions of F1 and F2
  (`Intertwines`, `pairGet`, `pairPut`, `IsProductDecomposition`,
  `IsPiDecomposition`), each with proved positive and negative examples;
* the *derived-law lemmas* (proved): `GetPut`, `PutPut` and `PutComm` follow
  from `PutGet` + cross-independence + joint extensionality;
* the statements of **F1** (pair decomposition) and **F2** (indexed
  decomposition), with proofs.
-/
import Toy.Lens.Family

namespace Toy

namespace Lens

universe u v w x

/-! ## Maps that carry one lens to another -/

section Intertwines

variable {S : Type u} {T : Type x} {A : Type v}

/--
`Intertwines f l m`: the map `f : S → T` carries the lens `l` on `S` to the
lens `m` on `T` (same view type): it preserves `get` and commutes with `put`.

Meant to capture "under the change of representation `f`, the lens `l` *is*
the lens `m`".  When `m` is `Lens.fst` this reads: "under `f`, `l.get` is the
first projection and `l.put` is first-coordinate update".
-/
structure Intertwines (f : S → T) (l : Lens S A) (m : Lens T A) : Prop where
  /-- `f` preserves the view. -/
  get_eq : ∀ s, m.get (f s) = l.get s
  /-- `f` commutes with writing. -/
  put_eq : ∀ s a, f (l.put s a) = m.put (f s) a

/-- Positive example for `Intertwines`: the identity map carries a lens to
itself. -/
theorem intertwines_id (l : Lens S A) : Intertwines (fun s => s) l l :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Positive example for `Intertwines`: swapping a pair carries `fst` to
`snd`. -/
theorem intertwines_swap {A : Type v} {B : Type w} :
    Intertwines (fun p : A × B => (p.2, p.1)) (fst : Lens (A × B) A) (snd : Lens (B × A) A) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- Negative example for `Intertwines`: the identity map does **not** carry the
state-twisting lens to `fst`, although the two lenses have the same `get`. -/
theorem not_intertwines_id_twist_fst :
    ¬ Intertwines (fun s => s) twist (fst : Lens (Bool × Bool) Bool) :=
  fun h => absurd (h.put_eq (false, false) true) (by decide)

end Intertwines

/-! ## Pairs of lenses: the candidate isomorphism and its candidate inverse -/

section Pair

variable {S : Type u} {A : Type v} {B : Type w}

/--
The pairing of the two views, `s ↦ (l₁.get s, l₂.get s)`: the *specific*
candidate isomorphism `S → A × B` of F1.
-/
def pairGet (l₁ : Lens S A) (l₂ : Lens S B) : S → A × B :=
  fun s => (l₁.get s, l₂.get s)

/--
Overwrite both fields of a base state `s₀`, first through `l₁`, then through
`l₂`: the *specific* candidate inverse of `pairGet` in F1.
-/
def pairPut (l₁ : Lens S A) (l₂ : Lens S B) (s₀ : S) : A × B → S :=
  fun p => l₂.put (l₁.put s₀ p.1) p.2

/-- Positive example for `pairGet`: for `fst`/`snd` it is the identity. -/
theorem pairGet_fst_snd (p : A × B) :
    pairGet (fst : Lens (A × B) A) (snd : Lens (A × B) B) p = p :=
  rfl

/-- Negative example for `pairGet`: for two aliasing copies of `fst` it
forgets the second component (it is not injective). -/
theorem pairGet_fst_fst_not_injective :
    ¬ Function.Injective
        (pairGet (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool)) := by
  intro h
  have h' : ((false, false) : Bool × Bool) = (false, true) := h rfl
  exact absurd h' (by decide)

/-- Positive example for `pairPut`: for `fst`/`snd` it returns its argument,
whatever the base state. -/
theorem pairPut_fst_snd (s₀ p : A × B) :
    pairPut (fst : Lens (A × B) A) (snd : Lens (A × B) B) s₀ p = p :=
  rfl

/-- Negative example for `pairPut`: for two aliasing copies of `fst` the second
write clobbers the first, so `pairPut` is not a right inverse of `pairGet`. -/
theorem pairGet_pairPut_fst_fst_ne :
    pairGet (fst : Lens (Bool × Bool) Bool) fst
        (pairPut (fst : Lens (Bool × Bool) Bool) fst (false, false) (true, false))
      ≠ (true, false) := by
  decide

/--
`IsProductDecomposition l₁ l₂` is the **conclusion of F1**: the two lenses
present the state type as the product of their view types.

Precisely: the *specific* map `pairGet l₁ l₂ = fun s => (l₁.get s, l₂.get s)`
is a bijection `S → A × B`, and under it `l₁` is the first-projection lens and
`l₂` is the second-projection lens.  Unfolded, the four fields say

* `injective`  : `pairGet l₁ l₂ s = pairGet l₁ l₂ t → s = t`;
* `surjective` : `∀ p : A × B, ∃ s, pairGet l₁ l₂ s = p`;
* `intertwines_fst.put_eq` :
    `(l₁.get (l₁.put s a), l₂.get (l₁.put s a)) = (a, l₂.get s)`;
* `intertwines_snd.put_eq` :
    `(l₁.get (l₂.put s b), l₂.get (l₂.put s b)) = (l₁.get s, b)`;

(the two `get_eq` components hold by `rfl`).

Meant to capture "setting one field changes that field and nothing else, and
there is nothing else in the state".
-/
structure IsProductDecomposition (l₁ : Lens S A) (l₂ : Lens S B) : Prop where
  /-- The pairing map is injective: no hidden state. -/
  injective : Function.Injective (pairGet l₁ l₂)
  /-- The pairing map is surjective: every pair of field values occurs. -/
  surjective : Function.Surjective (pairGet l₁ l₂)
  /-- Under the pairing map, `l₁` is the first-projection lens. -/
  intertwines_fst : Intertwines (pairGet l₁ l₂) l₁ (fst : Lens (A × B) A)
  /-- Under the pairing map, `l₂` is the second-projection lens. -/
  intertwines_snd : Intertwines (pairGet l₁ l₂) l₂ (snd : Lens (A × B) B)

/-- Positive example for `IsProductDecomposition`, and the **non-vacuity
witness for F1**: `fst` and `snd` on any product. -/
theorem fst_snd_isProductDecomposition :
    IsProductDecomposition (fst : Lens (A × B) A) (snd : Lens (A × B) B) where
  injective := fun _ _ h => h
  surjective := fun p => ⟨p, rfl⟩
  intertwines_fst := ⟨fun _ => rfl, fun _ _ => rfl⟩
  intertwines_snd := ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- **Non-vacuity of F1.**  `fst` and `snd` on *any* product (empty or not)
satisfy every hypothesis of F1.  (A ground instance on `Bool × Bool` is
`Toy.Lens.f1_nonvacuity_bool`.) -/
theorem fst_snd_satisfy_f1_hypotheses :
    (fst : Lens (A × B) A).PutGet ∧ (snd : Lens (A × B) B).PutGet ∧
    PutIndep (fst : Lens (A × B) A) (snd : Lens (A × B) B) ∧
    PutIndep (snd : Lens (A × B) B) (fst : Lens (A × B) A) ∧
    JointExt (fst : Lens (A × B) A) (snd : Lens (A × B) B) ∧
    (Nonempty (A × B) → Nonempty (A × B)) :=
  ⟨fst_putGet, snd_putGet, fst_snd_putIndep, snd_fst_putIndep, fst_snd_jointExt, fun h => h⟩

/-- Negative example for `IsProductDecomposition`: two aliasing copies of
`fst`.  (More negative examples, one per hypothesis of F1, are in
`Toy.Lens.Tightness`.) -/
theorem fst_fst_not_isProductDecomposition :
    ¬ IsProductDecomposition (fst : Lens (Bool × Bool) Bool) (fst : Lens (Bool × Bool) Bool) :=
  fun h => pairGet_fst_fst_not_injective h.injective

/-- **The witness is forced.**  Any map `f : S → A × B` that preserves both
views is equal to `pairGet l₁ l₂`.  So "there is *some* bijection `S ≃ A × B`
compatible with the two getters" and "`pairGet` is a bijection" are the same
statement, whereas "there is some bijection `S ≃ A × B`" (with no
compatibility) is strictly weaker; see
`Toy.Lens.ghost_admits_unrelated_bijection`.  Each of the two compatibility
hypotheses is needed: `Toy.Lens.eq_pairGet_tight_left` and
`Toy.Lens.eq_pairGet_tight_right`. -/
theorem eq_pairGet_of_get_eq {l₁ : Lens S A} {l₂ : Lens S B} (f : S → A × B)
    (h₁ : ∀ s, (f s).1 = l₁.get s) (h₂ : ∀ s, (f s).2 = l₂.get s) :
    f = pairGet l₁ l₂ := by
  funext s
  show f s = (l₁.get s, l₂.get s)
  rw [← h₁ s, ← h₂ s]

/-! ## Derived-law lemmas (proved)

`PutGet` for each lens, cross-independence in both directions and joint
extensionality already imply `GetPut`, `PutPut` and commuting puts; no
nonemptiness assumption is needed for any of the three.
-/

/-- Joint extensionality is symmetric in the two lenses. -/
theorem JointExt.symm {l₁ : Lens S A} {l₂ : Lens S B} (h : JointExt l₁ l₂) : JointExt l₂ l₁ :=
  fun s t h₂ h₁ => h s t h₁ h₂

/-- **Derived law 1.** `PutGet l₁`, `PutIndep l₁ l₂` and `JointExt l₁ l₂` imply
`GetPut l₁`.  (Nothing is assumed about the laws of `l₂`.) -/
theorem getPut_of_putGet_putIndep_jointExt {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₁₂ : PutIndep l₁ l₂) (hext : JointExt l₁ l₂) :
    l₁.GetPut :=
  fun s => hext _ _ (h₁ s (l₁.get s)) (h₁₂ s (l₁.get s))

/-- **Derived law 2.** `PutGet l₁`, `PutIndep l₁ l₂` and `JointExt l₁ l₂` imply
`PutPut l₁`.  (Nothing is assumed about the laws of `l₂`.) -/
theorem putPut_of_putGet_putIndep_jointExt {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₁₂ : PutIndep l₁ l₂) (hext : JointExt l₁ l₂) :
    l₁.PutPut :=
  fun s a a' =>
    hext _ _ ((h₁ (l₁.put s a) a').trans (h₁ s a').symm)
      ((h₁₂ (l₁.put s a) a').trans ((h₁₂ s a).trans (h₁₂ s a').symm))

/-- **Derived law 3.** `PutGet` for both lenses, `PutIndep` in both directions
and `JointExt` imply that the two puts commute. -/
theorem putComm_of_putGet_putIndep_jointExt {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₂ : l₂.PutGet)
    (h₁₂ : PutIndep l₁ l₂) (h₂₁ : PutIndep l₂ l₁)
    (hext : JointExt l₁ l₂) :
    PutComm l₁ l₂ :=
  fun s a b =>
    hext _ _
      (((h₂₁ (l₁.put s a) b).trans (h₁ s a)).trans (h₁ (l₂.put s b) a).symm)
      ((h₂ (l₁.put s a) b).trans (((h₁₂ (l₂.put s b) a).trans (h₂ s b)).symm))

/-- **Derived laws, bundled.** Under the five laws of F1 (no nonemptiness
assumption) both lenses are very well-behaved and their puts commute. -/
theorem veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt
    {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₂ : l₂.PutGet)
    (h₁₂ : PutIndep l₁ l₂) (h₂₁ : PutIndep l₂ l₁)
    (hext : JointExt l₁ l₂) :
    l₁.VeryWellBehaved ∧ l₂.VeryWellBehaved ∧ PutComm l₁ l₂ :=
  ⟨⟨getPut_of_putGet_putIndep_jointExt h₁ h₁₂ hext, h₁,
      putPut_of_putGet_putIndep_jointExt h₁ h₁₂ hext⟩,
   ⟨getPut_of_putGet_putIndep_jointExt h₂ h₂₁ hext.symm, h₂,
      putPut_of_putGet_putIndep_jointExt h₂ h₂₁ hext.symm⟩,
   putComm_of_putGet_putIndep_jointExt h₁ h₂ h₁₂ h₂₁ hext⟩

/-! ## F1 — pair decomposition -/

/--
**F1 (pair decomposition).**  If each lens satisfies `PutGet`, the two lenses
are cross-independent in both directions, they are jointly extensional, and
the state type is nonempty whenever `A × B` is, then the specific map
`fun s => (l₁.get s, l₂.get s)` is a bijection `S → A × B` under which `l₁.put`
is first-coordinate update and `l₂.put` is second-coordinate update.

`GetPut`, `PutPut` and commuting puts are **not** assumed; they follow
(`veryWellBehaved_and_putComm_of_putGet_putIndep_jointExt`).  A caller holding
`hS : Nonempty S` passes `fun _ => hS`.  The hypothesis `hS` is exactly the
nonemptiness condition of the equivalence
`isProductDecomposition_iff_putGet_putIndep_jointExt_imp_nonempty`.
-/
theorem isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty
    {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₂ : l₂.PutGet)
    (h₁₂ : PutIndep l₁ l₂) (h₂₁ : PutIndep l₂ l₁)
    (hext : JointExt l₁ l₂) (hS : Nonempty (A × B) → Nonempty S) :
    IsProductDecomposition l₁ l₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- injective: joint extensionality, verbatim
    intro s t h
    exact hext s t (congrArg Prod.fst h) (congrArg Prod.snd h)
  · -- surjective: write `p.1` then `p.2` into any state
    intro p
    obtain ⟨s₀⟩ := hS ⟨p⟩
    exact ⟨l₂.put (l₁.put s₀ p.1) p.2, Prod.ext ((h₂₁ _ p.2).trans (h₁ s₀ p.1)) (h₂ _ p.2)⟩
  · exact ⟨fun _ => rfl, fun s a => Prod.ext (h₁ s a) (h₁₂ s a)⟩
  · exact ⟨fun _ => rfl, fun s b => Prod.ext (h₂₁ s b) (h₂ s b)⟩

/--
**F1, exact form.**  The conclusion of F1 holds *if and only if* the five laws
hold and the state type is nonempty whenever `A × B` is.

So the hypothesis list of F1 is not merely sufficient but equivalent to the
conclusion.
-/
theorem isProductDecomposition_iff_putGet_putIndep_jointExt_imp_nonempty
    {l₁ : Lens S A} {l₂ : Lens S B} :
    IsProductDecomposition l₁ l₂ ↔
      l₁.PutGet ∧ l₂.PutGet ∧ PutIndep l₁ l₂ ∧ PutIndep l₂ l₁ ∧ JointExt l₁ l₂ ∧
        (Nonempty (A × B) → Nonempty S) := by
  constructor
  · intro h
    exact ⟨fun s a => congrArg Prod.fst (h.intertwines_fst.put_eq s a),
           fun s b => congrArg Prod.snd (h.intertwines_snd.put_eq s b),
           fun s a => congrArg Prod.snd (h.intertwines_fst.put_eq s a),
           fun s b => congrArg Prod.fst (h.intertwines_snd.put_eq s b),
           fun s t h₁ h₂ => h.injective (Prod.ext h₁ h₂),
           fun ⟨p⟩ => let ⟨s, _⟩ := h.surjective p; ⟨s⟩⟩
  · rintro ⟨h₁, h₂, h₁₂, h₂₁, hext, hne⟩
    exact isProductDecomposition_of_putGet_putIndep_jointExt_imp_nonempty h₁ h₂ h₁₂ h₂₁ hext hne

/--
**F1, explicit inverse.**  For *every* base state `s₀`, the map
`pairPut l₁ l₂ s₀ = fun p => l₂.put (l₁.put s₀ p.1) p.2` is a two-sided inverse
of `pairGet l₁ l₂`.

This needs only **one** direction of cross-independence, `PutIndep l₂ l₁`
(the put applied second must not disturb the view written first); it does not
use `PutIndep l₁ l₂`.
-/
theorem pairPut_leftInverse_rightInverse_of_putGet_putIndep_jointExt
    {l₁ : Lens S A} {l₂ : Lens S B}
    (h₁ : l₁.PutGet) (h₂ : l₂.PutGet)
    (h₂₁ : PutIndep l₂ l₁)
    (hext : JointExt l₁ l₂) (s₀ : S) :
    Function.LeftInverse (pairPut l₁ l₂ s₀) (pairGet l₁ l₂) ∧
      Function.RightInverse (pairPut l₁ l₂ s₀) (pairGet l₁ l₂) := by
  refine ⟨fun s => ?_, fun p => ?_⟩
  · -- `pairPut s₀ (pairGet s)` and `s` have the same two views
    exact hext _ _ ((h₂₁ _ _).trans (h₁ s₀ _)) (h₂ _ _)
  · exact Prod.ext ((h₂₁ _ p.2).trans (h₁ s₀ p.1)) (h₂ _ p.2)

end Pair

/-! ## Families of lenses -/

section Family

variable {S : Type u} {ι : Type w} {A : ι → Type v}

/--
`IsPiDecomposition l` is the **conclusion of F2**: the family of lenses
presents the state type as the dependent product of the view types.

Precisely: the *specific* map `famGet l = fun s i => (l i).get s` is a
bijection `S → (i : ι) → A i`, and under it each `l i` is the `i`-th
coordinate lens `coord i`.  Unfolded, `(intertwines i).put_eq` says
`famGet l ((l i).put s a) = update (famGet l s) i a`.
-/
structure IsPiDecomposition [DecidableEq ι] (l : (i : ι) → Lens S (A i)) : Prop where
  /-- The tuple-of-views map is injective: no hidden state. -/
  injective : Function.Injective (famGet l)
  /-- The tuple-of-views map is surjective: every tuple of field values occurs. -/
  surjective : Function.Surjective (famGet l)
  /-- Under the tuple-of-views map, `l i` is the `i`-th coordinate lens. -/
  intertwines : ∀ i, Intertwines (famGet l) (l i) (coord i)

/-- Positive example for `IsPiDecomposition`, and the **non-vacuity witness
for F2**: the coordinate lenses on a full dependent product (any index type,
finite or not). -/
theorem coord_isPiDecomposition [DecidableEq ι] :
    IsPiDecomposition (fun i => coord (A := A) i) where
  injective := fun _ _ h => h
  surjective := fun f => ⟨f, rfl⟩
  intertwines := fun _ => ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- **Non-vacuity of F2.**  The coordinate lenses on `Bool → Bool` satisfy
every hypothesis of F2: the three laws, a finite index type, and the
nonemptiness condition. -/
theorem coord_bool_satisfy_f2_hypotheses :
    (∀ i : Bool, (coord (A := fun _ : Bool => Bool) i).PutGet) ∧
    PairwiseIndep (fun i : Bool => coord (A := fun _ : Bool => Bool) i) ∧
    FamJointExt (fun i : Bool => coord (A := fun _ : Bool => Bool) i) ∧
    (∀ i : Bool, i ∈ [false, true]) ∧
    (Nonempty ((i : Bool) → (fun _ : Bool => Bool) i) → Nonempty ((_ : Bool) → Bool)) := by
  refine ⟨coord_putGet, coord_pairwiseIndep, coord_famJointExt, ?_, fun h => h⟩
  intro i
  cases i <;> simp

/-- Negative example for `IsPiDecomposition`: the two-field family on a record
with a ghost component. -/
theorem ghostFam_not_isPiDecomposition : ¬ IsPiDecomposition ghostFam :=
  fun h => famGet_ghostFam_not_injective h.injective

/-! ### Derived-law lemmas for families (proved)

Each lemma uses only the laws at the indices it talks about, and none needs
`DecidableEq ι` (the case split on index equality is classical).
-/

/-- **Derived law 1 (family).**  If `l i` satisfies `PutGet`, writing through
`l i` leaves every *other* view unchanged, and the family is jointly
extensional, then `l i` satisfies `GetPut`. -/
theorem getPut_of_putGet_pairwiseIndep_famJointExt
    {l : (i : ι) → Lens S (A i)} {i : ι}
    (hpg : (l i).PutGet) (hind : ∀ j, i ≠ j → PutIndep (l i) (l j))
    (hext : FamJointExt l) :
    (l i).GetPut := by
  intro s
  apply hext
  intro j
  exact Classical.byCases
    (fun h : i = j => h ▸ hpg s ((l i).get s))
    (fun h : i ≠ j => hind j h s ((l i).get s))

/-- **Derived law 2 (family).**  Under the same hypotheses as derived law 1,
`l i` satisfies `PutPut`. -/
theorem putPut_of_putGet_pairwiseIndep_famJointExt
    {l : (i : ι) → Lens S (A i)} {i : ι}
    (hpg : (l i).PutGet) (hind : ∀ j, i ≠ j → PutIndep (l i) (l j))
    (hext : FamJointExt l) :
    (l i).PutPut := by
  intro s a a'
  apply hext
  intro j
  exact Classical.byCases
    (fun h : i = j => h ▸ (hpg ((l i).put s a) a').trans (hpg s a').symm)
    (fun h : i ≠ j => (hind j h _ a').trans ((hind j h s a).trans (hind j h s a').symm))

/-- **Derived law 3 (family).**  For distinct indices `i ≠ j`: if `l i` and
`l j` satisfy `PutGet`, writing through either of them leaves every other view
unchanged, and the family is jointly extensional, then the puts of `l i` and
`l j` commute. -/
theorem putComm_of_putGet_pairwiseIndep_famJointExt
    {l : (i : ι) → Lens S (A i)} {i j : ι} (hij : i ≠ j)
    (hpi : (l i).PutGet) (hpj : (l j).PutGet)
    (hindi : ∀ k, i ≠ k → PutIndep (l i) (l k))
    (hindj : ∀ k, j ≠ k → PutIndep (l j) (l k))
    (hext : FamJointExt l) :
    PutComm (l i) (l j) := by
  intro s a b
  apply hext
  intro k
  refine Classical.byCases (fun hi : i = k => ?_) (fun hi : i ≠ k => ?_)
  · subst hi
    exact ((hindj i (fun h => hij h.symm) _ b).trans (hpi s a)).trans (hpi _ a).symm
  · refine Classical.byCases (fun hj : j = k => ?_) (fun hj : j ≠ k => ?_)
    · subst hj
      exact (hpj _ b).trans (((hindi j hi _ a).trans (hpj s b)).symm)
    · exact ((hindj k hj _ b).trans (hindi k hi s a)).trans
        (((hindi k hi _ a).trans (hindj k hj s b)).symm)

/-! ### F2 — indexed decomposition -/

/--
**F2 (indexed decomposition, finite index type).**  If every lens of the
family satisfies `PutGet`, the family is pairwise cross-independent and jointly
extensional, the index type is *finite* (enumerated by a list, duplicates
allowed) and the state type is nonempty whenever the product
`(i : ι) → A i` is, then the specific map `fun s i => (l i).get s` is a
bijection `S → (i : ι) → A i` under which each `(l i).put` is update of
coordinate `i`.

Finiteness of `ι` cannot be dropped: see
`Toy.Lens.evCoord_tight_finite_index`.  A caller holding `hS : Nonempty S`
passes `fun _ => hS`.
-/
theorem isPiDecomposition_of_putGet_pairwiseIndep_famJointExt_finite_imp_nonempty
    [DecidableEq ι] {l : (i : ι) → Lens S (A i)}
    (hpg : ∀ i, (l i).PutGet) (hind : PairwiseIndep l) (hext : FamJointExt l)
    (elems : List ι) (helems : ∀ i, i ∈ elems)
    (hS : Nonempty ((i : ι) → A i) → Nonempty S) :
    IsPiDecomposition l := by
  refine ⟨fun s t h => hext s t (fun i => congrFun h i), ?_, ?_⟩
  · -- surjective: write the coordinates listed in `elems` one after another
    intro f
    obtain ⟨s₀⟩ := hS ⟨f⟩
    suffices ∀ xs : List ι, ∃ s : S, ∀ i ∈ xs, (l i).get s = f i by
      obtain ⟨s, hs⟩ := this elems
      exact ⟨s, funext (fun i => hs i (helems i))⟩
    intro xs
    induction xs with
    | nil => exact ⟨s₀, fun _ h => nomatch h⟩
    | cons j rest ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨(l j).put s (f j), fun i hi => ?_⟩
      by_cases hij : i = j
      · subst hij
        exact hpg i s (f i)
      · cases hi with
        | head => exact absurd rfl hij
        | tail _ hmem => exact (hind j i (Ne.symm hij) s (f j)).trans (hs i hmem)
  · intro i
    refine ⟨fun _ => rfl, fun s a => funext fun j => ?_⟩
    show (l j).get ((l i).put s a) = update (famGet l s) i a j
    by_cases hji : j = i
    · subst hji
      rw [update_same]
      exact hpg j s a
    · rw [update_of_ne _ hji]
      exact hind i j (Ne.symm hji) s a

/--
**F2, exact form (finite index type).**  For a finite index type, the
conclusion of F2 holds if and only if the three laws hold and the state type
is nonempty whenever the product `(i : ι) → A i` is.
-/
theorem isPiDecomposition_iff_putGet_pairwiseIndep_famJointExt_imp_nonempty_of_finite
    [DecidableEq ι] {l : (i : ι) → Lens S (A i)}
    (elems : List ι) (helems : ∀ i, i ∈ elems) :
    IsPiDecomposition l ↔
      (∀ i, (l i).PutGet) ∧ PairwiseIndep l ∧ FamJointExt l ∧
        (Nonempty ((i : ι) → A i) → Nonempty S) := by
  constructor
  · intro h
    refine ⟨fun i s a => ?_, fun i j hij s a => ?_, fun s t hst => h.injective (funext hst),
      fun ⟨f⟩ => let ⟨s, _⟩ := h.surjective f; ⟨s⟩⟩
    · exact (congrFun ((h.intertwines i).put_eq s a) i).trans (update_same (famGet l s) i a)
    · exact (congrFun ((h.intertwines i).put_eq s a) j).trans
        (update_of_ne (famGet l s) (fun hji => hij hji.symm) a)
  · rintro ⟨hpg, hind, hext, hne⟩
    exact isPiDecomposition_of_putGet_pairwiseIndep_famJointExt_finite_imp_nonempty
      hpg hind hext elems helems hne

end Family

end Lens

end Toy
