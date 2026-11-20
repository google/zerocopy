import Toy.Sep.Heap
import Toy.Sep.Algebras

/-!
# Precision and the conjunction-distribution law

* In an arbitrary `SepStruct` (no laws) the distribution law
  `(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` (for all `P`, `Q`) holds **exactly** when `R`
  has unique frames (`UniqueFrame R`), not when `R` is precise.
* Precision implies the law under **right** cancellativity; the law implies
  precision under **left** cancellativity. Neither cancellativity hypothesis can be
  dropped, even in partial commutative monoids with unit (`OrAlg`, `Fork`).
* `Precise`, `UniqueFrame` and `ConjDistrib` all place `R` on the right of `*`.
* In the heap model (cancellative), `R` is precise iff the law holds for `R`.
* The imprecise assertions "exactly one cell, at some address" (`oneCell`) and
  "some cell is allocated" (`someCellAllocated`) violate the law.
-/

namespace Toy.Sep

open SepStruct

section Generic

variable {S : Type u} [SepStruct S]

/-- **Exact form of the distribution law (no algebraic laws).** In every
separation structure, `(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` holds for all `P`, `Q`
iff any two decompositions of a state whose right parts satisfy `R` have the same
left part. -/
theorem conjDistrib_iff_uniqueFrame (R : Assn S) : ConjDistrib R ↔ UniqueFrame R := by
  constructor
  · intro hd f₁ r₁ f₂ r₂ d₁ d₂ he hR₁ hR₂
    obtain ⟨f₃, _, _, _, ⟨hf₁, hf₂⟩, _⟩ :=
      hd (sing f₁) (sing f₂) (union f₁ r₁)
        ⟨f₁, r₁, d₁, rfl, rfl, hR₁⟩ ⟨f₂, r₂, d₂, he, rfl, hR₂⟩
    exact (hf₁ : f₃ = f₁).symm.trans hf₂
  · intro huf P Q h ⟨f₁, r₁, d₁, e₁, hP, hR₁⟩ ⟨f₂, r₂, d₂, e₂, hQ, hR₂⟩
    have hf : f₁ = f₂ := huf f₁ r₁ f₂ r₂ d₁ d₂ (e₁.symm.trans e₂) hR₁ hR₂
    subst hf
    exact ⟨f₁, r₁, d₁, e₁, ⟨hP, hQ⟩, hR₁⟩

/-- **Precise frames distribute, given right cancellativity.** If the separation
structure is right-cancellative and `R` is precise, then
`(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` for all `P`, `Q`. -/
theorem conjDistrib_of_precise_of_rightCancel (hrc : RightCancel S) {R : Assn S}
    (hp : Precise R) : ConjDistrib R := by
  refine (conjDistrib_iff_uniqueFrame R).2 fun f₁ r₁ f₂ r₂ d₁ d₂ he hR₁ hR₂ => ?_
  have hr := hp f₁ r₁ f₂ r₂ d₁ d₂ he hR₁ hR₂
  subst hr
  exact hrc f₁ f₂ r₁ d₁ d₂ he

/-- **Distributing frames are precise, given left cancellativity.** If the
separation structure is left-cancellative and
`(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` holds for all `P`, `Q`, then `R` is precise. -/
theorem precise_of_conjDistrib_of_leftCancel (hlc : LeftCancel S) {R : Assn S}
    (hd : ConjDistrib R) : Precise R := by
  have huf := (conjDistrib_iff_uniqueFrame R).1 hd
  intro f₁ r₁ f₂ r₂ d₁ d₂ he hR₁ hR₂
  have hf := huf f₁ r₁ f₂ r₂ d₁ d₂ he hR₁ hR₂
  subst hf
  exact hlc r₁ r₂ f₁ d₁ d₂ he

end Generic

/-! ## Derivable hypotheses (proved): in commutative structures the two
cancellation laws coincide -/

section Derivable

variable {S : Type u} [SepStruct S]

/-- With symmetric disjointness and commutative union, left cancellativity
implies right cancellativity. -/
theorem rightCancel_of_disjSymm_of_unionComm_of_leftCancel (hs : DisjSymm S) (hc : UnionComm S)
    (hl : LeftCancel S) : RightCancel S := by
  intro a b c hac hbc he
  have hca := hs _ _ hac
  have hcb := hs _ _ hbc
  exact hl a b c hca hcb ((hc c a hca).trans (he.trans (hc c b hcb).symm))

/-- With symmetric disjointness and commutative union, right cancellativity
implies left cancellativity. -/
theorem leftCancel_of_disjSymm_of_unionComm_of_rightCancel (hs : DisjSymm S) (hc : UnionComm S)
    (hr : RightCancel S) : LeftCancel S := by
  intro a b c hca hcb he
  have hac := hs _ _ hca
  have hbc := hs _ _ hcb
  exact hr a b c hac hbc ((hc a c hac).trans (he.trans (hc b c hbc).symm))

/-- With symmetric disjointness and commutative union, left and right
cancellativity are equivalent. -/
theorem leftCancel_iff_rightCancel_of_disjSymm_of_unionComm (hs : DisjSymm S)
    (hc : UnionComm S) : LeftCancel S ↔ RightCancel S :=
  ⟨rightCancel_of_disjSymm_of_unionComm_of_leftCancel hs hc,
    leftCancel_of_disjSymm_of_unionComm_of_rightCancel hs hc⟩

end Derivable

/-! Tightness of the hypotheses of `rightCancel_of_disjSymm_of_unionComm_of_leftCancel`
and `leftCancel_of_disjSymm_of_unionComm_of_rightCancel` (canonical form). Each
also refutes `LeftCancel S ↔ RightCancel S` for the structure in question. -/

/-- Everything disjoint, `a ∘ b = b` (right projection). -/
@[reducible] def projRightSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun _ b => b⟩

/-- Everything disjoint, `a ∘ b = a` (left projection). -/
@[reducible] def projLeftSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun a _ => a⟩

/-- Booleans under `||`, with `a ⊥ b` iff `b = true` (asymmetric disjointness). -/
@[reducible] def orDisjRightSepStruct : SepStruct Bool := ⟨fun _ y => y = true, fun x y => x || y⟩

/-- Booleans under `||`, with `a ⊥ b` iff `a = true` (asymmetric disjointness). -/
@[reducible] def orDisjLeftSepStruct : SepStruct Bool := ⟨fun x _ => x = true, fun x y => x || y⟩

/-- `UnionComm` cannot be dropped from `rightCancel_of_disjSymm_of_unionComm_of_leftCancel`. -/
theorem projRight_disjSymm_leftCancel_not_rightCancel :
    @DisjSymm Nat projRightSepStruct ∧ @LeftCancel Nat projRightSepStruct ∧
    ¬ @RightCancel Nat projRightSepStruct := by
  refine ⟨fun _ _ _ => trivial, fun _ _ _ _ _ he => he, fun h => ?_⟩
  have : (0 : Nat) = 1 := h 0 1 0 trivial trivial rfl
  cases this

/-- `DisjSymm` cannot be dropped from `rightCancel_of_disjSymm_of_unionComm_of_leftCancel`. -/
theorem orDisjRight_unionComm_leftCancel_not_rightCancel :
    @UnionComm Bool orDisjRightSepStruct ∧ @LeftCancel Bool orDisjRightSepStruct ∧
    ¬ @RightCancel Bool orDisjRightSepStruct := by
  refine ⟨fun a b _ => Bool.or_comm a b, fun a b _ ha hb _ => ?_, fun h => ?_⟩
  · have ha : a = true := ha
    have hb : b = true := hb
    rw [ha, hb]
  · have : false = true := h false true true rfl rfl rfl
    cases this

/-- `LeftCancel` cannot be dropped from
`rightCancel_of_disjSymm_of_unionComm_of_leftCancel` (the partial commutative
monoid `OrAlg`). -/
theorem orAlg_disjSymm_unionComm_not_rightCancel :
    DisjSymm OrAlg ∧ UnionComm OrAlg ∧ ¬ RightCancel OrAlg :=
  ⟨orAlg_isSepAlgebra.disjSymm, orAlg_isSepAlgebra.comm, orAlg_not_rightCancel⟩

/-- `UnionComm` cannot be dropped from `leftCancel_of_disjSymm_of_unionComm_of_rightCancel`. -/
theorem projLeft_disjSymm_rightCancel_not_leftCancel :
    @DisjSymm Nat projLeftSepStruct ∧ @RightCancel Nat projLeftSepStruct ∧
    ¬ @LeftCancel Nat projLeftSepStruct := by
  refine ⟨fun _ _ _ => trivial, fun _ _ _ _ _ he => he, fun h => ?_⟩
  have : (0 : Nat) = 1 := h 0 1 0 trivial trivial rfl
  cases this

/-- `DisjSymm` cannot be dropped from `leftCancel_of_disjSymm_of_unionComm_of_rightCancel`. -/
theorem orDisjLeft_unionComm_rightCancel_not_leftCancel :
    @UnionComm Bool orDisjLeftSepStruct ∧ @RightCancel Bool orDisjLeftSepStruct ∧
    ¬ @LeftCancel Bool orDisjLeftSepStruct := by
  refine ⟨fun a b _ => Bool.or_comm a b, fun a b _ ha hb _ => ?_, fun h => ?_⟩
  · have ha : a = true := ha
    have hb : b = true := hb
    rw [ha, hb]
  · have : false = true := h false true true rfl rfl rfl
    cases this

/-- `RightCancel` cannot be dropped from
`leftCancel_of_disjSymm_of_unionComm_of_rightCancel` (the partial commutative
monoid `OrAlg`). -/
theorem orAlg_disjSymm_unionComm_not_leftCancel :
    DisjSymm OrAlg ∧ UnionComm OrAlg ∧ ¬ LeftCancel OrAlg :=
  ⟨orAlg_isSepAlgebra.disjSymm, orAlg_isSepAlgebra.comm, orAlg_not_leftCancel⟩

/-- In the heap model, `Precise R` says exactly that every heap has at most one
subheap (`Heap.Sub`) satisfying `R`. -/
theorem heap_precise_iff_atMostOneSubheap {V : Type} (R : Assn (Heap V)) :
    Precise R ↔ ∀ h r₁ r₂ : Heap V, Heap.Sub r₁ h → Heap.Sub r₂ h → R r₁ → R r₂ → r₁ = r₂ := by
  constructor
  · intro hp h r₁ r₂ h1 h2 hR1 hR2
    obtain ⟨f₁, d₁, e₁⟩ := (Heap.exists_frame_iff_sub r₁ h).2 h1
    obtain ⟨f₂, d₂, e₂⟩ := (Heap.exists_frame_iff_sub r₂ h).2 h2
    exact hp f₁ r₁ f₂ r₂ d₁ d₂ (e₁.symm.trans e₂) hR1 hR2
  · intro hs f₁ r₁ f₂ r₂ d₁ d₂ he hR1 hR2
    exact hs (union f₁ r₁) r₁ r₂ ((Heap.exists_frame_iff_sub r₁ _).1 ⟨f₁, d₁, rfl⟩)
      ((Heap.exists_frame_iff_sub r₂ _).1 ⟨f₂, d₂, he⟩) hR1 hR2

/-- **Heap model: precision characterizes distribution.** For every assertion `R`
on finite heaps, `R` is precise (equivalently, by
`heap_precise_iff_atMostOneSubheap`, every heap has at most one subheap satisfying
`R`) iff `(P * R) ∧ (Q * R) ⊢ (P ∧ Q) * R` for all `P`, `Q`. -/
theorem heap_precise_iff_conjDistrib {V : Type} (R : Assn (Heap V)) :
    Precise R ↔ ConjDistrib R := by
  exact ⟨conjDistrib_of_precise_of_rightCancel (heap_rightCancel V),
    precise_of_conjDistrib_of_leftCancel (heap_leftCancel V)⟩

/-! ## Imprecise heap assertions (proved) -/

/-- "Exactly one cell is allocated, at some address, with some value":
`∃ k v. k ↦ v`. Imprecise. -/
def oneCell : Assn (Heap Nat) := fun h => ∃ k v, h = Heap.pt k v

/-- "Some cell is allocated" (the heap is nonempty): `∃ k. (k ↦ -) * true`.
Imprecise. -/
def someCellAllocated : Assn (Heap Nat) := fun h => ∃ k, h.val k ≠ none

theorem pt01_disj_pt12 : disj (Heap.pt 0 1 : Heap Nat) (Heap.pt 1 2) := by
  intro j; by_cases hj : j = 0 <;> simp [hj]

theorem pt12_disj_pt01 : disj (Heap.pt 1 2 : Heap Nat) (Heap.pt 0 1) :=
  heap_disjSymm Nat _ _ pt01_disj_pt12

theorem pt01_union_pt12_comm :
    union (Heap.pt 0 1 : Heap Nat) (Heap.pt 1 2) = union (Heap.pt 1 2) (Heap.pt 0 1) :=
  heap_unionComm Nat _ _ pt01_disj_pt12

theorem pt01_ne_pt12 : (Heap.pt 0 1 : Heap Nat) ≠ Heap.pt 1 2 := by
  intro h
  have := congrArg (fun x : Heap Nat => x.val 0) h
  simp at this

theorem oneCell_not_precise : ¬ Precise oneCell := by
  intro hp
  have := hp (Heap.pt 0 1) (Heap.pt 1 2) (Heap.pt 1 2) (Heap.pt 0 1)
    pt01_disj_pt12 pt12_disj_pt01 pt01_union_pt12_comm ⟨1, 2, rfl⟩ ⟨0, 1, rfl⟩
  exact pt01_ne_pt12 this.symm

/-- **The distribution law fails for `oneCell`**, with explicit witnesses:
`P = {0 ↦ 1}`, `Q = {1 ↦ 2}`, state `(0 ↦ 1) ∘ (1 ↦ 2)`. -/
theorem oneCell_conjDistrib_fails :
    sep (sing (Heap.pt 0 1)) oneCell (union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    sep (sing (Heap.pt 1 2)) oneCell (union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    ¬ sep (conj (sing (Heap.pt 0 1)) (sing (Heap.pt 1 2))) oneCell
        (union (Heap.pt 0 1) (Heap.pt 1 2)) := by
  refine ⟨⟨_, _, pt01_disj_pt12, rfl, rfl, ⟨1, 2, rfl⟩⟩,
    ⟨_, _, pt12_disj_pt01, pt01_union_pt12_comm, rfl, ⟨0, 1, rfl⟩⟩, ?_⟩
  rintro ⟨a, _, _, _, ⟨h1, h2⟩, _⟩
  exact pt01_ne_pt12 ((h1 : a = _).symm.trans (h2 : a = _))

theorem oneCell_not_conjDistrib : ¬ ConjDistrib oneCell := by
  intro hd
  obtain ⟨h1, h2, h3⟩ := oneCell_conjDistrib_fails
  exact h3 (hd _ _ _ h1 h2)

theorem someCellAllocated_not_precise : ¬ Precise someCellAllocated := by
  intro hp
  have := hp (Heap.pt 0 1) (Heap.pt 1 2) (Heap.pt 1 2) (Heap.pt 0 1)
    pt01_disj_pt12 pt12_disj_pt01 pt01_union_pt12_comm ⟨1, by simp⟩ ⟨0, by simp⟩
  exact pt01_ne_pt12 this.symm

/-- **The distribution law fails for "some cell is allocated"**, with the same
witnesses as for `oneCell`. -/
theorem someCellAllocated_conjDistrib_fails :
    sep (sing (Heap.pt 0 1)) someCellAllocated (union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    sep (sing (Heap.pt 1 2)) someCellAllocated (union (Heap.pt 0 1) (Heap.pt 1 2)) ∧
    ¬ sep (conj (sing (Heap.pt 0 1)) (sing (Heap.pt 1 2))) someCellAllocated
        (union (Heap.pt 0 1) (Heap.pt 1 2)) := by
  refine ⟨⟨_, _, pt01_disj_pt12, rfl, rfl, ⟨1, by simp⟩⟩,
    ⟨_, _, pt12_disj_pt01, pt01_union_pt12_comm, rfl, ⟨0, by simp⟩⟩, ?_⟩
  rintro ⟨a, _, _, _, ⟨h1, h2⟩, _⟩
  exact pt01_ne_pt12 ((h1 : a = _).symm.trans (h2 : a = _))

theorem someCellAllocated_not_conjDistrib : ¬ ConjDistrib someCellAllocated := by
  intro hd
  obtain ⟨h1, h2, h3⟩ := someCellAllocated_conjDistrib_fails
  exact h3 (hd _ _ _ h1 h2)

/-! ## Tightness counterexamples in canonical form (proved) -/

/-- **Tightness of `Precise` in `conjDistrib_of_precise_of_rightCancel`**: the heap
model is right-cancellative, yet the distribution law fails for the imprecise
`oneCell`. -/
theorem heap_rightCancel_and_oneCell_not_conjDistrib :
    RightCancel (Heap Nat) ∧ ¬ ConjDistrib oneCell :=
  ⟨heap_rightCancel Nat, oneCell_not_conjDistrib⟩

/-- `{true}` is precise in `OrAlg`. -/
theorem orAlg_true_precise : Precise (sing (⟨true⟩ : OrAlg)) := by
  intro _ r₁ _ r₂ _ _ _ h1 h2
  exact (h1 : r₁ = _).trans (h2 : r₂ = _).symm

/-- **Tightness of `RightCancel` in `conjDistrib_of_precise_of_rightCancel`**: in
the non-cancellative partial commutative monoid `OrAlg`, the frame `{true}` is precise but
the distribution law fails (`P = {false}`, `Q = {true}`, state `true`). -/
theorem orAlg_true_precise_and_not_conjDistrib :
    Precise (sing (⟨true⟩ : OrAlg)) ∧ ¬ ConjDistrib (sing (⟨true⟩ : OrAlg)) := by
  refine ⟨orAlg_true_precise, ?_⟩
  intro hd
  have h := hd (sing ⟨false⟩) (sing ⟨true⟩) ⟨true⟩
    ⟨⟨false⟩, ⟨true⟩, trivial, rfl, rfl, rfl⟩ ⟨⟨true⟩, ⟨true⟩, trivial, rfl, rfl, rfl⟩
  obtain ⟨a, _, _, _, ⟨h1, h2⟩, _⟩ := h
  have := (h1 : a = _).symm.trans (h2 : a = _)
  cases this

/-- **Tightness of `ConjDistrib` in `precise_of_conjDistrib_of_leftCancel`**: the
heap model is left-cancellative, yet `oneCell` is not precise. -/
theorem heap_leftCancel_and_oneCell_not_precise :
    LeftCancel (Heap Nat) ∧ ¬ Precise oneCell :=
  ⟨heap_leftCancel Nat, oneCell_not_precise⟩

instance : DecidablePred forkR := fun x => inferInstanceAs (Decidable (x = .a ∨ x = .b))

theorem forkR_uniqueFrame : UniqueFrame forkR := by
  intro f₁ r₁ f₂ r₂
  cases f₁ <;> cases r₁ <;> cases f₂ <;> cases r₂ <;> decide

theorem forkR_conjDistrib : ConjDistrib forkR := by
  intro P Q h ⟨f₁, r₁, d₁, e₁, hP, hR₁⟩ ⟨f₂, r₂, d₂, e₂, hQ, hR₂⟩
  have hf : f₁ = f₂ := forkR_uniqueFrame f₁ r₁ f₂ r₂ d₁ d₂ (e₁.symm.trans e₂) hR₁ hR₂
  subst hf
  exact ⟨f₁, r₁, d₁, e₁, ⟨hP, hQ⟩, hR₁⟩

theorem forkR_not_precise : ¬ Precise forkR := by
  intro hp
  have := hp .p .a .p .b (by decide) (by decide) (by decide) (Or.inl rfl) (Or.inr rfl)
  cases this

/-- **Tightness of `LeftCancel` in `precise_of_conjDistrib_of_leftCancel`**: in the
non-cancellative partial commutative monoid `Fork`, the frame `forkR = {a, b}` satisfies
the distribution law but is not precise (`p ∘ a = p ∘ b`). -/
theorem forkR_conjDistrib_and_not_precise :
    ConjDistrib forkR ∧ ¬ Precise forkR :=
  ⟨forkR_conjDistrib, forkR_not_precise⟩

end Toy.Sep
