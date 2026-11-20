/-
# Small models for the diagonal arguments

Small models for the abstract recursion theorem and for Lawvere's theorem: one model where all
hypotheses hold (non-vacuity), and one model per hypothesis where the other hypotheses hold and
the conclusion fails.

These models are *not* computability models. A model of the recursion theorem's hypotheses
with genuinely rich admissible transformers would be an acceptable numbering of the partial
computable functions, which is not built here.
-/
import ToyRice.Recursion

namespace Toy.Rice.Models

/-- Codes and behaviours `Bool`, identity semantics, admissible class `A`. -/
abbrev boolSys (A : (Bool → Bool) → Prop) : System := ⟨Bool, Bool, id, A⟩

theorem not_has_no_fixpoint (c : Bool) : (!c) ≠ c := by cases c <;> decide

theorem boolSys_not_fixpointPrinciple_of_not {A : (Bool → Bool) → Prop} (h : A not) :
    ¬ FixpointPrinciple (boolSys A) := by
  intro hfix
  obtain ⟨c, hc⟩ := hfix not h
  exact not_has_no_fixpoint c hc

/-- The conclusion of `diagonalFixedPoint_of_represents_diagonal_precompClosed`, as a
predicate. -/
def DiagConclusion (S : System) (app : S.Code → S.Code → Option S.Code) (d : S.Code → S.Code) :
    Prop :=
  ∀ f : S.Code → S.Code, S.Adm f →
    (∃ e, ∀ x, app e x = some (f (d x))) ∧
    (∀ e, (∀ x, app e x = some (f (d x))) → S.sem (f (d e)) = S.sem (d e))

theorem fixpointPrinciple_of_diagConclusion {S : System} {app : S.Code → S.Code → Option S.Code}
    {d : S.Code → S.Code} (h : DiagConclusion S app d) : FixpointPrinciple S := by
  intro f hf
  obtain ⟨⟨e, he⟩, hw⟩ := h f hf
  exact ⟨d e, hw e he⟩

/-- Admissible: the identity and the constant `false`. -/
def adm0 (f : Bool → Bool) : Prop := f = id ∨ f = fun _ => false

/-- Code `true` computes the identity; code `false` computes the constant `false`. -/
def app0 : Bool → Bool → Option Bool
  | true, x => some x
  | false, _ => some false

/-! ## Recursion theorem: non-vacuity model

Codes `(b, n)`: a behaviour bit `b` and a tag `n`; the semantics forgets the tag. Admissible:
the constants and the maps `x ↦ (x.1, m)` (keep the behaviour, set the tag). A code `(b, 2m)`
computes the constant `(b, m)`; a code `(b, 2m + 1)` computes `x ↦ (x.1, m)`. The diagonal
`d x = (x.1, x.2 + 1)` changes every code, is not admissible, and yet precomposition with it
preserves admissibility. The fixed points produced are semantic, not literal. -/

/-- Admissible transformers of the tag model. -/
def tagAdm (f : Bool × Nat → Bool × Nat) : Prop :=
  (∃ k, f = fun _ => k) ∨ (∃ m, f = fun x => (x.1, m))

/-- The tag model. -/
abbrev tagSys : System := ⟨Bool × Nat, Bool, Prod.fst, tagAdm⟩

/-- Application in the tag model. -/
def tagApp (e x : Bool × Nat) : Option (Bool × Nat) :=
  if e.2 % 2 = 0 then some (e.1, e.2 / 2) else some (x.1, e.2 / 2)

/-- The diagonal transformer of the tag model. -/
def tagDiag (x : Bool × Nat) : Bool × Nat := (x.1, x.2 + 1)

/-- All hypotheses of `diagonalFixedPoint_of_represents_diagonal_precompClosed` hold in the tag
model, with a diagonal `tagDiag` that moves every code and is not itself admissible (so the
textbook hypothesis "the diagonal is admissible" fails while the theorem applies); constants are
admissible and admissible maps compose. For the admissible `f x = (x.1, 0)` the code `e = (true, 1)`
computes `f ∘ tagDiag`, and `f (tagDiag e) ≠ tagDiag e`: the fixed point is semantic only. -/
theorem kleene_nonvacuous :
    Represents tagSys tagApp ∧ IsDiagonal tagSys tagApp tagDiag ∧
      PrecompClosed tagSys tagDiag ∧ ¬ tagSys.Adm tagDiag ∧ (∀ x, tagDiag x ≠ x) ∧
      ConstClosed tagSys ∧ CompClosed tagSys ∧
      (tagSys.Adm (fun x => (x.1, 0)) ∧
        (∀ x, tagApp (true, 1) x = some ((fun x : Bool × Nat => (x.1, 0)) (tagDiag x))) ∧
        (fun x : Bool × Nat => (x.1, 0)) (tagDiag (true, 1)) ≠ tagDiag (true, 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨Or.inr ⟨0, rfl⟩, fun x => ?_, ?_⟩⟩
  · rintro f (⟨⟨kb, km⟩, rfl⟩ | ⟨m, rfl⟩)
    · refine ⟨(kb, 2 * km), fun x => ?_⟩
      have h1 : 2 * km % 2 = 0 := by omega
      have h2 : 2 * km / 2 = km := by omega
      simp [tagApp, h1, h2]
    · refine ⟨(false, 2 * m + 1), fun x => ?_⟩
      have h1 : (2 * m + 1) % 2 = 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      simp [tagApp, h1, h2]
  · rintro ⟨b, n⟩ z h
    show b = z.1
    unfold tagApp at h
    split at h <;> (injection h with h; subst h; rfl)
  · rintro f (⟨k, rfl⟩ | ⟨m, rfl⟩)
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨m, rfl⟩
  · rintro (⟨k, hk⟩ | ⟨m, hm⟩)
    · have h1 := congrFun hk (true, 0)
      have h2 := congrFun hk (false, 0)
      have h3 : ((true, 1) : Bool × Nat) = (false, 1) := h1.trans h2.symm
      cases h3
    · have h1 := congrFun hm (true, 0)
      have h2 := congrFun hm (true, 1)
      simp [tagDiag] at h1 h2
      omega
  · rintro ⟨b, n⟩ h
    have : n + 1 = n := congrArg Prod.snd h
    omega
  · intro k; exact Or.inl ⟨k, rfl⟩
  · rintro f g (⟨k, rfl⟩ | ⟨m, rfl⟩) (⟨k', rfl⟩ | ⟨m', rfl⟩)
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inl ⟨(k'.1, m), rfl⟩
    · exact Or.inr ⟨m, rfl⟩
  · simp [tagApp, tagDiag]
  · simp [tagDiag]

/-- A degenerate two-element instance (`d = id`, identity semantics), kept as an example: all
hypotheses hold, but `PrecompClosed S id` holds in every system, so it tests little. -/
theorem kleene_nonvacuous_trivialDiagonal :
    Represents (boolSys adm0) app0 ∧ IsDiagonal (boolSys adm0) app0 id ∧
      PrecompClosed (boolSys adm0) id := by
  refine ⟨?_, ?_, fun f hf => hf⟩
  · intro f hf
    rcases hf with rfl | rfl
    · exact ⟨true, fun _ => rfl⟩
    · exact ⟨false, fun _ => rfl⟩
  · intro x z h
    cases x <;> simp [app0] at h <;> subst h <;> rfl

/-! ## Recursion theorem: closure under precomposition is needed -/

/-- Admissible: Boolean negation and the constant `false`. -/
def adm1 (f : Bool → Bool) : Prop := f = not ∨ f = fun _ => false

def app1 : Bool → Bool → Option Bool
  | true, x => some (!x)
  | false, _ => some false

/-- With `d = const false`: representability and the diagonal property hold, but
precomposition with `d` does not preserve admissibility, and the conclusion fails (indeed the
fixpoint principle fails). -/
theorem kleene_tight_precompClosed :
    Represents (boolSys adm1) app1 ∧ IsDiagonal (boolSys adm1) app1 (fun _ => false) ∧
      ¬ DiagConclusion (boolSys adm1) app1 (fun _ => false) := by
  refine ⟨?_, ?_, fun h => boolSys_not_fixpointPrinciple_of_not (Or.inl rfl)
    (fixpointPrinciple_of_diagConclusion h)⟩
  · intro f hf
    rcases hf with rfl | rfl
    · exact ⟨true, fun _ => rfl⟩
    · exact ⟨false, fun _ => rfl⟩
  · intro x z h
    cases x <;> simp [app1] at h <;> subst h <;> rfl

theorem adm1_not_precompClosed : ¬ PrecompClosed (boolSys adm1) (fun _ => false) := by
  intro h
  rcases h not (Or.inl rfl) with h1 | h1
  · have := congrFun h1 true; exact absurd this (by decide)
  · have := congrFun h1 true; exact absurd this (by decide)

theorem adm1_not_compClosed : ¬ CompClosed (boolSys adm1) := fun h =>
  adm1_not_precompClosed (precompClosed_of_compClosed_adm h (Or.inr rfl))

/-! ## Recursion theorem: representability is needed -/

/-- Every transformer admissible; no code ever halts. -/
def adm2 (_ : Bool → Bool) : Prop := True

def app2 : Bool → Bool → Option Bool := fun _ _ => none

/-- With `d = id`: the diagonal property holds vacuously and precomposition preserves
admissibility, but no admissible transformer is computed by a code, and the fixpoint principle
fails. -/
theorem kleene_tight_represents :
    IsDiagonal (boolSys adm2) app2 id ∧ PrecompClosed (boolSys adm2) id ∧
      ¬ DiagConclusion (boolSys adm2) app2 id :=
  ⟨fun _ _ h => by simp [app2] at h, fun _ _ => trivial,
    fun h => boolSys_not_fixpointPrinciple_of_not trivial (fixpointPrinciple_of_diagConclusion h)⟩

theorem app2_not_represents : ¬ Represents (boolSys adm2) app2 := by
  intro h
  obtain ⟨e, he⟩ := h id trivial
  have := he true
  simp [app2] at this

/-! ## Recursion theorem: the diagonal property is needed -/

/-- Admissible: the identity and Boolean negation. -/
def adm3 (f : Bool → Bool) : Prop := f = id ∨ f = not

def app3 : Bool → Bool → Option Bool
  | true, x => some (!x)
  | false, x => some x

/-- With `d = id`: representability holds and precomposition preserves admissibility, but
`id` is not diagonal for `app3`, and the fixpoint principle fails. -/
theorem kleene_tight_diagonal :
    Represents (boolSys adm3) app3 ∧ PrecompClosed (boolSys adm3) id ∧
      ¬ DiagConclusion (boolSys adm3) app3 id := by
  refine ⟨?_, fun f hf => hf, fun h => boolSys_not_fixpointPrinciple_of_not (Or.inr rfl)
    (fixpointPrinciple_of_diagConclusion h)⟩
  intro f hf
  rcases hf with rfl | rfl
  · exact ⟨false, fun _ => rfl⟩
  · exact ⟨true, fun _ => rfl⟩

theorem adm3_compClosed : CompClosed (boolSys adm3) := by
  intro f g hf hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl
  · left; funext x; cases x <;> rfl

/-- In this model no transformer `d` with admissible precompositions is diagonal (by the
recursion theorem). -/
theorem adm3_no_diagonal (d : Bool → Bool) (hpre : PrecompClosed (boolSys adm3) d) :
    ¬ IsDiagonal (boolSys adm3) app3 d := fun hd =>
  boolSys_not_fixpointPrinciple_of_not (Or.inr rfl)
    (fixpointPrinciple_of_represents_diagonal_precompClosed app3 d kleene_tight_diagonal.1 hd
      hpre)

theorem id_not_diagonal_app3 : ¬ IsDiagonal (boolSys adm3) app3 id := by
  intro h
  have := h true false rfl
  exact Bool.noConfusion this

/-! ## Lawvere's theorem -/

/-- Constant maps `Bool → Bool`. -/
def IsConst (g : Bool → Bool) : Prop := ∃ k, g = fun _ => k

/-- `phiConst a` is the constant map with value `a`. -/
def phiConst (a _ : Bool) : Bool := a

/-- `phiTrue` represents only the constant-`true` map. -/
def phiTrue (_ _ : Unit) : Bool := true

theorem phiConst_represents_const : ∀ g, IsConst g → ∃ a, ∀ x, phiConst a x = g x := by
  rintro g ⟨k, rfl⟩
  exact ⟨k, fun _ => rfl⟩

/-- The conclusion of `lawvere_fixedPoint_of_represents_diagonal`, as a predicate. -/
def LawvereConclusion {A : Type} {Y : Type} (φ : A → A → Y) (t : Y → Y) : Prop :=
  (∃ a, ∀ x, φ a x = t (φ x x)) ∧ (∀ a, (∀ x, φ a x = t (φ x x)) → t (φ a a) = φ a a)

/-- Non-vacuity of `lawvere_fixedPoint_of_represents_diagonal` with a two-element `Y`:
`phiConst` represents the constant maps, and the diagonal of `t = const true` is constant. -/
theorem lawvere_nonvacuous :
    (∀ g, IsConst g → ∃ a, ∀ x, phiConst a x = g x) ∧
      IsConst (fun x => (fun _ : Bool => true) (phiConst x x)) :=
  ⟨phiConst_represents_const, ⟨true, rfl⟩⟩

/-- Representability is needed: with the class of all maps, the diagonal condition holds
trivially, `phiTrue` does not represent every map, and the conclusion fails for negation. -/
theorem lawvere_tight_represents :
    (fun _ : Unit → Bool => True) (fun x => !(phiTrue x x)) ∧
      ¬ (∀ g : Unit → Bool, (fun _ => True) g → ∃ a, ∀ x, phiTrue a x = g x) ∧
      ¬ LawvereConclusion phiTrue not := by
  refine ⟨trivial, ?_, fun ⟨⟨a, ha⟩, _⟩ => Bool.noConfusion (ha ())⟩
  intro h
  obtain ⟨a, ha⟩ := h (fun _ => false) trivial
  exact Bool.noConfusion (ha ())

/-- The diagonal condition is needed: `phiConst` represents all constant maps, the diagonal of
negation, `x ↦ !x`, is not constant, and the conclusion fails for negation. -/
theorem lawvere_tight_diagonal :
    (∀ g, IsConst g → ∃ a, ∀ x, phiConst a x = g x) ∧
      ¬ IsConst (fun x => !(phiConst x x)) ∧ ¬ LawvereConclusion phiConst not := by
  refine ⟨phiConst_represents_const, ?_, fun ⟨⟨a, ha⟩, _⟩ => ?_⟩
  · rintro ⟨k, hk⟩
    have h1 := congrFun hk true
    have h2 := congrFun hk false
    simp [phiConst] at h1 h2
    rw [h2] at h1
    exact Bool.noConfusion h1
  · have := ha a
    simp [phiConst] at this

end Toy.Rice.Models
