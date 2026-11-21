/-
Conservativity does not imply the expansion property: a direct countermodel
built from a back-and-forth argument for a single unary predicate and Cantor's
diagonal argument (no compactness).
-/
import Toy.Extension.Axiomatic

namespace Toy.Extension

/-! ### Back-and-forth for one unary predicate -/

/-- `p` and its complement are both infinite: no finite tuple exhausts either. -/
def BothInfinite {β : Type} (p : β → Prop) : Prop :=
  ∀ (n : Nat) (b : Fin n → β), (∃ x, p x ∧ ∀ i, x ≠ b i) ∧ (∃ x, ¬ p x ∧ ∀ i, x ≠ b i)

/-- Two tuples have the same equality pattern and the same `P`-pattern. -/
def SameType {α β : Type} (p : α → Prop) (q : β → Prop) {n : Nat}
    (a : Fin n → α) (b : Fin n → β) : Prop :=
  (∀ i j, a i = a j ↔ b i = b j) ∧ ∀ i, (p (a i) ↔ q (b i))

section BackAndForth

variable {α β : Type} {p : α → Prop} {q : β → Prop}

theorem SameType.symm {n : Nat} {a : Fin n → α} {b : Fin n → β} (h : SameType p q a b) :
    SameType q p b a :=
  ⟨fun i j => (h.1 i j).symm, fun i => (h.2 i).symm⟩

theorem fin_succ_cases {n : Nat} {P : Fin (n + 1) → Prop} (h0 : P ⟨0, Nat.succ_pos n⟩)
    (hs : ∀ i : Fin n, P i.succ) : ∀ j, P j
  | ⟨0, _⟩ => h0
  | ⟨k + 1, hk⟩ => hs ⟨k, Nat.lt_of_succ_lt_succ hk⟩

/-- One step of the back-and-forth: any new element on one side can be matched. -/
theorem SameType.extend (hq : BothInfinite q) {n : Nat} {a : Fin n → α} {b : Fin n → β}
    (h : SameType p q a b) (x : α) : ∃ y, SameType p q (scons x a) (scons y b) := by
  classical
  by_cases hx : ∃ i, x = a i
  · obtain ⟨i, rfl⟩ := hx
    refine ⟨b i, ?_, ?_⟩
    · refine fin_succ_cases ?_ ?_
      · refine fin_succ_cases ?_ ?_
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
        · intro k; exact h.1 i k
      · intro j
        refine fin_succ_cases ?_ ?_
        · exact h.1 j i
        · intro k; exact h.1 j k
    · refine fin_succ_cases ?_ ?_
      · exact h.2 i
      · intro j; exact h.2 j
  · have hfresh : ∃ y, (p x ↔ q y) ∧ ∀ i, y ≠ b i := by
      by_cases hpx : p x
      · obtain ⟨y, hy, hyb⟩ := (hq n b).1
        exact ⟨y, ⟨fun _ => hy, fun _ => hpx⟩, hyb⟩
      · obtain ⟨y, hy, hyb⟩ := (hq n b).2
        exact ⟨y, ⟨fun h' => absurd h' hpx, fun h' => absurd h' hy⟩, hyb⟩
    obtain ⟨y, hpy, hyb⟩ := hfresh
    refine ⟨y, ?_, ?_⟩
    · refine fin_succ_cases ?_ ?_
      · refine fin_succ_cases ?_ ?_
        · exact ⟨fun _ => rfl, fun _ => rfl⟩
        · intro k
          exact ⟨fun e => absurd ⟨k, e⟩ hx, fun e => absurd e (hyb k)⟩
      · intro j
        refine fin_succ_cases ?_ ?_
        · exact ⟨fun e => absurd ⟨j, e.symm⟩ hx, fun e => absurd e.symm (hyb j)⟩
        · intro k; exact h.1 j k
    · refine fin_succ_cases ?_ ?_
      · exact hpy
      · intro j; exact h.2 j

/-- Terms of `{P}` are variables. -/
theorem term_LP_var {n : Nat} : ∀ t : Term LP n, ∃ i, t = .var i
  | .var i => ⟨i, rfl⟩
  | .app f _ => f.elim

/-- Back-and-forth lemma: tuples of the same type satisfy the same formulas,
when both structures have infinite `P` and infinite complement. -/
theorem sat_iff_of_sameType (hp : BothInfinite p) (hq : BothInfinite q) {n : Nat}
    (φ : Formula LP n) : ∀ (a : Fin n → α) (b : Fin n → β), SameType p q a b →
      (Sat (pStr p) a φ ↔ Sat (pStr q) b φ) := by
  induction φ with
  | eq s t =>
    intro a b h
    obtain ⟨i, rfl⟩ := term_LP_var s
    obtain ⟨j, rfl⟩ := term_LP_var t
    exact h.1 i j
  | rel r ts =>
    intro a b h
    obtain ⟨i, hi⟩ := term_LP_var (ts ⟨0, Nat.zero_lt_one⟩)
    show p ((ts ⟨0, Nat.zero_lt_one⟩).eval (pStr p) a) ↔ q ((ts ⟨0, Nat.zero_lt_one⟩).eval (pStr q) b)
    rw [hi]
    exact h.2 i
  | falsum => intro _ _ _; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro a b h
    exact imp_congr (ihφ a b h) (ihψ a b h)
  | and φ ψ ihφ ihψ =>
    intro a b h
    exact and_congr (ihφ a b h) (ihψ a b h)
  | or φ ψ ihφ ihψ =>
    intro a b h
    exact or_congr (ihφ a b h) (ihψ a b h)
  | all φ ih =>
    intro a b h
    constructor
    · intro hall y
      obtain ⟨x, hxy⟩ := h.symm.extend hp y
      exact (ih _ _ hxy.symm).1 (hall x)
    · intro hall x
      obtain ⟨y, hxy⟩ := h.extend hq x
      exact (ih _ _ hxy).2 (hall y)
  | ex φ ih =>
    intro a b h
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, hxy⟩ := h.extend hq x
      exact ⟨y, (ih _ _ hxy).1 hx⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hxy⟩ := h.symm.extend hp y
      exact ⟨x, (ih _ _ hxy.symm).2 hy⟩

/-- Structures for `{P}` whose `P` and complement are both infinite satisfy the
same sentences (elementary equivalence; classical, here by back-and-forth). -/
theorem models_iff_of_bothInfinite (hp : BothInfinite p) (hq : BothInfinite q)
    (φ : Sentence LP) : (pStr p).Models φ ↔ (pStr q).Models φ :=
  sat_iff_of_sameType hp hq φ noVars noVars ⟨fun i => i.elim0, fun i => i.elim0⟩

end BackAndForth

/-! ### Two elementarily equivalent structures of different shapes -/

/-- A finite sum used as an upper bound. -/
def finSum : {n : Nat} → (Fin n → Nat) → Nat
  | 0, _ => 0
  | _ + 1, f => f ⟨0, Nat.succ_pos _⟩ + finSum (fun i => f i.succ)

theorem le_finSum : ∀ {n : Nat} (f : Fin n → Nat) (i : Fin n), f i ≤ finSum f
  | 0, _, i => i.elim0
  | _ + 1, _, ⟨0, _⟩ => Nat.le_add_right _ _
  | _ + 1, f, ⟨k + 1, hk⟩ =>
    Nat.le_trans (le_finSum (fun i => f i.succ) ⟨k, Nat.lt_of_succ_lt_succ hk⟩) (Nat.le_add_left _ _)

/-- `P` on `ℕ ⊕ ℕ`: the left summand. -/
def pN (x : Nat ⊕ Nat) : Prop := x.isLeft = true

/-- `P` on `ℕ ⊕ (ℕ → Bool)`: the left summand (countable), whose complement
`ℕ → Bool` is uncountable. -/
def pM (x : Nat ⊕ (Nat → Bool)) : Prop := x.isLeft = true

/-- The structure `N₀ = (ℕ ⊕ ℕ, P = left)`. -/
def N0 : Str LP (Nat ⊕ Nat) := pStr pN

/-- The structure `M₀ = (ℕ ⊕ (ℕ → Bool), P = left)`. -/
def M0 : Str LP (Nat ⊕ (Nat → Bool)) := pStr pM

theorem bothInfinite_pN : BothInfinite pN := by
  intro n b
  let code : Nat ⊕ Nat → Nat := fun x => Sum.elim id id x
  have hlt : ∀ i, code (b i) < finSum (fun i => code (b i)) + 1 :=
    fun i => Nat.lt_succ_of_le (le_finSum (fun i => code (b i)) i)
  refine ⟨⟨.inl (finSum (fun i => code (b i)) + 1), rfl, fun i e => ?_⟩,
          ⟨.inr (finSum (fun i => code (b i)) + 1), fun h => Bool.noConfusion h, fun i e => ?_⟩⟩
  · have := hlt i; rw [← e] at this; exact Nat.lt_irrefl _ this
  · have := hlt i; rw [← e] at this; exact Nat.lt_irrefl _ this

theorem bothInfinite_pM : BothInfinite pM := by
  intro n b
  let code : Nat ⊕ (Nat → Bool) → Nat := fun x => Sum.elim id (fun _ => 0) x
  have hlt : ∀ i, code (b i) < finSum (fun i => code (b i)) + 1 :=
    fun i => Nat.lt_succ_of_le (le_finSum (fun i => code (b i)) i)
  let getR : Nat ⊕ (Nat → Bool) → (Nat → Bool) := fun x => Sum.elim (fun _ _ => false) id x
  let g : Nat → Bool := fun k => if hk : k < n then !(getR (b ⟨k, hk⟩) k) else false
  refine ⟨⟨.inl (finSum (fun i => code (b i)) + 1), rfl, fun i e => ?_⟩,
          ⟨.inr g, fun h => Bool.noConfusion h, fun i e => ?_⟩⟩
  · have := hlt i; rw [← e] at this; exact Nat.lt_irrefl _ this
  · have hgi : g i.val = !(getR (b i) i.val) := dite_eq_left i.isLt
    rw [← e] at hgi
    have hgi' : g i.val = !(g i.val) := hgi
    generalize g i.val = c at hgi'
    cases c <;> exact absurd hgi' (by decide)

/-! ### The injection axioms and the countermodel -/

/-- `f t` for the fresh unary function symbol `f` of `LP.addFn 1`. -/
def tF {n : Nat} (t : Term (LP.addFn 1) n) : Term (LP.addFn 1) n :=
  .app (none : (LP.addFn 1).Fn) (fun _ => t)

/-- The atom `P t` over `LP.addFn 1`. -/
def atomP {n : Nat} (t : Term (LP.addFn 1) n) : Formula (LP.addFn 1) n :=
  .rel PRel.P (fun _ => t)

/-- `∀ x, ¬ P x → P (f x)`. -/
def injAx1 : Sentence (LP.addFn 1) :=
  .all (.imp (atomP (.var 0)).not (atomP (tF (.var 0))))

/-- `∀ x y, ¬ P x → ¬ P y → f x = f y → x = y`. -/
def injAx2 : Sentence (LP.addFn 1) :=
  .all (.all (.imp (atomP (.var 1)).not (.imp (atomP (.var 0)).not
    (.imp (.eq (tF (.var 1)) (tF (.var 0))) (.eq (.var 1) (.var 0))))))

/-- `T' = Th(N₀) + "f injects the complement of P into P"`. -/
def injTheory : Theory (LP.addFn 1) :=
  ((Theory.th N0).map (SigHom.inclFn LP 1)).union (Theory.ofList [injAx1, injAx2])

/-- The expansion of `N₀` by `f (inl n) = f (inr n) = inl n`. -/
def N0f : Str (LP.addFn 1) (Nat ⊕ Nat) :=
  N0.withFn (fun args => .inl (Sum.elim id id (args ⟨0, Nat.zero_lt_one⟩)))

theorem N0f_models_injTheory : N0f.ModelsTh injTheory := by
  rintro φ (hφ | hφ)
  · exact (modelsTh_map (SigHom.inclFn LP 1) N0f _).2 (modelsTh_th N0) φ hφ
  · cases hφ with
    | head => intro _ _; rfl
    | tail _ h =>
      cases h with
      | head =>
        intro x y hx hy hxy
        cases x with
        | inl _ => exact absurd rfl hx
        | inr m =>
          cases y with
          | inl _ => exact absurd rfl hy
          | inr k =>
            have : m = k := Sum.inl.inj hxy
            show (Sum.inr m : Nat ⊕ Nat) = Sum.inr k
            rw [this]
      | tail _ h => cases h

/-- Cantor: there is no injection `(ℕ → Bool) → ℕ`. -/
theorem cantor_no_injection (h : (Nat → Bool) → Nat)
    (hinj : ∀ g₁ g₂, h g₁ = h g₂ → g₁ = g₂) : False := by
  have key : ∃ k : Nat → (Nat → Bool), ∀ g, k (h g) = g := by
    classical
    refine ⟨fun n => if hn : ∃ g, h g = n then Classical.choose hn else fun _ => false, ?_⟩
    intro g
    have hex : ∃ g', h g' = h g := ⟨g, rfl⟩
    show (if hn : ∃ g', h g' = h g then Classical.choose hn else fun _ => false) = g
    rw [dite_eq_left hex]
    exact hinj _ _ (Classical.choose_spec hex)
  obtain ⟨k, hk⟩ := key
  have hd : k (h (fun i => !(k i i))) (h (fun i => !(k i i))) =
      !(k (h (fun i => !(k i i))) (h (fun i => !(k i i)))) :=
    congrFun (hk (fun i => !(k i i))) (h (fun i => !(k i i)))
  revert hd
  cases k (h (fun i => !(k i i))) (h (fun i => !(k i i))) <;> decide

/-- `M₀` is a model of `Th(N₀)` (elementary equivalence by back-and-forth). -/
theorem M0_models_thN0 : M0.ModelsTh (Theory.th N0) :=
  fun φ hφ => (models_iff_of_bothInfinite bothInfinite_pN bothInfinite_pM φ).1 hφ

/-- `M₀` has no expansion to a model of `injTheory` (Cantor). -/
theorem M0_no_expansion :
    ¬ ∃ S' : Str (LP.addFn 1) (Nat ⊕ (Nat → Bool)),
        S'.reduct (SigHom.inclFn LP 1) = M0 ∧ S'.ModelsTh injTheory := by
  rintro ⟨S', hred, hS'⟩
  have hP : ∀ x, S'.rel PRel.P (fun _ => x) ↔ pM x := by
    intro x
    have := congrArg (fun S : Str LP _ => S.rel PRel.P (fun _ => x)) hred
    exact Iff.of_eq this
  let F : Nat ⊕ (Nat → Bool) → Nat ⊕ (Nat → Bool) := fun x => S'.fn none (fun _ => x)
  have h1 : ∀ x, ¬ S'.rel PRel.P (fun _ => x) → S'.rel PRel.P (fun _ => F x) :=
    fun x => hS' injAx1 (Or.inr (List.Mem.head _)) x
  have h2 : ∀ x y, ¬ S'.rel PRel.P (fun _ => x) → ¬ S'.rel PRel.P (fun _ => y) →
      F x = F y → x = y :=
    fun x y => hS' injAx2 (Or.inr (List.Mem.tail _ (List.Mem.head _))) x y
  let hfun : (Nat → Bool) → Nat := fun g => Sum.elim id (fun _ => 0) (F (.inr g))
  have hnp : ∀ g, ¬ S'.rel PRel.P (fun _ => (.inr g : Nat ⊕ (Nat → Bool))) :=
    fun g hc => Bool.noConfusion ((hP _).1 hc)
  have hleft : ∀ g, F (.inr g) = .inl (hfun g) := by
    intro g
    have hpf := (hP _).1 (h1 _ (hnp g))
    show F (.inr g) = .inl (Sum.elim id (fun _ => 0) (F (.inr g)))
    revert hpf
    cases F (.inr g) with
    | inl m => intro _; rfl
    | inr _ => intro hc; exact Bool.noConfusion hc
  apply cantor_no_injection hfun
  intro g₁ g₂ e
  have := h2 _ _ (hnp g₁) (hnp g₂) (by rw [hleft, hleft, e])
  exact Sum.inr.inj this

/-- Corollary: `injTheory` does not have the expansion property over `Th(N₀)`. -/
theorem injTheory_not_expansionProperty :
    ¬ ExpansionProperty (SigHom.inclFn LP 1) (Theory.th N0) injTheory := by
  intro hexp
  obtain ⟨S', hred, hS'⟩ := hexp _ M0 M0_models_thN0
  exact M0_no_expansion ⟨S', hred, hS'⟩

/-- **Main result (counterexample).** Conservativity does not imply the
expansion property: `T' = Th(N₀) + "f injects ¬P into P"` is conservative over
`T = Th(N₀)` (the complete theory of `(ℕ ⊕ ℕ, P = left)`) but does not have the
expansion property; the witness is the model `M₀ = (ℕ ⊕ (ℕ → Bool), P = left)`
of `T`, which has no expansion to a model of `T'`. -/
theorem conservative_not_implies_expansionProperty :
    Conservative (SigHom.inclFn LP 1) (Theory.th N0) injTheory ∧
    ¬ ExpansionProperty (SigHom.inclFn LP 1) (Theory.th N0) injTheory ∧
    M0.ModelsTh (Theory.th N0) ∧
    ¬ ∃ S' : Str (LP.addFn 1) (Nat ⊕ (Nat → Bool)),
        S'.reduct (SigHom.inclFn LP 1) = M0 ∧ S'.ModelsTh injTheory := by
  refine ⟨?_, injTheory_not_expansionProperty, M0_models_thN0, M0_no_expansion⟩
  intro φ h β S hS
  exact hS φ ((models_map (SigHom.inclFn LP 1) N0f φ).1 (h _ N0f N0f_models_injTheory))

end Toy.Extension
