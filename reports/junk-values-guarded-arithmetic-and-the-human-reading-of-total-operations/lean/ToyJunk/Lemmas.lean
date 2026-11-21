import ToyJunk.Basic

/-!
# Basic lemmas: three-valued connectives, the `Int` embedding, and the bridge to Lean's
operators
-/

namespace Toy.Junk

/-! ## Three-valued connectives -/

theorem obind2_eq_some {x y : Option Int} {f : Int → Int → Option Int} {v : Int} :
    obind2 x y f = some v ↔ ∃ a b, x = some a ∧ y = some b ∧ f a b = some v := by
  cases x <;> cases y <;> simp [obind2]

theorem hAtom_eq_some {rel : Int → Int → Bool} {x y : Option Int} {b : Bool} :
    hAtom rel x y = some b ↔ ∃ a a', x = some a ∧ y = some a' ∧ rel a a' = b := by
  cases x <;> cases y <;> simp [hAtom]

theorem tvNot_eq_some {x : Option Bool} {b : Bool} : tvNot x = some b ↔ x = some (!b) := by
  cases x with
  | none => simp [tvNot]
  | some a => cases a <;> cases b <;> simp [tvNot]

theorem tvAnd_eq_some_true {c : Conn} {x y : Option Bool} :
    tvAnd c x y = some true ↔ x = some true ∧ y = some true := by
  cases c <;> rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [tvAnd]

theorem tvAnd_eq_some_false {c : Conn} {x y : Option Bool} :
    tvAnd c x y = some false → x = some false ∨ y = some false := by
  cases c <;> rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [tvAnd]

theorem tvOr_eq_some_true {c : Conn} {x y : Option Bool} :
    tvOr c x y = some true → x = some true ∨ y = some true := by
  cases c <;> rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [tvOr]

theorem tvOr_eq_some_false {c : Conn} {x y : Option Bool} :
    tvOr c x y = some false ↔ x = some false ∧ y = some false := by
  cases c <;> rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp [tvOr]

theorem tvAnd_some_false (c : Conn) (y : Option Bool) : tvAnd c (some false) y = some false := by
  cases c <;> rfl

theorem tvAnd_some_true_some (c : Conn) (b : Bool) : tvAnd c (some true) (some b) = some b := by
  cases c <;> cases b <;> rfl

theorem tvOr_some_some (c : Conn) (a b : Bool) : tvOr c (some a) (some b) = some (a || b) := by
  cases c <;> cases a <;> cases b <;> rfl

theorem tvImp_some_false (c : Conn) (y : Option Bool) : tvImp c (some false) y = some true := by
  cases c <;> rfl

theorem tvImp_some_true_some (c : Conn) (b : Bool) : tvImp c (some true) (some b) = some b := by
  cases c <;> cases b <;> rfl

theorem tvAll_eq_some_true {α : Type} {f : α → Option Bool} :
    tvAll f = some true ↔ ∀ v, f v = some true := by
  unfold tvAll
  by_cases h : ∀ v, f v = some true
  · simp [h]
  · simp only [h, ↓reduceIte]
    constructor
    · intro h2
      split at h2 <;> simp at h2
    · intro h2
      exact h2.elim

theorem tvAll_eq_some_false {α : Type} {f : α → Option Bool} :
    tvAll f = some false → ∃ v, f v = some false := by
  unfold tvAll
  split
  · simp
  · split
    · intro _; assumption
    · simp

theorem tvEx_eq_some_true {α : Type} {f : α → Option Bool} :
    tvEx f = some true ↔ ∃ v, f v = some true := by
  unfold tvEx
  by_cases h : ∃ v, f v = some true
  · simp [h]
  · simp only [h, ↓reduceIte]
    constructor
    · intro h2
      split at h2 <;> simp at h2
    · intro h2
      exact h2.elim

theorem tvEx_eq_some_false {α : Type} {f : α → Option Bool} :
    tvEx f = some false → ∀ v, f v = some false := by
  unfold tvEx
  split
  · simp
  · split
    · intro _; assumption
    · simp

open Classical in
theorem tvAll_some {α : Type} (g : α → Bool) :
    tvAll (fun v => some (g v)) = some (decide (∀ v, g v = true)) := by
  unfold tvAll
  by_cases h : ∀ v, g v = true
  · simp [h]
  · have h' : ∃ v, g v = false := by
      apply Classical.byContradiction
      intro hn
      apply h
      intro v
      cases hv : g v
      · exact absurd ⟨v, hv⟩ hn
      · rfl
    simp [h, h']

open Classical in
theorem tvEx_some {α : Type} (g : α → Bool) :
    tvEx (fun v => some (g v)) = some (decide (∃ v, g v = true)) := by
  unfold tvEx
  by_cases h : ∃ v, g v = true
  · simp [h]
  · have h' : ∀ v, g v = false := by
      intro v
      cases hv : g v
      · rfl
      · exact absurd ⟨v, hv⟩ h
    simp [h']

/-! ## The connective tables are Kleene's strong tables and McCarthy's sequential tables -/

/-- Position in the truth order false < undefined < true. -/
def tvRank : Option Bool → Nat
  | some false => 0
  | none => 1
  | some true => 2

theorem tvRank_inj {x y : Option Bool} (h : tvRank x = tvRank y) : x = y := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> simp_all [tvRank]

/-- **Strong Kleene tables.** Under `Conn.kleene`, conjunction is the minimum and
disjunction the maximum in the truth order false < undefined < true, negation reverses
the order, and implication is `¬x ∨ y`. -/
theorem kleene_tables (x y : Option Bool) :
    tvRank (tvAnd .kleene x y) = min (tvRank x) (tvRank y) ∧
      tvRank (tvOr .kleene x y) = max (tvRank x) (tvRank y) ∧
      tvRank (tvNot x) = 2 - tvRank x ∧
      tvImp .kleene x y = tvOr .kleene (tvNot x) y := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> decide

/-- **Sequential (McCarthy) tables.** Under `Conn.seq`, `x ∧ y` is `if x then y else false`
and `x ∨ y` is `if x then true else y`, both undefined when `x` is undefined; implication is
`¬x ∨ y`, i.e. `if x then y else true`. -/
theorem seq_tables (x y : Option Bool) :
    tvAnd .seq x y = x.bind (fun b => if b then y else some false) ∧
      tvOr .seq x y = x.bind (fun b => if b then some true else y) ∧
      tvImp .seq x y = x.bind (fun b => if b then y else some true) := by
  rcases x with _ | _ | _ <;> rcases y with _ | _ | _ <;> decide

/-- **Strong Kleene quantifier tables.** `tvAll f` is true iff every instance is true and
false iff some instance is false; `tvEx f` is true iff some instance is true and false iff
every instance is false. -/
theorem kleene_quantifier_tables {α : Type} (f : α → Option Bool) :
    (tvAll f = some true ↔ ∀ v, f v = some true) ∧
      (tvAll f = some false ↔ ∃ v, f v = some false) ∧
      (tvEx f = some true ↔ ∃ v, f v = some true) ∧
      (tvEx f = some false ↔ ∀ v, f v = some false) := by
  refine ⟨tvAll_eq_some_true, ⟨tvAll_eq_some_false, ?_⟩, tvEx_eq_some_true, ⟨tvEx_eq_some_false, ?_⟩⟩
  · rintro ⟨v, hv⟩
    have hn : ¬ ∀ w, f w = some true := fun ha => by rw [ha v] at hv; cases hv
    unfold tvAll
    simp only [hn, ↓reduceIte, show ∃ w, f w = some false from ⟨v, hv⟩]
  · intro ha
    have hn : ¬ ∃ w, f w = some true := fun ⟨w, hw⟩ => by rw [ha w] at hw; cases hw
    unfold tvEx
    split
    · next h1 => exact absurd h1 hn
    · first | rfl | simp [ha]

/-! ## The `Int` embedding -/

@[simp] theorem Srt.toInt_nat (v : Nat) : Srt.toInt .nat v = (v : Int) := rfl
@[simp] theorem Srt.toInt_int (v : Int) : Srt.toInt .int v = v := rfl

theorem toInt_opAdd (s : Srt) (x y : s.denote) :
    s.toInt (opAdd s x y) = s.toInt x + s.toInt y := by
  cases s <;> simp [opAdd, Srt.toInt]

theorem toInt_opMul (s : Srt) (x y : s.denote) :
    s.toInt (opMul s x y) = s.toInt x * s.toInt y := by
  cases s <;> simp [opMul, Srt.toInt]

/-- Values of Nat-sorted terms embed as nonnegative integers. -/
theorem toInt_nonneg_of_nat (v : Srt.denote .nat) : 0 ≤ Srt.toInt .nat v := by
  simp [Srt.toInt]

/-! ## Lean's reading is the junk record `leanJ` -/

/-- Lean's operators coincide with the junk-parameterized semantics at `leanJ`. -/
theorem evalT_leanJ (ρ : Env) : ∀ {s : Srt} (t : Term s), evalT leanJ ρ t = leanEvalT ρ t := by
  intro s t
  induction t with
  | natVar i => rfl
  | intVar i => rfl
  | natLit n => rfl
  | intLit z => rfl
  | @add s t u iht ihu => cases s <;> simp [evalT, leanEvalT, opAdd, iht, ihu]
  | @sub s t u iht ihu =>
    cases s <;> simp only [evalT, leanEvalT, jSub, iht, ihu] <;> simp [leanJ]
  | @mul s t u iht ihu => cases s <;> simp [evalT, leanEvalT, opMul, iht, ihu]
  | @div s t u iht ihu =>
    cases s <;> simp only [evalT, leanEvalT, jDiv, iht, ihu] <;> simp [leanJ]
  | @mod s t u iht ihu =>
    cases s <;> simp only [evalT, leanEvalT, jMod, iht, ihu] <;> simp [leanJ]
  | cast t iht => simp [evalT, leanEvalT, iht]
  | toNat t iht =>
    simp only [evalT, leanEvalT, jToNat, iht]
    simp [leanJ]

theorem toInt_eq_iff (s : Srt) (x y : s.denote) : s.toInt x = s.toInt y ↔ x = y := by
  cases s
  · exact Int.ofNat_inj
  · exact Iff.rfl

theorem toInt_le_iff (s : Srt) (x y : s.denote) : s.toInt x ≤ s.toInt y ↔ s.leP x y := by
  cases s <;> simp [Srt.toInt, Srt.leP]

theorem toInt_lt_iff (s : Srt) (x y : s.denote) : s.toInt x < s.toInt y ↔ s.ltP x y := by
  cases s <;> simp [Srt.toInt, Srt.ltP]

theorem toInt_dvd_iff (s : Srt) (x y : s.denote) : s.toInt x ∣ s.toInt y ↔ s.dvdP x y := by
  cases s
  · simp only [Srt.toInt, Srt.dvdP]; exact Int.natCast_dvd_natCast
  · simp [Srt.toInt, Srt.dvdP]

/-- Lean's reading of a formula is its total value at `leanJ`: `evalJ leanJ φ ρ` is true
exactly when the Lean proposition `leanEvalF φ ρ`, written with Lean's own operators and
relations, holds. -/
theorem evalJ_leanJ_iff : ∀ (φ : Formula) (ρ : Env), evalJ leanJ φ ρ = true ↔ leanEvalF φ ρ := by
  intro φ
  induction φ with
  | eq t u => intro ρ; simp [evalJ, leanEvalF, evalT_leanJ, toInt_eq_iff]
  | le t u => intro ρ; simp [evalJ, leanEvalF, evalT_leanJ, toInt_le_iff]
  | lt t u => intro ρ; simp [evalJ, leanEvalF, evalT_leanJ, toInt_lt_iff]
  | dvd d n => intro ρ; simp [evalJ, leanEvalF, evalT_leanJ, toInt_dvd_iff]
  | not φ ih => intro ρ; simp [evalJ, leanEvalF, ← ih]
  | and φ ψ ih₁ ih₂ => intro ρ; simp [evalJ, leanEvalF, ← ih₁, ← ih₂]
  | or φ ψ ih₁ ih₂ => intro ρ; simp [evalJ, leanEvalF, ← ih₁, ← ih₂]
  | imp φ ψ ih₁ ih₂ =>
    intro ρ
    simp only [evalJ, leanEvalF, ← ih₁, ← ih₂]
    cases evalJ leanJ φ ρ <;> cases evalJ leanJ ψ ρ <;> simp
  | allNat x φ ih => intro ρ; simp [evalJ, leanEvalF, ih]
  | allInt x φ ih => intro ρ; simp [evalJ, leanEvalF, ih]
  | exNat x φ ih => intro ρ; simp [evalJ, leanEvalF, ih]
  | exInt x φ ih => intro ρ; simp [evalJ, leanEvalF, ih]

/-! ## Variables not mentioned do not matter -/

theorem hEvalT_congr (r : SubReading) (ρ ρ' : Env) :
    ∀ {s : Srt} (t : Term s),
      (∀ i, t.mentionsNat i = true → ρ.nat i = ρ'.nat i) →
      (∀ i, t.mentionsInt i = true → ρ.int i = ρ'.int i) →
      hEvalT r ρ t = hEvalT r ρ' t := by
  intro s t
  induction t with
  | natVar i => intro hn _; simp [hEvalT, hn i (by simp [Term.mentionsNat])]
  | intVar i => intro _ hi; simp [hEvalT, hi i (by simp [Term.mentionsInt])]
  | natLit n => intro _ _; rfl
  | intLit z => intro _ _; rfl
  | add t u iht ihu | sub t u iht ihu | mul t u iht ihu | div t u iht ihu | mod t u iht ihu =>
    intro hn hi
    simp only [hEvalT]
    rw [iht (fun i h => hn i (by simp [Term.mentionsNat, h]))
          (fun i h => hi i (by simp [Term.mentionsInt, h])),
        ihu (fun i h => hn i (by simp [Term.mentionsNat, h]))
          (fun i h => hi i (by simp [Term.mentionsInt, h]))]
  | cast t iht =>
    intro hn hi
    simp only [hEvalT]
    exact iht (fun i h => hn i (by simp [Term.mentionsNat, h]))
      (fun i h => hi i (by simp [Term.mentionsInt, h]))
  | toNat t iht =>
    intro hn hi
    simp only [hEvalT]
    rw [iht (fun i h => hn i (by simp [Term.mentionsNat, h]))
      (fun i h => hi i (by simp [Term.mentionsInt, h]))]

theorem hEval_congr (c : Conn) (r : SubReading) :
    ∀ (φ : Formula) (ρ ρ' : Env),
      (∀ i, φ.mentionsNat i = true → ρ.nat i = ρ'.nat i) →
      (∀ i, φ.mentionsInt i = true → ρ.int i = ρ'.int i) →
      hEval c r φ ρ = hEval c r φ ρ' := by
  intro φ
  induction φ with
  | eq t u | le t u | lt t u | dvd t u =>
    intro ρ ρ' hn hi
    simp only [hEval]
    rw [hEvalT_congr r ρ ρ' t (fun i h => hn i (by simp [Formula.mentionsNat, h]))
          (fun i h => hi i (by simp [Formula.mentionsInt, h])),
        hEvalT_congr r ρ ρ' u (fun i h => hn i (by simp [Formula.mentionsNat, h]))
          (fun i h => hi i (by simp [Formula.mentionsInt, h]))]
  | not φ ih =>
    intro ρ ρ' hn hi
    simp only [hEval]
    rw [ih ρ ρ' hn hi]
  | and φ ψ ih₁ ih₂ | or φ ψ ih₁ ih₂ | imp φ ψ ih₁ ih₂ =>
    intro ρ ρ' hn hi
    simp only [hEval]
    rw [ih₁ ρ ρ' (fun i h => hn i (by simp [Formula.mentionsNat, h]))
          (fun i h => hi i (by simp [Formula.mentionsInt, h])),
        ih₂ ρ ρ' (fun i h => hn i (by simp [Formula.mentionsNat, h]))
          (fun i h => hi i (by simp [Formula.mentionsInt, h]))]
  | allNat x φ ih | exNat x φ ih =>
    intro ρ ρ' hn hi
    simp only [hEval]
    congr 1
    funext v
    apply ih
    · intro i h
      simp only [Env.setNat]
      split
      · rfl
      · exact hn i (by simpa [Formula.mentionsNat] using h)
    · intro i h
      exact hi i (by simpa [Formula.mentionsInt] using h)
  | allInt x φ ih | exInt x φ ih =>
    intro ρ ρ' hn hi
    simp only [hEval]
    congr 1
    funext v
    apply ih
    · intro i h
      exact hn i (by simpa [Formula.mentionsNat] using h)
    · intro i h
      simp only [Env.setInt]
      split
      · rfl
      · exact hi i (by simpa [Formula.mentionsInt] using h)

end Toy.Junk
