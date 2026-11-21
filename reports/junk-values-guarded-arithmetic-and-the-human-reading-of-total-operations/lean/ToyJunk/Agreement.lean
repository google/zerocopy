import ToyJunk.Instances

/-!
# Result 1: junk independence and agreement

Under the `partialNat` reading, a defined human value is reproduced by every junk record
(`evalJ_eq_of_hEval_eq_some_partialNat`). Consequently "defined everywhere" implies
"junk-independent"; the converse fails, and agreement-where-defined holds for every
formula and so implies neither.
-/

namespace Toy.Junk

/-! ## Value-level agreement lemmas -/

theorem toInt_jSub_of_hSub_partialNat (J : Junk) (s : Srt) (x y : s.denote) (v : Int)
    (h : hSub .partialNat s (s.toInt x) (s.toInt y) = some v) : s.toInt (jSub J s x y) = v := by
  cases s
  · change Nat at x y
    simp only [hSub, Srt.toInt] at h
    by_cases hle : (y : Int) ≤ x
    · have hle' : y ≤ x := by omega
      simp only [hle, ↓reduceIte, Option.some.injEq] at h
      simp only [jSub, Srt.toInt, hle', ↓reduceIte]
      omega
    · simp [hle] at h
  · simp only [hSub, Option.some.injEq] at h
    simpa [jSub, Srt.toInt] using h

theorem toInt_jDiv_of_hDiv (J : Junk) (s : Srt) (x y : s.denote) (v : Int)
    (h : hDiv (s.toInt x) (s.toInt y) = some v) : s.toInt (jDiv J s x y) = v := by
  simp only [hDiv] at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    cases s
    · simp only [Srt.toInt] at hd h
      simp only [jDiv, Srt.toInt, hd, ↓reduceIte, Int.natCast_ediv]
      exact h
    · simp only [Srt.toInt] at hd h
      simp only [jDiv, Srt.toInt, hd, ↓reduceIte]
      exact h
  · simp at h

theorem toInt_jMod_of_hMod (J : Junk) (s : Srt) (x y : s.denote) (v : Int)
    (h : hMod (s.toInt x) (s.toInt y) = some v) : s.toInt (jMod J s x y) = v := by
  simp only [hMod] at h
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    cases s
    · simp only [Srt.toInt] at hd h
      simp only [jMod, Srt.toInt, hd, ↓reduceIte, Int.natCast_emod]
      exact h
    · simp only [Srt.toInt] at hd h
      simp only [jMod, Srt.toInt, hd, ↓reduceIte]
      exact h
  · simp at h

theorem toInt_jToNat_of_hToNat (J : Junk) (z v : Int) (h : hToNat z = some v) :
    ((jToNat J z : Nat) : Int) = v := by
  simp only [hToNat] at h
  split at h
  · rename_i hz
    simp only [Option.some.injEq] at h
    simp only [jToNat, hz, ↓reduceIte, Int.toNat_of_nonneg hz]
    exact h
  · simp at h

/-- Term-level agreement: under the `partialNat` reading, a defined human value of a term
is the (embedded) total value of that term under every junk record. -/
theorem toInt_evalT_of_hEvalT_partialNat (J : Junk) (ρ : Env) :
    ∀ {s : Srt} (t : Term s) (v : Int),
      hEvalT .partialNat ρ t = some v → s.toInt (evalT J ρ t) = v := by
  intro s t
  induction t with
  | natVar i => intro v h; simp only [hEvalT, Option.some.injEq] at h; exact h
  | intVar i => intro v h; simp only [hEvalT, Option.some.injEq] at h; exact h
  | natLit n => intro v h; simp only [hEvalT, Option.some.injEq] at h; exact h
  | intLit z => intro v h; simp only [hEvalT, Option.some.injEq] at h; exact h
  | @add s t u iht ihu =>
    intro v h
    obtain ⟨x, y, hx, hy, hv⟩ := obind2_eq_some.mp h
    simp only [Option.some.injEq] at hv
    simp only [evalT, toInt_opAdd, iht x hx, ihu y hy, hv]
  | @mul s t u iht ihu =>
    intro v h
    obtain ⟨x, y, hx, hy, hv⟩ := obind2_eq_some.mp h
    simp only [Option.some.injEq] at hv
    simp only [evalT, toInt_opMul, iht x hx, ihu y hy, hv]
  | @sub s t u iht ihu =>
    intro v h
    obtain ⟨x, y, hx, hy, hv⟩ := obind2_eq_some.mp h
    rw [← iht x hx, ← ihu y hy] at hv
    exact toInt_jSub_of_hSub_partialNat J s _ _ v hv
  | @div s t u iht ihu =>
    intro v h
    obtain ⟨x, y, hx, hy, hv⟩ := obind2_eq_some.mp h
    rw [← iht x hx, ← ihu y hy] at hv
    exact toInt_jDiv_of_hDiv J s _ _ v hv
  | @mod s t u iht ihu =>
    intro v h
    obtain ⟨x, y, hx, hy, hv⟩ := obind2_eq_some.mp h
    rw [← iht x hx, ← ihu y hy] at hv
    exact toInt_jMod_of_hMod J s _ _ v hv
  | cast t iht =>
    intro v h
    simp only [hEvalT] at h
    exact iht v h
  | toNat t iht =>
    intro v h
    simp only [hEvalT] at h
    obtain ⟨z, hz, hv⟩ := Option.bind_eq_some_iff.mp h
    have := iht z hz
    simp only [Srt.toInt] at this
    simp only [evalT, Srt.toInt]
    rw [this]
    exact toInt_jToNat_of_hToNat J z v hv

/-! ## Main agreement theorem -/

/-- **Agreement.** Under the `partialNat` reading of natural subtraction and either
connective semantics, if the human value of `φ` at `ρ` is defined and equals `b`, then the
total value of `φ` at `ρ` equals `b` for every junk record `J`. -/
theorem evalJ_eq_of_hEval_eq_some_partialNat (c : Conn) (J : Junk) :
    ∀ (φ : Formula) (ρ : Env) (b : Bool),
      hEval c .partialNat φ ρ = some b → evalJ J φ ρ = b := by
  intro φ
  induction φ with
  | eq t u | le t u | lt t u | dvd t u =>
    intro ρ b h
    obtain ⟨x, y, hx, hy, rfl⟩ := hAtom_eq_some.mp h
    simp only [evalJ, toInt_evalT_of_hEvalT_partialNat J ρ t x hx,
      toInt_evalT_of_hEvalT_partialNat J ρ u y hy]
  | not φ ih =>
    intro ρ b h
    have := ih ρ (!b) (tvNot_eq_some.mp h)
    simp [evalJ, this]
  | and φ ψ ih₁ ih₂ =>
    intro ρ b h
    cases b
    · rcases tvAnd_eq_some_false h with h1 | h1
      · simp [evalJ, ih₁ ρ _ h1]
      · simp [evalJ, ih₂ ρ _ h1]
    · obtain ⟨h1, h2⟩ := tvAnd_eq_some_true.mp h
      simp [evalJ, ih₁ ρ _ h1, ih₂ ρ _ h2]
  | or φ ψ ih₁ ih₂ =>
    intro ρ b h
    cases b
    · obtain ⟨h1, h2⟩ := tvOr_eq_some_false.mp h
      simp [evalJ, ih₁ ρ _ h1, ih₂ ρ _ h2]
    · rcases tvOr_eq_some_true h with h1 | h1
      · simp [evalJ, ih₁ ρ _ h1]
      · simp [evalJ, ih₂ ρ _ h1]
  | imp φ ψ ih₁ ih₂ =>
    intro ρ b h
    simp only [hEval, tvImp] at h
    cases b
    · obtain ⟨h1, h2⟩ := tvOr_eq_some_false.mp h
      have := ih₁ ρ true (tvNot_eq_some.mp h1)
      simp [evalJ, this, ih₂ ρ _ h2]
    · rcases tvOr_eq_some_true h with h1 | h1
      · have := ih₁ ρ false (tvNot_eq_some.mp h1)
        simp [evalJ, this]
      · simp [evalJ, ih₂ ρ _ h1]
  | allNat x φ ih | allInt x φ ih =>
    intro ρ b h
    simp only [hEval] at h
    cases b
    · obtain ⟨v, hv⟩ := tvAll_eq_some_false h
      simp only [evalJ, decide_eq_false_iff_not, Classical.not_forall]
      exact ⟨v, by simp [ih _ _ hv]⟩
    · have hall := tvAll_eq_some_true.mp h
      simp only [evalJ, decide_eq_true_eq]
      intro v
      exact ih _ _ (hall v)
  | exNat x φ ih | exInt x φ ih =>
    intro ρ b h
    simp only [hEval] at h
    cases b
    · have hall := tvEx_eq_some_false h
      simp only [evalJ, decide_eq_false_iff_not, not_exists]
      intro v
      simp [ih _ _ (hall v)]
    · obtain ⟨v, hv⟩ := tvEx_eq_some_true.mp h
      simp only [evalJ, decide_eq_true_eq]
      exact ⟨v, ih _ _ hv⟩

/-- Restatement with the named predicate: under `partialNat`, every formula agrees with
every junk record wherever its human value is defined. -/
theorem agreesWhereDefined_partialNat (c : Conn) (J : Junk) (φ : Formula) :
    AgreesWhereDefined c .partialNat J φ :=
  fun ρ b h => evalJ_eq_of_hEval_eq_some_partialNat c J φ ρ b h

/-- **Defined everywhere ⇒ junk-independent** (under `partialNat`). -/
theorem junkIndependent_of_definedEverywhere_partialNat (c : Conn) (φ : Formula)
    (h : DefinedEverywhere c .partialNat φ) : JunkIndependent φ := by
  intro J J' ρ
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (h ρ)
  rw [evalJ_eq_of_hEval_eq_some_partialNat c J φ ρ b hb,
    evalJ_eq_of_hEval_eq_some_partialNat c J' φ ρ b hb]

/-- **Human-valid ⇒ Lean-valid** (under `partialNat`), for every formula. -/
theorem leanValid_of_humanValid_partialNat (c : Conn) (φ : Formula)
    (h : HumanValid c .partialNat φ) : LeanValid φ :=
  fun ρ => evalJ_eq_of_hEval_eq_some_partialNat c leanJ φ ρ true (h ρ)

/-- **Validity transfer for everywhere-defined formulas** (under `partialNat`). -/
theorem leanValid_iff_humanValid_of_definedEverywhere_partialNat (c : Conn) (φ : Formula)
    (h : DefinedEverywhere c .partialNat φ) : LeanValid φ ↔ HumanValid c .partialNat φ := by
  constructor
  · intro hv ρ
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (h ρ)
    have := evalJ_eq_of_hEval_eq_some_partialNat c leanJ φ ρ b hb
    rw [hv ρ] at this
    rw [hb, ← this]
  · exact leanValid_of_humanValid_partialNat c φ

/-! ## Non-vacuity -/

/-- Non-vacuity of `evalJ_eq_of_hEval_eq_some_partialNat`: the human value of `5 - 3 = 2`
(a natural subtraction inside its domain) is defined and true. -/
theorem nv_evalJ_eq_of_hEval_eq_some_partialNat (c : Conn) :
    hEval c .partialNat fFiveSubThree Env.zero = some true := by
  cases c <;> decide

/-- Non-vacuity of the "defined everywhere" hypotheses: the closed formula `5 - 3 = 2` is
defined at every environment. -/
theorem nv_definedEverywhere_partialNat (c : Conn) :
    DefinedEverywhere c .partialNat fFiveSubThree := by
  intro ρ
  cases c <;> simp [hEval, fFiveSubThree, hEvalT, obind2, hSub, hAtom]

/-- Non-vacuity of `leanValid_of_humanValid_partialNat`: `5 - 3 = 2` is human-valid. -/
theorem nv_humanValid_partialNat (c : Conn) : HumanValid c .partialNat fFiveSubThree := by
  intro ρ
  cases c <;> simp [hEval, fFiveSubThree, hEvalT, obind2, hSub, hAtom]

/-! ## Counterexamples -/

/-- The `partialNat` hypothesis of the agreement theorem is tight (witnessed at `Env.zero`,
for each `c`): under `intValued`, `(2 : Nat) - 3 < 0` has the defined human value `true`,
while its Lean value is `false` (truncated subtraction gives `(2 : Nat) - 3 = 0`). -/
theorem ce_agreement_intValued (c : Conn) :
    hEval c .intValued fNumeralNat Env.zero = some true ∧
      evalJ leanJ fNumeralNat Env.zero = false := by
  cases c <;> decide

/-- The definedness hypothesis of the agreement theorem is tight (witnessed at `Env.zero`,
for each `c`): `(x : Int) / 0 = 0` is human-undefined and its Lean value is `true` (`Int`
division by zero returns `0`), so "`evalJ leanJ φ ρ = false`" fails for `b = false`. -/
theorem ce_agreement_undefined (c : Conn) :
    hEval c .partialNat fDivZero Env.zero = none ∧ evalJ leanJ fDivZero Env.zero ≠ false := by
  cases c <;> decide

/-- **The converse fails.** `(a - b) * 0 = 0` is junk-independent, but under `partialNat`
its human value is undefined whenever `a < b` (term evaluation is strict, so `* 0` does not
absorb an undefined operand). -/
theorem ce_junkIndependent_not_definedEverywhere (c : Conn) :
    JunkIndependent fMulZero ∧ hEval c .partialNat fMulZero (envAB 0 1) = none ∧
      ¬ DefinedEverywhere c .partialNat fMulZero := by
  have hund : hEval c .partialNat fMulZero (envAB 0 1) = none := by cases c <;> decide
  refine ⟨?_, hund, fun h => h _ hund⟩
  intro J J' ρ
  simp [evalJ, fMulZero, evalT, opMul]

/-- **Agreement-where-defined gives neither junk independence nor definedness.** For each
connective semantics `c`: `a - b ≤ a` at `Nat` agrees with the `partialNat` human reading
wherever that is defined, for every junk record (as every formula does,
`agreesWhereDefined_partialNat`); it is Lean-valid; it is junk-dependent (with every junk
value equal to `1` it is false at `a = 0, b = 1`); and its human value is undefined at
`a = 0, b = 1`, so it is not defined everywhere. -/
theorem ce_agrees_not_junkIndependent (c : Conn) :
    (∀ J : Junk, AgreesWhereDefined c .partialNat J fSubLeSelf) ∧
      LeanValid fSubLeSelf ∧ evalJ oneJ fSubLeSelf (envAB 0 1) = false ∧
      ¬ JunkIndependent fSubLeSelf ∧
      hEval c .partialNat fSubLeSelf (envAB 0 1) = none ∧
      ¬ DefinedEverywhere c .partialNat fSubLeSelf := by
  have h1 : evalJ oneJ fSubLeSelf (envAB 0 1) = false := by decide
  have hund : hEval c .partialNat fSubLeSelf (envAB 0 1) = none := by cases c <;> decide
  refine ⟨fun J => agreesWhereDefined_partialNat c J fSubLeSelf, ?_, h1, ?_, hund,
    fun h => h _ hund⟩
  · intro ρ
    rw [evalJ_leanJ_iff]
    exact Nat.sub_le _ _
  · intro h
    have h2 : evalJ leanJ fSubLeSelf (envAB 0 1) = true := by decide
    have := h leanJ oneJ (envAB 0 1)
    rw [h1, h2] at this
    exact Bool.noConfusion this

/-- `(0 : Nat) - 1 = 0` (Lean-true by truncated subtraction) is junk-dependent; under
`partialNat` it is undefined at every environment, while under `intValued` it is defined
(and false) at every environment. So the definedness hypothesis and the `partialNat` reading
of `junkIndependent_of_definedEverywhere_partialNat` are tight (witnessed at this formula). -/
theorem ce_zeroSubOne_junkDependent (c : Conn) :
    ¬ JunkIndependent fZeroSubOne ∧ (∀ ρ, hEval c .partialNat fZeroSubOne ρ = none) ∧
      DefinedEverywhere c .intValued fZeroSubOne := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := h leanJ oneJ Env.zero
    revert this
    decide
  · intro ρ
    cases c <;> simp [hEval, fZeroSubOne, hEvalT, obind2, hSub, hAtom]
  · intro ρ
    cases c <;> simp [hEval, fZeroSubOne, hEvalT, obind2, hSub, hAtom]

/-- **Lean-valid does not imply human-valid.** `x / 0 = 0` at `Int` is Lean-valid, and
its human value is undefined at every environment under either reading. -/
theorem ce_leanValid_not_humanValid (c : Conn) (r : SubReading) :
    LeanValid fDivZero ∧ (∀ ρ, hEval c r fDivZero ρ = none) ∧ ¬ HumanValid c r fDivZero := by
  have hnone : ∀ ρ, hEval c r fDivZero ρ = none := by
    intro ρ
    simp [hEval, fDivZero, hEvalT, obind2, hDiv, DivDom, hAtom]
  refine ⟨?_, hnone, fun h => by have := h Env.zero; rw [hnone] at this; cases this⟩
  intro ρ
  simp [evalJ, fDivZero, evalT, jDiv, leanJ, DivDom]

/-- **Junk-independent and Lean-valid, yet undefined everywhere, with no multiplication.**
For every connective semantics and reading, `x / 0 = x / 0` and `x / 0 = 0 ∨ ¬ (x / 0 = 0)`
at `Int` are true at every environment under every junk record (so Lean-valid and
junk-independent), while their human value is undefined at every environment. -/
theorem ce_junkIndependent_leanValid_undefined (c : Conn) (r : SubReading) :
    (LeanValid fDivZeroRefl ∧ JunkIndependent fDivZeroRefl ∧
        ∀ ρ, hEval c r fDivZeroRefl ρ = none) ∧
      (LeanValid fDivZeroEM ∧ JunkIndependent fDivZeroEM ∧
        ∀ ρ, hEval c r fDivZeroEM ρ = none) := by
  have t1 : ∀ J ρ, evalJ J fDivZeroRefl ρ = true := by
    intro J ρ; simp [evalJ, fDivZeroRefl]
  have t2 : ∀ J ρ, evalJ J fDivZeroEM ρ = true := by
    intro J ρ; simp only [evalJ, fDivZeroEM]; cases evalJ J fDivZero ρ <;> rfl
  have hd : ∀ ρ, hEval c r fDivZero ρ = none := by
    intro ρ; simp [hEval, fDivZero, hEvalT, obind2, hDiv, DivDom, hAtom]
  refine ⟨⟨fun ρ => t1 leanJ ρ, fun J J' ρ => by rw [t1, t1], ?_⟩,
    ⟨fun ρ => t2 leanJ ρ, fun J J' ρ => by rw [t2, t2], ?_⟩⟩
  · intro ρ; simp [hEval, fDivZeroRefl, hEvalT, obind2, hDiv, DivDom, hAtom]
  · intro ρ
    simp only [hEval, fDivZeroEM]
    rw [hd ρ]
    cases c <;> rfl

/-- The human-validity hypothesis of `leanValid_of_humanValid_partialNat`, in canonical
form: under `partialNat`, `a - b + b = a` (at `Nat`) is not human-valid and not Lean-valid. -/
theorem ce_not_humanValid_not_leanValid (c : Conn) :
    ¬ HumanValid c .partialNat fSubAddCancel ∧ ¬ LeanValid fSubAddCancel := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h (envAB 0 1)
    have hn : hEval c .partialNat fSubAddCancel (envAB 0 1) = none := by cases c <;> decide
    rw [hn] at this
    cases this
  · have := h (envAB 0 1)
    revert this
    decide

/-- **No flip under `partialNat`, both directions.** For every connective semantics, junk
record, toy formula and environment: it is not the case that the human value is `false`
while the total value is `true`, and not the case that the human value is `true` while the
total value is `false`. (A restatement of `evalJ_eq_of_hEval_eq_some_partialNat`.) -/
theorem no_flip_partialNat (c : Conn) (J : Junk) (φ : Formula) (ρ : Env) :
    ¬ (hEval c .partialNat φ ρ = some false ∧ evalJ J φ ρ = true) ∧
      ¬ (hEval c .partialNat φ ρ = some true ∧ evalJ J φ ρ = false) := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · rw [evalJ_eq_of_hEval_eq_some_partialNat c J φ ρ false h1] at h2; cases h2
  · rw [evalJ_eq_of_hEval_eq_some_partialNat c J φ ρ true h1] at h2; cases h2

/-- The `partialNat` hypothesis of `leanValid_of_humanValid_partialNat` is tight (witness:
`(a b : Nat), a - b + b = a`, human-valid under `intValued`, Lean-false at `a = 0, b = 1`). -/
theorem ce_intValued_humanValid_not_leanValid (c : Conn) :
    HumanValid c .intValued fSubAddCancel ∧ ¬ LeanValid fSubAddCancel := by
  refine ⟨?_, ?_⟩
  · intro ρ
    cases c <;> simp [hEval, fSubAddCancel, hEvalT, obind2, hSub, hAtom]
  · intro h
    have := h (envAB 0 1)
    revert this
    decide

/-- The `partialNat` hypothesis of
`leanValid_iff_humanValid_of_definedEverywhere_partialNat` (canonical form): under
`intValued`, `a - b + b = a` (at `Nat`) is defined everywhere and human-valid, but not
Lean-valid, so the equivalence fails. -/
theorem ce_intValued_definedEverywhere_humanValid_not_leanValid (c : Conn) :
    DefinedEverywhere c .intValued fSubAddCancel ∧ HumanValid c .intValued fSubAddCancel ∧
      ¬ LeanValid fSubAddCancel := by
  obtain ⟨h1, h2⟩ := ce_intValued_humanValid_not_leanValid c
  exact ⟨fun ρ => by rw [h1 ρ]; simp, h1, h2⟩

end Toy.Junk
