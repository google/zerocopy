import ToyDrat.Certificate

/-!
# LRAT-style hint checking

In the LRAT format each RUP addition carries a list of antecedent clause identifiers in
propagation order. A hint checker does not search for unit clauses: it starts from the
negation of the added clause and processes the hinted clauses in order. In this toy model
(`hintReplay`) each hinted clause must have exactly one non-falsified literal *occurrence*,
which is then pushed on the trail (the literal may already be on the trail, so a clause that
is already satisfied is accepted), or no non-falsified literal, in which case the replay
succeeds and any remaining hints are ignored without being examined. A clause with a
repeated unassigned literal (`x₀ ∨ x₀`) is rejected, and a complementary pair on the initial
trail is not detected. Clause identifiers are positions in the current formula.

`lratRupCheck` is sound for RUP (`lrat_hint_replay_implies_rup`) and complete on
well-formed inputs, i.e. for non-tautological clauses and formulas without repeated
literals in a clause (`lratRupCheck_complete_of_wellformed`), but not complete in general
(`lratRupCheck_incomplete_tautology`, `lratRupCheck_incomplete_dup_lits`). The variant
`lratRupCheckDedup`, which also checks the initial trail for a complementary pair and
deduplicates literals, accepts some hint list exactly for the RUP clauses
(`lratRupCheckDedup_exists_iff_rup`).
-/

namespace Toy.Drat

/-- Replay hints: each hinted clause must have no non-falsified literal occurrence (success;
remaining hints are not examined) or exactly one (which is pushed on the trail, whether or
not it is already there); anything else, or a dangling index, fails. -/
def hintReplay (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match D.filter (fun l => !falsified τ l) with
      | [] => true
      | [l] => hintReplay F (l :: τ) is
      | _ => false

/-- LRAT-style RUP check of clause `C` with the given hint list. -/
def lratRupCheck (F : Formula) (C : Clause) (hints : List Nat) : Bool :=
  hintReplay F (negClause C) hints

/-- A deliberately *sloppy* hint replay that skips the unit test: it assigns the first
non-falsified literal of each hinted clause even when the clause has several. -/
def sloppyHintReplay (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match D.filter (fun l => !falsified τ l) with
      | [] => true
      | l :: _ => sloppyHintReplay F (l :: τ) is

/-! ## Hint replay implies RUP -/

theorem hintReplay_unitProp (F : Formula) :
    ∀ (hs : List Nat) (τ σ : Trail), hintReplay F τ hs = true → TrailSub τ σ →
      unitProp hs.length F σ = .conflict := by
  intro hs
  induction hs with
  | nil => intro τ σ h; simp [hintReplay] at h
  | cons i is ih =>
    intro τ σ h hsub
    simp only [hintReplay] at h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i D hD
      have hDF : D ∈ F := List.mem_iff_getElem?.2 ⟨i, hD⟩
      split at h
      · -- every literal of `D` is falsified by `τ`, hence by `σ`
        rename_i hnil
        have hall : ∀ l ∈ D, falsified σ l = true := by
          intro l hl
          have : ¬ (!falsified τ l) = true := List.filter_eq_nil_iff.1 hnil l hl
          exact falsified_mono hsub (by simpa using this)
        have hc : hasConflict F σ = true := by
          simp only [hasConflict, Bool.or_eq_true, List.any_eq_true, List.all_eq_true]
          exact Or.inr ⟨D, hDF, hall⟩
        cases is <;> simp [unitProp, hc]
      · -- `D` is unit under `τ` with remaining literal `l`
        rename_i l hone
        have hlD : l ∈ D := by
          have : l ∈ D.filter (fun l => !falsified τ l) := by rw [hone]; simp
          exact (List.mem_filter.1 this).1
        have hforce : ∀ m ∈ D, m = l ∨ falsified σ m = true := by
          intro m hm
          by_cases hf : falsified τ m = true
          · exact Or.inr (falsified_mono hsub hf)
          · have : m ∈ D.filter (fun l => !falsified τ l) :=
              List.mem_filter.2 ⟨hm, by simpa using hf⟩
            rw [hone] at this
            exact Or.inl (by simpa using this)
        have hl : l ∈ upRound F σ :=
          mem_upRound.2 (Or.inr ⟨D, hDF, mem_unitLits.2 ⟨hlD, hforce⟩⟩)
        have hsub' : TrailSub (l :: τ) (upRound F σ) := by
          intro m hm
          rcases List.mem_cons.1 hm with rfl | hm
          · exact hl
          · exact TrailSub_upRound F σ m (hsub m hm)
        have := ih (l :: τ) (upRound F σ) h hsub'
        simp only [List.length_cons, unitProp]
        split <;> simp_all
      · exact absurd h Bool.false_ne_true

/-- **LRAT hint soundness.** If replaying the hinted clauses in order from the negation of
`C` reaches a falsified clause (each earlier hinted clause being unit), then `C` is RUP
w.r.t. `F`; in fact budgeted propagation finds the conflict within `hints.length` rounds. -/
theorem lrat_hint_replay_implies_rup {F : Formula} {C : Clause} {hints : List Nat}
    (h : lratRupCheck F C hints = true) :
    unitProp hints.length F (negClause C) = .conflict ∧ RUP F C :=
  have hc := hintReplay_unitProp F hints _ _ h (fun _ hl => hl)
  ⟨hc, ⟨_, hc⟩⟩

/-- Corollary: an accepted hint list certifies semantic entailment. -/
theorem lrat_hint_replay_implies_entails {F : Formula} {C : Clause} {hints : List Nat}
    (h : lratRupCheck F C hints = true) : Entails F C :=
  rup_implies_entails (lrat_hint_replay_implies_rup h).2

/-- A three-clause formula refuted by unit propagation: `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
def chain3 : Formula := [[Lit.p 0], [Lit.n 0, Lit.p 1], [Lit.n 1]]

/-- Non-vacuity: the hint list `[0, 1, 2]` certifies the empty clause for `chain3`. -/
theorem lratRupCheck_chain3 : lratRupCheck chain3 [] [0, 1, 2] = true := by decide

/-- **Hint replay is order-sensitive.** The empty clause is RUP w.r.t. `chain3`, the hint list
`[0, 1, 2]` is accepted, but the same clauses in the order `[1, 0, 2]` are rejected (clause 1
is not unit under the empty trail). This concerns a fixed hint list; whether *some* hint list
is accepted is settled by `lratRupCheck_complete_of_wellformed` and the incompleteness
examples below. -/
theorem lrat_hint_order_matters :
    RUP chain3 [] ∧ lratRupCheck chain3 [] [0, 1, 2] = true ∧
      lratRupCheck chain3 [] [1, 0, 2] = false :=
  ⟨⟨2, by decide⟩, by decide, by decide⟩

/-- **The unit test on each hint is necessary.** The sloppy replay accepts the hint list
`[0, 1]` as a refutation of the *satisfiable* formula `(x₀ ∨ x₁) ∧ ¬x₀` (it assigns `x₀`
from the binary clause), while the unit-checking replay rejects it. -/
theorem sloppy_hint_replay_unsound :
    sloppyHintReplay [[Lit.p 0, Lit.p 1], [Lit.n 0]] (negClause []) [0, 1] = true ∧
      Satisfiable [[Lit.p 0, Lit.p 1], [Lit.n 0]] ∧
      lratRupCheck [[Lit.p 0, Lit.p 1], [Lit.n 0]] [] [0, 1] = false :=
  ⟨by decide, Satisfiable_example_pos, by decide⟩


/-! ## Completeness: which RUP clauses have an accepted hint list -/

/-- `C` contains no complementary pair of literals. -/
def NonTautological (C : Clause) : Prop := ∀ l ∈ C, l.neg ∉ C

/-- No clause of `F` repeats a literal. -/
def DupFreeClauses (F : Formula) : Prop := ∀ D ∈ F, D.Nodup

/-- Remove repeated literals, keeping the last occurrence of each. -/
def dedupLits : List Lit → List Lit
  | [] => []
  | l :: ls =>
    let r := dedupLits ls
    if decide (l ∈ r) then r else l :: r

/-- Hint replay as in `hintReplay`, but on the deduplicated non-falsified literals. -/
def hintStepDedup (F : Formula) : Trail → List Nat → Bool
  | _, [] => false
  | τ, i :: is =>
    match F[i]? with
    | none => false
    | some D =>
      match dedupLits (D.filter (fun l => !falsified τ l)) with
      | [] => true
      | [l] => hintStepDedup F (l :: τ) is
      | _ => false

/-- Hint replay that first checks the trail for a complementary pair (as `hasConflict` does),
then replays hints on deduplicated literals. -/
def hintReplayDedup (F : Formula) (τ : Trail) (hints : List Nat) : Bool :=
  τ.any (falsified τ) || hintStepDedup F τ hints

/-- LRAT-style RUP check with the initial trail-pair test and literal deduplication. -/
def lratRupCheckDedup (F : Formula) (C : Clause) (hints : List Nat) : Bool :=
  hintReplayDedup F (negClause C) hints

theorem mem_dedupLits_iff {xs : List Lit} {a : Lit} :
    a ∈ dedupLits xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => simp [dedupLits]
  | cons x xs ih =>
    simp only [dedupLits]
    by_cases hx : x ∈ dedupLits xs
    · simp only [hx, decide_true, ↓reduceIte, ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun hax => hax ▸ ih.1 hx) id⟩
    · simp [hx, ih]

theorem dedupLits_eq_nil_iff {xs : List Lit} :
    dedupLits xs = [] ↔ xs = [] := by
  constructor
  · intro h
    cases xs with
    | nil => rfl
    | cons x rest =>
      have hx : x ∈ dedupLits (x :: rest) := mem_dedupLits_iff.2 List.mem_cons_self
      rw [h] at hx
      cases hx
  · rintro rfl
    rfl

theorem dedupLits_singleton_of_unique {xs : List Lit} {l : Lit}
    (hl : l ∈ xs) (huniq : ∀ m ∈ xs, m = l) : dedupLits xs = [l] := by
  induction xs with
  | nil => cases hl
  | cons x rest ih =>
    have hx : x = l := huniq x List.mem_cons_self
    subst hx
    cases rest with
    | nil => rfl
    | cons y ys =>
      have hy : y = x := huniq y (List.mem_cons_of_mem _ List.mem_cons_self)
      have hrec : dedupLits (y :: ys) = [x] :=
        ih (hy ▸ List.mem_cons_self) (fun m hm => huniq m (List.mem_cons_of_mem _ hm))
      change (let r := dedupLits (y :: ys); if decide (x ∈ r) then r else x :: r) = [x]
      simp [hrec]

theorem hintStepDedup_unitProp (F : Formula) :
    ∀ (hs : List Nat) (τ σ : Trail), hintStepDedup F τ hs = true → TrailSub τ σ →
      unitProp hs.length F σ = .conflict := by
  intro hs
  induction hs with
  | nil => intro τ σ h; simp [hintStepDedup] at h
  | cons i is ih =>
    intro τ σ h hsub
    simp only [hintStepDedup] at h
    split at h
    · exact absurd h Bool.false_ne_true
    · rename_i D hD
      have hDF : D ∈ F := List.mem_iff_getElem?.2 ⟨i, hD⟩
      split at h
      · rename_i hnil
        have hfnil : D.filter (fun l => !falsified τ l) = [] := dedupLits_eq_nil_iff.1 hnil
        have hall : ∀ l ∈ D, falsified σ l = true := by
          intro l hl
          have : ¬ (!falsified τ l) = true := List.filter_eq_nil_iff.1 hfnil l hl
          exact falsified_mono hsub (by simpa using this)
        have hc : hasConflict F σ = true := by
          simp only [hasConflict, Bool.or_eq_true, List.any_eq_true, List.all_eq_true]
          exact Or.inr ⟨D, hDF, hall⟩
        cases is <;> simp [unitProp, hc]
      · rename_i l hone
        have hlD : l ∈ D := by
          have : l ∈ dedupLits (D.filter (fun l => !falsified τ l)) := by rw [hone]; simp
          exact (List.mem_filter.1 (mem_dedupLits_iff.1 this)).1
        have hforce : ∀ m ∈ D, m = l ∨ falsified σ m = true := by
          intro m hm
          cases hf : falsified τ m with
          | true => exact Or.inr (falsified_mono hsub hf)
          | false =>
            have hm' : m ∈ dedupLits (D.filter (fun l => !falsified τ l)) :=
              mem_dedupLits_iff.2 (List.mem_filter.2 ⟨hm, by simp [hf]⟩)
            rw [hone] at hm'
            exact Or.inl (by simpa using hm')
        have hl : l ∈ upRound F σ :=
          mem_upRound.2 (Or.inr ⟨D, hDF, mem_unitLits.2 ⟨hlD, hforce⟩⟩)
        have hsub' : TrailSub (l :: τ) (upRound F σ) := by
          intro m hm
          rcases List.mem_cons.1 hm with rfl | hm
          · exact hl
          · exact TrailSub_upRound F σ m (hsub m hm)
        have := ih (l :: τ) (upRound F σ) h hsub'
        simp only [List.length_cons, unitProp]
        split <;> simp_all
      · exact absurd h Bool.false_ne_true

theorem trail_equiv_falsified {τ₁ τ₂ : Trail} (heq : ∀ x, x ∈ τ₁ ↔ x ∈ τ₂) (l : Lit) :
    falsified τ₁ l = falsified τ₂ l := by
  simp [falsified, heq l.neg]

theorem hintStepDedup_trail_equiv (F : Formula) :
    ∀ (hs : List Nat) {τ₁ τ₂ : Trail}, (∀ x, x ∈ τ₁ ↔ x ∈ τ₂) →
      hintStepDedup F τ₁ hs = hintStepDedup F τ₂ hs := by
  intro hs
  induction hs with
  | nil => intros; rfl
  | cons i is ih =>
    intro τ₁ τ₂ heq
    have hfeq : (fun l => !falsified τ₁ l) = (fun l => !falsified τ₂ l) := by
      funext l
      rw [trail_equiv_falsified heq l]
    simp only [hintStepDedup, hfeq]
    cases hFi : F[i]? with
    | none => rfl
    | some D =>
      simp only []
      cases hdl : dedupLits (D.filter (fun l => !falsified τ₂ l)) with
      | nil => rfl
      | cons l rest =>
        cases rest with
        | nil =>
          exact ih (fun x => by simp only [List.mem_cons, heq x])
        | cons l₂ rest' => rfl

theorem step_forced_list (F : Formula) (τ : Trail) :
    ∀ (ls : List Lit), (∀ l ∈ ls, ∃ C ∈ F, l ∈ unitLits τ C) →
      ∀ (σ : Trail), TrailSub τ σ → σ.any (falsified σ) = false →
        (∃ hs, hintStepDedup F σ hs = true) ∨
          ∃ hs σ',
            (∀ rest, hintStepDedup F σ (hs ++ rest) = hintStepDedup F σ' rest) ∧
            TrailSub τ σ' ∧
            σ'.any (falsified σ') = false ∧
            (∀ x, x ∈ σ' ↔ x ∈ ls ∨ x ∈ σ) := by
  intro ls
  induction ls with
  | nil =>
    intro _ σ hsub hno
    exact Or.inr ⟨[], σ, fun _ => rfl, hsub, hno, fun x => by simp⟩
  | cons l ls ih =>
    intro hls σ hsub hno
    rcases ih (fun m hm => hls m (List.mem_cons_of_mem _ hm)) σ hsub hno with
      ⟨hs, htrue⟩ | ⟨hs, σ', hcomp, hsub', hno', hmem'⟩
    · exact Or.inl ⟨hs, htrue⟩
    · obtain ⟨D, hDF, hlunit⟩ := hls l List.mem_cons_self
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hDF
      obtain ⟨hlD, hforce⟩ := mem_unitLits.1 hlunit
      cases hfl : falsified σ' l with
      | true =>
        refine Or.inl ⟨hs ++ [i], ?_⟩
        rw [hcomp [i]]
        have hfnil : D.filter (fun m => !falsified σ' m) = [] := by
          rw [List.filter_eq_nil_iff]
          intro m hm
          rcases hforce m hm with rfl | hfm
          · simp [hfl]
          · simp [falsified_mono hsub' hfm]
        simp [hintStepDedup, hi, hfnil, dedupLits]
      | false =>
        have hdedup : dedupLits (D.filter (fun m => !falsified σ' m)) = [l] := by
          apply dedupLits_singleton_of_unique
          · exact List.mem_filter.2 ⟨hlD, by simp [hfl]⟩
          · intro m hm
            obtain ⟨hmD, hmf⟩ := List.mem_filter.1 hm
            rcases hforce m hmD with hml | hfm
            · exact hml
            · rw [falsified_mono hsub' hfm] at hmf
              simp at hmf
        have hno'' : (l :: σ').any (falsified (l :: σ')) = false := by
          rw [List.any_eq_false]
          intro m hm hfm
          simp only [falsified, decide_eq_true_eq, List.mem_cons] at hfm
          have hlneg_notin : l.neg ∉ σ' := by
            simpa [falsified] using hfl
          rcases List.mem_cons.1 hm with rfl | hmσ
          · rcases hfm with heq | hmem
            · exact Lit.neg_ne_self m heq
            · exact hlneg_notin hmem
          · rcases hfm with heq | hmem
            · have hm_eq : m = l.neg := by
                have := congrArg Lit.neg heq
                simpa using this
              exact hlneg_notin (hm_eq ▸ hmσ)
            · have hpair : σ'.any (falsified σ') = true :=
                List.any_eq_true.2 ⟨m, hmσ, by simpa [falsified] using hmem⟩
              rw [hno'] at hpair
              exact Bool.false_ne_true hpair
        refine Or.inr ⟨hs ++ [i], l :: σ', ?_, ?_, hno'', ?_⟩
        · intro rest
          rw [List.append_assoc, hcomp ([i] ++ rest)]
          simp [hintStepDedup, hi, hdedup]
        · exact fun x hx => List.mem_cons_of_mem _ (hsub' x hx)
        · intro x
          simp only [List.mem_cons, hmem' x]
          exact ⟨fun h => h.elim (Or.inl ∘ Or.inl) (fun h' => h'.elim (Or.inl ∘ Or.inr) Or.inr),
            fun h => h.elim (fun h' => h'.elim Or.inl (Or.inr ∘ Or.inl)) (Or.inr ∘ Or.inr)⟩

theorem hintReplayDedup_of_hasConflict {F : Formula} {τ : Trail}
    (hc : hasConflict F τ = true) : ∃ hints, hintReplayDedup F τ hints = true := by
  simp only [hasConflict, Bool.or_eq_true] at hc
  rcases hc with hpair | hcl
  · exact ⟨[], by simp [hintReplayDedup, hpair]⟩
  · obtain ⟨D, hDF, hall⟩ := List.any_eq_true.1 hcl
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hDF
    have hfnil : D.filter (fun l => !falsified τ l) = [] := by
      rw [List.filter_eq_nil_iff]
      intro l hl
      have hfl := List.all_eq_true.1 hall l hl
      simp [hfl]
    exact ⟨[i], by simp [hintReplayDedup, hintStepDedup, hi, hfnil, dedupLits]⟩

theorem unitProp_conflict_implies_hintReplayDedup (F : Formula) :
    ∀ (n : Nat) (τ : Trail), unitProp n F τ = .conflict →
      ∃ hints, hintReplayDedup F τ hints = true := by
  intro n
  induction n with
  | zero =>
    intro τ h
    simp only [unitProp] at h
    cases hc : hasConflict F τ with
    | false => simp [hc] at h
    | true => exact hintReplayDedup_of_hasConflict hc
  | succ n ih =>
    intro τ h
    simp only [unitProp] at h
    cases hc : hasConflict F τ with
    | true => exact hintReplayDedup_of_hasConflict hc
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      have hno : τ.any (falsified τ) = false := (Bool.or_eq_false_iff.1 hc).1
      let ls := (F.flatMap (unitLits τ)).filter (fun l => !decide (l ∈ τ))
      have hls : ∀ l ∈ ls, ∃ C ∈ F, l ∈ unitLits τ C := by
        intro l hl
        have hl' := (List.mem_filter.1 hl).1
        exact List.mem_flatMap.1 hl'
      rcases step_forced_list F τ ls hls τ (fun _ hx => hx) hno with
        ⟨hs, htrue⟩ | ⟨hs, σ', hcomp, _, hno', hmem'⟩
      · exact ⟨hs, by simp [hintReplayDedup, htrue]⟩
      · have hequiv : ∀ x, x ∈ σ' ↔ x ∈ upRound F τ := by
          intro x
          simp only [upRound, List.mem_append, hmem' x]
          exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
        have hno_up : (upRound F τ).any (falsified (upRound F τ)) = false := by
          rw [List.any_eq_false]
          intro m hm hfm
          have hm' : m ∈ σ' := (hequiv m).2 hm
          have hfm' : falsified σ' m = true := by
            rw [trail_equiv_falsified hequiv m]
            exact hfm
          have hpair : σ'.any (falsified σ') = true := List.any_eq_true.2 ⟨m, hm', hfm'⟩
          rw [hno'] at hpair
          exact Bool.false_ne_true hpair
        obtain ⟨hs₂, hrep₂⟩ := ih (upRound F τ) h
        simp only [hintReplayDedup, hno_up, Bool.false_or] at hrep₂
        refine ⟨hs ++ hs₂, ?_⟩
        simp only [hintReplayDedup, Bool.or_eq_true]
        right
        rw [hcomp hs₂, hintStepDedup_trail_equiv F hs₂ hequiv]
        exact hrep₂


/-- **Characterization of the deduplicating hint checker.** Some hint list is accepted by
`lratRupCheckDedup` exactly when `C` is RUP w.r.t. `F`. -/
theorem lratRupCheckDedup_exists_iff_rup (F : Formula) (C : Clause) :
    (∃ hints, lratRupCheckDedup F C hints = true) ↔ RUP F C := by
  constructor
  · rintro ⟨hints, h⟩
    simp only [lratRupCheckDedup, hintReplayDedup, Bool.or_eq_true] at h
    rcases h with hpair | hstep
    · exact ⟨0, by simp [unitProp, hasConflict, hpair]⟩
    · exact ⟨hints.length, hintStepDedup_unitProp F hints _ _ hstep (fun _ hl => hl)⟩
  · rintro ⟨n, hn⟩
    exact unitProp_conflict_implies_hintReplayDedup F n (negClause C) hn

theorem dedupLits_of_nodup : ∀ {xs : List Lit}, xs.Nodup → dedupLits xs = xs
  | [], _ => rfl
  | l :: ls, h => by
    rw [List.nodup_cons] at h
    have ih := dedupLits_of_nodup h.2
    simp only [dedupLits, ih, h.1, decide_false, Bool.false_eq_true, ↓reduceIte]

theorem hintStepDedup_eq_hintReplay {F : Formula} (hF : DupFreeClauses F) :
    ∀ (hs : List Nat) (τ : Trail), hintStepDedup F τ hs = hintReplay F τ hs := by
  intro hs
  induction hs with
  | nil => intro τ; rfl
  | cons i is ih =>
    intro τ
    simp only [hintStepDedup, hintReplay]
    cases hFi : F[i]? with
    | none => rfl
    | some D =>
      have hD : D ∈ F := List.mem_iff_getElem?.2 ⟨i, hFi⟩
      have hnd : (D.filter (fun l => !falsified τ l)).Nodup := (hF D hD).filter _
      simp only [dedupLits_of_nodup hnd]
      split <;> simp_all

theorem negClause_no_pair {C : Clause} (hC : NonTautological C) :
    (negClause C).any (falsified (negClause C)) = false := by
  rw [List.any_eq_false]
  intro l hl hf
  simp only [negClause, List.mem_map, falsified, decide_eq_true_eq] at hl hf
  obtain ⟨m, hm, rfl⟩ := hl
  obtain ⟨m', hm', heq⟩ := hf
  have : m' = m.neg := by
    have := congrArg Lit.neg heq
    simpa using this
  subst this
  exact hC m hm hm'

theorem lratRupCheckDedup_eq_of_wellformed {F : Formula} {C : Clause}
    (hC : NonTautological C) (hF : DupFreeClauses F) (hints : List Nat) :
    lratRupCheckDedup F C hints = lratRupCheck F C hints := by
  simp only [lratRupCheckDedup, hintReplayDedup, negClause_no_pair hC, Bool.false_or,
    lratRupCheck, hintStepDedup_eq_hintReplay hF]

/-- **LRAT hint replay is complete on well-formed inputs.** If `C` has no complementary pair,
no clause of `F` repeats a literal, and `C` is RUP w.r.t. `F`, then some hint list is
accepted by `lratRupCheck`. -/
theorem lratRupCheck_complete_of_wellformed {F : Formula} {C : Clause}
    (hC : NonTautological C) (hF : DupFreeClauses F) (h : RUP F C) :
    ∃ hints, lratRupCheck F C hints = true := by
  obtain ⟨hints, hh⟩ := (lratRupCheckDedup_exists_iff_rup F C).2 h
  exact ⟨hints, (lratRupCheckDedup_eq_of_wellformed hC hF hints) ▸ hh⟩

/-- **Incompleteness on a tautological clause.** `x₀ ∨ ¬x₀` is RUP w.r.t. the empty formula
(its negation is a complementary pair), the empty formula has no repeated literals, and
`lratRupCheck` rejects every hint list. -/
theorem lratRupCheck_incomplete_tautology :
    ¬ NonTautological [Lit.p 0, Lit.n 0] ∧ DupFreeClauses [] ∧ RUP [] [Lit.p 0, Lit.n 0] ∧
      ∀ hints, lratRupCheck [] [Lit.p 0, Lit.n 0] hints = false := by
  refine ⟨fun h => h (Lit.p 0) (by simp) (by decide), fun _ hD => absurd hD List.not_mem_nil,
    ⟨0, by decide⟩, fun hints => ?_⟩
  cases hints <;> rfl

/-- **Incompleteness with repeated literals.** The empty clause (which has no complementary
pair) is RUP w.r.t. `(x₀ ∨ x₀) ∧ (¬x₀ ∨ ¬x₀)`, and `lratRupCheck` rejects every hint list,
because each clause has two non-falsified literal occurrences under the empty trail. -/
theorem lratRupCheck_incomplete_dup_lits :
    NonTautological [] ∧ ¬ DupFreeClauses [[Lit.p 0, Lit.p 0], [Lit.n 0, Lit.n 0]] ∧
      RUP [[Lit.p 0, Lit.p 0], [Lit.n 0, Lit.n 0]] [] ∧
      ∀ hints, lratRupCheck [[Lit.p 0, Lit.p 0], [Lit.n 0, Lit.n 0]] [] hints = false := by
  refine ⟨fun _ hl => absurd hl List.not_mem_nil, fun h => ?_, ⟨1, by decide⟩, fun hints => ?_⟩
  · exact absurd (h [Lit.p 0, Lit.p 0] List.mem_cons_self) (by decide)
  · cases hints with
    | nil => rfl
    | cons i is =>
      cases i with
      | zero => rfl
      | succ j =>
        cases j with
        | zero => rfl
        | succ k => cases k <;> rfl

theorem hintReplay_blocked_resolvent_false :
    ∀ (hints : List Nat) (τ : Trail), Lit.p 0 ∉ τ → Lit.n 1 ∈ τ →
      hintReplay [[Lit.n 0, Lit.p 1]] τ hints = false
  | [], _, _, _ => rfl
  | i :: is, τ, hno0, hmem1 => by
    cases i with
    | zero =>
      have hf0 : falsified τ (Lit.n 0) = false := decide_eq_false hno0
      have hf1 : falsified τ (Lit.p 1) = true := decide_eq_true hmem1
      have hfilt : ([Lit.n 0, Lit.p 1] : Clause).filter (fun l => !falsified τ l) = [Lit.n 0] := by
        simp [hf0, hf1]
      simp only [hintReplay, List.getElem?_cons_zero, hfilt]
      apply hintReplay_blocked_resolvent_false is (Lit.n 0 :: τ)
      · intro hmem
        rcases List.mem_cons.1 hmem with h | h
        · exact absurd h (by decide)
        · exact hno0 h
      · exact List.mem_cons_of_mem _ hmem1
    | succ k => cases k <;> rfl

/-- The tautological resolvent `x₀ ∨ ¬x₁ ∨ x₁` of the blocked clause in `RAT_example_pos` is RUP
w.r.t. `¬x₀ ∨ x₁` at budget 0, but `lratRupCheck` rejects every hint list for it. A hint
checker without the trail-pair test cannot confirm such RAT resolvents. -/
theorem lratRupCheck_rejects_blocked_resolvent :
    RUP [[Lit.n 0, Lit.p 1]] (resolventOn [Lit.p 0, Lit.n 1] [Lit.n 0, Lit.p 1] (Lit.p 0)) ∧
      ∀ hints, lratRupCheck [[Lit.n 0, Lit.p 1]]
        (resolventOn [Lit.p 0, Lit.n 1] [Lit.n 0, Lit.p 1] (Lit.p 0)) hints = false :=
  ⟨⟨0, by decide⟩, fun hints =>
    hintReplay_blocked_resolvent_false hints (negClause [Lit.p 0, Lit.n 1, Lit.p 1])
      (by decide) (by decide)⟩

/-- The deduplicating checker accepts the three instances rejected above. -/
theorem lratRupCheckDedup_accepts_rejected_instances :
    lratRupCheckDedup [] [Lit.p 0, Lit.n 0] [] = true ∧
      lratRupCheckDedup [[Lit.p 0, Lit.p 0], [Lit.n 0, Lit.n 0]] [] [0, 1] = true ∧
      lratRupCheckDedup [[Lit.n 0, Lit.p 1]]
        (resolventOn [Lit.p 0, Lit.n 1] [Lit.n 0, Lit.p 1] (Lit.p 0)) [] = true := by
  decide

/-! ## Examples -/

section Examples

/-- Positive example of `lratRupCheck`: `x₀ ∧ (¬x₀ ∨ x₁)` derives `x₁` with hints `[1, 0]`:
under `¬x₁`, clause 1 is unit and assigns `¬x₀`, then clause 0 is falsified. -/
theorem lratRupCheck_example_pos :
    lratRupCheck [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] [1, 0] = true := by decide

/-- Negative example of `lratRupCheck`: a dangling clause index is rejected. -/
theorem lratRupCheck_example_neg :
    lratRupCheck [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] [1, 7] = false := by decide

/-- Negative example of `lratRupCheck`: an empty hint list never succeeds. -/
theorem lratRupCheck_nil (F : Formula) (C : Clause) : lratRupCheck F C [] = false := rfl

/-- Example: a hinted clause that is already satisfied is accepted. Under the trail
`x₀, ¬x₁` (the negation of `¬x₀ ∨ x₁`), clause 0 `x₀ ∨ x₁` has the single non-falsified
literal `x₀`, which is already true; clause 1 `¬x₀` is then falsified. -/
theorem lratRupCheck_example_satisfied_hint :
    lratRupCheck [[Lit.p 0, Lit.p 1], [Lit.n 0]] [Lit.n 0, Lit.p 1] [0, 1] = true := by decide

/-- Example: hints after the first falsified clause are not examined, even dangling ones. -/
theorem lratRupCheck_example_trailing_hints :
    lratRupCheck [[Lit.p 0], [Lit.n 0]] [] [0, 1, 999, 888] = true := by decide

/-- Positive example of `sloppyHintReplay`: on `x₀ ∧ ¬x₀` it accepts hints `[0, 1]`. -/
theorem sloppyHintReplay_example_pos : sloppyHintReplay [[Lit.p 0], [Lit.n 0]] [] [0, 1] = true := by
  decide

/-- Negative example of `sloppyHintReplay`: a list of hints that never reaches a falsified
clause is rejected. -/
theorem sloppyHintReplay_example_neg : sloppyHintReplay [[Lit.p 0, Lit.p 1]] [] [0] = false := by
  decide

/-- Negative example of `sloppyHintReplay`: a dangling index is rejected. -/
theorem sloppyHintReplay_example_neg_dangling : sloppyHintReplay [[Lit.p 0]] [] [5] = false := by
  decide

/-- Positive example of `NonTautological`. -/
theorem NonTautological_example_pos : NonTautological [Lit.p 0, Lit.p 1] := by
  intro l hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> decide

/-- Negative example of `NonTautological`. -/
theorem NonTautological_example_neg : ¬ NonTautological [Lit.p 0, Lit.n 0] :=
  lratRupCheck_incomplete_tautology.1

/-- Positive example of `DupFreeClauses`. -/
theorem DupFreeClauses_example_pos : DupFreeClauses chain3 := by
  intro D hD
  simp only [chain3, List.mem_cons, List.not_mem_nil, or_false] at hD
  rcases hD with rfl | rfl | rfl <;> decide

/-- Negative example of `DupFreeClauses`. -/
theorem DupFreeClauses_example_neg : ¬ DupFreeClauses [[Lit.p 0, Lit.p 0]] :=
  fun h => absurd (h [Lit.p 0, Lit.p 0] List.mem_cons_self) (by decide)

end Examples

end Toy.Drat
