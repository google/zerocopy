import ClaimStrength.Drift

/-!
# Testing readers at the frontier

Over a finite list `Q` of candidate claims, the unsupported claims (`¬ Supported E q`) are closed
upward in strength. (Undetermined claims are not: strengthening an undetermined claim can make it
contradicted, `undetermined_not_upward_closed`.) The *frontier* is the set of weakest unsupported
candidates. A reader whose endorsed set is closed under entailment within `Q` and who endorses no
frontier claim endorses no unsupported candidate of `Q`.
-/

namespace Toy.ClaimStrength

variable {W : Type}

/-- `q` is a weakest unsupported candidate: it is in `Q`, unsupported by `E`, and every
unsupported candidate it entails entails it back. -/
def Frontier (E Q : List (Claim W)) (q : Claim W) : Prop :=
  q ∈ Q ∧ ¬ Supported E q ∧ ∀ q' ∈ Q, ¬ Supported E q' → Entails q q' → Entails q' q

/-- The endorsed set is closed under entailment among the candidates `Q`. -/
def ClosedUnderEntailmentIn (Q : List (Claim W)) (End : Claim W → Prop) : Prop :=
  ∀ q ∈ Q, ∀ q' ∈ Q, End q → Entails q q' → End q'

/-- Unsupported claims are closed upward in strength: if `q` is unsupported and `q'` entails `q`,
then `q'` is unsupported. -/
theorem unsupported_of_entails {E : List (Claim W)} {q q' : Claim W}
    (h : ¬ Supported E q) (h' : Entails q' q) : ¬ Supported E q' :=
  fun hs => h (fun w hw => h' w (hs w hw))

/-- Every nonempty finite list of claims has an entailment-weakest element. -/
theorem exists_weakest :
    ∀ (L : List (Claim W)), L ≠ [] → ∃ m ∈ L, ∀ x ∈ L, Entails m x → Entails x m
  | [], h => absurd rfl h
  | [a], _ => ⟨a, List.mem_singleton_self a, fun x hx _ => by
      rw [List.mem_singleton] at hx; subst hx; exact entails_refl x⟩
  | a :: b :: rest, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_weakest (b :: rest) (List.cons_ne_nil _ _)
    by_cases hc : Entails m a ∧ ¬ Entails a m
    · refine ⟨a, List.mem_cons_self, fun x hx hax => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact entails_refl _
      · exact entails_trans (hmin x hx (entails_trans hc.1 hax)) hc.1
    · refine ⟨m, List.mem_cons_of_mem _ hm, fun x hx hmx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Classical.byContradiction fun hn => hc ⟨hmx, hn⟩
      · exact hmin x hx hmx

/-- If `q ∈ Q` is unsupported, it entails some frontier candidate. -/
theorem exists_frontier_below {E Q : List (Claim W)} {q : Claim W} (hq : q ∈ Q)
    (hns : ¬ Supported E q) : ∃ q', Frontier E Q q' ∧ Entails q q' := by
  classical
  let L := Q.filter (fun q' => decide (¬ Supported E q' ∧ Entails q q'))
  have hqL : q ∈ L := List.mem_filter.2 ⟨hq, by simp [hns, entails_refl]⟩
  obtain ⟨m, hmL, hmin⟩ := exists_weakest L (List.ne_nil_of_mem hqL)
  have hm := List.mem_filter.1 hmL
  simp only [decide_eq_true_eq] at hm
  refine ⟨m, ⟨hm.1, hm.2.1, fun q' hq' hns' hmq' => hmin q' ?_ hmq'⟩, hm.2.2⟩
  exact List.mem_filter.2 ⟨hq', by simp [hns', entails_trans hm.2.2 hmq']⟩

/-- **Frontier testing.** If the reader's endorsed set is closed under entailment among the
candidates `Q`, and the reader endorses no frontier candidate, then every endorsed candidate is
supported by the report. -/
theorem frontier_test_detects_overreading {E Q : List (Claim W)} {End : Claim W → Prop}
    (hclosed : ClosedUnderEntailmentIn Q End) (hfront : ∀ q, Frontier E Q q → ¬ End q) :
    ∀ q ∈ Q, End q → Supported E q := by
  intro q hq hE
  apply Classical.byContradiction
  intro hns
  obtain ⟨q', hf, hqq'⟩ := exists_frontier_below hq hns
  exact hfront q' hf (hclosed q hq q' hf.1 hE hqq')

/-! ## Examples, tightness, non-vacuity -/

/-- A strong unsupported claim. -/
def qStrong : Claim Nat := fun n => n = 1
/-- A weaker unsupported claim, entailed by `qStrong`. -/
def qWeak : Claim Nat := fun n => n ≠ 0
/-- A supported claim. -/
def qTriv : Claim Nat := fun _ => True
/-- The candidate list. -/
def candidates : List (Claim Nat) := [qStrong, qWeak, qTriv]

theorem qStrong_ne_qWeak : qStrong ≠ qWeak := by
  intro h
  have := congrFun h 2
  simp [qStrong, qWeak] at this

theorem qStrong_ne_qTriv : qStrong ≠ qTriv := by
  intro h
  have := congrFun h 2
  simp [qStrong, qTriv] at this

theorem qWeak_ne_qTriv : qWeak ≠ qTriv := by
  intro h
  have := congrFun h 0
  simp [qWeak, qTriv] at this

theorem qStrong_unsupported : ¬ Supported ([] : List (Claim Nat)) qStrong := by
  intro h; have := (supported_nil_iff _).1 h 0; simp [qStrong] at this

theorem qWeak_unsupported : ¬ Supported ([] : List (Claim Nat)) qWeak := by
  intro h; have := (supported_nil_iff _).1 h 0; simp [qWeak] at this

theorem qStrong_entails_qWeak : Entails qStrong qWeak := by
  intro n h; simp [qStrong, qWeak] at h ⊢; omega

theorem qWeak_not_entails_qStrong : ¬ Entails qWeak qStrong := by
  intro h; have := h 2 (by simp [qWeak]); simp [qStrong] at this

theorem frontier_example_pos : Frontier [] candidates qWeak := by
  refine ⟨by simp [candidates], qWeak_unsupported, fun q' hq' hns' hwq' => ?_⟩
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl
  · exact absurd (hwq' 2 (by simp [qWeak])) (by simp [qStrong])
  · exact entails_refl _
  · exact absurd (fun _ _ => trivial) hns'

theorem frontier_example_neg : ¬ Frontier [] candidates qStrong := by
  rintro ⟨-, -, h⟩
  exact qWeak_not_entails_qStrong (h qWeak (by simp [candidates]) qWeak_unsupported
    qStrong_entails_qWeak)

theorem closed_example_pos :
    ClosedUnderEntailmentIn candidates (fun q => Supported ([] : List (Claim Nat)) q) :=
  fun _ _ _ _ hs he w hw => he w (hs w hw)

theorem closed_example_neg : ¬ ClosedUnderEntailmentIn candidates (fun q => q = qStrong) := by
  intro h
  exact qStrong_ne_qWeak (h qStrong (by simp [candidates]) qWeak (by simp [candidates]) rfl
    qStrong_entails_qWeak).symm

/-- Tightness of `hclosed` in `frontier_test_detects_overreading` and in
`frontier_test_no_positiveOverReading` (witness class: three candidates over `Nat` with the empty
report): a reader endorsing only the strong claim satisfies `hfront` (it endorses no frontier
claim), and the conclusions of both theorems fail (it endorses an unsupported candidate, for
which answering *supported* is a positive over-reading). -/
theorem frontier_test_hclosed_tight :
    ¬ ClosedUnderEntailmentIn candidates (fun q => q = qStrong) ∧
    (∀ q, Frontier [] candidates q → ¬ (fun q => q = qStrong) q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qStrong) q → Supported [] q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qStrong) q → ¬ PositiveOverReading [] q .supported) := by
  refine ⟨closed_example_neg, fun q hf hq => ?_, fun h => ?_, fun h => ?_⟩
  · simp only at hq; subst hq; exact frontier_example_neg hf
  · exact qStrong_unsupported (h qStrong (by simp [candidates]) rfl)
  · exact h qStrong (by simp [candidates]) rfl ⟨rfl, qStrong_unsupported⟩

/-- Tightness of `hfront` in `frontier_test_detects_overreading` and in
`frontier_test_no_positiveOverReading` (witness class: three candidates over `Nat` with the empty
report): a reader closed under entailment among the candidates (`hclosed`) endorses the frontier
claim, and the conclusions of both theorems fail (it endorses an unsupported candidate). -/
theorem frontier_test_hfront_tight :
    ClosedUnderEntailmentIn candidates (fun q => q = qWeak ∨ q = qTriv) ∧
    ¬ (∀ q, Frontier [] candidates q → ¬ (fun q => q = qWeak ∨ q = qTriv) q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qWeak ∨ q = qTriv) q → Supported [] q) ∧
    ¬ (∀ q ∈ candidates, (fun q => q = qWeak ∨ q = qTriv) q →
        ¬ PositiveOverReading [] q .supported) := by
  refine ⟨fun q hq q' hq' hE he => ?_, fun h => h qWeak frontier_example_pos (Or.inl rfl),
    fun h => qWeak_unsupported (h qWeak (by simp [candidates]) (Or.inl rfl)),
    fun h => h qWeak (by simp [candidates]) (Or.inl rfl) ⟨rfl, qWeak_unsupported⟩⟩
  simp only [candidates, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with rfl | rfl | rfl
  · rcases hE with rfl | rfl
    · exact absurd (he 2 (by simp [qWeak])) (by simp [qStrong])
    · exact absurd (he 2 trivial) (by simp [qStrong])
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Non-vacuity: the reader who endorses exactly the supported candidates satisfies both
hypotheses, with a non-empty frontier. -/
theorem frontier_test_nonvacuous :
    ClosedUnderEntailmentIn candidates (fun q => Supported ([] : List (Claim Nat)) q) ∧
    (∀ q, Frontier [] candidates q → ¬ Supported ([] : List (Claim Nat)) q) ∧
    Frontier [] candidates qWeak :=
  ⟨closed_example_pos, fun _ hf => hf.2.1, frontier_example_pos⟩

/-! ## Connections and limits -/

/-- In terms of the reading-error predicates: under the hypotheses of
`frontier_test_detects_overreading`, answering *supported* for an endorsed candidate is never a
positive over-reading. -/
theorem frontier_test_no_positiveOverReading {E Q : List (Claim W)} {End : Claim W → Prop}
    (hclosed : ClosedUnderEntailmentIn Q End) (hfront : ∀ q, Frontier E Q q → ¬ End q) :
    ∀ q ∈ Q, End q → ¬ PositiveOverReading E q .supported :=
  fun q hq hE ⟨_, hns⟩ => hns (frontier_test_detects_overreading hclosed hfront q hq hE)

/-- Undetermined claims are not closed upward in strength: over `Nat`, `n = 0` is undetermined by
`[n ≤ 1]`, `False` entails it, and `False` is not undetermined (it is contradicted). -/
theorem undetermined_not_upward_closed :
    Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0) ∧
    Entails (fun _ : Nat => False) (fun n => n = 0) ∧
    ¬ Undetermined [fun n : Nat => n ≤ 1] (fun _ => False) :=
  ⟨undetermined_example_pos, fun _ h => h.elim, fun h => h.2 (fun _ _ h => h)⟩

/-- Claims are predicates, so every endorsement predicate `End : Claim W → Prop` treats logically
equivalent claims alike: framing effects between equivalent phrasings are not representable. -/
theorem endorsement_respects_equivalence (End : Claim W → Prop) {q₁ q₂ : Claim W}
    (h₁ : Entails q₁ q₂) (h₂ : Entails q₂ q₁) : End q₁ ↔ End q₂ := by
  have heq : q₁ = q₂ := funext fun w => propext ⟨h₁ w, h₂ w⟩
  rw [heq]

/-- Frontier testing says nothing about claims outside the candidate list: with `Q = [qTriv]`, a
reader endorsing only `qStrong` (which is not in `Q`) satisfies both hypotheses vacuously and
endorses an unsupported claim. -/
theorem frontier_test_outside_candidates :
    ClosedUnderEntailmentIn [qTriv] (fun q => q = qStrong) ∧
    (∀ q, Frontier [] [qTriv] q → ¬ (fun q => q = qStrong) q) ∧
    qStrong ∉ [qTriv] ∧ ¬ Supported ([] : List (Claim Nat)) qStrong := by
  refine ⟨fun q hq _ _ hE _ => ?_, fun q hf hq => ?_, ?_, qStrong_unsupported⟩
  · simp at hq; subst hq; exact absurd hE qStrong_ne_qTriv.symm
  · simp only at hq; subst hq
    have := hf.1; simp at this; exact qStrong_ne_qTriv this
  · simp; exact qStrong_ne_qTriv

/-- Tightness of `h` in `unsupported_of_entails` (witness class: the empty report over `Nat`),
with `q = q' = qTriv`: `q` is supported (`h` fails), `q'` entails `q`, and `q'` is supported (the
conclusion fails). -/
theorem unsupported_of_entails_h_tight :
    Supported ([] : List (Claim Nat)) qTriv ∧ Entails qTriv qTriv ∧
    Supported ([] : List (Claim Nat)) qTriv :=
  ⟨fun _ _ => trivial, fun _ h => h, fun _ _ => trivial⟩

/-- Tightness of `h'` in `unsupported_of_entails` (witness class: the empty report over `Nat`):
`qStrong` is unsupported, `qTriv` does not entail it, and `qTriv` is supported. -/
theorem unsupported_of_entails_h'_tight :
    ¬ Supported ([] : List (Claim Nat)) qStrong ∧ ¬ Entails qTriv qStrong ∧
    Supported ([] : List (Claim Nat)) qTriv :=
  ⟨qStrong_unsupported, fun h => by simpa [qStrong, qTriv] using h 0 trivial,
    fun _ _ => trivial⟩

/-- Non-vacuity of `unsupported_of_entails`: `qWeak` is unsupported and `qStrong` entails it. -/
theorem unsupported_of_entails_nonvacuous :
    ¬ Supported ([] : List (Claim Nat)) qWeak ∧ Entails qStrong qWeak :=
  ⟨qWeak_unsupported, qStrong_entails_qWeak⟩

/-- Tightness of `hq` in `exists_frontier_below` (witness class: a one-candidate list over `Nat`
with the empty report): `n = 1` is not a candidate, is unsupported, and entails no frontier
candidate. -/
theorem exists_frontier_below_hq_tight :
    (fun n : Nat => n = 1) ∉ [fun n : Nat => n = 2] ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 1) ∧
    ¬ (∃ q', Frontier ([] : List (Claim Nat)) [fun n => n = 2] q' ∧
      Entails (fun n : Nat => n = 1) q') := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.mem_singleton]
    intro h; have := congrFun h 1; simp at this
  · intro hs; have := hs 0 (models_nil 0); simp at this
  · rintro ⟨q', ⟨hq', _, _⟩, he⟩
    rw [List.mem_singleton] at hq'; subst hq'
    have := he 1 rfl; omega

/-- Tightness of `hns` in `exists_frontier_below` (witness class: three candidates over `Nat`
with the empty report): `qTriv` is a supported candidate and entails no frontier candidate. -/
theorem exists_frontier_below_hns_tight :
    qTriv ∈ candidates ∧ Supported ([] : List (Claim Nat)) qTriv ∧
    ¬ (∃ q', Frontier ([] : List (Claim Nat)) candidates q' ∧ Entails qTriv q') := by
  refine ⟨by simp [candidates], fun _ _ => trivial, ?_⟩
  rintro ⟨q', hf, he⟩
  exact hf.2.1 (fun w _ => he w trivial)

/-- Non-vacuity of `exists_frontier_below`: `qStrong` is an unsupported candidate. -/
theorem exists_frontier_below_nonvacuous :
    qStrong ∈ candidates ∧ ¬ Supported ([] : List (Claim Nat)) qStrong :=
  ⟨by simp [candidates], qStrong_unsupported⟩

/-- Tightness of `L ≠ []` in `exists_weakest` (witness class: the empty list of claims over
`Nat`): the hypothesis fails for the empty list, which has no weakest element. -/
theorem exists_weakest_tight :
    ¬ (([] : List (Claim Nat)) ≠ []) ∧
    ¬ (∃ m ∈ ([] : List (Claim Nat)), ∀ x ∈ ([] : List (Claim Nat)), Entails m x → Entails x m) :=
  ⟨fun h => h rfl, by simp⟩

/-- Non-vacuity of `exists_weakest`: the candidate list is nonempty. -/
theorem exists_weakest_nonvacuous : candidates ≠ [] := by simp [candidates]

/-- Tightness of `h₁` in `endorsement_respects_equivalence` (witness class: claims over `Nat`,
`q₁ = qWeak`, `q₂ = qStrong`): `qWeak` does not entail `qStrong` (`h₁` fails), `qStrong` entails
`qWeak` (`h₂` holds), and the endorsement predicate `q = qStrong` separates them. -/
theorem endorsement_respects_equivalence_h₁_tight :
    ¬ Entails qWeak qStrong ∧ Entails qStrong qWeak ∧
    ¬ ((fun q => q = qStrong) qWeak ↔ (fun q => q = qStrong) qStrong) :=
  ⟨qWeak_not_entails_qStrong, qStrong_entails_qWeak,
    fun h => qStrong_ne_qWeak (h.2 rfl).symm⟩

/-- Tightness of `h₂` in `endorsement_respects_equivalence` (witness class: claims over `Nat`,
`q₁ = qStrong`, `q₂ = qWeak`): `qStrong` entails `qWeak` (`h₁` holds), `qWeak` does not entail
`qStrong` (`h₂` fails), and the endorsement predicate `q = qStrong` separates them. -/
theorem endorsement_respects_equivalence_h₂_tight :
    Entails qStrong qWeak ∧ ¬ Entails qWeak qStrong ∧
    ¬ ((fun q => q = qStrong) qStrong ↔ (fun q => q = qStrong) qWeak) :=
  ⟨qStrong_entails_qWeak, qWeak_not_entails_qStrong,
    fun h => qStrong_ne_qWeak (h.1 rfl).symm⟩

/-- Non-vacuity of `endorsement_respects_equivalence`: `qWeak` and `n ≠ 0 ∧ True` are distinct
expressions of equivalent claims over `Nat`. -/
theorem endorsement_respects_equivalence_nonvacuous :
    Entails qWeak (fun n => n ≠ 0 ∧ True) ∧ Entails (fun n => n ≠ 0 ∧ True) qWeak :=
  ⟨fun _ h => ⟨h, trivial⟩, fun _ h => h.1⟩

end Toy.ClaimStrength
