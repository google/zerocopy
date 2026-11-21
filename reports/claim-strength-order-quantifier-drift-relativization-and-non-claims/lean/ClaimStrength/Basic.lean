/-!
# Claims, reports, and the three answers

A *claim* is a proposition over a space of interpretations `W` ("worlds"). A *report* is a
finite list `E` of claims it establishes. A reader asked about a candidate claim `q` can answer
*supported* (every world consistent with `E` satisfies `q`), *contradicted* (no world consistent
with `E` satisfies `q`), or *undetermined* (neither).

Vocabulary. Each phrase below names exactly one predicate:
* "supported" (also "established"): `Supported E q`;
* "unsupported" (also "not established"): `¬ Supported E q`;
* "contradicted": `Contradicted E q`; "not contradicted": `¬ Contradicted E q`;
* "undetermined": `Undetermined E q`, that is, unsupported and not contradicted.
An unsupported claim can be contradicted; an undetermined claim cannot.

This file is a toy model: worlds are an arbitrary type, claims are arbitrary predicates, and a
report is identified with the set of claims it establishes. It does not model natural language,
the content of any real report, or how a reader arrives at an answer.
-/

namespace Toy.ClaimStrength

/-- A claim: a proposition about an interpretation `w : W`. -/
abbrev Claim (W : Type) := W → Prop

variable {W : Type}

/-- Entailment between claims: every interpretation satisfying `A` satisfies `B`. -/
def Entails (A B : Claim W) : Prop := ∀ w, A w → B w

/-- The interpretations consistent with every claim established by the report `E`. -/
def Models (E : List (Claim W)) (w : W) : Prop := ∀ e ∈ E, e w

/-- A report is satisfiable when some interpretation is consistent with all of it. -/
def Satisfiable (E : List (Claim W)) : Prop := ∃ w, Models E w

/-- `q` is *supported* by `E`: every interpretation consistent with `E` satisfies `q`. Its
negation `¬ Supported E q` is called *unsupported*. -/
def Supported (E : List (Claim W)) (q : Claim W) : Prop := ∀ w, Models E w → q w

/-- `q` is *contradicted* by `E`: no interpretation consistent with `E` satisfies `q`. -/
def Contradicted (E : List (Claim W)) (q : Claim W) : Prop := ∀ w, Models E w → ¬ q w

/-- `q` is *undetermined* by `E`: unsupported and not contradicted. (This is strictly stronger
than *unsupported*, `¬ Supported E q`, which also holds for contradicted claims of a satisfiable
report.) -/
def Undetermined (E : List (Claim W)) (q : Claim W) : Prop :=
  ¬ Supported E q ∧ ¬ Contradicted E q

/-- The three answers a reader can give about a candidate claim. -/
inductive Answer
  | supported
  | undetermined
  | contradicted
  deriving DecidableEq, Repr

/-- `Correct E q a`: `a` is a correct answer about `q` given the report `E`. -/
def Correct (E : List (Claim W)) (q : Claim W) : Answer → Prop
  | .supported => Supported E q
  | .undetermined => Undetermined E q
  | .contradicted => Contradicted E q

/-- Exactly one of three propositions holds. -/
def ExactlyOne3 (a b c : Prop) : Prop :=
  (a ∧ ¬ b ∧ ¬ c) ∨ (¬ a ∧ b ∧ ¬ c) ∨ (¬ a ∧ ¬ b ∧ c)

/-- Positive over-reading: answering *supported* for an unsupported claim. -/
def PositiveOverReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .supported ∧ ¬ Supported E q

/-- Negative over-reading: answering *contradicted* for a claim that is not contradicted. -/
def NegativeOverReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .contradicted ∧ ¬ Contradicted E q

/-- Under-reading: answering *undetermined* for a claim that is supported or contradicted. -/
def UnderReading (E : List (Claim W)) (q : Claim W) (a : Answer) : Prop :=
  a = .undetermined ∧ (Supported E q ∨ Contradicted E q)

/-- A claim whose truth does not depend on the interpretation (for example, a statement about
the report itself rather than about the world). -/
def WorldIndependent (q : Claim W) : Prop := ∀ w w', q w → q w'

/-- The meta-level question "the report `E` establishes `q`", as a claim. It ignores its
argument: its truth is fixed once `E` and `q` are fixed. -/
def Establishes (E : List (Claim W)) (q : Claim W) : Claim W := fun _ => Supported E q

/-- An answer key: a list of questions with the answers it marks as correct. -/
abbrev AnswerKey (W : Type) := List (Claim W × Answer)

/-- Every entry of the answer key is a correct answer given `E`. -/
def KeyCorrect (E : List (Claim W)) (key : AnswerKey W) : Prop :=
  ∀ p ∈ key, Correct E p.1 p.2

/-! ## Definition examples -/

theorem entails_example_pos : Entails (fun n : Nat => n = 0) (fun n => n ≤ 1) := by
  intro n h; omega

theorem entails_example_neg : ¬ Entails (fun n : Nat => n ≤ 1) (fun n => n = 0) := by
  intro h; have := h 1 (by omega); omega

theorem models_example_pos : Models [fun n : Nat => n ≤ 3, fun n => 1 ≤ n] 2 := by
  intro e he; simp at he; rcases he with rfl | rfl <;> omega

theorem models_example_neg : ¬ Models [fun n : Nat => n ≤ 3, fun n => 1 ≤ n] 5 := by
  intro h; have := h (fun n => n ≤ 3) (by simp); omega

theorem satisfiable_example_pos : Satisfiable [fun n : Nat => n ≤ 3] :=
  ⟨0, by intro e he; simp at he; subst he; omega⟩

theorem satisfiable_example_neg : ¬ Satisfiable [fun n : Nat => n = 0, fun n => n = 1] := by
  rintro ⟨w, hw⟩
  have h0 := hw (fun n => n = 0) (by simp)
  have h1 := hw (fun n => n = 1) (by simp)
  have h0' : w = 0 := h0
  have h1' : w = 1 := h1
  omega

theorem supported_example_pos : Supported [fun n : Nat => n = 0] (fun n => n ≤ 1) := by
  intro w hw; have h' : w = 0 := hw (fun n => n = 0) (by simp); show w ≤ 1; omega

theorem supported_example_neg : ¬ Supported [fun n : Nat => n ≤ 1] (fun n => n = 0) := by
  intro h
  have := h 1 (by intro e he; simp at he; subst he; omega)
  omega

theorem contradicted_example_pos : Contradicted [fun n : Nat => n = 0] (fun n => n = 1) := by
  intro w hw; have h' : w = 0 := hw (fun n => n = 0) (by simp); show ¬ w = 1; omega

theorem contradicted_example_neg : ¬ Contradicted [fun n : Nat => n ≤ 1] (fun n => n = 0) := by
  intro h
  exact h 0 (by intro e he; simp at he; subst he; omega) rfl

theorem undetermined_example_pos : Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0) :=
  ⟨supported_example_neg, contradicted_example_neg⟩

theorem undetermined_example_neg : ¬ Undetermined [fun n : Nat => n = 0] (fun n => n ≤ 1) :=
  fun h => h.1 supported_example_pos

theorem correct_example_pos : Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined :=
  undetermined_example_pos

theorem correct_example_neg : ¬ Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .contradicted :=
  contradicted_example_neg

theorem exactlyOne3_example_pos : ExactlyOne3 True False False := by
  simp [ExactlyOne3]

theorem exactlyOne3_example_neg : ¬ ExactlyOne3 True True False := by
  simp [ExactlyOne3]

theorem positiveOverReading_example_pos :
    PositiveOverReading [fun n : Nat => n ≤ 1] (fun n => n = 0) .supported :=
  ⟨rfl, supported_example_neg⟩

theorem positiveOverReading_example_neg :
    ¬ PositiveOverReading [fun n : Nat => n = 0] (fun n => n ≤ 1) .supported :=
  fun h => h.2 supported_example_pos

theorem negativeOverReading_example_pos :
    NegativeOverReading [fun n : Nat => n ≤ 1] (fun n => n = 0) .contradicted :=
  ⟨rfl, contradicted_example_neg⟩

theorem negativeOverReading_example_neg :
    ¬ NegativeOverReading [fun n : Nat => n = 0] (fun n => n = 1) .contradicted :=
  fun h => h.2 contradicted_example_pos

theorem underReading_example_pos :
    UnderReading [fun n : Nat => n = 0] (fun n => n ≤ 1) .undetermined :=
  ⟨rfl, Or.inl supported_example_pos⟩

theorem underReading_example_neg :
    ¬ UnderReading [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined := by
  rintro ⟨-, h | h⟩
  · exact supported_example_neg h
  · exact contradicted_example_neg h

theorem worldIndependent_example_pos : WorldIndependent (fun _ : Nat => 2 + 2 = 4) :=
  fun _ _ h => h

theorem worldIndependent_example_neg : ¬ WorldIndependent (fun n : Nat => n = 0) := by
  intro h; have := h 0 1 rfl; omega

theorem establishes_example_pos :
    Establishes [fun n : Nat => n = 0] (fun n => n ≤ 1) 7 := supported_example_pos

theorem establishes_example_neg :
    ¬ Establishes [fun n : Nat => n ≤ 1] (fun n => n = 0) 7 := supported_example_neg

theorem keyCorrect_example_pos :
    KeyCorrect [fun n : Nat => n ≤ 1] [((fun n => n = 0), .undetermined)] := by
  intro p hp; simp at hp; subst hp; exact undetermined_example_pos

theorem keyCorrect_example_neg :
    ¬ KeyCorrect [fun n : Nat => n ≤ 1] [((fun n => n = 0), .contradicted)] := by
  intro h; exact contradicted_example_neg (h ((fun n => n = 0), .contradicted) (by simp))

/-! ## Basic lemmas -/

theorem models_nil (w : W) : Models ([] : List (Claim W)) w := by
  intro e he; cases he

theorem supported_nil_iff (q : Claim W) : Supported [] q ↔ ∀ w, q w :=
  ⟨fun h w => h w (models_nil w), fun h w _ => h w⟩

theorem contradicted_nil_iff (q : Claim W) : Contradicted [] q ↔ ∀ w, ¬ q w :=
  ⟨fun h w => h w (models_nil w), fun h w _ => h w⟩

theorem satisfiable_of_unsupported {E : List (Claim W)} {q : Claim W}
    (h : ¬ Supported E q) : Satisfiable E := by
  apply Classical.byContradiction
  intro hs
  exact h (fun w hw => absurd ⟨w, hw⟩ hs)

theorem satisfiable_of_not_contradicted {E : List (Claim W)} {q : Claim W}
    (h : ¬ Contradicted E q) : Satisfiable E := by
  apply Classical.byContradiction
  intro hs
  exact h (fun w hw => absurd ⟨w, hw⟩ hs)

/-! ## The three answers -/

/-- With an unsatisfiable report every claim is both supported and contradicted. -/
theorem unsatisfiable_supported_and_contradicted {E : List (Claim W)}
    (hE : ¬ Satisfiable E) (q : Claim W) : Supported E q ∧ Contradicted E q :=
  ⟨fun w hw => absurd ⟨w, hw⟩ hE, fun w hw => absurd ⟨w, hw⟩ hE⟩

/-- Tightness of `hE` in `unsatisfiable_supported_and_contradicted` (witness class: the empty
report over `Nat`): the report is satisfiable and `True` is supported but not contradicted. -/
theorem unsatisfiable_hE_tight :
    Satisfiable ([] : List (Claim Nat)) ∧
    ¬ (Supported ([] : List (Claim Nat)) (fun _ => True) ∧
      Contradicted ([] : List (Claim Nat)) (fun _ => True)) :=
  ⟨⟨0, models_nil 0⟩, fun h => (contradicted_nil_iff _).1 h.2 0 trivial⟩

/-- Non-vacuity of `unsatisfiable_supported_and_contradicted`: the one-claim report `[False]`
over `Nat` is unsatisfiable. -/
theorem unsatisfiable_nonvacuous : ¬ Satisfiable [fun _ : Nat => False] :=
  fun ⟨w, hw⟩ => hw (fun _ => False) (by simp)

/-- For every report `E` and claim `q`: exactly one of the three answers is correct iff `E` is
satisfiable. -/
theorem exactlyOne_answer_iff_satisfiable (E : List (Claim W)) (q : Claim W) :
    ExactlyOne3 (Supported E q) (Contradicted E q) (Undetermined E q) ↔ Satisfiable E := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hE
    obtain ⟨hs, hc⟩ := unsatisfiable_supported_and_contradicted hE q
    rcases h with ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · exact h hc
    · exact h hs
    · exact h hs
  · rintro ⟨w, hw⟩
    by_cases hs : Supported E q
    · have hc : ¬ Contradicted E q := fun hc => hc w hw (hs w hw)
      exact Or.inl ⟨hs, hc, fun h => h.1 hs⟩
    · by_cases hc : Contradicted E q
      · exact Or.inr (Or.inl ⟨hs, hc, fun h => h.2 hc⟩)
      · exact Or.inr (Or.inr ⟨hs, hc, hs, hc⟩)

/-- Over a satisfiable report the correct answer is unique: if `E` is satisfiable and both `a`
and `b` are correct answers about `q`, then `a = b`. -/
theorem correct_unique_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E) {q : Claim W}
    {a b : Answer} (ha : Correct E q a) (hb : Correct E q b) : a = b := by
  obtain ⟨w, hw⟩ := hE
  cases a <;> cases b <;> simp only [Correct, Undetermined] at ha hb ⊢
  all_goals first
    | rfl
    | exact absurd ha hb.1 | exact absurd hb ha.1
    | exact absurd ha hb.2 | exact absurd hb ha.2
    | exact absurd (ha w hw) (hb w hw) | exact absurd (hb w hw) (ha w hw)

/-- Tightness of `hE` in `correct_unique_of_satisfiable` (witness class: the unsatisfiable
one-claim report `[False]` over `Nat`): two different answers are correct. -/
theorem correct_unique_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun _ => True) .contradicted ∧
    Answer.supported ≠ Answer.contradicted := by
  have hns : ¬ Satisfiable [fun _ : Nat => False] :=
    fun ⟨w, hw⟩ => hw (fun _ => False) (by simp)
  exact ⟨hns, (unsatisfiable_supported_and_contradicted hns _).1,
    (unsatisfiable_supported_and_contradicted hns _).2, by decide⟩

/-- Tightness of `ha` in `correct_unique_of_satisfiable` (witness class: a satisfiable one-claim
report over `Nat`): the report is satisfiable, `b = undetermined` is correct, `a = supported` is
not, and `a ≠ b`. -/
theorem correct_unique_ha_tight :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    ¬ Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .supported ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined ∧
    Answer.supported ≠ Answer.undetermined :=
  ⟨⟨0, by intro e he; simp at he; subst he; omega⟩, supported_example_neg,
    undetermined_example_pos, by decide⟩

/-- Tightness of `hb` in `correct_unique_of_satisfiable` (witness class: a satisfiable one-claim
report over `Nat`): the report is satisfiable, `a = undetermined` is correct, `b = supported` is
not, and `a ≠ b`. -/
theorem correct_unique_hb_tight :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined ∧
    ¬ Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .supported ∧
    Answer.undetermined ≠ Answer.supported :=
  ⟨correct_unique_ha_tight.1, undetermined_example_pos, supported_example_neg, by decide⟩

/-- Non-vacuity of `correct_unique_of_satisfiable`: a satisfiable report and a claim for which
`undetermined` is correct (taking `a = b = undetermined`). -/
theorem correct_unique_nonvacuous :
    Satisfiable [fun n : Nat => n ≤ 1] ∧
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined :=
  ⟨correct_unique_ha_tight.1, undetermined_example_pos⟩

/-- Some answer is always correct. -/
theorem exists_correct (E : List (Claim W)) (q : Claim W) : ∃ a, Correct E q a := by
  by_cases hs : Supported E q
  · exact ⟨.supported, hs⟩
  · by_cases hc : Contradicted E q
    · exact ⟨.contradicted, hc⟩
    · exact ⟨.undetermined, hs, hc⟩

/-- The three reading-error predicates classify exactly the incorrect answers: for every report
`E`, claim `q`, and answer `a`, `a` is incorrect iff it is a positive over-reading, a negative
over-reading, or an under-reading. -/
theorem incorrect_iff_reading_error (E : List (Claim W)) (q : Claim W) (a : Answer) :
    ¬ Correct E q a ↔
      PositiveOverReading E q a ∨ NegativeOverReading E q a ∨ UnderReading E q a := by
  cases a
  · simp [Correct, PositiveOverReading, NegativeOverReading, UnderReading]
  · simp only [Correct, Undetermined, PositiveOverReading, NegativeOverReading, UnderReading,
      reduceCtorEq, false_and, true_and, false_or]
    constructor
    · intro h
      by_cases hs : Supported E q
      · exact Or.inl hs
      · exact Or.inr (Classical.byContradiction fun hc => h ⟨hs, hc⟩)
    · rintro (h | h) ⟨hs, hc⟩
      · exact hs h
      · exact hc h
  · simp [Correct, PositiveOverReading, NegativeOverReading, UnderReading]

/-- Extending a report preserves support: if every claim of `E` is in `E'`, a claim supported
by `E` is supported by `E'`. -/
theorem supported_mono {E E' : List (Claim W)} (hsub : ∀ e ∈ E, e ∈ E') {q : Claim W}
    (h : Supported E q) : Supported E' q :=
  fun w hw => h w (fun e he => hw e (hsub e he))

/-- Extending a report preserves contradiction: if every claim of `E` is in `E'`, a claim
contradicted by `E` is contradicted by `E'`. -/
theorem contradicted_mono {E E' : List (Claim W)} (hsub : ∀ e ∈ E, e ∈ E') {q : Claim W}
    (h : Contradicted E q) : Contradicted E' q :=
  fun w hw => h w (fun e he => hw e (hsub e he))

/-- Tightness of `hsub` in `supported_mono` (witness class: one-claim versus empty report over
`Nat`): `n = 0` is supported by `[n = 0]` but not by `[]`, and `[n = 0] ⊄ []`. -/
theorem supported_mono_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Supported [fun n : Nat => n = 0] (fun n => n = 0) ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 0) := by
  refine ⟨fun h => by simpa using h (fun n : Nat => n = 0) (by simp), ?_, ?_⟩
  · intro w hw; exact hw (fun n => n = 0) (by simp)
  · intro h; have := (supported_nil_iff _).1 h 1; omega

/-- Tightness of `hsub` in `contradicted_mono` (witness class: one-claim versus empty report
over `Nat`): `n = 1` is contradicted by `[n = 0]` but not by `[]`. -/
theorem contradicted_mono_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (fun n => n = 1) :=
  ⟨supported_mono_hsub_tight.1, contradicted_example_pos,
    fun h => (contradicted_nil_iff _).1 h 1 rfl⟩

/-- Tightness of `h` in `supported_mono` (witness class: the empty report extended to `[n ≤ 1]`
over `Nat`): `[] ⊆ [n ≤ 1]`, and `n = 0` is supported by neither report. -/
theorem supported_mono_h_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n ≤ 1]) ∧
    ¬ Supported ([] : List (Claim Nat)) (fun n => n = 0) ∧
    ¬ Supported [fun n : Nat => n ≤ 1] (fun n => n = 0) :=
  ⟨by simp, supported_mono_hsub_tight.2.2, supported_example_neg⟩

/-- Tightness of `h` in `contradicted_mono` (witness class: the empty report extended to
`[n ≤ 1]` over `Nat`): `[] ⊆ [n ≤ 1]`, and `n = 0` is contradicted by neither report. -/
theorem contradicted_mono_h_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n ≤ 1]) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (fun n => n = 0) ∧
    ¬ Contradicted [fun n : Nat => n ≤ 1] (fun n => n = 0) :=
  ⟨by simp, fun h => (contradicted_nil_iff _).1 h 0 rfl, contradicted_example_neg⟩

/-- Non-vacuity of `supported_mono` and `contradicted_mono`: `[n = 0] ⊆ [n = 0, n ≤ 5]`, with
`n ≤ 1` supported and `n = 1` contradicted by the smaller report. -/
theorem mono_nonvacuous :
    (∀ e ∈ [fun n : Nat => n = 0], e ∈ [fun n : Nat => n = 0, fun n => n ≤ 5]) ∧
    Supported [fun n : Nat => n = 0] (fun n => n ≤ 1) ∧
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1) :=
  ⟨by intro e he; simp at he; subst he; simp, supported_example_pos, contradicted_example_pos⟩

/-- If every claim of `E` is in `E'` and `E'` is satisfiable, an answer can change from `E` to
`E'` only if the `E`-answer was *undetermined*. -/
theorem answer_changes_only_from_undetermined_of_satisfiable {E E' : List (Claim W)}
    (hsub : ∀ e ∈ E, e ∈ E') (hsat : Satisfiable E') {q : Claim W} {a a' : Answer}
    (ha : Correct E q a) (ha' : Correct E' q a') : a' = a ∨ a = .undetermined := by
  cases a with
  | supported => exact Or.inl (correct_unique_of_satisfiable hsat ha' (supported_mono hsub ha))
  | contradicted =>
    exact Or.inl (correct_unique_of_satisfiable hsat ha' (contradicted_mono hsub ha))
  | undetermined => exact Or.inr rfl

/-- Tightness of `hsub` in `answer_changes_only_from_undetermined_of_satisfiable` (witness
class: one-claim versus empty report over `Nat`): `[n = 0] ⊄ []`, `[]` is satisfiable, and the
answer for `n = 0` changes from *supported* to *undetermined*. -/
theorem answer_changes_hsub_tight :
    ¬ (∀ e ∈ [fun n : Nat => n = 0], e ∈ ([] : List (Claim Nat))) ∧
    Satisfiable ([] : List (Claim Nat)) ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported ∧
    Correct ([] : List (Claim Nat)) (fun n => n = 0) .undetermined ∧
    ¬ ((Answer.undetermined = .supported) ∨ (Answer.supported = .undetermined)) := by
  refine ⟨supported_mono_hsub_tight.1, ⟨0, models_nil 0⟩, supported_mono_hsub_tight.2.1, ?_,
    by simp⟩
  refine ⟨supported_mono_hsub_tight.2.2, ?_⟩
  intro h; exact (contradicted_nil_iff _).1 h 0 rfl

/-- Tightness of `hsat` (witness class: extending the empty report over `Nat` by `False`): the
extension is unsatisfiable and makes *contradicted* correct for a previously supported claim. -/
theorem answer_changes_hsat_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun _ : Nat => False]) ∧
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct ([] : List (Claim Nat)) (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun _ => True) .contradicted ∧
    ¬ ((Answer.contradicted = .supported) ∨ (Answer.supported = .undetermined)) := by
  refine ⟨by simp, unsatisfiable_nonvacuous, fun _ _ => trivial, ?_, by simp⟩
  intro w hw; exact absurd (hw (fun _ => False) (by simp)) id

/-- Tightness of `ha` in `answer_changes_only_from_undetermined_of_satisfiable` (witness class:
the empty report extended to `[n = 0]` over `Nat`, claim `n = 0`): `hsub`, `hsat` and `ha'` (with
`a' = supported`) hold, `a = contradicted` is incorrect for `[]`, and the conclusion fails. -/
theorem answer_changes_ha_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    ¬ Correct ([] : List (Claim Nat)) (fun n => n = 0) .contradicted ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported ∧
    ¬ ((Answer.supported = .contradicted) ∨ (Answer.contradicted = .undetermined)) :=
  ⟨by simp, ⟨0, by intro e he; simp at he; subst he; rfl⟩,
    fun h => (contradicted_nil_iff _).1 h 0 rfl, supported_mono_hsub_tight.2.1, by simp⟩

/-- Tightness of `ha'` in `answer_changes_only_from_undetermined_of_satisfiable` (witness class:
the empty report extended to `[n = 0]` over `Nat`, claim `True`): `hsub`, `hsat` and `ha` (with
`a = supported`) hold, `a' = contradicted` is incorrect for `[n = 0]`, and the conclusion fails. -/
theorem answer_changes_ha'_tight :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    Correct ([] : List (Claim Nat)) (fun _ => True) .supported ∧
    ¬ Correct [fun n : Nat => n = 0] (fun _ => True) .contradicted ∧
    ¬ ((Answer.contradicted = .supported) ∨ (Answer.supported = .undetermined)) :=
  ⟨by simp, ⟨0, by intro e he; simp at he; subst he; rfl⟩, fun _ _ => trivial,
    fun h => h 0 (by intro e he; simp at he; subst he; rfl) trivial, by simp⟩

/-- Non-vacuity of `answer_changes_only_from_undetermined_of_satisfiable`: a genuine change from
*undetermined* to *supported* under a satisfiable report extension. -/
theorem answer_changes_nonvacuous :
    (∀ e ∈ ([] : List (Claim Nat)), e ∈ [fun n : Nat => n = 0]) ∧
    Satisfiable [fun n : Nat => n = 0] ∧
    Correct ([] : List (Claim Nat)) (fun n => n = 0) .undetermined ∧
    Correct [fun n : Nat => n = 0] (fun n => n = 0) .supported :=
  ⟨by simp, ⟨0, by intro e he; simp at he; subst he; rfl⟩,
    answer_changes_hsub_tight.2.2.2.1, answer_changes_hsub_tight.2.2.1⟩

/-- Non-vacuity of `exactlyOne_answer_iff_satisfiable`: a satisfiable report where the unique
correct answer is *undetermined*. -/
theorem exactlyOne_nonvacuous :
    ExactlyOne3 (Supported [fun n : Nat => n ≤ 1] (fun n => n = 0))
      (Contradicted [fun n : Nat => n ≤ 1] (fun n => n = 0))
      (Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0)) :=
  Or.inr (Or.inr ⟨supported_example_neg, contradicted_example_neg, undetermined_example_pos⟩)

/-! ## Undetermined claims and counterexamples -/

/-- `q` is undetermined by `E` iff some interpretation consistent with `E` satisfies `q` and
some interpretation consistent with `E` falsifies it. -/
theorem undetermined_iff_exists_both (E : List (Claim W)) (q : Claim W) :
    Undetermined E q ↔ (∃ w, Models E w ∧ q w) ∧ (∃ w, Models E w ∧ ¬ q w) := by
  constructor
  · rintro ⟨hs, hc⟩
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction
      intro h; exact hc (fun w hw hq => h ⟨w, hw, hq⟩)
    · apply Classical.byContradiction
      intro h; exact hs (fun w hw => Classical.byContradiction fun hq => h ⟨w, hw, hq⟩)
  · rintro ⟨⟨w₁, hw₁, hq₁⟩, ⟨w₂, hw₂, hq₂⟩⟩
    exact ⟨fun h => hq₂ (h w₂ hw₂), fun h => h w₁ hw₁ hq₁⟩

/-- Contradiction is support of the negation. -/
theorem contradicted_iff_supported_not (E : List (Claim W)) (q : Claim W) :
    Contradicted E q ↔ Supported E (fun w => ¬ q w) := Iff.rfl

/-- A claim of the report that entails `¬ q` (for example, an exhibited counterexample to a
universal claim `q`) makes `q` contradicted. -/
theorem contradicted_of_mem_entails_not {E : List (Claim W)} {q c : Claim W} (hc : c ∈ E)
    (hneg : Entails c (fun w => ¬ q w)) : Contradicted E q :=
  fun w hw => hneg w (hw c hc)

/-- Tightness of `hc` in `contradicted_of_mem_entails_not` (witness class: the empty report
over interpretations `Nat → Prop`): the counterexample claim entails `¬ q` but is not part of
the report, and `q` is not contradicted. -/
theorem contradicted_of_mem_hc_tight :
    (fun P : Nat → Prop => ¬ P 0) ∉ ([] : List (Claim (Nat → Prop))) ∧
    Entails (fun P : Nat → Prop => ¬ P 0) (fun P => ¬ (∀ m, P m)) ∧
    ¬ Contradicted ([] : List (Claim (Nat → Prop))) (fun P => ∀ m, P m) := by
  refine ⟨by simp, fun P h0 hall => h0 (hall 0), fun h => ?_⟩
  exact (contradicted_nil_iff _).1 h (fun _ => True) (fun _ => trivial)

/-- Tightness of `hneg` in `contradicted_of_mem_entails_not` (witness class: a one-claim report
over interpretations `Nat → Prop`): a report claim that does not entail `¬ q` need not
contradict `q`. -/
theorem contradicted_of_mem_hneg_tight :
    (fun P : Nat → Prop => P 0) ∈ [fun P : Nat → Prop => P 0] ∧
    ¬ Entails (fun P : Nat → Prop => P 0) (fun P => ¬ (∀ m, P m)) ∧
    ¬ Contradicted [fun P : Nat → Prop => P 0] (fun P => ∀ m, P m) := by
  refine ⟨by simp, fun h => h (fun _ => True) trivial (fun _ => trivial), fun h => ?_⟩
  exact h (fun _ => True) (by intro e he; simp at he; subst he; trivial) (fun _ => trivial)

/-- Non-vacuity of `contradicted_of_mem_entails_not`. -/
theorem contradicted_of_mem_nonvacuous :
    (fun P : Nat → Prop => ¬ P 0) ∈ [fun P : Nat → Prop => ¬ P 0] ∧
    Entails (fun P : Nat → Prop => ¬ P 0) (fun P => ¬ (∀ m, P m)) :=
  ⟨by simp, fun P h0 hall => h0 (hall 0)⟩

/-- A single report claim entailing `¬ q` is sufficient for `Contradicted E q` but not
necessary: over `Nat`, the satisfiable report `[n ≤ 1, 1 ≤ n]` contradicts `n = 0 ∨ n = 2`,
although neither of its claims alone entails the negation. -/
theorem contradicted_jointly_without_single_claim :
    Satisfiable [fun n : Nat => n ≤ 1, fun n => 1 ≤ n] ∧
    Contradicted [fun n : Nat => n ≤ 1, fun n => 1 ≤ n] (fun n => n = 0 ∨ n = 2) ∧
    ∀ c ∈ [fun n : Nat => n ≤ 1, fun n => 1 ≤ n],
      ¬ Entails c (fun n => ¬ (n = 0 ∨ n = 2)) := by
  refine ⟨⟨1, by intro e he; simp at he; rcases he with rfl | rfl <;> simp⟩, ?_, ?_⟩
  · intro w hw hq
    have h1 : w ≤ 1 := hw (fun n => n ≤ 1) (by simp)
    have h2 : 1 ≤ w := hw (fun n => 1 ≤ n) (by simp)
    omega
  · intro c hc
    simp at hc
    rcases hc with rfl | rfl
    · intro h; exact h 0 (by decide) (Or.inl rfl)
    · intro h; exact h 2 (by decide) (Or.inr rfl)

/-- "Unsupported" does not imply "contradicted": over two interpretations with the empty report,
`b = true` is unsupported but not contradicted. -/
theorem unsupported_not_imply_contradicted :
    ¬ (∀ (E : List (Claim Bool)) (q : Claim Bool), ¬ Supported E q → Contradicted E q) := by
  intro h
  have hns : ¬ Supported ([] : List (Claim Bool)) (fun b => b = true) := by
    intro hs; have := (supported_nil_iff _).1 hs false; simp at this
  have := h [] (fun b => b = true) hns
  exact (contradicted_nil_iff _).1 this true rfl

/-- The universal claim "every `m` satisfies `P`" is undetermined by the empty report, and is
contradicted once the counterexample claim "`P 0` fails" is added. Worlds are interpretations of
the predicate `P`. -/
theorem universal_undetermined_until_counterexample :
    Undetermined ([] : List (Claim (Nat → Prop))) (fun P => ∀ m, P m) ∧
    Contradicted [fun P : Nat → Prop => ¬ P 0] (fun P => ∀ m, P m) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h; exact (supported_nil_iff _).1 h (fun _ => False) 0
  · intro h; exact (contradicted_nil_iff _).1 h (fun _ => True) (fun _ => trivial)
  · exact contradicted_of_mem_entails_not (c := fun P : Nat → Prop => ¬ P 0) (by simp)
      (fun P h0 hall => h0 (hall 0))

/-! ## Object-level versus meta-level questions -/

/-- For a world-independent question, *undetermined* is never the correct answer (for any
report, satisfiable or not). -/
theorem worldIndependent_not_undetermined (E : List (Claim W)) {q : Claim W}
    (hq : WorldIndependent q) : ¬ Undetermined E q := by
  rintro ⟨hs, hc⟩
  apply hs
  intro w hw
  apply Classical.byContradiction
  intro hnq
  exact hc (fun w' _ hq' => hnq (hq w' w hq'))

/-- The meta-level question "the report establishes `q`" is world-independent. -/
theorem establishes_worldIndependent (E : List (Claim W)) (q : Claim W) :
    WorldIndependent (Establishes E q) := fun _ _ h => h

/-- If `q` is unsupported by the report, the meta-level question "the report establishes `q`"
is contradicted. -/
theorem establishes_contradicted_of_unsupported {E : List (Claim W)} {q : Claim W}
    (h : ¬ Supported E q) : Contradicted E (Establishes E q) :=
  fun _ _ hs => h hs

/-- Tightness of `h` in `establishes_contradicted_of_unsupported` (witness class: the empty
report over `Nat`): `True` is supported and "the report establishes `True`" is not contradicted. -/
theorem establishes_contradicted_h_tight :
    Supported ([] : List (Claim Nat)) (fun _ => True) ∧
    ¬ Contradicted ([] : List (Claim Nat)) (Establishes [] (fun _ => True)) :=
  ⟨fun _ _ => trivial, fun h => h 0 (models_nil 0) (fun _ _ => trivial)⟩

/-- Non-vacuity of `establishes_contradicted_of_unsupported`: `n = 0` is unsupported by
`[n ≤ 1]` over `Nat`. -/
theorem establishes_contradicted_nonvacuous :
    ¬ Supported [fun n : Nat => n ≤ 1] (fun n => n = 0) := supported_example_neg

/-- For every report `E` and claim `q`, an answer key that marks the meta-level question "the
report establishes `q`" as *undetermined* is incorrect. -/
theorem establishes_undetermined_key_never_correct (E : List (Claim W)) (q : Claim W) :
    ¬ KeyCorrect E [(Establishes E q, .undetermined)] :=
  fun hk => worldIndependent_not_undetermined E (establishes_worldIndependent E q)
    (hk (Establishes E q, .undetermined) (by simp))

/-- When the report leaves `q` undetermined (`Undetermined E q`), the answer key that marks the
meta-level question "the report establishes `q`" as *contradicted* and the object-level question
`q` as *undetermined* is correct. -/
theorem establishes_answer_key {E : List (Claim W)} {q : Claim W} (h : Undetermined E q) :
    KeyCorrect E [(Establishes E q, .contradicted), (q, .undetermined)] := by
  intro p hp
  simp at hp
  rcases hp with rfl | rfl
  · exact establishes_contradicted_of_unsupported h.1
  · exact h

/-- Tightness of `hq` in `worldIndependent_not_undetermined` (witness class: the empty report
over `Bool`): a world-dependent claim can be undetermined. This is also the positive control for
the impossibility. -/
theorem worldIndependent_tight :
    ¬ WorldIndependent (fun b : Bool => b = true) ∧
    Undetermined ([] : List (Claim Bool)) (fun b => b = true) := by
  refine ⟨fun h => by simpa using h true false rfl, ?_, ?_⟩
  · intro hs; have := (supported_nil_iff _).1 hs false; simp at this
  · intro hc; exact (contradicted_nil_iff _).1 hc true rfl

/-- Tightness of `h` in `establishes_answer_key` (witness class: the empty report over `Nat`):
when the report supports `q`, `q` is not undetermined and the key is wrong. -/
theorem establishes_answer_key_tight :
    ¬ Undetermined ([] : List (Claim Nat)) (fun _ => True) ∧
    ¬ KeyCorrect ([] : List (Claim Nat))
      [(Establishes [] (fun _ => True), .contradicted), ((fun _ => True), .undetermined)] := by
  refine ⟨fun h => h.1 (fun _ _ => trivial), fun hk => ?_⟩
  have := hk (Establishes [] (fun _ : Nat => True), .contradicted) (by simp)
  exact this 0 (models_nil 0) (fun _ _ => trivial)

/-- Non-vacuity of `establishes_answer_key` and `worldIndependent_not_undetermined`. -/
theorem establishes_answer_key_nonvacuous :
    Undetermined [fun n : Nat => n ≤ 1] (fun n => n = 0) ∧
    WorldIndependent (Establishes [fun n : Nat => n ≤ 1] (fun n => n = 0)) :=
  ⟨undetermined_example_pos, establishes_worldIndependent _ _⟩

end Toy.ClaimStrength
