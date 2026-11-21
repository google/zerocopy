import ClaimStrength.Basic

/-!
# Compound questions: answer tables over satisfiable reports

Over a satisfiable report, given the (unique) answers for `q₁` and `q₂`, the answer for
`q₁ ∧ q₂` is a function of the component answers except when both are *undetermined*, where it
can be *undetermined* or *contradicted*; dually for `q₁ ∨ q₂`. The tables below list, for each
pair of component answers, exactly the answers the compound can have:
`and_answer_mem_andTable_of_satisfiable` shows no other answer occurs, and `andTable_realizable`
shows every listed answer occurs in some instance. This is the supervaluation pattern
(truth-value gaps with non-truth-functional compounds).
-/

namespace Toy.ClaimStrength

variable {W : Type}

/-- The possible answers for `q₁ ∧ q₂` given the answers for `q₁` and `q₂`. -/
def andTable : Answer → Answer → List Answer
  | .contradicted, _ => [.contradicted]
  | .supported, b => [b]
  | .undetermined, .contradicted => [.contradicted]
  | .undetermined, .supported => [.undetermined]
  | .undetermined, .undetermined => [.undetermined, .contradicted]

/-- The possible answers for `q₁ ∨ q₂` given the answers for `q₁` and `q₂`. -/
def orTable : Answer → Answer → List Answer
  | .supported, _ => [.supported]
  | .contradicted, b => [b]
  | .undetermined, .supported => [.supported]
  | .undetermined, .contradicted => [.undetermined]
  | .undetermined, .undetermined => [.undetermined, .supported]

/-- The answer for `¬ q` given the answer for `q`. -/
def negAnswer : Answer → Answer
  | .supported => .contradicted
  | .undetermined => .undetermined
  | .contradicted => .supported

theorem andTable_example_pos : Answer.contradicted ∈ andTable .supported .contradicted := by
  decide

theorem andTable_example_neg : Answer.supported ∉ andTable .undetermined .undetermined := by
  decide

theorem orTable_example_pos : Answer.supported ∈ orTable .undetermined .undetermined := by
  decide

theorem orTable_example_neg : Answer.contradicted ∉ orTable .undetermined .undetermined := by
  decide

theorem negAnswer_example_pos : negAnswer .supported = .contradicted := rfl

theorem negAnswer_example_neg : negAnswer .undetermined ≠ .supported := by decide

/-- Soundness of the conjunction table over a satisfiable report. -/
theorem and_answer_mem_andTable_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E)
    {q₁ q₂ : Claim W} {a₁ a₂ a : Answer}
    (h₁ : Correct E q₁ a₁) (h₂ : Correct E q₂ a₂)
    (h : Correct E (fun w => q₁ w ∧ q₂ w) a) : a ∈ andTable a₁ a₂ := by
  -- Compute a correct answer for the conjunction from the component answers, then use
  -- uniqueness over a satisfiable report.
  have key : ∀ b, Correct E (fun w => q₁ w ∧ q₂ w) b → b ∈ andTable a₁ a₂ → a ∈ andTable a₁ a₂ :=
    fun b hb hmem => (correct_unique_of_satisfiable hE h hb) ▸ hmem
  cases a₁ <;> cases a₂ <;> simp only [Correct, Undetermined] at h₁ h₂
  · exact key .supported (fun w hw => ⟨h₁ w hw, h₂ w hw⟩) (by decide)
  · refine key .undetermined ⟨fun hs => h₂.1 (fun w hw => (hs w hw).2),
      fun hc => h₂.2 (fun w hw hq => hc w hw ⟨h₁ w hw, hq⟩)⟩ (by decide)
  · exact key .contradicted (fun w hw hq => h₂ w hw hq.2) (by decide)
  · refine key .undetermined ⟨fun hs => h₁.1 (fun w hw => (hs w hw).1),
      fun hc => h₁.2 (fun w hw hq => hc w hw ⟨hq, h₂ w hw⟩)⟩ (by decide)
  · cases a with
    | supported =>
      exact absurd (fun w hw => (h w hw).1) h₁.1
    | undetermined => decide
    | contradicted => decide
  · exact key .contradicted (fun w hw hq => h₂ w hw hq.2) (by decide)
  · exact key .contradicted (fun w hw hq => h₁ w hw hq.1) (by decide)
  · exact key .contradicted (fun w hw hq => h₁ w hw hq.1) (by decide)
  · exact key .contradicted (fun w hw hq => h₁ w hw hq.1) (by decide)

/-- Soundness of the disjunction table over a satisfiable report. -/
theorem or_answer_mem_orTable_of_satisfiable {E : List (Claim W)} (hE : Satisfiable E)
    {q₁ q₂ : Claim W} {a₁ a₂ a : Answer}
    (h₁ : Correct E q₁ a₁) (h₂ : Correct E q₂ a₂)
    (h : Correct E (fun w => q₁ w ∨ q₂ w) a) : a ∈ orTable a₁ a₂ := by
  have key : ∀ b, Correct E (fun w => q₁ w ∨ q₂ w) b → b ∈ orTable a₁ a₂ → a ∈ orTable a₁ a₂ :=
    fun b hb hmem => (correct_unique_of_satisfiable hE h hb) ▸ hmem
  cases a₁ <;> cases a₂ <;> simp only [Correct, Undetermined] at h₁ h₂
  · exact key .supported (fun w hw => Or.inl (h₁ w hw)) (by decide)
  · exact key .supported (fun w hw => Or.inl (h₁ w hw)) (by decide)
  · exact key .supported (fun w hw => Or.inl (h₁ w hw)) (by decide)
  · exact key .supported (fun w hw => Or.inr (h₂ w hw)) (by decide)
  · cases a with
    | contradicted =>
      exact absurd (fun w hw hq => h w hw (Or.inl hq)) h₁.2
    | undetermined => decide
    | supported => decide
  · refine key .undetermined ⟨fun hs => h₁.1 (fun w hw => (hs w hw).resolve_right (h₂ w hw)),
      fun hc => h₁.2 (fun w hw hq => hc w hw (Or.inl hq))⟩ (by decide)
  · exact key .supported (fun w hw => Or.inr (h₂ w hw)) (by decide)
  · refine key .undetermined ⟨fun hs => h₂.1 (fun w hw => (hs w hw).resolve_left (h₁ w hw)),
      fun hc => h₂.2 (fun w hw hq => hc w hw (Or.inr hq))⟩ (by decide)
  · exact key .contradicted (fun w hw hq => hq.elim (h₁ w hw) (h₂ w hw)) (by decide)

/-- Negation: for every report `E` (satisfiable or not), if `a` is a correct answer for `q`
then `negAnswer a` is a correct answer for `¬ q`. Over a satisfiable report this fixes the
answer for `¬ q` uniquely (`correct_unique_of_satisfiable`); over an unsatisfiable report both
*supported* and *contradicted* are correct for every claim. -/
theorem neg_answer_correct {E : List (Claim W)} {q : Claim W} {a : Answer}
    (h : Correct E q a) : Correct E (fun w => ¬ q w) (negAnswer a) := by
  cases a with
  | supported => exact fun w hw hn => hn (h w hw)
  | contradicted => exact h
  | undetermined =>
    refine ⟨h.2, fun hc => h.1 (fun w hw => Classical.byContradiction (hc w hw))⟩

/-! ## Realizability: every listed answer occurs -/

/-- Claims over four interpretations, given by Boolean tables. -/
abbrev BB := Bool × Bool

theorem correct_nil_of_bool (f : BB → Bool) (a : Answer)
    (h : (a = .supported ∧ ∀ x y : Bool, f (x, y) = true) ∨
      (a = .contradicted ∧ ∀ x y : Bool, f (x, y) = false) ∨
      (a = .undetermined ∧ (∃ x y : Bool, f (x, y) = true) ∧ ∃ x y : Bool, f (x, y) = false)) :
    Correct ([] : List (Claim BB)) (fun w => f w = true) a := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, ⟨x, y, h1⟩, ⟨x', y', h2⟩⟩
  · exact (supported_nil_iff _).2 (fun ⟨x, y⟩ => h x y)
  · exact (contradicted_nil_iff _).2 (fun ⟨x, y⟩ => by simp [h x y])
  · refine ⟨fun hs => ?_, fun hc => ?_⟩
    · have := (supported_nil_iff _).1 hs (x', y'); simp [h2] at this
    · exact (contradicted_nil_iff _).1 hc (x, y) h1

/-- A canonical claim with a given answer under the empty report. -/
def canon : Answer → BB → Bool
  | .supported => fun _ => true
  | .contradicted => fun _ => false
  | .undetermined => fun w => w.1

theorem canon_correct (a : Answer) :
    Correct ([] : List (Claim BB)) (fun w => canon a w = true) a := by
  apply correct_nil_of_bool
  cases a
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inr (Or.inr ⟨rfl, ⟨true, true, rfl⟩, ⟨false, false, rfl⟩⟩)
  · exact Or.inr (Or.inl ⟨rfl, by decide⟩)

/-- Every answer listed in the conjunction table occurs for some pair of claims with the given
component answers (four interpretations, empty report). -/
theorem andTable_realizable (a₁ a₂ : Answer) :
    ∀ a ∈ andTable a₁ a₂, ∃ q₁ q₂ : Claim BB,
      Correct [] q₁ a₁ ∧ Correct [] q₂ a₂ ∧ Correct [] (fun w => q₁ w ∧ q₂ w) a := by
  intro a ha
  -- The cell (undetermined, undetermined) with answer contradicted uses `q₂ := ¬ q₁`.
  by_cases hspecial : a₁ = .undetermined ∧ a₂ = .undetermined ∧ a = .contradicted
  · obtain ⟨rfl, rfl, rfl⟩ := hspecial
    refine ⟨fun w => w.1 = true, fun w => (!w.1) = true, canon_correct .undetermined, ?_, ?_⟩
    · apply correct_nil_of_bool (fun w => !w.1)
      exact Or.inr (Or.inr ⟨rfl, ⟨false, false, rfl⟩, ⟨true, true, rfl⟩⟩)
    · exact (contradicted_nil_iff _).2 (fun ⟨x, y⟩ => by cases x <;> simp)
  · refine ⟨fun w => canon a₁ w = true, fun w => canon a₂ w = true,
      canon_correct _, canon_correct _, ?_⟩
    have hc : Correct ([] : List (Claim BB))
        (fun w => (canon a₁ w && canon a₂ w) = true) a := by
      apply correct_nil_of_bool
      cases a₁ <;> cases a₂ <;> cases a <;> simp [andTable] at ha hspecial <;>
        simp [canon] <;> first | decide | exact ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
    simpa [Bool.and_eq_true] using hc

/-- Every answer listed in the disjunction table occurs for some pair of claims with the given
component answers (four interpretations, empty report). -/
theorem orTable_realizable (a₁ a₂ : Answer) :
    ∀ a ∈ orTable a₁ a₂, ∃ q₁ q₂ : Claim BB,
      Correct [] q₁ a₁ ∧ Correct [] q₂ a₂ ∧ Correct [] (fun w => q₁ w ∨ q₂ w) a := by
  intro a ha
  by_cases hspecial : a₁ = .undetermined ∧ a₂ = .undetermined ∧ a = .supported
  · obtain ⟨rfl, rfl, rfl⟩ := hspecial
    refine ⟨fun w => w.1 = true, fun w => (!w.1) = true, canon_correct .undetermined, ?_, ?_⟩
    · apply correct_nil_of_bool (fun w => !w.1)
      exact Or.inr (Or.inr ⟨rfl, ⟨false, false, rfl⟩, ⟨true, true, rfl⟩⟩)
    · exact (supported_nil_iff _).2 (fun ⟨x, y⟩ => by cases x <;> simp)
  · refine ⟨fun w => canon a₁ w = true, fun w => canon a₂ w = true,
      canon_correct _, canon_correct _, ?_⟩
    have hc : Correct ([] : List (Claim BB))
        (fun w => (canon a₁ w || canon a₂ w) = true) a := by
      apply correct_nil_of_bool
      cases a₁ <;> cases a₂ <;> cases a <;> simp [orTable] at ha hspecial <;>
        simp [canon] <;> first | decide | exact ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
    simpa [Bool.or_eq_true] using hc

/-- Tightness of `hE` in `and_answer_mem_andTable_of_satisfiable` (witness class: the
unsatisfiable one-claim report `[False]` over `Nat`): both conjuncts are (vacuously) supported
and the conjunction is (vacuously) contradicted, an answer outside the table cell
`[supported]`. -/
theorem and_answer_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => True) .supported ∧
    Correct [fun _ : Nat => False] (fun w => (fun _ => True) w ∧ (fun _ => True) w)
      .contradicted ∧
    Answer.contradicted ∉ andTable .supported .supported := by
  have hns : ¬ Satisfiable [fun _ : Nat => False] :=
    fun ⟨w, hw⟩ => hw (fun _ => False) (by simp)
  exact ⟨hns, (unsatisfiable_supported_and_contradicted hns _).1,
    (unsatisfiable_supported_and_contradicted hns _).2, by decide⟩

/-- Tightness of `hE` in `or_answer_mem_orTable_of_satisfiable` (witness class: the
unsatisfiable one-claim report `[False]` over `Nat`). -/
theorem or_answer_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Correct [fun _ : Nat => False] (fun _ => False) .contradicted ∧
    Correct [fun _ : Nat => False] (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .supported ∧
    Answer.supported ∉ orTable .contradicted .contradicted := by
  have hns : ¬ Satisfiable [fun _ : Nat => False] :=
    fun ⟨w, hw⟩ => hw (fun _ => False) (by simp)
  exact ⟨hns, (unsatisfiable_supported_and_contradicted hns _).2,
    (unsatisfiable_supported_and_contradicted hns _).1, by decide⟩

/-- Non-vacuity: the cell "one conjunct contradicted, the other undetermined" with a
satisfiable report, conjunction contradicted. -/
theorem and_answer_nonvacuous :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun w => canon .contradicted w = true) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => canon .undetermined w = true) .undetermined ∧
    Correct ([] : List (Claim BB))
      (fun w => canon .contradicted w = true ∧ canon .undetermined w = true) .contradicted :=
  ⟨⟨(true, true), models_nil _⟩, canon_correct _, canon_correct _,
    (contradicted_nil_iff _).2 (fun w h => by simp [canon] at h)⟩

/-- Non-vacuity of `or_answer_mem_orTable_of_satisfiable`: the cell (both disjuncts
undetermined) realized with answer *supported* (`q₂ := ¬ q₁`). -/
theorem or_answer_nonvacuous :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => (!w.1) = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ (!w.1) = true) .supported := by
  refine ⟨⟨(true, true), models_nil _⟩, canon_correct .undetermined, ?_, ?_⟩
  · apply correct_nil_of_bool (fun w => !w.1)
    exact Or.inr (Or.inr ⟨rfl, ⟨false, false, rfl⟩, ⟨true, true, rfl⟩⟩)
  · exact (supported_nil_iff _).2 (fun ⟨x, y⟩ => by cases x <;> simp)

/-! ## The undetermined cells with distinct, independent components -/

/-- In the cell (*undetermined*, *undetermined*) of the conjunction table both answers occur
with distinct component claims over four interpretations: `w.1 ∧ w.2` is undetermined and
`w.1 ∧ ¬ w.1` is contradicted. -/
theorem andTable_undetermined_cell_distinct :
    (fun w : BB => w.1 = true) ≠ (fun w => w.2 = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.2 = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∧ w.2 = true) .undetermined ∧
    (fun w : BB => w.1 = true) ≠ (fun w => (!w.1) = true) ∧
    Correct ([] : List (Claim BB)) (fun w => (!w.1) = true) .undetermined ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∧ (!w.1) = true) .contradicted := by
  refine ⟨fun h => ?_, canon_correct .undetermined, ?_, ?_, fun h => ?_, ?_, ?_⟩
  · have := congrFun h (true, false); simp at this
  · apply correct_nil_of_bool (fun w => w.2)
    exact Or.inr (Or.inr ⟨rfl, ⟨true, true, rfl⟩, ⟨false, false, rfl⟩⟩)
  · have := correct_nil_of_bool (fun w => w.1 && w.2) .undetermined
      (Or.inr (Or.inr ⟨rfl, ⟨true, true, rfl⟩, ⟨false, false, rfl⟩⟩))
    simpa [Bool.and_eq_true] using this
  · have := congrFun h (true, false); simp at this
  · apply correct_nil_of_bool (fun w => !w.1)
    exact Or.inr (Or.inr ⟨rfl, ⟨false, false, rfl⟩, ⟨true, true, rfl⟩⟩)
  · exact (contradicted_nil_iff _).2 (fun ⟨x, y⟩ => by cases x <;> simp)

/-- In the cell (*undetermined*, *undetermined*) of the disjunction table both answers occur
with distinct component claims: `w.1 ∨ w.2` is undetermined and `w.1 ∨ ¬ w.1` is supported. -/
theorem orTable_undetermined_cell_distinct :
    (fun w : BB => w.1 = true) ≠ (fun w => w.2 = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ w.2 = true) .undetermined ∧
    (fun w : BB => w.1 = true) ≠ (fun w => (!w.1) = true) ∧
    Correct ([] : List (Claim BB)) (fun w => w.1 = true ∨ (!w.1) = true) .supported := by
  refine ⟨andTable_undetermined_cell_distinct.1, ?_, andTable_undetermined_cell_distinct.2.2.2.2.1,
    (supported_nil_iff _).2 (fun ⟨x, y⟩ => by cases x <;> simp)⟩
  have := correct_nil_of_bool (fun w => w.1 || w.2) .undetermined
    (Or.inr (Or.inr ⟨rfl, ⟨true, true, rfl⟩, ⟨false, false, rfl⟩⟩))
  simpa [Bool.or_eq_true] using this

/-- If every consistent interpretation of `E` equals `w₀` (so `E` has at most one consistent
interpretation, given an element `w₀ : W`; `E` may also be unsatisfiable), no claim is
undetermined. Hence the cells of the answer tables that involve *undetermined* occur only for
reports with at least two consistent interpretations. -/
theorem not_undetermined_of_unique_model {E : List (Claim W)} {w₀ : W}
    (hu : ∀ w, Models E w → w = w₀) (q : Claim W) : ¬ Undetermined E q := by
  rw [undetermined_iff_exists_both]
  rintro ⟨⟨w₁, hw₁, hq₁⟩, ⟨w₂, hw₂, hq₂⟩⟩
  rw [hu w₁ hw₁] at hq₁
  rw [hu w₂ hw₂] at hq₂
  exact hq₂ hq₁

/-- Non-vacuity of `not_undetermined_of_unique_model`: over `Nat`, the report `[n = 0]` has the
unique consistent interpretation `0`. -/
theorem not_undetermined_of_unique_model_nonvacuous :
    ∀ w, Models [fun n : Nat => n = 0] w → w = 0 :=
  fun w hw => hw (fun n => n = 0) (by simp)

/-- Non-vacuity of `neg_answer_correct`: over the satisfiable report `[n ≤ 1]` the claim `n = 0`
is undetermined. -/
theorem neg_answer_nonvacuous :
    Correct [fun n : Nat => n ≤ 1] (fun n => n = 0) .undetermined := undetermined_example_pos

/-- Tightness of `h₁` in `and_answer_mem_andTable_of_satisfiable` (witness class: the empty
report over `Bool × Bool`, `q₁ = q₂ = True`, `a₁ = contradicted`, `a₂ = a = supported`): the
report is satisfiable, `h₂` and `h` hold, `h₁` fails, and `a` is outside the cell. -/
theorem and_answer_h₁_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w) .supported ∧
    Answer.supported ∉ andTable .contradicted .supported :=
  ⟨⟨(true, true), models_nil _⟩, fun h => h (true, true) (models_nil _) trivial,
    fun _ _ => trivial, fun _ _ => ⟨trivial, trivial⟩, by decide⟩

/-- Tightness of `h₂` in `and_answer_mem_andTable_of_satisfiable` (witness class: the empty
report over `Bool × Bool`, `q₁ = q₂ = True`, `a₂ = contradicted`, `a₁ = a = supported`): the
report is satisfiable, `h₁` and `h` hold, `h₂` fails, and `a` is outside the cell. -/
theorem and_answer_h₂_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w) .supported ∧
    Answer.supported ∉ andTable .supported .contradicted :=
  ⟨⟨(true, true), models_nil _⟩, fun _ _ => trivial,
    fun h => h (true, true) (models_nil _) trivial, fun _ _ => ⟨trivial, trivial⟩, by decide⟩

/-- Tightness of `h` in `and_answer_mem_andTable_of_satisfiable` (witness class: the empty report
over `Bool × Bool`, `q₁ = q₂ = True`, `a₁ = a₂ = supported`, `a = contradicted`): the report is
satisfiable, `h₁` and `h₂` hold, `h` fails, and `a` is outside the cell. -/
theorem and_answer_h_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    Correct ([] : List (Claim BB)) (fun _ => True) .supported ∧
    ¬ Correct ([] : List (Claim BB)) (fun w => (fun _ => True) w ∧ (fun _ => True) w)
      .contradicted ∧
    Answer.contradicted ∉ andTable .supported .supported :=
  ⟨⟨(true, true), models_nil _⟩, fun _ _ => trivial, fun _ _ => trivial,
    fun h => h (true, true) (models_nil _) ⟨trivial, trivial⟩, by decide⟩

/-- Tightness of `h₁` in `or_answer_mem_orTable_of_satisfiable` (witness class: the empty report
over `Bool × Bool`, `q₁ = q₂ = False`, `a₁ = supported`, `a₂ = a = contradicted`): the report is
satisfiable, `h₂` and `h` hold, `h₁` fails, and `a` is outside the cell. -/
theorem or_answer_h₁_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => False) .supported ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .contradicted ∧
    Answer.contradicted ∉ orTable .supported .contradicted :=
  ⟨⟨(true, true), models_nil _⟩, fun h => h (true, true) (models_nil _),
    fun _ _ h => h, fun _ _ h => h.elim id id, by decide⟩

/-- Tightness of `h₂` in `or_answer_mem_orTable_of_satisfiable` (witness class: the empty report
over `Bool × Bool`, `q₁ = q₂ = False`, `a₂ = supported`, `a₁ = a = contradicted`): the report is
satisfiable, `h₁` and `h` hold, `h₂` fails, and `a` is outside the cell. -/
theorem or_answer_h₂_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => False) .supported ∧
    Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .contradicted ∧
    Answer.contradicted ∉ orTable .contradicted .supported :=
  ⟨⟨(true, true), models_nil _⟩, fun _ _ h => h, fun h => h (true, true) (models_nil _),
    fun _ _ h => h.elim id id, by decide⟩

/-- Tightness of `h` in `or_answer_mem_orTable_of_satisfiable` (witness class: the empty report
over `Bool × Bool`, `q₁ = q₂ = False`, `a₁ = a₂ = contradicted`, `a = supported`): the report is
satisfiable, `h₁` and `h₂` hold, `h` fails, and `a` is outside the cell. -/
theorem or_answer_h_tight :
    Satisfiable ([] : List (Claim BB)) ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    Correct ([] : List (Claim BB)) (fun _ => False) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun w => (fun _ => False) w ∨ (fun _ => False) w)
      .supported ∧
    Answer.supported ∉ orTable .contradicted .contradicted :=
  ⟨⟨(true, true), models_nil _⟩, fun _ _ h => h, fun _ _ h => h,
    fun h => (h (true, true) (models_nil _)).elim id id, by decide⟩

/-- Tightness of `hu` in `not_undetermined_of_unique_model` (witness class: the empty report over
`Bool`, which has two consistent interpretations): `hu` fails for every choice of `w₀ : Bool`,
and the claim `b = true` is undetermined. -/
theorem not_undetermined_of_unique_model_hu_tight :
    (∀ w₀ : Bool, ¬ ∀ w, Models ([] : List (Claim Bool)) w → w = w₀) ∧
    Undetermined ([] : List (Claim Bool)) (fun b => b = true) := by
  refine ⟨fun w₀ h => ?_, worldIndependent_tight.2⟩
  cases w₀
  · exact absurd (h true (models_nil true)) (by decide)
  · exact absurd (h false (models_nil false)) (by decide)

/-- Tightness of `h` in `neg_answer_correct` (witness class: the empty report over `Bool × Bool`
with `q = True`): `contradicted` is incorrect for `True`, and `negAnswer contradicted = supported`
is incorrect for `¬ True`. -/
theorem neg_answer_h_tight :
    ¬ Correct ([] : List (Claim BB)) (fun _ => True) .contradicted ∧
    ¬ Correct ([] : List (Claim BB)) (fun _ => ¬ True) (negAnswer .contradicted) :=
  ⟨fun h => h (true, true) (models_nil _) trivial, fun h => h (true, true) (models_nil _) trivial⟩

end Toy.ClaimStrength

