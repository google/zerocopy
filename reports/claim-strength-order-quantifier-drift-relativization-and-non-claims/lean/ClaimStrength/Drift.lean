import ClaimStrength.Basic

/-!
# Domain and premise variance, and a catalogue of drifts

Each drift is stated with the uninterpreted predicates as the interpretation space `W`, so a
non-entailment `¬ Entails A B` is witnessed by one concrete interpretation (the countermodel)
satisfying `A` and falsifying `B`.
-/

namespace Toy.ClaimStrength

variable {α W : Type}

theorem entails_refl (q : Claim W) : Entails q q := fun _ h => h

theorem entails_trans {a b c : Claim W} (h₁ : Entails a b) (h₂ : Entails b c) : Entails a c :=
  fun w h => h₂ w (h₁ w h)

/-! ## Domain and premise variance -/

/-- A universal claim over domain `D` entails the same claim over `D'` (for every predicate)
iff `D' ⊆ D` (contravariance). -/
theorem forall_domain_entails_iff (D D' : α → Prop) :
    Entails (W := α → Prop) (fun P => ∀ x, D x → P x) (fun P => ∀ x, D' x → P x) ↔
      ∀ x, D' x → D x := by
  constructor
  · intro h x hx; exact h D (fun _ h => h) x hx
  · intro h P hP x hx; exact hP x (h x hx)

/-- An existential claim over domain `D` entails the same claim over `D'` (for every predicate)
iff `D ⊆ D'` (covariance). -/
theorem exists_domain_entails_iff (D D' : α → Prop) :
    Entails (W := α → Prop) (fun P => ∃ x, D x ∧ P x) (fun P => ∃ x, D' x ∧ P x) ↔
      ∀ x, D x → D' x := by
  constructor
  · intro h x hx
    obtain ⟨y, hy, e⟩ := h (fun y => y = x) ⟨x, hx, rfl⟩
    exact e ▸ hy
  · rintro h P ⟨x, hx, hP⟩; exact ⟨x, h x hx, hP⟩

/-- A claim with premise `H` entails the same claim with premise `H'` (for every conclusion
predicate) iff `H' ⊆ H`. This is the same law as `forall_domain_entails_iff`, read for a
premise instead of a domain. -/
theorem premise_entails_iff (H H' : α → Prop) :
    Entails (W := α → Prop) (fun C => ∀ x, H x → C x) (fun C => ∀ x, H' x → C x) ↔
      ∀ x, H' x → H x :=
  forall_domain_entails_iff H H'

/-- A claim relative to the assumption `H` entails the absolute claim (for every conclusion
predicate) iff `H` holds everywhere. -/
theorem relative_entails_absolute_iff (H : α → Prop) :
    Entails (W := α → Prop) (fun C => ∀ x, H x → C x) (fun C => ∀ x, C x) ↔ ∀ x, H x := by
  rw [show (fun C : α → Prop => ∀ x, C x) = (fun C => ∀ x, (fun _ => True) x → C x) from
    funext fun C => propext ⟨fun h x _ => h x, fun h x => h x trivial⟩]
  rw [premise_entails_iff]
  exact ⟨fun h x => h x trivial, fun h x _ => h x⟩

/-- Non-vacuity for the variance laws: a range-to-instance specialization that does hold
(`{k | 1 ≤ k} ⊇ {2}`) and an existential that widens. -/
theorem domain_variance_nonvacuous :
    Entails (W := Nat → Prop) (fun P => ∀ k, 1 ≤ k → P k) (fun P => ∀ k, k = 2 → P k) ∧
    Entails (W := Nat → Prop) (fun P => ∃ k, k = 2 ∧ P k) (fun P => ∃ k, 1 ≤ k ∧ P k) :=
  ⟨(forall_domain_entails_iff _ _).2 (fun k hk => by omega),
    (exists_domain_entails_iff _ _).2 (fun k hk => by omega)⟩

/-! ## The drift catalogue -/

/-- (a) A single counterexample is not a universal refutation. -/
theorem single_counterexample_not_universal :
    ¬ Entails (W := Nat → Prop) (fun P => ∃ m, ¬ P m) (fun P => ∀ m, ¬ P m) := by
  intro h
  exact h (fun m => m ≠ 0) ⟨0, fun h0 => h0 rfl⟩ 1 (by decide)

/-- (a) The converse: for every nonempty domain `α`, a universal refutation entails a single
counterexample. -/
theorem universal_refutation_entails_single_of_nonempty {α : Type} [Nonempty α] :
    Entails (W := α → Prop) (fun P => ∀ m, ¬ P m) (fun P => ∃ m, ¬ P m) :=
  fun _ h => let ⟨a⟩ := (inferInstance : Nonempty α); ⟨a, h a⟩

/-- Tightness of `[Nonempty α]` in `universal_refutation_entails_single_of_nonempty` (witness
class: the empty domain `Empty`): the universal refutation holds vacuously and no counterexample
exists. -/
theorem universal_refutation_nonempty_tight :
    ¬ Nonempty Empty ∧
    ¬ Entails (W := Empty → Prop) (fun P => ∀ m, ¬ P m) (fun P => ∃ m, ¬ P m) :=
  ⟨fun ⟨e⟩ => (nomatch e), fun h => by
    obtain ⟨e, _⟩ := h (fun _ => True) (fun e => nomatch e)
    exact nomatch e⟩

/-- Non-vacuity of `universal_refutation_entails_single_of_nonempty`: `Nat` is nonempty and the
predicate `False` is universally refuted. -/
theorem universal_refutation_nonvacuous :
    Nonempty Nat ∧ (fun P : Nat → Prop => ∀ m, ¬ P m) (fun _ => False) :=
  ⟨⟨0⟩, fun _ h => h⟩

/-- (a) A counterexample in a class does not give one in a subclass (here: all naturals versus
even naturals). -/
theorem counterexample_in_class_not_in_subclass :
    ¬ Entails (W := Nat → Prop) (fun P => ∃ m, ¬ P m) (fun P => ∃ m, m % 2 = 0 ∧ ¬ P m) := by
  intro h
  obtain ⟨m, hm, hP⟩ := h (fun m => m % 2 = 0) ⟨1, by decide⟩
  exact hP hm

/-- (a) The converse: a counterexample in a subclass is one in the class. -/
theorem counterexample_in_subclass_lifts {K K' : Nat → Prop} (h : ∀ m, K' m → K m) :
    Entails (W := Nat → Prop) (fun P => ∃ m, K' m ∧ ¬ P m) (fun P => ∃ m, K m ∧ ¬ P m) :=
  fun _ ⟨m, hm, hP⟩ => ⟨m, h m hm, hP⟩

/-- Tightness of `h` in `counterexample_in_subclass_lifts` (witness class: predicates on `Nat`,
`K'` = all naturals, `K` = even naturals): `K'` is not contained in `K`, and a counterexample in
`K'` does not give one in `K`. -/
theorem counterexample_in_subclass_lifts_h_tight :
    ¬ (∀ m : Nat, (fun _ => True) m → (fun m => m % 2 = 0) m) ∧
    ¬ Entails (W := Nat → Prop)
        (fun P => ∃ m, (fun _ => True) m ∧ ¬ P m)
        (fun P => ∃ m, (fun m => m % 2 = 0) m ∧ ¬ P m) := by
  refine ⟨fun h => absurd (h 1 trivial) (by decide), ?_⟩
  intro h
  obtain ⟨m, hm, hP⟩ := h (fun m => m % 2 = 0) ⟨1, trivial, by decide⟩
  exact hP hm

/-- (b) A result at one parameter value does not give it over a range. -/
theorem single_parameter_not_range :
    ¬ Entails (W := Nat → Prop) (fun P => P 2) (fun P => ∀ k, 1 ≤ k → P k) := by
  intro h
  exact absurd (h (fun k => k = 2) rfl 1 (by decide)) (by decide)

/-- (b) The converse: a range result specializes. -/
theorem range_entails_single :
    Entails (W := Nat → Prop) (fun P => ∀ k, 1 ≤ k → P k) (fun P => P 2) :=
  fun _ h => h 2 (by decide)

/-- (c) A pointwise bound (`∀∃`) is not a uniform bound (`∃∀`). -/
theorem pointwise_bound_not_uniform :
    ¬ Entails (W := Nat → Nat → Prop) (fun R => ∀ x, ∃ n, R x n) (fun R => ∃ n, ∀ x, R x n) := by
  intro h
  obtain ⟨n, hn⟩ := h (fun x n => x ≤ n) (fun x => ⟨x, Nat.le_refl x⟩)
  exact absurd (hn (n + 1)) (by omega)

/-- (c) The concrete instance over `Nat` with `≤`. -/
theorem nat_pointwise_bound_not_uniform :
    ¬ ((∀ x : Nat, ∃ n, x ≤ n) → ∃ n, ∀ x : Nat, x ≤ n) := by
  intro h
  obtain ⟨n, hn⟩ := h (fun x => ⟨x, Nat.le_refl x⟩)
  exact absurd (hn (n + 1)) (by omega)

/-- (c) The converse: a uniform bound is pointwise. -/
theorem uniform_entails_pointwise :
    Entails (W := Nat → Nat → Prop) (fun R => ∃ n, ∀ x, R x n) (fun R => ∀ x, ∃ n, R x n) :=
  fun _ ⟨n, hn⟩ x => ⟨n, hn x⟩

/-- (d) A claim relative to a per-instance assumption is not the absolute claim. -/
theorem relative_not_absolute :
    ¬ Entails (W := (Nat → Prop) × (Nat → Prop)) (fun w => ∀ x, w.1 x → w.2 x)
      (fun w => ∀ x, w.2 x) := by
  intro h
  exact absurd (h ((· = 0), (· = 0)) (fun _ hx => hx) 1) (by decide)

/-- (d) A claim relative to a global assumption is not the absolute claim. -/
theorem relative_to_assumption_not_absolute :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.2) :=
  fun h => h (False, False) (fun f => f)

/-- (d) The converse: the absolute claim gives the relative one. -/
theorem absolute_entails_relative :
    Entails (W := (Nat → Prop) × (Nat → Prop)) (fun w => ∀ x, w.2 x)
      (fun w => ∀ x, w.1 x → w.2 x) :=
  fun _ h x _ => h x

/-- (e) A sufficient condition is not a characterization (`if` is not `iff`): `A → B` does not
entail `A ↔ B` (countermodel `A = False`, `B = True`). -/
theorem sufficient_not_characterization :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.1 ↔ w.2) :=
  fun h => (h (False, True) (fun f => f.elim)).2 trivial

/-- (e) A sufficient condition does not give its converse: `A → B` does not entail `B → A`. -/
theorem sufficient_not_converse :
    ¬ Entails (W := Prop × Prop) (fun w => w.1 → w.2) (fun w => w.2 → w.1) :=
  fun h => h (False, True) (fun f => f.elim) trivial

/-- (e) The converse direction that holds: a characterization gives the sufficient condition. -/
theorem characterization_entails_sufficient :
    Entails (W := Prop × Prop) (fun w => w.1 ↔ w.2) (fun w => w.1 → w.2) :=
  fun _ h => h.1

/-- A checker: which inputs it accepts, and which inputs are good. -/
structure Checker where
  accept : Nat → Bool
  good : Nat → Prop

/-- Soundness polarity: acceptance implies goodness. -/
def CheckerSound (c : Checker) : Prop := ∀ p, c.accept p = true → c.good p

/-- Completeness polarity: goodness implies acceptance. -/
def CheckerComplete (c : Checker) : Prop := ∀ p, c.good p → c.accept p = true

/-- The checker that rejects every input (good inputs: all). -/
def rejectAll : Checker := ⟨fun _ => false, fun _ => True⟩

/-- The checker that accepts every input (good inputs: none). -/
def acceptAll : Checker := ⟨fun _ => true, fun _ => False⟩

/-- The checker that accepts exactly the even inputs (good inputs: the even numbers). -/
def evenChecker : Checker := ⟨fun n => decide (n % 2 = 0), fun n => n % 2 = 0⟩

/-- A checker that accepts only `0` (good inputs: the even numbers): sound, not complete. -/
def zeroChecker : Checker := ⟨fun n => decide (n = 0), fun n => n % 2 = 0⟩

theorem checkerSound_example_pos : CheckerSound zeroChecker ∧ zeroChecker.accept 0 = true :=
  ⟨fun p h => by have : p = 0 := of_decide_eq_true h; subst this; rfl, rfl⟩

theorem checkerSound_example_neg : ¬ CheckerSound acceptAll :=
  fun h => h 0 rfl

theorem checkerComplete_example_pos : CheckerComplete evenChecker ∧ evenChecker.good 0 :=
  ⟨fun _ h => decide_eq_true h, rfl⟩

theorem checkerComplete_example_neg : ¬ CheckerComplete rejectAll :=
  fun h => absurd (h 0 trivial) Bool.false_ne_true

/-- (e) A sound checker need not be complete (`zeroChecker` accepts only `0` but every even
number is good). -/
theorem checker_sound_not_complete : ¬ Entails CheckerSound CheckerComplete :=
  fun h => absurd (h _ checkerSound_example_pos.1 2 (show 2 % 2 = 0 from rfl)) (by decide)

/-- (e) A complete checker need not be sound (the checker that accepts everything). -/
theorem checker_complete_not_sound : ¬ Entails CheckerComplete CheckerSound :=
  fun h => checkerSound_example_neg (h _ (fun _ h => h.elim))

/-- (e) The converse direction that holds: sound and complete gives sound. -/
theorem checker_sound_complete_entails_sound :
    Entails (fun c => CheckerSound c ∧ CheckerComplete c) CheckerSound := fun _ h => h.1

/-- Non-vacuity of `checker_sound_complete_entails_sound`: `evenChecker` is sound and complete
and accepts `0`. -/
theorem checker_sound_complete_nonvacuous :
    CheckerSound evenChecker ∧ CheckerComplete evenChecker ∧ evenChecker.accept 0 = true :=
  ⟨fun _ h => (of_decide_eq_true h : _ % 2 = 0), checkerComplete_example_pos.1, rfl⟩

/-- Non-vacuity of `characterization_entails_sufficient`: `A = B = True` is a characterization. -/
theorem characterization_entails_sufficient_nonvacuous :
    (fun w : Prop × Prop => w.1 ↔ w.2) (True, True) := Iff.rfl

/-- (f) A conjunctive premise is not a disjunctive one. -/
theorem conj_premise_not_disj :
    ¬ Entails (W := Prop × Prop × Prop) (fun w => w.1 ∧ w.2.1 → w.2.2)
      (fun w => w.1 ∨ w.2.1 → w.2.2) :=
  fun h => h (True, False, False) (fun hc => hc.2) (Or.inl trivial)

/-- (f) The converse: a disjunctive premise gives the conjunctive one. -/
theorem disj_premise_entails_conj :
    Entails (W := Prop × Prop × Prop) (fun w => w.1 ∨ w.2.1 → w.2.2)
      (fun w => w.1 ∧ w.2.1 → w.2.2) :=
  fun _ h hc => h (Or.inl hc.1)

/-- (g) The converse of `unsupported_not_imply_contradicted` that holds: if `q` is contradicted
by `E` and `E` is satisfiable, then `q` is unsupported. -/
theorem unsupported_of_contradicted_of_satisfiable {E : List (Claim W)} {q : Claim W}
    (hc : Contradicted E q) (hE : Satisfiable E) : ¬ Supported E q :=
  fun hs => let ⟨w, hw⟩ := hE; hc w hw (hs w hw)

/-- Tightness of `hE` in `unsupported_of_contradicted_of_satisfiable` (witness class: the
unsatisfiable one-claim report `[False]` over `Nat`): the report is unsatisfiable, `True` is
contradicted, and `True` is supported. -/
theorem unsupported_of_contradicted_hE_tight :
    ¬ Satisfiable [fun _ : Nat => False] ∧
    Contradicted [fun _ : Nat => False] (fun _ => True) ∧
    Supported [fun _ : Nat => False] (fun _ => True) :=
  ⟨fun ⟨_, hw⟩ => hw (fun _ => False) (by simp), fun _ hw => absurd (hw (fun _ => False) (by simp)) id,
    fun _ _ => trivial⟩

/-- Tightness of `hc` in `unsupported_of_contradicted_of_satisfiable` (witness class: the empty
report over `Nat`): satisfiable, `True` is not contradicted and is supported. -/
theorem unsupported_of_contradicted_hc_tight :
    Satisfiable ([] : List (Claim Nat)) ∧ ¬ Contradicted ([] : List (Claim Nat)) (fun _ => True) ∧
    Supported ([] : List (Claim Nat)) (fun _ => True) :=
  ⟨⟨0, models_nil 0⟩, fun h => (contradicted_nil_iff _).1 h 0 trivial, fun _ _ => trivial⟩

/-- Non-vacuity of `unsupported_of_contradicted_of_satisfiable`. -/
theorem unsupported_of_contradicted_nonvacuous :
    Contradicted [fun n : Nat => n = 0] (fun n => n = 1) ∧ Satisfiable [fun n : Nat => n = 0] :=
  ⟨contradicted_example_pos, ⟨0, by intro e he; simp at he; subst he; rfl⟩⟩

/-- Non-vacuity of `counterexample_in_subclass_lifts`: even numbers inside all numbers. -/
theorem counterexample_in_subclass_lifts_nonvacuous :
    (∀ m, (fun m => m % 2 = 0) m → (fun _ => True) m) ∧
    (fun P : Nat → Prop => ∃ m, m % 2 = 0 ∧ ¬ P m) (fun m => m ≠ 0) :=
  ⟨fun _ _ => trivial, ⟨0, rfl, fun h => h rfl⟩⟩

/-- Non-vacuity of `range_entails_single`: the predicate `1 ≤ k` holds on the range. -/
theorem range_entails_single_nonvacuous :
    (fun P : Nat → Prop => ∀ k, 1 ≤ k → P k) (fun k => 1 ≤ k) := fun _ h => h

/-- Non-vacuity of `uniform_entails_pointwise`: the relation `n = 0` has the uniform bound `0`. -/
theorem uniform_entails_pointwise_nonvacuous :
    (fun R : Nat → Nat → Prop => ∃ n, ∀ x, R x n) (fun _ n => n = 0) := ⟨0, fun _ => rfl⟩

/-- Non-vacuity of `absolute_entails_relative`: the conclusion `True` holds absolutely. -/
theorem absolute_entails_relative_nonvacuous :
    (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.2 x) ((· = 0), fun _ => True) :=
  fun _ => trivial

/-- Non-vacuity of `disj_premise_entails_conj`: `(True ∨ False) → True`. -/
theorem disj_premise_entails_conj_nonvacuous :
    (fun w : Prop × Prop × Prop => w.1 ∨ w.2.1 → w.2.2) (True, False, True) := fun _ => trivial

end Toy.ClaimStrength
