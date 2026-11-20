import ToyIL.Consequence

/-!
# What each kind of triple licenses

* A valid IL error triple with a nonempty post is a true positive: some run from the pre
  reaches an error in a post state.
* A valid Hoare error triple with post `False` is exactly safety. A Hoare triple about the
  `ok` exit says nothing about errors.
* The converses fail: an IL error triple with empty post is valid for every program, and a
  Hoare error triple with a nonempty post can hold for a program with no reachable error.
-/

namespace Toy.IL

variable {σ : Type}

/-! ### True positives from IL -/

/-- A valid IL error triple `[P] c [er : Q]` with `Q` nonempty yields a true positive: some
run of `c` from a `P` state terminates with an error in a `Q` state. -/
theorem il_er_nonempty_post_true_positive {P Q : Assn σ} {c : Cmd σ}
    (hil : IL P c .er Q) (hne : ∃ t, Q t) : ∃ s t, P s ∧ Q t ∧ Exec c s .er t := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨s, hs, hst⟩ := hil t ht
  exact ⟨s, t, hs, ht, hst⟩

/-- The IL premise is needed: `skip` with the nonempty post `True`. -/
theorem il_er_nonempty_post_true_positive_il_tight :
    ¬ IL (fun _ : Nat => True) Cmd.skip .er (fun _ => True) ∧ (∃ _t : Nat, True) ∧
      ¬ ∃ s t, (fun _ : Nat => True) s ∧ (fun _ : Nat => True) t ∧ Exec Cmd.skip s .er t := by
  refine ⟨?_, ⟨0, trivial⟩, ?_⟩
  · intro h; obtain ⟨s, _, hs⟩ := h 0 trivial; simp at hs
  · rintro ⟨s, t, _, _, h⟩; simp at h

/-- Nonemptiness of the post is needed: the empty post makes the triple vacuously valid. -/
theorem il_er_nonempty_post_true_positive_nonempty_tight :
    IL (fun _ : Nat => True) Cmd.skip .er (fun _ => False) ∧ ¬ (∃ _t : Nat, False) ∧
      ¬ ∃ s t, (fun _ : Nat => True) s ∧ (fun _ : Nat => False) t ∧ Exec Cmd.skip s .er t := by
  refine ⟨fun _ h => h.elim, fun ⟨_, h⟩ => h, ?_⟩
  rintro ⟨s, t, _, h, _⟩; exact h

/-- Non-vacuity: `[x = 7] assume (x = 7); error() [er : x = 7]`. -/
theorem nonvacuity_il_true_positive :
    IL (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) .er (fun n => n = 7) ∧
      ∃ t : Nat, t = 7 := by
  refine ⟨?_, ⟨7, rfl⟩⟩
  rintro t rfl; exact ⟨7, rfl, .seqOk (.assume rfl) .error⟩

/-- The witness of an IL error triple is existential over the pre. Weakening the pre to
`True` keeps the triple valid, yet a caller that reaches the command in a state satisfying
`True` need not trigger the error: `[True] assume (x = 7); error() [er : x = 7]` is valid,
the command has no erroneous run from `0`, and `x := 0; assume (x = 7); error()` has no
reachable error from any state. -/
theorem il_er_true_pre_yet_caller_state_avoids_error :
    IL (fun _ : Nat => True) (.seq (.assume (fun n => n == 7)) .error) .er (fun n => n = 7) ∧
      (¬ ∃ t, Exec (Cmd.seq (.assume (fun n : Nat => n == 7)) .error) 0 .er t) ∧
      ¬ ErrReachable (fun _ : Nat => True)
        (.seq (.assign (fun _ => 0)) (.seq (.assume (fun n => n == 7)) .error)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro t rfl; exact ⟨7, trivial, .seqOk (.assume rfl) .error⟩
  · rintro ⟨t, h⟩; simp at h
  · rintro ⟨s, t, _, h⟩; simp at h

/-! ### IL error triples characterize error reachability -/

/-- An error is reachable from `P` iff some valid IL error triple from `P` has a nonempty
post (for `→`, the post-image `post c er P` itself is such a post). -/
theorem errReachable_iff_exists_il_er_nonempty {P : Assn σ} {c : Cmd σ} :
    ErrReachable P c ↔ ∃ Q, IL P c .er Q ∧ ∃ t, Q t := by
  constructor
  · rintro ⟨s, t, hs, hst⟩; exact ⟨post c .er P, il_post_self P c .er, t, s, hs, hst⟩
  · rintro ⟨Q, hil, hne⟩
    obtain ⟨s, t, hs, _, hst⟩ := il_er_nonempty_post_true_positive hil hne
    exact ⟨s, t, hs, hst⟩

/-- Safety from `P` holds iff *every* valid IL error triple from `P` has an empty post.
A single valid triple with empty post is not enough (see
`il_er_empty_post_valid_yet_unsafe`). -/
theorem safe_iff_all_il_er_posts_empty {P : Assn σ} {c : Cmd σ} :
    Safe P c ↔ ∀ Q, IL P c .er Q → ∀ t, ¬ Q t := by
  rw [safe_iff_not_errReachable, errReachable_iff_exists_il_er_nonempty]
  constructor
  · intro h Q hil t ht; exact h ⟨Q, hil, t, ht⟩
  · rintro h ⟨Q, hil, t, ht⟩; exact h Q hil t ht

/-- Non-vacuity of the characterization on both sides. -/
theorem nonvacuity_il_characterization :
    ErrReachable (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) ∧
      Safe (fun _ : Nat => True) (.seq (.assume (fun _ => false)) .error) :=
  ⟨errReachable_pos, safe_pos⟩

/-! ### Safety from Hoare -/

/-- Safety is exactly the Hoare error triple with post `False`. No `ok` triple is involved:
the `ok` exit carries no information about errors (see `safe_of_hoare_er_false_tight`). -/
theorem safe_iff_hoare_er_false {P : Assn σ} {c : Cmd σ} :
    Safe P c ↔ Hoare P c .er (fun _ => False) := by
  rw [hoare_iff]
  constructor
  · intro h s t hs hst; exact h s t hs hst
  · intro h s t hs hst; exact h s t hs hst

/-- The `→` direction of `safe_iff_hoare_er_false`, as the usual verification reading. -/
theorem safe_of_hoare_er_false {P : Assn σ} {c : Cmd σ}
    (h : Hoare P c .er (fun _ => False)) : Safe P c :=
  safe_iff_hoare_er_false.2 h

/-- The error-triple premise is needed, and an `ok` triple cannot replace it: `error()`
satisfies the strongest possible `ok` triple `{True} error() {ok : False}`, but not the
error triple, and it is unsafe. -/
theorem safe_of_hoare_er_false_tight :
    Hoare (fun _ : Nat => True) .error .ok (fun _ => False) ∧
      ¬ Hoare (fun _ : Nat => True) .error .er (fun _ => False) ∧
      ¬ Safe (fun _ : Nat => True) (.error : Cmd Nat) := by
  refine ⟨hoare_pos_error_ok, ?_, ?_⟩
  · intro h; exact h 0 ⟨0, trivial, .error⟩
  · intro h; exact h 0 0 trivial .error

/-- Non-vacuity: `{True} assume false; error() {er : False}`. -/
theorem nonvacuity_hoare_safe :
    Hoare (fun _ : Nat => True) (.seq (.assume (fun _ => false)) .error) .er (fun _ => False) :=
  safe_iff_hoare_er_false.1 safe_pos

/-- Compositional proofs of safety use `ok`-exit summaries: safety of `c₁; c₂` from `P`
follows from safety of `c₁` from `P`, an over-approximate `ok` summary `Q` of `c₁`, and
safety of `c₂` from `Q`. -/
theorem hoare_seq_er_false {P Q : Assn σ} {c₁ c₂ : Cmd σ}
    (h₁ : Hoare P c₁ .er (fun _ => False)) (hok : Hoare P c₁ .ok Q)
    (h₂ : Hoare Q c₂ .er (fun _ => False)) : Hoare P (.seq c₁ c₂) .er (fun _ => False) := by
  rintro t ⟨s, hs, hst⟩
  simp only [exec_seq_iff] at hst
  rcases hst with ⟨m, hm, hmt⟩ | ⟨_, h⟩
  · exact h₂ t ⟨m, hok m ⟨s, hs, hm⟩, hmt⟩
  · exact h₁ t ⟨s, hs, h⟩

/-- The error-exit triples of the parts from the same pre do not determine safety of a
sequence: `x := 7` and `assume (x = 7); error()` are each safe from `x = 0`, but their
sequence is not. -/
theorem safe_seq_not_of_safe_parts :
    Safe (fun n : Nat => n = 0) (.assign (fun _ => 7)) ∧
      Safe (fun n : Nat => n = 0) (.seq (.assume (fun n => n == 7)) .error) ∧
      ¬ Safe (fun n : Nat => n = 0)
        (.seq (.assign (fun _ => 7)) (.seq (.assume (fun n => n == 7)) .error)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t _ h; simp at h
  · rintro s t rfl h; simp at h
  · intro h; exact h 0 7 rfl (.seqOk .assign (.seqOk (.assume rfl) .error))

/-! ### The converses fail -/

/-- O'Hearn's "empty under-approximates" axiom, semantically: every IL triple with empty
post is valid. -/
theorem il_empty_post (P : Assn σ) (c : Cmd σ) (e : Exit) : IL P c e (fun _ => False) :=
  fun _ h => h.elim

/-- An IL error triple with empty post proves nothing about safety: it is valid for
`error()`, which is unsafe. -/
theorem il_er_empty_post_valid_yet_unsafe :
    IL (fun _ : Nat => True) .error .er (fun _ => False) ∧
      ¬ Safe (fun _ : Nat => True) (.error : Cmd Nat) :=
  ⟨il_empty_post _ _ _, fun h => h 0 0 trivial .error⟩

/-- The negative result stated as a refuted implication: a valid IL error triple with
empty post does not imply safety. -/
theorem not_il_er_empty_post_implies_safe :
    ¬ ∀ (P : Assn Nat) (c : Cmd Nat), IL P c .er (fun _ => False) → Safe P c :=
  fun h => il_er_empty_post_valid_yet_unsafe.2 (h _ _ il_er_empty_post_valid_yet_unsafe.1)

/-- Adding a valid normal-exit triple with a nonempty post does not help: `skip + error()`
satisfies `[True] c [ok : True]` and `[True] c [er : False]`, and it is unsafe. -/
theorem il_ok_nonempty_and_er_empty_yet_unsafe :
    let c : Cmd Nat := .choice Cmd.skip .error
    IL (fun _ => True) c .ok (fun _ => True) ∧ IL (fun _ => True) c .er (fun _ => False) ∧
      ¬ Safe (fun _ => True) c := by
  refine ⟨?_, il_empty_post _ _ _, ?_⟩
  · intro t _; exact ⟨t, trivial, .choiceL (by simp)⟩
  · intro h; exact h 0 0 trivial (.choiceR .error)

/-- Every Hoare triple with post `True` is valid. -/
theorem hoare_true_post (P : Assn σ) (c : Cmd σ) (e : Exit) : Hoare P c e (fun _ => True) :=
  fun _ _ => trivial

/-- O'Hearn's `usemkeven` pattern: `x := 2; assume (x = 4); error()`. -/
def mkevenProg : Cmd Nat := .seq (.assign (fun _ => 2)) (.seq (.assume (fun n => n == 4)) .error)

/-- A valid Hoare error triple with a nonempty post does not imply a reachable error:
`{True} mkevenProg {er : x = 4}` is valid (vacuously: there are no error exits) and the
post is nonempty, but no error is reachable. -/
theorem hoare_er_nonempty_post_without_reachable_error :
    Hoare (fun _ => True) mkevenProg .er (fun n => n = 4) ∧ (∃ t : Nat, t = 4) ∧
      ¬ ErrReachable (fun _ => True) mkevenProg := by
  refine ⟨?_, ⟨4, rfl⟩, ?_⟩
  · rintro t ⟨s, _, h⟩; simp [mkevenProg] at h
  · rintro ⟨s, t, _, h⟩; simp [mkevenProg] at h

/-- The negative result stated as a refuted implication. -/
theorem not_hoare_er_nonempty_post_implies_errReachable :
    ¬ ∀ (P Q : Assn Nat) (c : Cmd Nat), Hoare P c .er Q → (∃ t, Q t) → ErrReachable P c := by
  intro h
  obtain ⟨h₁, h₂, h₃⟩ := hoare_er_nonempty_post_without_reachable_error
  exact h₃ (h _ _ _ h₁ h₂)

/-- The body of O'Hearn's `mkeven()`: `x := 2`. -/
def mkevenBody : Cmd Nat := .assign (fun _ => 2)

/-- The check in O'Hearn's `usemkeven()`: `assume (x = 4); error()`. -/
def mkevenCheck : Cmd Nat := .seq (.assume (fun n => n == 4)) .error

theorem mkevenProg_eq : mkevenProg = .seq mkevenBody mkevenCheck := rfl

/-- O'Hearn's compositional false positive (POPL 2020, Section 3.3): the over-approximate
normal-exit summary `{True} x := 2 {ok : x = 2 ∨ x = 4}` is valid, the check satisfies the
true-positive error triple `[x = 2 ∨ x = 4] assume (x = 4); error() [er : x = 4]` with a
nonempty post, yet the composition has no reachable error. -/
theorem hoare_ok_summary_then_il_er_without_reachable_error :
    Hoare (fun _ => True) mkevenBody .ok (fun n => n = 2 ∨ n = 4) ∧
      IL (fun n => n = 2 ∨ n = 4) mkevenCheck .er (fun n => n = 4) ∧ (∃ t : Nat, t = 4) ∧
      ¬ ErrReachable (fun _ => True) (.seq mkevenBody mkevenCheck) := by
  refine ⟨?_, ?_, ⟨4, rfl⟩, ?_⟩
  · rintro t ⟨s, _, h⟩; simp [mkevenBody] at h; omega
  · rintro t rfl; exact ⟨4, Or.inr rfl, .seqOk (.assume rfl) .error⟩
  · rintro ⟨s, t, _, h⟩; simp [mkevenBody, mkevenCheck] at h

/-- The compositional negative result as a refuted implication: an over-approximate
`ok` summary of a prefix, followed by a true-positive error triple for the suffix from that
summary, does not yield a reachable error of the sequence. -/
theorem not_hoare_ok_then_il_er_implies_errReachable :
    ¬ ∀ (P Q R : Assn Nat) (c₁ c₂ : Cmd Nat),
      Hoare P c₁ .ok Q → IL Q c₂ .er R → (∃ t, R t) → ErrReachable P (.seq c₁ c₂) := by
  intro h
  obtain ⟨h₁, h₂, h₃, h₄⟩ := hoare_ok_summary_then_il_er_without_reachable_error
  exact h₄ (h _ _ _ _ _ h₁ h₂ h₃)

/-- Positive control: with an *under*-approximate `ok` summary of the prefix the
composition is a true positive (the IL sequencing rule). -/
theorem il_ok_then_il_er_errReachable {P Q R : Assn σ} {c₁ c₂ : Cmd σ}
    (h₁ : IL P c₁ .ok Q) (h₂ : IL Q c₂ .er R) (hne : ∃ t, R t) :
    ErrReachable P (.seq c₁ c₂) := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨m, hm, hmt⟩ := h₂ t ht
  obtain ⟨s, hs, hsm⟩ := h₁ m hm
  exact ⟨s, t, hs, .seqOk hsm hmt⟩

end Toy.IL
