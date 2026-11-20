/-!
# Toy incorrectness logic: commands, relational semantics, and the two kinds of triple

A small nondeterministic command language with two exit kinds (`ok`, `er`), a big-step
relational semantics, and the two semantic triples studied in this package:

* Hoare (over-approximate, partial-correctness) triples `{P} c {e : Q}`, meaning
  `post c e P ⊆ Q`;
* incorrectness (under-approximate) triples `[P] c [e : Q]`, meaning `Q ⊆ post c e P`.

The language follows the generic fragment of O'Hearn's *Incorrectness Logic* (POPL 2020):
deterministic state update (standing in for assignment `x := e`), `assume b`, `error()`,
sequencing, binary nondeterministic choice, and Kleene star. Assertions are semantic
(predicates on states), as in that paper.
-/

namespace Toy.IL

/-- Exit kinds: normal termination (`ok`) and erroneous termination (`er`, raised by
`error`). -/
inductive Exit where
  | ok
  | er
  deriving DecidableEq, Repr

/-- Commands over an arbitrary state type `σ`.

* `assign f` is a deterministic state update; it models an assignment `x := e` (with
  `f s = s[x ↦ ⟦e⟧ s]` when states are stores).
* `assume b` continues normally iff `b` holds and otherwise blocks (no outcome at all).
* `error` stops immediately with exit kind `er`, leaving the state unchanged.
* `seq`, `choice`, `star` are sequencing, nondeterministic choice and iteration (zero or
  more times). -/
inductive Cmd (σ : Type) where
  | assign (f : σ → σ)
  | assume (b : σ → Bool)
  | error
  | seq (c₁ c₂ : Cmd σ)
  | choice (c₁ c₂ : Cmd σ)
  | star (c : Cmd σ)

variable {σ : Type}

/-- `skip` is `assume true`. -/
def Cmd.skip : Cmd σ := .assume (fun _ => true)

/-- Big-step relational semantics with exit kinds: `Exec c s e t` says that `c`, started in
`s`, can terminate with exit kind `e` in state `t`.

This is the relational semantics of O'Hearn (POPL 2020, Fig. 4) presented inductively:
`⟦c₁;c₂⟧ok = ⟦c₁⟧ok;⟦c₂⟧ok`, `⟦c₁;c₂⟧er = ⟦c₁⟧er ∪ ⟦c₁⟧ok;⟦c₂⟧er` (an error
short-circuits the rest), and `⟦c⋆⟧e = ⋃ₙ ⟦cⁿ⟧e`. Divergence is implicit: a program that
never terminates simply has no outcome. -/
inductive Exec : Cmd σ → σ → Exit → σ → Prop where
  | assign {f : σ → σ} {s : σ} : Exec (.assign f) s .ok (f s)
  | assume {b : σ → Bool} {s : σ} : b s = true → Exec (.assume b) s .ok s
  | error {s : σ} : Exec .error s .er s
  | seqOk {c₁ c₂ : Cmd σ} {s m t : σ} {e : Exit} :
      Exec c₁ s .ok m → Exec c₂ m e t → Exec (.seq c₁ c₂) s e t
  | seqEr {c₁ c₂ : Cmd σ} {s t : σ} : Exec c₁ s .er t → Exec (.seq c₁ c₂) s .er t
  | choiceL {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} : Exec c₁ s e t → Exec (.choice c₁ c₂) s e t
  | choiceR {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} : Exec c₂ s e t → Exec (.choice c₁ c₂) s e t
  | starNil {c : Cmd σ} {s : σ} : Exec (.star c) s .ok s
  | starOk {c : Cmd σ} {s m t : σ} {e : Exit} :
      Exec c s .ok m → Exec (.star c) m e t → Exec (.star c) s e t
  | starEr {c : Cmd σ} {s t : σ} : Exec c s .er t → Exec (.star c) s .er t

/-! ### Inversion lemmas -/

@[simp] theorem exec_assign_iff {f : σ → σ} {s t : σ} {e : Exit} :
    Exec (.assign f) s e t ↔ e = .ok ∧ t = f s := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .assign

@[simp] theorem exec_assume_iff {b : σ → Bool} {s t : σ} {e : Exit} :
    Exec (.assume b) s e t ↔ e = .ok ∧ t = s ∧ b s = true := by
  constructor
  · intro h; cases h with | assume hb => exact ⟨rfl, rfl, hb⟩
  · rintro ⟨rfl, rfl, hb⟩; exact .assume hb

@[simp] theorem exec_error_iff {s t : σ} {e : Exit} :
    Exec (.error : Cmd σ) s e t ↔ e = .er ∧ t = s := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .error

@[simp] theorem exec_seq_iff {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} :
    Exec (.seq c₁ c₂) s e t ↔
      (∃ m, Exec c₁ s .ok m ∧ Exec c₂ m e t) ∨ (e = .er ∧ Exec c₁ s .er t) := by
  constructor
  · intro h
    cases h with
    | seqOk h₁ h₂ => exact Or.inl ⟨_, h₁, h₂⟩
    | seqEr h₁ => exact Or.inr ⟨rfl, h₁⟩
  · rintro (⟨m, h₁, h₂⟩ | ⟨rfl, h₁⟩)
    · exact .seqOk h₁ h₂
    · exact .seqEr h₁

@[simp] theorem exec_choice_iff {c₁ c₂ : Cmd σ} {s t : σ} {e : Exit} :
    Exec (.choice c₁ c₂) s e t ↔ Exec c₁ s e t ∨ Exec c₂ s e t := by
  constructor
  · intro h
    cases h with
    | choiceL h => exact Or.inl h
    | choiceR h => exact Or.inr h
  · rintro (h | h)
    · exact .choiceL h
    · exact .choiceR h

@[simp] theorem exec_skip_iff {s t : σ} {e : Exit} :
    Exec (Cmd.skip : Cmd σ) s e t ↔ e = .ok ∧ t = s := by
  simp [Cmd.skip]

/-- One-step unfolding of iteration (not a simp lemma: it would loop). -/
theorem exec_star_iff {c : Cmd σ} {s t : σ} {e : Exit} :
    Exec (.star c) s e t ↔
      (e = .ok ∧ t = s) ∨ (∃ m, Exec c s .ok m ∧ Exec (.star c) m e t) ∨
        (e = .er ∧ Exec c s .er t) := by
  constructor
  · intro h
    cases h with
    | starNil => exact Or.inl ⟨rfl, rfl⟩
    | starOk h₁ h₂ => exact Or.inr (Or.inl ⟨_, h₁, h₂⟩)
    | starEr h₁ => exact Or.inr (Or.inr ⟨rfl, h₁⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨m, h₁, h₂⟩ | ⟨rfl, h₁⟩)
    · exact .starNil
    · exact .starOk h₁ h₂
    · exact .starEr h₁

/-- Appending one more iteration: `c⋆ ; c ⊆ c⋆` (for both exit kinds). -/
theorem exec_star_snoc {c : Cmd σ} {s m t : σ} {e : Exit}
    (h₁ : Exec (.star c) s .ok m) (h₂ : Exec c m e t) : Exec (.star c) s e t := by
  generalize hc : Cmd.star c = cs at h₁
  generalize he : Exit.ok = eo at h₁
  induction h₁ with
  | starNil =>
    cases hc
    cases e with
    | ok => exact .starOk h₂ .starNil
    | er => exact .starEr h₂
  | starOk ha _ _ ih₂ =>
    cases hc
    exact .starOk ha (ih₂ h₂ rfl he)
  | starEr _ => cases he
  | assign => cases hc
  | assume _ => cases hc
  | error => cases hc
  | seqOk _ _ _ _ => cases hc
  | seqEr _ _ => cases hc
  | choiceL _ _ => cases hc
  | choiceR _ _ => cases hc

/-- An erroneous run of `c⋆` is a normal run of `c⋆` followed by one erroneous run of `c`. -/
theorem exec_star_er_split {c : Cmd σ} {s t : σ} (h : Exec (.star c) s .er t) :
    ∃ m, Exec (.star c) s .ok m ∧ Exec c m .er t := by
  generalize hc : Cmd.star c = cs at h
  generalize he : Exit.er = ee at h
  induction h with
  | starNil => cases he
  | starOk ha _ _ ih₂ =>
    cases hc
    obtain ⟨m, hm₁, hm₂⟩ := ih₂ rfl he
    exact ⟨m, .starOk ha hm₁, hm₂⟩
  | starEr ha =>
    cases hc
    exact ⟨_, .starNil, ha⟩
  | assign => cases hc
  | assume _ => cases hc
  | error => cases hc
  | seqOk _ _ _ _ => cases hc
  | seqEr _ _ => cases hc
  | choiceL _ _ => cases hc
  | choiceR _ _ => cases hc

/-! ### Assertions, post-images, triples -/

/-- Assertions are semantic: predicates on states (as in O'Hearn 2020, which treats
assertions as subsets of the state space). -/
abbrev Assn (σ : Type) := σ → Prop

/-- Entailment between semantic assertions: `P ⊆ Q` as sets of states. -/
def Entails (P Q : Assn σ) : Prop := ∀ s, P s → Q s

/-- Post-image of `c` at exit kind `e`: the states in which `c` can terminate with exit
kind `e` when started in some state satisfying `P` (O'Hearn 2020, Definition 1). -/
def post (c : Cmd σ) (e : Exit) (P : Assn σ) : Assn σ := fun t => ∃ s, P s ∧ Exec c s e t

/-- Hoare (over-approximate, partial-correctness) triple `{P} c {e : Q}`:
`post c e P ⊆ Q`. Every `e`-exit of `c` from a `P` state lands in `Q`. It says nothing
about termination and nothing about the other exit kind. -/
def Hoare (P : Assn σ) (c : Cmd σ) (e : Exit) (Q : Assn σ) : Prop := Entails (post c e P) Q

/-- Incorrectness (under-approximate) triple `[P] c [e : Q]`: `Q ⊆ post c e P`. Every
state in `Q` is reachable, with exit kind `e`, by running `c` from some state in `P`. -/
def IL (P : Assn σ) (c : Cmd σ) (e : Exit) (Q : Assn σ) : Prop := Entails Q (post c e P)

/-- Some run of `c` from a `P` state terminates with an error: a *true positive* bug
report for precondition `P`. -/
def ErrReachable (P : Assn σ) (c : Cmd σ) : Prop := ∃ s t, P s ∧ Exec c s .er t

/-- Safety from `P`: no run of `c` from a `P` state terminates with an error. -/
def Safe (P : Assn σ) (c : Cmd σ) : Prop := ∀ s t, P s → ¬ Exec c s .er t

theorem hoare_iff {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    Hoare P c e Q ↔ ∀ s t, P s → Exec c s e t → Q t := by
  constructor
  · intro h s t hs hst; exact h t ⟨s, hs, hst⟩
  · rintro h t ⟨s, hs, hst⟩; exact h s t hs hst

/-- O'Hearn 2020, Lemma 3 (Characterization): an IL triple holds iff every state of the
post is reachable from some state of the pre. -/
theorem il_iff {P Q : Assn σ} {c : Cmd σ} {e : Exit} :
    IL P c e Q ↔ ∀ t, Q t → ∃ s, P s ∧ Exec c s e t := Iff.rfl

theorem safe_iff_not_errReachable {P : Assn σ} {c : Cmd σ} :
    Safe P c ↔ ¬ ErrReachable P c := by
  constructor
  · rintro h ⟨s, t, hs, hst⟩; exact h s t hs hst
  · intro h s t hs hst; exact h ⟨s, t, hs, hst⟩

/-! ### Definition examples (positive and negative) -/

section Examples

/-- `x := x + 1; error()` from `0` errs in state `1`. -/
theorem exec_pos_seq_error : Exec (Cmd.seq (.assign Nat.succ) .error) 0 .er 1 :=
  .seqOk .assign .error

/-- Iteration admits three unrollings. -/
theorem exec_pos_star_three : Exec (Cmd.star (.assign Nat.succ)) 0 .ok 3 :=
  .starOk .assign (.starOk .assign (.starOk .assign .starNil))

/-- `error()` never terminates normally. -/
theorem exec_neg_error_ok (s t : Nat) : ¬ Exec (Cmd.error : Cmd Nat) s .ok t := by
  simp

/-- A failing `assume` has no outcome at all (it blocks rather than erring). -/
theorem exec_neg_assume_false (s t : Nat) (e : Exit) :
    ¬ Exec (Cmd.assume (fun _ => false) : Cmd Nat) s e t := by
  simp

/-- An error after an operation is reported in the updated state, not the initial one. -/
theorem exec_neg_seq_error_state : ¬ Exec (Cmd.seq (.assign Nat.succ) .error) 0 .er 0 := by
  simp

/-- Iterating an error-free body never errs. -/
theorem exec_neg_star_assign_er (f : Nat → Nat) (s t : Nat) :
    ¬ Exec (Cmd.star (.assign f)) s .er t := by
  intro h
  obtain ⟨_, _, h₂⟩ := exec_star_er_split h
  simp at h₂

theorem entails_pos : Entails (fun n : Nat => n = 0) (fun n => n ≤ 1) := by
  intro n hn; omega

theorem entails_neg : ¬ Entails (fun n : Nat => n ≤ 1) (fun n => n = 0) := by
  intro h; exact absurd (h 1 (by decide)) (by decide)

theorem post_pos : post (Cmd.assign Nat.succ) .ok (fun n => n = 0) 1 := ⟨0, rfl, .assign⟩

theorem post_neg : ¬ post (Cmd.assign Nat.succ) .ok (fun n => n = 0) 0 := by
  rintro ⟨s, hs, h⟩; simp at h

theorem hoare_pos : Hoare (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n = 1) := by
  rintro t ⟨s, rfl, h⟩; simp at h; omega

/-- A Hoare triple about the `ok` exit of `error()` holds with post `False`. -/
theorem hoare_pos_error_ok : Hoare (fun _ : Nat => True) .error .ok (fun _ => False) := by
  rintro t ⟨s, _, h⟩; simp at h

theorem hoare_neg : ¬ Hoare (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n = 0) := by
  intro h; exact absurd (h 1 post_pos) (by decide)

theorem il_pos : IL (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n = 1) := by
  intro t ht; subst ht; exact ⟨0, rfl, .assign⟩

/-- Under-approximation may drop a nondeterministic branch: `x := 0 + x := 2` achieves
`[ok : x = 2]`. -/
theorem il_pos_drop_branch :
    IL (fun _ : Nat => True) (.choice (.assign (fun _ => 0)) (.assign (fun _ => 2))) .ok
      (fun n => n = 2) := by
  intro t ht; subst ht; exact ⟨0, trivial, .choiceR .assign⟩

/-- An over-approximate post is not an under-approximate one: from `x = 0`, `x := x + 1`
does not achieve `[ok : x = 1 ∨ x = 2]`. -/
theorem il_neg : ¬ IL (fun n : Nat => n = 0) (.assign Nat.succ) .ok (fun n => n = 1 ∨ n = 2) := by
  intro h
  obtain ⟨s, hs, hst⟩ := h 2 (Or.inr rfl)
  simp at hst; omega

theorem errReachable_pos :
    ErrReachable (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) :=
  ⟨7, 7, rfl, .seqOk (.assume rfl) .error⟩

theorem errReachable_neg :
    ¬ ErrReachable (fun n : Nat => n = 0) (.seq (.assume (fun n => n == 7)) .error) := by
  rintro ⟨s, t, rfl, h⟩; simp at h

theorem safe_pos : Safe (fun _ : Nat => True) (.seq (.assume (fun _ => false)) .error) := by
  intro s t _ h; simp at h

theorem safe_neg : ¬ Safe (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) := by
  intro h; exact h 7 7 rfl (.seqOk (.assume rfl) .error)

end Examples

end Toy.IL
