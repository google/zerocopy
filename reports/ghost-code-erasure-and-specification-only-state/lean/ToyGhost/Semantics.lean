import ToyGhost.Language

/-!
# Fuel-indexed semantics with failure and divergence

`run n s σ` executes `s` from `σ` with fuel `n`: `some (.ok σ')` is normal
termination, `some .fail` is a failed assertion, and `none` means the fuel ran out.
A program *diverges* from `σ` when it runs out of fuel for every `n`. Because the
language is deterministic, every program has exactly one behaviour from every
state (`Behaves.unique`, `Behaves.exists`).
-/

namespace Toy.Ghost

/-- Result of a finished execution. -/
inductive Outcome where
  | ok (σ : Store)
  | fail

/-- Sequential composition of a partial result with a continuation. -/
def Outcome.bind : Option Outcome → (Store → Option Outcome) → Option Outcome
  | some (.ok σ), k => k σ
  | some .fail, _ => some .fail
  | none, _ => none

/-- Fuel-indexed big-step interpreter. Every construct consumes one unit of fuel. -/
def run : Nat → Stmt → Store → Option Outcome
  | 0, _, _ => none
  | _ + 1, .skip, σ => some (.ok σ)
  | _ + 1, .assign x e, σ => some (.ok (σ.update x (e.eval σ)))
  | _ + 1, .assert e, σ => if e.eval σ = 0 then some .fail else some (.ok σ)
  | n + 1, .seq s t, σ => Outcome.bind (run n s σ) (run n t)
  | n + 1, .ite c s t, σ => if c.eval σ = 0 then run n t σ else run n s σ
  | n + 1, .loop c b, σ =>
      if c.eval σ = 0 then some (.ok σ) else Outcome.bind (run n b σ) (run n (.loop c b))
  | n + 1, .ghost s, σ => run n s σ

/-- Complete behaviours of a deterministic program from one initial state. -/
inductive Behaviour where
  | term (σ : Store)
  | fail
  | diverge

/-- `Behaves s σ b`: running `s` from `σ` has behaviour `b`. -/
def Behaves (s : Stmt) (σ : Store) : Behaviour → Prop
  | .term σ' => ∃ n, run n s σ = some (.ok σ')
  | .fail => ∃ n, run n s σ = some .fail
  | .diverge => ∀ n, run n s σ = none

/-- `s` fails (an assertion is violated) when run from `σ`. -/
def Fails (s : Stmt) (σ : Store) : Prop := Behaves s σ .fail

/-- `s` diverges (runs out of fuel for every fuel bound) when run from `σ`. -/
def Diverges (s : Stmt) (σ : Store) : Prop := Behaves s σ .diverge

/-- Real-observable behaviours: final real store, failure, or divergence. -/
inductive RBehaviour where
  | term (r : RStore)
  | fail
  | diverge

/-- Forget the ghost part of a behaviour. -/
def Behaviour.real : Behaviour → RBehaviour
  | .term σ => .term (realPart σ)
  | .fail => .fail
  | .diverge => .diverge

/-- `RBehaves s σ rb`: running `s` from `σ` has real-observable behaviour `rb`. -/
def RBehaves (s : Stmt) (σ : Store) (rb : RBehaviour) : Prop :=
  ∃ b, Behaves s σ b ∧ b.real = rb

/-! ## Basic facts: monotonicity in fuel, determinism, totality -/

theorem Outcome.bind_eq_some {o : Option Outcome} {k : Store → Option Outcome} {r : Outcome}
    (h : Outcome.bind o k = some r) :
    (∃ σ, o = some (.ok σ) ∧ k σ = some r) ∨ (o = some .fail ∧ r = .fail) := by
  match o, h with
  | some (.ok σ), h => exact Or.inl ⟨σ, rfl, h⟩
  | some .fail, h => cases h; exact Or.inr ⟨rfl, rfl⟩

theorem run_succ_of_eq_some {n : Nat} {s : Stmt} {σ : Store} {o : Outcome}
    (h : run n s σ = some o) : run (n + 1) s σ = some o := by
  induction n generalizing s σ o with
  | zero => simp [run] at h
  | succ n ih =>
    cases s with
    | skip => simpa [run] using h
    | assign x e => simpa [run] using h
    | assert e => simpa [run] using h
    | seq s t =>
      simp only [run] at h ⊢
      rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨h1, rfl⟩
      · rw [ih h1]; exact ih h2
      · rw [ih h1]; rfl
    | ite c s t =>
      simp only [run] at h ⊢
      split <;> simp_all
    | loop c b =>
      simp only [run] at h ⊢
      split
      · simp_all
      · rename_i hc
        simp only [hc, ↓reduceIte] at h
        rcases Outcome.bind_eq_some h with ⟨σ1, h1, h2⟩ | ⟨h1, rfl⟩
        · rw [ih h1]; exact ih h2
        · rw [ih h1]; rfl
    | ghost s => simp only [run] at h ⊢; exact ih h

theorem run_mono {n m : Nat} {s : Stmt} {σ : Store} {o : Outcome}
    (h : run n s σ = some o) (hnm : n ≤ m) : run m s σ = some o := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact run_succ_of_eq_some ih

theorem run_det {n m : Nat} {s : Stmt} {σ : Store} {o o' : Outcome}
    (h : run n s σ = some o) (h' : run m s σ = some o') : o = o' := by
  rcases Nat.le_total n m with hnm | hmn
  · have := run_mono h hnm; rw [this] at h'; exact Option.some.inj h'
  · have := run_mono h' hmn; rw [this] at h; exact (Option.some.inj h).symm

/-- Determinism: a program has at most one behaviour from a given state. -/
theorem Behaves.unique {s : Stmt} {σ : Store} {b b' : Behaviour}
    (h : Behaves s σ b) (h' : Behaves s σ b') : b = b' := by
  cases b <;> cases b' <;> simp only [Behaves] at h h'
  · obtain ⟨n, hn⟩ := h; obtain ⟨m, hm⟩ := h'
    cases run_det hn hm; rfl
  · obtain ⟨n, hn⟩ := h; obtain ⟨m, hm⟩ := h'; cases run_det hn hm
  · obtain ⟨n, hn⟩ := h; rw [h' n] at hn; cases hn
  · obtain ⟨n, hn⟩ := h; obtain ⟨m, hm⟩ := h'; cases run_det hn hm
  · rfl
  · obtain ⟨n, hn⟩ := h; rw [h' n] at hn; cases hn
  · obtain ⟨n, hn⟩ := h'; rw [h n] at hn; cases hn
  · obtain ⟨n, hn⟩ := h'; rw [h n] at hn; cases hn
  · rfl

/-- Totality: every program has some behaviour from every state. -/
theorem Behaves.exists (s : Stmt) (σ : Store) : ∃ b, Behaves s σ b := by
  by_cases h : ∀ n, run n s σ = none
  · exact ⟨.diverge, h⟩
  · simp only [Classical.not_forall] at h
    obtain ⟨n, hn⟩ := h
    match hr : run n s σ, hn with
    | some (.ok σ'), _ => exact ⟨.term σ', n, hr⟩
    | some .fail, _ => exact ⟨.fail, n, hr⟩

theorem RBehaves.unique {s : Stmt} {σ : Store} {rb rb' : RBehaviour}
    (h : RBehaves s σ rb) (h' : RBehaves s σ rb') : rb = rb' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  rw [Behaves.unique hb hb']

theorem RBehaves.exists (s : Stmt) (σ : Store) : ∃ rb, RBehaves s σ rb := by
  obtain ⟨b, hb⟩ := Behaves.exists s σ
  exact ⟨b.real, b, hb, rfl⟩

/-- Once one behaviour is known, the real-observable behaviours are exactly its
projection. -/
theorem RBehaves.iff_of_behaves {s : Stmt} {σ : Store} {b0 : Behaviour}
    (h : Behaves s σ b0) (rb : RBehaviour) : RBehaves s σ rb ↔ rb = b0.real := by
  constructor
  · rintro ⟨b, hb, rfl⟩; rw [Behaves.unique hb h]
  · rintro rfl; exact ⟨b0, h, rfl⟩

theorem RBehaves.of_behaves {s : Stmt} {σ : Store} {b : Behaviour}
    (h : Behaves s σ b) : RBehaves s σ b.real := ⟨b, h, rfl⟩

end Toy.Ghost
