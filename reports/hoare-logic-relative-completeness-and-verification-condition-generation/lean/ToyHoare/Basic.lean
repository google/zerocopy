/-!
# A small While language: syntax and big-step semantics

Toy model of a deterministic imperative language with unbounded integer variables.
Variables are named by natural numbers; a store maps every variable to an `Int`.
-/

namespace Toy.Hoare

/-- A program state: every variable (named by a natural number) holds an unbounded integer.
Captures the state space of an idealized While language without heap, overflow, or errors. -/
abbrev Store := Nat → Int

/-- Functional update of a store: `upd s x v` maps `x` to `v` and agrees with `s` elsewhere.
Captures the effect of an assignment on the state. -/
def upd (s : Store) (x : Nat) (v : Int) : Store := fun y => if y = x then v else s y

/-- Integer expressions: literals, variables, `+`, `-`, `*`.
Multiplication is included so that programs can compute non-linear functions. -/
inductive AExp where
  | lit : Int → AExp
  | var : Nat → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  deriving Repr, DecidableEq

/-- Evaluation of integer expressions in a store (total; no overflow, no errors). -/
def AExp.eval : AExp → Store → Int
  | .lit n, _ => n
  | .var x, s => s x
  | .add a b, s => a.eval s + b.eval s
  | .sub a b, s => a.eval s - b.eval s
  | .mul a b, s => a.eval s * b.eval s

/-- Boolean expressions (loop and branch guards): constants, comparisons, and connectives. -/
inductive BExp where
  | tt : BExp
  | ff : BExp
  | eq : AExp → AExp → BExp
  | le : AExp → AExp → BExp
  | lt : AExp → AExp → BExp
  | not : BExp → BExp
  | and : BExp → BExp → BExp
  | or : BExp → BExp → BExp
  deriving Repr, DecidableEq

/-- Evaluation of boolean expressions in a store, as a `Bool` (guards always evaluate). -/
def BExp.eval : BExp → Store → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .eq a b, s => decide (a.eval s = b.eval s)
  | .le a b, s => decide (a.eval s ≤ b.eval s)
  | .lt a b, s => decide (a.eval s < b.eval s)
  | .not b, s => !(b.eval s)
  | .and b₁ b₂, s => b₁.eval s && b₂.eval s
  | .or b₁ b₂, s => b₁.eval s || b₂.eval s

/-- Commands of the While language: `skip`, assignment `x := e`, sequencing `c₁; c₂`,
conditional `if b then c₁ else c₂`, and loop `while b do c`. -/
inductive Com where
  | skip : Com
  | assign : Nat → AExp → Com
  | seq : Com → Com → Com
  | cond : BExp → Com → Com → Com
  | whileDo : BExp → Com → Com
  deriving Repr, DecidableEq

/-- Big-step (natural) semantics: `Exec c s s'` holds iff running `c` from `s` terminates in `s'`.
Diverging runs have no final state; the language is deterministic (`Exec.deterministic`). -/
inductive Exec : Com → Store → Store → Prop where
  | skip (s : Store) : Exec .skip s s
  | assign (x : Nat) (e : AExp) (s : Store) : Exec (.assign x e) s (upd s x (e.eval s))
  | seq {c₁ c₂ : Com} {s s₁ s₂ : Store} :
      Exec c₁ s s₁ → Exec c₂ s₁ s₂ → Exec (.seq c₁ c₂) s s₂
  | condTrue {b : BExp} {c₁ c₂ : Com} {s s' : Store} :
      b.eval s = true → Exec c₁ s s' → Exec (.cond b c₁ c₂) s s'
  | condFalse {b : BExp} {c₁ c₂ : Com} {s s' : Store} :
      b.eval s = false → Exec c₂ s s' → Exec (.cond b c₁ c₂) s s'
  | whileFalse {b : BExp} {c : Com} {s : Store} :
      b.eval s = false → Exec (.whileDo b c) s s
  | whileTrue {b : BExp} {c : Com} {s s₁ s₂ : Store} :
      b.eval s = true → Exec c s s₁ → Exec (.whileDo b c) s₁ s₂ → Exec (.whileDo b c) s s₂

/-- The big-step semantics is deterministic: a command has at most one final state. -/
theorem Exec.deterministic {c : Com} {s s₁ s₂ : Store}
    (h₁ : Exec c s s₁) (h₂ : Exec c s s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | skip => cases h₂; rfl
  | assign => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂a h₂b => cases ih₁ h₂a; exact ih₂ h₂b
  | condTrue hb _ ih =>
    cases h₂ with
    | condTrue _ h => exact ih h
    | condFalse hb' _ => rw [hb] at hb'; cases hb'
  | condFalse hb _ ih =>
    cases h₂ with
    | condTrue hb' _ => rw [hb] at hb'; cases hb'
    | condFalse _ h => exact ih h
  | whileFalse hb =>
    cases h₂ with
    | whileFalse _ => rfl
    | whileTrue hb' _ _ => rw [hb] at hb'; cases hb'
  | whileTrue hb _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileFalse hb' => rw [hb] at hb'; cases hb'
    | whileTrue _ h₂a h₂b => cases ih₁ h₂a; exact ih₂ h₂b

/-- Semantic assertions: arbitrary predicates on stores (the "expressive" assertion setting). -/
abbrev Assn := Store → Prop

/-- Partial-correctness validity of the Hoare triple `{P} c {Q}`: every terminating run of `c`
from a state satisfying `P` ends in a state satisfying `Q`. Divergence is allowed. -/
def Valid (P : Assn) (c : Com) (Q : Assn) : Prop :=
  ∀ s s', P s → Exec c s s' → Q s'

/-- Weakest liberal precondition: the states from which every terminating run of `c` ends in `Q`. -/
def wlp (c : Com) (Q : Assn) : Assn :=
  fun s => ∀ s', Exec c s s' → Q s'

theorem valid_iff_imp_wlp {P : Assn} {c : Com} {Q : Assn} :
    Valid P c Q ↔ ∀ s, P s → wlp c Q s :=
  ⟨fun h s hP s' hx => h s s' hP hx, fun h s s' hP hx => h s hP s' hx⟩

theorem wlp_valid (c : Com) (Q : Assn) : Valid (wlp c Q) c Q :=
  fun _ s' h hx => h s' hx

/-! ### Basic store lemmas -/

@[simp] theorem upd_same (s : Store) (x : Nat) (v : Int) : upd s x v x = v := by
  simp [upd]

@[simp] theorem upd_other (s : Store) {x y : Nat} (v : Int) (h : y ≠ x) : upd s x v y = s y := by
  simp [upd, h]

end Toy.Hoare
