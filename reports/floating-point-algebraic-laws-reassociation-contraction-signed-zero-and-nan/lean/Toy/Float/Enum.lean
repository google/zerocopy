/-
Toy.Float.Enum
==============

Boolean enumerators over the finitely many values of a format, with
correctness lemmas, and the `Decidable` instances they induce for universal
quantifiers over `FP f` and over environments `Fin n → FP f`. These make every
bounded claim about a concrete small format checkable by `decide +kernel`
(kernel evaluation; no native code).
-/
import Toy.Float.Defs

namespace Toy.Float

/-- `allBelow n g` is `true` iff `g i = true` for every `i < n`. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, g => g n && allBelow n g

theorem allBelow_iff (n : Nat) (g : Nat → Bool) :
    allBelow n g = true ↔ ∀ i, i < n → g i = true := by
  induction n with
  | zero => exact iff_of_true rfl (fun i hi => absurd hi (Nat.not_lt_zero i))
  | succ n ih =>
    show (g n && allBelow n g) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · exact h2 i h
      · subst h; exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

variable {f : Fmt}

namespace FP

/-- `true` iff `q` holds on every finite value. -/
def allFin (f : Fmt) (q : FP f → Bool) : Bool :=
  [false, true].all fun s =>
    allBelow f.expCount fun E => allBelow f.fracCount fun M =>
      if h : E < f.expCount ∧ M < f.fracCount then q (.fin s ⟨E, h.1⟩ ⟨M, h.2⟩) else true

/-- `true` iff `q` holds on every value of the format. -/
def all (f : Fmt) (q : FP f → Bool) : Bool :=
  q .nan && q (.inf false) && q (.inf true) && allFin f q

theorem allFin_iff (q : FP f → Bool) :
    allFin f q = true ↔ ∀ s E M, q (.fin s E M) = true := by
  unfold allFin
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, allBelow_iff]
  constructor
  · rintro ⟨h0, h1⟩ s E M
    cases s
    · have := h0 E.val E.isLt M.val M.isLt
      simpa [E.isLt, M.isLt] using this
    · have := h1 E.val E.isLt M.val M.isLt
      simpa [E.isLt, M.isLt] using this
  · intro h
    refine ⟨fun E hE M hM => ?_, fun E hE M hM => ?_⟩
    · simpa [hE, hM] using h false ⟨E, hE⟩ ⟨M, hM⟩
    · simpa [hE, hM] using h true ⟨E, hE⟩ ⟨M, hM⟩

theorem all_iff (q : FP f → Bool) : all f q = true ↔ ∀ x, q x = true := by
  unfold all
  simp only [Bool.and_eq_true, allFin_iff]
  constructor
  · rintro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ x
    cases x with
    | nan => exact h0
    | inf s => cases s <;> assumption
    | fin s E M => exact h3 s E M
  · intro h
    exact ⟨⟨⟨h _, h _⟩, h _⟩, fun s E M => h _⟩

instance decForall (P : FP f → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (all f (fun x => decide (P x)) = true) (by simp [all_iff])

end FP

/-- Prepend a value to an environment (variable `0` gets `a`). -/
def consEnv {α : Type} {n : Nat} (a : α) (env : Fin n → α) : Fin (n + 1) → α :=
  fun i => if h : i.val = 0 then a else env ⟨i.val - 1, by omega⟩

theorem consEnv_head_tail {α : Type} {n : Nat} (env : Fin (n + 1) → α) :
    consEnv (env ⟨0, by omega⟩) (fun i => env ⟨i.val + 1, by omega⟩) = env := by
  funext i
  unfold consEnv
  by_cases h : i.val = 0
  · simp only [h, dite_true]; congr 1; exact Fin.ext h.symm
  · simp only [h, dite_false]; congr; omega

/-- `true` iff `q` holds on every environment `Fin n → FP f`. -/
def allEnv (f : Fmt) : (n : Nat) → ((Fin n → FP f) → Bool) → Bool
  | 0, q => q Fin.elim0
  | n + 1, q => FP.all f fun a => allEnv f n fun env => q (consEnv a env)

theorem allEnv_iff : (n : Nat) → (q : (Fin n → FP f) → Bool) →
    allEnv f n q = true ↔ ∀ env, q env = true
  | 0, q => by
    constructor
    · intro h env
      have : env = Fin.elim0 := funext fun i => Fin.elim0 i
      subst this; exact h
    · intro h; exact h _
  | n + 1, q => by
    show FP.all f _ = true ↔ _
    rw [FP.all_iff]
    constructor
    · intro h env
      have := (allEnv_iff n _).mp (h (env ⟨0, by omega⟩)) (fun i => env ⟨i.val + 1, by omega⟩)
      rwa [consEnv_head_tail] at this
    · intro h a
      exact (allEnv_iff n _).mpr fun env => h _

instance decForallEnv (n : Nat) (P : (Fin n → FP f) → Prop) [DecidablePred P] :
    Decidable (∀ env, P env) :=
  decidable_of_iff (allEnv f n (fun env => decide (P env)) = true) (by simp [allEnv_iff])

instance {n : Nat} (S : Flags) (r : Rewrite f n) : Decidable (ValidMod S r) := by
  unfold ValidMod; infer_instance

instance {n : Nat} (r : Rewrite f n) : Decidable (Valid r) :=
  inferInstanceAs (Decidable (ValidMod {} r))

/-- The list of all values of a format (for display and search). -/
def FP.list (f : Fmt) : List (FP f) :=
  .nan :: .inf false :: .inf true ::
    ([false, true].flatMap fun s => (List.finRange f.expCount).flatMap fun E =>
      (List.finRange f.fracCount).map fun M => FP.fin s E M)

end Toy.Float
