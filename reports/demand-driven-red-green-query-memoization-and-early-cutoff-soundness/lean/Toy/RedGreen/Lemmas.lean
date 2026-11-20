/-
Toy.RedGreen.Lemmas
===================

Fully proved general lemmas: from-scratch evaluation is fuel-monotone, the
traced and untraced runs agree, and a consistent database gives a working
database satisfying the simulation invariant.
-/
import Toy.RedGreen.Basic

namespace Toy.RedGreen

theorem Prog.runT_fst {K V F : Type} (f : K → Out V) (fp : V → F) :
    ∀ p : Prog K V, (p.runT f fp).1 = p.run f
  | .ret _ => rfl
  | .panic => rfl
  | .fetch k c => by
    simp only [Prog.runT, Prog.run]
    cases f k with
    | val v => exact Prog.runT_fst f fp (c v)
    | panic => rfl
    | stuck => rfl

/-- Running against an oracle `g` that agrees with `f` wherever `f` is not
`stuck` gives the same outcome, provided the run against `f` is not `stuck`. -/
theorem Prog.run_congr_of_ne_stuck {K V : Type} (f g : K → Out V)
    (h : ∀ k, f k ≠ .stuck → g k = f k) :
    ∀ p : Prog K V, p.run f ≠ .stuck → p.run g = p.run f
  | .ret _, _ => rfl
  | .panic, _ => rfl
  | .fetch k c, hne => by
    simp only [Prog.run] at hne ⊢
    have hfk_ne : f k ≠ .stuck := by
      intro h0; rw [h0] at hne; exact hne rfl
    rw [h k hfk_ne]
    cases hfk : f k with
    | val v =>
      rw [hfk] at hne
      exact Prog.run_congr_of_ne_stuck f g h (c v) hne
    | panic => rfl
    | stuck => exact absurd hfk hfk_ne

/-- From-scratch evaluation is monotone in fuel: once it finishes, more fuel
gives the same outcome. -/
theorem eval_mono {Q I V : Type} (rules : Rules Q I V) (inp : I → V) :
    ∀ n m (k : Key Q I), n ≤ m → eval rules inp n k ≠ .stuck → eval rules inp m k = eval rules inp n k
  | 0, _, _, _, h => absurd rfl h
  | n + 1, m, k, hle, h => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases k with
    | inr i => rfl
    | inl q =>
      simp only [eval] at h ⊢
      exact Prog.run_congr_of_ne_stuck _ _
        (fun k' hk' => eval_mono rules inp n m' k' (by omega) hk') _ h

/-- Two finished from-scratch evaluations of the same key agree. -/
theorem eval_eq_of_ne_stuck {Q I V : Type} (rules : Rules Q I V) (inp : I → V) (k : Key Q I)
    {n m : Nat} (hn : eval rules inp n k ≠ .stuck) (hm : eval rules inp m k ≠ .stuck) :
    eval rules inp n k = eval rules inp m k := by
  rw [← eval_mono rules inp n (max n m) k (Nat.le_max_left _ _) hn,
      ← eval_mono rules inp m (max n m) k (Nat.le_max_right _ _) hm]

/-- A consistent database gives a starting working database satisfying the
simulation invariant (for any new input state). -/
theorem inv_start {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (oldInp newInp : I → V)
    (odb : OldDB Q I V F) (hcons : DBConsistent rules fp oldInp odb) :
    Inv rules fp oldInp newInp (start odb) := by
  intro q
  unfold start
  cases h : odb q with
  | none => trivial
  | some e => exact hcons q e h

/-- Refuting `AgreesWithEval` by a finished incremental outcome that differs
from a finished from-scratch outcome. -/
theorem not_agrees_of_wrong_outcome {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    {cfg : Config} {rules : Rules Q I V} {fp : V → F} {inp : I → V} {db : DB Q I V F}
    {k : Key Q I} (m n : Nat) (o : Out V) (hf : (fetch cfg rules fp inp m db k).1 = o)
    (ho : o ≠ .stuck) (he : eval rules inp n k ≠ .stuck) (hne : eval rules inp n k ≠ o) :
    ¬ AgreesWithEval cfg rules fp inp db k := by
  intro h
  obtain ⟨n', hn'⟩ := h.1 m (by rw [hf]; exact ho)
  rw [hf] at hn'
  have heq := eval_eq_of_ne_stuck rules inp k (by rw [hn']; exact ho) he
  exact hne (heq.symm.trans hn')

/-- Refuting `AgreesWithEval` by a fuel at which from-scratch evaluation
finishes but the incremental fetch does not. -/
theorem not_agrees_of_stuck {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    {cfg : Config} {rules : Rules Q I V} {fp : V → F} {inp : I → V} {db : DB Q I V F}
    {k : Key Q I} (n : Nat) (he : eval rules inp n k ≠ .stuck)
    (hf : (fetch cfg rules fp inp n db k).1 = .stuck) :
    ¬ AgreesWithEval cfg rules fp inp db k :=
  fun h => h.2 n he hf

/-- A finished from-scratch outcome excludes every other outcome at every
fuel. -/
theorem eval_ne_of_eval_eq {Q I V : Type} (rules : Rules Q I V) (inp : I → V) (k : Key Q I)
    {n₀ : Nat} {o₀ o : Out V} (h₀ : eval rules inp n₀ k = o₀) (hs : o₀ ≠ .stuck)
    (hos : o ≠ .stuck) (hne : o ≠ o₀) : ∀ n, eval rules inp n k ≠ o := by
  intro n hn
  have h := eval_eq_of_ne_stuck rules inp k (n := n) (m := n₀) (by rw [hn]; exact hos)
    (by rw [h₀]; exact hs)
  rw [hn, h₀] at h
  exact hne h

/-- A fetch that is `stuck` at every fuel is not eventually equal to a
terminating from-scratch evaluation. -/
theorem not_eventually_eq_of_stuck {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    {cfg : Config} {rules : Rules Q I V} {fp : V → F} {inp : I → V} {db : DB Q I V F}
    {k : Key Q I} (n₀ : Nat) (he : eval rules inp n₀ k ≠ .stuck)
    (hf : ∀ m, (fetch cfg rules fp inp m db k).1 = .stuck) :
    ¬ ∃ N, ∀ m, N ≤ m → (fetch cfg rules fp inp m db k).1 = eval rules inp m k := by
  intro ⟨N, hN⟩
  have h := hN (max N n₀) (Nat.le_max_left _ _)
  rw [hf, eval_mono rules inp n₀ (max N n₀) k (Nat.le_max_right _ _) he] at h
  exact he h.symm

/-- A fetch that is `stuck` at every fuel does not eventually finish. -/
theorem not_eventually_finishes_of_stuck {Q I V F : Type} [DecidableEq Q] [DecidableEq F]
    {cfg : Config} {rules : Rules Q I V} {fp : V → F} {inp : I → V} {db : DB Q I V F}
    {k : Key Q I} (hf : ∀ m, (fetch cfg rules fp inp m db k).1 = .stuck) :
    ¬ ∃ N, ∀ m, N ≤ m → (fetch cfg rules fp inp m db k).1 ≠ .stuck :=
  fun ⟨N, hN⟩ => hN N (Nat.le_refl N) (hf N)


theorem Prog.runT_congr_of_ne_stuck {K V F : Type} (f g : K → Out V) (fp : V → F)
    (h : ∀ k, f k ≠ .stuck → g k = f k) :
    ∀ p : Prog K V, (p.runT f fp).1 ≠ .stuck → p.runT g fp = p.runT f fp
  | .ret _, _ => rfl
  | .panic, _ => rfl
  | .fetch k c, hne => by
    simp only [Prog.runT] at hne ⊢
    have hfk_ne : f k ≠ .stuck := by
      intro h0; rw [h0] at hne; exact hne rfl
    rw [h k hfk_ne]
    cases hfk : f k with
    | val v =>
      rw [hfk] at hne
      simp only at hne ⊢
      rw [Prog.runT_congr_of_ne_stuck f g fp h (c v) hne]
    | panic => rfl
    | stuck => exact absurd hfk hfk_ne

/-- An input state determines at most one consistent entry per query. -/
theorem entryConsistent_unique {Q I V F : Type} (rules : Rules Q I V) (fp : V → F) (inp : I → V)
    (q : Q) {e e' : Entry Q I V F} (h : EntryConsistent rules fp inp q e)
    (h' : EntryConsistent rules fp inp q e') : e = e' := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨n', hn'⟩ := h'
  have key : ∀ a b, a ≤ b → ((rules q).runT (eval rules inp a) fp).1 ≠ .stuck →
      (rules q).runT (eval rules inp b) fp = (rules q).runT (eval rules inp a) fp :=
    fun a b hab hne =>
      Prog.runT_congr_of_ne_stuck _ _ fp (fun k hk => eval_mono rules inp a b k hab hk) _ hne
  have h1 := key n (max n n') (Nat.le_max_left _ _) (by rw [hn]; intro hc; cases hc)
  have h2 := key n' (max n n') (Nat.le_max_right _ _) (by rw [hn']; intro hc; cases hc)
  rw [hn] at h1
  rw [hn', h1] at h2
  cases e; cases e'
  cases h2
  rfl

end Toy.RedGreen
