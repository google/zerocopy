/-
Toy.SCT.Enum
============

An explicit finite list of all size-change graphs of a given shape, with membership and length.
Used to supply the finite colour set for the Ramsey argument and the counting bound for the
checker's fuel.
-/
import Toy.SCT.Graph

namespace Toy.SCT

/-- All three labels. -/
def allLabels : List Label := [Label.absent, Label.nonstrict, Label.strict]

theorem mem_allLabels (l : Label) : l ∈ allLabels := by
  cases l <;> simp [allLabels]

/-- Prepend a value to a tuple. -/
def finCons {α : Type} {n : Nat} (a : α) (f : Fin n → α) : Fin (n + 1) → α :=
  fun i => if h : i.val = 0 then a else f ⟨i.val - 1, by omega⟩

theorem finCons_head_tail {α : Type} {n : Nat} (f : Fin (n + 1) → α) :
    finCons (f 0) (fun i : Fin n => f i.succ) = f := by
  funext i
  unfold finCons
  by_cases h : i.val = 0
  · rw [dite_eq_left h]
    exact congrArg f (Fin.ext h.symm)
  · rw [dite_eq_right h]
    exact congrArg f (Fin.ext (by simp; omega))

/-- All functions `Fin n → α` whose values lie in `xs`. -/
def allFuns {α : Type} (xs : List α) : (n : Nat) → List (Fin n → α)
  | 0 => [fun i => i.elim0]
  | n + 1 => xs.flatMap (fun a => (allFuns xs n).map (fun f => finCons a f))

theorem mem_allFuns {α : Type} (xs : List α) (hxs : ∀ a, a ∈ xs) :
    ∀ (n : Nat) (f : Fin n → α), f ∈ allFuns xs n := by
  intro n
  induction n with
  | zero =>
    intro f
    have : f = fun i => i.elim0 := funext fun i => i.elim0
    simp [allFuns, this]
  | succ n ih =>
    intro f
    simp only [allFuns, List.mem_flatMap, List.mem_map]
    exact ⟨f 0, hxs _, fun i => f i.succ, ih _, finCons_head_tail f⟩

theorem length_flatMap_const {α β : Type} (g : α → List β) (c : Nat) (hg : ∀ a, (g a).length = c) :
    ∀ xs : List α, (xs.flatMap g).length = xs.length * c
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, hg, length_flatMap_const g c hg xs, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem length_allFuns {α : Type} (xs : List α) :
    ∀ n, (allFuns xs n).length = xs.length ^ n := by
  intro n
  induction n with
  | zero => simp [allFuns]
  | succ n ih =>
    simp only [allFuns]
    rw [length_flatMap_const _ (xs.length ^ n) (fun a => by rw [List.length_map, ih]),
      Nat.pow_succ, Nat.mul_comm]

/-- All size-change graphs with `nf` functions and `k` parameter slots. -/
def allSCG (nf k : Nat) : List (SCG nf k) :=
  (List.finRange nf).flatMap fun s => (List.finRange nf).flatMap fun d =>
    (allFuns (allFuns allLabels k) k).map fun l => ⟨s, d, l⟩

theorem mem_allSCG {nf k : Nat} (G : SCG nf k) : G ∈ allSCG nf k := by
  simp only [allSCG, List.mem_flatMap, List.mem_map]
  exact ⟨G.src, List.mem_finRange _, G.dst, List.mem_finRange _, G.lab,
    mem_allFuns _ (mem_allFuns _ mem_allLabels k) k _, rfl⟩

/-- There are `nf * nf * 3 ^ (k * k)` size-change graphs. -/
theorem length_allSCG (nf k : Nat) : (allSCG nf k).length = nf * nf * 3 ^ (k * k) := by
  have hl : (allFuns (allFuns allLabels k) k).length = 3 ^ (k * k) := by
    rw [length_allFuns, length_allFuns, Nat.pow_mul]
    rfl
  unfold allSCG
  rw [length_flatMap_const _ (nf * 3 ^ (k * k)) (fun s => by
    rw [length_flatMap_const _ (3 ^ (k * k)) (fun d => by rw [List.length_map, hl]),
      List.length_finRange]), List.length_finRange, Nat.mul_assoc]

end Toy.SCT
