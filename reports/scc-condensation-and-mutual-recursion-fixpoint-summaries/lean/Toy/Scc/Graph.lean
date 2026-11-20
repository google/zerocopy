/-
Toy.Scc.Graph
=============

Finite call graphs on `Fin n`, reachability (inductive and fuel-bounded),
SCC decompositions `comp : Fin n → Fin k`, the condensation, processing orders
of blocks, and the decidable SCC checker.

Everything in this file is a definition, a fully proved helper lemma, or a fully
proved example; the main results of the package are stated in `Toy.Scc.Decomp`,
`Toy.Scc.Fixpoint`, `Toy.Scc.Transfer` and `Toy.Scc.Termination`.
-/

namespace Toy.Scc

/-! ## Counting helpers (fully proved) -/

/-- If `p` implies `q` on `l` and some element of `l` satisfies `q` but not `p`, then
`q` holds strictly more often on `l` than `p`. -/
theorem countP_lt_countP_of_imp_of_exists {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      (∃ x ∈ l, q x = true ∧ p x = false) → l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx (List.not_mem_nil)
  | a :: l, himp, ⟨x, hx, hqx, hpx⟩ => by
      have himp' : ∀ y ∈ l, p y = true → q y = true :=
        fun y hy => himp y (List.mem_cons_of_mem a hy)
      have hmono : l.countP p ≤ l.countP q := List.countP_mono_left himp'
      simp only [List.countP_cons]
      rcases List.mem_cons.mp hx with rfl | hxl
      · simp only [hqx, hpx]
        simp
        omega
      · have ih := countP_lt_countP_of_imp_of_exists himp' ⟨x, hxl, hqx, hpx⟩
        have ha := himp a (List.mem_cons_self)
        cases hpa : p a <;> cases hqa : q a <;> simp_all <;> omega

/-! ## Call graphs and reachability -/

/-- A finite call graph on the functions `Fin n`: `E f g = true` iff `f` contains
a call to `g`.  This models the (static) call graph of a whole program. -/
abbrev Graph (n : Nat) := Fin n → Fin n → Bool

/-- Reflexive-transitive reachability in the call graph: `Reach E f g` iff there is
a call chain (of length `≥ 0`) from `f` to `g`. -/
inductive Reach {n : Nat} (E : Graph n) : Fin n → Fin n → Prop
  | refl (f : Fin n) : Reach E f f
  | step {f g h : Fin n} : E f g = true → Reach E g h → Reach E f h

theorem Reach.trans {n : Nat} {E : Graph n} {f g h : Fin n}
    (h₁ : Reach E f g) (h₂ : Reach E g h) : Reach E f h := by
  induction h₁ with
  | refl => exact h₂
  | step e _ ih => exact Reach.step e (ih h₂)

theorem Reach.single {n : Nat} {E : Graph n} {f g : Fin n} (e : E f g = true) : Reach E f g :=
  Reach.step e (Reach.refl g)

/-- A set of functions (as a Boolean predicate) closed under calls. -/
def ClosedUnder {n : Nat} (E : Graph n) (S : Fin n → Bool) : Prop :=
  ∀ x y, S x = true → E x y = true → S y = true

instance {n : Nat} (E : Graph n) (S : Fin n → Bool) : Decidable (ClosedUnder E S) :=
  inferInstanceAs (Decidable (∀ x y, S x = true → E x y = true → S y = true))

/-- Closed sets are closed under reachability (fully proved helper). -/
theorem Reach.mem_of_closed {n : Nat} {E : Graph n} {S : Fin n → Bool}
    (hS : ClosedUnder E S) {f g : Fin n} (hr : Reach E f g) (hf : S f = true) : S g = true := by
  induction hr with
  | refl => exact hf
  | step e _ ih => exact ih (hS _ _ hf e)

/-- One step of forward expansion of a set of reached functions. -/
def reachStep {n : Nat} (E : Graph n) (S : Fin n → Bool) : Fin n → Bool :=
  fun g => S g || (List.finRange n).any fun h => S h && E h g

/-- `reachFrom E f fuel` is the set of functions reachable from `f` by call chains
of length at most `fuel` (fuel-bounded closure). -/
def reachFrom {n : Nat} (E : Graph n) (f : Fin n) : Nat → Fin n → Bool
  | 0 => fun g => decide (g = f)
  | k + 1 => reachStep E (reachFrom E f k)

/-- Decidable reachability: the fuel-bounded closure with fuel `n`. -/
def reachB {n : Nat} (E : Graph n) (f g : Fin n) : Bool := reachFrom E f n g

theorem reachFrom_self {n : Nat} (E : Graph n) (f : Fin n) :
    ∀ k, reachFrom E f k f = true
  | 0 => by simp [reachFrom]
  | k + 1 => by simp [reachFrom, reachStep, reachFrom_self E f k]

/-- Soundness of the fuel-bounded closure (fully proved). -/
theorem reach_of_reachFrom {n : Nat} (E : Graph n) (f : Fin n) :
    ∀ k g, reachFrom E f k g = true → Reach E f g
  | 0, g, h => by
      have : g = f := by simpa [reachFrom] using h
      subst this; exact Reach.refl _
  | k + 1, g, h => by
      simp only [reachFrom, reachStep, Bool.or_eq_true, List.any_eq_true,
        Bool.and_eq_true] at h
      rcases h with h | ⟨x, _, hx, e⟩
      · exact reach_of_reachFrom E f k g h
      · exact (reach_of_reachFrom E f k x hx).trans (Reach.single e)

theorem reach_of_reachB {n : Nat} {E : Graph n} {f g : Fin n} (h : reachB E f g = true) :
    Reach E f g := reach_of_reachFrom E f n g h

/-- Certified completeness on a given instance: if the computed closure happens to be
closed under calls, it contains everything reachable (fully proved). -/
theorem reachB_of_reach_of_closed {n : Nat} {E : Graph n} {f g : Fin n}
    (hc : ClosedUnder E (reachFrom E f n)) (hr : Reach E f g) : reachB E f g = true :=
  Reach.mem_of_closed hc hr (reachFrom_self E f n)

/-- The fuel-bounded closure grows with the fuel (fully proved helper). -/
theorem reachFrom_mono_succ {n : Nat} (E : Graph n) (f : Fin n) (k : Nat) (g : Fin n)
    (h : reachFrom E f k g = true) : reachFrom E f (k + 1) g = true := by
  simp [reachFrom, reachStep, h]

theorem reachFrom_mono {n : Nat} (E : Graph n) (f : Fin n) {k k' : Nat} (hk : k ≤ k')
    (g : Fin n) (h : reachFrom E f k g = true) : reachFrom E f k' g = true := by
  induction hk with
  | refl => exact h
  | step _ ih => exact reachFrom_mono_succ E f _ g ih

/-! ## SCC decompositions -/

/-- `comp : Fin n → Fin k` is a (valid) SCC decomposition of `E`: two functions lie in
the same block exactly when they are mutually reachable.  This is the textbook
definition of the partition into strongly connected components, with blocks named
by `Fin k` (block names need not all be used). -/
def IsSccDecomp {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ f g, comp f = comp g ↔ (Reach E f g ∧ Reach E g f)

/-- Every block is mutually reachable inside the whole graph ("no over-merging").
Reachability is taken in all of `E`, not in the subgraph induced by the block. -/
def BlocksMutuallyReachable {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ f g, comp f = comp g → Reach E f g ∧ Reach E g f

/-- An edge of the condensation: some call crosses from block `c` to a different
block `d`. -/
def CondEdge {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) (c d : Fin k) : Prop :=
  c ≠ d ∧ ∃ f g, comp f = c ∧ comp g = d ∧ E f g = true

/-- The condensation (the quotient graph on blocks, keeping only edges between
distinct blocks) has no cycle. -/
def CondensationAcyclic {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Prop :=
  ∀ c, ¬ Relation.TransGen (CondEdge E comp) c c

/-- The decidable SCC checker: compares block equality with mutual reachability as
computed by the fuel-bounded closure, for all pairs. -/
def checkScc {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Bool :=
  (List.finRange n).all fun f => (List.finRange n).all fun g =>
    decide (comp f = comp g) == (reachB E f g && reachB E g f)

/-- A strengthened checker that additionally certifies that every computed closure is
closed under calls.  Used only to prove concrete examples without relying on the
completeness of `reachB`. -/
def checkSccCert {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) : Bool :=
  checkScc E comp && (List.finRange n).all fun f =>
    (List.finRange n).all fun x => (List.finRange n).all fun y =>
      !(reachFrom E f n x && E x y) || reachFrom E f n y

theorem closed_of_checkSccCert {n k : Nat} {E : Graph n} {comp : Fin n → Fin k}
    (h : checkSccCert E comp = true) (f : Fin n) : ClosedUnder E (reachFrom E f n) := by
  intro x y hx e
  simp only [checkSccCert, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  have := h.2 f x y
  simp [hx, e] at this
  exact this

/-- Fully proved soundness of the certified checker. -/
theorem isSccDecomp_of_checkSccCert {n k : Nat} {E : Graph n} {comp : Fin n → Fin k}
    (h : checkSccCert E comp = true) : IsSccDecomp E comp := by
  have hc : checkScc E comp = true := by
    simp only [checkSccCert, Bool.and_eq_true] at h; exact h.1
  intro f g
  simp only [checkScc, List.all_eq_true, List.mem_finRange, true_implies] at hc
  have hfg := hc f g
  constructor
  · intro heq
    have hb : (reachB E f g && reachB E g f) = true := by
      revert hfg
      cases reachB E f g <;> cases reachB E g f <;> simp [heq]
    simp only [Bool.and_eq_true] at hb
    exact ⟨reach_of_reachB hb.1, reach_of_reachB hb.2⟩
  · rintro ⟨r1, r2⟩
    have h1 := reachB_of_reach_of_closed (closed_of_checkSccCert h f) r1
    have h2 := reachB_of_reach_of_closed (closed_of_checkSccCert h g) r2
    simp only [h1, h2, Bool.and_self, beq_true, decide_eq_true_eq] at hfg
    exact hfg

/-! ## Processing orders of blocks -/

/-- Position of a block in a processing order: the index of its first occurrence
(`List.idxOf`), and `order.length` if the block does not occur.  The definition of
`CalleesFirst` below requires the blocks it compares to occur, so this out-of-range
value never decides a comparison there. -/
def pos {k : Nat} (order : List (Fin k)) (c : Fin k) : Nat := order.idxOf c

theorem pos_lt_length_of_mem {k : Nat} {order : List (Fin k)} {c : Fin k} (h : c ∈ order) :
    pos order c < order.length :=
  List.idxOf_lt_length_of_mem h

/-- On blocks that occur in the order, `pos` is injective (fully proved). -/
theorem eq_of_pos_eq_of_mem {k : Nat} {order : List (Fin k)} {c d : Fin k} (hc : c ∈ order)
    (hd : d ∈ order) (h : pos order c = pos order d) : c = d := by
  have hc' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hc)
  have hd' := List.getElem_idxOf (List.idxOf_lt_length_of_mem hd)
  have key : ∀ (i j : Nat) (hi : i < order.length) (hj : j < order.length), i = j →
      order[i] = order[j] := by
    intro i j _ _ hij; subst hij; rfl
  rw [← hc', ← hd']
  exact key _ _ _ _ h

/-- The order mentions the block of every function. -/
def Covers {n k : Nat} (comp : Fin n → Fin k) (order : List (Fin k)) : Prop :=
  ∀ f, comp f ∈ order

instance {n k : Nat} (comp : Fin n → Fin k) (order : List (Fin k)) :
    Decidable (Covers comp order) :=
  inferInstanceAs (Decidable (∀ f, comp f ∈ order))

/-- For a covering order, `pos` is injective on the blocks that are used by `comp`
(fully proved).  So the position in a covering order is a block rank that is
injective on used blocks, as required by card `lex-iff`. -/
theorem pos_injective_on_used_blocks_of_covers {n k : Nat} {comp : Fin n → Fin k}
    {order : List (Fin k)} (h : Covers comp order) :
    ∀ f g, pos order (comp f) = pos order (comp g) → comp f = comp g :=
  fun f g hfg => eq_of_pos_eq_of_mem (h f) (h g) hfg

/-- Callees first (a reverse topological order of the condensation): for every call
that crosses blocks, both endpoint blocks occur in `order`, and the callee's block
first occurs strictly earlier than the caller's block.  Blocks that take part in no
cross-block call are not constrained; `Covers` separately requires every function's
block to occur. -/
def CalleesFirst {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) (order : List (Fin k)) :
    Prop :=
  ∀ f g, E f g = true → comp f ≠ comp g →
    comp f ∈ order ∧ comp g ∈ order ∧ pos order (comp g) < pos order (comp f)

instance {n k : Nat} (E : Graph n) (comp : Fin n → Fin k) (order : List (Fin k)) :
    Decidable (CalleesFirst E comp order) :=
  inferInstanceAs (Decidable (∀ f g, E f g = true → comp f ≠ comp g →
    comp f ∈ order ∧ comp g ∈ order ∧ pos order (comp g) < pos order (comp f)))

/-- Any callees-first order (covering or not) certifies an acyclic condensation
(fully proved; this is the easy direction of the topological-order characterization). -/
theorem condensationAcyclic_of_calleesFirst {n k : Nat} {E : Graph n} {comp : Fin n → Fin k}
    {order : List (Fin k)} (h : CalleesFirst E comp order) : CondensationAcyclic E comp := by
  have key : ∀ c d, Relation.TransGen (CondEdge E comp) c d → pos order d < pos order c := by
    intro c d hcd
    induction hcd with
    | single e =>
        obtain ⟨hne, f, g, hf, hg, e⟩ := e
        subst hf; subst hg
        exact (h f g e hne).2.2
    | tail _ e ih =>
        obtain ⟨hne, f, g, hf, hg, e⟩ := e
        subst hf; subst hg
        exact Nat.lt_trans (h f g e hne).2.2 ih
  intro c hc
  exact Nat.lt_irrefl _ (key c c hc)

/-! ## Fixture graphs and examples -/

/-- `0 → 1`. -/
def gPath : Graph 2 := fun f g => decide (f.val = 0 ∧ g.val = 1)
/-- `0 → 1 → 0`. -/
def gCycle : Graph 2 := fun f g => decide (f ≠ g)
/-- No calls. -/
def gEmpty : Graph 2 := fun _ _ => false
/-- One self-recursive function. -/
def gLoop : Graph 1 := fun _ _ => true
/-- `0 → 1 → 2`. -/
def gPath3 : Graph 3 := fun f g => decide (g.val = f.val + 1)
/-- `0 → 0`, `0 → 1`, `1 → 1`. -/
def gMix : Graph 2 := fun f g => decide (f.val ≤ g.val)
/-- `0 → 1`, `1 → 1` (a caller and a self-recursive callee). -/
def gPathLoop1 : Graph 2 := fun _ g => decide (g.val = 1)

/-- Identity decomposition (every function its own block). -/
def idComp {n : Nat} : Fin n → Fin n := fun f => f
/-- Everything in one block. -/
def oneComp {n : Nat} : Fin n → Fin 1 := fun _ => 0
/-- Merges the endpoints of `0 → 1 → 2` into block `0`; `1` is block `1`. -/
def mergeComp3 : Fin 3 → Fin 2 := fun f => if f.val = 1 then 1 else 0
/-- Merges the first two functions of `0 → 1 → 2` into block `0`; `2` is block `1`
(a merge along the path that keeps the condensation acyclic). -/
def convexMerge3 : Fin 3 → Fin 2 := fun f => if f.val = 2 then 1 else 0

-- `Reach`: positive and negative examples.
example : Reach gPath 0 1 := Reach.single (by decide)
example : ¬ Reach gPath 1 0 := fun h =>
  absurd (Reach.mem_of_closed (S := fun x => decide (x = 1)) (by decide) h (by decide))
    (by decide)

theorem reach_gPath3_0_2 : Reach gPath3 0 2 :=
  (Reach.single (E := gPath3) (f := 0) (g := 1) (by decide)).trans (Reach.single (by decide))

theorem not_reach_gPath3_2_0 : ¬ Reach gPath3 2 0 := fun h =>
  absurd (Reach.mem_of_closed (S := fun x => decide (x = 2)) (by decide) h (by decide))
    (by decide)

-- `reachB`: positive and negative examples.
example : reachB gPath3 0 2 = true := by decide
example : reachB gPath3 2 0 = false := by decide

-- `IsSccDecomp`: positive examples (certified, fully proved).
theorem isSccDecomp_gPath_id : IsSccDecomp gPath idComp :=
  isSccDecomp_of_checkSccCert (by decide)
theorem isSccDecomp_gCycle_one : IsSccDecomp gCycle oneComp :=
  isSccDecomp_of_checkSccCert (by decide)
theorem isSccDecomp_gMix_id : IsSccDecomp gMix idComp :=
  isSccDecomp_of_checkSccCert (by decide)
theorem isSccDecomp_gPath3_id : IsSccDecomp gPath3 idComp :=
  isSccDecomp_of_checkSccCert (by decide)
theorem isSccDecomp_gPathLoop1_id : IsSccDecomp gPathLoop1 idComp :=
  isSccDecomp_of_checkSccCert (by decide)

theorem reach_gCycle (f g : Fin 2) : Reach gCycle f g := by
  by_cases h : f = g
  · subst h; exact Reach.refl _
  · exact Reach.single (by simp [gCycle, h])

-- `IsSccDecomp`: negative examples.
/-- Splitting the 2-cycle is not an SCC decomposition. -/
theorem not_isSccDecomp_gCycle_id : ¬ IsSccDecomp gCycle idComp := fun h =>
  absurd ((h 0 1).2 ⟨reach_gCycle 0 1, reach_gCycle 1 0⟩) (by decide)

/-- Merging `0 → 1` into one block is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath_one : ¬ IsSccDecomp gPath oneComp := fun h =>
  absurd ((h 0 1).1 rfl).2 (fun r =>
    absurd (Reach.mem_of_closed (S := fun x => decide (x = 1)) (by decide) r (by decide))
      (by decide))

/-- Merging the endpoints of `0 → 1 → 2` is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath3_merge : ¬ IsSccDecomp gPath3 mergeComp3 := fun h =>
  not_reach_gPath3_2_0 ((h 0 2).1 (by decide)).2

/-- Merging `0` and `1` of `0 → 1 → 2` is not an SCC decomposition. -/
theorem not_isSccDecomp_gPath3_convexMerge : ¬ IsSccDecomp gPath3 convexMerge3 := by
  intro h
  have r10 : Reach gPath3 1 0 := ((h 0 1).1 rfl).2
  exact absurd (Reach.mem_of_closed (S := fun x : Fin 3 => decide (1 ≤ x.val)) (by decide) r10
    (by decide)) (by decide)

-- `BlocksMutuallyReachable`: positive and negative examples.
example : BlocksMutuallyReachable gCycle idComp := by
  intro f g h; subst h; exact ⟨Reach.refl _, Reach.refl _⟩
example : ¬ BlocksMutuallyReachable gPath oneComp := fun h =>
  not_isSccDecomp_gPath_one (fun f g => ⟨h f g, fun _ => rfl⟩)

-- `CondensationAcyclic`: positive and negative examples.
example : CondensationAcyclic gPath idComp :=
  condensationAcyclic_of_calleesFirst (order := [1, 0]) (by decide)

theorem not_condensationAcyclic_gCycle_id : ¬ CondensationAcyclic gCycle idComp := by
  intro h
  have e01 : CondEdge gCycle idComp 0 1 := ⟨by decide, 0, 1, rfl, rfl, by decide⟩
  have e10 : CondEdge gCycle idComp 1 0 := ⟨by decide, 1, 0, rfl, rfl, by decide⟩
  exact h 0 (Relation.TransGen.tail (Relation.TransGen.single e01) e10)

-- `checkScc`: accepts and rejects.
example : checkScc gPath idComp = true := by decide
example : checkScc gCycle idComp = false := by decide
example : checkScc gPath oneComp = false := by decide

-- `Covers` and `CalleesFirst`: positive and negative examples.
example : Covers (idComp (n := 2)) [1, 0] := by decide
example : ¬ Covers (idComp (n := 2)) [1] := by decide
example : CalleesFirst gPath idComp [1, 0] := by decide
example : ¬ CalleesFirst gPath idComp [0, 1] := by decide
/-- Non-covering negative examples: a list that omits the caller block, or the callee
block, of a cross-block call is not callees-first. -/
theorem not_calleesFirst_gPath_omitted_caller : ¬ CalleesFirst gPath idComp [1] := by decide
theorem not_calleesFirst_gPath_omitted_callee : ¬ CalleesFirst gPath idComp [0] := by decide
/-- Non-covering positive example: a block with no cross-block calls need not be listed
for `CalleesFirst` (but `Covers` fails). -/
example : CalleesFirst gLoop oneComp [] ∧ ¬ Covers (oneComp (n := 1)) [] := by decide
/-- A duplicate entry is allowed: positions are first occurrences. -/
example : CalleesFirst gPath idComp [1, 0, 1] := by decide

/-- No order whatsoever is callees-first for the split 2-cycle. -/
theorem not_calleesFirst_gCycle_id (order : List (Fin 2)) :
    ¬ CalleesFirst gCycle idComp order := by
  intro h
  have h1 := (h 0 1 (by decide) (by decide)).2.2
  have h2 := (h 1 0 (by decide) (by decide)).2.2
  simp only [idComp] at h1 h2
  omega

/-- No order whatsoever is callees-first for the non-convex merge of `0 → 1 → 2`. -/
theorem not_calleesFirst_gPath3_merge (order : List (Fin 2)) :
    ¬ CalleesFirst gPath3 mergeComp3 order := by
  intro h
  have h1 := (h 0 1 (by decide) (by decide)).2.2
  have h2 := (h 1 2 (by decide) (by decide)).2.2
  simp only [mergeComp3] at h1 h2
  simp at h1 h2
  omega

end Toy.Scc
