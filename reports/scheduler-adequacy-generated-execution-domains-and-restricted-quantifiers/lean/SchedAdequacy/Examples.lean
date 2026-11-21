import SchedAdequacy.Basic
import SchedAdequacy.Traces
import SchedAdequacy.Bounded

/-!
# Concrete alphabet, example programs, and definition examples

Every example in this file is fully proved (by evaluation or by a short
argument). They test that each definition admits its intended instances and
rejects instances it must reject.
-/

namespace Toy.SchedAdequacy

/-- A four-letter action alphabet. -/
inductive Act where
  | a | b | c | d
  deriving DecidableEq, Repr

open Act Prog

/-- A racy single-variable semantics: `a` sets `x := 1`, `b` sets `x := 2`,
`c` sets `x := 3 * x`, `d` sets `x := x + 1`. -/
def Act.eff : Act → Nat → Nat
  | .a => fun _ => 1
  | .b => fun _ => 2
  | .c => fun x => 3 * x
  | .d => fun x => x + 1

/-- Final value of `x` (initially `0`) after a trace, under `Act.eff`. -/
def finalX (t : List Act) : Nat := finalState Act.eff 0 t

/-- A two-variable semantics in which `a` and `c` commute and `b` conflicts with
both: `a` increments the first component, `c` the second, and `b` swaps them. -/
def Act.effSwap : Act → Nat × Nat → Nat × Nat
  | .a => fun s => (s.1 + 1, s.2)
  | .b => fun s => (s.2, s.1)
  | .c => fun s => (s.1, s.2 + 1)
  | .d => fun s => s

/-- An integer counter: `a` increments, `b` decrements, `c` and `d` do nothing.
All effects commute, yet prefix states differ between orders. -/
def Act.effInc : Act → Int → Int
  | .a => fun x => x + 1
  | .b => fun x => x - 1
  | .c => fun x => x
  | .d => fun x => x

/-- A two-variable semantics in which only `b` and `c` conflict: `a` increments
the second component, `b` sets the first to `2`, `c` triples the first, and `d`
does nothing. -/
def Act.effPair : Act → Nat × Nat → Nat × Nat
  | .a => fun s => (s.1, s.2 + 1)
  | .b => fun s => (2, s.2)
  | .c => fun s => (3 * s.1, s.2)
  | .d => fun s => s

/-! ## Example programs -/

/-- `a ∥ b` -/
def parAB : Prog Act := par (act a) (act b)
/-- `a ; b` -/
def seqAB : Prog Act := seq (act a) (act b)
/-- `a ∥ (b ∥ c)` — a nested parallel composition. -/
def parA_parBC : Prog Act := par (act a) (par (act b) (act c))
/-- `a ∥ ((b ∥ c) ; d)` — a nested parallel composition with a sequential
component. -/
def parA_seqParBC_D : Prog Act := par (act a) (seq (par (act b) (act c)) (act d))
/-- `(a ; b) ∥ (c ; d)` — parallel composition of sequential threads, no nesting. -/
def parSeqAB_seqCD : Prog Act := par (seq (act a) (act b)) (seq (act c) (act d))
/-- `a ∥ (a ∥ a)` — nested, with repeated action labels. -/
def parA_parAA : Prog Act := par (act a) (par (act a) (act a))
/-- `(a ∥ c) ∥ b` — the actions of `a ∥ (b ∥ c)`, parenthesized and ordered
differently. -/
def parAC_B : Prog Act := par (par (act a) (act c)) (act b)
/-- `(a ∥ b) ∥ (c ∥ d)` — two nested parallel pairs. -/
def parAB_parCD : Prog Act := par (par (act a) (act b)) (par (act c) (act d))
/-- `a ∥ (b ∥ (c ∥ d))` — a right-nested chain of four parallel actions. -/
def spine4 : Prog Act := par (act a) (par (act b) (par (act c) (act d)))

/-! ## Independence relations on `Act` -/

/-- Every two distinct actions are independent. -/
def fullIndep : Act → Act → Prop := fun x y => x ≠ y

/-- Only `a` and `c` are independent; `b` conflicts with both `a` and `c`
(justified by `Act.effSwap`). -/
def indepOnlyAC : Act → Act → Prop := fun x y => (x = .a ∧ y = .c) ∨ (x = .c ∧ y = .a)

/-- All distinct pairs are independent except `b`–`c` (the two actions of the
inner parallel composition of `parA_parBC` conflict, nothing else does). -/
def indepExceptBC : Act → Act → Prop :=
  fun x y => x ≠ y ∧ ¬ (x = .b ∧ y = .c) ∧ ¬ (x = .c ∧ y = .b)

instance : DecidableRel fullIndep := fun x y => inferInstanceAs (Decidable (x ≠ y))
instance : DecidableRel indepOnlyAC := fun x y =>
  inferInstanceAs (Decidable ((x = .a ∧ y = .c) ∨ (x = .c ∧ y = .a)))
instance : DecidableRel indepExceptBC := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ ¬ (x = .b ∧ y = .c) ∧ ¬ (x = .c ∧ y = .b)))

/-! ## Definition examples -/

section Examples

/-- `shuffle` admits order-preserving merges. -/
theorem shuffle_pos : [a, c, b] ∈ shuffle [a, b] [c] := by decide
/-- `shuffle` rejects merges that reorder one list. -/
theorem shuffle_neg : [b, a, c] ∉ shuffle [a, b] [c] := by decide

/-- `Interleavings` of `a ∥ b` include `b` before `a`. -/
theorem interleavings_parAB_pos : [b, a] ∈ Interleavings parAB := by decide
/-- `Interleavings` of `a ; b` exclude `b` before `a`. -/
theorem interleavings_seqAB_neg : [b, a] ∉ Interleavings seqAB := by decide
/-- `Interleavings` exclude traces that drop an action. -/
theorem interleavings_parAB_neg_drop : [a] ∉ Interleavings parAB := by decide
/-- The six interleavings of `a ∥ (b ∥ c)`. -/
theorem interleavings_parA_parBC :
    Interleavings parA_parBC = [[a, b, c], [b, a, c], [b, c, a], [a, c, b], [c, a, b], [c, b, a]] := by
  decide

/-- The per-step generator can schedule the inner left action `b` first. -/
theorem runPerStep_pos : runPerStep [true, false] parA_parBC = [b, a, c] := by decide
/-- The per-step generator never violates sequencing. -/
theorem runPerStep_neg : ∀ o, runPerStep o seqAB ≠ [b, a] := by
  intro o; exact of_decide_eq_true rfl

/-- The shared-choice generator: bit `true` goes right twice, reaching `c`. -/
theorem runShared_pos : runShared [true] parA_parBC = [c, a, b] := by decide
/-- The shared-choice generator can never schedule `b` first in `a ∥ (b ∥ c)`. -/
theorem runShared_neg : ∀ o, (runShared o parA_parBC).head? ≠ some b := by
  intro o
  rcases o with _ | ⟨_ | _, _⟩ <;> exact of_decide_eq_true rfl

/-- The deterministic scheduler alternates its consumed oracle bits; on
`(a ; b) ∥ (c ; d)`, where every step crosses one `par` node, this alternates
between the two threads (under nested `par` it does not:
`runRoundRobin_nested_runs_left_first`). -/
theorem runRoundRobin_pos : runRoundRobin [] parSeqAB_seqCD = [a, c, b, d] := by decide
/-- The deterministic scheduler produces the same run whatever the oracle, so in
particular never the thread-by-thread order. -/
theorem runRoundRobin_neg : ∀ o, runRoundRobin o parSeqAB_seqCD ≠ [a, b, c, d] := by
  intro o; exact of_decide_eq_true rfl

/-- The sequencing-ignoring generator produces a forbidden order (its purpose as
a countermodel). -/
theorem runIgnoringSeq_pos : runIgnoringSeq [true] seqAB = [b, a] := by decide
/-- … but it never drops actions. -/
theorem runIgnoringSeq_neg : ∀ o, runIgnoringSeq o seqAB ≠ [a] := by
  intro o
  rcases o with _ | ⟨_ | _, _⟩ <;> exact of_decide_eq_true rfl

/-- `NoNestedPar` admits parallel sequential threads and sequenced parallels. -/
theorem noNestedPar_pos : NoNestedPar parSeqAB_seqCD ∧ NoNestedPar (seq parAB parAB) := by decide
/-- `NoNestedPar` rejects a `par` inside a `par`, also under a `seq`. -/
theorem noNestedPar_neg : ¬ NoNestedPar parA_parBC ∧ ¬ NoNestedPar parA_seqParBC_D := by decide

/-- `schedPoints` values. -/
theorem schedPoints_examples :
    schedPoints parAB = 1 ∧ schedPoints seqAB = 0 ∧ schedPoints parA_parBC = 3 ∧
    schedPoints parA_seqParBC_D = 4 ∧ schedPoints parSeqAB_seqCD = 3 := by decide

/-- `oraclesUpTo` contains short oracles … -/
theorem oraclesUpTo_pos : [true, false] ∈ oraclesUpTo 2 ∧ (oraclesUpTo 2).length = 7 := by decide
/-- … and no longer ones. -/
theorem oraclesUpTo_neg : [true, false, true] ∉ oraclesUpTo 2 := by decide

/-- `Complete`: the per-step generator is complete on `a ∥ (b ∥ c)`. -/
theorem complete_pos : Complete runPerStep parA_parBC :=
  complete_of_checkComplete (n := 3) (by decide)

/-- `Complete`: the shared-choice generator is not complete on `a ∥ (b ∥ c)`. -/
theorem complete_neg : ¬ Complete runShared parA_parBC := by
  intro h
  obtain ⟨o, ho⟩ := h [b, a, c] (by decide)
  exact runShared_neg o (by rw [ho]; rfl)

/-- `Sound`: the shared-choice generator is sound on `a ∥ (b ∥ c)`. -/
theorem sound_pos : Sound runShared parA_parBC := by
  intro o
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> exact of_decide_eq_true rfl

/-- `Sound`: the sequencing-ignoring generator is unsound on `a ; b`. -/
theorem sound_neg : ¬ Sound runIgnoringSeq seqAB :=
  not_sound_of_checkSound (n := 1) (by decide)

/-- `Symmetric`/`Irreflexive`: all three example relations are independence
relations. -/
theorem independence_pos :
    (Symmetric fullIndep ∧ Irreflexive fullIndep) ∧
    (Symmetric indepOnlyAC ∧ Irreflexive indepOnlyAC) ∧
    (Symmetric indepExceptBC ∧ Irreflexive indepExceptBC) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    first
    | (intro x y; cases x <;> cases y <;> simp [fullIndep, indepOnlyAC, indepExceptBC])
    | (intro x; cases x <;> simp [fullIndep, indepOnlyAC, indepExceptBC])

/-- `Symmetric`/`Irreflexive` reject the total relation and a one-way relation. -/
theorem independence_neg :
    ¬ Irreflexive (fun (_ _ : Act) => True) ∧ ¬ Symmetric (fun x y : Act => x = .a ∧ y = .b) := by
  refine ⟨fun h => h .a trivial, fun h => ?_⟩
  have := h .a .b ⟨rfl, rfl⟩
  exact Act.noConfusion this.1

/-- `TraceEquiv`: under full independence, `b a c` and `a b c` are equivalent. -/
theorem traceEquiv_pos : TraceEquiv fullIndep [b, a, c] [a, b, c] :=
  TraceEquiv.swap1 [] [c] b a (by decide)

/-- `b` has no `indepOnlyAC`-partner. -/
theorem indepOnlyAC_b_isolated : ∀ x, ¬ indepOnlyAC .b x ∧ ¬ indepOnlyAC x .b := by
  intro x; cases x <;> simp [indepOnlyAC]

/-- `TraceEquiv`: under `indepOnlyAC`, `b a c` and `a b c` are not equivalent;
and no trace is equivalent to one of a different length. -/
theorem traceEquiv_neg :
    ¬ TraceEquiv indepOnlyAC [b, a, c] [a, b, c] ∧ ¬ TraceEquiv fullIndep [a] [] := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := (head_eq_iff_of_traceEquiv_of_isolated indepOnlyAC_b_isolated h).mp rfl
    exact Act.noConfusion (Option.some.inj this)
  · exact Nat.noConfusion h.length_eq

/-- `TraceInvariant`: occurrence counts are invariant under every trace
equivalence. -/
theorem traceInvariant_count {α : Type} [DecidableEq α] (I : α → α → Prop) (x : α) (k : Nat) :
    TraceInvariant I (fun t => t.count x = k) :=
  fun s _t h (hs : s.count x = k) => (h.perm.count_eq x).symm.trans hs

/-- `TraceInvariant`: the final state is invariant when independent actions
commute (here: `Act.effSwap` and `indepOnlyAC`). -/
theorem commuting_effSwap : Commuting Act.effSwap indepOnlyAC := by
  intro x y h s
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- `Commuting`: `Act.effPair` justifies `indepExceptBC`. -/
theorem commuting_effPair : Commuting Act.effPair indepExceptBC := by
  intro x y h s
  cases x <;> cases y <;> simp [indepExceptBC, Act.effPair] at h ⊢

/-- `Commuting` rejects the racy semantics with full independence. -/
theorem commuting_neg : ¬ Commuting Act.eff fullIndep := by
  intro h
  have := h .a .b (by decide) 0
  exact absurd this (by decide)

/-- `TraceInvariant` positive example: final state of `Act.effSwap`. -/
theorem traceInvariant_finalState_effSwap (s₀ v : Nat × Nat) :
    TraceInvariant indepOnlyAC (fun t => finalState Act.effSwap s₀ t = v) :=
  fun s _t h (hs : finalState Act.effSwap s₀ s = v) =>
    (finalState_eq_of_traceEquiv commuting_effSwap s₀ h).symm.trans hs

/-- `TraceInvariant` negative example: "`b` is not first" is not invariant under
full independence. -/
theorem traceInvariant_neg : ¬ TraceInvariant fullIndep (fun t => t.head? ≠ some b) := by
  intro h
  exact h [a, b, c] [b, a, c] (TraceEquiv.swap1 [] [c] a b (by decide)) (by decide) rfl

/-- `MeetsEveryClass` positive example: under full independence the
shared-choice runs meet every class of `a ∥ (b ∥ c)`. -/
theorem meetsEveryClass_pos : MeetsEveryClass fullIndep runShared parA_parBC := by
  intro t ht
  refine ⟨[], ?_⟩
  rw [interleavings_parA_parBC] at ht
  show TraceEquiv fullIndep [a, b, c] t
  apply traceEquiv_of_perm (fun _ _ h => h)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `MeetsEveryClass` negative example: under `indepOnlyAC` the class of
`b a c` contains no shared-choice run. -/
theorem meetsEveryClass_neg : ¬ MeetsEveryClass indepOnlyAC runShared parA_parBC := by
  intro h
  obtain ⟨o, ho⟩ := h [b, a, c] (by decide)
  have := (head_eq_iff_of_traceEquiv_of_isolated indepOnlyAC_b_isolated ho).mpr rfl
  exact runShared_neg o this

/-- `OracleBounded` positive examples: the deterministic scheduler is
`0`-bounded; the shared-choice generator on `a ∥ (b ∥ c)` is `2`-bounded. -/
theorem oracleBounded_pos :
    OracleBounded runRoundRobin parAB 0 ∧ OracleBounded runShared parA_parBC 2 := by
  refine ⟨fun _ => rfl, ?_⟩
  intro o
  rcases o with _ | ⟨_ | _, _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩⟩ <;> rfl

/-- `OracleBounded` negative example: the per-step generator on `a ∥ b` reads
one bit, so it is not `0`-bounded. -/
theorem oracleBounded_neg : ¬ OracleBounded runPerStep parAB 0 := by
  intro h
  have := h [true]
  exact absurd this (by decide)

end Examples

end Toy.SchedAdequacy
