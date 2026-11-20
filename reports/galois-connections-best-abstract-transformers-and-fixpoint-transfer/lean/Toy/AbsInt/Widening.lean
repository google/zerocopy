/-
Toy.AbsInt.Widening
===================

Widening operators and iteration with widening (cards `R5-widen`,
`R5-widen-diverge`, `R5-widen-bridge`): with the
standard upper-bound and termination axioms, widened iteration reaches an
abstract post-fixpoint in finitely many steps even on domains of infinite height,
where plain Kleene iteration can diverge.  Includes definition examples,
tightness counterexamples, non-vacuity witnesses and boundary examples.
-/
import Toy.AbsInt.Fixpoint

namespace Toy.AbsInt

/-! ## Definitions -/

section Defs
variable {A : Type} [LE A]

/-- First upper-bound axiom of a widening: `a ≤ a ∇ b`. -/
def WidenUpperLeft (w : A → A → A) : Prop := ∀ a b, a ≤ w a b

/-- Second upper-bound axiom of a widening: `b ≤ a ∇ b`. -/
def WidenUpperRight (w : A → A → A) : Prop := ∀ a b, b ≤ w a b

/-- An ascending sequence: `b n ≤ b (n + 1)` for all `n`. -/
def Ascending (b : Nat → A) : Prop := ∀ n, b n ≤ b (n + 1)

/-- The widened chain of an input sequence: `c 0 = b 0`, `c (n+1) = c n ∇ b (n+1)`. -/
def widenChain (w : A → A → A) (b : Nat → A) : Nat → A
  | 0 => b 0
  | n + 1 => w (widenChain w b n) (b (n + 1))

/-- Termination axiom of a widening, in the form of Cousot & Cousot (1992),
condition (8): for every ascending input `b`, the widened chain is not strictly
increasing at every step, i.e. some `n` has `¬ widenChain w b n < widenChain w b (n+1)`.
Implied by the textbook "eventually stabilizes" condition
(`widenTerminates_of_widenStabilizes`).

It guarantees one non-strict step, which is exactly what a loop that stops at
the first post-fixpoint needs.  On a preorder that is not antisymmetric it does
not guarantee finitely many strict steps, nor stabilization up to `≤`, for
arbitrary ascending inputs (`pbWiden_terminates_infinitely_many_strict`). -/
def WidenTerminates (w : A → A → A) : Prop :=
  ∀ b : Nat → A, Ascending b → ¬ ∀ n, StrictLt (widenChain w b n) (widenChain w b (n + 1))

/-- The textbook termination axiom: the widened chain of every ascending input
eventually becomes constant, with constancy meaning Lean equality `=`.  On a
preorder that is not antisymmetric, a widening whose chains stabilize only up to
`a ≤ b ∧ b ≤ a` fails this condition although it satisfies `WidenTerminates`
(`widenTerminates_not_widenStabilizes_preorder`). -/
def WidenStabilizes (w : A → A → A) : Prop :=
  ∀ b : Nat → A, Ascending b → ∃ N, ∀ m, N ≤ m → widenChain w b m = widenChain w b N

end Defs

/-- Iteration with widening: `x 0 = a₀`, `x (n+1) = x n ∇ fs (x n)`.  It widens at
every step and never stops by itself; an analyzer stops at the first `n` with
`fs (x n) ≤ x n`.  Being a post-fixpoint is not preserved by later steps
(`widenIter_postFixpoint_not_persistent`). -/
def widenIter {A : Type} (w : A → A → A) (fs : A → A) (a₀ : A) : Nat → A
  | 0 => a₀
  | n + 1 => w (widenIter w fs a₀ n) (fs (widenIter w fs a₀ n))

/-! ## Main results -/

/-- **Termination of iteration with widening** (card `R5-widen`).  If the
abstract order is transitive, `∇` satisfies both upper-bound axioms and the
termination axiom, `fs` is monotone, and `a₀ ≤ fs a₀`, then some widened iterate
`widenIter ∇ fs a₀ n` is a post-fixpoint of `fs`.  No chain condition on the
domain is assumed.  Equivalently, the loop that widens until the first
post-fixpoint terminates. -/
theorem exists_widenIter_postFixpoint_of_trans_of_upperLeft_of_upperRight_of_terminates_of_monotone_of_le_apply
    {A : Type} [LE A] (htrans : IsTrans A) {w : A → A → A}
    (hL : WidenUpperLeft w) (hR : WidenUpperRight w) (hT : WidenTerminates w)
    {fs : A → A} (hmono : Monotone fs) (a₀ : A) (hstart : a₀ ≤ fs a₀) :
    ∃ n, PostFixpoint fs (widenIter w fs a₀ n) := by
  let x := widenIter w fs a₀
  let b : Nat → A := fun | 0 => a₀ | n + 1 => fs (x n)
  have hchain : ∀ n, widenChain w b n = x n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => show w (widenChain w b n) (fs (x n)) = w (x n) (fs (x n)); rw [ih]
  have hb : Ascending b := by
    intro n; cases n with
    | zero => exact hstart
    | succ n => exact hmono _ _ (hL (x n) (fs (x n)))
  exact Classical.byContradiction fun hne =>
    hT b hb fun n => by
      rw [hchain n, hchain (n + 1)]
      exact ⟨hL (x n) (fs (x n)), fun hback => hne ⟨n, htrans _ _ _ (hR (x n) (fs (x n))) hback⟩⟩

/-- **Textbook termination implies the termination axiom** (card
`R5-widen-bridge`, an auxiliary bridge).  The textbook termination axiom implies
the one used by `R5-widen`, with no order law assumed. -/
theorem widenTerminates_of_widenStabilizes {A : Type} [LE A] {w : A → A → A}
    (h : WidenStabilizes w) : WidenTerminates w := by
  intro b hb hall
  obtain ⟨N, hN⟩ := h b hb
  have hlt := hall N
  rw [hN (N + 1) (Nat.le_succ N)] at hlt
  exact StrictLt.irrefl _ hlt

/-! ## Helpers (proved) -/

/-- On a domain with the ascending chain condition every binary operator
satisfies the termination axiom (`widenTerminates_of_acc`). -/
theorem widenTerminates_of_acc {A : Type} [LE A] (hacc : ACC A) (w : A → A → A) :
    WidenTerminates w :=
  fun b _ hall => hacc ⟨widenChain w b, hall⟩

/-! ## The `UB` widening: jump to `top` on any increase -/

/-- Standard widening on `UB`: keep `a` if `b ≤ a`, otherwise jump to `top`. -/
def ubWiden (a b : UB) : UB := if b ≤ a then a else UB.top

theorem ubWiden_top (b : UB) : ubWiden UB.top b = UB.top := by
  unfold ubWiden; simp

theorem ubWiden_cases (a b : UB) : ubWiden a b = a ∨ ubWiden a b = UB.top := by
  unfold ubWiden
  by_cases h : b ≤ a
  · exact Or.inl (ite_of_pos h)
  · exact Or.inr (ite_of_neg h)

theorem ubWiden_upperLeft : WidenUpperLeft ubWiden := by
  intro a b
  unfold ubWiden
  by_cases h : b ≤ a
  · rw [ite_of_pos h]; exact UB.isRefl a
  · rw [ite_of_neg h]; exact UB.le_top a

theorem ubWiden_upperRight : WidenUpperRight ubWiden := by
  intro a b
  unfold ubWiden
  by_cases h : b ≤ a
  · rw [ite_of_pos h]; exact h
  · rw [ite_of_neg h]; exact UB.le_top b

theorem ubWiden_terminates : WidenTerminates ubWiden := by
  intro b _ hall
  have h0 := hall 0
  have h1 := hall 1
  change StrictLt (b 0) (ubWiden (b 0) (b 1)) at h0
  by_cases hb : b 1 ≤ b 0
  · unfold ubWiden at h0; rw [ite_of_pos hb] at h0; exact StrictLt.irrefl _ h0
  · have e : widenChain ubWiden b 1 = UB.top := by
      show ubWiden (b 0) (b 1) = UB.top
      unfold ubWiden; rw [ite_of_neg hb]
    change StrictLt (widenChain ubWiden b 1) (ubWiden (widenChain ubWiden b 1) (b 2)) at h1
    rw [e, ubWiden_top] at h1
    exact StrictLt.irrefl _ h1

theorem ubWiden_stabilizes : WidenStabilizes ubWiden := by
  intro b _
  by_cases hex : ∃ n, widenChain ubWiden b n = UB.top
  · obtain ⟨N, hN⟩ := hex
    have key : ∀ k, widenChain ubWiden b (N + k) = UB.top := by
      intro k
      induction k with
      | zero => exact hN
      | succ k ih =>
        show ubWiden (widenChain ubWiden b (N + k)) (b (N + k + 1)) = UB.top
        rw [ih, ubWiden_top]
    refine ⟨N, fun m hm => ?_⟩
    have : m = N + (m - N) := by omega
    rw [this, key, hN]
  · have hne : ∀ n, widenChain ubWiden b n ≠ UB.top := fun n h => hex ⟨n, h⟩
    have step : ∀ n, widenChain ubWiden b (n + 1) = widenChain ubWiden b n := by
      intro n
      have hn := hne (n + 1)
      change ubWiden (widenChain ubWiden b n) (b (n + 1)) ≠ UB.top at hn
      show ubWiden (widenChain ubWiden b n) (b (n + 1)) = widenChain ubWiden b n
      rcases ubWiden_cases (widenChain ubWiden b n) (b (n + 1)) with h | h
      · exact h
      · exact absurd h hn
    refine ⟨0, fun m _ => ?_⟩
    induction m with
    | zero => rfl
    | succ m ih => rw [step, ih (Nat.zero_le _)]

theorem widenIter_ub_one : widenIter ubWiden ubIncr UB.bot 1 = UB.top := by
  show ubWiden UB.bot (UB.atMost 0) = UB.top
  unfold ubWiden; simp

/-! ## Definition examples (proved) -/

theorem widenUpperLeft_example_pos : WidenUpperLeft ubWiden := ubWiden_upperLeft
theorem widenUpperLeft_example_neg : ¬ WidenUpperLeft (fun _ b : B2 => b) :=
  fun h => absurd (h B2.hi B2.lo) (by decide)
theorem widenUpperRight_example_pos : WidenUpperRight ubWiden := ubWiden_upperRight
theorem widenUpperRight_example_neg : ¬ WidenUpperRight (fun a _ : B2 => a) :=
  fun h => absurd (h B2.lo B2.hi) (by decide)

theorem ascending_example_pos : Ascending (fun n : Nat => n) := fun n => Nat.le_succ n
theorem ascending_example_neg : ¬ Ascending (fun n : Nat => 10 - n) :=
  fun h => absurd (h 0) (by decide)

theorem widenChain_example_pos : widenChain ubWiden (fun n => UB.atMost n) 1 = UB.top := by
  show ubWiden (UB.atMost 0) (UB.atMost 1) = UB.top
  unfold ubWiden; simp

theorem widenChain_example_neg : widenChain ubWiden (fun n => UB.atMost n) 1 ≠ UB.atMost 1 := by
  rw [widenChain_example_pos]; decide

theorem widenIter_example_pos : widenIter ubWiden ubIncr UB.bot 1 = UB.top := widenIter_ub_one

/-- Negative example: widened iteration differs from plain Kleene iteration
(which gives `atMost 0` at step 1). -/
theorem widenIter_example_neg :
    widenIter ubWiden ubIncr UB.bot 1 ≠ kleene ubIncr UB.bot 1 := by
  rw [widenIter_ub_one]; decide

theorem widenTerminates_example_pos : WidenTerminates ubWiden := ubWiden_terminates
theorem widenStabilizes_example_pos : WidenStabilizes ubWiden := ubWiden_stabilizes

theorem widenChain_max_id (n : Nat) : widenChain max (fun k : Nat => k) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => show max (widenChain max (fun k : Nat => k) n) (n + 1) = n + 1; rw [ih]; omega

/-- Negative example: `max` on `Nat` (the join) is not a widening — the widened
chain of `0, 1, 2, …` strictly increases forever. -/
theorem widenTerminates_example_neg : ¬ WidenTerminates (max : Nat → Nat → Nat) := by
  intro h
  apply h (fun k => k) (fun n => Nat.le_succ n)
  intro n
  rw [widenChain_max_id, widenChain_max_id]
  exact ⟨Nat.le_succ n, by omega⟩

theorem widenStabilizes_example_neg : ¬ WidenStabilizes (max : Nat → Nat → Nat) := by
  intro h
  obtain ⟨N, hN⟩ := h (fun k => k) (fun n => Nat.le_succ n)
  have := hN (N + 1) (Nat.le_succ N)
  rw [widenChain_max_id, widenChain_max_id] at this
  omega

/-! ## Non-vacuity witnesses (proved) -/

/-- Non-vacuity for `R5-widen`: all hypotheses hold for the `UB` domain with the
jump-to-`top` widening, the counter-loop transformer `ubIncr`, and `a₀ = bot`. -/
theorem widen_nonvacuous :
    IsTrans UB ∧ WidenUpperLeft ubWiden ∧ WidenUpperRight ubWiden ∧
      WidenTerminates ubWiden ∧ Monotone ubIncr ∧ UB.bot ≤ ubIncr UB.bot :=
  ⟨UB.isTrans, ubWiden_upperLeft, ubWiden_upperRight, ubWiden_terminates,
    ubIncr_monotone, UB.bot_le _⟩

theorem widenBridge_nonvacuous : WidenStabilizes ubWiden := ubWiden_stabilizes

/-! ## Plain iteration diverges where widening converges (proved) -/

/-- **Divergence without widening** (card `R5-widen-diverge`).  On the
infinite-height domain `UB`, for the counter loop (`counterStep`, monotone,
abstracted soundly and monotonically by `ubIncr`), with the jump-to-`top`
widening `ubWiden` satisfying every widening hypothesis of `R5-widen`: plain
Kleene iteration from `bot` never reaches a post-fixpoint, and no Kleene iterate
over-approximates the concrete least fixpoint; iteration with `ubWiden` reaches
the post-fixpoint `top` at step `1`, which does over-approximate it. -/
theorem kleene_diverges_widen_converges_ub :
    Monotone ubIncr ∧ IsBot UB.bot ∧ ¬ ACC UB ∧ Sound ubGamma counterStep ubIncr ∧
      Monotone counterStep ∧ IsTrans UB ∧ WidenUpperLeft ubWiden ∧
      WidenUpperRight ubWiden ∧ WidenTerminates ubWiden ∧
      (∀ n, ¬ PostFixpoint ubIncr (kleene ubIncr UB.bot n)) ∧
      (∀ n, ¬ lfp counterStep ≤ ubGamma (kleene ubIncr UB.bot n)) ∧
      widenIter ubWiden ubIncr UB.bot 1 = UB.top ∧
      PostFixpoint ubIncr (widenIter ubWiden ubIncr UB.bot 1) ∧
      lfp counterStep ≤ ubGamma (widenIter ubWiden ubIncr UB.bot 1) := by
  refine ⟨ubIncr_monotone, UB.bot_le, UB.not_acc, ubIncr_sound, counterStep_monotone,
    UB.isTrans, ubWiden_upperLeft, ubWiden_upperRight, ubWiden_terminates,
    kleene_ubIncr_not_postFixpoint, ?_, widenIter_ub_one, ?_, ?_⟩
  · intro n h
    cases n with
    | zero => exact h 0 (lfp_counterStep 0)
    | succ n =>
      rw [kleene_ubIncr_succ] at h
      have : n + 1 ≤ n := h (n + 1) (lfp_counterStep (n + 1))
      omega
  · rw [widenIter_ub_one]; exact UB.le_top _
  · rw [widenIter_ub_one]; exact fun _ _ => trivial

/-- Positive control for `R5-widen-diverge`: on the finite-height sign domain, plain
Kleene iteration of the monotone `signLoop` from `bot` reaches the
post-fixpoint `top` at step `2`. -/
theorem kleene_converges_sign :
    kleene signLoop Sign.bot 2 = Sign.top ∧ PostFixpoint signLoop (kleene signLoop Sign.bot 2) :=
  ⟨rfl, by decide⟩

/-! ## Fixtures for the tightness counterexamples of `R5-widen` -/

/-- `NT4w` widening table (satisfies both upper-bound axioms). -/
def nt4wWiden : NT4w → NT4w → NT4w
  | .bot, .bot => .bot
  | .bot, .u => .u
  | .bot, .t => .u
  | .bot, .w => .bot
  | .u, .bot => .u
  | .u, .u => .u
  | .u, .t => .u
  | .u, .w => .bot
  | .t, .bot => .t
  | .t, .u => .u
  | .t, .t => .t
  | .t, .w => .t
  | .w, .bot => .w
  | .w, .u => .bot
  | .w, .t => .t
  | .w, .w => .w

/-- `NT4w` abstract transformer (monotone). -/
def nt4wStep : NT4w → NT4w
  | .bot => .t
  | .u => .w
  | .t => .t
  | .w => .t

theorem nt4wIter_cases (n : Nat) :
    widenIter nt4wWiden nt4wStep NT4w.bot n = NT4w.bot ∨
      widenIter nt4wWiden nt4wStep NT4w.bot n = NT4w.u := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    have e : widenIter nt4wWiden nt4wStep NT4w.bot (n + 1) =
        nt4wWiden (widenIter nt4wWiden nt4wStep NT4w.bot n)
          (nt4wStep (widenIter nt4wWiden nt4wStep NT4w.bot n)) := rfl
    rw [e]
    rcases ih with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- `W4` widening ignoring its left argument (violates `WidenUpperLeft`). -/
def w4Widen (_ b : W4) : W4 :=
  match b with
  | .q => .q
  | _ => .p

/-- `W4` abstract transformer (monotone). -/
def w4Step : W4 → W4
  | .z => .m
  | .m => .m
  | .p => .q
  | .q => .p

theorem w4Iter_cases (n : Nat) :
    widenIter w4Widen w4Step W4.z n = W4.z ∨ widenIter w4Widen w4Step W4.z n = W4.p ∨
      widenIter w4Widen w4Step W4.z n = W4.q := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    have e : widenIter w4Widen w4Step W4.z (n + 1) =
        w4Widen (widenIter w4Widen w4Step W4.z n) (w4Step (widenIter w4Widen w4Step W4.z n)) := rfl
    rw [e]
    rcases ih with h | h | h <;> rw [h]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

theorem widenIter_left_const {A : Type} (fs : A → A) (a₀ : A) (n : Nat) :
    widenIter (fun a _ => a) fs a₀ n = a₀ := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem widenIter_max_succ (n : Nat) : widenIter max Nat.succ 0 n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show max (widenIter max Nat.succ 0 n) (Nat.succ (widenIter max Nat.succ 0 n)) = n + 1
    rw [ih]; omega

/-- Join on `PT` (componentwise maximum; `top` absorbing). -/
def ptJoin : PT → PT → PT
  | .pt i j, .pt i' j' => .pt (max i i') (max j j')
  | _, _ => .top

/-- A widening on `PT`: keep `a` if `b ≤ a`; from the bottom `pt 0 0` move to
`b`; jump to `top` on a comparable increase; take the join of incomparable
values.  It satisfies both upper-bound axioms and the termination axiom (for
ascending inputs), but the widened chain of a non-ascending input can increase
forever through the join branch. -/
def ptWiden (a b : PT) : PT :=
  if b ≤ a then a
  else if a = PT.pt 0 0 then b
  else if a ≤ b then PT.top
  else ptJoin a b

theorem ptWiden_top (b : PT) : ptWiden PT.top b = PT.top := by
  unfold ptWiden; rw [ite_of_pos (PT.le_top b)]

theorem ptWiden_upperLeft : WidenUpperLeft ptWiden := by
  intro a b
  unfold ptWiden
  by_cases h1 : b ≤ a
  · rw [ite_of_pos h1]; exact PT.isRefl a
  · rw [ite_of_neg h1]
    by_cases h2 : a = PT.pt 0 0
    · rw [ite_of_pos h2, h2]
      cases b with
      | pt i j => simp
      | top => exact PT.le_top _
    · rw [ite_of_neg h2]
      by_cases h3 : a ≤ b
      · rw [ite_of_pos h3]; exact PT.le_top a
      · rw [ite_of_neg h3]
        cases a <;> cases b <;> simp [ptJoin] <;> omega

theorem ptWiden_upperRight : WidenUpperRight ptWiden := by
  intro a b
  unfold ptWiden
  by_cases h1 : b ≤ a
  · rw [ite_of_pos h1]; exact h1
  · rw [ite_of_neg h1]
    by_cases h2 : a = PT.pt 0 0
    · rw [ite_of_pos h2]; exact PT.isRefl b
    · rw [ite_of_neg h2]
      by_cases h3 : a ≤ b
      · rw [ite_of_pos h3]; exact PT.le_top b
      · rw [ite_of_neg h3]
        cases a <;> cases b <;> simp [ptJoin] <;> omega

theorem ptWiden_terminates : WidenTerminates ptWiden := by
  intro b hasc hall
  have h0 := hall 0
  have h1 := hall 1
  have h2 := hall 2
  change StrictLt (b 0) (ptWiden (b 0) (b 1)) at h0
  have c1 : widenChain ptWiden b 1 = ptWiden (b 0) (b 1) := rfl
  have c2 : widenChain ptWiden b 2 = ptWiden (widenChain ptWiden b 1) (b 2) := rfl
  have c3 : widenChain ptWiden b 3 = ptWiden (widenChain ptWiden b 2) (b 3) := rfl
  by_cases hb1 : b 1 ≤ b 0
  · unfold ptWiden at h0; rw [ite_of_pos hb1] at h0; exact StrictLt.irrefl _ h0
  · by_cases hz : b 0 = PT.pt 0 0
    · have e1 : widenChain ptWiden b 1 = b 1 := by
        rw [c1]; unfold ptWiden; rw [ite_of_neg hb1, ite_of_pos hz]
      by_cases hb2 : b 2 ≤ b 1
      · have e2 : widenChain ptWiden b 2 = b 1 := by
          rw [c2, e1]; unfold ptWiden; rw [ite_of_pos hb2]
        rw [e1, e2] at h1; exact StrictLt.irrefl _ h1
      · have hz1 : b 1 ≠ PT.pt 0 0 := by
          intro h; apply hb1; rw [h, hz]; exact PT.isRefl _
        have e2 : widenChain ptWiden b 2 = PT.top := by
          rw [c2, e1]; unfold ptWiden; rw [ite_of_neg hb2, ite_of_neg hz1, ite_of_pos (hasc 1)]
        have e3 : widenChain ptWiden b 3 = PT.top := by rw [c3, e2, ptWiden_top]
        rw [e2, e3] at h2; exact StrictLt.irrefl _ h2
    · have e1 : widenChain ptWiden b 1 = PT.top := by
        rw [c1]; unfold ptWiden; rw [ite_of_neg hb1, ite_of_neg hz, ite_of_pos (hasc 0)]
      have e2 : widenChain ptWiden b 2 = PT.top := by rw [c2, e1, ptWiden_top]
      rw [e1, e2] at h1; exact StrictLt.irrefl _ h1

/-- A non-monotone transformer on `PT`. -/
def ptBadStep : PT → PT
  | .pt i j => if i ≤ j then .pt (j + 1) 0 else .pt 0 (i + 1)
  | .top => .top

/-- A monotone transformer on `PT` that moves "sideways": `(i, j) ↦ (i+1, j-1)`. -/
def ptShift : PT → PT
  | .pt i j => .pt (i + 1) (j - 1)
  | .top => .top

theorem ptShift_monotone : Monotone ptShift := by
  intro a b hab
  cases a <;> cases b <;> simp_all [ptShift] <;> omega

/-- Invariant of widened iteration of `ptBadStep` from `pt 0 0`, after step 0. -/
theorem ptBad_iter_inv (n : Nat) :
    ∃ i j, widenIter ptWiden ptBadStep (PT.pt 0 0) (n + 1) = PT.pt i j ∧
      (i = j + 1 ∨ j = i + 1) := by
  induction n with
  | zero =>
    refine ⟨1, 0, ?_, Or.inl rfl⟩
    show ptWiden (PT.pt 0 0) (ptBadStep (PT.pt 0 0)) = PT.pt 1 0
    unfold ptWiden; simp [ptBadStep]
  | succ n ih =>
    obtain ⟨i, j, hx, _hij⟩ := ih
    show ∃ i' j', ptWiden (widenIter ptWiden ptBadStep (PT.pt 0 0) (n + 1))
        (ptBadStep (widenIter ptWiden ptBadStep (PT.pt 0 0) (n + 1))) = PT.pt i' j' ∧ _
    rw [hx]
    by_cases hle : i ≤ j
    · have hj : j = i + 1 := by omega
      have hs : ptBadStep (PT.pt i j) = PT.pt (j + 1) 0 := by simp [ptBadStep, hle]
      rw [hs]
      have n1 : ¬ (PT.pt (j + 1) 0 ≤ PT.pt i j) := by simp; omega
      have n2 : PT.pt i j ≠ PT.pt 0 0 := by intro h; cases h; omega
      have n3 : ¬ (PT.pt i j ≤ PT.pt (j + 1) 0) := by simp; omega
      unfold ptWiden
      rw [ite_of_neg n1, ite_of_neg n2, ite_of_neg n3]
      exact ⟨max i (j + 1), max j 0, rfl, by omega⟩
    · have hi : i = j + 1 := by omega
      have hs : ptBadStep (PT.pt i j) = PT.pt 0 (i + 1) := by simp [ptBadStep, hle]
      rw [hs]
      have n1 : ¬ (PT.pt 0 (i + 1) ≤ PT.pt i j) := by simp; omega
      have n2 : PT.pt i j ≠ PT.pt 0 0 := by intro h; cases h; omega
      have n3 : ¬ (PT.pt i j ≤ PT.pt 0 (i + 1)) := by simp; omega
      unfold ptWiden
      rw [ite_of_neg n1, ite_of_neg n2, ite_of_neg n3]
      exact ⟨max i 0, max j (i + 1), rfl, by omega⟩

theorem ptBad_not_postFixpoint (i j : Nat) :
    ¬ PostFixpoint ptBadStep (PT.pt i j) := by
  unfold PostFixpoint
  by_cases hle : i ≤ j
  · simp [ptBadStep, hle]; omega
  · simp [ptBadStep, hle]; omega

theorem ptShift_iter (n : Nat) : widenIter ptWiden ptShift (PT.pt 0 1) n = PT.pt n 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show ptWiden (widenIter ptWiden ptShift (PT.pt 0 1) n)
      (ptShift (widenIter ptWiden ptShift (PT.pt 0 1) n)) = _
    rw [ih]
    have n1 : ¬ (ptShift (PT.pt n 1) ≤ PT.pt n 1) := by simp [ptShift]
    have n2 : PT.pt n 1 ≠ PT.pt 0 0 := by intro h; cases h
    have n3 : ¬ (PT.pt n 1 ≤ ptShift (PT.pt n 1)) := by simp [ptShift]
    unfold ptWiden
    rw [ite_of_neg n1, ite_of_neg n2, ite_of_neg n3]
    simp only [ptShift, ptJoin]
    congr 1 <;> omega

/-! ## Tightness counterexamples (proved) -/

/-- `R5-widen` needs transitivity: on the reflexive, non-transitive `NT4w`, all other
hypotheses hold, but widened iteration from `bot` alternates `bot, u, bot, u, …`
and never reaches a post-fixpoint. -/
theorem widen_tight_trans :
    ¬ IsTrans NT4w ∧ WidenUpperLeft nt4wWiden ∧ WidenUpperRight nt4wWiden ∧
      WidenTerminates nt4wWiden ∧ Monotone nt4wStep ∧ NT4w.bot ≤ nt4wStep NT4w.bot ∧
      ∀ n, ¬ PostFixpoint nt4wStep (widenIter nt4wWiden nt4wStep NT4w.bot n) := by
  refine ⟨NT4w.not_isTrans, ?_, ?_, widenTerminates_of_acc NT4w.acc _, ?_, by decide, ?_⟩
  · intro a b; cases a <;> cases b <;> decide
  · intro a b; cases a <;> cases b <;> decide
  · intro a b hab; cases a <;> cases b <;> first | decide | exact absurd hab (by decide)
  · intro n
    rcases nt4wIter_cases n with h | h <;> rw [h] <;> decide

/-- `R5-widen` needs `WidenUpperLeft`: on the poset `W4`, `w4Widen` ignores its left
argument; widened iteration from `z` goes `z, p, q, p, q, …`. -/
theorem widen_tight_upperLeft :
    IsTrans W4 ∧ ¬ WidenUpperLeft w4Widen ∧ WidenUpperRight w4Widen ∧
      WidenTerminates w4Widen ∧ Monotone w4Step ∧ W4.z ≤ w4Step W4.z ∧
      ∀ n, ¬ PostFixpoint w4Step (widenIter w4Widen w4Step W4.z n) := by
  refine ⟨W4.isTrans, ?_, ?_, widenTerminates_of_acc W4.acc _, ?_, by decide, ?_⟩
  · intro h; exact absurd (h W4.q W4.p) (by decide)
  · intro a b; cases a <;> cases b <;> decide
  · intro a b hab; cases a <;> cases b <;> first | decide | exact absurd hab (by decide)
  · intro n
    rcases w4Iter_cases n with h | h | h <;> rw [h] <;> decide

/-- `R5-widen` needs `WidenUpperRight`: the left projection on `B2` keeps the iteration
at `lo`, which is not a post-fixpoint of the constant-`hi` transformer. -/
theorem widen_tight_upperRight :
    IsTrans B2 ∧ WidenUpperLeft (fun a _ : B2 => a) ∧ ¬ WidenUpperRight (fun a _ : B2 => a) ∧
      WidenTerminates (fun a _ : B2 => a) ∧ Monotone (fun _ : B2 => B2.hi) ∧
      B2.lo ≤ (fun _ : B2 => B2.hi) B2.lo ∧
      ∀ n, ¬ PostFixpoint (fun _ : B2 => B2.hi)
        (widenIter (fun a _ : B2 => a) (fun _ : B2 => B2.hi) B2.lo n) := by
  refine ⟨B2.isTrans, fun a _ => B2.isRefl a, widenUpperRight_example_neg,
    widenTerminates_of_acc B2.acc _, fun _ _ _ => B2.isRefl _, by decide, ?_⟩
  intro n
  rw [widenIter_left_const]
  decide

/-- `R5-widen` needs the termination axiom: `max` on `Nat` satisfies both upper-bound
axioms, but widened iteration of `succ` from `0` is `0, 1, 2, …`. -/
theorem widen_tight_terminates :
    IsTrans Nat ∧ WidenUpperLeft (max : Nat → Nat → Nat) ∧
      WidenUpperRight (max : Nat → Nat → Nat) ∧ ¬ WidenTerminates (max : Nat → Nat → Nat) ∧
      Monotone Nat.succ ∧ 0 ≤ Nat.succ 0 ∧
      ∀ n, ¬ PostFixpoint Nat.succ (widenIter max Nat.succ 0 n) := by
  refine ⟨fun _ _ _ => Nat.le_trans, fun a b => by omega, fun a b => by omega,
    widenTerminates_example_neg, fun _ _ h => Nat.succ_le_succ h, Nat.zero_le _, ?_⟩
  intro n h
  rw [widenIter_max_succ] at h
  exact Nat.not_succ_le_self n h

/-- `R5-widen` needs monotone `fs`: on `PT` with `ptWiden`, the non-monotone
`ptBadStep` drives widened iteration from `pt 0 0` through incomparable values
forever (the join branch never triggers the jump to `top`). -/
theorem widen_tight_monotone :
    IsTrans PT ∧ WidenUpperLeft ptWiden ∧ WidenUpperRight ptWiden ∧
      WidenTerminates ptWiden ∧ ¬ Monotone ptBadStep ∧ PT.pt 0 0 ≤ ptBadStep (PT.pt 0 0) ∧
      ∀ n, ¬ PostFixpoint ptBadStep (widenIter ptWiden ptBadStep (PT.pt 0 0) n) := by
  refine ⟨PT.isTrans, ptWiden_upperLeft, ptWiden_upperRight, ptWiden_terminates, ?_, ?_, ?_⟩
  · intro h
    have := h (PT.pt 0 0) (PT.pt 1 0) (by simp)
    simp [ptBadStep] at this
  · simp [ptBadStep]
  · intro n
    cases n with
    | zero => unfold PostFixpoint; simp [widenIter, ptBadStep]
    | succ n =>
      obtain ⟨i, j, hx, _⟩ := ptBad_iter_inv n
      rw [hx]; exact ptBad_not_postFixpoint i j

/-- `R5-widen` needs `a₀ ≤ fs a₀`: on `PT` with `ptWiden`, the monotone `ptShift`
started at `pt 0 1` (with `pt 0 1 ≰ ptShift (pt 0 1) = pt 1 0`) gives widened
iterates `pt n 1`, none of which is a post-fixpoint. -/
theorem widen_tight_start :
    IsTrans PT ∧ WidenUpperLeft ptWiden ∧ WidenUpperRight ptWiden ∧
      WidenTerminates ptWiden ∧ Monotone ptShift ∧ ¬ (PT.pt 0 1 ≤ ptShift (PT.pt 0 1)) ∧
      ∀ n, ¬ PostFixpoint ptShift (widenIter ptWiden ptShift (PT.pt 0 1) n) := by
  refine ⟨PT.isTrans, ptWiden_upperLeft, ptWiden_upperRight, ptWiden_terminates,
    ptShift_monotone, by simp [ptShift], ?_⟩
  intro n
  rw [ptShift_iter]
  unfold PostFixpoint
  simp [ptShift]

/-- `R5-widen-bridge`: its premise cannot be dropped — `max` on `Nat` neither
stabilizes nor terminates. -/
theorem widenBridge_tight : ¬ WidenStabilizes (max : Nat → Nat → Nat) ∧
    ¬ WidenTerminates (max : Nat → Nat → Nat) :=
  ⟨widenStabilizes_example_neg, widenTerminates_example_neg⟩

/-! ## Boundary examples (proved) -/

/-- On the two-element total preorder `E2`, the operator that flips its left
argument satisfies every widening axiom used by `R5-widen` but not
`WidenStabilizes`: its widened chains cycle between two order-equivalent,
distinct elements. -/
def flipWiden : E2 → E2 → E2
  | .a, _ => .b
  | .b, _ => .a

theorem flipWiden_chain_step (n : Nat) :
    widenChain flipWiden (fun _ => E2.a) (n + 1) ≠ widenChain flipWiden (fun _ => E2.a) n := by
  show flipWiden (widenChain flipWiden (fun _ => E2.a) n) E2.a ≠
    widenChain flipWiden (fun _ => E2.a) n
  cases widenChain flipWiden (fun _ => E2.a) n <;> decide

theorem widenTerminates_not_widenStabilizes_preorder :
    IsRefl E2 ∧ IsTrans E2 ∧ ¬ IsAntisymm E2 ∧ HeightLE E2 0 ∧
      WidenUpperLeft flipWiden ∧ WidenUpperRight flipWiden ∧
      WidenTerminates flipWiden ∧ ¬ WidenStabilizes flipWiden := by
  refine ⟨E2.isRefl, E2.isTrans, E2.not_isAntisymm, E2.heightLE,
    fun _ _ => trivial, fun _ _ => trivial, ?_, ?_⟩
  · intro _ _ hall
    exact (hall 0).2 trivial
  · intro hstab
    obtain ⟨N, hN⟩ := hstab (fun _ => E2.a) (fun _ => trivial)
    exact flipWiden_chain_step N (hN (N + 1) (Nat.le_succ N))

/-- A monotone transformer on the chain `Fin 4`: `0, 1 ↦ 1`, `2, 3 ↦ 3`. -/
def step4 (i : Fin 4) : Fin 4 :=
  if i.val ≤ 1 then ⟨1, by omega⟩ else ⟨3, by omega⟩

/-- A widening on `Fin 4`: `1 ∇ 1 = 2`, otherwise the maximum. -/
def widen4 (a b : Fin 4) : Fin 4 :=
  if a.val = 1 ∧ b.val = 1 then ⟨2, by omega⟩
  else ⟨max a.val b.val, by have := a.isLt; have := b.isLt; omega⟩

theorem Fin4.acc : ACC (Fin 4) :=
  acc_of_rank (fun i => i.val) 3
    (fun a b hab => by
      have h1 : a.val ≤ b.val := hab.1
      have h2 : ¬ b.val ≤ a.val := hab.2
      omega)
    (fun i => by have := i.isLt; omega)

theorem widen4_stabilizes : WidenStabilizes widen4 := by
  intro b _
  let y := widenChain widen4 b
  have hy_asc : ∀ n, (y n).val ≤ (y (n + 1)).val := by
    intro n
    change (y n).val ≤ (widen4 (y n) (b (n + 1))).val
    unfold widen4
    split
    · rename_i h; dsimp; omega
    · exact Nat.le_max_left _ _
  have hy_mono : ∀ m n, m ≤ n → (y m).val ≤ (y n).val := by
    intro m n hmn
    induction hmn with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans ih (hy_asc _)
  have hex : ∃ N, ∀ m, N ≤ m → (y m).val = (y N).val := by
    apply Classical.byContradiction
    intro hno
    have next : ∀ k, ∃ m, k ≤ m ∧ (y k).val < (y m).val := by
      intro k
      apply Classical.byContradiction
      intro hnone
      apply hno
      refine ⟨k, fun m hm => ?_⟩
      have h1 : (y k).val ≤ (y m).val := hy_mono k m hm
      have h2 : ¬ (y k).val < (y m).val := fun hlt => hnone ⟨m, hm, hlt⟩
      omega
    obtain ⟨n1, _, h01⟩ := next 0
    obtain ⟨n2, _, h12⟩ := next n1
    obtain ⟨n3, _, h23⟩ := next n2
    obtain ⟨n4, _, h34⟩ := next n3
    have hlt := (y n4).isLt
    omega
  obtain ⟨N, hN⟩ := hex
  exact ⟨N, fun m hm => Fin.ext (hN m hm)⟩

/-- Under every hypothesis of `R5-widen` (on a total order, with
`WidenStabilizes` as well), widened iteration reaches a post-fixpoint at step `1`
(`x 1 = 1`) and leaves the post-fixpoints at step `2` (`x 2 = 2`,
`step4 2 = 3 ≰ 2`): post-fixpoints are not preserved by further widening, so the
iteration must stop at the first one. -/
theorem widenIter_postFixpoint_not_persistent :
    IsRefl (Fin 4) ∧ IsTrans (Fin 4) ∧ IsAntisymm (Fin 4) ∧
      WidenUpperLeft widen4 ∧ WidenUpperRight widen4 ∧
      WidenStabilizes widen4 ∧ WidenTerminates widen4 ∧
      Monotone step4 ∧ (⟨0, by omega⟩ : Fin 4) ≤ step4 ⟨0, by omega⟩ ∧
      PostFixpoint step4 (widenIter widen4 step4 ⟨0, by omega⟩ 1) ∧
      ¬ PostFixpoint step4 (widenIter widen4 step4 ⟨0, by omega⟩ 2) := by
  refine ⟨fun _ => Nat.le_refl _, fun _ _ _ => Nat.le_trans,
    fun _ _ h1 h2 => Fin.ext (Nat.le_antisymm h1 h2), ?_, ?_, widen4_stabilizes,
    widenTerminates_of_acc Fin4.acc _, ?_, by decide, by decide, by decide⟩
  · intro a b; unfold widen4; split
    · rename_i h; show a.val ≤ 2; omega
    · exact Nat.le_max_left _ _
  · intro a b; unfold widen4; split
    · rename_i h; show b.val ≤ 2; omega
    · exact Nat.le_max_right _ _
  · intro a b hab
    have hle : a.val ≤ b.val := hab
    show (step4 a).val ≤ (step4 b).val
    unfold step4
    split <;> split <;> dsimp <;> omega

/-- A preorder that is not antisymmetric: points `pt m s` (a natural number with a
tag) ordered by their numbers, plus a top element. -/
inductive PB | pt (m : Nat) (s : Bool) | top
  deriving DecidableEq, Repr

def PB.leb : PB → PB → Bool
  | .pt m _, .pt n _ => decide (m ≤ n)
  | _, .top => true
  | .top, .pt _ _ => false

instance : LE PB := ⟨fun a b => PB.leb a b = true⟩
instance (a b : PB) : Decidable (a ≤ b) := inferInstanceAs (Decidable (PB.leb a b = true))

@[simp] theorem PB.pt_le_pt (m n : Nat) (s t : Bool) : (PB.pt m s ≤ PB.pt n t) ↔ m ≤ n := by
  show PB.leb _ _ = true ↔ _
  simp [PB.leb]
@[simp] theorem PB.le_top (a : PB) : a ≤ PB.top := by
  show PB.leb _ _ = true
  cases a <;> rfl
@[simp] theorem PB.not_top_le_pt (m : Nat) (s : Bool) : ¬ (PB.top ≤ PB.pt m s) := by
  show ¬ (PB.leb _ _ = true)
  simp [PB.leb]

/-- A widening on `PB`: from a `false`-tagged point, re-tag on a non-increase and
jump to `top` on an increase; from a `true`-tagged point, keep it on a
non-increase and move to the new point, tagged `false`, on an increase. -/
def pbWiden : PB → PB → PB
  | .top, _ => .top
  | .pt _ _, .top => .top
  | .pt m false, .pt n _ => if n ≤ m then .pt m true else .top
  | .pt m true, .pt n _ => if n ≤ m then .pt m true else .pt n false

/-- An ascending input that repeats every value: `(0, true), (1, true), (1, true),
(2, true), (2, true), …`. -/
def pbStutter (n : Nat) : PB := .pt ((n + 1) / 2) true

theorem pbWiden_top_left (c : PB) : pbWiden PB.top c = PB.top := rfl

theorem pb_not_strict_from_top (c : PB) : ¬ StrictLt PB.top (pbWiden PB.top c) :=
  fun h => h.2 (PB.le_top _)

theorem pb_strict_from_false {n : Nat} {c : PB}
    (h : StrictLt (PB.pt n false) (pbWiden (PB.pt n false) c)) :
    pbWiden (PB.pt n false) c = PB.top := by
  cases c with
  | top => rfl
  | pt k u =>
    by_cases hk : k ≤ n
    · have e : pbWiden (PB.pt n false) (PB.pt k u) = PB.pt n true := by
        simp [pbWiden, hk]
      rw [e] at h
      exact absurd ((PB.pt_le_pt n n true false).mpr (Nat.le_refl n)) h.2
    · simp [pbWiden, hk]

theorem pb_strict_cases {a c : PB} (h : StrictLt a (pbWiden a c)) :
    pbWiden a c = PB.top ∨ ∃ n, pbWiden a c = PB.pt n false := by
  cases a with
  | top => exact Or.inl rfl
  | pt m s =>
    cases c with
    | top => cases s <;> exact Or.inl rfl
    | pt k u =>
      cases s with
      | false =>
        by_cases hk : k ≤ m
        · have e : pbWiden (PB.pt m false) (PB.pt k u) = PB.pt m true := by
            simp [pbWiden, hk]
          rw [e] at h
          exact absurd ((PB.pt_le_pt m m true false).mpr (Nat.le_refl m)) h.2
        · exact Or.inl (by simp [pbWiden, hk])
      | true =>
        by_cases hk : k ≤ m
        · have e : pbWiden (PB.pt m true) (PB.pt k u) = PB.pt m true := by
            simp [pbWiden, hk]
          rw [e] at h
          exact absurd (Nat.le_refl m |> (PB.pt_le_pt m m true true).mpr) h.2
        · exact Or.inr ⟨k, by simp [pbWiden, hk]⟩

theorem pbWiden_upperLeft : WidenUpperLeft pbWiden := by
  intro a c
  cases a with
  | top => exact PB.le_top _
  | pt m s =>
    cases c with
    | top => cases s <;> exact PB.le_top _
    | pt k u =>
      cases s with
      | false =>
        by_cases hk : k ≤ m
        · simp [pbWiden, hk]
        · simp [pbWiden, hk]
      | true =>
        by_cases hk : k ≤ m
        · simp [pbWiden, hk]
        · simp [pbWiden, hk]; omega

theorem pbWiden_upperRight : WidenUpperRight pbWiden := by
  intro a c
  cases a with
  | top => exact PB.le_top _
  | pt m s =>
    cases c with
    | top => cases s <;> exact PB.le_top _
    | pt k u =>
      cases s with
      | false =>
        by_cases hk : k ≤ m
        · simp [pbWiden, hk]
        · simp [pbWiden, hk]
      | true =>
        by_cases hk : k ≤ m
        · simp [pbWiden, hk]
        · simp [pbWiden, hk]

/-- `pbWiden` satisfies the termination axiom, indeed for every input sequence:
among the first three widened steps one is not strict. -/
theorem pbWiden_terminates : WidenTerminates pbWiden := by
  intro b _ hall
  have h0 : StrictLt (widenChain pbWiden b 0) (pbWiden (widenChain pbWiden b 0) (b 1)) := hall 0
  have h1 : StrictLt (widenChain pbWiden b 1) (pbWiden (widenChain pbWiden b 1) (b 2)) := hall 1
  have h2 : StrictLt (widenChain pbWiden b 2) (pbWiden (widenChain pbWiden b 2) (b 3)) := hall 2
  have c1 : widenChain pbWiden b 1 = pbWiden (widenChain pbWiden b 0) (b 1) := rfl
  have c2 : widenChain pbWiden b 2 = pbWiden (widenChain pbWiden b 1) (b 2) := rfl
  rcases pb_strict_cases h0 with e | ⟨n, e⟩
  · rw [c1, e] at h1
    exact pb_not_strict_from_top _ h1
  · rw [c1, e] at h1
    have e2 := pb_strict_from_false h1
    rw [c2, c1, e, e2] at h2
    exact pb_not_strict_from_top _ h2

theorem pbStutter_chain (k : Nat) :
    widenChain pbWiden pbStutter (2 * k) = PB.pt k true ∧
      widenChain pbWiden pbStutter (2 * k + 1) = PB.pt (k + 1) false := by
  induction k with
  | zero =>
    refine ⟨rfl, ?_⟩
    show pbWiden (PB.pt 0 true) (PB.pt 1 true) = PB.pt 1 false
    simp [pbWiden]
  | succ k ih =>
    have i1 : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
    have e1 : widenChain pbWiden pbStutter (2 * k + 1 + 1) =
        pbWiden (widenChain pbWiden pbStutter (2 * k + 1)) (pbStutter (2 * k + 1 + 1)) := rfl
    have d1 : (2 * k + 1 + 1 + 1) / 2 = k + 1 := by omega
    have s1 : widenChain pbWiden pbStutter (2 * (k + 1)) = PB.pt (k + 1) true := by
      rw [i1, e1, ih.2]
      simp [pbStutter, d1, pbWiden]
    refine ⟨s1, ?_⟩
    have e2 : widenChain pbWiden pbStutter (2 * (k + 1) + 1) =
        pbWiden (widenChain pbWiden pbStutter (2 * (k + 1))) (pbStutter (2 * (k + 1) + 1)) := rfl
    have d2 : (2 * (k + 1) + 1 + 1) / 2 = k + 1 + 1 := by omega
    rw [e2, s1]
    simp [pbStutter, d2, pbWiden]

theorem pbStutter_chain_val (n : Nat) :
    widenChain pbWiden pbStutter n = PB.pt ((n + 1) / 2) (n % 2 == 0) := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · subst hk
    rw [(pbStutter_chain k).1]
    have d : (2 * k + 1) / 2 = k := by omega
    have m : 2 * k % 2 = 0 := by omega
    simp [d, m]
  · subst hk
    rw [(pbStutter_chain k).2]
    have d : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    have m : (2 * k + 1) % 2 = 1 := by omega
    simp [d, m]

/-- On a preorder that is not antisymmetric, `WidenTerminates` (even for all
inputs) does not bound the number of strict steps of a widened chain, nor make
it stabilize up to `≤`: for the ascending, stuttering input `pbStutter`, the
widened chain of `pbWiden` is strict at every even step and keeps increasing. -/
theorem pbWiden_terminates_infinitely_many_strict :
    IsRefl PB ∧ IsTrans PB ∧ ¬ IsAntisymm PB ∧
      WidenUpperLeft pbWiden ∧ WidenUpperRight pbWiden ∧ WidenTerminates pbWiden ∧
      Ascending pbStutter ∧
      (∀ k, StrictLt (widenChain pbWiden pbStutter (2 * k))
        (widenChain pbWiden pbStutter (2 * k + 1))) ∧
      ¬ ∃ N, ∀ m, N ≤ m → widenChain pbWiden pbStutter m ≤ widenChain pbWiden pbStutter N := by
  refine ⟨?_, ?_, ?_, pbWiden_upperLeft, pbWiden_upperRight, pbWiden_terminates, ?_, ?_, ?_⟩
  · intro a; cases a <;> simp
  · intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all <;> omega
  · intro h
    have := h (PB.pt 0 false) (PB.pt 0 true) (by simp) (by simp)
    exact absurd this (by decide)
  · intro n
    show PB.pt ((n + 1) / 2) true ≤ PB.pt ((n + 1 + 1) / 2) true
    simp; omega
  · intro k
    rw [(pbStutter_chain k).1, (pbStutter_chain k).2]
    exact ⟨by simp, by simp⟩
  · intro ⟨N, hN⟩
    have := hN (N + 2) (by omega)
    rw [pbStutter_chain_val, pbStutter_chain_val] at this
    simp at this
    omega

end Toy.AbsInt
