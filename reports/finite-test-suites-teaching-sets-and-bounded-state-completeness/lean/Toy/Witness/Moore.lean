/-
Deterministic Moore machines, Moore's state-distinguishability bound (`≤ n - 2`
input symbols), general sharpness counterexamples for single-machine (`n - 2`),
two-machine (`n₁ + n₂ - 2`), and class-suite (`2k - 2`) horizons, completeness
of explicit finite word test suites under state and finite-alphabet bounds,
infinite-alphabet impossibility for `k ≥ 2` (and `k = 1` teachability), and
unbounded-state impossibility via the `deviateAfter` step-counting construction.
-/
import Toy.Witness.Core
import Toy.Witness.Unrestricted

namespace Toy.Witness

universe u v w

/-- A deterministic Moore transition system (without a designated start state)
over input alphabet `I`, output alphabet `O`, and state space `S`. Captures a
deterministic reactive implementation whose observable output depends only on
the current internal state. -/
structure MooreMachine (I : Type u) (O : Type v) (S : Type w) where
  step : S → I → S
  out  : S → O

/-- Execute a deterministic Moore machine from state `s` on input word `w`. -/
def MooreMachine.run {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) : S → List I → S
  | s, [] => s
  | s, a :: ws => M.run (M.step s a) ws

theorem MooreMachine.run_append {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s : S) (u v : List I) :
    M.run s (u ++ v) = M.run (M.run s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a us ih => exact ih (M.step s a)

/-- The input-output behavior of a Moore machine starting from state `s`: maps
each input word `w` to the output observed after executing `w` from `s` (so `[]`
observes `M.out s`). -/
def MooreMachine.behavior {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s : S) (w : List I) : O :=
  M.out (M.run s w)

/-- Two states `s, t` of a Moore machine `M` are behaviorally equivalent if they
produce identical outputs on every finite input word. -/
def StateEquiv {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s t : S) : Prop :=
  M.behavior s = M.behavior t

/-- Two states `s, t` of a Moore machine `M` agree up to length `k` if they
produce identical outputs on every input word of length at most `k`. -/
def AgreeUpTo {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s t : S) (k : Nat) : Prop :=
  ∀ w : List I, w.length ≤ k → M.behavior s w = M.behavior t w

/-- An initialized deterministic Moore machine with exactly `n` states (`Fin n`)
and a designated initial state `init`. -/
structure InitMooreMachine (I : Type u) (O : Type v) (n : Nat)
    extends MooreMachine I O (Fin n) where
  init : Fin n

/-- Input-output behavior of an initialized Moore machine from its initial state. -/
def InitMooreMachine.behavior {I : Type u} {O : Type v} {n : Nat}
    (M : InitMooreMachine I O n) : List I → O :=
  M.toMooreMachine.behavior M.init

/-- Functions `List I → O` realizable by some initialized deterministic Moore
machine with at most `k` states. Captures a conformance class bounded by an
explicit internal-state ceiling `k`. -/
def BoundedMooreBehaviors (I : Type u) (O : Type v) (k : Nat) :
    HypothesisClass (List I) O :=
  fun f => ∃ (m : Nat), m ≤ k ∧ ∃ M : InitMooreMachine I O m, M.behavior = f

/-- Functions `List I → O` realizable by some finite-state deterministic Moore
machine with no a priori bound on the number of states. -/
def FiniteStateMooreBehaviors (I : Type u) (O : Type v) :
    HypothesisClass (List I) O :=
  fun f => ∃ (n : Nat) (M : InitMooreMachine I O n), M.behavior = f

/-- `CoversAll L` means the finite list `L` contains every element of `α`. Used
to witness finiteness of an input alphabet `I`. -/
def CoversAll {α : Type u} (L : List α) : Prop :=
  ∀ a : α, a ∈ L

/-- All words of exact length `k` formed from symbols in `alphabet`. -/
def wordsOfLength {I : Type u} (alphabet : List I) : Nat → List (List I)
  | 0 => [[]]
  | k + 1 => alphabet.flatMap (fun a => (wordsOfLength alphabet k).map (a :: ·))

/-- All words of length at most `L` formed from symbols in `alphabet`. -/
def wordsUpTo {I : Type u} (alphabet : List I) : Nat → List (List I)
  | 0 => [[]]
  | L + 1 => wordsUpTo alphabet L ++ wordsOfLength alphabet (L + 1)

theorem mem_wordsOfLength_iff {I : Type u} {alphabet : List I}
    (hCover : CoversAll alphabet) :
    ∀ (k : Nat) (w : List I), w ∈ wordsOfLength alphabet k ↔ w.length = k := by
  intro k
  induction k with
  | zero =>
    intro w
    cases w with
    | nil => simp [wordsOfLength]
    | cons _ _ => simp [wordsOfLength]
  | succ k ih =>
    intro w
    cases w with
    | nil =>
      simp only [wordsOfLength, List.mem_flatMap, List.mem_map, List.length_nil]
      constructor
      · rintro ⟨_, _, _, _, h⟩; cases h
      · intro h; cases h
    | cons a ws =>
      simp only [wordsOfLength, List.mem_flatMap, List.mem_map, List.length_cons]
      constructor
      · rintro ⟨a', _, ws', hws', hcons⟩
        injection hcons with _ hws_eq
        subst hws_eq
        exact congrArg Nat.succ ((ih ws').mp hws')
      · intro hlen
        have hws : ws.length = k := Nat.succ.inj hlen
        exact ⟨a, hCover a, ws, (ih ws).mpr hws, rfl⟩

theorem mem_wordsUpTo_iff {I : Type u} {alphabet : List I}
    (hCover : CoversAll alphabet) :
    ∀ (L : Nat) (w : List I), w ∈ wordsUpTo alphabet L ↔ w.length ≤ L := by
  intro L
  induction L with
  | zero =>
    intro w
    cases w with
    | nil => simp [wordsUpTo]
    | cons _ _ => simp [wordsUpTo]
  | succ L ih =>
    intro w
    simp only [wordsUpTo, List.mem_append, ih w, mem_wordsOfLength_iff hCover (L + 1) w]
    omega

/-- Complete finite conformance test suite for a known `n₁`-state specification
machine `M` against all implementations with at most `k₂` states over `alphabet`:
every word of length at most `n₁ + k₂ - 2`, labeled by `M.behavior`. -/
def mooreSpecTestSuite {I : Type u} {O : Type v} {n₁ : Nat}
    (alphabet : List I) (M : InitMooreMachine I O n₁) (k₂ : Nat) :
    List (List I × O) :=
  labelSample M.behavior (wordsUpTo alphabet (n₁ + k₂ - 2))

/-- Universal finite conformance test suite for any behavior `h` in
`BoundedMooreBehaviors I O k` over `alphabet`: every word of length at most
`2 * k - 2`, labeled by `h`. -/
def mooreClassTestSuite {I : Type u} {O : Type v}
    (alphabet : List I) (k : Nat) (h : List I → O) :
    List (List I × O) :=
  labelSample h (wordsUpTo alphabet (2 * k - 2))

/-! ### Disjoint Union of Two Initialized Moore Machines -/

/-- Left embedding `Fin n₁ → Fin (n₁ + n₂)`. -/
def inlFin {n₁ n₂ : Nat} (s : Fin n₁) : Fin (n₁ + n₂) :=
  ⟨s.val, Nat.lt_of_lt_of_le s.isLt (Nat.le_add_right n₁ n₂)⟩

/-- Right embedding `Fin n₂ → Fin (n₁ + n₂)`. -/
def inrFin {n₁ n₂ : Nat} (s : Fin n₂) : Fin (n₁ + n₂) :=
  ⟨n₁ + s.val, Nat.add_lt_add_left s.isLt n₁⟩

/-- Disjoint union of two initialized Moore machines `M₁` (`n₁` states) and `M₂`
(`n₂` states) into a single Moore machine with `n₁ + n₂` states. -/
def disjointUnion {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂) :
    MooreMachine I O (Fin (n₁ + n₂)) where
  step s a :=
    if h : s.val < n₁ then
      inlFin (M₁.step ⟨s.val, h⟩ a)
    else
      inrFin (M₂.step ⟨s.val - n₁, by omega⟩ a)
  out s :=
    if h : s.val < n₁ then
      M₁.out ⟨s.val, h⟩
    else
      M₂.out ⟨s.val - n₁, by omega⟩

private theorem run_disjointUnion_inl {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂)
    (s : Fin n₁) (w : List I) :
    (disjointUnion M₁ M₂).run (inlFin s) w = inlFin (M₁.run s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons a ws ih =>
    simp only [MooreMachine.run, disjointUnion, inlFin, s.isLt, ↓reduceDIte]
    exact ih (M₁.step s a)

private theorem run_disjointUnion_inr {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂)
    (s : Fin n₂) (w : List I) :
    (disjointUnion M₁ M₂).run (inrFin s) w = inrFin (M₂.run s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons a ws ih =>
    have hnot : ¬ (n₁ + s.val < n₁) := by omega
    simp only [MooreMachine.run, disjointUnion, inrFin, hnot, ↓reduceDIte]
    have hsub : (⟨n₁ + s.val - n₁, by omega⟩ : Fin n₂) = s := by
      apply Fin.ext; simp
    rw [hsub]
    exact ih (M₂.step s a)

theorem behavior_disjointUnion_inl {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂)
    (s : Fin n₁) (w : List I) :
    (disjointUnion M₁ M₂).behavior (inlFin s) w = M₁.toMooreMachine.behavior s w := by
  unfold MooreMachine.behavior
  rw [run_disjointUnion_inl]
  simp only [disjointUnion, inlFin, (M₁.run s w).isLt, ↓reduceDIte]

theorem behavior_disjointUnion_inr {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂)
    (s : Fin n₂) (w : List I) :
    (disjointUnion M₁ M₂).behavior (inrFin s) w = M₂.toMooreMachine.behavior s w := by
  unfold MooreMachine.behavior
  rw [run_disjointUnion_inr]
  simp only [disjointUnion, inrFin]
  have hnot : ¬ (n₁ + (M₂.run s w).val < n₁) := by omega
  simp only [hnot, ↓reduceDIte]
  have hsub : (⟨n₁ + (M₂.run s w).val - n₁, by omega⟩ : Fin n₂) = M₂.run s w := by
    apply Fin.ext; simp
  rw [hsub]

/-! ### Delay Chain Machine (Sharpness of `n - 2`) -/

/-- `n`-state unary Moore machine over `Unit → Bool` whose transitions form a
saturating chain `0 → 1 → … → n - 1 → n - 1` and whose sole accepting state is
`n - 1`. -/
def delayChain (n : Nat) : MooreMachine Unit Bool (Fin n) where
  step i _ := if h : i.val + 1 < n then ⟨i.val + 1, h⟩ else i
  out i := decide (i.val + 1 = n)

private theorem delayChain_run_val {n : Nat} (s : Fin n) (w : List Unit) :
    ((delayChain n).run s w).val = min (s.val + w.length) (n - 1) := by
  induction w generalizing s with
  | nil =>
    simp only [MooreMachine.run, List.length_nil, Nat.add_zero]
    have := s.isLt
    omega
  | cons a ws ih =>
    simp only [MooreMachine.run, List.length_cons]
    rw [ih]
    simp only [delayChain]
    split
    · rename_i hlt
      simp only
      omega
    · rename_i hge
      have := s.isLt
      omega

/-! ### Two-Machine Sharpness Construction (`modCycleMachine` & `mimicSaturateMachine`) -/

/-- `(m₁ + 1)`-state unary cycle `0 → 1 → … → m₁ → 0` that outputs `true` only
at residue `(m₁ + m₂) % (m₁ + 1)`. Paired with `mimicSaturateMachine m₁ m₂`,
their first distinguishing word has exact length `m₁ + m₂ = (m₁ + 1) + (m₂ + 1) - 2`. -/
def modCycleMachine (m₁ m₂ : Nat) : InitMooreMachine Unit Bool (m₁ + 1) where
  step s _ := ⟨(s.val + 1) % (m₁ + 1), Nat.mod_lt _ (Nat.succ_pos m₁)⟩
  out s := decide (s.val = (m₁ + m₂) % (m₁ + 1))
  init := ⟨0, Nat.succ_pos m₁⟩

/-- `(m₂ + 1)`-state unary saturating chain `0 → 1 → … → m₂ → m₂` that mimics
`modCycleMachine m₁ m₂` on states `0, …, m₂ - 1` and outputs `false` at the
absorbing state `m₂`. -/
def mimicSaturateMachine (m₁ m₂ : Nat) : InitMooreMachine Unit Bool (m₂ + 1) where
  step s _ := if h : s.val + 1 < m₂ + 1 then ⟨s.val + 1, h⟩ else s
  out s := if s.val < m₂ then decide (s.val % (m₁ + 1) = (m₁ + m₂) % (m₁ + 1)) else false
  init := ⟨0, Nat.succ_pos m₂⟩

private theorem modCycleMachine_run_val (m₁ m₂ : Nat) (s : Fin (m₁ + 1)) (w : List Unit) :
    ((modCycleMachine m₁ m₂).run s w).val = (s.val + w.length) % (m₁ + 1) := by
  induction w generalizing s with
  | nil =>
    simp only [MooreMachine.run, List.length_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt s.isLt).symm
  | cons _ ws ih =>
    simp only [MooreMachine.run, List.length_cons]
    rw [ih]
    simp only [modCycleMachine]
    rw [Nat.mod_add_mod]
    congr 1
    omega

private theorem modCycleMachine_behavior (m₁ m₂ : Nat) (w : List Unit) :
    (modCycleMachine m₁ m₂).behavior w =
      decide (w.length % (m₁ + 1) = (m₁ + m₂) % (m₁ + 1)) := by
  simp only [InitMooreMachine.behavior, MooreMachine.behavior]
  have h := modCycleMachine_run_val m₁ m₂ (modCycleMachine m₁ m₂).init w
  change decide (((modCycleMachine m₁ m₂).run (modCycleMachine m₁ m₂).init w).val =
    (m₁ + m₂) % (m₁ + 1)) = _
  rw [h]
  simp [modCycleMachine]

private theorem mimicSaturateMachine_run_val (m₁ m₂ : Nat) (s : Fin (m₂ + 1)) (w : List Unit) :
    ((mimicSaturateMachine m₁ m₂).run s w).val = min (s.val + w.length) m₂ := by
  induction w generalizing s with
  | nil =>
    simp only [MooreMachine.run, List.length_nil, Nat.add_zero]
    have := s.isLt
    omega
  | cons _ ws ih =>
    simp only [MooreMachine.run, List.length_cons]
    rw [ih]
    simp only [mimicSaturateMachine]
    split
    · rename_i hlt
      simp only
      omega
    · rename_i hge
      have := s.isLt
      omega

private theorem mimicSaturateMachine_behavior (m₁ m₂ : Nat) (w : List Unit) :
    (mimicSaturateMachine m₁ m₂).behavior w =
      if min w.length m₂ < m₂ then
        decide ((min w.length m₂) % (m₁ + 1) = (m₁ + m₂) % (m₁ + 1))
      else
        false := by
  simp only [InitMooreMachine.behavior, MooreMachine.behavior]
  have h := mimicSaturateMachine_run_val m₁ m₂ (mimicSaturateMachine m₁ m₂).init w
  change (if ((mimicSaturateMachine m₁ m₂).run (mimicSaturateMachine m₁ m₂).init w).val < m₂ then
      decide (((mimicSaturateMachine m₁ m₂).run (mimicSaturateMachine m₁ m₂).init w).val % (m₁ + 1) =
        (m₁ + m₂) % (m₁ + 1))
    else false) = _
  rw [h]
  simp [mimicSaturateMachine]

private theorem mod_ne_of_sub_lt (t T n : Nat) (hlt : t < T) (hdiff : T - t < n) :
    t % n ≠ T % n := by
  intro heq
  have hpos : 0 < n := by omega
  have hd_pos : 0 < T - t := by omega
  have hT : T = t + (T - t) := by omega
  rw [hT, Nat.add_mod] at heq
  have hmod_d : (T - t) % n = T - t := Nat.mod_eq_of_lt hdiff
  rw [hmod_d] at heq
  have htlt : t % n < n := Nat.mod_lt t hpos
  by_cases hsum : t % n + (T - t) < n
  · rw [Nat.mod_eq_of_lt hsum] at heq
    omega
  · have hge : n ≤ t % n + (T - t) := by omega
    have hlt2 : t % n + (T - t) - n < n := by omega
    have hmod_sub : (t % n + (T - t)) % n = t % n + (T - t) - n := by
      have := Nat.mod_eq_sub_mod hge
      rw [this, Nat.mod_eq_of_lt hlt2]
    rw [hmod_sub] at heq
    omega

/-! ### Concrete Helper Machines & Elementary Pigeonhole -/

/-- 1-state Moore machine always outputting `y`. -/
def constMoore {I : Type u} {O : Type v} (y : O) : InitMooreMachine I O 1 where
  step s _ := s
  out _ := y
  init := ⟨0, by decide⟩

theorem constMoore_behavior {I : Type u} {O : Type v} (y : O) (w : List I) :
    (constMoore y : InitMooreMachine I O 1).behavior w = y := by
  simp only [InitMooreMachine.behavior, MooreMachine.behavior, constMoore]

/-- 2-state unary Moore machine alternating `false, true, false, true, …`. -/
def altMachine2 : InitMooreMachine Unit Bool 2 where
  step s _ := if s.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩
  out s := decide (s.val = 1)
  init := ⟨0, by decide⟩

/-- 2-state unary Moore machine outputting `false, true, true, true, …`. -/
def latchMachine2 : InitMooreMachine Unit Bool 2 where
  step _ _ := ⟨1, by decide⟩
  out s := decide (s.val = 1)
  init := ⟨0, by decide⟩

private theorem altMachine2_run_val (s : Fin 2) (w : List Unit) :
    (altMachine2.run s w).val = (s.val + w.length) % 2 := by
  induction w generalizing s with
  | nil =>
    simp only [MooreMachine.run, List.length_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt s.isLt).symm
  | cons _ ws ih =>
    simp only [MooreMachine.run, List.length_cons]
    rw [ih]
    match s with
    | ⟨0, _⟩ => simp [altMachine2]; omega
    | ⟨1, _⟩ => simp [altMachine2]; omega

theorem altMachine2_behavior (w : List Unit) :
    altMachine2.behavior w = decide (w.length % 2 = 1) := by
  simp only [InitMooreMachine.behavior, MooreMachine.behavior, altMachine2]
  have h := altMachine2_run_val ⟨0, by decide⟩ w
  simpa [altMachine2] using congrArg (fun k => decide (k = 1)) h

private theorem pigeonhole_fin :
    ∀ (n : Nat) (f : Fin (n + 1) → Fin n),
      ∃ i j : Fin (n + 1), i ≠ j ∧ f i = f j := by
  intro n
  induction n with
  | zero =>
    intro f
    exact Fin.elim0 (f ⟨0, Nat.zero_lt_succ 0⟩)
  | succ n ih =>
    intro f
    by_cases hex : ∃ i : Fin (n + 1), f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = f ⟨n + 1, Nat.lt_succ_self _⟩
    · rcases hex with ⟨i, hi⟩
      refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ⟨n + 1, Nat.lt_succ_self _⟩, ?_, hi⟩
      intro heq
      have hval := congrArg Fin.val heq
      exact Nat.ne_of_lt i.isLt hval
    · let last := f ⟨n + 1, Nat.lt_succ_self _⟩
      let g : Fin (n + 1) → Fin n := fun i =>
        let y := f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
        if hlt : y.val < last.val then
          ⟨y.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ last.isLt)⟩
        else
          have hne : y ≠ last := fun heq => hex ⟨i, heq⟩
          have hgt : last.val < y.val := by
            have hneval : y.val ≠ last.val := fun hv => hne (Fin.ext hv)
            omega
          ⟨y.val - 1, by have := y.isLt; omega⟩
      rcases ih g with ⟨i, j, hij, hgeq⟩
      refine ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, ?_, ?_⟩
      · intro heq
        have hv : i.val = j.val := congrArg (fun x : Fin (n + 2) => x.val) heq
        exact hij (Fin.ext hv)
      · have hval : (g i).val = (g j).val := congrArg Fin.val hgeq
        dsimp only [g] at hval
        have hnei : f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠ last := fun heq => hex ⟨i, heq⟩
        have hnej : f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ ≠ last := fun heq => hex ⟨j, heq⟩
        have hnevi : (f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).val ≠ last.val := fun hv => hnei (Fin.ext hv)
        have hnevj : (f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩).val ≠ last.val := fun hv => hnej (Fin.ext hv)
        apply Fin.ext
        split at hval <;> split at hval <;> dsimp only at hval <;> omega

/-! ### Definition Positive and Negative Examples -/

theorem stateEquiv_pos_example :
    let M : MooreMachine Unit Bool (Fin 2) := { step := fun s _ => s, out := fun _ => false }
    StateEquiv M ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  funext w
  simp [MooreMachine.behavior]

theorem stateEquiv_neg_example :
    let M : MooreMachine Unit Bool (Fin 2) :=
      { step := fun s _ => s, out := fun s => decide (s.val = 1) }
    ¬ StateEquiv M ⟨0, by decide⟩ ⟨1, by decide⟩ := by
  dsimp only
  intro heq
  have h := congrFun heq []
  cases h

theorem agreeUpTo_pos_example :
    AgreeUpTo (delayChain 3) ⟨0, by decide⟩ ⟨1, by decide⟩ 0 := by
  intro w hw
  cases w with
  | nil => decide
  | cons _ _ => simp at hw

theorem agreeUpTo_neg_example :
    ¬ AgreeUpTo (delayChain 3) ⟨0, by decide⟩ ⟨1, by decide⟩ 1 := by
  intro hAgree
  have h := hAgree [()] (by decide)
  cases h

theorem boundedMooreBehaviors_pos_example :
    BoundedMooreBehaviors Unit Bool 1 (fun _ => false) :=
  ⟨1, Nat.le_refl 1, constMoore false, funext (constMoore_behavior false)⟩

theorem boundedMooreBehaviors_neg_example :
    ¬ BoundedMooreBehaviors Unit Bool 1 (fun w => decide (1 ≤ w.length)) := by
  rintro ⟨m, hm, M, hM⟩
  have hm1 : m = 1 := by
    have hpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) M.init.isLt
    omega
  subst hm1
  have h0 := congrFun hM []
  have h1 := congrFun hM [()]
  simp only [InitMooreMachine.behavior, MooreMachine.behavior, MooreMachine.run] at h0 h1
  have hstep : M.step M.init () = M.init := by
    apply Fin.ext
    have hlt1 := (M.step M.init ()).isLt
    have hlt2 := M.init.isLt
    omega
  rw [hstep, h0] at h1
  cases h1

theorem finiteStateMooreBehaviors_pos_example :
    FiniteStateMooreBehaviors Unit Bool (fun _ => false) :=
  ⟨1, constMoore false, funext (constMoore_behavior false)⟩

private theorem count_false_replicate (a b : Nat) :
    (List.replicate a false ++ List.replicate b true).count false = a := by
  rw [List.count_append, List.count_replicate, List.count_replicate]
  simp

private theorem count_true_replicate (a b : Nat) :
    (List.replicate a false ++ List.replicate b true).count true = b := by
  rw [List.count_append, List.count_replicate, List.count_replicate]
  simp

/-- Myhill-Nerode negative example for `FiniteStateMooreBehaviors`: checking
whether a Boolean word contains equally many `false` and `true` symbols is not
realizable by any finite-state Moore machine. -/
theorem finiteStateMooreBehaviors_neg_example :
    ¬ FiniteStateMooreBehaviors Bool Bool
        (fun w => decide (w.count false = w.count true)) := by
  rintro ⟨n, M, hM⟩
  let f : Fin (n + 1) → Fin n := fun i => M.run M.init (List.replicate i.val false)
  rcases pigeonhole_fin n f with ⟨i, j, hij, hfeq⟩
  have hbehEq :
      M.behavior (List.replicate i.val false ++ List.replicate i.val true) =
      M.behavior (List.replicate j.val false ++ List.replicate i.val true) := by
    simp only [InitMooreMachine.behavior, MooreMachine.behavior, MooreMachine.run_append]
    exact congrArg (fun s => M.out (M.run s (List.replicate i.val true))) hfeq
  rw [hM] at hbehEq
  dsimp only at hbehEq
  rw [count_false_replicate, count_true_replicate,
      count_false_replicate, count_true_replicate] at hbehEq
  have htrue : decide (i.val = i.val) = true := decide_eq_true rfl
  rw [htrue] at hbehEq
  have hjne : j.val ≠ i.val := fun hv => hij (Fin.ext hv.symm)
  have hfalse : decide (j.val = i.val) = false := decide_eq_false hjne
  rw [hfalse] at hbehEq
  cases hbehEq

theorem coversAll_pos_example : CoversAll [false, true] := by
  intro b
  cases b <;> simp

theorem coversAll_neg_example : ¬ CoversAll [false] := by
  intro h
  have hmem := h true
  simp at hmem

/-! ### Result 7: Moore's Bound (`≤ n - 2` Input Symbols) -/

private theorem agreeUpTo_refl {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s : S) (k : Nat) :
    AgreeUpTo M s s k :=
  fun _ _ => rfl

private theorem agreeUpTo_symm {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) {s t : S} {k : Nat}
    (h : AgreeUpTo M s t k) : AgreeUpTo M t s k :=
  fun w hw => (h w hw).symm

private theorem agreeUpTo_trans {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) {s t u : S} {k : Nat}
    (h1 : AgreeUpTo M s t k) (h2 : AgreeUpTo M t u k) : AgreeUpTo M s u k :=
  fun w hw => (h1 w hw).trans (h2 w hw)

private theorem agreeUpTo_mono {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) {s t : S} {k₁ k₂ : Nat}
    (hle : k₁ ≤ k₂) (h : AgreeUpTo M s t k₂) : AgreeUpTo M s t k₁ :=
  fun w hw => h w (Nat.le_trans hw hle)

private theorem agreeUpTo_succ_iff {I : Type u} {O : Type v} {S : Type w}
    (M : MooreMachine I O S) (s t : S) (k : Nat) :
    AgreeUpTo M s t (k + 1) ↔
      AgreeUpTo M s t k ∧ ∀ a : I, AgreeUpTo M (M.step s a) (M.step t a) k := by
  constructor
  · intro h
    refine ⟨agreeUpTo_mono M (Nat.le_succ k) h, fun a w hw => ?_⟩
    exact h (a :: w) (by simp only [List.length_cons]; omega)
  · rintro ⟨h0, hstep⟩ w hw
    cases w with
    | nil => exact h0 [] (Nat.zero_le k)
    | cons a ws =>
      simp only [List.length_cons] at hw
      exact hstep a ws (by omega)

private theorem agreeUpTo_stabilize {I : Type u} {O : Type v} {n : Nat}
    (M : MooreMachine I O (Fin n)) (k : Nat)
    (hStab : ∀ u v : Fin n, AgreeUpTo M u v k → AgreeUpTo M u v (k + 1)) :
    ∀ (d : Nat) (u v : Fin n), AgreeUpTo M u v k → AgreeUpTo M u v (k + d) := by
  intro d
  induction d with
  | zero =>
    intro u v huv
    simpa using huv
  | succ d ih =>
    intro u v huv
    have h1 := (agreeUpTo_succ_iff M u v k).mp (hStab u v huv)
    have h2 : AgreeUpTo M u v (k + d) := ih u v huv
    have h3 : ∀ a : I, AgreeUpTo M (M.step u a) (M.step v a) (k + d) :=
      fun a => ih (M.step u a) (M.step v a) (h1.2 a)
    have hsucc : AgreeUpTo M u v ((k + d) + 1) :=
      (agreeUpTo_succ_iff M u v (k + d)).mpr ⟨h2, h3⟩
    simpa [Nat.add_assoc] using hsucc

private theorem nat_exists_min_pred (P : Nat → Prop) (N : Nat) (hN : P N) :
    ∃ K : Nat, K ≤ N ∧ P K ∧ ∀ j : Nat, j < K → ¬ P j := by
  suffices ∀ (M m : Nat), m ≤ M → P m →
      ∃ K : Nat, K ≤ m ∧ P K ∧ ∀ j : Nat, j < K → ¬ P j from
    this N N (Nat.le_refl N) hN
  intro M
  induction M with
  | zero =>
    intro m hm hPm
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨0, Nat.le_refl 0, hPm, fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | succ M ih =>
    intro m hm hPm
    by_cases hmM : m ≤ M
    · exact ih m hmM hPm
    · have hm_eq : m = M + 1 := by omega
      subst hm_eq
      by_cases hex : ∃ j : Nat, j ≤ M ∧ P j
      · rcases hex with ⟨j₀, hj₀, hPj₀⟩
        rcases ih j₀ hj₀ hPj₀ with ⟨K, hKj₀, hPK, hmin⟩
        exact ⟨K, by omega, hPK, hmin⟩
      · refine ⟨M + 1, Nat.le_refl _, hPm, fun j hj hPj => ?_⟩
        exact hex ⟨j, by omega, hPj⟩

private theorem pairwise_erase_of_mem {α : Type w} {R : α → α → Prop}
    {p : α} {P : List α} (hP : P.Pairwise R) (hp : p ∈ P) :
    ∃ Q : List α, Q.length + 1 = P.length ∧ Q.Pairwise R ∧
      (∀ q ∈ Q, q ∈ P) ∧ (∀ q ∈ Q, R p q ∨ R q p) := by
  induction P with
  | nil => cases hp
  | cons x xs ih =>
    rw [List.pairwise_cons] at hP
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hmem
    · exact ⟨xs, rfl, hP.2, fun q hq => by simp [hq], fun q hq => Or.inl (hP.1 q hq)⟩
    · rcases ih hP.2 hmem with ⟨Q, hlen, hQ, hsub, hrel⟩
      refine ⟨x :: Q, by simp [hlen], ?_, ?_, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨fun q hq => hP.1 q (hsub q hq), hQ⟩
      · intro q hq
        simp only [List.mem_cons] at hq ⊢
        rcases hq with rfl | hqQ
        · exact Or.inl rfl
        · exact Or.inr (hsub q hqQ)
      · intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with rfl | hqQ
        · exact Or.inr (hP.1 p hmem)
        · exact hrel q hqQ

private theorem exists_erase_of_mem_fin {n : Nat} (a : Fin n) (B : List (Fin n)) (h : a ∈ B) :
    ∃ B' : List (Fin n), B'.length + 1 = B.length ∧ ∀ b ∈ B, b ≠ a → b ∈ B' := by
  induction B with
  | nil => cases h
  | cons c cs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | hcs
    · refine ⟨cs, rfl, fun b hb hne => ?_⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hmem
      · exact absurd rfl hne
      · exact hmem
    · rcases ih hcs with ⟨cs', hlen, hsub⟩
      refine ⟨c :: cs', by simp [hlen], fun b hb hne => ?_⟩
      simp only [List.mem_cons] at hb ⊢
      rcases hb with rfl | hmem
      · exact Or.inl rfl
      · exact Or.inr (hsub b hmem hne)

private theorem nodup_fin_subset_length_le {n : Nat}
    (A B : List (Fin n)) (hnd : A.Nodup) (hsub : ∀ a ∈ A, a ∈ B) :
    A.length ≤ B.length := by
  induction A generalizing B with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    have haB : a ∈ B := hsub a (by simp)
    rcases exists_erase_of_mem_fin a B haB with ⟨B', hlen, hsubB⟩
    have has : ∀ x ∈ as, x ∈ B' := by
      intro x hx
      have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hx)
      exact hsubB x (hsub x (by simp [hx])) hne
    have hle := ih B' hnd.2 has
    simp only [List.length_cons]
    omega

private theorem grow_ineq_list {I : Type u} {O : Type v} {n : Nat}
    (M : MooreMachine I O (Fin n)) (j : Nat)
    (P : List (Fin n)) (hP : P.Pairwise (fun a b => ¬ AgreeUpTo M a b j))
    (u v : Fin n) (huv_eq : AgreeUpTo M u v j) (huv_neq : ¬ AgreeUpTo M u v (j + 1)) :
    ∃ P' : List (Fin n), P'.length = P.length + 1 ∧
      P'.Pairwise (fun a b => ¬ AgreeUpTo M a b (j + 1)) := by
  have liftIneq : ∀ {a b : Fin n}, ¬ AgreeUpTo M a b j → ¬ AgreeUpTo M a b (j + 1) :=
    fun hnot hsucc => hnot (agreeUpTo_mono M (Nat.le_succ j) hsucc)
  by_cases hex : ∃ p ∈ P, AgreeUpTo M u p j
  · rcases hex with ⟨p, hpP, hup⟩
    rcases pairwise_erase_of_mem hP hpP with ⟨Q, hQlen, hQpair, _, hQrel⟩
    have hQrel' : ∀ q ∈ Q, ¬ AgreeUpTo M p q j := by
      intro q hq
      rcases hQrel q hq with h1 | h2
      · exact h1
      · exact fun h => h2 (agreeUpTo_symm M h)
    have hQ_succ : Q.Pairwise (fun a b => ¬ AgreeUpTo M a b (j + 1)) :=
      hQpair.imp (fun h => liftIneq h)
    have hv_Q : ∀ q ∈ Q, ¬ AgreeUpTo M v q (j + 1) := by
      intro q hq hvq
      apply hQrel' q hq
      exact agreeUpTo_trans M (agreeUpTo_symm M hup)
        (agreeUpTo_trans M huv_eq (agreeUpTo_mono M (Nat.le_succ j) hvq))
    have hu_Q : ∀ q ∈ Q, ¬ AgreeUpTo M u q (j + 1) := by
      intro q hq huq
      apply hQrel' q hq
      exact agreeUpTo_trans M (agreeUpTo_symm M hup) (agreeUpTo_mono M (Nat.le_succ j) huq)
    refine ⟨u :: v :: Q, by simp only [List.length_cons]; omega, ?_⟩
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hqQ
      · exact huv_neq
      · exact hu_Q q hqQ
    · rw [List.pairwise_cons]
      exact ⟨hv_Q, hQ_succ⟩
  · refine ⟨u :: P, by simp, ?_⟩
    rw [List.pairwise_cons]
    refine ⟨?_, hP.imp (fun h => liftIneq h)⟩
    intro p hp hup
    exact hex ⟨p, hp, agreeUpTo_mono M (Nat.le_succ j) hup⟩

/-- Moore's distinguishability bound for deterministic Moore machines: two
states of an `n`-state Moore machine are behaviorally equivalent if and only if
they agree on all input words of length at most `n - 2` (equivalently,
agreement on all words of length `< n` suffices, see
`moore_state_equiv_iff_agree_lt_n`). -/
theorem moore_state_equiv_iff_agree_up_to
    {I : Type u} {O : Type v} {n : Nat}
    (M : MooreMachine I O (Fin n)) (s t : Fin n) :
    StateEquiv M s t ↔ AgreeUpTo M s t (n - 2) := by
  constructor
  · intro heq w _
    exact congrFun heq w
  · intro hAgree
    apply Classical.byContradiction
    intro hNotEq
    have hDiffW : ∃ w : List I, M.behavior s w ≠ M.behavior t w := by
      apply Classical.byContradiction
      intro hno
      apply hNotEq
      funext w
      apply Classical.byContradiction
      intro hne
      exact hno ⟨w, hne⟩
    rcases hDiffW with ⟨w, hw⟩
    have hNotLen : ¬ AgreeUpTo M s t w.length := fun hA => hw (hA w (Nat.le_refl _))
    rcases nat_exists_min_pred (fun k => ¬ AgreeUpTo M s t k) w.length hNotLen with
      ⟨K, _, hNotK, hBelow⟩
    have hChain : ∀ j : Nat, j ≤ K →
        ∃ P : List (Fin n), P.length = j + 2 ∧ P.Pairwise (fun a b => ¬ AgreeUpTo M a b j) := by
      intro j
      induction j with
      | zero =>
        intro _
        let u0 := M.run s w
        let v0 := M.run t w
        have huv0 : ¬ AgreeUpTo M u0 v0 0 := by
          intro hA
          have heq0 := hA [] (Nat.zero_le 0)
          exact hw heq0
        refine ⟨[u0, v0], rfl, ?_⟩
        rw [List.pairwise_cons]
        refine ⟨?_, by simp⟩
        intro b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        exact huv0
      | succ j ih =>
        intro hjK
        rcases ih (Nat.le_of_succ_le hjK) with ⟨P, hPlen, hPpair⟩
        have hSplit : ∃ u v : Fin n, AgreeUpTo M u v j ∧ ¬ AgreeUpTo M u v (j + 1) := by
          apply Classical.byContradiction
          intro hno
          have hStab : ∀ u v : Fin n, AgreeUpTo M u v j → AgreeUpTo M u v (j + 1) := by
            intro u v huv
            apply Classical.byContradiction
            intro hnot
            exact hno ⟨u, v, huv, hnot⟩
          have hj_lt : j < K := by omega
          have hAgj : AgreeUpTo M s t j := by
            apply Classical.byContradiction
            intro hnot
            exact hBelow j hj_lt hnot
          have hAgK : AgreeUpTo M s t (j + (K - j)) :=
            agreeUpTo_stabilize M j hStab (K - j) s t hAgj
          have hKeq : j + (K - j) = K := by omega
          rw [hKeq] at hAgK
          exact hNotK hAgK
        rcases hSplit with ⟨u, v, huv_eq, huv_neq⟩
        rcases grow_ineq_list M j P hPpair u v huv_eq huv_neq with ⟨P', hP'len, hP'pair⟩
        exact ⟨P', by omega, hP'pair⟩
    rcases hChain K (Nat.le_refl K) with ⟨PK, hPKlen, hPKpair⟩
    have hPKnd : PK.Nodup :=
      hPKpair.imp (fun hne (heq : _ = _) => hne (by subst heq; exact agreeUpTo_refl M _ K))
    have hPKle : PK.length ≤ (List.finRange n).length :=
      nodup_fin_subset_length_le PK (List.finRange n) hPKnd (fun x _ => List.mem_finRange x)
    rw [hPKlen, List.length_finRange] at hPKle
    have hKle : K ≤ n - 2 := by omega
    exact hNotK (agreeUpTo_mono M hKle hAgree)

/-- Non-vacuity witness for `moore_state_equiv_iff_agree_up_to` covering both
directions on non-constant 3-state machines without invoking the general
theorem:
1. on a 3-state alternating machine whose distinct states `0` and `1` both step
   to `2` (`out = [F, F, T]`), `StateEquiv` and `AgreeUpTo _ _ (3 - 2)` both
   hold while outputs are non-constant;
2. on `delayChain 3`, states `0` and `1` satisfy neither `StateEquiv` nor
   `AgreeUpTo _ _ (3 - 2)` (companion sharpness in `moore_bound_sharp`). -/
theorem moore_state_equiv_iff_agree_up_to_nonvacuity :
    let M : MooreMachine Unit Bool (Fin 3) :=
      { step := fun s _ => if s.val = 2 then ⟨0, by decide⟩ else ⟨2, by decide⟩
        out := fun s => decide (s.val = 2) }
    M.behavior ⟨0, by decide⟩ [] ≠ M.behavior ⟨0, by decide⟩ [()] ∧
    StateEquiv M ⟨0, by decide⟩ ⟨1, by decide⟩ ∧
    AgreeUpTo M ⟨0, by decide⟩ ⟨1, by decide⟩ (3 - 2) ∧
    ¬ StateEquiv (delayChain 3) ⟨0, by decide⟩ ⟨1, by decide⟩ ∧
    ¬ AgreeUpTo (delayChain 3) ⟨0, by decide⟩ ⟨1, by decide⟩ (3 - 2) := by
  let M : MooreMachine Unit Bool (Fin 3) :=
    { step := fun s _ => if s.val = 2 then ⟨0, by decide⟩ else ⟨2, by decide⟩
      out := fun s => decide (s.val = 2) }
  have hEq : StateEquiv M ⟨0, by decide⟩ ⟨1, by decide⟩ := by
    funext w
    cases w with
    | nil => rfl
    | cons _ ws => rfl
  refine ⟨by decide, hEq, fun w _ => congrFun hEq w, ?_, agreeUpTo_neg_example⟩
  intro hSe
  exact agreeUpTo_neg_example (fun w _ => congrFun hSe w)

/-- Immediate consequence of `moore_state_equiv_iff_agree_up_to` in strict-`< n`
word-length form. -/
theorem moore_state_equiv_iff_agree_lt_n
    {I : Type u} {O : Type v} {n : Nat}
    (M : MooreMachine I O (Fin n)) (s t : Fin n) :
    StateEquiv M s t ↔ ∀ w : List I, w.length < n → M.behavior s w = M.behavior t w := by
  constructor
  · intro heq w _
    exact congrFun heq w
  · intro hlt
    rw [moore_state_equiv_iff_agree_up_to]
    intro w hw
    have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
    by_cases hn1 : n = 1
    · subst hn1
      have hst : s = t := Fin.ext (by have := s.isLt; have := t.isLt; omega)
      rw [hst]
    · exact hlt w (by omega)

/-! ### Result 8: Two-Machine Form of Moore's Bound (Derived from Result 7) -/

/-- Two-machine form of Moore's bound: initialized deterministic Moore machines
`M₁` (`n₁` states) and `M₂` (`n₂` states) are behaviorally equal if and only if
they agree on all input words of length at most `n₁ + n₂ - 2`. -/
theorem moore_two_machine_equiv_iff_agree_up_to
    {I : Type u} {O : Type v} {n₁ n₂ : Nat}
    (M₁ : InitMooreMachine I O n₁) (M₂ : InitMooreMachine I O n₂) :
    M₁.behavior = M₂.behavior ↔
    ∀ w : List I, w.length ≤ n₁ + n₂ - 2 → M₁.behavior w = M₂.behavior w := by
  have hEq :
      M₁.behavior = M₂.behavior ↔
      StateEquiv (disjointUnion M₁ M₂) (inlFin M₁.init) (inrFin M₂.init) := by
    constructor
    · intro h
      funext w
      rw [behavior_disjointUnion_inl, behavior_disjointUnion_inr]
      exact congrFun h w
    · intro h
      funext w
      have hw := congrFun h w
      rw [behavior_disjointUnion_inl, behavior_disjointUnion_inr] at hw
      exact hw
  rw [hEq, moore_state_equiv_iff_agree_up_to]
  constructor
  · intro hAgree w hw
    have hw' := hAgree w hw
    rw [behavior_disjointUnion_inl, behavior_disjointUnion_inr] at hw'
    exact hw'
  · intro hAgree w hw
    rw [behavior_disjointUnion_inl, behavior_disjointUnion_inr]
    exact hAgree w hw

/-- Non-vacuity witness for `moore_two_machine_equiv_iff_agree_up_to`: two
distinctly sized initialized Moore machines (`1` state and `2` states) with
identical all-`false` behavior, verified directly without invoking Moore's
general theorem. -/
theorem moore_two_machine_equiv_iff_agree_up_to_nonvacuity :
    let M₁ : InitMooreMachine Unit Bool 1 := constMoore false
    let M₂ : InitMooreMachine Unit Bool 2 :=
      { step := fun s _ => s, out := fun _ => false, init := ⟨0, by decide⟩ }
    M₁.behavior = M₂.behavior ∧
    (∀ w : List Unit, w.length ≤ 1 + 2 - 2 → M₁.behavior w = M₂.behavior w) := by
  have heq : (constMoore false : InitMooreMachine Unit Bool 1).behavior =
      ({ step := fun s _ => s, out := fun _ => false, init := ⟨0, by decide⟩ } :
        InitMooreMachine Unit Bool 2).behavior := by
    funext w
    simp [InitMooreMachine.behavior, MooreMachine.behavior, constMoore]
  exact ⟨heq, fun w _ => congrFun heq w⟩

/-! ### Result 9: Sharpness of `n - 2` (`delayChain n`) -/

/-- Sharpness of Moore's `n - 2` bound: for every `n ≥ 2`, states `0` and `1`
of the `n`-state delay chain `delayChain n` agree on every input word of length
strictly less than `n - 2`, yet disagree on the word of length `n - 2`. -/
theorem moore_bound_sharp (n : Nat) (hn : 2 ≤ n) :
    ∃ (s₀ s₁ : Fin n), s₀.val = 0 ∧ s₁.val = 1 ∧
    (∀ w : List Unit, w.length < n - 2 →
      (delayChain n).behavior s₀ w = (delayChain n).behavior s₁ w) ∧
    (delayChain n).behavior s₀ (List.replicate (n - 2) ()) ≠
      (delayChain n).behavior s₁ (List.replicate (n - 2) ()) ∧
    ¬ StateEquiv (delayChain n) s₀ s₁ := by
  let s₀ : Fin n := ⟨0, by omega⟩
  let s₁ : Fin n := ⟨1, by omega⟩
  have hs0 : s₀.val = 0 := rfl
  have hs1 : s₁.val = 1 := rfl
  have hAgree : ∀ w : List Unit, w.length < n - 2 →
      (delayChain n).behavior s₀ w = (delayChain n).behavior s₁ w := by
    intro w hw
    change decide (((delayChain n).run s₀ w).val + 1 = n) =
      decide (((delayChain n).run s₁ w).val + 1 = n)
    have h0 := delayChain_run_val s₀ w
    have h1 := delayChain_run_val s₁ w
    have hlt0 : ((delayChain n).run s₀ w).val + 1 ≠ n := by omega
    have hlt1 : ((delayChain n).run s₁ w).val + 1 ≠ n := by omega
    rw [decide_eq_false hlt0, decide_eq_false hlt1]
  have hDiff : (delayChain n).behavior s₀ (List.replicate (n - 2) ()) ≠
      (delayChain n).behavior s₁ (List.replicate (n - 2) ()) := by
    change decide (((delayChain n).run s₀ (List.replicate (n - 2) ())).val + 1 = n) ≠
      decide (((delayChain n).run s₁ (List.replicate (n - 2) ())).val + 1 = n)
    have h0 := delayChain_run_val s₀ (List.replicate (n - 2) ())
    have h1 := delayChain_run_val s₁ (List.replicate (n - 2) ())
    have hlen : (List.replicate (n - 2) ()).length = n - 2 := List.length_replicate
    have hf0 : ((delayChain n).run s₀ (List.replicate (n - 2) ())).val + 1 ≠ n := by omega
    have ht1 : ((delayChain n).run s₁ (List.replicate (n - 2) ())).val + 1 = n := by omega
    rw [decide_eq_false hf0, decide_eq_true ht1]
    decide
  exact ⟨s₀, s₁, hs0, hs1, hAgree, hDiff,
    fun heq => hDiff (congrFun heq (List.replicate (n - 2) ()))⟩

/-- Non-vacuity witness for `moore_bound_sharp` at `n = 3`. -/
theorem moore_bound_sharp_nonvacuity : 2 ≤ (3 : Nat) := by decide

/-- Canonical tightness counterexample for `hn : 2 ≤ n` in `moore_bound_sharp`:
for `n = 1`, `Fin 1` has only one state, so every pair of states is equivalent
and the conclusion of `moore_bound_sharp` at `n = 1` fails. -/
theorem moore_bound_sharp_ce_small_n :
    ¬ (2 ≤ (1 : Nat)) ∧
    ¬ (∃ (s₀ s₁ : Fin 1), s₀.val = 0 ∧ s₁.val = 1 ∧
        (∀ w : List Unit, w.length < 1 - 2 →
          (delayChain 1).behavior s₀ w = (delayChain 1).behavior s₁ w) ∧
        (delayChain 1).behavior s₀ (List.replicate (1 - 2) ()) ≠
          (delayChain 1).behavior s₁ (List.replicate (1 - 2) ()) ∧
        ¬ StateEquiv (delayChain 1) s₀ s₁) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨s₀, s₁, _, _, _, _, hne⟩
  have hEq : s₀ = s₁ := Fin.ext (by have := s₀.isLt; have := s₁.isLt; omega)
  subst hEq
  exact hne rfl

/-! ### Results 10 & 11: Finite Test-Suite Completeness for Bounded-State Moore Machines -/

/-- Certification without the target-membership hypothesis: over a finite input
alphabet enumerated by `alphabet`, for any `n₁`-state specification machine `M`,
`mooreSpecTestSuite alphabet M k₂` is consistent with `M.behavior` and uniquely
certifies `M.behavior` among all behaviors in `BoundedMooreBehaviors I O k₂`
(even if `M.behavior` itself requires more than `k₂` states). -/
theorem finite_alphabet_bounded_moore_spec_suite_certifies
    {I : Type u} {O : Type v} {n₁ : Nat}
    (alphabet : List I) (M : InitMooreMachine I O n₁) (k₂ : Nat)
    (hCover : CoversAll alphabet) :
    Consistent (mooreSpecTestSuite alphabet M k₂) M.behavior ∧
    UniqueConsistent (BoundedMooreBehaviors I O k₂) M.behavior
      (mooreSpecTestSuite alphabet M k₂) := by
  refine ⟨consistent_labelSample M.behavior _, ?_⟩
  intro g hg hcon
  rcases hg with ⟨m₂, hm₂, M₂, rfl⟩
  symm
  rw [moore_two_machine_equiv_iff_agree_up_to M M₂]
  intro w hw
  have hle : w.length ≤ n₁ + k₂ - 2 := by omega
  have hmemW : w ∈ wordsUpTo alphabet (n₁ + k₂ - 2) :=
    (mem_wordsUpTo_iff hCover _ w).mpr hle
  exact ((consistent_labelSample_iff M.behavior M₂.behavior _).mp hcon w hmemW).symm

/-- Bounded-state test-suite completeness (asymmetric specification/implementation
state bounds): over a finite input alphabet enumerated by `alphabet`, for any
`n₁`-state specification machine `M` whose behavior belongs to
`BoundedMooreBehaviors I O k₂`, the explicit finite labeled suite
`mooreSpecTestSuite alphabet M k₂` (all words of length at most `n₁ + k₂ - 2`)
teaches `M.behavior` within `BoundedMooreBehaviors I O k₂`. Derived from
`finite_alphabet_bounded_moore_spec_suite_certifies` (and `hMem` is needed only
for the membership conjunct of `Teaches`). -/
theorem finite_alphabet_bounded_moore_spec_suite_teaches
    {I : Type u} {O : Type v} {n₁ : Nat}
    (alphabet : List I) (M : InitMooreMachine I O n₁) (k₂ : Nat)
    (hCover : CoversAll alphabet)
    (hMem : BoundedMooreBehaviors I O k₂ M.behavior) :
    Teaches (BoundedMooreBehaviors I O k₂) M.behavior
      (mooreSpecTestSuite alphabet M k₂) :=
  let hCert := finite_alphabet_bounded_moore_spec_suite_certifies alphabet M k₂ hCover
  ⟨hMem, hCert.1, hCert.2⟩

/-- Universal bounded-state test-suite completeness (corollary of
`moore_two_machine_equiv_iff_agree_up_to`): over a finite input alphabet
enumerated by `alphabet`, every behavior `h` realizable by a Moore machine with
at most `k` states is taught within `BoundedMooreBehaviors I O k` by
`mooreClassTestSuite alphabet k h` (all words of length at most `2 * k - 2`). -/
theorem finite_alphabet_bounded_moore_class_suite_teaches
    {I : Type u} {O : Type v}
    (alphabet : List I) (k : Nat) (h : List I → O)
    (hCover : CoversAll alphabet)
    (hMem : BoundedMooreBehaviors I O k h) :
    Teaches (BoundedMooreBehaviors I O k) h (mooreClassTestSuite alphabet k h) := by
  rcases hMem with ⟨n₁, hn₁, M, rfl⟩
  refine ⟨⟨n₁, hn₁, M, rfl⟩, consistent_labelSample M.behavior _, ?_⟩
  intro g hg hcon
  rcases hg with ⟨m₂, hm₂, M₂, rfl⟩
  symm
  rw [moore_two_machine_equiv_iff_agree_up_to M M₂]
  intro w hw
  have hle : w.length ≤ 2 * k - 2 := by omega
  have hmemW : w ∈ wordsUpTo alphabet (2 * k - 2) :=
    (mem_wordsUpTo_iff hCover _ w).mpr hle
  exact ((consistent_labelSample_iff M.behavior M₂.behavior _).mp hcon w hmemW).symm

/-- Non-vacuity witness for `finite_alphabet_bounded_moore_spec_suite_teaches`. -/
theorem finite_alphabet_bounded_moore_spec_suite_teaches_nonvacuity :
    CoversAll ([()] : List Unit) ∧
    BoundedMooreBehaviors Unit Bool 2 altMachine2.behavior :=
  ⟨fun u => by cases u; simp, ⟨2, Nat.le_refl 2, altMachine2, rfl⟩⟩

/-- Non-vacuity witness for `finite_alphabet_bounded_moore_class_suite_teaches`. -/
theorem finite_alphabet_bounded_moore_class_suite_teaches_nonvacuity :
    CoversAll ([()] : List Unit) ∧
    BoundedMooreBehaviors Unit Bool 2 altMachine2.behavior :=
  finite_alphabet_bounded_moore_spec_suite_teaches_nonvacuity

/-- 2-state Moore machine over `Bool` that outputs `true` iff input `true` has
ever been seen. -/
private def seenTrueMachine : InitMooreMachine Bool Bool 2 where
  step s a := if a then ⟨1, by decide⟩ else s
  out s := decide (s.val = 1)
  init := ⟨0, by decide⟩

private theorem seenTrueMachine_all_false (w : List Bool)
    (honly : ∀ b ∈ w, b = false) :
    seenTrueMachine.behavior w = false := by
  have hrun : ∀ (u : List Bool), (∀ b ∈ u, b = false) →
      seenTrueMachine.run ⟨0, by decide⟩ u = ⟨0, by decide⟩ := by
    intro u
    induction u with
    | nil => intro _; rfl
    | cons a us ih =>
      intro hall
      have ha : a = false := hall a (by simp)
      subst ha
      exact ih (fun b hb => hall b (by simp [hb]))
  change seenTrueMachine.out (seenTrueMachine.run ⟨0, by decide⟩ w) = false
  rw [hrun w honly]
  decide

private theorem mem_wordsUpTo_false_only (L : Nat) (w : List Bool)
    (hw : w ∈ wordsUpTo [false] L) : ∀ b ∈ w, b = false := by
  have hlen : ∀ (k : Nat) (u : List Bool), u ∈ wordsOfLength [false] k →
      ∀ b ∈ u, b = false := by
    intro k
    induction k with
    | zero =>
      intro u hu b hb
      simp [wordsOfLength] at hu
      subst hu; cases hb
    | succ k ih =>
      intro u hu b hb
      simp only [wordsOfLength, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_map] at hu
      rcases hu with ⟨us, hus, rfl⟩
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hmem
      · rfl
      · exact ih us hus b hmem
  induction L with
  | zero =>
    simp [wordsUpTo] at hw
    subst hw
    intro _ hb; cases hb
  | succ L ih =>
    simp only [wordsUpTo, List.mem_append] at hw
    rcases hw with h1 | h2
    · exact ih h1
    · exact hlen (L + 1) w h2

/-- Tightness counterexample for `hCover : CoversAll alphabet` in
`finite_alphabet_bounded_moore_spec_suite_teaches`. -/
theorem finite_alphabet_bounded_moore_spec_suite_ce_incomplete_alphabet :
    let M : InitMooreMachine Bool Bool 1 := constMoore false
    ¬ CoversAll ([false] : List Bool) ∧
    BoundedMooreBehaviors Bool Bool 2 M.behavior ∧
    ¬ Teaches (BoundedMooreBehaviors Bool Bool 2) M.behavior
        (mooreSpecTestSuite [false] M 2) := by
  refine ⟨coversAll_neg_example, ⟨1, by decide, constMoore false, rfl⟩, ?_⟩
  intro hT
  have hcon : Consistent (mooreSpecTestSuite [false] (constMoore false) 2)
      seenTrueMachine.behavior := by
    rw [mooreSpecTestSuite, consistent_labelSample_iff]
    intro w hw
    rw [constMoore_behavior, seenTrueMachine_all_false w (mem_wordsUpTo_false_only _ w hw)]
  have heq := hT.2.2 seenTrueMachine.behavior ⟨2, Nat.le_refl 2, seenTrueMachine, rfl⟩ hcon
  have hval := congrFun heq [true]
  rw [constMoore_behavior] at hval
  cases hval

/-- Tightness counterexample for `hCover : CoversAll alphabet` in
`finite_alphabet_bounded_moore_class_suite_teaches`. -/
theorem finite_alphabet_bounded_moore_class_suite_ce_incomplete_alphabet :
    let h : List Bool → Bool := fun _ => false
    ¬ CoversAll ([false] : List Bool) ∧
    BoundedMooreBehaviors Bool Bool 2 h ∧
    ¬ Teaches (BoundedMooreBehaviors Bool Bool 2) h
        (mooreClassTestSuite [false] 2 h) := by
  refine ⟨coversAll_neg_example, ⟨1, by decide, constMoore false, funext (constMoore_behavior false)⟩, ?_⟩
  intro hT
  have hcon : Consistent (mooreClassTestSuite [false] 2 (fun _ => false))
      seenTrueMachine.behavior := by
    rw [mooreClassTestSuite, consistent_labelSample_iff]
    intro w hw
    exact seenTrueMachine_all_false w (mem_wordsUpTo_false_only _ w hw)
  have heq := hT.2.2 seenTrueMachine.behavior ⟨2, Nat.le_refl 2, seenTrueMachine, rfl⟩ hcon
  have hval := congrFun heq [true]
  cases hval

/-- Tightness counterexample for `hMem : BoundedMooreBehaviors I O k₂ M.behavior`
in `finite_alphabet_bounded_moore_spec_suite_teaches`: a 2-state alternating
machine cannot satisfy the membership conjunct of `Teaches` within
`BoundedMooreBehaviors Unit Bool 1` (while certification of `≤ 1`-state
implementations still holds by `finite_alphabet_bounded_moore_spec_suite_certifies`). -/
theorem finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound :
    CoversAll ([()] : List Unit) ∧
    ¬ BoundedMooreBehaviors Unit Bool 1 altMachine2.behavior ∧
    ¬ Teaches (BoundedMooreBehaviors Unit Bool 1) altMachine2.behavior
        (mooreSpecTestSuite [()] altMachine2 1) := by
  have hnotMem : ¬ BoundedMooreBehaviors Unit Bool 1 altMachine2.behavior := by
    rintro ⟨m, hm, M, hM⟩
    have hm1 : m = 1 := by
      have hpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) M.init.isLt
      omega
    subst hm1
    have h0 := congrFun hM []
    have h1 := congrFun hM [()]
    have hstep : M.step M.init () = M.init := by
      apply Fin.ext
      have := (M.step M.init ()).isLt
      have := M.init.isLt
      omega
    simp only [InitMooreMachine.behavior, MooreMachine.behavior, MooreMachine.run] at h0 h1
    rw [hstep, h0] at h1
    cases h1
  exact ⟨fun u => by cases u; simp, hnotMem, fun hT => hnotMem hT.1⟩

/-- Tightness counterexample for `hMem : BoundedMooreBehaviors I O k h` in
`finite_alphabet_bounded_moore_class_suite_teaches`. -/
theorem finite_alphabet_bounded_moore_class_suite_ce_target_outside_bound :
    CoversAll ([()] : List Unit) ∧
    ¬ BoundedMooreBehaviors Unit Bool 1 altMachine2.behavior ∧
    ¬ Teaches (BoundedMooreBehaviors Unit Bool 1) altMachine2.behavior
        (mooreClassTestSuite [()] 1 altMachine2.behavior) :=
  ⟨finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound.1,
   finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound.2.1,
   fun hT => finite_alphabet_bounded_moore_spec_suite_ce_target_outside_bound.2.1 hT.1⟩

/-! ### One-State Boundary & Concrete Positive Control -/

/-- Every `≤ 1`-state Moore behavior is constant, and the single-example suite
`[([], c)]` teaches it within `BoundedMooreBehaviors I O 1` over EVERY input
alphabet `I` (including infinite alphabets such as `Nat`). -/
theorem bounded_one_state_moore_single_example_teaches
    {I : Type u} {O : Type v} (c : O) :
    Teaches (BoundedMooreBehaviors I O 1) (fun _ => c) [([], c)] := by
  refine ⟨⟨1, Nat.le_refl 1, constMoore c, funext (constMoore_behavior c)⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    rfl
  · rintro g ⟨m, hm, M, rfl⟩ hcon
    have hm1 : m = 1 := by have := M.init.isLt; omega
    subst hm1
    have h0 : M.out M.init = c := hcon ([], c) (by simp)
    funext w
    have hrun : M.run M.init w = M.init :=
      Fin.ext (by have := (M.run M.init w).isLt; have := M.init.isLt; omega)
    show M.out (M.run M.init w) = c
    rw [hrun, h0]

/-- Concrete positive control (self-contained, proved without invoking Moore's
general theorem): over `I = Unit` (`Nonempty Unit`, finite alphabet) and
`O = Bool` (`HasTwoDistinct Bool`), `List Unit` is infinite and
`BoundedMooreBehaviors Unit Bool 2` breaks single-point patch closure, allowing
the 3-word suite `[([], false), ([()], true), ([(), ()], false)]` to teach
`altMachine2.behavior`. -/
theorem bounded_two_state_moore_unit_positive_control :
    Nonempty Unit ∧
    HasTwoDistinct Bool ∧
    InfiniteDomain (List Unit) ∧
    ¬ ClosedUnderPointPatches (BoundedMooreBehaviors Unit Bool 2) ∧
    Teaches (BoundedMooreBehaviors Unit Bool 2) altMachine2.behavior
      [([], false), ([()], true), ([(), ()], false)] := by
  have hInf : InfiniteDomain (List Unit) := by
    intro L
    let k := (L.map List.length).foldr max 0 + 1
    refine ⟨List.replicate k (), ?_⟩
    intro hmem
    have hmemLen : k ∈ L.map List.length := by
      have hlen : (List.replicate k ()).length = k := List.length_replicate
      exact List.mem_map.mpr ⟨List.replicate k (), hmem, hlen⟩
    have aux : ∀ (M : List Nat) (x : Nat), x ∈ M → x ≤ M.foldr max 0 := by
      intro M
      induction M with
      | nil => intro _ hx; cases hx
      | cons b bs ih =>
        intro x hx
        simp only [List.mem_cons] at hx
        simp only [List.foldr]
        rcases hx with rfl | hm
        · exact Nat.le_max_left x _
        · exact Nat.le_trans (ih x hm) (Nat.le_max_right b _)
    have hle := aux _ k hmemLen
    omega
  have hNotPatch : ¬ ClosedUnderPointPatches (BoundedMooreBehaviors Unit Bool 2) := by
    intro hClosed
    have hBase : BoundedMooreBehaviors Unit Bool 2 (fun _ => false) :=
      ⟨1, by decide, constMoore false, funext (constMoore_behavior false)⟩
    rcases hClosed (fun _ => false) [(), ()] true hBase with ⟨m, hm, M, hM⟩
    have h0 : M.behavior [] = false := by
      rw [hM, patchAt_of_ne (fun _ => false) [(), ()] [] true (by decide)]
    have h1 : M.behavior [()] = false := by
      rw [hM, patchAt_of_ne (fun _ => false) [(), ()] [()] true (by decide)]
    have h2 : M.behavior [(), ()] = true := by
      rw [hM, patchAt_self]
    have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) M.init.isLt
    let s₀ := M.init
    let s₁ := M.step s₀ ()
    let s₂ := M.step s₁ ()
    have ho0 : M.out s₀ = false := h0
    have ho1 : M.out s₁ = false := h1
    have ho2 : M.out s₂ = true := h2
    have hne02 : s₀ ≠ s₂ := fun heq => by rw [heq, ho2] at ho0; cases ho0
    have hne12 : s₁ ≠ s₂ := fun heq => by rw [heq, ho2] at ho1; cases ho1
    have hs01 : s₀ = s₁ := by
      apply Fin.ext
      have h0lt := s₀.isLt
      have h1lt := s₁.isLt
      have h2lt := s₂.isLt
      have hv02 : s₀.val ≠ s₂.val := fun hv => hne02 (Fin.ext hv)
      have hv12 : s₁.val ≠ s₂.val := fun hv => hne12 (Fin.ext hv)
      omega
    have hs12 : s₁ = s₂ := by
      change M.step s₀ () = M.step s₁ ()
      rw [hs01]
    exact hne12 hs12
  refine ⟨⟨()⟩, hasTwoDistinct_pos_example, hInf, hNotPatch,
    ⟨2, Nat.le_refl 2, altMachine2, rfl⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · intro g hg hcon
    rcases hg with ⟨m, hm, M, rfl⟩
    have h0 : M.out M.init = false := hcon ([], false) (by simp)
    have h1 : M.out (M.step M.init ()) = true := hcon ([()], true) (by simp)
    have h2 : M.out (M.step (M.step M.init ()) ()) = false := hcon ([(), ()], false) (by simp)
    have hm_pos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) M.init.isLt
    have hm2 : m = 2 := by
      by_cases hm1 : m = 1
      · subst hm1
        have hst : M.step M.init () = M.init := by
          apply Fin.ext
          have := (M.step M.init ()).isLt
          have := M.init.isLt
          omega
        rw [hst, h0] at h1
        cases h1
      · omega
    subst hm2
    let s₀ := M.init
    let s₁ := M.step s₀ ()
    have hne01 : s₀ ≠ s₁ := by
      intro heq
      have h1' : M.out s₁ = true := h1
      rw [← heq, h0] at h1'
      cases h1'
    have hstep1 : M.step s₁ () = s₀ := by
      let s₂ := M.step s₁ ()
      have hne21 : s₂ ≠ s₁ := by
        intro heq
        have h2' : M.out s₂ = false := h2
        rw [heq] at h2'
        have h1' : M.out s₁ = true := h1
        rw [h1'] at h2'
        cases h2'
      have h0lt := s₀.isLt
      have h1lt := s₁.isLt
      have h2lt := s₂.isLt
      have hne01v : s₀.val ≠ s₁.val := fun hv => hne01 (Fin.ext hv)
      have hne21v : s₂.val ≠ s₁.val := fun hv => hne21 (Fin.ext hv)
      exact Fin.ext (by omega)
    have hrun : ∀ w : List Unit,
        M.run s₀ w = if w.length % 2 = 0 then s₀ else s₁ := by
      intro w
      suffices ∀ (k : Nat) (u : List Unit), u.length = k →
          M.run s₀ u = if k % 2 = 0 then s₀ else s₁ from this w.length w rfl
      intro k
      induction k with
      | zero =>
        intro u hu
        cases u with
        | nil => rfl
        | cons _ _ => simp at hu
      | succ k ih =>
        intro u hu
        have hlast : ∃ (pref : List Unit), u = pref ++ [()] ∧ pref.length = k := by
          cases hrev : u.reverse with
          | nil =>
            have : u = [] := List.reverse_eq_nil_iff.mp hrev
            subst this; simp at hu
          | cons a rest =>
            cases a
            refine ⟨rest.reverse, ?_, ?_⟩
            · have := congrArg List.reverse hrev
              simpa [List.reverse_cons] using this
            · have hlen := congrArg List.length hrev
              simp only [List.length_reverse, List.length_cons] at hlen
              rw [List.length_reverse]
              omega
        rcases hlast with ⟨pref, rfl, hpref⟩
        rw [MooreMachine.run_append, ih pref hpref]
        split
        · rename_i heven
          have hodd : ¬ ((k + 1) % 2 = 0) := by omega
          simp [MooreMachine.run, hodd, s₁]
        · rename_i hodd
          have heven : (k + 1) % 2 = 0 := by omega
          simp [MooreMachine.run, heven, hstep1]
    funext w
    rw [altMachine2_behavior]
    simp only [InitMooreMachine.behavior, MooreMachine.behavior]
    change M.out (M.run s₀ w) = _
    rw [hrun w]
    by_cases heven : w.length % 2 = 0
    · simp only [heven, ↓reduceIte]
      exact h0
    · have his1 : w.length % 2 = 1 := by omega
      simp only [heven, ↓reduceIte]
      rw [decide_eq_true his1]
      exact h1

/-! ### Results 12 & 13: General Sharpness of `n₁ + n₂ - 2` and `2k - 2` -/

/-- General two-machine sharpness of Moore's `n₁ + n₂ - 2` bound: for all
`m₁, m₂ : Nat` (giving `n₁ = m₁ + 1` and `n₂ = m₂ + 1` states, so
`n₁ + n₂ - 2 = m₁ + m₂`), the explicit unary machines `modCycleMachine m₁ m₂`
and `mimicSaturateMachine m₁ m₂` agree on every input word of length `< m₁ + m₂`
and disagree on `List.replicate (m₁ + m₂) ()`. -/
theorem moore_two_machine_bound_sharp (m₁ m₂ : Nat) :
    let M₁ := modCycleMachine m₁ m₂
    let M₂ := mimicSaturateMachine m₁ m₂
    (∀ w : List Unit, w.length < m₁ + m₂ → M₁.behavior w = M₂.behavior w) ∧
    M₁.behavior (List.replicate (m₁ + m₂) ()) ≠
      M₂.behavior (List.replicate (m₁ + m₂) ()) ∧
    M₁.behavior ≠ M₂.behavior := by
  have hAgree : ∀ w : List Unit, w.length < m₁ + m₂ →
      (modCycleMachine m₁ m₂).behavior w = (mimicSaturateMachine m₁ m₂).behavior w := by
    intro w hw
    rw [modCycleMachine_behavior, mimicSaturateMachine_behavior]
    by_cases hlt : w.length < m₂
    · have hmin : min w.length m₂ = w.length := by omega
      simp [hmin, hlt]
    · have hmin : min w.length m₂ = m₂ := by omega
      have hne : w.length % (m₁ + 1) ≠ (m₁ + m₂) % (m₁ + 1) :=
        mod_ne_of_sub_lt w.length (m₁ + m₂) (m₁ + 1) hw (by omega)
      simp [hmin, hne]
  have hDiff : (modCycleMachine m₁ m₂).behavior (List.replicate (m₁ + m₂) ()) ≠
      (mimicSaturateMachine m₁ m₂).behavior (List.replicate (m₁ + m₂) ()) := by
    rw [modCycleMachine_behavior, mimicSaturateMachine_behavior, List.length_replicate]
    have hmin : min (m₁ + m₂) m₂ = m₂ := by omega
    simp [hmin]
  have hNe : (modCycleMachine m₁ m₂).behavior ≠ (mimicSaturateMachine m₁ m₂).behavior :=
    fun heq => hDiff (congrFun heq (List.replicate (m₁ + m₂) ()))
  exact ⟨hAgree, hDiff, hNe⟩

/-- Non-vacuity witness for `moore_two_machine_bound_sharp` at `m₁ = 1, m₂ = 2`
(`n₁ = 2`, `n₂ = 3`, first difference at length `3 = 2 + 3 - 2`). -/
theorem moore_two_machine_bound_sharp_nonvacuity :
    (∀ w : List Unit, w.length < 3 →
      (modCycleMachine 1 2).behavior w = (mimicSaturateMachine 1 2).behavior w) ∧
    (modCycleMachine 1 2).behavior [(), (), ()] ≠
      (mimicSaturateMachine 1 2).behavior [(), (), ()] :=
  ⟨(moore_two_machine_bound_sharp 1 2).1, (moore_two_machine_bound_sharp 1 2).2.1⟩

/-- General sharpness of the `2 * k - 2` class-suite depth for every `k ≥ 2`:
`modCycleMachine (k - 1) (k - 1)` and `mimicSaturateMachine (k - 1) (k - 1)`
both lie in `BoundedMooreBehaviors Unit Bool k`, agree on every input word of
length `< 2 * k - 2`, and disagree at length `2 * k - 2`. Consequently, neither
`wordsUpTo [()] (2 * k - 3)` (all words of length `< 2 * k - 2`) nor
`wordsUpTo [()] (k - 1)` (all words of length `< k`) teaches
`(modCycleMachine (k - 1) (k - 1)).behavior` within
`BoundedMooreBehaviors Unit Bool k`. -/
theorem bounded_moore_class_suite_depth_sharp (k : Nat) (hk : 2 ≤ k) :
    let M₁ := modCycleMachine (k - 1) (k - 1)
    let M₂ := mimicSaturateMachine (k - 1) (k - 1)
    BoundedMooreBehaviors Unit Bool k M₁.behavior ∧
    BoundedMooreBehaviors Unit Bool k M₂.behavior ∧
    (∀ w : List Unit, w.length < 2 * k - 2 → M₁.behavior w = M₂.behavior w) ∧
    M₁.behavior (List.replicate (2 * k - 2) ()) ≠
      M₂.behavior (List.replicate (2 * k - 2) ()) ∧
    ¬ Teaches (BoundedMooreBehaviors Unit Bool k) M₁.behavior
        (labelSample M₁.behavior (wordsUpTo [()] (2 * k - 3))) ∧
    ¬ Teaches (BoundedMooreBehaviors Unit Bool k) M₁.behavior
        (labelSample M₁.behavior (wordsUpTo [()] (k - 1))) := by
  have hk_eq : (k - 1) + (k - 1) = 2 * k - 2 := by omega
  have hle : (k - 1) + 1 ≤ k := by omega
  have hSharp := moore_two_machine_bound_sharp (k - 1) (k - 1)
  rw [hk_eq] at hSharp
  have hMem1 : BoundedMooreBehaviors Unit Bool k (modCycleMachine (k - 1) (k - 1)).behavior :=
    ⟨(k - 1) + 1, hle, modCycleMachine (k - 1) (k - 1), rfl⟩
  have hMem2 : BoundedMooreBehaviors Unit Bool k (mimicSaturateMachine (k - 1) (k - 1)).behavior :=
    ⟨(k - 1) + 1, hle, mimicSaturateMachine (k - 1) (k - 1), rfl⟩
  have hCoverUnit : CoversAll ([()] : List Unit) := fun u => by cases u; simp
  have hNotT : ∀ L : Nat, L < 2 * k - 2 →
      ¬ Teaches (BoundedMooreBehaviors Unit Bool k) (modCycleMachine (k - 1) (k - 1)).behavior
          (labelSample (modCycleMachine (k - 1) (k - 1)).behavior (wordsUpTo [()] L)) := by
    intro L hL hT
    have hcon : Consistent
        (labelSample (modCycleMachine (k - 1) (k - 1)).behavior (wordsUpTo [()] L))
        (mimicSaturateMachine (k - 1) (k - 1)).behavior := by
      rw [consistent_labelSample_iff]
      intro w hw
      have hlen : w.length ≤ L := (mem_wordsUpTo_iff hCoverUnit L w).mp hw
      exact (hSharp.1 w (by omega)).symm
    have heq := hT.2.2 _ hMem2 hcon
    exact hSharp.2.2 heq.symm
  exact ⟨hMem1, hMem2, hSharp.1, hSharp.2.1, hNotT (2 * k - 3) (by omega),
    hNotT (k - 1) (by omega)⟩

/-- Non-vacuity witness for `bounded_moore_class_suite_depth_sharp` at `k = 3`. -/
theorem bounded_moore_class_suite_depth_sharp_nonvacuity : 2 ≤ (3 : Nat) := by decide

/-- Canonical tightness counterexample for `hk : 2 ≤ k` in
`bounded_moore_class_suite_depth_sharp`: at `k = 1`, `2 * 1 - 3 = 0`, and
`wordsUpTo [()] 0 = [[]]` DOES teach `(modCycleMachine 0 0).behavior` (constant
`true`) within `BoundedMooreBehaviors Unit Bool 1`. -/
theorem bounded_moore_class_suite_depth_sharp_ce_one_state :
    let M₁ := modCycleMachine (1 - 1) (1 - 1)
    let M₂ := mimicSaturateMachine (1 - 1) (1 - 1)
    ¬ (2 ≤ (1 : Nat)) ∧
    ¬ (BoundedMooreBehaviors Unit Bool 1 M₁.behavior ∧
       BoundedMooreBehaviors Unit Bool 1 M₂.behavior ∧
       (∀ w : List Unit, w.length < 2 * 1 - 2 → M₁.behavior w = M₂.behavior w) ∧
       M₁.behavior (List.replicate (2 * 1 - 2) ()) ≠
         M₂.behavior (List.replicate (2 * 1 - 2) ()) ∧
       ¬ Teaches (BoundedMooreBehaviors Unit Bool 1) M₁.behavior
           (labelSample M₁.behavior (wordsUpTo [()] (2 * 1 - 3))) ∧
       ¬ Teaches (BoundedMooreBehaviors Unit Bool 1) M₁.behavior
           (labelSample M₁.behavior (wordsUpTo [()] (1 - 1)))) := by
  refine ⟨by decide, ?_⟩
  intro ⟨_, _, _, _, hNotT, _⟩
  apply hNotT
  have hbeh : (modCycleMachine 0 0).behavior = fun _ => true := by
    funext w
    rw [modCycleMachine_behavior]
    simp [Nat.mod_one]
  change Teaches (BoundedMooreBehaviors Unit Bool 1) (modCycleMachine 0 0).behavior
      [([], (modCycleMachine 0 0).behavior [])]
  rw [hbeh]
  exact bounded_one_state_moore_single_example_teaches true

/-- Concrete `k = 2` check using `altMachine2` and `latchMachine2`: both belong
to `BoundedMooreBehaviors Unit Bool 2` and agree on all words of length `< 2`,
yet disagree at length `2 = 2 * 2 - 2`. -/
theorem two_state_moore_length_lt_k_insufficient :
    BoundedMooreBehaviors Unit Bool 2 altMachine2.behavior ∧
    BoundedMooreBehaviors Unit Bool 2 latchMachine2.behavior ∧
    (∀ w : List Unit, w.length < 2 → altMachine2.behavior w = latchMachine2.behavior w) ∧
    altMachine2.behavior [(), ()] ≠ latchMachine2.behavior [(), ()] ∧
    ¬ Teaches (BoundedMooreBehaviors Unit Bool 2) altMachine2.behavior
        (labelSample altMachine2.behavior (wordsUpTo [()] 1)) := by
  have hAgree : ∀ w : List Unit, w.length < 2 →
      altMachine2.behavior w = latchMachine2.behavior w := by
    intro w hw
    cases w with
    | nil => decide
    | cons u rest =>
      cases u
      cases rest with
      | nil => decide
      | cons _ _ => simp at hw; omega
  have hDiff : altMachine2.behavior [(), ()] ≠ latchMachine2.behavior [(), ()] := by decide
  have hNotT : ¬ Teaches (BoundedMooreBehaviors Unit Bool 2) altMachine2.behavior
      (labelSample altMachine2.behavior (wordsUpTo [()] 1)) := by
    intro hT
    have hcon : Consistent (labelSample altMachine2.behavior (wordsUpTo [()] 1))
        latchMachine2.behavior := by
      rw [consistent_labelSample_iff]
      intro w hw
      have hlen : w.length ≤ 1 :=
        (mem_wordsUpTo_iff (fun u => by cases u; simp) 1 w).mp hw
      exact (hAgree w (by omega)).symm
    have heq := hT.2.2 latchMachine2.behavior ⟨2, Nat.le_refl 2, latchMachine2, rfl⟩ hcon
    exact hDiff (congrFun heq [(), ()]).symm
  exact ⟨⟨2, Nat.le_refl 2, altMachine2, rfl⟩,
         ⟨2, Nat.le_refl 2, latchMachine2, rfl⟩,
         hAgree, hDiff, hNotT⟩

/-! ### Result 14: Infinite-Alphabet Impossibility for `k ≥ 2` -/

/-- General infinite-alphabet impossibility for bounded-state Moore machines:
for every state bound `k ≥ 2`, every infinite input alphabet `I`, and every
nontrivial output alphabet `O`, no finite labeled sample teaches any behavior
within `BoundedMooreBehaviors I O k`. (At `k = 1` the threshold flips:
`bounded_one_state_moore_single_example_teaches` shows `[([], c)]` teaches
every `1`-state behavior over every alphabet.) -/
theorem two_le_state_bound_infinite_alphabet_no_finite_teaching_set
    {I : Type u} {O : Type v} (k : Nat)
    (hk : 2 ≤ k)
    (hInf : InfiniteDomain I)
    (hTwo : HasTwoDistinct O) :
    ∀ (h : List I → O) (S : List (List I × O)),
      ¬ Teaches (BoundedMooreBehaviors I O k) h S := by
  classical
  intro h S hT
  rcases hT.1 with ⟨m, hm, M, rfl⟩
  rcases hInf (S.flatMap Prod.fst) with ⟨a₀, ha₀⟩
  have hS : ∀ p ∈ S, a₀ ∉ p.1 := fun p hp hmem =>
    ha₀ (List.mem_flatMap.mpr ⟨p, hp, hmem⟩)
  by_cases hex : ∃ q : Fin m, M.out q ≠ M.out (M.step M.init a₀)
  · rcases hex with ⟨q, hq⟩
    let M' : InitMooreMachine I O m :=
      { step := fun s a => if a = a₀ then q else M.step s a
        out := M.out
        init := M.init }
    have hrun : ∀ (w : List I) (s : Fin m), a₀ ∉ w → M'.run s w = M.run s w := by
      intro w
      induction w with
      | nil => intro _ _; rfl
      | cons a ws ih =>
        intro s hnot
        have hne : a ≠ a₀ := fun heq => hnot (heq ▸ List.mem_cons_self)
        have hnot' : a₀ ∉ ws := fun hmem => hnot (List.mem_cons_of_mem _ hmem)
        have hstep : M'.step s a = M.step s a := by simp [M', hne]
        show M'.run (M'.step s a) ws = M.run (M.step s a) ws
        rw [hstep]
        exact ih _ hnot'
    have hcon : Consistent S M'.behavior := by
      intro p hp
      show M.out (M'.run M.init p.1) = p.2
      rw [hrun p.1 M.init (hS p hp)]
      exact hT.2.1 p hp
    have heq := hT.2.2 M'.behavior ⟨m, hm, M', rfl⟩ hcon
    have hv := congrFun heq [a₀]
    apply hq
    have h1 : M'.behavior [a₀] = M.out q := by
      show M.out (M'.step M.init a₀) = M.out q
      simp [M']
    have h2 : M.behavior [a₀] = M.out (M.step M.init a₀) := rfl
    rw [← h1, ← h2, hv]
  · let c : O := M.out (M.step M.init a₀)
    have hall : ∀ q : Fin m, M.out q = c := fun q =>
      Classical.byContradiction fun hne => hex ⟨q, hne⟩
    have hconst : ∀ w, M.behavior w = c := fun w => hall _
    rcases hTwo with ⟨y₁, y₂, hy⟩
    have ⟨c', hc'⟩ : ∃ c' : O, c' ≠ c := by
      by_cases h1 : y₁ = c
      · exact ⟨y₂, fun h2 => hy (h1.trans h2.symm)⟩
      · exact ⟨y₁, h1⟩
    let T : InitMooreMachine I O 2 :=
      { step := fun s a => if a = a₀ then ⟨1, by decide⟩ else s
        out := fun s => if s.val = 0 then c else c'
        init := ⟨0, by decide⟩ }
    have hrunT : ∀ (w : List I), a₀ ∉ w → T.run ⟨0, by decide⟩ w = ⟨0, by decide⟩ := by
      intro w
      induction w with
      | nil => intro _; rfl
      | cons a ws ih =>
        intro hnot
        have hne : a ≠ a₀ := fun heq => hnot (heq ▸ List.mem_cons_self)
        have hnot' : a₀ ∉ ws := fun hmem => hnot (List.mem_cons_of_mem _ hmem)
        have hstep : T.step ⟨0, by decide⟩ a = ⟨0, by decide⟩ := by simp [T, hne]
        show T.run (T.step ⟨0, by decide⟩ a) ws = _
        rw [hstep]
        exact ih hnot'
    have hcon : Consistent S T.behavior := by
      intro p hp
      show T.out (T.run ⟨0, by decide⟩ p.1) = p.2
      rw [hrunT p.1 (hS p hp), ← hT.2.1 p hp, hconst]
      simp [T]
    have heq := hT.2.2 T.behavior ⟨2, hk, T, rfl⟩ hcon
    have hv := congrFun heq [a₀]
    rw [hconst] at hv
    apply hc'
    rw [← hv]
    symm
    show T.out (T.step ⟨0, by decide⟩ a₀) = c'
    simp [T]

/-- Non-vacuity witness for
`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`. -/
theorem two_le_state_bound_infinite_alphabet_no_finite_teaching_set_nonvacuity :
    2 ≤ (2 : Nat) ∧ InfiniteDomain Nat ∧ HasTwoDistinct Bool :=
  ⟨Nat.le_refl 2, infiniteDomain_pos_example, hasTwoDistinct_pos_example⟩

/-- Canonical tightness counterexample for `hk : 2 ≤ k` in
`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`: at `k = 1`,
`[([], false)]` teaches constant `false` even over the infinite alphabet `Nat`. -/
theorem two_le_state_bound_infinite_alphabet_ce_one_state :
    ¬ (2 ≤ (1 : Nat)) ∧
    InfiniteDomain Nat ∧
    HasTwoDistinct Bool ∧
    ¬ (∀ (h : List Nat → Bool) (S : List (List Nat × Bool)),
        ¬ Teaches (BoundedMooreBehaviors Nat Bool 1) h S) := by
  refine ⟨by decide, infiniteDomain_pos_example, hasTwoDistinct_pos_example, ?_⟩
  intro hall
  exact hall (fun _ => false) [([], false)]
    (bounded_one_state_moore_single_example_teaches false)

/-- Canonical tightness counterexample for `hInf : InfiniteDomain I` in
`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`: over the finite
alphabet `Unit` at `k = 2`, the 3-word suite teaches `altMachine2.behavior`. -/
theorem two_le_state_bound_infinite_alphabet_ce_finite_alphabet :
    2 ≤ (2 : Nat) ∧
    ¬ InfiniteDomain Unit ∧
    HasTwoDistinct Bool ∧
    ¬ (∀ (h : List Unit → Bool) (S : List (List Unit × Bool)),
        ¬ Teaches (BoundedMooreBehaviors Unit Bool 2) h S) := by
  refine ⟨Nat.le_refl 2, ?_, hasTwoDistinct_pos_example, ?_⟩
  · intro hInf
    rcases hInf [()] with ⟨u, hu⟩
    cases u
    exact hu (by simp)
  · intro hall
    exact hall altMachine2.behavior
      [([], false), ([()], true), ([(), ()], false)]
      bounded_two_state_moore_unit_positive_control.2.2.2.2

/-- Canonical tightness counterexample for `hTwo : HasTwoDistinct O` in
`two_le_state_bound_infinite_alphabet_no_finite_teaching_set`: over subsingleton
output `Unit`, the empty sample teaches `fun _ => ()` even over `Nat` at `k = 2`. -/
theorem two_le_state_bound_infinite_alphabet_ce_trivial_output :
    2 ≤ (2 : Nat) ∧
    InfiniteDomain Nat ∧
    ¬ HasTwoDistinct Unit ∧
    ¬ (∀ (h : List Nat → Unit) (S : List (List Nat × Unit)),
        ¬ Teaches (BoundedMooreBehaviors Nat Unit 2) h S) := by
  refine ⟨Nat.le_refl 2, infiniteDomain_pos_example, hasTwoDistinct_neg_example, ?_⟩
  intro hall
  apply hall (fun _ => ()) []
  refine ⟨⟨1, by decide, constMoore (), funext (constMoore_behavior ())⟩,
    (fun _ hp => by cases hp), ?_⟩
  intro g _ _
  funext w
  cases g w
  rfl

/-! ### Result 15: Step-Counting Deviation Family (`deviateAfter`, Moore 1956 Thm. 2) -/

private def encodePair {n k : Nat} (s : Fin n) (c : Fin (k + 1)) : Fin (n * (k + 1)) :=
  ⟨s.val * (k + 1) + c.val, by
    have hs : s.val + 1 ≤ n := s.isLt
    have hc : c.val < k + 1 := c.isLt
    have hmul : (s.val + 1) * (k + 1) ≤ n * (k + 1) := Nat.mul_le_mul_right (k + 1) hs
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega⟩

private def decodeState {n k : Nat} (idx : Fin (n * (k + 1))) : Fin n :=
  ⟨idx.val / (k + 1),
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq idx.isLt (Nat.mul_comm n (k + 1)))⟩

private def decodeCount {n k : Nat} (idx : Fin (n * (k + 1))) : Fin (k + 1) :=
  ⟨idx.val % (k + 1), Nat.mod_lt idx.val (Nat.succ_pos k)⟩

private theorem decodeState_encodePair {n k : Nat} (s : Fin n) (c : Fin (k + 1)) :
    decodeState (encodePair s c) = s := by
  apply Fin.ext
  simp only [decodeState, encodePair]
  have hpos : 0 < k + 1 := Nat.succ_pos k
  rw [Nat.mul_comm s.val (k + 1), Nat.mul_add_div hpos, Nat.div_eq_of_lt c.isLt, Nat.add_zero]

private theorem decodeCount_encodePair {n k : Nat} (s : Fin n) (c : Fin (k + 1)) :
    decodeCount (encodePair s c) = c := by
  apply Fin.ext
  simp only [decodeCount, encodePair]
  rw [Nat.mul_comm s.val (k + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]

/-- Product of `M : InitMooreMachine I O n` with a `(k + 1)`-state saturating
step counter (Moore 1956, Theorem 2, p. 140): behaves identically to `M` on
every input word of length `< k`, and switches permanently to output `y'` once
`k` or more steps have been taken. -/
def deviateAfter {I : Type u} {O : Type v} {n : Nat}
    (M : InitMooreMachine I O n) (k : Nat) (y' : O) :
    InitMooreMachine I O (n * (k + 1)) where
  step idx a :=
    let s := decodeState idx
    let c := decodeCount idx
    encodePair (M.step s a) ⟨min (c.val + 1) k, by omega⟩
  out idx :=
    let s := decodeState idx
    let c := decodeCount idx
    if c.val < k then M.out s else y'
  init := encodePair M.init ⟨0, Nat.succ_pos k⟩

private theorem deviateAfter_run {I : Type u} {O : Type v} {n : Nat}
    (M : InitMooreMachine I O n) (k : Nat) (y' : O)
    (s : Fin n) (c : Fin (k + 1)) (w : List I) :
    (deviateAfter M k y').run (encodePair s c) w =
      encodePair (M.run s w) ⟨min (c.val + w.length) k, by omega⟩ := by
  induction w generalizing s c with
  | nil =>
    simp only [MooreMachine.run, List.length_nil, Nat.add_zero]
    congr 1
    apply Fin.ext
    dsimp only
    have hc := c.isLt
    omega
  | cons a ws ih =>
    change (deviateAfter M k y').run
      (encodePair (M.step (decodeState (encodePair s c)) a)
        ⟨min ((decodeCount (encodePair s c)).val + 1) k, by omega⟩) ws = _
    simp only [decodeState_encodePair, decodeCount_encodePair]
    rw [ih]
    simp only [MooreMachine.run, List.length_cons]
    congr 1
    apply Fin.ext
    dsimp only
    omega

/-- Explicit `k`-step deviation witness (Moore 1956, Theorem 2, p. 140): for any
initialized Moore machine `M`, step threshold `k`, input symbol `a`, and output
`y' ≠ M.behavior (replicate k a)`, `deviateAfter M k y'` is a finite-state Moore
machine (with `n * (k + 1)` states) that agrees with `M` on every word of length
`< k` and disagrees with `M` at `List.replicate k a`. -/
theorem deviateAfter_agrees_before_and_differs_at
    {I : Type u} {O : Type v} {n : Nat}
    (M : InitMooreMachine I O n) (k : Nat) (a : I) (y' : O)
    (hDiff : y' ≠ M.behavior (List.replicate k a)) :
    (∀ w : List I, w.length < k → (deviateAfter M k y').behavior w = M.behavior w) ∧
    (deviateAfter M k y').behavior (List.replicate k a) = y' ∧
    (deviateAfter M k y').behavior ≠ M.behavior := by
  have hBefore : ∀ w : List I, w.length < k →
      (deviateAfter M k y').behavior w = M.behavior w := by
    intro w hw
    simp only [InitMooreMachine.behavior, MooreMachine.behavior]
    change (deviateAfter M k y').out
      ((deviateAfter M k y').run (encodePair M.init ⟨0, Nat.succ_pos k⟩) w) = _
    rw [deviateAfter_run]
    simp only [deviateAfter, decodeState_encodePair, decodeCount_encodePair, Nat.zero_add]
    have hlt : min w.length k < k := by omega
    simp [hlt]
  have hAt : (deviateAfter M k y').behavior (List.replicate k a) = y' := by
    simp only [InitMooreMachine.behavior, MooreMachine.behavior]
    change (deviateAfter M k y').out
      ((deviateAfter M k y').run (encodePair M.init ⟨0, Nat.succ_pos k⟩) (List.replicate k a)) = y'
    rw [deviateAfter_run]
    simp only [deviateAfter, decodeCount_encodePair,
      Nat.zero_add, List.length_replicate, Nat.min_self, Nat.lt_irrefl, ↓reduceIte]
  have hNe : (deviateAfter M k y').behavior ≠ M.behavior := by
    intro heq
    have hval := congrFun heq (List.replicate k a)
    rw [hAt] at hval
    exact hDiff hval
  exact ⟨hBefore, hAt, hNe⟩

/-- Non-vacuity witness for `deviateAfter_agrees_before_and_differs_at`. -/
theorem deviateAfter_agrees_before_and_differs_at_nonvacuity :
    (true : Bool) ≠ (constMoore false : InitMooreMachine Unit Bool 1).behavior (List.replicate 3 ()) := by
  rw [constMoore_behavior]
  decide

/-- Tightness counterexample for `hDiff` in `deviateAfter_agrees_before_and_differs_at`:
choosing `y' = M.behavior (List.replicate k a)` on `constMoore false` makes
`deviateAfter M k y'` behaviorally identical to `M`. -/
theorem deviateAfter_ce_same_output :
    let M : InitMooreMachine Unit Bool 1 := constMoore false
    ¬ ((false : Bool) ≠ M.behavior (List.replicate 2 ())) ∧
    ¬ ((∀ w : List Unit, w.length < 2 → (deviateAfter M 2 false).behavior w = M.behavior w) ∧
       (deviateAfter M 2 false).behavior (List.replicate 2 ()) = false ∧
       (deviateAfter M 2 false).behavior ≠ M.behavior) := by
  refine ⟨fun h => h rfl, ?_⟩
  intro ⟨_, _, hne⟩
  apply hne
  funext w
  simp only [InitMooreMachine.behavior, MooreMachine.behavior]
  change (deviateAfter (constMoore false) 2 false).out
    ((deviateAfter (constMoore false) 2 false).run (encodePair (constMoore false).init ⟨0, Nat.succ_pos 2⟩) w) = _
  rw [deviateAfter_run]
  simp only [deviateAfter, decodeCount_encodePair, constMoore]
  split <;> rfl

/-! ### Result 16: Unbounded-State Impossibility (Moore 1956, Theorem 2) -/

/-- Without an upper bound on state count, no finite labeled sample teaches any
behavior within `FiniteStateMooreBehaviors I O`, provided the input alphabet is
nonempty and the output alphabet has at least two distinct values (Moore 1956,
Theorem 2 and the remark following it, p. 140). -/
theorem unbounded_moore_no_finite_teaching_set
    {I : Type u} {O : Type v}
    (hI : Nonempty I)
    (hTwo : HasTwoDistinct O) :
    ∀ (h : List I → O) (S : List (List I × O)),
      ¬ Teaches (FiniteStateMooreBehaviors I O) h S := by
  intro h S hT
  rcases hT.1 with ⟨n, M, rfl⟩
  rcases hI with ⟨a⟩
  rcases hTwo with ⟨y₁, y₂, hyne⟩
  let k : Nat := (S.map (fun p => p.1.length)).foldr max 0 + 1
  have hltS : ∀ p ∈ S, p.1.length < k := by
    intro p hp
    have hmem : p.1.length ∈ S.map (fun q => q.1.length) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have hle : p.1.length ≤ (S.map (fun q => q.1.length)).foldr max 0 := by
      have aux : ∀ (L : List Nat) (x : Nat), x ∈ L → x ≤ L.foldr max 0 := by
        intro L
        induction L with
        | nil => intro _ hx; cases hx
        | cons b bs ih =>
          intro x hx
          simp only [List.mem_cons] at hx
          simp only [List.foldr]
          rcases hx with rfl | hm
          · exact Nat.le_max_left x _
          · exact Nat.le_trans (ih x hm) (Nat.le_max_right b _)
      exact aux _ _ hmem
    omega
  have ⟨y', hy'⟩ : ∃ y' : O, y' ≠ M.behavior (List.replicate k a) := by
    by_cases heq : M.behavior (List.replicate k a) = y₁
    · exact ⟨y₂, fun h2 => hyne (heq.symm.trans h2.symm)⟩
    · exact ⟨y₁, fun h1 => heq h1.symm⟩
  have hDev := deviateAfter_agrees_before_and_differs_at M k a y' hy'
  have hcon : Consistent S (deviateAfter M k y').behavior := by
    intro p hp
    rw [hDev.1 p.1 (hltS p hp)]
    exact hT.2.1 p hp
  have hMem : FiniteStateMooreBehaviors I O (deviateAfter M k y').behavior :=
    ⟨n * (k + 1), deviateAfter M k y', rfl⟩
  exact hDev.2.2 (hT.2.2 _ hMem hcon)

/-- Non-vacuity witness for `unbounded_moore_no_finite_teaching_set`. -/
theorem unbounded_moore_no_finite_teaching_set_nonvacuity :
    Nonempty Unit ∧ HasTwoDistinct Bool :=
  ⟨⟨()⟩, hasTwoDistinct_pos_example⟩

/-- Tightness counterexample for `hI : Nonempty I` in
`unbounded_moore_no_finite_teaching_set`: over the empty input alphabet `Empty`,
`List Empty` has only the empty word `[]`, so `[([], false)]` teaches constant
`false` even without a state bound. -/
theorem unbounded_moore_ce_empty_alphabet :
    ¬ Nonempty Empty ∧
    HasTwoDistinct Bool ∧
    ¬ (∀ (h : List Empty → Bool) (S : List (List Empty × Bool)),
        ¬ Teaches (FiniteStateMooreBehaviors Empty Bool) h S) := by
  refine ⟨fun ⟨e⟩ => Empty.elim e, hasTwoDistinct_pos_example, ?_⟩
  intro hall
  apply hall (fun _ => false) [([], false)]
  refine ⟨⟨1, constMoore false, funext (constMoore_behavior false)⟩, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  · intro g _ hcon
    funext w
    cases w with
    | nil => exact hcon ([], false) (by simp)
    | cons e _ => exact Empty.elim e

/-- Tightness counterexample for `hTwo : HasTwoDistinct O` in
`unbounded_moore_no_finite_teaching_set`: over a subsingleton output type `Unit`,
the empty sample teaches the unique function `List Unit → Unit`. -/
theorem unbounded_moore_ce_trivial_output :
    Nonempty Unit ∧
    ¬ HasTwoDistinct Unit ∧
    ¬ (∀ (h : List Unit → Unit) (S : List (List Unit × Unit)),
        ¬ Teaches (FiniteStateMooreBehaviors Unit Unit) h S) := by
  refine ⟨⟨()⟩, hasTwoDistinct_neg_example, ?_⟩
  intro hall
  apply hall (fun _ => ()) []
  refine ⟨⟨1, constMoore (), funext (constMoore_behavior ())⟩, (fun _ hp => by cases hp), ?_⟩
  intro g _ _
  funext w
  cases g w
  rfl

end Toy.Witness
