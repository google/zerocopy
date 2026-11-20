import ToyPredTrans.Basic

/-!
# Example programs and transformers; positive and negative examples for every definition

Everything in this file is fully proved.  The examples serve two purposes: they are the
concrete instances used by the tightness counterexamples and non-vacuity theorems, and they
test each definition of `Defs` against one instance it is meant to admit and one it is meant
to reject.
-/

namespace Toy.PredTrans

universe u

variable {σ : Type u}

/-! ## Example relational programs -/

/-- `skip`: the final state is the initial state. -/
def skipR : Rel σ := fun s s' => s' = s

/-- `havoc`: every state is a possible final state.  On an infinite state type this is
unbounded nondeterminism. -/
def havocR : Rel σ := fun _ _ => True

/-- The empty relation: no final state at all.  Read as a demonic update (`wlp emptyR`, the
total-correctness `wp` with the everywhere-true non-abortion predicate) this is the miraculous
program `magic`; under the partial-correctness reading of `wlp` it models guaranteed
divergence (`while true do skip`). -/
def emptyR : Rel σ := fun _ _ => False

/-- A boundedly nondeterministic program on `Nat`: add one or add two. -/
def stepR : Rel Nat := fun s s' => s' = s + 1 ∨ s' = s + 2

/-- A partial program on `Nat`: decrement.  The state `0` has no successor. -/
def predR : Rel Nat := fun s s' => s = s' + 1

/-- The predicate "nonzero" on `Nat`, used as the termination predicate of `predR`. -/
def posP : Pred Nat := fun s => s ≠ 0

/-! ## Example transformers -/

/-- `abort`: establishes nothing from any state.  Equal to `wp R (fun _ => False)` for
every `R`. -/
def abortT : Transformer σ := fun _ _ => False

/-- "Eventually always" on `Nat`: `Q` is established (from any state) when `Q` holds of all
sufficiently large numbers, i.e. of all but finitely many numbers.  This is the membership
test of the cofinite (Fréchet) filter; it is the key lawful-but-unintended transformer. -/
def eventually : Transformer Nat := fun Q _ => ∃ N, ∀ n, N ≤ n → Q n

/-- `Q` holds of every number from `N` on.  For fixed `N` this is the `wlp` of the program
"set the state to any number `≥ N`". -/
def fromN (N : Nat) : Transformer Nat := fun Q _ => ∀ n, N ≤ n → Q n

/-- Angelic havoc: `Q` is established when `Q` holds of at least one state. -/
def angelic : Transformer σ := fun Q _ => ∃ x, Q x

/-- Pointwise negation; an antitone transformer no program has. -/
def negT : Transformer σ := fun Q s => ¬ Q s

/-- The constant transformer: the precondition is `P` whatever the postcondition.  It is the
`wp` of the program that aborts outside `P` and is miraculous inside `P`
(`constT_eq_wp_emptyR`). -/
def constT (P : Pred σ) : Transformer σ := fun _ s => P s

/-! ## `wlp` and `wp`: positive and negative examples -/

/-- Positive: the `wlp` of `skip` is the identity transformer. -/
theorem wlp_skipR (Q : Pred σ) (s : σ) : wlp skipR Q s ↔ Q s := by
  constructor
  · intro h
    exact h s rfl
  · intro h s' hs
    have e : s' = s := hs
    rw [e]
    exact h

/-- Positive: after `stepR` from `0` the state is positive. -/
theorem wlp_stepR_pos : wlp stepR (fun n => 0 < n) 0 := by
  intro s' hs
  have hs' : s' = 0 + 1 ∨ s' = 0 + 2 := hs
  show 0 < s'
  omega

/-- Negative: `stepR` from `0` does not guarantee the final state `1` (it may be `2`). -/
theorem not_wlp_stepR_eq_one : ¬ wlp stepR (fun n => n = 1) 0 := by
  intro h
  have h2 : (2 : Nat) = 1 := h 2 (Or.inr rfl)
  omega

/-- Positive: decrementing `5` terminates and yields `4`. -/
theorem wp_predR_example : wp predR posP (fun n => n = 4) 5 := by
  refine ⟨?_, ?_⟩
  · show (5 : Nat) ≠ 0
    omega
  · intro s' hs
    have hs' : 5 = s' + 1 := hs
    show s' = 4
    omega

/-- Negative: at `0` the partial decrement establishes nothing under `wp`. -/
theorem not_wp_predR_zero (Q : Pred Nat) : ¬ wp predR posP Q 0 :=
  fun h => h.1 rfl

/-- In contrast, at `0` the liberal `wlp` of the decrement establishes everything, including
`False`: `wlp` does not see the missing successor. -/
theorem wlp_predR_zero (Q : Pred Nat) : wlp predR Q 0 := by
  intro s' hs
  have hs' : 0 = s' + 1 := hs
  omega

/-! ## `Monotone` -/

/-- Negative: negation is not monotone. -/
theorem not_monotone_negT : ¬ Monotone (negT : Transformer Unit) := by
  intro h
  have h1 : negT (fun _ : Unit => False) () := fun hf => hf
  exact h (fun _ => False) (fun _ => True) (fun _ hf => False.elim hf) () h1 trivial

/-- Positive: angelic havoc is monotone. -/
theorem monotone_angelic : Monotone (angelic : Transformer σ) := by
  intro P Q hPQ s h
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hPQ x hx⟩

/-! ## `abortT` -/

/-- `abortT` is `wp R (fun _ => False)` for every `R`. -/
theorem abortT_eq_wp (R : Rel σ) : (abortT : Transformer σ) = wp R (fun _ => False) :=
  trans_ext fun _ _ => ⟨fun h => False.elim h, fun h => h.1⟩

/-- Positive (`ConjNonempty`): `abortT` is positively conjunctive. -/
theorem conjNonempty_abortT : ConjNonempty (abortT : Transformer σ) := by
  intro ι Q hι s
  obtain ⟨i₀⟩ := hι
  exact ⟨fun h => False.elim h, fun h => h i₀⟩

/-- Positive (`Strict`): `abortT` is strict. -/
theorem strict_abortT : Strict (abortT : Transformer σ) := fun _ h => h

/-- Negative (`TopPreserving`): `abortT` does not preserve top. -/
theorem not_topPreserving_abortT : ¬ TopPreserving (abortT : Transformer Unit) :=
  fun h => h ()

/-- Negative (`ConjAll`): `abortT` is not universally conjunctive; the empty family fails. -/
theorem not_conjAll_abortT : ¬ ConjAll (abortT : Transformer Unit) :=
  fun h => not_topPreserving_abortT (topPreserving_of_conjAll h)

/-! ## `constT` -/

/-- The constant transformer is the `wp` of the empty relation with termination predicate
`P`; in particular it is positively conjunctive. -/
theorem constT_eq_wp_emptyR (P : Pred σ) : constT P = wp emptyR P :=
  trans_ext fun _ _ => ⟨fun h => ⟨h, fun _ hr => False.elim hr⟩, fun h => h.1⟩

/-! ## `eventually` -/

/-- `eventually` is monotone. -/
theorem monotone_eventually : Monotone eventually := by
  intro P Q hPQ s h
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun n hn => hPQ n (hN n hn)⟩

/-- Positive (`ConjBin`): `eventually` is binary conjunctive. -/
theorem conjBin_eventually : ConjBin eventually := by
  intro P Q s
  constructor
  · intro h
    obtain ⟨N, hN⟩ := h
    exact ⟨⟨N, fun n hn => (hN n hn).1⟩, ⟨N, fun n hn => (hN n hn).2⟩⟩
  · intro h
    obtain ⟨⟨N, hN⟩, ⟨M, hM⟩⟩ := h
    exact ⟨N + M, fun n hn => ⟨hN n (by omega), hM n (by omega)⟩⟩

/-- Positive (`TopPreserving`): `eventually` preserves top. -/
theorem topPreserving_eventually : TopPreserving eventually :=
  fun _ => ⟨0, fun _ _ => trivial⟩

/-- Positive (`Strict`): `eventually` is strict. -/
theorem strict_eventually : Strict eventually := by
  intro s h
  obtain ⟨N, hN⟩ := h
  exact hN N (Nat.le_refl N)

/-- Negative (`ConjNonempty`): `eventually` is not positively conjunctive.  Each predicate
`k ≤ ·` holds eventually, but their conjunction over all `k` is unsatisfiable. -/
theorem not_conjNonempty_eventually : ¬ ConjNonempty eventually := by
  intro h
  have key : eventually (fun n => ∀ k : Nat, k ≤ n) 0 :=
    (h Nat (fun k n => k ≤ n) ⟨0⟩ 0).mpr fun k => ⟨k, fun _ hn => hn⟩
  obtain ⟨N, hN⟩ := key
  have h1 : N + 1 ≤ N := hN N (Nat.le_refl N) (N + 1)
  omega

/-- Negative (`ConjAll`): `eventually` is not universally conjunctive. -/
theorem not_conjAll_eventually : ¬ ConjAll eventually :=
  fun h => not_conjNonempty_eventually (conjNonempty_of_conjAll h)

/-! ## `angelic` -/

/-- Negative (`ConjBin`): angelic havoc on a two-element state type is not binary
conjunctive. -/
theorem not_conjBin_angelic : ¬ ConjBin (angelic : Transformer Bool) := by
  intro h
  have key : angelic (fun b : Bool => b = true ∧ b = false) true :=
    (h (fun b => b = true) (fun b => b = false) true).mpr ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩
  obtain ⟨x, hx1, hx2⟩ := key
  rw [hx1] at hx2
  cases hx2

/-- Negative (`ConjNonempty`): angelic havoc is not positively conjunctive. -/
theorem not_conjNonempty_angelic : ¬ ConjNonempty (angelic : Transformer Bool) :=
  fun h => not_conjBin_angelic (conjBin_of_conjNonempty h)

/-- Positive (`OmegaContinuous`): angelic havoc is ω-continuous. -/
theorem omegaContinuous_angelic : OmegaContinuous (angelic : Transformer σ) := by
  intro Q _ s h
  obtain ⟨x, n, hx⟩ := h
  exact ⟨n, x, hx⟩

/-! ## `Strict` -/

/-- Positive: the `wp` of `skip` is strict. -/
theorem strict_wp_skipR (term : Pred σ) : Strict (wp skipR term) :=
  fun s h => h.2 s rfl

/-- Negative: the `wlp` of the empty relation is not strict (in the demonic-update reading this
is the miracle `magic`; in the partial-correctness reading, guaranteed divergence). -/
theorem not_strict_wlp_emptyR : ¬ Strict (wlp (emptyR : Rel Unit)) :=
  fun h => h () fun _ hr => hr

/-! ## `Chain` and `OmegaContinuous` -/

/-- Positive: the initial segments `{s | s ≤ n}` form a chain. -/
theorem chain_le : Chain (fun (n s : Nat) => s ≤ n) := by
  intro n s hs
  have hs' : s ≤ n := hs
  show s ≤ n + 1
  omega

/-- Negative: the singletons `{n}` do not form a chain. -/
theorem not_chain_eq : ¬ Chain (fun (n s : Nat) => s = n) := by
  intro h
  have h1 : (0 : Nat) = 0 + 1 := h 0 0 rfl
  omega

/-- Positive: the `wp` of `skip` (with any termination predicate) is ω-continuous. -/
theorem omegaContinuous_wp_skipR (term : Pred σ) : OmegaContinuous (wp skipR term) := by
  intro Q _ s h
  obtain ⟨ht, hw⟩ := h
  obtain ⟨n, hn⟩ := hw s rfl
  refine ⟨n, ht, ?_⟩
  intro s' hs
  have e : s' = s := hs
  rw [e]
  exact hn

/-- Positive: the `wlp` of the two-way choice `stepR` is ω-continuous. -/
theorem omegaContinuous_wlp_stepR : OmegaContinuous (wlp stepR) := by
  intro Q hQ s h
  obtain ⟨n₁, h₁⟩ := h (s + 1) (Or.inl rfl)
  obtain ⟨n₂, h₂⟩ := h (s + 2) (Or.inr rfl)
  refine ⟨n₁ + n₂, ?_⟩
  intro s' hs
  have hs' : s' = s + 1 ∨ s' = s + 2 := hs
  rcases hs' with e | e
  · rw [e]
    exact hQ.mono (by omega) _ h₁
  · rw [e]
    exact hQ.mono (by omega) _ h₂

/-- Negative: the `wlp` of `havoc` on `Nat` ("choose any natural number") is not
ω-continuous. -/
theorem not_omegaContinuous_wlp_havocR_nat : ¬ OmegaContinuous (wlp (havocR : Rel Nat)) := by
  intro h
  have h0 : wlp (havocR : Rel Nat) (fun t => ∃ n, t ≤ n) 0 := fun s' _ => ⟨s', Nat.le_refl s'⟩
  obtain ⟨n, hn⟩ := h (fun n s => s ≤ n) chain_le 0 h0
  have h1 : n + 1 ≤ n := hn (n + 1) trivial
  omega

/-- Negative: `eventually` is not ω-continuous. -/
theorem not_omegaContinuous_eventually : ¬ OmegaContinuous eventually := by
  intro h
  have h0 : eventually (fun t => ∃ n, t ≤ n) 0 := ⟨0, fun m _ => ⟨m, Nat.le_refl m⟩⟩
  obtain ⟨n, N, hN⟩ := h (fun n s => s ≤ n) chain_le 0 h0
  have h1 : N + n + 1 ≤ n := hN (N + n + 1) (by omega)
  omega

/-- The restriction to chains in `OmegaContinuous` matters: the same implication for an
arbitrary `Nat`-indexed family already fails for the two-way choice `stepR`. -/
theorem not_continuous_on_arbitrary_families_stepR :
    ¬ ∀ Q : Nat → Pred Nat, ∀ s, wlp stepR (fun t => ∃ n, Q n t) s → ∃ n, wlp stepR (Q n) s := by
  intro h
  obtain ⟨n, hn⟩ := h (fun n t => t = n) 0 fun s' _ => ⟨s', rfl⟩
  have h1 : (1 : Nat) = n := hn 1 (Or.inl rfl)
  have h2 : (2 : Nat) = n := hn 2 (Or.inr rfl)
  omega

/-- Scope of the one-sided law: pointwise negation is ω-continuous in the one-sided sense of
`OmegaContinuous` although it is not monotone.  So `OmegaContinuous` alone does not imply
`Monotone`. -/
theorem omegaContinuous_negT : OmegaContinuous (negT : Transformer σ) :=
  fun _ _ _ h => ⟨0, fun h0 => h ⟨0, h0⟩⟩

/-- `omegaContinuous_negT` together with `not_monotone_negT`, on the one-point state type. -/
theorem omegaContinuous_negT_not_monotone :
    OmegaContinuous (negT : Transformer Unit) ∧ ¬ Monotone (negT : Transformer Unit) :=
  ⟨omegaContinuous_negT, not_monotone_negT⟩

/-- Positive: a miracle is ω-continuous.  The `wp` of the empty relation (no outcome at all)
with any non-abortion predicate establishes every postcondition on that predicate, and is
ω-continuous. -/
theorem omegaContinuous_wp_emptyR (term : Pred σ) : OmegaContinuous (wp emptyR term) :=
  fun _ _ _ h => ⟨0, h.1, fun _ hr => False.elim hr⟩

/-! ## `Directed` and `DirContinuous` -/

/-- Positive (`Directed`): the initial segments `{s | s ≤ n}` of `Nat` form a directed family. -/
theorem directed_le : Directed (fun (n s : Nat) => s ≤ n) := by
  refine ⟨⟨0⟩, fun i j => ⟨i + j, fun s hs => ?_, fun s hs => ?_⟩⟩
  · have hs' : s ≤ i := hs
    show s ≤ i + j
    omega
  · have hs' : s ≤ j := hs
    show s ≤ i + j
    omega

/-- Negative (`Directed`): the singletons `{n}` of `Nat` do not form a directed family. -/
theorem not_directed_eq : ¬ Directed (fun (n s : Nat) => s = n) := by
  intro h
  obtain ⟨k, h0, h1⟩ := h.2 0 1
  have e0 : (0 : Nat) = k := h0 0 rfl
  have e1 : (1 : Nat) = k := h1 1 rfl
  omega

/-- Negative (`Directed`): the empty family is not directed. -/
theorem not_directed_empty : ¬ Directed (fun (i : PEmpty.{u + 1}) => (i.elim : Pred σ)) :=
  fun h => by
    obtain ⟨i⟩ := h.1
    exact i.elim

/-- Positive (`DirContinuous`): the `wp` of `skip`, with any non-abortion predicate, is
continuous over directed families. -/
theorem dirContinuous_wp_skipR (term : Pred σ) : DirContinuous (wp skipR term) := by
  intro ι Q _ s h
  obtain ⟨ht, hw⟩ := h
  obtain ⟨i, hi⟩ := hw s rfl
  refine ⟨i, ht, ?_⟩
  intro s' hs
  have e : s' = s := hs
  rw [e]
  exact hi

/-- Positive (`DirContinuous`): angelic havoc is continuous over directed families. -/
theorem dirContinuous_angelic : DirContinuous (angelic : Transformer σ) := by
  intro ι Q _ s h
  obtain ⟨x, i, hx⟩ := h
  exact ⟨i, x, hx⟩

/-- Scope of the one-sided law: pointwise negation is continuous over directed families in the
one-sided sense of `DirContinuous`, although it is not monotone. -/
theorem dirContinuous_negT : DirContinuous (negT : Transformer σ) := by
  intro ι Q hdir s h
  obtain ⟨i₀⟩ := hdir.1
  exact ⟨i₀, fun h0 => h ⟨i₀, h0⟩⟩

/-- Negative (`DirContinuous`): `eventually` is not continuous over directed families (it is
not even ω-continuous). -/
theorem not_dirContinuous_eventually : ¬ DirContinuous eventually :=
  fun h => not_omegaContinuous_eventually (omegaContinuous_of_dirContinuous h)

/-- Negative (`DirContinuous`): the `wlp` of `havoc` on `Nat` is not continuous over directed
families. -/
theorem not_dirContinuous_wlp_havocR_nat : ¬ DirContinuous (wlp (havocR : Rel Nat)) :=
  fun h => not_omegaContinuous_wlp_havocR_nat (omegaContinuous_of_dirContinuous h)

/-! ## `relOf` and `termOf` -/

/-- Positive: `relOf` recovers the identity relation from the `wlp` of `skip`. -/
theorem relOf_wlp_skipR : relOf (wlp (skipR : Rel σ)) = skipR := by
  apply rel_ext
  intro s s'
  constructor
  · intro h
    exact h (fun t => t = s) (fun _ ht => ht)
  · intro h Q hQ
    exact hQ s' h

/-- `relOf eventually` is the empty relation: from the point of view of `relOf`, `eventually`
has no possible outcome. -/
theorem relOf_eventually : relOf eventually = emptyR := by
  apply rel_ext
  intro s s'
  constructor
  · intro h
    have hne : eventually (fun t => t ≠ s') s := ⟨s' + 1, fun n hn hns => by omega⟩
    exact h _ hne rfl
  · intro h
    exact False.elim h

/-- Negative: the round trip through `relOf` does not recover `eventually`. -/
theorem wlp_relOf_eventually_ne : wlp (relOf eventually) ≠ eventually := by
  intro h
  have h1 : wlp (relOf eventually) (fun _ => False) 0 := by
    rw [relOf_eventually]
    intro s' hs
    exact hs
  rw [h] at h1
  exact strict_eventually 0 h1

/-- Negative (`termOf`): the partial decrement does not terminate at `0`. -/
theorem not_termOf_wp_predR_zero : ¬ termOf (wp predR posP) 0 := by
  rw [termOf_wp]
  exact fun h => h rfl

/-- Positive (`termOf`): the partial decrement terminates at `1`. -/
theorem termOf_wp_predR_one : termOf (wp predR posP) 1 := by
  rw [termOf_wp]
  show (1 : Nat) ≠ 0
  omega

/-! ## `FiniteImage` -/

/-- Positive: `stepR` has a finite image at every state. -/
theorem finiteImage_stepR (s : Nat) : FiniteImage stepR s := by
  refine ⟨[s + 1, s + 2], ?_⟩
  intro s' hs
  have hs' : s' = s + 1 ∨ s' = s + 2 := hs
  rcases hs' with e | e
  · rw [e]
    exact List.mem_cons_self
  · rw [e]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-- Positive: `skip` has a finite image at every state. -/
theorem finiteImage_skipR (s : σ) : FiniteImage skipR s := by
  refine ⟨[s], ?_⟩
  intro s' hs
  have e : s' = s := hs
  rw [e]
  exact List.mem_cons_self

/-- Positive: the empty relation has a finite (empty) image at every state. -/
theorem finiteImage_emptyR (s : σ) : FiniteImage emptyR s :=
  ⟨[], fun _ h => False.elim h⟩

/-- Every list of natural numbers has a strict upper bound. -/
theorem list_nat_bounded (l : List Nat) : ∃ b, ∀ x, x ∈ l → x < b := by
  induction l with
  | nil => exact ⟨0, fun x hx => (by cases hx)⟩
  | cons a l ih =>
    obtain ⟨b, hb⟩ := ih
    refine ⟨a + b + 1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with e | hx'
    · omega
    · have := hb x hx'
      omega

/-- Negative: `havoc` on `Nat` has an infinite image at every state. -/
theorem not_finiteImage_havocR_nat (s : Nat) : ¬ FiniteImage (havocR : Rel Nat) s := by
  intro h
  obtain ⟨l, hl⟩ := h
  obtain ⟨b, hb⟩ := list_nat_bounded l
  have := hb b (hl b trivial)
  omega

/-! ## `TotalOn` -/

/-- Positive: the decrement has a successor at every nonzero state. -/
theorem totalOn_predR_posP : TotalOn predR posP := by
  intro s hs
  have hs' : s ≠ 0 := hs
  exact ⟨s - 1, show s = s - 1 + 1 by omega⟩

/-- Negative: the decrement is not total on all states (`0` has no successor). -/
theorem not_totalOn_predR_true : ¬ TotalOn predR (fun _ => True) := by
  intro h
  obtain ⟨s', hs'⟩ := h 0 trivial
  have e : 0 = s' + 1 := hs'
  omega

/-! ## `ChaosNormal` -/

/-- Positive: a pair whose termination predicate holds everywhere is in chaos normal form. -/
theorem chaosNormal_of_forall_term (R : Rel σ) (term : Pred σ) (h : ∀ s, term s) :
    ChaosNormal R term :=
  fun s hs => (hs (h s)).elim

/-- Positive: `havoc` with any termination predicate is in chaos normal form. -/
theorem chaosNormal_havocR (term : Pred σ) : ChaosNormal havocR term :=
  fun _ _ _ => trivial

/-- Negative: the partial decrement with termination predicate `posP` is not in chaos normal
form (`0` is non-terminating but is not related to every state). -/
theorem not_chaosNormal_predR_posP : ¬ ChaosNormal predR posP := by
  intro h
  have e : (0 : Nat) = 0 + 1 := h 0 (fun hp => hp rfl) 0
  omega

/-! ## `RefinedBy` -/

/-- Positive: `abortT` is refined by every transformer. -/
theorem abortT_refinedBy (T : Transformer σ) : RefinedBy abortT T :=
  fun _ _ h => False.elim h

/-- Positive: `havoc` is refined by `stepR` (less nondeterminism). -/
theorem refinedBy_havocR_stepR : RefinedBy (wlp (havocR : Rel Nat)) (wlp stepR) :=
  fun _ _ h s' _ => h s' trivial

/-- Negative: `stepR` is not refined by `havoc` (more nondeterminism). -/
theorem not_refinedBy_stepR_havocR : ¬ RefinedBy (wlp stepR) (wlp (havocR : Rel Nat)) := by
  intro h
  have h1 : 0 < 0 := h (fun n => 0 < n) 0 wlp_stepR_pos 0 trivial
  omega

/-! ## `CountableState` -/

/-- Positive: `Nat` is countable. -/
theorem countableState_nat : CountableState Nat := ⟨id, fun _ _ h => h⟩

/-- Positive: `Bool` is countable. -/
theorem countableState_bool : CountableState Bool := by
  refine ⟨fun b => cond b 1 0, ?_⟩
  intro x y h
  cases x <;> cases y <;> first | rfl | cases h

/-- Negative: the type of infinite bit sequences is not countable (Cantor's diagonal
argument). -/
theorem not_countableState_nat_to_bool : ¬ CountableState (Nat → Bool) := by
  intro hc
  obtain ⟨f, hf⟩ := hc
  let d : Nat → Bool := fun n =>
    @decide (∀ g : Nat → Bool, f g = n → g n = false) (Classical.propDecidable _)
  cases hb : d (f d) with
  | true =>
    have h1 : ∀ g : Nat → Bool, f g = f d → g (f d) = false :=
      @of_decide_eq_true _ (Classical.propDecidable _) hb
    have h2 := h1 d rfl
    rw [hb] at h2
    cases h2
  | false =>
    have h1 : ¬ ∀ g : Nat → Bool, f g = f d → g (f d) = false :=
      @of_decide_eq_false _ (Classical.propDecidable _) hb
    apply h1
    intro g hg
    have e : g = d := hf _ _ hg
    rw [e]
    exact hb

/-! ## `ContinuumState` -/

/-- Positive: the type of infinite bit sequences has at most the cardinality of the continuum
(although it is not countable, `not_countableState_nat_to_bool`). -/
theorem continuumState_nat_to_bool : ContinuumState (Nat → Bool) := ⟨id, fun _ _ h => h⟩

/-- Positive: `Nat` has at most the cardinality of the continuum. -/
theorem continuumState_nat : ContinuumState Nat :=
  continuumState_of_countableState countableState_nat

/-- Cantor's theorem in the form needed here: no type `α` admits an injection from `α → Bool`
into `α`. -/
theorem no_injection_pred_bool (α : Type u) :
    ¬ ∃ f : (α → Bool) → α, ∀ x y, f x = f y → x = y := by
  intro hc
  obtain ⟨f, hf⟩ := hc
  let d : α → Bool := fun a =>
    @decide (∃ g : α → Bool, f g = a ∧ g a = false) (Classical.propDecidable _)
  cases hb : d (f d) with
  | true =>
    have h1 : ∃ g : α → Bool, f g = f d ∧ g (f d) = false :=
      @of_decide_eq_true _ (Classical.propDecidable _) hb
    obtain ⟨g, hg, hgf⟩ := h1
    have e : g = d := hf _ _ hg
    rw [e, hb] at hgf
    cases hgf
  | false =>
    have h1 : ¬ ∃ g : α → Bool, f g = f d ∧ g (f d) = false :=
      @of_decide_eq_false _ (Classical.propDecidable _) hb
    exact h1 ⟨d, rfl, hb⟩

/-- Negative: the type of predicates on infinite bit sequences, `(Nat → Bool) → Bool`, does
not inject into `Nat → Bool` (Cantor). -/
theorem not_continuumState_pred_nat_to_bool : ¬ ContinuumState ((Nat → Bool) → Bool) := by
  intro h
  obtain ⟨f, hf⟩ := h
  exact no_injection_pred_bool (Nat → Bool) ⟨f, hf⟩

/-! ## `FiniteState` -/

/-- Positive: `Bool` is a finite state type. -/
theorem finiteState_bool : FiniteState Bool := by
  refine ⟨[true, false], ?_⟩
  intro x
  cases x
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_self

/-- Negative: `Nat` is not a finite state type. -/
theorem not_finiteState_nat : ¬ FiniteState Nat := by
  intro h
  obtain ⟨l, hl⟩ := h
  obtain ⟨b, hb⟩ := list_nat_bounded l
  have := hb b (hl b)
  omega

/-! ## `comp`, `seqTerm`, `union` -/

/-- Positive: two `stepR` steps can go from `0` to `3`. -/
theorem comp_stepR_example : comp stepR stepR 0 3 :=
  ⟨1, Or.inl rfl, Or.inr rfl⟩

/-- Negative: two `stepR` steps cannot go from `0` to `1`. -/
theorem not_comp_stepR_example : ¬ comp stepR stepR 0 1 := by
  intro h
  obtain ⟨m, h1, h2⟩ := h
  have h1' : m = 0 + 1 ∨ m = 0 + 2 := h1
  have h2' : 1 = m + 1 ∨ 1 = m + 2 := h2
  omega

/-- Positive: `skip` followed by the partial decrement terminates from `1`. -/
theorem seqTerm_example : seqTerm skipR (fun _ => True) posP 1 := by
  refine ⟨trivial, ?_⟩
  intro s' hs
  have e : s' = 1 := hs
  rw [e]
  show (1 : Nat) ≠ 0
  omega

/-- Negative: `skip` followed by the partial decrement does not terminate from `0`. -/
theorem not_seqTerm_example : ¬ seqTerm skipR (fun _ => True) posP 0 :=
  fun h => h.2 0 rfl rfl

/-- Positive: the choice between `skip` and `stepR` may stay at `0`. -/
theorem union_example : union skipR stepR 0 0 := Or.inl rfl

/-- Negative: the choice between `skip` and `stepR` cannot go from `0` to `3`. -/
theorem not_union_example : ¬ union skipR stepR 0 3 := by
  intro h
  have h' : (3 : Nat) = 0 ∨ ((3 : Nat) = 0 + 1 ∨ (3 : Nat) = 0 + 2) := h
  omega

end Toy.PredTrans
