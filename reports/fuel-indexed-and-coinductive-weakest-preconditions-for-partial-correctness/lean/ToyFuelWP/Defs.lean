/-!
# Fuel-indexed and fixpoint weakest preconditions: definitions

This module fixes the toy model used throughout the package.

* A `System σ` is a small-step transition *relation* `step : σ → σ → Prop`
  (possibly nondeterministic, possibly infinitely branching) together with a
  predicate `terminal : σ → Prop` of halted states.
  A relation rather than a step function is used because the total-correctness
  results are about nondeterminism (finite versus infinite branching); a
  deterministic step function is the special case `Deterministic` (see
  `ofStepFn`).
* **Convention: terminal states halt.** Every weakest precondition, every run
  notion (`Reach`, `HasInfiniteRun`, `AlwaysDiverges`, `AllRunsEventually`) and
  every branching notion (`FinitelyBranching*`, `Deterministic`) inspects the
  successors of a state only when the state is *not* terminal; `step` edges
  leaving a terminal state are ignored by all of them. The raw helper
  `CanStep` looks only at the relation; every use of it in this package is
  guarded by `¬ S.terminal`.
* The case structure of `wpStep` ("if the state is terminal the postcondition
  holds; otherwise it can step and every successor satisfies the
  continuation") is the case structure of the weakest precondition of
  Iris-style program logics. It is *not* the same operator: Iris decides
  value-hood with a computable test, wraps the recursive occurrence in
  update modalities (which quantify existentially over ghost-state updates)
  and in a later modality, and takes a guarded (step-indexed) fixpoint.
  The results of this package rely on the recursive occurrence appearing only
  under universal quantification and implication (see the non-claims of the
  partial-correctness cards).
* `wpStep` is written with implications, `(terminal → Q) ∧ (¬ terminal → …)`,
  not with a disjunction. This keeps the partial-correctness results
  constructive (a disjunctive adequacy statement for all systems implies
  excluded middle), but it means that, without classical logic or a decidable
  `terminal`, a total-correctness judgement only yields `¬¬ terminal` at the
  end of a run (`wpFuelTotal_propSys_one_iff_not_not`).
* A state is **stuck** when it is not terminal and has no successor. Stuck
  states model run-time errors (undefined behaviour, failed assertions,
  panics); every weakest precondition below rejects them. (Calculi in which a
  command without outcomes is *miraculous* — satisfies every precondition —
  treat such states differently; here `wpLfp` obeys the law of the excluded
  miracle, `wpLfp_excluded_miracle`.)

The fuel-indexed transformers `wpFuel` and `wpFuelTotal` are defined by
structural recursion on a natural-number fuel counter; they differ only in the
value at fuel `0` (`True` for partial correctness, `False` for total
correctness). The fixpoint transformers `wpGfp` and `wpLfp` are the greatest
and least fixpoints of the same one-step operator `wpStep`, written
impredicatively (union of all post-fixed predicates, intersection of all
pre-fixed predicates) so that no coinductive types, `partial` definitions or
library fixpoint constructions are needed.

Only core Lean is used.
-/

namespace Toy.FuelWP

universe u

/-- A small-step transition system: a (possibly nondeterministic) one-step
relation and a predicate of terminal (halted) states.

It is meant to capture the operational semantics of a program: `step s t`
says that the machine can move from configuration `s` to configuration `t` in
one step, and `terminal s` says that `s` is a final configuration (for example
"the program returned"). Nothing is required of the two fields; in particular
terminal states may have outgoing edges, which every weakest precondition, run
notion and branching notion in this package ignores (only the raw helper
`CanStep` sees them). -/
structure System (σ : Type u) where
  /-- One-step transition relation (possibly nondeterministic). -/
  step : σ → σ → Prop
  /-- Terminal (halted, final) states. -/
  terminal : σ → Prop

variable {σ : Type u}

/-- `CanStep S s`: the state `s` has at least one successor in the raw relation
("`s` is reducible"). This is a raw helper: it does not apply the
terminal-states-halt convention (`CanStep termLoopSys ()` holds although no run
prefix leaves that terminal state), and every use of it in this package is
guarded by `¬ S.terminal s`. -/
def CanStep (S : System σ) (s : σ) : Prop := ∃ t, S.step s t

/-- `Stuck S s`: `s` is not terminal and has no successor. This is how run-time
errors are modelled. -/
def Stuck (S : System σ) (s : σ) : Prop := ¬ S.terminal s ∧ ∀ t, ¬ S.step s t

/-- The one-step weakest-precondition operator shared by every transformer in
the package.

`wpStep S Q X s` holds when: if `s` is terminal then the postcondition `Q`
holds at `s`; and if `s` is not terminal then `s` can step and every successor
satisfies `X`. (Successors of terminal states are ignored.) -/
def wpStep (S : System σ) (Q X : σ → Prop) (s : σ) : Prop :=
  (S.terminal s → Q s) ∧ (¬ S.terminal s → CanStep S s ∧ ∀ t, S.step s t → X t)

/-- **Partial-correctness fuel-indexed weakest precondition.**
`wpFuel S n Q s` is defined by structural recursion on the fuel `n`:
at fuel `0` it is `True` (running out of fuel counts as success), and
`wpFuel S (n+1) Q = wpStep S Q (wpFuel S n Q)`.

It captures what a framework without coinduction or general recursion can
define for partial correctness: "no error and no `Q`-violation is observable
within the first `n` observations of the run". -/
def wpFuel (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => True
  | n + 1, Q => wpStep S Q (wpFuel S n Q)

/-- **Total-correctness fuel-indexed weakest precondition.**
Identical to `wpFuel` except that running out of fuel counts as failure:
`wpFuelTotal S 0 Q s = False`. It captures "every run halts in a state
satisfying `Q`, without error, within the fuel budget". A terminal state
needs fuel `1`. -/
def wpFuelTotal (S : System σ) : Nat → (σ → Prop) → σ → Prop
  | 0, _ => fun _ => False
  | n + 1, Q => wpStep S Q (wpFuelTotal S n Q)

/-- `X` is a post-fixed point of `wpStep S Q` (`X ⊆ wpStep S Q X`): an invariant
that is never stuck, implies `Q` at terminal states, and is preserved by every
step from a non-terminal state. -/
def PostFixed (S : System σ) (Q X : σ → Prop) : Prop := ∀ s, X s → wpStep S Q X s

/-- `X` is a pre-fixed point of `wpStep S Q` (`wpStep S Q X ⊆ X`). -/
def PreFixed (S : System σ) (Q X : σ → Prop) : Prop := ∀ s, wpStep S Q X s → X s

/-- **Partial-correctness weakest precondition as a greatest fixpoint.**
`wpGfp S Q` is the union of all post-fixed points of `wpStep S Q`
("there is an invariant containing `s`"). By `wpGfp_unfold` and
`wpGfp_coinduction` it is the greatest fixpoint of `wpStep S Q`.

It captures the coinductive (greatest-fixpoint) definition of partial
correctness used by frameworks with coinduction: the run from `s` never
reaches an error and, if it halts, halts in `Q`; divergence is allowed. -/
def wpGfp (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∃ X : σ → Prop, PostFixed S Q X ∧ X s

/-- **Total-correctness weakest precondition as a least fixpoint.**
`wpLfp S Q` is the intersection of all pre-fixed points of `wpStep S Q`.
By `wpLfp_unfold` and `wpLfp_induction` it is the least fixpoint of
`wpStep S Q`.

It captures total correctness: every run from `s` halts, without error, in a
state satisfying `Q`. -/
def wpLfp (S : System σ) (Q : σ → Prop) (s : σ) : Prop :=
  ∀ X : σ → Prop, PreFixed S Q X → X s

/-- `Reach S s k t`: there is a run prefix of exactly `k` steps from `s` to `t`
in which every step is taken from a non-terminal state (terminal states halt,
so a run prefix never continues past one). -/
inductive Reach (S : System σ) : σ → Nat → σ → Prop
  /-- The empty run prefix. -/
  | refl (s : σ) : Reach S s 0 s
  /-- Extend a run prefix at the front by one step from a non-terminal state. -/
  | step {s t u : σ} {k : Nat} :
      ¬ S.terminal s → S.step s t → Reach S t k u → Reach S s (k + 1) u

/-- `RunEndOk S Q t`: a run prefix ending in `t` is acceptable for partial
correctness: if `t` is terminal (the run has ended) then `Q t`, and if `t` is
not terminal then the run can be extended (`t` has a successor). Equivalently,
`t` is not stuck and satisfies `Q` if terminal. Written with implications so
that it is constructive; `runEndOk_iff_or` gives the disjunctive reading
("ends in a terminal state satisfying `Q`, or is extendable") and
`runEndOk_iff_not_stuck` the "not stuck" reading, both classically. -/
def RunEndOk (S : System σ) (Q : σ → Prop) (t : σ) : Prop :=
  (S.terminal t → Q t) ∧ (¬ S.terminal t → CanStep S t)

/-- `HasInfiniteRun S s`: some run from `s` never halts — an infinite sequence
of states starting at `s` in which every state is non-terminal and steps to the
next. -/
def HasInfiniteRun (S : System σ) (s : σ) : Prop :=
  ∃ f : Nat → σ, f 0 = s ∧ ∀ i, ¬ S.terminal (f i) ∧ S.step (f i) (f (i + 1))

/-- `AlwaysDiverges S s`: *must-divergence without getting stuck* — every state
reachable from `s` is non-terminal and can step, so no run halts and no run
gets stuck. Contrast `HasInfiniteRun S s` (*may-divergence*: some run is
infinite, while other runs may halt or get stuck). -/
def AlwaysDiverges (S : System σ) (s : σ) : Prop :=
  ∀ k t, Reach S s k t → ¬ S.terminal t ∧ CanStep S t

/-- `FinitelyBranchingAt S t`: the successors of `t` are contained in a finite
list. -/
def FinitelyBranchingAt (S : System σ) (t : σ) : Prop :=
  ∃ l : List σ, ∀ u, S.step t u → u ∈ l

/-- `FinitelyBranchingFrom S s`: every non-terminal state reachable from `s`
is finitely branching. (Successors of terminal states are irrelevant.) -/
def FinitelyBranchingFrom (S : System σ) (s : σ) : Prop :=
  ∀ k t, Reach S s k t → ¬ S.terminal t → FinitelyBranchingAt S t

/-- `FinitelyBranching S`: every non-terminal state is finitely branching. -/
def FinitelyBranching (S : System σ) : Prop :=
  ∀ t, ¬ S.terminal t → FinitelyBranchingAt S t

/-- `Deterministic S`: every non-terminal state has at most one successor.
(Edges leaving terminal states are ignored, as everywhere in this package.) -/
def Deterministic (S : System σ) : Prop :=
  ∀ t, ¬ S.terminal t → ∀ u v, S.step t u → S.step t v → u = v

/-- The system induced by a partial step function `next` (as in an
interpreter): `s` steps to `t` iff `next s = some t`, and `halted` marks
terminal states. A non-halted state with `next s = none` is stuck. -/
def ofStepFn (next : σ → Option σ) (halted : σ → Prop) : System σ where
  step s t := next s = some t
  terminal := halted

/-- `AllRunsEventually S P s` (the CTL-style property "AF P"): along every
run from `s`, a state satisfying `P` is eventually reached; a run that halts
or gets stuck before reaching `P` violates it. This is the liveness property
"eventually outputs" when `P` marks the states that have produced the output.
-/
inductive AllRunsEventually (S : System σ) (P : σ → Prop) : σ → Prop
  /-- `P` holds now. -/
  | now {s : σ} : P s → AllRunsEventually S P s
  /-- `s` is non-terminal, can step, and every successor eventually reaches `P`. -/
  | later {s : σ} : ¬ S.terminal s → CanStep S s →
      (∀ t, S.step s t → AllRunsEventually S P t) → AllRunsEventually S P s

/-! ## Basic facts (definitional adequacy of the fixpoints) -/

section Basic

variable {S : System σ} {Q : σ → Prop}

theorem wpFuel_zero (S : System σ) (Q : σ → Prop) (s : σ) : wpFuel S 0 Q s ↔ True :=
  Iff.rfl

theorem wpFuel_succ (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuel S (n + 1) Q s ↔ wpStep S Q (wpFuel S n Q) s :=
  Iff.rfl

theorem wpFuelTotal_zero (S : System σ) (Q : σ → Prop) (s : σ) :
    wpFuelTotal S 0 Q s ↔ False :=
  Iff.rfl

theorem wpFuelTotal_succ (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuelTotal S (n + 1) Q s ↔ wpStep S Q (wpFuelTotal S n Q) s :=
  Iff.rfl

/-- `wpStep` is monotone in the continuation predicate. -/
theorem wpStep_mono {X Y : σ → Prop} (hXY : ∀ t, X t → Y t) {s : σ}
    (h : wpStep S Q X s) : wpStep S Q Y s :=
  ⟨h.1, fun hnt => ⟨(h.2 hnt).1, fun t ht => hXY t ((h.2 hnt).2 t ht)⟩⟩

/-- `wpGfp S Q` is itself a post-fixed point. -/
theorem wpGfp_postFixed (S : System σ) (Q : σ → Prop) : PostFixed S Q (wpGfp S Q) := by
  intro s ⟨X, hX, hs⟩
  exact wpStep_mono (fun t ht => ⟨X, hX, ht⟩) (hX s hs)

/-- Coinduction: every post-fixed point is contained in `wpGfp`
(so `wpGfp` is the greatest post-fixed point). -/
theorem wpGfp_coinduction {X : σ → Prop} (hX : PostFixed S Q X) {s : σ} (hs : X s) :
    wpGfp S Q s :=
  ⟨X, hX, hs⟩

/-- `wpGfp S Q` is a fixed point of `wpStep S Q`. -/
theorem wpGfp_unfold (S : System σ) (Q : σ → Prop) (s : σ) :
    wpGfp S Q s ↔ wpStep S Q (wpGfp S Q) s := by
  constructor
  · exact wpGfp_postFixed S Q s
  · intro h
    refine ⟨fun t => wpStep S Q (wpGfp S Q) t, ?_, h⟩
    intro t ht
    exact wpStep_mono (fun u hu => wpGfp_postFixed S Q u hu) ht

/-- `wpLfp S Q` is itself a pre-fixed point. -/
theorem wpLfp_preFixed (S : System σ) (Q : σ → Prop) : PreFixed S Q (wpLfp S Q) := by
  intro s h X hX
  exact hX s (wpStep_mono (fun t ht => ht X hX) h)

/-- Induction: `wpLfp` is contained in every pre-fixed point
(so `wpLfp` is the least pre-fixed point). -/
theorem wpLfp_induction {X : σ → Prop} (hX : PreFixed S Q X) {s : σ} (hs : wpLfp S Q s) :
    X s :=
  hs X hX

/-- `wpLfp S Q` is a fixed point of `wpStep S Q`. -/
theorem wpLfp_unfold (S : System σ) (Q : σ → Prop) (s : σ) :
    wpLfp S Q s ↔ wpStep S Q (wpLfp S Q) s := by
  constructor
  · intro h
    apply h (fun t => wpStep S Q (wpLfp S Q) t)
    intro t ht
    exact wpStep_mono (fun u hu => wpLfp_preFixed S Q u hu) ht
  · exact wpLfp_preFixed S Q s

/-- Invariants propagate along run prefixes. -/
theorem PostFixed.reach {X : σ → Prop} (hX : PostFixed S Q X) {s t : σ} {k : Nat}
    (hs : X s) (h : Reach S s k t) : X t := by
  induction h with
  | refl _ => exact hs
  | step hnt hst _ ih => exact ih (((hX _ hs).2 hnt).2 _ hst)

theorem reach_zero_iff {s t : σ} : Reach S s 0 t ↔ t = s := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    subst h
    exact Reach.refl t

theorem reach_succ_iff {s u : σ} {k : Nat} :
    Reach S s (k + 1) u ↔ ∃ t, ¬ S.terminal s ∧ S.step s t ∧ Reach S t k u := by
  constructor
  · intro h
    cases h with
    | step hnt hst hr => exact ⟨_, hnt, hst, hr⟩
  · rintro ⟨t, hnt, hst, hr⟩
    exact Reach.step hnt hst hr

/-- Classically, `RunEndOk` is the disjunction "terminal and `Q`, or
non-terminal and extendable". -/
theorem runEndOk_iff_or (S : System σ) (Q : σ → Prop) (t : σ) :
    RunEndOk S Q t ↔ (S.terminal t ∧ Q t) ∨ (¬ S.terminal t ∧ CanStep S t) := by
  constructor
  · intro ⟨h1, h2⟩
    by_cases ht : S.terminal t
    · exact Or.inl ⟨ht, h1 ht⟩
    · exact Or.inr ⟨ht, h2 ht⟩
  · rintro (⟨ht, hq⟩ | ⟨ht, hc⟩)
    · exact ⟨fun _ => hq, fun hn => absurd ht hn⟩
    · exact ⟨fun h => absurd h ht, fun _ => hc⟩

/-- `RunEndOk` is exactly fuel `1`. -/
theorem wpFuel_one_iff_runEndOk (S : System σ) (Q : σ → Prop) (t : σ) :
    wpFuel S 1 Q t ↔ RunEndOk S Q t := by
  constructor
  · intro h
    exact ⟨h.1, fun hn => (h.2 hn).1⟩
  · intro h
    exact ⟨h.1, fun hn => ⟨h.2 hn, fun _ _ => trivial⟩⟩

/-- `RunEndOk` is "not stuck, and `Q` if terminal". (Classical: the backward
direction uses `Classical.byContradiction` to extract a successor from
"not stuck".) -/
theorem runEndOk_iff_not_stuck (S : System σ) (Q : σ → Prop) (t : σ) :
    RunEndOk S Q t ↔ (S.terminal t → Q t) ∧ ¬ Stuck S t := by
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, fun ⟨hn, hno⟩ => ?_⟩
    obtain ⟨u, hu⟩ := h2 hn
    exact hno u hu
  · intro ⟨h1, h2⟩
    refine ⟨h1, fun hn => ?_⟩
    apply Classical.byContradiction
    intro hc
    exact h2 ⟨hn, fun u hu => hc ⟨u, hu⟩⟩

theorem AlwaysDiverges.here {s : σ} (h : AlwaysDiverges S s) :
    ¬ S.terminal s ∧ CanStep S s :=
  h 0 s (Reach.refl s)

theorem AlwaysDiverges.succ {s t : σ} (h : AlwaysDiverges S s) (hst : S.step s t) :
    AlwaysDiverges S t :=
  fun k u hr => h (k + 1) u (Reach.step h.here.1 hst hr)

theorem FinitelyBranchingFrom.here {s : σ} (h : FinitelyBranchingFrom S s)
    (hnt : ¬ S.terminal s) : FinitelyBranchingAt S s :=
  h 0 s (Reach.refl s) hnt

theorem FinitelyBranchingFrom.succ {s t : σ} (h : FinitelyBranchingFrom S s)
    (hnt : ¬ S.terminal s) (hst : S.step s t) : FinitelyBranchingFrom S t :=
  fun k u hr hu => h (k + 1) u (Reach.step hnt hst hr) hu

/-- Global finite branching implies finite branching from every state. -/
theorem finitelyBranchingFrom_of_finitelyBranching (h : FinitelyBranching S) (s : σ) :
    FinitelyBranchingFrom S s :=
  fun _ t _ hnt => h t hnt

/-- Deterministic systems are finitely branching. (Classical: the list is
`[u]` if a successor `u` exists and `[]` otherwise.) -/
theorem finitelyBranching_of_deterministic (h : Deterministic S) : FinitelyBranching S := by
  intro t ht
  by_cases hc : CanStep S t
  · obtain ⟨u, hu⟩ := hc
    exact ⟨[u], fun v hv => by rw [h t ht u v hu hv]; exact List.mem_singleton.mpr rfl⟩
  · exact ⟨[], fun v hv => absurd ⟨v, hv⟩ hc⟩

/-- Systems induced by step functions are deterministic. -/
theorem ofStepFn_deterministic (next : σ → Option σ) (halted : σ → Prop) :
    Deterministic (ofStepFn next halted) := by
  intro t _ u v hu hv
  have h : some u = some v := hu.symm.trans hv
  injection h

end Basic

end Toy.FuelWP
