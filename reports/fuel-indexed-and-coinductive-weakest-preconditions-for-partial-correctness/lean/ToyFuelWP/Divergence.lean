import ToyFuelWP.Systems

/-!
# Divergence and liveness (fully proved)

Partial-correctness weakest preconditions (`wpFuel`, `wpGfp`) cannot see
divergence: a state from which every run diverges satisfies all of them, for
every postcondition. Total-correctness weakest preconditions (`wpFuelTotal`,
`wpLfp`) reject every state with even one infinite run. Consequently no
positive partial-correctness weakest precondition (`wpGfp S Q`,
`wpFuel S n Q`, `∀ n, wpFuel S n Q`) equals a predicate that is false at an
always-diverging state; a liveness property such as "every run eventually
produces the output" is one such predicate on the systems below. Negations of
partial-correctness weakest preconditions are not covered (see
`ToyFuelWP.Boundaries`).
-/

namespace Toy.FuelWP

universe u

variable {σ : Type u}

section General

variable {S : System σ}

/-- A state from which every run diverges satisfies the partial-correctness
fuel WP at every fuel, for every postcondition. -/
theorem wpFuel_of_alwaysDiverges {s : σ} (h : AlwaysDiverges S s) (n : Nat) (Q : σ → Prop) :
    wpFuel S n Q s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    exact ⟨fun ht => absurd ht h.here.1, fun _ => ⟨h.here.2, fun t hst => ih (h.succ hst)⟩⟩

/-- A state from which every run diverges satisfies the greatest-fixpoint
partial-correctness WP for every postcondition. -/
theorem wpGfp_of_alwaysDiverges {s : σ} (h : AlwaysDiverges S s) (Q : σ → Prop) :
    wpGfp S Q s :=
  ⟨AlwaysDiverges S,
    fun _ ht => ⟨fun htt => absurd htt ht.here.1, fun _ => ⟨ht.here.2, fun _ hu => ht.succ hu⟩⟩,
    h⟩

/-- A state with an infinite run fails the total-correctness fuel WP at every
fuel, for every postcondition. -/
theorem not_wpFuelTotal_of_hasInfiniteRun {s : σ} (h : HasInfiniteRun S s) (n : Nat)
    (Q : σ → Prop) : ¬ wpFuelTotal S n Q s := by
  induction n generalizing s with
  | zero => exact fun hw => hw
  | succ n ih =>
    intro hw
    obtain ⟨f, hf0, hf⟩ := h
    subst hf0
    have hw' : wpFuelTotal S n Q (f 1) := (hw.2 (hf 0).1).2 (f 1) (hf 0).2
    exact ih ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩ hw'

/-- A state with an infinite run fails the least-fixpoint total-correctness WP,
for every postcondition. -/
theorem not_wpLfp_of_hasInfiniteRun {s : σ} (h : HasInfiniteRun S s) (Q : σ → Prop) :
    ¬ wpLfp S Q s := by
  intro hl
  have key : PreFixed S Q (fun t => ¬ HasInfiniteRun S t) := by
    intro u hu ⟨f, hf0, hf⟩
    subst hf0
    exact (hu.2 (hf 0).1).2 (f 1) (hf 0).2 ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩
  exact wpLfp_induction key hl h

/-- A state from which every run diverges fails the least-fixpoint total WP
(proved without choice). -/
theorem not_wpLfp_of_alwaysDiverges {s : σ} (h : AlwaysDiverges S s) (Q : σ → Prop) :
    ¬ wpLfp S Q s := by
  intro hl
  have key : PreFixed S Q (fun t => ¬ AlwaysDiverges S t) := by
    intro u hu hd
    obtain ⟨v, hv⟩ := hd.here.2
    exact (hu.2 hd.here.1).2 v hv (hd.succ hv)
  exact wpLfp_induction key hl h

/-- A state from which every run diverges fails the total fuel WP at every
fuel (proved without choice). -/
theorem not_wpFuelTotal_of_alwaysDiverges {s : σ} (h : AlwaysDiverges S s) (n : Nat)
    (Q : σ → Prop) : ¬ wpFuelTotal S n Q s := by
  induction n generalizing s with
  | zero => exact fun hw => hw
  | succ n ih =>
    intro hw
    obtain ⟨t, hst⟩ := h.here.2
    exact ih (h.succ hst) ((hw.2 h.here.1).2 t hst)

/-- If every run from `s` diverges then some run from `s` is infinite
(uses choice). -/
theorem alwaysDiverges_imp_hasInfiniteRun {s : σ} (h : AlwaysDiverges S s) :
    HasInfiniteRun S s := by
  have hnext : ∀ d : {t : σ // AlwaysDiverges S t},
      ∃ e : {t : σ // AlwaysDiverges S t}, S.step d.1 e.1 := fun d =>
    match d.2.here.2 with
    | ⟨u, hu⟩ => ⟨⟨u, d.2.succ hu⟩, hu⟩
  let nx : {t : σ // AlwaysDiverges S t} → {t : σ // AlwaysDiverges S t} :=
    fun d => Classical.choose (hnext d)
  let g : Nat → {t : σ // AlwaysDiverges S t} :=
    fun i => Nat.rec (motive := fun _ => {t : σ // AlwaysDiverges S t}) ⟨s, h⟩ (fun _ d => nx d) i
  refine ⟨fun i => (g i).1, rfl, fun i => ⟨(g i).2.here.1, ?_⟩⟩
  exact Classical.choose_spec (hnext (g i))

/-! ### Packaged statements -/

/-- **Divergence satisfies every partial-correctness WP and no
total-correctness WP.** If every run from `s` diverges (`AlwaysDiverges`),
then for every postcondition `Q` and fuel `n`: `wpFuel S n Q s` and
`wpGfp S Q s` hold, while `wpFuelTotal S n Q s` and `wpLfp S Q s` fail. -/
theorem alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp (S : System σ) (s : σ)
    (h : AlwaysDiverges S s) :
    (∀ n Q, wpFuel S n Q s) ∧ (∀ Q, wpGfp S Q s) ∧
      (∀ n Q, ¬ wpFuelTotal S n Q s) ∧ (∀ Q, ¬ wpLfp S Q s) :=
  ⟨wpFuel_of_alwaysDiverges h, wpGfp_of_alwaysDiverges h,
    not_wpFuelTotal_of_alwaysDiverges h, not_wpLfp_of_alwaysDiverges h⟩

/-- **One infinite run refutes every total-correctness WP.** If some run from
`s` is infinite, then for every postcondition `Q` and fuel `n`,
`wpFuelTotal S n Q s` and `wpLfp S Q s` fail. -/
theorem hasInfiniteRun_refutes_every_total_wp (S : System σ) (s : σ)
    (h : HasInfiniteRun S s) :
    (∀ n Q, ¬ wpFuelTotal S n Q s) ∧ (∀ Q, ¬ wpLfp S Q s) :=
  ⟨not_wpFuelTotal_of_hasInfiniteRun h, not_wpLfp_of_hasInfiniteRun h⟩

/-- **`wpGfp` of `False` is exactly "every run diverges"** (the analogue of
`wlp S false`). Equivalently (`forall_wpGfp_iff_alwaysDiverges`), `s`
satisfies the partial-correctness WP of every postcondition iff every run from
`s` diverges. -/
theorem wpGfp_false_iff_alwaysDiverges (S : System σ) (s : σ) :
    wpGfp S (fun _ => False) s ↔ AlwaysDiverges S s := by
  constructor
  · rintro ⟨X, hX, hs⟩ k t hr
    have ht := hX t (hX.reach hs hr)
    exact ⟨ht.1, (ht.2 ht.1).1⟩
  · intro h
    exact wpGfp_of_alwaysDiverges h _

theorem forall_wpGfp_iff_alwaysDiverges (S : System σ) (s : σ) :
    (∀ Q, wpGfp S Q s) ↔ AlwaysDiverges S s :=
  ⟨fun h => (wpGfp_false_iff_alwaysDiverges S s).mp (h _),
    fun h Q => wpGfp_of_alwaysDiverges h Q⟩

/-- **No positive partial-correctness WP expresses a predicate that is false
at an always-diverging state.** If `s` always diverges and the predicate
`R : σ → Prop` is false at `s`, then no postcondition `Q` makes `wpGfp S Q`
coincide with `R` on all states, and the same holds for `wpFuel S n Q` at
every fixed fuel `n` and for `fun t => ∀ n, wpFuel S n Q t`. The proof uses
nothing about `R` except `¬ R s`: every partial-correctness WP is forced true
at `s` (`wpGfp_of_alwaysDiverges`, `wpFuel_of_alwaysDiverges`). -/
theorem not_partial_wp_expressible_of_alwaysDiverges_of_not (S : System σ)
    (R : σ → Prop) (s : σ) (hdiv : AlwaysDiverges S s) (hviol : ¬ R s) :
    (¬ ∃ Q : σ → Prop, ∀ t, wpGfp S Q t ↔ R t) ∧
      (¬ ∃ (n : Nat) (Q : σ → Prop), ∀ t, wpFuel S n Q t ↔ R t) ∧
      (¬ ∃ Q : σ → Prop, ∀ t, (∀ n, wpFuel S n Q t) ↔ R t) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨Q, hQ⟩
    exact hviol ((hQ s).mp (wpGfp_of_alwaysDiverges hdiv Q))
  · rintro ⟨n, Q, hQ⟩
    exact hviol ((hQ s).mp (wpFuel_of_alwaysDiverges hdiv n Q))
  · rintro ⟨Q, hQ⟩
    exact hviol ((hQ s).mp (fun n => wpFuel_of_alwaysDiverges hdiv n Q))

/-- **Specialization to the liveness property `AllRunsEventually S P`.** If
some state `s` of `S` always diverges but violates `AllRunsEventually S P`,
then no postcondition `Q` makes `wpGfp S Q` coincide with
`AllRunsEventually S P`, and the same holds for `wpFuel S n Q` at every fixed
fuel `n` and for `∀ n, wpFuel S n Q`. This is
`not_partial_wp_expressible_of_alwaysDiverges_of_not` at
`R := AllRunsEventually S P`; nothing specific to liveness is used. -/
theorem allRunsEventually_not_partial_wp_of_divergent_violation (S : System σ)
    (P : σ → Prop) (s : σ) (hdiv : AlwaysDiverges S s) (hviol : ¬ AllRunsEventually S P s) :
    (¬ ∃ Q : σ → Prop, ∀ t, wpGfp S Q t ↔ AllRunsEventually S P t) ∧
      (¬ ∃ (n : Nat) (Q : σ → Prop), ∀ t, wpFuel S n Q t ↔ AllRunsEventually S P t) ∧
      (¬ ∃ Q : σ → Prop, ∀ t, (∀ n, wpFuel S n Q t) ↔ AllRunsEventually S P t) :=
  not_partial_wp_expressible_of_alwaysDiverges_of_not S (AllRunsEventually S P) s hdiv hviol

end General

/-! ### The two-state example -/

/-- In `spinOrOutSys`, the state `spin` never produces the output. -/
theorem spinOrOutSys_spin_not_allRunsEventually_isOut :
    ¬ AllRunsEventually spinOrOutSys isOut .spin := by
  have key : ∀ s, AllRunsEventually spinOrOutSys isOut s → s ≠ .spin := by
    intro s h
    induction h with
    | now hp => intro hs; subst hs; exact LO.spin_ne_out hp
    | later _ _ hall ih => intro hs; subst hs; exact ih .spin ⟨rfl, rfl⟩ rfl
  exact fun h => key .spin h rfl

theorem spinOrOutSys_out_allRunsEventually_isOut :
    AllRunsEventually spinOrOutSys isOut .out :=
  AllRunsEventually.now rfl

/-- **"Eventually outputs" is not a positive partial-correctness WP
(two-state system).** In `spinOrOutSys` (`spin → spin`, `out` terminal), the
liveness property `AllRunsEventually spinOrOutSys isOut` ("every run
eventually reaches `out`") is not equal, as a predicate on the two states, to
`wpGfp spinOrOutSys Q` for any postcondition `Q`, nor to
`wpFuel spinOrOutSys n Q` for any fuel `n` and `Q`, nor to
`fun s => ∀ n, wpFuel spinOrOutSys n Q s` for any `Q`.

In this system no edge enters `out` and `out` is terminal, so the property
holds exactly at `out` and coincides with `spinOrOutSys.terminal`; the
three-state `startSpinOutSys` example below exercises a run that reaches the
output only after a step. -/
theorem allRunsEventually_isOut_not_partial_wp_expressible :
    (¬ ∃ Q : LO → Prop, ∀ s, wpGfp spinOrOutSys Q s ↔ AllRunsEventually spinOrOutSys isOut s) ∧
      (¬ ∃ (n : Nat) (Q : LO → Prop),
        ∀ s, wpFuel spinOrOutSys n Q s ↔ AllRunsEventually spinOrOutSys isOut s) ∧
      (¬ ∃ Q : LO → Prop,
        ∀ s, (∀ n, wpFuel spinOrOutSys n Q s) ↔ AllRunsEventually spinOrOutSys isOut s) :=
  allRunsEventually_not_partial_wp_of_divergent_violation spinOrOutSys isOut .spin
    spinOrOutSys_alwaysDiverges spinOrOutSys_spin_not_allRunsEventually_isOut

/-- **Positive control (total correctness, this system only).** On the same
two-state system, `AllRunsEventually spinOrOutSys isOut` coincides with the
least-fixpoint total-correctness WP `wpLfp spinOrOutSys isOut`. This relies on
the output state `out` being terminal; on a system in which the output is
produced at a non-terminal state that keeps running (`spinOrEmitLoopSys`) no
total-correctness WP expresses the property either
(`spinOrEmitLoopSys_allRunsEventually_not_wp_expressible`). -/
theorem allRunsEventually_isOut_iff_wpLfp_isOut (s : LO) :
    wpLfp spinOrOutSys isOut s ↔ AllRunsEventually spinOrOutSys isOut s := by
  cases s with
  | spin =>
    exact ⟨fun h => absurd h (not_wpLfp_of_alwaysDiverges spinOrOutSys_alwaysDiverges _),
      fun h => absurd h spinOrOutSys_spin_not_allRunsEventually_isOut⟩
  | out =>
    refine ⟨fun _ => spinOrOutSys_out_allRunsEventually_isOut, fun _ => ?_⟩
    apply wpLfp_preFixed
    exact ⟨fun _ => rfl, fun h => absurd rfl h⟩

/-- The concrete divergent state `spin` satisfies every partial-correctness WP
and violates the liveness property. -/
theorem spinOrOutSys_spin_every_partial_wp_but_never_outputs :
    (∀ n Q, wpFuel spinOrOutSys n Q .spin) ∧ (∀ Q, wpGfp spinOrOutSys Q .spin) ∧
      ¬ AllRunsEventually spinOrOutSys isOut .spin :=
  ⟨wpFuel_of_alwaysDiverges spinOrOutSys_alwaysDiverges,
    wpGfp_of_alwaysDiverges spinOrOutSys_alwaysDiverges,
    spinOrOutSys_spin_not_allRunsEventually_isOut⟩

/-- The one-state loop satisfies every partial-correctness WP and no
total-correctness WP. -/
theorem loopSys_every_partial_wp_no_total_wp :
    (∀ n Q, wpFuel loopSys n Q ()) ∧ (∀ Q, wpGfp loopSys Q ()) ∧
      (∀ n Q, ¬ wpFuelTotal loopSys n Q ()) ∧ (∀ Q, ¬ wpLfp loopSys Q ()) :=
  alwaysDiverges_satisfies_every_partial_wp_and_no_total_wp loopSys () loopSys_alwaysDiverges

/-! ### The three-state example (output reached after a step) -/

theorem LO3.spin_ne_out : LO3.spin ≠ LO3.out := by
  intro h
  cases h

theorem LO3.start_ne_out : LO3.start ≠ LO3.out := by
  intro h
  cases h

/-- Every state reachable from `spin` in `startSpinOutSys` is `spin`. -/
theorem startSpinOutSys_reach_spin {s t : LO3} {k : Nat} (h : Reach startSpinOutSys s k t)
    (hs : s = .spin) : t = .spin := by
  induction h with
  | refl _ => exact hs
  | step _ hst _ ih =>
    subst hs
    rcases hst with ⟨h1, _⟩ | ⟨_, h2⟩
    · cases h1
    · exact ih h2

theorem startSpinOutSys_spin_alwaysDiverges : AlwaysDiverges startSpinOutSys .spin := by
  intro k t hr
  have ht : t = .spin := startSpinOutSys_reach_spin hr rfl
  subst ht
  exact ⟨LO3.spin_ne_out, ⟨.spin, Or.inr ⟨rfl, rfl⟩⟩⟩

theorem startSpinOutSys_spin_not_allRunsEventually :
    ¬ AllRunsEventually startSpinOutSys isOut3 .spin := by
  have key : ∀ s, AllRunsEventually startSpinOutSys isOut3 s → s ≠ .spin := by
    intro s h
    induction h with
    | now hp => intro hs; subst hs; exact LO3.spin_ne_out hp
    | later _ _ _ ih => intro hs; subst hs; exact ih .spin (Or.inr ⟨rfl, rfl⟩) rfl
  exact fun h => key .spin h rfl

/-- At `start` the output is produced after one step: `start` is not an output
state, and `AllRunsEventually` holds there through its `later` constructor. -/
theorem startSpinOutSys_start_allRunsEventually_later :
    ¬ isOut3 .start ∧ AllRunsEventually startSpinOutSys isOut3 .start := by
  refine ⟨LO3.start_ne_out,
    AllRunsEventually.later LO3.start_ne_out ⟨.out, Or.inl ⟨rfl, rfl⟩⟩ ?_⟩
  intro t ht
  rcases ht with ⟨_, h2⟩ | ⟨h1, _⟩
  · subst h2
    exact AllRunsEventually.now rfl
  · cases h1

/-- **"Eventually outputs" is not a positive partial-correctness WP
(three-state system).** In `startSpinOutSys` (`start → out`, `spin → spin`,
`out` terminal), `AllRunsEventually startSpinOutSys isOut3` holds at `start`
(after one step) and at `out`, fails at `spin`, and is not equal to
`wpGfp startSpinOutSys Q`, `wpFuel startSpinOutSys n Q` or
`∀ n, wpFuel startSpinOutSys n Q` for any `n` and `Q`. -/
theorem startSpinOutSys_allRunsEventually_not_partial_wp_expressible :
    (¬ ∃ Q : LO3 → Prop,
        ∀ s, wpGfp startSpinOutSys Q s ↔ AllRunsEventually startSpinOutSys isOut3 s) ∧
      (¬ ∃ (n : Nat) (Q : LO3 → Prop),
        ∀ s, wpFuel startSpinOutSys n Q s ↔ AllRunsEventually startSpinOutSys isOut3 s) ∧
      (¬ ∃ Q : LO3 → Prop,
        ∀ s, (∀ n, wpFuel startSpinOutSys n Q s) ↔ AllRunsEventually startSpinOutSys isOut3 s) :=
  allRunsEventually_not_partial_wp_of_divergent_violation startSpinOutSys isOut3 .spin
    startSpinOutSys_spin_alwaysDiverges startSpinOutSys_spin_not_allRunsEventually

end Toy.FuelWP
