/-!
# Transition systems, forward simulation, safety and termination

A transition system has a state type, a step relation and an initial-state predicate;
it has no action labels. A forward simulation `S ⊆ C × A` from a concrete system `C` to
an abstract system `A` relates initial states and matches every concrete step from a
related pair by zero or more abstract steps. The matching laws are separate `Prop`s:
`SimStepStar` (zero or more), `SimStepLock` (a single abstract step), `SimStepStutter`
(zero or one) and `SimStepWF` (one, or zero with a decrease of a measure in a
well-founded relation). Every matching law quantifies over all `S`-related pairs,
reachable or not.
-/

namespace Toy.Transfer

/-- A transition system. -/
structure TS where
  St : Type
  step : St → St → Prop
  init : St → Prop

/-- Reachable states: initial states, closed under steps. -/
inductive Reach (T : TS) : T.St → Prop where
  | init {s : T.St} : T.init s → Reach T s
  | step {s t : T.St} : Reach T s → T.step s t → Reach T t

/-- Reflexive–transitive closure of a relation. -/
inductive Star {α : Type} (r : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star r a a
  | tail {a b c : α} : Star r a b → r b c → Star r a c

theorem Reach.star {T : TS} {a b : T.St} (ha : Reach T a) (hab : Star T.step a b) :
    Reach T b := by
  induction hab with
  | refl => exact ha
  | tail _ hbc ih => exact .step ih hbc

/-- Initial states are related: every initial concrete state is `S`-related to some
initial abstract state. -/
def SimInit (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c, C.init c → ∃ a, A.init a ∧ S c a

/-- Star matching: every concrete step from an `S`-related pair is matched by zero or
more abstract steps ending in an `S`-related pair. -/
def SimStepStar (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → ∃ a', Star A.step a a' ∧ S c' a'

/-- Lock-step matching: every concrete step from an `S`-related pair is matched by a single
abstract step (a path of length one; the matching abstract successor need not be
unique). -/
def SimStepLock (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → ∃ a', A.step a a' ∧ S c' a'

/-- Stuttering matching: one abstract step, or none (the abstract state stays put). -/
def SimStepStutter (C A : TS) (S : C.St → A.St → Prop) : Prop :=
  ∀ c c' a, C.step c c' → S c a → (∃ a', A.step a a' ∧ S c' a') ∨ S c' a

/-- Well-founded stuttering matching: one abstract step, or none with a strict decrease
of the measure `μ` in the relation `lt`. -/
def SimStepWF (C A : TS) (S : C.St → A.St → Prop) {W : Type} (lt : W → W → Prop)
    (μ : C.St → A.St → W) : Prop :=
  ∀ c c' a, C.step c c' → S c a → (∃ a', A.step a a' ∧ S c' a') ∨ (S c' a ∧ lt (μ c' a) (μ c a))

theorem SimStepLock.toStar {C A : TS} {S : C.St → A.St → Prop} (hs : SimStepLock C A S) :
    SimStepStar C A S := fun c c' a hst hS =>
  let ⟨a', ha', hS'⟩ := hs c c' a hst hS
  ⟨a', .tail (.refl a) ha', hS'⟩

theorem SimStepStutter.toStar {C A : TS} {S : C.St → A.St → Prop} (hs : SimStepStutter C A S) :
    SimStepStar C A S := fun c c' a hst hS =>
  match hs c c' a hst hS with
  | .inl ⟨a', ha', hS'⟩ => ⟨a', .tail (.refl a) ha', hS'⟩
  | .inr hS' => ⟨a, .refl a, hS'⟩

theorem SimStepWF.toStutter {C A : TS} {S : C.St → A.St → Prop} {W : Type}
    {lt : W → W → Prop} {μ : C.St → A.St → W} (hs : SimStepWF C A S lt μ) :
    SimStepStutter C A S := fun c c' a hst hS =>
  match hs c c' a hst hS with
  | .inl h => .inl h
  | .inr ⟨hS', _⟩ => .inr hS'

/-- `s` is accessible (`Acc`) for the converse of the step relation. Equivalently
(`terminates_iff_no_infinite_run`), no infinite run starts at `s`. -/
def Terminates (T : TS) (s : T.St) : Prop := Acc (fun y x => T.step x y) s

/-- Every reachable state terminates (universal termination: every run from a reachable
state is finite). -/
def AllRunsFinite (T : TS) : Prop := ∀ s, Reach T s → Terminates T s

/-- Adequacy of `Terminates`: a terminating state starts no infinite run. -/
theorem Terminates.no_infinite_run {T : TS} {s : T.St} (hs : Terminates T s) :
    ¬ ∃ f : Nat → T.St, f 0 = s ∧ ∀ i, T.step (f i) (f (i + 1)) := by
  have key : ∀ x, Acc (fun y x => T.step x y) x →
      ∀ f : Nat → T.St, f 0 = x → (∀ i, T.step (f i) (f (i + 1))) → False := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro f hf0 hst
      exact ih (f 1) (hf0 ▸ hst 0) (fun i => f (i + 1)) rfl (fun i => hst (i + 1))
  rintro ⟨f, hf0, hst⟩
  exact key s hs f hf0 hst

/-- The converse of `Terminates.no_infinite_run` (classical, using choice): if no infinite
run starts at `s`, then `s` terminates. Together, `Terminates T s` holds exactly when no
infinite run starts at `s`. -/
theorem terminates_iff_no_infinite_run (T : TS) (s : T.St) :
    Terminates T s ↔ ¬ ∃ f : Nat → T.St, f 0 = s ∧ ∀ i, T.step (f i) (f (i + 1)) := by
  constructor
  · exact Terminates.no_infinite_run
  · intro hno
    refine Classical.byContradiction (fun hna => hno ?_)
    have hstep : ∀ x : { x : T.St // ¬ Terminates T x },
        ∃ y : { y : T.St // ¬ Terminates T y }, T.step x.1 y.1 := by
      intro ⟨x, hx⟩
      refine Classical.byContradiction (fun h => hx (Acc.intro x (fun y hxy => ?_)))
      exact Classical.byContradiction (fun hny => h ⟨⟨y, hny⟩, hxy⟩)
    let next : { x : T.St // ¬ Terminates T x } → { x : T.St // ¬ Terminates T x } :=
      fun x => Classical.choose (hstep x)
    have hnext : ∀ x, T.step x.1 (next x).1 := fun x => Classical.choose_spec (hstep x)
    let seq : Nat → { x : T.St // ¬ Terminates T x } := fun i => Nat.rec ⟨s, hna⟩ (fun _ prev => next prev) i
    exact ⟨fun i => (seq i).1, rfl, fun i => hnext (seq i)⟩

/-- Weak termination: some finite run from `s` reaches a state with no successor. -/
def WeaklyTerminates (T : TS) (s : T.St) : Prop := ∃ t, Star T.step s t ∧ ∀ u, ¬ T.step t u

/-! ## Safety along forward simulation -/

/-- **Reachable states are related.** If `S` relates initial states (`SimInit`) and matches every concrete
step by zero or more abstract steps (`SimStepStar`), then every reachable concrete state
is `S`-related to some reachable abstract state. -/
theorem reach_related_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) :
    ∀ c, Reach C c → ∃ a, S c a ∧ Reach A a := by
  intro c hc
  induction hc with
  | init h =>
    obtain ⟨a, ha, hS⟩ := hi _ h
    exact ⟨a, hS, .init ha⟩
  | step _ hst ih =>
    obtain ⟨a, hS, ha⟩ := ih
    obtain ⟨a', hstar, hS'⟩ := hs _ _ _ hst hS
    exact ⟨a', hS', ha.star hstar⟩

/-- **Invariants transfer down as an existential pullback.** Under `SimInit` and `SimStepStar`, if an
invariant `I` holds on every reachable abstract state, then every reachable concrete
state `c` satisfies the existential pullback `∃ a, S c a ∧ I a`. -/
theorem invariant_transfers_down_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (I : A.St → Prop)
    (hI : ∀ a, Reach A a → I a) :
    ∀ c, Reach C c → ∃ a, S c a ∧ I a := by
  intro c hc
  obtain ⟨a, hS, ha⟩ := reach_related_of_forward_simulation hi hs c hc
  exact ⟨a, hS, hI a ha⟩

/-- **Bugs transfer up.** Under `SimInit` and `SimStepStar`, if every abstract state
`S`-related to a bad concrete state is bad (`hbad`), then every reachable bad concrete
state is `S`-related to a reachable bad abstract state. -/
theorem bug_transfers_up_of_forward_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (BadC : C.St → Prop) (BadA : A.St → Prop)
    (hbad : ∀ c a, S c a → BadC c → BadA a) :
    ∀ c, Reach C c → BadC c → ∃ a, S c a ∧ Reach A a ∧ BadA a := by
  intro c hc hb
  obtain ⟨a, hS, ha⟩ := reach_related_of_forward_simulation hi hs c hc
  exact ⟨a, hS, ha, hbad c a hS hb⟩

/-- **Abstract bugs transfer down along a converse simulation** (a sufficient
condition). If the converse relation is a forward simulation from `A` to `C` (every
abstract initial state and every abstract step from a related pair is matched
concretely) and every concrete state `S`-related to a bad abstract state is bad, then
every reachable bad abstract state is `S`-related to a reachable bad concrete state.
`S` itself is not assumed to be a forward simulation from `C` to `A`. -/
theorem bug_transfers_down_of_converse_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit A C (fun a c => S c a)) (hs : SimStepStar A C (fun a c => S c a))
    (BadC : C.St → Prop) (BadA : A.St → Prop) (hbad : ∀ c a, S c a → BadA a → BadC c) :
    ∀ a, Reach A a → BadA a → ∃ c, S c a ∧ Reach C c ∧ BadC c :=
  bug_transfers_up_of_forward_simulation hi hs BadA BadC (fun a c hS hb => hbad c a hS hb)

/-- **Escape hatch for the universal pullback: functional simulations.** If `S` is a
forward simulation that relates each concrete state to at most one abstract state (for
example, the graph of a refinement mapping), then every abstract state related to a
reachable concrete state satisfies every abstract invariant. -/
theorem strong_pullback_of_functional_simulation {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) (hfun : ∀ c a a', S c a → S c a' → a = a')
    (I : A.St → Prop) (hI : ∀ a, Reach A a → I a) :
    ∀ c, Reach C c → ∀ a, S c a → I a := by
  intro c hc a hS
  obtain ⟨a₀, hS₀, ha₀⟩ := reach_related_of_forward_simulation hi hs c hc
  rw [hfun c a a₀ hS hS₀]
  exact hI a₀ ha₀

/-- **Escape hatch for the universal pullback: restricting to reachable abstract states.**
If `S` is a forward simulation, so is `S c a ∧ Reach A a`, and for the restricted
relation the universal pullback of every abstract invariant holds. -/
theorem reach_restricted_simulation_gives_strong_pullback {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepStar C A S) :
    SimInit C A (fun c a => S c a ∧ Reach A a) ∧
    SimStepStar C A (fun c a => S c a ∧ Reach A a) ∧
    ∀ (I : A.St → Prop), (∀ a, Reach A a → I a) →
      ∀ c, Reach C c → ∀ a, (S c a ∧ Reach A a) → I a := by
  refine ⟨fun c hc => ?_, fun c c' a hst ⟨hS, ha⟩ => ?_, fun I hI _ _ a ⟨_, ha⟩ => hI a ha⟩
  · obtain ⟨a, ha, hS⟩ := hi c hc
    exact ⟨a, ha, hS, .init ha⟩
  · obtain ⟨a', hstar, hS'⟩ := hs c c' a hst hS
    exact ⟨a', hstar, hS', ha.star hstar⟩

/-! ## Termination -/

/-- Key lemma for `allRunsFinite_transfers_down_of_lockstep`: under lock-step matching, a concrete state related to a
terminating abstract state terminates. -/
theorem terminates_of_lockstep_related {C A : TS} {S : C.St → A.St → Prop}
    (hs : SimStepLock C A S) {a : A.St} (ha : Terminates A a) :
    ∀ {c : C.St}, S c a → Terminates C c := by
  induction ha with
  | intro a _ ih =>
    intro c hS
    refine Acc.intro c (fun c' hst => ?_)
    obtain ⟨a', ha', hS'⟩ := hs c c' a hst hS
    exact ih a' ha' hS'

/-- **Termination transfers down along lock-step simulation.** If `S` relates initial
states and matches every concrete step from a related pair by a single abstract step,
and every reachable state of `A` terminates (`Acc` for the converse step relation), then
every reachable state of `C` terminates. -/
theorem allRunsFinite_transfers_down_of_lockstep {C A : TS} {S : C.St → A.St → Prop}
    (hi : SimInit C A S) (hs : SimStepLock C A S) (hA : AllRunsFinite A) :
    AllRunsFinite C := by
  intro c hc
  obtain ⟨a, hS, ha⟩ := reach_related_of_forward_simulation hi hs.toStar c hc
  exact terminates_of_lockstep_related hs (hA a ha) hS

/-- Key lemma for `allRunsFinite_transfers_down_of_wf_simulation`: under well-founded stuttering matching, a concrete state
related to a terminating abstract state terminates. -/
theorem terminates_of_wf_related {C A : TS} {S : C.St → A.St → Prop} {W : Type}
    {lt : W → W → Prop} (hwf : WellFounded lt) {μ : C.St → A.St → W}
    (hs : SimStepWF C A S lt μ) {a : A.St} (ha : Terminates A a) :
    ∀ {c : C.St}, S c a → Terminates C c := by
  induction ha with
  | intro a _ ihA =>
    have key : ∀ w, Acc lt w → ∀ c, μ c a = w → S c a → Terminates C c := by
      intro w hw
      induction hw with
      | intro w _ ihW =>
        intro c hμ hS
        refine Acc.intro c (fun c' hst => ?_)
        rcases hs c c' a hst hS with ⟨a', ha', hS'⟩ | ⟨hS', hlt⟩
        · exact ihA a' ha' hS'
        · exact ihW (μ c' a) (hμ ▸ hlt) c' rfl hS'
    intro c hS
    exact key (μ c a) (hwf.apply _) c rfl hS

/-- **The well-founded simulation criterion.** If `S` relates initial states, every
concrete step from a related pair is matched by one abstract step or by none with a
strict decrease of a measure `μ` in a well-founded relation `lt`, and every reachable
state of `A` terminates (`Acc` for the converse step relation), then every reachable
state of `C` terminates. -/
theorem allRunsFinite_transfers_down_of_wf_simulation {C A : TS} {S : C.St → A.St → Prop}
    {W : Type} (lt : W → W → Prop) (hwf : WellFounded lt) (μ : C.St → A.St → W)
    (hi : SimInit C A S) (hs : SimStepWF C A S lt μ) (hA : AllRunsFinite A) :
    AllRunsFinite C := by
  intro c hc
  obtain ⟨a, hS, ha⟩ := reach_related_of_forward_simulation hi hs.toStutter.toStar c hc
  exact terminates_of_wf_related hwf hs (hA a ha) hS

end Toy.Transfer
