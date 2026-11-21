import ToyTransfer.Simulation

/-!
# Countermodels and non-vacuity instances for forward simulation, safety and termination

All systems have at most three states (`Unit`, `Bool` or `Fin 3`).
-/

namespace Toy.Transfer

/-! ## Concrete transition systems -/

/-- One state, initial, with a self-loop: the run `() → () → ⋯` is infinite. -/
def tsLoop : TS := ⟨Unit, fun _ _ => True, fun _ => True⟩
/-- One state, initial, with no steps. -/
def tsHalt : TS := ⟨Unit, fun _ _ => False, fun _ => True⟩
/-- Two states; `false` is initial; the single step is `false → true`. -/
def tsTwoStep : TS := ⟨Bool, fun a b => a = false ∧ b = true, fun a => a = false⟩
/-- Two states; `false` is initial; no steps (so `true` is unreachable). -/
def tsBoolHalt : TS := ⟨Bool, fun _ _ => False, fun a => a = false⟩

theorem tsLoop_not_terminates : ¬ Terminates tsLoop () := by
  intro h
  exact h.no_infinite_run ⟨fun _ => (), rfl, fun _ => trivial⟩

theorem tsLoop_reach : Reach tsLoop () := .init trivial

theorem tsHalt_allRunsFinite : AllRunsFinite tsHalt :=
  fun _ _ => Acc.intro _ (fun _ h => h.elim)

theorem tsBoolHalt_allRunsFinite : AllRunsFinite tsBoolHalt :=
  fun _ _ => Acc.intro _ (fun _ h => h.elim)

theorem tsBoolHalt_reach_iff (a : tsBoolHalt.St) : Reach tsBoolHalt a ↔ a = false := by
  constructor
  · intro h
    induction h with
    | init h => exact h
    | step _ hst _ => exact hst.elim
  · intro h
    exact .init h

theorem tsTwoStep_reach_true : Reach tsTwoStep true :=
  Reach.step (Reach.init (T := tsTwoStep) (s := false) rfl)
    (show false = false ∧ true = true from ⟨rfl, rfl⟩)

theorem tsTwoStep_allRunsFinite : AllRunsFinite tsTwoStep := by
  have htrue : Terminates tsTwoStep true :=
    Acc.intro _ (fun _ h => Bool.noConfusion h.1)
  intro s _
  cases s with
  | true => exact htrue
  | false =>
    refine Acc.intro _ (fun y h => ?_)
    have hy : y = true := h.2
    subst hy
    exact htrue


/-! ## Safety along forward simulation -/

/-- **Countermodel for the universal pullback.** `C = tsHalt` (one state), `A = tsBoolHalt`
(abstract `true` unreachable), `S` relates the concrete state to both abstract states,
`I a := a = false`. `S` is a forward simulation and `I` holds on every reachable
abstract state, yet the reachable concrete state is `S`-related to an abstract state
violating `I`: the pullback `{c | ∀ a, S c a → I a}` fails. The existential pullback
`∃ a, S c a ∧ I a` holds in the same instance. -/
theorem strong_pullback_fails_with_unreachable_related_state :
    SimInit tsHalt tsBoolHalt (fun _ _ => True) ∧
    SimStepStar tsHalt tsBoolHalt (fun _ _ => True) ∧
    (∀ a, Reach tsBoolHalt a → a = false) ∧
    Reach tsHalt () ∧
    ¬ (∀ a, (fun (_ : Unit) (_ : Bool) => True) () a → a = false) ∧
    (∃ a, (fun (_ : Unit) (_ : Bool) => True) () a ∧ a = false) := by
  refine ⟨fun _ _ => ⟨false, rfl, trivial⟩, fun _ _ _ h => h.elim,
    fun a h => (tsBoolHalt_reach_iff a).1 h, .init trivial, fun h => ?_, ⟨false, trivial, rfl⟩⟩
  exact Bool.noConfusion (h true trivial)

/-- **Tightness of `SimInit`** for `reach_related_of_forward_simulation`,
`invariant_transfers_down_of_forward_simulation` (with `I := True`) and
`bug_transfers_up_of_forward_simulation` (with `BadC := True`, `BadA := True`): the empty
relation fails `SimInit`, satisfies `SimStepStar` vacuously, the invariant and bad-state
hypotheses hold trivially, and each conclusion fails at the reachable concrete state. -/
theorem forward_simulation_needs_init :
    ¬ SimInit tsHalt tsHalt (fun _ _ => False) ∧
    SimStepStar tsHalt tsHalt (fun _ _ => False) ∧
    (∀ a, Reach tsHalt a → True) ∧
    (∀ (c a : Unit), (fun (_ _ : Unit) => False) c a → True → True) ∧
    Reach tsHalt () ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ Reach tsHalt a) ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ True) ∧
    ¬ (∃ a, (fun (_ _ : Unit) => False) () a ∧ Reach tsHalt a ∧ True) := by
  refine ⟨fun h => (h () trivial).elim fun _ h => h.2, fun _ _ _ _ h => h.elim,
    fun _ _ => trivial, fun _ _ _ _ => trivial, .init trivial, ?_, ?_, ?_⟩ <;>
    exact fun ⟨_, h, _⟩ => h

/-- **Tightness of `SimStepStar`** for the same three theorems: `C = tsTwoStep`,
`A = tsHalt`, `S c _ := c = false` relates initial states but does not match the concrete
step `false → true`; the reachable concrete state `true` is related to nothing. -/
theorem forward_simulation_needs_step_matching :
    SimInit tsTwoStep tsHalt (fun c _ => c = false) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun c _ => c = false) ∧
    (∀ a, Reach tsHalt a → True) ∧
    (∀ (c : Bool) (a : Unit), (fun (c : Bool) (_ : Unit) => c = false) c a → True → True) ∧
    Reach tsTwoStep true ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ Reach tsHalt a) ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ True) ∧
    ¬ (∃ a, (fun (c : Bool) (_ : Unit) => c = false) true a ∧ Reach tsHalt a ∧ True) := by
  refine ⟨fun c hc => ⟨(), trivial, hc⟩, fun h => ?_, fun _ _ => trivial,
    fun _ _ _ _ => trivial, tsTwoStep_reach_true, ?_, ?_, ?_⟩
  · obtain ⟨_, _, hS⟩ := h false true () ⟨rfl, rfl⟩ rfl
    exact Bool.noConfusion hS
  all_goals exact fun ⟨_, h, _⟩ => Bool.noConfusion h

/-- **Tightness of the abstract invariant hypothesis** of
`invariant_transfers_down_of_forward_simulation`: with `I := False` (which fails on the
reachable abstract state), the total relation between one-state systems is a forward
simulation and the conclusion fails. -/
theorem invariant_transfer_needs_abstract_invariant :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ a, Reach tsHalt a → False) ∧
    Reach tsHalt () ∧ ¬ (∃ a, (fun (_ _ : Unit) => True) () a ∧ False) :=
  ⟨fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ _ h => h.elim, fun h => h () (.init trivial),
    .init trivial, fun ⟨_, _, h⟩ => h⟩

/-- **Tightness of `hbad`** of `bug_transfers_up_of_forward_simulation`: the total relation
between one-state systems is a forward simulation, the concrete state is bad
(`BadC := True`), no abstract state is bad (`BadA := False`), so `hbad` fails and so does
the conclusion. -/
theorem bug_transfer_needs_bad_compatibility :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ (c a : Unit), (fun (_ _ : Unit) => True) c a → True → False) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ a, (fun (_ _ : Unit) => True) () a ∧ Reach tsHalt a ∧ False) :=
  ⟨fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ _ h => h.elim, fun h => h () () trivial trivial,
    .init trivial, trivial, fun ⟨_, _, _, h⟩ => h⟩

/-- **Non-vacuity of `reach_related_of_forward_simulation` and
`invariant_transfers_down_of_forward_simulation`, with genuine stuttering.**
`C = tsTwoStep`, `A = tsBoolHalt`, `S _ a := a = false`: the concrete step `false → true`
is matched by zero abstract steps; the invariant `a = false` holds on every reachable
abstract state; the concrete state `true` is reachable. -/
theorem forward_simulation_nonvacuous :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepStar tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    (∀ a, Reach tsBoolHalt a → a = false) ∧
    Reach tsTwoStep true :=
  ⟨fun _ _ => ⟨false, rfl, rfl⟩, fun _ _ a _ ha => ⟨a, .refl a, ha⟩,
    fun a h => (tsBoolHalt_reach_iff a).1 h, tsTwoStep_reach_true⟩

/-- **Non-vacuity of `bug_transfers_up_of_forward_simulation`.** The identity relation on
`tsTwoStep`, with `BadC = BadA := (· = true)`: `hbad` holds, the bad concrete state `true`
is reachable, and the initial state `false` is not bad. -/
theorem bug_transfer_up_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧
    SimStepStar tsTwoStep tsTwoStep (fun c a => c = a) ∧
    (∀ (c a : Bool), c = a → c = true → a = true) ∧
    Reach tsTwoStep true ∧ tsTwoStep.init false ∧ ¬ (false = true) := by
  refine ⟨fun c hc => ⟨c, hc, rfl⟩, fun c c' a hst hS => ⟨c', ?_, rfl⟩,
    fun _ _ h hc => h ▸ hc, tsTwoStep_reach_true, rfl, Bool.noConfusion⟩
  subst hS
  exact .tail (.refl _) hst

/-! ## Abstract counterexamples and the converse simulation -/

/-- The relation `S () a := a = false` from `tsHalt` to `tsTwoStep`. -/
def relHaltTwoStep : tsHalt.St → tsTwoStep.St → Prop := fun _ a => a = false
/-- No concrete state of `tsHalt` is bad. -/
def badNone : tsHalt.St → Prop := fun _ => False
/-- The abstract state `true` of `tsTwoStep` is bad. -/
def badTrue : tsTwoStep.St → Prop := fun a => a = true

/-- **Spurious abstract counterexample.** `relHaltTwoStep` is a forward simulation from
`tsHalt` to `tsTwoStep`, related states agree on badness (`badNone`, `badTrue`), and the
converse relation relates initial states but does not match the abstract step
`false → true`. The abstract system reaches its bad state `true`; no reachable concrete
state is bad, and no concrete state is related to `true`. -/
theorem spurious_abstract_counterexample :
    SimInit tsHalt tsTwoStep relHaltTwoStep ∧ SimStepStar tsHalt tsTwoStep relHaltTwoStep ∧
    (∀ c a, relHaltTwoStep c a → (badNone c ↔ badTrue a)) ∧
    SimInit tsTwoStep tsHalt (fun a c => relHaltTwoStep c a) ∧
    ¬ SimStepStar tsTwoStep tsHalt (fun a c => relHaltTwoStep c a) ∧
    Reach tsTwoStep true ∧ badTrue true ∧
    (∀ c, Reach tsHalt c → ¬ badNone c) ∧
    (∀ c, ¬ relHaltTwoStep c true) ∧
    ¬ (∃ c, relHaltTwoStep c true ∧ Reach tsHalt c ∧ badNone c) := by
  refine ⟨fun _ _ => ⟨false, rfl, rfl⟩, fun _ _ _ h => h.elim, fun _ a ha => ?_,
    fun _ ha => ⟨(), trivial, ha⟩, fun h => ?_, tsTwoStep_reach_true, rfl,
    fun _ _ h => h, fun _ h => Bool.noConfusion h, fun ⟨_, _, _, h⟩ => h⟩
  · exact ⟨fun h => h.elim, fun h => Bool.noConfusion (ha.symm.trans h)⟩
  · obtain ⟨_, _, hS⟩ := h false true () ⟨rfl, rfl⟩ rfl
    exact Bool.noConfusion hS

/-- **Tightness of the converse `SimInit`** of `bug_transfers_down_of_converse_simulation`:
the empty relation fails converse `SimInit`, vacuously matches abstract steps and
satisfies the bad-state hypothesis; the reachable abstract state is bad (`BadA := True`)
and no concrete state is related to it. -/
theorem converse_simulation_needs_init :
    ¬ SimInit tsHalt tsHalt (fun (_ _ : Unit) => False) ∧
    SimStepStar tsHalt tsHalt (fun (_ _ : Unit) => False) ∧
    (∀ (c a : Unit), (fun (_ _ : Unit) => False) c a → True → True) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ c, (fun (_ _ : Unit) => False) c () ∧ Reach tsHalt c ∧ True) :=
  ⟨fun h => (h () trivial).elim fun _ h => h.2, fun _ _ _ _ h => h.elim, fun _ _ _ _ => trivial,
    .init trivial, trivial, fun ⟨_, h, _⟩ => h⟩

/-- **Tightness of the bad-state hypothesis** of
`bug_transfers_down_of_converse_simulation`: the total relation between one-state systems
is a forward simulation in both directions; the abstract state is bad (`BadA := True`),
the concrete one is not (`BadC := False`). -/
theorem converse_simulation_needs_bad_compatibility :
    SimInit tsHalt tsHalt (fun _ _ => True) ∧ SimStepStar tsHalt tsHalt (fun _ _ => True) ∧
    ¬ (∀ (c a : Unit), (fun (_ _ : Unit) => True) c a → True → False) ∧
    Reach tsHalt () ∧ True ∧
    ¬ (∃ c, (fun (_ _ : Unit) => True) c () ∧ Reach tsHalt c ∧ False) :=
  ⟨fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ _ h => h.elim, fun h => h () () trivial trivial,
    .init trivial, trivial, fun ⟨_, _, _, h⟩ => h⟩

/-- **Non-vacuity of `bug_transfers_down_of_converse_simulation`.** The identity relation
on `tsTwoStep`, read in both directions, with `BadC = BadA := (· = true)`; the abstract
bad state is reachable. -/
theorem converse_simulation_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun a c => c = a) ∧
    SimStepStar tsTwoStep tsTwoStep (fun a c => c = a) ∧
    (∀ (c a : Bool), c = a → a = true → c = true) ∧ Reach tsTwoStep true := by
  refine ⟨fun a ha => ⟨a, ha, rfl⟩, fun a a' c hst hS => ⟨a', ?_, rfl⟩,
    fun c a h ha => h ▸ ha, tsTwoStep_reach_true⟩
  subst hS
  exact .tail (.refl _) hst

/-- Abstract system on `Fin 3`: from the initial state `0`, steps to `1` and to `2`. -/
def tsBranch3 : TS := ⟨Fin 3, fun a b => a = 0 ∧ (b = 1 ∨ b = 2), fun a => a = 0⟩
/-- Concrete system on `Fin 2`: from the initial state `0`, a single step to `1`. -/
def tsLine2 : TS := ⟨Fin 2, fun c c' => c = 0 ∧ c' = 1, fun c => c = 0⟩
/-- Relates states with the same index. -/
def relSameIndex : tsLine2.St → tsBranch3.St → Prop := fun c a => c.val = a.val

/-- **Abstract bugs can transfer down without a converse simulation.** `relSameIndex` is
a forward simulation from `tsLine2` to `tsBranch3`, the converse relation relates initial
states, related states agree on badness (bad state `1` on both sides), and every
reachable bad abstract state is related to a reachable bad concrete state; yet the
converse relation does not match the abstract step `0 → 2`. -/
theorem abstract_bug_transfer_without_converse_step_matching :
    SimInit tsLine2 tsBranch3 relSameIndex ∧ SimStepStar tsLine2 tsBranch3 relSameIndex ∧
    SimInit tsBranch3 tsLine2 (fun a c => relSameIndex c a) ∧
    (∀ (c : Fin 2) (a : Fin 3), relSameIndex c a → (a = 1 ↔ c = 1)) ∧
    (∀ a : Fin 3, Reach tsBranch3 a → a = 1 →
      ∃ c : Fin 2, relSameIndex c a ∧ Reach tsLine2 c ∧ c = 1) ∧
    ¬ SimStepStar tsBranch3 tsLine2 (fun a c => relSameIndex c a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; subst hc; exact ⟨(0 : Fin 3), rfl, rfl⟩
  · intro c c' a ⟨hc, hc'⟩ hS
    subst hc hc'
    have ha : a = (0 : Fin 3) := Fin.ext hS.symm
    subst ha
    exact ⟨(1 : Fin 3), .tail (.refl (0 : Fin 3)) ⟨rfl, .inl rfl⟩, rfl⟩
  · intro a ha; subst ha; exact ⟨(0 : Fin 2), rfl, rfl⟩
  · intro c a hS
    constructor
    · intro ha; subst ha; exact Fin.ext hS
    · intro hc; subst hc; exact Fin.ext hS.symm
  · intro a _ ha
    subst ha
    exact ⟨(1 : Fin 2), rfl, Reach.step (Reach.init (T := tsLine2) (s := (0 : Fin 2)) rfl)
      ⟨rfl, rfl⟩, rfl⟩
  · intro hstar
    obtain ⟨c', _, hS'⟩ := hstar (0 : Fin 3) (2 : Fin 3) (0 : Fin 2) ⟨rfl, .inr rfl⟩ rfl
    have hlt : c'.val < 2 := c'.isLt
    have h2 : c'.val = 2 := hS'
    rw [h2] at hlt
    exact Nat.lt_irrefl 2 hlt

/-! ## Termination -/

/-- **Termination does not transfer down along stuttering simulation.** `C = tsLoop` (a
self-loop), `A = tsHalt` (no steps), `S` total. `S` relates initial states and matches the
concrete step by zero abstract steps (stuttering, hence also star matching, so safety
still transfers), but it is not a lock-step simulation; every reachable abstract state
terminates; the reachable concrete state does not, and the concrete system has an
infinite run from a reachable state. -/
theorem stuttering_simulation_does_not_transfer_termination :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧ SimStepStutter tsLoop tsHalt (fun _ _ => True) ∧
    SimStepStar tsLoop tsHalt (fun _ _ => True) ∧ ¬ SimStepLock tsLoop tsHalt (fun _ _ => True) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop ∧
    (∃ f : Nat → tsLoop.St, Reach tsLoop (f 0) ∧ ∀ i, tsLoop.step (f i) (f (i + 1))) := by
  have hst : SimStepStutter tsLoop tsHalt (fun _ _ => True) := fun _ _ _ _ _ => .inr trivial
  exact ⟨fun _ _ => ⟨(), trivial, trivial⟩, hst, hst.toStar,
    fun h => (h () () () trivial trivial).elim fun _ h => h.1, tsHalt_allRunsFinite,
    fun h => tsLoop_not_terminates (h () tsLoop_reach),
    ⟨fun _ => (), tsLoop_reach, fun _ => trivial⟩⟩

/-- Two states; `false` is initial and has no steps; the unreachable state `true` has a
self-loop. -/
def tsUnreachLoop : TS := ⟨Bool, fun a b => a = true ∧ b = true, fun a => a = false⟩

/-- **The termination transfer is about reachable states.** `C = tsUnreachLoop`,
`A = tsHalt`, `S c _ := c = false` is a lock-step simulation and every reachable abstract
state terminates; every reachable concrete state terminates (as
`allRunsFinite_transfers_down_of_lockstep` says), but the unreachable concrete state
`true` does not. -/
theorem lockstep_termination_transfer_is_about_reachable_states :
    SimInit tsUnreachLoop tsHalt (fun c _ => c = false) ∧
    SimStepLock tsUnreachLoop tsHalt (fun c _ => c = false) ∧
    AllRunsFinite tsHalt ∧ AllRunsFinite tsUnreachLoop ∧ ¬ Terminates tsUnreachLoop true := by
  have hreach : ∀ c, Reach tsUnreachLoop c → c = false := by
    intro c hc
    induction hc with
    | init h => exact h
    | step _ hst ih => exact Bool.noConfusion (hst.1.symm.trans ih)
  refine ⟨fun c hc => ⟨(), trivial, hc⟩,
    fun c _ _ hst hS => Bool.noConfusion (hst.1.symm.trans hS), tsHalt_allRunsFinite,
    fun c hc => ?_, fun h => h.no_infinite_run ⟨fun _ => true, rfl, fun _ => ⟨rfl, rfl⟩⟩⟩
  have hc' : c = false := hreach c hc
  subst hc'
  exact Acc.intro _ (fun _ h => Bool.noConfusion h.1)

/-- **Tightness of `SimInit`** for `allRunsFinite_transfers_down_of_lockstep` and
`allRunsFinite_transfers_down_of_wf_simulation`: the empty relation fails `SimInit` and is
vacuously a lock-step and a well-founded stuttering simulation (measure into `Unit` with
the empty, well-founded relation); `A` terminates; `C` does not. -/
theorem termination_transfer_needs_init :
    ¬ SimInit tsLoop tsHalt (fun _ _ => False) ∧
    SimStepLock tsLoop tsHalt (fun _ _ => False) ∧
    SimStepWF tsLoop tsHalt (fun _ _ => False) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop :=
  ⟨fun h => (h () trivial).elim fun _ h => h.2, fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim,
    ⟨fun _ => Acc.intro _ (fun _ h => h.elim)⟩, tsHalt_allRunsFinite,
    fun h => tsLoop_not_terminates (h () tsLoop_reach)⟩

/-- **Tightness of the abstract-termination hypothesis** for the same two theorems: the
total relation between two self-loops is a lock-step simulation and a well-founded
stuttering simulation for the empty (well-founded) relation on `Unit`; the abstract
system does not terminate, and neither does the concrete one (here `A = C = tsLoop`, so
the failed hypothesis and the failed conclusion are the same proposition
`¬ AllRunsFinite tsLoop`). -/
theorem termination_transfer_needs_abstract_termination :
    SimInit tsLoop tsLoop (fun _ _ => True) ∧ SimStepLock tsLoop tsLoop (fun _ _ => True) ∧
    SimStepWF tsLoop tsLoop (fun _ _ => True) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    ¬ AllRunsFinite tsLoop :=
  ⟨fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ _ _ _ => ⟨(), trivial, trivial⟩,
    fun _ _ _ _ _ => .inl ⟨(), trivial, trivial⟩, ⟨fun _ => Acc.intro _ (fun _ h => h.elim)⟩,
    fun h => tsLoop_not_terminates (h () tsLoop_reach)⟩

/-- **Tightness of well-foundedness** for `allRunsFinite_transfers_down_of_wf_simulation`:
the stuttering countermodel with the measure into `Unit` and the total relation
`fun _ _ => True`, which is not well-founded, satisfies `SimStepWF`; `A` terminates; `C`
does not. -/
theorem wf_simulation_needs_wellFounded :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧
    SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (_ _ : Unit) => True) (fun _ _ => ()) ∧
    ¬ WellFounded (fun (_ _ : Unit) => True) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop := by
  refine ⟨fun _ _ => ⟨(), trivial, trivial⟩, fun _ _ _ _ _ => .inr ⟨trivial, trivial⟩, ?_,
    tsHalt_allRunsFinite, fun h => tsLoop_not_terminates (h () tsLoop_reach)⟩
  intro hwf
  exact tsLoop_not_terminates (hwf.apply ())

/-- **Tightness of `SimStepWF`** for `allRunsFinite_transfers_down_of_wf_simulation`: in
the stuttering countermodel the relation `fun _ _ => False` on `Unit` is well-founded,
`SimInit` holds, every reachable abstract state terminates, but stuttering steps do not
decrease the measure (`SimStepWF` fails), and the concrete system does not terminate. -/
theorem wf_simulation_needs_measure_decrease :
    SimInit tsLoop tsHalt (fun _ _ => True) ∧
    WellFounded (fun (_ _ : Unit) => False) ∧
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) (fun (_ _ : Unit) => False) (fun _ _ => ()) ∧
    AllRunsFinite tsHalt ∧ ¬ AllRunsFinite tsLoop := by
  refine ⟨fun _ _ => ⟨(), trivial, trivial⟩, ⟨fun _ => Acc.intro _ (fun _ h => h.elim)⟩,
    fun h => ?_, tsHalt_allRunsFinite, fun h => tsLoop_not_terminates (h () tsLoop_reach)⟩
  rcases h () () () trivial trivial with ⟨_, h, _⟩ | ⟨_, h⟩
  · exact h
  · exact h

/-- **No well-founded measure exists for the stuttering countermodel.** For every type `W`,
every well-founded relation `lt` on `W` and every measure `μ`, the total relation between
`tsLoop` and `tsHalt` fails `SimStepWF` with `lt` and `μ`. This strengthens
`wf_simulation_needs_measure_decrease`, which shows the failure for one constant measure
into `Unit`. Proof: `SimInit` holds and every reachable abstract state terminates, so such a
measure would let `allRunsFinite_transfers_down_of_wf_simulation` conclude that every
reachable state of `tsLoop` terminates, contradicting
`stuttering_simulation_does_not_transfer_termination`. -/
theorem stuttering_countermodel_admits_no_wf_measure {W : Type} (lt : W → W → Prop)
    (hwf : WellFounded lt) (μ : tsLoop.St → tsHalt.St → W) :
    ¬ SimStepWF tsLoop tsHalt (fun _ _ => True) lt μ := by
  intro hstep
  have h := stuttering_simulation_does_not_transfer_termination
  exact h.2.2.2.2.2.1
    (allRunsFinite_transfers_down_of_wf_simulation lt hwf μ h.1 hstep h.2.2.2.2.1)

/-- **Non-vacuity of `allRunsFinite_transfers_down_of_lockstep`.** The identity relation on
`tsTwoStep` is a lock-step simulation and every reachable state of `tsTwoStep`
terminates. -/
theorem lockstep_nonvacuous :
    SimInit tsTwoStep tsTwoStep (fun c a => c = a) ∧
    SimStepLock tsTwoStep tsTwoStep (fun c a => c = a) ∧ AllRunsFinite tsTwoStep := by
  refine ⟨fun c hc => ⟨c, hc, rfl⟩, fun c c' a hst hS => ⟨c', ?_, rfl⟩, tsTwoStep_allRunsFinite⟩
  subst hS
  exact hst

/-- **Non-vacuity of `allRunsFinite_transfers_down_of_wf_simulation`, with genuine
stuttering.** `C = tsTwoStep`, `A = tsBoolHalt` (no steps), `S _ a := a = false`, measure
`μ c _ := if c then 0 else 1` into `Nat` with `<`: the concrete step `false → true` is
matched by zero abstract steps and the measure drops from 1 to 0. -/
theorem wf_simulation_nonvacuous :
    SimInit tsTwoStep tsBoolHalt (fun _ a => a = false) ∧
    SimStepWF tsTwoStep tsBoolHalt (fun _ a => a = false) (· < ·)
      (fun (c : Bool) (_ : Bool) => if c then 0 else 1) ∧
    WellFounded (fun (x y : Nat) => x < y) ∧ AllRunsFinite tsBoolHalt := by
  refine ⟨fun _ _ => ⟨false, rfl, rfl⟩, fun c c' a hst ha => .inr ⟨ha, ?_⟩,
    Nat.lt_wfRel.wf, tsBoolHalt_allRunsFinite⟩
  obtain ⟨hc, hc'⟩ := hst
  subst hc hc'
  exact Nat.zero_lt_one

/-- Two states; `false` is initial and steps to `false` and to `true`; `true` has no
steps. -/
def tsLoopOrHalt : TS := ⟨Bool, fun a _ => a = false, fun a => a = false⟩

/-- **Weak termination does not transfer down along lock-step simulation.** `C = tsLoop`,
`A = tsLoopOrHalt`, `S _ a := a = false` is a lock-step simulation (and a well-founded
stuttering simulation for the empty relation on `Unit`); every reachable abstract state
has a terminating run; the reachable concrete state has none. -/
theorem weak_termination_does_not_transfer_down_lockstep :
    SimInit tsLoop tsLoopOrHalt (fun _ a => a = false) ∧
    SimStepLock tsLoop tsLoopOrHalt (fun _ a => a = false) ∧
    SimStepWF tsLoop tsLoopOrHalt (fun _ a => a = false) (fun (_ _ : Unit) => False)
      (fun _ _ => ()) ∧
    (∀ a, Reach tsLoopOrHalt a → WeaklyTerminates tsLoopOrHalt a) ∧
    Reach tsLoop () ∧ ¬ WeaklyTerminates tsLoop () := by
  have hT : ∀ u, ¬ tsLoopOrHalt.step true u := fun _ h => Bool.noConfusion h
  refine ⟨fun _ _ => ⟨false, rfl, rfl⟩, fun _ _ a _ ha => ⟨false, ha, rfl⟩,
    fun _ _ a _ ha => .inl ⟨false, ha, rfl⟩, fun a _ => ?_, tsLoop_reach,
    fun ⟨_, _, h⟩ => h () trivial⟩
  cases a with
  | true => exact ⟨true, .refl true, hT⟩
  | false => exact ⟨true, .tail (.refl false) rfl, hT⟩

end Toy.Transfer
