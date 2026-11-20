# Simulation diagrams and multi-pass compiler correctness: a Lean 4 toy model of forward and backward simulations, the flip lemma, and end-to-end refinement

## Summary

This package is a kernel-checked Lean 4 development (core library only, no Mathlib) of the small-step simulation framework used by multi-pass verified compilers, in a toy model: labelled transition systems with silent steps and at most one event per step, and observable behaviours with *finite* traces (terminate, diverge silently, go wrong). It contains 13 theorem cards and 7 counterexample cards. All theorems are proved; every declaration of the library depends on at most the axioms `propext`, `Classical.choice`, `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Short answer to the design question** (In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?), in this toy model: each pass proves a *forward* simulation (an index in a well-founded order, an initial-state clause, a final-state clause, and a step diagram that allows stuttering only with a decreasing index). Forward simulations compose (`forward-simulations-compose`). By themselves they only give *source behaviours ⊆ target behaviours* for behaviours that do not go wrong, which is the wrong direction for compiler correctness. If moreover the **first** language of the pipeline is receptive and the **last** language is determinate (for the same event-matching relation `M`), the composed forward simulation can be flipped into a backward simulation, and a backward simulation gives refinement: every target behaviour is allowed by the source (`pipeline-end-to-end-refinement`). No receptiveness or determinacy is required of intermediate languages. Every ledgered hypothesis of every theorem card has a kernel-checked counterexample showing that it cannot simply be dropped. Two limits matter for design: a pass verified by a forward simulation cannot remove observable nondeterminism of a source or intermediate language that never goes wrong, because forward simulations preserve every behaviour that does not go wrong (`forward-sim-preserves-non-wrong-behaviours`); such a pass needs a backward simulation or another refinement proof, composed with the rest through `RefinedBy.trans` (`Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation`); and `RefinedBy` constrains only the modelled finite-trace behaviours, so target runs that emit infinitely many events are not constrained at all.

**One sentence per result** (the plain-language claim of each card, verbatim). Key hypotheses are named in each sentence; the full hypothesis ledgers are in **Findings**.

* **`partial-run-simulated`** (theorem, tier T0). If a relation R between the states of a source LTS L₁ and a target LTS L₂ satisfies the forward initial-state clause and the forward step diagram (for any index order, well-founded or not), then every finite run of L₁ from an initial state s₀, with trace t and ending in s, is matched by a run of L₂ with the same trace t that starts in an initial state related to s₀ and ends in a state related to s.
* **`terminating-behaviours-preserved`** (theorem, tier T0). With the forward initial-state clause, the forward step diagram (any index order) and the forward final-state clause, every terminating behaviour of the source (trace t, result r) is a terminating behaviour of the target with the same trace and result; well-foundedness of the index order is not needed.
* **`silent-divergence-preserved`** (theorem, tier T0). With a well-founded index order, the forward initial-state clause and the forward step diagram, every behaviour 'emit t, then run silently forever' of the source is a behaviour of the target; the final-state clause is not needed.
* **`forward-sim-preserves-non-wrong-behaviours`** (theorem, tier T0). A forward simulation (well-founded index order, initial, final and step clauses) preserves every behaviour of the source that is not a going-wrong behaviour: it is also a behaviour of the target. The same holds along a pipeline in which every pass has a forward simulation (FSimChain L L'), with no receptiveness or determinacy hypothesis.
* **`step-diagrams-compose`** (theorem, tier T0). If R₁ satisfies the forward step diagram from L₁ to L₂ with index order ord₁ and R₂ satisfies it from L₂ to L₃ with ord₂, then the relational composite compRel R₁ R₂ satisfies the forward step diagram from L₁ to L₃ for the lexicographic order compOrd ord₁ ord₂ (transitive closure of ord₂ on the first component, then ord₁); no well-foundedness is needed.
* **`forward-simulations-compose`** (theorem, tier T0). Forward simulations compose vertically: from a forward simulation (ord₁, R₁) from L₁ to L₂ and a forward simulation (ord₂, R₂) from L₂ to L₃, the pair (compOrd ord₁ ord₂, compRel R₁ R₂) is a forward simulation from L₁ to L₃. Clause by clause: the initial-state clauses compose (fsimInit_comp), the final-state clauses compose (fsimFinal_comp), compOrd ord₁ ord₂ is well-founded when ord₁ and ord₂ are (compOrd_wf), and the step clauses compose as in step-diagrams-compose.
* **`flip-forward-to-backward`** (theorem, tier T0). If (ord, R) is a forward simulation from L₁ to L₂, L₁ is receptive and L₂ is determinate with respect to the same event-matching relation M, then some backward simulation from L₁ to L₂ exists, and its relation contains every pair of states related by R. In the special case M = Eq every L₁ is receptive, so a forward simulation into an L₂ that is deterministic (determinate for Eq) suffices.
* **`backward-sim-gives-refinement`** (theorem, tier T0). If (ord, R) is a backward simulation from L₁ to L₂ — a well-founded index order; if L₁ has an initial state then so does L₂; if L₁ has an initial state then every initial state of L₂ is related to some initial state of L₁; and final-state, progress and step clauses that are required only when the related source state is Safe (cannot get stuck before its next observable event) — then L₂ refines L₁: every behaviour of L₂ is a behaviour of L₁ or extends the trace of a going-wrong behaviour of L₁.
* **`refinement-is-inclusion-when-source-never-goes-wrong`** (theorem, tier T0). If L₂ refines L₁ and L₁ has no going-wrong behaviour (NeverGoesWrong L₁, whole-program absence of going wrong), then every behaviour of L₂ is a behaviour of L₁; in particular this holds when a backward simulation from L₁ to L₂ exists.
* **`pipeline-collapses-to-one-forward-simulation`** (theorem, tier T0). A finite chain of forward simulations from L to L' (possibly empty) yields a single forward simulation from L to L', for some index type, order and relation (fsimChain_collapse); and a single forward simulation is a one-link chain (fsimChain_of_isForwardSim).
* **`pipeline-end-to-end-refinement`** (theorem, tier T0). If every pass of a pipeline from L to L' has a forward simulation (FSimChain L L'), the first language L is receptive and the last language L' is determinate for the same event-matching relation M, then L' refines L; nothing is assumed about the intermediate languages. In the special case M = Eq no receptiveness hypothesis is needed: a chain into a deterministic last language suffices.
* **`pipeline-behaviour-equality-when-first-never-goes-wrong`** (theorem, tier T0). If every pass of a pipeline from L to L' has a forward simulation (FSimChain L L'), the first language L is receptive and the last language L' is determinate for the same event-matching relation M, and L has no going-wrong behaviour (NeverGoesWrong L), then L and L' have exactly the same behaviours.
* **`refinement-is-a-preorder`** (theorem, tier T0). Improves is a partial order on behaviours (reflexive, transitive and antisymmetric) whose least element is goesWrong [] (it is improved by every behaviour); RefinedBy is reflexive and transitive on labelled transition systems, i.e. a preorder.
* **`cex-no-measure-infinite-stuttering`** (counterexample, tier T0). There is an instance in which the forward initial-state clause, final-state clause and step diagram all hold with an index order that is not well-founded, between the source Loop (which diverges silently) and the target Done 0 (which terminates at once): the target matches every source step by doing nothing, and silent divergence is not preserved.
* **`cex-going-wrong-not-preserved`** (counterexample, tier T0). There is an instance in which a source that is stuck at once (StuckNow) is forward-simulated, vacuously, by a target that terminates normally (Done 0), also as a one-pass chain: the source's going-wrong behaviour is not a behaviour of the target.
* **`cex-naive-lexicographic-order`** (counterexample, tier T1). There are two forward simulations, OneStep none 0 ⟶ Chain3 and Chain3 ⟶ Done 0 (the second with the non-transitive successor order), whose composite relation fails the step diagram for the lexicographic order without transitive closure, because one source step expands to two middle steps that each stutter in the last system; with compOrd the same composite relation satisfies the step diagram.
* **`cex-non-receptive-source`** (counterexample, tier T1). There is an instance in which a source that accepts only the input 0 is forward-simulated by a target that accepts inputs 0 and 1 and is determinate when any two inputs match: the target has the behaviour 'receive 1, return 1' that the source does not allow, no backward simulation exists, and the target does not refine the source (also as a one-pass pipeline whose first language never goes wrong).
* **`cex-determinacy-clauses-necessary`** (counterexample, tier T1). For each of the five clauses of Determinate M L₂ there is an instance in which a forward simulation exists, the source is receptive, the target satisfies the other four clauses but not this one, the target has a terminating behaviour that the source lacks, no backward simulation exists, and the target does not refine the source. The violations are: a state offering a silent step and an event, or two unmatched events (labels); two silent successors leading to different results (functional); two initial states (init); a final state that can still step (finalNoStep); a final state with two results (finalDet). Each is restated for one-pass pipelines whose first language never goes wrong (Toy.Sim.Cex.cex_pipeline_last_labels_mismatch, Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch, Toy.Sim.Cex.cex_pipeline_last_not_functional, Toy.Sim.Cex.cex_pipeline_last_two_initial_states, Toy.Sim.Cex.cex_pipeline_last_final_state_steps, Toy.Sim.Cex.cex_pipeline_last_two_results).
* **`cex-refinement-not-symmetric`** (counterexample, tier T0). There are instances showing that neither Improves nor RefinedBy is symmetric: going wrong at once is improved by terminating normally but not conversely, and a program that goes wrong at once (StuckNow) is refined by a program that terminates normally (Done 0) but not conversely.
* **`cex-inclusion-needs-source-never-goes-wrong`** (counterexample, tier T0). There is an instance (source StuckNow, which goes wrong at once; target Done 0) in which refinement holds, a backward simulation exists, and a one-pass chain with receptive first and determinate last language exists, yet the target's behaviour 'return 0' is not a source behaviour and the two behaviour sets differ. And there is an instance in which the source never goes wrong but, without refinement, a target behaviour is not a source behaviour.

**Before relying on any result, read its non-claims**: they are listed per result at the start of **Boundaries** (followed by escape hatches, open questions, and formulations found false). In particular: nothing here is a statement about a production compiler (the connection to CompCert is a separately labelled modelling bridge); behaviours with infinitely many events are not modelled, and the infinite reactive-trace case is not examined; per-state `Safe` is much weaker than whole-program `NeverGoesWrong`.

## Applicability

### What the findings apply to

The findings are theorems about the Lean definitions quoted under **Findings → Definitions**, checked by the Lean 4 kernel of the toolchain release `leanprover/lean4` `v4.34.1` (core library only; **no Mathlib**; `autoImplicit = false`). They hold for *every* instance of those definitions: arbitrary event type `E`, result type `Res`, state types, index types in `Type`, and index orders. Nothing beyond the Lean definitions is established by execution.

Basis: execution (Lean kernel check) for every theorem; derived (modeling bridge) for every statement about a real compiler, labelled separately below and per result.

### Model fidelity (toy model)

This is a **toy model**. The definitions are meant to capture the whole-program small-step semantics framework of multi-pass verified compilers, in the form used by the CompCert Coq development (`common/Smallstep.v`, `common/Behaviors.v`, `driver/Compiler.v` at commit `a4ad87b17898cf7b7c8638c32ad694a15f7c0032`, release tag `v3.16`; the relevant CompCert definitions are quoted under **Evidence**): a language is a labelled transition system; a pass is verified by a forward simulation with a well-founded index order; forward simulations compose with a lexicographic order using the transitive closure of the second order; a forward simulation from a receptive source to a determinate target is flipped into a backward simulation; a backward simulation gives behaviour refinement (`behavior_improves`).

Known gaps relative to CompCert (each is a modelling choice; none is a theorem about CompCert):

* **One event per step.** A step carries `Option E` (silent or one event), not a list of events. CompCert's `single_events` side conditions are therefore built in, and CompCert's `atomic` construction (used to flip its multi-event C semantics, `driver/Compiler.v` lines 413–416) is not modelled.
* **Finite traces only.** `Behavior` has `terminates t r`, `diverges t` (silent divergence after a finite trace `t`) and `goesWrong t`. CompCert's `Reacts` behaviour (infinitely many events) is omitted. Consequently a system whose every run emits events forever has *no* behaviour here, and `RefinedBy` does not constrain such runs. **The infinite reactive-trace case is not examined.**
* **No global environment.** There is no memory model, symbol table or global environment; CompCert's `fsim_public_preserved` / `bsim_public_preserved` clauses have no counterpart. Results are integers in CompCert and an arbitrary type `Res` here.
* **Event matching is an arbitrary relation `M : E → E → Prop`** in place of CompCert's `match_traces`; determinacy is split into five separately named clauses (CompCert's `sd_determ` bundles label matching and functionality).
* **All languages of a pipeline share one event type and one result type.** Passes that change the representation of events or results are not modelled.
* **Whole programs only.** No separate compilation, linking, or open (contextual) simulations.
* **Receptiveness and determinacy quantify over all states**, reachable or not (as in CompCert's records).
* **Strict final-state clause.** `FSimFinal` requires the target state related to a final source state to be final itself (as in CompCert's `fsim_match_final_states`).
* **No initial state means going wrong.** A program without an initial state has the behaviour `goesWrong []`, following CompCert's `program_goes_initially_wrong`; this convention is what makes "backward simulation gives refinement" true for the CompCert-shaped initial-state clauses.

Basis: derived (modeling bridge). The correspondence between the Lean definitions and the CompCert definitions is established by side-by-side reading of the quoted CompCert source at the pinned commit, not by any mechanical link; the gaps above are the differences identified by that reading. A theorem in this package transfers to CompCert only for the fragment where the gaps do not matter, and no such transfer is claimed here.

### Relationship between the subjects

The Lean toolchain is the checker of every theorem. CompCert at the pinned commit is the production framework the definitions are modelled on (source inspection only; CompCert is neither built nor executed). The cited papers are prior art for individual results (each card says which passage was read). The package does not depend on any other report.

### Versions

Lean `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), pinned in `lean/lean-toolchain`; Lake project `toy-sim`, library `ToySim`, no dependencies (`lean/lakefile.toml` has one `[[lean_lib]]` and no `[[require]]`). No other Lean version was examined.

The Archive of Formal Proofs entry `VeriComp` (prior art only, not executed) was read in its release archive for Isabelle2026 dated 2026-10-26; the archive URL and SHA-256 are under **Evidence → Primary sources**. Its lemma `forward_simulation_composition`, cited by several cards, exists only in the entry's releases from 2025-03-17 on.

## Findings

### Definitions

Throughout, `E` is the type of observable events and `Res` the type of results; `L₁` is the source side of a pass and `L₂` its target side. Quoted Lean source is from `lean/ToySim/Defs.lean` and `lean/ToySim/Simulation.lean` (doc comments abridged into the prose). In the theorem statements quoted below, `variable {E Res : Type}` is in scope. Every package declaration (namespace `Toy.Sim`) that this report cites by name has its source or its machine-printed statement quoted in a `lean` block: definitions and systems in this section, results and counterexamples with their cards, and supporting lemmas next to their mention or under **Evidence → Machine-printed statements of supporting declarations**. The auxiliary lemmas and proof-internal definitions of `lean/ToySim/ProofAux.lean` are not named; the proof outlines describe them in words.

#### Transition systems and executions

```lean
structure LTS (E Res : Type) where
  State : Type
  step : State → Option E → State → Prop   -- label `none` = silent step
  init : State → Prop
  final : State → Res → Prop

def obs : Option E → List E
  | none => []
  | some a => [a]

inductive Star (L : LTS E Res) : L.State → List E → L.State → Prop where
  | refl (s : L.State) : Star L s [] s
  | step {s s' s'' : L.State} {e : Option E} {t t' : List E}
      (h : L.step s e s') (hs : Star L s' t s'') (ht : t' = obs e ++ t) :
      Star L s t' s''

def Plus (L : LTS E Res) (s : L.State) (t : List E) (s'' : L.State) : Prop :=
  ∃ e s' t', L.step s e s' ∧ Star L s' t' s'' ∧ t = obs e ++ t'

def SilentDiv (L : LTS E Res) (s : L.State) : Prop :=
  ∃ f : Nat → L.State, f 0 = s ∧ ∀ n, L.step (f n) none (f (n + 1))

def Stuck (L : LTS E Res) (s : L.State) : Prop :=
  (∀ e s', ¬ L.step s e s') ∧ (∀ r, ¬ L.final s r)

def Safe (L : LTS E Res) (s : L.State) : Prop :=
  ∀ s', Star L s [] s' → (∃ r, L.final s' r) ∨ (∃ e s'', L.step s' e s'')
```

Meant to capture: the small-step semantics of one whole program in one language of a compiler pipeline. Nothing is assumed about determinism, and final states are not assumed to be stuck. `Safe L s` is *silent-prefix safety* ("`s` cannot get stuck before its next observable event", as CompCert's `safe`); it is a per-state condition and much weaker than whole-program `NeverGoesWrong`: the initial state of `EmitThenStuck`, which emits an event and then gets stuck, is `Safe` (`Toy.Sim.Examples.safe_pos`).

#### Behaviours and refinement

```lean
inductive Behavior (E Res : Type) where
  | terminates (t : List E) (r : Res)   -- emit t, stop in a final state with result r
  | diverges (t : List E)               -- emit t, then run silently forever
  | goesWrong (t : List E)              -- emit t, then be stuck in a non-final state

def Behavior.trace : Behavior E Res → List E
  | .terminates t _ => t
  | .diverges t => t
  | .goesWrong t => t

def HasBehavior (L : LTS E Res) : Behavior E Res → Prop
  | .terminates t r => ∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ L.final s r
  | .diverges t => ∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ SilentDiv L s
  | .goesWrong t =>
      (∃ s₀ s, L.init s₀ ∧ Star L s₀ t s ∧ Stuck L s) ∨ (t = [] ∧ ∀ s, ¬ L.init s)

def Improves (b₁ b₂ : Behavior E Res) : Prop :=        -- source b₁ permits target b₂
  b₁ = b₂ ∨ ∃ t, b₁ = .goesWrong t ∧ t <+: b₂.trace   -- `<+:` is list prefix

def RefinedBy (src tgt : LTS E Res) : Prop :=
  ∀ b₂, HasBehavior tgt b₂ → ∃ b₁, HasBehavior src b₁ ∧ Improves b₁ b₂

def NeverGoesWrong (L : LTS E Res) : Prop :=
  ∀ t, ¬ HasBehavior L (.goesWrong t)
```

Meant to capture: the observable meaning of a whole program (a set of behaviours, possibly several under nondeterminism) and undefined-behaviour-aware compiler correctness ("the compiled program only does what the source allows, where a source that goes wrong allows anything consistent with the trace so far"). Two conventions matter: behaviours with infinitely many events are **not modelled** (a program whose every run emits events forever has no behaviour, `Toy.Sim.Ex.chatter_no_behavior`), and a program **without initial state goes wrong with the empty trace**. `NeverGoesWrong` is whole-program safety (no going-wrong behaviour along any run, for any environment choice); in particular it implies an initial state exists (`Toy.Sim.NeverGoesWrong.exists_init`).

#### Forward simulation (source step ⇒ target steps)

A simulation is given by an index type `I : Type`, an order `ord : I → I → Prop`, and a relation `R : I → L₁.State → L₂.State → Prop`.

```lean
def FSimInit (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂

def FSimFinal (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r

def FSimStep (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
    ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
      R i' s₁' s₂'

structure IsForwardSim (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) :
    Prop where
  wf : WellFounded ord
  init : FSimInit L₁ L₂ R
  final : FSimFinal L₁ L₂ R
  step : FSimStep L₁ L₂ ord R
```

Meant to capture: the proof obligation discharged for one compiler pass in the "source step ⇒ target steps" direction (CompCert's `fsim_properties` without `fsim_public_preserved`). Well-foundedness is a separate field, not part of `FSimStep`.

#### Backward simulation (target step ⇒ source steps)

```lean
def BSimInitExists : Prop :=
  (∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂

def BSimInitMatch (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R i s₁' s₂

def BSimFinal (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ r, R i s₁ s₂ → Safe L₁ s₁ → L₂.final s₂ r →
    ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r

def BSimProgress (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂, R i s₁ s₂ → Safe L₁ s₁ →
    (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂')

def BSimStep (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) : Prop :=
  ∀ i s₁ s₂ e s₂', R i s₁ s₂ → Safe L₁ s₁ → L₂.step s₂ e s₂' →
    ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord i' i)) ∧
      R i' s₁' s₂'

structure IsBackwardSim (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop) :
    Prop where
  wf : WellFounded ord
  initExists : BSimInitExists L₁ L₂
  initMatch : BSimInitMatch L₁ L₂ R
  final : BSimFinal L₁ L₂ R
  progress : BSimProgress L₁ L₂ R
  step : BSimStep L₁ L₂ ord R
```

Meant to capture: the "target step ⇒ source steps" obligation, conditional on the source state being `Safe` (CompCert's `bsim_properties` without `bsim_public_preserved`). This is the direction that behaviour refinement needs.

#### Receptiveness and determinacy

`M : E → E → Prop` is an *event-matching relation*: `M a b` reads "`a` and `b` are alternative responses of the environment to the same interaction" (for example two values returned by the same read). `M = Eq` means the environment never has a choice.

```lean
def LabelMatch (M : E → E → Prop) : Option E → Option E → Prop
  | none, none => True
  | some a, some b => M a b
  | _, _ => False

def Receptive (M : E → E → Prop) (L : LTS E Res) : Prop :=
  ∀ s a s₁ b, L.step s (some a) s₁ → M a b → ∃ s₂, L.step s (some b) s₂

def StepLabelsMatch (M : E → E → Prop) (L : LTS E Res) : Prop :=
  ∀ s e₁ s₁ e₂ s₂, L.step s e₁ s₁ → L.step s e₂ s₂ → LabelMatch M e₁ e₂
def StepFunctional (L : LTS E Res) : Prop :=
  ∀ s e s₁ s₂, L.step s e s₁ → L.step s e s₂ → s₁ = s₂
def InitDeterminate (L : LTS E Res) : Prop :=
  ∀ s s', L.init s → L.init s' → s = s'
def FinalNoStep (L : LTS E Res) : Prop :=
  ∀ s r, L.final s r → ∀ e s', ¬ L.step s e s'
def FinalDeterminate (L : LTS E Res) : Prop :=
  ∀ s r r', L.final s r → L.final s r' → r = r'

structure Determinate (M : E → E → Prop) (L : LTS E Res) : Prop where
  labels : StepLabelsMatch M L
  functional : StepFunctional L
  init : InitDeterminate L
  finalNoStep : FinalNoStep L
  finalDet : FinalDeterminate L
```

Meant to capture: a source that cannot refuse an alternative environment response (`Receptive`; every system is receptive for `M = Eq`, `Toy.Sim.receptive_eq`) and a target whose only nondeterminism is the environment's choice among matching events (`Determinate`; for `M = Eq`, deterministic outright). No algebraic axiom on `M` appears in any statement, but `StepLabelsMatch M L` constrains `M` on the events of `L`: it forces `M a a` for every event `a` that `L` can emit and `M a b ∧ M b a` for any two events offered by the same state (`Toy.Sim.StepLabelsMatch.refl_symm`). Variance in `M`: `Receptive` is antitone — if `M' a b → M a b` for all `a b`, then `Receptive M L → Receptive M' L` (`Toy.Sim.Receptive.anti`) — and it is not monotone (`Toy.Sim.Examples.receptive_not_monotone`: `OneStep (some 0) 0` is receptive for `Eq` but not for the larger relation `AnyInput`); `Determinate` is monotone — if `M a b → M' a b` for all `a b`, then `Determinate M L → Determinate M' L` (`Toy.Sim.Determinate.mono`).

Machine-printed statements (output of `#check @<name>` with `set_option format.width 100` and `set_option pp.fieldNotation false`) of the lemmas named in this paragraph:

```lean
@Toy.Sim.receptive_eq : ∀ {E Res : Type} (L : Toy.Sim.LTS E Res), Toy.Sim.Receptive Eq L
@Toy.Sim.StepLabelsMatch.refl_symm : ∀ {E Res : Type} {M : E → E → Prop} {L : Toy.Sim.LTS E Res},
  Toy.Sim.StepLabelsMatch M L →
    ∀ {s s₁ s₂ : Toy.Sim.LTS.State L} {a b : E},
      Toy.Sim.LTS.step L s (some a) s₁ → Toy.Sim.LTS.step L s (some b) s₂ → M a a ∧ M a b ∧ M b a
@Toy.Sim.Receptive.anti : ∀ {E Res : Type} {M M' : E → E → Prop} {L : Toy.Sim.LTS E Res},
  Toy.Sim.Receptive M L → (∀ (a b : E), M' a b → M a b) → Toy.Sim.Receptive M' L
Toy.Sim.Examples.receptive_not_monotone : Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep (some 0) 0) ∧
  ¬Toy.Sim.Receptive Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.OneStep (some 0) 0)
@Toy.Sim.Determinate.mono : ∀ {E Res : Type} {M M' : E → E → Prop} {L : Toy.Sim.LTS E Res},
  Toy.Sim.Determinate M L → (∀ (a b : E), M a b → M' a b) → Toy.Sim.Determinate M' L
```

#### Composition data and pipelines

```lean
def compOrd (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop) :
    I₂ × I₁ → I₂ × I₁ → Prop :=
  fun p q => Relation.TransGen ord₂ p.1 q.1 ∨ (p.1 = q.1 ∧ ord₁ p.2 q.2)

def compRel {S₁ S₂ S₃ : Type} (R₁ : I₁ → S₁ → S₂ → Prop) (R₂ : I₂ → S₂ → S₃ → Prop) :
    I₂ × I₁ → S₁ → S₃ → Prop :=
  fun p s₁ s₃ => ∃ s₂, R₁ p.2 s₁ s₂ ∧ R₂ p.1 s₂ s₃

inductive FSimChain : LTS E Res → LTS E Res → Prop where
  | nil (L : LTS E Res) : FSimChain L L
  | cons {L₁ L₂ L₃ : LTS E Res} {I : Type} (ord : I → I → Prop)
      (R : I → L₁.State → L₂.State → Prop) :
      IsForwardSim L₁ L₂ ord R → FSimChain L₂ L₃ → FSimChain L₁ L₃
```

`Relation.TransGen` is the transitive closure from the Lean core library. `compOrd` is lexicographic on `I₂ × I₁` with the transitive closure of the second-pass order (one source step may expand to several middle steps, each of which may stutter in the second pass); when `ord₂` is transitive, `compOrd` is the plain lexicographic order (`Toy.Sim.compOrd_iff_lex_of_transitive`). `FSimChain L L'` captures a multi-pass compiler in which every pass has a forward simulation (zero passes allowed); nothing is assumed about the intermediate languages.

A helper used only to state counterexamples (in `lean/ToySim/Counterexamples.lean`):

```lean
def NoBackwardSim (L₁ L₂ : LTS E Res) : Prop :=
  ¬ ∃ (I : Type) (ord : I → I → Prop) (R : I → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord R
```

#### Positive and negative examples of each definition (all proved)

Names are in `Toy.Sim.Examples` (file `lean/ToySim/Examples.lean`).

| Definition | Admits (positive example) | Rejects (negative example) |
| :--- | :--- | :--- |
| `obs` | `obs_pos` | `obs_neg` |
| `Star` | `star_pos` | `star_neg` |
| `Plus` | `plus_pos` | `plus_neg` |
| `SilentDiv` | `silentDiv_pos` | `silentDiv_neg` |
| `Stuck` | `stuck_pos` | `stuck_neg` |
| `Safe` | `safe_pos` (includes `EmitThenStuck`, `Safe` at its initial state yet going wrong after `[1]`) | `safe_neg` |
| `Behavior.trace` | `trace_pos` | — (a projection) |
| `HasBehavior` | `hasBehavior_pos` | `hasBehavior_neg` |
| `Improves` | `improves_pos` | `improves_neg` |
| `RefinedBy` | `refinedBy_pos`, `positive_control_src_tgt`, `nonvacuous_preorder` | `refinedBy_neg` |
| `NeverGoesWrong` | `neverGoesWrong_pos` | `neverGoesWrong_neg` |
| `FSimInit` / `FSimFinal` / `FSimStep` | `fsimInit_pos` / `fsimFinal_pos` / `fsimStep_pos` | `fsimInit_neg` / `fsimFinal_neg` / `fsimStep_neg` |
| `IsForwardSim` | `isForwardSim_pos` | `isForwardSim_neg` (no forward simulation at all from a diverging to a terminating program) |
| `BSimInitExists` / `BSimInitMatch` / `BSimFinal` / `BSimProgress` / `BSimStep` | `bsimInitExists_pos` / `bsimInitMatch_pos` / `bsimFinal_pos` / `bsimProgress_pos` / `bsimStep_pos` | `bsimInitExists_neg` / `bsimInitMatch_neg` / `bsimFinal_neg` / `bsimProgress_neg` / `bsimStep_neg` |
| `IsBackwardSim` | `isBackwardSim_pos` (relation `SrcTgtBackRel`, which contains the forward relation `SrcTgtRel`: `Toy.Sim.Ex.srcTgtRel_sub_srcTgtBackRel`) | `isBackwardSim_neg` |
| `NoBackwardSim` | `noBackwardSim_pos` | `noBackwardSim_neg` |
| `LabelMatch` / `Receptive` | `labelMatch_pos` / `receptive_pos` | `labelMatch_neg` / `receptive_neg` |
| `StepLabelsMatch` / `StepFunctional` / `InitDeterminate` / `FinalNoStep` / `FinalDeterminate` / `Determinate` | `stepLabelsMatch_pos` / `stepFunctional_pos` / `initDeterminate_pos` / `finalNoStep_pos` / `finalDeterminate_pos` / `determinate_pos` | `stepLabelsMatch_neg` / `stepFunctional_neg` / `initDeterminate_neg` / `finalNoStep_neg` / `finalDeterminate_neg` / `determinate_neg` |
| `compOrd` / `compRel` / `FSimChain` | `compOrd_pos` / `compRel_pos` / `fsimChain_pos` | `compOrd_neg` / `compRel_neg` / `fsimChain_neg` |

Machine-printed statements of every name in the table, in table order (`#check @<name>`, same options as above). Each statement shows the concrete instance that the definition admits or rejects; the systems and helper relations it mentions are quoted under **Concrete systems**.

```lean
Toy.Sim.Examples.obs_pos : Toy.Sim.obs (some 3) = [3] ∧ Toy.Sim.obs none = []
Toy.Sim.Examples.obs_neg : Toy.Sim.obs (some 3) ≠ []
Toy.Sim.Examples.star_pos : Toy.Sim.Star Toy.Sim.Ex.Src Toy.Sim.Ex.SrcSt.start [5] (Toy.Sim.Ex.SrcSt.done 5)
Toy.Sim.Examples.star_neg : ¬Toy.Sim.Star (Toy.Sim.Ex.Done 0) () [7] ()
Toy.Sim.Examples.plus_pos : Toy.Sim.Plus Toy.Sim.Ex.Tgt Toy.Sim.Ex.TgtSt.ready [5] (Toy.Sim.Ex.TgtSt.done 5)
Toy.Sim.Examples.plus_neg : ¬Toy.Sim.Plus (Toy.Sim.Ex.Done 0) () [] () ∧ Toy.Sim.Star (Toy.Sim.Ex.Done 0) () [] ()
Toy.Sim.Examples.silentDiv_pos : Toy.Sim.SilentDiv Toy.Sim.Ex.Loop ()
Toy.Sim.Examples.silentDiv_neg : ¬Toy.Sim.SilentDiv (Toy.Sim.Ex.Done 0) () ∧ ¬Toy.Sim.SilentDiv Toy.Sim.Ex.Chatter ()
Toy.Sim.Examples.stuck_pos : Toy.Sim.Stuck Toy.Sim.Ex.StuckNow () ∧ Toy.Sim.Stuck Toy.Sim.Ex.Crash true
Toy.Sim.Examples.stuck_neg : ¬Toy.Sim.Stuck (Toy.Sim.Ex.Done 0) () ∧ ¬Toy.Sim.Stuck Toy.Sim.Ex.Loop ()
Toy.Sim.Examples.safe_pos : Toy.Sim.Safe Toy.Sim.Ex.Src Toy.Sim.Ex.SrcSt.start ∧
  Toy.Sim.Safe (Toy.Sim.Ex.Done 0) () ∧
    Toy.Sim.Safe Toy.Sim.Ex.EmitThenStuck false ∧
      Toy.Sim.HasBehavior Toy.Sim.Ex.EmitThenStuck (Toy.Sim.Behavior.goesWrong [1])
Toy.Sim.Examples.safe_neg : ¬Toy.Sim.Safe Toy.Sim.Ex.Crash false ∧ ¬Toy.Sim.Stuck Toy.Sim.Ex.Crash false
Toy.Sim.Examples.trace_pos : Toy.Sim.Behavior.trace (Toy.Sim.Behavior.terminates [1, 2] 0) = [1, 2] ∧
  Toy.Sim.Behavior.trace (Toy.Sim.Behavior.goesWrong [3]) = [3]
Toy.Sim.Examples.hasBehavior_pos : Toy.Sim.HasBehavior Toy.Sim.Ex.Src (Toy.Sim.Behavior.terminates [5] 5) ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.diverges []) ∧
    Toy.Sim.HasBehavior Toy.Sim.Ex.Crash (Toy.Sim.Behavior.goesWrong []) ∧
      Toy.Sim.HasBehavior Toy.Sim.Ex.NoInit (Toy.Sim.Behavior.goesWrong [])
Toy.Sim.Examples.hasBehavior_neg : ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1) ∧
  ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.goesWrong []) ∧
    ¬Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.terminates [] 0) ∧
      ∀ (b : Toy.Sim.Behavior Nat Nat), ¬Toy.Sim.HasBehavior Toy.Sim.Ex.Chatter b
Toy.Sim.Examples.improves_pos : Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [1])
    (Toy.Sim.Behavior.terminates [1, 2] 0) ∧
  Toy.Sim.Improves (Toy.Sim.Behavior.diverges [4]) (Toy.Sim.Behavior.diverges [4])
Toy.Sim.Examples.improves_neg : ¬Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [1]) (Toy.Sim.Behavior.terminates [2] 0) ∧
  ¬Toy.Sim.Improves (Toy.Sim.Behavior.diverges []) (Toy.Sim.Behavior.terminates [] 0) ∧
    ¬Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 0) (Toy.Sim.Behavior.terminates [] 1)
Toy.Sim.Examples.refinedBy_pos : Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0) ∧
  Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Src
Toy.Sim.Examples.positive_control_src_tgt : Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  ∀ (b : Toy.Sim.Behavior Nat Nat), Toy.Sim.HasBehavior Toy.Sim.Ex.Tgt b → Toy.Sim.HasBehavior Toy.Sim.Ex.Src b
Toy.Sim.Examples.nonvacuous_preorder : (Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [])
      (Toy.Sim.Behavior.goesWrong [1]) ∧
    Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [1]) (Toy.Sim.Behavior.terminates [1, 2] 0)) ∧
  (Toy.Sim.Improves (Toy.Sim.Behavior.diverges [4]) (Toy.Sim.Behavior.diverges [4]) ∧
      Toy.Sim.Improves (Toy.Sim.Behavior.diverges [4]) (Toy.Sim.Behavior.diverges [4])) ∧
    Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow Toy.Sim.Ex.Src ∧ Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
Toy.Sim.Examples.refinedBy_neg : ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow ∧
  ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Examples.neverGoesWrong_pos : Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Src ∧ Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Loop
Toy.Sim.Examples.neverGoesWrong_neg : ¬Toy.Sim.NeverGoesWrong Toy.Sim.Ex.StuckNow ∧
  ¬Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Crash ∧ ¬Toy.Sim.NeverGoesWrong Toy.Sim.Ex.NoInit
Toy.Sim.Examples.fsimInit_pos : Toy.Sim.FSimInit Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtRel
Toy.Sim.Examples.fsimFinal_pos : Toy.Sim.FSimFinal Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtRel
Toy.Sim.Examples.fsimStep_pos : Toy.Sim.FSimStep Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtRel
Toy.Sim.Examples.fsimInit_neg : ¬Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse
Toy.Sim.Examples.fsimFinal_neg : ¬Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue
Toy.Sim.Examples.fsimStep_neg : ¬Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relBefore
Toy.Sim.Examples.isForwardSim_pos : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Src (fun x x_1 => False) fun x s s' => s = s'
Toy.Sim.Examples.isForwardSim_neg : ¬∃ I ord R, Toy.Sim.IsForwardSim Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) ord R
Toy.Sim.Examples.bsimInitExists_pos : Toy.Sim.BSimInitExists Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
Toy.Sim.Examples.bsimInitMatch_pos : Toy.Sim.BSimInitMatch Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtBackRel
Toy.Sim.Examples.bsimFinal_pos : Toy.Sim.BSimFinal Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtBackRel
Toy.Sim.Examples.bsimProgress_pos : Toy.Sim.BSimProgress Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtBackRel
Toy.Sim.Examples.bsimStep_pos : Toy.Sim.BSimStep Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
  Toy.Sim.Ex.SrcTgtBackRel
Toy.Sim.Examples.bsimInitExists_neg : ¬Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
Toy.Sim.Examples.bsimInitMatch_neg : ¬Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relFalse
Toy.Sim.Examples.bsimFinal_neg : ¬Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue
Toy.Sim.Examples.bsimProgress_neg : ¬Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow Toy.Sim.Cex.relTrue
Toy.Sim.Examples.bsimStep_neg : ¬Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relToFalse
Toy.Sim.Examples.isBackwardSim_pos : Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
  Toy.Sim.Ex.SrcTgtBackRel
Toy.Sim.Ex.srcTgtRel_sub_srcTgtBackRel : ∀ (i : Nat) (s₁ : Toy.Sim.Ex.SrcSt) (s₂ : Toy.Sim.Ex.TgtSt),
  Toy.Sim.Ex.SrcTgtRel i s₁ s₂ → ∃ i', Toy.Sim.Ex.SrcTgtBackRel i' s₁ s₂
Toy.Sim.Examples.isBackwardSim_neg : Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Examples.noBackwardSim_pos : Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep none 0)
  (Toy.Sim.Ex.TwoBranch none none 0 1)
Toy.Sim.Examples.noBackwardSim_neg : ¬Toy.Sim.NoBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
Toy.Sim.Examples.labelMatch_pos : Toy.Sim.LabelMatch Eq (some 1) (some 1) ∧
  Toy.Sim.LabelMatch Toy.Sim.Ex.AnyInput (some 0) (some 1) ∧ Toy.Sim.LabelMatch Eq none none
Toy.Sim.Examples.receptive_pos : Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep (some 0) 0)
Toy.Sim.Examples.labelMatch_neg : ¬Toy.Sim.LabelMatch Toy.Sim.Ex.AnyInput none (some 1) ∧
  ¬Toy.Sim.LabelMatch Toy.Sim.Ex.AnyInput (some 1) none ∧ ¬Toy.Sim.LabelMatch Eq (some 0) (some 1)
Toy.Sim.Examples.receptive_neg : ¬Toy.Sim.Receptive Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.OneStep (some 0) 0)
Toy.Sim.Examples.stepLabelsMatch_pos : Toy.Sim.StepLabelsMatch Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt
Toy.Sim.Examples.stepFunctional_pos : Toy.Sim.StepFunctional Toy.Sim.Ex.Tgt
Toy.Sim.Examples.initDeterminate_pos : Toy.Sim.InitDeterminate Toy.Sim.Ex.Tgt
Toy.Sim.Examples.finalNoStep_pos : Toy.Sim.FinalNoStep Toy.Sim.Ex.Tgt
Toy.Sim.Examples.finalDeterminate_pos : Toy.Sim.FinalDeterminate Toy.Sim.Ex.Tgt
Toy.Sim.Examples.determinate_pos : Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt
Toy.Sim.Examples.stepLabelsMatch_neg : ¬Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch none (some 1) 0 1)
Toy.Sim.Examples.stepFunctional_neg : ¬Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
  ¬Toy.Sim.StepFunctional Toy.Sim.Ex.Mid
Toy.Sim.Examples.initDeterminate_neg : ¬Toy.Sim.InitDeterminate Toy.Sim.Ex.TwoInits
Toy.Sim.Examples.finalNoStep_neg : ¬Toy.Sim.FinalNoStep Toy.Sim.Ex.FinalSteps
Toy.Sim.Examples.finalDeterminate_neg : ¬Toy.Sim.FinalDeterminate Toy.Sim.Ex.TwoResults
Toy.Sim.Examples.determinate_neg : ¬Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Mid
Toy.Sim.Examples.compOrd_pos : Toy.Sim.compOrd (fun i' i => i' < i) Toy.Sim.Cex.succOrd (0, 9) (2, 0) ∧
  Toy.Sim.compOrd (fun i' i => i' < i) Toy.Sim.Cex.succOrd (1, 3) (1, 4)
Toy.Sim.Examples.compRel_pos : Toy.Sim.compRel Toy.Sim.Ex.SrcMidRel Toy.Sim.Ex.MidTgtRel ((), 1) Toy.Sim.Ex.SrcSt.start
  Toy.Sim.Ex.TgtSt.ready
Toy.Sim.Examples.fsimChain_pos : Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Src
Toy.Sim.Examples.compOrd_neg : ¬Toy.Sim.compOrd (fun i' i => i' < i) Toy.Sim.Cex.succOrd (1, 4) (1, 4) ∧
  ¬Toy.Sim.compOrd (fun i' i => i' < i) Toy.Sim.Cex.succOrd (2, 0) (1, 5)
Toy.Sim.Examples.compRel_neg : ¬Toy.Sim.compRel Toy.Sim.Ex.SrcMidRel Toy.Sim.Ex.MidTgtRel ((), 0) Toy.Sim.Ex.SrcSt.start
    Toy.Sim.Ex.TgtSt.ready
Toy.Sim.Examples.fsimChain_neg : ¬Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
```

### Concrete systems

Witnesses and counterexamples use small concrete systems with events and results in `Nat`, defined in `Toy.Sim.Ex` (`lean/ToySim/Systems.lean`) unless another namespace is given.

| System | Description | Behaviours |
| :--- | :--- | :--- |
| `Done r` | one state, no step, final with result `r` | exactly `terminates [] r` (`done_behavior`) |
| `Loop` | one state, silent self-loop | exactly `diverges []` (`loop_behavior`) |
| `StuckNow` | one state, no step, not final | exactly `goesWrong []` (`stuckNow_behavior`) |
| `NoInit` | no initial state | exactly `goesWrong []` (`noInit_behavior`) |
| `Chatter` | one state emitting event `0` forever | none (`chatter_no_behavior`) |
| `TwoResults` | one state, final with results `0` and `1` | `terminates [] 0`, `terminates [] 1` |
| `OneStep e r` | one step labelled `e`, then final with `r` | exactly `terminates (obs e) r` (`oneStep_behavior`) |
| `Crash` | one silent step, then stuck | includes `goesWrong []` |
| `EmitThenStuck` | emits event `1`, then stuck | includes `goesWrong [1]` |
| `Spin` | one silent step, then a silent self-loop | includes `diverges []` |
| `TwoInits`, `FinalSteps` | targets violating one determinacy clause each | see the source below |
| `TwoBranch e₁ e₂ r₁ r₂` | from the initial state, `e₁` leads to result `r₁` and `e₂` to result `r₂` | includes both branches |
| `Src`, `Mid`, `Tgt` | "read an input `n`, return `n`": `Src` has a silent start-up step, `Tgt` a silent step after the read, `Mid` is internally nondeterministic | `Tgt`: exactly `terminates [n] n` for each `n` (`Toy.Sim.Examples.tgt_behavior`) |
| `Chain3` (in `Toy.Sim.Cex`) | two silent steps, then final with `0` | used for the composite-order counterexample |
| `StuckOrDone`, `DoneOrChatter`, `TermOrDiverge`, `DoneWithJunk` (in `Toy.Sim.Boundary`) | two initial states (stuck / final `0`); two initial states (final `0` / emitting `0` forever); silently to final `0` or to a silent loop; final initial state plus an unreachable state with two silent successors | used by boundary facts |

Machine-printed statements of the behaviour lemmas cited in the table (`#check @<name>`, same options as above):

```lean
Toy.Sim.Ex.done_behavior : ∀ (r : Nat) (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior (Toy.Sim.Ex.Done r) b ↔ b = Toy.Sim.Behavior.terminates [] r
Toy.Sim.Ex.loop_behavior : ∀ (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior Toy.Sim.Ex.Loop b ↔ b = Toy.Sim.Behavior.diverges []
Toy.Sim.Ex.stuckNow_behavior : ∀ (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow b ↔ b = Toy.Sim.Behavior.goesWrong []
Toy.Sim.Ex.noInit_behavior : ∀ (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior Toy.Sim.Ex.NoInit b ↔ b = Toy.Sim.Behavior.goesWrong []
Toy.Sim.Ex.chatter_no_behavior : ∀ (b : Toy.Sim.Behavior Nat Nat), ¬Toy.Sim.HasBehavior Toy.Sim.Ex.Chatter b
Toy.Sim.Ex.oneStep_behavior : ∀ (e : Option Nat) (r : Nat) (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep e r) b ↔ b = Toy.Sim.Behavior.terminates (Toy.Sim.obs e) r
Toy.Sim.Examples.tgt_behavior : ∀ (b : Toy.Sim.Behavior Nat Nat),
  Toy.Sim.HasBehavior Toy.Sim.Ex.Tgt b ↔ ∃ n, b = Toy.Sim.Behavior.terminates [n] n
```

Lean source of the systems and helper relations used in the counterexample statements quoted below:

```lean
-- namespace Toy.Sim.Ex (lean/ToySim/Systems.lean)
abbrev Done (r : Nat) : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ r' => r' = r

abbrev Loop : LTS Nat Nat where
  State := Unit
  step := fun _ e _ => e = none
  init := fun _ => True
  final := fun _ _ => False

abbrev StuckNow : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ _ => False

abbrev NoInit : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => False
  final := fun _ _ => False

abbrev Chatter : LTS Nat Nat where
  State := Unit
  step := fun _ e _ => e = some 0
  init := fun _ => True
  final := fun _ _ => False

abbrev TwoResults : LTS Nat Nat where
  State := Unit
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun _ r => r = 0 ∨ r = 1

abbrev OneStep (e : Option Nat) (r : Nat) : LTS Nat Nat where
  State := Bool
  step := fun s e' s' => s = false ∧ e' = e ∧ s' = true
  init := fun s => s = false
  final := fun s r' => s = true ∧ r' = r

abbrev Crash : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = none ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

abbrev EmitThenStuck : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = some 1 ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

abbrev Spin : LTS Nat Nat where
  State := Bool
  step := fun _ e s' => e = none ∧ s' = true
  init := fun s => s = false
  final := fun _ _ => False

abbrev TwoInits : LTS Nat Nat where
  State := Bool
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun s r => (s = false ∧ r = 0) ∨ (s = true ∧ r = 1)

abbrev FinalSteps : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = false ∧ e = none ∧ s' = true
  init := fun s => s = false
  final := fun s r => (s = false ∧ r = 0) ∨ (s = true ∧ r = 1)

inductive Three where
  | root | left | right
  deriving DecidableEq

abbrev TwoBranch (e₁ e₂ : Option Nat) (r₁ r₂ : Nat) : LTS Nat Nat where
  State := Three
  step := fun s e s' => s = .root ∧ ((e = e₁ ∧ s' = .left) ∨ (e = e₂ ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => (s = .left ∧ r = r₁) ∨ (s = .right ∧ r = r₂)

def branchRel : Unit → Bool → Three → Prop :=
  fun _ s s' => (s = false ∧ s' = .root) ∨ (s = true ∧ s' = .left)

inductive SrcSt where
  | start | ready | done (n : Nat)

inductive SrcStep : SrcSt → Option Nat → SrcSt → Prop where
  | boot : SrcStep .start none .ready
  | read (n : Nat) : SrcStep .ready (some n) (.done n)

abbrev Src : LTS Nat Nat where
  State := SrcSt
  step := SrcStep
  init := fun s => s = .start
  final := fun s r => s = .done r

inductive MidSt where
  | ready | gotA (n : Nat) | gotB (n : Nat) | done (n : Nat)

inductive MidStep : MidSt → Option Nat → MidSt → Prop where
  | readA (n : Nat) : MidStep .ready (some n) (.gotA n)
  | readB (n : Nat) : MidStep .ready (some n) (.gotB n)
  | retA (n : Nat) : MidStep (.gotA n) none (.done n)
  | retB (n : Nat) : MidStep (.gotB n) none (.done n)

abbrev Mid : LTS Nat Nat where
  State := MidSt
  step := MidStep
  init := fun s => s = .ready
  final := fun s r => s = .done r

inductive TgtSt where
  | ready | got (n : Nat) | done (n : Nat)

inductive TgtStep : TgtSt → Option Nat → TgtSt → Prop where
  | read (n : Nat) : TgtStep .ready (some n) (.got n)
  | ret (n : Nat) : TgtStep (.got n) none (.done n)

abbrev Tgt : LTS Nat Nat where
  State := TgtSt
  step := TgtStep
  init := fun s => s = .ready
  final := fun s r => s = .done r

abbrev AnyInput : Nat → Nat → Prop := fun _ _ => True

inductive SrcTgtRel : Nat → SrcSt → TgtSt → Prop where
  | start : SrcTgtRel 1 .start .ready
  | ready : SrcTgtRel 0 .ready .ready
  | done (n : Nat) : SrcTgtRel 0 (.done n) (.done n)

inductive SrcMidRel : Nat → SrcSt → MidSt → Prop where
  | start : SrcMidRel 1 .start .ready
  | ready : SrcMidRel 0 .ready .ready
  | done (n : Nat) : SrcMidRel 0 (.done n) (.done n)

inductive MidTgtRel : Unit → MidSt → TgtSt → Prop where
  | ready : MidTgtRel () .ready .ready
  | gotA (n : Nat) : MidTgtRel () (.gotA n) (.got n)
  | gotB (n : Nat) : MidTgtRel () (.gotB n) (.got n)
  | done (n : Nat) : MidTgtRel () (.done n) (.done n)

inductive SrcTgtBackRel : Nat → SrcSt → TgtSt → Prop where
  | start : SrcTgtBackRel 0 .start .ready
  | ready : SrcTgtBackRel 0 .ready .ready
  | got (n : Nat) : SrcTgtBackRel 1 (.done n) (.got n)
  | done (n : Nat) : SrcTgtBackRel 0 (.done n) (.done n)

-- namespace Toy.Sim.Cex (lean/ToySim/Counterexamples.lean)
abbrev relTrue {α β : Type} : Unit → α → β → Prop := fun _ _ _ => True

abbrev relFalse {α β : Type} : Unit → α → β → Prop := fun _ _ _ => False

abbrev relEq {α : Type} : Unit → α → α → Prop := fun _ s s' => s = s'

abbrev emptyOrd : Unit → Unit → Prop := fun _ _ => False

abbrev fullOrd : Unit → Unit → Prop := fun _ _ => True

abbrev relBefore : Unit → Bool → Unit → Prop := fun _ s _ => s = false

abbrev Chain3 : LTS Nat Nat where
  State := Three
  step := fun s e s' =>
    e = none ∧ ((s = .root ∧ s' = .left) ∨ (s = .left ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => s = .right ∧ r = 0

def chainRel₁ : Unit → Bool → Three → Prop :=
  fun _ s s' => (s = false ∧ s' = .root) ∨ (s = true ∧ s' = .right)

def chainRel₂ : Nat → Three → Unit → Prop :=
  fun i s _ => (s = .root ∧ i = 2) ∨ (s = .left ∧ i = 1) ∨ (s = .right ∧ i = 0)

def succOrd : Nat → Nat → Prop := fun i' i => i' + 1 = i

def naiveCompOrd {I₁ I₂ : Type} (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop) :
    I₂ × I₁ → I₂ × I₁ → Prop :=
  fun p q => ord₂ p.1 q.1 ∨ (p.1 = q.1 ∧ ord₁ p.2 q.2)

abbrev relToFalse : Unit → Unit → Bool → Prop := fun _ _ s' => s' = false

-- namespace Toy.Sim.Examples (lean/ToySim/Examples.lean)
def spinRel : Nat → Bool → Unit → Prop :=
  fun i s _ => (s = false ∧ i = 1) ∨ (s = true ∧ i = 0)
```

Lean source of the four systems used by the boundary facts (listed in the table above) and of the relation `chooseRel` used in one of them; `Three` is the three-state type quoted above (states `root`, `left`, `right`):

```lean
-- namespace Toy.Sim.Boundary (lean/ToySim/Boundaries.lean)
abbrev StuckOrDone : LTS Nat Nat where
  State := Bool
  step := fun _ _ _ => False
  init := fun _ => True
  final := fun s r => s = true ∧ r = 0

abbrev DoneOrChatter : LTS Nat Nat where
  State := Bool
  step := fun s e s' => s = true ∧ e = some 0 ∧ s' = true
  init := fun _ => True
  final := fun s r => s = false ∧ r = 0

abbrev TermOrDiverge : LTS Nat Nat where
  State := Three
  step := fun s e s' =>
    e = none ∧ ((s = .root ∧ (s' = .left ∨ s' = .right)) ∨ (s = .right ∧ s' = .right))
  init := fun s => s = .root
  final := fun s r => s = .left ∧ r = 0

def chooseRel : Unit → Three → Unit → Prop := fun _ s _ => s = .root

abbrev DoneWithJunk : LTS Nat Nat where
  State := Bool
  step := fun s e _ => s = true ∧ e = none
  init := fun s => s = false
  final := fun s r => s = false ∧ r = 0
```

### Results

Each result below gives: kind and tier; the Lean statement (exact source signature; for the core results also the restatement with every named clause unfolded, from `lean/ToySim/Unfolded.lean`, where each restatement is derived from the folded statement in Lean); a proof outline; the hypothesis ledger with tightness and counterexample names; the depth label; the non-vacuity witness (theorem cards) or positive control (counterexample cards); prior art; the design question; and the evidence basis. The non-claims of every result are listed at the start of **Boundaries**. Counterexample statements are quoted as machine-printed by Lean (`#check`); every counterexample is a single theorem stating that a concrete instance satisfies all other hypotheses of the result and that its conclusion fails.

#### `partial-run-simulated`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `simulation_star` composed with the initial-state clause; restated for labelled transition systems with one event per step.

**Lean:** `Toy.Sim.fsimInit_fsimStep_partial_run_simulated`; unfolded restatement: `Toy.Sim.Unfolded.partial_run_simulated`.

**Plain claim.** If a relation R between the states of a source LTS L₁ and a target LTS L₂ satisfies the forward initial-state clause and the forward step diagram (for any index order, well-founded or not), then every finite run of L₁ from an initial state s₀, with trace t and ending in s, is matched by a run of L₂ with the same trace t that starts in an initial state related to s₀ and ends in a state related to s.

**Lean statement.**

```lean
-- Toy.Sim.fsimInit_fsimStep_partial_run_simulated
theorem fsimInit_fsimStep_partial_run_simulated
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    {s₀ s : L₁.State} {t : List E} (h₀ : L₁.init s₀) (hrun : Star L₁ s₀ t s) :
    ∃ i₀ i s₀' s', L₂.init s₀' ∧ R i₀ s₀ s₀' ∧ Star L₂ s₀' t s' ∧ R i s s'
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.partial_run_simulated
theorem partial_run_simulated
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (s₀ s : L₁.State) (t : List E) (h₀ : L₁.init s₀) (hrun : Star L₁ s₀ t s) :
    ∃ i₀ i s₀' s', L₂.init s₀' ∧ R i₀ s₀ s₀' ∧ Star L₂ s₀' t s' ∧ R i s s'
```

**Proof outline.** Induction on the source run `Star L₁ s₀ t s` (an auxiliary lemma): each source step is matched by the step diagram, whose `Plus`/`Star` alternative is weakened to `Star`; the runs are concatenated with `Toy.Sim.Star.trans`. The initial target state comes from `FSimInit`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimInit L₁ L₂ R` | supplies a related initial target state for the start of the run | tight: `Toy.Sim.Cex.cex_fsim_without_init_clause` |
| `FSimStep L₁ L₂ ord R` | matches each source step by target steps with the same trace | tight: `Toy.Sim.Cex.cex_fsim_without_step_diagram` |
| `L₁.init s₀` | the forward clauses only constrain source states reachable from a related initial state | tight: `Toy.Sim.Cex.cex_partial_run_from_non_initial_state` |
| `Star L₁ s₀ t s` | the run being simulated | tight: `Toy.Sim.Cex.cex_partial_run_without_source_run` |

**Depth:** shallow — Induction on the source run; each step is one use of the step diagram.

**Non-vacuity witness.** Src and Tgt (read one input, return it) with the relation SrcTgtRel and the run start ⟶ done 5 with trace [5]. (`Toy.Sim.Examples.nonvacuous_partial_run_simulated`)

```lean
Toy.Sim.Examples.nonvacuous_partial_run_simulated : Toy.Sim.FSimInit Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.FSimStep Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtRel ∧
    Toy.Sim.LTS.init Toy.Sim.Ex.Src Toy.Sim.Ex.SrcSt.start ∧
      Toy.Sim.Star Toy.Sim.Ex.Src Toy.Sim.Ex.SrcSt.start [5] (Toy.Sim.Ex.SrcSt.done 5)
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `simulation_star` (line 937), simulation of a source execution by a target execution with the same trace.
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: record `fsim_properties` (line 566) has the same four clauses (well-founded index order, initial states, final states, step diagram 'Plus, or Star with a smaller index'), plus a clause about public symbols that has no counterpart in this model.

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimInit_fsimStep_partial_run_simulated`, `Toy.Sim.Unfolded.partial_run_simulated`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `simulation_star` composed with `fsim_match_initial_states` (quoted under Evidence), restricted to steps with at most one event. It is not claimed that CompCert's lemma was checked against this model mechanically.

#### `terminating-behaviours-preserved`

**Kind:** theorem. **Tier:** T0 — Standard: the termination case of CompCert's `forward_simulation_state_behaves` (common/Behaviors.v, line 284) and of Theorem 4 of Leroy (JAR 2009, Section 3.7); here the measure is not needed for this case.

**Lean:** `Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates`; unfolded restatement: `Toy.Sim.Unfolded.terminating_behaviours_preserved`.

**Plain claim.** With the forward initial-state clause, the forward step diagram (any index order) and the forward final-state clause, every terminating behaviour of the source (trace t, result r) is a terminating behaviour of the target with the same trace and result; well-foundedness of the index order is not needed.

**Lean statement.**

```lean
-- Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates
theorem fsimInit_fsimStep_fsimFinal_preserve_terminates
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    (hfinal : FSimFinal L₁ L₂ R)
    {t : List E} {r : Res} (hb : HasBehavior L₁ (.terminates t r)) :
    HasBehavior L₂ (.terminates t r)
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.terminating_behaviours_preserved
theorem terminating_behaviours_preserved
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r)
    (t : List E) (r : Res)
    (hb : ∃ s₀ s, L₁.init s₀ ∧ Star L₁ s₀ t s ∧ L₁.final s r) :
    ∃ s₀' s', L₂.init s₀' ∧ Star L₂ s₀' t s' ∧ L₂.final s' r
```

**Proof outline.** Derived in Lean from `fsimInit_fsimStep_partial_run_simulated` and one use of `FSimFinal`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimInit L₁ L₂ R` | start of the matched run | tight: `Toy.Sim.Cex.cex_fsim_without_init_clause` |
| `FSimStep L₁ L₂ ord R` | matches the source run step by step | tight: `Toy.Sim.Cex.cex_fsim_without_step_diagram` |
| `FSimFinal L₁ L₂ R` | the related target state is final with the same result | tight: `Toy.Sim.Cex.cex_fsim_without_final_clause` |
| `HasBehavior L₁ (.terminates t r)` | the behaviour being preserved | tight: `Toy.Sim.Cex.cex_preservation_without_source_behavior` |

**Depth:** shallow — Partial-run simulation followed by one use of the final-state clause.

**Non-vacuity witness.** Src and Tgt with SrcTgtRel; Src has the behaviour 'read 5, return 5'. (`Toy.Sim.Examples.nonvacuous_preserve_terminates`)

```lean
Toy.Sim.Examples.nonvacuous_preserve_terminates : Toy.Sim.FSimInit Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.FSimStep Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtRel ∧
    Toy.Sim.FSimFinal Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt Toy.Sim.Ex.SrcTgtRel ∧
      Toy.Sim.HasBehavior Toy.Sim.Ex.Src (Toy.Sim.Behavior.terminates [5] 5)
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `forward_simulation_state_behaves` (line 284), `forward_simulation_behavior_improves` (line 316) and `forward_simulation_same_safe_behavior` (line 337).
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 3.7 (Definition 12, Theorem 4): the 'star' forward simulation diagram, with a measure on source states in a well-founded order that must decrease when the target stutters, introduced to rule out the 'infinite stuttering problem'; Theorem 4: under the initial-state, final-state and star-simulation hypotheses, every behaviour of the source that does not go wrong is a behaviour of the target. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates`, `Toy.Sim.Unfolded.terminating_behaviours_preserved`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors the termination case of CompCert's `forward_simulation_state_behaves`; the observation that well-foundedness is not needed for this case is a fact about the model and is consistent with that proof, but is not separately checked in CompCert.

#### `silent-divergence-preserved`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `simulation_forever_silent`; the 'star' simulation with a well-founded measure of Leroy (JAR 2009, Section 3.7, Theorem 4).

**Lean:** `Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges`; unfolded restatement: `Toy.Sim.Unfolded.silent_divergence_preserved`.

**Plain claim.** With a well-founded index order, the forward initial-state clause and the forward step diagram, every behaviour 'emit t, then run silently forever' of the source is a behaviour of the target; the final-state clause is not needed.

**Lean statement.**

```lean
-- Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges
theorem wf_fsimInit_fsimStep_preserve_diverges
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hwf : WellFounded ord)
    (hinit : FSimInit L₁ L₂ R) (hstep : FSimStep L₁ L₂ ord R)
    {t : List E} (hb : HasBehavior L₁ (.diverges t)) :
    HasBehavior L₂ (.diverges t)
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.silent_divergence_preserved
theorem silent_divergence_preserved
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hwf : WellFounded ord)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    (t : List E)
    (hb : ∃ s₀ s, L₁.init s₀ ∧ Star L₁ s₀ t s ∧
      ∃ f : Nat → L₁.State, f 0 = s ∧ ∀ n, L₁.step (f n) none (f (n + 1))) :
    ∃ s₀' s', L₂.init s₀' ∧ Star L₂ s₀' t s' ∧
      ∃ g : Nat → L₂.State, g 0 = s' ∧ ∀ n, L₂.step (g n) none (g (n + 1))
```

**Proof outline.** Simulate the finite prefix with `fsimInit_fsimStep_partial_run_simulated`. Then consider the set of target states that silently reach a state related to some point `f n` of the source's infinite silent run. By well-founded induction on the index, every state of this set has a silent successor in the set: a stuttering step decreases the index, so after finitely many stutters the target makes a `Plus` step, whose first step is silent because the trace is empty. A choice principle (`Classical.axiomOfChoice`, used in an auxiliary lemma) then assembles the infinite target run as a function `Nat → L₂.State`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `WellFounded ord` | rules out infinite stuttering: the target cannot match infinitely many source steps by doing nothing | tight: `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved` |
| `FSimInit L₁ L₂ R` | start of the matched run | tight: `Toy.Sim.Cex.cex_fsim_without_init_clause_diverges` |
| `FSimStep L₁ L₂ ord R` | matches the source run step by step | tight: `Toy.Sim.Cex.cex_fsim_without_step_diagram_diverges` |
| `HasBehavior L₁ (.diverges t)` | the behaviour being preserved | tight: `Toy.Sim.Cex.cex_preservation_without_source_behavior` |

**Depth:** substantive — Well-founded induction on the index to find the next target step, then a choice principle to assemble the infinite target run as a function.

**Non-vacuity witness.** Spin (a silent step, then a silent self-loop) simulated by Loop: the target stutters once, then follows the loop. (`Toy.Sim.Examples.nonvacuous_preserve_diverges`)

```lean
Toy.Sim.Examples.nonvacuous_preserve_diverges : (WellFounded fun i' i => i' < i) ∧
  Toy.Sim.FSimInit Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop Toy.Sim.Examples.spinRel ∧
    Toy.Sim.FSimStep Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop (fun i' i => i' < i) Toy.Sim.Examples.spinRel ∧
      Toy.Sim.HasBehavior Toy.Sim.Ex.Spin (Toy.Sim.Behavior.diverges [])
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `simulation_forever_silent` (line 972).
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 3.7 (Definition 12, Theorem 4): the 'star' forward simulation diagram, with a measure on source states in a well-founded order that must decrease when the target stutters, introduced to rule out the 'infinite stuttering problem'; Theorem 4: under the initial-state, final-state and star-simulation hypotheses, every behaviour of the source that does not go wrong is a behaviour of the target. (Passages checked in the author's version of the article.)
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges`, `Toy.Sim.Unfolded.silent_divergence_preserved`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `simulation_forever_silent`, which uses the well-founded `order` of `fsim_properties`. In CompCert, silent divergence is `Forever_silent`, defined coinductively; here it is a function `Nat → State`, which is why a choice principle is used.

#### `forward-sim-preserves-non-wrong-behaviours`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `forward_simulation_same_safe_behavior`; Theorem 4 of Leroy (JAR 2009, Section 3.7); property (3) of Leroy (CACM 2009, Section 2.1). The chain form iterates the single-pass form.

**Lean:** `Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors`, `Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors`.

**Plain claim.** A forward simulation (well-founded index order, initial, final and step clauses) preserves every behaviour of the source that is not a going-wrong behaviour: it is also a behaviour of the target. The same holds along a pipeline in which every pass has a forward simulation (FSimChain L L'), with no receptiveness or determinacy hypothesis.

**Lean statement.**

```lean
-- Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors
theorem isForwardSim_preserves_non_goesWrong_behaviors
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsForwardSim L₁ L₂ ord R)
    {b : Behavior E Res} (hb : HasBehavior L₁ b) (hnw : ∀ t, b ≠ .goesWrong t) :
    HasBehavior L₂ b

-- Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors
theorem fsimChain_preserves_non_goesWrong_behaviors {L L' : LTS E Res}
    (hchain : FSimChain L L')
    {b : Behavior E Res} (hb : HasBehavior L b) (hnw : ∀ t, b ≠ .goesWrong t) :
    HasBehavior L' b
```

**Proof outline.** Case analysis on the behaviour: the terminating case uses `fsimInit_fsimStep_fsimFinal_preserve_terminates`, the diverging case `wf_fsimInit_fsimStep_preserve_diverges`, and the going-wrong case is excluded by the hypothesis. The chain form is induction on `FSimChain`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `IsForwardSim L₁ L₂ ord R, clause wf (single-pass theorem)` | needed for diverging behaviours | tight: `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved` |
| `IsForwardSim L₁ L₂ ord R, clause init (single-pass theorem)` | start of the matched run | tight: `Toy.Sim.Cex.cex_fsim_without_init_clause` |
| `IsForwardSim L₁ L₂ ord R, clause final (single-pass theorem)` | needed for terminating behaviours | tight: `Toy.Sim.Cex.cex_fsim_without_final_clause` |
| `IsForwardSim L₁ L₂ ord R, clause step (single-pass theorem)` | matches the source run step by step | tight: `Toy.Sim.Cex.cex_fsim_without_step_diagram` |
| `FSimChain L L' (chain theorem)` | every pass has a forward simulation | tight: `Toy.Sim.Cex.cex_pipeline_preserves_without_chain` |
| `HasBehavior L₁ b / HasBehavior L b (both theorems)` | the behaviour being preserved | tight: `Toy.Sim.Cex.cex_preservation_without_source_behavior` |
| `∀ t, b ≠ .goesWrong t (both theorems)` | going-wrong behaviours are not preserved | tight: `Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved` |

**Depth:** shallow — Case split on the behaviour and the two preservation results; induction on the chain.

**Non-vacuity witness.** Src and Tgt with SrcTgtRel and the behaviour 'read 5, return 5'; the chain Src ⟶ Mid ⟶ Tgt and the same behaviour. (`Toy.Sim.Examples.nonvacuous_isForwardSim_preserves`, `Toy.Sim.Examples.nonvacuous_pipeline_preserves`)

```lean
Toy.Sim.Examples.nonvacuous_isForwardSim_preserves : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
    (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.Src (Toy.Sim.Behavior.terminates [5] 5) ∧
    ∀ (t : List Nat), Toy.Sim.Behavior.terminates [5] 5 ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Examples.nonvacuous_pipeline_preserves : Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.Src (Toy.Sim.Behavior.terminates [5] 5) ∧
    ∀ (t : List Nat), Toy.Sim.Behavior.terminates [5] 5 ≠ Toy.Sim.Behavior.goesWrong t
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `forward_simulation_state_behaves` (line 284), `forward_simulation_behavior_improves` (line 316) and `forward_simulation_same_safe_behavior` (line 337).
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 3.7 (Definition 12, Theorem 4): the 'star' forward simulation diagram, with a measure on source states in a well-founded order that must decrease when the target stutters, introduced to rule out the 'infinite stuttering problem'; Theorem 4: under the initial-state, final-state and star-simulation hypotheses, every behaviour of the source that does not go wrong is a behaviour of the target. (Passages checked in the author's version of the article.)
- X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814. Section 2.1 states whole-program behaviour-preservation properties; for source and target languages that are deterministic and execution environments that are deterministic (so each program has exactly one behaviour), 'S safe implies every behaviour of C is a behaviour of S' is equivalent to the easier 'every non-wrong behaviour of S is a behaviour of C'. Section 2.3 composes compiler passes for any transitive whole-program preservation property; it does not concern step-level simulation diagrams or stuttering orders. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors`, `Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `forward_simulation_same_safe_behavior` (`not_wrong beh`), but only for finite-trace behaviours: CompCert's statement also covers `Reacts`, which this model omits.

#### `step-diagrams-compose`

**Kind:** theorem. **Tier:** T0 — Standard: the simulation clause of CompCert's `compose_forward_simulations`, with the same composite relation and order; VeriComp's `forward_simulation_composition` uses the same order shape.

**Lean:** `Toy.Sim.fsimStep_comp`; unfolded restatement: `Toy.Sim.Unfolded.step_diagrams_compose`.

**Plain claim.** If R₁ satisfies the forward step diagram from L₁ to L₂ with index order ord₁ and R₂ satisfies it from L₂ to L₃ with ord₂, then the relational composite compRel R₁ R₂ satisfies the forward step diagram from L₁ to L₃ for the lexicographic order compOrd ord₁ ord₂ (transitive closure of ord₂ on the first component, then ord₁); no well-foundedness is needed.

**Lean statement.**

```lean
-- Toy.Sim.fsimStep_comp
theorem fsimStep_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimStep L₁ L₂ ord₁ R₁) (h₂ : FSimStep L₂ L₃ ord₂ R₂) :
    FSimStep L₁ L₃ (compOrd ord₁ ord₂) (compRel R₁ R₂)
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.step_diagrams_compose
theorem step_diagrams_compose
    (L₁ L₂ L₃ : LTS E Res) (I₁ I₂ : Type)
    (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop)
    (R₁ : I₁ → L₁.State → L₂.State → Prop) (R₂ : I₂ → L₂.State → L₃.State → Prop)
    (h₁ : ∀ i s₁ s₂ e s₁', R₁ i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord₁ i' i)) ∧
        R₁ i' s₁' s₂')
    (h₂ : ∀ i s₂ s₃ e s₂', R₂ i s₂ s₃ → L₂.step s₂ e s₂' →
      ∃ i' s₃', (Plus L₃ s₃ (obs e) s₃' ∨ (Star L₃ s₃ (obs e) s₃' ∧ ord₂ i' i)) ∧
        R₂ i' s₂' s₃') :
    ∀ (i : I₂ × I₁) (s₁ : L₁.State) (s₃ : L₃.State) (e : Option E) (s₁' : L₁.State),
      (∃ s₂, R₁ i.2 s₁ s₂ ∧ R₂ i.1 s₂ s₃) → L₁.step s₁ e s₁' →
      ∃ (i' : I₂ × I₁) (s₃' : L₃.State),
        (Plus L₃ s₃ (obs e) s₃' ∨
          (Star L₃ s₃ (obs e) s₃' ∧
            (Relation.TransGen ord₂ i'.1 i.1 ∨ (i'.1 = i.1 ∧ ord₁ i'.2 i.2)))) ∧
        ∃ s₂', R₁ i'.2 s₁' s₂' ∧ R₂ i'.1 s₂' s₃'
```

**Proof outline.** Given a related pair through a middle state, apply the first pass's step diagram. If the middle run is a `Plus`, the second pass simulates the whole middle run step by step (two auxiliary lemmas, for `Star` and for `Plus` middle runs), recording that either the target made a `Plus` or every middle step stuttered, in which case the second index decreased in `Relation.TransGen ord₂`. If the middle run is empty (the first pass stuttered with zero steps), the second index is kept and the first index decreases, which is the second disjunct of `compOrd`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimStep L₁ L₂ ord₁ R₁` | step diagram of the first pass | tight: `Toy.Sim.Cex.cex_comp_without_first_step_diagram` |
| `FSimStep L₂ L₃ ord₂ R₂` | step diagram of the second pass | tight: `Toy.Sim.Cex.cex_comp_without_second_step_diagram` |

**Depth:** substantive — Induction over the middle-language steps produced by the first pass, tracking whether the last system moved and how the second index changed.

**Non-vacuity witness.** Src ⟶ Mid (stuttering first pass) and Mid ⟶ Tgt (lock-step second pass); and OneStep none 0 ⟶ Chain3 ⟶ Done 0, where one source step becomes two middle steps that each stutter in the last system, so that the transitive closure in compOrd is used. (`Toy.Sim.Examples.nonvacuous_comp`, `Toy.Sim.Examples.nonvacuous_comp_transGen`)

```lean
Toy.Sim.Examples.nonvacuous_comp : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Mid (fun i' i => i' < i)
    Toy.Sim.Ex.SrcMidRel ∧
  Toy.Sim.IsForwardSim Toy.Sim.Ex.Mid Toy.Sim.Ex.Tgt (fun x x_1 => False) Toy.Sim.Ex.MidTgtRel
Toy.Sim.Examples.nonvacuous_comp_transGen : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 0) Toy.Sim.Cex.Chain3
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.chainRel₁ ∧
  Toy.Sim.IsForwardSim Toy.Sim.Cex.Chain3 (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.succOrd Toy.Sim.Cex.chainRel₂ ∧
    Relation.TransGen Toy.Sim.Cex.succOrd 0 2 ∧
      ¬Toy.Sim.Cex.succOrd 0 2 ∧
        Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.Done 0)
          (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.succOrd)
          (Toy.Sim.compRel Toy.Sim.Cex.chainRel₁ Toy.Sim.Cex.chainRel₂)
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `compose_forward_simulations` (line 1003); the composite index order is `lex_ord (clos_trans _ order') order` (line 1011), i.e. lexicographic with the transitive closure of the second-pass order, and the composite relation is relational composition through a middle state.
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)
- N. Lynch and F. Vaandrager, 'Forward and Backward Simulations: Part I: Untimed Systems', Information and Computation 121(2):214-233, 1995, doi:10.1006/inco.1995.1134 (Crossref title 'Forward and Backward Simulations'). Section 3.2: forward simulations between automata, without a stuttering measure; Proposition 3.9 (forward simulations form a preorder, by plain relational composition) and Theorem 3.10 (soundness for finite-trace inclusion). There is no divergence preservation and no composite index order. Terminology differs: both of their simulation notions follow the steps of the implementation automaton, and their 'backward simulation' (Section 3.3) matches from post-state to pre-state. (Passages checked in the authors' version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimStep_comp`, `Toy.Sim.Unfolded.step_diagrams_compose`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors the step-diagram part of CompCert's `compose_forward_simulations`, whose composite order is `lex_ord (clos_trans _ order') order` (quoted under Evidence), i.e. the same shape as `compOrd`.

#### `forward-simulations-compose`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `compose_forward_simulations`; VeriComp's `forward_simulation_composition`; well-foundedness of lexicographic products and transitive closures is textbook.

**Lean:** `Toy.Sim.isForwardSim_comp`, `Toy.Sim.fsimInit_comp`, `Toy.Sim.fsimFinal_comp`, `Toy.Sim.compOrd_wf`.

**Plain claim.** Forward simulations compose vertically: from a forward simulation (ord₁, R₁) from L₁ to L₂ and a forward simulation (ord₂, R₂) from L₂ to L₃, the pair (compOrd ord₁ ord₂, compRel R₁ R₂) is a forward simulation from L₁ to L₃. Clause by clause: the initial-state clauses compose (fsimInit_comp), the final-state clauses compose (fsimFinal_comp), compOrd ord₁ ord₂ is well-founded when ord₁ and ord₂ are (compOrd_wf), and the step clauses compose as in step-diagrams-compose.

**Lean statement.**

```lean
-- Toy.Sim.isForwardSim_comp
theorem isForwardSim_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : IsForwardSim L₁ L₂ ord₁ R₁) (h₂ : IsForwardSim L₂ L₃ ord₂ R₂) :
    IsForwardSim L₁ L₃ (compOrd ord₁ ord₂) (compRel R₁ R₂)

-- Toy.Sim.fsimInit_comp
theorem fsimInit_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimInit L₁ L₂ R₁) (h₂ : FSimInit L₂ L₃ R₂) :
    FSimInit L₁ L₃ (compRel R₁ R₂)

-- Toy.Sim.fsimFinal_comp
theorem fsimFinal_comp {L₁ L₂ L₃ : LTS E Res} {I₁ I₂ : Type}
    {R₁ : I₁ → L₁.State → L₂.State → Prop} {R₂ : I₂ → L₂.State → L₃.State → Prop}
    (h₁ : FSimFinal L₁ L₂ R₁) (h₂ : FSimFinal L₂ L₃ R₂) :
    FSimFinal L₁ L₃ (compRel R₁ R₂)

-- Toy.Sim.compOrd_wf
theorem compOrd_wf {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop}
    (h₁ : WellFounded ord₁) (h₂ : WellFounded ord₂) :
    WellFounded (compOrd ord₁ ord₂)
```

**Proof outline.** `isForwardSim_comp` assembles `compOrd_wf`, `fsimInit_comp`, `fsimFinal_comp` and `fsimStep_comp`. `compOrd_wf` embeds `compOrd` in the lexicographic product of `Relation.TransGen ord₂` (well-founded because `ord₂` is) and `ord₁`; the initial and final clauses compose by chasing the middle state.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `WellFounded ord₁ (first pass; isForwardSim_comp and compOrd_wf)` | well-foundedness of the composite order | tight: `Toy.Sim.Cex.cex_comp_without_first_wf`, `Toy.Sim.Cex.cex_compOrd_wf_needs_both` |
| `WellFounded ord₂ (second pass; isForwardSim_comp and compOrd_wf)` | well-foundedness of the composite order | tight: `Toy.Sim.Cex.cex_comp_without_second_wf`, `Toy.Sim.Cex.cex_compOrd_wf_needs_both` |
| `FSimInit L₁ L₂ R₁ (isForwardSim_comp and fsimInit_comp)` | initial clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_first_init` |
| `FSimInit L₂ L₃ R₂ (isForwardSim_comp and fsimInit_comp)` | initial clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_second_init` |
| `FSimFinal L₁ L₂ R₁ (isForwardSim_comp and fsimFinal_comp)` | final clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_first_final` |
| `FSimFinal L₂ L₃ R₂ (isForwardSim_comp and fsimFinal_comp)` | final clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_second_final` |
| `FSimStep L₁ L₂ ord₁ R₁ (isForwardSim_comp)` | step clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_first_step_diagram` |
| `FSimStep L₂ L₃ ord₂ R₂ (isForwardSim_comp)` | step clause of the composite | tight: `Toy.Sim.Cex.cex_comp_without_second_step_diagram` |

**Depth:** shallow — Assembles the four clauses; the step clause (step-diagrams-compose) is the substantive one, the others are one-line compositions and a subrelation argument for well-foundedness.

**Non-vacuity witness.** Src ⟶ Mid ⟶ Tgt; and OneStep none 0 ⟶ Chain3 ⟶ Done 0 (second pass with a non-transitive, well-founded order). (`Toy.Sim.Examples.nonvacuous_comp`, `Toy.Sim.Examples.nonvacuous_comp_transGen`)

```lean
Toy.Sim.Examples.nonvacuous_comp : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Mid (fun i' i => i' < i)
    Toy.Sim.Ex.SrcMidRel ∧
  Toy.Sim.IsForwardSim Toy.Sim.Ex.Mid Toy.Sim.Ex.Tgt (fun x x_1 => False) Toy.Sim.Ex.MidTgtRel
Toy.Sim.Examples.nonvacuous_comp_transGen : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 0) Toy.Sim.Cex.Chain3
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.chainRel₁ ∧
  Toy.Sim.IsForwardSim Toy.Sim.Cex.Chain3 (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.succOrd Toy.Sim.Cex.chainRel₂ ∧
    Relation.TransGen Toy.Sim.Cex.succOrd 0 2 ∧
      ¬Toy.Sim.Cex.succOrd 0 2 ∧
        Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.Done 0)
          (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.succOrd)
          (Toy.Sim.compRel Toy.Sim.Cex.chainRel₁ Toy.Sim.Cex.chainRel₂)
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `compose_forward_simulations` (line 1003); the composite index order is `lex_ord (clos_trans _ order') order` (line 1011), i.e. lexicographic with the transitive closure of the second-pass order, and the composite relation is relational composition through a middle state.
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)
- N. Lynch and F. Vaandrager, 'Forward and Backward Simulations: Part I: Untimed Systems', Information and Computation 121(2):214-233, 1995, doi:10.1006/inco.1995.1134 (Crossref title 'Forward and Backward Simulations'). Section 3.2: forward simulations between automata, without a stuttering measure; Proposition 3.9 (forward simulations form a preorder, by plain relational composition) and Theorem 3.10 (soundness for finite-trace inclusion). There is no divergence preservation and no composite index order. Terminology differs: both of their simulation notions follow the steps of the implementation automaton, and their 'backward simulation' (Section 3.3) matches from post-state to pre-state. (Passages checked in the authors' version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.isForwardSim_comp`, `Toy.Sim.fsimInit_comp`, `Toy.Sim.fsimFinal_comp`, `Toy.Sim.compOrd_wf`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `compose_forward_simulations` without the `public_symbol` clause. The composite relation and order are exposed here; CompCert's statement hides them inside `forward_simulation`.

#### `flip-forward-to-backward`

**Kind:** theorem. **Tier:** T0 — Standard: Theorem 2 of Ševčík et al. (POPL 2011, Section 4), including the clause 'contains R'; CompCert's `forward_to_backward_simulation` states the version without that clause. Restated with an arbitrary event-matching relation M (in place of 'labels of the same kind' or `match_traces`), with one event per step built into the model (so there is no `single_events` side condition), and with determinacy split into five separately named clauses. The second theorem is the instance M = Eq.

**Lean:** `Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim`, `Toy.Sim.forwardSim_deterministic_target_gives_backwardSim`; unfolded restatement: `Toy.Sim.Unfolded.flip_forward_to_backward`.

**Plain claim.** If (ord, R) is a forward simulation from L₁ to L₂, L₁ is receptive and L₂ is determinate with respect to the same event-matching relation M, then some backward simulation from L₁ to L₂ exists, and its relation contains every pair of states related by R. In the special case M = Eq every L₁ is receptive, so a forward simulation into an L₂ that is deterministic (determinate for Eq) suffices.

**Lean statement.**

```lean
-- Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim
theorem forwardSim_receptive_determinate_gives_backwardSim
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop} (M : E → E → Prop)
    (hsim : IsForwardSim L₁ L₂ ord R)
    (hrec : Receptive M L₁) (hdet : Determinate M L₂) :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord' R' ∧ ∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂

-- Toy.Sim.forwardSim_deterministic_target_gives_backwardSim
theorem forwardSim_deterministic_target_gives_backwardSim
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsForwardSim L₁ L₂ ord R) (hdet : Determinate Eq L₂) :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      IsBackwardSim L₁ L₂ ord' R' ∧ ∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.flip_forward_to_backward
theorem flip_forward_to_backward
    (M : E → E → Prop) (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    -- forward simulation
    (hwf : WellFounded ord)
    (hinit : ∀ s₁, L₁.init s₁ → ∃ i s₂, L₂.init s₂ ∧ R i s₁ s₂)
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ → L₁.final s₁ r → L₂.final s₂ r)
    (hstep : ∀ i s₁ s₂ e s₁', R i s₁ s₂ → L₁.step s₁ e s₁' →
      ∃ i' s₂', (Plus L₂ s₂ (obs e) s₂' ∨ (Star L₂ s₂ (obs e) s₂' ∧ ord i' i)) ∧
        R i' s₁' s₂')
    -- receptive source
    (hrec : ∀ s a s₁ b, L₁.step s (some a) s₁ → M a b → ∃ s₂, L₁.step s (some b) s₂)
    -- determinate target
    (hlabels : ∀ s e₁ s₁ e₂ s₂, L₂.step s e₁ s₁ → L₂.step s e₂ s₂ → LabelMatch M e₁ e₂)
    (hfunctional : ∀ s e s₁ s₂, L₂.step s e s₁ → L₂.step s e s₂ → s₁ = s₂)
    (hinitDet : ∀ s s', L₂.init s → L₂.init s' → s = s')
    (hfinalNoStep : ∀ s r, L₂.final s r → ∀ e s', ¬ L₂.step s e s')
    (hfinalDet : ∀ s r r', L₂.final s r → L₂.final s r' → r = r') :
    ∃ (I' : Type) (ord' : I' → I' → Prop) (R' : I' → L₁.State → L₂.State → Prop),
      -- backward simulation, clause by clause
      WellFounded ord' ∧
      ((∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂) ∧
      (∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R' i s₁' s₂) ∧
      -- (`Safe L₁ s₁` is unfolded: `s₁` cannot get stuck before its next event)
      (∀ i s₁ s₂ r, R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        L₂.final s₂ r → ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r) ∧
      (∀ i s₁ s₂, R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂')) ∧
      (∀ i s₁ s₂ e s₂', R' i s₁ s₂ →
        (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
        L₂.step s₂ e s₂' →
        ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord' i' i)) ∧
          R' i' s₁' s₂') ∧
      -- the backward relation contains the forward relation
      (∀ i s₁ s₂, R i s₁ s₂ → ∃ i', R' i' s₁ s₂)
```

**Proof outline.** The backward simulation is constructed explicitly, as an auxiliary inductive relation over an auxiliary index type with two kinds of indices, `after n` and `before n` (`n : Nat`). An index `after n` relates a source state to every target state that reaches a forward-related state in `n` silent steps; an index `before n` relates a source state that can emit an event `a` to the target states between a forward-related state and the matching emission of `a`, with `n` steps left. The index order is `<` within each kind with every `before` below every `after`, so it is well-founded. From a related pair with a safe source state, well-founded induction on the forward index (an auxiliary lemma) finds a silently reachable source state that is either final (then the target is final with the same result, by `FSimFinal`, determinacy of results and `FinalNoStep`) or takes a step matched by a target `Plus`. A target step is then matched using determinacy: silent target steps are forced by `StepLabelsMatch` and `StepFunctional`; when the target emits an event `b` where the forward simulation predicted a matching event `a`, receptiveness of the source supplies a source step emitting `b`, whose forward-simulated target run must, by determinacy, pass through the target's actual successor. The forward relation is contained in the backward one at index `after 0`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `IsForwardSim L₁ L₂ ord R, clause wf (both theorems)` | rules out infinite stuttering | tight: `Toy.Sim.Cex.cex_flip_without_wf` |
| `IsForwardSim L₁ L₂ ord R, clause init (both theorems)` | initial states | tight: `Toy.Sim.Cex.cex_flip_without_init_clause` |
| `IsForwardSim L₁ L₂ ord R, clause final (both theorems)` | final states and results | tight: `Toy.Sim.Cex.cex_flip_without_final_clause` |
| `IsForwardSim L₁ L₂ ord R, clause step (both theorems)` | step diagram | tight: `Toy.Sim.Cex.cex_flip_without_step_diagram` |
| `Receptive M L₁ (first theorem; automatic for M = Eq)` | the source accepts every alternative environment response the target may receive | tight: `Toy.Sim.Cex.cex_flip_nonreceptive_source` |
| `Determinate M L₂, clause labels (StepLabelsMatch; both theorems, the second at M = Eq)` | two steps from one target state carry matching labels | tight: `Toy.Sim.Cex.cex_flip_target_labels_mismatch`, `Toy.Sim.Cex.cex_flip_target_event_labels_mismatch` |
| `Determinate M L₂, clause functional (StepFunctional)` | the label determines the target successor | tight: `Toy.Sim.Cex.cex_flip_target_not_functional` |
| `Determinate M L₂, clause init (InitDeterminate)` | at most one initial target state | tight: `Toy.Sim.Cex.cex_flip_target_two_initial_states` |
| `Determinate M L₂, clause finalNoStep (FinalNoStep)` | final target states do not step | tight: `Toy.Sim.Cex.cex_flip_target_final_state_steps` |
| `Determinate M L₂, clause finalDet (FinalDeterminate)` | a final target state has one result | tight: `Toy.Sim.Cex.cex_flip_target_two_results` |

**Depth:** substantive — Needs a new relation that also covers target states in the middle of the steps simulating one source step, a determinacy argument for silent prefixes, and a two-level index order.

**Non-vacuity witness.** Src and Tgt with SrcTgtRel, where any two inputs match (AnyInput): Src accepts every input and Tgt is determinate; in the same instance the conclusion holds with the backward relation SrcTgtBackRel, which contains SrcTgtRel. For M = Eq: Spin simulated by the deterministic one-state system Loop. (`Toy.Sim.Examples.nonvacuous_flip`, `Toy.Sim.Examples.nonvacuous_flip_with_conclusion`, `Toy.Sim.Examples.nonvacuous_deterministic_target`)

```lean
Toy.Sim.Examples.nonvacuous_flip : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧ Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt
Toy.Sim.Examples.nonvacuous_flip_with_conclusion : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
    (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
    Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt ∧
      Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtBackRel ∧
        ∀ (i : Nat) (s₁ : Toy.Sim.Ex.SrcSt) (s₂ : Toy.Sim.Ex.TgtSt),
          Toy.Sim.Ex.SrcTgtRel i s₁ s₂ → ∃ i', Toy.Sim.Ex.SrcTgtBackRel i' s₁ s₂
Toy.Sim.Examples.nonvacuous_deterministic_target : Toy.Sim.IsForwardSim Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop
    (fun i' i => i' < i) Toy.Sim.Examples.spinRel ∧
  Toy.Sim.FSimChain Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop ∧ Toy.Sim.Determinate Eq Toy.Sim.Ex.Loop
```

**Prior art.**

- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, 'Relaxed-memory concurrency and verified compilation', POPL 2011, pp. 43-54, doi:10.1145/1926385.1926393. Section 4 defines labels 'of the same kind' (te ≍ te': they differ only in input values), receptive thread LTSs (Definition 2), determinate thread LTSs (Definition 3: co-enabled labels are of the same kind, and equal labels lead to equal states), threadwise forward and backward simulations with a well-founded order for stuttering (Definitions 4-5), and Theorem 2: 'If R is a threadwise forward simulation from S to T, S is receptive, and T is determinate, then there is a threadwise backward simulation that contains R.' This is the step-level flip theorem, including the clause 'contains R'; their simulations also treat explicit failure labels and are lifted to a concurrent TSO machine, which this package does not model. (Section 4 read in the authors' version of the paper.)
- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, 'CompCertTSO: A Verified Compiler for Relaxed-Memory Concurrency', Journal of the ACM 60(3), article 22, pp. 22:1-22:50, 2013, doi:10.1145/2487241.2487248. Journal version of the POPL 2011 paper; bibliographic record verified, the body (including the number of the corresponding theorem) was not examined for this package.
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: section FORWARD_TO_BACKWARD (line 1608), lemma `forward_to_backward_simulation` (line 1863): `forward_simulation L1 L2 -> receptive L1 -> determinate L2 -> backward_simulation L1 L2`. CompCert's `forward_simulation` and `backward_simulation` hide the simulation relations, so this lemma does not state that the backward relation contains the forward one (the statement here does).
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: records `receptive` (line 1050) and `determinate` (line 1058), stated with the trace relation `match_traces` and a separate `single_events` field (`sr_traces`, `sd_traces`); CompCert's `sd_determ` bundles the label-matching and functionality clauses that are separate here.
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 2.1 (Definitions 2-5, Figure 2) relates whole-program behaviour inclusions — 'backward simulation' (every behaviour of the compiled program C is a behaviour of the source S), 'forward simulation' (every behaviour of S is a behaviour of C), and their versions for safe programs — and shows that the forward inclusion implies the backward one when C is deterministic, i.e. admits a single behaviour (target language without internal nondeterminism and a deterministic execution environment). These are behaviour-set statements, not step-level simulation diagrams; the article has no step-level receptiveness or determinacy conditions and no step-level flip theorem. (Passages checked in the author's version of the article.)
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim`, `Toy.Sim.forwardSim_deterministic_target_gives_backwardSim`, `Toy.Sim.Unfolded.flip_forward_to_backward`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `forward_to_backward_simulation` (receptive source, determinate target) and Theorem 2 of Ševčík et al. (POPL 2011), restricted to single-event steps; CompCert's `receptive`/`determinate` also require `single_events`, which is built into this model, and CompCert's lemma does not state that the backward relation contains the forward one. Multi-event steps (CompCert's `atomic` construction) are not modelled.

#### `backward-sim-gives-refinement`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `backward_simulation_behavior_improves`, restricted to finite-trace behaviours.

**Lean:** `Toy.Sim.backwardSim_gives_refinedBy`; unfolded restatement: `Toy.Sim.Unfolded.backward_sim_gives_refinement`.

**Plain claim.** If (ord, R) is a backward simulation from L₁ to L₂ — a well-founded index order; if L₁ has an initial state then so does L₂; if L₁ has an initial state then every initial state of L₂ is related to some initial state of L₁; and final-state, progress and step clauses that are required only when the related source state is Safe (cannot get stuck before its next observable event) — then L₂ refines L₁: every behaviour of L₂ is a behaviour of L₁ or extends the trace of a going-wrong behaviour of L₁.

**Lean statement.**

```lean
-- Toy.Sim.backwardSim_gives_refinedBy
theorem backwardSim_gives_refinedBy
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) : RefinedBy L₁ L₂
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.backward_sim_gives_refinement
theorem backward_sim_gives_refinement
    (L₁ L₂ : LTS E Res) (I : Type) (ord : I → I → Prop)
    (R : I → L₁.State → L₂.State → Prop)
    (hwf : WellFounded ord)
    (hinitExists : (∃ s₁, L₁.init s₁) → ∃ s₂, L₂.init s₂)
    (hinitMatch : ∀ s₁ s₂, L₁.init s₁ → L₂.init s₂ → ∃ i s₁', L₁.init s₁' ∧ R i s₁' s₂)
    -- (`Safe L₁ s₁` is unfolded: `s₁` cannot get stuck before its next event)
    (hfinal : ∀ i s₁ s₂ r, R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      L₂.final s₂ r → ∃ s₁', Star L₁ s₁ [] s₁' ∧ L₁.final s₁' r)
    (hprogress : ∀ i s₁ s₂, R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      (∃ r, L₂.final s₂ r) ∨ (∃ e s₂', L₂.step s₂ e s₂'))
    (hstep : ∀ i s₁ s₂ e s₂', R i s₁ s₂ →
      (∀ s₁', Star L₁ s₁ [] s₁' → (∃ r, L₁.final s₁' r) ∨ (∃ e s₁'', L₁.step s₁' e s₁'')) →
      L₂.step s₂ e s₂' →
      ∃ i' s₁', (Plus L₁ s₁ (obs e) s₁' ∨ (Star L₁ s₁ (obs e) s₁' ∧ ord i' i)) ∧
        R i' s₁' s₂') :
    ∀ b₂, HasBehavior L₂ b₂ →
      ∃ b₁, HasBehavior L₁ b₁ ∧ (b₁ = b₂ ∨ ∃ t, b₁ = .goesWrong t ∧ t <+: b₂.trace)
```

**Proof outline.** If the source has no initial state, its behaviour `goesWrong []` permits every target behaviour. Otherwise, by induction on the target run (an auxiliary lemma), each target run from an initial state is matched by a source run with the same trace ending in a related state, unless the source meets an unsafe state on the way, in which case it goes wrong after a prefix of the trace. The terminating case then uses `BSimFinal`, the going-wrong case `BSimProgress`, the empty-program case `BSimInitExists`, and the diverging case a well-founded-induction-plus-choice argument dual to the forward divergence proof: if no silently reachable source state is stuck, the source diverges silently.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `IsBackwardSim.wf : WellFounded ord` | rules out infinite stuttering of the source | tight: `Toy.Sim.Cex.cex_bsim_without_wf` |
| `IsBackwardSim.initExists : BSimInitExists L₁ L₂` | if the source can start, so can the target | tight: `Toy.Sim.Cex.cex_bsim_without_initExists` |
| `IsBackwardSim.initMatch : BSimInitMatch L₁ L₂ R` | initial target states are related to initial source states (when the source has one) | tight: `Toy.Sim.Cex.cex_bsim_without_initMatch` |
| `IsBackwardSim.final : BSimFinal L₁ L₂ R` | a final target state is matched by a silently reachable final source state with the same result | tight: `Toy.Sim.Cex.cex_bsim_without_final_clause` |
| `IsBackwardSim.progress : BSimProgress L₁ L₂ R` | the target is not stuck while the source is Safe | tight: `Toy.Sim.Cex.cex_bsim_without_progress` |
| `IsBackwardSim.step : BSimStep L₁ L₂ ord R` | target steps are matched by source steps with the same trace | tight: `Toy.Sim.Cex.cex_bsim_without_step_diagram` |

**Depth:** substantive — Classical case analysis on whether the source stays Safe along the target's trace; well-founded induction and a choice principle for the diverging case.

**Non-vacuity witness.** Src and Tgt with the backward relation SrcTgtBackRel, in which the source stutters on the target's last silent step. (`Toy.Sim.Examples.nonvacuous_backwardSim`)

```lean
Toy.Sim.Examples.nonvacuous_backwardSim : Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtBackRel ∧
  Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Src
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: definition `safe` (line 1274: every state reachable by silent steps is final or can step) and record `bsim_properties` (line 1289) with the same clauses (well-founded index order, initial states exist, initial states match, final states, progress, step diagram; the last three conditional on `safe`), plus a clause about public symbols that has no counterpart in this model.
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `backward_simulation_behavior_improves` (line 493) and `backward_simulation_same_safe_behavior` (line 519).
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `behavior_improves` (line 81), `behavior_improves_refl` (line 84), `behavior_improves_trans` (line 90), `behavior_improves_bot` (line 102); `program_behaves` (line 141) includes the constructor `program_goes_initially_wrong` (line 145) for programs without initial state. CompCert's `program_behavior` (line 41) also has a constructor for infinite event traces, which this package omits.
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.backwardSim_gives_refinedBy`, `Toy.Sim.Unfolded.backward_sim_gives_refinement`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `backward_simulation_behavior_improves` for finite-trace behaviours only. In this model a backward simulation is strictly stronger than `RefinedBy` on runs with infinitely many events (`Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs`), because such runs are not behaviours here.

#### `refinement-is-inclusion-when-source-never-goes-wrong`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `backward_simulation_same_safe_behavior`; property (2) of Leroy (CACM 2009, Section 2.1); Definition 3 of Leroy (JAR 2009, Section 2.1).

**Lean:** `Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset`, `Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset`.

**Plain claim.** If L₂ refines L₁ and L₁ has no going-wrong behaviour (NeverGoesWrong L₁, whole-program absence of going wrong), then every behaviour of L₂ is a behaviour of L₁; in particular this holds when a backward simulation from L₁ to L₂ exists.

**Lean statement.**

```lean
-- Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset
theorem refinedBy_neverGoesWrong_behaviors_subset {L₁ L₂ : LTS E Res}
    (href : RefinedBy L₁ L₂) (hsafe : NeverGoesWrong L₁)
    {b : Behavior E Res} (hb : HasBehavior L₂ b) : HasBehavior L₁ b

-- Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset
theorem backwardSim_neverGoesWrong_behaviors_subset
    {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop}
    (hsim : IsBackwardSim L₁ L₂ ord R) (hsafe : NeverGoesWrong L₁)
    {b : Behavior E Res} (hb : HasBehavior L₂ b) : HasBehavior L₁ b
```

**Proof outline.** Unfold `Improves`: the second alternative would give the source a going-wrong behaviour, excluded by `NeverGoesWrong`. The backward-simulation form composes this with `backwardSim_gives_refinedBy`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `RefinedBy L₁ L₂ (first theorem)` | relates target behaviours to source behaviours | tight: `Toy.Sim.Cex.cex_inclusion_without_refinement` |
| `IsBackwardSim L₁ L₂ ord R (second theorem)` | gives RefinedBy L₁ L₂. Ledgered here as one structure: the counterexample has no backward simulation at all. Its six clauses are ledgered one by one on `backward-sim-gives-refinement`, whose per-clause counterexamples (Toy.Sim.Cex.cex_bsim_without_wf, Toy.Sim.Cex.cex_bsim_without_initExists, Toy.Sim.Cex.cex_bsim_without_initMatch, Toy.Sim.Cex.cex_bsim_without_final_clause, Toy.Sim.Cex.cex_bsim_without_progress, Toy.Sim.Cex.cex_bsim_without_step_diagram) all take L₁ = Done 0, which never goes wrong (Toy.Sim.Ex.done_neverGoesWrong), and conclude ¬ RefinedBy (Done 0) L₂. Because Improves is reflexive (Toy.Sim.Improves.refl), each such L₂ has a behaviour that is not a behaviour of Done 0, so each counterexample also shows that its clause cannot be dropped from the second theorem; this last step is a short argument from the quoted statements, not a separately stated Lean theorem. | tight: `Toy.Sim.Cex.cex_inclusion_without_refinement` |
| `NeverGoesWrong L₁ (both theorems)` | excludes the going-wrong alternative of Improves | tight: `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong` |
| `HasBehavior L₂ b (both theorems)` | the target behaviour being transferred | tight: `Toy.Sim.Cex.cex_inclusion_without_target_behavior` |

**Depth:** shallow — Unfolding Improves: the going-wrong alternative is excluded by hypothesis.

**Non-vacuity witness.** Src and Tgt: Tgt refines Src, a backward simulation SrcTgtBackRel exists, Src never goes wrong, and Tgt has the behaviour 'read 5, return 5'. (`Toy.Sim.Examples.nonvacuous_refinement_inclusion`)

```lean
Toy.Sim.Examples.nonvacuous_refinement_inclusion : Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtBackRel ∧
    Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Src ∧ Toy.Sim.HasBehavior Toy.Sim.Ex.Tgt (Toy.Sim.Behavior.terminates [5] 5)
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `backward_simulation_behavior_improves` (line 493) and `backward_simulation_same_safe_behavior` (line 519).
- X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814. Section 2.1 states whole-program behaviour-preservation properties; for source and target languages that are deterministic and execution environments that are deterministic (so each program has exactly one behaviour), 'S safe implies every behaviour of C is a behaviour of S' is equivalent to the easier 'every non-wrong behaviour of S is a behaviour of C'. Section 2.3 composes compiler passes for any transitive whole-program preservation property; it does not concern step-level simulation diagrams or stuttering orders. (Passages checked in the author's version of the article.)
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 2.1 (Definitions 2-5, Figure 2) relates whole-program behaviour inclusions — 'backward simulation' (every behaviour of the compiled program C is a behaviour of the source S), 'forward simulation' (every behaviour of S is a behaviour of C), and their versions for safe programs — and shows that the forward inclusion implies the backward one when C is deterministic, i.e. admits a single behaviour (target language without internal nondeterminism and a deterministic execution environment). These are behaviour-set statements, not step-level simulation diagrams; the article has no step-level receptiveness or determinacy conditions and no step-level flip theorem. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset`, `Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors CompCert's `backward_simulation_same_safe_behavior`, for finite-trace behaviours only.

#### `pipeline-collapses-to-one-forward-simulation`

**Kind:** theorem. **Tier:** T0 — Standard: iterated use of CompCert's `compose_forward_simulations` in `cstrategy_semantic_preservation`.

**Lean:** `Toy.Sim.fsimChain_collapse`, `Toy.Sim.fsimChain_of_isForwardSim`.

**Plain claim.** A finite chain of forward simulations from L to L' (possibly empty) yields a single forward simulation from L to L', for some index type, order and relation (fsimChain_collapse); and a single forward simulation is a one-link chain (fsimChain_of_isForwardSim).

**Lean statement.**

```lean
-- Toy.Sim.fsimChain_collapse
theorem fsimChain_collapse {L L' : LTS E Res} (h : FSimChain L L') :
    ∃ (I : Type) (ord : I → I → Prop) (R : I → L.State → L'.State → Prop),
      IsForwardSim L L' ord R

-- Toy.Sim.fsimChain_of_isForwardSim
theorem fsimChain_of_isForwardSim {L₁ L₂ : LTS E Res} {I : Type} {ord : I → I → Prop}
    {R : I → L₁.State → L₂.State → Prop} (h : IsForwardSim L₁ L₂ ord R) :
    FSimChain L₁ L₂
```

**Proof outline.** Induction on `FSimChain`, using the identity simulation `Toy.Sim.isForwardSim_id` for the empty chain and `isForwardSim_comp` for each link. `fsimChain_of_isForwardSim` is the one-link chain.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimChain L L' (fsimChain_collapse)` | the passes being collapsed | tight: `Toy.Sim.Examples.isForwardSim_neg` |
| `IsForwardSim L₁ L₂ ord R (fsimChain_of_isForwardSim)` | the single pass. Ledgered here as one structure: the counterexample has no forward simulation at all. Its four clauses are ledgered one by one on `forward-sim-preserves-non-wrong-behaviours` (single-pass theorem), whose per-clause counterexamples (Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved, Toy.Sim.Cex.cex_fsim_without_init_clause, Toy.Sim.Cex.cex_fsim_without_final_clause, Toy.Sim.Cex.cex_fsim_without_step_diagram) each exhibit a behaviour of L₁ that does not go wrong and is not a behaviour of L₂. A chain FSimChain L₁ L₂ would preserve that behaviour (Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors), so each counterexample also shows that its clause cannot be dropped here; this last step is a short argument from the quoted statements, not a separately stated Lean theorem. | tight: `Toy.Sim.Examples.fsimChain_neg` |

**Depth:** shallow — Induction on the chain using the identity simulation and vertical composition.

**Non-vacuity witness.** The two-pass chain Src ⟶ Mid ⟶ Tgt; the forward simulation SrcTgtRel from Src to Tgt. (`Toy.Sim.Examples.fsimChain_pos`, `Toy.Sim.Examples.isForwardSim_pos`)

```lean
Toy.Sim.Examples.fsimChain_pos : Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Src
Toy.Sim.Examples.isForwardSim_pos : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Src (fun x x_1 => False) fun x s s' => s = s'
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `compose_forward_simulations` (line 1003); the composite index order is `lex_ord (clos_trans _ order') order` (line 1011), i.e. lexicographic with the transitive closure of the second-pass order, and the composite relation is relational composition through a middle state.
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file driver/Compiler.v: theorem `cstrategy_semantic_preservation` (line 353) composes the per-pass forward simulations with `compose_forward_simulations` into a forward simulation from `Cstrategy.semantics p` to `Asm.semantics tp`, and flips it once (line 413) — not directly, but after `factor_forward_simulation` (line 414) into a forward simulation from `atomic (Cstrategy.semantics p)`, whose receptiveness comes from `atomic_receptive` and `Cstrategy.semantics_strongly_receptive` (line 415) because Cstrategy steps may carry several events; determinacy of the last language is `Asm.semantics_determinate` (line 416). CompCert's end-to-end theorem for C, `c_semantic_preservation` (line 419), then prepends the backward simulation `Cstrategy.strategy_simulation` from the nondeterministic `Csem` using `compose_backward_simulation` (line 425); `transf_c_program_correct` (line 446) restates it.

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimChain_collapse`, `Toy.Sim.fsimChain_of_isForwardSim`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors the repeated use of `compose_forward_simulations` in CompCert's `driver/Compiler.v` to collapse the forward passes of the pipeline.

#### `pipeline-end-to-end-refinement`

**Kind:** theorem. **Tier:** T0 — Standard structure: CompCert's `cstrategy_semantic_preservation` (compose the forward simulations, flip once) followed by `backward_simulation_behavior_improves`; CompCert additionally needs the `atomic` construction because its first language has multi-event steps.

**Lean:** `Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy`, `Toy.Sim.fsimChain_deterministic_last_gives_refinedBy`; unfolded restatement: `Toy.Sim.Unfolded.pipeline_end_to_end_refinement`.

**Plain claim.** If every pass of a pipeline from L to L' has a forward simulation (FSimChain L L'), the first language L is receptive and the last language L' is determinate for the same event-matching relation M, then L' refines L; nothing is assumed about the intermediate languages. In the special case M = Eq no receptiveness hypothesis is needed: a chain into a deterministic last language suffices.

**Lean statement.**

```lean
-- Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy
theorem fsimChain_receptive_first_determinate_last_gives_refinedBy
    {L L' : LTS E Res} (M : E → E → Prop)
    (hchain : FSimChain L L') (hrec : Receptive M L) (hdet : Determinate M L') :
    RefinedBy L L'

-- Toy.Sim.fsimChain_deterministic_last_gives_refinedBy
theorem fsimChain_deterministic_last_gives_refinedBy
    {L L' : LTS E Res} (hchain : FSimChain L L') (hdet : Determinate Eq L') :
    RefinedBy L L'
```

Unfolded (every named clause replaced by its definition):

```lean
-- Toy.Sim.Unfolded.pipeline_end_to_end_refinement
theorem pipeline_end_to_end_refinement
    (M : E → E → Prop) (L L' : LTS E Res)
    (hchain : FSimChain L L')
    -- the first language is receptive
    (hrec : ∀ s a s₁ b, L.step s (some a) s₁ → M a b → ∃ s₂, L.step s (some b) s₂)
    -- the last language is determinate
    (hlabels : ∀ s e₁ s₁ e₂ s₂, L'.step s e₁ s₁ → L'.step s e₂ s₂ → LabelMatch M e₁ e₂)
    (hfunctional : ∀ s e s₁ s₂, L'.step s e s₁ → L'.step s e s₂ → s₁ = s₂)
    (hinitDet : ∀ s s', L'.init s → L'.init s' → s = s')
    (hfinalNoStep : ∀ s r, L'.final s r → ∀ e s', ¬ L'.step s e s')
    (hfinalDet : ∀ s r r', L'.final s r → L'.final s r' → r = r') :
    ∀ b', HasBehavior L' b' →
      ∃ b, HasBehavior L b ∧ (b = b' ∨ ∃ t, b = .goesWrong t ∧ t <+: b'.trace)
```

**Proof outline.** Collapse the chain to one forward simulation (`fsimChain_collapse`), flip it once (`forwardSim_receptive_determinate_gives_backwardSim`), and apply `backwardSim_gives_refinedBy`. The `M = Eq` form uses `Toy.Sim.receptive_eq`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimChain L L' (both theorems)` | every pass has a forward simulation | tight: `Toy.Sim.Cex.cex_pipeline_without_chain` |
| `Receptive M L (first theorem; automatic for M = Eq)` | the first language accepts every alternative environment response | tight: `Toy.Sim.Cex.cex_pipeline_nonreceptive_first` |
| `Determinate M L', clause labels (both theorems, the second at M = Eq)` | two steps from one state of the last language carry matching labels | tight: `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch` |
| `Determinate M L', clause functional` | the label determines the successor in the last language | tight: `Toy.Sim.Cex.cex_pipeline_last_not_functional` |
| `Determinate M L', clause init` | at most one initial state of the last language | tight: `Toy.Sim.Cex.cex_pipeline_last_two_initial_states` |
| `Determinate M L', clause finalNoStep` | final states of the last language do not step | tight: `Toy.Sim.Cex.cex_pipeline_last_final_state_steps` |
| `Determinate M L', clause finalDet` | a final state of the last language has one result | tight: `Toy.Sim.Cex.cex_pipeline_last_two_results` |

**Depth:** shallow — Shallow given vertical composition, the flip lemma and 'backward simulation gives refinement', which are the substantive ingredients.

**Non-vacuity witness.** The pipeline Src ⟶ Mid ⟶ Tgt, whose intermediate language Mid is not determinate; for M = Eq, the one-pass chain from Spin to the deterministic Loop. (`Toy.Sim.Examples.nonvacuous_pipeline`, `Toy.Sim.Examples.nonvacuous_deterministic_target`)

```lean
Toy.Sim.Examples.nonvacuous_pipeline : Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
    Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt ∧
      Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Src ∧
        Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Mid (fun i' i => i' < i) Toy.Sim.Ex.SrcMidRel ∧
          Toy.Sim.IsForwardSim Toy.Sim.Ex.Mid Toy.Sim.Ex.Tgt (fun x x_1 => False) Toy.Sim.Ex.MidTgtRel ∧
            ¬Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Mid
Toy.Sim.Examples.nonvacuous_deterministic_target : Toy.Sim.IsForwardSim Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop
    (fun i' i => i' < i) Toy.Sim.Examples.spinRel ∧
  Toy.Sim.FSimChain Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop ∧ Toy.Sim.Determinate Eq Toy.Sim.Ex.Loop
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file driver/Compiler.v: theorem `cstrategy_semantic_preservation` (line 353) composes the per-pass forward simulations with `compose_forward_simulations` into a forward simulation from `Cstrategy.semantics p` to `Asm.semantics tp`, and flips it once (line 413) — not directly, but after `factor_forward_simulation` (line 414) into a forward simulation from `atomic (Cstrategy.semantics p)`, whose receptiveness comes from `atomic_receptive` and `Cstrategy.semantics_strongly_receptive` (line 415) because Cstrategy steps may carry several events; determinacy of the last language is `Asm.semantics_determinate` (line 416). CompCert's end-to-end theorem for C, `c_semantic_preservation` (line 419), then prepends the backward simulation `Cstrategy.strategy_simulation` from the nondeterministic `Csem` using `compose_backward_simulation` (line 425); `transf_c_program_correct` (line 446) restates it.
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: section FORWARD_TO_BACKWARD (line 1608), lemma `forward_to_backward_simulation` (line 1863): `forward_simulation L1 L2 -> receptive L1 -> determinate L2 -> backward_simulation L1 L2`. CompCert's `forward_simulation` and `backward_simulation` hide the simulation relations, so this lemma does not state that the backward relation contains the forward one (the statement here does).
- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, 'Relaxed-memory concurrency and verified compilation', POPL 2011, pp. 43-54, doi:10.1145/1926385.1926393. Section 4 defines labels 'of the same kind' (te ≍ te': they differ only in input values), receptive thread LTSs (Definition 2), determinate thread LTSs (Definition 3: co-enabled labels are of the same kind, and equal labels lead to equal states), threadwise forward and backward simulations with a well-founded order for stuttering (Definitions 4-5), and Theorem 2: 'If R is a threadwise forward simulation from S to T, S is receptive, and T is determinate, then there is a threadwise backward simulation that contains R.' This is the step-level flip theorem, including the clause 'contains R'; their simulations also treat explicit failure labels and are lifted to a concurrent TSO machine, which this package does not model. (Section 4 read in the authors' version of the paper.)
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `backward_simulation_behavior_improves` (line 493) and `backward_simulation_same_safe_behavior` (line 519).
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)
- X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814. Section 2.1 states whole-program behaviour-preservation properties; for source and target languages that are deterministic and execution environments that are deterministic (so each program has exactly one behaviour), 'S safe implies every behaviour of C is a behaviour of S' is equivalent to the easier 'every non-wrong behaviour of S is a behaviour of C'. Section 2.3 composes compiler passes for any transitive whole-program preservation property; it does not concern step-level simulation diagrams or stuttering orders. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy`, `Toy.Sim.fsimChain_deterministic_last_gives_refinedBy`, `Toy.Sim.Unfolded.pipeline_end_to_end_refinement`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — CompCert's `cstrategy_semantic_preservation` (`driver/Compiler.v`, quoted under Evidence) is organised the same way: the forward simulations of all passes are composed and flipped once, with the first language receptive (through `atomic` and `Cstrategy.semantics_strongly_receptive`) and the last language (`Asm.semantics`) determinate. CompCert additionally needs the `atomic` construction because its first language has multi-event steps, and its `c_semantic_preservation` prepends a backward simulation for the nondeterministic C semantics; neither is modelled here.

#### `pipeline-behaviour-equality-when-first-never-goes-wrong`

**Kind:** theorem. **Tier:** T0 — Standard: combination of CompCert's `forward_simulation_same_safe_behavior` and `backward_simulation_same_safe_behavior`.

**Lean:** `Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff`.

**Plain claim.** If every pass of a pipeline from L to L' has a forward simulation (FSimChain L L'), the first language L is receptive and the last language L' is determinate for the same event-matching relation M, and L has no going-wrong behaviour (NeverGoesWrong L), then L and L' have exactly the same behaviours.

**Lean statement.**

```lean
-- Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff
theorem fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff
    {L L' : LTS E Res} (M : E → E → Prop)
    (hchain : FSimChain L L') (hrec : Receptive M L) (hdet : Determinate M L')
    (hsafe : NeverGoesWrong L) (b : Behavior E Res) :
    HasBehavior L' b ↔ HasBehavior L b
```

**Proof outline.** The inclusion `L' ⊆ L` is end-to-end refinement plus `refinedBy_neverGoesWrong_behaviors_subset`; the inclusion `L ⊆ L'` is `fsimChain_preserves_non_goesWrong_behaviors`, applicable because `NeverGoesWrong L` excludes going-wrong behaviours of `L`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `FSimChain L L'` | every pass has a forward simulation | tight: `Toy.Sim.Cex.cex_pipeline_without_chain` |
| `Receptive M L` | the first language accepts every alternative environment response | tight: `Toy.Sim.Cex.cex_pipeline_nonreceptive_first` |
| `Determinate M L', clause labels` | two steps from one state of the last language carry matching labels | tight: `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch` |
| `Determinate M L', clause functional` | the label determines the successor in the last language | tight: `Toy.Sim.Cex.cex_pipeline_last_not_functional` |
| `Determinate M L', clause init` | at most one initial state of the last language | tight: `Toy.Sim.Cex.cex_pipeline_last_two_initial_states` |
| `Determinate M L', clause finalNoStep` | final states of the last language do not step | tight: `Toy.Sim.Cex.cex_pipeline_last_final_state_steps` |
| `Determinate M L', clause finalDet` | a final state of the last language has one result | tight: `Toy.Sim.Cex.cex_pipeline_last_two_results` |
| `NeverGoesWrong L` | excludes the going-wrong alternative of refinement | tight: `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong` |

**Depth:** shallow — The two inclusions are the end-to-end refinement theorem (with NeverGoesWrong) and behaviour preservation along the chain.

**Non-vacuity witness.** The pipeline Src ⟶ Mid ⟶ Tgt; Src never goes wrong; Src and Tgt have the same behaviours (proved directly). (`Toy.Sim.Examples.nonvacuous_pipeline_behaviors_iff`)

```lean
Toy.Sim.Examples.nonvacuous_pipeline_behaviors_iff : Toy.Sim.FSimChain Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
    Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt ∧
      Toy.Sim.NeverGoesWrong Toy.Sim.Ex.Src ∧
        ¬Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Mid ∧
          ∀ (b : Toy.Sim.Behavior Nat Nat), Toy.Sim.HasBehavior Toy.Sim.Ex.Tgt b ↔ Toy.Sim.HasBehavior Toy.Sim.Ex.Src b
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `forward_simulation_state_behaves` (line 284), `forward_simulation_behavior_improves` (line 316) and `forward_simulation_same_safe_behavior` (line 337).
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `backward_simulation_behavior_improves` (line 493) and `backward_simulation_same_safe_behavior` (line 519).
- X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814. Section 2.1 states whole-program behaviour-preservation properties; for source and target languages that are deterministic and execution environments that are deterministic (so each program has exactly one behaviour), 'S safe implies every behaviour of C is a behaviour of S' is equivalent to the easier 'every non-wrong behaviour of S is a behaviour of C'. Section 2.3 composes compiler passes for any transitive whole-program preservation property; it does not concern step-level simulation diagrams or stuttering orders. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — This mirrors the combination of CompCert's `forward_simulation_same_safe_behavior` and `backward_simulation_same_safe_behavior`, for finite-trace behaviours only.

#### `refinement-is-a-preorder`

**Kind:** theorem. **Tier:** T0 — Standard: CompCert's `behavior_improves_refl`, `behavior_improves_trans` and `behavior_improves_bot`.

**Lean:** `Toy.Sim.Improves.refl`, `Toy.Sim.Improves.trans`, `Toy.Sim.Improves.antisymm`, `Toy.Sim.improves_goesWrong_nil`, `Toy.Sim.RefinedBy.refl`, `Toy.Sim.RefinedBy.trans`.

**Plain claim.** Improves is a partial order on behaviours (reflexive, transitive and antisymmetric) whose least element is goesWrong [] (it is improved by every behaviour); RefinedBy is reflexive and transitive on labelled transition systems, i.e. a preorder.

**Lean statement.**

```lean
-- Toy.Sim.Improves.refl
theorem Improves.refl (b : Behavior E Res) : Improves b b

-- Toy.Sim.Improves.trans
theorem Improves.trans {b₁ b₂ b₃ : Behavior E Res}
    (h₁₂ : Improves b₁ b₂) (h₂₃ : Improves b₂ b₃) : Improves b₁ b₃

-- Toy.Sim.Improves.antisymm
theorem Improves.antisymm {b₁ b₂ : Behavior E Res}
    (h₁₂ : Improves b₁ b₂) (h₂₁ : Improves b₂ b₁) : b₁ = b₂

-- Toy.Sim.improves_goesWrong_nil
theorem improves_goesWrong_nil (b : Behavior E Res) : Improves (.goesWrong []) b

-- Toy.Sim.RefinedBy.refl
theorem RefinedBy.refl (L : LTS E Res) : RefinedBy L L

-- Toy.Sim.RefinedBy.trans
theorem RefinedBy.trans {L₁ L₂ L₃ : LTS E Res}
    (h₁₂ : RefinedBy L₁ L₂) (h₂₃ : RefinedBy L₂ L₃) : RefinedBy L₁ L₃
```

**Proof outline.** Direct unfolding of `Improves` and `RefinedBy`; antisymmetry of `Improves` compares trace lengths of mutual prefixes.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `Improves b₁ b₂ (Improves.trans)` | first link of the chain | tight: `Toy.Sim.Cex.cex_improves_trans_needs_both` |
| `Improves b₂ b₃ (Improves.trans)` | second link of the chain | tight: `Toy.Sim.Cex.cex_improves_trans_needs_both` |
| `Improves b₁ b₂ (Improves.antisymm)` | one direction | tight: `Toy.Sim.Cex.cex_improves_antisymm_needs_both` |
| `Improves b₂ b₁ (Improves.antisymm)` | the other direction | tight: `Toy.Sim.Cex.cex_improves_antisymm_needs_both` |
| `RefinedBy L₁ L₂ (RefinedBy.trans)` | first refinement | tight: `Toy.Sim.Cex.cex_refinedBy_trans_needs_both` |
| `RefinedBy L₂ L₃ (RefinedBy.trans)` | second refinement | tight: `Toy.Sim.Cex.cex_refinedBy_trans_needs_both` |

**Depth:** shallow — Direct from the definitions and transitivity of the list prefix order.

**Non-vacuity witness.** A composable Improves chain goesWrong [] ⟶ goesWrong [1] ⟶ terminates [1, 2] 0, a mutual Improves pair (equal behaviours), and a composable refinement chain StuckNow ⟶ Src ⟶ Tgt. (`Toy.Sim.Examples.nonvacuous_preorder`)

```lean
Toy.Sim.Examples.nonvacuous_preorder : (Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [])
      (Toy.Sim.Behavior.goesWrong [1]) ∧
    Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [1]) (Toy.Sim.Behavior.terminates [1, 2] 0)) ∧
  (Toy.Sim.Improves (Toy.Sim.Behavior.diverges [4]) (Toy.Sim.Behavior.diverges [4]) ∧
      Toy.Sim.Improves (Toy.Sim.Behavior.diverges [4]) (Toy.Sim.Behavior.diverges [4])) ∧
    Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow Toy.Sim.Ex.Src ∧ Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
```

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `behavior_improves` (line 81), `behavior_improves_refl` (line 84), `behavior_improves_trans` (line 90), `behavior_improves_bot` (line 102); `program_behaves` (line 141) includes the constructor `program_goes_initially_wrong` (line 145) for programs without initial state. CompCert's `program_behavior` (line 41) also has a constructor for infinite event traces, which this package omits.

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Improves.refl`, `Toy.Sim.Improves.trans`, `Toy.Sim.Improves.antisymm`, `Toy.Sim.improves_goesWrong_nil`, `Toy.Sim.RefinedBy.refl`, `Toy.Sim.RefinedBy.trans`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — `Improves` is CompCert's `behavior_improves` restricted to finite-trace behaviours; `Improves.refl`, `Improves.trans`, `improves_goesWrong_nil` mirror `behavior_improves_refl`, `behavior_improves_trans`, `behavior_improves_bot`.

#### `cex-no-measure-infinite-stuttering`

**Kind:** counterexample. **Tier:** T0 — The infinite stuttering problem is described in Leroy (JAR 2009, Section 3.7), which introduces the well-founded measure to rule it out.

**Lean:** `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved`.

**Plain claim.** There is an instance in which the forward initial-state clause, final-state clause and step diagram all hold with an index order that is not well-founded, between the source Loop (which diverges silently) and the target Done 0 (which terminates at once): the target matches every source step by doing nothing, and silent divergence is not preserved.

**Lean statement.**

```lean
Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved : ¬WellFounded Toy.Sim.Cex.fullOrd ∧
  Toy.Sim.FSimInit Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relTrue ∧
    Toy.Sim.FSimFinal Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relTrue ∧
      Toy.Sim.FSimStep Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.fullOrd Toy.Sim.Cex.relTrue ∧
        Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.diverges []) ∧
          ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.diverges []) ∧
            Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ∧
              ∀ (t : List Nat), Toy.Sim.Behavior.diverges [] ≠ Toy.Sim.Behavior.goesWrong t
```

**Depth:** shallow — Finite case analysis on one-state systems.

**Positive control** (a nearby setting where the conclusion that fails here does hold): `Toy.Sim.Examples.positive_control_diverges`

```lean
Toy.Sim.Examples.positive_control_diverges : Toy.Sim.IsForwardSim Toy.Sim.Ex.Spin Toy.Sim.Ex.Loop (fun i' i => i' < i)
    Toy.Sim.Examples.spinRel ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.Spin (Toy.Sim.Behavior.diverges []) ∧
    Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.diverges [])
```

**Shows necessity of:** silent-divergence-preserved: WellFounded ord; forward-sim-preserves-non-wrong-behaviours: clause wf; flip-forward-to-backward: clause wf (through Toy.Sim.Cex.cex_flip_without_wf).

**Prior art.**

- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 3.7 (Definition 12, Theorem 4): the 'star' forward simulation diagram, with a measure on source states in a well-founded order that must decrease when the target stutters, introduced to rule out the 'infinite stuttering problem'; Theorem 4: under the initial-state, final-state and star-simulation hypotheses, every behaviour of the source that does not go wrong is a behaviour of the target. (Passages checked in the author's version of the article.)
- M. Cho, Y. Song, D. Lee, L. Gäher, D. Dreyer, 'Stuttering for Free', Proceedings of the ACM on Programming Languages 7(OOPSLA2):1677-1704, 2023, doi:10.1145/3622857. According to its abstract, soundness of stuttering simulations can be ensured with only 'asynchronous progress' instead of a bounded number of stuttering steps before synchronous progress, and the resulting technique (FreeSim, mechanized in Coq) simplifies the meta-theory of CompCert. (Abstract read; body not examined.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates the 'infinite stuttering problem' that Leroy (JAR 2009, Section 3.7) gives as the reason for the well-founded measure.

#### `cex-going-wrong-not-preserved`

**Kind:** counterexample. **Tier:** T0 — That compilers must be allowed to remove going-wrong behaviours (and that forward preservation is therefore stated only for behaviours that do not go wrong) is explained in Leroy (JAR 2009, Section 2.1) with dead-code elimination of a division by zero.

**Lean:** `Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved`.

**Plain claim.** There is an instance in which a source that is stuck at once (StuckNow) is forward-simulated, vacuously, by a target that terminates normally (Done 0), also as a one-pass chain: the source's going-wrong behaviour is not a behaviour of the target.

**Lean statement.**

```lean
Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved : Toy.Sim.IsForwardSim Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow (Toy.Sim.Behavior.goesWrong []) ∧
    ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.goesWrong []) ∧
      Toy.Sim.FSimChain Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0)
```

**Depth:** shallow — Finite case analysis on one-state systems.

**Shows necessity of:** forward-sim-preserves-non-wrong-behaviours: ∀ t, b ≠ .goesWrong t (both theorems).

**Prior art.**

- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 2.1, motivating Definition 3: a source that would go wrong on an integer division by zero whose result is unused is compiled by dead-code elimination into a program that does not go wrong, so compilers must be allowed to remove going-wrong behaviours. (Passage checked in the author's version of the article.)
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `forward_simulation_state_behaves` (line 284), `forward_simulation_behavior_improves` (line 316) and `forward_simulation_same_safe_behavior` (line 337).

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates why CompCert's forward preservation corollary is stated only for `not_wrong` behaviours.

#### `cex-naive-lexicographic-order`

**Kind:** counterexample. **Tier:** T1 — The need for the transitive closure is built into CompCert's and VeriComp's composite orders; this is a minimal machine-checked instance showing why.

**Lean:** `Toy.Sim.Cex.cex_comp_naive_lex_order_fails`.

**Plain claim.** There are two forward simulations, OneStep none 0 ⟶ Chain3 and Chain3 ⟶ Done 0 (the second with the non-transitive successor order), whose composite relation fails the step diagram for the lexicographic order without transitive closure, because one source step expands to two middle steps that each stutter in the last system; with compOrd the same composite relation satisfies the step diagram.

**Lean statement.**

```lean
Toy.Sim.Cex.cex_comp_naive_lex_order_fails : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 0) Toy.Sim.Cex.Chain3
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.chainRel₁ ∧
  Toy.Sim.IsForwardSim Toy.Sim.Cex.Chain3 (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.succOrd Toy.Sim.Cex.chainRel₂ ∧
    ¬Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.Done 0)
          (Toy.Sim.Cex.naiveCompOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.succOrd)
          (Toy.Sim.compRel Toy.Sim.Cex.chainRel₁ Toy.Sim.Cex.chainRel₂) ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.Done 0)
        (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.succOrd)
        (Toy.Sim.compRel Toy.Sim.Cex.chainRel₁ Toy.Sim.Cex.chainRel₂)
```

**Depth:** shallow — Finite case analysis on systems with at most three states.

**Shows necessity of:** step-diagrams-compose: the transitive closure in compOrd.

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: lemma `compose_forward_simulations` (line 1003); the composite index order is `lex_ord (clos_trans _ order') order` (line 1011), i.e. lexicographic with the transitive closure of the second-pass order, and the composite relation is relational composition through a middle state.
- M. Desharnais-Schäfer, 'A Generic Framework for Verified Compilers', Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020; read in its release archive for Isabelle2026 dated 2026-10-26, https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz, SHA-256 `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547` (Isabelle/HOL; related paper: M. Desharnais and S. Brunthaler, CPP 2021, doi:10.1145/3437992.3439923). Unlabelled transition systems with behaviours Terminates, Diverges and Goes_wrong (no event traces); locales `forward_simulation` and `backward_simulation` with a well-founded order, stuttering being a zero-step move with a smaller index; lemma `forward_simulation_composition` composes forward simulations with the order `lex_prodp order2++ order1` (lexicographic, transitive closure of the second-pass order), the same shape as `compOrd`; lemma `state_behaves_forward_to_backward` transfers behaviours from a safe source state to a right-unique (deterministic) target. Without events there is no receptiveness or event-matching determinacy. (Read in that archive: theories `VeriComp/Behaviour.thy` (datatype `behaviour`, line 5) and `VeriComp/Simulation.thy` (locales `backward_simulation`, line 13, and `forward_simulation`, line 148; lemmas `state_behaves_forward_to_backward`, line 273, and `forward_simulation_composition`, line 699). The release matters: the entry's history dates the addition of the forward-simulation composition lemmas to July 10, 2024, and `forward_simulation_composition` is absent from the entry's release archives dated 2020-02-25 (Isabelle2019) and 2024-05-26 (Isabelle2024) and present from the archive dated 2025-03-17 (Isabelle2025) on.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_comp_naive_lex_order_fails`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates why CompCert's and VeriComp's composite orders use the transitive closure of the second-pass order.

#### `cex-non-receptive-source`

**Kind:** counterexample. **Tier:** T1 — Receptiveness is a hypothesis of Theorem 2 of Ševčík et al. (POPL 2011) and of CompCert's `forward_to_backward_simulation`; this is a minimal machine-checked instance showing that it cannot be dropped.

**Lean:** `Toy.Sim.Cex.cex_flip_nonreceptive_source`, `Toy.Sim.Cex.cex_pipeline_nonreceptive_first`.

**Plain claim.** There is an instance in which a source that accepts only the input 0 is forward-simulated by a target that accepts inputs 0 and 1 and is determinate when any two inputs match: the target has the behaviour 'receive 1, return 1' that the source does not allow, no backward simulation exists, and the target does not refine the source (also as a one-pass pipeline whose first language never goes wrong).

**Lean statement.**

```lean
Toy.Sim.Cex.cex_flip_nonreceptive_source : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep (some 0) 0)
    (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Ex.branchRel ∧
  Toy.Sim.Determinate Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
    ¬Toy.Sim.Receptive Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.OneStep (some 0) 0) ∧
      Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) (Toy.Sim.Behavior.terminates [1] 1) ∧
        ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Behavior.terminates [1] 1) ∧
          Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
            ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1)
Toy.Sim.Cex.cex_pipeline_nonreceptive_first : Toy.Sim.FSimChain (Toy.Sim.Ex.OneStep (some 0) 0)
    (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
  Toy.Sim.Determinate Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
    ¬Toy.Sim.Receptive Toy.Sim.Ex.AnyInput (Toy.Sim.Ex.OneStep (some 0) 0) ∧
      Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.OneStep (some 0) 0) ∧
        ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
          ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) (Toy.Sim.Behavior.terminates [1] 1) ↔
              Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Behavior.terminates [1] 1))
```

**Depth:** shallow — Finite case analysis on systems with at most three states.

**Positive control** (a nearby setting where the conclusion that fails here does hold): `Toy.Sim.Examples.positive_control_flip`

```lean
Toy.Sim.Examples.positive_control_flip : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
    Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt ∧
      Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtBackRel ∧
        (∀ (i : Nat) (s₁ : Toy.Sim.Ex.SrcSt) (s₂ : Toy.Sim.Ex.TgtSt),
            Toy.Sim.Ex.SrcTgtRel i s₁ s₂ → ∃ i', Toy.Sim.Ex.SrcTgtBackRel i' s₁ s₂) ∧
          ¬Toy.Sim.NoBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧ Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
```

**Shows necessity of:** flip-forward-to-backward: Receptive M L₁; pipeline-end-to-end-refinement: Receptive M L; pipeline-behaviour-equality-when-first-never-goes-wrong: Receptive M L.

**Prior art.**

- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, 'Relaxed-memory concurrency and verified compilation', POPL 2011, pp. 43-54, doi:10.1145/1926385.1926393. Section 4 defines labels 'of the same kind' (te ≍ te': they differ only in input values), receptive thread LTSs (Definition 2), determinate thread LTSs (Definition 3: co-enabled labels are of the same kind, and equal labels lead to equal states), threadwise forward and backward simulations with a well-founded order for stuttering (Definitions 4-5), and Theorem 2: 'If R is a threadwise forward simulation from S to T, S is receptive, and T is determinate, then there is a threadwise backward simulation that contains R.' This is the step-level flip theorem, including the clause 'contains R'; their simulations also treat explicit failure labels and are lifted to a concurrent TSO machine, which this package does not model. (Section 4 read in the authors' version of the paper.)
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: records `receptive` (line 1050) and `determinate` (line 1058), stated with the trace relation `match_traces` and a separate `single_events` field (`sr_traces`, `sd_traces`); CompCert's `sd_determ` bundles the label-matching and functionality clauses that are separate here.

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_flip_nonreceptive_source`, `Toy.Sim.Cex.cex_pipeline_nonreceptive_first`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates why receptiveness is a hypothesis of CompCert's `forward_to_backward_simulation`.

#### `cex-determinacy-clauses-necessary`

**Kind:** counterexample. **Tier:** T1 — That a forward simulation into a nondeterministic target admits extra target behaviours is stated at the level of behaviour sets in Leroy (JAR 2009, Section 2.1); the necessity of each of the five determinacy clauses separately is made precise here as minimal machine-checked instances.

**Lean:** `Toy.Sim.Cex.cex_flip_target_labels_mismatch`, `Toy.Sim.Cex.cex_flip_target_event_labels_mismatch`, `Toy.Sim.Cex.cex_flip_target_not_functional`, `Toy.Sim.Cex.cex_flip_target_two_initial_states`, `Toy.Sim.Cex.cex_flip_target_final_state_steps`, `Toy.Sim.Cex.cex_flip_target_two_results`, `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_not_functional`, `Toy.Sim.Cex.cex_pipeline_last_two_initial_states`, `Toy.Sim.Cex.cex_pipeline_last_final_state_steps`, `Toy.Sim.Cex.cex_pipeline_last_two_results`.

**Plain claim.** For each of the five clauses of Determinate M L₂ there is an instance in which a forward simulation exists, the source is receptive, the target satisfies the other four clauses but not this one, the target has a terminating behaviour that the source lacks, no backward simulation exists, and the target does not refine the source. The violations are: a state offering a silent step and an event, or two unmatched events (labels); two silent successors leading to different results (functional); two initial states (init); a final state that can still step (finalNoStep); a final state with two results (finalDet). Each is restated for one-pass pipelines whose first language never goes wrong (Toy.Sim.Cex.cex_pipeline_last_labels_mismatch, Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch, Toy.Sim.Cex.cex_pipeline_last_not_functional, Toy.Sim.Cex.cex_pipeline_last_two_initial_states, Toy.Sim.Cex.cex_pipeline_last_final_state_steps, Toy.Sim.Cex.cex_pipeline_last_two_results).

**Lean statement.**

```lean
Toy.Sim.Cex.cex_flip_target_labels_mismatch : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 0)
    (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Ex.branchRel ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 0) ∧
    ¬Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
      Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
              Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) (Toy.Sim.Behavior.terminates [1] 1) ∧
                ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Behavior.terminates [1] 1) ∧
                  Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
                    ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none (some 1) 0 1)
Toy.Sim.Cex.cex_flip_target_event_labels_mismatch : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep (some 0) 0)
    (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Ex.branchRel ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep (some 0) 0) ∧
    ¬Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
      Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
              Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) (Toy.Sim.Behavior.terminates [1] 1) ∧
                ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Behavior.terminates [1] 1) ∧
                  Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
                    ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1)
Toy.Sim.Cex.cex_flip_target_not_functional : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 0)
    (Toy.Sim.Ex.TwoBranch none none 0 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Ex.branchRel ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 0) ∧
    Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
      ¬Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
              Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch none none 0 1) (Toy.Sim.Behavior.terminates [] 1) ∧
                ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Behavior.terminates [] 1) ∧
                  Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
                    ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none none 0 1)
Toy.Sim.Cex.cex_flip_target_two_initial_states : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoInits Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relToFalse ∧
    Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
      Toy.Sim.StepLabelsMatch M Toy.Sim.Ex.TwoInits ∧
        Toy.Sim.StepFunctional Toy.Sim.Ex.TwoInits ∧
          ¬Toy.Sim.InitDeterminate Toy.Sim.Ex.TwoInits ∧
            Toy.Sim.FinalNoStep Toy.Sim.Ex.TwoInits ∧
              Toy.Sim.FinalDeterminate Toy.Sim.Ex.TwoInits ∧
                Toy.Sim.HasBehavior Toy.Sim.Ex.TwoInits (Toy.Sim.Behavior.terminates [] 1) ∧
                  ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1) ∧
                    Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoInits ∧
                      ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoInits
Toy.Sim.Cex.cex_flip_target_final_state_steps : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep none 1) Toy.Sim.Ex.FinalSteps
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 1) ∧
    Toy.Sim.StepLabelsMatch Eq Toy.Sim.Ex.FinalSteps ∧
      Toy.Sim.StepFunctional Toy.Sim.Ex.FinalSteps ∧
        Toy.Sim.InitDeterminate Toy.Sim.Ex.FinalSteps ∧
          ¬Toy.Sim.FinalNoStep Toy.Sim.Ex.FinalSteps ∧
            Toy.Sim.FinalDeterminate Toy.Sim.Ex.FinalSteps ∧
              Toy.Sim.HasBehavior Toy.Sim.Ex.FinalSteps (Toy.Sim.Behavior.terminates [] 0) ∧
                ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 1) (Toy.Sim.Behavior.terminates [] 0) ∧
                  Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep none 1) Toy.Sim.Ex.FinalSteps ∧
                    ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 1) Toy.Sim.Ex.FinalSteps
Toy.Sim.Cex.cex_flip_target_two_results : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoResults Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
    Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
      Toy.Sim.StepLabelsMatch M Toy.Sim.Ex.TwoResults ∧
        Toy.Sim.StepFunctional Toy.Sim.Ex.TwoResults ∧
          Toy.Sim.InitDeterminate Toy.Sim.Ex.TwoResults ∧
            Toy.Sim.FinalNoStep Toy.Sim.Ex.TwoResults ∧
              ¬Toy.Sim.FinalDeterminate Toy.Sim.Ex.TwoResults ∧
                Toy.Sim.HasBehavior Toy.Sim.Ex.TwoResults (Toy.Sim.Behavior.terminates [] 1) ∧
                  ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1) ∧
                    Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoResults ∧
                      ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoResults
Toy.Sim.Cex.cex_pipeline_last_labels_mismatch : Toy.Sim.FSimChain (Toy.Sim.Ex.OneStep none 0)
    (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 0) ∧
    ¬Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
      Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
              Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.OneStep none 0) ∧
                ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) ∧
                  ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch none (some 1) 0 1) (Toy.Sim.Behavior.terminates [1] 1) ↔
                      Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Behavior.terminates [1] 1))
Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch : Toy.Sim.FSimChain (Toy.Sim.Ex.OneStep (some 0) 0)
    (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep (some 0) 0) ∧
    ¬Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
      Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
              Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.OneStep (some 0) 0) ∧
                ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1) ∧
                  ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch (some 0) (some 1) 0 1)
                        (Toy.Sim.Behavior.terminates [1] 1) ↔
                      Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep (some 0) 0) (Toy.Sim.Behavior.terminates [1] 1))
Toy.Sim.Cex.cex_pipeline_last_not_functional : Toy.Sim.FSimChain (Toy.Sim.Ex.OneStep none 0)
    (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 0) ∧
    Toy.Sim.StepLabelsMatch Eq (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
      ¬Toy.Sim.StepFunctional (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
        Toy.Sim.InitDeterminate (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
          Toy.Sim.FinalNoStep (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
            Toy.Sim.FinalDeterminate (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
              Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.OneStep none 0) ∧
                ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
                  ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.TwoBranch none none 0 1) (Toy.Sim.Behavior.terminates [] 1) ↔
                      Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 0) (Toy.Sim.Behavior.terminates [] 1))
Toy.Sim.Cex.cex_pipeline_last_two_initial_states : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoInits ∧
    Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
      Toy.Sim.StepLabelsMatch M Toy.Sim.Ex.TwoInits ∧
        Toy.Sim.StepFunctional Toy.Sim.Ex.TwoInits ∧
          ¬Toy.Sim.InitDeterminate Toy.Sim.Ex.TwoInits ∧
            Toy.Sim.FinalNoStep Toy.Sim.Ex.TwoInits ∧
              Toy.Sim.FinalDeterminate Toy.Sim.Ex.TwoInits ∧
                Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done 0) ∧
                  ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoInits ∧
                    ¬(Toy.Sim.HasBehavior Toy.Sim.Ex.TwoInits (Toy.Sim.Behavior.terminates [] 1) ↔
                        Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1))
Toy.Sim.Cex.cex_pipeline_last_final_state_steps : Toy.Sim.FSimChain (Toy.Sim.Ex.OneStep none 1) Toy.Sim.Ex.FinalSteps ∧
  Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep none 1) ∧
    Toy.Sim.StepLabelsMatch Eq Toy.Sim.Ex.FinalSteps ∧
      Toy.Sim.StepFunctional Toy.Sim.Ex.FinalSteps ∧
        Toy.Sim.InitDeterminate Toy.Sim.Ex.FinalSteps ∧
          ¬Toy.Sim.FinalNoStep Toy.Sim.Ex.FinalSteps ∧
            Toy.Sim.FinalDeterminate Toy.Sim.Ex.FinalSteps ∧
              Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.OneStep none 1) ∧
                ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep none 1) Toy.Sim.Ex.FinalSteps ∧
                  ¬(Toy.Sim.HasBehavior Toy.Sim.Ex.FinalSteps (Toy.Sim.Behavior.terminates [] 0) ↔
                      Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep none 1) (Toy.Sim.Behavior.terminates [] 0))
Toy.Sim.Cex.cex_pipeline_last_two_results : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoResults ∧
    Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
      Toy.Sim.StepLabelsMatch M Toy.Sim.Ex.TwoResults ∧
        Toy.Sim.StepFunctional Toy.Sim.Ex.TwoResults ∧
          Toy.Sim.InitDeterminate Toy.Sim.Ex.TwoResults ∧
            Toy.Sim.FinalNoStep Toy.Sim.Ex.TwoResults ∧
              ¬Toy.Sim.FinalDeterminate Toy.Sim.Ex.TwoResults ∧
                Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done 0) ∧
                  ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.TwoResults ∧
                    ¬(Toy.Sim.HasBehavior Toy.Sim.Ex.TwoResults (Toy.Sim.Behavior.terminates [] 1) ↔
                        Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1))
```

**Depth:** shallow — Finite case analysis on systems with at most three states.

**Positive control** (a nearby setting where the conclusion that fails here does hold): `Toy.Sim.Examples.positive_control_flip`

```lean
Toy.Sim.Examples.positive_control_flip : Toy.Sim.IsForwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i)
    Toy.Sim.Ex.SrcTgtRel ∧
  Toy.Sim.Receptive Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Src ∧
    Toy.Sim.Determinate Toy.Sim.Ex.AnyInput Toy.Sim.Ex.Tgt ∧
      Toy.Sim.IsBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt (fun i' i => i' < i) Toy.Sim.Ex.SrcTgtBackRel ∧
        (∀ (i : Nat) (s₁ : Toy.Sim.Ex.SrcSt) (s₂ : Toy.Sim.Ex.TgtSt),
            Toy.Sim.Ex.SrcTgtRel i s₁ s₂ → ∃ i', Toy.Sim.Ex.SrcTgtBackRel i' s₁ s₂) ∧
          ¬Toy.Sim.NoBackwardSim Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt ∧ Toy.Sim.RefinedBy Toy.Sim.Ex.Src Toy.Sim.Ex.Tgt
```

**Shows necessity of:** flip-forward-to-backward: each Determinate clause (both theorems); pipeline-end-to-end-refinement: each Determinate clause (through the pipeline restatements); pipeline-behaviour-equality-when-first-never-goes-wrong: each Determinate clause.

**Prior art.**

- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, 'Relaxed-memory concurrency and verified compilation', POPL 2011, pp. 43-54, doi:10.1145/1926385.1926393. Section 4 defines labels 'of the same kind' (te ≍ te': they differ only in input values), receptive thread LTSs (Definition 2), determinate thread LTSs (Definition 3: co-enabled labels are of the same kind, and equal labels lead to equal states), threadwise forward and backward simulations with a well-founded order for stuttering (Definitions 4-5), and Theorem 2: 'If R is a threadwise forward simulation from S to T, S is receptive, and T is determinate, then there is a threadwise backward simulation that contains R.' This is the step-level flip theorem, including the clause 'contains R'; their simulations also treat explicit failure labels and are lifted to a concurrent TSO machine, which this package does not model. (Section 4 read in the authors' version of the paper.)
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Smallstep.v: records `receptive` (line 1050) and `determinate` (line 1058), stated with the trace relation `match_traces` and a separate `single_events` field (`sr_traces`, `sd_traces`); CompCert's `sd_determ` bundles the label-matching and functionality clauses that are separate here.
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 2.1 (Definitions 2-5, Figure 2) relates whole-program behaviour inclusions — 'backward simulation' (every behaviour of the compiled program C is a behaviour of the source S), 'forward simulation' (every behaviour of S is a behaviour of C), and their versions for safe programs — and shows that the forward inclusion implies the backward one when C is deterministic, i.e. admits a single behaviour (target language without internal nondeterminism and a deterministic execution environment). These are behaviour-set statements, not step-level simulation diagrams; the article has no step-level receptiveness or determinacy conditions and no step-level flip theorem. (Passages checked in the author's version of the article.)

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_flip_target_labels_mismatch`, `Toy.Sim.Cex.cex_flip_target_event_labels_mismatch`, `Toy.Sim.Cex.cex_flip_target_not_functional`, `Toy.Sim.Cex.cex_flip_target_two_initial_states`, `Toy.Sim.Cex.cex_flip_target_final_state_steps`, `Toy.Sim.Cex.cex_flip_target_two_results`, `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch`, `Toy.Sim.Cex.cex_pipeline_last_not_functional`, `Toy.Sim.Cex.cex_pipeline_last_two_initial_states`, `Toy.Sim.Cex.cex_pipeline_last_final_state_steps`, `Toy.Sim.Cex.cex_pipeline_last_two_results`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexamples are about the toy systems only; they illustrate why each field of CompCert's `determinate` record (with `sd_determ` split into two clauses) is a hypothesis of `forward_to_backward_simulation`.

#### `cex-refinement-not-symmetric`

**Kind:** counterexample. **Tier:** T0 — Immediate from the definition of `behavior_improves` in CompCert.

**Lean:** `Toy.Sim.Cex.cex_improves_not_symmetric`, `Toy.Sim.Cex.cex_refinedBy_not_symmetric`.

**Plain claim.** There are instances showing that neither Improves nor RefinedBy is symmetric: going wrong at once is improved by terminating normally but not conversely, and a program that goes wrong at once (StuckNow) is refined by a program that terminates normally (Done 0) but not conversely.

**Lean statement.**

```lean
Toy.Sim.Cex.cex_improves_not_symmetric : Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [])
    (Toy.Sim.Behavior.terminates [] 0) ∧
  ¬Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 0) (Toy.Sim.Behavior.goesWrong [])
Toy.Sim.Cex.cex_refinedBy_not_symmetric : Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0) ∧
  ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow
```

**Depth:** shallow — Finite case analysis on one-state systems.

**Shows necessity of:** refinement-is-a-preorder: the relations are a partial order and a preorder, not equivalences.

**Prior art.**

- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `behavior_improves` (line 81), `behavior_improves_refl` (line 84), `behavior_improves_trans` (line 90), `behavior_improves_bot` (line 102); `program_behaves` (line 141) includes the constructor `program_goes_initially_wrong` (line 145) for programs without initial state. CompCert's `program_behavior` (line 41) also has a constructor for infinite event traces, which this package omits.

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_improves_not_symmetric`, `Toy.Sim.Cex.cex_refinedBy_not_symmetric`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates that CompCert's `behavior_improves` is an order, not an equivalence.

#### `cex-inclusion-needs-source-never-goes-wrong`

**Kind:** counterexample. **Tier:** T0 — This is the reason CompCert states behaviour inclusion for source programs that do not go wrong (Leroy, CACM 2009, property (2); Leroy, JAR 2009, Definition 3).

**Lean:** `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong`, `Toy.Sim.Cex.cex_inclusion_without_refinement`.

**Plain claim.** There is an instance (source StuckNow, which goes wrong at once; target Done 0) in which refinement holds, a backward simulation exists, and a one-pass chain with receptive first and determinate last language exists, yet the target's behaviour 'return 0' is not a source behaviour and the two behaviour sets differ. And there is an instance in which the source never goes wrong but, without refinement, a target behaviour is not a source behaviour.

**Lean statement.**

```lean
Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0) ∧
    Toy.Sim.IsBackwardSim Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
      Toy.Sim.FSimChain Toy.Sim.Ex.StuckNow (Toy.Sim.Ex.Done 0) ∧
        Toy.Sim.Receptive M Toy.Sim.Ex.StuckNow ∧
          Toy.Sim.Determinate M (Toy.Sim.Ex.Done 0) ∧
            Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ∧
              ¬Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow (Toy.Sim.Behavior.terminates [] 0) ∧
                ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ↔
                    Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow (Toy.Sim.Behavior.terminates [] 0))
Toy.Sim.Cex.cex_inclusion_without_refinement : Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done 0) ∧
  Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 1) (Toy.Sim.Behavior.terminates [] 1) ∧
    ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1)
```

**Depth:** shallow — Finite case analysis on one-state systems.

**Shows necessity of:** refinement-is-inclusion-when-source-never-goes-wrong: NeverGoesWrong L₁, and RefinedBy / IsBackwardSim; pipeline-behaviour-equality-when-first-never-goes-wrong: NeverGoesWrong L.

**Prior art.**

- X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814. Section 2.1 states whole-program behaviour-preservation properties; for source and target languages that are deterministic and execution environments that are deterministic (so each program has exactly one behaviour), 'S safe implies every behaviour of C is a behaviour of S' is equivalent to the easier 'every non-wrong behaviour of S is a behaviour of C'. Section 2.3 composes compiler passes for any transitive whole-program preservation property; it does not concern step-level simulation diagrams or stuttering orders. (Passages checked in the author's version of the article.)
- X. Leroy, 'A formally verified compiler back-end', Journal of Automated Reasoning 43(4):363-446, 2009, doi:10.1007/s10817-009-9155-4. Section 2.1 (Definitions 2-5, Figure 2) relates whole-program behaviour inclusions — 'backward simulation' (every behaviour of the compiled program C is a behaviour of the source S), 'forward simulation' (every behaviour of S is a behaviour of C), and their versions for safe programs — and shows that the forward inclusion implies the backward one when C is deterministic, i.e. admits a single behaviour (target language without internal nondeterminism and a deterministic execution environment). These are behaviour-set statements, not step-level simulation diagrams; the article has no step-level receptiveness or determinacy conditions and no step-level flip theorem. (Passages checked in the author's version of the article.)
- CompCert, repository AbsInt/CompCert, release tag v3.16, commit a4ad87b17898cf7b7c8638c32ad694a15f7c0032, file common/Behaviors.v: `backward_simulation_behavior_improves` (line 493) and `backward_simulation_same_safe_behavior` (line 519).

**Design question.** In a multi-pass verified compiler, what must each pass prove so that end-to-end correctness follows, and when is a forward simulation (source step implies target steps) enough instead of the backward simulation (target step implies source steps) that end-to-end refinement needs?

Basis: execution (Lean kernel check) — `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong`, `Toy.Sim.Cex.cex_inclusion_without_refinement`; axioms listed under **Evidence**.

Basis: derived (modeling bridge) — The counterexample is about the toy systems only; it illustrates why CompCert's `backward_simulation_same_safe_behavior` assumes that every source behaviour is `not_wrong`.

## Boundaries

### Non-claims (per result)

What each result does **not** show. These are part of the result: quote them together with the plain-language claim.

#### Non-claims of `partial-run-simulated`

- Says nothing about what the target does after the matched run: if the source is stuck at s, the related target state may step, terminate, or belong to a system with no behaviour at all in this model (Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved, Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior).
- Does not say the target has only such runs: target runs with no source counterpart are possible (Toy.Sim.Cex.cex_flip_target_not_functional).
- Uses neither well-foundedness nor the final-state clause, and by itself yields neither termination nor divergence of the target.
- This is the whole content of a forward simulation for a source behaviour that goes wrong: the trace emitted before going wrong is a trace of a partial target run. It is not claimed that some target behaviour improves on the going-wrong source behaviour.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `terminating-behaviours-preserved`

- No converse: a terminating behaviour of the target need not be a behaviour of the source (Toy.Sim.Cex.cex_flip_target_not_functional).
- Nothing about divergence: preserving silent divergence additionally needs a well-founded index order (Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved).
- The final-state clause requires the related target state to be final itself; a pass whose target needs further silent steps after the source has finished does not satisfy this clause as stated, and no result here covers that weaker clause.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `silent-divergence-preserved`

- Only silent divergence after a finite trace. A source run that emits infinitely many events is not a behaviour in this model and nothing is claimed about it.
- The target's infinite silent run is asserted to exist; it is not claimed to be related step for step to the source run.
- Without a well-founded order the three forward clauses can hold between a diverging source and a target that terminates at once (Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved).
- Well-foundedness of the index order is shown necessary only within this step-diagram formulation; other ways of ruling out infinite stuttering in the literature (for example the 'asynchronous progress' simulations of Cho et al., PACMPL 7(OOPSLA2), 2023) are not covered or compared here.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `forward-sim-preserves-non-wrong-behaviours`

- This is not refinement: the inclusion goes from source behaviours to target behaviours. The target may have additional behaviours that the source does not allow (Toy.Sim.Cex.cex_flip_target_not_functional).
- Unlike CompCert's `forward_simulation_behavior_improves`, nothing is claimed for going-wrong source behaviours: in this model 'some target behaviour improves on it' can fail because the target may have no behaviour at all (Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior).
- Consequence for compiler design: because every non-going-wrong source behaviour survives, a pass verified by a forward simulation cannot remove observable nondeterminism of a source that never goes wrong (Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation).
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `step-diagrams-compose`

- The transitive closure in compOrd cannot be dropped in general: with the plain lexicographic order the same composite relation can fail the step diagram (Toy.Sim.Cex.cex_comp_naive_lex_order_fails).
- Escape hatch: the transitive closure in `compOrd` matters only when ord₂ is not transitive (as for `succOrd` in Toy.Sim.Cex.cex_comp_naive_lex_order_fails); when ord₂ is transitive (for example `<` on `Nat`), `compOrd` coincides with the plain lexicographic order (Toy.Sim.compOrd_iff_lex_of_transitive, Toy.Sim.Cex.compOrd_iff_naiveCompOrd_of_transitive).
- The claim is about this particular composite relation and order; it does not say they are the only or the smallest ones.
- Composition of backward simulations is not addressed.
- Vertical composition only (stacking passes); nothing about composing simulations of separately compiled modules.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `forward-simulations-compose`

- The counterexamples show that no hypothesis can be dropped in general; they do not show that the composite fails whenever one pass fails a clause. For example, if R₁ never relates any state to a middle state where R₂ fails a clause, or if one of the index types is empty, the composite can still be a forward simulation.
- The middle language is hidden inside the composite relation; nothing is concluded about it.
- Does not give refinement between L₁ and L₃; see pipeline-end-to-end-refinement for the extra hypotheses that requires.
- Says nothing about the order type of compOrd or about bounds on the number of stuttering steps.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `flip-forward-to-backward`

- Does not say that R itself is a backward simulation. The backward relation is in general a different, larger relation; the statement exposes only its existence and that it contains R.
- Does not allow a pass verified by a forward simulation (or a chain of them) to remove observable nondeterminism of a source or intermediate language: forward simulations preserve every behaviour of the source that does not go wrong (Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors), so if the source has two such behaviours the target has both, whatever its determinacy. A pass that fixes an unspecified choice (for example an evaluation order) must be verified another way, for example by a backward simulation, and composed through `RefinedBy.trans`. Lean instance: Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation (a source that may return 0 or 1 and never goes wrong is refined by the deterministic `Done 0`, and a backward simulation exists, but no forward simulation exists). CompCert's end-to-end theorem for C, `c_semantic_preservation` (driver/Compiler.v, line 419), prepends such a backward simulation from `Csem` to its forward-simulated pipeline.
- Escape hatch (different matching relations): the source and target need not use literally the same relation; if the source is receptive for M₁, the target determinate for M₂, and M₂ ⊆ M₁, then the target is determinate for M₁ (Toy.Sim.Determinate.mono) and the theorem applies with M := M₁. No algebraic axiom on M appears in the statement, but determinacy constrains M on the target's events: M is reflexive on every event the target can emit and symmetric on any two events offered by the same target state (Toy.Sim.StepLabelsMatch.refl_symm); determinacy of an event-emitting target is impossible for an irreflexive M. Receptiveness for a smaller relation is not enough: in Toy.Sim.Cex.cex_flip_nonreceptive_source the source is receptive for Eq while the target is determinate only for AnyInput.
- `Receptive` and `Determinate` quantify over all states, including unreachable ones. Nondeterminism confined to unreachable states need not break the conclusion (Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism). Whether the theorem holds in general with both conditions restricted to reachable states (or to an invariant) is not proved in this package.
- Unknown (not examined): `FSimFinal` requires a target state related to a final source state to be final itself, with no trailing silent target steps. Whether the flip lemma (and hence end-to-end refinement) still holds when `FSimFinal` is weakened to 'the related target state reaches, by silent steps, a final state with the same result' is not examined in this package.
- One observable event per step (`Option E`) is built into `LTS`. CompCert's `receptive` and `determinate` records include a separate `single_events` condition, and for its multi-event C semantics CompCert flips the forward simulation only after the `atomic` construction (driver/Compiler.v, lines 413-416). Nothing here is claimed for semantics whose steps carry several events.
- `Safe L₁ s₁` in the backward clauses means only that s₁ cannot get stuck along silent steps before its next observable event (as CompCert's `Smallstep.safe`); it does not mean that s₁ never goes wrong after later events, and it is strictly weaker than whole-program `NeverGoesWrong L₁` (Toy.Sim.Examples.safe_pos: the initial state of `EmitThenStuck` is `Safe` although the program goes wrong after the trace [1]). A backward simulation constrains the target only while the related source state is Safe; nothing is concluded about target steps taken after the source has gone wrong.
- Determinate Eq forbids a target state from offering two different events, so a target that reads inputs from the environment is not covered by the M = Eq special case; it needs the general theorem with a receptive source.
- No claim that receptiveness or determinacy hold for any real language.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `backward-sim-gives-refinement`

- `RefinedBy` and `HasBehavior` ignore runs that emit infinitely many events — not only in targets with no modelled behaviour at all (Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), but also in targets that have modelled behaviours plus a run that emits events forever: `DoneOrChatter` has exactly the behaviours of `Done 0` and refines it although one of its runs emits the event 0 forever (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). So neither `RefinedBy L₁ L₂` nor `∀ b, HasBehavior L₂ b ↔ HasBehavior L₁ b` constrains executions of L₂ that emit infinitely many events.
- A backward simulation constrains every target step, including the steps of runs that emit infinitely many events, but its consequence `RefinedBy` forgets those runs: from `Done 0` to `DoneOrChatter` there is no backward simulation, yet `RefinedBy (Done 0) DoneOrChatter` holds (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). `RefinedBy` is a strictly weaker guarantee than `IsBackwardSim`.
- Refinement is not behaviour inclusion: if the source can go wrong, the target may have behaviours the source does not have (Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong).
- Refinement is not behaviour equality: the source may have behaviours that the target lacks.
- If the source has no initial state it goes wrong with the empty trace by convention, and then every target is a refinement.
- Does not preserve termination, timing, resource use, or security hyperproperties such as noninterference or constant-time execution. Under `RefinedBy`, a source that goes wrong after trace t permits every target behaviour whose trace extends t (including divergence and further events); and even when the source never goes wrong, a target may drop a terminating behaviour in favour of divergence (Toy.Sim.Boundary.refinedBy_may_drop_termination: `Loop` refines a source that may return 0 or diverge).
- `Safe L₁ s₁` in the backward clauses means only that s₁ cannot get stuck along silent steps before its next observable event (as CompCert's `Smallstep.safe`); it does not mean that s₁ never goes wrong after later events, and it is strictly weaker than whole-program `NeverGoesWrong L₁` (Toy.Sim.Examples.safe_pos: the initial state of `EmitThenStuck` is `Safe` although the program goes wrong after the trace [1]).
- The source behaviour that is improved upon is not exposed and need not be unique.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `refinement-is-inclusion-when-source-never-goes-wrong`

- NeverGoesWrong quantifies over all behaviours of the source, hence over all environment choices; it is a property of the whole source program, not of one run. It is much stronger than the per-state condition Safe used inside backward simulations (Toy.Sim.Examples.safe_pos).
- Gives inclusion, not equality, of behaviour sets.
- `RefinedBy` and `HasBehavior` ignore runs that emit infinitely many events — not only in targets with no modelled behaviour at all (Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), but also in targets that have modelled behaviours plus a run that emits events forever: `DoneOrChatter` has exactly the behaviours of `Done 0` and refines it although one of its runs emits the event 0 forever (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). So neither `RefinedBy L₁ L₂` nor `∀ b, HasBehavior L₂ b ↔ HasBehavior L₁ b` constrains executions of L₂ that emit infinitely many events. In particular `NeverGoesWrong Chatter` holds and every source is refined by `Chatter` (Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), so the inclusion says nothing about such a target.
- Does not preserve termination, timing, resource use, or security hyperproperties such as noninterference or constant-time execution. Under `RefinedBy`, a source that goes wrong after trace t permits every target behaviour whose trace extends t (including divergence and further events); and even when the source never goes wrong, a target may drop a terminating behaviour in favour of divergence (Toy.Sim.Boundary.refinedBy_may_drop_termination: `Loop` refines a source that may return 0 or diverge).
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `pipeline-collapses-to-one-forward-simulation`

- The resulting index type, order and relation are not exposed (they are the iterated compOrd and compRel, ending with the identity).
- Nothing is retained about the intermediate languages.
- All languages of a chain share one event type and one result type; passes that change how events or results are represented are not modelled.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Behaviours with infinitely many events are not modelled; a system whose every run emits events forever has no behaviour at all in this model (Toy.Sim.Ex.chatter_no_behavior).
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `pipeline-end-to-end-refinement`

- Does not allow a pass verified by a forward simulation (or a chain of them) to remove observable nondeterminism of a source or intermediate language: forward simulations preserve every behaviour of the source that does not go wrong (Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors), so if the source has two such behaviours the target has both, whatever its determinacy. A pass that fixes an unspecified choice (for example an evaluation order) must be verified another way, for example by a backward simulation, and composed through `RefinedBy.trans`. Lean instance: Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation (a source that may return 0 or 1 and never goes wrong is refined by the deterministic `Done 0`, and a backward simulation exists, but no forward simulation exists). CompCert's end-to-end theorem for C, `c_semantic_preservation` (driver/Compiler.v, line 419), prepends such a backward simulation from `Csem` to its forward-simulated pipeline.
- Escape hatch for mixed pipelines: a pass verified only by a backward simulation cannot be a link of `FSimChain`, but it yields `RefinedBy` (Toy.Sim.backwardSim_gives_refinedBy), and `RefinedBy` is transitive (Toy.Sim.RefinedBy.trans), so such passes compose end to end with a forward-simulated segment that has been flipped once.
- Escape hatch (different matching relations): the source and target need not use literally the same relation; if the source is receptive for M₁, the target determinate for M₂, and M₂ ⊆ M₁, then the target is determinate for M₁ (Toy.Sim.Determinate.mono) and the theorem applies with M := M₁. No algebraic axiom on M appears in the statement, but determinacy constrains M on the target's events: M is reflexive on every event the target can emit and symmetric on any two events offered by the same target state (Toy.Sim.StepLabelsMatch.refl_symm); determinacy of an event-emitting target is impossible for an irreflexive M.
- `Receptive` and `Determinate` quantify over all states, including unreachable ones. Nondeterminism confined to unreachable states need not break the conclusion (Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism). Whether the theorem holds in general with both conditions restricted to reachable states (or to an invariant) is not proved in this package.
- Unknown (not examined): `FSimFinal` requires a target state related to a final source state to be final itself, with no trailing silent target steps. Whether the flip lemma (and hence end-to-end refinement) still holds when `FSimFinal` is weakened to 'the related target state reaches, by silent steps, a final state with the same result' is not examined in this package.
- One observable event per step (`Option E`) is built into `LTS`. CompCert's `receptive` and `determinate` records include a separate `single_events` condition, and for its multi-event C semantics CompCert flips the forward simulation only after the `atomic` construction (driver/Compiler.v, lines 413-416). Nothing here is claimed for semantics whose steps carry several events.
- `RefinedBy` and `HasBehavior` ignore runs that emit infinitely many events — not only in targets with no modelled behaviour at all (Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), but also in targets that have modelled behaviours plus a run that emits events forever: `DoneOrChatter` has exactly the behaviours of `Done 0` and refines it although one of its runs emits the event 0 forever (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). So neither `RefinedBy L₁ L₂` nor `∀ b, HasBehavior L₂ b ↔ HasBehavior L₁ b` constrains executions of L₂ that emit infinitely many events.
- Does not preserve termination, timing, resource use, or security hyperproperties such as noninterference or constant-time execution. Under `RefinedBy`, a source that goes wrong after trace t permits every target behaviour whose trace extends t (including divergence and further events); and even when the source never goes wrong, a target may drop a terminating behaviour in favour of divergence (Toy.Sim.Boundary.refinedBy_may_drop_termination: `Loop` refines a source that may return 0 or diverge).
- All languages of a chain share one event type and one result type; passes that change how events or results are represented are not modelled.
- Intermediate languages are unconstrained: they need be neither receptive nor determinate (witness: Mid). Conversely nothing is concluded about them.
- Per-pass refinement is not concluded: a single pass with a forward simulation into a nondeterministic intermediate language need not refine its source.
- Refinement, not inclusion or equality of behaviours; see pipeline-behaviour-equality-when-first-never-goes-wrong for the extra hypothesis that gives equality.
- A last language that reads inputs from the environment is not determinate for Eq; it needs the general theorem with a receptive first language.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `pipeline-behaviour-equality-when-first-never-goes-wrong`

- Consequence, not an extra assumption: under these hypotheses L' exhibits every behaviour of L. So no such pipeline exists from a first language that never goes wrong and has an observable choice into a last language that lacks one of the choices; the pass that fixes the choice needs a different proof method (Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation).
- Equality of behaviour sets, not bisimilarity of the two systems.
- `RefinedBy` and `HasBehavior` ignore runs that emit infinitely many events — not only in targets with no modelled behaviour at all (a system whose every run emits events forever has no behaviour, Toy.Sim.Ex.chatter_no_behavior; such a target refines every source vacuously, Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), but also in targets that have modelled behaviours plus a run that emits events forever: `DoneOrChatter` has exactly the behaviours of `Done 0` and refines it although one of its runs emits the event 0 forever (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). So neither `RefinedBy L₁ L₂` nor `∀ b, HasBehavior L₂ b ↔ HasBehavior L₁ b` constrains executions of L₂ that emit infinitely many events.
- Escape hatch (different matching relations): the source and target need not use literally the same relation; if the source is receptive for M₁, the target determinate for M₂, and M₂ ⊆ M₁, then the target is determinate for M₁ (Toy.Sim.Determinate.mono) and the theorem applies with M := M₁. No algebraic axiom on M appears in the statement, but determinacy constrains M on the target's events: M is reflexive on every event the target can emit and symmetric on any two events offered by the same target state (Toy.Sim.StepLabelsMatch.refl_symm); determinacy of an event-emitting target is impossible for an irreflexive M.
- NeverGoesWrong is a hypothesis about all behaviours of the first language (all environment choices); the per-state condition Safe is much weaker and does not suffice.
- All languages of a chain share one event type and one result type; passes that change how events or results are represented are not modelled.
- Equality of behaviour sets says nothing about timing, resource use, or security hyperproperties such as noninterference.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.
- Whole programs only: nothing is claimed about separate compilation, linking, or open (contextual) simulations.

#### Non-claims of `refinement-is-a-preorder`

- RefinedBy is not antisymmetric: StuckNow and NoInit refine each other and are different systems (Toy.Sim.Boundary.refinedBy_not_antisymmetric).
- Mutual refinement does not imply equal behaviour sets: a system with behaviours goesWrong [] and terminates [] 0 and a system with only goesWrong [] refine each other, because goesWrong [] is improved by every behaviour (Toy.Sim.Boundary.mutual_refinedBy_different_behaviors).
- Neither Improves nor RefinedBy is symmetric (Toy.Sim.Cex.cex_improves_not_symmetric, Toy.Sim.Cex.cex_refinedBy_not_symmetric).
- `RefinedBy` and `HasBehavior` ignore runs that emit infinitely many events — not only in targets with no modelled behaviour at all (Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior), but also in targets that have modelled behaviours plus a run that emits events forever: `DoneOrChatter` has exactly the behaviours of `Done 0` and refines it although one of its runs emits the event 0 forever (Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs). So neither `RefinedBy L₁ L₂` nor `∀ b, HasBehavior L₂ b ↔ HasBehavior L₁ b` constrains executions of L₂ that emit infinitely many events.
- Toy model: one event per step (`Option E`), no memory model, no global environment or symbol tables; nothing here is a statement about a production compiler.

#### Non-claims of `cex-no-measure-infinite-stuttering`

- Shows that the named hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.
- Well-foundedness of the index order is shown necessary only within this step-diagram formulation; other ways of ruling out infinite stuttering in the literature (for example the 'asynchronous progress' simulations of Cho et al., PACMPL 7(OOPSLA2), 2023) are not covered or compared here.
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-going-wrong-not-preserved`

- Shows that the named hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.
- Model-specific limitation, recorded separately: in this model a going-wrong source can even be forward-simulated by a target with no behaviour at all (Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior: the target emits events forever), so CompCert's `forward_simulation_behavior_improves` ('some target behaviour improves on each source behaviour') has no counterpart here; CompCert's `program_behaves_exists` (common/Behaviors.v, line 264) relies on behaviours with infinitely many events, which are omitted.
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-naive-lexicographic-order`

- Shows that this particular simpler order fails for this composite relation, not that no other order could work.
- Escape hatch: the transitive closure in `compOrd` matters only when ord₂ is not transitive (as for `succOrd` in Toy.Sim.Cex.cex_comp_naive_lex_order_fails); when ord₂ is transitive (for example `<` on `Nat`), `compOrd` coincides with the plain lexicographic order (Toy.Sim.compOrd_iff_lex_of_transitive, Toy.Sim.Cex.compOrd_iff_naiveCompOrd_of_transitive).
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-non-receptive-source`

- Shows that the named hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.
- The source here is receptive for Eq but the target is determinate only for AnyInput: receptiveness for a smaller relation than the target's is not enough. (If M₂ ⊆ M₁ the general theorem applies, by Toy.Sim.Determinate.mono.)
- `Receptive` and `Determinate` quantify over all states, including unreachable ones. Nondeterminism confined to unreachable states need not break the conclusion (Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism). Whether the theorem holds in general with both conditions restricted to reachable states (or to an invariant) is not proved in this package.
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-determinacy-clauses-necessary`

- Shows that the named hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.
- The two-initial-states counterexample uses a target initial state that is related to no source state; it does not show that `InitDeterminate` is needed when the forward initial clause is strengthened to cover every initial target state.
- `Receptive` and `Determinate` quantify over all states, including unreachable ones. Nondeterminism confined to unreachable states need not break the conclusion (Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism). Whether the theorem holds in general with both conditions restricted to reachable states (or to an invariant) is not proved in this package.
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-refinement-not-symmetric`

- Shows only that symmetry fails in these instances; it says nothing about which other pairs refine each other.
- RefinedBy also fails antisymmetry, and mutual refinement does not give equal behaviour sets (Toy.Sim.Boundary.refinedBy_not_antisymmetric, Toy.Sim.Boundary.mutual_refinedBy_different_behaviors).
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

#### Non-claims of `cex-inclusion-needs-source-never-goes-wrong`

- Shows that the named hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.
- The hypothesis that cannot be dropped is whole-program NeverGoesWrong; the per-state condition Safe used inside backward simulations is a different, much weaker property.
- The systems are toy systems chosen for minimality; nothing is claimed about real languages.

### Escape hatches

Ways in which a result can still be applied, or a counterexample avoided, when a hypothesis is weakened (each backed by a proved Lean fact where one is named):

- (`step-diagrams-compose`) Escape hatch: the transitive closure in `compOrd` matters only when ord₂ is not transitive (as for `succOrd` in Toy.Sim.Cex.cex_comp_naive_lex_order_fails); when ord₂ is transitive (for example `<` on `Nat`), `compOrd` coincides with the plain lexicographic order (Toy.Sim.compOrd_iff_lex_of_transitive, Toy.Sim.Cex.compOrd_iff_naiveCompOrd_of_transitive).
- (`flip-forward-to-backward`) Escape hatch (different matching relations): the source and target need not use literally the same relation; if the source is receptive for M₁, the target determinate for M₂, and M₂ ⊆ M₁, then the target is determinate for M₁ (Toy.Sim.Determinate.mono) and the theorem applies with M := M₁. No algebraic axiom on M appears in the statement, but determinacy constrains M on the target's events: M is reflexive on every event the target can emit and symmetric on any two events offered by the same target state (Toy.Sim.StepLabelsMatch.refl_symm); determinacy of an event-emitting target is impossible for an irreflexive M. Receptiveness for a smaller relation is not enough: in Toy.Sim.Cex.cex_flip_nonreceptive_source the source is receptive for Eq while the target is determinate only for AnyInput.
- (`pipeline-end-to-end-refinement`) Escape hatch for mixed pipelines: a pass verified only by a backward simulation cannot be a link of `FSimChain`, but it yields `RefinedBy` (Toy.Sim.backwardSim_gives_refinedBy), and `RefinedBy` is transitive (Toy.Sim.RefinedBy.trans), so such passes compose end to end with a forward-simulated segment that has been flipped once.
- (`pipeline-end-to-end-refinement`) Escape hatch (different matching relations): the source and target need not use literally the same relation; if the source is receptive for M₁, the target determinate for M₂, and M₂ ⊆ M₁, then the target is determinate for M₁ (Toy.Sim.Determinate.mono) and the theorem applies with M := M₁. No algebraic axiom on M appears in the statement, but determinacy constrains M on the target's events: M is reflexive on every event the target can emit and symmetric on any two events offered by the same target state (Toy.Sim.StepLabelsMatch.refl_symm); determinacy of an event-emitting target is impossible for an irreflexive M.

### Unknown and not examined

- **Unknown (not examined): weaker final-state clause.** `FSimFinal` requires the target state related to a final source state to be final itself. Whether the flip lemma (and hence end-to-end refinement) still holds when `FSimFinal` is weakened to "the related target state reaches, by silent steps, a final state with the same result" was not examined.
- **Unknown: receptiveness and determinacy restricted to reachable states.** Both conditions quantify over all states. Nondeterminism confined to unreachable states need not break the flip conclusion (`Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism`, one instance), but whether the flip lemma holds in general with both conditions restricted to reachable states (or to an invariant) is not proved.
- **Not examined: behaviours with infinitely many events (reactive traces).** They are not modelled. A system whose every run emits events forever has no behaviour, `RefinedBy` and `HasBehavior` do not constrain such runs (`Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior`, `Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs`), and CompCert's `forward_simulation_behavior_improves` ("some target behaviour improves on each source behaviour") has no counterpart here (a going-wrong source can be forward-simulated by a target with no behaviour at all, `Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior`). Adding infinite-trace behaviours would change these facts; that model was not examined.
- **Not examined: multi-event steps.** Steps carry at most one event; CompCert's `single_events` conditions, `atomic` construction (`common/Smallstep.v` line 1924), `factor_forward_simulation` (line 2004) and `strongly_receptive` (line 2130) are not modelled, and no claim is made about whether receptiveness and determinacy suffice in a multi-event semantics.
- **Not shown: necessity of `InitDeterminate` under a stronger forward initial clause.** The two-initial-states counterexample uses a target initial state related to no source state; whether `InitDeterminate` is still needed when the forward initial clause is strengthened to cover every initial target state is not shown.
- **Not examined: composition of backward simulations** (CompCert's `compose_backward_simulation`, `common/Smallstep.v` line 1566, assumes `single_events L3`; no counterpart is stated here) and the reverse implication "backward simulation ⇒ forward simulation for a deterministic source". Mixed pipelines are covered only at the level of refinement, through `Toy.Sim.RefinedBy.trans`.
- **Not examined: separate compilation, linking, open or contextual simulations, concurrency, memory models.** The further-reading list under **Evidence** names work on these topics; none of it is cited as prior art for a specific result.
- **No separation claimed between the measure form and the indexed form** of forward simulation: `Toy.Sim.isForwardSim_measure_iff` characterises the measure form (a `Nat`-valued measure on source states, covering stuttering bounds of order type at most ω) as an instance of the indexed form; it is not claimed that some pass has an indexed simulation but no measure-form one.
- **Not claimed: anything about timing, resource use, liveness beyond the modelled behaviours, or hyperproperties** such as noninterference; refinement may replace termination by divergence for a source that never goes wrong (`Toy.Sim.Boundary.refinedBy_may_drop_termination`).

### Tightness status

All 72 ledgered hypotheses of the 13 theorem cards are `tight`, each with a named, fully proved counterexample theorem stating "all other hypotheses hold and the conclusion fails". No hypothesis is labelled `harmless` or `unknown` (0 such entries). A counterexample shows that a hypothesis cannot simply be dropped; it does not show that the conclusion fails whenever the hypothesis fails.

### Formulations found false and replaced

The following formulations were considered while fixing the statements and are **false in this model**; they were replaced by the statements above. None of the published statements was found false, and no statement was dropped: all five core results were proved as stated.

1. **"A forward simulation maps every source behaviour to a target behaviour that improves on it"** (the shape of CompCert's `forward_simulation_behavior_improves`) is false here because behaviours with infinitely many events are not modelled: `Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior` gives a forward simulation from a stuck source to a target that has no behaviour at all. Replacement: preservation of terminating and silently diverging behaviours (`terminating-behaviours-preserved`, `silent-divergence-preserved`), plus the partial-run theorem for the going-wrong case (`partial-run-simulated`).
2. **"Backward simulation ⇒ refinement" with going wrong defined only as "stuck in a non-final state"** is false for the CompCert-shaped initial-state clauses: a source with no initial state would have no behaviour at all, both initial clauses hold vacuously, and the target is unconstrained. Replacement: the convention that a program with no initial state has the behaviour `goesWrong []` (part of `HasBehavior`, following CompCert's `program_goes_initially_wrong`).
3. **Composite order without transitive closure.** The plain lexicographic order on `I₂ × I₁` does not make the composite step diagram hold in general (`Toy.Sim.Cex.cex_comp_naive_lex_order_fails`, with the non-transitive successor order); it does when `ord₂` is transitive (`Toy.Sim.compOrd_iff_lex_of_transitive`).
4. **Receptiveness for a smaller relation than the target's.** A flip lemma with independent matching relations for source and target is false; the same `M` (or `M₂ ⊆ M₁` via `Toy.Sim.Determinate.mono`) is needed (`Toy.Sim.Cex.cex_flip_nonreceptive_source`).

## Evidence

### Kernel-check record

* Toolchain: `leanprover/lean4:v4.34.1` (Git tag `v4.34.1` of `leanprover/lean4`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, resolved through the GitHub API on 2026-11-20). Core library only; no Mathlib; no Lake dependencies.
* `lake build` of `lean/` succeeds with no errors and no `sorry` warnings. No Lean source contains `sorry`, `admit`, `native_decide`, an `axiom` or `opaque` declaration, `implemented_by`, `@[extern]`, `unsafe`, or `debug.skipKernelTC`.
* Axiom audit (Lean's `collectAxioms` over every non-internal declaration of the library modules `ToySim.*`, 674 declarations): every declaration depends on a subset of `propext`, `Classical.choice`, `Quot.sound`. The full per-declaration list is `audit/axioms.json`.
* Statement hashes: for every Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (the `repr` of the type, and of the value for non-theorems, of every package-local constant reachable from the statement, sorted, one per line; theorem bodies are excluded, so the hashes do not depend on proofs). These are the values below.
* Proof structure: the five core results (`fsimInit_fsimStep_partial_run_simulated`, `wf_fsimInit_fsimStep_preserve_diverges`, `fsimStep_comp`, `forwardSim_receptive_determinate_gives_backwardSim`, `backwardSim_gives_refinedBy`) are proved in `lean/ToySim/Statements.lean` using auxiliary lemmas and proof-internal definitions in `lean/ToySim/ProofAux.lean` (namespace `Toy.Sim.ProofAux`); all other theorems of `Statements.lean` are derived from them; `lean/ToySim/Unfolded.lean` derives each unfolded restatement from its folded statement. Observed on 2026-11-20.

#### Per-name record (every name referenced by `results.json`)

| Lean name | Role(s) | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Sim.Cex.cex_bsim_without_final_clause` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.final : BSimFinal L₁ L₂ R` | `propext` | `2cc99a15c8fc6460325ff3f793f553ef3ce622f7fb75344bfca32871edac762d` | `7c0738ba30105bee75413500b840f4f6492b4f399d410175c95020eb8e175eb7` (33) |
| `Toy.Sim.Cex.cex_bsim_without_initExists` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.initExists : BSimInitExists L₁ L₂` | `propext` | `242f243ddc5a7cf3724103848df9e73653bca800dbdc6d1756dded5faaa1fe3c` | `5ffb949cea97a7ee8d37645b4059972430cead2d6fe20743dd408a7064ca3b4e` (34) |
| `Toy.Sim.Cex.cex_bsim_without_initMatch` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.initMatch : BSimInitMatch L₁ L₂ R` | `propext` | `21f910a47e38105320e17389791d81b86e497c7c864011da2bf006ce745bf629` | `e41e624edc1399089fd00191c167580a7fb873dddfe4e7718bfa5ad5f84f0d0e` (33) |
| `Toy.Sim.Cex.cex_bsim_without_progress` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.progress : BSimProgress L₁ L₂ R` | `propext` | `2f15c20dcea484ea954fdfc900c5ece9ac0789edac730679dd16557c0fbd768d` | `866feb81bae4afd1dc4a6b4a076ee906baa1790c9994a83ae6ba0c8d448be1e5` (34) |
| `Toy.Sim.Cex.cex_bsim_without_step_diagram` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.step : BSimStep L₁ L₂ ord R` | `propext` | `988fe9a7258a6430d67c6b8602c1f36d4d48c5202ab1d2a3af28dd6fc275d46f` | `c96e41565feff0c7e3d9250de178733526739448cbad217d01a9e88478c5a766` (33) |
| `Toy.Sim.Cex.cex_bsim_without_wf` | backward-sim-gives-refinement: counterexample for `IsBackwardSim.wf : WellFounded ord` | `propext` | `1a3aeb99228ade2290a010abc0b18c952d9508c1a212fbf9e2fed1608170e2af` | `87c24023abe2540b234f1dbd7ee7a876db928cecf82eefe1765f6efab0b41bc7` (35) |
| `Toy.Sim.Cex.cex_compOrd_wf_needs_both` | forward-simulations-compose: counterexample for `WellFounded ord₁ (first pass; isForwardSim_comp and compOrd_wf)`; forward-simulations-compose: counterexample for `WellFounded ord₂ (second pass; isForwardSim_comp and compOrd_wf)` | none | `9f69b97debad45b9793a52cab574a7b2a09df0b5200b23da14dcfa5e44f929f0` | `76c357f7acee21f4ce53adaa91034dc87ffe52b0da9088759f1d09d6d3821b43` (3) |
| `Toy.Sim.Cex.cex_comp_naive_lex_order_fails` | cex-naive-lexicographic-order: result | `Quot.sound`, `propext` | `b3120349eb88f26e421e0079ad30597d5caeafff73f78fb09042c0f7c5704ae0` | `7ba9a58e81fd296a3b5f325c880fc0aaafeba29ce30afb7dc813a5592bde761c` (31) |
| `Toy.Sim.Cex.cex_comp_without_first_final` | forward-simulations-compose: counterexample for `FSimFinal L₁ L₂ R₁ (isForwardSim_comp and fsimFinal_comp)` | `propext` | `be748e5b65439bd4695e5d647993d10eb063d34e67be930751c8f56f75ddc023` | `9951a41840416098279c50359bf07129c552171b7d787beca2f057fcba5c7c43` (23) |
| `Toy.Sim.Cex.cex_comp_without_first_init` | forward-simulations-compose: counterexample for `FSimInit L₁ L₂ R₁ (isForwardSim_comp and fsimInit_comp)` | `propext` | `ae3ac2ab964d6b5e397ae0fe6ba4f0f11d786ecaa69910a123a2bbc57508c055` | `2eeda37a2cfa88131745bfb09a18a7c96d072c77088119b886e2961688147936` (24) |
| `Toy.Sim.Cex.cex_comp_without_first_step_diagram` | forward-simulations-compose: counterexample for `FSimStep L₁ L₂ ord₁ R₁ (isForwardSim_comp)`; step-diagrams-compose: counterexample for `FSimStep L₁ L₂ ord₁ R₁` | `propext` | `b8b9086599b7c4f1ecc11237b0e8902cfd4142e2bf6d6743f46220d73672aea9` | `9227fe3935d110b13a1cc6a4cc5af40836429f82da09b769076ccd1652078e51` (24) |
| `Toy.Sim.Cex.cex_comp_without_first_wf` | forward-simulations-compose: counterexample for `WellFounded ord₁ (first pass; isForwardSim_comp and compOrd_wf)` | `propext` | `0b7e963ce0224d11452d14ff0e0fa6e38857914ef3fffd45b3a0b00616a72a3a` | `0b49d79130600aabe6aa5e737425607ad1e909334d76e5dbeebeeab87ff3be9a` (23) |
| `Toy.Sim.Cex.cex_comp_without_second_final` | forward-simulations-compose: counterexample for `FSimFinal L₂ L₃ R₂ (isForwardSim_comp and fsimFinal_comp)` | `propext` | `653df71cfc5ad3e7b1ea34edbd86b644b2b53bc57d6a4d58cbaa74e544fe251f` | `9951a41840416098279c50359bf07129c552171b7d787beca2f057fcba5c7c43` (23) |
| `Toy.Sim.Cex.cex_comp_without_second_init` | forward-simulations-compose: counterexample for `FSimInit L₂ L₃ R₂ (isForwardSim_comp and fsimInit_comp)` | `propext` | `79ee2c8c4c678ab1fef147565b3f9c6048dc2165d5607cc96e68340b7c89ee9c` | `2eeda37a2cfa88131745bfb09a18a7c96d072c77088119b886e2961688147936` (24) |
| `Toy.Sim.Cex.cex_comp_without_second_step_diagram` | forward-simulations-compose: counterexample for `FSimStep L₂ L₃ ord₂ R₂ (isForwardSim_comp)`; step-diagrams-compose: counterexample for `FSimStep L₂ L₃ ord₂ R₂` | `propext` | `5abe0b45bd8d18fc8afd8eb8df6b0db2e64ff9ee85e74c274233d6c01f66dd23` | `9227fe3935d110b13a1cc6a4cc5af40836429f82da09b769076ccd1652078e51` (24) |
| `Toy.Sim.Cex.cex_comp_without_second_wf` | forward-simulations-compose: counterexample for `WellFounded ord₂ (second pass; isForwardSim_comp and compOrd_wf)` | `propext` | `5f3f99b16de3e4bc9d108b950d69645e954efebbda0439e3c81a676851dc1631` | `0b49d79130600aabe6aa5e737425607ad1e909334d76e5dbeebeeab87ff3be9a` (23) |
| `Toy.Sim.Cex.cex_flip_nonreceptive_source` | cex-non-receptive-source: result; flip-forward-to-backward: counterexample for `Receptive M L₁ (first theorem; automatic for M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `2ac0784ab4a3bc0e31ca0c18c84329b9ede21cdde08441285a1d733de4edfe78` | `c12076fdc4448685a16ff1093e29660c1a938d75aa1f193bc3580d08ead56e87` (60) |
| `Toy.Sim.Cex.cex_flip_target_event_labels_mismatch` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause labels (StepLabelsMatch; both theorems, the second at M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `288bc9f33245748674632d82622f27469c9822b1ce9e8de83ad7b22bd321d7c0` | `214cad4c86fec9c3b5533289a378d39348ddf2ba6c24c0d33b3d39fbdc35f20c` (57) |
| `Toy.Sim.Cex.cex_flip_target_final_state_steps` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause finalNoStep (FinalNoStep)` | `Classical.choice`, `Quot.sound`, `propext` | `c7ed1ba6c31a7e4cfe807ac63f1bbcdfe0b2c92917012bf1a66374f3526bb354` | `08c96e97259118108b6dd5afd1114427416f4671cc0a453cb5abaaa1ea5d3d85` (53) |
| `Toy.Sim.Cex.cex_flip_target_labels_mismatch` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause labels (StepLabelsMatch; both theorems, the second at M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `ee72ea9308af1154d77e86d88f1ec7a464871f51feb8a28686653928388ad112` | `214cad4c86fec9c3b5533289a378d39348ddf2ba6c24c0d33b3d39fbdc35f20c` (57) |
| `Toy.Sim.Cex.cex_flip_target_not_functional` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause functional (StepFunctional)` | `Classical.choice`, `Quot.sound`, `propext` | `efb8b483a86d1a385f97b27362a6e8a223a84de11d433213cbbfa3ef398dada4` | `214cad4c86fec9c3b5533289a378d39348ddf2ba6c24c0d33b3d39fbdc35f20c` (57) |
| `Toy.Sim.Cex.cex_flip_target_two_initial_states` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause init (InitDeterminate)` | `Classical.choice`, `Quot.sound`, `propext` | `433d4217231dc7bb4f0742ae60cbcbfa24f3d39a93eaafbe9e5c7f0dbfb07dce` | `5cfad22fc2de1c6e5cc6a1e661cd6d7a2d9afba811e1f15b00fec2350a143b99` (53) |
| `Toy.Sim.Cex.cex_flip_target_two_results` | cex-determinacy-clauses-necessary: result; flip-forward-to-backward: counterexample for `Determinate M L₂, clause finalDet (FinalDeterminate)` | `Classical.choice`, `Quot.sound`, `propext` | `34060ebb13337f1b13b51ff0db0d49e98aa7f45459a03cdef9d1bde706be7b6b` | `c673dea5da394c367e2e26787f4f631f783bd0ca0e7f8fd741de6b89e5d2624d` (53) |
| `Toy.Sim.Cex.cex_flip_without_final_clause` | flip-forward-to-backward: counterexample for `IsForwardSim L₁ L₂ ord R, clause final (both theorems)` | `Classical.choice`, `Quot.sound`, `propext` | `d76921cef83465740e8c91efa7cabf9c91095ab5b1cfae5000651a59e81a4ef6` | `3098f1b14ab914560eab687bcfcb6fbe268c6dbb04f1bcb86841e6c34135ce98` (51) |
| `Toy.Sim.Cex.cex_flip_without_init_clause` | flip-forward-to-backward: counterexample for `IsForwardSim L₁ L₂ ord R, clause init (both theorems)` | `propext` | `106cba64cb7f966dab12f6d61514b824066dba5a4a6e082560ba2da0a80e25e3` | `e2e96cff432db145aa5c37fcbba2b22be798bc50f2869e74ebda2f850092f25d` (52) |
| `Toy.Sim.Cex.cex_flip_without_step_diagram` | flip-forward-to-backward: counterexample for `IsForwardSim L₁ L₂ ord R, clause step (both theorems)` | `Classical.choice`, `Quot.sound`, `propext` | `e805d6a10542283edb65b9fe3e0cc78b5fb9b22936d2c8137e933eff6908d26a` | `fae736354ead5e0e3b88cb963d3358236aa999f16417f1561c57af710fbc05f8` (52) |
| `Toy.Sim.Cex.cex_flip_without_wf` | flip-forward-to-backward: counterexample for `IsForwardSim L₁ L₂ ord R, clause wf (both theorems)` | `Classical.choice`, `Quot.sound`, `propext` | `3418c14f2314a16c41db2d5749b917b6fc5dd423d60d4342912f30984deee8b5` | `e2da5359077fec8bfd127fc09ecf8b20f666d4b4daf69901bc185379c82dfa9c` (53) |
| `Toy.Sim.Cex.cex_forwardSim_goesWrong_not_preserved` | cex-going-wrong-not-preserved: result; forward-sim-preserves-non-wrong-behaviours: counterexample for `∀ t, b ≠ .goesWrong t (both theorems)` | `propext` | `089eebdf7aa6a8c8f3a7518cb9dab3072e56a22b29645ea25782be225e1b0fde` | `5f43d86db3214e53c60049068eebf79801feab09db211b137f7e113f3b290508` (34) |
| `Toy.Sim.Cex.cex_fsim_without_final_clause` | forward-sim-preserves-non-wrong-behaviours: counterexample for `IsForwardSim L₁ L₂ ord R, clause final (single-pass theorem)`; terminating-behaviours-preserved: counterexample for `FSimFinal L₁ L₂ R` | `propext` | `3c80398ec7efab6b8fbdedf1663edd4d419c66d265e3eb3abf4bcbc7054df3b5` | `6606cbb7117481f5dc495355167851b980d52cb0595abb163e74681753df66d3` (27) |
| `Toy.Sim.Cex.cex_fsim_without_init_clause` | forward-sim-preserves-non-wrong-behaviours: counterexample for `IsForwardSim L₁ L₂ ord R, clause init (single-pass theorem)`; partial-run-simulated: counterexample for `FSimInit L₁ L₂ R`; terminating-behaviours-preserved: counterexample for `FSimInit L₁ L₂ R` | `propext` | `12c5ac4be64b21512f2c30f4d0d6b28240eb7aea4ef7a573abc0719fbdea6566` | `04862c5b423b143d5d5844a15018d02e6cb23931de94af7ca51383d66e6651b7` (28) |
| `Toy.Sim.Cex.cex_fsim_without_init_clause_diverges` | silent-divergence-preserved: counterexample for `FSimInit L₁ L₂ R` | `propext` | `743d32dc319a34587641f74662e454f39a1661a112489f6aa993ac280ae5afd2` | `df4ed3d082bc0e8f2448a656094e6c616a02ae12b574f308eaafdb6d092b3502` (27) |
| `Toy.Sim.Cex.cex_fsim_without_step_diagram` | forward-sim-preserves-non-wrong-behaviours: counterexample for `IsForwardSim L₁ L₂ ord R, clause step (single-pass theorem)`; partial-run-simulated: counterexample for `FSimStep L₁ L₂ ord R`; terminating-behaviours-preserved: counterexample for `FSimStep L₁ L₂ ord R` | `propext` | `bd5e69c5e4554fb402ae4d2af2ae27f00b34883812d7adecc6c981b9094ced06` | `de250fd2a29aa8b96a357dbc4ef060440f4342f4627fe3d4b9b4d160d09118f5` (27) |
| `Toy.Sim.Cex.cex_fsim_without_step_diagram_diverges` | silent-divergence-preserved: counterexample for `FSimStep L₁ L₂ ord R` | `propext` | `c4eb186939b6d54d3741d576dc918d7dc6107f257aaed54192c418031bce4d1f` | `c5965acbc0b54a451f3e002e484c6ad784bab9c9e91195bbde1323e4398ec776` (26) |
| `Toy.Sim.Cex.cex_fsim_without_wf_divergence_not_preserved` | cex-no-measure-infinite-stuttering: result; forward-sim-preserves-non-wrong-behaviours: counterexample for `IsForwardSim L₁ L₂ ord R, clause wf (single-pass theorem)`; silent-divergence-preserved: counterexample for `WellFounded ord` | `propext` | `bc19b4198607a62f74818c0b843a31174c80cb60460da3d5e77b621f7a0f6964` | `fb30548f92c49b9683a89e910d457854cea305f13f7e61ac0e95f44ba39fde21` (29) |
| `Toy.Sim.Cex.cex_improves_antisymm_needs_both` | refinement-is-a-preorder: counterexample for `Improves b₁ b₂ (Improves.antisymm)`; refinement-is-a-preorder: counterexample for `Improves b₂ b₁ (Improves.antisymm)` | none | `a77b3e999be367b81d8e0b040fd8d1514d99d2b36a5cdc310d4d718f37bc5b65` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.Cex.cex_improves_not_symmetric` | cex-refinement-not-symmetric: result | none | `6f7bb89d357233da0cef20c107647ab2f555ab1c1497821aea44dfb09d3da156` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.Cex.cex_improves_trans_needs_both` | refinement-is-a-preorder: counterexample for `Improves b₁ b₂ (Improves.trans)`; refinement-is-a-preorder: counterexample for `Improves b₂ b₃ (Improves.trans)` | `propext` | `aac93420e8094993fa1a152c09349374331813bcfa3dbd15dbc90c17bf1fc658` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.Cex.cex_inclusion_needs_source_never_goes_wrong` | cex-inclusion-needs-source-never-goes-wrong: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `NeverGoesWrong L`; refinement-is-inclusion-when-source-never-goes-wrong: counterexample for `NeverGoesWrong L₁ (both theorems)` | `propext` | `1acdc90781060ad66eda924142663904121fc0c42ef6e50b70d55cba252f131e` | `e3d9a5a1fbb0bd48622cf1968d0a23db0e909428e6f0f1190a86323a465127c6` (57) |
| `Toy.Sim.Cex.cex_inclusion_without_refinement` | cex-inclusion-needs-source-never-goes-wrong: result; refinement-is-inclusion-when-source-never-goes-wrong: counterexample for `IsBackwardSim L₁ L₂ ord R (second theorem)`; refinement-is-inclusion-when-source-never-goes-wrong: counterexample for `RefinedBy L₁ L₂ (first theorem)` | `propext` | `0e23f7734c2c307cceacffbdd6dbfc81ad320da1887082052703c5f7f651a36f` | `f90113790d4d19c590ffbd0ec0c18e98f1f21e541d66382affc816a4cfe40073` (23) |
| `Toy.Sim.Cex.cex_inclusion_without_target_behavior` | refinement-is-inclusion-when-source-never-goes-wrong: counterexample for `HasBehavior L₂ b (both theorems)` | `propext` | `92c3b44f637b8465be3ed3aa03ee80bb85ac489421a9adcf83b68e51d13ede0f` | `74dc2973d5351250f1787d073263e6bc6bab8f5bf049bedaa5cf48b201d196de` (37) |
| `Toy.Sim.Cex.cex_partial_run_from_non_initial_state` | partial-run-simulated: counterexample for `L₁.init s₀` | none | `9d566f31157a228d6b32d12c85b4ac794207b01def64822d4ebe9645a1011f00` | `dac8785a59f3781ab91823b8e7128defeb7106fd3450aafe84e3a42cd9670750` (17) |
| `Toy.Sim.Cex.cex_partial_run_without_source_run` | partial-run-simulated: counterexample for `Star L₁ s₀ t s` | `propext` | `0c238d37b87b0f74d1c61e9108d298b16b6f3e8c2c28fcd16e3e2e9d562bf52e` | `7680abafff91a0a2579304fd9e0a27d8b899c3df5c9019250c04b798aa5b4c4d` (16) |
| `Toy.Sim.Cex.cex_pipeline_last_event_labels_mismatch` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause labels`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause labels (both theorems, the second at M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `23ac3a33a003eb9295d15f6eeeff24aca9c1bbd0f9e1e95d486153991722cd8c` | `1dac0a32b0d3585d43007fc2240e10b88d038ea60a1500f7583640e2175f671f` (50) |
| `Toy.Sim.Cex.cex_pipeline_last_final_state_steps` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause finalNoStep`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause finalNoStep` | `Classical.choice`, `Quot.sound`, `propext` | `b66d68802418f09419195a9641d8f67b485005897c41f890ed38df3d3114d603` | `461a4bfc19e83c6e8c18c237092d6a43a20b00526dfb24a7b90163d8a33c3137` (46) |
| `Toy.Sim.Cex.cex_pipeline_last_labels_mismatch` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause labels`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause labels (both theorems, the second at M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `aa796c684d1b42741a3d1586e491e9a105a6f881699c657e34cefc1fc32bfbfc` | `1dac0a32b0d3585d43007fc2240e10b88d038ea60a1500f7583640e2175f671f` (50) |
| `Toy.Sim.Cex.cex_pipeline_last_not_functional` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause functional`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause functional` | `Classical.choice`, `Quot.sound`, `propext` | `71677f3692042849fd66534578ba668dce4b1ddadc230c5f5e1f520bf18e165b` | `1dac0a32b0d3585d43007fc2240e10b88d038ea60a1500f7583640e2175f671f` (50) |
| `Toy.Sim.Cex.cex_pipeline_last_two_initial_states` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause init`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause init` | `Classical.choice`, `Quot.sound`, `propext` | `f9905e7ef1dd123da6f7dee30e0289712aa1ac12c811f7c1878ef63068cae479` | `9fb12d183f0703c0ca0c2fafe147152ab78d5aaee5d0867109bc44a1d725587a` (46) |
| `Toy.Sim.Cex.cex_pipeline_last_two_results` | cex-determinacy-clauses-necessary: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Determinate M L', clause finalDet`; pipeline-end-to-end-refinement: counterexample for `Determinate M L', clause finalDet` | `Classical.choice`, `Quot.sound`, `propext` | `685a99c070e4070d19d61362481b4758e5b4756bd5d85a9ac91c6849961fd240` | `b9c7c5bd2d0debfcaa0af33d25f3ea1e6d820ad8f9db82af41aafe49c8534198` (46) |
| `Toy.Sim.Cex.cex_pipeline_nonreceptive_first` | cex-non-receptive-source: result; pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `Receptive M L`; pipeline-end-to-end-refinement: counterexample for `Receptive M L (first theorem; automatic for M = Eq)` | `Classical.choice`, `Quot.sound`, `propext` | `5784ef762159fd701f2470305b0015b183872330634c44d514e6cceee4184963` | `95b8654a0e132b9eb1c9acd3272f8df68d9de782f00040a30cfe381905c1707a` (53) |
| `Toy.Sim.Cex.cex_pipeline_preserves_without_chain` | forward-sim-preserves-non-wrong-behaviours: counterexample for `FSimChain L L' (chain theorem)` | `propext` | `b082ba14f527d4f50f9757804387987ae5848df1dbe4e0c0168a06172922d051` | `6414467d3d21d627dc414341d69b47e03455720822c9fe55b9b9ae65ed5d5762` (31) |
| `Toy.Sim.Cex.cex_pipeline_without_chain` | pipeline-behaviour-equality-when-first-never-goes-wrong: counterexample for `FSimChain L L'`; pipeline-end-to-end-refinement: counterexample for `FSimChain L L' (both theorems)` | `propext` | `5bf836d99509588d781fb901b63f148089dea34ee755b88b350b7ee0ed011427` | `d8326e63cb50bcf152b88aeed47cae541e407428350f2429b62dc51d906b8fe5` (47) |
| `Toy.Sim.Cex.cex_preservation_without_source_behavior` | forward-sim-preserves-non-wrong-behaviours: counterexample for `HasBehavior L₁ b / HasBehavior L b (both theorems)`; silent-divergence-preserved: counterexample for `HasBehavior L₁ (.diverges t)`; terminating-behaviours-preserved: counterexample for `HasBehavior L₁ (.terminates t r)` | `propext` | `dd9aa0a6c5770eebb41d1bd158480212c45e267eb3c681bf08fa4226f4f58c31` | `167822a6c1caeed1997914530e08a8c9466c48b3240d549c086e4aad9a9e8c69` (33) |
| `Toy.Sim.Cex.cex_refinedBy_not_symmetric` | cex-refinement-not-symmetric: result | `propext` | `6928fe9daf5d5046bff3ad514ad0bb0d6667e738e614717a96e5e15402a5439a` | `5035cb0534fc2a892a510b7460f9b849382f66e164587289052386a6df120742` (26) |
| `Toy.Sim.Cex.cex_refinedBy_trans_needs_both` | refinement-is-a-preorder: counterexample for `RefinedBy L₁ L₂ (RefinedBy.trans)`; refinement-is-a-preorder: counterexample for `RefinedBy L₂ L₃ (RefinedBy.trans)` | `propext` | `d54ab69b12a841804a18bf6a3e211ed945fd97fec89d8d5c7ac83e689688827b` | `8b4887d96b81a6a4254ba5a12a2335bd7e75a1de1cace759141e055402c1cdc8` (25) |
| `Toy.Sim.Examples.fsimChain_neg` | pipeline-collapses-to-one-forward-simulation: counterexample for `IsForwardSim L₁ L₂ ord R (fsimChain_of_isForwardSim)` | `propext` | `47ca06a145e9e70ec7494fbcba0b51898b4bd571fd3d5d5b9c8ef23b73fd280e` | `bf3acde0d8c525ea8d4e737c988c864c06128f673cfd2bdf3a3c6bbd9bad08ba` (21) |
| `Toy.Sim.Examples.fsimChain_pos` | pipeline-collapses-to-one-forward-simulation: non-vacuity witness | `propext` | `a7ac16fb7003af05cedb752805f330bc732757359229e1939bc0b24130dd98d2` | `75f99996dc6cb4287a526979c827bc4b54169b370933a0f8d5ff6f37521a2477` (36) |
| `Toy.Sim.Examples.isForwardSim_neg` | pipeline-collapses-to-one-forward-simulation: counterexample for `FSimChain L L' (fsimChain_collapse)` | none | `6d509a7fd6d497abe21739a786adf2a5e6e7459b01cfb8c9a1c578f134378f26` | `3138ebea88b6db0500be59daca1a4c38c6654516d4da4e6396483030e9ca5651` (19) |
| `Toy.Sim.Examples.isForwardSim_pos` | pipeline-collapses-to-one-forward-simulation: non-vacuity witness | `propext` | `7b4a7ecc0486dba23b8a05c680abacb58b5c238d9fcf40c74416f2063c5ab907` | `01da51471cd61bb14048f0deb08c54481a1c641ccb2c882f46c0a0625e1fa68c` (37) |
| `Toy.Sim.Examples.nonvacuous_backwardSim` | backward-sim-gives-refinement: non-vacuity witness | `propext` | `dfbba8167c020d0ea06c62102aad8be7f7a483f4ea9f95858ec541c5362513cd` | `437a79ba960b89a66f169b86770c69a4174f44cbc19e1e4169f0986fbdcb784e` (52) |
| `Toy.Sim.Examples.nonvacuous_comp` | forward-simulations-compose: non-vacuity witness; step-diagrams-compose: non-vacuity witness | `propext` | `e3b9cfa1591ca1126b1771ec79cf890bc0190712a168ff693b3eb9b2a4f988fb` | `47e785bf9c85f1d7bbb2abcea40ea4908ee5208a41900953649e735d5bcb7713` (53) |
| `Toy.Sim.Examples.nonvacuous_comp_transGen` | forward-simulations-compose: non-vacuity witness; step-diagrams-compose: non-vacuity witness | `Quot.sound`, `propext` | `d7885e3c1a2e89b4b6c978ff584a899d8d106b48366e07053eb8a051490c1e64` | `2937c5c4bfffb74ef704d1c8d2ad4bb44dbf6e1782d9d004d71bfa740e1600a2` (30) |
| `Toy.Sim.Examples.nonvacuous_deterministic_target` | flip-forward-to-backward: non-vacuity witness; pipeline-end-to-end-refinement: non-vacuity witness | `propext` | `3c5a7afb2943b90edfce53c04be74c1a3e335a407301cb129c04b7343068d368` | `c02413f2c6220f1f670f5ac854b1e367ad7f1c254f5e3b0798af501c2613f91c` (34) |
| `Toy.Sim.Examples.nonvacuous_flip` | flip-forward-to-backward: non-vacuity witness | `propext` | `c54e7989f4a2b764147e2f394e54e021b3aba9c2ff899a26b8c4feec1248b1b0` | `bd3eac2d0ba1991bcc9d8507389741c0674d999bd496c08b39b88cff9ae50625` (50) |
| `Toy.Sim.Examples.nonvacuous_flip_with_conclusion` | flip-forward-to-backward: non-vacuity witness | `propext` | `4205626726e826370c7ee9eb740512fec934a493c629f0456f01dd6d9d7b7a12` | `f721ff4d17035c1339def1aefff4a4a325387f8460ff3f54eac7620f1a996c4b` (63) |
| `Toy.Sim.Examples.nonvacuous_isForwardSim_preserves` | forward-sim-preserves-non-wrong-behaviours: non-vacuity witness | `propext` | `154890df8c7e6e60cfa954299fdacbe96abfd72d194607a535ab34c7a1785d38` | `f9928fa2c90806cfed0821bb7f846ed568f6a7b260e825083b71507d1fb4849d` (47) |
| `Toy.Sim.Examples.nonvacuous_partial_run_simulated` | partial-run-simulated: non-vacuity witness | `propext` | `5c8d02c7e15d6eac572afaf73d086b1e98b1603d9937e2ff4fd3687bc581cc49` | `f210979a5e1783397d58d934b82f2d2e9277d5f0c47e22a80089dff42e078a2d` (33) |
| `Toy.Sim.Examples.nonvacuous_pipeline` | pipeline-end-to-end-refinement: non-vacuity witness | `propext` | `9580b4fb1b5c5c84ee9ddaa21875da1750d97c41b902b96875cf40f858bbe33a` | `084eb9791afb849350b55266e09bbfa172d41daa478b9d3d4481022b322ff7be` (80) |
| `Toy.Sim.Examples.nonvacuous_pipeline_behaviors_iff` | pipeline-behaviour-equality-when-first-never-goes-wrong: non-vacuity witness | `propext` | `294d9978f7e9a097c47391ec317c84ed6adb0276fdb1df3d8ccd718ced6fff8c` | `30de7bc839e369285879fcd717381593bbabcf05fcae02c5dd945034d61f3892` (71) |
| `Toy.Sim.Examples.nonvacuous_pipeline_preserves` | forward-sim-preserves-non-wrong-behaviours: non-vacuity witness | `propext` | `01aa437b4623eb71b00126644756c182156b98fd4f31153a92a62c116fab2e6f` | `3fe0686c36b416dc1c5795c538dee5b8d080d0c458113ace613a5a5d8da246f9` (46) |
| `Toy.Sim.Examples.nonvacuous_preorder` | refinement-is-a-preorder: non-vacuity witness | `propext` | `642f299da94a445abd2d357d0eed02f5d4b11441c1c95dfe47e7529e290337d3` | `7a026fd4146b14a14a4e33a0a6ed44df9703904346d110ca5c0c4d32501136e2` (41) |
| `Toy.Sim.Examples.nonvacuous_preserve_diverges` | silent-divergence-preserved: non-vacuity witness | `propext` | `c0e02985e11621ba2d07c04e38429aaa64d8843e60afa1c5b584e02a5669106f` | `ed4a179725627b518ce2fd4353e33324fed43457d5edc6e622a1312c1d01a968` (27) |
| `Toy.Sim.Examples.nonvacuous_preserve_terminates` | terminating-behaviours-preserved: non-vacuity witness | `propext` | `54164ab083de616176dc467bfb8dad84d4cb81e9bdcf71ac6156b1820e8ac0ef` | `4f3a0dd41337c3aaa02a120e0efe01f9cbbc8fa1bfbeaff2e07e3217021dc8c9` (45) |
| `Toy.Sim.Examples.nonvacuous_refinement_inclusion` | refinement-is-inclusion-when-source-never-goes-wrong: non-vacuity witness | `propext` | `e8cfb47d741ce3366579d4ef4c2fb11bf96296646a95160e2be49a024dbe45ce` | `02b7680b9de47d85bd30679b65ef1c90b57886824bec2b492d2b7ce5ffc7a16d` (55) |
| `Toy.Sim.Examples.positive_control_diverges` | cex-no-measure-infinite-stuttering: positive control | `propext` | `7bc9e583c7889db96b298dc2492b5fffb30221bdd9bff6c9d961c36535a7cd1e` | `6bb9b7ab7842edd74cfb6be40f8b7836a84a694a69df69b06121f178c361c37f` (30) |
| `Toy.Sim.Examples.positive_control_flip` | cex-determinacy-clauses-necessary: positive control; cex-non-receptive-source: positive control | `propext` | `1aa4854c54b21ce918d9514b4719614ef402e48a60655323c739fab0670b4204` | `bfb336486ad61f4b5ef6b90566eb9e8f53530faae73a1dd1597a88fcd9af3875` (77) |
| `Toy.Sim.Improves.antisymm` | refinement-is-a-preorder: result | `Quot.sound`, `propext` | `10fd361e7251009230eb6365b34db96b068f792adc4f525f3c618e7803a7eeb8` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.Improves.refl` | refinement-is-a-preorder: result | none | `804be681c7e6fcf7f270c243292f7db4997f19a141860e0885802464d921b64c` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.Improves.trans` | refinement-is-a-preorder: result | `propext` | `821d16fe633c38f3a7a009b5f2ea41cf8a2d2efac05c409f42f43f6d418dc0ca` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.RefinedBy.refl` | refinement-is-a-preorder: result | none | `a92747964bdde5aace7447dcdb5099894c1dd43bf46686f42c234c940a122079` | `c13fe0e2b363f44517a75fa2477ec48371e540bfbaaefa77e4dca00a72f3d6ea` (24) |
| `Toy.Sim.RefinedBy.trans` | refinement-is-a-preorder: result | `propext` | `4849c1b55f037550dcd794c043e6822788a7e5fe65ebc97f405d0c0436a9e53a` | `c13fe0e2b363f44517a75fa2477ec48371e540bfbaaefa77e4dca00a72f3d6ea` (24) |
| `Toy.Sim.Unfolded.backward_sim_gives_refinement` | backward-sim-gives-refinement: result | `Classical.choice`, `Quot.sound`, `propext` | `f25434b2ad52f8ae4c5f995838e1a950c0af3930817bbd8515c33933af1aac67` | `3457a380e95c32f75ef5731b4dcd73b153cd1e25c866bdde999b98a6ccf3c9ec` (23) |
| `Toy.Sim.Unfolded.flip_forward_to_backward` | flip-forward-to-backward: result | `propext` | `717660d36568ef821a1eb495e5c5f68d3fb9e7e18fdc2c8f637f0286739b6889` | `2ddd93d92aadd0539ca52c41d5e4c3ac26c96eccda419544791ed0f99c5ba43d` (16) |
| `Toy.Sim.Unfolded.partial_run_simulated` | partial-run-simulated: result | `propext` | `e59a0702383a21ccced33b924065efaa1dbb4bb1b56df94e4bcb62d3cc1553d0` | `30a45f41983b3dd2f771d906e171a20bd3c02dad37152a9ba5eb0c0b7dd4be2d` (11) |
| `Toy.Sim.Unfolded.pipeline_end_to_end_refinement` | pipeline-end-to-end-refinement: result | `Classical.choice`, `Quot.sound`, `propext` | `8ec07dd7957b8fbfad2f0cfb1f9c500901d1072d9ab00640ea5e52456a911b01` | `2f6bfc6122b84182d716f1305d2fd9b2521ce55c553ae06118c890c16afa251e` (35) |
| `Toy.Sim.Unfolded.silent_divergence_preserved` | silent-divergence-preserved: result | `Classical.choice`, `propext` | `156d20bacb9433dd0d8d3ce67bfc602ffd049e375311382f17b1e440345fea8e` | `30a45f41983b3dd2f771d906e171a20bd3c02dad37152a9ba5eb0c0b7dd4be2d` (11) |
| `Toy.Sim.Unfolded.step_diagrams_compose` | step-diagrams-compose: result | `propext` | `75c82cdfd77dc60167a313d93b442dba0b24401ca6ce0bbec804351cef9be973` | `a006286439c214e8b25a051be7bd3e892afc31fdfa196d711de0f4f37135f52e` (10) |
| `Toy.Sim.Unfolded.terminating_behaviours_preserved` | terminating-behaviours-preserved: result | `propext` | `b898adab2dcb2803964324a49cd62df5fa533fdd842ef3ededba0e8b54711c97` | `62c7431fd46f63759e8763d236c3704193f6d1a2bfced1c21368b1e6965e2993` (12) |
| `Toy.Sim.backwardSim_gives_refinedBy` | backward-sim-gives-refinement: result | `Classical.choice`, `Quot.sound`, `propext` | `7a9edfe3f95435f140f39a88bf6dc1a2db1fb987223ccab96020caed43b98417` | `6b72c3523be028cb2ecde2930c44e0b67ada813291d42d24ac00b1b61f8783c6` (33) |
| `Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset` | refinement-is-inclusion-when-source-never-goes-wrong: result | `Classical.choice`, `Quot.sound`, `propext` | `8802312e07f849febcbc0bb75b141ce392ec241b4ead01437416fa227327f59b` | `08d1f5cb915b1f65ac5dc540a800297210bb930cdfbb03b0bf3a8f0baef51b48` (31) |
| `Toy.Sim.compOrd_wf` | forward-simulations-compose: result | none | `0efd624aa7a11c8d32f62aea6fd5beb4f7618dfa400fd4912f5e40c31d3fbbf4` | `d4d958144981a2e504a2289e25907401839efdfde71c0613109b50701951f631` (1) |
| `Toy.Sim.forwardSim_deterministic_target_gives_backwardSim` | flip-forward-to-backward: result | `propext` | `ee950f1cc513663f4ab91484520f7b5189cad9c395eb52d3dfd9c57c3cf06fee` | `c423713484fd1901b44d9afeaf400e879947932876ddda371f3fe59214d4a043` (36) |
| `Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim` | flip-forward-to-backward: result | `propext` | `c9ba7e77daf10e14327b0ebfb7a8f06cad042b8b5ee50e4732fea55906906a38` | `3ed6252a00823c027aa532750868ea6bb7341bc134091cf6c537953c982380a3` (37) |
| `Toy.Sim.fsimChain_collapse` | pipeline-collapses-to-one-forward-simulation: result | `propext` | `6d0f20a81678ae47eaeb28478825d75cc9416c42ba16640c3c6740d4a7d38381` | `146b8b31cb8fd484b1cf17f980fa3f16b71cb739aa667544d09645e2d9f5d91f` (20) |
| `Toy.Sim.fsimChain_deterministic_last_gives_refinedBy` | pipeline-end-to-end-refinement: result | `Classical.choice`, `Quot.sound`, `propext` | `4796edf9c820c05824483cbbb28e912c2db999c2efd36aa57af342a1bf41aefb` | `1d3e018888cb829e06f55dca590bb6ddbdf5c841a2461b10eefe898527b02558` (44) |
| `Toy.Sim.fsimChain_of_isForwardSim` | pipeline-collapses-to-one-forward-simulation: result | none | `f0feae98568750d1b9a206b5b89cd4b2fc3ed438f5da4552cce05338a49271da` | `146b8b31cb8fd484b1cf17f980fa3f16b71cb739aa667544d09645e2d9f5d91f` (20) |
| `Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors` | forward-sim-preserves-non-wrong-behaviours: result | `Classical.choice`, `propext` | `62a8b802af04f2c52164f609d119f4f79674c2098789f8bbc4f34f1624165ff7` | `400396e2325e0a37e38381b75161a1c522541b0b8602057d693bb49de41fb3a4` (30) |
| `Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy` | pipeline-end-to-end-refinement: result | `Classical.choice`, `Quot.sound`, `propext` | `91d903ba03e3022498f039822488e7f137cb2308fdc06ba93dd27be726cf14b3` | `838e948d84db002e88b93a111999c749e46306834cdbfc80f69393ec029ba069` (45) |
| `Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff` | pipeline-behaviour-equality-when-first-never-goes-wrong: result | `Classical.choice`, `Quot.sound`, `propext` | `995e1b5d17b594bc0bbb2b63794ec1c2271bfd727e009bd45e874c9daa6e032c` | `b73a6b582cb99a9938dfd3d8936454ed6c7491e81444a48357a6e2625271d837` (43) |
| `Toy.Sim.fsimFinal_comp` | forward-simulations-compose: result | none | `f3a842e0b27cc6f1a8c6d17161365d8354980f37b9e81447d0ca256691db1725` | `2c83e1cf7a24500a53f0abcf854014665a0ee90ae1baa2a4feab574d8e90233b` (6) |
| `Toy.Sim.fsimInit_comp` | forward-simulations-compose: result | none | `4243db5ef29ecee6330acef77101730cb7475b22f162b0069990ccd8c25555d9` | `4ff9b8bd38306c2c6368c6fac257dc48bb8fef7a2665de0e4cafa8001c0c0c08` (6) |
| `Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates` | terminating-behaviours-preserved: result | `propext` | `fb6736ea047b7dea53462a9c874172c8cff2667f7c4e81db67454a514afad4e5` | `dd7426bfdc20c0e424d5ac885cf2a6b7c1baac991f675358ed53df568d9234e8` (25) |
| `Toy.Sim.fsimInit_fsimStep_partial_run_simulated` | partial-run-simulated: result | `propext` | `576d77970ebee84b30199b9b7b3b980d3cadefedc46239e2771eb3adb4b2bf91` | `2ea06c45dbe211ec98e74d51a2884f963e13acdf920c8aaca151e4a0330ec0b9` (13) |
| `Toy.Sim.fsimStep_comp` | step-diagrams-compose: result | `propext` | `31917a3a3c3c54d6e381838d790d7e849e33fa62facc3c9115fae0f6eb3a7e78` | `65b865db21381638911eee12643cec0c418746193ffd8f81c2a679a788fe54d2` (13) |
| `Toy.Sim.improves_goesWrong_nil` | refinement-is-a-preorder: result | none | `fa8c520dba5a91c8d17e136fceb3f4c5570ae2d06a755aca0b4277e9d2ac8d2a` | `58ca24d17e723c5fed7e765a122eb241ba8c7ef57994fa8bc8cc69ae08e2ceb2` (9) |
| `Toy.Sim.isForwardSim_comp` | forward-simulations-compose: result | `propext` | `0080b57e5739124a2d792e7e4d575723a74a07c4a0bfbecda59bf7cfe256bd17` | `08c66cb60c1ec987b70d27093f367073a5e911a2e50a15a02209b4b8b6ff63aa` (19) |
| `Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors` | forward-sim-preserves-non-wrong-behaviours: result | `Classical.choice`, `propext` | `6feb4733f76b4f4d07ee17ce7b3853894f3f4e449f558c2c1511def78ceb5d10` | `6d74d62d15b4759536a8d1e86e12f5fd36158a40e51291284423d34d1f3ce077` (27) |
| `Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset` | refinement-is-inclusion-when-source-never-goes-wrong: result | none | `dd41f305b634c06af459145600d9f5cc7ba489f1a6dcc9cb4e4e64403f2db3f2` | `cb856b7e0c8f4451db8e8dc7d51e4f9573e0c064b6b5e7a8302541c746ece3db` (25) |
| `Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges` | silent-divergence-preserved: result | `Classical.choice`, `propext` | `83e736d6aac4a71d540c2e52ddd491aaf45436f7fb1567ddbeaaf870e765b38c` | `33f1325ecaaaf98c771c476d8b219b27ace268da4cf03c2f68da3e5f7955c831` (24) |

#### Machine-printed statements

Output of `#check @<name>` (with `set_option format.width 100` and `set_option pp.fieldNotation false`), in the built environment, for every name in the table above whose machine-printed statement is not already quoted under **Findings** (counterexample, non-vacuity and positive-control statements are quoted there with their cards; the main theorems are quoted there as source signatures and are repeated here machine-printed).

```lean
Toy.Sim.Cex.cex_bsim_without_final_clause : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
    Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
      Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
        Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Cex.cex_bsim_without_initExists : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
    Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
      Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
        Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
Toy.Sim.Cex.cex_bsim_without_initMatch : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
    Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relFalse ∧
      Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relFalse ∧
        Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Cex.cex_bsim_without_progress : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow ∧
    Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow Toy.Sim.Cex.relTrue ∧
      Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow Toy.Sim.Cex.relTrue ∧
        Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.StuckNow
Toy.Sim.Cex.cex_bsim_without_step_diagram : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0) ∧
    Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0) Toy.Sim.Cex.relToFalse ∧
      Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0) Toy.Sim.Cex.relToFalse ∧
        Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0) Toy.Sim.Cex.relToFalse ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.OneStep (some 7) 0)
Toy.Sim.Cex.cex_bsim_without_wf : Toy.Sim.BSimInitExists (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop ∧
  Toy.Sim.BSimInitMatch (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop Toy.Sim.Cex.relTrue ∧
    Toy.Sim.BSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop Toy.Sim.Cex.relTrue ∧
      Toy.Sim.BSimProgress (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop Toy.Sim.Cex.relTrue ∧
        Toy.Sim.BSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop Toy.Sim.Cex.fullOrd Toy.Sim.Cex.relTrue ∧
          ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.Loop
Toy.Sim.Cex.cex_compOrd_wf_needs_both : WellFounded Toy.Sim.Cex.emptyOrd ∧
  ¬WellFounded (Toy.Sim.compOrd Toy.Sim.Cex.fullOrd Toy.Sim.Cex.emptyOrd) ∧
    ¬WellFounded (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.fullOrd)
Toy.Sim.Cex.cex_comp_without_first_final : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
    Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
      Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 1) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
        ¬Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
              (Toy.Sim.compRel Toy.Sim.Cex.relTrue Toy.Sim.Cex.relEq) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relTrue Toy.Sim.Cex.relEq)
Toy.Sim.Cex.cex_comp_without_first_init : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
    Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
      Toy.Sim.IsForwardSim Toy.Sim.Ex.NoInit Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
        ¬Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
              (Toy.Sim.compRel Toy.Sim.Cex.relFalse Toy.Sim.Cex.relEq) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relFalse Toy.Sim.Cex.relEq)
Toy.Sim.Cex.cex_comp_without_first_step_diagram : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
      Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
        ¬Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relBefore Toy.Sim.Cex.relEq) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relBefore Toy.Sim.Cex.relEq)
Toy.Sim.Cex.cex_comp_without_first_wf : Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relEq ∧
  Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relEq ∧
    Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.fullOrd Toy.Sim.Cex.relEq ∧
      Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
        ¬WellFounded (Toy.Sim.compOrd Toy.Sim.Cex.fullOrd Toy.Sim.Cex.emptyOrd) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.fullOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relEq)
Toy.Sim.Cex.cex_comp_without_second_final : Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  WellFounded Toy.Sim.Cex.emptyOrd ∧
    Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
        ¬Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relTrue) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relTrue)
Toy.Sim.Cex.cex_comp_without_second_init : Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  WellFounded Toy.Sim.Cex.emptyOrd ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
        ¬Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relFalse) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relFalse)
Toy.Sim.Cex.cex_comp_without_second_step_diagram : Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep (some 7) 0)
    (Toy.Sim.Ex.OneStep (some 7) 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  WellFounded Toy.Sim.Cex.emptyOrd ∧
    Toy.Sim.FSimInit (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
      Toy.Sim.FSimFinal (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
        ¬Toy.Sim.FSimStep (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relBefore) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.emptyOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relBefore)
Toy.Sim.Cex.cex_comp_without_second_wf : Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relEq ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relEq ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.fullOrd Toy.Sim.Cex.relEq ∧
        ¬WellFounded (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.fullOrd) ∧
          ¬Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
              (Toy.Sim.compOrd Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.fullOrd)
              (Toy.Sim.compRel Toy.Sim.Cex.relEq Toy.Sim.Cex.relEq)
Toy.Sim.Cex.cex_flip_without_final_clause : ∀ (M : Nat → Nat → Prop),
  WellFounded Toy.Sim.Cex.emptyOrd ∧
    Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
        Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
          Toy.Sim.Determinate M (Toy.Sim.Ex.Done 1) ∧
            Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
              ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Cex.cex_flip_without_init_clause : ∀ (M : Nat → Nat → Prop),
  WellFounded Toy.Sim.Cex.emptyOrd ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
      Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
        Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
          Toy.Sim.Determinate M Toy.Sim.Ex.NoInit ∧
            Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit ∧
              ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit
Toy.Sim.Cex.cex_flip_without_step_diagram : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
      Toy.Sim.Receptive Eq (Toy.Sim.Ex.OneStep (some 7) 0) ∧
        Toy.Sim.Determinate Eq (Toy.Sim.Ex.Done 0) ∧
          Toy.Sim.NoBackwardSim (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) ∧
            ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0)
Toy.Sim.Cex.cex_flip_without_wf : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.FSimInit Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relTrue ∧
    Toy.Sim.FSimFinal Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relTrue ∧
      Toy.Sim.FSimStep Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.fullOrd Toy.Sim.Cex.relTrue ∧
        Toy.Sim.Receptive M Toy.Sim.Ex.Loop ∧
          Toy.Sim.Determinate M (Toy.Sim.Ex.Done 0) ∧
            Toy.Sim.NoBackwardSim Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) ∧
              ¬Toy.Sim.RefinedBy Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0)
Toy.Sim.Cex.cex_fsim_without_final_clause : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.relTrue ∧
    Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
      Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ∧
        ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 1) (Toy.Sim.Behavior.terminates [] 0) ∧
          ∀ (t : List Nat), Toy.Sim.Behavior.terminates [] 0 ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_fsim_without_init_clause : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimFinal (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.relFalse ∧
    Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
      Toy.Sim.LTS.init (Toy.Sim.Ex.Done 0) () ∧
        Toy.Sim.Star (Toy.Sim.Ex.Done 0) () [] () ∧
          (¬∃ i₀ i s₀' s',
                Toy.Sim.LTS.init Toy.Sim.Ex.NoInit s₀' ∧
                  Toy.Sim.Cex.relFalse i₀ () s₀' ∧
                    Toy.Sim.Star Toy.Sim.Ex.NoInit s₀' [] s' ∧ Toy.Sim.Cex.relFalse i () s') ∧
            Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ∧
              ¬Toy.Sim.HasBehavior Toy.Sim.Ex.NoInit (Toy.Sim.Behavior.terminates [] 0) ∧
                ∀ (t : List Nat), Toy.Sim.Behavior.terminates [] 0 ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_fsim_without_init_clause_diverges : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimStep Toy.Sim.Ex.Loop Toy.Sim.Ex.NoInit Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
    Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.diverges []) ∧
      ¬Toy.Sim.HasBehavior Toy.Sim.Ex.NoInit (Toy.Sim.Behavior.diverges []) ∧
        ∀ (t : List Nat), Toy.Sim.Behavior.diverges [] ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_fsim_without_step_diagram : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
    Toy.Sim.FSimFinal (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relBefore ∧
      Toy.Sim.LTS.init (Toy.Sim.Ex.OneStep (some 7) 0) false ∧
        Toy.Sim.Star (Toy.Sim.Ex.OneStep (some 7) 0) false [7] true ∧
          (¬∃ i₀ i s₀' s',
                Toy.Sim.LTS.init (Toy.Sim.Ex.Done 0) s₀' ∧
                  Toy.Sim.Cex.relBefore i₀ false s₀' ∧
                    Toy.Sim.Star (Toy.Sim.Ex.Done 0) s₀' [7] s' ∧ Toy.Sim.Cex.relBefore i true s') ∧
            Toy.Sim.HasBehavior (Toy.Sim.Ex.OneStep (some 7) 0) (Toy.Sim.Behavior.terminates [7] 0) ∧
              ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [7] 0) ∧
                ∀ (t : List Nat), Toy.Sim.Behavior.terminates [7] 0 ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_fsim_without_step_diagram_diverges : WellFounded Toy.Sim.Cex.emptyOrd ∧
  Toy.Sim.FSimInit Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.relTrue ∧
    Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.diverges []) ∧
      ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.diverges []) ∧
        ∀ (t : List Nat), Toy.Sim.Behavior.diverges [] ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_improves_antisymm_needs_both : Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong [])
    (Toy.Sim.Behavior.terminates [] 0) ∧
  Toy.Sim.Behavior.goesWrong [] ≠ Toy.Sim.Behavior.terminates [] 0
Toy.Sim.Cex.cex_improves_trans_needs_both : (Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 1)
      (Toy.Sim.Behavior.terminates [] 1) ∧
    ¬Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 0) (Toy.Sim.Behavior.terminates [] 1)) ∧
  Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 0) (Toy.Sim.Behavior.terminates [] 0) ∧
    ¬Toy.Sim.Improves (Toy.Sim.Behavior.terminates [] 0) (Toy.Sim.Behavior.terminates [] 1)
Toy.Sim.Cex.cex_inclusion_without_target_behavior : Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) ∧
  Toy.Sim.IsBackwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
    Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done 0) ∧
      ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1)
Toy.Sim.Cex.cex_partial_run_from_non_initial_state : Toy.Sim.FSimInit Toy.Sim.Ex.NoInit (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.relFalse ∧
  Toy.Sim.FSimStep Toy.Sim.Ex.NoInit (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relFalse ∧
    Toy.Sim.Star Toy.Sim.Ex.NoInit () [] () ∧
      ¬∃ i₀ i s₀' s',
          Toy.Sim.LTS.init (Toy.Sim.Ex.Done 0) s₀' ∧
            Toy.Sim.Cex.relFalse i₀ () s₀' ∧ Toy.Sim.Star (Toy.Sim.Ex.Done 0) s₀' [] s' ∧ Toy.Sim.Cex.relFalse i () s'
Toy.Sim.Cex.cex_partial_run_without_source_run : Toy.Sim.FSimInit (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.relEq ∧
  Toy.Sim.FSimStep (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
    Toy.Sim.LTS.init (Toy.Sim.Ex.Done 0) () ∧
      ¬∃ i₀ i s₀' s',
          Toy.Sim.LTS.init (Toy.Sim.Ex.Done 0) s₀' ∧
            Toy.Sim.Cex.relEq i₀ () s₀' ∧ Toy.Sim.Star (Toy.Sim.Ex.Done 0) s₀' [7] s' ∧ Toy.Sim.Cex.relEq i () s'
Toy.Sim.Cex.cex_pipeline_preserves_without_chain : ¬Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
  Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 0) ∧
    (∀ (t : List Nat), Toy.Sim.Behavior.terminates [] 0 ≠ Toy.Sim.Behavior.goesWrong t) ∧
      ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 1) (Toy.Sim.Behavior.terminates [] 0)
Toy.Sim.Cex.cex_pipeline_without_chain : ∀ (M : Nat → Nat → Prop),
  Toy.Sim.Receptive M (Toy.Sim.Ex.Done 0) ∧
    Toy.Sim.Determinate M (Toy.Sim.Ex.Done 1) ∧
      ¬Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
        ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1) ∧
          Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done 0) ∧
            ¬(Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 1) (Toy.Sim.Behavior.terminates [] 1) ↔
                Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1))
Toy.Sim.Cex.cex_preservation_without_source_behavior : Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0)
    Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relEq ∧
  ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.terminates [] 1) ∧
    ¬Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) (Toy.Sim.Behavior.diverges []) ∧
      Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) ∧
        (∀ (t : List Nat), Toy.Sim.Behavior.terminates [] 1 ≠ Toy.Sim.Behavior.goesWrong t) ∧
          ∀ (t : List Nat), Toy.Sim.Behavior.diverges [] ≠ Toy.Sim.Behavior.goesWrong t
Toy.Sim.Cex.cex_refinedBy_trans_needs_both : (Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 1) (Toy.Sim.Ex.Done 1) ∧
    ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)) ∧
  Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 0) ∧ ¬Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Examples.fsimChain_neg : ¬Toy.Sim.FSimChain (Toy.Sim.Ex.Done 0) (Toy.Sim.Ex.Done 1)
Toy.Sim.Examples.isForwardSim_neg : ¬∃ I ord R, Toy.Sim.IsForwardSim Toy.Sim.Ex.Loop (Toy.Sim.Ex.Done 0) ord R
@Toy.Sim.Improves.antisymm : ∀ {E Res : Type} {b₁ b₂ : Toy.Sim.Behavior E Res},
  Toy.Sim.Improves b₁ b₂ → Toy.Sim.Improves b₂ b₁ → b₁ = b₂
@Toy.Sim.Improves.refl : ∀ {E Res : Type} (b : Toy.Sim.Behavior E Res), Toy.Sim.Improves b b
@Toy.Sim.Improves.trans : ∀ {E Res : Type} {b₁ b₂ b₃ : Toy.Sim.Behavior E Res},
  Toy.Sim.Improves b₁ b₂ → Toy.Sim.Improves b₂ b₃ → Toy.Sim.Improves b₁ b₃
@Toy.Sim.RefinedBy.refl : ∀ {E Res : Type} (L : Toy.Sim.LTS E Res), Toy.Sim.RefinedBy L L
@Toy.Sim.RefinedBy.trans : ∀ {E Res : Type} {L₁ L₂ L₃ : Toy.Sim.LTS E Res},
  Toy.Sim.RefinedBy L₁ L₂ → Toy.Sim.RefinedBy L₂ L₃ → Toy.Sim.RefinedBy L₁ L₃
@Toy.Sim.Unfolded.backward_sim_gives_refinement : ∀ {E Res : Type} (L₁ L₂ : Toy.Sim.LTS E Res) (I : Type)
  (ord : I → I → Prop) (R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop),
  WellFounded ord →
    ((∃ s₁, Toy.Sim.LTS.init L₁ s₁) → ∃ s₂, Toy.Sim.LTS.init L₂ s₂) →
      (∀ (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂),
          Toy.Sim.LTS.init L₁ s₁ → Toy.Sim.LTS.init L₂ s₂ → ∃ i s₁', Toy.Sim.LTS.init L₁ s₁' ∧ R i s₁' s₂) →
        (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (r : Res),
            R i s₁ s₂ →
              (∀ (s₁' : Toy.Sim.LTS.State L₁),
                  Toy.Sim.Star L₁ s₁ [] s₁' →
                    (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨ ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                Toy.Sim.LTS.final L₂ s₂ r → ∃ s₁', Toy.Sim.Star L₁ s₁ [] s₁' ∧ Toy.Sim.LTS.final L₁ s₁' r) →
          (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂),
              R i s₁ s₂ →
                (∀ (s₁' : Toy.Sim.LTS.State L₁),
                    Toy.Sim.Star L₁ s₁ [] s₁' →
                      (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨ ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                  (∃ r, Toy.Sim.LTS.final L₂ s₂ r) ∨ ∃ e s₂', Toy.Sim.LTS.step L₂ s₂ e s₂') →
            (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E)
                (s₂' : Toy.Sim.LTS.State L₂),
                R i s₁ s₂ →
                  (∀ (s₁' : Toy.Sim.LTS.State L₁),
                      Toy.Sim.Star L₁ s₁ [] s₁' →
                        (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨ ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                    Toy.Sim.LTS.step L₂ s₂ e s₂' →
                      ∃ i' s₁',
                        (Toy.Sim.Plus L₁ s₁ (Toy.Sim.obs e) s₁' ∨ Toy.Sim.Star L₁ s₁ (Toy.Sim.obs e) s₁' ∧ ord i' i) ∧
                          R i' s₁' s₂') →
              ∀ (b₂ : Toy.Sim.Behavior E Res),
                Toy.Sim.HasBehavior L₂ b₂ →
                  ∃ b₁,
                    Toy.Sim.HasBehavior L₁ b₁ ∧
                      (b₁ = b₂ ∨ ∃ t, b₁ = Toy.Sim.Behavior.goesWrong t ∧ t <+: Toy.Sim.Behavior.trace b₂)
@Toy.Sim.Unfolded.flip_forward_to_backward : ∀ {E Res : Type} (M : E → E → Prop) (L₁ L₂ : Toy.Sim.LTS E Res) (I : Type)
  (ord : I → I → Prop) (R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop),
  WellFounded ord →
    (∀ (s₁ : Toy.Sim.LTS.State L₁), Toy.Sim.LTS.init L₁ s₁ → ∃ i s₂, Toy.Sim.LTS.init L₂ s₂ ∧ R i s₁ s₂) →
      (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (r : Res),
          R i s₁ s₂ → Toy.Sim.LTS.final L₁ s₁ r → Toy.Sim.LTS.final L₂ s₂ r) →
        (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
            R i s₁ s₂ →
              Toy.Sim.LTS.step L₁ s₁ e s₁' →
                ∃ i' s₂',
                  (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ ord i' i) ∧
                    R i' s₁' s₂') →
          (∀ (s : Toy.Sim.LTS.State L₁) (a : E) (s₁ : Toy.Sim.LTS.State L₁) (b : E),
              Toy.Sim.LTS.step L₁ s (some a) s₁ → M a b → ∃ s₂, Toy.Sim.LTS.step L₁ s (some b) s₂) →
            (∀ (s : Toy.Sim.LTS.State L₂) (e₁ : Option E) (s₁ : Toy.Sim.LTS.State L₂) (e₂ : Option E)
                (s₂ : Toy.Sim.LTS.State L₂),
                Toy.Sim.LTS.step L₂ s e₁ s₁ → Toy.Sim.LTS.step L₂ s e₂ s₂ → Toy.Sim.LabelMatch M e₁ e₂) →
              (∀ (s : Toy.Sim.LTS.State L₂) (e : Option E) (s₁ s₂ : Toy.Sim.LTS.State L₂),
                  Toy.Sim.LTS.step L₂ s e s₁ → Toy.Sim.LTS.step L₂ s e s₂ → s₁ = s₂) →
                (∀ (s s' : Toy.Sim.LTS.State L₂), Toy.Sim.LTS.init L₂ s → Toy.Sim.LTS.init L₂ s' → s = s') →
                  (∀ (s : Toy.Sim.LTS.State L₂) (r : Res),
                      Toy.Sim.LTS.final L₂ s r →
                        ∀ (e : Option E) (s' : Toy.Sim.LTS.State L₂), ¬Toy.Sim.LTS.step L₂ s e s') →
                    (∀ (s : Toy.Sim.LTS.State L₂) (r r' : Res),
                        Toy.Sim.LTS.final L₂ s r → Toy.Sim.LTS.final L₂ s r' → r = r') →
                      ∃ I' ord' R',
                        WellFounded ord' ∧
                          ((∃ s₁, Toy.Sim.LTS.init L₁ s₁) → ∃ s₂, Toy.Sim.LTS.init L₂ s₂) ∧
                            (∀ (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂),
                                Toy.Sim.LTS.init L₁ s₁ →
                                  Toy.Sim.LTS.init L₂ s₂ → ∃ i s₁', Toy.Sim.LTS.init L₁ s₁' ∧ R' i s₁' s₂) ∧
                              (∀ (i : I') (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (r : Res),
                                  R' i s₁ s₂ →
                                    (∀ (s₁' : Toy.Sim.LTS.State L₁),
                                        Toy.Sim.Star L₁ s₁ [] s₁' →
                                          (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨
                                            ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                                      Toy.Sim.LTS.final L₂ s₂ r →
                                        ∃ s₁', Toy.Sim.Star L₁ s₁ [] s₁' ∧ Toy.Sim.LTS.final L₁ s₁' r) ∧
                                (∀ (i : I') (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂),
                                    R' i s₁ s₂ →
                                      (∀ (s₁' : Toy.Sim.LTS.State L₁),
                                          Toy.Sim.Star L₁ s₁ [] s₁' →
                                            (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨
                                              ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                                        (∃ r, Toy.Sim.LTS.final L₂ s₂ r) ∨ ∃ e s₂', Toy.Sim.LTS.step L₂ s₂ e s₂') ∧
                                  (∀ (i : I') (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E)
                                      (s₂' : Toy.Sim.LTS.State L₂),
                                      R' i s₁ s₂ →
                                        (∀ (s₁' : Toy.Sim.LTS.State L₁),
                                            Toy.Sim.Star L₁ s₁ [] s₁' →
                                              (∃ r, Toy.Sim.LTS.final L₁ s₁' r) ∨
                                                ∃ e s₁'', Toy.Sim.LTS.step L₁ s₁' e s₁'') →
                                          Toy.Sim.LTS.step L₂ s₂ e s₂' →
                                            ∃ i' s₁',
                                              (Toy.Sim.Plus L₁ s₁ (Toy.Sim.obs e) s₁' ∨
                                                  Toy.Sim.Star L₁ s₁ (Toy.Sim.obs e) s₁' ∧ ord' i' i) ∧
                                                R' i' s₁' s₂') ∧
                                    ∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂),
                                      R i s₁ s₂ → ∃ i', R' i' s₁ s₂
@Toy.Sim.Unfolded.partial_run_simulated : ∀ {E Res : Type} (L₁ L₂ : Toy.Sim.LTS E Res) (I : Type) (ord : I → I → Prop)
  (R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop),
  (∀ (s₁ : Toy.Sim.LTS.State L₁), Toy.Sim.LTS.init L₁ s₁ → ∃ i s₂, Toy.Sim.LTS.init L₂ s₂ ∧ R i s₁ s₂) →
    (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
        R i s₁ s₂ →
          Toy.Sim.LTS.step L₁ s₁ e s₁' →
            ∃ i' s₂',
              (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ ord i' i) ∧
                R i' s₁' s₂') →
      ∀ (s₀ s : Toy.Sim.LTS.State L₁) (t : List E),
        Toy.Sim.LTS.init L₁ s₀ →
          Toy.Sim.Star L₁ s₀ t s →
            ∃ i₀ i s₀' s', Toy.Sim.LTS.init L₂ s₀' ∧ R i₀ s₀ s₀' ∧ Toy.Sim.Star L₂ s₀' t s' ∧ R i s s'
@Toy.Sim.Unfolded.pipeline_end_to_end_refinement : ∀ {E Res : Type} (M : E → E → Prop) (L L' : Toy.Sim.LTS E Res),
  Toy.Sim.FSimChain L L' →
    (∀ (s : Toy.Sim.LTS.State L) (a : E) (s₁ : Toy.Sim.LTS.State L) (b : E),
        Toy.Sim.LTS.step L s (some a) s₁ → M a b → ∃ s₂, Toy.Sim.LTS.step L s (some b) s₂) →
      (∀ (s : Toy.Sim.LTS.State L') (e₁ : Option E) (s₁ : Toy.Sim.LTS.State L') (e₂ : Option E)
          (s₂ : Toy.Sim.LTS.State L'),
          Toy.Sim.LTS.step L' s e₁ s₁ → Toy.Sim.LTS.step L' s e₂ s₂ → Toy.Sim.LabelMatch M e₁ e₂) →
        (∀ (s : Toy.Sim.LTS.State L') (e : Option E) (s₁ s₂ : Toy.Sim.LTS.State L'),
            Toy.Sim.LTS.step L' s e s₁ → Toy.Sim.LTS.step L' s e s₂ → s₁ = s₂) →
          (∀ (s s' : Toy.Sim.LTS.State L'), Toy.Sim.LTS.init L' s → Toy.Sim.LTS.init L' s' → s = s') →
            (∀ (s : Toy.Sim.LTS.State L') (r : Res),
                Toy.Sim.LTS.final L' s r → ∀ (e : Option E) (s' : Toy.Sim.LTS.State L'), ¬Toy.Sim.LTS.step L' s e s') →
              (∀ (s : Toy.Sim.LTS.State L') (r r' : Res),
                  Toy.Sim.LTS.final L' s r → Toy.Sim.LTS.final L' s r' → r = r') →
                ∀ (b' : Toy.Sim.Behavior E Res),
                  Toy.Sim.HasBehavior L' b' →
                    ∃ b,
                      Toy.Sim.HasBehavior L b ∧
                        (b = b' ∨ ∃ t, b = Toy.Sim.Behavior.goesWrong t ∧ t <+: Toy.Sim.Behavior.trace b')
@Toy.Sim.Unfolded.silent_divergence_preserved : ∀ {E Res : Type} (L₁ L₂ : Toy.Sim.LTS E Res) (I : Type)
  (ord : I → I → Prop) (R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop),
  WellFounded ord →
    (∀ (s₁ : Toy.Sim.LTS.State L₁), Toy.Sim.LTS.init L₁ s₁ → ∃ i s₂, Toy.Sim.LTS.init L₂ s₂ ∧ R i s₁ s₂) →
      (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
          R i s₁ s₂ →
            Toy.Sim.LTS.step L₁ s₁ e s₁' →
              ∃ i' s₂',
                (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ ord i' i) ∧
                  R i' s₁' s₂') →
        ∀ (t : List E),
          (∃ s₀ s,
              Toy.Sim.LTS.init L₁ s₀ ∧
                Toy.Sim.Star L₁ s₀ t s ∧ ∃ f, f 0 = s ∧ ∀ (n : Nat), Toy.Sim.LTS.step L₁ (f n) none (f (n + 1))) →
            ∃ s₀' s',
              Toy.Sim.LTS.init L₂ s₀' ∧
                Toy.Sim.Star L₂ s₀' t s' ∧ ∃ g, g 0 = s' ∧ ∀ (n : Nat), Toy.Sim.LTS.step L₂ (g n) none (g (n + 1))
@Toy.Sim.Unfolded.step_diagrams_compose : ∀ {E Res : Type} (L₁ L₂ L₃ : Toy.Sim.LTS E Res) (I₁ I₂ : Type)
  (ord₁ : I₁ → I₁ → Prop) (ord₂ : I₂ → I₂ → Prop) (R₁ : I₁ → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop)
  (R₂ : I₂ → Toy.Sim.LTS.State L₂ → Toy.Sim.LTS.State L₃ → Prop),
  (∀ (i : I₁) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
      R₁ i s₁ s₂ →
        Toy.Sim.LTS.step L₁ s₁ e s₁' →
          ∃ i' s₂',
            (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ ord₁ i' i) ∧
              R₁ i' s₁' s₂') →
    (∀ (i : I₂) (s₂ : Toy.Sim.LTS.State L₂) (s₃ : Toy.Sim.LTS.State L₃) (e : Option E) (s₂' : Toy.Sim.LTS.State L₂),
        R₂ i s₂ s₃ →
          Toy.Sim.LTS.step L₂ s₂ e s₂' →
            ∃ i' s₃',
              (Toy.Sim.Plus L₃ s₃ (Toy.Sim.obs e) s₃' ∨ Toy.Sim.Star L₃ s₃ (Toy.Sim.obs e) s₃' ∧ ord₂ i' i) ∧
                R₂ i' s₂' s₃') →
      ∀ (i : I₂ × I₁) (s₁ : Toy.Sim.LTS.State L₁) (s₃ : Toy.Sim.LTS.State L₃) (e : Option E)
        (s₁' : Toy.Sim.LTS.State L₁),
        (∃ s₂, R₁ (Prod.snd i) s₁ s₂ ∧ R₂ (Prod.fst i) s₂ s₃) →
          Toy.Sim.LTS.step L₁ s₁ e s₁' →
            ∃ i' s₃',
              (Toy.Sim.Plus L₃ s₃ (Toy.Sim.obs e) s₃' ∨
                  Toy.Sim.Star L₃ s₃ (Toy.Sim.obs e) s₃' ∧
                    (Relation.TransGen ord₂ (Prod.fst i') (Prod.fst i) ∨
                      Prod.fst i' = Prod.fst i ∧ ord₁ (Prod.snd i') (Prod.snd i))) ∧
                ∃ s₂', R₁ (Prod.snd i') s₁' s₂' ∧ R₂ (Prod.fst i') s₂' s₃'
@Toy.Sim.Unfolded.terminating_behaviours_preserved : ∀ {E Res : Type} (L₁ L₂ : Toy.Sim.LTS E Res) (I : Type)
  (ord : I → I → Prop) (R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop),
  (∀ (s₁ : Toy.Sim.LTS.State L₁), Toy.Sim.LTS.init L₁ s₁ → ∃ i s₂, Toy.Sim.LTS.init L₂ s₂ ∧ R i s₁ s₂) →
    (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
        R i s₁ s₂ →
          Toy.Sim.LTS.step L₁ s₁ e s₁' →
            ∃ i' s₂',
              (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ ord i' i) ∧
                R i' s₁' s₂') →
      (∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (r : Res),
          R i s₁ s₂ → Toy.Sim.LTS.final L₁ s₁ r → Toy.Sim.LTS.final L₂ s₂ r) →
        ∀ (t : List E) (r : Res),
          (∃ s₀ s, Toy.Sim.LTS.init L₁ s₀ ∧ Toy.Sim.Star L₁ s₀ t s ∧ Toy.Sim.LTS.final L₁ s r) →
            ∃ s₀' s', Toy.Sim.LTS.init L₂ s₀' ∧ Toy.Sim.Star L₂ s₀' t s' ∧ Toy.Sim.LTS.final L₂ s' r
@Toy.Sim.backwardSim_gives_refinedBy : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type} {ord : I → I → Prop}
  {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.IsBackwardSim L₁ L₂ ord R → Toy.Sim.RefinedBy L₁ L₂
@Toy.Sim.backwardSim_neverGoesWrong_behaviors_subset : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.IsBackwardSim L₁ L₂ ord R →
    Toy.Sim.NeverGoesWrong L₁ → ∀ {b : Toy.Sim.Behavior E Res}, Toy.Sim.HasBehavior L₂ b → Toy.Sim.HasBehavior L₁ b
@Toy.Sim.compOrd_wf : ∀ {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop},
  WellFounded ord₁ → WellFounded ord₂ → WellFounded (Toy.Sim.compOrd ord₁ ord₂)
@Toy.Sim.forwardSim_deterministic_target_gives_backwardSim : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.IsForwardSim L₁ L₂ ord R →
    Toy.Sim.Determinate Eq L₂ →
      ∃ I' ord' R',
        Toy.Sim.IsBackwardSim L₁ L₂ ord' R' ∧
          ∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂), R i s₁ s₂ → ∃ i', R' i' s₁ s₂
@Toy.Sim.forwardSim_receptive_determinate_gives_backwardSim : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop} (M : E → E → Prop),
  Toy.Sim.IsForwardSim L₁ L₂ ord R →
    Toy.Sim.Receptive M L₁ →
      Toy.Sim.Determinate M L₂ →
        ∃ I' ord' R',
          Toy.Sim.IsBackwardSim L₁ L₂ ord' R' ∧
            ∀ (i : I) (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂), R i s₁ s₂ → ∃ i', R' i' s₁ s₂
@Toy.Sim.fsimChain_collapse : ∀ {E Res : Type} {L L' : Toy.Sim.LTS E Res},
  Toy.Sim.FSimChain L L' → ∃ I ord R, Toy.Sim.IsForwardSim L L' ord R
@Toy.Sim.fsimChain_deterministic_last_gives_refinedBy : ∀ {E Res : Type} {L L' : Toy.Sim.LTS E Res},
  Toy.Sim.FSimChain L L' → Toy.Sim.Determinate Eq L' → Toy.Sim.RefinedBy L L'
@Toy.Sim.fsimChain_of_isForwardSim : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type} {ord : I → I → Prop}
  {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.IsForwardSim L₁ L₂ ord R → Toy.Sim.FSimChain L₁ L₂
@Toy.Sim.fsimChain_preserves_non_goesWrong_behaviors : ∀ {E Res : Type} {L L' : Toy.Sim.LTS E Res},
  Toy.Sim.FSimChain L L' →
    ∀ {b : Toy.Sim.Behavior E Res},
      Toy.Sim.HasBehavior L b → (∀ (t : List E), b ≠ Toy.Sim.Behavior.goesWrong t) → Toy.Sim.HasBehavior L' b
@Toy.Sim.fsimChain_receptive_first_determinate_last_gives_refinedBy : ∀ {E Res : Type} {L L' : Toy.Sim.LTS E Res}
  (M : E → E → Prop), Toy.Sim.FSimChain L L' → Toy.Sim.Receptive M L → Toy.Sim.Determinate M L' → Toy.Sim.RefinedBy L L'
@Toy.Sim.fsimChain_receptive_first_determinate_last_neverGoesWrong_first_behaviors_iff : ∀ {E Res : Type}
  {L L' : Toy.Sim.LTS E Res} (M : E → E → Prop),
  Toy.Sim.FSimChain L L' →
    Toy.Sim.Receptive M L →
      Toy.Sim.Determinate M L' →
        Toy.Sim.NeverGoesWrong L → ∀ (b : Toy.Sim.Behavior E Res), Toy.Sim.HasBehavior L' b ↔ Toy.Sim.HasBehavior L b
@Toy.Sim.fsimFinal_comp : ∀ {E Res : Type} {L₁ L₂ L₃ : Toy.Sim.LTS E Res} {I₁ I₂ : Type}
  {R₁ : I₁ → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop}
  {R₂ : I₂ → Toy.Sim.LTS.State L₂ → Toy.Sim.LTS.State L₃ → Prop},
  Toy.Sim.FSimFinal L₁ L₂ R₁ → Toy.Sim.FSimFinal L₂ L₃ R₂ → Toy.Sim.FSimFinal L₁ L₃ (Toy.Sim.compRel R₁ R₂)
@Toy.Sim.fsimInit_comp : ∀ {E Res : Type} {L₁ L₂ L₃ : Toy.Sim.LTS E Res} {I₁ I₂ : Type}
  {R₁ : I₁ → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop}
  {R₂ : I₂ → Toy.Sim.LTS.State L₂ → Toy.Sim.LTS.State L₃ → Prop},
  Toy.Sim.FSimInit L₁ L₂ R₁ → Toy.Sim.FSimInit L₂ L₃ R₂ → Toy.Sim.FSimInit L₁ L₃ (Toy.Sim.compRel R₁ R₂)
@Toy.Sim.fsimInit_fsimStep_fsimFinal_preserve_terminates : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.FSimInit L₁ L₂ R →
    Toy.Sim.FSimStep L₁ L₂ ord R →
      Toy.Sim.FSimFinal L₁ L₂ R →
        ∀ {t : List E} {r : Res},
          Toy.Sim.HasBehavior L₁ (Toy.Sim.Behavior.terminates t r) →
            Toy.Sim.HasBehavior L₂ (Toy.Sim.Behavior.terminates t r)
@Toy.Sim.fsimInit_fsimStep_partial_run_simulated : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.FSimInit L₁ L₂ R →
    Toy.Sim.FSimStep L₁ L₂ ord R →
      ∀ {s₀ s : Toy.Sim.LTS.State L₁} {t : List E},
        Toy.Sim.LTS.init L₁ s₀ →
          Toy.Sim.Star L₁ s₀ t s →
            ∃ i₀ i s₀' s', Toy.Sim.LTS.init L₂ s₀' ∧ R i₀ s₀ s₀' ∧ Toy.Sim.Star L₂ s₀' t s' ∧ R i s s'
@Toy.Sim.fsimStep_comp : ∀ {E Res : Type} {L₁ L₂ L₃ : Toy.Sim.LTS E Res} {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop}
  {ord₂ : I₂ → I₂ → Prop} {R₁ : I₁ → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop}
  {R₂ : I₂ → Toy.Sim.LTS.State L₂ → Toy.Sim.LTS.State L₃ → Prop},
  Toy.Sim.FSimStep L₁ L₂ ord₁ R₁ →
    Toy.Sim.FSimStep L₂ L₃ ord₂ R₂ → Toy.Sim.FSimStep L₁ L₃ (Toy.Sim.compOrd ord₁ ord₂) (Toy.Sim.compRel R₁ R₂)
@Toy.Sim.improves_goesWrong_nil : ∀ {E Res : Type} (b : Toy.Sim.Behavior E Res),
  Toy.Sim.Improves (Toy.Sim.Behavior.goesWrong []) b
@Toy.Sim.isForwardSim_comp : ∀ {E Res : Type} {L₁ L₂ L₃ : Toy.Sim.LTS E Res} {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop}
  {ord₂ : I₂ → I₂ → Prop} {R₁ : I₁ → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop}
  {R₂ : I₂ → Toy.Sim.LTS.State L₂ → Toy.Sim.LTS.State L₃ → Prop},
  Toy.Sim.IsForwardSim L₁ L₂ ord₁ R₁ →
    Toy.Sim.IsForwardSim L₂ L₃ ord₂ R₂ → Toy.Sim.IsForwardSim L₁ L₃ (Toy.Sim.compOrd ord₁ ord₂) (Toy.Sim.compRel R₁ R₂)
@Toy.Sim.isForwardSim_preserves_non_goesWrong_behaviors : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  Toy.Sim.IsForwardSim L₁ L₂ ord R →
    ∀ {b : Toy.Sim.Behavior E Res},
      Toy.Sim.HasBehavior L₁ b → (∀ (t : List E), b ≠ Toy.Sim.Behavior.goesWrong t) → Toy.Sim.HasBehavior L₂ b
@Toy.Sim.refinedBy_neverGoesWrong_behaviors_subset : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res},
  Toy.Sim.RefinedBy L₁ L₂ →
    Toy.Sim.NeverGoesWrong L₁ → ∀ {b : Toy.Sim.Behavior E Res}, Toy.Sim.HasBehavior L₂ b → Toy.Sim.HasBehavior L₁ b
@Toy.Sim.wf_fsimInit_fsimStep_preserve_diverges : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res} {I : Type}
  {ord : I → I → Prop} {R : I → Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop},
  WellFounded ord →
    Toy.Sim.FSimInit L₁ L₂ R →
      Toy.Sim.FSimStep L₁ L₂ ord R →
        ∀ {t : List E},
          Toy.Sim.HasBehavior L₁ (Toy.Sim.Behavior.diverges t) → Toy.Sim.HasBehavior L₂ (Toy.Sim.Behavior.diverges t)
```

#### Machine-printed statements of supporting declarations

Output of `#check @<name>` (with `set_option format.width 100` and `set_option pp.fieldNotation false`), in the built environment, for the supporting lemmas, helper theorems and boundary facts that **Findings** or **Boundaries** cite by name and whose statements are not quoted elsewhere in this report. They are not card results; like every declaration of the library they are covered by `lake build` and the axiom audit. The systems they mention are quoted under **Findings → Concrete systems**.

```lean
@Toy.Sim.NeverGoesWrong.exists_init : ∀ {E Res : Type} {L : Toy.Sim.LTS E Res},
  Toy.Sim.NeverGoesWrong L → ∃ s, Toy.Sim.LTS.init L s
@Toy.Sim.compOrd_iff_lex_of_transitive : ∀ {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop},
  (∀ (a b c : I₂), ord₂ a b → ord₂ b c → ord₂ a c) →
    ∀ (p q : I₂ × I₁),
      Toy.Sim.compOrd ord₁ ord₂ p q ↔
        ord₂ (Prod.fst p) (Prod.fst q) ∨ Prod.fst p = Prod.fst q ∧ ord₁ (Prod.snd p) (Prod.snd q)
@Toy.Sim.Cex.compOrd_iff_naiveCompOrd_of_transitive : ∀ {I₁ I₂ : Type} {ord₁ : I₁ → I₁ → Prop} {ord₂ : I₂ → I₂ → Prop},
  (∀ (a b c : I₂), ord₂ a b → ord₂ b c → ord₂ a c) →
    ∀ (p q : I₂ × I₁), Toy.Sim.compOrd ord₁ ord₂ p q ↔ Toy.Sim.Cex.naiveCompOrd ord₁ ord₂ p q
@Toy.Sim.Star.trans : ∀ {E Res : Type} {L : Toy.Sim.LTS E Res} {s s' s'' : Toy.Sim.LTS.State L} {t t' : List E},
  Toy.Sim.Star L s t s' → Toy.Sim.Star L s' t' s'' → Toy.Sim.Star L s (t ++ t') s''
@Toy.Sim.isForwardSim_id : ∀ {E Res : Type} (L : Toy.Sim.LTS E Res),
  Toy.Sim.IsForwardSim L L (fun x x_1 => False) fun x s s' => s = s'
@Toy.Sim.isForwardSim_measure_iff : ∀ {E Res : Type} {L₁ L₂ : Toy.Sim.LTS E Res}
  (R : Toy.Sim.LTS.State L₁ → Toy.Sim.LTS.State L₂ → Prop) (m : Toy.Sim.LTS.State L₁ → Nat),
  (Toy.Sim.IsForwardSim L₁ L₂ (fun i' i => m i' < m i) fun i s₁ s₂ => i = s₁ ∧ R s₁ s₂) ↔
    (∀ (s₁ : Toy.Sim.LTS.State L₁), Toy.Sim.LTS.init L₁ s₁ → ∃ s₂, Toy.Sim.LTS.init L₂ s₂ ∧ R s₁ s₂) ∧
      (∀ (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (r : Res),
          R s₁ s₂ → Toy.Sim.LTS.final L₁ s₁ r → Toy.Sim.LTS.final L₂ s₂ r) ∧
        ∀ (s₁ : Toy.Sim.LTS.State L₁) (s₂ : Toy.Sim.LTS.State L₂) (e : Option E) (s₁' : Toy.Sim.LTS.State L₁),
          R s₁ s₂ →
            Toy.Sim.LTS.step L₁ s₁ e s₁' →
              ∃ s₂',
                (Toy.Sim.Plus L₂ s₂ (Toy.Sim.obs e) s₂' ∨ Toy.Sim.Star L₂ s₂ (Toy.Sim.obs e) s₂' ∧ m s₁' < m s₁) ∧
                  R s₁' s₂'
Toy.Sim.Ex.done_neverGoesWrong : ∀ (r : Nat), Toy.Sim.NeverGoesWrong (Toy.Sim.Ex.Done r)
Toy.Sim.Examples.refinedBy_vacuous_for_target_without_behavior : ∀ (L : Toy.Sim.LTS Nat Nat),
  Toy.Sim.RefinedBy L Toy.Sim.Ex.Chatter
Toy.Sim.Cex.cex_forwardSim_goesWrong_target_without_behavior : Toy.Sim.IsForwardSim Toy.Sim.Ex.StuckNow
    Toy.Sim.Ex.Chatter Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relTrue ∧
  Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow (Toy.Sim.Behavior.goesWrong []) ∧
    ∀ (b : Toy.Sim.Behavior Nat Nat), ¬Toy.Sim.HasBehavior Toy.Sim.Ex.Chatter b
Toy.Sim.Boundary.refinedBy_not_antisymmetric : Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow Toy.Sim.Ex.NoInit ∧
  Toy.Sim.RefinedBy Toy.Sim.Ex.NoInit Toy.Sim.Ex.StuckNow ∧ Toy.Sim.Ex.StuckNow ≠ Toy.Sim.Ex.NoInit
Toy.Sim.Boundary.mutual_refinedBy_different_behaviors : Toy.Sim.RefinedBy Toy.Sim.Boundary.StuckOrDone
    Toy.Sim.Ex.StuckNow ∧
  Toy.Sim.RefinedBy Toy.Sim.Ex.StuckNow Toy.Sim.Boundary.StuckOrDone ∧
    Toy.Sim.HasBehavior Toy.Sim.Boundary.StuckOrDone (Toy.Sim.Behavior.terminates [] 0) ∧
      ¬Toy.Sim.HasBehavior Toy.Sim.Ex.StuckNow (Toy.Sim.Behavior.terminates [] 0)
Toy.Sim.Boundary.refinedBy_blind_to_infinite_event_runs : (∀ (b : Toy.Sim.Behavior Nat Nat),
    Toy.Sim.HasBehavior Toy.Sim.Boundary.DoneOrChatter b ↔ Toy.Sim.HasBehavior (Toy.Sim.Ex.Done 0) b) ∧
  Toy.Sim.RefinedBy (Toy.Sim.Ex.Done 0) Toy.Sim.Boundary.DoneOrChatter ∧
    (∃ f,
        Toy.Sim.LTS.init Toy.Sim.Boundary.DoneOrChatter (f 0) ∧
          ∀ (n : Nat), Toy.Sim.LTS.step Toy.Sim.Boundary.DoneOrChatter (f n) (some 0) (f (n + 1))) ∧
      Toy.Sim.NoBackwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Boundary.DoneOrChatter
Toy.Sim.Boundary.refinedBy_may_drop_termination : Toy.Sim.NeverGoesWrong Toy.Sim.Boundary.TermOrDiverge ∧
  Toy.Sim.HasBehavior Toy.Sim.Boundary.TermOrDiverge (Toy.Sim.Behavior.terminates [] 0) ∧
    Toy.Sim.HasBehavior Toy.Sim.Boundary.TermOrDiverge (Toy.Sim.Behavior.diverges []) ∧
      Toy.Sim.RefinedBy Toy.Sim.Boundary.TermOrDiverge Toy.Sim.Ex.Loop ∧
        ¬Toy.Sim.HasBehavior Toy.Sim.Ex.Loop (Toy.Sim.Behavior.terminates [] 0)
Toy.Sim.Boundary.resolving_nondeterminism_needs_backward_simulation : Toy.Sim.NeverGoesWrong
    (Toy.Sim.Ex.TwoBranch none none 0 1) ∧
  Toy.Sim.Determinate Eq (Toy.Sim.Ex.Done 0) ∧
    Toy.Sim.IsBackwardSim (Toy.Sim.Ex.TwoBranch none none 0 1) (Toy.Sim.Ex.Done 0) Toy.Sim.Cex.emptyOrd
        Toy.Sim.Boundary.chooseRel ∧
      Toy.Sim.RefinedBy (Toy.Sim.Ex.TwoBranch none none 0 1) (Toy.Sim.Ex.Done 0) ∧
        ¬∃ I ord R, Toy.Sim.IsForwardSim (Toy.Sim.Ex.TwoBranch none none 0 1) (Toy.Sim.Ex.Done 0) ord R
Toy.Sim.Boundary.flip_conclusion_with_unreachable_nondeterminism : Toy.Sim.IsForwardSim (Toy.Sim.Ex.Done 0)
    Toy.Sim.Boundary.DoneWithJunk Toy.Sim.Cex.emptyOrd Toy.Sim.Cex.relToFalse ∧
  ¬Toy.Sim.StepFunctional Toy.Sim.Boundary.DoneWithJunk ∧
    ¬Toy.Sim.Determinate Eq Toy.Sim.Boundary.DoneWithJunk ∧
      Toy.Sim.IsBackwardSim (Toy.Sim.Ex.Done 0) Toy.Sim.Boundary.DoneWithJunk Toy.Sim.Cex.emptyOrd
          Toy.Sim.Cex.relToFalse ∧
        ∀ (i s₁ : Unit) (s₂ : Bool), Toy.Sim.Cex.relToFalse i s₁ s₂ → ∃ i', Toy.Sim.Cex.relToFalse i' s₁ s₂
```

### Primary sources

**CompCert Coq development** — repository `AbsInt/CompCert`, release tag `v3.16`, commit `a4ad87b17898cf7b7c8638c32ad694a15f7c0032` (tag resolved to this commit through the GitHub API on 2026-11-20). Files read at that commit, with SHA-256 of the fetched file: `common/Smallstep.v` (`5b98c051f4b412f1f6cb2d7d3ca0dbf33b0db48f6e98a2f8698859f6b16db400`), `common/Behaviors.v` (`474bc162f3b5083f0f8aedd59ccaaeec49a7d7f8fa16105c8534924058a7cd17`), `driver/Compiler.v` (`d235bb45e166d0144eaf864794484bfaf01c1bd97ae1a129ae7f550e034fa972`). Line numbers below refer to that commit.

| File | Declaration (line) | Counterpart here |
| :--- | :--- | :--- |
| `common/Smallstep.v` | `fsim_properties` (566) | `IsForwardSim` and its clauses |
| `common/Smallstep.v` | `forward_simulation_star_wf` (659), `forward_simulation_star` (688) | `isForwardSim_measure_iff` (reference lemma) |
| `common/Smallstep.v` | `simulation_star` (937) | `fsimInit_fsimStep_partial_run_simulated` |
| `common/Smallstep.v` | `forever_silent` (399), `simulation_forever_silent` (972) | `SilentDiv`, `wf_fsimInit_fsimStep_preserve_diverges` |
| `common/Smallstep.v` | `compose_forward_simulations` (1003), composite order (1011) | `isForwardSim_comp`, `compOrd`, `compRel` |
| `common/Smallstep.v` | `single_events` (1047), `receptive` (1050), `determinate` (1058) | `Receptive`, `Determinate` |
| `common/Smallstep.v` | `safe` (1274), `bsim_properties` (1289) | `Safe`, `IsBackwardSim` and its clauses |
| `common/Smallstep.v` | section `FORWARD_TO_BACKWARD` (1608), `forward_to_backward_simulation` (1863) | `forwardSim_receptive_determinate_gives_backwardSim` (CompCert's statement does not state "contains R") |
| `common/Smallstep.v` | `atomic` (1924), `factor_forward_simulation` (2004), `strongly_receptive` (2130) | not modelled (multi-event steps) |
| `common/Behaviors.v` | `program_behavior` (41), `behavior_improves` (81), `behavior_improves_refl` (84), `behavior_improves_trans` (90), `behavior_improves_bot` (102), `program_behaves` (141), `program_goes_initially_wrong` (145) | `Behavior` (without `Reacts`), `Improves`, `HasBehavior` |
| `common/Behaviors.v` | `program_behaves_exists` (264) | no counterpart (relies on `Reacts`) |
| `common/Behaviors.v` | `forward_simulation_state_behaves` (284), `forward_simulation_behavior_improves` (316), `forward_simulation_same_safe_behavior` (337) | forward preservation (the second has no counterpart here) |
| `common/Behaviors.v` | `backward_simulation_behavior_improves` (493), `backward_simulation_same_safe_behavior` (519) | `backwardSim_gives_refinedBy`, `backwardSim_neverGoesWrong_behaviors_subset` |
| `driver/Compiler.v` | `compose_forward_simulations` uses (20 uses, lines 369–406), `cstrategy_semantic_preservation` (353; flip at 413–416), `c_semantic_preservation` (419; leading backward simulation, 425), `transf_c_program_correct` (446) | `fsimChain_collapse`, `fsimChain_receptive_first_determinate_last_gives_refinedBy`; the nondeterminism non-claim |

Quoted definitions (verbatim):

```coq
(* common/Smallstep.v, lines 566-584 *)
Record fsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    fsim_order_wf: well_founded order;
    fsim_match_initial_states:
      forall s1, initial_state L1 s1 ->
      exists i, exists s2, initial_state L2 s2 /\ match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i))
      /\ match_states i' s1' s2';
    fsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

(* common/Smallstep.v, lines 937-940 *)
Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ match_states i' s1' s2'.

(* common/Smallstep.v, lines 972-975 *)
Lemma simulation_forever_silent:
  forall i s1 s2,
  Forever_silent L1 s1 -> match_states i s1 s2 ->
  Forever_silent L2 s2.

(* common/Smallstep.v, lines 1003-1004 and 1010-1011 *)
Lemma compose_forward_simulations:
  forall L1 L2 L3, forward_simulation L1 L2 -> forward_simulation L2 L3 -> forward_simulation L1 L3.
  (* ... *)
  set (ff_index := (index' * index)%type).
  set (ff_order := lex_ord (clos_trans _ order') order).

(* common/Smallstep.v, lines 1047-1071 *)
Definition single_events (L: semantics) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (symbolenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (symbolenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

(* common/Smallstep.v, lines 1274-1278 *)
Definition safe (L: semantics) (s: state L) : Prop :=
  forall s',
  Star L s E0 s' ->
  (exists r, final_state L s' r)
  \/ (exists t, exists s'', Step L s' t s'').

(* common/Smallstep.v, lines 1289-1315 *)
Record bsim_properties (L1 L2: semantics) (index: Type)
                       (order: index -> index -> Prop)
                       (match_states: index -> state L1 -> state L2 -> Prop) : Prop := {
    bsim_order_wf: well_founded order;
    bsim_initial_states_exist:
      forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
    bsim_match_initial_states:
      forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
      exists i, exists s1', initial_state L1 s1' /\ match_states i s1' s2;
    bsim_match_final_states:
      forall i s1 s2 r,
      match_states i s1 s2 -> safe L1 s1 -> final_state L2 s2 r ->
      exists s1', Star L1 s1 E0 s1' /\ final_state L1 s1' r;
    bsim_progress:
      forall i s1 s2,
      match_states i s1 s2 -> safe L1 s1 ->
      (exists r, final_state L2 s2 r) \/
      (exists t, exists s2', Step L2 s2 t s2');
    bsim_simulation:
      forall s2 t s2', Step L2 s2 t s2' ->
      forall i s1, match_states i s1 s2 -> safe L1 s1 ->
      exists i', exists s1',
         (Plus L1 s1 t s1' \/ (Star L1 s1 t s1' /\ order i' i))
      /\ match_states i' s1' s2';
    bsim_public_preserved:
      forall id, Senv.public_symbol (symbolenv L2) id = Senv.public_symbol (symbolenv L1) id
  }.

(* common/Smallstep.v, lines 1863-1866 *)
Lemma forward_to_backward_simulation:
  forall L1 L2,
  forward_simulation L1 L2 -> receptive L1 -> determinate L2 ->
  backward_simulation L1 L2.
```

```coq
(* common/Behaviors.v, lines 41-45 *)
Inductive program_behavior: Type :=
  | Terminates: trace -> int -> program_behavior
  | Diverges: trace -> program_behavior
  | Reacts: traceinf -> program_behavior
  | Goes_wrong: trace -> program_behavior.

(* common/Behaviors.v, lines 81-82 *)
Definition behavior_improves (beh1 beh2: program_behavior) : Prop :=
  beh1 = beh2 \/ exists t, beh1 = Goes_wrong t /\ behavior_prefix t beh2.

(* common/Behaviors.v, lines 141-147 *)
Inductive program_behaves: program_behavior -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves s beh ->
      program_behaves beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves (Goes_wrong E0).

(* common/Behaviors.v, lines 316-319 *)
Theorem forward_simulation_behavior_improves:
  forall L1 L2, forward_simulation L1 L2 ->
  forall beh1, program_behaves L1 beh1 ->
  exists beh2, program_behaves L2 beh2 /\ behavior_improves beh1 beh2.

(* common/Behaviors.v, lines 337-341 *)
Corollary forward_simulation_same_safe_behavior:
  forall L1 L2, forward_simulation L1 L2 ->
  forall beh,
  program_behaves L1 beh -> not_wrong beh ->
  program_behaves L2 beh.

(* common/Behaviors.v, lines 493-496 *)
Theorem backward_simulation_behavior_improves:
  forall L1 L2, backward_simulation L1 L2 ->
  forall beh2, program_behaves L2 beh2 ->
  exists beh1, program_behaves L1 beh1 /\ behavior_improves beh1 beh2.

(* common/Behaviors.v, lines 519-522 *)
Corollary backward_simulation_same_safe_behavior:
  forall L1 L2, backward_simulation L1 L2 ->
  (forall beh, program_behaves L1 beh -> not_wrong beh) ->
  (forall beh, program_behaves L2 beh -> program_behaves L1 beh).
```

```coq
(* driver/Compiler.v, lines 353-357 *)
Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
  /\ backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
  (* ... lines 413-416 of the proof: *)
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.

(* driver/Compiler.v, lines 419-425 *)
Theorem c_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
```

**Articles and mechanizations** (bibliographic records checked against Crossref on 2026-11-20; which passages were read is stated in each card's prior-art entry):

- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, "Relaxed-memory concurrency and verified compilation", POPL 2011 (Proceedings of the 38th annual ACM SIGPLAN-SIGACT symposium on Principles of programming languages), pp. 43–54, doi:10.1145/1926385.1926393. Section 4, Definitions 2–5, Theorem 2 ("If R is a threadwise forward simulation from S to T, S is receptive, and T is determinate, then there is a threadwise backward simulation that contains R."). (Crossref renders the first author's name as "Ŝevčik".)
- J. Ševčík, V. Vafeiadis, F. Zappa Nardelli, S. Jagannathan, P. Sewell, "CompCertTSO: A Verified Compiler for Relaxed-Memory Concurrency", Journal of the ACM 60(3), article 22, pp. 22:1–22:50, 2013, doi:10.1145/2487241.2487248 (Crossref title "CompCertTSO"). Body not examined.
- X. Leroy, "A Formally Verified Compiler Back-end", Journal of Automated Reasoning 43(4):363–446, 2009, doi:10.1007/s10817-009-9155-4. Sections 2.1 and 3.7 (Definition 12, Theorem 4).
- X. Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7):107–115, 2009, doi:10.1145/1538788.1538814. Sections 2.1, 2.3.
- N. Lynch, F. Vaandrager, "Forward and Backward Simulations: Part I: Untimed Systems", Information and Computation 121(2):214–233, 1995, doi:10.1006/inco.1995.1134 (Crossref title "Forward and Backward Simulations"). Section 3.2. Terminology warning: in that article a forward and a backward simulation from A to B both follow the steps of A and both establish trace inclusion of A in B; they differ in whether the matching B-step is found from the pre-state or from the post-state. Here (as in CompCert) *forward* and *backward* say which program leads: source steps matched by the target, or target steps matched by the source.
- M. Desharnais-Schäfer, "A Generic Framework for Verified Compilers", Archive of Formal Proofs, entry `VeriComp`, first published February 10, 2020. Read in the entry's release archive for Isabelle2026, dated 2026-10-26: https://isa-afp.org/release/afp-VeriComp-2026-10-26.tar.gz (SHA-256 of the downloaded archive `a45a410e58aa9850f2e3195010e9a86c1469c35e5f1846eea44067ee4662a547`; SHA-256 of `VeriComp/Simulation.thy` inside it `012d131b8d40f5fb7c309e3d0a3d4814855f1c1369971250766ebc708312bc0d`). Line numbers refer to that archive. `VeriComp/Behaviour.thy` lines 5–6: `datatype 'state behaviour = Terminates 'state | Diverges | is_wrong: Goes_wrong 'state`. `VeriComp/Simulation.thy`: locale `backward_simulation` (line 13), locale `forward_simulation` (line 148; its simulation clause, rendered here with Unicode symbols, is "`match i s1 s2 ⟹ step1 s1 s1' ⟹ (∃i' s2'. step2⁺⁺ s2 s2' ∧ match i' s1' s2') ∨ (∃i'. match i' s1' s2 ∧ i' ⊏ i)`"), lemma `state_behaves_forward_to_backward` (line 273; assumes `right_unique step2` and `L1.safe s1`), and lemma `forward_simulation_composition` (line 699, quoted below; `⁺⁺` is the transitive closure and `prod.swap` reorders the index pair). The entry page https://isa-afp.org/entries/VeriComp.html and its "download latest" link `afp-VeriComp-current.tar.gz` follow each new Isabelle release, so they identify no fixed text; the dated release archive and its hash are the identity used here. The release is material: the entry's history records under July 10, 2024 "Generalized the definition of bisimulation to have distinct orderings for forward and backward simulations. Added lemmas for composition of forward simulations and bisimulations.", and `forward_simulation_composition` is absent from the release archives dated 2020-02-25 (Isabelle2019, SHA-256 `ca6c0f1e3eedc5fc1d83c8a240c1ea10764861798ec7916b229412ebbc55c377`) and 2024-05-26 (Isabelle2024, SHA-256 `1802d0f77157400cd939f0247d36e40f934ff4e8db03b60a2584bc8a4b6c35be`) and present in the archive dated 2025-03-17 (Isabelle2025, SHA-256 `42baa98c08b3c524c8fe859bcdc05e2f1d1817ca1cc616f87d36f6ed1047a7e6`), whose `VeriComp/Simulation.thy` is byte-identical to the one in the 2026-10-26 archive. Related paper: M. Desharnais, S. Brunthaler, "Towards efficient and verified virtual machines for dynamic languages", CPP 2021, pp. 61–75, doi:10.1145/3437992.3439923.

```text
(* VeriComp/Simulation.thy, lines 699-704, release archive 2026-10-26 *)
lemma forward_simulation_composition:
  assumes
    "forward_simulation step1 final1 step2 final2 match1 order1"
    "forward_simulation step2 final2 step3 final3 match2 order2"
  defines "ORDER \<equiv> \<lambda>i i'. lex_prodp order2\<^sup>+\<^sup>+ order1 (prod.swap i) (prod.swap i')"
  shows "forward_simulation step1 final1 step3 final3 (rel_comp match1 match2) ORDER"
```

- M. Cho, Y. Song, D. Lee, L. Gäher, D. Dreyer, "Stuttering for Free", Proceedings of the ACM on Programming Languages 7(OOPSLA2):1677–1704, 2023, doi:10.1145/3622857. Abstract only.

**Further reading** (bibliographic records only; contents not examined, so none of these is cited as prior art for a specific result): R. Milner, "An algebraic definition of simulation between programs", IJCAI 1971; F. L. Morris, "Advice on structuring compilers and proving them correct", POPL 1973, doi:10.1145/512927.512941; M. Abadi, L. Lamport, "The existence of refinement mappings", TCS 82(2), 1991, doi:10.1016/0304-3975(91)90224-P; K. S. Namjoshi, "A simple characterization of stuttering bisimulation", FSTTCS 1997, doi:10.1007/bfb0058037; P. Manolios, "Correctness of Pipelined Machines", FMCAD 2000, doi:10.1007/3-540-40922-x_11; W.-P. de Roever, K. Engelhardt, "Data Refinement: Model-Oriented Proof Methods and their Comparison", CUP 1998, doi:10.1017/cbo9780511663079; D. Sangiorgi, "Introduction to Bisimulation and Coinduction", CUP 2011, doi:10.1017/cbo9780511777110; A. Lochbihler, "Verifying a Compiler for Java Threads", ESOP 2010, doi:10.1007/978-3-642-11957-6_23; Y. K. Tan et al., "A new verified compiler backend for CakeML", ICFP 2016, doi:10.1145/2951913.2951924, and "The verified CakeML compiler backend", JFP 29, 2019, doi:10.1017/S0956796818000229; R. Kumar et al., "CakeML: a verified implementation of ML", POPL 2014, doi:10.1145/2535838.2535841; D. Patterson, A. Ahmed, "The next 700 compiler correctness theorems (functional pearl)", PACMPL 3(ICFP), 2019, doi:10.1145/3341689; G. Stewart et al., "Compositional CompCert", POPL 2015, doi:10.1145/2676726.2676985; C.-K. Hur et al., "The marriage of bisimulations and Kripke logical relations", POPL 2012, doi:10.1145/2103656.2103666; G. Neis et al., "Pilsner: a compositionally verified compiler for a higher-order imperative language", ICFP 2015, doi:10.1145/2784731.2784764; Y. Song et al., "CompCertM: CompCert with C-assembly linking and lightweight modular verification", PACMPL 4(POPL), 2020, doi:10.1145/3371091; J. Koenig, Z. Shao, "CompCertO: compiling certified open C components", PLDI 2021, doi:10.1145/3453483.3454097; M. Sammler et al., "DimSum: A Decentralized Approach to Multi-language Semantics and Verification", PACMPL 7(POPL), 2023, doi:10.1145/3571220.

**Observation dates.** Build, axiom audit, statement hashes, CompCert source reading at the pinned commit, Lean tag resolution and Crossref checks: 2026-11-20. Archive of Formal Proofs entry `VeriComp`: entry page read, and the release archives dated 2020-02-25, 2024-05-26, 2025-03-17 and 2026-10-26 downloaded, hashed and read: 2026-11-20. The prior-art passages quoted inside the cards were read at the sources named there; their wording is preserved from those readings.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed beyond the toolchain download by `elan`; the package has no Lake dependencies.

**Primary command**, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, fails if any Lean source contains `sorry`, `admit`, `native_decide` or an `axiom` declaration, then runs an audit program (embedded in the script) that uses Lean's `collectAxioms` to check that every declaration of the library depends only on `propext`, `Classical.choice`, `Quot.sound`, and recomputes, for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s) and every name in `audit/statements.json`, the SHA-256 of the statement (`repr` of its type) and of its definition closure (`repr` of the type, and of the value for non-theorems, of every package-local constant reachable from the statement, sorted, newline-joined; theorem bodies excluded), comparing them with `audit/statements.json`. It prints `REVALIDATED` and exits 0 iff all checks pass. A pass establishes exactly these facts: the statements recorded here are unchanged (including every definition they depend on) and are kernel-checked with standard axioms only; it says nothing about CompCert.

**Manual equivalent** (the same checks without the script), from the package directory:

```sh
cd lean
lake build                                   # must succeed with no errors and no "declaration uses `sorry`" warnings
lake env lean PrintAxioms.lean               # `#print axioms` for every name referenced by results.json
lake env lean StatementAudit.lean > /tmp/statement_audit.txt
python3 - <<'EOF'
import hashlib, json, re
a = json.loads(re.search(r"REVALIDATE_JSON (\{.*\})", open("/tmp/statement_audit.txt").read()).group(1))
rec = json.load(open("../audit/statements.json"))["statements"]
bad = [s["name"] for s in a["stmts"] if rec.get(s["name"]) != {
    "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
    "closure_size": len(s["closure"]),
    "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest()}]
ax = [d["name"] for d in a["decls"] if set(d["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}]
print("hashed", len(a["stmts"]), "mismatches", len(bad), "declarations", len(a["decls"]), "non-standard axioms", len(ax))
EOF
```

Expected output of the last command: `hashed 108 mismatches 0 declarations 674 non-standard axioms 0`. `lean/PrintAxioms.lean` and `lean/StatementAudit.lean` are outside the library target (not built by `lake build`); every line printed by the former must mention only `propext`, `Classical.choice`, `Quot.sound` (or "does not depend on any axioms"). `lean/StatementAudit.lean` is the audit program embedded in `support/revalidate.py`, instantiated with the recorded names: it prints, per library declaration, its axioms, and per recorded name the `repr` of its type and the sorted `repr` texts of its definition closure, which are exactly the texts hashed into `audit/statements.json`.

**Cheap discriminating checks after a change.** If only proofs changed, the statement and closure hashes must be unchanged; any hash change means a statement or a definition it depends on changed, and every card that references the name must be re-read. To revalidate the modelling bridge against a newer CompCert, re-read the quoted declarations of `common/Smallstep.v`, `common/Behaviors.v` and `driver/Compiler.v` at the new commit and compare them with the quotes under **Evidence**; no cheaper check exists for the bridge, because it is not mechanized.

