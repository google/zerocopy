/-
  Event-Based Decentralized Linking with Dual Nondeterminism (Toy Model)

  Captures:
  1. DimSum-style transition systems with demonic choice across transitions and
     angelic choice inside each target set (`Step : S -> Option E -> (S -> Prop) -> Prop`).
  2. Greatest-fixpoint (coinductive) branching-sensitive refinement `Refines`
     with reflexivity and transitivity (`refines_refl`, `refines_trans`).
  3. Turn-based event linking `linkMod` and its horizontal compositionality
     (`link_horizontal_comp`).
  4. Polarity mismatch counterexample between DimSum polarity (no step = NB bottom,
     empty target set = UB top) and Melocoton `umrel` polarity (no step = stuck/UB,
     empty target set = NB vacuous): `polarity_mismatch_breaks_refinement`.

  Model-system relation: none proved. This is a standalone Mathlib-free Lean 4
  toy mechanization illustrating the formal structure of the cited papers.
-/

namespace EventLinking

/-- A module over visible event alphabet `E` with dual nondeterminism.
    In DimSum polarity:
    - Multiple `step s a P` derivations represent demonic choice.
    - Multiple states `s'` satisfying `P s'` represent angelic choice.
    - No `step s a P` represents NB (no behavior, bottom of refinement).
    - `step s a (fun _ => False)` represents UB (undefined behavior, top of refinement). -/
structure Module (E : Type) where
  State : Type
  step : State → Option E → (State → Prop) → Prop
  init : State

/-- Weak-style single-event or silent-step simulation relation (strong on `Option E`
    for simplicity in this toy model: silent steps match silent steps and visible
    events match identical visible events). -/
def IsSim {E : Type} (M1 M2 : Module E) (R : M1.State → M2.State → Prop) : Prop :=
  ∀ s1 s2 a P1, R s1 s2 → M1.step s1 a P1 →
    ∃ P2, M2.step s2 a P2 ∧ ∀ s2', P2 s2' → ∃ s1', P1 s1' ∧ R s1' s2'

/-- Greatest-fixpoint refinement `M1 ⪯ M2` in DimSum polarity. -/
def Refines {E : Type} (M1 M2 : Module E) : Prop :=
  ∃ R : M1.State → M2.State → Prop, R M1.init M2.init ∧ IsSim M1 M2 R

theorem refines_refl {E : Type} (M : Module E) : Refines M M := by
  refine ⟨Eq, rfl, ?_⟩
  intro s1 s2 a P1 hEq hStep
  subst hEq
  exact ⟨P1, hStep, fun s' hP => ⟨s', hP, rfl⟩⟩

theorem refines_trans {E : Type} {M1 M2 M3 : Module E}
    (h12 : Refines M1 M2) (h23 : Refines M2 M3) : Refines M1 M3 := by
  rcases h12 with ⟨R12, hInit12, hSim12⟩
  rcases h23 with ⟨R23, hInit23, hSim23⟩
  refine ⟨fun s1 s3 => ∃ s2, R12 s1 s2 ∧ R23 s2 s3, ⟨M2.init, hInit12, hInit23⟩, ?_⟩
  intro s1 s3 a P1 ⟨s2, h1, h2⟩ hStep1
  rcases hSim12 s1 s2 a P1 h1 hStep1 with ⟨P2, hStep2, hMatch12⟩
  rcases hSim23 s2 s3 a P2 h2 hStep2 with ⟨P3, hStep3, hMatch23⟩
  refine ⟨P3, hStep3, ?_⟩
  intro s3' hP3
  rcases hMatch23 s3' hP3 with ⟨s2', hP2, hR23⟩
  rcases hMatch12 s2' hP2 with ⟨s1', hP1, hR12⟩
  exact ⟨s1', hP1, s2', hR12, hR23⟩

/-- Turn ownership in turn-based binary linking (mirroring DimSum's `{E, L, R}`). -/
inductive Turn where
  | ext
  | left
  | right
  deriving DecidableEq, Repr

/-- Target-set lifting for updating only the left component of a linked state. -/
def liftLeft {S1 S2 : Type} (P1 : S1 → Prop) (s2 : S2) (t' : Turn) :
    (Turn × S1 × S2) → Prop :=
  fun st => st.1 = t' ∧ P1 st.2.1 ∧ st.2.2 = s2

/-- Target-set lifting for updating only the right component of a linked state. -/
def liftRight {S1 S2 : Type} (s1 : S1) (P2 : S2 → Prop) (t' : Turn) :
    (Turn × S1 × S2) → Prop :=
  fun st => st.1 = t' ∧ st.2.1 = s1 ∧ P2 st.2.2

/-- A DimSum-style event-based linking combinator parameterized by a routing
    function `route : E -> Turn`:
    - Silent (`none`) steps run in the currently active module without changing turn.
    - Visible (`some e`) outgoing events from `left` or `right` transfer control:
      * If `route e` is the opposite module, the event is internalized (`none`) and
        delivered to the peer (modeled as a handoff step whose next turn is the peer).
      * If `route e = Turn.ext`, the event is emitted externally (`some e`) and
        control yields to `Turn.ext`.
    - When `Turn.ext` holds control, an incoming external event `some e` routed to
      `left` or `right` activates that module. -/
inductive LinkStep {E : Type} (route : E → Turn) (M1 M2 : Module E) :
    (Turn × M1.State × M2.State) → Option E → ((Turn × M1.State × M2.State) → Prop) → Prop where
  | leftTau {s1 s2 P1} :
      M1.step s1 none P1 →
      LinkStep route M1 M2 (.left, s1, s2) none (liftLeft P1 s2 .left)
  | rightTau {s1 s2 P2} :
      M2.step s2 none P2 →
      LinkStep route M1 M2 (.right, s1, s2) none (liftRight s1 P2 .right)
  | leftToRight {s1 s2 e P1} :
      route e = .right →
      M1.step s1 (some e) P1 →
      LinkStep route M1 M2 (.left, s1, s2) none (liftLeft P1 s2 .right)
  | rightToLeft {s1 s2 e P2} :
      route e = .left →
      M2.step s2 (some e) P2 →
      LinkStep route M1 M2 (.right, s1, s2) none (liftRight s1 P2 .left)
  | leftToExt {s1 s2 e P1} :
      route e = .ext →
      M1.step s1 (some e) P1 →
      LinkStep route M1 M2 (.left, s1, s2) (some e) (liftLeft P1 s2 .ext)
  | rightToExt {s1 s2 e P2} :
      route e = .ext →
      M2.step s2 (some e) P2 →
      LinkStep route M1 M2 (.right, s1, s2) (some e) (liftRight s1 P2 .ext)
  | extToLeft {s1 s2 e P1} :
      route e = .left →
      M1.step s1 (some e) P1 →
      LinkStep route M1 M2 (.ext, s1, s2) (some e) (liftLeft P1 s2 .left)
  | extToRight {s1 s2 e P2} :
      route e = .right →
      M2.step s2 (some e) P2 →
      LinkStep route M1 M2 (.ext, s1, s2) (some e) (liftRight s1 P2 .right)

def linkMod {E : Type} (route : E → Turn) (M1 M2 : Module E) : Module E where
  State := Turn × M1.State × M2.State
  step := LinkStep route M1 M2
  init := (.ext, M1.init, M2.init)

/-- Horizontal compositionality of event-based linking (`link_horizontal_comp`):
    if `M1 ⪯ M1'` and `M2 ⪯ M2'`, then `linkMod route M1 M2 ⪯ linkMod route M1' M2'`. -/
theorem link_horizontal_comp {E : Type} (route : E → Turn)
    {M1 M1' M2 M2' : Module E}
    (h1 : Refines M1 M1') (h2 : Refines M2 M2') :
    Refines (linkMod route M1 M2) (linkMod route M1' M2') := by
  rcases h1 with ⟨R1, hInit1, hSim1⟩
  rcases h2 with ⟨R2, hInit2, hSim2⟩
  let R : (Turn × M1.State × M2.State) → (Turn × M1'.State × M2'.State) → Prop :=
    fun st st' => st.1 = st'.1 ∧ R1 st.2.1 st'.2.1 ∧ R2 st.2.2 st'.2.2
  refine ⟨R, ⟨rfl, hInit1, hInit2⟩, ?_⟩
  intro st1 st2 a P1 ⟨hTurn, hR1, hR2⟩ hStep
  cases hStep with
  | leftTau hM1 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim1 _ _ _ _ hR1 hM1 with ⟨P1', hM1', hMatch⟩
    refine ⟨liftLeft P1' s2' .left, LinkStep.leftTau hM1', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u1' hu1' with ⟨u1, hu1, hR1'⟩
    exact ⟨(.left, u1, _), ⟨rfl, hu1, rfl⟩, ⟨ht''.symm, hR1', hu2' ▸ hR2⟩⟩
  | rightTau hM2 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim2 _ _ _ _ hR2 hM2 with ⟨P2', hM2', hMatch⟩
    refine ⟨liftRight s1' P2' .right, LinkStep.rightTau hM2', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u2' hu2' with ⟨u2, hu2, hR2'⟩
    exact ⟨(.right, _, u2), ⟨rfl, rfl, hu2⟩, ⟨ht''.symm, hu1' ▸ hR1, hR2'⟩⟩
  | leftToRight hRoute hM1 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim1 _ _ _ _ hR1 hM1 with ⟨P1', hM1', hMatch⟩
    refine ⟨liftLeft P1' s2' .right, LinkStep.leftToRight hRoute hM1', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u1' hu1' with ⟨u1, hu1, hR1'⟩
    exact ⟨(.right, u1, _), ⟨rfl, hu1, rfl⟩, ⟨ht''.symm, hR1', hu2' ▸ hR2⟩⟩
  | rightToLeft hRoute hM2 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim2 _ _ _ _ hR2 hM2 with ⟨P2', hM2', hMatch⟩
    refine ⟨liftRight s1' P2' .left, LinkStep.rightToLeft hRoute hM2', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u2' hu2' with ⟨u2, hu2, hR2'⟩
    exact ⟨(.left, _, u2), ⟨rfl, rfl, hu2⟩, ⟨ht''.symm, hu1' ▸ hR1, hR2'⟩⟩
  | leftToExt hRoute hM1 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim1 _ _ _ _ hR1 hM1 with ⟨P1', hM1', hMatch⟩
    refine ⟨liftLeft P1' s2' .ext, LinkStep.leftToExt hRoute hM1', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u1' hu1' with ⟨u1, hu1, hR1'⟩
    exact ⟨(.ext, u1, _), ⟨rfl, hu1, rfl⟩, ⟨ht''.symm, hR1', hu2' ▸ hR2⟩⟩
  | rightToExt hRoute hM2 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim2 _ _ _ _ hR2 hM2 with ⟨P2', hM2', hMatch⟩
    refine ⟨liftRight s1' P2' .ext, LinkStep.rightToExt hRoute hM2', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u2' hu2' with ⟨u2, hu2, hR2'⟩
    exact ⟨(.ext, _, u2), ⟨rfl, rfl, hu2⟩, ⟨ht''.symm, hu1' ▸ hR1, hR2'⟩⟩
  | extToLeft hRoute hM1 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim1 _ _ _ _ hR1 hM1 with ⟨P1', hM1', hMatch⟩
    refine ⟨liftLeft P1' s2' .left, LinkStep.extToLeft hRoute hM1', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u1' hu1' with ⟨u1, hu1, hR1'⟩
    exact ⟨(.left, u1, _), ⟨rfl, hu1, rfl⟩, ⟨ht''.symm, hR1', hu2' ▸ hR2⟩⟩
  | extToRight hRoute hM2 =>
    rcases st2 with ⟨t2, s1', s2'⟩
    simp only at hTurn hR1 hR2
    subst hTurn
    rcases hSim2 _ _ _ _ hR2 hM2 with ⟨P2', hM2', hMatch⟩
    refine ⟨liftRight s1' P2' .right, LinkStep.extToRight hRoute hM2', ?_⟩
    intro ⟨t'', u1', u2'⟩ ⟨ht'', hu1', hu2'⟩
    rcases hMatch u2' hu2' with ⟨u2, hu2, hR2'⟩
    exact ⟨(.right, _, u2), ⟨rfl, rfl, hu2⟩, ⟨ht''.symm, hu1' ▸ hR1, hR2'⟩⟩

/-! ### Polarity Mismatch Counterexample (DimSum vs. Melocoton `umrel`) -/

/-- The module with NO transitions (`step := fun _ _ _ => False`).
    In DimSum: `NB` (no behavior, bottom of refinement).
    In Melocoton `umrel`: stuck / undefined behavior (fails WP adequacy). -/
def modNoStep : Module Unit where
  State := Unit
  step := fun _ _ _ => False
  init := ()

/-- The module with one silent transition to the EMPTY target set (`fun _ => False`).
    In DimSum: `UB` (undefined behavior, top of refinement).
    In Melocoton `umrel`: vacuous / `NB` (satisfies any WP postcondition). -/
def modEmptySet : Module Unit where
  State := Unit
  step := fun _ a P => a = none ∧ P = (fun _ => False)
  init := ()

/-- Melocoton-style `umrel` one-step safety/WP judgment on the exact same
    `State -> Option E -> (State -> Prop) -> Prop` data shape:
    outer choice over `P` is angelic (`∃ P`), inner choice over `s' ∈ P` is demonic (`∀ s'`).
    A state is 1-step safe for postcondition `Q` iff there exists a step whose
    every target state satisfies `Q`. -/
def MeloOneStepSafe {E : Type} (M : Module E) (Q : M.State → Prop) : Prop :=
  ∃ a P, M.step M.init a P ∧ ∀ s', P s' → Q s'

/-- Melocoton-polarity refinement (dual to DimSum): `M1` refines `M2` under
    `umrel` polarity iff every postcondition proved safe for `M2` is safe for `M1`
    (equivalently, every angelic step of `M2` is matched by an angelic step of `M1`
    whose demonic outcomes are covered by `M2`). -/
def MeloRefines {E : Type} (M1 M2 : Module E) : Prop :=
  ∃ R : M1.State → M2.State → Prop, R M1.init M2.init ∧
    ∀ s1 s2 a P2, R s1 s2 → M2.step s2 a P2 →
      ∃ P1, M1.step s1 a P1 ∧ ∀ s1', P1 s1' → ∃ s2', P2 s2' ∧ R s1' s2'

/-- Sharp polarity-mismatch counterexample:
    1. Under DimSum polarity, `modNoStep ⪯ modEmptySet` (NB ≤ UB) and NOT the converse.
    2. Under Melocoton `umrel` polarity, the order INVERTS strictly:
       `MeloRefines modEmptySet modNoStep` and `¬ MeloRefines modNoStep modEmptySet`.
    3. Moreover, importing a DimSum `UB` module (`modEmptySet`) into Melocoton's
       `umrel` WP makes `False` vacuously provable, whereas importing a DimSum `NB`
       module (`modNoStep`) is stuck even for `True`. -/
theorem polarity_mismatch_breaks_refinement :
    Refines modNoStep modEmptySet ∧
    ¬ Refines modEmptySet modNoStep ∧
    MeloRefines modEmptySet modNoStep ∧
    ¬ MeloRefines modNoStep modEmptySet ∧
    MeloOneStepSafe modEmptySet (fun _ => False) ∧
    ¬ MeloOneStepSafe modNoStep (fun _ => True) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- DimSum: modNoStep <= modEmptySet
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro _ _ _ _ _ hStep
    exact False.elim hStep
  · -- DimSum: NOT (modEmptySet <= modNoStep)
    rintro ⟨R, hInit, hSim⟩
    have hStep : modEmptySet.step () none (fun _ => False) := ⟨rfl, rfl⟩
    rcases hSim () () none (fun _ => False) hInit hStep with ⟨_, hNo, _⟩
    exact hNo
  · -- Melocoton: MeloRefines modEmptySet modNoStep
    refine ⟨fun _ _ => True, trivial, ?_⟩
    intro _ _ _ _ _ hNo
    exact False.elim hNo
  · -- Melocoton: NOT (MeloRefines modNoStep modEmptySet)
    rintro ⟨R, hInit, hSim⟩
    have hStep : modEmptySet.step () none (fun _ => False) := ⟨rfl, rfl⟩
    rcases hSim () () none (fun _ => False) hInit hStep with ⟨_, hNo, _⟩
    exact hNo
  · -- Melocoton WP on DimSum UB vacuously proves False
    exact ⟨none, (fun _ => False), ⟨rfl, rfl⟩, fun _ hF => False.elim hF⟩
  · -- Melocoton WP on DimSum NB is stuck even for True
    rintro ⟨_, _, hNo, _⟩
    exact hNo

end EventLinking
