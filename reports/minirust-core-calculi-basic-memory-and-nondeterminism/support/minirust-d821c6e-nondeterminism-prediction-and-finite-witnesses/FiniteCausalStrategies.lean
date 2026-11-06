import AnnealResearch.Execution

/-!
An owned perfect-information causal safety game. The state is the strategy's
entire permitted observation; no partial-observation or prophecy theorem is
claimed. Legal angelic answers form a finite list at each state. Demonic
successors and the state/action types need not be finite or inhabited.

The premise Winning is a proof of EVERY finite approximant, not the outcome of
finitely many tests. Classical extraction supplies no computable synthesis or
termination guarantee. Allowed stops use the explicitly selected optional-stop
policy below. This module is not a Rust/MiniRust semantics or authority bridge.
-/

namespace AnnealResearch.FiniteCausalStrategies

universe u v w

variable {State : Type u} {Action : Type v}

/-- The raw relation is given independently of all safety/strategy definitions. -/
structure Game (State : Type u) (Action : Type v) where
  legalActions : State → List Action
  raw : State → Action → State → Prop
  bad : State → Prop
  allowed : State → Prop
  raw_legal : ∀ {before action after}, raw before action after →
    action ∈ legalActions before

def Enabled (game : Game State Action) (state : State) (action : Action) : Prop :=
  ∃ after, game.raw state action after

def GoodAction (game : Game State Action) (X : State → Prop)
    (state : State) (action : Action) : Prop :=
  action ∈ game.legalActions state ∧ Enabled game state action ∧
    ∀ after, game.raw state action after → X after

/-- Current nonbadness, then either an allowed stop or a legal enabled action
whose EVERY actual demonic successor belongs to X. -/
def Transformer (game : Game State Action) (X : State → Prop) (state : State) : Prop :=
  ¬ game.bad state ∧ (game.allowed state ∨ ∃ action, GoodAction game X state action)

def Approximant (game : Game State Action) : Nat → State → Prop
  | 0, _ => True
  | n + 1, state => Transformer game (Approximant game n) state

def Winning (game : Game State Action) (state : State) : Prop :=
  ∀ n, Approximant game n state

/-- One policy is used for the entire resolved execution. There is no Winning,
legality, enabledness or desired-result guard in this relation. -/
def Resolved (game : Game State Action) (policy : State → Option Action)
    (before after : State) : Prop :=
  ∃ action, policy before = some action ∧ game.raw before action after

def StopPolicy (game : Game State Action) (policy : State → Option Action) : Prop :=
  ∀ state, game.allowed state → policy state = none

theorem transformer_mono (game : Game State Action) {X Y : State → Prop}
    (inclusion : ∀ state, X state → Y state) :
    ∀ state, Transformer game X state → Transformer game Y state := by
  intro state member
  rcases member with ⟨nonbad, stopped | ⟨action, legal, enabled, successors⟩⟩
  · exact ⟨nonbad, Or.inl stopped⟩
  · exact ⟨nonbad, Or.inr ⟨action, legal, enabled,
      fun after edge => inclusion after (successors after edge)⟩⟩

theorem approximant_down (game : Game State Action) (n : Nat) :
    ∀ state, Approximant game (n + 1) state → Approximant game n state := by
  induction n with
  | zero => intro state member; exact True.intro
  | succ n ih =>
      intro state member
      exact transformer_mono game (fun after proof => ih after proof) state member

/-- An elementary pointwise descent helper, with no finiteness premise. -/
theorem descending_le {α : Type w} (P : Nat → α → Prop)
    (down : ∀ n value, P (n + 1) value → P n value)
    {low high : Nat} (ordered : low ≤ high) (value : α) :
    P high value → P low value := by
  rcases Nat.exists_eq_add_of_le ordered with ⟨extra, rfl⟩
  clear ordered
  induction extra with
  | zero => intro member; exact member
  | succ extra ih =>
      intro member
      exact ih (down (low + extra) value member)

/-- A single member of a fixed finite list works at every depth. Duplicates are
harmless, and no decidable equality or globally inhabited answer type is needed. -/
theorem finite_list_intersection {α : Type w} (choices : List α)
    (P : Nat → α → Prop)
    (down : ∀ n value, P (n + 1) value → P n value) :
    (∀ n, ∃ value, value ∈ choices ∧ P n value) →
      ∃ value, value ∈ choices ∧ ∀ n, P n value := by
  classical
  induction choices with
  | nil =>
      intro every
      rcases every 0 with ⟨value, member, atZero⟩
      simp at member
  | cons head tail ih =>
      intro every
      by_cases headWorks : ∀ n, P n head
      · exact ⟨head, List.mem_cons_self, headWorks⟩
      · rcases Classical.not_forall.mp headWorks with ⟨failedDepth, fails⟩
        have tailEvery : ∀ n, ∃ value, value ∈ tail ∧ P n value := by
          intro n
          rcases every (max n failedDepth) with ⟨value, member, deeper⟩
          rcases List.mem_cons.mp member with equalHead | inTail
          · subst value
            exact False.elim (fails
              (descending_le P down (Nat.le_max_right n failedDepth) head deeper))
          · exact ⟨value, inTail,
              descending_le P down (Nat.le_max_left n failedDepth) value deeper⟩
        rcases ih tailEvery with ⟨value, member, allDepths⟩
        exact ⟨value, List.mem_cons_of_mem head member, allDepths⟩

theorem winning_nonbad (game : Game State Action) {state : State}
    (member : Winning game state) : ¬ game.bad state :=
  (member 1).1

theorem winning_postfixed (game : Game State Action) {state : State}
    (member : Winning game state) : Transformer game (Winning game) state := by
  classical
  refine ⟨winning_nonbad game member, ?_⟩
  by_cases stopped : game.allowed state
  · exact Or.inl stopped
  · apply Or.inr
    let condition : Nat → Action → Prop := fun n action =>
      Enabled game state action ∧
        ∀ after, game.raw state action after → Approximant game n after
    have down : ∀ n action, condition (n + 1) action → condition n action := by
      intro n action selected
      exact ⟨selected.1,
        fun after edge => approximant_down game n after (selected.2 after edge)⟩
    have every : ∀ n, ∃ action, action ∈ game.legalActions state ∧ condition n action := by
      intro n
      rcases (member (n + 1)).2 with allowed | ⟨action, legal, enabled, successors⟩
      · exact False.elim (stopped allowed)
      · exact ⟨action, legal, enabled, successors⟩
    rcases finite_list_intersection (game.legalActions state) condition down every with
      ⟨action, legal, allDepths⟩
    exact ⟨action, legal, (allDepths 0).1,
      fun after edge n => (allDepths n).2 after edge⟩

theorem winning_unfold (game : Game State Action) (state : State) :
    Winning game state ↔ Transformer game (Winning game) state := by
  constructor
  · exact winning_postfixed game
  · intro closed n
    cases n with
    | zero => exact True.intro
    | succ n =>
        exact transformer_mono game (fun after winning => winning n) state closed

theorem winning_action (game : Game State Action) {state : State}
    (member : Winning game state) (notAllowed : ¬ game.allowed state) :
    ∃ action, GoodAction game (Winning game) state action :=
  (winning_postfixed game member).2.resolve_left notAllowed

/-- At Allowed states choose none even if raw actions exist. Outside Winning,
none supplies no classification guarantee. There is no default Action value. -/
noncomputable def extractedStrategy (game : Game State Action) : State → Option Action := by
  classical
  exact fun state =>
    if allowed : game.allowed state then none
    else if winning : Winning game state then
      some (Classical.choose (winning_action game winning allowed))
    else none

theorem extracted_at_allowed (game : Game State Action) {state : State}
    (allowed : game.allowed state) : extractedStrategy game state = none := by
  classical
  simp [extractedStrategy, allowed]

theorem extracted_at_winning_nonallowed (game : Game State Action) {state : State}
    (member : Winning game state) (notAllowed : ¬ game.allowed state) :
    ∃ action, extractedStrategy game state = some action ∧
      GoodAction game (Winning game) state action := by
  classical
  refine ⟨Classical.choose (winning_action game member notAllowed), ?_,
    Classical.choose_spec (winning_action game member notAllowed)⟩
  simp [extractedStrategy, notAllowed, member]

theorem extracted_step_preserves_winning (game : Game State Action)
    {before after : State} (member : Winning game before)
    (edge : Resolved game (extractedStrategy game) before after) : Winning game after := by
  classical
  rcases edge with ⟨action, selected, rawEdge⟩
  by_cases allowed : game.allowed before
  · have halted : extractedStrategy game before = none := extracted_at_allowed game allowed
    rw [halted] at selected
    cases selected
  · rcases extracted_at_winning_nonallowed game member allowed with
      ⟨chosen, chosenByPolicy, good⟩
    have same : chosen = action := Option.some.inj (chosenByPolicy.symm.trans selected)
    subst chosen
    exact good.2.2 after rawEdge

theorem extracted_reachable_winning (game : Game State Action)
    {initial reached : State} (member : Winning game initial)
    (path : Execution.Reach (Resolved game (extractedStrategy game)) initial reached) :
    Winning game reached := by
  apply Execution.invariant_reachable (Invariant := Winning game) member ?_ path
  intro before after beforeWinning edge
  exact extracted_step_preserves_winning game beforeWinning edge

/-- Legality/enabledness is asserted on the reachable winning region, not for
all states or for arbitrary policies. Allowed states take the distinct stop arm. -/
theorem extracted_reachable_selection (game : Game State Action)
    {initial reached : State} (member : Winning game initial)
    (path : Execution.Reach (Resolved game (extractedStrategy game)) initial reached) :
    (game.allowed reached ∧ extractedStrategy game reached = none) ∨
      ∃ action, extractedStrategy game reached = some action ∧
        GoodAction game (Winning game) reached action := by
  classical
  by_cases allowed : game.allowed reached
  · exact Or.inl ⟨allowed, extracted_at_allowed game allowed⟩
  · exact Or.inr (extracted_at_winning_nonallowed game
      (extracted_reachable_winning game member path) allowed)

theorem extracted_noUB (game : Game State Action) {initial : State}
    (member : Winning game initial) :
    Execution.NoUB (Resolved game (extractedStrategy game)) game.bad initial := by
  apply Execution.invariant_noUB (Invariant := Winning game) member
  · intro before after beforeWinning edge
    exact extracted_step_preserves_winning game beforeWinning edge
  · intro state stateWinning
    exact winning_nonbad game stateWinning

theorem extracted_progress (game : Game State Action) {initial : State}
    (member : Winning game initial) :
    Execution.ReachableProgress (Resolved game (extractedStrategy game)) game.allowed initial := by
  intro reached path
  rcases extracted_reachable_selection game member path with
    ⟨allowed, halted⟩ | ⟨action, selected, legal, ⟨after, rawEdge⟩, successors⟩
  · exact Or.inl allowed
  · exact Or.inr ⟨after, action, selected, rawEdge⟩

theorem extracted_no_successor_at_allowed (game : Game State Action) {state : State}
    (allowed : game.allowed state) :
    ¬ ∃ after, Resolved game (extractedStrategy game) state after := by
  rintro ⟨after, action, selected, rawEdge⟩
  rw [extracted_at_allowed game allowed] at selected
  cases selected

theorem extracted_verified (game : Game State Action) {initial : State}
    (member : Winning game initial) :
    Execution.Verified (Resolved game (extractedStrategy game)) game.bad game.allowed initial :=
  ⟨extracted_noUB game member, extracted_progress game member⟩

/-- Converse for ONE actual fixed policy. Progress supplies enabledness; every
raw successor of its selected action is an actual resolved successor. -/
theorem verified_strategy_approximant (game : Game State Action)
    (policy : State → Option Action) (n : Nat) :
    ∀ initial, Execution.Verified (Resolved game policy) game.bad game.allowed initial →
      Approximant game n initial := by
  induction n with
  | zero => intro initial verified; exact True.intro
  | succ n ih =>
      intro initial verified
      refine ⟨verified.1 initial (Execution.Reach.refl _), ?_⟩
      rcases verified.2 initial (Execution.Reach.refl _) with
        allowed | ⟨after, action, selected, rawEdge⟩
      · exact Or.inl allowed
      · refine Or.inr ⟨action, game.raw_legal rawEdge, ⟨after, rawEdge⟩, ?_⟩
        intro target edge
        have actual : Resolved game policy initial target := ⟨action, selected, edge⟩
        apply ih target
        constructor
        · exact Execution.NoUB.after_step verified.1 actual
        · intro reached suffix
          exact verified.2 reached
            ((Execution.Reach.tail (Execution.Reach.refl initial) actual).trans suffix)

theorem winning_iff_classified_strategy (game : Game State Action) (initial : State) :
    Winning game initial ↔
      ∃ policy : State → Option Action, StopPolicy game policy ∧
        Execution.Verified (Resolved game policy) game.bad game.allowed initial := by
  constructor
  · intro member
    exact ⟨extractedStrategy game,
      fun state allowed => extracted_at_allowed game allowed, extracted_verified game member⟩
  · rintro ⟨policy, stopPolicy, verified⟩
    intro n
    exact verified_strategy_approximant game policy n initial verified

/- Ordered load-bearing audits. These are not finite-test or synthesis results. -/
#print axioms transformer_mono
#print axioms approximant_down
#print axioms finite_list_intersection
#print axioms winning_postfixed
#print axioms winning_unfold
#print axioms extracted_at_allowed
#print axioms extracted_at_winning_nonallowed
#print axioms extracted_reachable_winning
#print axioms extracted_reachable_selection
#print axioms extracted_noUB
#print axioms extracted_progress
#print axioms extracted_no_successor_at_allowed
#print axioms verified_strategy_approximant
#print axioms winning_iff_classified_strategy

end AnnealResearch.FiniteCausalStrategies
