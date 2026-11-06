import AnnealResearch.FiniteCausalStrategies

/-!
Owned operational discriminators for the accepted finite-action criterion.
Both games have Allowed=False. Raw machines and observers are declared before
their safety proofs. Full-state observation is explicit; no blind-policy,
source/prophecy, fairness or computable-synthesis claim is made.
-/

namespace AnnealResearch.FiniteStrategyDiscriminators

open FiniteCausalStrategies

/-- The response sees its present request, not the next demonic request. -/
def expected (request : Nat) : Bool := decide (request % 2 = 0)

inductive ResponseState where
  | ready (request : Nat) (commits : List (Nat × Bool))
  | failed (request : Nat) (commits : List (Nat × Bool))
  deriving DecidableEq, Repr

def responseCommits : ResponseState → List (Nat × Bool)
  | .ready _ commits | .failed _ commits => commits

def responseBad : ResponseState → Prop
  | .ready _ _ => False
  | .failed _ _ => True

/-- Correct response commits now; every Nat is an actual demonic next request.
Incorrect responses also execute and record the attempted response before Bad. -/
inductive ResponseRaw : ResponseState → Bool → ResponseState → Prop where
  | respond (request : Nat) (commits : List (Nat × Bool)) (next : Nat) :
      ResponseRaw (.ready request commits) (expected request)
        (.ready next (commits ++ [(request, expected request)]))
  | wrong (request : Nat) (commits : List (Nat × Bool)) (answer : Bool)
      (incorrect : answer ≠ expected request) :
      ResponseRaw (.ready request commits) answer
        (.failed request (commits ++ [(request, answer)]))

theorem bool_member (answer : Bool) : answer ∈ [false, true] := by
  cases answer <;> simp

def responseGame : Game ResponseState Bool where
  legalActions := fun _ => [false, true]
  raw := ResponseRaw
  bad := responseBad
  allowed := fun _ => False
  raw_legal := by
    intro before answer after edge
    exact bool_member answer

inductive SearchState where
  | search (candidate : Nat)
  | ticks (remaining : Nat)
  deriving DecidableEq, Repr

def searchBad : SearchState → Prop
  | .ticks 0 => True
  | _ => False

def Committed : SearchState → Prop
  | .ticks _ => True
  | .search _ => False

def searchActions : SearchState → List Bool
  | .search _ => [false, true]
  | .ticks 0 => []
  | .ticks (_ + 1) => [false]

inductive SearchRaw : SearchState → Bool → SearchState → Prop where
  | grow (candidate : Nat) :
      SearchRaw (.search candidate) false (.search (candidate + 1))
  | commit (candidate : Nat) :
      SearchRaw (.search candidate) true (.ticks candidate)
  | tick (remaining : Nat) :
      SearchRaw (.ticks (remaining + 1)) false (.ticks remaining)

def searchGame : Game SearchState Bool where
  legalActions := searchActions
  raw := SearchRaw
  bad := searchBad
  allowed := fun _ => False
  raw_legal := by
    intro before answer after edge
    cases edge <;> simp [searchActions]

/-- None outside the actual search run certifies no global classified policy. -/
def alwaysSearch : SearchState → Option Bool
  | .search _ => some false
  | .ticks _ => none

/- Derive every response approximant directly, without first assuming a safe
policy or invoking the core's converse. -/
theorem response_approximants (depth : Nat) :
    ∀ request commits,
      Approximant responseGame depth (.ready request commits) := by
  induction depth with
  | zero => intro request commits; exact True.intro
  | succ depth ih =>
      intro request commits
      refine ⟨?_, Or.inr ⟨expected request, bool_member _,
        ⟨.ready 0 (commits ++ [(request, expected request)]),
          ResponseRaw.respond request commits 0⟩, ?_⟩⟩
      · exact fun impossible => impossible
      · intro after edge
        cases edge
        · exact ih _ _
        · contradiction

theorem response_winning (request : Nat) (commits : List (Nat × Bool)) :
    Winning responseGame (.ready request commits) := by
  intro depth
  exact response_approximants depth request commits

theorem response_extracted_verified (request : Nat) (commits : List (Nat × Bool)) :
    Execution.Verified (Resolved responseGame (extractedStrategy responseGame))
      responseGame.bad responseGame.allowed (.ready request commits) :=
  extracted_verified responseGame (response_winning request commits)

/-- Safety of every successor rules out a wrong answer, without assuming which
answer Classical.choose returned. -/
theorem response_extracted_answer (request : Nat) (commits : List (Nat × Bool)) :
    extractedStrategy responseGame (.ready request commits) = some (expected request) := by
  rcases extracted_at_winning_nonallowed responseGame (response_winning request commits)
      (fun impossible => impossible) with ⟨answer, selected, good⟩
  by_cases correct : answer = expected request
  · simpa only [correct] using selected
  · have failedWinning := good.2.2
      (.failed request (commits ++ [(request, answer)]))
      (ResponseRaw.wrong request commits answer correct)
    exact False.elim ((winning_nonbad responseGame failedWinning) True.intro)

/-- Each actual extracted response commits in one step. The next request is
unrestricted Nat; no favorable demonic successor is selected here. -/
theorem response_extracted_step_iff (request : Nat) (commits : List (Nat × Bool))
    (after : ResponseState) :
    Resolved responseGame (extractedStrategy responseGame) (.ready request commits) after ↔
      ∃ next, after = .ready next (commits ++ [(request, expected request)]) := by
  constructor
  · rintro ⟨answer, selected, edge⟩
    have correct : answer = expected request :=
      Option.some.inj (selected.symm.trans (response_extracted_answer request commits))
    subst answer
    cases edge
    · exact ⟨_, rfl⟩
    · contradiction
  · rintro ⟨next, rfl⟩
    exact ⟨expected request, response_extracted_answer request commits,
      ResponseRaw.respond request commits next⟩

theorem response_step_commits (request : Nat) (commits : List (Nat × Bool))
    {after : ResponseState}
    (edge : Resolved responseGame (extractedStrategy responseGame) (.ready request commits) after) :
    responseCommits after = commits ++ [(request, expected request)] := by
  rcases (response_extracted_step_iff request commits after).mp edge with ⟨next, rfl⟩
  rfl

def responseLog (requests : Nat → Nat) : Nat → List (Nat × Bool)
  | 0 => []
  | count + 1 => responseLog requests count ++ [(requests count, expected (requests count))]

def responseRun (requests : Nat → Nat) (count : Nat) : ResponseState :=
  .ready (requests count) (responseLog requests count)

theorem response_run_step (requests : Nat → Nat) (count : Nat) :
    Resolved responseGame (extractedStrategy responseGame)
      (responseRun requests count) (responseRun requests (count + 1)) :=
  (response_extracted_step_iff (requests count) (responseLog requests count) _).mpr
    ⟨requests (count + 1), rfl⟩

theorem response_actual_run (requests : Nat → Nat) : ∀ count,
    Execution.Reach (Resolved responseGame (extractedStrategy responseGame))
      (responseRun requests 0) (responseRun requests count) ∧
    Resolved responseGame (extractedStrategy responseGame)
      (responseRun requests count) (responseRun requests (count + 1)) := by
  intro count
  have reached : Execution.Reach (Resolved responseGame (extractedStrategy responseGame))
      (responseRun requests 0) (responseRun requests count) := by
    induction count with
    | zero => exact Execution.Reach.refl _
    | succ count ih => exact Execution.Reach.tail ih (response_run_step requests count)
  exact ⟨reached, response_run_step requests count⟩

/- Search can diverge safely without ever returning a candidate. -/
theorem always_search_edge_iff (candidate : Nat) (after : SearchState) :
    Resolved searchGame alwaysSearch (.search candidate) after ↔
      after = .search (candidate + 1) := by
  constructor
  · rintro ⟨answer, selected, edge⟩
    have chosen : answer = false := (Option.some.inj selected).symm
    subst answer
    cases edge
    rfl
  · intro same
    subst after
    exact ⟨false, rfl, SearchRaw.grow candidate⟩

theorem always_search_reachable (initial : Nat) {reached : SearchState}
    (path : Execution.Reach (Resolved searchGame alwaysSearch) (.search initial) reached) :
    ∃ candidate, reached = .search candidate := by
  apply Execution.invariant_reachable
    (Invariant := fun state : SearchState => ∃ candidate, state = .search candidate) ⟨initial, rfl⟩ ?_ path
  intro before after shape edge
  rcases shape with ⟨candidate, rfl⟩
  exact ⟨candidate + 1, (always_search_edge_iff candidate after).mp edge⟩

theorem always_search_verified (initial : Nat) :
    Execution.Verified (Resolved searchGame alwaysSearch)
      searchGame.bad searchGame.allowed (.search initial) := by
  apply Execution.invariant_verified
    (Invariant := fun state : SearchState => ∃ candidate, state = .search candidate) ⟨initial, rfl⟩
  · intro before after shape edge
    rcases shape with ⟨candidate, rfl⟩
    exact ⟨candidate + 1, (always_search_edge_iff candidate after).mp edge⟩
  · intro state shape
    rcases shape with ⟨candidate, rfl⟩
    exact fun impossible => impossible
  · intro state shape
    rcases shape with ⟨candidate, rfl⟩
    exact Or.inr ⟨.search (candidate + 1), false, rfl, SearchRaw.grow candidate⟩

theorem always_search_never_commits (initial : Nat) {reached : SearchState}
    (path : Execution.Reach (Resolved searchGame alwaysSearch) (.search initial) reached) :
    ¬ Committed reached := by
  rcases always_search_reachable initial path with ⟨candidate, rfl⟩
  exact fun impossible => impossible

def searchRun (count : Nat) : SearchState := .search count

theorem always_search_actual_run : ∀ count,
    Execution.Reach (Resolved searchGame alwaysSearch) (searchRun 0) (searchRun count) ∧
    Resolved searchGame alwaysSearch (searchRun count) (searchRun (count + 1)) ∧
    ¬ Committed (searchRun count) := by
  intro count
  have reached : Execution.Reach (Resolved searchGame alwaysSearch)
      (searchRun 0) (searchRun count) := by
    induction count with
    | zero => exact Execution.Reach.refl _
    | succ count ih =>
        exact Execution.Reach.tail ih ⟨false, rfl, SearchRaw.grow count⟩
  exact ⟨reached, ⟨false, rfl, SearchRaw.grow count⟩, fun impossible => impossible⟩

/-- A suffix retains both the safety and progress components for the SAME
resolved relation/policy. This is not a new strategy choice at the suffix. -/
theorem verified_suffix {State : Type} {Step : State → State → Prop}
    {Bad Allowed : State → Prop} {initial reached : State}
    (verified : Execution.Verified Step Bad Allowed initial)
    (path : Execution.Reach Step initial reached) :
    Execution.Verified Step Bad Allowed reached := by
  constructor
  · intro after suffix
    exact verified.1 after (path.trans suffix)
  · intro after suffix
    exact verified.2 after (path.trans suffix)

theorem no_verified_countdown (policy : SearchState → Option Bool) : ∀ remaining,
    ¬ Execution.Verified (Resolved searchGame policy)
      searchGame.bad searchGame.allowed (.ticks remaining) := by
  intro remaining
  induction remaining with
  | zero =>
      intro verified
      exact verified.1 (.ticks 0) (Execution.Reach.refl _) True.intro
  | succ remaining ih =>
      intro verified
      rcases verified.2 (.ticks (remaining + 1)) (Execution.Reach.refl _) with
        stopped | ⟨after, edge⟩
      · exact stopped
      · have destination : after = .ticks remaining := by
          rcases edge with ⟨answer, selected, rawEdge⟩
          cases rawEdge
          rfl
        subst after
        exact ih (verified_suffix verified (Execution.Reach.tail (Execution.Reach.refl _) edge))

/-- Progress is essential: an artificial none at a positive countdown would
otherwise remove its actual future Bad path from the resolved relation. -/
theorem classified_policy_cannot_reach_commit (policy : SearchState → Option Bool)
    {initial reached : SearchState}
    (verified : Execution.Verified (Resolved searchGame policy)
      searchGame.bad searchGame.allowed initial)
    (path : Execution.Reach (Resolved searchGame policy) initial reached) :
    ¬ Committed reached := by
  cases reached with
  | search candidate => exact fun impossible => impossible
  | ticks remaining =>
      exact False.elim (no_verified_countdown policy remaining (verified_suffix verified path))

def artificialStop : SearchState → Option Bool := fun _ => none

theorem artificial_countdown_stop (remaining : Nat) :
    Execution.NoUB (Resolved searchGame artificialStop) searchGame.bad (.ticks (remaining + 1)) ∧
    ¬ Execution.Verified (Resolved searchGame artificialStop)
      searchGame.bad searchGame.allowed (.ticks (remaining + 1)) := by
  constructor
  · apply Execution.invariant_noUB
      (Invariant := fun state : SearchState => state = .ticks (remaining + 1)) rfl
    · intro before after same edge
      rcases edge with ⟨answer, selected, rawEdge⟩
      cases selected
    · intro state same
      subst state
      exact fun impossible => impossible
  · exact no_verified_countdown artificialStop (remaining + 1)

theorem search_winning (candidate : Nat) : Winning searchGame (.search candidate) := by
  intro depth
  exact verified_strategy_approximant searchGame alwaysSearch depth (.search candidate)
    (always_search_verified candidate)

/-- Reuse the accepted atomic-Nat obstruction; this is a comparison of distinct
owned subjects, not a source refinement or a returned prediction witness. -/
theorem finite_search_is_not_an_atomic_witness :
    Winning searchGame (.search 0) ∧
    ¬ Execution.Prediction.GreatestSafety .root ∧
    ((∀ horizon, ∃ prediction, Execution.Prediction.SafeFor horizon prediction) ∧
      ¬ (∃ prediction, ∀ horizon, Execution.Prediction.SafeFor horizon prediction)) :=
  ⟨search_winning 0, Execution.Prediction.root_not_in_greatestSafety,
    Execution.Prediction.quantifier_exchange_fails⟩

/- Audits count substantive bindings/controls, not each step of an example. -/
#print axioms response_approximants
#print axioms response_extracted_verified
#print axioms response_extracted_answer
#print axioms response_extracted_step_iff
#print axioms response_actual_run
#print axioms always_search_verified
#print axioms always_search_never_commits
#print axioms always_search_actual_run
#print axioms no_verified_countdown
#print axioms classified_policy_cannot_reach_commit
#print axioms artificial_countdown_stop
#print axioms finite_search_is_not_an_atomic_witness

end AnnealResearch.FiniteStrategyDiscriminators
