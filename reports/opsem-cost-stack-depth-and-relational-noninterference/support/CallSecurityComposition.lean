import AnnealResearch.CallSecuritySpecimens

/-!
Two-stage labeled matching, with actual related successors. The generic cuts
are zero, one and two stages; they are not arbitrary internal-call cuts.
Concrete stages below are actual three-Step normal calls of the accepted
specimens, including their address, unit cost and returned-zero events.
No future-extension predicate filters a one-stage path.
-/

namespace AnnealResearch.CallSecurityComposition

open CallSecuritySpecimens

universe u v w

inductive Cut where
  | zero
  | one
  | two
  deriving DecidableEq, Repr

/-- Two-sided matching keeps the same orientation of Entry/Exit in both fields.
The matched poststate is an actual successor of the matching entry. -/
structure StageMatch {Left : Type u} {Right : Type v} {Label : Type w}
    (left : Left → Label → Left → Prop)
    (right : Right → Label → Right → Prop)
    (Entry Exit : Left → Right → Prop) : Prop where
  forward : ∀ {beforeL beforeR label afterL}, Entry beforeL beforeR →
    left beforeL label afterL →
      ∃ afterR, right beforeR label afterR ∧ Exit afterL afterR
  backward : ∀ {beforeL beforeR label afterR}, Entry beforeL beforeR →
    right beforeR label afterR →
      ∃ afterL, left beforeL label afterL ∧ Exit afterL afterR

/-- A one-stage path requires no second-stage successor. -/
inductive StagePath {State : Type u} {Label : Type w}
    (first second : State → Label → State → Prop) :
    Cut → State → List Label → State → Prop where
  | zero (entry : State) : StagePath first second .zero entry [] entry
  | one {entry after label} (edge : first entry label after) :
      StagePath first second .one entry [label] after
  | two {entry middle after firstLabel secondLabel}
      (firstEdge : first entry firstLabel middle)
      (secondEdge : second middle secondLabel after) :
      StagePath first second .two entry [firstLabel, secondLabel] after

def CutRelation {Left : Type u} {Right : Type v}
    (R0 R1 R2 : Left → Right → Prop) : Cut → Left → Right → Prop
  | .zero, left, right => R0 left right
  | .one, left, right => R1 left right
  | .two, left, right => R2 left right

def StageObservations {State : Type u} {Label : Type w}
    (first second : State → Label → State → Prop)
    (cut : Cut) (entry : State) (labels : List Label) : Prop :=
  ∃ after, StagePath first second cut entry labels after

/-- Exactly three real microevent steps, with their actual appended visible
history as label. This is not an assumption of whole-run equivalence. -/
def ThreeSteps (mode : Mode) (before : Config) (label : Trace) (after : Config) : Prop :=
  ∃ middle1 middle2, Step mode before middle1 ∧
    Step mode middle1 middle2 ∧ Step mode middle2 after ∧
      observe after = observe before ++ label

def FirstStage (mode : Mode) (before : Config) (label : Trace) (after : Config) : Prop :=
  ∃ secret, before = root secret ∧ ThreeSteps mode before label after

def SecondStage (mode : Mode) (before : Config) (label : Trace) (after : Config) : Prop :=
  ∃ secret bit, before = between secret bit ∧ ThreeSteps mode before label after

def secondTrace (bit : Bool) : Trace :=
  [address .second bit, charge .second, returned .second]

def InitialRelated (left right : Config) : Prop :=
  ∃ leftSecret rightSecret, left = root leftSecret ∧ right = root rightSecret

def BoundaryRelated (left right : Config) : Prop :=
  ∃ leftSecret rightSecret bit,
    left = between leftSecret bit ∧ right = between rightSecret bit

def FinalRelated (left right : Config) : Prop :=
  ∃ leftSecret rightSecret firstBit secondBit,
    left = completed leftSecret firstBit secondBit ∧
      right = completed rightSecret firstBit secondBit

def cutPhase : Cut → Phase
  | .zero => .firstAddress
  | .one => .secondAddress
  | .two => .finished

/-- Flatten only complete-call labels. No list prefix inside a label is thereby
promoted to a generic stage cut. -/
def CallCutRuns (mode : Mode) (cut : Cut) : Observations.TraceSet Bool Visible :=
  fun secret trace => ∃ labels after,
    StagePath (FirstStage mode) (SecondStage mode) cut (root secret) labels after ∧
      trace = labels.flatten

theorem stage_prefix_forward
    {Left : Type u} {Right : Type v} {Label : Type w}
    {leftFirst leftSecond : Left → Label → Left → Prop}
    {rightFirst rightSecond : Right → Label → Right → Prop}
    {R0 R1 R2 : Left → Right → Prop}
    (firstMatch : StageMatch leftFirst rightFirst R0 R1)
    (secondMatch : StageMatch leftSecond rightSecond R1 R2)
    {leftEntry : Left} {rightEntry : Right}
    (related : R0 leftEntry rightEntry)
    {cut : Cut} {labels : List Label} {leftAfter : Left}
    (path : StagePath leftFirst leftSecond cut leftEntry labels leftAfter) :
    ∃ rightAfter, StagePath rightFirst rightSecond cut rightEntry labels rightAfter ∧
      CutRelation R0 R1 R2 cut leftAfter rightAfter := by
  cases path with
  | zero => exact ⟨rightEntry, StagePath.zero _, related⟩
  | one edge =>
      rcases firstMatch.forward related edge with ⟨after, matched, postRelated⟩
      exact ⟨after, StagePath.one matched, postRelated⟩
  | two firstEdge secondEdge =>
      rcases firstMatch.forward related firstEdge with ⟨middle, matchedFirst, atMiddle⟩
      rcases secondMatch.forward atMiddle secondEdge with ⟨after, matchedSecond, atAfter⟩
      exact ⟨after, StagePath.two matchedFirst matchedSecond, atAfter⟩

theorem stage_prefix_backward
    {Left : Type u} {Right : Type v} {Label : Type w}
    {leftFirst leftSecond : Left → Label → Left → Prop}
    {rightFirst rightSecond : Right → Label → Right → Prop}
    {R0 R1 R2 : Left → Right → Prop}
    (firstMatch : StageMatch leftFirst rightFirst R0 R1)
    (secondMatch : StageMatch leftSecond rightSecond R1 R2)
    {leftEntry : Left} {rightEntry : Right}
    (related : R0 leftEntry rightEntry)
    {cut : Cut} {labels : List Label} {rightAfter : Right}
    (path : StagePath rightFirst rightSecond cut rightEntry labels rightAfter) :
    ∃ leftAfter, StagePath leftFirst leftSecond cut leftEntry labels leftAfter ∧
      CutRelation R0 R1 R2 cut leftAfter rightAfter := by
  cases path with
  | zero => exact ⟨leftEntry, StagePath.zero _, related⟩
  | one edge =>
      rcases firstMatch.backward related edge with ⟨after, matched, postRelated⟩
      exact ⟨after, StagePath.one matched, postRelated⟩
  | two firstEdge secondEdge =>
      rcases firstMatch.backward related firstEdge with ⟨middle, matchedFirst, atMiddle⟩
      rcases secondMatch.backward atMiddle secondEdge with ⟨after, matchedSecond, atAfter⟩
      exact ⟨after, StagePath.two matchedFirst matchedSecond, atAfter⟩

theorem stage_observations_iff
    {Left : Type u} {Right : Type v} {Label : Type w}
    {leftFirst leftSecond : Left → Label → Left → Prop}
    {rightFirst rightSecond : Right → Label → Right → Prop}
    {R0 R1 R2 : Left → Right → Prop}
    (firstMatch : StageMatch leftFirst rightFirst R0 R1)
    (secondMatch : StageMatch leftSecond rightSecond R1 R2)
    {leftEntry : Left} {rightEntry : Right}
    (related : R0 leftEntry rightEntry) (cut : Cut) (labels : List Label) :
    StageObservations leftFirst leftSecond cut leftEntry labels ↔
      StageObservations rightFirst rightSecond cut rightEntry labels := by
  constructor
  · rintro ⟨after, path⟩
    rcases stage_prefix_forward firstMatch secondMatch related path with
      ⟨matched, matchedPath, postRelated⟩
    exact ⟨matched, matchedPath⟩
  · rintro ⟨after, path⟩
    rcases stage_prefix_backward firstMatch secondMatch related path with
      ⟨matched, matchedPath, postRelated⟩
    exact ⟨matched, matchedPath⟩

/- Both directions bind the labels and residuals to actual three-Step calls. -/
theorem first_stage_iff (mode : Mode) (before : Config) (label : Trace) (after : Config) :
    FirstStage mode before label after ↔
      ∃ secret bit, before = root secret ∧ label = firstTrace bit ∧
        after = between secret bit := by
  constructor
  · rintro ⟨secret, rfl, middle1, middle2, edge1, edge2, edge3, observed⟩
    cases edge1
    cases edge2
    cases edge3
    refine ⟨secret, _, rfl, ?_, rfl⟩
    exact observed.symm
  · rintro ⟨secret, bit, rfl, rfl, rfl⟩
    exact ⟨secret, rfl, afterAddress1 secret bit, afterCost1 secret bit,
      Step.address1 mode secret bit [],
      Step.cost1 mode secret bit [address .first bit],
      Step.return1 mode secret bit [address .first bit, charge .first], rfl⟩

theorem second_stage_iff (mode : Mode) (before : Config) (label : Trace) (after : Config) :
    SecondStage mode before label after ↔
      ∃ secret firstBit secondBit, before = between secret firstBit ∧
        SecondAllowed mode secret firstBit secondBit ∧
          label = secondTrace secondBit ∧ after = completed secret firstBit secondBit := by
  constructor
  · rintro ⟨secret, firstBit, rfl, middle1, middle2, edge1, edge2, edge3, observed⟩
    cases edge1 <;> cases edge2 <;> cases edge3
    · refine ⟨secret, firstBit, _, rfl, rfl, ?_, rfl⟩
      apply Eq.symm
      apply List.append_cancel_left (as := firstTrace firstBit)
      exact observed
    · refine ⟨secret, firstBit, _, rfl, True.intro, ?_, rfl⟩
      apply Eq.symm
      apply List.append_cancel_left (as := firstTrace firstBit)
      exact observed
  · rintro ⟨secret, firstBit, secondBit, rfl, allowed, rfl, rfl⟩
    exact ⟨secret, firstBit, rfl, afterAddress2 secret firstBit secondBit,
      afterCost2 secret firstBit secondBit,
      second_address_edge mode secret firstBit secondBit allowed,
      Step.cost2 mode secret firstBit (firstTrace firstBit ++ [address .second secondBit]),
      Step.return2 mode secret firstBit
        (firstTrace firstBit ++ [address .second secondBit, charge .second]), rfl⟩

/-- Projection of actual Config fields, not injectivity of an abstract encoding. -/
theorem first_stage_at_root_iff (mode : Mode) (secret : Bool)
    (label : Trace) (after : Config) :
    FirstStage mode (root secret) label after ↔
      ∃ bit, label = firstTrace bit ∧ after = between secret bit := by
  rw [first_stage_iff]
  constructor
  · rintro ⟨actualSecret, bit, entry, observed, final⟩
    have sameSecret : secret = actualSecret := congrArg Config.secret entry
    subst actualSecret
    exact ⟨bit, observed, final⟩
  · rintro ⟨bit, observed, final⟩
    exact ⟨secret, bit, rfl, observed, final⟩

theorem second_stage_at_between_iff (mode : Mode) (secret firstBit : Bool)
    (label : Trace) (after : Config) :
    SecondStage mode (between secret firstBit) label after ↔
      ∃ secondBit, SecondAllowed mode secret firstBit secondBit ∧
        label = secondTrace secondBit ∧ after = completed secret firstBit secondBit := by
  rw [second_stage_iff]
  constructor
  · rintro ⟨actualSecret, actualBit, secondBit, entry, allowed, observed, final⟩
    have sameSecret : secret = actualSecret := congrArg Config.secret entry
    have sameBit : firstBit = actualBit :=
      Option.some.inj (congrArg Config.retainedBit entry)
    subst actualSecret
    subst actualBit
    exact ⟨secondBit, allowed, observed, final⟩
  · rintro ⟨secondBit, allowed, observed, final⟩
    exact ⟨secret, firstBit, secondBit, rfl, allowed, observed, final⟩

theorem stage_path_operational {mode : Mode} {secret : Bool} {cut : Cut}
    {labels : List Trace} {after : Config}
    (path : StagePath (FirstStage mode) (SecondStage mode) cut (root secret) labels after) :
    Execution.Reach (Step mode) (root secret) after ∧
      after.phase = cutPhase cut ∧ observe after = labels.flatten := by
  cases path with
  | zero => exact ⟨Execution.Reach.refl _, rfl, rfl⟩
  | one edge =>
      rcases (first_stage_at_root_iff mode secret _ _).mp edge with ⟨bit, rfl, rfl⟩
      exact ⟨between_reachable mode secret bit, rfl, rfl⟩
  | two firstEdge secondEdge =>
      rcases (first_stage_at_root_iff mode secret _ _).mp firstEdge with
        ⟨firstBit, rfl, rfl⟩
      rcases (second_stage_at_between_iff mode secret firstBit _ _).mp secondEdge with
        ⟨secondBit, allowed, rfl, rfl⟩
      exact ⟨completed_reachable mode secret firstBit secondBit allowed, rfl, rfl⟩

/-- Converse coverage is restricted to the declared call cuts, not the four
internal address/cost cut phases. No future normal extension is a premise. -/
theorem operational_cut_stage_path {mode : Mode} {secret : Bool} {cut : Cut}
    {after : Config} (path : Execution.Reach (Step mode) (root secret) after)
    (atCut : after.phase = cutPhase cut) :
    ∃ labels, StagePath (FirstStage mode) (SecondStage mode) cut (root secret) labels after ∧
      observe after = labels.flatten := by
  have shape := reachable_shape path
  cases cut with
  | zero =>
      cases shape with
      | initial => exact ⟨[], StagePath.zero _, rfl⟩
      | firstAddress bit => cases atCut
      | firstCost bit => cases atCut
      | firstReturned bit => cases atCut
      | secondAddress firstBit secondBit allowed => cases atCut
      | secondCost firstBit secondBit allowed => cases atCut
      | secondReturned firstBit secondBit allowed => cases atCut
  | one =>
      cases shape with
      | initial => cases atCut
      | firstAddress bit => cases atCut
      | firstCost bit => cases atCut
      | firstReturned bit =>
          exact ⟨[firstTrace bit],
            StagePath.one ((first_stage_at_root_iff mode secret _ _).mpr ⟨bit, rfl, rfl⟩),
            rfl⟩
      | secondAddress firstBit secondBit allowed => cases atCut
      | secondCost firstBit secondBit allowed => cases atCut
      | secondReturned firstBit secondBit allowed => cases atCut
  | two =>
      cases shape with
      | initial => cases atCut
      | firstAddress bit => cases atCut
      | firstCost bit => cases atCut
      | firstReturned bit => cases atCut
      | secondAddress firstBit secondBit allowed => cases atCut
      | secondCost firstBit secondBit allowed => cases atCut
      | secondReturned firstBit secondBit allowed =>
          exact ⟨[firstTrace firstBit, secondTrace secondBit],
            StagePath.two
              ((first_stage_at_root_iff mode secret _ _).mpr ⟨firstBit, rfl, rfl⟩)
              ((second_stage_at_between_iff mode secret firstBit _ _).mpr
                ⟨secondBit, allowed, rfl, rfl⟩), rfl⟩

theorem call_cut_runs_iff (mode : Mode) (cut : Cut) (secret : Bool) (trace : Trace) :
    CallCutRuns mode cut secret trace ↔
      ∃ after, Execution.Reach (Step mode) (root secret) after ∧
        after.phase = cutPhase cut ∧ observe after = trace := by
  constructor
  · rintro ⟨labels, after, path, observed⟩
    rcases stage_path_operational path with ⟨actualPath, atCut, actualHistory⟩
    exact ⟨after, actualPath, atCut, actualHistory.trans observed.symm⟩
  · rintro ⟨after, path, atCut, observed⟩
    rcases operational_cut_stage_path path atCut with ⟨labels, stagePath, actualHistory⟩
    exact ⟨labels, after, stagePath, observed.symm.trans actualHistory⟩

theorem fresh_first_matching :
    StageMatch (FirstStage .fresh) (FirstStage .fresh) InitialRelated BoundaryRelated := by
  constructor
  · intro left right label afterLeft related edge
    rcases related with ⟨leftSecret, rightSecret, rfl, rfl⟩
    rcases (first_stage_at_root_iff .fresh leftSecret _ _).mp edge with ⟨bit, rfl, rfl⟩
    exact ⟨between rightSecret bit,
      (first_stage_at_root_iff .fresh rightSecret _ _).mpr ⟨bit, rfl, rfl⟩,
      leftSecret, rightSecret, bit, rfl, rfl⟩
  · intro left right label afterRight related edge
    rcases related with ⟨leftSecret, rightSecret, rfl, rfl⟩
    rcases (first_stage_at_root_iff .fresh rightSecret _ _).mp edge with ⟨bit, rfl, rfl⟩
    exact ⟨between leftSecret bit,
      (first_stage_at_root_iff .fresh leftSecret _ _).mpr ⟨bit, rfl, rfl⟩,
      leftSecret, rightSecret, bit, rfl, rfl⟩

theorem fresh_second_matching :
    StageMatch (SecondStage .fresh) (SecondStage .fresh) BoundaryRelated FinalRelated := by
  constructor
  · intro left right label afterLeft related edge
    rcases related with ⟨leftSecret, rightSecret, bit, rfl, rfl⟩
    rcases (second_stage_at_between_iff .fresh leftSecret bit _ _).mp edge with
      ⟨secondBit, allowed, rfl, rfl⟩
    exact ⟨completed rightSecret bit secondBit,
      (second_stage_at_between_iff .fresh rightSecret bit _ _).mpr
        ⟨secondBit, True.intro, rfl, rfl⟩,
      leftSecret, rightSecret, bit, secondBit, rfl, rfl⟩
  · intro left right label afterRight related edge
    rcases related with ⟨leftSecret, rightSecret, bit, rfl, rfl⟩
    rcases (second_stage_at_between_iff .fresh rightSecret bit _ _).mp edge with
      ⟨secondBit, allowed, rfl, rfl⟩
    exact ⟨completed leftSecret bit secondBit,
      (second_stage_at_between_iff .fresh leftSecret bit _ _).mpr
        ⟨secondBit, True.intro, rfl, rfl⟩,
      leftSecret, rightSecret, bit, secondBit, rfl, rfl⟩

/-- Derived through the generic local matching theorem and real call bindings.
The already-accepted microevent NI theorem is not used to discharge this result. -/
theorem fresh_call_cut_noninterference (cut : Cut) :
    Observations.FiniteNoninterference PublicRelated (CallCutRuns .fresh cut) := by
  intro leftSecret rightSecret related trace
  have initial : InitialRelated (root leftSecret) (root rightSecret) :=
    ⟨leftSecret, rightSecret, rfl, rfl⟩
  constructor
  · rintro ⟨labels, after, path, observed⟩
    rcases stage_prefix_forward fresh_first_matching fresh_second_matching initial path with
      ⟨target, targetPath, postRelated⟩
    exact ⟨labels, target, targetPath, observed⟩
  · rintro ⟨labels, after, path, observed⟩
    rcases stage_prefix_backward fresh_first_matching fresh_second_matching initial path with
      ⟨target, targetPath, postRelated⟩
    exact ⟨labels, target, targetPath, observed⟩

/-- Both compared boundaries are actual first-call returns with the same first
label. The retained second call cannot match from this fixed related pair. -/
theorem retained_boundary_mismatch :
    FirstStage .retained (root false) (firstTrace false) (between false false) ∧
    FirstStage .retained (root true) (firstTrace false) (between true false) ∧
    BoundaryRelated (between false false) (between true false) ∧
    SecondStage .retained (between false false) (secondTrace false)
      (completed false false false) ∧
    ¬ ∃ target, SecondStage .retained (between true false) (secondTrace false) target := by
  refine ⟨(first_stage_at_root_iff .retained false _ _).mpr ⟨false, rfl, rfl⟩,
    (first_stage_at_root_iff .retained true _ _).mpr ⟨false, rfl, rfl⟩,
    ⟨false, true, false, rfl, rfl⟩,
    (second_stage_at_between_iff .retained false false _ _).mpr ⟨false, rfl, rfl, rfl⟩,
    ?_⟩
  rintro ⟨target, edge⟩
  rcases (second_stage_at_between_iff .retained true false _ _).mp edge with
    ⟨secondBit, allowed, observed, final⟩
  change secondBit = true at allowed
  subst secondBit
  simp [secondTrace, address, bitLocation] at observed

theorem marginal_summary_does_not_supply_stage_contract :
    (∀ which, Observations.FiniteNoninterference PublicRelated (CallRuns .retained which)) ∧
    ¬ StageMatch (SecondStage .retained) (SecondStage .retained)
      BoundaryRelated FinalRelated := by
  constructor
  · exact retained_marginals_noninterference
  · intro contract
    rcases retained_boundary_mismatch with
      ⟨leftFirst, rightFirst, related, leftSecond, noMatch⟩
    rcases contract.forward related leftSecond with ⟨target, matched, postRelated⟩
    exact noMatch ⟨target, matched⟩

/- Generic stage cuts are batch boundaries. The accepted specimen theorem
fresh_all_microevent_prefixes_noninterference separately covers its internal
one-event prefixes. No contextual/probabilistic/unbounded-call claim follows. -/
#print axioms stage_prefix_forward
#print axioms stage_prefix_backward
#print axioms stage_observations_iff
#print axioms first_stage_iff
#print axioms second_stage_iff
#print axioms stage_path_operational
#print axioms operational_cut_stage_path
#print axioms call_cut_runs_iff
#print axioms fresh_first_matching
#print axioms fresh_second_matching
#print axioms fresh_call_cut_noninterference
#print axioms retained_boundary_mismatch
#print axioms marginal_summary_does_not_supply_stage_contract

end AnnealResearch.CallSecurityComposition
