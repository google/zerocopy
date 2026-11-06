import AnnealResearch.DesignModelTransfer

set_option Elab.async false

/-!
# R-ADEV-03 Module 2: Negative Controls Challenging Weak and Circular Conformance
Compacted for Linux `x86_64` `-M768`: `set_option Elab.async false`, zero `inductive`/`structure`,
`noncomputable def` on value definitions, 15 top-level declarations.
-/

namespace AnnealResearch.DesignModelControls

open AnnealResearch.DesignModelTransfer

def IsTerminal (i : LeaseImplState) : Prop :=
  i.2.2.2.1 = (false, true) ∨ i.2.2.2.1 = (true, false)

def SameCompletedOutput (m : LeaseModelState) (i : LeaseImplState) : Prop :=
  m.1 = i.1 ∧
  ((m.2 = (false, true, true) ∧ i.2.2.2.1 = (false, true)) ∨
   (m.2 = (false, true, false) ∧ i.2.2.2.1 = (true, false)))

def CompletedOutputConformance
    (modelSys : Execution.System LeaseModelState)
    (implSys : Execution.System LeaseImplState)
    (mInit : LeaseModelState) (iInit : LeaseImplState) : Prop :=
  ∀ iTerm, Execution.Reaches implSys iInit iTerm → IsTerminal iTerm →
    ∃ mTerm, Execution.Reaches modelSys mInit mTerm ∧
      SameCompletedOutput mTerm iTerm ∧ (implSys.2 iTerm → modelSys.2 mTerm)

theorem faithful_impl_satisfies_completed_conformance (req : RequestKind) :
    CompletedOutputConformance leaseModelSys faithfulLeaseImplSys
      (modelInit req) (implInit req) := by
  have hPend : ∀ {s : LeaseImplState}, s.2.2.2.1 = (false, false) → IsTerminal s → False := by
    intro s hOut hTerm; rcases hTerm with hOk | hErr
    · rw [hOut] at hOk; have hF : false = true := congrArg Prod.snd hOk; cases hF
    · rw [hOut] at hErr; have hF : false = true := congrArg Prod.fst hErr; cases hF
  intro iTerm hReach hTerm
  rcases prefix_conformance_reaches_related (faithful_impl_conforms req) hReach with
    ⟨mTerm, hReachM, hRel⟩
  change mTerm = modelOfImpl iTerm at hRel; subst hRel
  have hStateSet :
      (∃ r, iTerm = implInit r) ∨
      (∃ r, iTerm = (r, (false, true), (false, true), (false, false), false)) ∨
      iTerm = ((false, false), (true, false), (false, true), (false, false), false) ∨
      iTerm = ((false, false), (true, true), (true, false), (false, true), false) ∨
      iTerm = ((false, true), (true, true), (true, false), (true, false), false) ∨
      iTerm = ((true, false), (false, true), (false, true), (true, true), false) := by
    refine Execution.invariant_reachable
      (Step := faithfulLeaseImplSys.1)
      (Invariant := fun s : LeaseImplState =>
        (∃ r, s = implInit r) ∨
        (∃ r, s = (r, (false, true), (false, true), (false, false), false)) ∨
        s = ((false, false), (true, false), (false, true), (false, false), false) ∨
        s = ((false, false), (true, true), (true, false), (false, true), false) ∨
        s = ((false, true), (true, true), (true, false), (true, false), false) ∨
        s = ((true, false), (false, true), (false, true), (true, true), false))
      (initial := implInit req)
      ?_ ?_ hReach
    · exact Or.inl ⟨req, rfl⟩
    · intro a b _ hStep
      rcases hStep with ⟨r, _, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩ | ⟨_, hb⟩
      · subst hb; exact Or.inr (Or.inl ⟨r, rfl⟩)
      · subst hb; exact Or.inr (Or.inr (Or.inl rfl))
      · subst hb; exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · subst hb; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · subst hb; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      · subst hb; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hStateSet with ⟨r, hi⟩ | ⟨r, hi⟩ | hi | hi | hi | hi
  · subst hi; exact False.elim (hPend rfl hTerm)
  · subst hi; exact False.elim (hPend rfl hTerm)
  · subst hi; exact False.elim (hPend rfl hTerm)
  · subst hi
    refine ⟨modelOfImpl ((false, false), (true, true), (true, false), (false, true), false),
      hReachM, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    intro hBad; change false = true at hBad; cases hBad
  · subst hi
    refine ⟨modelOfImpl ((false, true), (true, true), (true, false), (true, false), false),
      hReachM, ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    intro hBad; change false = true at hBad; cases hBad
  · subst hi
    rcases hTerm with hOk | hErr
    · have hF : true = false := congrArg Prod.fst hOk; cases hF
    · have hF : true = false := congrArg Prod.snd hErr; cases hF

noncomputable def transientFaultThenRecoverImplSys : Execution.System LeaseImplState :=
  (fun s t =>
    (s = implInit (false, false) ∧
      t = ((false, false), (true, false), (false, false), (false, false), true)) ∨
    (s = ((false, false), (true, false), (false, false), (false, false), true) ∧
      t = ((false, false), (true, true), (true, false), (false, true), false)),
   fun s => s.2.2.2.2 = true)

theorem transient_fault_impl_satisfies_completed_conformance :
    CompletedOutputConformance leaseModelSys transientFaultThenRecoverImplSys
      (modelInit (false, false)) (implInit (false, false)) := by
  intro iTerm hReach hTerm
  have hInv :
      iTerm = implInit (false, false) ∨
      iTerm = ((false, false), (true, false), (false, false), (false, false), true) ∨
      iTerm = ((false, false), (true, true), (true, false), (false, true), false) := by
    refine Execution.invariant_reachable
      (Step := transientFaultThenRecoverImplSys.1)
      (Invariant := fun s : LeaseImplState =>
        s = implInit (false, false) ∨
        s = ((false, false), (true, false), (false, false), (false, false), true) ∨
        s = ((false, false), (true, true), (true, false), (false, true), false))
      (initial := implInit (false, false))
      ?_ ?_ hReach
    · exact Or.inl rfl
    · intro a b _ hStep
      rcases hStep with ⟨_, hb⟩ | ⟨_, hb⟩
      · subst hb; exact Or.inr (Or.inl rfl)
      · subst hb; exact Or.inr (Or.inr rfl)
  rcases hInv with hInit | hFault | hComp
  · subst hInit; rcases hTerm with hOk | hErr
    · have hF : false = true := congrArg Prod.snd hOk; cases hF
    · have hF : false = true := congrArg Prod.fst hErr; cases hF
  · subst hFault; rcases hTerm with hOk | hErr
    · have hF : false = true := congrArg Prod.snd hOk; cases hF
    · have hF : false = true := congrArg Prod.fst hErr; cases hF
  · subst hComp
    have hM1 : Execution.Reaches leaseModelSys (modelInit (false, false))
        ((false, false), (false, false, true)) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨(false, false), rfl, rfl⟩)
    have hMR : Execution.Reaches leaseModelSys (modelInit (false, false))
        ((false, false), (false, true, true)) :=
      Execution.Reach.tail hM1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    refine ⟨((false, false), (false, true, true)), hMR, ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    intro hBad; change false = true at hBad; cases hBad

theorem completed_conformance_fails_to_transfer_noUB :
    Execution.SysNoUB leaseModelSys (modelInit (false, false)) ∧
    CompletedOutputConformance leaseModelSys transientFaultThenRecoverImplSys
      (modelInit (false, false)) (implInit (false, false)) ∧
    ¬ Execution.SysNoUB transientFaultThenRecoverImplSys (implInit (false, false)) := by
  refine ⟨lease_model_noUB (false, false),
    transient_fault_impl_satisfies_completed_conformance, ?_⟩
  have hRF : Execution.Reaches transientFaultThenRecoverImplSys (implInit (false, false))
      ((false, false), (true, false), (false, false), (false, false), true) :=
    Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨rfl, rfl⟩)
  exact Execution.bad_prefix_not_noUB hRF rfl

noncomputable def faultBeforeDivergenceImplSys : Execution.System LeaseImplState :=
  (fun s t =>
    (s = implInit (true, false) ∧
      t = ((true, false), (false, true), (false, false), (true, true), true)) ∨
    (s = ((true, false), (false, true), (false, false), (true, true), true) ∧
      t = ((true, false), (false, true), (false, false), (true, true), true)),
   fun s => s.2.2.2.2 = true)

theorem fault_before_divergence_counterexample :
    (∀ s, Execution.Reaches faultBeforeDivergenceImplSys (implInit (true, false)) s →
      ¬ IsTerminal s) ∧
    CompletedOutputConformance leaseModelSys faultBeforeDivergenceImplSys
      (modelInit (true, false)) (implInit (true, false)) ∧
    ¬ Execution.SysNoUB faultBeforeDivergenceImplSys (implInit (true, false)) ∧
    (∀ Rel, ¬ PrefixConformance leaseModelSys faultBeforeDivergenceImplSys Rel
        (modelInit (true, false)) (implInit (true, false))) := by
  have hNoTerm : ∀ s, Execution.Reaches faultBeforeDivergenceImplSys
      (implInit (true, false)) s → ¬ IsTerminal s := by
    intro s hReach hTerm
    have hInv : s = implInit (true, false) ∨
        s = ((true, false), (false, true), (false, false), (true, true), true) := by
      refine Execution.invariant_reachable
        (Step := faultBeforeDivergenceImplSys.1)
        (Invariant := fun x : LeaseImplState =>
          x = implInit (true, false) ∨
          x = ((true, false), (false, true), (false, false), (true, true), true))
        (initial := implInit (true, false))
        ?_ ?_ hReach
      · exact Or.inl rfl
      · intro a b _ hStep; rcases hStep with ⟨_, hb⟩ | ⟨_, hb⟩
        · subst hb; exact Or.inr rfl
        · subst hb; exact Or.inr rfl
    rcases hInv with hInit | hLoop
    · subst hInit; rcases hTerm with hOk | hErr
      · have hF : false = true := congrArg Prod.snd hOk; cases hF
      · have hF : false = true := congrArg Prod.fst hErr; cases hF
    · subst hLoop; rcases hTerm with hOk | hErr
      · have hF : true = false := congrArg Prod.fst hOk; cases hF
      · have hF : true = false := congrArg Prod.snd hErr; cases hF
  have hUnsafe : ¬ Execution.SysNoUB faultBeforeDivergenceImplSys (implInit (true, false)) := by
    have hRF : Execution.Reaches faultBeforeDivergenceImplSys (implInit (true, false))
        ((true, false), (false, true), (false, false), (true, true), true) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨rfl, rfl⟩)
    exact Execution.bad_prefix_not_noUB hRF rfl
  refine ⟨hNoTerm, ?_, hUnsafe, ?_⟩
  · intro iTerm hReach hTerm; exact False.elim (hNoTerm iTerm hReach hTerm)
  · intro Rel hConf
    exact hUnsafe (prefix_conformance_transfers_noUB hConf (lease_model_noUB (true, false)))

def ExistentialBranchConformance
    {MState IState : Type}
    (modelSys : Execution.System MState) (implSys : Execution.System IState)
    (Rel : MState → IState → Prop) (mInit : MState) (iInit : IState) : Prop :=
  Rel mInit iInit ∧
  (∃ m' i', modelSys.1 mInit m' ∧ implSys.1 iInit i' ∧ Rel m' i') ∧
  (∀ m i, Rel m i → implSys.2 i → modelSys.2 m)

noncomputable def demonicTwoBranchImplSys : Execution.System LeaseImplState :=
  (fun s t =>
    (s = implInit (false, false) ∧
      t = ((false, false), (false, true), (false, true), (false, false), false)) ∨
    (s = implInit (false, false) ∧
      t = ((false, false), (true, false), (false, false), (false, false), true)) ∨
    (s = ((false, false), (false, true), (false, true), (false, false), false) ∧
      t = ((false, false), (true, true), (true, false), (false, true), false)),
   fun s => s.2.2.2.2 = true)

theorem omitted_demonic_branch_control :
    ExistentialBranchConformance leaseModelSys demonicTwoBranchImplSys LeaseRelated
      (modelInit (false, false)) (implInit (false, false)) ∧
    ¬ Execution.SysNoUB demonicTwoBranchImplSys (implInit (false, false)) ∧
    (∀ Rel, ¬ PrefixConformance leaseModelSys demonicTwoBranchImplSys Rel
        (modelInit (false, false)) (implInit (false, false))) := by
  have hUnsafe : ¬ Execution.SysNoUB demonicTwoBranchImplSys (implInit (false, false)) := by
    have hRF : Execution.Reaches demonicTwoBranchImplSys (implInit (false, false))
        ((false, false), (true, false), (false, false), (false, false), true) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact Execution.bad_prefix_not_noUB hRF rfl
  refine ⟨⟨rfl, ?_, (faithful_impl_conforms (false, false)).2.2⟩, hUnsafe, ?_⟩
  · exact ⟨((false, false), (false, false, true)),
      ((false, false), (false, true), (false, true), (false, false), false),
      Or.inl ⟨(false, false), rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩, rfl⟩
  · intro Rel hConf
    exact hUnsafe (prefix_conformance_transfers_noUB hConf (lease_model_noUB (false, false)))

def CircularRel
    (ModelInv : LeaseModelState → Prop) (implSys : Execution.System LeaseImplState)
    (m : LeaseModelState) (i : LeaseImplState) : Prop :=
  ModelInv m ∧ ¬ implSys.2 i

def CircularConformance
    (modelSys : Execution.System LeaseModelState) (implSys : Execution.System LeaseImplState)
    (ModelInv : LeaseModelState → Prop) (mInit : LeaseModelState) (iInit : LeaseImplState) : Prop :=
  CircularRel ModelInv implSys mInit iInit ∧
  (∀ m i i', CircularRel ModelInv implSys m i → implSys.1 i i' →
    ∃ m', Execution.Reaches modelSys m m' ∧ CircularRel ModelInv implSys m' i')

theorem circular_premise_control
    (modelSys : Execution.System LeaseModelState) (implSys : Execution.System LeaseImplState)
    (ModelInv : LeaseModelState → Prop) (mInit : LeaseModelState) (iInit : LeaseImplState) :
    (∀ m i, CircularRel ModelInv implSys m i → implSys.2 i → modelSys.2 m) ∧
    (CircularConformance modelSys implSys ModelInv mInit iInit →
      Execution.SysNoUB implSys iInit) ∧
    leaseModelSys.2 ((false, false), (true, false, false)) := by
  refine ⟨?_, ?_, rfl⟩
  · intro m i hRel hBadI; exact False.elim (hRel.2 hBadI)
  · intro hCirc
    apply Execution.invariant_noUB
      (Invariant := fun i => ∃ m, CircularRel ModelInv implSys m i)
    · exact ⟨mInit, hCirc.1⟩
    · intro s t hInv hStep
      rcases hInv with ⟨m, hRel⟩
      rcases hCirc.2 m s t hRel hStep with ⟨m', _, hRel'⟩
      exact ⟨m', hRel'⟩
    · intro s hInv; rcases hInv with ⟨_, _, hNotBad⟩; exact hNotBad

#print axioms faithful_impl_satisfies_completed_conformance
#print axioms transient_fault_impl_satisfies_completed_conformance
#print axioms completed_conformance_fails_to_transfer_noUB
#print axioms fault_before_divergence_counterexample
#print axioms omitted_demonic_branch_control
#print axioms circular_premise_control

end AnnealResearch.DesignModelControls
