import AnnealResearch.Execution

set_option Elab.async false

/-!
# R-ADEV-03 Module 1: Non-Circular Safety Transfer from Design Models

Compacted for the Linux `x86_64` `-M768` envelope: `set_option Elab.async false`,
zero `inductive`/`structure` declarations, `noncomputable def` on all value-level
definitions, and 20 top-level declarations total.
-/

namespace AnnealResearch.Execution

universe u

abbrev System (S : Type u) : Type u :=
  (S → S → Prop) × (S → Prop)

abbrev Reaches {S : Type u} (sys : System S) (a b : S) : Prop :=
  Reach sys.1 a b

abbrev SysNoUB {S : Type u} (sys : System S) (initial : S) : Prop :=
  NoUB sys.1 sys.2 initial

end AnnealResearch.Execution

namespace AnnealResearch.DesignModelTransfer

universe u

theorem reaches_trans {S : Type u} {sys : Execution.System S} {a b c : S}
    (hab : Execution.Reaches sys a b) (hbc : Execution.Reaches sys b c) :
    Execution.Reaches sys a c :=
  Execution.Reach.trans hab hbc

def PrefixConformance
    {MState IState : Type u}
    (modelSys : Execution.System MState)
    (implSys : Execution.System IState)
    (Rel : MState → IState → Prop)
    (mInit : MState) (iInit : IState) : Prop :=
  Rel mInit iInit ∧
  (∀ m i i', Rel m i → implSys.1 i i' →
    ∃ m', Execution.Reaches modelSys m m' ∧ Rel m' i') ∧
  (∀ m i, Rel m i → implSys.2 i → modelSys.2 m)

theorem prefix_conformance_reaches_related
    {MState IState : Type u}
    {modelSys : Execution.System MState} {implSys : Execution.System IState}
    {Rel : MState → IState → Prop} {mInit : MState} {iInit i : IState}
    (hConf : PrefixConformance modelSys implSys Rel mInit iInit)
    (hReach : Execution.Reaches implSys iInit i) :
    ∃ m, Execution.Reaches modelSys mInit m ∧ Rel m i := by
  induction hReach with
  | refl =>
    exact ⟨mInit, Execution.Reach.refl mInit, hConf.1⟩
  | tail _ hStep ih =>
    rcases ih with ⟨mMid, hReachMid, hRelMid⟩
    rcases hConf.2.1 mMid _ _ hRelMid hStep with ⟨m', hReachStep, hRel'⟩
    exact ⟨m', reaches_trans hReachMid hReachStep, hRel'⟩

theorem prefix_conformance_transfers_noUB
    {MState IState : Type u}
    {modelSys : Execution.System MState} {implSys : Execution.System IState}
    {Rel : MState → IState → Prop} {mInit : MState} {iInit : IState}
    (hConf : PrefixConformance modelSys implSys Rel mInit iInit)
    (hModelSafe : Execution.SysNoUB modelSys mInit) :
    Execution.SysNoUB implSys iInit := by
  intro i hReach hBadI
  rcases prefix_conformance_reaches_related hConf hReach with ⟨m, hReachM, hRel⟩
  exact hModelSafe m hReachM (hConf.2.2 m i hRel hBadI)

/-! ## Concrete Lease Design Model and Operational Client -/

-- RequestKind: (false,false)=validOp, (false,true)=invalidInputErr, (true,false)=divergingLoop
abbrev RequestKind : Type := Bool × Bool

-- LeasePhase: (false,false,false)=unacquired, (false,false,true)=exclusiveHeld,
-- (false,true,false)=ordinaryErr, (false,true,true)=released, (true,false,false)=protocolFault
abbrev LeaseModelState : Type := RequestKind × (Bool × Bool × Bool)

noncomputable def modelInit (req : RequestKind) : LeaseModelState :=
  (req, (false, false, false))

noncomputable def leaseModelSys : Execution.System LeaseModelState :=
  (fun s t =>
    (∃ req : RequestKind,
      s = (req, (false, false, false)) ∧
      t = (req, (false, false, true))) ∨
    (s = ((false, false), (false, false, true)) ∧
      t = ((false, false), (false, true, true))) ∨
    (s = ((false, true), (false, false, true)) ∧
      t = ((false, true), (false, true, false))) ∨
    (s = ((true, false), (false, false, true)) ∧
      t = ((true, false), (false, false, true))),
   fun s => s.2 = (true, false, false))

theorem lease_model_noUB (req : RequestKind) :
    Execution.SysNoUB leaseModelSys (modelInit req) := by
  apply Execution.invariant_noUB (Invariant := fun s : LeaseModelState => s.2.1 = false)
  · rfl
  · intro s t _ hStep
    rcases hStep with ⟨_, _, ht⟩ | ⟨_, ht⟩ | ⟨_, ht⟩ | ⟨_, ht⟩
    · subst ht; rfl
    · subst ht; rfl
    · subst ht; rfl
    · subst ht; rfl
  · intro s hInv hBad
    change s.2 = (true, false, false) at hBad
    have h1 : s.2.1 = true := congrArg Prod.fst hBad
    rw [hInv] at h1
    cases h1

-- LeaseImplState := RequestKind × SlotState × HandleState × ImplOutcome × fault
-- SlotState: (false,false)=idle, (false,true)=claimed, (true,false)=worked, (true,true)=closed
-- HandleState: (false,false)=none, (false,true)=active, (true,false)=released
-- ImplOutcome: (false,false)=pending, (false,true)=ok, (true,false)=err, (true,true)=diverging
abbrev LeaseImplState : Type :=
  RequestKind × (Bool × Bool) × (Bool × Bool) × (Bool × Bool) × Bool

noncomputable def implInit (req : RequestKind) : LeaseImplState :=
  (req, (false, false), (false, false), (false, false), false)

noncomputable def faithfulLeaseImplSys : Execution.System LeaseImplState :=
  (fun s t =>
    (∃ req : RequestKind,
      s = implInit req ∧
      t = (req, (false, true), (false, true), (false, false), false)) ∨
    (s = ((false, false), (false, true), (false, true), (false, false), false) ∧
      t = ((false, false), (true, false), (false, true), (false, false), false)) ∨
    (s = ((false, false), (true, false), (false, true), (false, false), false) ∧
      t = ((false, false), (true, true), (true, false), (false, true), false)) ∨
    (s = ((false, true), (false, true), (false, true), (false, false), false) ∧
      t = ((false, true), (true, true), (true, false), (true, false), false)) ∨
    (s = ((true, false), (false, true), (false, true), (false, false), false) ∧
      t = ((true, false), (false, true), (false, true), (true, true), false)) ∨
    (s = ((true, false), (false, true), (false, true), (true, true), false) ∧
      t = ((true, false), (false, true), (false, true), (true, true), false)),
   fun s => s.2.2.2.2 = true)

noncomputable def modelOfImpl (s : LeaseImplState) : LeaseModelState :=
  (s.1,
   cond s.2.2.2.2
     (true, false, false)
     (cond s.2.1.1
       (cond s.2.1.2
         (cond s.2.2.2.1.1 (false, true, false) (false, true, true))
         (false, false, true))
       (cond s.2.1.2
         (false, false, true)
         (false, false, false))))

def LeaseRelated (m : LeaseModelState) (i : LeaseImplState) : Prop :=
  m = modelOfImpl i

theorem faithful_impl_conforms (req : RequestKind) :
    PrefixConformance leaseModelSys faithfulLeaseImplSys LeaseRelated
      (modelInit req) (implInit req) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro m i i' hRel hStep
    change m = modelOfImpl i at hRel
    subst hRel
    rcases hStep with
      ⟨r, hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl (r, (false, true), (false, true), (false, false), false),
        Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨r, rfl, rfl⟩),
        rfl⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl ((false, false), (true, false), (false, true), (false, false), false),
        Execution.Reach.refl _,
        rfl⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl ((false, false), (true, true), (true, false), (false, true), false),
        Execution.Reach.tail (Execution.Reach.refl _) (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        rfl⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl ((false, true), (true, true), (true, false), (true, false), false),
        Execution.Reach.tail (Execution.Reach.refl _) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
        rfl⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl ((true, false), (false, true), (false, true), (true, true), false),
        Execution.Reach.tail (Execution.Reach.refl _) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))),
        rfl⟩
    · subst hi; subst hi'
      exact ⟨modelOfImpl ((true, false), (false, true), (false, true), (true, true), false),
        Execution.Reach.tail (Execution.Reach.refl _) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))),
        rfl⟩
  · intro m i hRel hBad
    change m = modelOfImpl i at hRel
    change i.2.2.2.2 = true at hBad
    subst hRel
    change (cond i.2.2.2.2 (true, false, false)
      (cond i.2.1.1
        (cond i.2.1.2
          (cond i.2.2.2.1.1 (false, true, false) (false, true, true))
          (false, false, true))
        (cond i.2.1.2 (false, false, true) (false, false, false)))) = (true, false, false)
    rw [hBad]
    rfl

theorem faithful_impl_noUB_transferred (req : RequestKind) :
    Execution.SysNoUB faithfulLeaseImplSys (implInit req) :=
  prefix_conformance_transfers_noUB (faithful_impl_conforms req) (lease_model_noUB req)

theorem faithful_impl_admits_all_three_outcomes :
    Execution.Reaches faithfulLeaseImplSys (implInit (false, false))
      ((false, false), (true, true), (true, false), (false, true), false) ∧
    (Execution.Reaches faithfulLeaseImplSys (implInit (false, true))
      ((false, true), (true, true), (true, false), (true, false), false) ∧
      ¬ faithfulLeaseImplSys.2
        ((false, true), (true, true), (true, false), (true, false), false)) ∧
    (Execution.Reaches faithfulLeaseImplSys (implInit (true, false))
      ((true, false), (false, true), (false, true), (true, true), false) ∧
      faithfulLeaseImplSys.1
        ((true, false), (false, true), (false, true), (true, true), false)
        ((true, false), (false, true), (false, true), (true, true), false)) := by
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have h1 : Execution.Reaches faithfulLeaseImplSys (implInit (false, false))
        ((false, false), (false, true), (false, true), (false, false), false) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨(false, false), rfl, rfl⟩)
    have h2 : Execution.Reaches faithfulLeaseImplSys (implInit (false, false))
        ((false, false), (true, false), (false, true), (false, false), false) :=
      Execution.Reach.tail h1 (Or.inr (Or.inl ⟨rfl, rfl⟩))
    exact Execution.Reach.tail h2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  · have h1 : Execution.Reaches faithfulLeaseImplSys (implInit (false, true))
        ((false, true), (false, true), (false, true), (false, false), false) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨(false, true), rfl, rfl⟩)
    exact Execution.Reach.tail h1 (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  · intro hBad
    change false = true at hBad
    cases hBad
  · have h1 : Execution.Reaches faithfulLeaseImplSys (implInit (true, false))
        ((true, false), (false, true), (false, true), (false, false), false) :=
      Execution.Reach.tail (Execution.Reach.refl _) (Or.inl ⟨(true, false), rfl, rfl⟩)
    exact Execution.Reach.tail h1 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))

#print axioms reaches_trans
#print axioms prefix_conformance_transfers_noUB
#print axioms lease_model_noUB
#print axioms faithful_impl_conforms
#print axioms faithful_impl_noUB_transferred
#print axioms faithful_impl_admits_all_three_outcomes

end AnnealResearch.DesignModelTransfer
