/-
# Tightness counterexamples, non-vacuity witnesses, positive controls

Canonical form of a tightness counterexample: a concrete instance satisfies all the *other*
hypotheses of the named result, and the result's conclusion fails. Canonical form of a
non-vacuity witness: a concrete instance satisfies all hypotheses of the named result.
-/
import ToyRice.Examples

namespace Toy.Rice.Controls

open Toy.Rice Toy.Rice.Examples

/-! ## `not_decidedInside_of_fixpointPrinciple_extensional_nontrivial` -/

/-- Without the fixpoint principle (lookup tables), a nontrivial extensional predicate is
decided inside the system. Also the positive control. -/
theorem rice_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ NontrivialPred Tables.IsZeroFn ∧
      DecidedInside Tables.sys Tables.IsZeroFn :=
  ⟨Tables.isZeroFn_extensional, Tables.isZeroFn_nontrivial, Tables.isZeroFn_decidedInside⟩

/-- Without extensionality (padded system, `EvenPad`), a nontrivial predicate is decided
inside a system with the fixpoint principle. -/
theorem rice_tight_extensional :
    FixpointPrinciple Padded.sys ∧ NontrivialPred Padded.EvenPad ∧
      DecidedInside Padded.sys Padded.EvenPad :=
  ⟨Padded.fixpointPrinciple, Padded.evenPad_nontrivial, decidedInside_pos_padded⟩

/-- Without "some code satisfies `P`" (here `P = False`), the conclusion fails. -/
theorem rice_tight_nontrivial_hasMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => False) ∧
      (∃ _ : Padded.Code, ¬ False) ∧ DecidedInside Padded.sys (fun _ => False) :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, ⟨.hid true 0, id⟩,
    ⟨fun _ => false, fun _ => ⟨fun h => Bool.noConfusion h, False.elim⟩,
      fun _ b => Padded.constClosed b⟩⟩

/-- Without "some code violates `P`" (here `P = True`), the conclusion fails. -/
theorem rice_tight_nontrivial_hasNonMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      (∃ _ : Padded.Code, True) ∧ DecidedInside Padded.sys (fun _ => True) :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, ⟨.hid true 0, trivial⟩,
    ⟨fun _ => true, fun _ => ⟨fun _ => trivial, fun _ => rfl⟩,
      fun a _ => Padded.constClosed a⟩⟩

/-- All hypotheses hold together (padded system, `BehTrue`; flat system, `Halts`). -/
theorem rice_nonvacuous :
    (FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue) ∧
    (FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧ NontrivialPred Flat.Halts) :=
  ⟨⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.behTrue_nontrivial⟩,
    ⟨Flat.fixpointPrinciple, Flat.extensional_all _, Flat.halts_nontrivial⟩⟩

/-! ## `swappedSwitch_not_admissible_of_fixpointPrinciple_extensional_decides` -/

/-- Without the fixpoint principle: in the lookup-table system the swapped switch on
`zeroCheck` (with `a = []` a zero table and `b = [(0, 1)]` a nonzero one) is admissible. -/
theorem riceSharp_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ Decides Tables.zeroCheck Tables.IsZeroFn ∧
      Tables.IsZeroFn [] ∧ ¬ Tables.IsZeroFn [(0, 1)] ∧
      Tables.sys.Adm (switch Tables.zeroCheck [(0, 1)] []) :=
  ⟨Tables.isZeroFn_extensional, Tables.zeroCheck_decides, fun _ => rfl, isZeroFn_neg,
    Tables.zeroCheck_switchAdmissible _ _⟩

/-- Without extensionality: the swapped switch on `evenPadCheck` is admissible. -/
theorem riceSharp_tight_extensional :
    FixpointPrinciple Padded.sys ∧ Decides Padded.evenPadCheck Padded.EvenPad ∧
      Padded.EvenPad (.hid true 0) ∧ ¬ Padded.EvenPad (.hid true 1) ∧
      Padded.sys.Adm (switch Padded.evenPadCheck (.hid true 1) (.hid true 0)) :=
  ⟨Padded.fixpointPrinciple, Padded.evenPadCheck_decides, rfl,
    by unfold Padded.EvenPad; decide, Padded.evenPadCheck_switchAdmissible _ _⟩

/-- Without `Decides`: the constant-`false` checker does not decide halting, and its swapped
switch (a constant) is admissible. Here `a = tt` halts and `b = bot` does not. -/
theorem riceSharp_tight_decides :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Flat.Halts Flat.Flat.tt ∧ ¬ Flat.Halts Flat.Flat.bot ∧
      Flat.sys.Adm (switch (fun _ => false) Flat.Flat.bot Flat.Flat.tt) := by
  refine ⟨Flat.fixpointPrinciple, Flat.extensional_all _, fun h => Flat.Flat.noConfusion h,
    halts_neg, ?_⟩
  intro x y _
  right; rfl

/-- Without `P a`: with `a = b = bot` (only `¬ P b` holds), the swapped switch is the constant
`bot`, which is admissible. -/
theorem riceSharp_tight_member :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ ¬ Flat.Halts Flat.Flat.bot ∧
      Flat.sys.Adm (switch Flat.haltCheck Flat.Flat.bot Flat.Flat.bot) := by
  refine ⟨Flat.fixpointPrinciple, Flat.extensional_all _, Flat.haltCheck_decides,
    halts_neg, ?_⟩
  intro x y _
  left
  show cond (Flat.haltCheck x) Flat.Flat.bot Flat.Flat.bot = Flat.Flat.bot
  cases Flat.haltCheck x <;> rfl

/-- Without `¬ P b`: with `a = b = tt` (only `P a` holds), the swapped switch is the constant
`tt`, which is admissible. -/
theorem riceSharp_tight_nonmember :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ Flat.Halts Flat.Flat.tt ∧
      Flat.sys.Adm (switch Flat.haltCheck Flat.Flat.tt Flat.Flat.tt) := by
  refine ⟨Flat.fixpointPrinciple, Flat.extensional_all _, Flat.haltCheck_decides,
    fun h => Flat.Flat.noConfusion h, ?_⟩
  intro x y _
  right
  show cond (Flat.haltCheck x) Flat.Flat.tt Flat.Flat.tt =
    cond (Flat.haltCheck y) Flat.Flat.tt Flat.Flat.tt
  cases Flat.haltCheck x <;> cases Flat.haltCheck y <;> rfl

theorem riceSharp_nonvacuous :
    FixpointPrinciple Flat.sys ∧ Extensional Flat.sys Flat.Halts ∧
      Decides Flat.haltCheck Flat.Halts ∧ Flat.Halts Flat.Flat.tt ∧
      ¬ Flat.Halts Flat.Flat.bot :=
  ⟨Flat.fixpointPrinciple, Flat.extensional_all _, Flat.haltCheck_decides,
    fun h => Flat.Flat.noConfusion h, halts_neg⟩

/-! ## `not_decidedBy_of_fixpointPrinciple_switchClosed_extensional_nontrivial` -/

theorem riceClosure_tight_fixpointPrinciple :
    SwitchClosed Tables.sys (SwitchAdmissible Tables.sys) ∧
      Extensional Tables.sys Tables.IsZeroFn ∧ NontrivialPred Tables.IsZeroFn ∧
      DecidedBy Tables.sys (SwitchAdmissible Tables.sys) Tables.IsZeroFn :=
  ⟨fun _ h => h, Tables.isZeroFn_extensional, Tables.isZeroFn_nontrivial,
    ⟨Tables.zeroCheck, Tables.zeroCheck_switchAdmissible, Tables.zeroCheck_decides⟩⟩

/-- Without `SwitchClosed`: with `K` = all checkers, the behaviour-reading checker decides
`BehTrue` in the padded system. Being an honest Boolean function is not enough; its switches
must be admissible. -/
theorem riceClosure_tight_switchClosed :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue ∧ DecidedBy Padded.sys (fun _ => True) Padded.BehTrue :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.behTrue_nontrivial,
    ⟨Padded.Code.beh, trivial, fun _ => Iff.rfl⟩⟩

theorem riceClosure_tight_extensional :
    FixpointPrinciple Padded.sys ∧ SwitchClosed Padded.sys (SwitchAdmissible Padded.sys) ∧
      NontrivialPred Padded.EvenPad ∧
      DecidedBy Padded.sys (SwitchAdmissible Padded.sys) Padded.EvenPad :=
  ⟨Padded.fixpointPrinciple, fun _ h => h, Padded.evenPad_nontrivial,
    ⟨_, Padded.evenPadCheck_switchAdmissible, Padded.evenPadCheck_decides⟩⟩

theorem riceClosure_tight_nontrivial_hasMember :
    FixpointPrinciple Padded.sys ∧ SwitchClosed Padded.sys (SwitchAdmissible Padded.sys) ∧
      Extensional Padded.sys (fun _ => False) ∧ (∃ _ : Padded.Code, ¬ False) ∧
      DecidedBy Padded.sys (SwitchAdmissible Padded.sys) (fun _ => False) :=
  ⟨Padded.fixpointPrinciple, fun _ h => h, fun _ _ _ => Iff.rfl, ⟨.hid true 0, id⟩,
    ⟨fun _ => false, fun _ b => Padded.constClosed b,
      fun _ => ⟨fun h => Bool.noConfusion h, False.elim⟩⟩⟩

theorem riceClosure_tight_nontrivial_hasNonMember :
    FixpointPrinciple Padded.sys ∧ SwitchClosed Padded.sys (SwitchAdmissible Padded.sys) ∧
      Extensional Padded.sys (fun _ => True) ∧ (∃ _ : Padded.Code, True) ∧
      DecidedBy Padded.sys (SwitchAdmissible Padded.sys) (fun _ => True) :=
  ⟨Padded.fixpointPrinciple, fun _ h => h, fun _ _ _ => Iff.rfl, ⟨.hid true 0, trivial⟩,
    ⟨fun _ => true, fun a _ => Padded.constClosed a, fun _ => ⟨fun _ => trivial, fun _ => rfl⟩⟩⟩

theorem riceClosure_nonvacuous :
    FixpointPrinciple Padded.sys ∧
      SwitchClosed Padded.sys (fun chk => chk = Padded.litTrueCheck) ∧
      Extensional Padded.sys Padded.BehTrue ∧ NontrivialPred Padded.BehTrue := by
  refine ⟨Padded.fixpointPrinciple, ?_, Padded.behTrue_extensional, Padded.behTrue_nontrivial⟩
  rintro _ rfl; exact Padded.litTrueCheck_switchAdmissible

/-! ## `decidedInside_iff_trivial_of_fixpointPrinciple_constClosed_extensional` -/

theorem riceChar_tight_fixpointPrinciple :
    ConstClosed Tables.sys ∧ Extensional Tables.sys Tables.IsZeroFn ∧
      ¬ (DecidedInside Tables.sys Tables.IsZeroFn ↔
          (∀ c, Tables.IsZeroFn c) ∨ (∀ c, ¬ Tables.IsZeroFn c)) := by
  refine ⟨Tables.constClosed, Tables.isZeroFn_extensional, fun h => ?_⟩
  rcases h.1 Tables.isZeroFn_decidedInside with hall | hnone
  · exact isZeroFn_neg (hall _)
  · exact hnone [] (fun _ => rfl)

/-- Without `ConstClosed`: with no admissible transformers, the fixpoint principle holds
vacuously, the trivial predicate `True` is extensional, but it is not decided inside. -/
theorem riceChar_tight_constClosed :
    FixpointPrinciple emptyAdmSys ∧ Extensional emptyAdmSys (fun _ => True) ∧
      ¬ (DecidedInside emptyAdmSys (fun _ => True) ↔
          (∀ _ : Bool, True) ∨ (∀ _ : Bool, ¬ True)) := by
  refine ⟨fun _ h => h.elim, fun _ _ _ => Iff.rfl, fun h => ?_⟩
  obtain ⟨_, _, hsw⟩ := h.2 (Or.inl fun _ => trivial)
  exact hsw true true

theorem riceChar_tight_extensional :
    FixpointPrinciple Padded.sys ∧ ConstClosed Padded.sys ∧
      ¬ (DecidedInside Padded.sys Padded.EvenPad ↔
          (∀ c, Padded.EvenPad c) ∨ (∀ c, ¬ Padded.EvenPad c)) := by
  refine ⟨Padded.fixpointPrinciple, Padded.constClosed, fun h => ?_⟩
  rcases h.1 decidedInside_pos_padded with hall | hnone
  · exact evenPad_neg (hall _)
  · exact hnone (.hid false 2) rfl

/-- Non-vacuity, exercising both sides of the equivalence in the padded system: the trivial
predicate `True` is decided inside and is trivial; the nontrivial predicate `BehTrue` is not
decided inside and is not trivial. -/
theorem riceChar_nonvacuous :
    FixpointPrinciple Padded.sys ∧ ConstClosed Padded.sys ∧
      (Extensional Padded.sys (fun _ => True) ∧ DecidedInside Padded.sys (fun _ => True) ∧
        ((∀ _ : Padded.Code, True) ∨ (∀ _ : Padded.Code, ¬ True))) ∧
      (Extensional Padded.sys Padded.BehTrue ∧ ¬ DecidedInside Padded.sys Padded.BehTrue ∧
        ¬ ((∀ c, Padded.BehTrue c) ∨ (∀ c, ¬ Padded.BehTrue c))) := by
  refine ⟨Padded.fixpointPrinciple, Padded.constClosed,
    ⟨fun _ _ _ => Iff.rfl, ⟨fun _ => true, fun _ => ⟨fun _ => trivial, fun _ => rfl⟩,
      fun a _ => Padded.constClosed a⟩, Or.inl fun _ => trivial⟩,
    ⟨Padded.behTrue_extensional, Padded.behTrue_not_decidedInside, ?_⟩⟩
  rintro (h | h)
  · exact behTrue_neg (h _)
  · exact h (.hid true 7) rfl

/-! ## `sem_constant_of_fixpointPrinciple_allSwitchesAdmissible` and
`fixpointPrinciple_allAdm_iff_sem_constant_of_nonempty` -/

/-- Without the fixpoint principle: in `allAdm id` on `Bool` every switch is admissible and the
semantics is not constant. -/
theorem semConst_tight_fixpointPrinciple :
    (∀ chk : Bool → Bool, SwitchAdmissible (allAdm (id : Bool → Bool)) chk) ∧
      ¬ ∀ c d : Bool, (allAdm (id : Bool → Bool)).sem c = (allAdm (id : Bool → Bool)).sem d :=
  ⟨fun _ _ _ => trivial, fun h => Bool.noConfusion (h true false)⟩

/-- Without all switches admissible: the flat-domain system has the fixpoint principle and a
nonconstant semantics. -/
theorem semConst_tight_allSwitches :
    FixpointPrinciple Flat.sys ∧ ¬ ∀ c d : Flat.Flat, Flat.sys.sem c = Flat.sys.sem d :=
  ⟨Flat.fixpointPrinciple, fun h => Flat.Flat.noConfusion (h Flat.Flat.tt Flat.Flat.ff)⟩

theorem semConst_nonvacuous :
    FixpointPrinciple (allAdm (fun _ : Bool => ())) ∧
      ∀ chk : Bool → Bool, SwitchAdmissible (allAdm (fun _ : Bool => ())) chk :=
  ⟨fun _ _ => ⟨true, rfl⟩, fun _ _ _ => trivial⟩

/-- The unique map out of the empty type. -/
def emptySem (e : Empty) : Unit := nomatch e

/-- With an empty code type the equivalence fails: the semantics is vacuously constant, but the
fixpoint principle fails (the identity is admissible and there is no code). -/
theorem allAdm_tight_nonempty :
    ¬ (FixpointPrinciple (allAdm emptySem) ↔ ∀ c d : Empty, emptySem c = emptySem d) := by
  intro h
  obtain ⟨c, _⟩ := h.2 (fun c _ => nomatch c) id trivial
  exact nomatch c

/-- Non-vacuity, exercising both sides of the equivalence: a constant semantics on `Bool`
(fixpoint principle holds) and the identity semantics on `Bool` (it fails). -/
theorem allAdm_nonvacuous :
    Nonempty Bool ∧ FixpointPrinciple (allAdm (fun _ : Bool => ())) ∧
      ¬ FixpointPrinciple (allAdm (id : Bool → Bool)) := by
  refine ⟨⟨true⟩, fun _ _ => ⟨true, rfl⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h not trivial
  exact Models.not_has_no_fixpoint c hc

/-! ## `rejectAll_sound_switchAdmissible_of_constClosed` -/

theorem rejectAll_tight_constClosed :
    ¬ (SoundFor (fun _ : Bool => false) (fun _ : Bool => True) ∧
        SwitchAdmissible emptyAdmSys (fun _ => false)) :=
  fun ⟨_, h⟩ => h true true

theorem rejectAll_nonvacuous : ConstClosed Padded.sys ∧ FixpointPrinciple Padded.sys :=
  ⟨Padded.constClosed, Padded.fixpointPrinciple⟩

/-! ## `exists_satisfying_rejected_of_fixpointPrinciple_extensional_nontrivial_sound_switchAdmissible` -/

/-- Without the fixpoint principle: `zeroCheck` is sound, switch-admissible, and rejects no
zero-function table. Also the positive control. -/
theorem incomplete_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ NontrivialPred Tables.IsZeroFn ∧
      SoundFor Tables.zeroCheck Tables.IsZeroFn ∧ SwitchAdmissible Tables.sys Tables.zeroCheck ∧
      ¬ ∃ c, Tables.IsZeroFn c ∧ Tables.zeroCheck c = false := by
  refine ⟨Tables.isZeroFn_extensional, Tables.isZeroFn_nontrivial,
    fun c h => (Tables.zeroCheck_decides c).1 h, Tables.zeroCheck_switchAdmissible, ?_⟩
  rintro ⟨c, hc, hr⟩
  rw [(Tables.zeroCheck_decides c).2 hc] at hr
  exact Bool.noConfusion hr

theorem incomplete_tight_extensional :
    FixpointPrinciple Padded.sys ∧ NontrivialPred Padded.EvenPad ∧
      SoundFor Padded.evenPadCheck Padded.EvenPad ∧
      SwitchAdmissible Padded.sys Padded.evenPadCheck ∧
      ¬ ∃ c, Padded.EvenPad c ∧ Padded.evenPadCheck c = false := by
  refine ⟨Padded.fixpointPrinciple, Padded.evenPad_nontrivial,
    fun c h => (Padded.evenPadCheck_decides c).1 h, Padded.evenPadCheck_switchAdmissible, ?_⟩
  rintro ⟨c, hc, hr⟩
  rw [(Padded.evenPadCheck_decides c).2 hc] at hr
  exact Bool.noConfusion hr

theorem incomplete_tight_nontrivial_hasMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => False) ∧
      (∃ _ : Padded.Code, ¬ False) ∧
      SoundFor (fun _ : Padded.Code => false) (fun _ => False) ∧
      SwitchAdmissible Padded.sys (fun _ => false) ∧
      ¬ ∃ c : Padded.Code, False ∧ (fun _ : Padded.Code => false) c = false :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, ⟨.hid true 0, id⟩,
    fun _ h => Bool.noConfusion h, fun _ b => Padded.constClosed b, fun ⟨_, h, _⟩ => h⟩

theorem incomplete_tight_nontrivial_hasNonMember :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      (∃ _ : Padded.Code, True) ∧ SoundFor (fun _ : Padded.Code => true) (fun _ => True) ∧
      SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∃ c : Padded.Code, True ∧ (fun _ : Padded.Code => true) c = false :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, ⟨.hid true 0, trivial⟩,
    fun _ _ => trivial, fun a _ => Padded.constClosed a, fun ⟨_, _, h⟩ => Bool.noConfusion h⟩

/-- Without soundness: the accept-all checker never rejects. -/
theorem incomplete_tight_sound :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue ∧ SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∃ c, Padded.BehTrue c ∧ (fun _ : Padded.Code => true) c = false :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.behTrue_nontrivial,
    fun a _ => Padded.constClosed a, fun ⟨_, _, h⟩ => Bool.noConfusion h⟩

/-- Without switch-admissibility: the behaviour-reading checker is sound and complete. -/
theorem incomplete_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue ∧ SoundFor Padded.Code.beh Padded.BehTrue ∧
      ¬ ∃ c, Padded.BehTrue c ∧ Padded.Code.beh c = false := by
  refine ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.behTrue_nontrivial,
    fun _ h => h, ?_⟩
  rintro ⟨c, hc, hr⟩
  change c.beh = true at hc
  rw [hc] at hr
  exact Bool.noConfusion hr

theorem incomplete_nonvacuous :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      NontrivialPred Padded.BehTrue ∧ SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.behTrue_nontrivial,
    Padded.litTrueCheck_sound, Padded.litTrueCheck_switchAdmissible⟩

/-! ## `exists_sameSem_accepted_rejected_of_fixpointPrinciple_switchAdmissible` -/

/-- Without the fixpoint principle: `zeroCheck` accepts and rejects something but never splits
a behaviour. Also the positive control. -/
theorem split_tight_fixpointPrinciple :
    SwitchAdmissible Tables.sys Tables.zeroCheck ∧ (∃ c, Tables.zeroCheck c = true) ∧
      (∃ d, Tables.zeroCheck d = false) ∧
      ¬ ∃ c d, Tables.sys.sem c = Tables.sys.sem d ∧ Tables.zeroCheck c = true ∧
          Tables.zeroCheck d = false := by
  refine ⟨Tables.zeroCheck_switchAdmissible, ⟨[], by decide⟩, ⟨[(0, 1)], by decide⟩, ?_⟩
  rintro ⟨c, d, hcd, hc, hd⟩
  have hzc := (Tables.zeroCheck_decides c).1 hc
  have hzd := (Tables.isZeroFn_extensional c d hcd).1 hzc
  rw [(Tables.zeroCheck_decides d).2 hzd] at hd
  exact Bool.noConfusion hd

/-- Without switch-admissibility: the behaviour-reading checker accepts and rejects but never
splits a behaviour. -/
theorem split_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ (∃ c, Padded.Code.beh c = true) ∧
      (∃ d, Padded.Code.beh d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.Code.beh c = true ∧
          Padded.Code.beh d = false := by
  refine ⟨Padded.fixpointPrinciple, ⟨.hid true 0, rfl⟩, ⟨.hid false 0, rfl⟩, ?_⟩
  rintro ⟨c, d, hcd, hc, hd⟩
  change c.beh = d.beh at hcd
  rw [hcd, hd] at hc
  exact Bool.noConfusion hc

theorem split_tight_accepts :
    FixpointPrinciple Padded.sys ∧ SwitchAdmissible Padded.sys (fun _ => false) ∧
      (∃ d : Padded.Code, (fun _ : Padded.Code => false) d = false) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧
          (fun _ : Padded.Code => false) c = true ∧ (fun _ : Padded.Code => false) d = false :=
  ⟨Padded.fixpointPrinciple, fun _ b => Padded.constClosed b, ⟨.hid true 0, rfl⟩,
    fun ⟨_, _, _, h, _⟩ => Bool.noConfusion h⟩

theorem split_tight_rejects :
    FixpointPrinciple Padded.sys ∧ SwitchAdmissible Padded.sys (fun _ => true) ∧
      (∃ c : Padded.Code, (fun _ : Padded.Code => true) c = true) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧
          (fun _ : Padded.Code => true) c = true ∧ (fun _ : Padded.Code => true) d = false :=
  ⟨Padded.fixpointPrinciple, fun a _ => Padded.constClosed a, ⟨.hid true 0, rfl⟩,
    fun ⟨_, _, _, _, h⟩ => Bool.noConfusion h⟩

theorem split_nonvacuous :
    FixpointPrinciple Padded.sys ∧ SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) :=
  ⟨Padded.fixpointPrinciple, Padded.litTrueCheck_switchAdmissible, ⟨.lit true 0, rfl⟩,
    ⟨.hid true 0, rfl⟩⟩

/-! ## `exists_sameSem_satisfying_accepted_rejected_of_fixpointPrinciple_extensional_sound_switchAdmissible` -/

/-- Without the fixpoint principle: `zeroCheck` is sound for `IsZeroFn`, accepts and rejects,
but never splits a behaviour. -/
theorem soundSplit_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ SoundFor Tables.zeroCheck Tables.IsZeroFn ∧
      SwitchAdmissible Tables.sys Tables.zeroCheck ∧ (∃ c, Tables.zeroCheck c = true) ∧
      (∃ d, Tables.zeroCheck d = false) ∧
      ¬ ∃ c d, Tables.sys.sem c = Tables.sys.sem d ∧ Tables.IsZeroFn c ∧ Tables.IsZeroFn d ∧
          Tables.zeroCheck c = true ∧ Tables.zeroCheck d = false := by
  obtain ⟨_, hacc, hrej, hno⟩ := split_tight_fixpointPrinciple
  refine ⟨Tables.isZeroFn_extensional, fun c h => (Tables.zeroCheck_decides c).1 h,
    Tables.zeroCheck_switchAdmissible, hacc, hrej, ?_⟩
  rintro ⟨c, d, hcd, _, _, hc, hd⟩
  exact hno ⟨c, d, hcd, hc, hd⟩

/-- Without extensionality: `litTrueCheck` is sound for the non-extensional predicate "is a
literal `true` program", and no rejected code satisfies that predicate. -/
theorem soundSplit_tight_extensional :
    FixpointPrinciple Padded.sys ∧
      SoundFor Padded.litTrueCheck (fun c => Padded.litTrueCheck c = true) ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.litTrueCheck c = true ∧
          Padded.litTrueCheck d = true ∧ Padded.litTrueCheck c = true ∧
          Padded.litTrueCheck d = false := by
  refine ⟨Padded.fixpointPrinciple, fun _ h => h, Padded.litTrueCheck_switchAdmissible,
    ⟨.lit true 0, rfl⟩, ⟨.hid true 0, rfl⟩, ?_⟩
  rintro ⟨_, _, _, _, h1, _, h2⟩
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- Without soundness: `litTrueCheck` is not sound for `False`, and the conclusion (which
asserts `False` of an accepted code) fails. -/
theorem soundSplit_tight_sound :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => False) ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ False ∧ False ∧
          Padded.litTrueCheck c = true ∧ Padded.litTrueCheck d = false :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, Padded.litTrueCheck_switchAdmissible,
    ⟨.lit true 0, rfl⟩, ⟨.hid true 0, rfl⟩, fun ⟨_, _, _, h, _⟩ => h⟩

/-- Without switch-admissibility: the behaviour-reading checker is sound for `BehTrue`, accepts
and rejects, but never splits a behaviour. -/
theorem soundSplit_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor Padded.Code.beh Padded.BehTrue ∧
      (∃ c, Padded.Code.beh c = true) ∧ (∃ d, Padded.Code.beh d = false) ∧
      ¬ ∃ c d, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.BehTrue c ∧ Padded.BehTrue d ∧
          Padded.Code.beh c = true ∧ Padded.Code.beh d = false := by
  obtain ⟨_, hacc, hrej, hno⟩ := split_tight_switchAdmissible
  refine ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, fun _ h => h, hacc, hrej, ?_⟩
  rintro ⟨c, d, hcd, _, _, hc, hd⟩
  exact hno ⟨c, d, hcd, hc, hd⟩

theorem soundSplit_tight_accepts :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor (fun _ : Padded.Code => false) Padded.BehTrue ∧
      SwitchAdmissible Padded.sys (fun _ => false) ∧
      (∃ d : Padded.Code, (fun _ : Padded.Code => false) d = false) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧ Padded.BehTrue c ∧
          Padded.BehTrue d ∧ (fun _ : Padded.Code => false) c = true ∧
          (fun _ : Padded.Code => false) d = false :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, fun _ h => Bool.noConfusion h,
    fun _ b => Padded.constClosed b, ⟨.hid true 0, rfl⟩,
    fun ⟨_, _, _, _, _, h, _⟩ => Bool.noConfusion h⟩

/-- Without "rejects some code": the accept-all checker is sound for `True`. -/
theorem soundSplit_tight_rejects :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      SoundFor (fun _ : Padded.Code => true) (fun _ => True) ∧
      SwitchAdmissible Padded.sys (fun _ => true) ∧
      (∃ c : Padded.Code, (fun _ : Padded.Code => true) c = true) ∧
      ¬ ∃ c d : Padded.Code, Padded.sys.sem c = Padded.sys.sem d ∧ True ∧ True ∧
          (fun _ : Padded.Code => true) c = true ∧ (fun _ : Padded.Code => true) d = false :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, fun _ _ => trivial,
    fun a _ => Padded.constClosed a, ⟨.hid true 0, rfl⟩,
    fun ⟨_, _, _, _, _, _, h⟩ => Bool.noConfusion h⟩

theorem soundSplit_nonvacuous :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      (∃ c, Padded.litTrueCheck c = true) ∧ (∃ d, Padded.litTrueCheck d = false) :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, Padded.litTrueCheck_sound,
    Padded.litTrueCheck_switchAdmissible, ⟨.lit true 0, rfl⟩, ⟨.hid true 0, rfl⟩⟩

/-! ## `nonempty_subsingleton_of_weaklyPointSurjective` -/

/-- Without weak point-surjectivity: `phiConst` represents only the constant maps, and `Bool`
does not have exactly one element. Also the positive control. -/
theorem cantor_tight_surjective :
    ¬ (∀ g : Bool → Bool, ∃ a, ∀ x, Models.phiConst a x = g x) ∧
      ¬ (Nonempty Bool ∧ ∀ y y' : Bool, y = y') := by
  refine ⟨fun h => ?_, fun ⟨_, h⟩ => Bool.noConfusion (h true false)⟩
  obtain ⟨a, ha⟩ := h not
  have h1 := ha true
  have h2 := ha false
  simp [Models.phiConst] at h1 h2
  rw [h2] at h1
  exact Bool.noConfusion h1

/-- Non-vacuity: with `Y = Unit`, the map `fun _ _ => ()` on `A = Unit` is weakly
point-surjective. (By the theorem, any instance has `Y` a singleton.) -/
theorem cantor_nonvacuous : ∀ g : Unit → Unit, ∃ a : Unit, ∀ x, (fun _ _ => ()) a x = g x :=
  fun _ => ⟨(), fun _ => rfl⟩

/-! ## `forall_exists_sameSem_rejected_of_fixpointPrinciple_extensional_violated_sound_switchAdmissible` -/

/-- Checker used below: accept codes whose behaviour bit or tag is set. -/
def tagOr (c : Bool × Bool) : Bool := c.1 || c.2

/-- A system on codes `(b, t)` (behaviour bit, tag) whose admissible transformers are exactly the
switches on `tagOr`. -/
def twinAdm (f : Bool × Bool → Bool × Bool) : Prop := ∃ a b, f = switch tagOr a b

/-- The twin system. -/
abbrev twinSys : System := ⟨Bool × Bool, Bool, Prod.fst, twinAdm⟩

theorem twin_fixpointPrinciple : FixpointPrinciple twinSys := by
  rintro f ⟨⟨a1, a2⟩, ⟨b1, b2⟩, rfl⟩
  cases a1 with
  | true => exact ⟨(true, false), rfl⟩
  | false =>
    cases b1 with
    | false => exact ⟨(false, false), rfl⟩
    | true => exact ⟨(false, true), rfl⟩

theorem twin_tagOr_switchAdmissible : SwitchAdmissible twinSys tagOr :=
  fun a b => ⟨a, b, rfl⟩

theorem twin_tagOr_not_extensional : ¬ Extensional twinSys (fun c => tagOr c = true) := by
  intro h
  have := (h (false, true) (false, false) rfl).1 rfl
  exact Bool.noConfusion this

/-- Without the fixpoint principle (lookup tables): `zeroCheck` is sound for `IsZeroFn`, some
table violates it, and every table with the behaviour of `[]` is accepted. Also the positive
control. -/
theorem incompleteAll_tight_fixpointPrinciple :
    Extensional Tables.sys Tables.IsZeroFn ∧ (∃ b, ¬ Tables.IsZeroFn b) ∧
      SoundFor Tables.zeroCheck Tables.IsZeroFn ∧ SwitchAdmissible Tables.sys Tables.zeroCheck ∧
      ¬ ∀ a, ∃ c, Tables.sys.sem c = Tables.sys.sem a ∧ Tables.zeroCheck c = false := by
  refine ⟨Tables.isZeroFn_extensional, ⟨[(0, 1)], isZeroFn_neg⟩,
    fun c h => (Tables.zeroCheck_decides c).1 h, Tables.zeroCheck_switchAdmissible, fun h => ?_⟩
  obtain ⟨c, hc, hr⟩ := h []
  have hz : Tables.IsZeroFn c := (Tables.isZeroFn_extensional [] c hc.symm).1 (fun _ => rfl)
  rw [(Tables.zeroCheck_decides c).2 hz] at hr
  exact Bool.noConfusion hr

/-- Without extensionality (twin system): `tagOr` is sound for the non-extensional predicate
"`tagOr` accepts", some code violates it, `tagOr` is switch-admissible, and every code with
behaviour `true` is accepted. -/
theorem incompleteAll_tight_extensional :
    FixpointPrinciple twinSys ∧ (∃ b, ¬ tagOr b = true) ∧
      SoundFor tagOr (fun c => tagOr c = true) ∧ SwitchAdmissible twinSys tagOr ∧
      ¬ ∀ a, ∃ c, twinSys.sem c = twinSys.sem a ∧ tagOr c = false := by
  refine ⟨twin_fixpointPrinciple, ⟨(false, false), fun h => Bool.noConfusion h⟩, fun _ h => h,
    twin_tagOr_switchAdmissible, fun h => ?_⟩
  obtain ⟨⟨c1, c2⟩, hc, hr⟩ := h (true, false)
  change c1 = true at hc
  subst hc
  exact Bool.noConfusion hr

/-- Without "some code violates `P`" (here `P = True`): the accept-all checker is sound and
rejects nothing. -/
theorem incompleteAll_tight_violated :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys (fun _ => True) ∧
      SoundFor (fun _ : Padded.Code => true) (fun _ => True) ∧
      SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧
          (fun _ : Padded.Code => true) c = false :=
  ⟨Padded.fixpointPrinciple, fun _ _ _ => Iff.rfl, fun _ _ => trivial,
    fun a _ => Padded.constClosed a, fun h => by
      obtain ⟨_, _, hr⟩ := h (.hid true 0)
      exact Bool.noConfusion hr⟩

/-- Without soundness: the accept-all checker is switch-admissible and rejects nothing. -/
theorem incompleteAll_tight_sound :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SwitchAdmissible Padded.sys (fun _ => true) ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧
          (fun _ : Padded.Code => true) c = false :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, ⟨.hid false 0, behTrue_neg⟩,
    fun a _ => Padded.constClosed a, fun h => by
      obtain ⟨_, _, hr⟩ := h (.hid true 0)
      exact Bool.noConfusion hr⟩

/-- Without switch-admissibility: the behaviour-reading checker is sound for `BehTrue` and
accepts every code of behaviour `true`. -/
theorem incompleteAll_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.Code.beh Padded.BehTrue ∧
      ¬ ∀ a : Padded.Code, ∃ c, Padded.sys.sem c = Padded.sys.sem a ∧ Padded.Code.beh c = false :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, ⟨.hid false 0, behTrue_neg⟩,
    fun _ h => h, fun h => by
      obtain ⟨c, hc, hr⟩ := h (.hid true 0)
      change c.beh = true at hc
      rw [hc] at hr
      exact Bool.noConfusion hr⟩

/-- All hypotheses hold (padded system, `BehTrue`, `litTrueCheck`). -/
theorem incompleteAll_nonvacuous :
    FixpointPrinciple Padded.sys ∧ Extensional Padded.sys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible Padded.sys Padded.litTrueCheck :=
  ⟨Padded.fixpointPrinciple, Padded.behTrue_extensional, ⟨.hid false 0, behTrue_neg⟩,
    Padded.litTrueCheck_sound, Padded.litTrueCheck_switchAdmissible⟩

/-! ## `exists_sameSem_rejected_or_exists_sameSem_accepted_of_fixpointPrinciple_switchAdmissible` -/

/-- Without the fixpoint principle (lookup tables): `zeroCheck` accepts every table with the
behaviour of `[]` and rejects every table with the behaviour of `[(0, 1)]`. Also the positive
control. -/
theorem splitAll_tight_fixpointPrinciple :
    SwitchAdmissible Tables.sys Tables.zeroCheck ∧
      ¬ ∀ a b, (∃ c, Tables.sys.sem c = Tables.sys.sem a ∧ Tables.zeroCheck c = false) ∨
          (∃ c, Tables.sys.sem c = Tables.sys.sem b ∧ Tables.zeroCheck c = true) := by
  refine ⟨Tables.zeroCheck_switchAdmissible, fun h => ?_⟩
  rcases h [] [(0, 1)] with ⟨c, hc, hr⟩ | ⟨c, hc, ha⟩
  · have hz : Tables.IsZeroFn c := (Tables.isZeroFn_extensional [] c hc.symm).1 (fun _ => rfl)
    rw [(Tables.zeroCheck_decides c).2 hz] at hr
    exact Bool.noConfusion hr
  · have hz : Tables.IsZeroFn c := (Tables.zeroCheck_decides c).1 ha
    exact isZeroFn_neg ((Tables.isZeroFn_extensional c [(0, 1)] hc).1 hz)

/-- Without switch-admissibility: the behaviour-reading checker accepts all codes of behaviour
`true` and rejects all codes of behaviour `false`. -/
theorem splitAll_tight_switchAdmissible :
    FixpointPrinciple Padded.sys ∧
      ¬ ∀ a b, (∃ c, Padded.sys.sem c = Padded.sys.sem a ∧ Padded.Code.beh c = false) ∨
          (∃ c, Padded.sys.sem c = Padded.sys.sem b ∧ Padded.Code.beh c = true) := by
  refine ⟨Padded.fixpointPrinciple, fun h => ?_⟩
  rcases h (.hid true 0) (.hid false 0) with ⟨c, hc, hr⟩ | ⟨c, hc, ha⟩
  · change c.beh = true at hc
    rw [hc] at hr
    exact Bool.noConfusion hr
  · change c.beh = false at hc
    rw [hc] at ha
    exact Bool.noConfusion ha

/-- All hypotheses hold, with a checker that takes both verdicts (padded system,
`litTrueCheck`). -/
theorem splitAll_nonvacuous :
    FixpointPrinciple Padded.sys ∧ SwitchAdmissible Padded.sys Padded.litTrueCheck ∧
      Padded.litTrueCheck (.lit true 0) = true ∧ Padded.litTrueCheck (.hid true 0) = false :=
  ⟨Padded.fixpointPrinciple, Padded.litTrueCheck_switchAdmissible, rfl, rfl⟩

/-! ## `not_decidedInside_restrict_of_fixpointPrinciple_eqTestClosed_extensionalFragment_extensional_nontrivial` -/

/-- Without the fixpoint principle: in `allAdm id` on `Bool` (all transformers admissible, so
closed under code-equality tests), with the whole code type as fragment, "is `true`" is decided
inside the restriction. -/
theorem restrict_tight_fixpointPrinciple :
    EqTestClosed (allAdm (id : Bool → Bool)) ∧
      Extensional (allAdm (id : Bool → Bool)) (fun _ => True) ∧
      Extensional ((allAdm (id : Bool → Bool)).restrict (fun _ => True)) (fun x => x.val = true) ∧
      NontrivialPred (fun x : Subtype (fun _ : Bool => True) => x.val = true) ∧
      DecidedInside ((allAdm (id : Bool → Bool)).restrict (fun _ => True)) (fun x => x.val = true) :=
  ⟨fun _ _ _ _ _ => trivial, fun _ _ _ => Iff.rfl,
    fun c d h => by
      show c.val = true ↔ d.val = true
      have h' : c.val = d.val := h
      rw [h'],
    ⟨⟨⟨true, trivial⟩, rfl⟩, ⟨⟨false, trivial⟩, fun h => Bool.noConfusion h⟩⟩,
    decidedInside_restrict_of_switchAdmissible (S := allAdm (id : Bool → Bool)) (chk := id)
      (fun _ _ => trivial) (fun _ _ => Iff.rfl)⟩

/-- Without closure under code-equality tests (lifted lookup tables): the halting fragment is
closed under same behaviour and "halts and computes the zero function" is decided inside the
restriction. Also the positive control. -/
theorem restrict_tight_eqTestClosed :
    FixpointPrinciple Lifted.sys ∧ Extensional Lifted.sys Lifted.Halts ∧
      Extensional Lifted.totalSys (fun x => Lifted.HaltsZero x.val) ∧
      NontrivialPred (fun x : Lifted.totalSys.Code => Lifted.HaltsZero x.val) ∧
      DecidedInside Lifted.totalSys (fun x => Lifted.HaltsZero x.val) :=
  ⟨Lifted.fixpointPrinciple, Lifted.halts_extensional,
    extensional_restrict Lifted.sys Lifted.haltsZero_extensional,
    Lifted.haltsZero_nontrivial_fragment,
    ⟨Lifted.fragCheck, Lifted.fragCheck_decides, Lifted.fragCheck_switchAdmissible⟩⟩

/-- Without the fragment being closed under same behaviour (padded system, fragment "is a
literal program"): `BehTrue` is decided inside the restriction by `litTrueCheck`. -/
theorem restrict_tight_extensionalFragment :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional (Padded.sys.restrict Padded.IsLit) (fun x => Padded.BehTrue x.val) ∧
      NontrivialPred (fun x : {c // Padded.IsLit c} => Padded.BehTrue x.val) ∧
      DecidedInside (Padded.sys.restrict Padded.IsLit) (fun x => Padded.BehTrue x.val) := by
  refine ⟨Padded.fixpointPrinciple, Padded.eqTestClosed,
    extensional_restrict Padded.sys Padded.behTrue_extensional,
    ⟨⟨⟨.lit true 0, trivial⟩, rfl⟩, ⟨⟨.lit false 0, trivial⟩, fun h => Bool.noConfusion h⟩⟩,
    decidedInside_restrict_of_switchAdmissible Padded.sys Padded.litTrueCheck_switchAdmissible ?_⟩
  intro c hc
  cases c with
  | lit b n => exact Iff.rfl
  | hid b n => exact absurd hc id

/-- Without extensionality of the predicate (padded system, whole code type as fragment):
`EvenPad` is decided inside the restriction. -/
theorem restrict_tight_extensional :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      NontrivialPred (fun x : Subtype (fun _ : Padded.Code => True) => Padded.EvenPad x.val) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun x => Padded.EvenPad x.val) :=
  ⟨Padded.fixpointPrinciple, Padded.eqTestClosed, fun _ _ _ => Iff.rfl,
    ⟨⟨⟨.hid true 0, trivial⟩, rfl⟩, ⟨⟨.hid true 1, trivial⟩, by unfold Padded.EvenPad; decide⟩⟩,
    decidedInside_restrict_of_switchAdmissible Padded.sys Padded.evenPadCheck_switchAdmissible
      (fun c _ => Padded.evenPadCheck_decides c)⟩

/-- Without "some fragment code satisfies `P`" (here `P = False`): decided by a constant. -/
theorem restrict_tight_hasMember :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      Extensional (Padded.sys.restrict (fun _ => True)) (fun _ => False) ∧
      (∃ _ : Subtype (fun _ : Padded.Code => True), ¬ False) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun _ => False) :=
  ⟨Padded.fixpointPrinciple, Padded.eqTestClosed, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    ⟨⟨.hid true 0, trivial⟩, id⟩,
    decidedInside_restrict_of_switchAdmissible Padded.sys (P := fun _ => False) (chk := fun _ => false)
      (fun _ b => Padded.constClosed b) (fun _ _ => ⟨fun h => Bool.noConfusion h, False.elim⟩)⟩

/-- Without "some fragment code violates `P`" (here `P = True`): decided by a constant. -/
theorem restrict_tight_hasNonMember :
    FixpointPrinciple Padded.sys ∧ EqTestClosed Padded.sys ∧
      Extensional Padded.sys (fun _ => True) ∧
      Extensional (Padded.sys.restrict (fun _ => True)) (fun _ => True) ∧
      (∃ _ : Subtype (fun _ : Padded.Code => True), True) ∧
      DecidedInside (Padded.sys.restrict (fun _ => True)) (fun _ => True) :=
  ⟨Padded.fixpointPrinciple, Padded.eqTestClosed, fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl,
    ⟨⟨.hid true 0, trivial⟩, trivial⟩,
    decidedInside_restrict_of_switchAdmissible Padded.sys (P := fun _ => True) (chk := fun _ => true)
      (fun a _ => Padded.constClosed a) (fun _ _ => ⟨fun _ => trivial, fun _ => rfl⟩)⟩

/-- All hypotheses hold with a nontrivial fragment: in the padded system with divergence, the
halting fragment is closed under same behaviour, and "returns `true`" is extensional and
nontrivial on it. -/
theorem restrict_nonvacuous :
    FixpointPrinciple PaddedDiv.sys ∧ EqTestClosed PaddedDiv.sys ∧
      Extensional PaddedDiv.sys PaddedDiv.Halts ∧ NontrivialPred PaddedDiv.Halts ∧
      Extensional (PaddedDiv.sys.restrict PaddedDiv.Halts) (fun x => PaddedDiv.ReturnsTrue x.val) ∧
      NontrivialPred (fun x : {c // PaddedDiv.Halts c} => PaddedDiv.ReturnsTrue x.val) :=
  ⟨PaddedDiv.fixpointPrinciple, PaddedDiv.eqTestClosed, PaddedDiv.halts_extensional,
    ⟨⟨.lit (some true) 0, fun h => by cases h⟩, ⟨.lit none 0, fun h => h rfl⟩⟩,
    extensional_restrict PaddedDiv.sys PaddedDiv.returnsTrue_extensional,
    PaddedDiv.returnsTrue_nontrivial_halting⟩

/-! ## Converse of the abstract Rice theorem -/

/-- Codes and behaviours `ℕ`, identity semantics; admissible: constants and shifts `n ↦ n + k`. -/
abbrev natShiftSys : System :=
  ⟨Nat, Nat, id, fun f => (∃ k, f = fun _ => k) ∨ (∃ k, f = fun n => n + k)⟩

/-- **The converse of the abstract Rice theorem fails, even with constants and composition.**
The system of constants and shifts on `ℕ` is closed under constants and composition, lacks the
fixpoint principle (the shift by one has no fixed point), and yet decides no nontrivial predicate
inside (every predicate is extensional here, since the semantics is the identity). -/
theorem converse_fails_constClosed_compClosed_noFixpoint_nothingNontrivialDecided :
    ConstClosed natShiftSys ∧ CompClosed natShiftSys ∧ ¬ FixpointPrinciple natShiftSys ∧
      (∀ P : Nat → Prop, Extensional natShiftSys P) ∧
      ∀ P : Nat → Prop, NontrivialPred P → ¬ DecidedInside natShiftSys P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact Or.inl ⟨k, rfl⟩
  · rintro f g (⟨kf, rfl⟩ | ⟨kf, rfl⟩) (⟨kg, rfl⟩ | ⟨kg, rfl⟩)
    · exact Or.inl ⟨kf, rfl⟩
    · exact Or.inl ⟨kf, rfl⟩
    · exact Or.inl ⟨kg + kf, rfl⟩
    · exact Or.inr ⟨kg + kf, by funext (n : Nat); exact Nat.add_assoc n kg kf⟩
  · intro hfix
    obtain ⟨c, hc⟩ := hfix (fun n => n + 1) (Or.inr ⟨1, rfl⟩)
    exact Nat.succ_ne_self c hc
  · intro P c d h
    have h' : c = d := h
    subst h'
    exact Iff.rfl
  · rintro P ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨chk, hdec, hsw⟩
    have hca : chk a = true := (hdec a).2 ha
    have hcb : chk b = false := by
      cases h : chk b with
      | false => rfl
      | true => exact absurd ((hdec b).1 h) hb
    rcases hsw 0 1 with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h0 := congrFun hk a
      have h1 := congrFun hk b
      simp [switch, hca, hcb] at h0 h1
      omega
    · have h2 := congrFun hk 2
      simp only [switch] at h2
      cases h2c : chk 2 <;> simp [h2c] at h2 <;> omega

/-! ## Boundary facts used by the non-claims -/

/-- A degenerate form of the failure of the converse: the only admissible transformer is Boolean
negation, so not even constant switches are admissible and nothing at all is decided inside. -/
theorem converse_fails_noFixpoint_nothingDecided :
    ¬ FixpointPrinciple (Models.boolSys (fun f => f = not)) ∧
      ∀ P : Bool → Prop, ¬ DecidedInside (Models.boolSys (fun f => f = not)) P := by
  refine ⟨Models.boolSys_not_fixpointPrinciple_of_not rfl, ?_⟩
  rintro P ⟨chk, _, hsw⟩
  have h := congrFun (hsw true true) true
  change cond (chk true) true true = !true at h
  cases hc : chk true <;> rw [hc] at h <;> exact Bool.noConfusion h

/-- **The fixpoint principle can hold for degenerate reasons.** With no admissible
transformers it holds vacuously, and then nothing at all (not even a trivial predicate) is
decided inside the system. -/
theorem emptyAdm_fixpointPrinciple_nothingDecided :
    FixpointPrinciple emptyAdmSys ∧ ∀ P : Bool → Prop, ¬ DecidedInside emptyAdmSys P :=
  ⟨fun _ h => h.elim, fun _ ⟨_, _, hsw⟩ => hsw true true⟩

/-- A system whose semantics is not surjective: one code, behaving as `true`; behaviours `Bool`;
every transformer admissible. -/
def nonSurjSys : System := ⟨Unit, Bool, fun _ => true, fun _ => True⟩

/-- **The verdict split concerns realizable behaviours only.** In `nonSurjSys` the fixpoint
principle holds and the accept-all checker is switch-admissible, yet the behaviour `true` has all
its codes accepted while the different behaviour `false`, which no code has, has all its (zero)
codes rejected. -/
theorem verdictSplit_unrealizableBehaviour :
    FixpointPrinciple nonSurjSys ∧ SwitchAdmissible nonSurjSys (fun _ => true) ∧
      ∃ b₁ b₂ : nonSurjSys.Beh, b₁ ≠ b₂ ∧
        (∀ c, nonSurjSys.sem c = b₁ → (fun _ : Unit => true) c = true) ∧
        (∀ c, nonSurjSys.sem c = b₂ → (fun _ : Unit => true) c = false) :=
  ⟨fun _ _ => ⟨(), rfl⟩, fun _ _ => trivial, true, false, fun h => Bool.noConfusion h,
    fun _ _ => rfl, fun _ h => Bool.noConfusion h⟩

/-- The padded system with its behaviours embedded in `Option Bool`, so that the behaviour `none`
is the behaviour of no code. -/
def paddedOptSys : System := ⟨Padded.Code, Option Bool, fun c => some c.beh, Padded.Admissible⟩

/-- **Per-behaviour incompleteness concerns realizable behaviours only.** In `paddedOptSys` all
hypotheses of the per-behaviour incompleteness theorem hold for `BehTrue` and `litTrueCheck`, yet
the behaviour `none`, which no code has, contains no rejected code. -/
theorem incompleteAll_unrealizableBehaviour :
    FixpointPrinciple paddedOptSys ∧ Extensional paddedOptSys Padded.BehTrue ∧
      (∃ b, ¬ Padded.BehTrue b) ∧ SoundFor Padded.litTrueCheck Padded.BehTrue ∧
      SwitchAdmissible paddedOptSys Padded.litTrueCheck ∧
      ∃ b : paddedOptSys.Beh, ¬ ∃ c, paddedOptSys.sem c = b ∧ Padded.litTrueCheck c = false := by
  refine ⟨?_, ?_, ⟨.hid false 0, behTrue_neg⟩, Padded.litTrueCheck_sound,
    Padded.litTrueCheck_switchAdmissible, none, fun ⟨_, h, _⟩ => by cases h⟩
  · intro f hf
    obtain ⟨c, hc⟩ := Padded.fixpointPrinciple f hf
    exact ⟨c, congrArg some hc⟩
  · intro c d h
    exact Padded.behTrue_extensional c d (Option.some.inj h)

end Toy.Rice.Controls
