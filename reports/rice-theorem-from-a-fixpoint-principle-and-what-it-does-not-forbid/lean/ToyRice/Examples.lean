/-
# Definition examples

For each core definition: at least one intended instance it admits and at least one it must
reject, all fully proved. Where possible the negative example is a near miss (for instance a
checker that is sound but not complete), so that the example tests something real.
-/
import ToyRice.Tables
import ToyRice.Flat
import ToyRice.Padded
import ToyRice.Models
import ToyRice.Lifted
import ToyRice.PaddedDiv

namespace Toy.Rice.Examples

open Toy.Rice

/-- A system with no admissible transformers at all. -/
abbrev emptyAdmSys : System := ⟨Bool, Bool, id, fun _ => False⟩

/-! ### `FixpointPrinciple` -/

theorem fixpointPrinciple_pos_flat : FixpointPrinciple Flat.sys := Flat.fixpointPrinciple
theorem fixpointPrinciple_pos_padded : FixpointPrinciple Padded.sys := Padded.fixpointPrinciple
theorem fixpointPrinciple_neg_tables : ¬ FixpointPrinciple Tables.sys :=
  Tables.not_fixpointPrinciple
theorem fixpointPrinciple_neg_total : ¬ FixpointPrinciple Lifted.totalSys :=
  Lifted.total_not_fixpointPrinciple

/-! ### `Extensional` -/

theorem extensional_pos : Extensional Padded.sys Padded.BehTrue := Padded.behTrue_extensional
theorem extensional_pos_tables : Extensional Tables.sys Tables.IsZeroFn :=
  Tables.isZeroFn_extensional
theorem extensional_neg : ¬ Extensional Padded.sys Padded.EvenPad :=
  Padded.evenPad_not_extensional
/-- Near miss: "the code is a literal `true` program" is sound for an extensional property but
is itself not extensional. -/
theorem extensional_neg_litTrue :
    ¬ Extensional Padded.sys (fun c => Padded.litTrueCheck c = true) := by
  intro h
  have := (h (.lit true 0) (.hid true 0) rfl).1 rfl
  exact Bool.noConfusion this

/-! ### `NontrivialPred` -/

theorem nontrivialPred_pos : NontrivialPred Flat.Halts := Flat.halts_nontrivial
theorem nontrivialPred_neg_true : ¬ NontrivialPred (fun _ : Bool => True) :=
  fun ⟨_, ⟨_, h⟩⟩ => h trivial
theorem nontrivialPred_neg_false : ¬ NontrivialPred (fun _ : Bool => False) :=
  fun ⟨⟨_, h⟩, _⟩ => h

/-! ### `Decides` -/

theorem decides_pos : Decides Tables.zeroCheck Tables.IsZeroFn := Tables.zeroCheck_decides
/-- Near miss: the syntactic checker `allOutputsZero` is sound for `IsZeroFn` but does not
decide it. -/
theorem decides_neg : ¬ Decides Tables.allOutputsZero Tables.IsZeroFn := fun h =>
  Tables.allOutputsZero_sound_not_complete.2 ((decides_iff_sound_complete _ _).1 h).2

/-! ### `switch` (small cases) -/

example : switch Flat.haltCheck Flat.Flat.tt Flat.Flat.bot Flat.Flat.bot = Flat.Flat.bot := rfl
example : switch Flat.haltCheck Flat.Flat.tt Flat.Flat.bot Flat.Flat.ff = Flat.Flat.tt := rfl
example : switch Flat.haltCheck Flat.Flat.bot Flat.Flat.tt Flat.Flat.bot = Flat.Flat.tt := rfl

/-! ### `SwitchAdmissible` -/

theorem switchAdmissible_pos : SwitchAdmissible Padded.sys Padded.evenPadCheck :=
  Padded.evenPadCheck_switchAdmissible
theorem switchAdmissible_pos_tables : SwitchAdmissible Tables.sys Tables.zeroCheck :=
  Tables.zeroCheck_switchAdmissible
/-- Near miss: `haltCheck` decides halting on the flat domain (it is an honest Boolean
function), but its swapped switch is not monotone, so it is not switch-admissible. -/
theorem switchAdmissible_neg : ¬ SwitchAdmissible Flat.sys Flat.haltCheck :=
  fun h => Flat.swappedSwitch_not_admissible (h _ _)

/-! ### `DecidedInside` -/

theorem decidedInside_pos_tables : DecidedInside Tables.sys Tables.IsZeroFn :=
  Tables.isZeroFn_decidedInside
theorem decidedInside_pos_padded : DecidedInside Padded.sys Padded.EvenPad :=
  ⟨_, Padded.evenPadCheck_decides, Padded.evenPadCheck_switchAdmissible⟩

/-- Direct negative example, not using the abstract Rice theorem: any checker deciding halting
on the flat domain has a non-monotone swapped switch. -/
theorem decidedInside_neg_direct : ¬ DecidedInside Flat.sys Flat.Halts := by
  rintro ⟨chk, hdec, hsw⟩
  have h1 : chk Flat.Flat.bot = false := by
    cases h : chk Flat.Flat.bot with
    | false => rfl
    | true => exact absurd rfl ((hdec _).1 h)
  have h2 : chk Flat.Flat.tt = true := (hdec _).2 (fun h => Flat.Flat.noConfusion h)
  have := hsw Flat.Flat.bot Flat.Flat.tt Flat.Flat.bot Flat.Flat.tt (Or.inl rfl)
  change Flat.le (cond (chk Flat.Flat.bot) Flat.Flat.bot Flat.Flat.tt)
    (cond (chk Flat.Flat.tt) Flat.Flat.bot Flat.Flat.tt) at this
  rw [h1, h2] at this
  rcases this with h | h <;> cases h

/-! ### `SoundFor` and `CompleteFor` -/

theorem soundFor_pos : SoundFor Padded.litTrueCheck Padded.BehTrue := Padded.litTrueCheck_sound
theorem soundFor_neg : ¬ SoundFor (fun _ : Padded.Code => true) Padded.BehTrue :=
  fun h => Bool.noConfusion (h (.hid false 0) rfl)
theorem completeFor_pos : CompleteFor (fun _ : Padded.Code => true) Padded.BehTrue :=
  fun _ _ => rfl
/-- Near miss: `litTrueCheck` is sound but not complete for `BehTrue`. -/
theorem completeFor_neg : ¬ CompleteFor Padded.litTrueCheck Padded.BehTrue :=
  fun h => Bool.noConfusion (h (.hid true 0) rfl)

/-! ### Closure laws -/

theorem constClosed_pos : ConstClosed Padded.sys := Padded.constClosed
theorem constClosed_pos_tables : ConstClosed Tables.sys := Tables.constClosed
theorem constClosed_neg : ¬ ConstClosed emptyAdmSys := fun h => h true
theorem compClosed_pos : CompClosed Padded.sys := Padded.compClosed
theorem compClosed_pos_tables : CompClosed Tables.sys := Tables.compClosed
theorem compClosed_neg : ¬ CompClosed (Models.boolSys Models.adm1) := Models.adm1_not_compClosed
theorem switchClosed_pos :
    SwitchClosed Padded.sys (fun chk => chk = Padded.evenPadCheck) := by
  rintro _ rfl; exact Padded.evenPadCheck_switchAdmissible
theorem switchClosed_neg : ¬ SwitchClosed Padded.sys (fun _ => True) :=
  fun h => Padded.behCheck_not_switchAdmissible (h _ trivial)

theorem eqTestClosed_pos : EqTestClosed Padded.sys := Padded.eqTestClosed
theorem eqTestClosed_pos_div : EqTestClosed PaddedDiv.sys := PaddedDiv.eqTestClosed
theorem eqTestClosed_neg : ¬ EqTestClosed Flat.sys := Flat.not_eqTestClosed
theorem eqTestClosed_neg_lifted : ¬ EqTestClosed Lifted.sys := Lifted.not_eqTestClosed

/-! ### `DecidedBy` -/

/-- With `K` the (nonempty, proper) class of switch-admissible checkers of the padded system,
the syntactic predicate `EvenPad` is decided by a checker in `K`. -/
theorem decidedBy_pos : DecidedBy Padded.sys (SwitchAdmissible Padded.sys) Padded.EvenPad :=
  ⟨Padded.evenPadCheck, Padded.evenPadCheck_switchAdmissible, Padded.evenPadCheck_decides⟩
/-- With the same class, the extensional predicate `BehTrue` is not decided by a checker in `K`,
although the behaviour-reading checker (outside `K`) decides it. -/
theorem decidedBy_neg : ¬ DecidedBy Padded.sys (SwitchAdmissible Padded.sys) Padded.BehTrue ∧
    Decides Padded.Code.beh Padded.BehTrue :=
  ⟨not_decidedBy_of_fixpointPrinciple_switchClosed_extensional_nontrivial
    Padded.fixpointPrinciple (fun _ h => h) Padded.behTrue_extensional Padded.behTrue_nontrivial,
    fun _ => Iff.rfl⟩

/-! ### `System.restrict` -/

/-- Restricting the lifted lookup-table system to its halting fragment loses the fixpoint
principle. -/
theorem restrict_example :
    FixpointPrinciple Lifted.sys ∧ ¬ FixpointPrinciple (Lifted.sys.restrict Lifted.Halts) :=
  ⟨Lifted.fixpointPrinciple, Lifted.total_not_fixpointPrinciple⟩

/-- Positive example: a fragment switch whose strict extension is admissible in the full
system is admissible in the restriction. -/
theorem restrict_adm_pos :
    (Lifted.sys.restrict Lifted.Halts).Adm
      (switch Lifted.fragCheck ⟨some [], rfl⟩ ⟨some [(0, 1)], rfl⟩) :=
  Lifted.fragCheck_switchAdmissible _ _

/-- Negative example: the restriction does not admit every fragment map (the fragment map
induced by `List.tail` agrees with no admissible full-system transformer). -/
theorem restrict_adm_neg :
    ¬ ∀ g : Lifted.totalSys.Code → Lifted.totalSys.Code, (Lifted.sys.restrict Lifted.Halts).Adm g :=
  Lifted.totalSys_adm_proper

/-- Degenerate case, recorded so that it is not mistaken for a meaningful example: the two-element
total fragment of the flat domain admits every map and decides every predicate. -/
theorem restrict_degenerate_flat (P : Flat.totalSys.Code → Prop) :
    (∀ g, Flat.totalSys.Adm g) ∧ DecidedInside Flat.totalSys P :=
  ⟨Flat.totalSys_adm, Flat.totalSys_decides_every_predicate P⟩

/-! ### `Represents` and `IsDiagonal` -/

theorem represents_pos : Represents Models.tagSys Models.tagApp :=
  Models.kleene_nonvacuous.1
theorem represents_neg : ¬ Represents (Models.boolSys Models.adm2) Models.app2 :=
  Models.app2_not_represents
theorem isDiagonal_pos : IsDiagonal Models.tagSys Models.tagApp Models.tagDiag :=
  Models.kleene_nonvacuous.2.1
theorem isDiagonal_neg : ¬ IsDiagonal (Models.boolSys Models.adm3) Models.app3 id :=
  Models.id_not_diagonal_app3
/-- A non-identity diagonal that is not itself admissible, yet precomposition with it preserves
admissibility. -/
theorem precompClosed_pos : PrecompClosed Models.tagSys Models.tagDiag ∧
    ¬ Models.tagSys.Adm Models.tagDiag :=
  ⟨Models.kleene_nonvacuous.2.2.1, Models.kleene_nonvacuous.2.2.2.1⟩
/-- A second positive example: precomposition with the erasure map in the padded system. -/
theorem precompClosed_pos_padded : PrecompClosed Padded.sys Padded.Code.erase :=
  precompClosed_of_compClosed_adm Padded.compClosed (Or.inr ⟨[], id, fun _ _ => rfl⟩)
theorem precompClosed_neg : ¬ PrecompClosed (Models.boolSys Models.adm1) (fun _ => false) :=
  Models.adm1_not_precompClosed

/-! ### Toy-system definitions -/

theorem flat_monotone_pos : Flat.Monotone (switch Flat.haltCheck Flat.Flat.tt Flat.Flat.bot) :=
  Flat.unswappedSwitch_admissible
theorem flat_monotone_neg : ¬ Flat.Monotone (switch Flat.haltCheck Flat.Flat.bot Flat.Flat.tt) :=
  Flat.swappedSwitch_not_admissible

theorem tables_admissible_pos : Tables.Admissible Tables.bump := Tables.bump_admissible
theorem tables_admissible_neg : ¬ Tables.Admissible List.tail := Tables.tail_not_admissible

theorem padded_admissible_pos :
    Padded.Admissible (switch Padded.litTrueCheck (.lit true 0) (.hid false 0)) :=
  Padded.litTrueCheck_switchAdmissible _ _

/-- Flip the behaviour bit, keeping the form and the padding. -/
def flipBeh : Padded.Code → Padded.Code
  | .lit b n => .lit (!b) n
  | .hid b n => .hid (!b) n

/-- Flipping the behaviour bit is not admissible in the padded system. -/
theorem padded_admissible_neg : ¬ Padded.Admissible flipBeh := by
  intro h
  obtain ⟨c, hc⟩ := Padded.fixpointPrinciple _ h
  cases c with
  | lit b n => exact Models.not_has_no_fixpoint b hc
  | hid b n => exact Models.not_has_no_fixpoint b hc

theorem isZeroFn_pos : Tables.IsZeroFn [(0, 0), (0, 5)] := by
  intro n; cases n <;> simp [Tables.eval]
theorem isZeroFn_neg : ¬ Tables.IsZeroFn [(0, 1)] := fun h => by
  have := h 0; simp [Tables.eval] at this

theorem halts_pos : Flat.Halts Flat.Flat.ff := fun h => Flat.Flat.noConfusion h
theorem halts_neg : ¬ Flat.Halts Flat.Flat.bot := fun h => h rfl

theorem evenPad_pos : Padded.EvenPad (.hid false 2) := rfl
theorem evenPad_neg : ¬ Padded.EvenPad (.lit true 3) := by unfold Padded.EvenPad; decide

theorem behTrue_pos : Padded.BehTrue (.hid true 7) := rfl
theorem behTrue_neg : ¬ Padded.BehTrue (.lit false 7) := fun h => Bool.noConfusion h

end Toy.Rice.Examples
