import ToyPin.Unpin

/-!
# Tightness of each condition, with concrete one-field witnesses

All declarations below have one field of a non-`Unpin` type, structurally projected, and
differ from the sound base declaration `dBase` in exactly one choice. Each `_tight` theorem
states, in canonical form, that the declaration satisfies the five other conditions, violates
the named one, that a concrete program is accepted by `SafeProgram` (the remaining
hypothesis of `addrInv_of_structural_pinning_conditions`), and that the conclusion fails
along that program; it also records which invariant fails (`SelfRefOK` or `ListOK`) and that
the other one holds. The witness class is "a one-field declaration and a safe program of at
most six operations". These theorems do not prove that a condition is necessary for every
declaration. All are checked by evaluation (`decide`).
-/

namespace Toy.Pin

/-- The sound base declaration: one non-`Unpin` field, structurally projected; `S` is not
`Unpin`; trivial destructor; not packed. -/
def dBase : Decl := ⟨[false], false, [.projPin 0], [], false⟩

/-- Common prefix: create an `S`, pin it, project its field structurally, and let the field
store its own address. -/
def pinAndInit : List Op := [.new, .pin 0, .projPin 0 0, .initSelf (0, 0)]

/-- Common prefix with the intrusive list instead of the self-reference. -/
def pinAndLink : List Op := [.new, .pin 0, .projPin 0 0, .link (0, 0)]

theorem dBase_satisfies_all :
    UnpinOnlyIfPinnedFieldsUnpin dBase ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase := by decide

/-! ### (a) `S : Unpin` although a structurally pinned field is not -/

def dA : Decl := { dBase with unpin := true }
/-- `Pin::get_mut` on `S` then `mem::replace(&mut *s, S::new())` moves the pinned field. -/
def progA : List Op := pinAndInit ++ [.replaceStruct 0]

/-- **(a) is tight** (one-field witness `dA`, 5-operation program): the other five
conditions hold, the program is safe, and the self-reference invariant fails (the list
invariant holds). -/
theorem unpinOnlyIf_tight :
    ¬ UnpinOnlyIfPinnedFieldsUnpin dA ∧ DtorNoMoveOutOfPinned dA ∧ DropGuaranteeForPinned dA ∧
      NoPinnedTake dA ∧ NotPackedIfPinned dA ∧ ProjectionConsistent dA ∧
      SafeProgram dA State.init progA ∧
      ¬ (∀ s ∈ states State.init (compile dA progA), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dA progA), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dA progA), ListOK s) := by decide

/-! ### (b) the destructor moves out of the pinned field -/

def dB : Decl := { dBase with dtor := [.moveOut 0] }
def progB : List Op := pinAndInit ++ [.drop 0]

/-- **(b) is tight** (one-field witness `dB`, 5-operation program); `SelfRefOK` fails. -/
theorem dtorNoMoveOut_tight :
    UnpinOnlyIfPinnedFieldsUnpin dB ∧ ¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧
      NoPinnedTake dB ∧ NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧
      SafeProgram dB State.init progB ∧
      ¬ (∀ s ∈ states State.init (compile dB progB), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dB progB), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dB progB), ListOK s) := by decide

/-! ### (c) the API or the destructor overwrites the pinned field without dropping it -/

def dC : Decl := { dBase with api := [.projPin 0, .overwrite 0] }
/-- The breakage is visible only through the intrusive list: the self-reference vanishes
together with the overwritten value. -/
def progC : List Op := pinAndLink ++ [.overwrite 0 0]

/-- **(c) is tight, API part** (one-field witness `dC`, 5-operation program): `ListOK` fails
and `SelfRefOK` holds in every visited state. -/
theorem dropGuaranteeForPinned_api_tight :
    UnpinOnlyIfPinnedFieldsUnpin dC ∧ DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧
      NoPinnedTake dC ∧ NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧
      SafeProgram dC State.init progC ∧
      ¬ (∀ s ∈ states State.init (compile dC progC), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dC progC), ¬ ListOK s) ∧
      (∀ s ∈ states State.init (compile dC progC), SelfRefOK s) := by decide

/-- The same violation of (c) by the destructor instead of the API. -/
def dC' : Decl := { dBase with dtor := [.overwrite 0] }
def progC' : List Op := pinAndLink ++ [.drop 0]

/-- **(c) is tight, destructor part** (one-field witness `dC'`, 5-operation program):
`ListOK` fails and `SelfRefOK` holds in every visited state. -/
theorem dropGuaranteeForPinned_dtor_tight :
    UnpinOnlyIfPinnedFieldsUnpin dC' ∧ DtorNoMoveOutOfPinned dC' ∧
      ¬ DropGuaranteeForPinned dC' ∧ NoPinnedTake dC' ∧ NotPackedIfPinned dC' ∧
      ProjectionConsistent dC' ∧ SafeProgram dC' State.init progC' ∧
      ¬ (∀ s ∈ states State.init (compile dC' progC'), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dC' progC'), ¬ ListOK s) ∧
      (∀ s ∈ states State.init (compile dC' progC'), SelfRefOK s) := by decide

/-- With only the self-reference, the overwrite of (c) is not detected: the self-referential
value disappears with its memory. -/
theorem dropGuaranteeForPinned_invisible_to_selfRef :
    SafeProgram dC State.init (pinAndInit ++ [.overwrite 0 0]) ∧
      ∀ s ∈ states State.init (compile dC (pinAndInit ++ [.overwrite 0 0])), AddrInv s := by
  decide

/-! ### (d) a move-out operation on `Pin<&mut S>` -/

def dD : Decl := { dBase with api := [.projPin 0, .take 0] }
def progD : List Op := pinAndInit ++ [.take 0 0]

/-- **(d) is tight** (one-field witness `dD`, 5-operation program); `SelfRefOK` fails. -/
theorem noPinnedTake_tight :
    UnpinOnlyIfPinnedFieldsUnpin dD ∧ DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧
      ¬ NoPinnedTake dD ∧ NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧
      SafeProgram dD State.init progD ∧
      ¬ (∀ s ∈ states State.init (compile dD progD), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dD progD), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dD progD), ListOK s) := by decide

/-! ### (e) `#[repr(packed)]`: the drop glue moves the field to an aligned temporary -/

def dE : Decl := { dBase with packed := true }
def progE : List Op := pinAndInit ++ [.drop 0]

/-- **(e) is tight** (one-field witness `dE`, 5-operation program); `SelfRefOK` fails. -/
theorem notPacked_tight :
    UnpinOnlyIfPinnedFieldsUnpin dE ∧ DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧
      NoPinnedTake dE ∧ ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧
      SafeProgram dE State.init progE ∧
      ¬ (∀ s ∈ states State.init (compile dE progE), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dE progE), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dE progE), ListOK s) := by decide

/-! ### (f): both a structural and a non-structural projection of one field -/

def dF : Decl := { dBase with api := [.projPin 0, .projMut 0] }
/-- A second `S` at address 1 (unpinned); the non-structural projection yields `&mut F` to
the pinned field of the first, and `mem::swap` exchanges the two fields. -/
def progF : List Op := [.new, .new, .pin 0, .projPin 0 0, .initSelf (0, 0), .swapField 0 1 0]

/-- **(f) is tight** (one-field witness `dF`, 6-operation program); `SelfRefOK` fails. -/
theorem projectionConsistent_tight :
    UnpinOnlyIfPinnedFieldsUnpin dF ∧ DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧
      NoPinnedTake dF ∧ NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧
      SafeProgram dF State.init progF ∧
      ¬ (∀ s ∈ states State.init (compile dF progF), AddrInv s) ∧
      (∃ s ∈ states State.init (compile dF progF), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile dF progF), ListOK s) := by decide

/-- **(a), (b), (d), (e), (f) are also tight through the list invariant.** Replacing the
self-reference by a list link in each witness program gives a safe program along which
`ListOK` fails. -/
theorem conditions_abdef_tight_via_list :
    (SafeProgram dA State.init (pinAndLink ++ [.replaceStruct 0]) ∧
      ∃ s ∈ states State.init (compile dA (pinAndLink ++ [.replaceStruct 0])), ¬ ListOK s) ∧
    (SafeProgram dB State.init (pinAndLink ++ [.drop 0]) ∧
      ∃ s ∈ states State.init (compile dB (pinAndLink ++ [.drop 0])), ¬ ListOK s) ∧
    (SafeProgram dD State.init (pinAndLink ++ [.take 0 0]) ∧
      ∃ s ∈ states State.init (compile dD (pinAndLink ++ [.take 0 0])), ¬ ListOK s) ∧
    (SafeProgram dE State.init (pinAndLink ++ [.drop 0]) ∧
      ∃ s ∈ states State.init (compile dE (pinAndLink ++ [.drop 0])), ¬ ListOK s) ∧
    (SafeProgram dF State.init [.new, .new, .pin 0, .projPin 0 0, .link (0, 0), .swapField 0 1 0] ∧
      ∃ s ∈ states State.init
        (compile dF [.new, .new, .pin 0, .projPin 0 0, .link (0, 0), .swapField 0 1 0]),
        ¬ ListOK s) := by decide

/-- **(a)–(e) are not sufficient on their own.** The one-field declaration `dF` satisfies
(a)–(e); the program `progF` is accepted by `SafeProgram dF` and breaks `SelfRefOK`, so not
every safe program keeps `AddrInv`. -/
theorem conditions_a_to_e_insufficient :
    UnpinOnlyIfPinnedFieldsUnpin dF ∧ DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧
      NoPinnedTake dF ∧ NotPackedIfPinned dF ∧
      SafeProgram dF State.init progF ∧
      (∃ s ∈ states State.init (compile dF progF), ¬ SelfRefOK s) ∧
      ¬ SafeProgramsKeepAddrInv dF := by
  obtain ⟨ha, hb, hc, hd, he, -, hsafe, hfail, hself, -⟩ := projectionConsistent_tight
  exact ⟨ha, hb, hc, hd, he, hsafe, hself, fun h => hfail (h progF hsafe)⟩

/-- Positive control for `projectionConsistent_tight`, on one program: with the same
declaration `dF`, the 6-operation program that uses the non-structural `&mut F` only to
*assign* (drop the old value in place, then write — the effect of `Pin::set`) is safe and
keeps both invariants. Only this program is checked. -/
theorem projection_inconsistent_assign_harmless :
    SafeProgram dF State.init (pinAndLink ++ [.initSelf (0, 0), .assignField 0 0]) ∧
      ∀ s ∈ states State.init (compile dF (pinAndLink ++ [.initSelf (0, 0), .assignField 0 0])),
        AddrInv s := by decide

/-- Positive control for `projectionConsistent_tight`, on one declaration: if the field's
type is `Unpin`, offering both projections satisfies all six conditions, so every safe
program keeps `AddrInv` (`addrInv_of_structural_pinning_conditions`). -/
def dFUnpin : Decl := ⟨[true], false, [.projPin 0, .projMut 0], [], false⟩

theorem projection_inconsistent_unpin_field_sound : SafeProgramsKeepAddrInv dFUnpin :=
  fun prog hsafe => addrInv_of_structural_pinning_conditions dFUnpin
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) prog hsafe

/-! ### Instances for the `Unpin` results -/

/-- A declaration where the all-fields rule refuses `Unpin` but the pinned-fields rule
grants it: a non-`Unpin` field projected only non-structurally, and an `Unpin` field
projected structurally. -/
def dConservative : Decl := ⟨[false, true], true, [.projMut 0, .projPin 1], [], false⟩

/-- **The all-fields rule is strictly conservative on `dConservative`.** For `dConservative`
(declared `Unpin`), the all-fields rule says no, the pinned-fields rule says yes, and every
safe program keeps `AddrInv`. -/
theorem autoUnpin_conservative :
    autoUnpin dConservative = false ∧ PinnedFieldsUnpin dConservative ∧
      dConservative.unpin = true ∧ SafeProgramsKeepAddrInv dConservative :=
  ⟨by decide, by decide, rfl,
    (unpin_sound_iff_pinnedFieldsUnpin dConservative rfl).mpr (by decide)⟩

/-- The rule "always `Unpin`" omits the structurally pinned non-`Unpin` field of `dBase` and
is unsound. -/
theorem alwaysUnpin_unsound : ¬ SoundUnpinRule (fun _ => true) :=
  soundUnpinRule_false_of_grants_structural_nonUnpin _ dBase (by decide) (by decide)
    (by decide) (by decide) (by decide) 0 (by decide) rfl rfl

/-- A rule that agrees with `pinnedFieldsRule` except that it grants `Unpin` to every packed
declaration. -/
def rPackedOrPinned (d : Decl) : Bool := d.packed || pinnedFieldsRule d

theorem rPackedOrPinned_sound : SoundUnpinRule rPackedOrPinned := by
  rw [soundUnpinRule_iff]
  intro d _ _ _ he _ hr i hi
  unfold rPackedOrPinned at hr
  cases hp : d.packed with
  | true =>
    cases hty : d.fieldTy i with
    | true => rfl
    | false => exact absurd ⟨hi, hty⟩ (he hp i)
  | false =>
    rw [hp, Bool.false_or] at hr
    exact of_decide_eq_true hr i hi

/-- **Off the (b)–(f) domain, `pinnedFieldsRule` is not the most permissive sound rule.**
`rPackedOrPinned` is sound, grants `Unpin` whenever `pinnedFieldsRule` does, and also grants
it to `dE` (which violates (e) and has a structurally pinned non-`Unpin` field), where
`pinnedFieldsRule` refuses. -/
theorem pinnedFieldsRule_not_greatest_without_b_to_f :
    SoundUnpinRule rPackedOrPinned ∧
      (∀ d, pinnedFieldsRule d = true → rPackedOrPinned d = true) ∧
      DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧ dE.PinnedNonUnpinField 0 ∧
      rPackedOrPinned dE = true ∧ pinnedFieldsRule dE = false :=
  ⟨rPackedOrPinned_sound, fun d h => by simp [rPackedOrPinned, h], by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A declared-`Unpin` struct with a non-`Unpin` field and **no** structural projection: it
satisfies `PinnedFieldsUnpin` vacuously, and every safe program keeps `AddrInv` because no
address-sensitive state can arise (`no_addrState_without_structural_projection`). In this
model the struct itself is never address-sensitive. -/
def dNoProj : Decl := ⟨[false], true, [], [], false⟩

theorem noProjection_unpin_vacuously_sound :
    dNoProj.unpin = true ∧ (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧ dNoProj.fieldTy 0 = false ∧
      PinnedFieldsUnpin dNoProj ∧ SafeProgramsKeepAddrInv dNoProj ∧
      ∀ prog, SafeProgram dNoProj State.init prog →
        ∀ s ∈ states State.init (compile dNoProj prog),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none :=
  by
    have hno : ∀ i, ApiOp.projPin i ∉ dNoProj.api := fun i h => by
      simp [dNoProj] at h
    exact ⟨rfl, hno, rfl, by decide,
      (unpin_sound_iff_pinnedFieldsUnpin dNoProj rfl).mpr (by decide),
      fun prog hsafe => no_addrState_without_structural_projection dNoProj hno prog hsafe⟩

/-! ### Tightness of the remaining hypotheses -/

/-- **The safety hypothesis `hsafe` of `addrInv_of_structural_pinning_conditions` is tight**
(one-field witness `dBase`, 5-operation program): `dBase` satisfies (a)–(f), the program
`progA` (which uses a `&mut S` to a pinned `S` that safe code cannot obtain) is not accepted
by `SafeProgram`, and `AddrInv` fails along it. -/
theorem safeProgram_tight :
    UnpinOnlyIfPinnedFieldsUnpin dBase ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ ¬ SafeProgram dBase State.init progA ∧
      ¬ ∀ s ∈ states State.init (compile dBase progA), AddrInv s := by decide

/-- `dBase` keeps the invariants for all safe programs. -/
theorem dBase_sound : SafeProgramsKeepAddrInv dBase := fun prog hsafe =>
  addrInv_of_structural_pinning_conditions dBase (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) prog hsafe

/-- **The hypothesis `hu : d.unpin = true` of `unpin_sound_iff_pinnedFieldsUnpin` is tight**
(one-field witness `dBase`): `dBase.unpin = false`, and the equivalence fails because all
its safe programs keep the invariants while its structurally pinned field is not `Unpin`. -/
theorem unpin_iff_hu_tight :
    dBase.unpin = false ∧ ¬ (SafeProgramsKeepAddrInv dBase ↔ PinnedFieldsUnpin dBase) ∧
      SafeProgramsKeepAddrInv dBase ∧ ¬ PinnedFieldsUnpin dBase :=
  have hp : ¬ PinnedFieldsUnpin dBase := by decide
  ⟨rfl, fun h => hp (h.mp dBase_sound), dBase_sound, hp⟩

/-- **The hypothesis `hu` of
`unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` is tight** (one-field
witness `dBase`, `i = 0`): the other hypotheses hold and the conclusion fails, because the
witness program is not safe. -/
theorem unpinWitness_hu_tight :
    dBase.unpin = false ∧ ApiOp.projPin 0 ∈ dBase.api ∧ dBase.fieldTy 0 = false ∧
      ¬ (SafeProgram dBase State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dBase (unpinWitness 0)), ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dBase (unpinWitness 0)), ListOK s)) := by decide

/-- The structurally pinned field of `dUnpinField` is `Unpin`. -/
def dUnpinField : Decl := ⟨[true], true, [.projPin 0], [], false⟩

/-- **The hypothesis `hty` of
`unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` is tight** (one-field
witness `dUnpinField`, `i = 0`): the other hypotheses hold, the witness program is safe, and
it keeps both invariants, so the conclusion fails. -/
theorem unpinWitness_fieldTy_tight :
    dUnpinField.unpin = true ∧ ApiOp.projPin 0 ∈ dUnpinField.api ∧
      dUnpinField.fieldTy 0 = true ∧
      SafeProgram dUnpinField State.init (unpinWitness 0) ∧
      (∀ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), AddrInv s) ∧
      ¬ (SafeProgram dUnpinField State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dUnpinField (unpinWitness 0)), ListOK s)) := by
  decide

/-- A declared-`Unpin` struct whose non-`Unpin` field is projected only non-structurally. -/
def dUnpinNonStructural : Decl := ⟨[false], true, [.projMut 0], [], false⟩

/-- **The hypothesis `hproj` of
`unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` is tight** (one-field
witness `dUnpinNonStructural`, `i = 0`): the other hypotheses hold and the conclusion fails
(the witness program is not safe); moreover every safe program keeps `AddrInv` for this
declaration. -/
theorem unpinWitness_projPin_tight :
    dUnpinNonStructural.unpin = true ∧ ApiOp.projPin 0 ∉ dUnpinNonStructural.api ∧
      dUnpinNonStructural.fieldTy 0 = false ∧
      ¬ (SafeProgram dUnpinNonStructural State.init (unpinWitness 0) ∧
        (∃ s ∈ states State.init (compile dUnpinNonStructural (unpinWitness 0)),
          ¬ SelfRefOK s) ∧
        (∀ s ∈ states State.init (compile dUnpinNonStructural (unpinWitness 0)), ListOK s)) ∧
      SafeProgramsKeepAddrInv dUnpinNonStructural :=
  ⟨rfl, by decide, rfl, by decide,
    (unpin_sound_iff_pinnedFieldsUnpin dUnpinNonStructural rfl).mpr (by decide)⟩

/-! ### Tightness of the hypotheses of the rule-level results -/

/-- A rule that agrees with `pinnedFieldsRule` on declarations satisfying (b)–(f) and grants
`Unpin` to every declaration violating one of them. -/
def permissiveRule (d : Decl) : Bool :=
  pinnedFieldsRule d ||
    !decide (DtorNoMoveOutOfPinned d ∧ DropGuaranteeForPinned d ∧ NoPinnedTake d ∧
      NotPackedIfPinned d ∧ ProjectionConsistent d)

theorem permissiveRule_sound : SoundUnpinRule permissiveRule := by
  rw [soundUnpinRule_iff]
  intro d hb hc hd he hf hr
  have hall : DtorNoMoveOutOfPinned d ∧ DropGuaranteeForPinned d ∧ NoPinnedTake d ∧
      NotPackedIfPinned d ∧ ProjectionConsistent d := ⟨hb, hc, hd, he, hf⟩
  unfold permissiveRule at hr
  rw [decide_eq_true hall, Bool.not_true, Bool.or_false] at hr
  exact of_decide_eq_true hr

/-- **Each of (b)–(f) is tight in `pinnedFieldsRule_greatest_under_b_to_f` and in
`soundUnpinRule_false_of_grants_structural_nonUnpin`** (one-field witnesses `dB`, `dC`, `dD`,
`dE`, `dF`, field 0): the rule `permissiveRule` is sound; each witness satisfies the other
four of (b)–(f), violates the named one, has a structurally projected non-`Unpin` field 0, and
is granted `Unpin` by `permissiveRule` but not by `pinnedFieldsRule`. So both conclusions
fail. -/
theorem ruleResults_b_to_f_tight :
    SoundUnpinRule permissiveRule ∧
    (¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧ NoPinnedTake dB ∧
      NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧ ApiOp.projPin 0 ∈ dB.api ∧
      dB.fieldTy 0 = false ∧ permissiveRule dB = true ∧ pinnedFieldsRule dB = false) ∧
    (DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧ NoPinnedTake dC ∧
      NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧ ApiOp.projPin 0 ∈ dC.api ∧
      dC.fieldTy 0 = false ∧ permissiveRule dC = true ∧ pinnedFieldsRule dC = false) ∧
    (DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧ ¬ NoPinnedTake dD ∧
      NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧ ApiOp.projPin 0 ∈ dD.api ∧
      dD.fieldTy 0 = false ∧ permissiveRule dD = true ∧ pinnedFieldsRule dD = false) ∧
    (DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧ ApiOp.projPin 0 ∈ dE.api ∧
      dE.fieldTy 0 = false ∧ permissiveRule dE = true ∧ pinnedFieldsRule dE = false) ∧
    (DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧ NoPinnedTake dF ∧
      NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧ ApiOp.projPin 0 ∈ dF.api ∧
      dF.fieldTy 0 = false ∧ permissiveRule dF = true ∧ pinnedFieldsRule dF = false) :=
  ⟨permissiveRule_sound, by decide, by decide, by decide, by decide, by decide⟩

/-- **The hypothesis `hr` of `pinnedFieldsRule_greatest_under_b_to_f` is tight** (witness: the
rule "always `Unpin`" and `dBase`): the rule is not sound, `dBase` satisfies (b)–(f), the rule
grants it `Unpin`, and `pinnedFieldsRule dBase = false`. -/
theorem pinnedFieldsRule_greatest_hr_tight :
    ¬ SoundUnpinRule (fun _ => true) ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ (fun _ => true : Decl → Bool) dBase = true ∧
      pinnedFieldsRule dBase = false :=
  ⟨alwaysUnpin_unsound, by decide, by decide, by decide, by decide, by decide, rfl, by decide⟩

/-- The rule "never `Unpin`" is sound. -/
theorem neverUnpin_sound : SoundUnpinRule (fun _ => false) :=
  (soundUnpinRule_iff _).mpr fun _ _ _ _ _ _ h => by cases h

/-- **The hypothesis `h : r d = true` of `pinnedFieldsRule_greatest_under_b_to_f` and of
`soundUnpinRule_false_of_grants_structural_nonUnpin` is tight** (witness: the sound rule
"never `Unpin`" and `dBase`, field 0): `dBase` satisfies (b)–(f) and has a structurally
projected non-`Unpin` field, the rule does not grant `Unpin`, `pinnedFieldsRule dBase = false`
and the rule is sound, so both conclusions fail. -/
theorem ruleResults_h_tight :
    SoundUnpinRule (fun _ => false) ∧ DtorNoMoveOutOfPinned dBase ∧
      DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧ NotPackedIfPinned dBase ∧
      ProjectionConsistent dBase ∧ ApiOp.projPin 0 ∈ dBase.api ∧ dBase.fieldTy 0 = false ∧
      (fun _ => false : Decl → Bool) dBase = false ∧ pinnedFieldsRule dBase = false :=
  ⟨neverUnpin_sound, by decide, by decide, by decide, by decide, by decide, by decide, rfl, rfl,
    by decide⟩

/-- **The hypothesis `hproj` of `soundUnpinRule_false_of_grants_structural_nonUnpin` is
tight** (witness: `pinnedFieldsRule`, `dConservative`, field 0): `dConservative` satisfies
(b)–(f), field 0 has a non-`Unpin` type but no structural projection, the rule grants
`Unpin`, and the rule is sound. -/
theorem soundUnpinRule_false_hproj_tight :
    DtorNoMoveOutOfPinned dConservative ∧ DropGuaranteeForPinned dConservative ∧
      NoPinnedTake dConservative ∧ NotPackedIfPinned dConservative ∧
      ProjectionConsistent dConservative ∧ ApiOp.projPin 0 ∉ dConservative.api ∧
      dConservative.fieldTy 0 = false ∧ pinnedFieldsRule dConservative = true ∧
      SoundUnpinRule pinnedFieldsRule :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    pinnedFieldsRule_sound⟩

/-- **The hypothesis `hty` of `soundUnpinRule_false_of_grants_structural_nonUnpin` is tight**
(witness: `pinnedFieldsRule`, `dUnpinField`, field 0): `dUnpinField` satisfies (b)–(f),
field 0 is structurally projected but of `Unpin` type, the rule grants `Unpin`, and the rule
is sound. -/
theorem soundUnpinRule_false_hty_tight :
    DtorNoMoveOutOfPinned dUnpinField ∧ DropGuaranteeForPinned dUnpinField ∧
      NoPinnedTake dUnpinField ∧ NotPackedIfPinned dUnpinField ∧
      ProjectionConsistent dUnpinField ∧ ApiOp.projPin 0 ∈ dUnpinField.api ∧
      dUnpinField.fieldTy 0 = true ∧ pinnedFieldsRule dUnpinField = true ∧
      SoundUnpinRule pinnedFieldsRule :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    pinnedFieldsRule_sound⟩

/-- Non-vacuity of `soundUnpinRule_false_of_grants_structural_nonUnpin`: the rule "always
`Unpin`", `dBase` and field 0 satisfy all its hypotheses. -/
theorem soundUnpinRule_false_nonvacuous :
    DtorNoMoveOutOfPinned dBase ∧ DropGuaranteeForPinned dBase ∧ NoPinnedTake dBase ∧
      NotPackedIfPinned dBase ∧ ProjectionConsistent dBase ∧ ApiOp.projPin 0 ∈ dBase.api ∧
      dBase.fieldTy 0 = false ∧ (fun _ => true : Decl → Bool) dBase = true := by decide

/-- **The hypothesis `h` of `autoUnpin_implies_pinnedFieldsUnpin` is tight** (witness:
`dBase`): `autoUnpin dBase = false` and `PinnedFieldsUnpin dBase` fails. -/
theorem autoUnpin_implies_h_tight :
    autoUnpin dBase = false ∧ ¬ PinnedFieldsUnpin dBase := by decide

end Toy.Pin
