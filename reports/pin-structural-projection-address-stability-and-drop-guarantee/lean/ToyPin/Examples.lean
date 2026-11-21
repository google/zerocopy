import ToyPin.CoreForget

/-!
# Definition examples and non-vacuity witnesses

Positive examples (instances a definition must admit) and negative examples (instances it
must reject) for every core definition, plus the non-vacuity witnesses of the main results.
All are checked by evaluation.
-/

namespace Toy.Pin

open State

/-! ## Primitive semantics -/

/-- `setSelf` has an effect only at a pinned location holding a non-`Unpin` value. -/
theorem setSelf_requires_pinned_nonUnpin :
    -- unpinned: no effect
    runActs State.init [.alloc [some false], .setSelf (0, 0)] =
      runActs State.init [.alloc [some false]] ∧
    -- pinned but `Unpin`: no effect
    runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)] =
      runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)] ∧
    -- pinned and non-`Unpin`: the self-pointer is set
    (runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)]).leafAt
      (0, 0) = some ⟨0, false, some (0, 0)⟩ := by decide

/-- `register` likewise needs a pinned non-`Unpin` value. -/
theorem register_requires_pinned_nonUnpin :
    (runActs State.init [.alloc [some false], .register (0, 0)]).registry = [] ∧
    (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0), .register (0, 0)]).registry = [] ∧
    (runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .register (0, 0)]).registry
      = [((0, 0), 0)] := by decide

/-- A moved value keeps its identity and its (now stale) self-pointer; the destructor unlinks
by the current address only. -/
theorem moveOut_keeps_stale_pointer :
    (runActs State.init coreMoveActs).leafAt (1, 0) = some ⟨0, false, some (0, 0)⟩ ∧
    (runActs State.init coreMoveActs).leafAt (0, 0) = none := by decide

/-! ## `SelfRefOK`, `ListOK`, `AddrInv` -/

def stSelf : State :=
  runActs State.init [.alloc [some false], .pinObj 0, .pinField (0, 0), .setSelf (0, 0)]
def stLinked : State := applyAct stSelf (.register (0, 0))

theorem selfRefOK_pos : SelfRefOK State.init ∧ SelfRefOK stSelf := by decide
theorem selfRefOK_neg : ¬ SelfRefOK (applyAct stSelf (.moveOut (0, 0))) := by decide
theorem listOK_pos : ListOK State.init ∧ ListOK stLinked := by decide
theorem listOK_neg : ¬ ListOK (applyAct stLinked (.write (0, 0) false)) ∧
    ¬ ListOK (applyAct stLinked (.dealloc 0)) ∧ ¬ ListOK (applyAct stLinked (.moveOut (0, 0))) := by
  decide
/-- Dropping in place unlinks the value, so the list invariant survives a proper drop and
the following deallocation. -/
theorem listOK_after_proper_drop :
    ListOK (runActs stLinked [.dropLeaf (0, 0), .dealloc 0]) := by decide
theorem addrInv_pos : AddrInv stLinked := by decide
theorem addrInv_neg : ¬ AddrInv (applyAct stLinked (.moveOut (0, 0))) := by decide

/-! ## `PinnedNonUnpin`, `NoPinnedMove`, `DropGuaranteeAct` -/

theorem pinnedNonUnpin_pos : PinnedNonUnpin stSelf (0, 0) := by decide
theorem pinnedNonUnpin_neg :
    ¬ PinnedNonUnpin (runActs State.init [.alloc [some false]]) (0, 0) ∧
    ¬ PinnedNonUnpin (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)]) (0, 0) ∧
    ¬ PinnedNonUnpin (applyAct stSelf (.dropLeaf (0, 0))) (0, 0) := by decide

theorem noPinnedMove_pos :
    NoPinnedMove (runActs State.init [.alloc [some false]]) (.moveOut (0, 0)) ∧
    NoPinnedMove (runActs State.init [.alloc [some true], .pinObj 0, .pinField (0, 0)])
      (.moveOut (0, 0)) := by decide
theorem noPinnedMove_neg :
    ¬ NoPinnedMove stSelf (.moveOut (0, 0)) ∧ ¬ NoPinnedMove stSelf (.moveObj 0) ∧
    ¬ NoPinnedMove stSelf (.swap (0, 0) (0, 0)) := by decide

theorem dropGuaranteeAct_pos :
    DropGuaranteeAct (applyAct stSelf (.dropLeaf (0, 0))) (.dealloc 0) ∧
    DropGuaranteeAct (applyAct stSelf (.dropLeaf (0, 0))) (.write (0, 0) false) := by decide
/-- `dealloc`, `write` and `freeTemp` of a pinned non-`Unpin` value violate the drop guarantee.
`dropTemp`/`freeTemp` act on the most recently allocated object whatever its origin; in
`stSelf` that is the pinned object itself. -/
theorem dropGuaranteeAct_neg :
    ¬ DropGuaranteeAct stSelf (.dealloc 0) ∧ ¬ DropGuaranteeAct stSelf (.write (0, 0) true) ∧
      ¬ DropGuaranteeAct stSelf .freeTemp ∧ stSelf.heap.length = 1 ∧
      (applyAct stSelf .freeTemp).isLive 0 = false := by
  decide

/-! ## Declarations and the conditions -/

theorem pinnedNonUnpinField_pos : dBase.PinnedNonUnpinField 0 := by decide
theorem pinnedNonUnpinField_neg :
    ¬ dBase.PinnedNonUnpinField 1 ∧ ¬ dFUnpin.PinnedNonUnpinField 0 ∧
    ¬ ({ dBase with api := [.projMut 0] } : Decl).PinnedNonUnpinField 0 := by decide

/-- Each condition holds for `dBase` and fails for the corresponding variant. -/
theorem conditions_pos_neg :
    (UnpinOnlyIfPinnedFieldsUnpin dBase ∧ ¬ UnpinOnlyIfPinnedFieldsUnpin dA) ∧
    (DtorNoMoveOutOfPinned dBase ∧ ¬ DtorNoMoveOutOfPinned dB) ∧
    (DropGuaranteeForPinned dBase ∧ ¬ DropGuaranteeForPinned dC) ∧
    (NoPinnedTake dBase ∧ ¬ NoPinnedTake dD) ∧
    (NotPackedIfPinned dBase ∧ ¬ NotPackedIfPinned dE) ∧
    (ProjectionConsistent dBase ∧ ¬ ProjectionConsistent dF) := by decide

/-- The conditions only constrain structurally pinned non-`Unpin` fields: a declaration whose
only structurally pinned field is `Unpin` satisfies them all, even if packed, `Unpin`, with
a moving destructor, a take, an overwrite and a non-structural projection of that field. -/
def dPermissive : Decl :=
  ⟨[true, false], true, [.projPin 0, .projMut 0, .take 0, .overwrite 0, .projMut 1],
    [.moveOut 0, .overwrite 0, .moveOut 1], true⟩

theorem conditions_vacuous_without_pinned_nonUnpin :
    UnpinOnlyIfPinnedFieldsUnpin dPermissive ∧ DtorNoMoveOutOfPinned dPermissive ∧
    DropGuaranteeForPinned dPermissive ∧ NoPinnedTake dPermissive ∧
    NotPackedIfPinned dPermissive ∧ ProjectionConsistent dPermissive := by decide

/-! ## Safe operations -/

/-- Safe code may move a field out of an unpinned `S`, but not out of a pinned `S` that is not
`Unpin` and offers no non-structural projection; it may not pin twice; it may not drop a
leaked object. -/
theorem safeOp_pos_neg :
    let st1 := runActs State.init (compile dBase [.new])
    let st2 := runActs State.init (compile dBase [.new, .pin 0])
    SafeOp dBase st1 (.replaceField 0 0) ∧ SafeOp dBase st1 (.replaceStruct 0) ∧
    ¬ SafeOp dBase st2 (.replaceField 0 0) ∧ ¬ SafeOp dBase st2 (.replaceStruct 0) ∧
    ¬ SafeOp dBase st2 (.pin 0) ∧ SafeOp dBase st2 (.projPin 0 0) ∧
    ¬ SafeOp dBase st1 (.projPin 0 0) ∧ ¬ SafeOp dBase st2 (.take 0 0) ∧
    SafeOp dD st2 (.take 0 0) := by decide

theorem safeProgram_pos_neg :
    SafeProgram dBase State.init (pinAndInit ++ [.drop 0]) ∧
    ¬ SafeProgram dBase State.init (pinAndInit ++ [.replaceStruct 0]) ∧
    ¬ SafeProgram dBase State.init [.pin 0] := by decide

/-! ## Non-vacuity of the structural-pinning theorem -/

/-- A richer sound declaration: field 0 non-`Unpin` and structurally pinned; field 1
non-`Unpin` and non-structural, with a take, an overwrite, and a destructor that moves it out
and overwrites it; field 2 `Unpin` with both projections. -/
def dRich : Decl :=
  ⟨[false, false, true], false,
    [.projPin 0, .projMut 1, .take 1, .overwrite 1, .projPin 2, .projMut 2],
    [.moveOut 1, .overwrite 1], false⟩

def progRich : List Op :=
  [.new, .new, .pin 0, .projPin 0 0, .projPin 0 2, .initSelf (0, 0), .link (0, 0),
    .replaceField 0 1, .swapField 0 1 1, .take 0 1, .overwrite 0 1, .assignField 0 2,
    .replaceField 0 2, .replaceStruct 1, .pin 1, .projPin 1 0, .link (1, 0), .forget 1,
    .drop 0, .drop 5]

/-- **Non-vacuity of `addrInv_of_structural_pinning_conditions`.** `dRich` satisfies all six
conditions and `progRich` is a safe program for it that establishes a self-reference and two
list entries. -/
theorem structural_nonvacuous :
    UnpinOnlyIfPinnedFieldsUnpin dRich ∧ DtorNoMoveOutOfPinned dRich ∧
    DropGuaranteeForPinned dRich ∧ NoPinnedTake dRich ∧ NotPackedIfPinned dRich ∧
    ProjectionConsistent dRich ∧ SafeProgram dRich State.init progRich ∧
    (runActs State.init (compile dRich (progRich.take 17))).registry.length = 2 := by decide

/-- The conclusion, checked directly on the witness. -/
theorem structural_nonvacuous_conclusion :
    ∀ s ∈ states State.init (compile dRich progRich), AddrInv s := by decide

/-! ## Non-vacuity for the `Unpin` results -/

/-- Hypotheses of `unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field` hold
for `dA`, field 0. -/
theorem unpin_unsound_nonvacuous :
    dA.unpin = true ∧ ApiOp.projPin 0 ∈ dA.api ∧ dA.fieldTy 0 = false := by decide

/-- Hypothesis of `unpin_sound_iff_pinnedFieldsUnpin` holds for a declaration on each side of
the equivalence. -/
theorem unpin_iff_nonvacuous :
    dConservative.unpin = true ∧ PinnedFieldsUnpin dConservative ∧
    dA.unpin = true ∧ ¬ PinnedFieldsUnpin dA := by decide

theorem pinnedFieldsUnpin_pos_neg :
    PinnedFieldsUnpin dConservative ∧ PinnedFieldsUnpin dFUnpin ∧ ¬ PinnedFieldsUnpin dBase := by
  decide

/-- Hypotheses of `pinnedFieldsRule_greatest_under_b_to_f` hold for the sound rule
`pinnedFieldsRule` and the declaration `dConservative`, which it grants `Unpin`. -/
theorem pinnedFieldsRule_greatest_nonvacuous :
    SoundUnpinRule pinnedFieldsRule ∧ DtorNoMoveOutOfPinned dConservative ∧
      DropGuaranteeForPinned dConservative ∧ NoPinnedTake dConservative ∧
      NotPackedIfPinned dConservative ∧ ProjectionConsistent dConservative ∧
      pinnedFieldsRule dConservative = true :=
  ⟨pinnedFieldsRule_sound, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **A declaration to which the all-fields rule grants `Unpin`**: `dUnpinField` satisfies
(b)–(f), `autoUnpin dUnpinField = true`, and with `unpin := autoUnpin dUnpinField` every safe
program keeps `AddrInv`. -/
theorem autoUnpin_true_witness :
    autoUnpin dUnpinField = true ∧ DtorNoMoveOutOfPinned dUnpinField ∧
      DropGuaranteeForPinned dUnpinField ∧ NoPinnedTake dUnpinField ∧
      NotPackedIfPinned dUnpinField ∧ ProjectionConsistent dUnpinField ∧
      SafeProgramsKeepAddrInv { dUnpinField with unpin := autoUnpin dUnpinField } :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    autoUnpin_sound dUnpinField (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-- **The all-fields rule does not repair a declaration violating (b)–(f).** `autoUnpin dB`
is `false`, `dB` violates (b), and with `unpin := autoUnpin dB` some safe program breaks
`AddrInv` (`dtorNoMoveOut_tight`). -/
theorem autoUnpin_does_not_rescue_dB :
    autoUnpin dB = false ∧ ¬ DtorNoMoveOutOfPinned dB ∧
      ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB } := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have e : ({ dB with unpin := autoUnpin dB } : Decl) = dB := by decide
  rw [e] at h
  obtain ⟨-, -, -, -, -, -, hsafe, hfail, -⟩ := dtorNoMoveOut_tight
  exact hfail (h progB hsafe)

theorem not_safeProgramsKeepAddrInv_of {d : Decl} {prog : List Op}
    (hs : SafeProgram d State.init prog)
    (hf : ¬ ∀ s ∈ states State.init (compile d prog), AddrInv s) :
    ¬ SafeProgramsKeepAddrInv d := fun h => hf (h prog hs)

/-- **Each of (b)–(f) is tight in the unfolded statement of `autoUnpin_sound`** (one-field
witnesses `dB`, `dC`, `dD`, `dE`, `dF`, each satisfying the other four conditions by the
`_tight` theorems): the all-fields rule refuses `Unpin` to each, and with
`unpin := autoUnpin X` some safe program breaks `AddrInv`. -/
theorem autoUnpin_sound_b_to_f_tight :
    (autoUnpin dB = false ∧ ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB }) ∧
    (autoUnpin dC = false ∧ ¬ SafeProgramsKeepAddrInv { dC with unpin := autoUnpin dC }) ∧
    (autoUnpin dD = false ∧ ¬ SafeProgramsKeepAddrInv { dD with unpin := autoUnpin dD }) ∧
    (autoUnpin dE = false ∧ ¬ SafeProgramsKeepAddrInv { dE with unpin := autoUnpin dE }) ∧
    (autoUnpin dF = false ∧ ¬ SafeProgramsKeepAddrInv { dF with unpin := autoUnpin dF }) := by
  have eB : ({ dB with unpin := autoUnpin dB } : Decl) = dB := by decide
  have eC : ({ dC with unpin := autoUnpin dC } : Decl) = dC := by decide
  have eD : ({ dD with unpin := autoUnpin dD } : Decl) = dD := by decide
  have eE : ({ dE with unpin := autoUnpin dE } : Decl) = dE := by decide
  have eF : ({ dF with unpin := autoUnpin dF } : Decl) = dF := by decide
  rw [eB, eC, eD, eE, eF]
  obtain ⟨-, -, -, -, -, -, sB, fB, -⟩ := dtorNoMoveOut_tight
  obtain ⟨-, -, -, -, -, -, sC, fC, -⟩ := dropGuaranteeForPinned_api_tight
  obtain ⟨-, -, -, -, -, -, sD, fD, -⟩ := noPinnedTake_tight
  obtain ⟨-, -, -, -, -, -, sE, fE, -⟩ := notPacked_tight
  obtain ⟨-, -, -, -, -, -, sF, fF, -⟩ := projectionConsistent_tight
  exact ⟨⟨by decide, not_safeProgramsKeepAddrInv_of sB fB⟩,
    ⟨by decide, not_safeProgramsKeepAddrInv_of sC fC⟩,
    ⟨by decide, not_safeProgramsKeepAddrInv_of sD fD⟩,
    ⟨by decide, not_safeProgramsKeepAddrInv_of sE fE⟩,
    ⟨by decide, not_safeProgramsKeepAddrInv_of sF fF⟩⟩

/-- **A leaked object's fields can still change** (references survive `forget` in this
model). On `dUnpinField` (which satisfies (a)–(f)), after `forget 0` the continuation
`assignField 0 0` is safe and replaces the value in field `(0, 0)`; on `dRich` (not `Unpin`,
satisfying (a)–(f)), after `forget 0` the continuation `overwrite 0 1` is safe and writes into
the leaked object. -/
theorem forget_does_not_freeze_fields :
    SafeProgram dUnpinField State.init [.new, .pin 0, .projPin 0 0, .forget 0, .assignField 0 0] ∧
      (runActs State.init (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0])).isLeaked 0
        = true ∧
      (runActs State.init
          (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0, .assignField 0 0])).leafAt
          (0, 0) ≠
        (runActs State.init (compile dUnpinField [.new, .pin 0, .projPin 0 0, .forget 0])).leafAt
          (0, 0) ∧
      SafeProgram dRich State.init
        [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0, .overwrite 0 1] ∧
      (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0])).isLeaked 0
        = true ∧
      (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0,
            .overwrite 0 1])).leafAt (0, 1) ≠
        (runActs State.init (compile dRich
          [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .forget 0])).leafAt
          (0, 1) := by
  decide

theorem autoUnpin_pos_neg :
    autoUnpin dFUnpin = true ∧ autoUnpin dConservative = false ∧ autoUnpin dBase = false := by
  decide

/-! ## Tightness for the scope theorems -/

/-- **The hypothesis `hsafe` of `addrState_only_at_structurally_projected_fields` (and of
`no_addrState_without_structural_projection`) is tight** (witness: `dNoProj`, which offers no
structural projection, and the 4-operation program `pinAndInit`): the program is not safe,
and its final state holds a self-pointer at a field index without a structural projection. -/
theorem addrState_hsafe_tight :
    ¬ SafeProgram dNoProj State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit), AddrStateAtProjected dNoProj s) ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) := by
  have hmem : runActs State.init (compile dNoProj pinAndInit) ∈
      states State.init (compile dNoProj pinAndInit) := by decide
  have hv : (runActs State.init (compile dNoProj pinAndInit)).leafAt (0, 0) =
      some ⟨0, false, some (0, 0)⟩ := by decide
  refine ⟨by decide, fun h => ?_, fun h => ?_⟩
  · have := (h _ hmem).1 (0, 0) _ hv (0, 0) rfl
    simp [dNoProj] at this
  · have := (h _ hmem).2 (0, 0) _ hv
    simp at this

/-- **The hypothesis `hno` of `no_addrState_without_structural_projection` is tight**
(witness: `dBase` and `pinAndInit`): `dBase` offers a structural projection, the program is
safe, and its final state holds a self-pointer. -/
theorem noAddrState_hno_tight :
    ¬ (∀ i, ApiOp.projPin i ∉ dBase.api) ∧ SafeProgram dBase State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dBase pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) := by
  have hmem : runActs State.init (compile dBase pinAndInit) ∈
      states State.init (compile dBase pinAndInit) := by decide
  have hv : (runActs State.init (compile dBase pinAndInit)).leafAt (0, 0) =
      some ⟨0, false, some (0, 0)⟩ := by decide
  refine ⟨fun h => h 0 (by decide), by decide, fun h => ?_⟩
  have := (h _ hmem).2 (0, 0) _ hv
  simp at this

end Toy.Pin
