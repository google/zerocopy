import ToyPin.Scope

/-!
# Deriving `Unpin` for a struct with structurally pinned fields

* `PinnedFieldsUnpin d`: every structurally pinned field's type is `Unpin` (the conjunction
  over structurally pinned fields only).
* `autoUnpin d`: every field's type is `Unpin` (the conjunction over all fields, which is
  what Rust's auto trait computes for a struct without a manual `impl`).

Results (`d.unpin = true` means that `S` is *declared* `Unpin`; `d.fieldTy i = true` means
that field `i`'s *type* is `Unpin`):

* `unpin_sound_iff_pinnedFieldsUnpin`: for a declaration with `d.unpin = true` (no other
  hypothesis), every program accepted by `SafeProgram d` from `State.init` keeps `AddrInv`
  in every visited state iff `PinnedFieldsUnpin d`.
* `unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field`: with
  `d.unpin = true`, a structurally projected field `i` of non-`Unpin` type gives an explicit
  safe program that breaks `SelfRefOK`.
* `soundUnpinRule_iff`, `pinnedFieldsRule_greatest_under_b_to_f`,
  `soundUnpinRule_false_of_grants_structural_nonUnpin`: rules deciding `d.unpin`, judged
  on declarations satisfying (b)–(f).
* `autoUnpin_implies_pinnedFieldsUnpin`, `autoUnpin_sound`: the all-fields rule.

Scope: address-sensitive state exists only at structurally projected fields
(`addrState_only_at_structurally_projected_fields`); a declaration without structural
projections has none (`no_addrState_without_structural_projection`), so for it every
`unpin` value is sound in this model.
-/

namespace Toy.Pin

open State

/-- Every structurally pinned field's type is `Unpin`. -/
def PinnedFieldsUnpin (d : Decl) : Prop :=
  ∀ i, ApiOp.projPin i ∈ d.api → d.fieldTy i = true

/-- The conjunction of `Unpin` over all fields (the auto-trait rule). -/
def autoUnpin (d : Decl) : Bool := d.fieldUnpin.all id

instance (d : Decl) : Decidable (PinnedFieldsUnpin d) :=
  decidable_of_iff (∀ i < d.nfields, ApiOp.projPin i ∈ d.api → d.fieldTy i = true)
    ⟨fun h i hi => by
      by_cases hlt : i < d.nfields
      · exact h i hlt hi
      · exact Decl.fieldTy_eq_true_of_le (by omega), fun h i _ => h i⟩

/-- Condition (a) is exactly "`S : Unpin` implies `PinnedFieldsUnpin`". -/
theorem unpinOnlyIf_iff_pinnedFieldsUnpin (d : Decl) :
    UnpinOnlyIfPinnedFieldsUnpin d ↔ (d.unpin = true → PinnedFieldsUnpin d) := Iff.rfl

theorem autoUnpin_implies_pinnedFieldsUnpin (d : Decl) (h : autoUnpin d = true) :
    PinnedFieldsUnpin d := by
  intro i _
  unfold Decl.fieldTy
  cases hi : d.fieldUnpin[i]? with
  | none => rfl
  | some b =>
    have hmem : b ∈ d.fieldUnpin := List.mem_of_getElem? hi
    unfold autoUnpin at h
    rw [List.all_eq_true] at h
    simpa using h b hmem

theorem Decl.fieldUnpin_getElem?_of_fieldTy_false {d : Decl} {i : Nat}
    (h : d.fieldTy i = false) : d.fieldUnpin[i]? = some false := by
  unfold Decl.fieldTy at h
  cases hi : d.fieldUnpin[i]? with
  | none => rw [hi] at h; cases h
  | some b => rw [hi] at h; simp at h; rw [h]

theorem self_mem_states (st : State) (as : List Act) : st ∈ states st as := by
  cases as <;> simp [states]

/-- The witness program: create an `S`, pin it, project field `i` structurally, let the
field's value store its own address, then `mem::replace` the whole `S` through `&mut S`
(available in safe code because `S : Unpin`). -/
def unpinWitness (i : Nat) : List Op :=
  [.new, .pin 0, .projPin 0 i, .initSelf (0, i), .replaceStruct 0]

theorem isPinnedLoc_pinField_self (st : State) (l : Loc) (h : l.1 < st.heap.length) :
    (applyAct st (.pinField l)).isPinnedLoc l = true := by
  simp only [applyAct, isPinnedLoc]
  rw [modifyObj_heap]
  simp only [ite_true]
  cases ho : st.heap[l.1]? with
  | none => rw [List.getElem?_eq_none_iff] at ho; omega
  | some o => simp

/-- **A declared-`Unpin` struct with a structurally projected non-`Unpin` field: the witness
program is safe and breaks the self-reference invariant.** For every declaration `d` with
`d.unpin = true`, and every field index `i` with `ApiOp.projPin i ∈ d.api` and
`d.fieldTy i = false`, the program `unpinWitness i` is accepted by `SafeProgram d` from
`State.init`, some visited state violates `SelfRefOK`, and every visited state satisfies
`ListOK` (the program never links into the list). No other condition on `d` is assumed. -/
theorem unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field (d : Decl)
    (hu : d.unpin = true) (i : Nat) (hproj : ApiOp.projPin i ∈ d.api)
    (hty : d.fieldTy i = false) :
    SafeProgram d State.init (unpinWitness i) ∧
      (∃ s ∈ states State.init (compile d (unpinWitness i)), ¬ SelfRefOK s) ∧
      (∀ s ∈ states State.init (compile d (unpinWitness i)), ListOK s) := by
  have hfu := Decl.fieldUnpin_getElem?_of_fieldTy_false hty
  -- the states
  let s1 := applyAct State.init (.alloc (d.fieldUnpin.map some))
  let s2 := applyAct s1 (.pinObj 0)
  let s3 := applyAct s2 (.pinField (0, i))
  let s4 := applyAct s3 (.setSelf (0, i))
  let s5 := applyAct s4 (.moveObj 0)
  have hlen1 : s1.heap.length = 1 := rfl
  have hlen2 : s2.heap.length = 1 := by simp [s2, applyAct, hlen1]
  have hlen3 : s3.heap.length = 1 := by simp [s3, applyAct, hlen2]
  have hleaf1 : s1.leafAt (0, i) = some ⟨i, false, none⟩ := by
    show (Obj.fresh (mkFields 0 (d.fieldUnpin.map some))).leaf i = _
    simp [Obj.leaf, Obj.fresh, getElem?_mkFields, hfu]
  have hleaf3 : s3.leafAt (0, i) = some ⟨i, false, none⟩ := by
    have e3 : s3.leafAt (0, i) = s2.leafAt (0, i) :=
      leafAt_modifyObj_of_fields
        (f := fun o => { o with pinnedFields := i :: o.pinnedFields }) (fun _ => rfl) _
    have e2 : s2.leafAt (0, i) = s1.leafAt (0, i) :=
      leafAt_modifyObj_of_fields (f := fun o => { o with pinned := true }) (fun _ => rfl) _
    rw [e3, e2, hleaf1]
  have hpin3 : s3.isPinnedLoc (0, i) = true :=
    isPinnedLoc_pinField_self s2 (0, i) (by simp [hlen2])
  have hs4 : s4 = s3.setLeaf (0, i) (some ⟨i, false, some (0, i)⟩) := by
    show applyAct s3 (.setSelf (0, i)) = _
    simp only [applyAct, hleaf3, hpin3]
    rfl
  have hleaf4 : s4.leafAt (0, i) = some ⟨i, false, some (0, i)⟩ := by
    rw [hs4]; exact leafAt_setLeaf_self_of_some _ hleaf3
  have hlen4 : s4.heap.length = 1 := by rw [hs4]; simp [hlen3]
  have hleaf5 : s5.leafAt (1, i) = some ⟨i, false, some (0, i)⟩ := by
    show ((s4.modifyObj 0 _).push _).leafAt (1, i) = _
    have : (1 : Nat) = (s4.modifyObj 0 fun o => { o with fields := o.fields.map fun _ => none }).heap.length := by
      simp [hlen4]
    rw [this, leafAt_push_eq]
    rw [← hleaf4]
    unfold State.leafAt
    cases ho : s4.heap[0]? <;> simp [Obj.leaf, Obj.fresh]
  -- liveness facts for safety
  have hlive1 : s1.isLive 0 = true := rfl
  have hpinned1 : s1.isPinned 0 = false := rfl
  have hlive2 : s2.isLive 0 = true := rfl
  have hpinned2 : s2.isPinned 0 = true := rfl
  have hlive3 : s3.isLive 0 = true := rfl
  have hlive4 : s4.isLive 0 = true := by
    rw [hs4]
    unfold State.setLeaf State.isLive
    rw [modifyObj_heap]
    simp only [ite_true]
    exact (by
      have : s3.isLive 0 = true := hlive3
      unfold State.isLive at this
      cases ho : s3.heap[0]? with
      | none => rw [ho] at this; cases this
      | some o => rw [ho] at this; simpa using this)
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨trivial, ⟨hlive1, hpinned1⟩, ⟨hlive2, hpinned2, hproj⟩, ⟨hlive3, hpin3⟩,
      ⟨hlive4, Or.inr hu⟩, trivial⟩
  · have hmem : s5 ∈ states State.init (compile d (unpinWitness i)) := by
      simp only [unpinWitness, compile, List.flatMap_cons, List.flatMap_nil, expand,
        List.append_nil, List.cons_append, List.nil_append, states, List.mem_cons]
      right; right; right; right; right
      exact self_mem_states _ _
    refine ⟨s5, hmem, fun hok => ?_⟩
    have := hok (1, i) _ hleaf5
    simp at this
  · intro s hs e he
    have hno : ∀ a ∈ compile d (unpinWitness i), ∀ m, a ≠ .register m := by
      intro a ha m hm
      subst hm
      simp [unpinWitness, compile, expand] at ha
    have := registry_sub_of_no_register _ State.init hno s hs e he
    simp [State.init] at this

/-- The conclusion of `unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field`
implies that `AddrInv` fails along the witness program. -/
theorem not_forall_addrInv_of_exists_not_selfRefOK {ss : List State}
    (h : ∃ s ∈ ss, ¬ SelfRefOK s) : ¬ ∀ s ∈ ss, AddrInv s := by
  obtain ⟨s, hs, hn⟩ := h
  exact fun hall => hn (hall s hs).1

/-- With `S : Unpin`, all six conditions follow from `PinnedFieldsUnpin` (there is then no
structurally pinned non-`Unpin` field at all). -/
theorem conds_of_unpin_pinnedFieldsUnpin (d : Decl) (h : PinnedFieldsUnpin d) :
    UnpinOnlyIfPinnedFieldsUnpin d ∧ DtorNoMoveOutOfPinned d ∧ DropGuaranteeForPinned d ∧
      NoPinnedTake d ∧ NotPackedIfPinned d ∧ ProjectionConsistent d := by
  have hn : ∀ i, ¬ d.PinnedNonUnpinField i := fun i hi => by
    have := h i hi.1; rw [hi.2] at this; cases this
  exact ⟨fun _ => h, fun i hi => absurd hi (hn i), fun i hi => absurd hi (hn i),
    fun i hi => absurd hi (hn i), fun _ => hn, fun i hi => absurd hi (hn i)⟩

/-- **Characterization of a sound `Unpin` declaration.** For a declaration with
`d.unpin = true` (and no other hypothesis), every program accepted by `SafeProgram d` from
`State.init` keeps both address-sensitive invariants in every visited state if and only if
every structurally projected field's type is `Unpin`. If `d` offers no structural projection,
both sides hold vacuously (`no_addrState_without_structural_projection`). -/
theorem unpin_sound_iff_pinnedFieldsUnpin (d : Decl) (hu : d.unpin = true) :
    SafeProgramsKeepAddrInv d ↔ PinnedFieldsUnpin d := by
  constructor
  · intro hs i hi
    cases hty : d.fieldTy i with
    | true => rfl
    | false =>
      have hw := unpinWitness_breaks_selfRef_of_unpin_of_structural_nonUnpin_field d hu i hi hty
      exact absurd (hs _ hw.1) (not_forall_addrInv_of_exists_not_selfRefOK hw.2.1)
  · intro h prog hsafe
    obtain ⟨ha, hb, hc, hd, he, hf⟩ := conds_of_unpin_pinnedFieldsUnpin d h
    exact addrInv_of_structural_pinning_conditions d ha hb hc hd he hf prog hsafe

/-- **If every structurally projected field has an `Unpin` type, every safe program keeps
`AddrInv`, whatever `d.unpin` is.** All six conditions then hold
(`conds_of_unpin_pinnedFieldsUnpin`). In particular this covers every declaration without
structural projections, and every declaration offering both projections of `Unpin` fields. -/
theorem sound_of_pinnedFieldsUnpin (d : Decl) (h : PinnedFieldsUnpin d) :
    SafeProgramsKeepAddrInv d := by
  intro prog hsafe
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := conds_of_unpin_pinnedFieldsUnpin d h
  exact addrInv_of_structural_pinning_conditions d ha hb hc hd he hf prog hsafe

/-- A rule `r : Decl → Bool` decides the `unpin` field of a declaration (it may inspect the
whole declaration, including the `unpin` value it replaces). It is **sound** if, for every
declaration `d` satisfying (b)–(f), setting `unpin := r d` makes every program accepted by
`SafeProgram` from `State.init` keep `AddrInv` in every visited state. Declarations violating
one of (b)–(f) impose no constraint on `r`. -/
def SoundUnpinRule (r : Decl → Bool) : Prop :=
  ∀ d : Decl, DtorNoMoveOutOfPinned d → DropGuaranteeForPinned d → NoPinnedTake d →
    NotPackedIfPinned d → ProjectionConsistent d → SafeProgramsKeepAddrInv { d with unpin := r d }

/-- **Characterization of sound `Unpin` rules on declarations satisfying (b)–(f).** A rule is
sound iff, on every declaration satisfying (b)–(f), it grants `unpin = true` only when every
structurally pinned field's type is `Unpin`. -/
theorem soundUnpinRule_iff (r : Decl → Bool) :
    SoundUnpinRule r ↔ ∀ d : Decl, DtorNoMoveOutOfPinned d → DropGuaranteeForPinned d →
      NoPinnedTake d → NotPackedIfPinned d → ProjectionConsistent d → r d = true →
        PinnedFieldsUnpin d := by
  constructor
  · intro hr d hb hc hd he hf hrd
    have := hr d hb hc hd he hf
    rw [hrd] at this
    exact (unpin_sound_iff_pinnedFieldsUnpin { d with unpin := true } rfl).mp this
  · intro hr d hb hc hd he hf prog hsafe
    refine addrInv_of_structural_pinning_conditions { d with unpin := r d } ?_ hb hc hd he hf
      prog hsafe
    intro hu
    exact hr d hb hc hd he hf hu

/-- The pinned-fields rule: `S : Unpin` iff every structurally pinned field is `Unpin`. -/
def pinnedFieldsRule (d : Decl) : Bool := decide (PinnedFieldsUnpin d)

theorem pinnedFieldsRule_sound : SoundUnpinRule pinnedFieldsRule :=
  (soundUnpinRule_iff _).mpr fun _ _ _ _ _ _ h => of_decide_eq_true h

/-- **On declarations satisfying (b)–(f), the pinned-fields rule is the most permissive
sound rule.** Every sound rule that grants `Unpin` to a declaration satisfying (b)–(f) agrees
with `pinnedFieldsRule` there. (Off that domain sound rules are unconstrained; see
`pinnedFieldsRule_not_greatest_without_b_to_f`.) -/
theorem pinnedFieldsRule_greatest_under_b_to_f (r : Decl → Bool) (hr : SoundUnpinRule r)
    (d : Decl) (hb : DtorNoMoveOutOfPinned d) (hc : DropGuaranteeForPinned d)
    (hd : NoPinnedTake d) (he : NotPackedIfPinned d) (hf : ProjectionConsistent d)
    (h : r d = true) : pinnedFieldsRule d = true :=
  decide_eq_true ((soundUnpinRule_iff r).mp hr d hb hc hd he hf h)

/-- **Granting `Unpin` while omitting a structurally pinned non-`Unpin` field is unsound.**
If a rule grants `unpin = true` to some declaration satisfying (b)–(f) that has a field `i`
with `ApiOp.projPin i ∈ d.api` and `d.fieldTy i = false`, the rule is not sound. -/
theorem soundUnpinRule_false_of_grants_structural_nonUnpin (r : Decl → Bool) (d : Decl)
    (hb : DtorNoMoveOutOfPinned d) (hc : DropGuaranteeForPinned d) (hd : NoPinnedTake d)
    (he : NotPackedIfPinned d) (hf : ProjectionConsistent d) (i : Nat)
    (hproj : ApiOp.projPin i ∈ d.api) (hty : d.fieldTy i = false) (h : r d = true) :
    ¬ SoundUnpinRule r := by
  intro hr
  have := (soundUnpinRule_iff r).mp hr d hb hc hd he hf h i hproj
  rw [hty] at this; cases this

/-- The pinned-fields rule does not read the `unpin` value it replaces. -/
theorem pinnedFieldsRule_ignores_unpin (d : Decl) (u : Bool) :
    pinnedFieldsRule { d with unpin := u } = pinnedFieldsRule d := rfl

/-- The all-fields rule does not read the `unpin` value it replaces. -/
theorem autoUnpin_ignores_unpin (d : Decl) (u : Bool) :
    autoUnpin { d with unpin := u } = autoUnpin d := rfl

/-- The auto-trait rule (all fields) is a sound rule (on declarations satisfying (b)–(f),
by the definition of `SoundUnpinRule`). -/
theorem autoUnpin_sound : SoundUnpinRule autoUnpin :=
  (soundUnpinRule_iff _).mpr fun d _ _ _ _ _ h => autoUnpin_implies_pinnedFieldsUnpin d h

end Toy.Pin
