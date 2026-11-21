import ToyPin.Examples

/-!
# Companion theorems

Combined tightness witnesses and further definition examples. Each combined theorem restates,
as one conjunction, facts that are otherwise spread over several theorems of this package, so
that a tightness witness says in one place that all other hypotheses hold and the conclusion
fails. The definitions introduced here (`dZero`, `dZeroOutOfBounds`, `progZero`) are used only
in this module.
-/

namespace Toy.Pin

open State

/-! ## Definition examples for `AddrStateAtProjected` and `Op.Mentions` -/

/-- `AddrStateAtProjected` admits the final state of the safe program
`pinAndLink ++ [.initSelf (0, 0)]` on `dBase` (one list entry and one self-pointer, both at
field 0, which `dBase` projects structurally), and rejects the final state of the program
`pinAndInit` on `dNoProj` (which offers no structural projection; the program is not safe for
`dNoProj`), whose field `(0, 0)` holds a self-pointer. -/
theorem addrStateAtProjected_pos_neg :
    SafeProgram dBase State.init (pinAndLink ++ [.initSelf (0, 0)]) ∧
      (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))).registry =
        [((0, 0), 0)] ∧
      (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))).leafAt (0, 0) =
        some ⟨0, false, some (0, 0)⟩ ∧
      AddrStateAtProjected dBase
        (runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)]))) ∧
      ¬ AddrStateAtProjected dNoProj (runActs State.init (compile dNoProj pinAndInit)) := by
  have hs : SafeProgram dBase State.init (pinAndLink ++ [.initSelf (0, 0)]) := by decide
  have hmem : runActs State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)])) ∈
      states State.init (compile dBase (pinAndLink ++ [.initSelf (0, 0)])) := by decide
  have hv : (runActs State.init (compile dNoProj pinAndInit)).leafAt (0, 0) =
      some ⟨0, false, some (0, 0)⟩ := by decide
  refine ⟨hs, by decide, by decide,
    addrState_only_at_structurally_projected_fields dBase _ hs _ hmem, fun h => ?_⟩
  have := h.1 (0, 0) _ hv (0, 0) rfl
  simp [dNoProj] at this

/-- `Op.Mentions b` holds for an operation whose target object, or one of the two objects of
a swap, is `b`; it fails for `new` and for operations on other objects. A field index equal
to `b` does not count. -/
theorem op_mentions_pos_neg :
    (Op.drop 0).Mentions 0 ∧ (Op.swapField 1 0 0).Mentions 0 ∧ (Op.initSelf (0, 2)).Mentions 0 ∧
      ¬ Op.new.Mentions 0 ∧ ¬ (Op.projPin 1 0).Mentions 0 ∧ ¬ (Op.link (1, 0)).Mentions 0 := by
  decide

/-! ## A non-empty safe program for `dFUnpin` -/

/-- `projection_inconsistent_unpin_field_sound` is not about an empty set of programs: this
6-operation program pins the object, projects its `Unpin` field structurally, lets the field
attempt a self-reference (a no-op on an `Unpin` value), replaces the field through the
non-structural projection, and drops the object; it is accepted by `SafeProgram dFUnpin`. -/
theorem dFUnpin_nonvacuous :
    SafeProgram dFUnpin State.init
      [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .replaceField 0 0, .drop 0] := by
  decide

/-! ## Combined tightness witness for (b)–(f) in `autoUnpin_sound` -/

/-- **Each of (b)–(f) is tight in the unfolded statement of `autoUnpin_sound`, in one
statement.** For each one-field witness (`dB`; `dC` and `dC'` for (c); `dD`; `dE`; `dF`): the
other four of (b)–(f) hold, the named one fails, `autoUnpin` refuses `Unpin`, and with
`unpin := autoUnpin X` not every safe program keeps `AddrInv`. -/
theorem autoUnpin_sound_b_to_f_tight_combined :
    (¬ DtorNoMoveOutOfPinned dB ∧ DropGuaranteeForPinned dB ∧ NoPinnedTake dB ∧
      NotPackedIfPinned dB ∧ ProjectionConsistent dB ∧
      autoUnpin dB = false ∧ ¬ SafeProgramsKeepAddrInv { dB with unpin := autoUnpin dB }) ∧
    (DtorNoMoveOutOfPinned dC ∧ ¬ DropGuaranteeForPinned dC ∧ NoPinnedTake dC ∧
      NotPackedIfPinned dC ∧ ProjectionConsistent dC ∧
      autoUnpin dC = false ∧ ¬ SafeProgramsKeepAddrInv { dC with unpin := autoUnpin dC }) ∧
    (DtorNoMoveOutOfPinned dC' ∧ ¬ DropGuaranteeForPinned dC' ∧ NoPinnedTake dC' ∧
      NotPackedIfPinned dC' ∧ ProjectionConsistent dC' ∧
      autoUnpin dC' = false ∧ ¬ SafeProgramsKeepAddrInv { dC' with unpin := autoUnpin dC' }) ∧
    (DtorNoMoveOutOfPinned dD ∧ DropGuaranteeForPinned dD ∧ ¬ NoPinnedTake dD ∧
      NotPackedIfPinned dD ∧ ProjectionConsistent dD ∧
      autoUnpin dD = false ∧ ¬ SafeProgramsKeepAddrInv { dD with unpin := autoUnpin dD }) ∧
    (DtorNoMoveOutOfPinned dE ∧ DropGuaranteeForPinned dE ∧ NoPinnedTake dE ∧
      ¬ NotPackedIfPinned dE ∧ ProjectionConsistent dE ∧
      autoUnpin dE = false ∧ ¬ SafeProgramsKeepAddrInv { dE with unpin := autoUnpin dE }) ∧
    (DtorNoMoveOutOfPinned dF ∧ DropGuaranteeForPinned dF ∧ NoPinnedTake dF ∧
      NotPackedIfPinned dF ∧ ¬ ProjectionConsistent dF ∧
      autoUnpin dF = false ∧ ¬ SafeProgramsKeepAddrInv { dF with unpin := autoUnpin dF }) := by
  obtain ⟨hB, hC, hD, hE, hF⟩ := autoUnpin_sound_b_to_f_tight
  have eC' : ({ dC' with unpin := autoUnpin dC' } : Decl) = dC' := by decide
  obtain ⟨-, -, -, -, -, -, sC', fC', -⟩ := dropGuaranteeForPinned_dtor_tight
  exact ⟨⟨by decide, by decide, by decide, by decide, by decide, hB.1, hB.2⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, hC.1, hC.2⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, by decide,
      by rw [eC']; exact not_safeProgramsKeepAddrInv_of sC' fC'⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, hD.1, hD.2⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, hE.1, hE.2⟩,
    ⟨by decide, by decide, by decide, by decide, by decide, hF.1, hF.2⟩⟩

/-! ## Combined tightness witness and a non-empty witness for the scope theorem -/

/-- **`hsafe` of `no_addrState_without_structural_projection` is tight, in one statement**
(witness: `dNoProj` and `pinAndInit`): the other hypothesis `hno` holds, the program is not
accepted by `SafeProgram`, and the conclusion fails along it. -/
theorem noAddrState_hsafe_tight :
    (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧ ¬ SafeProgram dNoProj State.init pinAndInit ∧
      ¬ (∀ s ∈ states State.init (compile dNoProj pinAndInit),
          s.registry = [] ∧ ∀ l v, s.leafAt l = some v → v.selfPtr = none) :=
  ⟨noProjection_unpin_vacuously_sound.2.1, addrState_hsafe_tight.1, addrState_hsafe_tight.2.2⟩

/-- Both hypotheses of `no_addrState_without_structural_projection` hold for `dNoProj` and a
non-empty 5-operation program that pins the object, replaces its field and the whole struct,
and drops it. -/
theorem noAddrState_nonvacuous_nonempty :
    (∀ i, ApiOp.projPin i ∉ dNoProj.api) ∧
      SafeProgram dNoProj State.init [.new, .pin 0, .replaceField 0 0, .replaceStruct 0, .drop 0] :=
  ⟨noProjection_unpin_vacuously_sound.2.1, by decide⟩

/-! ## Tightness of the leaf-level corollary `unmentioned_object_leaves_and_entries` -/

/-- **`hb` of `unmentioned_object_leaves_and_entries` is tight** (one-field witness `dBase`,
`State.init`, `b = 0`, continuation `[new]`): `hmention` holds, `hb` fails, and the leaf-level
conclusion fails. -/
theorem unmentioned_leaves_hb_tight :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states State.init (compile dBase [.new]),
        (∀ i, s.leafAt (0, i) = State.init.leafAt (0, i)) ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = State.init.leafAt e.1 := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have hmem : runActs State.init (compile dBase [.new]) ∈
      states State.init (compile dBase [.new]) := by decide
  have h0 := (h _ hmem).1 0
  revert h0; decide

/-- **`hmention` of `unmentioned_object_leaves_and_entries` is tight** (one-field witness
`dBase`, the leaked state `stLeaked`, `b = 0`, continuation `[assignField 0 0]`): `hb` holds,
`hmention` fails, and the leaf-level conclusion fails. -/
theorem unmentioned_leaves_hmention_tight :
    0 < stLeaked.heap.length ∧ ¬ (∀ op ∈ [Op.assignField 0 0], ¬ op.Mentions 0) ∧
      ¬ ∀ s ∈ states stLeaked (compile dBase [.assignField 0 0]),
        (∀ i, s.leafAt (0, i) = stLeaked.leafAt (0, i)) ∧
          ∀ e ∈ stLeaked.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = stLeaked.leafAt e.1 := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have hmem : runActs stLeaked (compile dBase [.assignField 0 0]) ∈
      states stLeaked (compile dBase [.assignField 0 0]) := by decide
  have h0 := (h _ hmem).1 0
  revert h0; decide

/-- A zero-field unit struct, declared `Unpin`. -/
def dZero : Decl := ⟨[], true, [], [], false⟩

/-- **On a zero-field declaration, violating `hb` does not break the leaf-level corollary.**
For `dZero`, `State.init`, `b = 0` and the continuation `[new]`: `hb` fails and `hmention`
holds; the conclusion of `unmentioned_object_unchanged` fails (an object now exists at
address 0), but the conclusion of `unmentioned_object_leaves_and_entries` holds, because the
new object has no fields and the list is empty. -/
theorem unmentioned_leaves_hb_not_tight_on_zero_field :
    ¬ (0 < State.init.heap.length) ∧ (∀ op ∈ [Op.new], ¬ op.Mentions 0) ∧
      (¬ ∀ s ∈ states State.init (compile dZero [.new]),
        s.heap[0]? = State.init.heap[0]? ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 → e ∈ s.registry) ∧
      (∀ s ∈ states State.init (compile dZero [.new]),
        (∀ i, s.leafAt (0, i) = State.init.leafAt (0, i)) ∧
          ∀ e ∈ State.init.registry, e.1.1 = 0 →
            e ∈ s.registry ∧ s.leafAt e.1 = State.init.leafAt e.1) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro s hs
  simp only [compile, List.flatMap_cons, List.flatMap_nil, expand, List.append_nil,
    states, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ he => by cases he⟩
  · refine ⟨fun i => ?_, fun _ he => by cases he⟩
    simp [dZero, applyAct, State.init, State.push, State.leafAt, Obj.fresh, Obj.leaf, mkFields]

/-! ## Zero-field declarations and out-of-range indices -/

/-- A zero-field packed declaration, declared `Unpin`, whose API and destructor name the
out-of-range field index 0. -/
def dZeroOutOfBounds : Decl :=
  ⟨[], true, [.projPin 0, .projMut 0, .take 0, .overwrite 0], [.moveOut 0, .overwrite 0], true⟩

/-- A 9-operation program for `dZeroOutOfBounds` that uses every API operation at index 0. -/
def progZero : List Op :=
  [.new, .pin 0, .projPin 0 0, .initSelf (0, 0), .link (0, 0), .take 0 0,
    .overwrite 0 0, .replaceStruct 0, .drop 0]

/-- **Zero-field declarations are sound, including with out-of-range indices.** `dZero` and
`dZeroOutOfBounds` satisfy (a)–(f), are granted `Unpin` by `autoUnpin` and by
`pinnedFieldsRule`, and keep `AddrInv` for every safe program; `progZero` is accepted by
`SafeProgram dZeroOutOfBounds` and keeps `AddrInv` in every visited state. -/
theorem zero_field_declarations_sound :
    UnpinOnlyIfPinnedFieldsUnpin dZero ∧ DtorNoMoveOutOfPinned dZero ∧
    DropGuaranteeForPinned dZero ∧ NoPinnedTake dZero ∧
    NotPackedIfPinned dZero ∧ ProjectionConsistent dZero ∧
    autoUnpin dZero = true ∧ pinnedFieldsRule dZero = true ∧
    SafeProgramsKeepAddrInv dZero ∧
    UnpinOnlyIfPinnedFieldsUnpin dZeroOutOfBounds ∧ DtorNoMoveOutOfPinned dZeroOutOfBounds ∧
    DropGuaranteeForPinned dZeroOutOfBounds ∧ NoPinnedTake dZeroOutOfBounds ∧
    NotPackedIfPinned dZeroOutOfBounds ∧ ProjectionConsistent dZeroOutOfBounds ∧
    autoUnpin dZeroOutOfBounds = true ∧ pinnedFieldsRule dZeroOutOfBounds = true ∧
    SafeProgramsKeepAddrInv dZeroOutOfBounds ∧
    SafeProgram dZeroOutOfBounds State.init progZero ∧
    (∀ s ∈ states State.init (compile dZeroOutOfBounds progZero), AddrInv s) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, rfl, by decide,
   fun prog hs => addrInv_of_structural_pinning_conditions dZero
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) prog hs,
   by decide, by decide, by decide, by decide, by decide, by decide, rfl, by decide,
   fun prog hs => addrInv_of_structural_pinning_conditions dZeroOutOfBounds
     (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) prog hs,
   by decide, by decide⟩

/-- A zero-field declaration, `dConservative` and `dUnpinNonStructural` each have a non-empty
safe program: the soundness statements for them (`zero_field_declarations_sound`,
`autoUnpin_conservative`, `unpinWitness_projPin_tight`) are not about an empty set of
programs. The programs pin the object, use the non-structural or `&mut S` access that `SafeOp`
grants, and drop the object. -/
theorem sound_declarations_nonvacuous :
    SafeProgram dZero State.init [.new, .pin 0, .replaceStruct 0, .drop 0] ∧
      SafeProgram dConservative State.init
        [.new, .pin 0, .projPin 0 1, .initSelf (0, 1), .replaceField 0 0, .replaceStruct 0,
          .drop 0] ∧
      SafeProgram dUnpinNonStructural State.init
        [.new, .pin 0, .replaceField 0 0, .replaceStruct 0, .drop 0] := by
  decide

end Toy.Pin
