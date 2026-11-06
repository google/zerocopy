import AnnealResearch.HelperValueControls

/-!
Specification-challenge contracts for the selected two-level helper heap
(R-ADEV-01, motivating A-ADEV-03 and supporting A-ADEV-01/02/04).

This module reuses the accepted `HelperValueHeap`, `HelperNestedMutation`, and
`HelperValueControls` definitions and theorems via import rather than replaying
them. It separates four outcome expectations over the admitted domain
`RootImage heap root value`:

1. `MatchesOutput`: returned output equals `(callback value).2`.
2. `OkActiveValue`: on `.ok res`, the returned active receiver has a closed
   `RootImage` and `readParent` observation equal to `(callback value).1`.
3. `ErrorActiveValue`: on `.error err`, the returned active receiver has a
   closed `RootImage` and `readParent` observation equal to `(callback value).1`.
4. `PreservesClosedAliases`: every initially closed `RootImage` and `LeafImage`
   in `heap` remains a closed image with unchanged `readParent`/`readLeaf` value.

It then compares four contract levels over `RootImage heap root value`:
- `WeakContract`: `MatchesOutput` and `OkActiveValue` only.
- `ActiveStrengthenedContract`: adds `ErrorActiveValue`, still omitting alias preservation.
- `AliasStrengthenedContract`: adds `PreservesClosedAliases`, still omitting error active value.
- `StrongContract`: requires all four expectations.

This tests specification-challenge discrimination on a fixed owned vocabulary;
it does not certify human intent, supply a general specification-equivalence
decision procedure, or establish Rust/libspecr/GC implementation adequacy.
-/

namespace AnnealResearch.SpecValidation

open HelperValueHeap HelperNestedMutation HelperValueControls

/-- Candidate operation signature specialized to `Except E A` callback outputs. -/
def CandidateOp (E A : Type) : Type :=
  Heap → Nat → (Nat → Nat × Except E A) → Option (Outcome (Except E A))

/-- `overwriteInPlace` specialized to `CandidateOp E A`. -/
def overwriteInPlaceExcept {E A : Type} (heap : Heap) (root : Nat)
    (callback : Nat → Nat × Except E A) : Option (Outcome (Except E A)) :=
  overwriteInPlace heap root callback

/-- The outcome returns the callback's second projection. -/
def MatchesOutput {E A : Type} (value : Nat)
    (callback : Nat → Nat × Except E A)
    (actual : Outcome (Except E A)) : Prop :=
  actual.output = (callback value).2

/-- On an `.ok` callback output, the active receiver observes the changed value. -/
def OkActiveValue {E A : Type} (value : Nat)
    (callback : Nat → Nat × Except E A)
    (actual : Outcome (Except E A)) : Prop :=
  ∀ res, (callback value).2 = .ok res →
    RootImage actual.heap actual.receiver (callback value).1 ∧
      readParent actual.heap actual.receiver = some (callback value).1

/-- On an `.error` callback output, the active receiver observes the changed value. -/
def ErrorActiveValue {E A : Type} (value : Nat)
    (callback : Nat → Nat × Except E A)
    (actual : Outcome (Except E A)) : Prop :=
  ∀ err, (callback value).2 = .error err →
    RootImage actual.heap actual.receiver (callback value).1 ∧
      readParent actual.heap actual.receiver = some (callback value).1

/-- Every initially closed root and leaf alias retains its closed image and value. -/
def PreservesClosedAliases {E A : Type} (heap : Heap)
    (actual : Outcome (Except E A)) : Prop :=
  (∀ oldRoot oldValue, RootImage heap oldRoot oldValue →
    RootImage actual.heap oldRoot oldValue ∧
      readParent actual.heap oldRoot = some oldValue) ∧
  (∀ oldLeaf oldValue, LeafImage heap oldLeaf oldValue →
    LeafImage actual.heap oldLeaf oldValue ∧
      readLeaf actual.heap oldLeaf = some oldValue)

/-- Explicitly weak contract that checks only output matching and `.ok` active value. -/
def WeakContract {E A : Type} (op : CandidateOp E A) : Prop :=
  ∀ heap root value callback,
    RootImage heap root value →
    ∃ actual, op heap root callback = some actual ∧
      MatchesOutput value callback actual ∧
      OkActiveValue value callback actual

/-- Partial strengthening that adds `ErrorActiveValue` but omits alias preservation. -/
def ActiveStrengthenedContract {E A : Type} (op : CandidateOp E A) : Prop :=
  ∀ heap root value callback,
    RootImage heap root value →
    ∃ actual, op heap root callback = some actual ∧
      MatchesOutput value callback actual ∧
      OkActiveValue value callback actual ∧
      ErrorActiveValue value callback actual

/-- Partial strengthening that adds `PreservesClosedAliases` but omits error active value. -/
def AliasStrengthenedContract {E A : Type} (op : CandidateOp E A) : Prop :=
  ∀ heap root value callback,
    RootImage heap root value →
    ∃ actual, op heap root callback = some actual ∧
      MatchesOutput value callback actual ∧
      OkActiveValue value callback actual ∧
      PreservesClosedAliases heap actual

/-- Full contract requiring output matching, `.ok`/`.error` active value, and alias preservation. -/
def StrongContract {E A : Type} (op : CandidateOp E A) : Prop :=
  ∀ heap root value callback,
    RootImage heap root value →
    ∃ actual, op heap root callback = some actual ∧
      MatchesOutput value callback actual ∧
      OkActiveValue value callback actual ∧
      ErrorActiveValue value callback actual ∧
      PreservesClosedAliases heap actual

theorem nested_satisfies_weak {E A : Type} :
    WeakContract (@nested (Except E A)) := by
  intro heap root value callback image
  refine ⟨expected heap (callback value).1 (callback value).2,
    nested_exact heap root value callback image, rfl, ?_⟩
  intro _ _
  exact ⟨expected_root_image heap (callback value).1,
    expected_active_value heap (callback value).1⟩

theorem commitOnlyOnOk_satisfies_weak {E A : Type} :
    WeakContract (@commitOnlyOnOk E A) := by
  intro heap root value callback image
  have parentRead : readParent heap root = some value :=
    root_image_read heap root value image
  cases hcb : callback value with
  | mk changed output =>
    cases output with
    | ok result =>
      refine ⟨expected heap changed (.ok result), ?_, ?_, ?_⟩
      · simp only [commitOnlyOnOk, parentRead, hcb] <;> rfl
      · simp only [MatchesOutput, hcb] <;> rfl
      · intro _ _
        rw [hcb]
        exact ⟨expected_root_image heap changed, expected_active_value heap changed⟩
    | error fault =>
      refine ⟨{ output := .error fault, receiver := root, heap := heap }, ?_, ?_, ?_⟩
      · simp only [commitOnlyOnOk, parentRead, hcb] <;> rfl
      · simp only [MatchesOutput, hcb] <;> rfl
      · intro res hok
        rw [hcb] at hok
        cases hok

theorem overwriteInPlace_satisfies_weak {E A : Type} :
    WeakContract (@overwriteInPlaceExcept E A) := by
  intro heap root value callback image
  rcases image with ⟨child, rootInside, childInside, parentStored, leafStored⟩
  have rootRead : readCell heap root = some (.parent child) := by
    simp only [readCell, rootInside, ite_true, parentStored]
  have leafRead : readLeaf heap child = some value :=
    leaf_image_read heap child value ⟨childInside, leafStored⟩
  have ne : root ≠ child :=
    root_image_tags_distinct heap root child value parentStored leafStored
  cases hcb : callback value with
  | mk changed output =>
    have newImage : RootImage (overwriteLeaf heap child changed) root changed := by
      refine ⟨child, rootInside, childInside, ?_, ?_⟩
      · simp [overwriteLeaf, ne, parentStored]
      · simp [overwriteLeaf]
    refine ⟨{ output := output, receiver := root, heap := overwriteLeaf heap child changed },
      ?_, ?_, ?_⟩
    · simp only [overwriteInPlaceExcept, overwriteInPlace, rootRead, leafRead, hcb] <;> rfl
    · simp only [MatchesOutput, hcb] <;> rfl
    · intro _ _
      rw [hcb]
      exact ⟨newImage, root_image_read (overwriteLeaf heap child changed) root changed newImage⟩

theorem overwriteInPlace_satisfies_activeStrengthened {E A : Type} :
    ActiveStrengthenedContract (@overwriteInPlaceExcept E A) := by
  intro heap root value callback image
  rcases image with ⟨child, rootInside, childInside, parentStored, leafStored⟩
  have rootRead : readCell heap root = some (.parent child) := by
    simp only [readCell, rootInside, ite_true, parentStored]
  have leafRead : readLeaf heap child = some value :=
    leaf_image_read heap child value ⟨childInside, leafStored⟩
  have ne : root ≠ child :=
    root_image_tags_distinct heap root child value parentStored leafStored
  cases hcb : callback value with
  | mk changed output =>
    have newImage : RootImage (overwriteLeaf heap child changed) root changed := by
      refine ⟨child, rootInside, childInside, ?_, ?_⟩
      · simp [overwriteLeaf, ne, parentStored]
      · simp [overwriteLeaf]
    have newRead : readParent (overwriteLeaf heap child changed) root = some changed :=
      root_image_read (overwriteLeaf heap child changed) root changed newImage
    refine ⟨{ output := output, receiver := root, heap := overwriteLeaf heap child changed },
      ?_, ?_, ?_, ?_⟩
    · simp only [overwriteInPlaceExcept, overwriteInPlace, rootRead, leafRead, hcb] <;> rfl
    · simp only [MatchesOutput, hcb] <;> rfl
    · intro _ _
      rw [hcb]
      exact ⟨newImage, newRead⟩
    · intro _ _
      rw [hcb]
      exact ⟨newImage, newRead⟩

theorem commitOnlyOnOk_satisfies_aliasStrengthened {E A : Type} :
    AliasStrengthenedContract (@commitOnlyOnOk E A) := by
  intro heap root value callback image
  have parentRead : readParent heap root = some value :=
    root_image_read heap root value image
  cases hcb : callback value with
  | mk changed output =>
    cases output with
    | ok result =>
      refine ⟨expected heap changed (.ok result), ?_, ?_, ?_, ?_⟩
      · simp only [commitOnlyOnOk, parentRead, hcb] <;> rfl
      · simp only [MatchesOutput, hcb] <;> rfl
      · intro _ _
        rw [hcb]
        exact ⟨expected_root_image heap changed, expected_active_value heap changed⟩
      · constructor
        · intro oldRoot oldValue oldImage
          exact ⟨expected_preserves_root_image heap changed oldRoot oldValue oldImage,
            expected_preserves_root_value heap changed oldRoot oldValue oldImage⟩
        · intro oldLeaf oldValue oldImage
          exact ⟨expected_preserves_leaf_image heap changed oldLeaf oldValue oldImage,
            expected_preserves_leaf_value heap changed oldLeaf oldValue oldImage⟩
    | error fault =>
      refine ⟨{ output := .error fault, receiver := root, heap := heap }, ?_, ?_, ?_, ?_⟩
      · simp only [commitOnlyOnOk, parentRead, hcb] <;> rfl
      · simp only [MatchesOutput, hcb] <;> rfl
      · intro res hok
        rw [hcb] at hok
        cases hok
      · constructor
        · intro oldRoot oldValue oldImage
          exact ⟨oldImage, root_image_read heap oldRoot oldValue oldImage⟩
        · intro oldLeaf oldValue oldImage
          exact ⟨oldImage, leaf_image_read heap oldLeaf oldValue oldImage⟩

theorem nested_satisfies_strong {E A : Type} :
    StrongContract (@nested (Except E A)) := by
  intro heap root value callback image
  refine ⟨expected heap (callback value).1 (callback value).2,
    nested_exact heap root value callback image, rfl, ?_, ?_, ?_⟩
  · intro _ _
    exact ⟨expected_root_image heap (callback value).1,
      expected_active_value heap (callback value).1⟩
  · intro _ _
    exact ⟨expected_root_image heap (callback value).1,
      expected_active_value heap (callback value).1⟩
  · constructor
    · intro oldRoot oldValue oldImage
      exact ⟨expected_preserves_root_image heap (callback value).1 oldRoot oldValue oldImage,
        expected_preserves_root_value heap (callback value).1 oldRoot oldValue oldImage⟩
    · intro oldLeaf oldValue oldImage
      exact ⟨expected_preserves_leaf_image heap (callback value).1 oldLeaf oldValue oldImage,
        expected_preserves_leaf_value heap (callback value).1 oldLeaf oldValue oldImage⟩

theorem strong_implies_active_and_alias {E A : Type} {op : CandidateOp E A}
    (strong : StrongContract op) :
    ActiveStrengthenedContract op ∧ AliasStrengthenedContract op := by
  constructor
  · intro heap root value callback image
    rcases strong heap root value callback image with
      ⟨actual, run, outEq, okAct, errAct, _⟩
    exact ⟨actual, run, outEq, okAct, errAct⟩
  · intro heap root value callback image
    rcases strong heap root value callback image with
      ⟨actual, run, outEq, okAct, _, aliases⟩
    exact ⟨actual, run, outEq, okAct, aliases⟩

theorem strong_implies_weak {E A : Type} {op : CandidateOp E A}
    (strong : StrongContract op) :
    WeakContract op := by
  intro heap root value callback image
  rcases strong heap root value callback image with
    ⟨actual, run, outEq, okAct, _, _⟩
  exact ⟨actual, run, outEq, okAct⟩

#print axioms nested_satisfies_weak
#print axioms commitOnlyOnOk_satisfies_weak
#print axioms overwriteInPlace_satisfies_weak
#print axioms overwriteInPlace_satisfies_activeStrengthened
#print axioms commitOnlyOnOk_satisfies_aliasStrengthened
#print axioms nested_satisfies_strong
#print axioms strong_implies_active_and_alias
#print axioms strong_implies_weak

end AnnealResearch.SpecValidation
