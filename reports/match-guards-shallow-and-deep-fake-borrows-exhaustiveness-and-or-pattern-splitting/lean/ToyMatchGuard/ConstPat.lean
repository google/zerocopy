/-
Constant patterns: structural lowering versus the type's `==`.

These are definitions of a toy model. `smatch c v` is meant to capture lowering a constant
pattern `c` to structural tests on a canonical value tree (compare the active variant, then the
fields, recursively; leaves are compared by bit pattern). `teq T` is meant to capture the
type's `PartialEq::eq`, which may be derived (structural composition of the field equalities) or
manual at each node, with IEEE-style equality on float leaves. These are not Rust's definitions.
-/

namespace Toy.MatchGuard.ConstPat

/-- Toy floating-point payloads; each constructor is a distinct bit pattern. -/
inductive F where
  | pzero
  | nzero
  | one
  | nan
  deriving DecidableEq, Repr

/-- IEEE-style equality on toy floats: `nan` equals nothing (not even itself) and the two zeros
are equal. -/
def F.ieeeEq : F → F → Bool
  | .nan, _ => false
  | _, .nan => false
  | .pzero, .nzero => true
  | .nzero, .pzero => true
  | a, b => decide (a = b)

/-- Canonical value trees: integers, floats, pairs (structs) and two-variant sums (enums). -/
inductive CVal where
  | int (n : Int)
  | flt (f : F)
  | pair (a b : CVal)
  | inl (a : CVal)
  | inr (a : CVal)
  deriving DecidableEq, Repr

/-- How a struct or enum node implements `==`: derived, or a manual function. -/
inductive EqImpl where
  | derived
  | manual (eq : CVal → CVal → Bool)

/-- Toy types: integers, floats, products and sums, each product or sum carrying its `==`
implementation. -/
inductive CTy where
  | int
  | flt
  | prod (impl : EqImpl) (A B : CTy)
  | sum (impl : EqImpl) (A B : CTy)

/-- Typing of value trees. -/
def HasTy : CVal → CTy → Prop
  | .int _, .int => True
  | .flt _, .flt => True
  | .pair a b, .prod _ A B => HasTy a A ∧ HasTy b B
  | .inl a, .sum _ A _ => HasTy a A
  | .inr b, .sum _ _ B => HasTy b B
  | _, _ => False

/-- The type's `==`: derived nodes compare the variant and then the fields with the fields'
`==`; manual nodes call their function; float leaves use IEEE-style equality. -/
def teq : CTy → CVal → CVal → Bool
  | .int, .int a, .int b => decide (a = b)
  | .flt, .flt a, .flt b => a.ieeeEq b
  | .prod .derived A B, .pair a1 b1, .pair a2 b2 => teq A a1 a2 && teq B b1 b2
  | .prod (.manual f) _ _, x, y => f x y
  | .sum .derived A _, .inl a1, .inl a2 => teq A a1 a2
  | .sum .derived _ B, .inr b1, .inr b2 => teq B b1 b2
  | .sum (.manual f) _ _, x, y => f x y
  | _, _, _ => false

/-- Structural lowering of a constant pattern `c` tested against a scrutinee `v`: compare the
active variant, then the fields, recursively; leaves by bit pattern. -/
def smatch : CVal → CVal → Bool
  | .int a, .int b => decide (a = b)
  | .flt a, .flt b => decide (a = b)
  | .pair a1 b1, .pair a2 b2 => smatch a1 a2 && smatch b1 b2
  | .inl a, .inl b => smatch a b
  | .inr a, .inr b => smatch a b
  | _, _ => false

/-- Every struct or enum node of the type has a derived `==`. -/
def AllDerived : CTy → Prop
  | .int | .flt => True
  | .prod .derived A B | .sum .derived A B => AllDerived A ∧ AllDerived B
  | .prod (.manual _) _ _ | .sum (.manual _) _ _ => False

/-- The type has no float leaf. -/
def NoFloat : CTy → Prop
  | .int => True
  | .flt => False
  | .prod _ A B | .sum _ A B => NoFloat A ∧ NoFloat B

/-- The structural lowering agrees with the type's `==` for every constant `c` and every
scrutinee `v` of the type. -/
def LoweringAgrees (T : CTy) : Prop := ∀ c v, HasTy c T → HasTy v T → smatch c v = teq T c v

/-! ### Lemmas -/

theorem smatch_refl : ∀ c : CVal, smatch c c = true
  | .int _ => by simp [smatch]
  | .flt _ => by simp [smatch]
  | .pair a b => by simp [smatch, smatch_refl a, smatch_refl b]
  | .inl a => by simp [smatch, smatch_refl a]
  | .inr a => by simp [smatch, smatch_refl a]

/-- A canonical inhabitant of each toy type. -/
def inhabit : CTy → CVal
  | .int => .int 0
  | .flt => .flt .pzero
  | .prod _ A B => .pair (inhabit A) (inhabit B)
  | .sum _ A _ => .inl (inhabit A)

theorem hasTy_inhabit : ∀ T : CTy, HasTy (inhabit T) T
  | .int => trivial
  | .flt => trivial
  | .prod _ A B => ⟨hasTy_inhabit A, hasTy_inhabit B⟩
  | .sum _ A _ => hasTy_inhabit A

theorem exists_teq_self_false_of_allDerived_of_not_noFloat : ∀ T : CTy, AllDerived T →
    ¬ NoFloat T → ∃ c, HasTy c T ∧ teq T c c = false
  | .int, _, h => absurd trivial h
  | .flt, _, _ => ⟨.flt .nan, trivial, rfl⟩
  | .prod impl A B, hd, hf => by
    cases impl with
    | manual f => exact hd.elim
    | derived =>
      by_cases hA : NoFloat A
      · have hB : ¬ NoFloat B := fun hB => hf ⟨hA, hB⟩
        obtain ⟨c, hc, he⟩ := exists_teq_self_false_of_allDerived_of_not_noFloat B hd.2 hB
        exact ⟨.pair (inhabit A) c, ⟨hasTy_inhabit A, hc⟩, by simp [teq, he]⟩
      · obtain ⟨c, hc, he⟩ := exists_teq_self_false_of_allDerived_of_not_noFloat A hd.1 hA
        exact ⟨.pair c (inhabit B), ⟨hc, hasTy_inhabit B⟩, by simp [teq, he]⟩
  | .sum impl A B, hd, hf => by
    cases impl with
    | manual f => exact hd.elim
    | derived =>
      by_cases hA : NoFloat A
      · have hB : ¬ NoFloat B := fun hB => hf ⟨hA, hB⟩
        obtain ⟨c, hc, he⟩ := exists_teq_self_false_of_allDerived_of_not_noFloat B hd.2 hB
        exact ⟨.inr c, hc, by simp [teq, he]⟩
      · obtain ⟨c, hc, he⟩ := exists_teq_self_false_of_allDerived_of_not_noFloat A hd.1 hA
        exact ⟨.inl c, hc, by simp [teq, he]⟩

/-! ### Results -/

theorem loweringAgrees_aux : ∀ (T : CTy), AllDerived T → NoFloat T → LoweringAgrees T
  | .int, _, _ => by
    intro c v hc hv
    cases c <;> cases v <;> simp_all [HasTy, smatch, teq]
  | .flt, _, hf => absurd hf id
  | .prod impl A B, hd, hf => by
    cases impl with
    | manual f => exact hd.elim
    | derived =>
      intro c v hc hv
      cases c <;> cases v <;> simp only [HasTy] at hc hv <;> try (exact hc.elim) <;>
        try (exact hv.elim)
      rename_i a1 b1 a2 b2
      simp only [smatch, teq]
      rw [loweringAgrees_aux A hd.1 hf.1 a1 a2 hc.1 hv.1,
        loweringAgrees_aux B hd.2 hf.2 b1 b2 hc.2 hv.2]
  | .sum impl A B, hd, hf => by
    cases impl with
    | manual f => exact hd.elim
    | derived =>
      intro c v hc hv
      cases c <;> cases v <;> simp only [HasTy] at hc hv <;> try (exact hc.elim) <;>
        try (exact hv.elim)
      · rename_i a1 a2
        simp only [smatch, teq]
        exact loweringAgrees_aux A hd.1 hf.1 a1 a2 hc hv
      · simp [smatch, teq]
      · simp [smatch, teq]
      · rename_i b1 b2
        simp only [smatch, teq]
        exact loweringAgrees_aux B hd.2 hf.2 b1 b2 hc hv

/-- **Structural lowering agrees with derived equality on float-free types.** For every toy type
`T` whose struct and enum nodes all have a derived `==` (`AllDerived T`) and which has no float
leaf (`NoFloat T`), for every constant `c` and every scrutinee `v` of type `T`,
`smatch c v = teq T c v`. -/
theorem loweringAgrees_of_allDerived_of_noFloat (T : CTy) (hd : AllDerived T) (hf : NoFloat T) :
    LoweringAgrees T :=
  loweringAgrees_aux T hd hf

/-- **Characterization among derived types.** For every toy type `T` whose struct and enum nodes
all have a derived `==` (`AllDerived T`), the structural lowering agrees with `teq T` for every
constant and scrutinee of type `T` (`LoweringAgrees T`) iff `T` has no float leaf. -/
theorem loweringAgrees_iff_noFloat_of_allDerived (T : CTy) (hd : AllDerived T) :
    LoweringAgrees T ↔ NoFloat T := by
  constructor
  · intro hag
    by_cases hf : NoFloat T
    · exact hf
    · obtain ⟨c, hc, he⟩ := exists_teq_self_false_of_allDerived_of_not_noFloat T hd hf
      have := hag c c hc hc
      rw [smatch_refl, he] at this
      cases this
  · exact loweringAgrees_of_allDerived_of_noFloat T hd

/-! ### Instances -/

/-- A manual `==` on a two-variant enum of integers that compares payloads and ignores the
variant (it identifies `inl n` with `inr n`). -/
def payloadEq : CVal → CVal → Bool
  | .inl (.int a), .inl (.int b) | .inl (.int a), .inr (.int b)
  | .inr (.int a), .inl (.int b) | .inr (.int a), .inr (.int b) => decide (a = b)
  | _, _ => false

/-- An enum of two integer variants whose `==` is `payloadEq`. -/
def manualVariantTy : CTy := .sum (.manual payloadEq) .int .int

/-- A struct `(i32, E)` with derived `==`, where `E` is `manualVariantTy`. -/
def nestedManualTy : CTy := .prod .derived .int manualVariantTy

/-- An enum of two integer variants whose manual `==` happens to be structural. -/
def manualStructuralTy : CTy := .sum (.manual smatch) .int .int

/-- **Counterexample (derived `==`).** `manualVariantTy` has no float leaf but a manual `==`
(`AllDerived` fails), and `LoweringAgrees` fails for it: for the constant `inl 0` and the
scrutinee `inr 0` (both of that type), the structural lowering says "no match" and `==` says
"equal". -/
theorem manualVariantTy_noFloat_and_lowering_disagrees :
    NoFloat manualVariantTy ∧ ¬ AllDerived manualVariantTy ∧ ¬ LoweringAgrees manualVariantTy ∧
      HasTy (.inl (.int 0)) manualVariantTy ∧ HasTy (.inr (.int 0)) manualVariantTy ∧
      smatch (.inl (.int 0)) (.inr (.int 0)) = false ∧
      teq manualVariantTy (.inl (.int 0)) (.inr (.int 0)) = true := by
  refine ⟨⟨trivial, trivial⟩, id, ?_, trivial, trivial, rfl, rfl⟩
  intro h
  have := h (.inl (.int 0)) (.inr (.int 0)) trivial trivial
  revert this; decide

/-- **Counterexample (derived at every level).** `nestedManualTy` has a derived `==` at the top,
no float leaf, and a manual `==` one level down; for the constant `(0, inl 0)` and the scrutinee
`(0, inr 0)` the lowering and `==` disagree. -/
theorem nestedManualTy_lowering_disagrees :
    NoFloat nestedManualTy ∧ ¬ AllDerived nestedManualTy ∧
      HasTy (.pair (.int 0) (.inl (.int 0))) nestedManualTy ∧
      HasTy (.pair (.int 0) (.inr (.int 0))) nestedManualTy ∧
      smatch (.pair (.int 0) (.inl (.int 0))) (.pair (.int 0) (.inr (.int 0))) = false ∧
      teq nestedManualTy (.pair (.int 0) (.inl (.int 0))) (.pair (.int 0) (.inr (.int 0))) = true :=
  ⟨⟨trivial, trivial, trivial⟩, fun h => h.2, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, rfl, rfl⟩

/-- **Counterexample (no float, NaN).** The float type satisfies `AllDerived` (its `==` is the
IEEE-style leaf equality), has a float leaf (`NoFloat` fails), and `LoweringAgrees` fails for it:
for the constant `nan` and the scrutinee `nan` (same bit pattern) the structural lowering matches
and `==` says "not equal". -/
theorem flt_allDerived_and_lowering_disagrees_nan :
    AllDerived .flt ∧ ¬ NoFloat .flt ∧ ¬ LoweringAgrees .flt ∧
      smatch (.flt .nan) (.flt .nan) = true ∧ teq .flt (.flt .nan) (.flt .nan) = false := by
  refine ⟨trivial, id, ?_, rfl, rfl⟩
  intro h
  have := h (.flt .nan) (.flt .nan) trivial trivial
  revert this; decide

/-- **Counterexample (no float, signed zero).** For the non-NaN constant `+0` and the scrutinee
`-0` the structural (bitwise) lowering says "no match" and `==` says "equal". -/
theorem flt_lowering_disagrees_signedZero :
    smatch (.flt .pzero) (.flt .nzero) = false ∧ teq .flt (.flt .pzero) (.flt .nzero) = true :=
  ⟨rfl, rfl⟩

/-- **Positive control (the marker is not necessary).** `manualStructuralTy` has a manual `==`
(so `AllDerived` fails) and the structural lowering nevertheless agrees with its `==` for every
constant and scrutinee of the type. -/
theorem manualStructuralTy_loweringAgrees_and_not_allDerived :
    LoweringAgrees manualStructuralTy ∧ ¬ AllDerived manualStructuralTy := by
  refine ⟨?_, id⟩
  intro c v _ _
  rfl

/-- **Non-vacuity.** The struct `(i32, Option<i32>)`-like type with derived `==` everywhere
satisfies `AllDerived` and `NoFloat`, and has a value. -/
def derivedTy : CTy := .prod .derived .int (.sum .derived .int .int)

theorem derivedTy_allDerived_noFloat :
    AllDerived derivedTy ∧ NoFloat derivedTy ∧ HasTy (.pair (.int 1) (.inr (.int 2))) derivedTy :=
  ⟨⟨trivial, trivial, trivial⟩, ⟨trivial, trivial, trivial⟩, ⟨trivial, trivial⟩⟩

/-! ### Agreement for one fixed constant -/

/-- Whether a value tree contains a `nan` leaf. -/
def HasNan : CVal → Prop
  | .int _ => False
  | .flt f => f = .nan
  | .pair a b => HasNan a ∨ HasNan b
  | .inl a | .inr a => HasNan a

/-- Every float leaf of the value tree is `one` (no `nan`, `+0` or `-0` leaf). -/
def NoNanNoZeroLeaf : CVal → Prop
  | .int _ => True
  | .flt f => f = .one
  | .pair a b => NoNanNoZeroLeaf a ∧ NoNanNoZeroLeaf b
  | .inl a | .inr a => NoNanNoZeroLeaf a

/-- Swaps the two zero leaves (`+0` with `-0`) everywhere in a value tree. -/
def flipZeros : CVal → CVal
  | .int n => .int n
  | .flt .pzero => .flt .nzero
  | .flt .nzero => .flt .pzero
  | .flt f => .flt f
  | .pair a b => .pair (flipZeros a) (flipZeros b)
  | .inl a => .inl (flipZeros a)
  | .inr a => .inr (flipZeros a)

theorem smatch_eq_decide (c v : CVal) : smatch c v = decide (c = v) := by
  induction c generalizing v with
  | int a => cases v <;> simp [smatch]
  | flt a => cases v <;> simp [smatch]
  | pair a1 b1 iha ihb => cases v <;> simp [smatch, iha, ihb]
  | inl a iha => cases v <;> simp [smatch, iha]
  | inr a iha => cases v <;> simp [smatch, iha]

theorem hasTy_flipZeros (T : CTy) (c : CVal) (hc : HasTy c T) : HasTy (flipZeros c) T := by
  induction T generalizing c with
  | int => cases c <;> simp_all [HasTy, flipZeros]
  | flt =>
    cases c <;> simp only [HasTy] at hc <;> try (exact hc.elim)
    rename_i f
    cases f <;> trivial
  | prod _ A B ihA ihB =>
    cases c <;> try (exact hc.elim)
    exact ⟨ihA _ hc.1, ihB _ hc.2⟩
  | sum _ A B ihA ihB =>
    cases c <;> try (exact hc.elim)
    · exact ihA _ hc
    · exact ihB _ hc

theorem teq_self_false_of_hasNan (T : CTy) (c : CVal) (hd : AllDerived T) (hc : HasTy c T)
    (hn : HasNan c) : teq T c c = false := by
  induction T generalizing c with
  | int => cases c <;> simp_all [HasTy, HasNan]
  | flt =>
    cases c <;> try (exact hc.elim)
    rename_i f; cases f <;> simp [HasNan] at hn <;> rfl
  | prod impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      rcases hn with hn | hn
      · simp [teq, ihA _ hd.1 hc.1 hn]
      · simp [teq, ihB _ hd.2 hc.2 hn]
  | sum impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      · exact ihA _ hd.1 hc hn
      · exact ihB _ hd.2 hc hn

theorem teq_flipZeros_of_not_hasNan (T : CTy) (c : CVal) (hd : AllDerived T) (hc : HasTy c T)
    (hn : ¬ HasNan c) : teq T c (flipZeros c) = true := by
  induction T generalizing c with
  | int => cases c <;> simp_all [HasTy, flipZeros, teq]
  | flt =>
    cases c <;> try (exact hc.elim)
    rename_i f; cases f <;> simp [HasNan] at hn <;> rfl
  | prod impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      simp [flipZeros, teq,
        ihA _ hd.1 hc.1 (fun h => hn (Or.inl h)),
        ihB _ hd.2 hc.2 (fun h => hn (Or.inr h))]
  | sum impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      · exact ihA _ hd.1 hc hn
      · exact ihB _ hd.2 hc hn

theorem ne_flipZeros_of_not_hasNan_of_not_noNanNoZeroLeaf (c : CVal) (hn : ¬ HasNan c)
    (hcs : ¬ NoNanNoZeroLeaf c) : c ≠ flipZeros c := by
  induction c with
  | int _ => exact absurd trivial hcs
  | flt f => cases f <;> simp [HasNan, NoNanNoZeroLeaf] at hn hcs <;> decide
  | pair a b iha ihb =>
    by_cases ha : NoNanNoZeroLeaf a
    · have hb : ¬ NoNanNoZeroLeaf b := fun hb => hcs ⟨ha, hb⟩
      have hne := ihb (fun h => hn (Or.inr h)) hb
      intro e; exact hne (CVal.pair.inj e).2
    · have hne := iha (fun h => hn (Or.inl h)) ha
      intro e; exact hne (CVal.pair.inj e).1
  | inl a iha =>
    have hne := iha hn hcs
    intro e; exact hne (CVal.inl.inj e)
  | inr a iha =>
    have hne := iha hn hcs
    intro e; exact hne (CVal.inr.inj e)

theorem smatch_eq_teq_of_allDerived_of_noNanNoZeroLeaf (T : CTy) (c v : CVal) (hd : AllDerived T)
    (hc : HasTy c T) (hv : HasTy v T) (hcs : NoNanNoZeroLeaf c) : smatch c v = teq T c v := by
  induction T generalizing c v with
  | int =>
    cases c <;> try (exact hc.elim)
    cases v <;> try (exact hv.elim)
    rfl
  | flt =>
    cases c <;> try (exact hc.elim)
    cases v <;> try (exact hv.elim)
    rename_i fc fv
    cases fc <;> simp [NoNanNoZeroLeaf] at hcs
    cases fv <;> rfl
  | prod impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      cases v <;> try (exact hv.elim)
      simp only [smatch, teq]
      rw [ihA _ _ hd.1 hc.1 hv.1 hcs.1, ihB _ _ hd.2 hc.2 hv.2 hcs.2]
  | sum impl A B ihA ihB =>
    cases impl with
    | manual _ => exact hd.elim
    | derived =>
      cases c <;> try (exact hc.elim)
      · cases v <;> try (exact hv.elim)
        · exact ihA _ _ hd.1 hc hv hcs
        · rfl
      · cases v <;> try (exact hv.elim)
        · rfl
        · exact ihB _ _ hd.2 hc hv hcs

/-- **Agreement for one fixed constant.** For every toy type `T` with `AllDerived T` and every
constant `c` of type `T`, the structural lowering of `c` agrees with `teq T c` on every scrutinee
of type `T` iff every float leaf of `c` is `one` (`c` has no `nan`, `+0` or `-0` leaf). -/
theorem smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived {T : CTy} {c : CVal}
    (hd : AllDerived T) (hc : HasTy c T) :
    (∀ v, HasTy v T → smatch c v = teq T c v) ↔ NoNanNoZeroLeaf c := by
  constructor
  · intro hag
    by_cases hcs : NoNanNoZeroLeaf c
    · exact hcs
    · exfalso
      by_cases hn : HasNan c
      · have h := hag c hc
        rw [smatch_refl, teq_self_false_of_hasNan T c hd hc hn] at h
        cases h
      · have h := hag (flipZeros c) (hasTy_flipZeros T c hc)
        rw [smatch_eq_decide, teq_flipZeros_of_not_hasNan T c hd hc hn] at h
        exact ne_flipZeros_of_not_hasNan_of_not_noNanNoZeroLeaf c hn hcs (of_decide_eq_true h)
  · exact fun hcs v hv => smatch_eq_teq_of_allDerived_of_noNanNoZeroLeaf T c v hd hc hv hcs

/-- Example (agreement for one fixed constant on a type with a float leaf): the type
`Option<f32>`-like `.sum .derived .int .flt` has a float leaf, and the constant `inl 0` (`None`)
nevertheless agrees with `==` on every scrutinee of that type. -/
theorem optFlt_none_agrees :
    ¬ NoFloat (.sum .derived .int .flt) ∧
      ∀ v, HasTy v (.sum .derived .int .flt) →
        smatch (.inl (.int 0)) v = teq (.sum .derived .int .flt) (.inl (.int 0)) v :=
  ⟨fun h => h.2, (smatch_agrees_with_teq_iff_noNanNoZeroLeaf_of_allDerived
    (T := .sum .derived .int .flt) (c := .inl (.int 0)) ⟨trivial, trivial⟩ trivial).mpr trivial⟩

/-! ### Definition examples -/

/-- Positive example (`AllDerived`). -/
theorem allDerived_example : AllDerived derivedTy := ⟨trivial, trivial, trivial⟩
/-- Negative example (`AllDerived`). -/
theorem not_allDerived_example : ¬ AllDerived manualVariantTy := id
/-- Positive example (`NoFloat`). -/
theorem noFloat_example : NoFloat derivedTy := ⟨trivial, trivial, trivial⟩
/-- Negative example (`NoFloat`). -/
theorem not_noFloat_example : ¬ NoFloat (.prod .derived .int .flt) := fun h => h.2
/-- Positive example (`HasTy`). -/
theorem hasTy_example : HasTy (.inl (.int 3)) manualVariantTy := trivial
/-- Negative example (`HasTy`). -/
theorem not_hasTy_example : ¬ HasTy (.flt .one) manualVariantTy := id
/-- Positive example (`smatch`): same variant and fields. -/
theorem smatch_example : smatch (.inr (.int 2)) (.inr (.int 2)) = true := rfl
/-- Negative example (`smatch`): different variants. -/
theorem smatch_example_false : smatch (.inl (.int 2)) (.inr (.int 2)) = false := rfl
/-- Positive example (`LoweringAgrees`). -/
theorem loweringAgrees_example : LoweringAgrees derivedTy :=
  loweringAgrees_of_allDerived_of_noFloat _ derivedTy_allDerived_noFloat.1
    derivedTy_allDerived_noFloat.2.1
/-- Negative example (`LoweringAgrees`). -/
theorem not_loweringAgrees_example : ¬ LoweringAgrees manualVariantTy := by
  intro h
  have := h (.inl (.int 0)) (.inr (.int 0)) trivial trivial
  revert this; decide

/-- **Counterexample (all-derived hypothesis of the characterization).** `manualVariantTy` is not
all-derived, has no float leaf, and the structural lowering does not agree with its `==`; so
`LoweringAgrees ↔ NoFloat` fails for it. -/
theorem manualVariantTy_not_allDerived_and_iff_fails :
    ¬ AllDerived manualVariantTy ∧ ¬ (LoweringAgrees manualVariantTy ↔ NoFloat manualVariantTy) := by
  refine ⟨id, ?_⟩
  intro h
  exact not_loweringAgrees_example (h.mpr ⟨trivial, trivial⟩)

end Toy.MatchGuard.ConstPat
