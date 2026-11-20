import Toy.Codec.Defs

/-!
# Positive and negative examples for every core definition

Every definition in `Toy.Codec.Defs` is exercised here with at least one fully
proved positive example (an intended instance it admits) and at least one fully
proved negative example (an instance it must reject).
-/

namespace Toy.Codec

/-! ## Concrete reference codecs and helper maps -/

/-- A lawful, non-surjective codec `Bool → Nat` encoding `false ↦ 0`, `true ↦ 1`,
    and rejecting every `n ≥ 2` as junk. -/
def boolToNatCodec : Codec Bool Nat where
  enc
    | false => 0
    | true => 1
  dec
    | 0 => some false
    | 1 => some true
    | _ + 2 => none

/-- A lawful, non-surjective codec `Nat → Nat` shifting by `+1` (rejecting `0` as junk). -/
def natSuccCodec : Codec Nat Nat where
  enc n := n + 1
  dec
    | 0 => none
    | n + 1 => some n

/-- A malleable codec `Bool → Nat` satisfying `DecEnc` but violating `EncDec` and `DecInj`:
    both `1` and `2` decode to `true`, while `enc true = 1` and `n ≥ 3` is rejected. -/
def nonCanonicalBoolCodec : Codec Bool Nat where
  enc
    | false => 0
    | true => 1
  dec
    | 0 => some false
    | 1 => some true
    | 2 => some true
    | _ + 3 => none

/-- An always-failing codec on `Bool`: satisfies `EncDec` and `DecInj` vacuously,
    but rejects every encoded value (`¬ DecEnc`). -/
def alwaysFailBoolCodec : Codec Bool Bool where
  enc b := b
  dec _ := none

/-- An always-failing codec with a non-injective encoder `Bool → Unit`:
    satisfies `EncDec`, yet `enc` is not injective. -/
def alwaysFailConstCodec : Codec Bool Unit where
  enc _ := ()
  dec _ := none

/-- A codec whose decoder is injective (`DecInj`) and surjective, yet disagrees
    with `enc`: violates both `DecEnc` and `EncDec`. -/
def shiftedBoolCodec : Codec Bool Bool where
  enc b := b
  dec b := some (!b)

/-- A minimal malleable codec `Unit → Bool` with empty `Junk`:
    `enc () = false`, `dec _ = some ()`. -/
def malleableUnitBoolCodec : Codec Unit Bool where
  enc _ := false
  dec _ := some ()

/-- A minimal always-failing codec `Unit → Unit`:
    `enc () = ()`, `dec () = none`. -/
def alwaysFailUnitCodec : Codec Unit Unit where
  enc _ := ()
  dec _ := none

/-- Variable-length prefix-free framed codec `Bool → List Bool`:
    `false ↦ [false]`, `true ↦ [true, true]`; rejects `[true]` and `[true, false]`. -/
def varLenBoolFramedCodec : FramedCodec Bool Bool where
  enc
    | false => [false]
    | true => [true, true]
  decPrefix
    | false :: rest => some (false, rest)
    | true :: true :: rest => some (true, rest)
    | _ => none

/-- Always-failing framed codec `Unit → List Bool` with non-empty encoding `[false]`. -/
def alwaysFailFramedCodec : FramedCodec Unit Bool where
  enc _ := [false]
  decPrefix _ := none

/-- Malleable framed codec `Unit → List Bool` with `enc () = [false]` that also
    accepts leading `true` as `()`. Satisfies `PrefixDecEnc` and `NonEmptyEnc`,
    but violates `PrefixEncDec`. -/
def malleableFramedCodec : FramedCodec Unit Bool where
  enc _ := [false]
  decPrefix
    | _ :: rest => some ((), rest)
    | [] => none

/-- Lawful framed codec on `Unit` whose codeword is the empty list `[]`.
    Satisfies `PrefixDecEnc`, `PrefixEncDec`, and `PrefixFree`, but violates `NonEmptyEnc`
    and causes `listCodec` to fail `DecEnc`. -/
def emptyUnitFramedCodec : FramedCodec Unit Bool where
  enc _ := []
  decPrefix rest := some ((), rest)

/-- Injective, non-empty, non-prefix-free encoding `Bool → List Bool`:
    `false ↦ [false]`, `true ↦ [false, false]`. -/
def ambiguousEnc : Bool → List Bool
  | false => [false]
  | true => [false, false]

/-- A fully lawful single-value codec (`DecEnc ∧ EncDec`) whose encoder `ambiguousEnc`
    is injective and non-empty, yet not prefix-free. -/
def ambiguousCodec : Codec Bool (List Bool) where
  enc := ambiguousEnc
  dec
    | [false] => some false
    | [false, false] => some true
    | _ => none

/-- An always-failing framed codec using `ambiguousEnc`. Satisfies `PrefixEncDec`
    and `NonEmptyEnc`, but violates `PrefixDecEnc` and `PrefixFree`. -/
def ambiguousFailFramedCodec : FramedCodec Bool Bool where
  enc := ambiguousEnc
  decPrefix _ := none

/-! ## Examples for `LeftInv`, `RightInv`, `IsEquiv`, `Equiv` -/

theorem ex_leftInv_pos : LeftInv (fun b : Bool => !b) (fun b : Bool => !b) := by
  intro b; cases b <;> rfl

theorem ex_leftInv_neg : ¬ LeftInv (fun _ : Bool => ()) (fun _ : Unit => false) := by
  intro h
  have htrue := h true
  cases htrue

theorem ex_rightInv_pos : RightInv (fun b : Bool => !b) (fun b : Bool => !b) := by
  intro b; cases b <;> rfl

theorem ex_rightInv_neg : ¬ RightInv (fun _ : Unit => false) (fun _ : Bool => ()) := by
  intro h
  have htrue := h true
  cases htrue

theorem ex_isEquiv_pos : IsEquiv (fun b : Bool => !b) (fun b : Bool => !b) :=
  ⟨ex_leftInv_pos, ex_rightInv_pos⟩

theorem ex_isEquiv_neg : ¬ IsEquiv (fun _ : Bool => ()) (fun _ : Unit => false) := by
  intro h
  exact ex_leftInv_neg h.1

/-- Positive example of `Equiv`: Boolean negation `Bool ≃ Bool`. -/
def boolNotEquiv : Equiv Bool Bool where
  toFun b := !b
  invFun b := !b
  left_inv := ex_leftInv_pos
  right_inv := ex_rightInv_pos

theorem ex_equiv_pos : Nonempty (Equiv Bool Bool) := ⟨boolNotEquiv⟩

theorem ex_equiv_neg : ¬ Nonempty (Equiv Bool Unit) := by
  rintro ⟨e⟩
  have h1 : e.invFun (e.toFun false) = false := e.left_inv false
  have h2 : e.invFun (e.toFun true) = true := e.left_inv true
  have hu : e.toFun false = e.toFun true := Subsingleton.elim _ _
  rw [hu] at h1
  rw [h1] at h2
  cases h2

/-! ## Examples for `DecEnc`, `EncDec`, `DecInj`, `Lawful`, `canonicalize` -/

theorem boolToNatCodec_decEnc : DecEnc boolToNatCodec := by
  intro a; cases a <;> rfl

theorem boolToNatCodec_encDec : EncDec boolToNatCodec := by
  intro b a h
  match b with
  | 0 => cases h; rfl
  | 1 => cases h; rfl
  | _ + 2 => cases h

theorem boolToNatCodec_decInj : DecInj boolToNatCodec := by
  intro b₁ b₂ a h₁ h₂
  have e₁ := boolToNatCodec_encDec b₁ a h₁
  have e₂ := boolToNatCodec_encDec b₂ a h₂
  exact e₁.symm.trans e₂

theorem boolToNatCodec_lawful : Lawful boolToNatCodec :=
  ⟨boolToNatCodec_decEnc, boolToNatCodec_encDec⟩

theorem natSuccCodec_decEnc : DecEnc natSuccCodec := by
  intro n; rfl

theorem natSuccCodec_encDec : EncDec natSuccCodec := by
  intro b a h
  cases b with
  | zero => cases h
  | succ k => cases h; rfl

theorem natSuccCodec_lawful : Lawful natSuccCodec :=
  ⟨natSuccCodec_decEnc, natSuccCodec_encDec⟩

theorem ex_decEnc_pos : DecEnc boolToNatCodec := boolToNatCodec_decEnc

theorem ex_decEnc_neg : ¬ DecEnc alwaysFailBoolCodec := by
  intro h
  have h0 := h false
  cases h0

theorem ex_encDec_pos : EncDec boolToNatCodec := boolToNatCodec_encDec

theorem ex_encDec_neg : ¬ EncDec nonCanonicalBoolCodec := by
  intro h
  have h2 : nonCanonicalBoolCodec.enc true = 2 := h 2 true rfl
  cases h2

theorem ex_decInj_pos : DecInj boolToNatCodec := boolToNatCodec_decInj

theorem ex_decInj_neg : ¬ DecInj nonCanonicalBoolCodec := by
  intro h
  have h12 : (1 : Nat) = 2 := h 1 2 true rfl rfl
  cases h12

theorem ex_lawful_pos : Lawful boolToNatCodec := boolToNatCodec_lawful

theorem ex_lawful_neg_malleable : ¬ Lawful nonCanonicalBoolCodec := by
  intro h; exact ex_encDec_neg h.2

theorem ex_lawful_neg_failing : ¬ Lawful alwaysFailBoolCodec := by
  intro h; exact ex_decEnc_neg h.1

theorem ex_canonicalize_pos :
    Lawful (canonicalize nonCanonicalBoolCodec) ∧
    (canonicalize nonCanonicalBoolCodec).dec 1 = some true ∧
    (canonicalize nonCanonicalBoolCodec).dec 2 = none := by
  refine ⟨⟨?_, ?_⟩, rfl, rfl⟩
  · intro a; cases a <;> rfl
  · intro b a h
    unfold canonicalize at h
    dsimp only at h
    split at h
    · split at h
      · rename_i he; cases h; exact he
      · cases h
    · cases h

theorem ex_canonicalize_neg : ¬ DecEnc (canonicalize alwaysFailBoolCodec) := by
  intro h
  have hf := h false
  cases hf

/-! ## Examples for `classicalDec`, `classicalCodec`, `FiberSplit`, `codecOfFiberSplit`, `fiberSplitOfLawful` -/

theorem ex_classicalCodec_pos :
    (classicalCodec boolToNatCodec.enc).dec 1 = some true ∧
    (classicalCodec boolToNatCodec.enc).dec 2 = none := by
  constructor
  · unfold classicalCodec classicalDec
    dsimp only
    split
    · rename_i h1
      have hspec := Classical.choose_spec h1
      cases hc : Classical.choose h1 with
      | true => rfl
      | false => rw [hc] at hspec; cases hspec
    · rename_i hn
      exact absurd ⟨true, rfl⟩ hn
  · unfold classicalCodec classicalDec
    dsimp only
    split
    · rename_i h2
      rcases h2 with ⟨a, ha⟩
      cases a <;> cases ha
    · rfl

theorem ex_classicalCodec_neg : ¬ DecEnc (classicalCodec (fun _ : Bool => ())) := by
  intro h
  have hf := h false
  have ht := h true
  change classicalDec (fun _ : Bool => ()) () = some false at hf
  change classicalDec (fun _ : Bool => ()) () = some true at ht
  rw [hf] at ht
  cases ht

/-- Computable `FiberSplit` for `boolToNatCodec.enc`. -/
def boolToNatFiberSplit : FiberSplit boolToNatCodec.enc
  | 0 => PSum.inl ⟨false, rfl⟩
  | 1 => PSum.inl ⟨true, rfl⟩
  | _ + 2 => PSum.inr (fun a h => by cases a <;> cases h)

theorem ex_fiberSplit_pos : Lawful (codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit) := by
  constructor
  · intro a; cases a <;> rfl
  · intro b a h
    match b with
    | 0 => cases h; rfl
    | 1 => cases h; rfl
    | _ + 2 => cases h

/-- A `FiberSplit` for the non-injective function `fun _ : Bool => ()`. -/
def constUnitFiberSplit : FiberSplit (fun _ : Bool => ())
  | () => PSum.inl ⟨false, rfl⟩

theorem ex_fiberSplit_neg_nonInjective :
    ¬ DecEnc (codecOfFiberSplit (fun _ : Bool => ()) constUnitFiberSplit) := by
  intro h
  have ht := h true
  cases ht

theorem ex_fiberSplitOfLawful_pos :
    fiberSplitOfLawful boolToNatCodec boolToNatCodec_decEnc boolToNatCodec_encDec 1 =
      PSum.inl ⟨true, rfl⟩ ∧
    (match fiberSplitOfLawful boolToNatCodec boolToNatCodec_decEnc boolToNatCodec_encDec 2 with
     | PSum.inl _ => false
     | PSum.inr _ => true) = true :=
  ⟨rfl, rfl⟩

theorem ex_fiberSplitOfLawful_neg :
    ¬ ∃ s : FiberSplit alwaysFailBoolCodec.enc,
        (codecOfFiberSplit alwaysFailBoolCodec.enc s).dec false = alwaysFailBoolCodec.dec false := by
  rintro ⟨s, hs⟩
  unfold codecOfFiberSplit alwaysFailBoolCodec at hs
  dsimp only at hs
  split at hs
  · cases hs
  · rename_i hn _; exact hn false rfl

/-! ## Examples for `Codec.id`, `Codec.comp`, `Codec.prod`, `Codec.sum` -/

theorem codecId_decEnc (A : Type u) : DecEnc (Codec.id A) := fun _ => rfl
theorem codecId_encDec (A : Type u) : EncDec (Codec.id A) := fun _ _ h => by cases h; rfl
theorem codecId_lawful (A : Type u) : Lawful (Codec.id A) := ⟨codecId_decEnc A, codecId_encDec A⟩

theorem ex_codecId_neg : (Codec.id Bool).dec false ≠ some true := by
  intro h; cases h

theorem ex_comp_pos : Lawful (boolToNatCodec.comp natSuccCodec) := by
  constructor
  · intro a; cases a <;> rfl
  · intro b a h
    match b with
    | 0 => cases h
    | 1 => cases h; rfl
    | 2 => cases h; rfl
    | _ + 3 => cases h

theorem ex_comp_neg : ¬ DecEnc (alwaysFailBoolCodec.comp (Codec.id Bool)) := by
  intro h
  have hf := h false
  cases hf

theorem ex_prod_pos : Lawful (boolToNatCodec.prod (Codec.id Bool)) := by
  constructor
  · rintro ⟨a₁, a₂⟩; cases a₁ <;> rfl
  · rintro ⟨b₁, b₂⟩ ⟨a₁, a₂⟩ h
    match b₁ with
    | 0 => cases h; rfl
    | 1 => cases h; rfl
    | _ + 2 => cases h

theorem ex_prod_neg : ¬ EncDec (nonCanonicalBoolCodec.prod (Codec.id Bool)) := by
  intro h
  have h2 := h (2, false) (true, false) rfl
  cases h2

theorem ex_sum_pos : Lawful (boolToNatCodec.sum (Codec.id Bool)) := by
  constructor
  · rintro (a₁ | a₂)
    · cases a₁ <;> rfl
    · rfl
  · rintro (b₁ | b₂) a h
    · match b₁ with
      | 0 => cases h; rfl
      | 1 => cases h; rfl
      | _ + 2 => cases h
    · cases h; rfl

theorem ex_sum_neg : ¬ DecEnc (alwaysFailBoolCodec.sum (Codec.id Bool)) := by
  intro h
  have hf := h (Sum.inl false)
  cases hf

/-! ## Examples for framed codecs, sequencing, and codeword properties -/

theorem varLenBoolFramedCodec_prefixDecEnc : PrefixDecEnc varLenBoolFramedCodec := by
  intro a rest; cases a <;> rfl

theorem varLenBoolFramedCodec_prefixEncDec : PrefixEncDec varLenBoolFramedCodec := by
  intro xs a rest h
  match xs with
  | [] => cases h
  | false :: t => cases h; rfl
  | true :: [] => cases h
  | true :: false :: _ => cases h
  | true :: true :: t => cases h; rfl

theorem varLenBoolFramedCodec_prefixFree : PrefixFree varLenBoolFramedCodec.enc := by
  intro a₁ a₂ s h
  cases a₁ <;> cases a₂ <;> cases h <;> rfl

theorem varLenBoolFramedCodec_imagePrefixFree : ImagePrefixFree varLenBoolFramedCodec.enc := by
  intro a₁ a₂ s h
  cases a₁ <;> cases a₂ <;> cases s <;> cases h <;> rfl

theorem varLenBoolFramedCodec_nonEmptyEnc : NonEmptyEnc varLenBoolFramedCodec.enc := by
  intro a; cases a <;> intro h <;> cases h

theorem ex_prefixDecEnc_pos : PrefixDecEnc varLenBoolFramedCodec :=
  varLenBoolFramedCodec_prefixDecEnc

theorem ex_prefixDecEnc_neg : ¬ PrefixDecEnc alwaysFailFramedCodec := by
  intro h
  have h0 := h () []
  cases h0

theorem ex_prefixEncDec_pos : PrefixEncDec varLenBoolFramedCodec :=
  varLenBoolFramedCodec_prefixEncDec

theorem ex_prefixEncDec_neg : ¬ PrefixEncDec malleableFramedCodec := by
  intro h
  have h1 := h [true] () [] rfl
  cases h1

theorem ex_seq_pos :
    PrefixDecEnc (varLenBoolFramedCodec.seq varLenBoolFramedCodec) ∧
    PrefixEncDec (varLenBoolFramedCodec.seq varLenBoolFramedCodec) := by
  constructor
  · rintro ⟨a₁, a₂⟩ rest
    cases a₁ <;> cases a₂ <;> rfl
  · intro xs p rest h
    unfold FramedCodec.seq at h
    dsimp only at h
    cases h₁ : varLenBoolFramedCodec.decPrefix xs with
    | none => rw [h₁] at h; cases h
    | some p₁ =>
      obtain ⟨a₁, rest₁⟩ := p₁
      rw [h₁] at h
      dsimp only at h
      cases h₂ : varLenBoolFramedCodec.decPrefix rest₁ with
      | none => rw [h₂] at h; cases h
      | some p₂ =>
        obtain ⟨a₂, rest₂⟩ := p₂
        rw [h₂] at h
        cases h
        have e₁ := varLenBoolFramedCodec_prefixEncDec xs a₁ rest₁ h₁
        have e₂ := varLenBoolFramedCodec_prefixEncDec rest₁ a₂ rest h₂
        rw [e₁, e₂, ← List.append_assoc]
        rfl

theorem ex_seq_neg :
    ¬ PrefixDecEnc (alwaysFailFramedCodec.seq varLenBoolFramedCodec) := by
  intro h
  have h0 := h ((), false) []
  cases h0

theorem ex_prefixFree_pos : PrefixFree varLenBoolFramedCodec.enc :=
  varLenBoolFramedCodec_prefixFree

theorem ex_prefixFree_neg : ¬ PrefixFree ambiguousEnc := by
  intro h
  have hft : false = true := h false true [false] rfl
  cases hft

theorem ex_imagePrefixFree_pos : ImagePrefixFree varLenBoolFramedCodec.enc :=
  varLenBoolFramedCodec_imagePrefixFree

theorem ex_imagePrefixFree_neg : ¬ ImagePrefixFree ambiguousEnc := by
  intro h
  have hs : [false] = [] := h false true [false] rfl
  cases hs

theorem ex_nonEmptyEnc_pos : NonEmptyEnc varLenBoolFramedCodec.enc :=
  varLenBoolFramedCodec_nonEmptyEnc

theorem ex_nonEmptyEnc_neg : ¬ NonEmptyEnc emptyUnitFramedCodec.enc := by
  intro h
  exact h () rfl

theorem ex_listCodec_pos :
    (listCodec varLenBoolFramedCodec).dec
      ((listCodec varLenBoolFramedCodec).enc [false, true, false]) = some [false, true, false] := by
  simp [listCodec, encList, varLenBoolFramedCodec]
  rw [decList]; simp
  rw [decList]; simp
  rw [decList]; simp
  rw [decList]

theorem ex_listCodec_neg : ¬ DecEnc (listCodec emptyUnitFramedCodec) := by
  intro h
  have h1 := h [()]
  simp [listCodec, encList, emptyUnitFramedCodec] at h1
  rw [decList] at h1
  cases h1

/-- Negative example exercising the rejecting branch of `decList`'s progress guard:
    on `emptyUnitFramedCodec`, `decPrefix [true] = some ((), [true])` makes no progress
    (`rest.length = 1 ≥ 1`), so `decList` returns `none`. -/
theorem ex_decList_guard_rejects : decList emptyUnitFramedCodec [true] = none := by
  rw [decList]
  simp [emptyUnitFramedCodec]

/-! ## Examples for `Junk`, `inlMatcher`, `decompToFun`/`decompInvFun`, `codecOfSplit`, `junkToC`, `complementEquivOfCodecEq` -/

theorem ex_junk_pos : Nonempty (Junk boolToNatCodec) := ⟨⟨2, rfl⟩⟩

theorem ex_junk_neg : boolToNatCodec.dec 0 ≠ none := by
  intro h; cases h

theorem ex_inlMatcher_pos : inlMatcher (Sum.inl true : Bool ⊕ Nat) = some true := rfl

theorem ex_inlMatcher_neg : inlMatcher (Sum.inr 0 : Bool ⊕ Nat) = none := rfl

theorem ex_decomp_pos : IsEquiv (decompToFun boolToNatCodec) (decompInvFun boolToNatCodec) := by
  constructor
  · intro b
    match b with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  · rintro (a | ⟨b, hb⟩)
    · cases a <;> rfl
    · match b with
      | 0 => cases hb
      | 1 => cases hb
      | _ + 2 => rfl

theorem ex_decomp_neg_malleable :
    ¬ IsEquiv (decompToFun nonCanonicalBoolCodec) (decompInvFun nonCanonicalBoolCodec) := by
  intro h
  have h2 := h.1 2
  cases h2

theorem ex_decomp_neg_failing :
    ¬ IsEquiv (decompToFun alwaysFailUnitCodec) (decompInvFun alwaysFailUnitCodec) := by
  intro h
  have h0 := h.2 (Sum.inl ())
  cases h0

/-- Concrete coproduct decomposition `Nat ≃ Bool ⊕ Nat` matching `boolToNatCodec`. -/
def natBoolSplitToFun : Nat → Bool ⊕ Nat
  | 0 => Sum.inl false
  | 1 => Sum.inl true
  | n + 2 => Sum.inr n

/-- Inverse of `natBoolSplitToFun`. -/
def natBoolSplitInvFun : Bool ⊕ Nat → Nat
  | Sum.inl false => 0
  | Sum.inl true => 1
  | Sum.inr n => n + 2

theorem natBoolSplit_leftInv : LeftInv natBoolSplitToFun natBoolSplitInvFun := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem natBoolSplit_rightInv : RightInv natBoolSplitToFun natBoolSplitInvFun := by
  rintro (a | k)
  · cases a <;> rfl
  · rfl

/-- Bundled equivalence `Nat ≃ Bool ⊕ Nat` corresponding to `boolToNatCodec`. -/
def natBoolEquiv : Equiv Nat (Bool ⊕ Nat) where
  toFun := natBoolSplitToFun
  invFun := natBoolSplitInvFun
  left_inv := natBoolSplit_leftInv
  right_inv := natBoolSplit_rightInv

/-- A second decomposition `Nat ≃ Bool ⊕ { n : Nat // 2 ≤ n }` with a distinct
    complement type, inducing the same codec as `natBoolSplitToFun`. -/
def natBoolSubSplitToFun : Nat → Bool ⊕ { n : Nat // 2 ≤ n }
  | 0 => Sum.inl false
  | 1 => Sum.inl true
  | n + 2 => Sum.inr ⟨n + 2, Nat.le_add_left 2 n⟩

def natBoolSubSplitInvFun : Bool ⊕ { n : Nat // 2 ≤ n } → Nat
  | Sum.inl false => 0
  | Sum.inl true => 1
  | Sum.inr ⟨n, _⟩ => n

theorem natBoolSubSplit_leftInv : LeftInv natBoolSubSplitToFun natBoolSubSplitInvFun := by
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem natBoolSubSplit_rightInv : RightInv natBoolSubSplitToFun natBoolSubSplitInvFun := by
  rintro (a | ⟨n, hn⟩)
  · cases a <;> rfl
  · match n, hn with
    | 0, hn => cases hn
    | 1, hn => cases hn with | step h => cases h
    | _ + 2, _ => rfl

theorem natBoolSplit_eq_subSplit :
    codecOfSplit natBoolSplitToFun natBoolSplitInvFun =
      codecOfSplit natBoolSubSplitToFun natBoolSubSplitInvFun := by
  apply Codec.ext
  · funext a; cases a <;> rfl
  · funext b
    match b with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem ex_codecOfSplit_pos : codecOfSplit natBoolSplitToFun natBoolSplitInvFun = boolToNatCodec := by
  apply Codec.ext
  · funext a; cases a <;> rfl
  · funext b
    match b with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem ex_codecOfSplit_neg :
    ¬ EncDec (codecOfSplit (fun _ : Bool => (Sum.inl () : Unit ⊕ Empty))
      (fun x => match x with | Sum.inl () => false | Sum.inr e => Empty.elim e)) := by
  intro h
  have ht := h true () rfl
  cases ht

theorem ex_junkToC_pos :
    junkToC natBoolSplitToFun natBoolSplitInvFun ⟨2, rfl⟩ = 0 ∧
    junkToC natBoolSplitToFun natBoolSplitInvFun ⟨5, rfl⟩ = 3 :=
  ⟨rfl, rfl⟩

/-- Split maps `Unit ↔ Empty ⊕ Bool` satisfying `LeftInv` and `RightInv` on `Sum.inl`,
    but failing `RightInv` on `Sum.inr true`. -/
def collidingJunkToFun : Unit → Empty ⊕ Bool := fun _ => Sum.inr false
def collidingJunkInvFun : Empty ⊕ Bool → Unit
  | Sum.inl e => Empty.elim e
  | Sum.inr _ => ()

/-- Negative example exercising `junkToC`: without `RightInv` on `Sum.inr`, `junkToC`
    cannot invert `g ∘ Sum.inr` (`junkToC ... ⟨g (Sum.inr true), rfl⟩ = false ≠ true`). -/
theorem ex_junkToC_neg_nonRightInv :
    LeftInv collidingJunkToFun collidingJunkInvFun ∧
    (∀ a : Empty, collidingJunkToFun (collidingJunkInvFun (Sum.inl a)) = Sum.inl a) ∧
    junkToC collidingJunkToFun collidingJunkInvFun
      ⟨collidingJunkInvFun (Sum.inr true), rfl⟩ ≠ true := by
  refine ⟨fun u => by cases u; rfl, fun a => Empty.elim a, ?_⟩
  intro h
  cases h

theorem ex_complementEquivOfCodecEq_pos :
    (complementEquivOfCodecEq natBoolSplitToFun natBoolSplitInvFun
      natBoolSubSplitToFun natBoolSubSplitInvFun
      natBoolSplit_leftInv natBoolSplit_rightInv
      natBoolSubSplit_leftInv natBoolSubSplit_rightInv
      natBoolSplit_eq_subSplit).toFun 3 = ⟨5, Nat.le_add_left 2 3⟩ := rfl

/-- Negative example for `complementEquivOfCodecEq`: when one split lacks `LeftInv`
    (`Bool → Empty ⊕ Unit` vs `Bool ≃ Empty ⊕ Bool`), equal induced codecs do not yield
    an equivalence of complements (`¬ Nonempty (Equiv Unit Bool)`). -/
theorem ex_complementEquivOfCodecEq_neg :
    codecOfSplit (fun _ : Bool => (Sum.inr () : Empty ⊕ Unit))
      (fun x => match x with | Sum.inl e => Empty.elim e | Sum.inr () => false) =
    codecOfSplit (Sum.inr : Bool → Empty ⊕ Bool)
      (fun x => match x with | Sum.inl e => Empty.elim e | Sum.inr b => b) ∧
    ¬ Nonempty (Equiv Unit Bool) := by
  refine ⟨Codec.ext (funext fun e => Empty.elim e) (funext fun _ => rfl), ?_⟩
  rintro ⟨φ⟩
  exact ex_equiv_neg ⟨⟨φ.invFun, φ.toFun, φ.right_inv, φ.left_inv⟩⟩

end Toy.Codec
