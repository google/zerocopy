import Toy.Codec.Defs
import Toy.Codec.Examples

/-!
# Counterexamples, positive controls, and hypothesis-tightness witnesses

This module provides:
1. Standalone counterexample theorems showing why single codec laws and non-prefix-free
   encodings fail to prevent malleability, vacuous rejection, or concatenation ambiguity:
   - `decEnc_admits_malleable_codec`
   - `encDec_admits_always_failing_codec`
   - `lawful_injective_nonEmpty_enc_admits_ambiguous_concat`
2. Proved positive controls and boundary witnesses (including the uniquely decodable
   non-prefix-free code `suffixEnc`, lenient list round-tripping `lenientFc`,
   whole-input non-composability of `encList`, whole-input vs. prefix non-malleability
   `firstOnly`, `ImagePrefixFree` vs. `PrefixFree`, and non-intertwined equal complements).
3. Canonical hypothesis-tightness counterexamples for every `tight` hypothesis of
   every theorem in `Toy.Codec.Statements`, each showing that a concrete instance
   satisfies all remaining hypotheses while the conclusion fails.
-/

namespace Toy.Codec

/-! ## Helper codecs and maps for counterexamples -/

/-- Boolean negation codec `Bool → Bool` (lawful, with encoder distinct from `id`). -/
def boolNotCodec : Codec Bool Bool where
  enc b := !b
  dec b := some (!b)

theorem boolNotCodec_decEnc : DecEnc boolNotCodec := by
  intro b; cases b <;> rfl

theorem boolNotCodec_encDec : EncDec boolNotCodec := by
  intro b a h; cases b <;> cases h <;> rfl

theorem nonCanonicalBoolCodec_decEnc : DecEnc nonCanonicalBoolCodec := by
  intro a; cases a <;> rfl

theorem alwaysFailBoolCodec_encDec : EncDec alwaysFailBoolCodec := by
  intro b a h; cases h

theorem alwaysFailConstCodec_encDec : EncDec alwaysFailConstCodec := by
  intro b a h; cases h

theorem shiftedBoolCodec_decInj : DecInj shiftedBoolCodec := by
  intro b₁ b₂ a h₁ h₂
  cases b₁ <;> cases b₂ <;> cases h₁ <;> cases h₂ <;> rfl

theorem malleableUnitBoolCodec_decEnc : DecEnc malleableUnitBoolCodec := by
  intro a; cases a; rfl

theorem alwaysFailUnitCodec_encDec : EncDec alwaysFailUnitCodec := by
  intro b a h; cases h

theorem ambiguousCodec_decEnc : DecEnc ambiguousCodec := by
  intro a; cases a <;> rfl

theorem ambiguousCodec_encDec : EncDec ambiguousCodec := by
  intro b a h
  match b with
  | [false] => cases h; rfl
  | [false, false] => cases h; rfl
  | [] => cases h
  | [true] => cases h
  | [false, true] => cases h
  | [true, _] => cases h
  | _ :: _ :: _ :: _ => simp [ambiguousCodec] at h

theorem ambiguousEnc_injective : Function.Injective ambiguousEnc := by
  intro a₁ a₂ h
  cases a₁ <;> cases a₂ <;> cases h <;> rfl

theorem ambiguousEnc_nonEmpty : NonEmptyEnc ambiguousEnc := by
  intro a; cases a <;> intro h <;> cases h

theorem alwaysFailFramedCodec_prefixEncDec : PrefixEncDec alwaysFailFramedCodec := by
  intro xs a rest h; cases h

theorem alwaysFailFramedCodec_nonEmptyEnc : NonEmptyEnc alwaysFailFramedCodec.enc := by
  intro a h; cases h

theorem malleableFramedCodec_prefixDecEnc : PrefixDecEnc malleableFramedCodec := by
  intro a rest; cases a; rfl

theorem malleableFramedCodec_nonEmptyEnc : NonEmptyEnc malleableFramedCodec.enc := by
  intro a h; cases h

theorem emptyUnitFramedCodec_prefixDecEnc : PrefixDecEnc emptyUnitFramedCodec := by
  intro a rest; cases a; rfl

theorem emptyUnitFramedCodec_prefixEncDec : PrefixEncDec emptyUnitFramedCodec := by
  intro xs a rest h
  cases a
  cases h
  rfl

theorem emptyUnitFramedCodec_prefixFree : PrefixFree emptyUnitFramedCodec.enc := by
  intro a₁ a₂ _ _
  cases a₁; cases a₂; rfl

theorem ambiguousFailFramedCodec_prefixEncDec : PrefixEncDec ambiguousFailFramedCodec := by
  intro xs a rest h; cases h

/-! ## Standalone counterexample theorems -/

/-- `DecEnc` alone admits malleability:
    `nonCanonicalBoolCodec : Codec Bool Nat` satisfies `DecEnc`, yet fails both
    `EncDec` and `DecInj` because two distinct wire values (`1` and `2`) decode to
    the same source value `true`. -/
theorem decEnc_admits_malleable_codec :
    DecEnc nonCanonicalBoolCodec ∧
    ¬ EncDec nonCanonicalBoolCodec ∧
    ¬ DecInj nonCanonicalBoolCodec ∧
    (1 : Nat) ≠ 2 ∧
    nonCanonicalBoolCodec.dec 1 = some true ∧
    nonCanonicalBoolCodec.dec 2 = some true :=
  ⟨nonCanonicalBoolCodec_decEnc, ex_encDec_neg, ex_decInj_neg, by decide, rfl, rfl⟩

/-- `EncDec` alone admits the always-failing decoder:
    `alwaysFailBoolCodec : Codec Bool Bool` satisfies `EncDec`, yet fails `DecEnc`
    and rejects every input (`dec b = none` for all `b`). -/
theorem encDec_admits_always_failing_codec :
    EncDec alwaysFailBoolCodec ∧
    ¬ DecEnc alwaysFailBoolCodec ∧
    (∀ b : Bool, alwaysFailBoolCodec.dec b = none) :=
  ⟨alwaysFailBoolCodec_encDec, ex_decEnc_neg, fun _ => rfl⟩

/-- Single-value lawfulness with an injective, non-empty encoding admits ambiguous
    concatenation when prefix-freeness is absent:
    `ambiguousCodec` (`false ↦ [false]`, `true ↦ [false, false]`) satisfies `DecEnc`,
    `EncDec`, `Function.Injective enc`, and `NonEmptyEnc`, yet violates `PrefixFree`
    and maps `[false, false] ≠ [true]` to the same concatenation `[false, false]`,
    so no list decoder can satisfy `DecEnc`. -/
theorem lawful_injective_nonEmpty_enc_admits_ambiguous_concat :
    DecEnc ambiguousCodec ∧
    EncDec ambiguousCodec ∧
    Function.Injective ambiguousCodec.enc ∧
    NonEmptyEnc ambiguousCodec.enc ∧
    ¬ PrefixFree ambiguousCodec.enc ∧
    (([false, false] : List Bool) ≠ [true] ∧
      encList ambiguousCodec.enc [false, false] = encList ambiguousCodec.enc [true]) ∧
    (∀ dec : List Bool → Option (List Bool), ¬ DecEnc ⟨encList ambiguousCodec.enc, dec⟩) := by
  refine ⟨ambiguousCodec_decEnc, ambiguousCodec_encDec, ambiguousEnc_injective,
    ambiguousEnc_nonEmpty, ex_prefixFree_neg, ⟨by decide, rfl⟩, ?_⟩
  intro dec hde
  have h1 := hde [false, false]
  have h2 := hde [true]
  change dec [false, false] = some [false, false] at h1
  change dec [false, false] = some [true] at h2
  rw [h1] at h2
  cases h2

/-! ## Positive controls and boundary witnesses -/

/-- A non-prefix-free suffix code (`false ↦ [false]`, `true ↦ [false, true]`) that is
    nonetheless uniquely decodable under concatenation via 1-token lookahead. -/
def suffixEnc : Bool → List Bool
  | false => [false]
  | true => [false, true]

/-- Computable whole-list decoder for `encList suffixEnc` using 1-token lookahead. -/
def decSuffixList : List Bool → Option (List Bool)
  | [] => some []
  | false :: true :: rest => (decSuffixList rest).map (true :: ·)
  | false :: rest => (decSuffixList rest).map (false :: ·)
  | true :: _ => none

private theorem encList_suffixEnc_ne_true_cons :
    ∀ (as : List Bool) (t : List Bool), encList suffixEnc as ≠ true :: t
  | [], _, h => by cases h
  | false :: _, _, h => by cases h
  | true :: _, _, h => by cases h

private theorem suffixListCodec_decEnc : DecEnc ⟨encList suffixEnc, decSuffixList⟩ := by
  intro as
  change decSuffixList (encList suffixEnc as) = some as
  induction as with
  | nil => rfl
  | cons a tail ih =>
    cases a with
    | false =>
      change decSuffixList (false :: encList suffixEnc tail) = some (false :: tail)
      cases h : encList suffixEnc tail with
      | nil =>
        change (decSuffixList []).map (false :: ·) = some (false :: tail)
        rw [← h, ih]; rfl
      | cons b bs =>
        cases b with
        | false =>
          change (decSuffixList (false :: bs)).map (false :: ·) = some (false :: tail)
          rw [← h, ih]; rfl
        | true =>
          exact absurd h (encList_suffixEnc_ne_true_cons tail bs)
    | true =>
      change (decSuffixList (encList suffixEnc tail)).map (true :: ·) = some (true :: tail)
      rw [ih]; rfl

private theorem suffixListCodec_encDec_aux :
    ∀ (xs : List Bool) (as : List Bool), decSuffixList xs = some as → encList suffixEnc as = xs
  | [], _, h => by cases h; rfl
  | true :: _, _, h => by cases h
  | [false], _, h => by
    change (some []).map (false :: ·) = _ at h
    cases h; rfl
  | false :: true :: ys, _, h => by
    change (decSuffixList ys).map (true :: ·) = _ at h
    cases hd : decSuffixList ys with
    | none => rw [hd] at h; cases h
    | some tail =>
      rw [hd] at h; cases h
      have e := suffixListCodec_encDec_aux ys tail hd
      change false :: true :: encList suffixEnc tail = false :: true :: ys
      rw [e]
  | false :: false :: ys, _, h => by
    change (decSuffixList (false :: ys)).map (false :: ·) = _ at h
    cases hd : decSuffixList (false :: ys) with
    | none => rw [hd] at h; cases h
    | some tail =>
      rw [hd] at h; cases h
      have e := suffixListCodec_encDec_aux (false :: ys) tail hd
      change false :: encList suffixEnc tail = false :: false :: ys
      rw [e]
termination_by xs => xs.length

/-- Positive control for `lawful_injective_nonEmpty_enc_admits_ambiguous_concat`:
    `suffixEnc` (`false ↦ [false]`, `true ↦ [false, true]`) is injective and non-empty
    and violates `PrefixFree`, yet `encList suffixEnc` is injective and admits the
    computable lawful (`DecEnc ∧ EncDec`) list decoder `decSuffixList`. -/
theorem suffixEnc_not_prefixFree_yet_concat_lawful :
    Function.Injective suffixEnc ∧
    NonEmptyEnc suffixEnc ∧
    ¬ PrefixFree suffixEnc ∧
    Function.Injective (encList suffixEnc) ∧
    DecEnc ⟨encList suffixEnc, decSuffixList⟩ ∧
    EncDec ⟨encList suffixEnc, decSuffixList⟩ := by
  refine ⟨?_, ?_, ?_, ?_, suffixListCodec_decEnc, suffixListCodec_encDec_aux⟩
  · intro a₁ a₂ h; cases a₁ <;> cases a₂ <;> cases h <;> rfl
  · intro a; cases a <;> intro h <;> cases h
  · intro h
    have hft : false = true := h false true [true] rfl
    cases hft
  · intro l₁ l₂ h
    have d₁ := suffixListCodec_decEnc l₁
    have d₂ := suffixListCodec_decEnc l₂
    change decSuffixList (encList suffixEnc l₁) = some l₁ at d₁
    change decSuffixList (encList suffixEnc l₂) = some l₂ at d₂
    rw [h, d₂] at d₁
    exact Option.some.inj d₁.symm

/-- A decoder that is injective on accepted inputs (`DecInj`) and surjective need not
    satisfy either `DecEnc` or `EncDec` with respect to a fixed encoder. -/
theorem decInj_and_surjective_dec_not_lawful :
    DecInj shiftedBoolCodec ∧
    (∀ a : Bool, ∃ b : Bool, shiftedBoolCodec.dec b = some a) ∧
    ¬ DecEnc shiftedBoolCodec ∧
    ¬ EncDec shiftedBoolCodec := by
  refine ⟨shiftedBoolCodec_decInj, ?_, ?_, ?_⟩
  · intro a; cases a
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩
  · intro h; have hf := h false; cases hf
  · intro h; have hf := h false true rfl; cases hf

/-- A constant encoding has a prefix-free image (`ImagePrefixFree`), yet fails
    `PrefixFree` because `PrefixFree` bundles encoder injectivity. -/
theorem const_imagePrefixFree_not_prefixFree :
    ImagePrefixFree (fun _ : Bool => [true]) ∧ ¬ PrefixFree (fun _ : Bool => [true]) := by
  constructor
  · intro _ _ s he
    cases s with
    | nil => rfl
    | cons _ _ => simp at he
  · intro h
    have hft : false = true := h false true [] rfl
    cases hft

/-- A framed codec that violates `PrefixDecEnc` on arbitrary remainders, yet whose
    induced `listCodec` satisfies `DecEnc` (`PrefixDecEnc` is sufficient, not necessary). -/
def lenientFc : FramedCodec Unit Bool where
  enc _ := [true]
  decPrefix
    | true :: rest => if rest.all id = true then some ((), rest) else none
    | _ => none

private theorem lenient_all (as : List Unit) : (encList lenientFc.enc as).all id = true := by
  induction as with
  | nil => rfl
  | cons _ tail ih =>
    change (true :: encList lenientFc.enc tail).all id = true
    simp only [List.all_cons, id, Bool.true_and]
    exact ih

theorem lenient_not_prefixDecEnc_yet_listCodec_decEnc :
    ¬ PrefixDecEnc lenientFc ∧ NonEmptyEnc lenientFc.enc ∧ DecEnc (listCodec lenientFc) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h1 := h () [false]
    cases h1
  · intro _ h
    cases h
  · intro as
    change decList lenientFc (encList lenientFc.enc as) = some as
    induction as with
    | nil => rw [encList, decList]
    | cons a tail ih =>
      have h : encList lenientFc.enc (a :: tail) = true :: encList lenientFc.enc tail := rfl
      rw [h, decList]
      have hp : lenientFc.decPrefix (true :: encList lenientFc.enc tail) =
          some ((), encList lenientFc.enc tail) := by
        change (if (encList lenientFc.enc tail).all id = true then
          some ((), encList lenientFc.enc tail) else none) = _
        simp only [lenient_all tail, ↓reduceIte]
      simp only [hp]
      have hlt : (encList lenientFc.enc tail).length <
          (true :: encList lenientFc.enc tail).length := by simp
      simp only [hlt, ↓reduceDIte, ih]
      rfl

/-- `encList enc` is never `PrefixFree` when `A` is inhabited (`[]` is a prefix of `[a]`),
    so no framed codec with encoder `encList enc` can satisfy `PrefixDecEnc`. -/
theorem encList_not_prefixFree {A : Type u} {β : Type v} (enc : A → List β) (a : A) :
    ¬ PrefixFree (encList enc) := by
  intro h
  have := h [] [a] (encList enc [a]) rfl
  cases this

theorem no_prefixDecEnc_for_encList {A : Type u} {β : Type v} (enc : A → List β) (a : A)
    (decP : List β → Option (List A × List β)) :
    ¬ PrefixDecEnc (⟨encList enc, decP⟩ : FramedCodec (List A) β) := by
  intro h
  have h1 := h [] (encList enc [a])
  have h2 := h [a] []
  change decP ([] ++ encList enc [a]) = some ([], encList enc [a]) at h1
  change decP (encList enc [a] ++ []) = some ([a], []) at h2
  rw [List.nil_append] at h1
  rw [List.append_nil] at h2
  rw [h1] at h2
  cases h2

/-- Whole-input codec obtained by discarding the unconsumed remainder of `fc.decPrefix`. -/
def firstOnly {A : Type u} {β : Type v} (fc : FramedCodec A β) : Codec A (List β) where
  enc := fc.enc
  dec xs := (fc.decPrefix xs).map Prod.fst

/-- Discarding the remainder of a lawful framed codec preserves `DecEnc` but violates
    whole-input `DecInj` (and `EncDec`). -/
theorem framed_lawful_but_firstOnly_not_decInj :
    PrefixDecEnc varLenBoolFramedCodec ∧
    PrefixEncDec varLenBoolFramedCodec ∧
    DecEnc (firstOnly varLenBoolFramedCodec) ∧
    ¬ DecInj (firstOnly varLenBoolFramedCodec) := by
  refine ⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixEncDec, ?_, ?_⟩
  · intro a; cases a <;> rfl
  · intro h
    have := h [false] [false, false] false rfl rfl
    cases this

/-- Two decompositions of `Bool` as `Unit ⊕ Unit` with identical complement type `Unit`
    that induce distinct codecs (showing equivalence of complements must intertwine). -/
def splitBoolFalseToFun : Bool → Unit ⊕ Unit
  | false => Sum.inl ()
  | true => Sum.inr ()

def splitBoolFalseInvFun : Unit ⊕ Unit → Bool
  | Sum.inl () => false
  | Sum.inr () => true

def splitBoolTrueToFun : Bool → Unit ⊕ Unit
  | true => Sum.inl ()
  | false => Sum.inr ()

def splitBoolTrueInvFun : Unit ⊕ Unit → Bool
  | Sum.inl () => true
  | Sum.inr () => false

theorem same_complement_different_codec :
    LeftInv splitBoolFalseToFun splitBoolFalseInvFun ∧
    RightInv splitBoolFalseToFun splitBoolFalseInvFun ∧
    LeftInv splitBoolTrueToFun splitBoolTrueInvFun ∧
    RightInv splitBoolTrueToFun splitBoolTrueInvFun ∧
    Nonempty (Equiv Unit Unit) ∧
    codecOfSplit splitBoolFalseToFun splitBoolFalseInvFun ≠
      codecOfSplit splitBoolTrueToFun splitBoolTrueInvFun ∧
    ¬ (∃ φ : Equiv Unit Unit, ∀ b : Bool,
        splitBoolTrueToFun b = Sum.map id φ.toFun (splitBoolFalseToFun b)) := by
  refine ⟨by intro b; cases b <;> rfl,
    by rintro (⟨⟩ | ⟨⟩) <;> rfl,
    by intro b; cases b <;> rfl,
    by rintro (⟨⟩ | ⟨⟩) <;> rfl,
    ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩, ?_, ?_⟩
  · intro h
    have hf := congrFun (congrArg Codec.enc h) ()
    cases hf
  · rintro ⟨φ, hφ⟩
    have hf := hφ false
    cases hf

/-! ## Tightness counterexamples for characterization, bijection, and canonicalization theorems -/

/-- Tightness of `DecEnc` in `decEnc_imp_enc_injective`. -/
theorem ce_decEnc_imp_enc_injective_drop_decEnc :
    EncDec alwaysFailConstCodec ∧ ¬ Function.Injective alwaysFailConstCodec.enc := by
  refine ⟨alwaysFailConstCodec_encDec, ?_⟩
  intro hinj
  have hft : false = true := hinj rfl
  cases hft

/-- Tightness of the graph-converse hypothesis in `decEqSomeIff_imp_enc_injective`. -/
theorem ce_decEqSomeIff_imp_enc_injective_drop_hconv :
    EncDec alwaysFailConstCodec ∧
    ¬ (∀ (b : Unit) (a : Bool),
        alwaysFailConstCodec.dec b = some a ↔ alwaysFailConstCodec.enc a = b) ∧
    ¬ Function.Injective alwaysFailConstCodec.enc := by
  refine ⟨alwaysFailConstCodec_encDec, ?_, ce_decEnc_imp_enc_injective_drop_decEnc.2⟩
  intro h
  have h0 := (h () false).mpr rfl
  cases h0

/-- Auxiliary witness: `DecInj` alone does not imply `EncDec` or `DecEnc`. -/
theorem ce_decInj_not_implies_encDec :
    DecInj shiftedBoolCodec ∧ ¬ DecEnc shiftedBoolCodec ∧ ¬ EncDec shiftedBoolCodec := by
  refine ⟨shiftedBoolCodec_decInj, ?_, ?_⟩
  · intro h; have hf := h false; cases hf
  · intro h; have hf := h false true rfl; cases hf

/-- Tightness of `c₁.enc = c₂.enc` in `dec_unique_of_lawful`. -/
theorem ce_dec_unique_drop_henc :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    DecEnc boolNotCodec ∧ EncDec boolNotCodec ∧
    (Codec.id Bool).dec ≠ boolNotCodec.dec := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool,
    boolNotCodec_decEnc, boolNotCodec_encDec, ?_⟩
  intro h
  have hf := congrFun h false
  cases hf

/-- Tightness of `DecEnc c₁` in `dec_unique_of_lawful`. -/
theorem ce_dec_unique_drop_hde1 :
    alwaysFailBoolCodec.enc = (Codec.id Bool).enc ∧
    EncDec alwaysFailBoolCodec ∧
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    alwaysFailBoolCodec.dec ≠ (Codec.id Bool).dec := by
  refine ⟨rfl, alwaysFailBoolCodec_encDec, codecId_decEnc Bool, codecId_encDec Bool, ?_⟩
  intro h
  have hf := congrFun h false
  cases hf

/-- Tightness of `EncDec c₁` in `dec_unique_of_lawful`. -/
theorem ce_dec_unique_drop_hed1 :
    nonCanonicalBoolCodec.enc = boolToNatCodec.enc ∧
    DecEnc nonCanonicalBoolCodec ∧
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec ∧
    nonCanonicalBoolCodec.dec ≠ boolToNatCodec.dec := by
  refine ⟨by funext a; cases a <;> rfl, nonCanonicalBoolCodec_decEnc,
    boolToNatCodec_decEnc, boolToNatCodec_encDec, ?_⟩
  intro h
  have h2 := congrFun h 2
  cases h2

/-- Tightness of `DecEnc c₂` in `dec_unique_of_lawful`. -/
theorem ce_dec_unique_drop_hde2 :
    (Codec.id Bool).enc = alwaysFailBoolCodec.enc ∧
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    EncDec alwaysFailBoolCodec ∧
    (Codec.id Bool).dec ≠ alwaysFailBoolCodec.dec := by
  refine ⟨rfl, codecId_decEnc Bool, codecId_encDec Bool, alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := congrFun h false
  cases hf

/-- Tightness of `EncDec c₂` in `dec_unique_of_lawful`. -/
theorem ce_dec_unique_drop_hed2 :
    boolToNatCodec.enc = nonCanonicalBoolCodec.enc ∧
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec ∧
    DecEnc nonCanonicalBoolCodec ∧
    boolToNatCodec.dec ≠ nonCanonicalBoolCodec.dec := by
  refine ⟨by funext a; cases a <;> rfl, boolToNatCodec_decEnc, boolToNatCodec_encDec,
    nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 := congrFun h 2
  cases h2

/-- Tightness of `Function.Injective f` in `classicalCodec_decEnc_of_injective`. -/
theorem ce_classicalCodec_decEnc_drop_inj :
    ¬ Function.Injective (fun _ : Bool => ()) ∧
    ¬ DecEnc (classicalCodec (fun _ : Bool => ())) := by
  refine ⟨?_, ex_classicalCodec_neg⟩
  intro h
  have hft : false = true := h rfl
  cases hft

/-- Tightness of `DecEnc c` in `classicalCodec_recover_of_lawful`. -/
theorem ce_classicalCodec_recover_drop_decEnc :
    EncDec alwaysFailBoolCodec ∧
    classicalCodec alwaysFailBoolCodec.enc ≠ alwaysFailBoolCodec := by
  refine ⟨alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hdec := congrFun (congrArg Codec.dec h) false
  unfold classicalCodec classicalDec at hdec
  dsimp only at hdec
  split at hdec
  · cases hdec
  · rename_i hn; exact absurd ⟨false, rfl⟩ hn

/-- Tightness of `EncDec c` in `classicalCodec_recover_of_lawful`. -/
theorem ce_classicalCodec_recover_drop_encDec :
    DecEnc nonCanonicalBoolCodec ∧
    classicalCodec nonCanonicalBoolCodec.enc ≠ nonCanonicalBoolCodec := by
  refine ⟨nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have hdec := congrFun (congrArg Codec.dec h) 2
  unfold classicalCodec classicalDec at hdec
  dsimp only at hdec
  split at hdec
  · rename_i hex; rcases hex with ⟨a, ha⟩; cases a <;> cases ha
  · cases hdec

/-- Tightness of `Function.Injective f` in `codecOfFiberSplit_decEnc_of_injective`. -/
theorem ce_codecOfFiberSplit_decEnc_drop_inj :
    EncDec (codecOfFiberSplit (fun _ : Bool => ()) constUnitFiberSplit) ∧
    ¬ DecEnc (codecOfFiberSplit (fun _ : Bool => ()) constUnitFiberSplit) := by
  refine ⟨?_, ex_fiberSplit_neg_nonInjective⟩
  intro b a h
  cases b; cases h; rfl

/-- Computable `FiberSplit` for the identity map on `Bool`. -/
def idBoolFiberSplit : FiberSplit (fun b : Bool => b) := fun b => PSum.inl ⟨b, rfl⟩

/-- Tightness of `DecEnc c` in `codecOfFiberSplit_eq_of_lawful`. -/
theorem ce_codecOfFiberSplit_eq_drop_decEnc :
    EncDec alwaysFailBoolCodec ∧
    codecOfFiberSplit alwaysFailBoolCodec.enc idBoolFiberSplit ≠ alwaysFailBoolCodec := by
  refine ⟨alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := congrFun (congrArg Codec.dec h) false
  cases hf

/-- Computable `FiberSplit` for `nonCanonicalBoolCodec.enc` (which equals `boolToNatCodec.enc`). -/
def nonCanonicalBoolFiberSplit : FiberSplit nonCanonicalBoolCodec.enc
  | 0 => PSum.inl ⟨false, rfl⟩
  | 1 => PSum.inl ⟨true, rfl⟩
  | _ + 2 => PSum.inr (fun a h => by cases a <;> cases h)

/-- Tightness of `EncDec c` in `codecOfFiberSplit_eq_of_lawful`. -/
theorem ce_codecOfFiberSplit_eq_drop_encDec :
    DecEnc nonCanonicalBoolCodec ∧
    codecOfFiberSplit nonCanonicalBoolCodec.enc nonCanonicalBoolFiberSplit ≠
      nonCanonicalBoolCodec := by
  refine ⟨nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 := congrFun (congrArg Codec.dec h) 2
  cases h2

/-- Tightness of `DecEnc c` in `lawful_dec_isSome_iff_mem_range`. -/
theorem ce_lawful_dec_isSome_drop_decEnc :
    EncDec alwaysFailBoolCodec ∧
    ¬ (∀ b : Bool, (alwaysFailBoolCodec.dec b).isSome = true ↔
        ∃ a : Bool, alwaysFailBoolCodec.enc a = b) := by
  refine ⟨alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := (h false).mpr ⟨false, rfl⟩
  cases hf

/-- Tightness of `EncDec c` in `lawful_dec_isSome_iff_mem_range`. -/
theorem ce_lawful_dec_isSome_drop_encDec :
    DecEnc nonCanonicalBoolCodec ∧
    ¬ (∀ b : Nat, (nonCanonicalBoolCodec.dec b).isSome = true ↔
        ∃ a : Bool, nonCanonicalBoolCodec.enc a = b) := by
  refine ⟨nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  obtain ⟨a, ha⟩ := (h 2).mp rfl
  cases a <;> cases ha

/-- Tightness of `DecEnc c` in `junk_iff_not_in_image_of_lawful`. -/
theorem ce_junk_iff_not_in_image_of_lawful_drop_decEnc :
    EncDec alwaysFailBoolCodec ∧
    ¬ (∀ b : Bool, alwaysFailBoolCodec.dec b = none ↔
        ∀ a : Bool, alwaysFailBoolCodec.enc a ≠ b) := by
  refine ⟨alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  exact (h false).mp rfl false rfl

/-- Tightness of `EncDec c` in `junk_iff_not_in_image_of_lawful`. -/
theorem ce_junk_iff_not_in_image_of_lawful_drop_encDec :
    DecEnc nonCanonicalBoolCodec ∧
    ¬ (∀ b : Nat, nonCanonicalBoolCodec.dec b = none ↔
        ∀ a : Bool, nonCanonicalBoolCodec.enc a ≠ b) := by
  refine ⟨nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 : nonCanonicalBoolCodec.dec 2 = none :=
    (h 2).mpr (fun a ha => by cases a <;> cases ha)
  cases h2

/-- Tightness of `DecEnc c` in `canonicalize_decEnc_of_decEnc`. -/
theorem ce_canonicalize_decEnc_drop_decEnc :
    EncDec alwaysFailBoolCodec ∧ ¬ DecEnc (canonicalize alwaysFailBoolCodec) :=
  ⟨alwaysFailBoolCodec_encDec, ex_canonicalize_neg⟩

/-! ## Tightness counterexamples for closure theorems -/

theorem ce_comp_decEnc_drop_hde1 :
    EncDec alwaysFailBoolCodec ∧ DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    ¬ DecEnc (alwaysFailBoolCodec.comp (Codec.id Bool)) :=
  ⟨alwaysFailBoolCodec_encDec, codecId_decEnc Bool, codecId_encDec Bool, ex_comp_neg⟩

theorem ce_comp_decEnc_drop_hde2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ EncDec alwaysFailBoolCodec ∧
    ¬ DecEnc ((Codec.id Bool).comp alwaysFailBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := h false
  cases hf

theorem ce_comp_encDec_drop_hed1 :
    DecEnc nonCanonicalBoolCodec ∧ DecEnc (Codec.id Nat) ∧ EncDec (Codec.id Nat) ∧
    ¬ EncDec (nonCanonicalBoolCodec.comp (Codec.id Nat)) := by
  refine ⟨nonCanonicalBoolCodec_decEnc, codecId_decEnc Nat, codecId_encDec Nat, ?_⟩
  intro h
  have h2 := h 2 true rfl
  cases h2

theorem ce_comp_encDec_drop_hed2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ DecEnc nonCanonicalBoolCodec ∧
    ¬ EncDec ((Codec.id Bool).comp nonCanonicalBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 := h 2 true rfl
  cases h2

theorem ce_prod_decEnc_drop_hde1 :
    EncDec alwaysFailBoolCodec ∧ DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    ¬ DecEnc (alwaysFailBoolCodec.prod (Codec.id Bool)) := by
  refine ⟨alwaysFailBoolCodec_encDec, codecId_decEnc Bool, codecId_encDec Bool, ?_⟩
  intro h
  have hf := h (false, false)
  cases hf

theorem ce_prod_decEnc_drop_hde2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ EncDec alwaysFailBoolCodec ∧
    ¬ DecEnc ((Codec.id Bool).prod alwaysFailBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := h (false, false)
  cases hf

theorem ce_prod_encDec_drop_hed1 :
    DecEnc nonCanonicalBoolCodec ∧ DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    ¬ EncDec (nonCanonicalBoolCodec.prod (Codec.id Bool)) :=
  ⟨nonCanonicalBoolCodec_decEnc, codecId_decEnc Bool, codecId_encDec Bool, ex_prod_neg⟩

theorem ce_prod_encDec_drop_hed2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ DecEnc nonCanonicalBoolCodec ∧
    ¬ EncDec ((Codec.id Bool).prod nonCanonicalBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 := h (false, 2) (false, true) rfl
  cases h2

theorem ce_sum_decEnc_drop_hde1 :
    EncDec alwaysFailBoolCodec ∧ DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    ¬ DecEnc (alwaysFailBoolCodec.sum (Codec.id Bool)) :=
  ⟨alwaysFailBoolCodec_encDec, codecId_decEnc Bool, codecId_encDec Bool, ex_sum_neg⟩

theorem ce_sum_decEnc_drop_hde2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ EncDec alwaysFailBoolCodec ∧
    ¬ DecEnc ((Codec.id Bool).sum alwaysFailBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, alwaysFailBoolCodec_encDec, ?_⟩
  intro h
  have hf := h (Sum.inr false)
  cases hf

theorem ce_sum_encDec_drop_hed1 :
    DecEnc nonCanonicalBoolCodec ∧ DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧
    ¬ EncDec (nonCanonicalBoolCodec.sum (Codec.id Bool)) := by
  refine ⟨nonCanonicalBoolCodec_decEnc, codecId_decEnc Bool, codecId_encDec Bool, ?_⟩
  intro h
  have h2 := h (Sum.inl 2) (Sum.inl true) rfl
  cases h2

theorem ce_sum_encDec_drop_hed2 :
    DecEnc (Codec.id Bool) ∧ EncDec (Codec.id Bool) ∧ DecEnc nonCanonicalBoolCodec ∧
    ¬ EncDec ((Codec.id Bool).sum nonCanonicalBoolCodec) := by
  refine ⟨codecId_decEnc Bool, codecId_encDec Bool, nonCanonicalBoolCodec_decEnc, ?_⟩
  intro h
  have h2 := h (Sum.inr 2) (Sum.inr true) rfl
  cases h2

/-! ## Tightness counterexamples for framed codec theorems -/

theorem ce_prefixDecEnc_imp_prefixFree_drop_hpde :
    PrefixEncDec ambiguousFailFramedCodec ∧
    NonEmptyEnc ambiguousFailFramedCodec.enc ∧
    ¬ PrefixFree ambiguousFailFramedCodec.enc :=
  ⟨ambiguousFailFramedCodec_prefixEncDec, ambiguousEnc_nonEmpty, ex_prefixFree_neg⟩

theorem ce_seq_prefixDecEnc_drop_h1 :
    PrefixEncDec alwaysFailFramedCodec ∧
    PrefixDecEnc varLenBoolFramedCodec ∧
    PrefixEncDec varLenBoolFramedCodec ∧
    ¬ PrefixDecEnc (alwaysFailFramedCodec.seq varLenBoolFramedCodec) :=
  ⟨alwaysFailFramedCodec_prefixEncDec, varLenBoolFramedCodec_prefixDecEnc,
    varLenBoolFramedCodec_prefixEncDec, ex_seq_neg⟩

theorem ce_seq_prefixDecEnc_drop_h2 :
    PrefixDecEnc varLenBoolFramedCodec ∧
    PrefixEncDec varLenBoolFramedCodec ∧
    PrefixEncDec alwaysFailFramedCodec ∧
    ¬ PrefixDecEnc (varLenBoolFramedCodec.seq alwaysFailFramedCodec) := by
  refine ⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixEncDec,
    alwaysFailFramedCodec_prefixEncDec, ?_⟩
  intro h
  have h0 := h (false, ()) []
  cases h0

theorem ce_seq_prefixEncDec_drop_h1 :
    PrefixDecEnc malleableFramedCodec ∧
    PrefixDecEnc varLenBoolFramedCodec ∧
    PrefixEncDec varLenBoolFramedCodec ∧
    ¬ PrefixEncDec (malleableFramedCodec.seq varLenBoolFramedCodec) := by
  refine ⟨malleableFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixDecEnc,
    varLenBoolFramedCodec_prefixEncDec, ?_⟩
  intro h
  have h1 := h [true, false] ((), false) [] rfl
  cases h1

theorem ce_seq_prefixEncDec_drop_h2 :
    PrefixDecEnc varLenBoolFramedCodec ∧
    PrefixEncDec varLenBoolFramedCodec ∧
    PrefixDecEnc malleableFramedCodec ∧
    ¬ PrefixEncDec (varLenBoolFramedCodec.seq malleableFramedCodec) := by
  refine ⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixEncDec,
    malleableFramedCodec_prefixDecEnc, ?_⟩
  intro h
  have h1 := h [false, true] (false, ()) [] rfl
  cases h1

/-- Tightness of `hpde : PrefixDecEnc fc` in `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc`. -/
theorem ce_listCodec_decEnc_iff_drop_prefixDecEnc :
    NonEmptyEnc alwaysFailFramedCodec.enc ∧
    PrefixEncDec alwaysFailFramedCodec ∧
    ¬ (DecEnc (listCodec alwaysFailFramedCodec) ↔ NonEmptyEnc alwaysFailFramedCodec.enc) := by
  refine ⟨alwaysFailFramedCodec_nonEmptyEnc, alwaysFailFramedCodec_prefixEncDec, ?_⟩
  intro hiff
  have hde := hiff.mpr alwaysFailFramedCodec_nonEmptyEnc
  have h1 := hde [()]
  simp [listCodec, encList, alwaysFailFramedCodec] at h1
  rw [decList] at h1
  simp at h1

/-- Witness that the right-hand side `NonEmptyEnc fc.enc` in
    `listCodec_decEnc_iff_nonEmptyEnc_of_prefixDecEnc` is genuinely non-trivial
    under `PrefixDecEnc` (on subsingleton domain `Unit`): `emptyUnitFramedCodec`
    satisfies `PrefixDecEnc`, `PrefixEncDec`, and `PrefixFree`, while violating both
    `NonEmptyEnc` and `DecEnc (listCodec _)`. -/
theorem ce_listCodec_decEnc_drop_nonEmptyEnc :
    PrefixDecEnc emptyUnitFramedCodec ∧
    PrefixEncDec emptyUnitFramedCodec ∧
    PrefixFree emptyUnitFramedCodec.enc ∧
    ¬ NonEmptyEnc emptyUnitFramedCodec.enc ∧
    ¬ DecEnc (listCodec emptyUnitFramedCodec) :=
  ⟨emptyUnitFramedCodec_prefixDecEnc, emptyUnitFramedCodec_prefixEncDec,
    emptyUnitFramedCodec_prefixFree, ex_nonEmptyEnc_neg, ex_listCodec_neg⟩

theorem ce_listCodec_encDec_drop_prefixEncDec :
    PrefixDecEnc malleableFramedCodec ∧
    NonEmptyEnc malleableFramedCodec.enc ∧
    ¬ EncDec (listCodec malleableFramedCodec) := by
  refine ⟨malleableFramedCodec_prefixDecEnc, malleableFramedCodec_nonEmptyEnc, ?_⟩
  intro h
  have hdec : (listCodec malleableFramedCodec).dec [true] = some [()] := by
    simp [listCodec]
    rw [decList]
    simp [malleableFramedCodec]
    rw [decList]
  have h1 : encList malleableFramedCodec.enc [()] = [true] := h [true] [()] hdec
  cases h1

/-! ## Tightness counterexamples for prism and complement theorems -/

/-- Without `DecEnc`, `LeftInv (decompToFun c) (decompInvFun c)` still holds under `EncDec`,
    but `RightInv` fails and `Equiv B (A ⊕ Junk c)` can be uninhabited. -/
theorem ce_lawful_decomp_drop_decEnc :
    EncDec alwaysFailUnitCodec ∧
    LeftInv (decompToFun alwaysFailUnitCodec) (decompInvFun alwaysFailUnitCodec) ∧
    ¬ RightInv (decompToFun alwaysFailUnitCodec) (decompInvFun alwaysFailUnitCodec) ∧
    ¬ IsEquiv (decompToFun alwaysFailUnitCodec) (decompInvFun alwaysFailUnitCodec) ∧
    ¬ Nonempty (Equiv Unit (Unit ⊕ Junk alwaysFailUnitCodec)) := by
  refine ⟨alwaysFailUnitCodec_encDec, ?_, ?_, ex_decomp_neg_failing, ?_⟩
  · intro u; cases u; rfl
  · intro hr; have h0 := hr (Sum.inl ()); cases h0
  rintro ⟨e⟩
  have h1 : e.toFun (e.invFun (Sum.inl ())) = Sum.inl () := e.right_inv (Sum.inl ())
  have h2 : e.toFun (e.invFun (Sum.inr ⟨(), rfl⟩)) = Sum.inr ⟨(), rfl⟩ :=
    e.right_inv (Sum.inr ⟨(), rfl⟩)
  have hu : e.invFun (Sum.inl ()) = e.invFun (Sum.inr ⟨(), rfl⟩) := Subsingleton.elim _ _
  rw [hu] at h1
  rw [h1] at h2
  cases h2

/-- Without `EncDec`, `RightInv (decompToFun c) (decompInvFun c)` still holds under `DecEnc`,
    but `LeftInv` fails and `Equiv B (A ⊕ Junk c)` can be uninhabited. -/
theorem ce_lawful_decomp_drop_encDec :
    DecEnc malleableUnitBoolCodec ∧
    RightInv (decompToFun malleableUnitBoolCodec) (decompInvFun malleableUnitBoolCodec) ∧
    ¬ LeftInv (decompToFun malleableUnitBoolCodec) (decompInvFun malleableUnitBoolCodec) ∧
    ¬ IsEquiv (decompToFun malleableUnitBoolCodec) (decompInvFun malleableUnitBoolCodec) ∧
    ¬ Nonempty (Equiv Bool (Unit ⊕ Junk malleableUnitBoolCodec)) := by
  refine ⟨malleableUnitBoolCodec_decEnc, ?_, ?_, ?_, ?_⟩
  · rintro (⟨⟩ | ⟨b, hb⟩)
    · rfl
    · cases hb
  · intro hl; have ht := hl true; cases ht
  · intro h; have ht := h.1 true; cases ht
  · rintro ⟨e⟩
    have hsub : ∀ x y : Unit ⊕ Junk malleableUnitBoolCodec, x = y := by
      rintro (⟨⟩ | ⟨_, hb⟩) (⟨⟩ | ⟨_, hb'⟩)
      · rfl
      · cases hb'
      · cases hb
      · cases hb
    have h1 := e.left_inv false
    have h2 := e.left_inv true
    rw [hsub (e.toFun false) (e.toFun true)] at h1
    rw [h1] at h2
    cases h2

/-- Split maps satisfying `RightInv` but failing `LeftInv` (`Bool` ↔ `Unit ⊕ Empty`). -/
def badLeftSplitToFun : Bool → Unit ⊕ Empty := fun _ => Sum.inl ()
def badLeftSplitInvFun : Unit ⊕ Empty → Bool
  | Sum.inl () => false
  | Sum.inr e => Empty.elim e

theorem badLeftSplit_rightInv : RightInv badLeftSplitToFun badLeftSplitInvFun := by
  rintro (⟨⟩ | e)
  · rfl
  · exact Empty.elim e

/-- Tightness of `LeftInv f g` in `decomp_induces_lawful_and_complement`. -/
theorem ce_decomp_induces_drop_leftInv :
    RightInv badLeftSplitToFun badLeftSplitInvFun ∧
    ¬ (DecEnc (codecOfSplit badLeftSplitToFun badLeftSplitInvFun) ∧
       EncDec (codecOfSplit badLeftSplitToFun badLeftSplitInvFun) ∧
       (∀ k : Empty, (codecOfSplit badLeftSplitToFun badLeftSplitInvFun).dec
         (badLeftSplitInvFun (Sum.inr k)) = none) ∧
       (∀ j : Junk (codecOfSplit badLeftSplitToFun badLeftSplitInvFun),
         badLeftSplitInvFun (Sum.inr (junkToC badLeftSplitToFun badLeftSplitInvFun j)) = j.1) ∧
       (∀ (k : Empty) (hj : (codecOfSplit badLeftSplitToFun badLeftSplitInvFun).dec
         (badLeftSplitInvFun (Sum.inr k)) = none),
         junkToC badLeftSplitToFun badLeftSplitInvFun ⟨badLeftSplitInvFun (Sum.inr k), hj⟩ = k) ∧
       (∀ b : Bool,
         Sum.map id Subtype.val
           (decompToFun (codecOfSplit badLeftSplitToFun badLeftSplitInvFun) b) =
         Sum.map id (fun k => badLeftSplitInvFun (Sum.inr k)) (badLeftSplitToFun b))) :=
  ⟨badLeftSplit_rightInv, fun h => ex_codecOfSplit_neg h.2.1⟩

/-- Split maps satisfying `LeftInv` but failing `RightInv` on `Sum.inl` (`Unit` ↔ `Unit ⊕ Unit`). -/
def badRightInlSplitToFun : Unit → Unit ⊕ Unit := fun _ => Sum.inr ()
def badRightInlSplitInvFun : Unit ⊕ Unit → Unit := fun _ => ()

theorem badRightInlSplit_leftInv : LeftInv badRightInlSplitToFun badRightInlSplitInvFun := by
  intro u; cases u; rfl

/-- Tightness of `RightInv f g` (on `Sum.inl`) in `decomp_induces_lawful_and_complement`. -/
theorem ce_decomp_induces_drop_rightInv :
    LeftInv badRightInlSplitToFun badRightInlSplitInvFun ∧
    ¬ (DecEnc (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun) ∧
       EncDec (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun) ∧
       (∀ k : Unit, (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun).dec
         (badRightInlSplitInvFun (Sum.inr k)) = none) ∧
       (∀ j : Junk (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun),
         badRightInlSplitInvFun
           (Sum.inr (junkToC badRightInlSplitToFun badRightInlSplitInvFun j)) = j.1) ∧
       (∀ (k : Unit) (hj : (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun).dec
         (badRightInlSplitInvFun (Sum.inr k)) = none),
         junkToC badRightInlSplitToFun badRightInlSplitInvFun
           ⟨badRightInlSplitInvFun (Sum.inr k), hj⟩ = k) ∧
       (∀ b : Unit,
         Sum.map id Subtype.val
           (decompToFun (codecOfSplit badRightInlSplitToFun badRightInlSplitInvFun) b) =
         Sum.map id (fun k => badRightInlSplitInvFun (Sum.inr k)) (badRightInlSplitToFun b))) := by
  refine ⟨badRightInlSplit_leftInv, ?_⟩
  intro h
  have h0 := h.1 ()
  cases h0

/-- Split maps satisfying `LeftInv` and `RightInv` on `Sum.inl`, but failing `RightInv` on `Sum.inr`:
    shows `RightInv` on `Sum.inr` is specifically needed for the complement characterization. -/
def badRightInrSplitToFun : Unit → Unit ⊕ Bool := fun _ => Sum.inl ()
def badRightInrSplitInvFun : Unit ⊕ Bool → Unit := fun _ => ()

theorem ce_decomp_induces_drop_rightInv_inr :
    LeftInv badRightInrSplitToFun badRightInrSplitInvFun ∧
    (∀ a : Unit, badRightInrSplitToFun (badRightInrSplitInvFun (Sum.inl a)) = Sum.inl a) ∧
    DecEnc (codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun) ∧
    EncDec (codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun) ∧
    ¬ (∀ k : Bool, (codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun).dec
        (badRightInrSplitInvFun (Sum.inr k)) = none) := by
  refine ⟨fun u => by cases u; rfl, fun a => by cases a; rfl,
    fun a => by cases a; rfl, fun b a _ => by cases a; cases b; rfl, ?_⟩
  intro h
  have hf := h false
  cases hf

/-- Helper splits for `codecOfSplit_eq_iff_exists_intertwining_equiv` tightness counterexamples. -/
def emptyBoolSplitToFun : Bool → Empty ⊕ Bool := Sum.inr
def emptyBoolSplitInvFun : Empty ⊕ Bool → Bool
  | Sum.inl e => Empty.elim e
  | Sum.inr b => b

def badEmptyUnitSplitToFun : Bool → Empty ⊕ Unit := fun _ => Sum.inr ()
def badEmptyUnitSplitInvFun : Empty ⊕ Unit → Bool
  | Sum.inl e => Empty.elim e
  | Sum.inr () => false

def unitEmptySplitToFun : Unit → Unit ⊕ Empty := fun _ => Sum.inl ()
def unitEmptySplitInvFun : Unit ⊕ Empty → Unit
  | Sum.inl () => ()
  | Sum.inr e => Empty.elim e

theorem emptyBoolSplit_leftInv : LeftInv emptyBoolSplitToFun emptyBoolSplitInvFun := fun _ => rfl
theorem emptyBoolSplit_rightInv : RightInv emptyBoolSplitToFun emptyBoolSplitInvFun := by
  rintro (e | b); exact Empty.elim e; rfl

theorem badEmptyUnitSplit_rightInv : RightInv badEmptyUnitSplitToFun badEmptyUnitSplitInvFun := by
  rintro (e | ⟨⟩); exact Empty.elim e; rfl

theorem unitEmptySplit_leftInv : LeftInv unitEmptySplitToFun unitEmptySplitInvFun := by
  intro u; cases u; rfl
theorem unitEmptySplit_rightInv : RightInv unitEmptySplitToFun unitEmptySplitInvFun := by
  rintro (⟨⟩ | e); rfl; exact Empty.elim e

/-- Tightness of `hl₁ : LeftInv f₁ g₁` in `codecOfSplit_eq_iff_exists_intertwining_equiv`. -/
theorem ce_codecOfSplit_eq_iff_drop_hl1 :
    RightInv badEmptyUnitSplitToFun badEmptyUnitSplitInvFun ∧
    LeftInv emptyBoolSplitToFun emptyBoolSplitInvFun ∧
    RightInv emptyBoolSplitToFun emptyBoolSplitInvFun ∧
    ¬ (codecOfSplit badEmptyUnitSplitToFun badEmptyUnitSplitInvFun =
        codecOfSplit emptyBoolSplitToFun emptyBoolSplitInvFun ↔
      ∃ (φ : Equiv Unit Bool), ∀ b : Bool,
        emptyBoolSplitToFun b = Sum.map id φ.toFun (badEmptyUnitSplitToFun b)) := by
  refine ⟨badEmptyUnitSplit_rightInv, emptyBoolSplit_leftInv, emptyBoolSplit_rightInv, ?_⟩
  intro hiff
  have heq : codecOfSplit badEmptyUnitSplitToFun badEmptyUnitSplitInvFun =
      codecOfSplit emptyBoolSplitToFun emptyBoolSplitInvFun :=
    Codec.ext (funext fun a => Empty.elim a) (funext fun _ => rfl)
  obtain ⟨φ, _⟩ := hiff.mp heq
  exact ex_equiv_neg ⟨⟨φ.invFun, φ.toFun, φ.right_inv, φ.left_inv⟩⟩

/-- Tightness of `hr₁ : RightInv f₁ g₁` in `codecOfSplit_eq_iff_exists_intertwining_equiv`. -/
theorem ce_codecOfSplit_eq_iff_drop_hr1 :
    LeftInv badRightInrSplitToFun badRightInrSplitInvFun ∧
    LeftInv unitEmptySplitToFun unitEmptySplitInvFun ∧
    RightInv unitEmptySplitToFun unitEmptySplitInvFun ∧
    ¬ (codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun =
        codecOfSplit unitEmptySplitToFun unitEmptySplitInvFun ↔
      ∃ (φ : Equiv Bool Empty), ∀ b : Unit,
        unitEmptySplitToFun b = Sum.map id φ.toFun (badRightInrSplitToFun b)) := by
  refine ⟨fun u => by cases u; rfl, unitEmptySplit_leftInv, unitEmptySplit_rightInv, ?_⟩
  intro hiff
  have heq : codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun =
      codecOfSplit unitEmptySplitToFun unitEmptySplitInvFun :=
    Codec.ext (funext fun u => by cases u; rfl) (funext fun b => by cases b; rfl)
  obtain ⟨φ, _⟩ := hiff.mp heq
  exact Empty.elim (φ.toFun false)

/-- Tightness of `hl₂ : LeftInv f₂ g₂` in `codecOfSplit_eq_iff_exists_intertwining_equiv`. -/
theorem ce_codecOfSplit_eq_iff_drop_hl2 :
    LeftInv emptyBoolSplitToFun emptyBoolSplitInvFun ∧
    RightInv emptyBoolSplitToFun emptyBoolSplitInvFun ∧
    RightInv badEmptyUnitSplitToFun badEmptyUnitSplitInvFun ∧
    ¬ (codecOfSplit emptyBoolSplitToFun emptyBoolSplitInvFun =
        codecOfSplit badEmptyUnitSplitToFun badEmptyUnitSplitInvFun ↔
      ∃ (φ : Equiv Bool Unit), ∀ b : Bool,
        badEmptyUnitSplitToFun b = Sum.map id φ.toFun (emptyBoolSplitToFun b)) := by
  refine ⟨emptyBoolSplit_leftInv, emptyBoolSplit_rightInv, badEmptyUnitSplit_rightInv, ?_⟩
  intro hiff
  have heq : codecOfSplit emptyBoolSplitToFun emptyBoolSplitInvFun =
      codecOfSplit badEmptyUnitSplitToFun badEmptyUnitSplitInvFun :=
    Codec.ext (funext fun a => Empty.elim a) (funext fun _ => rfl)
  obtain ⟨φ, _⟩ := hiff.mp heq
  exact ex_equiv_neg ⟨φ⟩

/-- Tightness of `hr₂ : RightInv f₂ g₂` in `codecOfSplit_eq_iff_exists_intertwining_equiv`. -/
theorem ce_codecOfSplit_eq_iff_drop_hr2 :
    LeftInv unitEmptySplitToFun unitEmptySplitInvFun ∧
    RightInv unitEmptySplitToFun unitEmptySplitInvFun ∧
    LeftInv badRightInrSplitToFun badRightInrSplitInvFun ∧
    ¬ (codecOfSplit unitEmptySplitToFun unitEmptySplitInvFun =
        codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun ↔
      ∃ (φ : Equiv Empty Bool), ∀ b : Unit,
        badRightInrSplitToFun b = Sum.map id φ.toFun (unitEmptySplitToFun b)) := by
  refine ⟨unitEmptySplit_leftInv, unitEmptySplit_rightInv, fun u => by cases u; rfl, ?_⟩
  intro hiff
  have heq : codecOfSplit unitEmptySplitToFun unitEmptySplitInvFun =
      codecOfSplit badRightInrSplitToFun badRightInrSplitInvFun :=
    Codec.ext (funext fun u => by cases u; rfl) (funext fun b => by cases b; rfl)
  obtain ⟨φ, _⟩ := hiff.mp heq
  exact Empty.elim (φ.invFun false)

/-- Tightness of `heq` in `complementEquivOfCodecEq_intertwines`: two mutually inverse
    decompositions with different induced codecs admit no intertwining map. -/
theorem ce_intertwines_drop_heq :
    LeftInv splitBoolFalseToFun splitBoolFalseInvFun ∧
    RightInv splitBoolFalseToFun splitBoolFalseInvFun ∧
    LeftInv splitBoolTrueToFun splitBoolTrueInvFun ∧
    RightInv splitBoolTrueToFun splitBoolTrueInvFun ∧
    ¬ (∃ φ : Unit → Unit, ∀ b : Bool,
        splitBoolTrueToFun b = Sum.map id φ (splitBoolFalseToFun b)) := by
  refine ⟨same_complement_different_codec.1, same_complement_different_codec.2.1,
    same_complement_different_codec.2.2.1, same_complement_different_codec.2.2.2.1, ?_⟩
  rintro ⟨φ, hφ⟩
  have hf := hφ false
  cases hf

/-! ## Additional boundary witnesses and tightness counterexamples -/

/-- Shifts `n : Nat` into the rejected-wire subtype `Junk nonCanonicalBoolCodec` (`b ≥ 3`). -/
def nonCanonicalBoolJunk (n : Nat) : Junk nonCanonicalBoolCodec :=
  ⟨n + 3, rfl⟩

/-- Non-canonical forward map `Nat → Bool ⊕ Junk nonCanonicalBoolCodec`
    sending `0 ↦ inl false`, `1 ↦ inl true`, and `n + 2 ↦ inr ⟨n + 3, rfl⟩`. -/
def nonCanonicalBoolEquivToFun : Nat → Bool ⊕ Junk nonCanonicalBoolCodec
  | 0 => Sum.inl false
  | 1 => Sum.inl true
  | n + 2 => Sum.inr (nonCanonicalBoolJunk n)

/-- Two-sided inverse of `nonCanonicalBoolEquivToFun`. -/
def nonCanonicalBoolEquivInvFun : Bool ⊕ Junk nonCanonicalBoolCodec → Nat
  | Sum.inl false => 0
  | Sum.inl true => 1
  | Sum.inr ⟨0, h⟩ => nomatch h
  | Sum.inr ⟨1, h⟩ => nomatch h
  | Sum.inr ⟨2, h⟩ => nomatch h
  | Sum.inr ⟨n + 3, _⟩ => n + 2

/-- Explicit non-canonical bijection `Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec)`. -/
def nonCanonicalBoolJunkEquiv : Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec) where
  toFun := nonCanonicalBoolEquivToFun
  invFun := nonCanonicalBoolEquivInvFun
  left_inv
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl
  right_inv
    | Sum.inl false => rfl
    | Sum.inl true => rfl
    | Sum.inr ⟨0, h⟩ => by cases h
    | Sum.inr ⟨1, h⟩ => by cases h
    | Sum.inr ⟨2, h⟩ => by cases h
    | Sum.inr ⟨_ + 3, _⟩ => rfl

/-- Bare existence of an equivalence `B ≃ A ⊕ Junk c` does not make `c` lawful:
    `nonCanonicalBoolCodec` satisfies `DecEnc` yet violates `EncDec` (and its canonical
    maps fail `IsEquiv`), while `nonCanonicalBoolJunkEquiv` witnesses
    `Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec)`. -/
theorem nonCanonicalBoolCodec_not_encDec_yet_admits_equiv :
    DecEnc nonCanonicalBoolCodec ∧
    ¬ EncDec nonCanonicalBoolCodec ∧
    ¬ IsEquiv (decompToFun nonCanonicalBoolCodec) (decompInvFun nonCanonicalBoolCodec) ∧
    Nonempty (Equiv Nat (Bool ⊕ Junk nonCanonicalBoolCodec)) :=
  ⟨nonCanonicalBoolCodec_decEnc, ex_encDec_neg, ex_decomp_neg_malleable,
    ⟨nonCanonicalBoolJunkEquiv⟩⟩

/-- Always-failing framed codec on `Bool` with empty codewords `enc _ = []`:
    has two distinct source values (`false ≠ true`) and satisfies `PrefixEncDec`,
    yet violates `PrefixDecEnc` and `NonEmptyEnc`. -/
def emptyBoolFailFramedCodec : FramedCodec Bool Bool where
  enc _ := []
  decPrefix _ := none

/-- Tightness of `hpde : PrefixDecEnc fc` in `nonEmptyEnc_of_prefixDecEnc_of_ne`:
    `Bool` has distinct elements `false ≠ true` and `emptyBoolFailFramedCodec`
    satisfies `PrefixEncDec`, while `NonEmptyEnc` fails when `PrefixDecEnc` is dropped. -/
theorem ce_nonEmptyEnc_of_prefixDecEnc_of_ne_drop_hpde :
    (false ≠ true) ∧
    PrefixEncDec emptyBoolFailFramedCodec ∧
    ¬ PrefixDecEnc emptyBoolFailFramedCodec ∧
    ¬ NonEmptyEnc emptyBoolFailFramedCodec.enc := by
  refine ⟨Bool.noConfusion, (fun _ _ _ h => by cases h), ?_, ?_⟩
  · intro h; have h0 := h false []; cases h0
  · intro h; exact h false rfl

/-- General remainder-discarding boundary: for any framed codec `fc` satisfying
    `PrefixDecEnc fc`, `firstOnly fc` (`xs ↦ (fc.decPrefix xs).map Prod.fst`) satisfies
    `DecEnc`, yet whenever `A` and the token type `β` are inhabited (`a : A`, `t : β`) it
    violates both `DecInj` and `EncDec` because `fc.enc a` and `fc.enc a ++ [t]` have
    distinct lengths and both decode to `a`. -/
theorem firstOnly_decEnc_and_not_decInj {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) (a : A) (t : β) :
    DecEnc (firstOnly fc) ∧ ¬ DecInj (firstOnly fc) ∧ ¬ EncDec (firstOnly fc) := by
  have hde : DecEnc (firstOnly fc) := fun a' => by
    show (fc.decPrefix (fc.enc a')).map Prod.fst = some a'
    have h0 := hpde a' []
    rw [List.append_nil] at h0
    rw [h0]
    rfl
  have hni : ¬ DecInj (firstOnly fc) := fun hinj => by
    have h1 : (firstOnly fc).dec (fc.enc a) = some a := hde a
    have h2 : (firstOnly fc).dec (fc.enc a ++ [t]) = some a := by
      show (fc.decPrefix (fc.enc a ++ [t])).map Prod.fst = some a
      rw [hpde a [t]]
      rfl
    have heq := hinj _ _ a h1 h2
    have hlen := congrArg List.length heq
    rw [List.length_append] at hlen
    exact Nat.ne_of_lt (Nat.lt_succ_self (fc.enc a).length) hlen
  refine ⟨hde, hni, fun hed => hni ?_⟩
  intro b₁ b₂ a' hb₁ hb₂
  exact (hed b₁ a' hb₁).symm.trans (hed b₂ a' hb₂)

/-- Non-vacuous negative example for `Codec.id`: `Codec.id Bool` is distinct both from
    the lawful non-identity codec `boolNotCodec` and from the failing codec `alwaysFailBoolCodec`. -/
theorem ex_codecId_ne_boolNot :
    Codec.id Bool ≠ boolNotCodec ∧ Codec.id Bool ≠ alwaysFailBoolCodec := by
  constructor
  · intro h
    have hf := congrFun (congrArg Codec.enc h) false
    cases hf
  · intro h
    have hf := congrFun (congrArg Codec.dec h) false
    cases hf

end Toy.Codec
