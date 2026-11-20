import Toy.Codec.Defs
import Toy.Codec.Examples
import Toy.Codec.Counterexamples

/-!
# Non-vacuity witnesses and supporting structural lemmas

Every theorem in `Toy.Codec.Statements` has a corresponding concrete,
non-degenerate non-vacuity witness here proving that all of its hypotheses
hold simultaneously (and, for hypothesis-free equivalences, demonstrating both
positive and negative instances). Supporting unconditional and derivability
lemmas cited by the result cards are also proved here without `sorry`.
-/

namespace Toy.Codec

/-! ## Unconditional structural identities and derivability lemmas (fully proved) -/

/-- `(classicalCodec f).enc = f` definitionally. -/
theorem classicalCodec_enc {A : Type u} {B : Type v} (f : A → B) :
    (classicalCodec f).enc = f := rfl

/-- `codecOfFiberSplit f s` always satisfies `EncDec`, without needing `Function.Injective f`. -/
theorem codecOfFiberSplit_encDec {A : Type u} {B : Type v}
    (f : A → B) (s : FiberSplit f) : EncDec (codecOfFiberSplit f s) := by
  intro b a h
  change (match s b with | PSum.inl ⟨a', _⟩ => some a' | PSum.inr _ => none) = some a at h
  cases hs : s b with
  | inl p =>
    rw [hs] at h
    cases h
    exact p.2
  | inr _ =>
    rw [hs] at h
    cases h

/-- `canonicalize c` always satisfies `EncDec`, without needing `DecEnc c` or `Function.Injective c.enc`. -/
theorem canonicalize_encDec {A : Type u} {B : Type v} [DecidableEq B]
    (c : Codec A B) : EncDec (canonicalize c) := by
  intro b a h
  unfold canonicalize at h
  dsimp only at h
  split at h
  · split at h
    · rename_i he; cases h; exact he
    · cases h
  · cases h

/-- `EncDec c` implies `DecInj c` unconditionally (without `DecEnc c`). -/
theorem encDec_imp_decInj {A : Type u} {B : Type v} (c : Codec A B)
    (hed : EncDec c) : DecInj c := by
  intro b₁ b₂ a h₁ h₂
  exact (hed b₁ a h₁).symm.trans (hed b₂ a h₂)

/-- Equivalent characterization of `DecEnc ∧ EncDec` matching EverParse §2.1's
    "correct and exact" (`DecEnc` plus accepting only wire values in `range enc`). -/
theorem lawful_iff_decEnc_and_accepts_only_range {A : Type u} {B : Type v} (c : Codec A B) :
    (DecEnc c ∧ EncDec c) ↔
    (DecEnc c ∧ ∀ b : B, (c.dec b).isSome = true → ∃ a : A, c.enc a = b) := by
  constructor
  · rintro ⟨hde, hed⟩
    refine ⟨hde, fun b hs => ?_⟩
    cases hd : c.dec b with
    | none => rw [hd] at hs; cases hs
    | some a => exact ⟨a, hed b a hd⟩
  · rintro ⟨hde, hex⟩
    refine ⟨hde, fun b a hd => ?_⟩
    have hs : (c.dec b).isSome = true := by rw [hd]; rfl
    obtain ⟨a', ha'⟩ := hex b hs
    subst ha'
    rw [hde a'] at hd
    cases hd
    rfl

/-- Dual uniqueness: equal decoders determine equal encoders using only `DecEnc c₁`
    and `EncDec c₂`. -/
theorem enc_unique_of_dec_eq {A : Type u} {B : Type v} (c₁ c₂ : Codec A B)
    (hdec : c₁.dec = c₂.dec) (hde₁ : DecEnc c₁) (hed₂ : EncDec c₂) :
    c₁.enc = c₂.enc := by
  funext a
  have h := hde₁ a
  rw [hdec] at h
  exact (hed₂ _ a h).symm

/-- Each half of `lawful_dec_isSome_iff_mem_range` uses a single round-trip law. -/
theorem isSome_imp_mem_range_of_encDec {A : Type u} {B : Type v} (c : Codec A B)
    (hed : EncDec c) (b : B) : (c.dec b).isSome = true → ∃ a : A, c.enc a = b := by
  intro h
  cases hd : c.dec b with
  | none => rw [hd] at h; cases h
  | some a => exact ⟨a, hed b a hd⟩

theorem mem_range_imp_isSome_of_decEnc {A : Type u} {B : Type v} (c : Codec A B)
    (hde : DecEnc c) (b : B) : (∃ a : A, c.enc a = b) → (c.dec b).isSome = true := by
  rintro ⟨a, rfl⟩
  rw [hde a]; rfl

/-- Constructive derivation (zero axioms, no codec laws needed) of the conclusion of
    `junk_iff_not_in_image_of_lawful` from that of `lawful_dec_isSome_iff_mem_range`. -/
theorem eq_none_iff_of_isSome_iff {A : Type u} {B : Type v} (c : Codec A B) (b : B)
    (h : (c.dec b).isSome = true ↔ ∃ a : A, c.enc a = b) :
    c.dec b = none ↔ ∀ a : A, c.enc a ≠ b := by
  constructor
  · intro hn a ha
    have hs := h.mpr ⟨a, ha⟩
    rw [hn] at hs
    cases hs
  · intro hall
    cases hd : c.dec b with
    | none => rfl
    | some _ =>
      obtain ⟨a, ha⟩ := h.mp (by rw [hd]; rfl)
      exact absurd ha (hall a)

/-- Exact relation between indexed `PrefixFree` and set-level `ImagePrefixFree`:
    `PrefixFree enc` holds iff `enc` is injective and `ImagePrefixFree enc` holds. -/
theorem prefixFree_iff_injective_and_imagePrefixFree {A : Type u} {β : Type v}
    (enc : A → List β) :
    PrefixFree enc ↔ (Function.Injective enc ∧ ImagePrefixFree enc) := by
  constructor
  · intro h
    refine ⟨fun a₁ a₂ he => h a₁ a₂ [] (by rw [List.append_nil]; exact he), ?_⟩
    intro a₁ a₂ s he
    have ha := h a₁ a₂ s he
    subst ha
    have hlen := congrArg List.length he
    rw [List.length_append] at hlen
    have hs0 : s.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero hs0
  · rintro ⟨hinj, himg⟩ a₁ a₂ s he
    have hs := himg a₁ a₂ s he
    subst hs
    rw [List.append_nil] at he
    exact hinj he

/-- Under `PrefixDecEnc`, an empty codeword `fc.enc a₀ = []` forces every value of `A`
    to equal `a₀` (so `A` is a subsingleton). -/
theorem prefixDecEnc_nil_codeword_imp_subsingleton {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) (a₀ : A) (h0 : fc.enc a₀ = []) :
    ∀ a : A, a = a₀ := by
  intro a
  have h1 := hpde a₀ (fc.enc a)
  rw [h0, List.nil_append] at h1
  have h2 := hpde a []
  rw [List.append_nil, h1] at h2
  exact (Prod.mk.inj (Option.some.inj h2)).1.symm

/-- Under `PrefixFree`, an empty codeword `enc a₀ = []` likewise forces every value of
    `A` to equal `a₀`. -/
theorem prefixFree_nil_codeword_imp_subsingleton {A : Type u} {β : Type v}
    (enc : A → List β) (hpf : PrefixFree enc) (a₀ : A) (h0 : enc a₀ = []) :
    ∀ a : A, a = a₀ := by
  intro a
  exact (hpf a₀ a (enc a) (by rw [h0, List.nil_append])).symm

/-- Consequently, whenever `A` has two distinct elements, `NonEmptyEnc fc.enc` is
    automatically derivable from `PrefixDecEnc fc`. -/
theorem nonEmptyEnc_of_prefixDecEnc_of_ne {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hpde : PrefixDecEnc fc) {x y : A} (hxy : x ≠ y) :
    NonEmptyEnc fc.enc := fun a ha =>
  hxy ((prefixDecEnc_nil_codeword_imp_subsingleton fc hpde a ha x).trans
    (prefixDecEnc_nil_codeword_imp_subsingleton fc hpde a ha y).symm)

/-- Unconditional necessity: `DecEnc (listCodec fc)` implies `NonEmptyEnc fc.enc`
    for every framed codec. -/
theorem nonEmptyEnc_of_listCodec_decEnc {A : Type u} {β : Type v}
    (fc : FramedCodec A β) (hde : DecEnc (listCodec fc)) : NonEmptyEnc fc.enc := by
  intro a ha
  have h1 := hde [a]
  have h0 := hde []
  change decList fc (fc.enc a ++ []) = some [a] at h1
  change decList fc [] = some [] at h0
  rw [ha, List.append_nil, h0] at h1
  cases h1

/-- For every codec (without any laws), `c.dec` factors through `decompToFun c` and `inlMatcher`. -/
theorem dec_eq_inlMatcher_decompToFun {A : Type u} {B : Type v}
    (c : Codec A B) (b : B) : c.dec b = inlMatcher (decompToFun c b) := by
  unfold decompToFun
  split <;> simp_all [inlMatcher]

/-- For every codec (without any laws), `codecOfSplit (decompToFun c) (decompInvFun c) = c`. -/
theorem codecOfSplit_decomp_eq {A : Type u} {B : Type v} (c : Codec A B) :
    codecOfSplit (decompToFun c) (decompInvFun c) = c := by
  cases c with
  | mk e d =>
    unfold codecOfSplit
    congr 1
    funext b
    exact (dec_eq_inlMatcher_decompToFun ⟨e, d⟩ b).symm

/-- `decompToFun c (c.enc a) = Sum.inl a` is a direct specialization of
    `RightInv (decompToFun c) (decompInvFun c)` at `Sum.inl a`. -/
theorem decompToFun_enc_of_rightInv {A : Type u} {B : Type v} (c : Codec A B)
    (hr : RightInv (decompToFun c) (decompInvFun c)) (a : A) :
    decompToFun c (c.enc a) = Sum.inl a :=
  hr (Sum.inl a)

/-- The reverse direction of `codecOfSplit_eq_iff_exists_intertwining_equiv` holds
    for any intertwining function `φ : C₁ → C₂` using only `hr₁` and `hl₂`. -/
theorem codecOfSplit_eq_of_intertwining_fun
    {A : Type u} {B : Type v} {C₁ : Type w₁} {C₂ : Type w₂}
    (f₁ : B → A ⊕ C₁) (g₁ : A ⊕ C₁ → B)
    (f₂ : B → A ⊕ C₂) (g₂ : A ⊕ C₂ → B)
    (hr₁ : RightInv f₁ g₁) (hl₂ : LeftInv f₂ g₂)
    (φ : C₁ → C₂) (hφ : ∀ b : B, f₂ b = Sum.map id φ (f₁ b)) :
    codecOfSplit f₁ g₁ = codecOfSplit f₂ g₂ := by
  apply Codec.ext
  · funext a
    change g₁ (Sum.inl a) = g₂ (Sum.inl a)
    have h1 : f₂ (g₁ (Sum.inl a)) = Sum.inl a := by
      rw [hφ, hr₁]; rfl
    have h2 := hl₂ (g₁ (Sum.inl a))
    rw [h1] at h2
    exact h2.symm
  · funext b
    change inlMatcher (f₁ b) = inlMatcher (f₂ b)
    rw [hφ]
    cases f₁ b <;> rfl

/-! ## Non-vacuity witnesses for characterization, bijection, and canonicalization theorems -/

theorem nv_decEnc_imp_enc_injective : DecEnc boolToNatCodec :=
  boolToNatCodec_decEnc

theorem nv_lawful_iff_dec_eq_some_iff :
    (DecEnc boolToNatCodec ∧ EncDec boolToNatCodec) ∧
    (∀ (b : Nat) (a : Bool), boolToNatCodec.dec b = some a ↔ boolToNatCodec.enc a = b) := by
  refine ⟨boolToNatCodec_lawful, fun b a => ⟨boolToNatCodec_encDec b a, ?_⟩⟩
  intro h
  rw [← h]
  exact boolToNatCodec_decEnc a

theorem nv_decEqSomeIff_imp_enc_injective :
    ∀ (b : Nat) (a : Bool), boolToNatCodec.dec b = some a ↔ boolToNatCodec.enc a = b :=
  nv_lawful_iff_dec_eq_some_iff.2

theorem nv_lawful_iff_decEnc_and_decInj :
    (DecEnc boolToNatCodec ∧ EncDec boolToNatCodec) ∧
    (DecEnc boolToNatCodec ∧ DecInj boolToNatCodec) :=
  ⟨boolToNatCodec_lawful, ⟨boolToNatCodec_decEnc, boolToNatCodec_decInj⟩⟩

theorem nv_dec_unique_of_lawful :
    boolToNatCodec.enc = (codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit).enc ∧
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec ∧
    DecEnc (codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit) ∧
    EncDec (codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit) :=
  ⟨rfl, boolToNatCodec_decEnc, boolToNatCodec_encDec,
    ex_fiberSplit_pos.1, ex_fiberSplit_pos.2⟩

theorem boolToNat_enc_injective : Function.Injective boolToNatCodec.enc := by
  intro a₁ a₂ h
  cases a₁ <;> cases a₂ <;> cases h <;> rfl

theorem nv_classicalCodec_decEnc_of_injective :
    Function.Injective boolToNatCodec.enc :=
  boolToNat_enc_injective

theorem nv_classicalCodec_encDec :
    EncDec (classicalCodec boolToNatCodec.enc) ∧
    EncDec (classicalCodec (fun _ : Bool => ())) := by
  constructor
  · intro b a h
    unfold classicalCodec classicalDec at h
    dsimp only at h
    split at h
    · rename_i hex; cases h; exact Classical.choose_spec hex
    · cases h
  · intro b a h
    unfold classicalCodec classicalDec at h
    dsimp only at h
    split at h
    · rename_i hex; cases h; exact Classical.choose_spec hex
    · cases h

theorem nv_classicalCodec_recover_of_lawful :
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec :=
  boolToNatCodec_lawful

theorem nv_codecOfFiberSplit_decEnc_of_injective :
    Function.Injective boolToNatCodec.enc ∧ Nonempty (FiberSplit boolToNatCodec.enc) :=
  ⟨boolToNat_enc_injective, ⟨boolToNatFiberSplit⟩⟩

theorem nv_codecOfFiberSplit_eq_of_lawful :
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec ∧
    codecOfFiberSplit boolToNatCodec.enc boolToNatFiberSplit = boolToNatCodec := by
  refine ⟨boolToNatCodec_decEnc, boolToNatCodec_encDec, ?_⟩
  apply Codec.ext
  · rfl
  · funext b
    match b with
    | 0 => rfl
    | 1 => rfl
    | _ + 2 => rfl

theorem nv_lawful_dec_isSome_iff_mem_range :
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec :=
  boolToNatCodec_lawful

theorem nv_junk_iff_not_in_image_of_lawful :
    DecEnc boolToNatCodec ∧ EncDec boolToNatCodec :=
  boolToNatCodec_lawful

theorem nv_canonicalize_decEnc_of_decEnc :
    DecEnc nonCanonicalBoolCodec ∧ ¬ EncDec nonCanonicalBoolCodec ∧
    DecEnc (canonicalize nonCanonicalBoolCodec) ∧ EncDec (canonicalize nonCanonicalBoolCodec) :=
  ⟨nonCanonicalBoolCodec_decEnc, ex_encDec_neg, ex_canonicalize_pos.1.1, ex_canonicalize_pos.1.2⟩

/-! ## Non-vacuity witnesses for closure theorems -/

theorem nv_comp_decEnc : DecEnc boolToNatCodec ∧ DecEnc natSuccCodec :=
  ⟨boolToNatCodec_decEnc, natSuccCodec_decEnc⟩

theorem nv_comp_encDec : EncDec boolToNatCodec ∧ EncDec natSuccCodec :=
  ⟨boolToNatCodec_encDec, natSuccCodec_encDec⟩

theorem nv_prod_decEnc : DecEnc boolToNatCodec ∧ DecEnc natSuccCodec :=
  ⟨boolToNatCodec_decEnc, natSuccCodec_decEnc⟩

theorem nv_prod_encDec : EncDec boolToNatCodec ∧ EncDec natSuccCodec :=
  ⟨boolToNatCodec_encDec, natSuccCodec_encDec⟩

theorem nv_sum_decEnc : DecEnc boolToNatCodec ∧ DecEnc natSuccCodec :=
  ⟨boolToNatCodec_decEnc, natSuccCodec_decEnc⟩

theorem nv_sum_encDec : EncDec boolToNatCodec ∧ EncDec natSuccCodec :=
  ⟨boolToNatCodec_encDec, natSuccCodec_encDec⟩

/-! ## Non-vacuity witnesses for framed codec theorems -/

theorem nv_framed_lawful_iff_decPrefix_eq_some_iff :
    (PrefixDecEnc varLenBoolFramedCodec ∧ PrefixEncDec varLenBoolFramedCodec) ∧
    (∀ (xs : List Bool) (a : Bool) (rest : List Bool),
      varLenBoolFramedCodec.decPrefix xs = some (a, rest) ↔
        xs = varLenBoolFramedCodec.enc a ++ rest) := by
  refine ⟨⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixEncDec⟩, ?_⟩
  intro xs a rest
  refine ⟨varLenBoolFramedCodec_prefixEncDec xs a rest, fun h => ?_⟩
  rw [h]
  exact varLenBoolFramedCodec_prefixDecEnc a rest

theorem nv_prefixDecEnc_imp_prefixFree : PrefixDecEnc varLenBoolFramedCodec :=
  varLenBoolFramedCodec_prefixDecEnc

theorem nv_seq_prefixDecEnc :
    PrefixDecEnc varLenBoolFramedCodec ∧ PrefixDecEnc varLenBoolFramedCodec :=
  ⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_prefixDecEnc⟩

theorem nv_seq_prefixEncDec :
    PrefixEncDec varLenBoolFramedCodec ∧ PrefixEncDec varLenBoolFramedCodec :=
  ⟨varLenBoolFramedCodec_prefixEncDec, varLenBoolFramedCodec_prefixEncDec⟩

/-- Exercises both a positive `PrefixDecEnc` instance where `NonEmptyEnc` (and hence
    `DecEnc (listCodec _)`) holds (`varLenBoolFramedCodec`) and a negative `PrefixDecEnc`
    instance where both sides fail (`emptyUnitFramedCodec`). -/
theorem nv_listCodec_decEnc_iff_nonEmptyEnc :
    (PrefixDecEnc varLenBoolFramedCodec ∧ NonEmptyEnc varLenBoolFramedCodec.enc) ∧
    (PrefixDecEnc emptyUnitFramedCodec ∧
      ¬ NonEmptyEnc emptyUnitFramedCodec.enc ∧
      ¬ DecEnc (listCodec emptyUnitFramedCodec)) :=
  ⟨⟨varLenBoolFramedCodec_prefixDecEnc, varLenBoolFramedCodec_nonEmptyEnc⟩,
   ⟨emptyUnitFramedCodec_prefixDecEnc, ex_nonEmptyEnc_neg, ex_listCodec_neg⟩⟩

theorem nv_listCodec_encDec : PrefixEncDec varLenBoolFramedCodec :=
  varLenBoolFramedCodec_prefixEncDec

/-! ## Non-vacuity witnesses for prism and complement theorems -/

theorem nv_decomp_isEquiv_iff_lawful :
    (IsEquiv (decompToFun boolToNatCodec) (decompInvFun boolToNatCodec) ∧
      DecEnc boolToNatCodec ∧ EncDec boolToNatCodec) ∧
    (¬ IsEquiv (decompToFun nonCanonicalBoolCodec) (decompInvFun nonCanonicalBoolCodec) ∧
      ¬ EncDec nonCanonicalBoolCodec) ∧
    (¬ IsEquiv (decompToFun alwaysFailUnitCodec) (decompInvFun alwaysFailUnitCodec) ∧
      ¬ DecEnc alwaysFailUnitCodec) := by
  refine ⟨⟨ex_decomp_pos, boolToNatCodec_lawful⟩,
    ⟨ex_decomp_neg_malleable, ex_encDec_neg⟩,
    ⟨ex_decomp_neg_failing, ?_⟩⟩
  intro h
  have h0 := h ()
  cases h0

theorem nv_decomp_induces_lawful_and_complement :
    LeftInv natBoolSplitToFun natBoolSplitInvFun ∧
    RightInv natBoolSplitToFun natBoolSplitInvFun :=
  ⟨natBoolSplit_leftInv, natBoolSplit_rightInv⟩

/-- Explicit complement equivalence `Equiv Nat { n : Nat // 2 ≤ n }` intertwining
    `natBoolSplitToFun` and `natBoolSubSplitToFun`. -/
def natBoolSubEquiv : Equiv Nat { n : Nat // 2 ≤ n } where
  toFun n := ⟨n + 2, Nat.le_add_left 2 n⟩
  invFun k := k.1 - 2
  left_inv n := by show n + 2 - 2 = n; omega
  right_inv k := by
    obtain ⟨k, hk⟩ := k
    show (⟨k - 2 + 2, _⟩ : { n : Nat // 2 ≤ n }) = ⟨k, hk⟩
    congr 1
    omega

/-- Exercises both sides of `codecOfSplit_eq_iff_exists_intertwining_equiv`:
    1. `(natBoolSplitToFun, natBoolSplitInvFun)` and `(natBoolSubSplitToFun, natBoolSubSplitInvFun)`
       satisfy all four inverse hypotheses, induce equal codecs, and are intertwined by `natBoolSubEquiv`;
    2. `(splitBoolFalseToFun, splitBoolFalseInvFun)` and `(splitBoolTrueToFun, splitBoolTrueInvFun)`
       satisfy all four inverse hypotheses, induce distinct codecs, and admit no intertwining equivalence. -/
theorem nv_codecOfSplit_eq_iff_exists_intertwining_equiv :
    (LeftInv natBoolSplitToFun natBoolSplitInvFun ∧
     RightInv natBoolSplitToFun natBoolSplitInvFun ∧
     LeftInv natBoolSubSplitToFun natBoolSubSplitInvFun ∧
     RightInv natBoolSubSplitToFun natBoolSubSplitInvFun ∧
     codecOfSplit natBoolSplitToFun natBoolSplitInvFun =
       codecOfSplit natBoolSubSplitToFun natBoolSubSplitInvFun ∧
     (∀ b : Nat, natBoolSubSplitToFun b =
       Sum.map id natBoolSubEquiv.toFun (natBoolSplitToFun b))) ∧
    (LeftInv splitBoolFalseToFun splitBoolFalseInvFun ∧
     RightInv splitBoolFalseToFun splitBoolFalseInvFun ∧
     LeftInv splitBoolTrueToFun splitBoolTrueInvFun ∧
     RightInv splitBoolTrueToFun splitBoolTrueInvFun ∧
     codecOfSplit splitBoolFalseToFun splitBoolFalseInvFun ≠
       codecOfSplit splitBoolTrueToFun splitBoolTrueInvFun ∧
     ¬ (∃ φ : Equiv Unit Unit, ∀ b : Bool,
         splitBoolTrueToFun b = Sum.map id φ.toFun (splitBoolFalseToFun b))) := by
  refine ⟨⟨natBoolSplit_leftInv, natBoolSplit_rightInv,
    natBoolSubSplit_leftInv, natBoolSubSplit_rightInv,
    natBoolSplit_eq_subSplit, ?_⟩,
    ⟨same_complement_different_codec.1,
     same_complement_different_codec.2.1,
     same_complement_different_codec.2.2.1,
     same_complement_different_codec.2.2.2.1,
     same_complement_different_codec.2.2.2.2.2.1,
     same_complement_different_codec.2.2.2.2.2.2⟩⟩
  intro n
  match n with
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-! ## Additional non-vacuity and general boundary lemmas -/

/-- Non-vacuity witness for `nonEmptyEnc_of_prefixDecEnc_of_ne`: `varLenBoolFramedCodec`
    satisfies `PrefixDecEnc` on `Bool` (`false ≠ true`) and has non-empty codewords. -/
theorem nv_nonEmptyEnc_of_prefixDecEnc_of_ne :
    PrefixDecEnc varLenBoolFramedCodec ∧
    (false ≠ true) ∧
    NonEmptyEnc varLenBoolFramedCodec.enc :=
  ⟨varLenBoolFramedCodec_prefixDecEnc, Bool.noConfusion, varLenBoolFramedCodec_nonEmptyEnc⟩

/-- General form of the complement-split boundary remark: `LeftInv f g` together with
    `RightInv` restricted to `Sum.inl` already suffices for `DecEnc` and `EncDec` of
    `codecOfSplit f g` (`RightInv` on `Sum.inr` is needed only to identify `C` with
    `Junk (codecOfSplit f g)`). -/
theorem codecOfSplit_lawful_of_leftInv_and_rightInv_inl
    {A : Type u} {B : Type v} {C : Type w}
    (f : B → A ⊕ C) (g : A ⊕ C → B)
    (hl : LeftInv f g)
    (hr_inl : ∀ a : A, f (g (Sum.inl a)) = Sum.inl a) :
    DecEnc (codecOfSplit f g) ∧ EncDec (codecOfSplit f g) := by
  constructor
  · intro a
    show inlMatcher (f (g (Sum.inl a))) = some a
    rw [hr_inl a]
    rfl
  · intro b a h
    change inlMatcher (f b) = some a at h
    show g (Sum.inl a) = b
    cases hf : f b with
    | inl a' => rw [hf] at h; cases h; rw [← hf, hl]
    | inr _ => rw [hf] at h; cases h

/-- Left-biased untagged union of two codecs sharing a single wire type `B`
    (cf. Isabelle AFP `Optics` `prism_plus` and Hackage `partial-isomorphisms` `(|||)`). -/
def untaggedSum {A₁ : Type u₁} {A₂ : Type u₂} {B : Type v}
    (c₁ : Codec A₁ B) (c₂ : Codec A₂ B) : Codec (A₁ ⊕ A₂) B where
  enc
    | Sum.inl a₁ => c₁.enc a₁
    | Sum.inr a₂ => c₂.enc a₂
  dec b :=
    match c₁.dec b with
    | some a₁ => some (Sum.inl a₁)
    | none => (c₂.dec b).map Sum.inr

/-- Any untagged union codec with encoder `Sum.elim c₁.enc c₂.enc` that satisfies `DecEnc`
    necessarily has disjoint branch encoder images (`∀ a₁ a₂, c₁.enc a₁ ≠ c₂.enc a₂`). -/
theorem untaggedSum_decEnc_imp_disjoint_images
    {A₁ : Type u₁} {A₂ : Type u₂} {B : Type v}
    (enc₁ : A₁ → B) (enc₂ : A₂ → B) (dec : B → Option (A₁ ⊕ A₂))
    (hde : DecEnc ⟨fun s => match s with | Sum.inl a₁ => enc₁ a₁ | Sum.inr a₂ => enc₂ a₂, dec⟩) :
    ∀ (a₁ : A₁) (a₂ : A₂), enc₁ a₁ ≠ enc₂ a₂ := by
  intro a₁ a₂ heq
  have h₁ : dec (enc₁ a₁) = some (Sum.inl a₁) := hde (Sum.inl a₁)
  have h₂ : dec (enc₂ a₂) = some (Sum.inr a₂) := hde (Sum.inr a₂)
  rw [heq, h₂] at h₁
  cases h₁

/-- When both branch codecs `c₁` and `c₂` are lawful (`DecEnc ∧ EncDec`), their
    untagged union `untaggedSum c₁ c₂` into a shared wire type `B` is lawful if and
    only if `c₁.enc` and `c₂.enc` have disjoint images. -/
theorem untaggedSum_lawful_iff_disjoint_images
    {A₁ : Type u₁} {A₂ : Type u₂} {B : Type v}
    (c₁ : Codec A₁ B) (c₂ : Codec A₂ B)
    (hde₁ : DecEnc c₁) (hed₁ : EncDec c₁)
    (hde₂ : DecEnc c₂) (hed₂ : EncDec c₂) :
    Lawful (untaggedSum c₁ c₂) ↔ ∀ (a₁ : A₁) (a₂ : A₂), c₁.enc a₁ ≠ c₂.enc a₂ := by
  constructor
  · intro hlaw
    exact untaggedSum_decEnc_imp_disjoint_images c₁.enc c₂.enc (untaggedSum c₁ c₂).dec hlaw.1
  · intro hdisj
    constructor
    · rintro (a₁ | a₂)
      · show (match c₁.dec (c₁.enc a₁) with
          | some x => some (Sum.inl x) | none => (c₂.dec (c₁.enc a₁)).map Sum.inr) =
            some (Sum.inl a₁)
        rw [hde₁ a₁]
      · show (match c₁.dec (c₂.enc a₂) with
          | some x => some (Sum.inl x) | none => (c₂.dec (c₂.enc a₂)).map Sum.inr) =
            some (Sum.inr a₂)
        cases hc₁ : c₁.dec (c₂.enc a₂) with
        | some a₁ => exact absurd (hed₁ _ a₁ hc₁) (hdisj a₁ a₂)
        | none => rw [hde₂ a₂]; rfl
    · intro b s hs
      change (match c₁.dec b with
        | some x => some (Sum.inl x) | none => (c₂.dec b).map Sum.inr) = some s at hs
      cases hc₁ : c₁.dec b with
      | some a₁ =>
        rw [hc₁] at hs
        cases hs
        exact hed₁ b a₁ hc₁
      | none =>
        rw [hc₁] at hs
        cases hc₂ : c₂.dec b with
        | none => rw [hc₂] at hs; cases hs
        | some a₂ =>
          rw [hc₂] at hs
          cases hs
          exact hed₂ b a₂ hc₂

/-! ## Bare `encList` list as the first field of a lawful `FramedCodec.seq` record

`no_prefixDecEnc_for_encList` shows that no framed codec whose encoder is `encList enc`
satisfies `PrefixDecEnc`, so `seq_prefixDecEnc` never applies to a record with such a
field. This is not an impossibility result: the record below has a bare `encList`-encoded
list as its first field, no length prefix and no terminator, and is still lawful, because
the following field's codewords share no token with the element codewords. -/

/-- Element encoder for the bare-list positive control: `false ↦ [0]`, `true ↦ [1]`. -/
def bareListElemEnc : Bool → List Nat
  | false => [0]
  | true => [1]

/-- Greedy list reader: consume element tokens `0`/`1` until any other token or the end
    of the input, and return the decoded elements together with the remaining tokens. -/
def bareListGreedy : List Nat → List Bool × List Nat
  | 0 :: r => ((bareListGreedy r).1.cons false, (bareListGreedy r).2)
  | 1 :: r => ((bareListGreedy r).1.cons true, (bareListGreedy r).2)
  | r => ([], r)

/-- Framed codec for `List Bool` with the bare encoder `encList bareListElemEnc`
    (no length prefix, no terminator) and the greedy prefix decoder. -/
def bareListFc : FramedCodec (List Bool) Nat where
  enc := encList bareListElemEnc
  decPrefix xs := some (bareListGreedy xs)

/-- An ordinary `Nat` field `n ↦ [n + 2]` whose codewords use only tokens `≥ 2`
    (no length prefix, no terminator). -/
def natFieldFc : FramedCodec Nat Nat where
  enc n := [n + 2]
  decPrefix
    | (k + 2) :: r => some (k, r)
    | _ => none

theorem bareListGreedy_encList (xs : List Bool) (n : Nat) (rest : List Nat) :
    bareListGreedy (encList bareListElemEnc xs ++ (n + 2) :: rest) = (xs, (n + 2) :: rest) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · show bareListGreedy (0 :: (encList bareListElemEnc bs ++ (n + 2) :: rest)) = _
      simp only [bareListGreedy, ih]
    · show bareListGreedy (1 :: (encList bareListElemEnc bs ++ (n + 2) :: rest)) = _
      simp only [bareListGreedy, ih]

theorem bareListGreedy_sound : ∀ (ys : List Nat),
    ys = encList bareListElemEnc (bareListGreedy ys).1 ++ (bareListGreedy ys).2
  | [] => rfl
  | 0 :: r => by
      have ih := bareListGreedy_sound r
      simp only [bareListGreedy]
      show 0 :: r = [0] ++ (encList bareListElemEnc (bareListGreedy r).1 ++ (bareListGreedy r).2)
      rw [← ih]; rfl
  | 1 :: r => by
      have ih := bareListGreedy_sound r
      simp only [bareListGreedy]
      show 1 :: r = [1] ++ (encList bareListElemEnc (bareListGreedy r).1 ++ (bareListGreedy r).2)
      rw [← ih]; rfl
  | (k + 2) :: r => rfl

theorem bareListSeq_decPrefix_eq (ys : List Nat) :
    (bareListFc.seq natFieldFc).decPrefix ys =
      (natFieldFc.decPrefix (bareListGreedy ys).2).map
        (fun p => (((bareListGreedy ys).1, p.1), p.2)) := by
  simp only [FramedCodec.seq, bareListFc]
  cases natFieldFc.decPrefix (bareListGreedy ys).2 <;> rfl

/-- A bare `encList`-encoded list can be the first field of a lawful `FramedCodec.seq`
    record: `bareListFc` fails `PrefixDecEnc` (so `seq_prefixDecEnc` does not apply), yet
    `bareListFc.seq natFieldFc` satisfies both `PrefixDecEnc` and `PrefixEncDec`. -/
theorem bareList_first_field_lawful :
    ¬ PrefixDecEnc bareListFc ∧
    PrefixDecEnc (bareListFc.seq natFieldFc) ∧
    PrefixEncDec (bareListFc.seq natFieldFc) := by
  refine ⟨no_prefixDecEnc_for_encList bareListElemEnc false _, ?_, ?_⟩
  · rintro ⟨xs, n⟩ rest
    rw [bareListSeq_decPrefix_eq]
    have : (bareListFc.seq natFieldFc).enc (xs, n) ++ rest =
        encList bareListElemEnc xs ++ (n + 2) :: rest := by
      simp [FramedCodec.seq, bareListFc, natFieldFc]
    rw [this, bareListGreedy_encList]
    rfl
  · intro ys ⟨xs, n⟩ rest h
    rw [bareListSeq_decPrefix_eq] at h
    have hs := bareListGreedy_sound ys
    generalize bareListGreedy ys = g at h hs
    obtain ⟨l, r⟩ := g
    simp only at h hs
    match r, h, hs with
    | (k + 2) :: r', h, hs =>
      simp only [natFieldFc, Option.map] at h
      cases h
      rw [hs]; simp [FramedCodec.seq, bareListFc, natFieldFc]
    | [], h, _ => simp [natFieldFc] at h
    | 0 :: _, h, _ => simp [natFieldFc] at h
    | 1 :: _, h, _ => simp [natFieldFc] at h

/-! ## Every function has a `FiberSplit` classically

The `hde` and `hed` arguments of `fiberSplitOfLawful` are needed only for its choice-free
construction from `c.dec`: with `Classical.choice`, every function has a `FiberSplit`. -/

open Classical in
/-- Classical fiber split of an arbitrary function, built with `Classical.choice`. -/
noncomputable def classicalFiberSplit {A : Type u} {B : Type v} (f : A → B) : FiberSplit f :=
  fun b => if h : ∃ a, f a = b then PSum.inl ⟨Classical.choose h, Classical.choose_spec h⟩
    else PSum.inr (fun a ha => h ⟨a, ha⟩)

/-- Classically, `FiberSplit f` is inhabited for every function `f`. -/
theorem fiberSplit_exists_for_every_function {A : Type u} {B : Type v} (f : A → B) :
    Nonempty (FiberSplit f) := ⟨classicalFiberSplit f⟩

end Toy.Codec
